using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace Knapsack
{

    public class Transaction
    {
        public int Id { get; set; }
        public int Size { get; set; }
        public double Fee { get; set; }
    }

    /// <summary>
    /// Following the book by Martello & Toth p. 16-19
    /// Algorithm based on the fact that there is an optimal solution to the
    /// continuous 0-1 Knapsack problem.
    /// For j in {0,1,2,3,...n-1}=N define JC.Select(j => fees[j] / sizes[j]).ToList();
    /// where JC is initialized to be {0,1,2,3,...n-1}
    /// The procedure determines J1 and J0 using at each iteration the median of R
    /// to partition the set of items in N but not in J0 or J1.
    /// Once the final partition is known the critical item s is identified
    /// </summary>
    public static class CKP
    {
        private static HashSet<int> J1;
        private static HashSet<int> J0;
        private static HashSet<int> JC;
        private static HashSet<int> UnityXs;
        private static int _c = 0;

        private static void CriticalItem(int n, int c, List<double> fees, List<int> sizes)
        {

            HashSet<int> G = new HashSet<int>();
            HashSet<int> L = new HashSet<int>();
            HashSet<int> E = new HashSet<int>();


            for (int i = 0; i < n; i++) JC.Add(i);

            _c = c;
            int c1 = 0;
            int c2 = 0;
            var partition = false;
            while (!partition)
            {
                var R = JC.Select(j => fees[j] / sizes[j]).ToList();
                var lamda = 0.0;
                if (R.Count % 2 == 0)
                {
                    R.Sort();
                    lamda = (R[(R.Count / 2) - 1] + R[R.Count / 2]) / 2;
                }
                else
                    lamda = R.Count > 1 ? R.LowerMedian() : R.First();

                G = new HashSet<int>(JC.Where(j => fees[j] / sizes[j] > lamda));
                L = new HashSet<int>(JC.Where(j => fees[j] / sizes[j] < lamda));
                E = new HashSet<int>(JC.Where(j => fees[j] / sizes[j] == lamda));

                c1 = G.Count > 0 ? G.Select(j => sizes[j]).Sum() : 0;
                c2 = c1 + (E.Count > 0 ? E.Select(j => sizes[j]).Sum() : 0);

                partition = c1 <= _c && _c < c2;

                if (!partition)
                {
                    if (c1 > _c)
                    {
                        J0.UnionWith(L);
                        J0.UnionWith(E);
                        JC = G;
                    }
                    else
                    {
                        J1.UnionWith(G);
                        J1.UnionWith(E);
                        JC = L;
                        _c -= c2;
                    }
                }
            }
            J1.UnionWith(G);
            J0.UnionWith(L);
            JC = E;
            _c -= c1;
        }
        public static double MaximumProfit(int n, int c, List<double> Ps, List<int> Ws)
        {
            J1 = new HashSet<int>();
            J0 = new HashSet<int>();
            JC = new HashSet<int>();

            CriticalItem(n, c, Ps, Ws);

            var ws = 0;
            var sigma = 0;
            foreach (var e in JC)
            {
                ws += Ws[e];
                if (ws > _c) break;
                sigma++;
            }
            var s = JC.ElementAt(sigma);

            UnityXs = new HashSet<int>(J1.Union(JC.Where((x, j) => j < sigma - 1).ToList()));

            var maxProfit = 0.0;
            foreach (var o in UnityXs) maxProfit += Ps[o];

            var ZeroXs = Ws.Select((k, i) => new { k, i }).Where(x => !UnityXs.Contains(x.i)).Select(x => x.i);

            var max = 0.0;
            var newIndex = 0;
            foreach (var index in ZeroXs)
            {
                if (Ws[index] <= _c && Ps[index] > max)
                {
                    max = Ps[index];
                    newIndex = index;
                }
            }

            return maxProfit + max;
        }


    }

    /// <summary>
    /// Martello Toth p.30-32
    /// The Horowitz-Sahni algorithm.
    /// Forward move: insert the largest possible set of new consecutive items into the current 
    /// solution.
    /// Backtracking move: remove the last inserted item from the current solution
    /// Whenever a forward move is exhausted, the upper bound 
    ///U corresponding to the current solution is computed and compared with the best
    ///solution so far, in order to check whether further forward moves could lead to
    ///a better one: if so, a new forward move is performed, otherwise a backtracking
    ///follows.When the last item has been considered, the current solution is complete
    ///and possible updating of the best solution so far occurs.The algorithm stops when
    ///no further backtracking can be performed. 
    /// </summary>
    public static class HSKP
    {
        private static List<byte> X = new List<byte>();
        private static List<byte> Xh = new List<byte>();
        private static List<double> P = new List<double>();
        private static List<int> W = new List<int>();
        private static int n = 0;
        private static int c = 0;

        private static double z = 0.0;
        private static double zh = 0.0;
        private static int j = 0;
        private static int capacity = 0;
        private static bool SolutionFound = false;

        private static void FindUpperBound()
        {
            var wSum = 0.0;
            int r = j;
            for (int k = j; k < n; k++)
            {
                wSum += W[k];
                if (wSum > c) break;
                r++;
            }
            var U = P.Where((x, l) => l >= j && l < r - 1).Sum() + Math.Floor((capacity - W.Where((x, l) => l >= j && l < r - 1).Sum()) * P[r] / W[r]);
            if (z >= zh + U) BackTrack();
        }

        private static void BackTrack()
        {
            var source = Xh.Where((x, k) => k < j && x == 1).Select((x, k) => k);
            if (!source.Any())
            {
                SolutionFound = true;
                return;
            }
            var i = source.Max();
            capacity += W[i];
            zh -= P[i];
            Xh[i] = 0;
            j = i + 1;
            FindUpperBound();
        }

        private static void ForwardStep()
        {
            do
            {
                while (W[j] <= capacity)
                {
                    capacity -= W[j];
                    zh += P[j];
                    Xh[j] = 1;
                    j++;
                }
                if (j <= n - 1)
                {
                    Xh[j] = 0;
                    j++;
                }
                if (j < n - 1 && !SolutionFound) FindUpperBound();
            } while (j == n - 1 && !SolutionFound);
        }

        private static void UpdateSolution()
        {
            if (zh > z)
            {
                z = zh;
                X = Xh;
            }
            j = n - 1;
            if (Xh[n - 1] == 1)
            {
                capacity += W[n - 1];
                zh -= P[n - 1];
                Xh[n - 1] = 0;
            }
        }
        public static double HSMaximumProfit(int len, int cap, List<double> Ps, List<int> Ws)
        {
            n = len;
            c = cap;
            capacity = c;

            foreach (var item in Ps) P.Add(item);
            P.Add(0);
            foreach (var item in Ws) W.Add(item);
            W.Add(int.MaxValue);

            for (int i = 0; i < n; i++) X.Add(0);
            for (int i = 0; i < n; i++) Xh.Add(0);

            FindUpperBound();
            ForwardStep();
            UpdateSolution();

            var ZeroXs = X.Select((k, i) => new { k, i }).Where(x => x.k == 0).Select(x => x.i);

            var max = 0.0;
            var newIndex = 0;
            foreach (var index in ZeroXs)
            {
                if (Ws[index] <= capacity && Ps[index] > max)
                {
                    max = Ps[index];
                    newIndex = index;
                }
            }
            var result = z + max;

            return result;
        }
    }

    /// <summary>
    /// Brute Force 
    /// Compute all combinations of n per k k=1,2,...n
    /// and for each of them find the coresponding fee.
    /// Finally select the combination that returns the maximal solution
    /// </summary>
    public static class BruteForce
    {
        private static int capacity = 0;
        private static double CalculateMax(IEnumerable<IEnumerable<Transaction>> combinations)
        {

            var max = 0;
            IEnumerable<Transaction> bc = null;
            foreach (var comb in combinations)
            {
                var sum = comb.Sum(x => x.Size);
                var maxFee = comb.Sum(x => x.Fee);
                if (sum <= capacity && maxFee > max)
                {
                    max = sum;
                    bc = comb;
                }
            }
            if (bc == null || !bc.Any()) return 0.0;
            else
                return bc.Sum(x => x.Fee);
        }
        public static double BFMaxFee(List<Transaction> transactions, int c)
        {
            capacity = c;
            var n = transactions.Count;
            var max = 0.0;
            for (int i = 1; i <= n; i++)
            {
                var combs = transactions.DifferentCombinations(i);
                var calculation = CalculateMax(combs);
                if (calculation > max) max = calculation;
            }
            return max;
        }
    }
    class Program
    {
        static List<Transaction> Transactions = new List<Transaction>
        {
            new Transaction
            {
                Id = 1,
                Size = 57247,
                Fee = 0.0887
            },
            new Transaction
            {
                Id = 2,
                Size = 98732,
                Fee = 0.1856
            },
            new Transaction
            {
                Id = 3,
                Size = 134928,
                Fee = 0.2307
            },
            new Transaction
            {
                Id = 4,
                Size = 77275,
                Fee = 0.1522
            },
            new Transaction
            {
                Id = 5,
                Size = 29240,
                Fee = 0.0532
            },
            new Transaction
            {
                Id = 6,
                Size = 15440,
                Fee = 0.0250
            },
            new Transaction
            {
                Id = 7,
                Size = 70820,
                Fee = 0.1409
            },
            new Transaction
            {
                Id = 8,
                Size = 139603,
                Fee = 0.2541
            },
            new Transaction
            {
                Id = 9,
                Size = 63718,
                Fee = 0.1147
            },
            new Transaction
            {
                Id = 10,
                Size = 143807,
                Fee = 0.2660
            },
            new Transaction
            {
                Id = 11,
                Size = 190457,
                Fee = 0.2933
            },
            new Transaction
            {
                Id = 12,
                Size = 40572,
                Fee = 0.0686
            },
        };

        static void Main(string[] args)
        {

            //We sort the transactions using the delegate.
            //This is necessary for Horowitz algorithm but not for CKP
            Transactions.Sort(delegate (Transaction x, Transaction y) { return (x.Fee / x.Size).CompareTo(y.Fee / y.Size); });
            Transactions.Reverse();

            var fees = Transactions.Select(x => x.Fee).ToList();
            var sizes = Transactions.Select(x => x.Size).ToList();

            var n = 12;
            var c = 500000;

            Console.WriteLine($"Brute Force algorithm: {12.5 + BruteForce.BFMaxFee(Transactions, c)}");
            Console.ReadLine();

            Console.WriteLine($"Horowitz-Sahni algorithm: {12.5 + HSKP.HSMaximumProfit(n, c, fees, sizes)}");
            Console.ReadLine();

            Console.WriteLine($"Critical item algorithm:{12.5 + CKP.MaximumProfit(n, c, fees, sizes)}");
            Console.ReadLine();

        }
    }
}
