module

public import CFSG.Monster.AxisCount.CertBasic

public section

namespace CFSG.Monster.AxisCount.Cert

open CFSG.Monster.AxisCount.Native

@[expose] def orbit0 : OrbitData where
  gamma := []
  UA := [pl 0, .sign 1582, .rho (false, 1631, 2431), .rho (false, 0, 2770), .rho (false, 0, 20),
        pl 72, .xi, .xi, .rho (false, 0, 12), pl 40, .xi, .xi, .rho (false, 0, 58), pl 73, pl 0]
  UB := [pl 0, .sign 3157, .rho (false, 2655, 1727), .rho (false, 0, 3261), .rho (false, 0, 40),
        pl 74, .xi, .xi, .rho (false, 0, 20), pl 75, .xi, .rho (false, 0, 24), pl 76, pl 0]
  h := #[[pl 0, .rho (false, 0, 3928), .rho (false, 0, 34), pl 77, .xi, .xi, pl 0],
        [pl 0, .rho (false, 0, 2377), .rho (false, 0, 42), pl 78, .xi, .xi, pl 0],
        [pl 0, .sign 1793, .rho (false, 182, 1295), .rho (false, 0, 1454), .rho (false, 0, 30),
         pl 80, .xi, .xi, .rho (false, 0, 36), pl 81, .xi, pl 0]]
  kappaPlus := #[[],
                [pl 0, .sign 59, .rho (true, 4, 0), pl 79, pl 0],
                [pl 0, .rho (true, 309, 2191), .rho (false, 0, 58), pl 82, pl 0]]
  kappaMinus := #[[],
                 [pl 0, .sign 4, .rho (true, 63, 0), .rho (false, 0, 62), pl 79, pl 0],
                 [pl 0, .rho (false, 309, 2191), .rho (false, 0, 770), .rho (false, 0, 58), pl 82,
                  pl 0]]
  tPlus := #[0, 1, 2]
  tMinus := #[0, 1, 2]
  size := #[46575, 4098600, 4147200]
  lam := #[16445440, 2224128, 61568]

@[expose] def orbit1 : OrbitData where
  gamma := [pl 0, .sign 1682, .rho (true, 142, 1350), .rho (false, 0, 1788), .rho (false, 0, 46),
             pl 1, .xi, .xi, pl 2, .xi, .xi, .rho (false, 0, 58), pl 3, .xi, .xi,
             .rho (false, 0, 24), pl 4, pl 0, .tau]
  UA := [pl 0, .sign 3963, .rho (true, 3092, 407), .rho (false, 0, 2745), .rho (false, 0, 10), pl 83,
        .xi, .xi, .rho (false, 0, 6), pl 47, .xi, pl 0]
  UB := [pl 0, .sign 2990, .rho (false, 3986, 1106), .rho (false, 0, 2153), .rho (false, 0, 58),
        pl 84, .xi, .xi, .rho (false, 0, 18), pl 85, pl 0]
  h := #[[pl 0, .rho (false, 0, 3928), .rho (false, 0, 34), pl 77, .xi, .xi, pl 0],
        [pl 0, .rho (false, 0, 4008), .rho (false, 0, 6), pl 88, .xi, .xi, pl 0],
        [pl 0, .rho (false, 0, 1798), .rho (false, 0, 16), pl 90, .xi, .xi, pl 0],
        [pl 0, .sign 3910, .rho (true, 3352, 3705), .rho (false, 0, 209), .rho (false, 0, 2), pl 94,
         .xi, .xi, pl 2, .xi, .xi, .rho (false, 0, 58), pl 95, .xi, .xi, pl 0],
        [pl 0, .sign 3404, .rho (false, 1581, 1843), .rho (false, 0, 743), .rho (false, 0, 2),
         pl 97, .xi, .xi, pl 2, .xi, .xi, .rho (false, 0, 58), pl 95, .xi, .xi, pl 0]]
  kappaPlus := #[[pl 0, .sign 30, .rho (false, 3254, 2283), .rho (false, 0, 317),
                 .rho (false, 0, 10), pl 86, .xi, .xi, pl 0],
                [pl 0, .sign 253, .rho (true, 142, 1350), .rho (false, 0, 2628), .rho (false, 0, 6),
                 pl 89, .xi, pl 2, pl 0],
                [pl 0, .sign 3914, .rho (true, 1388, 2096), .rho (false, 0, 2517),
                 .rho (false, 0, 60), pl 91, .xi, .rho (false, 0, 40), pl 92, pl 0],
                [pl 0, .sign 1414, .rho (true, 313, 515), .rho (false, 0, 2741), pl 96, pl 0],
                [pl 0, .sign 577, .rho (true, 1870, 640), .rho (false, 0, 1343),
                 .rho (false, 0, 34), pl 98, pl 0]]
  kappaMinus := #[[pl 0, .sign 2276, .rho (false, 2217, 2186), .rho (false, 0, 1874),
                  .rho (false, 0, 10), pl 87, .xi, pl 0],
                 [pl 0, .rho (false, 0, 9), pl 0],
                 [pl 0, .sign 1491, .rho (false, 1170, 768), .rho (false, 0, 3257),
                  .rho (false, 0, 12), pl 93, .xi, .rho (false, 0, 40), pl 92, pl 0],
                 [pl 0, .sign 1862, .rho (true, 1663, 3839), .rho (false, 0, 2848), pl 96, pl 0],
                 [pl 0, .sign 577, .rho (true, 1328, 2745), .rho (false, 0, 258),
                  .rho (false, 0, 34), pl 98, pl 0]]
  tPlus := #[2, 0, 1, 3, 4]
  tMinus := #[2, 1, 1, 3, 4]
  size := #[241920, 135, 32400, 3870720, 4147200]
  lam := #[16445440, 110592, 5087232, 606208, 6623232]

@[expose] def orbit2 : OrbitData where
  gamma := [pl 0, .sign 2247, .rho (false, 3627, 3205), .rho (false, 0, 4045), .rho (false, 0, 24),
             pl 5, .xi, .xi, .rho (false, 0, 60), pl 6, .xi, .rho (false, 0, 60), pl 7, .xi,
             .rho (false, 0, 30), pl 8, pl 0, .tau]
  UA := [pl 0, .sign 1631, .rho (true, 63, 0), .rho (false, 0, 3118), .rho (false, 0, 2), pl 99, pl 0]
  UB := [pl 0, .sign 2300, .rho (true, 63, 0), .rho (false, 0, 3412), .rho (false, 0, 22), pl 100,
        pl 0]
  h := #[[pl 0, .rho (false, 0, 3928), .rho (false, 0, 34), pl 77, .xi, .xi, pl 0],
        [pl 0, .sign 3910, .rho (true, 3352, 3705), .rho (false, 0, 209), .rho (false, 0, 2), pl 94,
         .xi, .xi, pl 2, .xi, .xi, .rho (false, 0, 58), pl 95, .xi, .xi, pl 0],
        [pl 0, .sign 2334, .rho (false, 737, 2245), .rho (false, 0, 2942), .rho (false, 0, 34),
         pl 105, .xi, .xi, .rho (false, 0, 6), pl 106, .xi, .xi, .rho (false, 0, 60), pl 107, .xi,
         .xi, pl 0],
        [pl 0, .sign 64, .rho (false, 103, 1822), .rho (false, 0, 158), pl 109, .xi, pl 110, .xi,
         .xi, pl 0],
        [pl 0, .sign 530, .rho (false, 826, 0), .rho (false, 0, 3904), .rho (false, 0, 12), pl 113,
         .xi, .xi, .rho (false, 0, 36), pl 81, .xi, pl 0],
        [pl 0, .rho (true, 3369, 1313), .rho (false, 0, 911), .rho (false, 0, 40), pl 117, .xi, .xi,
         .rho (false, 0, 36), pl 81, .xi, .xi, pl 0],
        [pl 0, .sign 2560, .rho (false, 2566, 1359), .rho (false, 0, 2959), pl 120, .xi,
         .rho (false, 0, 2), pl 121, .xi, .xi, pl 0],
        [pl 0, .sign 1787, .rho (false, 3860, 2589), .rho (false, 0, 74), .rho (false, 0, 18),
         pl 124, .xi, .xi, .rho (false, 0, 2), pl 63, .xi, .rho (false, 0, 14), pl 125, .xi, .xi,
         pl 0],
        []]
  kappaPlus := #[[pl 0, .sign 314, .rho (false, 23, 23), .rho (false, 0, 325), .rho (false, 0, 58),
                 pl 101, .xi, .xi, .rho (false, 0, 60), pl 102, pl 0],
                [pl 0, .sign 3352, .rho (true, 824, 773), .rho (false, 0, 1482),
                 .rho (false, 0, 60), pl 104, pl 0],
                [pl 0, .sign 7, .rho (false, 2823, 1953), .rho (false, 0, 4011),
                 .rho (false, 0, 58), pl 108, pl 0],
                [pl 0, .sign 64, .rho (false, 65, 185), .rho (false, 0, 3897), pl 111, .xi, pl 2,
                 .xi, .xi, pl 0],
                [pl 0, .sign 2601, .rho (false, 3584, 174), .rho (false, 0, 119),
                 .rho (false, 0, 40), pl 114, .xi, .xi, .rho (false, 0, 12), pl 115, pl 0],
                [pl 0, .sign 240, .rho (false, 2198, 2186), .rho (false, 0, 881),
                 .rho (false, 0, 58), pl 118, .xi, .xi, .rho (false, 0, 40), pl 92, pl 0],
                [pl 0, .sign 2999, .rho (true, 3827, 716), .rho (false, 0, 2264),
                 .rho (false, 0, 18), pl 122, .xi, .xi, pl 2, pl 0],
                [pl 0, .sign 1316, .rho (true, 4048, 4047), .rho (false, 0, 3240),
                 .rho (false, 0, 42), pl 126, pl 0],
                [pl 0, .rho (false, 0, 62), pl 0]]
  kappaMinus := #[[pl 0, .sign 3876, .rho (true, 9, 54), .rho (false, 0, 3901), .rho (false, 0, 54),
                  pl 103, .xi, pl 0],
                 [pl 0, .sign 2585, .rho (false, 2334, 2352), .rho (false, 0, 2409),
                  .rho (false, 0, 60), pl 104, pl 0],
                 [pl 0, .sign 7, .rho (true, 2879, 158), .rho (false, 0, 3981), .rho (false, 0, 58),
                  pl 108, pl 0],
                 [pl 0, .sign 1228, .rho (false, 1213, 813), .rho (false, 0, 1129),
                  .rho (false, 0, 34), pl 112, .xi, .xi, .rho (false, 0, 58), pl 28, .xi, pl 0],
                 [pl 0, .sign 2601, .rho (true, 2569, 64), .rho (false, 0, 526),
                  .rho (false, 0, 40), pl 114, .xi, .xi, .rho (false, 0, 36), pl 116, pl 0],
                 [pl 0, .sign 3453, .rho (true, 2108, 0), .rho (false, 0, 3089),
                  .rho (false, 0, 48), pl 119, .xi, .rho (false, 0, 40), pl 92, pl 0],
                 [pl 0, .sign 1537, .rho (false, 1867, 2560), .rho (false, 0, 810),
                  .rho (false, 0, 10), pl 123, .xi, .xi, pl 2, pl 0],
                 [pl 0, .sign 1316, .rho (true, 2763, 1088), .rho (false, 0, 4057),
                  .rho (false, 0, 42), pl 126, pl 0],
                 [pl 0, .sign 192, .rho (true, 2117, 1959), .rho (false, 0, 2383),
                  .rho (false, 0, 6), pl 127, .xi, .xi, pl 128, .xi, pl 129, pl 0]]
  tPlus := #[1, 5, 6, 2, 4, 3, 3, 7, 2]
  tMinus := #[2, 5, 6, 2, 4, 3, 3, 7, 0]
  size := #[3542, 518144, 3627008, 16192, 485760, 971520, 32384, 2637824, 1]
  lam := #[16445440, 606208, 16429056, 20538, 7077946, 11726860, 368652, 9327634, 63]

@[expose] def orbit3 : OrbitData where
  gamma := [pl 0, .sign 970, .rho (false, 58, 58), .rho (false, 0, 1926), .rho (false, 0, 62),
             pl 9, .xi, .xi, pl 10, .xi, pl 0, .tau, pl 0, .xi, .xi, .rho (false, 0, 60), pl 11,
             .xi, .xi, .rho (false, 0, 58), pl 12, .xi, .xi, pl 0, .tau, .tau, pl 0, .xi, .xi,
             .rho (false, 0, 24), pl 13, .xi, .xi, .rho (false, 0, 42), pl 14, .xi, pl 0, .tau,
             pl 0, .xi, .xi, .rho (false, 0, 24), pl 13, .xi, .xi, .rho (false, 0, 58), pl 15, pl 0,
             .tau, .tau, pl 0, .xi, .xi, .rho (false, 0, 18), pl 16, .xi, .xi, .rho (false, 0, 30),
             pl 17, pl 0, .tau, pl 0, .xi, .rho (false, 0, 20), pl 18, .xi, pl 0, .tau]
  UA := [pl 0, .sign 2054, .rho (true, 411, 3072), .rho (false, 0, 3526), .rho (false, 0, 60),
        pl 130, .xi, .xi, .rho (false, 0, 6), pl 131, .xi, .xi, pl 0]
  UB := [pl 0, .sign 1291, .rho (true, 471, 1788), .rho (false, 0, 2375), .rho (false, 0, 12),
        pl 132, .xi, .rho (false, 0, 6), pl 47, .xi, .xi, pl 0]
  h := #[[pl 0, .rho (false, 0, 3928), .rho (false, 0, 34), pl 77, .xi, .xi, pl 0],
        [pl 0, .rho (false, 0, 4008), .rho (false, 0, 6), pl 88, .xi, .xi, pl 0],
        [pl 0, .rho (false, 0, 2377), .rho (false, 0, 42), pl 78, .xi, .xi, pl 0],
        [pl 0, .rho (false, 0, 835), .rho (false, 0, 2), pl 141, .xi, .xi, pl 0],
        [pl 0, .rho (false, 0, 1798), .rho (false, 0, 16), pl 90, .xi, .xi, pl 0],
        [pl 0, .rho (false, 0, 923), .rho (false, 0, 12), pl 149, .xi, .xi, pl 0],
        [pl 0, .rho (false, 0, 3827), .rho (false, 0, 34), pl 153, .xi, .xi, pl 0],
        [pl 0, .sign 3910, .rho (true, 3352, 3705), .rho (false, 0, 209), .rho (false, 0, 2), pl 94,
         .xi, .xi, pl 2, .xi, .xi, .rho (false, 0, 58), pl 95, .xi, .xi, pl 0],
        [pl 0, .sign 3404, .rho (false, 1581, 1843), .rho (false, 0, 743), .rho (false, 0, 2),
         pl 97, .xi, .xi, pl 2, .xi, .xi, .rho (false, 0, 58), pl 95, .xi, .xi, pl 0],
        [pl 0, .sign 2334, .rho (false, 737, 2245), .rho (false, 0, 2942), .rho (false, 0, 34),
         pl 105, .xi, .xi, .rho (false, 0, 6), pl 106, .xi, .xi, .rho (false, 0, 60), pl 107, .xi,
         .xi, pl 0],
        [pl 0, .sign 1290, .rho (true, 3135, 60), .rho (false, 0, 2338), .rho (false, 0, 58),
         pl 162, .xi, .xi, .rho (false, 0, 60), pl 163, .xi, .xi, .rho (false, 0, 58), pl 95, .xi,
         .xi, pl 0],
        [pl 0, .sign 530, .rho (false, 826, 0), .rho (false, 0, 3904), .rho (false, 0, 12), pl 113,
         .xi, .xi, .rho (false, 0, 36), pl 81, .xi, pl 0],
        [pl 0, .sign 158, .rho (false, 2305, 238), .rho (false, 0, 2978), .rho (false, 0, 8),
         pl 171, .xi, .xi, .rho (false, 0, 36), pl 81, .xi, pl 0],
        [pl 0, .rho (true, 215, 1582), .rho (false, 0, 2303), .rho (false, 0, 28), pl 174, .xi, .xi,
         .rho (false, 0, 36), pl 81, .xi, .xi, pl 0],
        [pl 0, .sign 2294, .rho (true, 2249, 2139), .rho (false, 0, 2001), .rho (false, 0, 36),
         pl 176, .xi, .rho (false, 0, 36), pl 81, .xi, pl 0],
        [pl 0, .sign 2865, .rho (true, 73, 2575), .rho (false, 0, 1127), .rho (false, 0, 10),
         pl 178, .xi, .xi, .rho (false, 0, 36), pl 81, .xi, pl 0]]
  kappaPlus := #[[pl 0, .sign 622, .rho (false, 2825, 2600), .rho (false, 0, 1909),
                 .rho (false, 0, 30), pl 133, .xi, .xi, pl 53, pl 0],
                [pl 0, .sign 1048, .rho (false, 1326, 3352), .rho (false, 0, 4022),
                 .rho (false, 0, 46), pl 135, .xi, .xi, .rho (false, 0, 6), pl 136, .xi, .xi,
                 .rho (false, 0, 36), pl 137, pl 0],
                [pl 0, .sign 3643, .rho (true, 1853, 878), .rho (false, 0, 1037),
                 .rho (false, 0, 20), pl 138, .xi, .rho (false, 0, 48), pl 139, pl 0],
                [pl 0, .sign 1228, .rho (true, 1542, 2535), .rho (false, 0, 3491),
                 .rho (false, 0, 48), pl 142, .xi, .xi, .rho (false, 0, 24), pl 143, pl 0],
                [pl 0, .sign 2493, .rho (true, 1581, 1843), .rho (false, 0, 2684),
                 .rho (false, 0, 54), pl 146, .xi, .rho (false, 0, 4), pl 23, pl 0],
                [pl 0, .sign 2187, .rho (true, 2096, 371), .rho (false, 0, 1927), pl 150, .xi,
                 .rho (false, 0, 36), pl 151, .xi, pl 0],
                [pl 0, .sign 3136, .rho (true, 2202, 3210), .rho (false, 0, 2958),
                 .rho (false, 0, 34), pl 154, .xi, .xi, pl 2, pl 0],
                [pl 0, .sign 119, .rho (false, 259, 518), .rho (false, 0, 2401), pl 156, pl 0],
                [pl 0, .sign 2014, .rho (false, 3238, 3618), .rho (false, 0, 3771),
                 .rho (false, 0, 36), pl 157, .xi, .rho (false, 0, 12), pl 158, pl 0],
                [pl 0, .sign 3858, .rho (false, 3868, 2569), .rho (false, 0, 1679), pl 160, .xi,
                 .xi, .rho (false, 0, 6), pl 131, .xi, pl 0],
                [pl 0, .sign 2369, .rho (true, 806, 1157), .rho (false, 0, 3582), pl 164, .xi,
                 .rho (false, 0, 60), pl 102, pl 0],
                [pl 0, .sign 13, .rho (true, 427, 432), .rho (false, 0, 1916), .rho (false, 0, 10),
                 pl 167, .xi, pl 168, pl 0],
                [pl 0, .sign 2068, .rho (true, 1260, 3170), .rho (false, 0, 2458),
                 .rho (false, 0, 6), pl 172, .xi, .rho (false, 0, 40), pl 92, pl 0],
                [pl 0, .sign 4029, .rho (true, 2183, 1354), .rho (false, 0, 1377), pl 175, pl 0],
                [pl 0, .sign 3935, .rho (true, 97, 1831), .rho (false, 0, 684), .rho (false, 0, 36),
                 pl 177, .xi, pl 128, pl 0],
                [pl 0, .sign 58, .rho (true, 3345, 2864), .rho (false, 0, 2865),
                 .rho (false, 0, 58), pl 179, .xi, .rho (false, 0, 40), pl 180, pl 0]]
  kappaMinus := #[[pl 0, .sign 2886, .rho (true, 539, 2529), .rho (false, 0, 1992), pl 134, .xi,
                  pl 53, pl 0],
                 [pl 0, .sign 2108, .rho (false, 12, 51), .rho (false, 0, 546), .rho (false, 0, 6),
                  pl 0, pl 0],
                 [pl 0, .sign 4069, .rho (true, 2254, 3218), .rho (false, 0, 2326), pl 140, .xi,
                  .xi, .rho (false, 0, 48), pl 139, pl 0],
                 [pl 0, .sign 1985, .rho (false, 1906, 256), .rho (false, 0, 2266), pl 144, .xi,
                  .xi, .rho (false, 0, 28), pl 145, pl 0],
                 [pl 0, .sign 3325, .rho (false, 1648, 560), .rho (false, 0, 3613),
                  .rho (false, 0, 60), pl 147, .xi, .rho (false, 0, 24), pl 148, pl 0],
                 [pl 0, .sign 4032, .rho (true, 583, 3476), .rho (false, 0, 3097),
                  .rho (false, 0, 34), pl 152, .xi, .xi, .rho (false, 0, 40), pl 92, pl 0],
                 [pl 0, .sign 320, .rho (true, 1032, 2748), .rho (false, 0, 2056), pl 155, .xi,
                  .rho (false, 0, 2), pl 121, .xi, pl 0],
                 [pl 0, .sign 369, .rho (true, 77, 2566), .rho (false, 0, 2533), pl 156, pl 0],
                 [pl 0, .sign 646, .rho (false, 3680, 3479), .rho (false, 0, 3520),
                  .rho (false, 0, 16), pl 159, .xi, .rho (false, 0, 12), pl 158, pl 0],
                 [pl 0, .sign 2847, .rho (false, 1087, 60), .rho (false, 0, 2345), pl 161, .xi, .xi,
                  .rho (false, 0, 6), pl 131, .xi, pl 0],
                 [pl 0, .sign 2137, .rho (true, 2049, 60), .rho (false, 0, 1437),
                  .rho (false, 0, 36), pl 165, .xi, .xi, .rho (false, 0, 60), pl 166, pl 0],
                 [pl 0, .sign 2107, .rho (true, 2849, 128), .rho (false, 0, 1343),
                  .rho (false, 0, 6), pl 169, .xi, .rho (false, 0, 6), pl 170, pl 0],
                 [pl 0, .sign 1, .rho (false, 2307, 722), .rho (false, 0, 2132), .rho (false, 0, 6),
                  pl 173, .xi, .xi, .rho (false, 0, 40), pl 92, pl 0],
                 [pl 0, .sign 984, .rho (false, 2911, 39), .rho (false, 0, 3615), pl 175, pl 0],
                 [pl 0, .sign 3935, .rho (true, 3902, 246), .rho (false, 0, 1098),
                  .rho (false, 0, 36), pl 177, .xi, pl 128, pl 0],
                 [pl 0, .sign 2213, .rho (true, 3516, 3099), .rho (false, 0, 570),
                  .rho (false, 0, 12), pl 181, .xi, .xi, pl 110, pl 0]]
  tPlus := #[3, 1, 3, 4, 3, 2, 3, 9, 11, 10, 6, 7, 6, 11, 5, 6]
  tMinus := #[3, 3, 3, 4, 4, 3, 2, 9, 11, 10, 6, 7, 6, 11, 5, 5]
  size := #[12096, 63, 40320, 60480, 30240, 2160, 72, 1032192, 2211840, 774144, 129024, 1935360,
           967680, 1032192, 32256, 32256]
  lam := #[16445440, 110592, 2224128, 4497408, 5087232, 14352384, 348160, 606208, 6623232, 16429056,
         126976, 7077946, 15851800, 6766872, 2351384, 589945]

@[expose] def orbit4 : OrbitData where
  gamma := [pl 0, .sign 3412, .rho (false, 2023, 280), .rho (false, 0, 1859), .rho (false, 0, 32),
             pl 19, .xi, .rho (false, 0, 24), pl 20, .xi, .xi, .rho (false, 0, 46), pl 21, pl 0,
             .tau, pl 0, .xi, .rho (false, 0, 50), pl 22, pl 0, .tau, .tau, pl 0, .xi,
             .rho (false, 0, 4), pl 23, .xi, pl 0, .tau]
  UA := [pl 0, .sign 704, .rho (true, 722, 630), .rho (false, 0, 3088), .rho (false, 0, 46), pl 182,
        .xi, .rho (false, 0, 48), pl 183, pl 0]
  UB := [pl 0, .sign 597, .rho (false, 2706, 1122), .rho (false, 0, 3413), .rho (false, 0, 36),
        pl 184, .xi, .xi, .rho (false, 0, 48), pl 183, pl 0]
  h := #[[pl 0, .rho (false, 0, 3928), .rho (false, 0, 34), pl 77, .xi, .xi, pl 0],
        [pl 0, .rho (false, 0, 4008), .rho (false, 0, 6), pl 88, .xi, .xi, pl 0],
        [pl 0, .rho (false, 0, 1798), .rho (false, 0, 16), pl 90, .xi, .xi, pl 0],
        [pl 0, .rho (false, 0, 923), .rho (false, 0, 12), pl 149, .xi, .xi, pl 0],
        [pl 0, .rho (false, 0, 2145), .rho (false, 0, 6), pl 38, .xi, .xi, pl 0],
        [pl 0, .rho (false, 0, 3307), .rho (false, 0, 10), pl 202, .xi, .xi, pl 0],
        [pl 0, .sign 3910, .rho (true, 3352, 3705), .rho (false, 0, 209), .rho (false, 0, 2), pl 94,
         .xi, .xi, pl 2, .xi, .xi, .rho (false, 0, 58), pl 95, .xi, .xi, pl 0],
        [pl 0, .sign 3404, .rho (false, 1581, 1843), .rho (false, 0, 743), .rho (false, 0, 2),
         pl 97, .xi, .xi, pl 2, .xi, .xi, .rho (false, 0, 58), pl 95, .xi, .xi, pl 0],
        [pl 0, .sign 2334, .rho (false, 737, 2245), .rho (false, 0, 2942), .rho (false, 0, 34),
         pl 105, .xi, .xi, .rho (false, 0, 6), pl 106, .xi, .xi, .rho (false, 0, 60), pl 107, .xi,
         .xi, pl 0],
        [pl 0, .sign 1290, .rho (true, 3135, 60), .rho (false, 0, 2338), .rho (false, 0, 58),
         pl 162, .xi, .xi, .rho (false, 0, 60), pl 163, .xi, .xi, .rho (false, 0, 58), pl 95, .xi,
         .xi, pl 0],
        [pl 0, .sign 2329, .rho (true, 3450, 1477), .rho (false, 0, 573), .rho (false, 0, 40),
         pl 217, .xi, .xi, .rho (false, 0, 6), pl 136, .xi, .xi, pl 218, .xi, .xi, pl 0],
        [pl 0, .sign 530, .rho (false, 826, 0), .rho (false, 0, 3904), .rho (false, 0, 12), pl 113,
         .xi, .xi, .rho (false, 0, 36), pl 81, .xi, pl 0],
        [pl 0, .sign 94, .rho (false, 2305, 238), .rho (false, 0, 3426), .rho (false, 0, 14),
         pl 225, .xi, .xi, .rho (false, 0, 36), pl 81, .xi, pl 0],
        [pl 0, .rho (true, 15, 15), .rho (false, 0, 1546), .rho (false, 0, 60), pl 227, .xi, .xi,
         .rho (false, 0, 36), pl 81, .xi, .xi, pl 0]]
  kappaPlus := #[[pl 0, .sign 676, .rho (false, 57, 57), .rho (false, 0, 563), .rho (false, 0, 40),
                 pl 185, .xi, .xi, .rho (false, 0, 6), pl 186, pl 0],
                [pl 0, .sign 3210, .rho (false, 1813, 2129), .rho (false, 0, 407),
                 .rho (false, 0, 12), pl 189, .xi, pl 2, pl 0],
                [pl 0, .sign 2786, .rho (true, 833, 1179), .rho (false, 0, 2196),
                 .rho (false, 0, 10), pl 191, .xi, .xi, .rho (false, 0, 48), pl 192, pl 0],
                [pl 0, .sign 3033, .rho (true, 952, 2900), .rho (false, 0, 2581), pl 195, .xi,
                 .rho (false, 0, 22), pl 196, pl 0],
                [pl 0, .sign 445, .rho (false, 237, 1748), .rho (false, 0, 2061),
                 .rho (false, 0, 18), pl 199, .xi, .rho (false, 0, 40), pl 200, .xi, pl 0],
                [pl 0, .sign 3722, .rho (false, 605, 886), .rho (false, 0, 2456),
                 .rho (false, 0, 40), pl 203, .xi, .rho (false, 0, 34), pl 204, .xi,
                 .rho (false, 0, 10), pl 205, pl 0],
                [pl 0, .sign 1274, .rho (true, 3878, 1545), .rho (false, 0, 1333),
                 .rho (false, 0, 12), pl 207, .xi, .rho (false, 0, 20), pl 208, .xi, pl 0],
                [pl 0, .sign 2719, .rho (false, 2891, 1048), .rho (false, 0, 967),
                 .rho (false, 0, 34), pl 210, .xi, .rho (false, 0, 40), pl 92, pl 0],
                [pl 0, .sign 3173, .rho (true, 3125, 4041), .rho (false, 0, 2917),
                 .rho (false, 0, 46), pl 212, .xi, .xi, pl 213, pl 0],
                [pl 0, .sign 700, .rho (true, 345, 972), .rho (false, 0, 2104), .rho (false, 0, 54),
                 pl 215, .xi, .xi, .rho (false, 0, 40), pl 180, pl 0],
                [pl 0, .sign 162, .rho (true, 4077, 3298), .rho (false, 0, 1211),
                 .rho (false, 0, 48), pl 219, .xi, .xi, .rho (false, 0, 40), pl 180, pl 0],
                [pl 0, .sign 41, .rho (true, 17, 46), .rho (false, 0, 227), .rho (false, 0, 34),
                 pl 221, .xi, .rho (false, 0, 10), pl 222, pl 0],
                [pl 0, .sign 2008, .rho (false, 118, 2575), .rho (false, 0, 3301),
                 .rho (false, 0, 54), pl 226, .xi, .rho (false, 0, 40), pl 92, pl 0],
                [pl 0, .sign 1227, .rho (false, 1317, 3849), .rho (false, 0, 2885), pl 228, pl 0]]
  kappaMinus := #[[pl 0, .sign 250, .rho (false, 1026, 60), .rho (false, 0, 831), .rho (false, 0, 6),
                  pl 187, .xi, .rho (false, 0, 6), pl 188, pl 0],
                 [pl 0, .sign 3304, .rho (true, 1210, 2903), .rho (false, 0, 2518),
                  .rho (false, 0, 40), pl 190, .xi, .xi, pl 2, pl 0],
                 [pl 0, .sign 287, .rho (false, 1852, 850), .rho (false, 0, 571),
                  .rho (false, 0, 34), pl 193, .xi, .xi, .rho (false, 0, 18), pl 194, pl 0],
                 [pl 0, .sign 1073, .rho (true, 2521, 232), .rho (false, 0, 2897), pl 197, .xi, .xi,
                  pl 198, pl 0],
                 [pl 0, .sign 3951, .rho (false, 3873, 2344), .rho (false, 0, 1219),
                  .rho (false, 0, 12), pl 93, .xi, pl 201, pl 0],
                 [pl 0, .rho (false, 48, 15), .rho (false, 0, 118), .rho (false, 0, 60), pl 206,
                  pl 0],
                 [pl 0, .sign 3532, .rho (false, 1093, 2703), .rho (false, 0, 3119),
                  .rho (false, 0, 16), pl 209, .xi, .rho (false, 0, 20), pl 208, .xi, pl 0],
                 [pl 0, .sign 3305, .rho (false, 925, 758), .rho (false, 0, 2658),
                  .rho (false, 0, 18), pl 211, .xi, .rho (false, 0, 40), pl 92, pl 0],
                 [pl 0, .sign 3096, .rho (true, 3879, 1553), .rho (false, 0, 2717),
                  .rho (false, 0, 36), pl 214, .xi, .xi, pl 213, pl 0],
                 [pl 0, .sign 3823, .rho (true, 1870, 640), .rho (false, 0, 3637),
                  .rho (false, 0, 12), pl 216, .xi, .xi, pl 0],
                 [pl 0, .sign 3916, .rho (false, 1482, 2122), .rho (false, 0, 1389), pl 220, .xi,
                  .xi, pl 0],
                 [pl 0, .sign 2287, .rho (false, 269, 2693), .rho (false, 0, 3353), pl 223, .xi,
                  .xi, .rho (false, 0, 46), pl 224, pl 0],
                 [pl 0, .sign 2020, .rho (false, 1938, 826), .rho (false, 0, 2876),
                  .rho (false, 0, 54), pl 226, .xi, .rho (false, 0, 40), pl 92, pl 0],
                 [pl 0, .sign 222, .rho (true, 1476, 3519), .rho (false, 0, 1558), pl 228, pl 0]]
  tPlus := #[3, 4, 3, 4, 2, 1, 11, 10, 6, 10, 9, 7, 8, 8]
  tMinus := #[4, 4, 3, 4, 4, 4, 11, 10, 6, 10, 9, 7, 8, 8]
  size := #[26880, 120, 3360, 13440, 240, 15, 3440640, 3440640, 430080, 215040, 245760, 215040,
           245760, 15360]
  lam := #[16445440, 110592, 5087232, 14352384, 1654784, 434176, 606208, 6623232, 16429056, 126976,
         1617920, 7077946, 4519984, 2664496]

@[expose] def orbit5 : OrbitData where
  gamma := [pl 0, .sign 425, .rho (true, 632, 3476), .rho (false, 0, 665), .rho (false, 0, 28),
             pl 24, .xi, .rho (false, 0, 24), pl 20, .xi, .xi, .rho (false, 0, 60), pl 25, .xi, .xi,
             .rho (false, 0, 60), pl 26, pl 0, .tau, pl 0, .xi, .rho (false, 0, 58), pl 27, .xi,
             .rho (false, 0, 58), pl 28, .xi, pl 0, .tau]
  UA := [pl 0, .sign 2618, .rho (true, 3927, 296), .rho (false, 0, 382), .rho (false, 0, 20), pl 229,
        .xi, .rho (false, 0, 20), pl 230, .xi, .rho (false, 0, 58), pl 28, .xi, .xi, pl 0]
  UB := [pl 0, .sign 3669, .rho (false, 1310, 1832), .rho (false, 0, 44), .rho (false, 0, 58),
        pl 231, .xi, .xi, pl 232, .xi, .xi, .rho (false, 0, 60), pl 233, .xi, .xi, pl 0]
  h := #[[pl 0, .rho (false, 0, 3928), .rho (false, 0, 34), pl 77, .xi, .xi, pl 0],
        [pl 0, .rho (false, 0, 2377), .rho (false, 0, 42), pl 78, .xi, .xi, pl 0],
        [pl 0, .rho (false, 0, 835), .rho (false, 0, 2), pl 141, .xi, .xi, pl 0],
        [pl 0, .rho (false, 0, 923), .rho (false, 0, 12), pl 149, .xi, .xi, pl 0],
        [pl 0, .sign 2865, .rho (true, 73, 2575), .rho (false, 0, 1127), .rho (false, 0, 10),
         pl 178, .xi, .xi, .rho (false, 0, 36), pl 81, .xi, pl 0],
        [pl 0, .sign 2566, .rho (true, 295, 3165), .rho (false, 0, 3126), .rho (false, 0, 12),
         pl 249, .xi, .rho (false, 0, 36), pl 81, .xi, pl 0],
        [pl 0, .sign 290, .rho (false, 1353, 185), .rho (false, 0, 1441), .rho (false, 0, 20),
         pl 254, .xi, .xi, pl 110, .xi, .xi, pl 0],
        [pl 0, .sign 1793, .rho (false, 182, 1295), .rho (false, 0, 1454), .rho (false, 0, 30),
         pl 80, .xi, .xi, .rho (false, 0, 36), pl 81, .xi, pl 0],
        [pl 0, .sign 3851, .rho (false, 533, 3461), .rho (false, 0, 3112), .rho (false, 0, 28),
         pl 260, .xi, .rho (false, 0, 36), pl 81, .xi, pl 0],
        [pl 0, .rho (false, 0, 1359), .rho (false, 0, 24), pl 265, .xi, pl 2, .xi, .xi, pl 0]]
  kappaPlus := #[[pl 0, .sign 1128, .rho (true, 800, 1978), .rho (false, 0, 1596), pl 234, .xi, .xi,
                 .rho (false, 0, 6), pl 235, .xi, .rho (false, 0, 58), pl 28, .xi, .xi, pl 0],
                [pl 0, .sign 321, .rho (false, 17, 46), .rho (false, 0, 2705), .rho (false, 0, 48),
                 pl 236, .xi, .rho (false, 0, 62), pl 237, pl 0],
                [pl 0, .sign 1226, .rho (false, 560, 1141), .rho (false, 0, 3982),
                 .rho (false, 0, 24), pl 240, .xi, .xi, .rho (false, 0, 14), pl 69, .xi, pl 241,
                 pl 0],
                [pl 0, .sign 3349, .rho (false, 635, 3115), .rho (false, 0, 521),
                 .rho (false, 0, 18), pl 243, .xi, pl 244, .xi, .rho (false, 0, 12), pl 158, pl 0],
                [pl 0, .sign 2368, .rho (true, 2595, 3849), .rho (false, 0, 2867),
                 .rho (false, 0, 54), pl 246, .xi, .xi, .rho (false, 0, 38), pl 247, pl 0],
                [pl 0, .sign 1099, .rho (true, 3273, 963), .rho (false, 0, 3886),
                 .rho (false, 0, 24), pl 250, .xi, .rho (false, 0, 18), pl 251, .xi,
                 .rho (false, 0, 12), pl 158, pl 0],
                [pl 0, .sign 3072, .rho (true, 1060, 487), .rho (false, 0, 1349),
                 .rho (false, 0, 60), pl 255, .xi, pl 53, pl 0],
                [pl 0, .sign 2334, .rho (false, 743, 2556), .rho (false, 0, 1064),
                 .rho (false, 0, 40), pl 257, .xi, .xi, .rho (false, 0, 60), pl 107, .xi, pl 0],
                [pl 0, .sign 3438, .rho (false, 1764, 2108), .rho (false, 0, 2261),
                 .rho (false, 0, 20), pl 261, .xi, .rho (false, 0, 6), pl 259, .xi, pl 0],
                [pl 0, .sign 2236, .rho (false, 815, 2938), .rho (false, 0, 3031),
                 .rho (false, 0, 10), pl 266, .xi, .rho (false, 0, 60), pl 163, .xi, .xi, pl 267,
                 pl 0]]
  kappaMinus := #[[pl 0, .sign 3166, .rho (true, 51, 51), .rho (false, 0, 1812), pl 0],
                 [pl 0, .sign 280, .rho (false, 58, 58), .rho (false, 0, 241), .rho (false, 0, 60),
                  pl 238, .xi, .rho (false, 0, 62), pl 239, pl 0],
                 [pl 0, .sign 561, .rho (false, 421, 3172), .rho (false, 0, 3825),
                  .rho (false, 0, 36), pl 242, .xi, .xi, pl 128, pl 0],
                 [pl 0, .rho (true, 589, 852), .rho (false, 0, 625), .rho (false, 0, 6), pl 245,
                  .xi, .xi, pl 2, pl 0],
                 [pl 0, .sign 2122, .rho (true, 2743, 15), .rho (false, 0, 358),
                  .rho (false, 0, 36), pl 248, .xi, .xi, .rho (false, 0, 38), pl 247, pl 0],
                 [pl 0, .sign 1892, .rho (true, 944, 484), .rho (false, 0, 194), pl 252, .xi, .xi,
                  pl 253, .xi, .rho (false, 0, 12), pl 158, pl 0],
                 [pl 0, .sign 823, .rho (false, 2119, 1954), .rho (false, 0, 1760),
                  .rho (false, 0, 24), pl 256, .xi, pl 53, pl 0],
                 [pl 0, .sign 4023, .rho (true, 2369, 2943), .rho (false, 0, 847),
                  .rho (false, 0, 40), pl 258, .xi, .rho (false, 0, 6), pl 259, .xi, .xi, pl 0],
                 [pl 0, .sign 2142, .rho (true, 961, 3315), .rho (false, 0, 339),
                  .rho (false, 0, 40), pl 262, .xi, .rho (false, 0, 6), pl 263, .xi, .xi,
                  .rho (false, 0, 60), pl 264, pl 0],
                 [pl 0, .sign 1024, .rho (false, 1230, 3170), .rho (false, 0, 768),
                  .rho (false, 0, 10), pl 268, .xi, .xi, pl 2, .xi, pl 267, pl 0]]
  tPlus := #[2, 7, 3, 3, 9, 11, 9, 11, 7, 5]
  tMinus := #[5, 6, 5, 6, 9, 11, 9, 11, 7, 5]
  size := #[891, 1995840, 49896, 24948, 456192, 1596672, 20736, 912384, 3193344, 41472]
  lam := #[16445440, 2224128, 4497408, 14352384, 589945, 16445561, 4198521, 61568, 15925376, 15659136]

end CFSG.Monster.AxisCount.Cert
