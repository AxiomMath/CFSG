module

public import CFSG.Monster.AxisCount.SchreierBasic

public section

namespace CFSG.Monster.AxisCount.HS

open CFSG.Monster.AxisCount.Native

@[expose] def sorbit0 : SOrbit where
  uHpp := #[[], []]
  uBaby := #[0, 0]
  lHpp := #[[], [hl 0, .rho (false, 0, 62), hl 0], [], [], [], []]
  lBaby := #[1, 1, 0, 0, 0, 0]

@[expose] def sorbit1 : SOrbit where
  uHpp :=
    #[[hl 0, .rho (false, 0, 3257), .rho (false, 0, 34), hl 20, .xi, .xi, .rho (false, 0, 1098),
       .rho (false, 0, 46), hl 21, .xi, .xi, .sign 2875, .rho (false, 2634, 1226),
       .rho (false, 0, 2484), .rho (false, 0, 34), hl 22, hl 0],
      [hl 0, .xi, .rho (false, 0, 3112), .rho (false, 0, 58), hl 23, .xi, .xi, .sign 3840,
       .rho (true, 3890, 3273), .rho (false, 0, 12), .rho (false, 0, 12), hl 24, hl 0]]
  uBaby := #[2, 1]
  lHpp :=
    #[[],
      [],
      [],
      [hl 0, .xi, .xi, .rho (false, 0, 3914), .rho (false, 0, 30), hl 25, .xi, .xi,
       .rho (false, 0, 2291), .rho (false, 0, 6), hl 26, .xi, .sign 587,
       .rho (false, 3588, 3246), .rho (false, 0, 987), .rho (false, 0, 60), hl 27, hl 0],
      [hl 0, .xi, .xi, .rho (false, 0, 3914), .rho (false, 0, 30), hl 25, .xi, .xi,
       .rho (false, 0, 2291), .rho (false, 0, 6), hl 26, .xi, .sign 587,
       .rho (false, 3588, 3246), .rho (false, 0, 987), .rho (false, 0, 60), hl 27, hl 0],
      [hl 0, .xi, .xi, .rho (false, 0, 3914), .rho (false, 0, 30), hl 25, .xi, .xi,
       .rho (false, 0, 2291), .rho (false, 0, 6), hl 26, .xi, .sign 587,
       .rho (false, 3588, 3246), .rho (false, 0, 987), .rho (false, 0, 60), hl 27, hl 0],
      [hl 0, hl 28, .xi, .sign 1613, .rho (true, 1651, 908), .rho (false, 0, 3415),
       .rho (false, 0, 60), hl 29, hl 0],
      [hl 0, hl 28, .xi, .sign 1613, .rho (true, 1651, 908), .rho (false, 0, 3415),
       .rho (false, 0, 60), hl 29, hl 0],
      [hl 0, .xi, .rho (false, 0, 3112), .rho (false, 0, 58), hl 23, .xi, .xi, .sign 256,
       .rho (true, 272, 1786), .rho (false, 0, 1471), .rho (false, 0, 2), hl 30, hl 0],
      [hl 0, .xi, .rho (false, 0, 3112), .rho (false, 0, 58), hl 23, .xi, .xi, .sign 256,
       .rho (true, 272, 1786), .rho (false, 0, 1471), .rho (false, 0, 2), hl 30, hl 0]]
  lBaby := #[0, 0, 1, 1, 1, 1, 9, 9, 1, 1]

@[expose] def sorbit2 : SOrbit where
  uHpp := #[[], []]
  uBaby := #[0, 0]
  lHpp :=
    #[[],
      [],
      [],
      [],
      [],
      [],
      [hl 0, .xi, .xi, .rho (false, 0, 3914), .rho (false, 0, 30), hl 25, .xi, .xi,
       .rho (false, 0, 2124), .rho (false, 0, 30), hl 31, .xi, .sign 31, .rho (true, 2830, 3361),
       .rho (false, 0, 300), .rho (false, 0, 40), hl 32, hl 0],
      [hl 0, .xi, .xi, .rho (false, 0, 3914), .rho (false, 0, 30), hl 25, .xi, .xi,
       .rho (false, 0, 2124), .rho (false, 0, 30), hl 31, .xi, .sign 31, .rho (true, 2830, 3361),
       .rho (false, 0, 300), .rho (false, 0, 40), hl 32, hl 0],
      [hl 0, .xi, .rho (false, 0, 3112), .rho (false, 0, 58), hl 23, .xi, .xi, .sign 1024,
       .rho (true, 1040, 2940), .rho (false, 0, 2361), .rho (false, 0, 12), hl 33, hl 0],
      [hl 0, .xi, .rho (false, 0, 3112), .rho (false, 0, 58), hl 23, .xi, .xi, .sign 256,
       .rho (false, 274, 1239), .rho (false, 0, 3607), .rho (false, 0, 12), hl 33, hl 0],
      [hl 0, .rho (false, 0, 10), hl 34, .xi, .xi, .rho (false, 0, 2681), .rho (false, 0, 10),
       hl 35, .xi, .sign 3416, .rho (true, 1584, 1553), .rho (false, 0, 3704),
       .rho (false, 0, 36), hl 36, hl 0],
      [hl 0, .rho (false, 0, 10), hl 34, .xi, .xi, .rho (false, 0, 2681), .rho (false, 0, 10),
       hl 35, .xi, .sign 3416, .rho (true, 1584, 1553), .rho (false, 0, 3704),
       .rho (false, 0, 36), hl 36, hl 0],
      [hl 0, hl 28, .xi, .sign 3638, .rho (true, 310, 2700), .rho (false, 0, 1088),
       .rho (false, 0, 14), hl 37, hl 0],
      [hl 0, hl 28, .xi, .sign 3638, .rho (true, 310, 2700), .rho (false, 0, 1088),
       .rho (false, 0, 14), hl 37, hl 0],
      [],
      [],
      [],
      []]
  lBaby := #[0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 8, 8, 8, 8, 0, 0, 0, 0]

@[expose] def sorbit3 : SOrbit where
  uHpp :=
    #[[hl 0, .rho (false, 0, 10), hl 34, .xi, .rho (false, 0, 4050), .rho (false, 0, 30), hl 38,
       .xi, .sign 2673, .rho (true, 2384, 1663), .rho (false, 0, 1314), .rho (false, 0, 48),
       hl 39, hl 0],
      [hl 0, hl 28, .xi, .sign 89, .rho (false, 1290, 643), .rho (false, 0, 104),
       .rho (false, 0, 58), hl 40, hl 0]]
  uBaby := #[8, 9]
  lHpp :=
    #[[hl 0, hl 28, .xi, .sign 2670, .rho (true, 1563, 2245), .rho (false, 0, 1346),
       .rho (false, 0, 36), hl 41, hl 0],
      [hl 0, .rho (false, 0, 947), .rho (false, 0, 20), hl 42, .xi, .xi, .rho (false, 0, 3876),
       .rho (false, 0, 6), hl 43, .xi, .sign 2378, .rho (false, 1616, 1471),
       .rho (false, 0, 709), .rho (false, 0, 60), hl 44, hl 0],
      [hl 0, .rho (false, 0, 2519), .rho (false, 0, 48), hl 45, .xi, .xi, .rho (false, 0, 831),
       .rho (false, 0, 10), hl 46, .xi, .xi, .sign 1607, .rho (true, 358, 972),
       .rho (false, 0, 4010), .rho (false, 0, 48), hl 47, hl 0],
      [hl 0, .xi, .rho (false, 0, 268), .rho (false, 0, 10), hl 48, .xi, .rho (false, 0, 679),
       .rho (false, 0, 18), hl 49, .xi, .xi, .sign 3950, .rho (false, 6, 57),
       .rho (false, 0, 3423), .rho (false, 0, 54), hl 50, hl 0],
      [hl 0, .rho (false, 0, 3257), .rho (false, 0, 34), hl 20, .xi, .xi, .rho (false, 0, 2340),
       .rho (false, 0, 6), hl 51, .xi, .xi, .sign 3875, .rho (true, 1901, 2258),
       .rho (false, 0, 1903), .rho (false, 0, 24), hl 52, hl 0],
      [hl 0, .rho (false, 0, 1767), .rho (false, 0, 48), hl 53, .xi, .sign 2829,
       .rho (false, 40, 23), .rho (false, 0, 1461), .rho (false, 0, 12), hl 54, hl 0],
      [hl 0, .rho (false, 0, 10), hl 34, .xi, .rho (false, 0, 1343), .rho (false, 0, 34), hl 55,
       .xi, .sign 317, .rho (false, 603, 624), .rho (false, 0, 2079), .rho (false, 0, 40), hl 56,
       hl 0],
      [hl 0, hl 28, .xi, .sign 2317, .rho (true, 524, 1353), .rho (false, 0, 2678),
       .rho (false, 0, 58), hl 57, hl 0],
      [hl 0, .rho (false, 0, 1380), .rho (false, 0, 54), hl 58, .xi, .xi, .rho (false, 0, 1682),
       .rho (false, 0, 30), hl 59, .xi, .xi, .sign 3160, .rho (false, 3687, 48),
       .rho (false, 0, 1585), .rho (false, 0, 18), hl 60, hl 0],
      [hl 0, .rho (false, 0, 1767), .rho (false, 0, 48), hl 53, .xi, .sign 3649,
       .rho (false, 3158, 3346), .rho (false, 0, 3729), hl 61, hl 0],
      [hl 0, hl 28, .xi, .sign 3167, .rho (false, 2852, 1157), .rho (false, 0, 1925),
       .rho (false, 0, 46), hl 62, hl 0],
      [hl 0, .rho (false, 0, 3257), .rho (false, 0, 34), hl 20, .xi, .rho (false, 0, 2314),
       .rho (false, 0, 6), hl 63, .xi, .xi, .sign 1630, .rho (true, 1908, 2560),
       .rho (false, 0, 537), .rho (false, 0, 36), hl 64, hl 0],
      [hl 0, .rho (false, 0, 3257), .rho (false, 0, 34), hl 20, .xi, .rho (false, 0, 2175),
       .rho (false, 0, 34), hl 65, .xi, .sign 3359, .rho (true, 1886, 3873),
       .rho (false, 0, 2111), .rho (false, 0, 20), hl 66, hl 0],
      [hl 0, hl 28, .xi, .xi, .sign 3083, .rho (true, 2883, 1051), .rho (false, 0, 1503),
       .rho (false, 0, 36), hl 67, hl 0],
      [hl 0, .rho (false, 0, 1767), .rho (false, 0, 48), hl 53, .xi, .xi, .rho (false, 0, 3711),
       .rho (false, 0, 34), hl 68, .xi, .xi, .sign 2645, .rho (true, 127, 57),
       .rho (false, 0, 2289), .rho (false, 0, 48), hl 69, hl 0],
      [hl 0, .rho (false, 0, 1767), .rho (false, 0, 48), hl 53, .xi, .rho (false, 0, 731),
       .rho (false, 0, 6), hl 70, .xi, .xi, .sign 828, .rho (false, 3908, 2559),
       .rho (false, 0, 2834), .rho (false, 0, 2), hl 71, hl 0],
      [hl 0, .rho (false, 0, 2519), .rho (false, 0, 48), hl 45, .xi, .rho (false, 0, 3852),
       .rho (false, 0, 6), hl 72, .xi, .xi, .sign 1321, .rho (true, 1090, 565),
       .rho (false, 0, 2696), .rho (false, 0, 30), hl 73, hl 0],
      [hl 0, hl 1, .xi, .xi, .rho (false, 0, 34), .rho (false, 0, 58), hl 74, .xi, .xi,
       .sign 2317, .rho (true, 826, 0), .rho (false, 0, 173), .rho (false, 0, 46), hl 75, hl 0],
      [hl 0, hl 28, .xi, .sign 576, .rho (false, 2687, 3967), .rho (false, 0, 1903),
       .rho (false, 0, 20), hl 76, hl 0],
      [hl 0, .rho (false, 0, 2519), .rho (false, 0, 48), hl 45, .xi, .rho (false, 0, 1682),
       .rho (false, 0, 30), hl 59, .xi, .sign 3887, .rho (true, 1065, 835),
       .rho (false, 0, 1230), .rho (false, 0, 48), hl 77, hl 0],
      [hl 0, .rho (false, 0, 268), .rho (false, 0, 10), hl 48, .xi, .rho (false, 0, 679),
       .rho (false, 0, 18), hl 49, .xi, .sign 1368, .rho (true, 1880, 1048),
       .rho (false, 0, 4031), .rho (false, 0, 26), hl 78, hl 0],
      [hl 0, .rho (false, 0, 3257), .rho (false, 0, 34), hl 20, .xi, .xi, .rho (false, 0, 2175),
       .rho (false, 0, 34), hl 65, .xi, .sign 2571, .rho (false, 3600, 174),
       .rho (false, 0, 365), .rho (false, 0, 24), hl 79, hl 0],
      [hl 0, .rho (false, 0, 10), hl 34, .xi, .rho (false, 0, 2314), .rho (false, 0, 6), hl 63,
       .xi, .sign 827, .rho (true, 374, 2181), .rho (false, 0, 3533), .rho (false, 0, 16), hl 80,
       hl 0],
      [hl 0, .rho (false, 0, 20), .rho (false, 0, 6), hl 81, .xi, .xi, .sign 3109,
       .rho (true, 3931, 1956), .rho (false, 0, 2608), .rho (false, 0, 58), hl 82, hl 0],
      [hl 0, .rho (false, 0, 2519), .rho (false, 0, 48), hl 45, .xi, .xi, .rho (false, 0, 3852),
       .rho (false, 0, 6), hl 72, .xi, .xi, .sign 110, .rho (false, 76, 2698),
       .rho (false, 0, 3672), .rho (false, 0, 40), hl 83, hl 0],
      [hl 0, .rho (false, 0, 947), .rho (false, 0, 20), hl 42, .xi, .rho (false, 0, 2314),
       .rho (false, 0, 6), hl 63, .xi, .sign 3684, .rho (true, 3947, 660), .rho (false, 0, 2466),
       .rho (false, 0, 18), hl 84, hl 0],
      [hl 0, .rho (false, 0, 2519), .rho (false, 0, 48), hl 45, .xi, .xi, .rho (false, 0, 3455),
       .rho (false, 0, 10), hl 85, .xi, .xi, .sign 2311, .rho (true, 2430, 2943),
       .rho (false, 0, 2994), .rho (false, 0, 18), hl 86, hl 0],
      [hl 0, .rho (false, 0, 10), hl 34, .xi, .rho (false, 0, 1343), .rho (false, 0, 34), hl 55,
       .xi, .xi, .sign 1640, .rho (false, 2413, 1106), .rho (false, 0, 569), .rho (false, 0, 30),
       hl 87, hl 0],
      [hl 0, hl 28, .xi, .sign 1862, .rho (false, 2143, 797), .rho (false, 0, 3098),
       .rho (false, 0, 38), hl 88, hl 0],
      [hl 0, hl 28, .xi, .sign 369, .rho (true, 3613, 1587), .rho (false, 0, 3065),
       .rho (false, 0, 18), hl 89, hl 0],
      [hl 0, hl 28, .xi, .sign 1335, .rho (false, 1329, 2697), .rho (false, 0, 2685),
       .rho (false, 0, 58), hl 90, hl 0],
      [hl 0, hl 28, .xi, .sign 3667, .rho (true, 2920, 48), .rho (false, 0, 3054),
       .rho (false, 0, 18), hl 91, hl 0]]
  lBaby :=
    #[8, 8, 8, 5, 8, 9, 8, 9, 8, 9, 8, 8, 8, 8, 8, 8, 8, 8, 9, 8, 8, 8, 8, 8, 8, 8, 8, 8, 9, 9,
      9, 9]

end CFSG.Monster.AxisCount.HS
