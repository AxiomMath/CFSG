module

public import CFSG.Monster.AxisCount.BabyBasic

public section

namespace CFSG.Monster.AxisCount.Baby

open CFSG.Monster.AxisCount.Native

@[expose] def babyOrbit0 : BabyOrbit where
  gamma := []
  U := [[bpl 0, .sign 3184, .rho (true, 3614, 1840), .rho (false, 0, 3921), .rho (false, 0, 60),
       bpl 67, .xi, .xi, .rho (false, 0, 56), bpl 68, .xi, .rho (false, 0, 58), bpl 69, bpl 0],
     [bpl 0, .sign 597, .rho (true, 2172, 929), .rho (false, 0, 1450), .rho (false, 0, 16),
       bpl 70, .xi, .rho (false, 0, 36), bpl 35, .xi, .rho (false, 0, 34), bpl 71, bpl 0],
     [bpl 0, .sign 1404, .rho (true, 3383, 1310), .rho (false, 0, 1338), .rho (false, 0, 60),
       bpl 72, .xi, .rho (false, 0, 22), bpl 50, .xi, .rho (false, 0, 14), bpl 73, .xi, bpl 0],
     [bpl 0, .sign 380, .rho (false, 2940, 1051), .rho (false, 0, 2412), .rho (false, 0, 22),
       bpl 74, .xi, .rho (false, 0, 36), bpl 49, .xi, .xi, .rho (false, 0, 40), bpl 75, bpl 0]]
  h := #[[bpl 0, .rho (false, 0, 3928), .rho (false, 0, 34), bpl 9, .xi, .xi, bpl 0]]
  kappaPlus := #[[]]
  kappaMinus := #[[bpl 0, .rho (false, 0, 62), bpl 0]]
  tPlus := #[1]
  tMinus := #[1]
  size := #[46575]
  lam := #[16445440]

@[expose] def babyOrbit1 : BabyOrbit where
  gamma := [.tau 1]
  U := [[bpl 0, .sign 2427, .rho (false, 3910, 2758), .rho (false, 0, 2698),
       .rho (false, 0, 12), bpl 76, bpl 0],
     [bpl 0, .sign 2893, .rho (false, 3961, 2758), .rho (false, 0, 3200),
       .rho (false, 0, 30), bpl 77, bpl 0],
     [bpl 0, .sign 1136, .rho (false, 1036, 655), .rho (false, 0, 743), .rho (false, 0, 62),
       bpl 78, bpl 0],
     [bpl 0, .sign 3649, .rho (true, 2351, 238), .rho (false, 0, 856), .rho (false, 0, 58),
       bpl 79, bpl 0]]
  h := #[[bpl 0, .rho (false, 0, 3928), .rho (false, 0, 34), bpl 9, .xi, .xi, bpl 0],
      [bpl 0, .sign 74, .rho (true, 3691, 3132), .rho (false, 0, 88), .rho (false, 0, 40),
       bpl 80, .xi, .xi, .rho (false, 0, 56), bpl 54, .xi, .rho (false, 0, 58), bpl 27, .xi,
       .xi, bpl 0],
      [bpl 0, .sign 64, .rho (false, 103, 1822), .rho (false, 0, 158), bpl 13, .xi, bpl 14,
       .xi, .xi, bpl 0],
      [bpl 0, .sign 1024, .rho (false, 1058, 2529), .rho (false, 0, 4065), bpl 82, .xi,
       .rho (false, 0, 58), bpl 31, .xi, .xi, bpl 0],
      []]
  kappaPlus := #[[bpl 0, .xi, .xi, bpl 0],
                [bpl 0, .rho (true, 1291, 649), .rho (false, 0, 2944), .rho (false, 0, 60),
                 bpl 81, bpl 0],
                [bpl 0, .rho (false, 1, 0), .rho (false, 0, 6), bpl 0],
                [bpl 0, .rho (false, 61, 0), .rho (false, 0, 10), bpl 66, bpl 0],
                [bpl 0, .rho (false, 0, 62), bpl 0]]
  kappaMinus := #[[bpl 0, .rho (false, 1, 0), .xi, bpl 0],
                 [bpl 0, .rho (true, 1291, 649), .rho (false, 0, 2999), .rho (false, 0, 60),
                  bpl 81, bpl 0],
                 [bpl 0, .rho (false, 1, 0), .rho (false, 0, 62), bpl 0],
                 [bpl 0, .rho (false, 61, 0), .rho (false, 0, 52), bpl 66, bpl 0],
                 []]
  tPlus := #[1, 4, 2, 3, 1]
  tMinus := #[1, 4, 2, 3, 0]
  size := #[462, 22528, 2464, 21120, 1]
  lam := #[16445440, 11247616, 20538, 3055628, 63]

@[expose] def babyOrbit2 : BabyOrbit where
  gamma := [.tau 2,
           .blk [bpl 0, .xi, .xi, bpl 14, .xi, bpl 0],
           .tau 1]
  U := [[bpl 0, .sign 3615, .rho (true, 1600, 3839), .rho (false, 0, 3469), .rho (false, 0, 24),
       bpl 83, .xi, .xi, .rho (false, 0, 40), bpl 84, bpl 0],
     [bpl 0, .sign 1025, .rho (true, 2370, 2559), .rho (false, 0, 997), .rho (false, 0, 40),
       bpl 85, .xi, .xi, .rho (false, 0, 60), bpl 12, .xi, .xi, bpl 0],
     [bpl 0, .sign 1089, .rho (false, 1087, 60), .rho (false, 0, 3868), .rho (false, 0, 30),
       bpl 86, .xi, .rho (false, 0, 12), bpl 46, bpl 0],
     [bpl 0, .sign 2109, .rho (true, 2595, 3849), .rho (false, 0, 2997), .rho (false, 0, 60),
       bpl 87, .xi, .xi, .rho (false, 0, 58), bpl 3, .xi, .xi, bpl 0]]
  h := #[[bpl 0, .rho (false, 0, 3928), .rho (false, 0, 34), bpl 9, .xi, .xi, bpl 0],
      [bpl 0, .rho (false, 0, 4008), .rho (false, 0, 6), bpl 10, .xi, .xi, bpl 0],
      [bpl 0, .rho (false, 0, 923), .rho (false, 0, 12), bpl 17, .xi, .xi, bpl 0],
      [bpl 0, .sign 74, .rho (true, 3691, 3132), .rho (false, 0, 88), .rho (false, 0, 40),
       bpl 80, .xi, .xi, .rho (false, 0, 56), bpl 54, .xi, .rho (false, 0, 58), bpl 27, .xi,
       .xi, bpl 0]]
  kappaPlus := #[[bpl 0, .rho (false, 64, 57), .rho (false, 0, 56), .xi, .xi, bpl 0],
                [bpl 0, .xi, .xi, bpl 14, .xi, bpl 0],
                [bpl 0, .sign 2601, .rho (true, 1792, 110), .rho (false, 0, 3654),
                 .rho (false, 0, 30), bpl 89, .xi, .xi, .rho (false, 0, 12), bpl 18, bpl 0],
                [bpl 0, .sign 3073, .rho (true, 523, 1093), .rho (false, 0, 1977), bpl 91,
                 bpl 0]]
  kappaMinus := #[[bpl 0, .sign 64, .rho (false, 7, 63), .rho (false, 0, 3846), bpl 88, .xi,
                  bpl 0],
                 [bpl 0, .rho (false, 0, 6), bpl 0],
                 [bpl 0, .rho (false, 3161, 1234), .rho (false, 0, 1376), .rho (false, 0, 6),
                  bpl 90, .xi, .xi, .rho (false, 0, 12), bpl 18, bpl 0],
                 [bpl 0, .sign 3073, .rho (true, 3637, 2843), .rho (false, 0, 2543), bpl 91,
                  bpl 0]]
  tPlus := #[4, 1, 3, 5]
  tMinus := #[4, 2, 3, 5]
  size := #[12096, 63, 2160, 32256]
  lam := #[16445440, 110592, 14352384, 11247616]

@[expose] def babyOrbit3 : BabyOrbit where
  gamma := [.tau 2,
           .blk [bpl 0, .xi, .xi, .rho (false, 0, 58), bpl 5, .xi, bpl 0],
           .tau 1]
  U := [[bpl 0, .sign 64, .rho (true, 1044, 855), .rho (false, 0, 4024), .rho (false, 0, 54),
       bpl 92, .xi, .rho (false, 0, 36), bpl 15, bpl 0],
     [bpl 0, .sign 1298, .rho (false, 1371, 660), .rho (false, 0, 3536), .rho (false, 0, 24),
       bpl 93, .xi, .rho (false, 0, 36), bpl 15, bpl 0],
     [bpl 0, .sign 586, .rho (false, 3639, 2606), .rho (false, 0, 113), .rho (false, 0, 48),
       bpl 94, .xi, .xi, .rho (false, 0, 12), bpl 52, bpl 0],
     [bpl 0, .sign 1100, .rho (true, 1069, 2897), .rho (false, 0, 3546), .rho (false, 0, 34),
       bpl 95, .xi, .rho (false, 0, 36), bpl 53, bpl 0]]
  h := #[[bpl 0, .rho (false, 0, 3928), .rho (false, 0, 34), bpl 9, .xi, .xi, bpl 0],
      [bpl 0, .rho (false, 0, 3684), .rho (false, 0, 10), bpl 100, .xi, .xi, bpl 0],
      [bpl 0, .rho (false, 0, 1501), .rho (false, 0, 6), bpl 101, .xi, .xi, bpl 0],
      [bpl 0, .rho (false, 0, 871), .rho (false, 0, 12), bpl 65, .xi, .xi, bpl 0],
      [bpl 0, .sign 74, .rho (true, 3691, 3132), .rho (false, 0, 88), .rho (false, 0, 40),
       bpl 80, .xi, .xi, .rho (false, 0, 56), bpl 54, .xi, .rho (false, 0, 58), bpl 27, .xi,
       .xi, bpl 0],
      [bpl 0, .sign 98, .rho (true, 1395, 2108), .rho (false, 0, 104), .rho (false, 0, 48),
       bpl 106, .xi, .xi, .rho (false, 0, 56), bpl 54, .xi, .rho (false, 0, 58), bpl 27, .xi,
       .xi, bpl 0]]
  kappaPlus := #[[bpl 0, .sign 2083, .rho (true, 623, 3115), .rho (false, 0, 1424),
                 .rho (false, 0, 34), bpl 96, .xi, .xi, .rho (false, 0, 20), bpl 97, bpl 0],
                [bpl 0, .rho (true, 1145, 2572), .rho (false, 0, 8), .xi, .xi,
                 .rho (false, 0, 58), bpl 3, bpl 0],
                [bpl 0, .sign 59, .rho (true, 1140, 650), .rho (false, 0, 308),
                 .rho (false, 0, 20), bpl 102, .xi, .xi, .rho (false, 0, 12), bpl 18, bpl 0],
                [bpl 0, .rho (true, 10, 53), .rho (false, 0, 3839), bpl 104, .xi, .xi,
                 .rho (false, 0, 58), bpl 31, .xi, .xi, bpl 0],
                [bpl 0, .sign 1311, .rho (false, 1047, 875), .rho (false, 0, 3134),
                 .rho (false, 0, 6), bpl 105, .xi, .xi, bpl 0],
                [bpl 0, .sign 3853, .rho (true, 3685, 296), .rho (false, 0, 609),
                 .rho (false, 0, 54), bpl 107, bpl 0]]
  kappaMinus := #[[bpl 0, .sign 3340, .rho (false, 3856, 1590), .rho (false, 0, 409),
                  .rho (false, 0, 48), bpl 98, .xi, .xi, .rho (false, 0, 36), bpl 99, bpl 0],
                 [bpl 0, .rho (true, 1149, 565), .rho (false, 0, 2048), .xi,
                  .rho (false, 0, 58), bpl 3, bpl 0],
                 [bpl 0, .sign 1838, .rho (false, 2100, 1347), .rho (false, 0, 748),
                  .rho (false, 0, 40), bpl 103, .xi, .xi, .rho (false, 0, 12), bpl 18, bpl 0],
                 [bpl 0, .rho (false, 46, 46), .rho (false, 0, 60), bpl 16, bpl 0],
                 [bpl 0, .sign 1311, .rho (true, 311, 2746), .rho (false, 0, 740),
                  .rho (false, 0, 6), bpl 105, .xi, .xi, bpl 0],
                 [bpl 0, .sign 3853, .rho (false, 343, 484), .rho (false, 0, 3801),
                  .rho (false, 0, 54), bpl 107, bpl 0]]
  tPlus := #[3, 4, 3, 1, 5, 6]
  tMinus := #[3, 4, 2, 3, 5, 6]
  size := #[840, 3360, 120, 15, 26880, 15360]
  lam := #[16445440, 7200768, 6725632, 1941504, 11247616, 7774208]

@[expose] def babyOrbit4 : BabyOrbit where
  gamma := [.tau 2,
           .blk [bpl 0, .xi, .xi, bpl 8, .xi, .rho (false, 0, 58), bpl 3, .xi, bpl 0],
           .tau 1]
  U := [[bpl 0, .sign 3191, .rho (false, 0, 3967), .rho (false, 0, 58), bpl 108, bpl 0],
     [bpl 0, .sign 1329, .rho (true, 63, 0), .rho (false, 0, 1660), .rho (false, 0, 48),
       bpl 109, bpl 0],
     [bpl 0, .sign 1583, .rho (true, 63, 0), .rho (false, 0, 2536), .rho (false, 0, 40),
       bpl 110, bpl 0],
     [bpl 0, .sign 1659, .rho (true, 63, 0), .rho (false, 0, 1761), .rho (false, 0, 58),
       bpl 111, bpl 0]]
  h := #[[bpl 0, .rho (false, 0, 3928), .rho (false, 0, 34), bpl 9, .xi, .xi, bpl 0],
      [bpl 0, .rho (false, 0, 861), .rho (false, 0, 20), bpl 113, .xi, .xi, bpl 0],
      [bpl 0, .sign 74, .rho (true, 3691, 3132), .rho (false, 0, 88), .rho (false, 0, 40),
       bpl 80, .xi, .xi, .rho (false, 0, 56), bpl 54, .xi, .rho (false, 0, 58), bpl 27, .xi,
       .xi, bpl 0],
      [bpl 0, .sign 70, .rho (true, 23, 23), .rho (false, 0, 646), .rho (false, 0, 6), bpl 28,
       .xi, .xi, bpl 8, .xi, .xi, bpl 14, .xi, bpl 0],
      [bpl 0, .sign 64, .rho (false, 103, 1822), .rho (false, 0, 158), bpl 13, .xi, bpl 14,
       .xi, .xi, bpl 0],
      [bpl 0, .sign 1024, .rho (false, 1058, 2529), .rho (false, 0, 4065), bpl 82, .xi,
       .rho (false, 0, 58), bpl 31, .xi, .xi, bpl 0],
      [bpl 0, .sign 290, .rho (false, 1353, 185), .rho (false, 0, 1441), .rho (false, 0, 20),
       bpl 24, .xi, .xi, bpl 14, .xi, .xi, bpl 0],
      [bpl 0, .sign 2904, .rho (false, 1398, 185), .rho (false, 0, 3340), .rho (false, 0, 40),
       bpl 118, .xi, .xi, .rho (false, 0, 58), bpl 31, .xi, .xi, bpl 0],
      []]
  kappaPlus := #[[bpl 0, .sign 70, .rho (false, 9, 54), .rho (false, 0, 185),
                 .rho (false, 0, 6), bpl 112, .xi, .xi, bpl 8, bpl 0],
                [bpl 0, .sign 121, .rho (true, 63, 0), .rho (false, 0, 57),
                 .rho (false, 0, 6), bpl 28, .xi, .xi, bpl 8, bpl 0],
                [bpl 0, .sign 1646, .rho (false, 1332, 649), .rho (false, 0, 1367),
                 .rho (false, 0, 12), bpl 114, bpl 0],
                [bpl 0, .rho (true, 124, 133), .rho (false, 0, 2867), .rho (false, 0, 6),
                 bpl 28, bpl 0],
                [bpl 0, .sign 64, .rho (false, 65, 185), .rho (false, 0, 3513), bpl 88, .xi,
                 bpl 14, .xi, .xi, bpl 0],
                [bpl 0, .sign 775, .rho (false, 1060, 487), .rho (false, 0, 3979),
                 .rho (false, 0, 60), bpl 115, .xi, .xi, .rho (false, 0, 12), bpl 18, bpl 0],
                [bpl 0, .rho (false, 1097, 643), .rho (false, 0, 3721), .rho (false, 0, 6),
                 bpl 10, .xi, .xi, bpl 14, .xi, .xi, bpl 0],
                [bpl 0, .sign 1045, .rho (false, 1345, 2575), .rho (false, 0, 830),
                 .rho (false, 0, 48), bpl 119, .xi, .rho (false, 0, 12), bpl 18, bpl 0],
                [bpl 0, .rho (false, 0, 62), bpl 0]]
  kappaMinus := #[[bpl 0, .rho (true, 6, 57), .rho (false, 0, 59), .xi, .rho (false, 0, 58),
                  bpl 3, bpl 0],
                 [bpl 0, .rho (false, 0, 62), .xi, bpl 0],
                 [bpl 0, .sign 1566, .rho (false, 789, 2885), .rho (false, 0, 2318),
                  .rho (false, 0, 12), bpl 114, bpl 0],
                 [bpl 0, .sign 112, .rho (false, 51, 51), .rho (false, 0, 306),
                  .rho (false, 0, 6), bpl 28, bpl 0],
                 [bpl 0, .rho (true, 3178, 3474), .rho (false, 0, 3088), .xi, .xi, bpl 14,
                  .xi, bpl 0],
                 [bpl 0, .sign 2642, .rho (true, 3445, 1162), .rho (false, 0, 2276), bpl 116,
                  .xi, .xi, .rho (false, 0, 40), bpl 11, bpl 0],
                 [bpl 0, .sign 118, .rho (false, 42, 63), .rho (false, 0, 2414),
                  .rho (false, 0, 10), bpl 117, .xi, .xi, bpl 14, .xi, bpl 0],
                 [bpl 0, .sign 1059, .rho (true, 290, 3175), .rho (false, 0, 3867),
                  .rho (false, 0, 60), bpl 120, .xi, .rho (false, 0, 12), bpl 18, bpl 0],
                 [bpl 0, .sign 70, .rho (false, 111, 3513), .rho (false, 0, 3887),
                  .rho (false, 0, 6), bpl 28, .xi, .xi, bpl 8, .xi, .xi, bpl 14, .xi, bpl 0]]
  tPlus := #[3, 2, 8, 7, 4, 5, 5, 6, 4]
  tMinus := #[4, 4, 8, 7, 4, 5, 5, 6, 1]
  size := #[420, 42, 21504, 1024, 672, 13440, 1792, 7680, 1]
  lam := #[16445440, 11264000, 11247616, 28672, 20538, 3055628, 4198521, 4841551, 63]

@[expose] def babyOrbit5 : BabyOrbit where
  gamma := [.tau 2,
           .blk [bpl 0, .xi, .rho (false, 0, 12), bpl 34, .xi, .xi, .rho (false, 0, 12),
                  bpl 52, bpl 0],
           .tau 1,
           .blk [bpl 0, .xi, .rho (false, 0, 20), bpl 1, .xi, bpl 0],
           .tau 1]
  U := [[bpl 0, .sign 2341, .rho (false, 40, 23), .rho (false, 0, 2013), .rho (false, 0, 18),
       bpl 121, bpl 0],
     [bpl 0, .sign 3904, .rho (true, 3095, 427), .rho (false, 0, 3092), .rho (false, 0, 58),
       bpl 122, bpl 0],
     [bpl 0, .sign 1877, .rho (true, 39, 39), .rho (false, 0, 3215), .rho (false, 0, 46),
       bpl 123, bpl 0],
     [bpl 0, .sign 321, .rho (true, 2060, 335), .rho (false, 0, 1812), .rho (false, 0, 30),
       bpl 124, bpl 0]]
  h := #[[bpl 0, .rho (false, 0, 3928), .rho (false, 0, 34), bpl 9, .xi, .xi, bpl 0],
      [bpl 0, .rho (false, 0, 4008), .rho (false, 0, 6), bpl 10, .xi, .xi, bpl 0],
      [bpl 0, .rho (false, 0, 923), .rho (false, 0, 12), bpl 17, .xi, .xi, bpl 0],
      [bpl 0, .sign 74, .rho (true, 3691, 3132), .rho (false, 0, 88), .rho (false, 0, 40),
       bpl 80, .xi, .xi, .rho (false, 0, 56), bpl 54, .xi, .rho (false, 0, 58), bpl 27, .xi,
       .xi, bpl 0],
      [bpl 0, .sign 70, .rho (true, 23, 23), .rho (false, 0, 646), .rho (false, 0, 6), bpl 28,
       .xi, .xi, bpl 8, .xi, .xi, bpl 14, .xi, bpl 0],
      [bpl 0, .sign 64, .rho (false, 103, 1822), .rho (false, 0, 158), bpl 13, .xi, bpl 14,
       .xi, .xi, bpl 0],
      [bpl 0, .sign 1024, .rho (false, 1058, 2529), .rho (false, 0, 4065), bpl 82, .xi,
       .rho (false, 0, 58), bpl 31, .xi, .xi, bpl 0],
      [bpl 0, .sign 768, .rho (false, 780, 4041), .rho (false, 0, 2505), bpl 139, .xi,
       .rho (false, 0, 58), bpl 31, .xi, .xi, bpl 0],
      [bpl 0, .sign 64, .rho (false, 87, 3374), .rho (false, 0, 174), bpl 88, .xi, bpl 14,
       .xi, .xi, bpl 0],
      [bpl 0, .sign 1332, .rho (false, 0, 3876), .rho (false, 0, 58), bpl 58, .xi, .xi,
       .rho (false, 0, 58), bpl 31, .xi, .xi, bpl 0],
      [bpl 0, .sign 290, .rho (false, 1353, 185), .rho (false, 0, 1441), .rho (false, 0, 20),
       bpl 24, .xi, .xi, bpl 14, .xi, .xi, bpl 0],
      []]
  kappaPlus := #[[bpl 0, .sign 3073, .rho (true, 126, 185), .rho (false, 0, 812),
                 .rho (false, 0, 40), bpl 125, .xi, bpl 8, bpl 0],
                [bpl 0, .sign 826, .rho (true, 819, 4041), .rho (false, 0, 3147),
                 .rho (false, 0, 58), bpl 127, .xi, .xi, .rho (false, 0, 58), bpl 33, .xi,
                 .rho (false, 0, 12), bpl 18, bpl 0],
                [bpl 0, .sign 314, .rho (true, 3610, 2833), .rho (false, 0, 2092),
                 .rho (false, 0, 58), bpl 128, .xi, .xi, .rho (false, 0, 58), bpl 31, .xi,
                 bpl 0],
                [bpl 0, .sign 3898, .rho (true, 1317, 3849), .rho (false, 0, 530), bpl 130,
                 bpl 0],
                [bpl 0, .sign 124, .rho (true, 117, 2700), .rho (false, 0, 3656),
                 .rho (false, 0, 58), bpl 131, .xi, .rho (false, 0, 58), bpl 2, bpl 0],
                [bpl 0, .sign 2096, .rho (false, 3106, 3681), .rho (false, 0, 3224),
                 .rho (false, 0, 10), bpl 133, .xi, bpl 8, bpl 0],
                [bpl 0, .sign 2892, .rho (false, 3356, 609), .rho (false, 0, 2494),
                 .rho (false, 0, 48), bpl 135, .xi, .xi, bpl 136, bpl 0],
                [bpl 0, .sign 3900, .rho (true, 1296, 3382), .rho (false, 0, 1219), .xi,
                 .rho (false, 0, 58), bpl 31, .xi, .xi, bpl 0],
                [bpl 0, .sign 1, .rho (false, 1025, 60), .rho (false, 0, 502),
                 .rho (false, 0, 6), bpl 10, .xi, .xi, bpl 14, .xi, bpl 0],
                [bpl 0, .sign 3684, .rho (true, 2372, 4095), .rho (false, 0, 3901),
                 .rho (false, 0, 60), bpl 141, .xi, .xi, .rho (false, 0, 12), bpl 18, bpl 0],
                [bpl 0, .sign 267, .rho (false, 10, 53), .rho (false, 0, 1363),
                 .rho (false, 0, 34), bpl 143, .xi, .xi, bpl 14, bpl 0],
                [bpl 0, .rho (false, 0, 59), bpl 0]]
  kappaMinus := #[[bpl 0, .sign 513, .rho (false, 3686, 168), .rho (false, 0, 2718),
                  .rho (false, 0, 60), bpl 126, .xi, .xi, bpl 8, bpl 0],
                 [bpl 0, .rho (true, 63, 0), .rho (false, 0, 3076), .xi, bpl 0],
                 [bpl 0, .sign 2678, .rho (false, 283, 3681), .rho (false, 0, 80),
                  .rho (false, 0, 36), bpl 129, .xi, .rho (false, 0, 12), bpl 18, bpl 0],
                 [bpl 0, .sign 369, .rho (false, 1108, 3294), .rho (false, 0, 305), bpl 130,
                  bpl 0],
                 [bpl 0, .rho (true, 117, 2700), .rho (false, 0, 3190), .rho (false, 0, 58),
                  bpl 132, .xi, .rho (false, 0, 58), bpl 2, bpl 0],
                 [bpl 0, .sign 2072, .rho (true, 3362, 579), .rho (false, 0, 2778), bpl 134,
                  .xi, .xi, .rho (false, 0, 58), bpl 2, bpl 0],
                 [bpl 0, .sign 634, .rho (true, 1877, 832), .rho (false, 0, 952),
                  .rho (false, 0, 40), bpl 137, .xi, .rho (false, 0, 36), bpl 138, .xi, bpl 0],
                 [bpl 0, .sign 61, .rho (false, 2571, 329), .rho (false, 0, 719), bpl 140,
                  .xi, .rho (false, 0, 58), bpl 31, .xi, .xi, bpl 0],
                 [bpl 0, .sign 1142, .rho (false, 2098, 323), .rho (false, 0, 1190),
                  .rho (false, 0, 6), bpl 28, .xi, .xi, bpl 8, .xi, .xi, .rho (false, 0, 58),
                  bpl 3, bpl 0],
                 [bpl 0, .sign 101, .rho (true, 3107, 3651), .rho (false, 0, 1006),
                  .rho (false, 0, 24), bpl 142, .xi, .xi, .rho (false, 0, 12), bpl 18, bpl 0],
                 [bpl 0, .sign 1291, .rho (true, 3435, 916), .rho (false, 0, 3061),
                  .rho (false, 0, 46), bpl 144, .xi, bpl 14, bpl 0],
                 [bpl 0, .sign 826, .rho (true, 32, 0), .rho (false, 0, 2496),
                  .rho (false, 0, 58), bpl 145, .xi, .xi, .rho (false, 0, 58), bpl 42, .xi,
                  .xi, .rho (false, 0, 12), bpl 18, bpl 0]]
  tPlus := #[5, 3, 4, 9, 8, 6, 6, 5, 5, 8, 7, 5]
  tMinus := #[5, 5, 5, 9, 8, 6, 5, 5, 4, 8, 8, 2]
  size := #[192, 30, 240, 16384, 6144, 1920, 1920, 3840, 32, 15360, 512, 1]
  lam := #[16445440, 110592, 14352384, 11247616, 28672, 20538, 3055628, 1789986, 20540, 9744664,
        4198521, 63]

@[expose] def babyOrbit6 : BabyOrbit where
  gamma := [.tau 2,
           .blk [bpl 0, .xi, .xi, .rho (false, 0, 58), bpl 33, .xi, .rho (false, 0, 36),
                  bpl 59, bpl 0],
           .tau 1,
           .blk [bpl 0, .xi, .xi, .rho (false, 0, 38), bpl 60, .xi, bpl 0],
           .tau 1]
  U := [[bpl 0, .sign 2083, .rho (true, 350, 365), .rho (false, 0, 2922), .rho (false, 0, 18),
       bpl 146, .xi, .rho (false, 0, 40), bpl 19, bpl 0],
     [bpl 0, .sign 1326, .rho (true, 104, 3374), .rho (false, 0, 3670), bpl 147, .xi, .xi,
       .rho (false, 0, 12), bpl 52, bpl 0],
     [bpl 0, .sign 549, .rho (false, 2146, 768), .rho (false, 0, 2433), .rho (false, 0, 6),
       bpl 148, .xi, .rho (false, 0, 36), bpl 53, bpl 0],
     [bpl 0, .sign 2102, .rho (false, 3692, 424), .rho (false, 0, 3744), .rho (false, 0, 54),
       bpl 149, .xi, .xi, .rho (false, 0, 12), bpl 52, bpl 0]]
  h := #[[bpl 0, .rho (false, 0, 3928), .rho (false, 0, 34), bpl 9, .xi, .xi, bpl 0],
      [bpl 0, .rho (false, 0, 3684), .rho (false, 0, 10), bpl 100, .xi, .xi, bpl 0],
      [bpl 0, .rho (false, 0, 1501), .rho (false, 0, 6), bpl 101, .xi, .xi, bpl 0],
      [bpl 0, .rho (false, 0, 871), .rho (false, 0, 12), bpl 65, .xi, .xi, bpl 0],
      [bpl 0, .sign 74, .rho (true, 3691, 3132), .rho (false, 0, 88), .rho (false, 0, 40),
       bpl 80, .xi, .xi, .rho (false, 0, 56), bpl 54, .xi, .rho (false, 0, 58), bpl 27, .xi,
       .xi, bpl 0],
      [bpl 0, .sign 98, .rho (true, 1395, 2108), .rho (false, 0, 104), .rho (false, 0, 48),
       bpl 106, .xi, .xi, .rho (false, 0, 56), bpl 54, .xi, .rho (false, 0, 58), bpl 27, .xi,
       .xi, bpl 0]]
  kappaPlus := #[[bpl 0, .sign 1792, .rho (true, 2659, 1792), .rho (false, 0, 455),
                 .rho (false, 0, 10), bpl 150, .xi, .rho (false, 0, 20), bpl 151, .xi, bpl 0],
                [bpl 0, .sign 110, .rho (false, 3607, 3513), .rho (false, 0, 1055),
                 .rho (false, 0, 54), bpl 153, .xi, .xi, .rho (false, 0, 58), bpl 2, bpl 0],
                [bpl 0, .sign 1059, .rho (false, 3850, 963), .rho (false, 0, 3379),
                 .rho (false, 0, 60), bpl 120, .xi, .rho (false, 0, 12), bpl 18, bpl 0],
                [bpl 0, .sign 3154, .rho (true, 615, 972), .rho (false, 0, 3932),
                 .rho (false, 0, 12), bpl 154, .xi, .xi, .rho (false, 0, 58), bpl 42, .xi,
                 .rho (false, 0, 60), bpl 155, bpl 0],
                [bpl 0, .sign 3590, .rho (true, 1396, 688), .rho (false, 0, 3628),
                 .rho (false, 0, 20), bpl 157, .xi, bpl 8, bpl 0],
                [bpl 0, .sign 3841, .rho (false, 1374, 2577), .rho (false, 0, 1147),
                 .rho (false, 0, 30), bpl 159, .xi, .xi, .rho (false, 0, 40), bpl 19, bpl 0]]
  kappaMinus := #[[bpl 0, .sign 2103, .rho (true, 339, 460), .rho (false, 0, 3958),
                  .rho (false, 0, 24), bpl 152, .xi, .xi, .rho (false, 0, 36), bpl 138, .xi,
                  .xi, bpl 0],
                 [bpl 0, .sign 2109, .rho (false, 2081, 1954), .rho (false, 0, 1893),
                  .rho (false, 0, 60), bpl 20, .xi, .xi, bpl 8, .xi, .xi, bpl 0],
                 [bpl 0, .sign 3898, .rho (true, 3706, 301), .rho (false, 0, 2648),
                  .rho (false, 0, 58), bpl 132, .xi, .rho (false, 0, 58), bpl 31, .xi,
                  .rho (false, 0, 58), bpl 3, bpl 0],
                 [bpl 0, .sign 3644, .rho (false, 326, 2570), .rho (false, 0, 319),
                  .rho (false, 0, 46), bpl 156, bpl 0],
                 [bpl 0, .sign 1893, .rho (false, 3089, 3474), .rho (false, 0, 1758),
                  .rho (false, 0, 20), bpl 158, .xi, bpl 8, bpl 0],
                 [bpl 0, .sign 3605, .rho (false, 2110, 60), .rho (false, 0, 57),
                  .rho (false, 0, 58), bpl 160, .xi, .xi, bpl 0]]
  tPlus := #[5, 6, 6, 3, 8, 9]
  tMinus := #[5, 5, 4, 6, 8, 9]
  size := #[840, 3360, 120, 15, 26880, 15360]
  lam := #[16445440, 7200768, 6725632, 1941504, 11247616, 7774208]

@[expose] def babyOrbit7 : BabyOrbit where
  gamma := [.tau 2,
           .blk [bpl 0, .xi, bpl 23, .xi, .rho (false, 0, 60), bpl 47, .xi, .xi, bpl 0],
           .tau 1,
           .blk [bpl 0, .xi, .rho (false, 0, 58), bpl 2, .xi, .rho (false, 0, 58), bpl 3,
                  .xi, bpl 0],
           .tau 1]
  U := [[bpl 0, .sign 59, .rho (false, 870, 1828), .rho (false, 0, 1788), .rho (false, 0, 36),
       bpl 161, .xi, .rho (false, 0, 20), bpl 162, .xi, .rho (false, 0, 60), bpl 22, .xi,
       bpl 0],
     [bpl 0, .sign 3177, .rho (false, 3398, 1862), .rho (false, 0, 2108),
       .rho (false, 0, 54), bpl 163, .xi, .xi, .rho (false, 0, 6), bpl 51, .xi, .xi,
       .rho (false, 0, 60), bpl 22, .xi, bpl 0],
     [bpl 0, .sign 2672, .rho (false, 3644, 402), .rho (false, 0, 3581), .rho (false, 0, 46),
       bpl 164, .xi, .rho (false, 0, 36), bpl 165, .xi, .xi, bpl 0],
     [bpl 0, .sign 303, .rho (false, 2336, 2350), .rho (false, 0, 1880), .rho (false, 0, 36),
       bpl 166, .xi, .rho (false, 0, 6), bpl 167, .xi, .xi, .rho (false, 0, 58), bpl 3, .xi,
       .xi, bpl 0]]
  h := #[[bpl 0, .rho (false, 0, 3928), .rho (false, 0, 34), bpl 9, .xi, .xi, bpl 0],
      [bpl 0, .rho (false, 0, 923), .rho (false, 0, 12), bpl 17, .xi, .xi, bpl 0],
      [bpl 0, .sign 290, .rho (false, 1353, 185), .rho (false, 0, 1441), .rho (false, 0, 20),
       bpl 24, .xi, .xi, bpl 14, .xi, .xi, bpl 0]]
  kappaPlus := #[[bpl 0, .sign 1031, .rho (true, 2073, 899), .rho (false, 0, 1214),
                 .rho (false, 0, 6), bpl 112, .xi, .rho (false, 0, 58), bpl 2, .xi, .xi,
                 bpl 14, .xi, .xi, bpl 0],
                [bpl 0, .sign 3197, .rho (false, 2419, 2700), .rho (false, 0, 1766),
                 .rho (false, 0, 54), bpl 168, .xi, .rho (false, 0, 6), bpl 51, .xi, .xi,
                 .rho (false, 0, 12), bpl 18, bpl 0],
                [bpl 0, .sign 3072, .rho (true, 1060, 487), .rho (false, 0, 1349),
                 .rho (false, 0, 60), bpl 25, .xi, bpl 8, bpl 0]]
  kappaMinus := #[[bpl 0, .sign 3166, .rho (true, 51, 51), .rho (false, 0, 1812), bpl 0],
                 [bpl 0, .sign 58, .rho (false, 613, 724), .rho (false, 0, 2003),
                  .rho (false, 0, 20), bpl 169, .xi, .xi, bpl 14, bpl 0],
                 [bpl 0, .sign 823, .rho (false, 2119, 1954), .rho (false, 0, 1632),
                  .rho (false, 0, 24), bpl 26, .xi, bpl 8, bpl 0]]
  tPlus := #[4, 5, 9]
  tMinus := #[7, 8, 9]
  size := #[891, 24948, 20736]
  lam := #[16445440, 14352384, 4198521]

@[expose] def babyOrbit8 : BabyOrbit where
  gamma := [.tau 1,
           .blk [bpl 0, .xi, .rho (false, 0, 6), bpl 61, .xi, .xi, .rho (false, 0, 60),
                  bpl 12, .xi, .xi, bpl 0],
           .tau 2,
           .blk [bpl 0, .xi, .rho (false, 0, 58), bpl 2, .xi, .rho (false, 0, 58), bpl 3,
                  .xi, bpl 0],
           .tau 1]
  U := [[bpl 0, .sign 3614, .rho (true, 63, 0), .rho (false, 0, 3702), .rho (false, 0, 58),
       bpl 170, bpl 0],
     [bpl 0, .sign 3173, .rho (true, 1909, 2698), .rho (false, 0, 3509), .rho (false, 0, 46),
       bpl 171, .xi, .rho (false, 0, 60), bpl 47, .xi, .xi, bpl 0],
     [bpl 0, .sign 1911, .rho (false, 862, 1157), .rho (false, 0, 759), .rho (false, 0, 6),
       bpl 172, .xi, .xi, .rho (false, 0, 60), bpl 47, bpl 0],
     [bpl 0, .sign 3403, .rho (false, 615, 972), .rho (false, 0, 3567), .rho (false, 0, 6),
       bpl 173, .xi, .xi, .rho (false, 0, 60), bpl 12, .xi, .xi, bpl 0]]
  h := #[[bpl 0, .rho (false, 0, 3928), .rho (false, 0, 34), bpl 9, .xi, .xi, bpl 0],
      [bpl 0, .rho (false, 0, 4008), .rho (false, 0, 6), bpl 10, .xi, .xi, bpl 0],
      [bpl 0, .rho (false, 0, 923), .rho (false, 0, 12), bpl 17, .xi, .xi, bpl 0],
      [bpl 0, .rho (false, 0, 2291), .rho (false, 0, 6), bpl 64, .xi, .xi, bpl 0],
      [bpl 0, .rho (false, 0, 1511), .rho (false, 0, 40), bpl 180, .xi, .xi, bpl 0],
      [bpl 0, .sign 74, .rho (true, 3691, 3132), .rho (false, 0, 88), .rho (false, 0, 40),
       bpl 80, .xi, .xi, .rho (false, 0, 56), bpl 54, .xi, .rho (false, 0, 58), bpl 27, .xi,
       .xi, bpl 0],
      [bpl 0, .sign 290, .rho (false, 1353, 185), .rho (false, 0, 1441), .rho (false, 0, 20),
       bpl 24, .xi, .xi, bpl 14, .xi, .xi, bpl 0],
      [bpl 0, .rho (false, 3072, 60), .rho (false, 0, 3732), .rho (false, 0, 6), bpl 28, .xi,
       .xi, bpl 8, .xi, bpl 14, .xi, .xi, bpl 0]]
  kappaPlus := #[[bpl 0, .sign 70, .rho (false, 1331, 2181), .rho (false, 0, 458), bpl 21, .xi,
                 .xi, bpl 8, .xi, bpl 14, .xi, bpl 0],
                [bpl 0, .sign 3093, .rho (true, 1087, 60), .rho (false, 0, 2048),
                 .rho (false, 0, 6), bpl 175, .xi, .rho (false, 0, 58), bpl 2, .xi,
                 .rho (false, 0, 58), bpl 3, .xi, .xi, bpl 0],
                [bpl 0, .sign 3859, .rho (false, 637, 3371), .rho (false, 0, 2181), bpl 176,
                 .xi, .rho (false, 0, 58), bpl 33, .xi, .rho (false, 0, 12), bpl 18, bpl 0],
                [bpl 0, .sign 82, .rho (false, 3692, 424), .rho (false, 0, 3901),
                 .rho (false, 0, 30), bpl 178, .xi, .xi, .rho (false, 0, 6), bpl 51, .xi, .xi,
                 .rho (false, 0, 12), bpl 18, bpl 0],
                [bpl 0, .sign 1851, .rho (false, 1582, 1584), .rho (false, 0, 270),
                 .rho (false, 0, 36), bpl 38, .xi, bpl 23, .xi, .rho (false, 0, 12), bpl 18,
                 bpl 0],
                [bpl 0, .sign 1810, .rho (false, 3706, 301), .rho (false, 0, 3426),
                 .rho (false, 0, 48), bpl 181, .xi, .rho (false, 0, 36), bpl 53, bpl 0],
                [bpl 0, .sign 1916, .rho (true, 2855, 1977), .rho (false, 0, 3070),
                 .rho (false, 0, 18), bpl 183, .xi, .rho (false, 0, 22), bpl 55, .xi,
                 .rho (false, 0, 12), bpl 18, bpl 0],
                [bpl 0, .sign 3584, .rho (true, 2613, 323), .rho (false, 0, 2142),
                 .rho (false, 0, 54), bpl 29, .xi, .xi, bpl 8, bpl 0]]
  kappaMinus := #[[bpl 0, .sign 1328, .rho (false, 53, 53), .rho (false, 0, 1853),
                  .rho (false, 0, 54), bpl 174, .xi, .rho (false, 0, 58), bpl 2, bpl 0],
                 [bpl 0, .sign 2172, .rho (true, 43, 43), .rho (false, 0, 3362), bpl 0],
                 [bpl 0, .sign 2124, .rho (true, 1111, 3170), .rho (false, 0, 2857),
                  .rho (false, 0, 54), bpl 177, .xi, .rho (false, 0, 12), bpl 18, bpl 0],
                 [bpl 0, .sign 59, .rho (false, 1355, 688), .rho (false, 0, 2619),
                  .rho (false, 0, 48), bpl 179, .xi, .xi, bpl 8, bpl 0],
                 [bpl 0, .sign 267, .rho (true, 2153, 3170), .rho (false, 0, 3000),
                  .rho (false, 0, 34), bpl 143, .xi, .xi, bpl 14, bpl 0],
                 [bpl 0, .sign 2088, .rho (true, 1662, 3711), .rho (false, 0, 2473),
                  .rho (false, 0, 24), bpl 182, .xi, .xi, .rho (false, 0, 12), bpl 36, .xi,
                  .rho (false, 0, 20), bpl 43, bpl 0],
                 [bpl 0, .sign 866, .rho (false, 882, 484), .rho (false, 0, 3051),
                  .rho (false, 0, 58), bpl 184, .xi, .xi, .rho (false, 0, 12), bpl 4, .xi,
                  .rho (false, 0, 12), bpl 18, bpl 0],
                 [bpl 0, .sign 3649, .rho (false, 2615, 118), .rho (false, 0, 2625),
                  .rho (false, 0, 10), bpl 30, .xi, .xi, bpl 8, bpl 0]]
  tPlus := #[5, 4, 5, 6, 5, 9, 8, 9]
  tMinus := #[8, 8, 8, 8, 7, 8, 8, 9]
  size := #[864, 27, 2160, 4320, 36, 18432, 13824, 6912]
  lam := #[16445440, 110592, 14352384, 13873152, 376832, 11247616, 4198521, 606329]

@[expose] def babyOrbit9 : BabyOrbit where
  gamma := [.tau 1,
           .blk [bpl 0, .xi, .rho (false, 0, 58), bpl 62, .xi, .rho (false, 0, 18), bpl 63,
                  .xi, bpl 0],
           .tau 2,
           .blk [bpl 0, .xi, .xi, .rho (false, 0, 56), bpl 6, .xi, .rho (false, 0, 10),
                  bpl 7, .xi, bpl 0],
           .tau 2,
           .blk [bpl 0, .xi, .xi, bpl 8, .xi, .xi, bpl 0],
           .tau 1,
           .blk [bpl 0, .xi, .rho (false, 0, 58), bpl 2, bpl 0]]
  U := [[bpl 0, .sign 3352, .rho (true, 3180, 402), .rho (false, 0, 1973), .rho (false, 0, 2),
       bpl 185, .xi, .xi, .rho (false, 0, 58), bpl 42, .xi, .rho (false, 0, 24), bpl 186,
       bpl 0],
     [bpl 0, .sign 1832, .rho (true, 259, 518), .rho (false, 0, 3889), .rho (false, 0, 44),
       bpl 187, .xi, .xi, .rho (false, 0, 36), bpl 49, .xi, .xi, .rho (false, 0, 10), bpl 188,
       bpl 0],
     [bpl 0, .sign 1344, .rho (true, 3584, 174), .rho (false, 0, 123), .rho (false, 0, 48),
       bpl 189, .xi, .xi, .rho (false, 0, 58), bpl 190, .xi, .rho (false, 0, 24), bpl 48,
       bpl 0],
     [bpl 0, .sign 344, .rho (true, 3847, 4041), .rho (false, 0, 3033), .rho (false, 0, 2),
       bpl 191, .xi, .xi, .rho (false, 0, 58), bpl 33, .xi, .xi, .rho (false, 0, 10), bpl 192,
       bpl 0]]
  h := #[[bpl 0, .rho (false, 0, 3928), .rho (false, 0, 34), bpl 9, .xi, .xi, bpl 0],
      [bpl 0, .rho (false, 0, 3992), .rho (false, 0, 6), bpl 32, .xi, .xi, bpl 0],
      [bpl 0, .rho (false, 0, 4008), .rho (false, 0, 6), bpl 10, .xi, .xi, bpl 0],
      [bpl 0, .rho (false, 0, 2314), .rho (false, 0, 6), bpl 41, .xi, .xi, bpl 0],
      [bpl 0, .rho (false, 0, 1378), .rho (false, 0, 54), bpl 44, .xi, .xi, bpl 0]]
  kappaPlus := #[[bpl 0, .sign 3630, .rho (true, 1662, 3711), .rho (false, 0, 2625),
                 .rho (false, 0, 48), bpl 37, .xi, .xi, bpl 8, bpl 0],
                [bpl 0, .sign 827, .rho (false, 116, 2566), .rho (false, 0, 4069),
                 .rho (false, 0, 36), bpl 38, .xi, bpl 8, bpl 0],
                [bpl 0, .rho (false, 1026, 60), .rho (false, 0, 3246), .rho (false, 0, 6),
                 bpl 194, .xi, .xi, .rho (false, 0, 58), bpl 33, .xi, .xi,
                 .rho (false, 0, 14), bpl 195, .xi, bpl 0],
                [bpl 0, .sign 778, .rho (true, 2364, 722), .rho (false, 0, 1394),
                 .rho (false, 0, 6), bpl 196, .xi, .rho (false, 0, 58), bpl 62, .xi, .xi,
                 .rho (false, 0, 56), bpl 197, bpl 0],
                [bpl 0, .sign 82, .rho (false, 2838, 2593), .rho (false, 0, 590),
                 .rho (false, 0, 48), bpl 201, .xi, .xi, .rho (false, 0, 38), bpl 202, .xi,
                 .xi, .rho (false, 0, 62), bpl 56, bpl 0]]
  kappaMinus := #[[bpl 0, .sign 2619, .rho (false, 1536, 222), .rho (false, 0, 806),
                  .rho (false, 0, 36), bpl 193, .xi, .rho (false, 0, 6), bpl 57, .xi, bpl 14,
                  bpl 0],
                 [bpl 0, .sign 21, .rho (false, 1828, 1589), .rho (false, 0, 471),
                  .rho (false, 0, 60), bpl 39, .xi, .xi, .rho (false, 0, 6), bpl 40, .xi, .xi,
                  bpl 14, bpl 0],
                 [bpl 0, .sign 119, .rho (false, 67, 133), .rho (false, 0, 1785), bpl 21,
                  bpl 0],
                 [bpl 0, .sign 3387, .rho (false, 104, 3374), .rho (false, 0, 3804),
                  .rho (false, 0, 32), bpl 198, .xi, .rho (false, 0, 12), bpl 199, .xi, .xi,
                  .rho (false, 0, 14), bpl 200, bpl 0],
                 [bpl 0, .sign 873, .rho (false, 3587, 402), .rho (false, 0, 3292),
                  .rho (false, 0, 18), bpl 45, .xi, .xi, .rho (false, 0, 40), bpl 19, bpl 0]]
  tPlus := #[9, 9, 5, 8, 6]
  tMinus := #[8, 7, 9, 8, 9]
  size := #[23100, 100, 3850, 15400, 4125]
  lam := #[16445440, 569344, 110592, 12296192, 6643712]

end CFSG.Monster.AxisCount.Baby
