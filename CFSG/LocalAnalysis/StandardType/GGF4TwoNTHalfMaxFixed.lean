module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfMaxMod
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfMaxDefs

public section

namespace CFSG.StandardType.HalfMaxF4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration CFSG.RankThree.E6
  CFSG.StandardType.ExcFramesHalf

open scoped Matrix

private structure V4 where
  x0 : ℤ
  x1 : ℤ
  x2 : ℤ
  x3 : ℤ

private def V4.get (v : V4) : ℕ → ℤ
  | 0 => v.x0
  | 1 => v.x1
  | 2 => v.x2
  | _ => v.x3

private def tab : List V4 := [
    ⟨1, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩,
    ⟨-1, 0, 0, 0⟩, ⟨1, 1, 0, 0⟩, ⟨0, -1, 0, 0⟩, ⟨0, 1, 2, 0⟩,
    ⟨0, 1, 1, 0⟩, ⟨0, 0, -1, 0⟩, ⟨0, 0, 1, 1⟩, ⟨0, 0, 0, -1⟩,
    ⟨-1, -1, 0, 0⟩, ⟨1, 1, 2, 0⟩, ⟨0, -1, -2, 0⟩, ⟨0, 1, 2, 2⟩,
    ⟨1, 1, 1, 0⟩, ⟨0, 1, 1, 1⟩, ⟨0, -1, -1, 0⟩, ⟨0, 0, -1, -1⟩,
    ⟨-1, -1, -2, 0⟩, ⟨1, 2, 2, 0⟩, ⟨1, 1, 2, 2⟩, ⟨0, -1, -2, -2⟩,
    ⟨1, 1, 1, 1⟩, ⟨0, 1, 2, 1⟩, ⟨-1, -1, -1, 0⟩, ⟨0, -1, -1, -1⟩,
    ⟨-1, -2, -2, 0⟩, ⟨-1, -1, -2, -2⟩, ⟨1, 2, 2, 2⟩, ⟨1, 1, 2, 1⟩,
    ⟨-1, -1, -1, -1⟩, ⟨0, -1, -2, -1⟩, ⟨-1, -2, -2, -2⟩, ⟨1, 2, 4, 2⟩,
    ⟨1, 2, 2, 1⟩, ⟨-1, -1, -2, -1⟩, ⟨-1, -2, -4, -2⟩, ⟨1, 3, 4, 2⟩,
    ⟨1, 2, 3, 1⟩, ⟨-1, -2, -2, -1⟩, ⟨-1, -3, -4, -2⟩, ⟨2, 3, 4, 2⟩,
    ⟨1, 2, 3, 2⟩, ⟨-1, -2, -3, -1⟩, ⟨-2, -3, -4, -2⟩, ⟨-1, -2, -3, -2⟩]

private def reflTab : List (List ℕ) := [
    [
      4, 5, 2, 3, 0, 1, 12, 13, 16, 9, 10, 11, 6, 7, 20, 22,
      8, 24, 26, 19, 14, 21, 15, 29, 17, 31, 18, 32, 28, 23, 30, 25,
      27, 37, 34, 35, 36, 33, 38, 43, 40, 41, 46, 39, 44, 45, 42, 47],
    [
      5, 6, 8, 3, 12, 0, 1, 7, 2, 18, 17, 11, 4, 21, 14, 15,
      16, 10, 9, 27, 28, 13, 30, 23, 24, 25, 26, 19, 20, 34, 22, 36,
      32, 33, 29, 39, 31, 41, 42, 35, 40, 37, 38, 43, 44, 45, 46, 47],
    [
      0, 7, 9, 10, 4, 13, 14, 1, 8, 2, 3, 19, 20, 5, 6, 15,
      16, 25, 18, 11, 12, 21, 22, 23, 31, 17, 26, 33, 28, 29, 35, 24,
      37, 27, 38, 30, 40, 32, 34, 39, 36, 45, 42, 43, 44, 41, 46, 47],
    [
      0, 1, 10, 11, 4, 5, 6, 15, 17, 19, 2, 3, 12, 22, 23, 7,
      24, 8, 27, 9, 29, 30, 13, 14, 16, 25, 32, 18, 34, 20, 21, 31,
      26, 33, 28, 35, 36, 37, 38, 39, 44, 41, 42, 43, 40, 47, 46, 45]]

private def reflIdx (g r : ℕ) : ℕ := (reflTab.getD g []).getD r 0

private def rv (r : ℕ) : V4 := tab.getD r ⟨0, 0, 0, 0⟩

private def dig (k : ℕ) : ℕ → ℕ
  | 0 => k % 48
  | 1 => k / 48 % 48
  | 2 => k / 2304 % 48
  | _ => k / 110592 % 48

private def succKey (g k : ℕ) : ℕ :=
  reflIdx g (dig k 0) + 48 * reflIdx g (dig k 1) + 2304 * reflIdx g (dig k 2) +
    110592 * reflIdx g (dig k 3)

private def keys : List ℕ := [
    229146, 229150, 229204, 229239, 229488, 229531, 260381, 260398, 261478,
    261484, 262389, 262411, 265680, 265722, 266020, 266062, 266343, 266347,
    276695, 276714, 277887, 277900, 278709, 278727, 297430, 297451, 297957,
    297965, 299116, 299134, 305495, 305501, 306148, 306159, 306336, 306358,
    306447, 306471, 307509, 307511, 308524, 308538, 325887, 325894, 326736,
    326759, 326932, 326957, 336432, 336474, 336628, 336670, 338247, 338251,
    350220, 350254, 350501, 350534, 352259, 352267, 368838, 368874, 369217,
    369254, 370883, 370887, 375844, 375879, 376128, 376171, 377274, 377278,
    394044, 394067, 394181, 394219, 395894, 395902, 405505, 405543, 405750,
    405779, 407606, 407610, 425766, 425772, 425953, 425956, 426144, 426149,
    441745, 441749, 441936, 441942, 442132, 442140, 892310, 892318, 892764,
    892787, 893285, 893323, 908050, 908062, 908900, 908910, 909613, 909643,
    940631, 940646, 941679, 941684, 942253, 942275, 947669, 947702, 947939,
    947947, 948396, 948430, 957143, 957154, 957996, 957999, 958373, 958398,
    961374, 961387, 961501, 961522, 962468, 962494, 979455, 979475, 980653,
    980663, 981284, 981302, 989055, 989070, 990101, 990119, 990492, 990514,
    1019418, 1019422, 1019476, 1019511, 1019760, 1019803, 1021392, 1021434, 1021732,
    1021774, 1022055, 1022059, 1052957, 1052974, 1054054, 1054060, 1054965, 1054987,
    1057750, 1057771, 1058277, 1058285, 1059436, 1059454, 1066967, 1066986, 1068159,
    1068172, 1068981, 1068999, 1069071, 1069095, 1070133, 1070135, 1071148, 1071162,
    1088855, 1088861, 1089508, 1089519, 1089696, 1089718, 1090815, 1090822, 1091664,
    1091687, 1091860, 1091885, 1124372, 1124398, 1125037, 1125058, 1126398, 1126411,
    1126992, 1127034, 1127284, 1127326, 1128327, 1128331, 1131940, 1131975, 1132224,
    1132267, 1132746, 1132750, 1142990, 1143018, 1143751, 1143778, 1145022, 1145031,
    1182157, 1182187, 1182308, 1182318, 1183858, 1183870, 1190510, 1190516, 1190884,
    1190887, 1191072, 1191085, 1191175, 1191207, 1191806, 1191822, 1193266, 1193274,
    1215655, 1215661, 1216080, 1216094, 1216276, 1216292, 1237540, 1237575, 1237824,
    1237867, 1238970, 1238974, 1239600, 1239642, 1239796, 1239838, 1241415, 1241419,
    1255692, 1255726, 1255973, 1256006, 1257731, 1257739, 1258044, 1258067, 1258181,
    1258219, 1259894, 1259902, 1272006, 1272042, 1272385, 1272422, 1274051, 1274055,
    1276417, 1276455, 1276662, 1276691, 1278518, 1278522, 1319718, 1319724, 1319905,
    1319908, 1320096, 1320101, 1321873, 1321877, 1322064, 1322070, 1322260, 1322268,
    1776758, 1776762, 1777782, 1777811, 1778017, 1778055, 1792594, 1792602, 1793918,
    1793934, 1794343, 1794375, 1808957, 1808966, 1810286, 1810294, 1810663, 1810691,
    1827773, 1827778, 1828902, 1828918, 1829089, 1829118, 1843907, 1843911, 1844257,
    1844294, 1844646, 1844682, 1855038, 1855047, 1855783, 1855810, 1856414, 1856442,
    1864006, 1864019, 1865383, 1865405, 1865822, 1865846, 1873510, 1873518, 1874833,
    1874861, 1875030, 1875058, 1884940, 1884958, 1885365, 1885373, 1886518, 1886539,
    1906092, 1906115, 1906502, 1906510, 1906757, 1906795, 1917518, 1917542, 1918279,
    1918301, 1919158, 1919171, 1921877, 1921910, 1922556, 1922590, 1922963, 1922971,
    1952894, 1952908, 1953319, 1953324, 1953701, 1953717, 1956454, 1956460, 1956693,
    1956715, 1957805, 1957822, 1974775, 1974803, 1975550, 1975558, 1976621, 1976630,
    1989415, 1989429, 1990037, 1990046, 1990428, 1990444, 2016725, 2016758, 2016995,
    2017003, 2017452, 2017486, 2030486, 2030494, 2030940, 2030963, 2031461, 2031499,
    2035038, 2035051, 2035165, 2035186, 2036132, 2036158, 2048530, 2048542, 2049380,
    2049390, 2050093, 2050123, 2064639, 2064659, 2065837, 2065847, 2066468, 2066486,
    2074199, 2074214, 2075247, 2075252, 2075821, 2075843, 2076543, 2076558, 2077589,
    2077607, 2077980, 2078002, 2083799, 2083810, 2084652, 2084655, 2085029, 2085054,
    2106532, 2106567, 2106816, 2106859, 2107338, 2107342, 2108496, 2108538, 2108788,
    2108830, 2109831, 2109835, 2142925, 2142955, 2143076, 2143086, 2144626, 2144638,
    2158868, 2158894, 2159533, 2159554, 2160894, 2160907, 2161159, 2161191, 2161790,
    2161806, 2163250, 2163258, 2172878, 2172906, 2173639, 2173666, 2174910, 2174919,
    2197159, 2197165, 2197584, 2197598, 2197780, 2197796, 2204270, 2204276, 2204644,
    2204647, 2204832, 2204845, 2658892, 2658906, 2659797, 2659799, 2660655, 2660679,
    2672948, 2672966, 2673997, 2674007, 2674671, 2674691, 2680310, 2680314, 2680518,
    2680547, 2680897, 2680935, 2712932, 2712940, 2713638, 2713645, 2713825, 2713845,
    2714737, 2714774, 2715126, 2715162, 2715251, 2715255, 2739765, 2739783, 2740095,
    2740108, 2741159, 2741178, 2748733, 2748755, 2749695, 2749700, 2750567, 2750582,
    2763229, 2763237, 2764177, 2764196, 2764374, 2764396, 2785845, 2785853, 2786188,
    2786206, 2787190, 2787211, 2802630, 2802658, 2803009, 2803037, 2803894, 2803902,
    2806333, 2806354, 2807300, 2807326, 2807694, 2807707, 2808884, 2808894, 2809666,
    2809678, 2809933, 2809963, 2821494, 2821516, 2821729, 2821748, 2822317, 2822325,
    2827078, 2827084, 2827989, 2828011, 2828477, 2828494, 2869105, 2869134, 2869494,
    2869510, 2870573, 2870578, 2874145, 2874165, 2874534, 2874541, 2875172, 2875180,
    2901443, 2901447, 2901793, 2901830, 2902182, 2902218, 2919486, 2919495, 2920231,
    2920258, 2920862, 2920890, 2931062, 2931066, 2932086, 2932115, 2932321, 2932359,
    2937670, 2937683, 2939047, 2939069, 2939486, 2939510, 2946898, 2946906, 2948222,
    2948238, 2948647, 2948679, 2951782, 2951790, 2953105, 2953133, 2953302, 2953330,
    2958653, 2958662, 2959982, 2959990, 2960359, 2960387, 2968253, 2968258, 2969382,
    2969398, 2969569, 2969598, 2993237, 2993270, 2993916, 2993950, 2994323, 2994331,
    3005100, 3005123, 3005510, 3005518, 3005765, 3005803, 3007078, 3007084, 3007317,
    3007339, 3008429, 3008446, 3043852, 3043870, 3044277, 3044285, 3045430, 3045451,
    3046135, 3046163, 3046910, 3046918, 3047981, 3047990, 3069518, 3069542, 3070279,
    3070301, 3071158, 3071171, 3072295, 3072309, 3072917, 3072926, 3073308, 3073324,
    3088766, 3088780, 3089191, 3089196, 3089573, 3089589, 3447468, 3447490, 3448133,
    3448151, 3448815, 3448830, 3449452, 3449466, 3449685, 3449687, 3450735, 3450759,
    3468636, 3468652, 3469157, 3469166, 3469543, 3469557, 3472718, 3472734, 3472882,
    3472890, 3473479, 3473511, 3488503, 3488530, 3489278, 3489306, 3489390, 3489399,
    3502335, 3502348, 3502773, 3502791, 3503543, 3503562, 3532373, 3532398, 3533052,
    3533055, 3533927, 3533938, 3537365, 3537381, 3538087, 3538092, 3538526, 3538540,
    3546481, 3546518, 3546870, 3546906, 3546995, 3546999, 3559989, 3560007, 3560319,
    3560332, 3561383, 3561402, 3576566, 3576570, 3576774, 3576803, 3577153, 3577191,
    3580477, 3580499, 3581439, 3581444, 3582311, 3582326, 3610444, 3610458, 3611349,
    3611351, 3612207, 3612231, 3615709, 3615717, 3616657, 3616676, 3616854, 3616876,
    3622196, 3622214, 3623245, 3623255, 3623919, 3623939, 3641444, 3641452, 3642150,
    3642157, 3642337, 3642357, 3654214, 3654220, 3655125, 3655147, 3655613, 3655630,
    3668276, 3668286, 3669058, 3669070, 3669325, 3669355, 3672637, 3672658, 3673604,
    3673630, 3673998, 3674011, 3689013, 3689021, 3689356, 3689374, 3690358, 3690379,
    3710065, 3710094, 3710454, 3710470, 3711533, 3711538, 3724321, 3724341, 3724710,
    3724717, 3725348, 3725356, 3742662, 3742690, 3743041, 3743069, 3743926, 3743934,
    3752310, 3752332, 3752545, 3752564, 3753133, 3753141, 3986596, 3986621, 3986880,
    3986903, 3987759, 3987766, 4005460, 4005476, 4005744, 4005758, 4006183, 4006189,
    4022989, 4022999, 4023140, 4023158, 4024191, 4024211, 4041223, 4041245, 4041854,
    4041878, 4042342, 4042355, 4043726, 4043734, 4044269, 4044278, 4044487, 4044515,
    4055055, 4055060, 4055725, 4055747, 4056119, 4056134, 4085328, 4085350, 4085620,
    4085631, 4086695, 4086701, 4090320, 4090333, 4090660, 4090663, 4091294, 4091300,
    4096767, 4096780, 4097205, 4097223, 4097975, 4097994, 4115191, 4115218, 4115966,
    4115994, 4116078, 4116087, 4129358, 4129374, 4129522, 4129530, 4130119, 4130151,
    4133717, 4133742, 4134396, 4134399, 4135271, 4135282, 4147564, 4147578, 4147797,
    4147799, 4148847, 4148871, 4154837, 4154853, 4155559, 4155564, 4155998, 4156012,
    4184748, 4184770, 4185413, 4185431, 4186095, 4186110, 4194396, 4194412, 4194917,
    4194926, 4195303, 4195317, 4431700, 4431708, 4431984, 4431990, 4432225, 4432229,
    4444708, 4444733, 4444992, 4445015, 4446063, 4446070, 4465212, 4465234, 4465349,
    4465367, 4466559, 4466574, 4483585, 4483613, 4483830, 4483858, 4484710, 4484718,
    4499910, 4499926, 4500289, 4500318, 4500461, 4500466, 4508940, 4508943, 4509221,
    4509246, 4510007, 4510018, 4518192, 4518214, 4518388, 4518399, 4519607, 4519613,
    4532688, 4532693, 4533025, 4533028, 4533414, 4533420, 4552719, 4552724, 4553389,
    4553411, 4553783, 4553798, 4555344, 4555366, 4555636, 4555647, 4556711, 4556717,
    4571342, 4571350, 4571885, 4571894, 4572103, 4572131, 4573447, 4573469, 4574078,
    4574102, 4574566, 4574579, 4578768, 4578781, 4579108, 4579111, 4579742, 4579748,
    4589773, 4589783, 4589924, 4589942, 4590975, 4590995, 4627108, 4627133, 4627392,
    4627415, 4628271, 4628278, 4636756, 4636772, 4637040, 4637054, 4637479, 4637485,
    4892068, 4892076, 4892352, 4892358, 4892737, 4892741, 4910116, 4910132, 4910400,
    4910414, 4911175, 4911181, 4928316, 4928332, 4928453, 4928462, 4929223, 4929237,
    4939777, 4939796, 4940022, 4940044, 4940461, 4940469, 4942278, 4942285, 4942436,
    4942444, 4942657, 4942677, 4951303, 4951308, 4951589, 4951605, 4951934, 4951948,
    4960560, 4960573, 4960756, 4960759, 4961534, 4961540, 4970064, 4970069, 4970353,
    4970356, 4970742, 4970748, 4981296, 4981318, 4981492, 4981503, 4982711, 4982717,
    4995084, 4995087, 4995365, 4995390, 4996151, 4996162, 5002704, 5002709, 5003041,
    5003044, 5003430, 5003436, 5013702, 5013718, 5014081, 5014110, 5014253, 5014258,
    5034241, 5034269, 5034486, 5034514, 5035366, 5035374, 5048124, 5048146, 5048261,
    5048279, 5049471, 5049486, 5059876, 5059901, 5060160, 5060183, 5061231, 5061238,
    5079124, 5079132, 5079408, 5079414, 5079649, 5079653, 5205072, 5205077, 5205361,
    5205364, 5205750, 5205756, 5220912, 5220925, 5221108, 5221111, 5221886, 5221892,
    5236999, 5237004, 5237285, 5237301, 5237630, 5237644, 5253318, 5253325, 5253476,
    5253484, 5253697, 5253717, 5255425, 5255444, 5255670, 5255692, 5256109, 5256117,
    5269308, 5269324, 5269445, 5269454, 5270215, 5270229, 5281060, 5281076, 5281344,
    5281358, 5282119, 5282125, 5290660, 5290668, 5290944, 5290950, 5291329, 5291333]

private def bitset (l : List ℕ) : ℕ := l.foldl (fun b k => b ||| (1 <<< k)) 0

private def ent (k i a : ℕ) : ℤ := (rv (dig k a)).get i

private def addOne (k i a : ℕ) : ℤ := ent k i a + (if i = a then 1 else 0)

private def minorsB (k : ℕ) : Bool :=
  (List.range 4).all fun i => (List.range 4).all fun j => (List.range 4).all fun a =>
    (List.range 4).all fun b => (addOne k i a * addOne k j b - addOne k i b * addOne k j a) % 3 == 0

private def zeroB (k : ℕ) : Bool :=
  (List.range 4).all fun i => (List.range 4).all fun a => addOne k i a % 3 == 0

private def fixB (k ρ : ℕ) : Bool :=
  (List.range 4).all fun i =>
    ent k i 0 * (rv ρ).get 0 + ent k i 1 * (rv ρ).get 1 + ent k i 2 * (rv ρ).get 2 +
      ent k i 3 * (rv ρ).get 3 == (rv ρ).get i

private def rootsB (k : ℕ) : Bool := (List.range 48).any fun ρ => fixB k ρ

private def goodB (k : ℕ) : Bool := !minorsB k || zeroB k || rootsB k

private def checkBound : Bool :=
  (List.range 4).all fun g => (List.range 48).all fun r => reflIdx g r < 48

private def checkParents : Bool :=
  (List.range 48).all fun r => r < 4 ||
    (List.range r).any fun r' => (List.range 4).any fun g => reflIdx g r' == r

private def checkClosure : Bool :=
  (bitset keys).testBit (0 + 48 * 1 + 2304 * 2 + 110592 * 3) &&
  keys.all fun k => k < 48 ^ 4 && (List.range 4).all fun g => (bitset keys).testBit (succKey g k)

private def checkGood : Bool := keys.all goodB

private theorem checkBound_eq : checkBound = true := by decide +kernel

private theorem checkParents_eq : checkParents = true := by decide +kernel

private theorem checkClosure_eq : checkClosure = true := by decide +kernel

private theorem checkGood_eq : checkGood = true := by decide +kernel

private def RV (r : ℕ) : Fin Tag.F4.rank → ℤ := fun i => (rv r).get i.val

private theorem simple_eq_RV : ∀ j : Fin Tag.F4.rank, Pi.single j (1 : ℤ) = RV j.val := by
  decide +kernel

private theorem reflect_RV :
    ∀ (g : Fin Tag.F4.rank) (r : Fin 48), reflect .F4 g (RV r.val) = RV (reflIdx g.val r.val) := by
  decide +kernel

private theorem mem_of_testBit_bitset (l : List ℕ) (k : ℕ) (h : (bitset l).testBit k = true) :
    k ∈ l := by
  have key : ∀ (l : List ℕ) (b : ℕ), (l.foldl (fun b k => b ||| (1 <<< k)) b).testBit k = true →
      b.testBit k = true ∨ k ∈ l := by
    intro l
    induction l with
    | nil => intro b hb; exact Or.inl hb
    | cons a l ih =>
      intro b hb
      rcases ih _ hb with h1 | h1
      · rw [Nat.testBit_or, Bool.or_eq_true, Nat.testBit_shiftLeft] at h1
        rcases h1 with h2 | h2
        · exact Or.inl h2
        · right
          have : k = a := by
            simp only [Nat.testBit_one_eq_true_iff_self_eq_zero, Bool.and_eq_true,
              decide_eq_true_eq] at h2
            omega
          simp [this]
      · exact Or.inr (List.mem_cons_of_mem a h1)
  rcases key l 0 h with h0 | h0
  · simp at h0
  · exact h0

private theorem reflIdx_lt {g r : ℕ} (hg : g < 4) (hr : r < 48) : reflIdx g r < 48 := by
  have h := checkBound_eq
  simp only [checkBound, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact h g hg r hr

private theorem dig_lt (k j : ℕ) : dig k j < 48 := by
  match j with
  | 0 => exact Nat.mod_lt _ (by norm_num)
  | 1 => exact Nat.mod_lt _ (by norm_num)
  | 2 => exact Nat.mod_lt _ (by norm_num)
  | _ + 3 => exact Nat.mod_lt _ (by norm_num)

private theorem dig_succKey {g : ℕ} (hg : g < 4) (k j : ℕ) (hj : j < 4) :
    dig (succKey g k) j = reflIdx g (dig k j) := by
  have key : ∀ a0 a1 a2 a3 : ℕ, a0 < 48 → a1 < 48 → a2 < 48 → a3 < 48 →
      dig (a0 + 48 * a1 + 2304 * a2 + 110592 * a3) 0 = a0 ∧
      dig (a0 + 48 * a1 + 2304 * a2 + 110592 * a3) 1 = a1 ∧
      dig (a0 + 48 * a1 + 2304 * a2 + 110592 * a3) 2 = a2 ∧
      dig (a0 + 48 * a1 + 2304 * a2 + 110592 * a3) 3 = a3 := by
    intro a0 a1 a2 a3 h0 h1 h2 h3
    simp only [dig]
    refine ⟨by omega, by omega, by omega, by omega⟩
  obtain ⟨e0, e1, e2, e3⟩ := key _ _ _ _ (reflIdx_lt hg (dig_lt k 0)) (reflIdx_lt hg (dig_lt k 1))
    (reflIdx_lt hg (dig_lt k 2)) (reflIdx_lt hg (dig_lt k 3))
  unfold succKey
  interval_cases j <;> assumption

private theorem isRoot_RV : ∀ r, r < 48 → IsRoot .F4 (RV r) := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro hr
    by_cases h4 : r < 4
    · rw [← simple_eq_RV ⟨r, h4⟩]
      exact IsRoot.basis _
    · have hp := checkParents_eq
      simp only [checkParents, List.all_eq_true, List.mem_range, Bool.or_eq_true,
        decide_eq_true_eq, List.any_eq_true, beq_iff_eq] at hp
      obtain ⟨r', hr', g, hg, heq⟩ := (hp r hr).resolve_left h4
      have h1 := ih r' hr' (hr'.trans hr)
      have h2 := reflect_RV ⟨g, hg⟩ ⟨r', hr'.trans hr⟩
      simp only [heq] at h2
      rw [← h2]
      exact IsRoot.reflect _ h1

private theorem wordProd_smul' (ω : List (Fin Tag.F4.rank)) (v : Fin Tag.F4.rank → ℤ) :
    (coxeterSystem .F4).wordProd ω • v = ω.foldr (reflect .F4) v := by
  induction ω with
  | nil => simp
  | cons i ω ih =>
    rw [CoxeterSystem.wordProd_cons, mul_smul, ih, simple_smul]
    rfl

private theorem closure_facts :
    (bitset keys).testBit (0 + 48 * 1 + 2304 * 2 + 110592 * 3) = true ∧
    ∀ k ∈ keys, k < 48 ^ 4 ∧ ∀ g < 4, (bitset keys).testBit (succKey g k) = true := by
  have hcl := checkClosure_eq
  unfold checkClosure at hcl
  rw [Bool.and_eq_true] at hcl
  obtain ⟨h1, h2⟩ := hcl
  refine ⟨h1, ?_⟩
  intro k hk
  have := List.all_eq_true.mp h2 k hk
  rw [Bool.and_eq_true] at this
  obtain ⟨h3, h4⟩ := this
  refine ⟨by simpa using h3, ?_⟩
  intro g hg
  have := List.all_eq_true.mp h4 g (List.mem_range.mpr hg)
  exact this

private theorem exists_key (ω : List (Fin Tag.F4.rank)) :
    ∃ k ∈ keys, ∀ j : Fin Tag.F4.rank,
      ω.foldr (reflect .F4) (Pi.single j 1) = RV (dig k j.val) := by
  have hcl := closure_facts
  induction ω with
  | nil =>
    refine ⟨0 + 48 * 1 + 2304 * 2 + 110592 * 3, mem_of_testBit_bitset _ _ hcl.1, ?_⟩
    intro j
    rw [List.foldr_nil, simple_eq_RV]
    have hj : ∀ j : Fin Tag.F4.rank, dig (0 + 48 * 1 + 2304 * 2 + 110592 * 3) j.val = j.val := by
      decide +kernel
    rw [hj]
  | cons g ω ih =>
    obtain ⟨k, hk, hcol⟩ := ih
    refine ⟨succKey g.val k, mem_of_testBit_bitset _ _ ((hcl.2 k hk).2 g.val g.isLt), ?_⟩
    intro j
    rw [List.foldr_cons, hcol j]
    have hlt : dig k j.val < 48 := dig_lt k j.val
    rw [dig_succKey g.isLt k j.val j.isLt]
    exact reflect_RV g ⟨dig k j.val, hlt⟩

private theorem sum_rank (f : Fin Tag.F4.rank → ℤ) :
    ∑ i, f i = f ⟨0, by decide⟩ + f ⟨1, by decide⟩ + f ⟨2, by decide⟩ + f ⟨3, by decide⟩ :=
  Fin.sum_univ_four f

theorem halfMaxFixedRoot_F4_three : HalfMaxFixedRoot .F4 3 := by
  intro w hge hlt
  obtain ⟨ω, rfl⟩ := (coxeterSystem .F4).wordProd_surjective w
  obtain ⟨k, hk, hcol⟩ := exists_key ω
  have hW : ∀ i a : Fin Tag.F4.rank,
      weylMatrix ((coxeterSystem .F4).wordProd ω) i a = ent k i.val a.val := by
    intro i a
    rw [weylMatrix_apply, wordProd_smul', hcol a]
    rfl
  set M := weylMatrix ((coxeterSystem .F4).wordProd ω) with hM
  set N : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) (ZMod 3) := modMat 3 M with hN
  have hrank : (N + 1).rank ≤ 1 := by
    refine rank_add_one_le_one_of_card_eigenspace N ?_
    rw [Nat.card_zmod]
    exact hge
  have hne : N + 1 ≠ 0 := by
    intro h0
    have hall : ∀ z : Fin Tag.F4.rank → ZMod 3, Nᵀ *ᵥ z = (-1 : ZMod 3) • z := by
      intro z
      have h1 : (N + 1)ᵀ *ᵥ z = 0 := by rw [h0]; simp
      rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.add_mulVec, Matrix.one_mulVec] at h1
      funext i
      have h2 := congrFun h1 i
      simp only [Pi.add_apply, Pi.zero_apply] at h2
      simp only [Pi.smul_apply, smul_eq_mul]
      have key : ∀ x y : ZMod 3, y + x = 0 → y = -1 * x := by decide
      exact key _ _ h2
    have hcard : Nat.card {z : Fin Tag.F4.rank → ZMod 3 // Nᵀ *ᵥ z = (-1 : ZMod 3) • z} =
        3 ^ Tag.F4.rank := by
      rw [Nat.card_congr (Equiv.subtypeUnivEquiv hall), Nat.card_eq_fintype_card]
      simp [Fintype.card_fun]
    exact absurd hcard (ne_of_lt hlt)
  obtain ⟨l, c, hl, hc, hlc⟩ := exists_vecMulVec_of_rank_le_one hrank hne
  have hmin : ∀ i j a b : Fin Tag.F4.rank,
      (N + 1) i a * (N + 1) j b = (N + 1) i b * (N + 1) j a := by
    intro i j a b
    rw [hlc]
    simp only [Matrix.vecMulVec_apply]
    ring
  have hcast : ∀ i a : Fin Tag.F4.rank,
      ((addOne k i.val a.val : ℤ) : ZMod 3) = (N + 1) i a := by
    intro i a
    simp only [addOne, hN, modMat, Matrix.add_apply, Matrix.map_apply, Matrix.one_apply,
      ← hW i a, Fin.ext_iff]
    split_ifs <;> simp
  have hgood : goodB k = true := List.all_eq_true.mp checkGood_eq k hk
  have hminB : minorsB k = true := by
    unfold minorsB
    simp only [List.all_eq_true, List.mem_range, beq_iff_eq]
    intro i hi j hj a ha b hb
    have h1 := hmin ⟨i, hi⟩ ⟨j, hj⟩ ⟨a, ha⟩ ⟨b, hb⟩
    rw [← hcast, ← hcast, ← hcast, ← hcast] at h1
    have h2 : ((addOne k i a * addOne k j b - addOne k i b * addOne k j a : ℤ) : ZMod 3) = 0 := by
      push_cast
      rw [h1]
      ring
    have h3 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp h2
    exact Int.emod_eq_zero_of_dvd (by exact_mod_cast h3)
  simp only [goodB, Bool.or_eq_true, Bool.not_eq_true'] at hgood
  rcases hgood with (h | h) | h
  · rw [hminB] at h
    exact absurd h (by simp)
  · exfalso
    apply hne
    ext i a
    have h1 := List.all_eq_true.mp (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
      a.val (List.mem_range.mpr a.isLt)
    have h2 := (ZMod.intCast_zmod_eq_zero_iff_dvd (addOne k i.val a.val) 3).mpr
      (by exact_mod_cast Int.dvd_of_emod_eq_zero (beq_iff_eq.mp h1))
    rw [hcast] at h2
    simpa using h2
  · obtain ⟨ρ, hρ, hfix⟩ := List.any_eq_true.mp h
    have hρ48 : ρ < 48 := List.mem_range.mp hρ
    refine ⟨RV ρ, isRoot_RV ρ hρ48, ?_⟩
    rw [← weylMatrix_mulVec]
    show M.mulVec (RV ρ) = RV ρ
    funext i
    have h1 := beq_iff_eq.mp (List.all_eq_true.mp hfix i.val (List.mem_range.mpr i.isLt))
    simp only [Matrix.mulVec, dotProduct, sum_rank, hW]
    simpa [RV] using h1

end CFSG.StandardType.HalfMaxF4


