module

public section

namespace CFSG.Quasithin.B45Alt7

@[expose] def a7CosW : List (List Bool) :=
  [[true, true, true, true], [true, true, true, false, true], [false, false, true, true], [true,
  true, false, true, false, true, true], [true, false, true, false, true, true, true], [false,
  true, false, true, true, true, true], [false]]

@[expose] def indQ (i : Nat) : List Nat :=
  if i = 5 then [6, 3, 15, 11] else if i = 8 then [6, 2, 10, 13]
  else if i = 6 then [4, 12, 10, 11] else [14, 7, 8, 10]

@[expose] def indP (i : Nat) : List Nat :=
  if i = 5 then [15, 13, 12, 10] else if i = 8 then [13, 2, 3, 6]
  else if i = 6 then [12, 7, 1, 3] else [7, 12, 9, 4]

@[expose] def indB0 : List Nat :=
  [3261, 16482, 34575, 65683, 263712, 536722, 1049997, 2237030, 4203106, 8520974, 16782351,
  33555462, 67249696, 134361828, 1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 4096, 8192, 131072]

@[expose] def indB1 : List Nat :=
  [26717428, 35791394, 68778703, 149775285, 28518824, 43680179, 83683285, 136000154, 427, 758,
  1130, 2232, 4350, 8431, 16444, 32869, 65647, 131284, 262301, 524492, 1048684, 2097209, 4194499,
  8388626, 16777308, 33554637, 67109090, 134217867]

@[expose] def indT0 : List Nat :=
  [16384, 32768, 65536, 131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608, 16777216,
  19873793, 33554432, 67108864, 1605634, 29605892, 2408456, 134217728, 25690128, 103055392,
  23281728, 211386496, 77103360, 155419136, 50578432, 16877568, 227020800, 247013376]

@[expose] def indT1 : List Nat :=
  [38294969, 193608082, 240767473, 258282014, 75848759, 144937378, 94182089, 105983933, 139837738,
  171512450, 164734183, 85129270, 89920156, 59845394, 219827834, 19894051, 96543919, 152221874,
  27583964, 49870491, 202524804, 19630642, 172906847, 261055909, 19170577, 45654818, 82156868,
  150360456]

@[expose] def indMa0 : List Nat :=
  [1, 7, 2, 16, 25, 50, 897, 201, 641, 392, 3074, 13312, 4105, 8202, 3932160, 3407872, 262144,
  1310720, 15679489, 28262401, 4194304, 24068097, 196608, 81920, 180224, 35160066, 67108864,
  136626184]

@[expose] def indMb0 : List Nat :=
  [7, 16, 34, 65, 258, 521, 1027, 2176, 4096, 8322, 10, 2, 130, 137, 262144, 524288, 1048576,
  2097152, 4194304, 8388608, 16777216, 19873793, 33554432, 67108864, 1605634, 2408456, 134217728,
  211386496]

@[expose] def indMa1 : List Nat :=
  [2, 3, 13, 6, 32, 48, 208, 96, 256, 512, 1024, 2048, 57856, 35584, 55040, 41984, 984064, 330752,
  525824, 787712, 6292480, 11536128, 12584192, 4196608, 33555200, 50332928, 218106624, 100667136]

@[expose] def indMb1 : List Nat :=
  [9, 2, 1, 14, 176, 144, 240, 16, 6656, 12032, 17920, 35584, 69376, 134656, 262912, 525824,
  1050112, 2100480, 4196608, 8391680, 16778752, 33555200, 67111936, 134217984, 1280, 3072, 3584,
  2048]

@[expose] def indNs0 : List Nat := [0, 14, 28]

@[expose] def indAW0 : List (List (List Bool)) :=
  [[[false, true, true, false], [true], [true, true, false, false], [true, true, true]], [[true,
  false, true, true], [true], []]]

@[expose] def indKers0 : List (List (Nat × List (List Bool) × List Nat)) :=
  [[(4470, [[], [false], [true], [false, false], [false, true], [true, true], [true, false, false],
  [true, false, true], [false, true, true], [true, true, true], [false, true, false, true], [false,
  false, true, true], [true, false, false, true, true], [true, true, false, false, true, true]],
  [1684, 416, 2612, 205, 1054, 4137, 649, 12257, 2481, 9245, 553, 592, 5274, 5678])], [(2617, [[],
  [false], [true], [false, false], [true, false], [true, true], [true, false, false], [false, true,
  false], [true, true, false], [false, true, true], [true, true, false, false], [true, false, true,
  false], [false, false, true, true], [true, true, true, false, false]], [1495, 4993, 15150, 13946,
  10830, 3463, 5503, 9859, 5775, 16104, 8836, 10893, 15925, 13137])]]

@[expose] def indPsi0 : List Nat := [10523, 3681]

@[expose] def indDw0 : List (List (List Bool)) :=
  [[[], [false], [true], [false, false], [false, true], [true, false], [false, false, true],
  [false, true, true], [true, false, true], [false, false, true, true], [false, true, true, true],
  [true, false, true, true], [false, true, true, true, false], [false, true, true, true, true]],
  [[], [false], [true], [false, false], [false, true], [true, false], [true, true], [false, false,
  true], [false, true, false], [false, true, true], [true, false, false], [true, true, false],
  [true, true, true], [true, true, true, true]]]

@[expose] def indRc0 : List (List Nat) :=
  [[0, 9450, 3052, 11426, 9590, 1089, 10178, 1537, 9031, 2461, 11806, 2550, 11636, 136], [0, 10108,
  9538, 14109, 4691, 9543, 4202, 568, 4395, 140, 4532, 1846, 1472, 9707]]

@[expose] def indMinv0 : List (List Nat) :=
  [[795, 780, 830, 774, 823, 806, 1073, 14368, 3112, 358, 686, 8936, 311, 4926], [11945, 6576,
  12143, 5084, 13471, 8758, 13153, 11984, 8233, 14467, 13254, 1090, 2838, 13079]]

@[expose] def indNs1 : List Nat := [0, 4, 8, 28]

@[expose] def indAW1 : List (List (List Bool)) :=
  [[[false, false], [false, false, true, true]], [[true, false], [false]], [[true, true, false,
  false], [], [true, false], [false, true]]]

@[expose] def indKers1 : List (List (Nat × List (List Bool) × List Nat)) :=
  [[(2, [[], [false], [true, false], [false, true, false]], [3, 1, 10, 6])], [(8, [[], [false],
  [true], [false, true]], [4, 8, 10, 1])], [(478699, [[], [false], [true], [false, false], [true,
  false], [false, true], [true, true], [true, false, false], [false, true, false], [true, true,
  false], [false, false, true], [true, false, true], [false, true, true], [true, true, true],
  [false, true, false, false], [true, false, true, false], [false, true, true, false], [true, true,
  true, false], [true, false, false, true], [false, true, false, true]], [71917, 1071, 11, 548494,
  898559, 871059, 1200, 845954, 347213, 2367, 333555, 828493, 125798, 774993, 432089, 197352,
  491885, 891135, 562260, 44419])]]

@[expose] def indPsi1 : List Nat := [1, 4, 28744]

@[expose] def indDw1 : List (List (List Bool)) :=
  [[[], [false], [true], [true, false]], [[], [false], [false, true], [false, true, false]], [[],
  [false], [true], [false, false], [false, true], [true, false], [true, true], [false, false,
  true], [false, true, false], [false, true, true], [true, false, true], [true, true, false],
  [true, true, true], [false, false, true, false], [false, false, true, true], [false, true, false,
  true], [false, true, true, false], [false, true, true, true], [true, false, true, false], [true,
  true, false, true]]]

@[expose] def indRc1 : List (List Nat) :=
  [[0, 9, 4, 1], [2, 7, 0, 4], [624269, 648551, 552856, 0, 20249, 195329, 244699, 184249, 259267,
  784562, 673523, 716592, 100883, 664976, 602007, 741840, 756948, 653491, 136566, 646572]]

@[expose] def indMinv1 : List (List Nat) :=
  [[15, 10, 14, 8], [12, 11, 2, 3], [249309, 995970, 879635, 81073, 200283, 628583, 799708, 422536,
  474514, 369382, 743332, 119547, 542182, 228965, 299690, 339499, 621792, 749000, 166918, 659642]]

@[expose] def regW : List (List Bool) :=
  [[false, true, false, true, true, true, true, true, true],
   [true, false, true, true, true, true, true, true, false]]

end CFSG.Quasithin.B45Alt7
