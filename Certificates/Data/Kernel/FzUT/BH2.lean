module

public import Certificates.Data.Kernel.FzUT.BFacts

public section

namespace CFSG.KC.FzBMod

structure H2D where
  g1 : Nat
  g2 : Nat
  o1 : Nat
  o2 : Nat
  o3 : Nat
  o01 : Nat
  o02 : Nat
  o03 : Nat
  o12 : Nat
  o13 : Nat
  o23 : Nat
  e12 : Bool
  e13 : Bool
  e23 : Bool
  w1 : List Nat
  ra : List Nat
  rb : List Nat

@[expose] noncomputable def powN (c : Bool) (a k : Nat) : Nat := itN (mulN c a) k 0

@[expose] noncomputable def ordOK (c : Bool) (a o : Nat) : Bool :=
  bAnd(Nat.beq (powN c a o) 0, bIf(Nat.beq (powN c a (Nat.shiftRight o 1)) 0, false, true))

@[expose] noncomputable def pairT (c : Bool) (a b : Nat) (e : Bool) (o : Nat) : Bool :=
  bAnd(bIf(e, Nat.beq (mulN c a b) (mulN c b a),
    bIf(Nat.beq (mulN c a b) (mulN c b a), false, true)), ordOK c (mulN c a b) o)

@[expose] noncomputable def pick (y0 y1 y2 y3 i : Nat) : Nat :=
  nIf(Nat.beq i 0, y0, nIf(Nat.beq i 1, y1, nIf(Nat.beq i 2, y2, y3)))

@[expose] noncomputable def evY (c : Bool) (y0 y1 y2 y3 : Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun i _ r => mulN c (pick y0 y1 y2 y3 i) r) w

@[expose] noncomputable def h2L1 (c : Bool) (D : H2D) (y : Nat) : Bool :=
  bAnd(ordOK c y D.o1, pairT c 128 y true D.o01)

@[expose] noncomputable def h2L2 (c : Bool) (D : H2D) (y1 y : Nat) : Bool :=
  bAnd(ordOK c y D.o2, bAnd(pairT c 128 y true D.o02, pairT c y1 y D.e12 D.o12))

@[expose] noncomputable def h2L3 (c : Bool) (D : H2D) (y1 y2 y : Nat) : Bool :=
  bAnd(ordOK c y D.o3, bAnd(pairT c 128 y true D.o03,
    bAnd(pairT c y1 y D.e13 D.o13, pairT c y2 y D.e23 D.o23)))

@[expose] noncomputable def h2Leaf (c : Bool) (D : H2D) (y1 y2 y3 : Nat) : Bool :=
  bIf(Nat.beq (evY c 128 y1 y2 y3 D.ra) (evY c 128 y1 y2 y3 D.rb),
    bAnd(w0N (evY c 128 y1 y2 y3 D.w1), w0N y3), true)

@[expose] noncomputable def h2Srch (c : Bool) (D : H2D) (SL : List Nat) (r : Nat) : Bool :=
  allL SL (fun y2 => bIf(h2L2 c D r y2,
    allL SL (fun y3 => bIf(h2L3 c D r y2 y3, h2Leaf c D r y2 y3, true)), true))

@[expose] noncomputable def h2RecOK (c : Bool) (R1 : List Nat) (rec : Nat) : Bool :=
  letN (fld(rec, 10, 1023)) (fun h => letN (fld(rec, 20, 1023)) (fun hi =>
    bAnd(Nat.beq (mulN c h hi) 0, bAnd(Nat.beq (mulN c hi h) 0,
    bAnd(Nat.beq (mulN c h 128) (mulN c 128 h),
    bAnd(Nat.beq (mulN c (mulN c h (fld(rec, 0, 1023))) hi) (fld(rec, 30, 1023)),
    bAnd(memL (fld(rec, 30, 1023)) R1,
    allN 8 (fun i => w0N (mulN c (mulN c hi (w0E i)) h)))))))))

@[expose] noncomputable def h2Consts (c : Bool) (D : H2D) : Bool :=
  Nat.blt D.g1 1024 && Nat.blt D.g2 1024 &&
  Nat.beq (mulN c D.g1 832) (mulN c 832 D.g1) && Nat.beq (mulN c D.g2 832) (mulN c 832 D.g2) &&
  Nat.beq (mulN c 128 832) (mulN c 832 128) &&
  ordOK c D.g1 D.o1 && ordOK c D.g2 D.o2 && ordOK c 128 D.o3 &&
  pairT c 832 D.g1 true D.o01 && pairT c 832 D.g2 true D.o02 && pairT c 832 128 true D.o03 &&
  pairT c D.g1 D.g2 D.e12 D.o12 && pairT c D.g1 128 D.e13 D.o13 && pairT c D.g2 128 D.e23 D.o23 &&
  Nat.beq (evY c 832 D.g1 D.g2 128 D.ra) (evY c 832 D.g1 D.g2 128 D.rb) &&
  Nat.beq (evY c 832 D.g1 D.g2 128 D.w1) 1

@[expose] noncomputable def h2SLOK (c : Bool) (SL : List Nat) : Bool :=
  allN 1024 (fun v => bIf(Nat.beq (mulN c v 128) (mulN c 128 v), memL v SL, true))

@[expose] noncomputable def h2Cover (c : Bool) (D : H2D) (SL REC : List Nat) : Bool :=
  allL SL (fun y => bIf(h2L1 c D y, anyL REC (fun rec => Nat.beq (fld(rec, 0, 1023)) y), true))

@[expose] noncomputable def h2DI : H2D :=
  ⟨320, 46, 2, 4, 2, 2, 4, 2, 8, 2, 2, false, true, false, [2, 2], [2, 2, 1], [1, 2, 2]⟩

@[expose] noncomputable def h2DII : H2D :=
  ⟨320, 6, 2, 2, 2, 2, 2, 2, 8, 2, 4, false, true, false, [3, 2, 3, 2], [2, 3, 2, 1],
    [1, 2, 3, 2]⟩

@[expose] noncomputable def h2D (c : Bool) : H2D := Bool.rec (motive := fun _ => H2D) h2DII h2DI c

@[expose] noncomputable def h2SL : List Nat :=
  [0, 1, 2, 3, 20, 21, 22, 23, 40, 41, 42, 43, 60, 61, 62, 63, 64, 65, 66, 67, 84, 85, 86,
    87, 104, 105, 106, 107, 124, 125, 126, 127, 128, 129, 130, 131, 148, 149, 150, 151, 168,
    169, 170, 171, 188, 189, 190, 191, 192, 193, 194, 195, 212, 213, 214, 215, 232, 233, 234,
    235, 252, 253, 254, 255, 256, 257, 258, 259, 276, 277, 278, 279, 296, 297, 298, 299, 316,
    317, 318, 319, 320, 321, 322, 323, 340, 341, 342, 343, 360, 361, 362, 363, 380, 381, 382,
    383, 384, 385, 386, 387, 404, 405, 406, 407, 424, 425, 426, 427, 444, 445, 446, 447, 448,
    449, 450, 451, 468, 469, 470, 471, 488, 489, 490, 491, 508, 509, 510, 511, 512, 513, 514,
    515, 532, 533, 534, 535, 552, 553, 554, 555, 572, 573, 574, 575, 576, 577, 578, 579, 596,
    597, 598, 599, 616, 617, 618, 619, 636, 637, 638, 639, 640, 641, 642, 643, 660, 661, 662,
    663, 680, 681, 682, 683, 700, 701, 702, 703, 704, 705, 706, 707, 724, 725, 726, 727, 744,
    745, 746, 747, 764, 765, 766, 767, 768, 769, 770, 771, 788, 789, 790, 791, 808, 809, 810,
    811, 828, 829, 830, 831, 832, 833, 834, 835, 852, 853, 854, 855, 872, 873, 874, 875, 892,
    893, 894, 895, 896, 897, 898, 899, 916, 917, 918, 919, 936, 937, 938, 939, 956, 957, 958,
    959, 960, 961, 962, 963, 980, 981, 982, 983, 1000, 1001, 1002, 1003, 1020, 1021, 1022,
    1023]

@[expose] noncomputable def h2R1 : List Nat :=
  [1, 2, 129, 130, 256, 276, 296, 320, 340, 360, 512, 640, 768, 832]

@[expose] noncomputable def h2Rec : List Nat :=
  [1073741825, 2147483650, 2684878851, 138512695425, 139586437250, 140123832451,
    274877907200, 274898900225, 274940885250, 274919894275, 296352743700, 296373736725,
    296415721750, 296394730775, 317827580200, 317848573225, 317890558250, 317869567275,
    318364975420, 318385968445, 318427934014, 318406981951, 343597384000, 343618377025,
    343660362050, 343639371075, 365072220500, 365093213525, 365135198550, 365114207575,
    386547057000, 386568050025, 386610035050, 386589044075, 387084452220, 387105445245,
    387147410814, 387126458751, 274945212800, 274966205825, 275008190850, 274987199875,
    296420049300, 296441042325, 296483027350, 296462036375, 317894885800, 317915878825,
    317957863850, 317936872875, 318432281020, 318453274045, 318495239614, 318474287551,
    343664689600, 343685682625, 343727667650, 343706676675, 365139526100, 365160519125,
    365202504150, 365181513175, 386614362600, 386635355625, 386677340650, 386656349675,
    387151757820, 387172750845, 387214716414, 387193764351, 549755814400, 549757913601,
    549799896598, 549797801495, 687194768000, 687196867201, 687238850198, 687236755095,
    824633721600, 824635820801, 824677803796, 824675708693, 893353198400, 893355297601,
    893397280596, 893395185493, 824701027200, 824703126401, 824745109396, 824743014293,
    893420504000, 893422603201, 893464586196, 893462491093]

end CFSG.KC.FzBMod
