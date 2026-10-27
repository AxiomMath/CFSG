module

public import Certificates.Kernel.AE5X.Data
public import Certificates.Data.Kernel.WrPackX
public import Certificates.Kernel.AE5Sq.Data

public noncomputable section

namespace CFSG.KD.AE5X

open CFSG.KC.WrTwin CFSG.KC.WrPack CFSG.KC.WrPackX CFSG.KD.AE5Sq

abbrev PairD : Type :=
  List Nat × List Nat × List Nat × List Nat × List ((Nat × Nat) × Nat) × ((Nat × Nat) × Nat)

@[expose] def mkD (i j : Nat) (P2 L : List Nat) (W : List ((Nat × Nat) × Nat))
    (w3 : (Nat × Nat) × Nat) : PairD :=
  (M10lit.getD i [], M10lit.getD j [], P2, L, W, w3)

@[expose] def PD : List PairD :=
  [mkD 0 1 Pl2_0 L_0 W_0 w3_0, mkD 1 0 Pl2_1 L_1 W_1 w3_1, mkD 2 3 Pl2_2 L_2 W_2 w3_2,
    mkD 3 2 Pl2_3 L_3 W_3 w3_3, mkD 4 5 Pl2_4 L_4 W_4 w3_4, mkD 5 4 Pl2_5 L_5 W_5 w3_5,
    mkD 6 7 Pl2_6 L_6 W_6 w3_6, mkD 7 6 Pl2_7 L_7 W_7 w3_7, mkD 8 9 Pl2_8 L_8 W_8 w3_8,
    mkD 9 8 Pl2_9 L_9 W_9 w3_9]

@[expose] def pairChk (d : PairD) : Bool :=
  d.2.2.1 == dbl 5 pilit (prodLP 5 d.1 d.2.1) && d.2.2.2.1 == L18P 5 e10L pilit d.1 d.2.1 &&
    a1P 5 e10L d.2.2.2.1 &&
    a2P 5 e10L pilit d.1 d.2.1 d.2.2.1 d.2.2.2.1 P60lit V16lit d.2.2.2.2.1 &&
    a3P 5 e10L pilit M10lit d.1 d.2.1 P60lit P120lit V16lit d.2.2.2.2.2

@[expose] def a5Chk (d : PairD) : Bool :=
  a5P 5 e10L pilit a0lit b0lit Ms3lit d.1 d.2.1 d.2.2.1 d.2.2.2.1 P120lit Vlit

theorem x5_pins : (P120lit == P120 &&
    Ms3lit == M10lit.map (List.map fun m => (m, pm 5 m pilit, ord4P 5 e10L pilit m)) &&
    Mall2lit == dbl 5 pilit M10lit.flatten) = true := by
  decide +kernel

theorem x5_cent : centOK 5 pilit [a0lit, b0lit] P120lit Vlit [e10L] = true := by decide +kernel

theorem x5_odd : (M10lit.all fun A => centOK 5 pilit A P120lit Vlit Mall2lit) = true := by
  decide +kernel

theorem x5_odd15 :
    (Mall2lit.all fun c => !inPiP e10L pilit (pw 5 e10L 15 c) || inPiP e10L pilit c) = true := by
  decide +kernel

theorem x5_inv : (M10lit.all fun A => A.all fun m =>
    !(!inPiP e10L pilit m && inPiP e10L pilit (pm 5 m m)) || eqPiP 5 pilit m (A.getD 1 e10L)) =
    true := by
  decide +kernel

theorem x5_zv : (M10lit.all fun A => samePerm 5 (A.getD 1 e10L) e10L) = true := by decide +kernel

theorem x5_twins : (M10lit.all fun A => M10lit.all fun B =>
    !twinP 5 pilit A B || PD.any fun d => A == d.1 && B == d.2.1) = true := by
  decide +kernel

theorem x5_pair_0 : pairChk (mkD 0 1 Pl2_0 L_0 W_0 w3_0) = true := by decide +kernel
theorem x5_pair_1 : pairChk (mkD 1 0 Pl2_1 L_1 W_1 w3_1) = true := by decide +kernel
theorem x5_pair_2 : pairChk (mkD 2 3 Pl2_2 L_2 W_2 w3_2) = true := by decide +kernel
theorem x5_pair_3 : pairChk (mkD 3 2 Pl2_3 L_3 W_3 w3_3) = true := by decide +kernel
theorem x5_pair_4 : pairChk (mkD 4 5 Pl2_4 L_4 W_4 w3_4) = true := by decide +kernel
theorem x5_pair_5 : pairChk (mkD 5 4 Pl2_5 L_5 W_5 w3_5) = true := by decide +kernel
theorem x5_pair_6 : pairChk (mkD 6 7 Pl2_6 L_6 W_6 w3_6) = true := by decide +kernel
theorem x5_pair_7 : pairChk (mkD 7 6 Pl2_7 L_7 W_7 w3_7) = true := by decide +kernel
theorem x5_pair_8 : pairChk (mkD 8 9 Pl2_8 L_8 W_8 w3_8) = true := by decide +kernel
theorem x5_pair_9 : pairChk (mkD 9 8 Pl2_9 L_9 W_9 w3_9) = true := by decide +kernel

theorem x5_a5_0 : a5Chk (mkD 0 1 Pl2_0 L_0 W_0 w3_0) = true := by decide +kernel
theorem x5_a5_1 : a5Chk (mkD 1 0 Pl2_1 L_1 W_1 w3_1) = true := by decide +kernel
theorem x5_a5_2 : a5Chk (mkD 2 3 Pl2_2 L_2 W_2 w3_2) = true := by decide +kernel
theorem x5_a5_3 : a5Chk (mkD 3 2 Pl2_3 L_3 W_3 w3_3) = true := by decide +kernel
theorem x5_a5_4 : a5Chk (mkD 4 5 Pl2_4 L_4 W_4 w3_4) = true := by decide +kernel
theorem x5_a5_5 : a5Chk (mkD 5 4 Pl2_5 L_5 W_5 w3_5) = true := by decide +kernel
theorem x5_a5_6 : a5Chk (mkD 6 7 Pl2_6 L_6 W_6 w3_6) = true := by decide +kernel
theorem x5_a5_7 : a5Chk (mkD 7 6 Pl2_7 L_7 W_7 w3_7) = true := by decide +kernel
theorem x5_a5_8 : a5Chk (mkD 8 9 Pl2_8 L_8 W_8 w3_8) = true := by decide +kernel
theorem x5_a5_9 : a5Chk (mkD 9 8 Pl2_9 L_9 W_9 w3_9) = true := by decide +kernel

end CFSG.KD.AE5X

end
