module

public import CFSG.Quasithin.Recognition.St84.Gen.TreeLLBase

import CFSG.Quasithin.Recognition.St84.Gen.L2RankOne
import CFSG.Quasithin.Recognition.St84.TransferVertex
import CFSG.Quasithin.EmptyFaithful.T1521SBlkBasic
import CFSG.Quasithin.Vol2.E2SevenKG2L2
import CFSG.Quasithin.Vol2.Ch11SecAKE8
public import CFSG.Quasithin.H13.NQCatA314ShortMap

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.Quasithin.St84
  CFSG.Quasithin.Fan86 CFSG.Quasithin.Fan86.Univ

variable {H : Type} [Group H] [Finite H] {L1 L2 S : Subgroup H} {m n : ℕ}

theorem f112ll_card_S_inf_K_of_tree (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (h1 : IsL2Quot m (oTwoQuot ↥L1)) (h2 : IsL2Quot n (oTwoQuot ↥L2))
    {X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S)}
    (hX0 : X.vert 0 = baseA (f112Gold L1 L2 S)) (hX1 : X.vert 1 = baseB (f112Gold L1 L2 S)) :
    Nat.card ↥(S ⊓ f112saK L1 L2 S) = Nat.card ↥X.S := by
  have hR : Hyp111R L1 L2 S := hyp111R_of_isL2Quot (by omega) (by omega) hF.1 h1 h2
  let D := f112EOddBaseEdgeData hF hR X hX0 hX1
  have hKe : pCoreOf 2 D.Ke = S ⊓ D.Ke := f112ll_pCoreOf_K_eq hF hm hn h1 h2
  have hY : S ⊓ D.Ke ≤ f112P1 D.L1 D.L2 D.S :=
    (inf_le_right : S ⊓ D.Ke ≤ D.Ke).trans (D.le_Ke.trans inf_le_left)
  have hmap : (D.X.S).map D.E.subtype = f112OfA D.L1 D.L2 D.S (S ⊓ D.Ke) := by
    rw [D.S_map, hKe]
  exact (card_of_map_eq (L1 := D.L1) (L2 := D.L2) (S := D.S) (E := D.E) hY hmap).symm

theorem f112ll_card_pCoreOf_P1'_of_tree (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (h1 : IsL2Quot m (oTwoQuot ↥L1)) (h2 : IsL2Quot n (oTwoQuot ↥L2))
    {X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S)}
    (hX0 : X.vert 0 = baseA (f112Gold L1 L2 S)) (hX1 : X.vert 1 = baseB (f112Gold L1 L2 S)) :
    Nat.card ↥(pCoreOf 2 (oTwoPrime (f112saP1' L1 L2 S))) = Nat.card ↥(pCoreOf 2 (X.L 0)) := by
  have hR : Hyp111R L1 L2 S := hyp111R_of_isL2Quot (by omega) (by omega) hF.1 h1 h2
  let D := f112EOddBaseEdgeData hF hR X hX0 hX1
  have hQα : pCoreOf 2 (oTwoPrime D.Pα) ≤ f112P1 D.L1 D.L2 D.S :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 (oTwoPrime D.Pα)).trans
      ((oTwoPrime_le D.Pα).trans D.le_Pα)
  exact (card_of_map_eq (L1 := D.L1) (L2 := D.L2) (S := D.S) (E := D.E) hQα
    D.pCoreOf_L_zero_map).symm

theorem f112ll_card_pCoreOf_P2'_of_tree (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (h1 : IsL2Quot m (oTwoQuot ↥L1)) (h2 : IsL2Quot n (oTwoQuot ↥L2))
    {X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S)}
    (hX0 : X.vert 0 = baseA (f112Gold L1 L2 S)) (hX1 : X.vert 1 = baseB (f112Gold L1 L2 S)) :
    Nat.card ↥(pCoreOf 2 (oTwoPrime (f112saP2' L1 L2 S))) = Nat.card ↥(pCoreOf 2 (X.L 1)) := by
  have hR : Hyp111R L1 L2 S := hyp111R_of_isL2Quot (by omega) (by omega) hF.1 h1 h2
  let D := f112EOddBaseEdgeData hF hR X hX0 hX1
  have hQβ : pCoreOf 2 (oTwoPrime D.Pβ) ≤ f112P2 D.L1 D.L2 D.S :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 (oTwoPrime D.Pβ)).trans
      ((oTwoPrime_le D.Pβ).trans D.le_Pβ)
  exact (card_of_map_eq_ofB (L1 := D.L1) (L2 := D.L2) (S := D.S) (E := D.E) hQβ
    D.pCoreOf_L_one_map).symm

theorem f112ll_card_pCoreOf_inf_of_tree (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (h1 : IsL2Quot m (oTwoQuot ↥L1)) (h2 : IsL2Quot n (oTwoQuot ↥L2))
    {X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S)}
    (hX0 : X.vert 0 = baseA (f112Gold L1 L2 S)) (hX1 : X.vert 1 = baseB (f112Gold L1 L2 S)) :
    Nat.card ↥(pCoreOf 2 (oTwoPrime (f112saP1' L1 L2 S)) ⊓
        pCoreOf 2 (oTwoPrime (f112saP2' L1 L2 S))) =
      Nat.card ↥(pCoreOf 2 (X.L 0) ⊓ pCoreOf 2 (X.L 1)) := by
  have hR : Hyp111R L1 L2 S := hyp111R_of_isL2Quot (by omega) (by omega) hF.1 h1 h2
  let D := f112EOddBaseEdgeData hF hR X hX0 hX1
  have hQα : pCoreOf 2 D.Pα ≤ f112P1 D.L1 D.L2 D.S :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 D.Pα).trans D.le_Pα
  have hQβ : pCoreOf 2 D.Pβ ≤ f112P2 D.L1 D.L2 D.S :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 D.Pβ).trans D.le_Pβ
  have hY : pCoreOf 2 D.Pα ⊓ pCoreOf 2 D.Pβ ≤ f112P1 D.L1 D.L2 D.S := inf_le_left.trans hQα
  have hmap : (D.X.Q 0 ⊓ D.X.Q 1).map D.E.subtype =
      f112OfA D.L1 D.L2 D.S (pCoreOf 2 D.Pα ⊓ pCoreOf 2 D.Pβ) := by
    rw [Subgroup.map_inf (D.X.Q 0) (D.X.Q 1) D.E.subtype D.E.subtype_injective,
      D.Q_zero_map, D.Q_one_map]
    exact ofA_map_inf_ofB_map D.L1 D.L2 D.S hQα hQβ
  have h := card_of_map_eq (L1 := D.L1) (L2 := D.L2) (S := D.S) (E := D.E) hY hmap
  have hP : Nat.card ↥(pCoreOf 2 (oTwoPrime D.Pα) ⊓ pCoreOf 2 (oTwoPrime D.Pβ)) =
      Nat.card ↥(pCoreOf 2 D.Pα ⊓ pCoreOf 2 D.Pβ) := by
    rw [pCoreOf_oTwoPrime D.Pα, pCoreOf_oTwoPrime D.Pβ]
  haveI : Finite ↥(X.Gi 0) := X.hyp.finite_stab (X.vert 0)
  haveI : Finite ↥(X.Gi 1) := X.hyp.finite_stab (X.vert 1)
  have hQ : Nat.card ↥(pCoreOf 2 (oTwoPrime (X.Gi 0)) ⊓ pCoreOf 2 (oTwoPrime (X.Gi 1))) =
      Nat.card ↥(D.X.Q 0 ⊓ D.X.Q 1) := by
    rw [pCoreOf_oTwoPrime (X.Gi 0), pCoreOf_oTwoPrime (X.Gi 1)]
    rfl
  exact hP.trans (h.symm.trans hQ.symm)

theorem f112ll_isLin2Type_oTwoPrime_P1'_of_tree (hF : F112HypW L1 L2 S) (hm : 2 ≤ m)
    (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1)) (h2 : IsL2Quot n (oTwoQuot ↥L2))
    {X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S)}
    (hX0 : X.vert 0 = baseA (f112Gold L1 L2 S)) (hX1 : X.vert 1 = baseB (f112Gold L1 L2 S))
    {f : ℕ} (hL : IsLin2Type (X.L 0) f) : IsLin2Type (oTwoPrime (f112saP1' L1 L2 S)) f := by
  have hR : Hyp111R L1 L2 S := hyp111R_of_isL2Quot (by omega) (by omega) hF.1 h1 h2
  let D := f112EOddBaseEdgeData hF hR X hX0 hX1
  have hLα : oTwoPrime D.Pα ≤ f112P1 D.L1 D.L2 D.S := (oTwoPrime_le D.Pα).trans D.le_Pα
  have h1' : IsLin2Type ((D.X.L 0).map D.E.subtype) f :=
    CFSG.Quasithin.H13.NQCat.A314D.IsLin2Type.map_of_injective'
      D.E.subtype D.E.subtype_injective hL
  have h2 : IsLin2Type (f112OfA D.L1 D.L2 D.S (oTwoPrime D.Pα)) f := D.L_zero_map ▸ h1'
  have h3 : IsLin2Type ((oTwoPrime D.Pα).subgroupOf (f112P1 D.L1 D.L2 D.S)) f :=
    CFSG.Quasithin.H13.NQCat.A314D.IsLin2Type.of_map_injective
      (f112Gold D.L1 D.L2 D.S).ofA (f112Gold D.L1 D.L2 D.S).ofA_injective h2
  have h4 : IsLin2Type (((oTwoPrime D.Pα).subgroupOf (f112P1 D.L1 D.L2 D.S)).map
      (f112P1 D.L1 D.L2 D.S).subtype) f :=
    CFSG.Quasithin.H13.NQCat.A314D.IsLin2Type.map_of_injective'
      (f112P1 D.L1 D.L2 D.S).subtype (f112P1 D.L1 D.L2 D.S).subtype_injective h3
  rwa [Subgroup.map_subgroupOf_eq_of_le hLα] at h4

theorem f112ll_isLin2Type_oTwoPrime_P2'_of_tree (hF : F112HypW L1 L2 S) (hm : 2 ≤ m)
    (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1)) (h2 : IsL2Quot n (oTwoQuot ↥L2))
    {X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S)}
    (hX0 : X.vert 0 = baseA (f112Gold L1 L2 S)) (hX1 : X.vert 1 = baseB (f112Gold L1 L2 S))
    {f : ℕ} (hL : IsLin2Type (X.L 1) f) : IsLin2Type (oTwoPrime (f112saP2' L1 L2 S)) f := by
  have hR : Hyp111R L1 L2 S := hyp111R_of_isL2Quot (by omega) (by omega) hF.1 h1 h2
  let D := f112EOddBaseEdgeData hF hR X hX0 hX1
  have hLβ : oTwoPrime D.Pβ ≤ f112P2 D.L1 D.L2 D.S := (oTwoPrime_le D.Pβ).trans D.le_Pβ
  have h1' : IsLin2Type ((D.X.L 1).map D.E.subtype) f :=
    CFSG.Quasithin.H13.NQCat.A314D.IsLin2Type.map_of_injective'
      D.E.subtype D.E.subtype_injective hL
  have h2 : IsLin2Type (f112OfB D.L1 D.L2 D.S (oTwoPrime D.Pβ)) f := D.L_one_map ▸ h1'
  have h3 : IsLin2Type ((oTwoPrime D.Pβ).subgroupOf (f112P2 D.L1 D.L2 D.S)) f :=
    CFSG.Quasithin.H13.NQCat.A314D.IsLin2Type.of_map_injective
      (f112Gold D.L1 D.L2 D.S).ofB (f112Gold D.L1 D.L2 D.S).ofB_injective h2
  have h4 : IsLin2Type (((oTwoPrime D.Pβ).subgroupOf (f112P2 D.L1 D.L2 D.S)).map
      (f112P2 D.L1 D.L2 D.S).subtype) f :=
    CFSG.Quasithin.H13.NQCat.A314D.IsLin2Type.map_of_injective'
      (f112P2 D.L1 D.L2 D.S).subtype (f112P2 D.L1 D.L2 D.S).subtype_injective h3
  rwa [Subgroup.map_subgroupOf_eq_of_le hLβ] at h4

theorem f112ll_eq_of_isLin2Type_oTwoPrime_P1' (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (h1 : IsL2Quot m (oTwoQuot ↥L1)) (h2 : IsL2Quot n (oTwoQuot ↥L2)) {f : ℕ} (hf : 2 ≤ f)
    (hL : IsLin2Type (oTwoPrime (f112saP1' L1 L2 S)) f) : f = m := by
  have hPSLf : IsPSL 2 2 f (oTwoQuot ↥(oTwoPrime (f112saP1' L1 L2 S))) :=
    isPSL_of_isLin2Type1521 hf hL
  have hPSLm : IsPSL 2 2 m (oTwoQuot ↥(oTwoPrime (f112saP1' L1 L2 S))) := by
    obtain ⟨e⟩ := f112ll_isL2Quot_oTwoPrime_P1' hF hm hn h1 h2
    exact CFSG.Quasithin.E2.isPSL_two_two_of_mulEquiv_psl2 hm e
  exact CFSG.Quasithin.Vol2.Ch11.SecA.C10KH.eq_of_isPSL_two_two hPSLf hPSLm

theorem f112ll_eq_of_isLin2Type_oTwoPrime_P2' (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (h1 : IsL2Quot m (oTwoQuot ↥L1)) (h2 : IsL2Quot n (oTwoQuot ↥L2)) {f : ℕ} (hf : 2 ≤ f)
    (hL : IsLin2Type (oTwoPrime (f112saP2' L1 L2 S)) f) : f = n := by
  have hPSLf : IsPSL 2 2 f (oTwoQuot ↥(oTwoPrime (f112saP2' L1 L2 S))) :=
    isPSL_of_isLin2Type1521 hf hL
  have hPSLn : IsPSL 2 2 n (oTwoQuot ↥(oTwoPrime (f112saP2' L1 L2 S))) := by
    obtain ⟨e⟩ := f112ll_isL2Quot_oTwoPrime_P2' hF hm hn h1 h2
    exact CFSG.Quasithin.E2.isPSL_two_two_of_mulEquiv_psl2 hn e
  exact CFSG.Quasithin.Vol2.Ch11.SecA.C10KH.eq_of_isPSL_two_two hPSLf hPSLn

theorem f112ll_isElemAbelian_pCoreOf_P1'_of_tree (hF : F112HypW L1 L2 S) (hm : 2 ≤ m)
    (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1)) (h2 : IsL2Quot n (oTwoQuot ↥L2))
    {X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S)}
    (hX0 : X.vert 0 = baseA (f112Gold L1 L2 S)) (hX1 : X.vert 1 = baseB (f112Gold L1 L2 S))
    (hE : IsElemAbelian 2 (pCoreOf 2 (X.L 0))) :
    IsElemAbelian 2 (pCoreOf 2 (oTwoPrime (f112saP1' L1 L2 S))) := by
  have hR : Hyp111R L1 L2 S := hyp111R_of_isL2Quot (by omega) (by omega) hF.1 h1 h2
  let D := f112EOddBaseEdgeData hF hR X hX0 hX1
  have hQα : pCoreOf 2 (oTwoPrime D.Pα) ≤ f112P1 D.L1 D.L2 D.S :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 (oTwoPrime D.Pα)).trans
      ((oTwoPrime_le D.Pα).trans D.le_Pα)
  exact (isElemAbelian_of_map_iff (L1 := D.L1) (L2 := D.L2) (S := D.S) (E := D.E) hQα
    D.pCoreOf_L_zero_map).mp hE

theorem f112ll_isElemAbelian_pCoreOf_P2'_of_tree (hF : F112HypW L1 L2 S) (hm : 2 ≤ m)
    (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1)) (h2 : IsL2Quot n (oTwoQuot ↥L2))
    {X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S)}
    (hX0 : X.vert 0 = baseA (f112Gold L1 L2 S)) (hX1 : X.vert 1 = baseB (f112Gold L1 L2 S))
    (hE : IsElemAbelian 2 (pCoreOf 2 (X.L 1))) :
    IsElemAbelian 2 (pCoreOf 2 (oTwoPrime (f112saP2' L1 L2 S))) := by
  have hR : Hyp111R L1 L2 S := hyp111R_of_isL2Quot (by omega) (by omega) hF.1 h1 h2
  let D := f112EOddBaseEdgeData hF hR X hX0 hX1
  have hQβ : pCoreOf 2 (oTwoPrime D.Pβ) ≤ f112P2 D.L1 D.L2 D.S :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 (oTwoPrime D.Pβ)).trans
      ((oTwoPrime_le D.Pβ).trans D.le_Pβ)
  exact (isElemAbelian_of_map_iff_ofB (L1 := D.L1) (L2 := D.L2) (S := D.S) (E := D.E) hQβ
    D.pCoreOf_L_one_map).mp hE

theorem f112ll_commutator_pCoreOf_P1'_of_tree (hF : F112HypW L1 L2 S) (hm : 2 ≤ m)
    (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1)) (h2 : IsL2Quot n (oTwoQuot ↥L2))
    {X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S)}
    (hX0 : X.vert 0 = baseA (f112Gold L1 L2 S)) (hX1 : X.vert 1 = baseB (f112Gold L1 L2 S))
    (hc : ⁅pCoreOf 2 (X.L 0), X.L 0⁆ = pCoreOf 2 (X.L 0)) :
    ⁅pCoreOf 2 (oTwoPrime (f112saP1' L1 L2 S)), oTwoPrime (f112saP1' L1 L2 S)⁆ =
      pCoreOf 2 (oTwoPrime (f112saP1' L1 L2 S)) := by
  have hR : Hyp111R L1 L2 S := hyp111R_of_isL2Quot (by omega) (by omega) hF.1 h1 h2
  let D := f112EOddBaseEdgeData hF hR X hX0 hX1
  have hLα : oTwoPrime D.Pα ≤ f112P1 D.L1 D.L2 D.S := (oTwoPrime_le D.Pα).trans D.le_Pα
  have hQα : pCoreOf 2 (oTwoPrime D.Pα) ≤ f112P1 D.L1 D.L2 D.S :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 (oTwoPrime D.Pα)).trans hLα
  have hc' : ⁅pCoreOf 2 (D.X.L 0), D.X.L 0⁆ = pCoreOf 2 (D.X.L 0) := hc
  have hcomm : f112OfA D.L1 D.L2 D.S
      (⁅pCoreOf 2 (oTwoPrime D.Pα), oTwoPrime D.Pα⁆) =
      f112OfA D.L1 D.L2 D.S (pCoreOf 2 (oTwoPrime D.Pα)) := by
    rw [← f112_ofA_commutator D.L1 D.L2 D.S hQα hLα]
    calc ⁅f112OfA D.L1 D.L2 D.S (pCoreOf 2 (oTwoPrime D.Pα)),
          f112OfA D.L1 D.L2 D.S (oTwoPrime D.Pα)⁆
        = ⁅(pCoreOf 2 (D.X.L 0)).map D.E.subtype, (D.X.L 0).map D.E.subtype⁆ := by
          rw [← D.pCoreOf_L_zero_map, ← D.L_zero_map]
      _ = (⁅pCoreOf 2 (D.X.L 0), D.X.L 0⁆).map D.E.subtype :=
          (Subgroup.map_commutator (f := D.E.subtype)
            (H₁ := pCoreOf 2 (D.X.L 0)) (H₂ := D.X.L 0)).symm
      _ = (pCoreOf 2 (D.X.L 0)).map D.E.subtype := by rw [hc']
      _ = f112OfA D.L1 D.L2 D.S (pCoreOf 2 (oTwoPrime D.Pα)) := D.pCoreOf_L_zero_map
  have hsub : (⁅pCoreOf 2 (oTwoPrime D.Pα), oTwoPrime D.Pα⁆).subgroupOf
      (f112P1 D.L1 D.L2 D.S) =
      (pCoreOf 2 (oTwoPrime D.Pα)).subgroupOf (f112P1 D.L1 D.L2 D.S) :=
    Subgroup.map_injective (f := (f112Gold D.L1 D.L2 D.S).ofA)
      (f112Gold D.L1 D.L2 D.S).ofA_injective hcomm
  have hEq : ⁅pCoreOf 2 (oTwoPrime D.Pα), oTwoPrime D.Pα⁆ =
      pCoreOf 2 (oTwoPrime D.Pα) := by
    have hinf := Subgroup.subgroupOf_inj.mp hsub
    rwa [inf_eq_left.mpr (Subgroup.commutator_le_of_le hQα hLα),
      inf_eq_left.mpr hQα] at hinf
  exact hEq

theorem f112ll_commutator_pCoreOf_P2'_of_tree (hF : F112HypW L1 L2 S) (hm : 2 ≤ m)
    (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1)) (h2 : IsL2Quot n (oTwoQuot ↥L2))
    {X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S)}
    (hX0 : X.vert 0 = baseA (f112Gold L1 L2 S)) (hX1 : X.vert 1 = baseB (f112Gold L1 L2 S))
    (hc : ⁅pCoreOf 2 (X.L 1), X.L 1⁆ = pCoreOf 2 (X.L 1)) :
    ⁅pCoreOf 2 (oTwoPrime (f112saP2' L1 L2 S)), oTwoPrime (f112saP2' L1 L2 S)⁆ =
      pCoreOf 2 (oTwoPrime (f112saP2' L1 L2 S)) := by
  have hR : Hyp111R L1 L2 S := hyp111R_of_isL2Quot (by omega) (by omega) hF.1 h1 h2
  let D := f112EOddBaseEdgeData hF hR X hX0 hX1
  have hLβ : oTwoPrime D.Pβ ≤ f112P2 D.L1 D.L2 D.S := (oTwoPrime_le D.Pβ).trans D.le_Pβ
  have hQβ : pCoreOf 2 (oTwoPrime D.Pβ) ≤ f112P2 D.L1 D.L2 D.S :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 (oTwoPrime D.Pβ)).trans hLβ
  have hc' : ⁅pCoreOf 2 (D.X.L 1), D.X.L 1⁆ = pCoreOf 2 (D.X.L 1) := hc
  have hcomm : f112OfB D.L1 D.L2 D.S
      (⁅pCoreOf 2 (oTwoPrime D.Pβ), oTwoPrime D.Pβ⁆) =
      f112OfB D.L1 D.L2 D.S (pCoreOf 2 (oTwoPrime D.Pβ)) := by
    rw [← f112_ofB_commutator D.L1 D.L2 D.S hQβ hLβ]
    calc ⁅f112OfB D.L1 D.L2 D.S (pCoreOf 2 (oTwoPrime D.Pβ)),
          f112OfB D.L1 D.L2 D.S (oTwoPrime D.Pβ)⁆
        = ⁅(pCoreOf 2 (D.X.L 1)).map D.E.subtype, (D.X.L 1).map D.E.subtype⁆ := by
          rw [← D.pCoreOf_L_one_map, ← D.L_one_map]
      _ = (⁅pCoreOf 2 (D.X.L 1), D.X.L 1⁆).map D.E.subtype :=
          (Subgroup.map_commutator (f := D.E.subtype)
            (H₁ := pCoreOf 2 (D.X.L 1)) (H₂ := D.X.L 1)).symm
      _ = (pCoreOf 2 (D.X.L 1)).map D.E.subtype := by rw [hc']
      _ = f112OfB D.L1 D.L2 D.S (pCoreOf 2 (oTwoPrime D.Pβ)) := D.pCoreOf_L_one_map
  have hsub : (⁅pCoreOf 2 (oTwoPrime D.Pβ), oTwoPrime D.Pβ⁆).subgroupOf
      (f112P2 D.L1 D.L2 D.S) =
      (pCoreOf 2 (oTwoPrime D.Pβ)).subgroupOf (f112P2 D.L1 D.L2 D.S) :=
    Subgroup.map_injective (f := (f112Gold D.L1 D.L2 D.S).ofB)
      (f112Gold D.L1 D.L2 D.S).ofB_injective hcomm
  have hEq : ⁅pCoreOf 2 (oTwoPrime D.Pβ), oTwoPrime D.Pβ⁆ =
      pCoreOf 2 (oTwoPrime D.Pβ) := by
    have hinf := Subgroup.subgroupOf_inj.mp hsub
    rwa [inf_eq_left.mpr (Subgroup.commutator_le_of_le hQβ hLβ),
      inf_eq_left.mpr hQβ] at hinf
  exact hEq

end CFSG.Quasithin.F112R.St84
