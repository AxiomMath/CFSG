module

public import CFSG.Quasithin.Recognition.St84.AppTreeSAE
import CFSG.Quasithin.Recognition.St84.AppTreeSAP1
import CFSG.Quasithin.Recognition.St84.Gen.L2RankOne
import CFSG.Quasithin.Recognition.St84.Gen.TreeEOdd

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.LieType.BorelTits CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.Quasithin.F112R CFSG.Quasithin.St84 CFSG.Quasithin.Fan86 CFSG.Quasithin.Fan86.Univ
open scoped Pointwise

variable {H : Type} [Group H] [Finite H]

theorem f112sl_EOdd_inf_ofA_range {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) :
    f112EOdd L1 L2 S ⊓ (f112Gold L1 L2 S).ofA.range =
      ((oTwoRes L1 ⊔ (oTwoRes L2 ⊓ bigB L1 L2 S)).subgroupOf (f112P1 L1 L2 S)).map
        (f112Gold L1 L2 S).ofA := by
  simpa [f112saP1', f112saX2] using
    f112_EOdd_inf_ofA_range_of_hyp111R hF.toW
      (Hyp111R.of_hyp111 rankOneListedFacts hF.1)

theorem f112sl_EOdd_inf_ofB_range {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) :
    f112EOdd L1 L2 S ⊓ (f112Gold L1 L2 S).ofB.range =
      ((oTwoRes L2 ⊔ (oTwoRes L1 ⊓ bigB L1 L2 S)).subgroupOf (f112P2 L1 L2 S)).map
        (f112Gold L1 L2 S).ofB := by
  simpa [f112saP2', f112saX1] using
    f112_EOdd_inf_ofB_range_of_hyp111R hF.toW
      (Hyp111R.of_hyp111 rankOneListedFacts hF.1)

theorem f112sl_EOdd_inf_ofA_range_inf_ofB_range
    {L1 L2 S : Subgroup H} (hF : F112Hyp L1 L2 S) :
    f112EOdd L1 L2 S ⊓ (f112Gold L1 L2 S).ofA.range ⊓ (f112Gold L1 L2 S).ofB.range =
      ((oTwoRes L1 ⊓ bigB L1 L2 S ⊔ (oTwoRes L2 ⊓ bigB L1 L2 S)).subgroupOf
        (f112P1 L1 L2 S)).map (f112Gold L1 L2 S).ofA := by
  simpa [f112saK, f112saX1, f112saX2] using
    f112_EOdd_inf_ofA_range_inf_ofB_range_of_hyp111R hF.toW
      (Hyp111R.of_hyp111 rankOneListedFacts hF.1)

theorem f112sl_le_sup_pCoreOf_P1 {L1 L2 S : Subgroup H}
    {n : ℕ} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) {R : Subgroup H}
    (hR : IsPGroup 2 R) (hRB : R ≤ bigB L1 L2 S)
    (hBR : bigB L1 L2 S ≤ Subgroup.normalizer (R : Set H)) :
    R ≤ L1 ⊔ pCoreOf 2 (f112P1 L1 L2 S) := by
  have hR111 : Hyp111R L1 L2 S :=
    hyp111R_of_isL2Quot (m := 1) (n := n) (by norm_num) (by omega) hF.1
      (isL2Quot_of_VS3 h1) h2
  have hLidx : (pCoreOf 2 L1).relIndex L1 = 6 := by
    have h3 : (pCoreOf 2 L1).subgroupOf L1 = CFSG.pCore 2 ↥L1 := by
      ext x
      show (x : H) ∈ (CFSG.pCore 2 ↥L1).map L1.subtype ↔ x ∈ CFSG.pCore 2 ↥L1
      exact Subgroup.mem_map_iff_mem L1.subtype_injective
    rw [Subgroup.relIndex, h3, Subgroup.index_eq_card]
    exact f112sa_card_oTwoQuot_vs3 h1
  have hB1 : IsPGroup 2 ↥(L1 ⊓ bigB L1 L2 S) := by
    rw [F1.inf_bigB_eq_borelOf hR111, f112sa_borelOf_left_eq hF h1]
    exact hF.1.h1.sylow.2.1
  exact isPGroup_le_sup_pCoreOf_of_relIndex_three
    (L := L1) (B := bigB L1 L2 S) (R := R)
    (F1.bigB_le_normalizer_left hR111).1
    (F1.pCoreOf_parabolic_le_bigB hR111)
    (by
      have h := f112sa_relIndex_left hF h1 hn h2
      rw [f112_inf_eq_bigB_of_hyp111R hR111] at h
      simpa using h)
    hLidx hB1 hRB hR hBR

theorem f112sl_pCoreOf_X2_le_sup_P1 {L1 L2 S : Subgroup H}
    {n : ℕ} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    pCoreOf 2 (oTwoRes L2 ⊓ bigB L1 L2 S) ≤ L1 ⊔ pCoreOf 2 (f112P1 L1 L2 S) := by
  have hR111 : Hyp111R L1 L2 S :=
    hyp111R_of_isL2Quot (m := 1) (n := n) (by norm_num) (by omega) hF.1
      (isL2Quot_of_VS3 h1) h2
  have hBL2 : bigB L1 L2 S ≤ Subgroup.normalizer (L2 : Set H) :=
    (F1.bigB_le_normalizer_left hR111).2
  have hBo2 : bigB L1 L2 S ≤ Subgroup.normalizer (oTwoRes L2 : Set H) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    show conjSub b (oTwoRes L2) = oTwoRes L2
    rw [conjSub_oTwoRes, F1.conjSub_eq_of_mem_normalizer (hBL2 hb)]
  have hBX2 : bigB L1 L2 S ≤
      Subgroup.normalizer ((oTwoRes L2 ⊓ bigB L1 L2 S : Subgroup H) : Set H) :=
    (le_inf hBo2 Subgroup.le_normalizer).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hX2B : oTwoRes L2 ⊓ bigB L1 L2 S ≤ bigB L1 L2 S := inf_le_right
  have hRB : pCoreOf 2 (oTwoRes L2 ⊓ bigB L1 L2 S) ≤ bigB L1 L2 S :=
    (pCoreOf_le 2 _).trans hX2B
  have hBR : bigB L1 L2 S ≤
      Subgroup.normalizer (pCoreOf 2 (oTwoRes L2 ⊓ bigB L1 L2 S) : Set H) :=
    hBX2.trans (normalizer_le_normalizer_pCoreOf 2 _)
  exact f112sl_le_sup_pCoreOf_P1 hF h1 hn h2 (pCoreOf_isPGroup 2 _) hRB hBR

end CFSG.Quasithin.F112R.St84
