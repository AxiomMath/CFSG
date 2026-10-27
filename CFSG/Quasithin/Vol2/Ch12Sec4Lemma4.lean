module

public import CFSG.Quasithin.Vol2.Ch12Sec4L5Off
public import CFSG.Quasithin.Vol2.Ch12Sec4L5Fus

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped IsMulCommutative

theorem lemma12_4_4_of
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3) (hpre : Pre1242)
    (h3228 : Stmt3_2_2_eight) (h1229 : Stmt12_2_9) (h12210 : Stmt12_2_10)
    (h1241 : Lemma12_4_1) (h42 : AsB42) (h63 : ASInputs.AS_E_6_3) : Lemma12_4_4 := by
  intro G _ _ T L V hcx h5
  obtain ⟨z, hf⟩ := Cx5Facts.of h1222 hpre hcx h5
  have := hf.comm
  have hs := hf.one_lt_sParam h331 h1222 h323 h3228 h12210 h1229 hpre h42 h63 hcx h5
  obtain ⟨g, hg1, hg2⟩ := h1241 G T L V hcx.hyp (lemma12_4_3_one_of_pre hpre G T L V hcx)
    hf.isElemAbelian hs
  obtain ⟨g', hg'1, hg'2, hg'T, hg'c⟩ := hf.exists_conj_le_T hcx hg1 hg2
  have hAN : CFSG.conjugate V g' ≤ Subgroup.normalizer (V : Set G) :=
    (le_normalizer_of_commutator_le hg'2).1
  have hA1 : autOn (CFSG.conjugate V g') V ≠ ⊥ := by
    intro h
    apply hg'1
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff]
    intro a ha
    have h1 : conjAct V ⟨a, hAN ha⟩ ∈ autOn (CFSG.conjugate V g') V :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 ha)
    rw [h, Subgroup.mem_bot] at h1
    exact A4.conjAct_eq_one_iff.1 h1
  have hr : Nat.card ↥V ≤ Nat.card (autOn (CFSG.conjugate V g') V) *
      Nat.card (fixV (autOn (CFSG.conjugate V g') V)) := by
    have h1 := card_autOn_eq_relIndex hAN
    have h2 := Subgroup.relIndex_mul_card
      (CFSG.conjugate V g' ⊓ Subgroup.centralizer (V : Set G)) (CFSG.conjugate V g')
    rw [show CFSG.conjugate V g' ⊓ Subgroup.centralizer (V : Set G) ⊓ CFSG.conjugate V g' =
        CFSG.conjugate V g' ⊓ Subgroup.centralizer (V : Set G) from inf_eq_left.2 inf_le_left,
      ← h1, card_conjugate_eq] at h2
    rw [fixV_autOn_eq hAN, card_subgroupOf_eq_card_inf, ← h2]
    exact Nat.mul_le_mul_left _ hg'c
  have hz := hf.mem_commutator_of_le_T h1222 h3228 h12210 h1229 hpre h42 hcx h5 hg'T
    (Cx5Conj.isElemAbelian_conjugate hf.isElemAbelian g') hA1 hr
  exact hg'1 (hf.commutator_eq_bot_of_mem h1222 h323 h3228 h12210 h1229 hpre h42 hcx h5
    (hg'2 hz).2)

end CFSG.Quasithin.H13
