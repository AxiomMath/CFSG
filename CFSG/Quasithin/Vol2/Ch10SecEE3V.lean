module

public import CFSG.Quasithin.Vol2.Ch10SecEE3Alt
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch10SecB6C23
public import CFSG.Quasithin.Vol2.Ch10SecEBlock

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecE

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem relIndex_sup_eq_relIndex [Finite G] {B R : Subgroup G}
    (h : R ≤ Subgroup.normalizer (B : Set G)) : R.relIndex (B ⊔ R) = R.relIndex B := by
  have : (B.subgroupOf R).Normal := Subgroup.normal_subgroupOf_of_le_normalizer h
  have : (B.subgroupOf (R ⊔ B)).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer h
  have h4 : Nat.card (B ⊔ R : Subgroup G) * Nat.card (B ⊓ R : Subgroup G) =
      Nat.card B * Nat.card R := by
    have e := Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient R B h).toEquiv
    have h1 := Subgroup.relIndex_mul_card B (R ⊔ B)
    have h2 := Subgroup.relIndex_mul_card B R
    rw [inf_eq_left.mpr (le_sup_right : B ≤ R ⊔ B)] at h1
    have e' : B.relIndex R = B.relIndex (R ⊔ B) := e
    rw [sup_comm, ← h1, ← h2, e']
    ring
  have h1 := Subgroup.relIndex_mul_card R (B ⊔ R)
  have h3 := Subgroup.relIndex_mul_card R B
  rw [inf_eq_left.mpr (le_sup_right : R ≤ B ⊔ R)] at h1
  rw [inf_comm] at h3
  have hpos : 0 < Nat.card R * Nat.card (B ⊓ R : Subgroup G) :=
    Nat.mul_pos Nat.card_pos Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right hpos
  calc R.relIndex (B ⊔ R) * (Nat.card R * Nat.card (B ⊓ R : Subgroup G))
      = Nat.card (B ⊔ R : Subgroup G) * Nat.card (B ⊓ R : Subgroup G) := by rw [← h1]; ring
    _ = R.relIndex B * (Nat.card R * Nat.card (B ⊓ R : Subgroup G)) := by rw [h4, ← h3]; ring

theorem isSylowTwoOf_sup_of_inf [Finite G] {B R : Subgroup G}
    (hRN : R ≤ Subgroup.normalizer (B : Set G)) (hR : IsPGroup 2 R)
    (hsyl : IsSylowTwoOf (R ⊓ B) B) : IsSylowTwoOf R (B ⊔ R) := by
  refine ⟨le_sup_right, hR, ?_⟩
  show ¬ 2 ∣ R.relIndex (B ⊔ R)
  rw [relIndex_sup_eq_relIndex hRN, ← Subgroup.inf_relIndex_right]
  exact hsyl.2.2

variable [Finite G] {T L I : Subgroup G}

theorem isSylowTwoOf_T1_sup (hyp : Hyp10 G T L I) :
    IsSylowTwoOf (Ch10.T1 T L) (L ⊔ Ch10.T1 T L) := by
  refine isSylowTwoOf_sup_of_inf inf_le_right (hyp.fsu.sylow.1.to_le inf_le_left) ?_
  have e : Ch10.T1 T L ⊓ L = T ⊓ L :=
    le_antisymm (inf_le_inf_right _ inf_le_left)
      (le_inf (le_inf inf_le_left (inf_le_right.trans Subgroup.le_normalizer)) inf_le_right)
  rw [e]
  exact SecA.isSylowTwoOf_inf hyp.fsu.maximal.1

theorem fsuVM_le_pCoreOf (hyp : Hyp10 G T L I) : fsuVM T L I ≤ pCoreOf 2 (fsuL0 T L ⊔ T) :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ((SecA.fsuVM_le_T hyp).trans le_sup_right)
    (fsuL0_sup_le_normalizer T L I) (SecA.isPGroup_fsuVM hyp)

theorem pCoreOf_L0T_le_pCoreOf (hyp : Hyp10 G T L I) :
    pCoreOf 2 (fsuL0 T L ⊔ T) ≤ pCoreOf 2 (L ⊔ Ch10.T1 T L) := by
  have h1 : pCoreOf 2 (fsuL0 T L ⊔ T) ≤ Ch10.T1 T L := SecB.pCoreOf_L0T_le_T1 hyp
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (h1.trans le_sup_right) ?_
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  exact (sup_le ((SecA.le_fsuL0 T L).trans le_sup_left)
    ((inf_le_left : Ch10.T1 T L ≤ T).trans le_sup_right)).trans
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)

omit [Finite G] in
theorem T1_le_normalizer_blockU : Ch10.T1 T L ≤ Subgroup.normalizer (blockU L : Set G) :=
  SecA.le_normalizer_commutator
    (inf_le_right.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
    inf_le_right

theorem blockU_eq_fsuUL (h113 : ASInputs.AS_C_1_13) (hyp : Hyp10 G T L I)
    (h2 : Ch10.Case10_1_1Two T L I) (hb : IsShort2 L ∧ IsAltType L 5) :
    blockU L = fsuUL T L I ∧
      pCoreOf 2 (L ⊔ Ch10.T1 T L) = fsuUL T L I ⊔ (Ch10.T1 T L ⊓ Subgroup.centralizer (L : Set G)) ∧
      fsuUL T L I ⊓ (Ch10.T1 T L ⊓ Subgroup.centralizer (L : Set G)) = ⊥ := by
  obtain ⟨hO, hinf, ⟨_, hU⟩, -, -, -⟩ :=
    (h113 G L (Ch10.T1 T L) (isSylowTwoOf_T1_sup hyp) inf_le_right hb.1).2.1 5 (Or.inr rfl) hb.2
  set C := Ch10.T1 T L ⊓ Subgroup.centralizer (L : Set G) with hC
  have hLU : L ≤ Subgroup.normalizer (blockU L : Set G) :=
    SecA.le_normalizer_commutator (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
      Subgroup.le_normalizer
  have hle : fsuUL T L I ≤ blockU L := by
    have h1 : fsuVM T L I ≤ blockU L ⊔ C := by
      rw [← hO]
      exact (fsuVM_le_pCoreOf hyp).trans (pCoreOf_L0T_le_pCoreOf hyp)
    have h3 : ⁅L, blockU L ⊔ C⁆ ≤ blockU L := by
      refine commutator_sup_le (Subgroup.le_normalizer_iff_commutator_le_right.mp hLU) ?_
        Subgroup.le_normalizer (inf_le_left.trans T1_le_normalizer_blockU)
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer.mpr]
      · exact bot_le
      · rw [Subgroup.le_centralizer_iff]
        exact inf_le_right
    calc fsuUL T L I = ⁅L, fsuVM T L I⁆ := Subgroup.commutator_comm _ _
      _ ≤ ⁅L, blockU L ⊔ C⁆ := Subgroup.commutator_mono le_rfl h1
      _ ≤ blockU L := h3
  obtain ⟨-, _, hV₁⟩ := h2
  have hc1 := card_of_alternatingNatural_five hV₁
  have hc2 := card_of_alternatingNatural_five hU
  have heq : fsuUL T L I = blockU L := Subgroup.eq_of_le_of_card_ge hle (by rw [hc1, hc2])
  rw [← heq] at hO hinf
  exact ⟨heq.symm, hO, hinf⟩

end CFSG.Quasithin.Vol2.Ch10.SecE
