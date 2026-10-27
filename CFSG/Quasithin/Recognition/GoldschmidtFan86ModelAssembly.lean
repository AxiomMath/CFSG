module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86ModelLattice
public import CFSG.Quasithin.Recognition.GoldschmidtFan86ModelSylow
public import CFSG.Quasithin.Recognition.GoldschmidtFan86ModelFrob
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Hyp

public section

namespace CFSG.Quasithin.Fan86.Model

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

theorem normalizer_subgroupOf_le {N : Type*} [Group N] {S P : Subgroup N} (hSP : S ≤ P)
    (hnorm : Subgroup.normalizer (S : Set N) ≤ S) :
    Subgroup.normalizer ((S.subgroupOf P : Subgroup ↥P) : Set ↥P) ≤ S.subgroupOf P := by
  intro x hx
  have hx' : x ∈ (Subgroup.normalizer (S : Set N)).subgroupOf P := by
    rw [Subgroup.subgroupOf_normalizer_eq hSP]
    exact hx
  exact hnorm hx'

theorem hyp53_of_lattice {N : Type} [Group N] [Finite N] (L : TwoLocalLattice N) {a : ℕ}
    (hS : Nat.card L.S = 2 ^ a) (h₁ : Nat.card L.P₁ = 5 * 2 ^ a)
    (h₂ : Nat.card L.P₂ = 3 * 2 ^ a) (hc₁ : CharTwo L.P₁) (hc₂ : CharTwo L.P₂)
    (hO₁ : 4 * Nat.card (pCoreOf 2 L.P₁) = 2 ^ a) :
    Hyp53 (GoldAmalgam.ofSubgroupPair L.P₁ L.P₂) ∧ Nat.card ↥(L.P₁ ⊓ L.P₂) = 2 ^ a ∧
      2 * Nat.card (pCoreOf 2 L.P₂) = 2 ^ a := by
  have hq₁ : Nat.card (oTwoQuot ↥L.P₁) = 20 := by
    have hmul := card_oTwoQuot_mul ↥L.P₁
    rw [← card_pCoreOf, h₁] at hmul
    have hpos : 0 < Nat.card (pCoreOf 2 L.P₁) := Nat.card_pos
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [hmul, ← hO₁]
    ring
  have hSP₂ : IsPGroup 2 (L.S.subgroupOf L.P₂) :=
    L.sylow.1.comap_of_injective L.P₂.subtype L.P₂.subtype_injective
  have hcardS₂ : Nat.card (L.S.subgroupOf L.P₂) = 2 ^ a :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe L.S_le_P₂).toEquiv).trans hS
  have hidx₂ : (L.S.subgroupOf L.P₂).index = 3 := by
    have h := Subgroup.card_mul_index (L.S.subgroupOf L.P₂)
    rw [hcardS₂, h₂] at h
    exact Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num : 0 < 2) a) (h.trans (mul_comm _ _))
  obtain ⟨hcore₂, ⟨e₂⟩⟩ := pCore_index_three hSP₂ hidx₂
    (normalizer_subgroupOf_le L.S_le_P₂ L.normS)
  refine ⟨⟨inferInstance, inferInstance, faithful L, isPGroup_inf L, index_left L hS h₁,
    index_right L hS h₂, charTwo_top_of_charTwo _ hc₁, charTwo_top_of_charTwo _ hc₂,
    Or.inr (nonempty_oTwoQuot_sz_zero hq₁), isL2Quot_one_iff_perm3.2 ⟨e₂⟩⟩, ?_, ?_⟩
  · rw [inf_eq L, hS]
  · rw [card_pCoreOf, hcore₂, hcardS₂]

theorem inf_centralizer_subgroupOf_le {G : Type*} [Group G] {M X J : Subgroup G} (hJM : J ≤ M)
    (h : X ⊓ Subgroup.centralizer (J : Set G) ≤ J) :
    X.subgroupOf M ⊓ Subgroup.centralizer ((J.subgroupOf M : Subgroup ↥M) : Set ↥M) ≤
      J.subgroupOf M := by
  intro x hx
  obtain ⟨hxX, hxC⟩ := hx
  refine h ⟨hxX, Subgroup.mem_centralizer_iff.2 fun j hj => ?_⟩
  exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hxC ⟨j, hJM hj⟩ hj)

theorem isYAmalgamPair_lattice {N : Type*} [Group N] (L : TwoLocalLattice N) :
    IsYAmalgamPair L.S L.P₁ L.P₂ :=
  L.isYAmalgamPair_S L.isMaximalTwoLocal_P₁ L.isMaximalTwoLocal_P₂
    (fun h => L.P₁_not_le_P₂ h.le) L.S_le_P₁ L.S_le_P₂

end CFSG.Quasithin.Fan86.Model
