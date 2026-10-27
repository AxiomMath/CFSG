module

public import CFSG.Quasithin.Recognition.GoldschmidtStatement
public import CFSG.Quasithin.Recognition.GoldschmidtSearch

public section

universe u

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

structure IsGoldschmidtTriple {D : Type*} [Group D] (G₁ G₂ : Subgroup D) : Prop where
  gen : G₁ ⊔ G₂ = ⊤
  quotient₁ : Nonempty (↥G₁ ⧸ pCore 2 ↥G₁ ≃* Equiv.Perm (Fin 3))
  quotient₂ : Nonempty (↥G₂ ⧸ pCore 2 ↥G₂ ≃* Equiv.Perm (Fin 3))
  sylow : ∃ T : Sylow 2 D, (T : Subgroup D) = G₁ ⊓ G₂

structure IsGoldschmidtAmalgam {D : Type*} [Group D] (G₁ G₂ : Subgroup D) : Prop
    extends IsGoldschmidtTriple G₁ G₂ where
  pCore_eq_bot : pCore 2 D = ⊥

namespace IsGoldschmidtTriple

variable {D : Type*} [Group D] [Finite D] {G₁ G₂ : Subgroup D}

omit [Finite D] in
theorem isPGroup_inf (h : IsGoldschmidtTriple G₁ G₂) : IsPGroup 2 ↥(G₁ ⊓ G₂) := by
  obtain ⟨T, hT⟩ := h.sylow
  have := T.isPGroup'
  rw [hT] at this
  exact this

theorem pCore_le_inf (h : IsGoldschmidtTriple G₁ G₂) : pCore 2 D ≤ G₁ ⊓ G₂ := by
  obtain ⟨T, hT⟩ := h.sylow
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : (pCore 2 D).Normal := pCore_normal 2
  rw [← hT]
  exact (pCore_isPGroup 2).le_sylow_of_normal T

omit [Finite D] in
theorem le_pCore_of_normal_le_inf (h : IsGoldschmidtTriple G₁ G₂) {N : Subgroup D} [N.Normal]
    (hN : N ≤ G₁ ⊓ G₂) : N ≤ pCore 2 D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_pCore 2 inferInstance ?_
  exact (h.isPGroup_inf).to_le hN

omit [Finite D] in
theorem symm (h : IsGoldschmidtTriple G₁ G₂) : IsGoldschmidtTriple G₂ G₁ where
  gen := by rw [sup_comm]; exact h.gen
  quotient₁ := h.quotient₂
  quotient₂ := h.quotient₁
  sylow := by rw [inf_comm]; exact h.sylow

theorem relIndex_inf_left (h : IsGoldschmidtTriple G₁ G₂) : (G₁ ⊓ G₂).relIndex G₁ = 3 := by
  obtain ⟨T, hT⟩ := h.sylow
  have hTle : (T : Subgroup D) ≤ G₁ := hT ▸ inf_le_left
  obtain ⟨e⟩ := h.quotient₁
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (pCore_isPGroup (G := ↥G₁) 2).exists_card_eq
  have hcardQ : Nat.card (↥G₁ ⧸ pCore 2 ↥G₁) = 6 := by
    rw [Nat.card_congr e.toEquiv, gold_card_perm_fin_three]
  have hG1 : Nat.card ↥G₁ = 3 * 2 ^ (k + 1) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (pCore 2 ↥G₁)
    rw [hcardQ, hk] at h1
    rw [h1]
    ring
  have hS := GoldAmalgam.sylow_index_eq_three_of_card (T.subtype hTle) (k + 1) hG1
  have hrel : (G₁ ⊓ G₂).relIndex G₁ = (↑(T.subtype hTle) : Subgroup ↥G₁).index := by
    unfold Subgroup.relIndex
    rw [← hT]
    rfl
  rw [hrel]
  exact hS

theorem relIndex_inf_right (h : IsGoldschmidtTriple G₁ G₂) : (G₁ ⊓ G₂).relIndex G₂ = 3 := by
  rw [inf_comm]
  exact h.symm.relIndex_inf_left

end IsGoldschmidtTriple

section Bound

variable {D : Type*} [Group D] [Finite D] {G₁ G₂ : Subgroup D}

theorem IsGoldschmidtTriple.isFaithful_ofSubgroupPair_iff (h : IsGoldschmidtTriple G₁ G₂) :
    (GoldAmalgam.ofSubgroupPair G₁ G₂).IsFaithful ↔ pCore 2 D = ⊥ := by
  rw [GoldAmalgam.ofSubgroupPair_isFaithful_iff G₁ G₂ h.gen]
  constructor
  · intro hf
    exact hf _ (pCore_normal 2) h.pCore_le_inf
  · intro hO N hN hle
    have := h.le_pCore_of_normal_le_inf hle
    rw [hO] at this
    exact le_bot_iff.mp this

theorem card_inf_le_of_goldschmidtEdgeBound (hb : GoldschmidtEdgeBoundSubgroups.{u}) {D : Type u}
    [Group D] [Finite D] {G₁ G₂ : Subgroup D} (h : IsGoldschmidtAmalgam G₁ G₂) :
    Nat.card ↥(G₁ ⊓ G₂) ≤ 2 ^ 7 :=
  hb D G₁ G₂ h.gen h.toIsGoldschmidtTriple.relIndex_inf_left
    h.toIsGoldschmidtTriple.relIndex_inf_right (fun N hN hle => by
      have := h.toIsGoldschmidtTriple.le_pCore_of_normal_le_inf hle
      rw [h.pCore_eq_bot] at this
      exact le_bot_iff.mp this)

end Bound

end CFSG.Quasithin
