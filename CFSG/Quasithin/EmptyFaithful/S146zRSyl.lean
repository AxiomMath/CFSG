module

public import CFSG.Quasithin.EmptyFaithful.S146zRL3Case

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

section Sylow

variable {X : Type} [Group X] [Finite X]

theorem q_card_of_isSylowTwoOf {P N : Subgroup X} (h : IsSylowTwoOf P N) :
    Nat.card P = 2 ^ (Nat.card N).factorization 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP2 : IsPGroup 2 ↥(P.subgroupOf N) :=
    h.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe h.1).symm
  have := Sylow.card_eq_multiplicity (hP2.toSylow h.2.2)
  rw [IsPGroup.toSylow_coe] at this
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.1).toEquiv] at this

variable {N₁ N₂ : Subgroup X} {ŝ : X}

theorem q_sylow_sup_eq (hF : CaseIFacts N₁ N₂ ŝ) {P : Subgroup X}
    (hP : IsSylowTwoOf P (N₁ ⊔ N₂)) : P = (P ⊓ N₁) ⊔ (P ⊓ N₂) := by
  have h1 : IsSylowTwoOf (P ⊓ N₁) N₁ :=
    B6.isSylowTwoOf_inf_normal hP le_sup_left (q_sup_le_normalizer hF)
  have hN₂ : N₁ ⊔ N₂ ≤ Subgroup.normalizer (N₂ : Set X) :=
    sup_le (q_normalizes_of_comm hF.comm) Subgroup.le_normalizer
  have h2 : IsSylowTwoOf (P ⊓ N₂) N₂ := B6.isSylowTwoOf_inf_normal hP le_sup_right hN₂
  have hcomm : ∀ a ∈ P ⊓ N₁, ∀ b ∈ P ⊓ N₂, a * b = b * a := fun a ha b hb =>
    hF.comm a ha.2 b hb.2
  have hdisj : Disjoint (P ⊓ N₁) (P ⊓ N₂) := by
    rw [Subgroup.disjoint_def]
    intro x hx hy
    have : x ∈ N₁ ⊓ N₂ := ⟨hx.2, hy.2⟩
    rw [hF.disj, Subgroup.mem_bot] at this
    exact this
  have hle : (P ⊓ N₁) ⊔ (P ⊓ N₂) ≤ P := sup_le inf_le_left inf_le_left
  have hP' := q_card_of_isSylowTwoOf hP
  have h1' := q_card_of_isSylowTwoOf h1
  have h2' := q_card_of_isSylowTwoOf h2
  rw [q_card_sup_pair hF, Nat.factorization_pow] at hP'
  rw [q_card_conj_eq hF] at h2'
  have hcard : Nat.card P ≤ Nat.card ↥((P ⊓ N₁) ⊔ (P ⊓ N₂)) := by
    rw [SBc15.card_sup_eq_mul_of_commute hcomm hdisj, h1', h2', hP', ← pow_add]
    simp [two_mul]
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

theorem q_inf_sup_eq (hF : CaseIFacts N₁ N₂ ŝ) {T' : Subgroup X}
    (hT' : IsSylowTwoOf T' (⊤ : Subgroup X)) :
    T' ⊓ (N₁ ⊔ N₂) = (T' ⊓ N₁) ⊔ (T' ⊓ N₂) := by
  have hSyl0 : IsSylowTwoOf (T' ⊓ (N₁ ⊔ N₂)) (N₁ ⊔ N₂) :=
    B6.isSylowTwoOf_inf_normal hT' le_top
      (le_top.trans (Subgroup.normalizer_eq_top_iff.mpr hF.normal).ge)
  have h := q_sylow_sup_eq hF hSyl0
  have e1 : T' ⊓ (N₁ ⊔ N₂) ⊓ N₁ = T' ⊓ N₁ := by
    rw [inf_assoc, inf_eq_right.mpr (le_sup_left : N₁ ≤ N₁ ⊔ N₂)]
  have e2 : T' ⊓ (N₁ ⊔ N₂) ⊓ N₂ = T' ⊓ N₂ := by
    rw [inf_assoc, inf_eq_right.mpr (le_sup_right : N₂ ≤ N₁ ⊔ N₂)]
  rw [e1, e2] at h
  exact h

theorem q_isSylowTwoOf_inf_fst (hF : CaseIFacts N₁ N₂ ŝ) {T' : Subgroup X}
    (hT' : IsSylowTwoOf T' (⊤ : Subgroup X)) : IsSylowTwoOf (T' ⊓ N₁) N₁ := by
  have h0 : IsSylowTwoOf (T' ⊓ (N₁ ⊔ N₂)) (N₁ ⊔ N₂) :=
    B6.isSylowTwoOf_inf_normal hT' le_top
      (le_top.trans (Subgroup.normalizer_eq_top_iff.mpr hF.normal).ge)
  have := B6.isSylowTwoOf_inf_normal h0 (le_sup_left : N₁ ≤ N₁ ⊔ N₂) (q_sup_le_normalizer hF)
  rwa [inf_assoc, inf_eq_right.mpr (le_sup_left : N₁ ≤ N₁ ⊔ N₂)] at this

theorem q_isSylowTwoOf_inf_snd (hF : CaseIFacts N₁ N₂ ŝ) {T' : Subgroup X}
    (hT' : IsSylowTwoOf T' (⊤ : Subgroup X)) : IsSylowTwoOf (T' ⊓ N₂) N₂ := by
  have h0 : IsSylowTwoOf (T' ⊓ (N₁ ⊔ N₂)) (N₁ ⊔ N₂) :=
    B6.isSylowTwoOf_inf_normal hT' le_top
      (le_top.trans (Subgroup.normalizer_eq_top_iff.mpr hF.normal).ge)
  have hN₂ : N₁ ⊔ N₂ ≤ Subgroup.normalizer (N₂ : Set X) :=
    sup_le (q_normalizes_of_comm hF.comm) Subgroup.le_normalizer
  have := B6.isSylowTwoOf_inf_normal h0 (le_sup_right : N₂ ≤ N₁ ⊔ N₂) hN₂
  rwa [inf_assoc, inf_eq_right.mpr (le_sup_right : N₂ ≤ N₁ ⊔ N₂)] at this

noncomputable def q_equiv_snd (hF : CaseIFacts N₁ N₂ ŝ) : ↥N₂ ≃* ↥N₁ :=
  (MulEquiv.subgroupCongr hF.conj).trans
    (N₁.equivMapOfInjective (MulAut.conj ŝ).toMonoidHom (MulAut.conj ŝ).injective).symm

end Sylow

end CFSG.Quasithin
