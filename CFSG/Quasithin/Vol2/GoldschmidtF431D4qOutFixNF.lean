module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qStructSyl

public section

namespace CFSG.Quasithin.H13.F431.D4q.Out

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431.D4q.Struct CFSG.LieType.Chevalley
  CFSG.Blueprint CFSG.Blueprint.Chevalley

set_option linter.unusedSectionVars false


section Commute

variable {K : Type} [Field K] [Finite K] (σ : K ≃+* K)

theorem fieldActor_comm (δ δ' : K ≃+* K) :
    (fieldActor σ δ : MulAut (Cm σ)) * fieldActor σ δ' = fieldActor σ δ' * fieldActor σ δ := by
  rw [← fieldActor_mul, ← fieldActor_mul]
  exact congrArg (fieldActor σ) (RingEquiv.ext fun c => ringEquiv_comm_of_finite δ' δ c)

theorem commute_conj_fieldActor_iff (δ δ' : K ≃+* K) (y : Cm σ) :
    (fieldActor σ δ : MulAut (Cm σ)) * (MulAut.conj y * fieldActor σ δ') =
        (MulAut.conj y * fieldActor σ δ') * fieldActor σ δ ↔ fieldActor σ δ y = y := by
  have h1 : (fieldActor σ δ : MulAut (Cm σ)) * (MulAut.conj y * fieldActor σ δ') =
      MulAut.conj (fieldActor σ δ y) * (fieldActor σ δ * fieldActor σ δ') := by
    rw [← mul_assoc, mulAut_mul_conj σ, mul_assoc]
  have h2 : (MulAut.conj y * fieldActor σ δ') * fieldActor σ δ =
      MulAut.conj y * (fieldActor σ δ * fieldActor σ δ') := by
    rw [mul_assoc, fieldActor_comm σ δ' δ]
  rw [h1, h2]
  constructor
  · intro h
    exact conj_injective σ (mul_right_cancel h)
  · intro h
    rw [h]

end Commute

section Count

variable {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {f : ℕ} (hf : 1 ≤ f)
  (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ.toRingHom c = c ^ (2 ^ f))

include hf hK hσ

theorem card_of_normal_form {M : Subgroup (MulAut (Cm σ))} {Q : Subgroup (Cm σ)}
    {S : Subgroup (K ≃+* K)}
    (h : ∀ α : MulAut (Cm σ), α ∈ M ↔ ∃ y ∈ Q, ∃ δ ∈ S, α = MulAut.conj y * fieldActor σ δ) :
    Nat.card M = Nat.card Q * Nat.card S := by
  let Φ : ↥Q × ↥S → ↥M := fun p => ⟨MulAut.conj (p.1 : Cm σ) * fieldActor σ (p.2 : K ≃+* K),
    (h _).2 ⟨p.1, p.1.2, p.2, p.2.2, rfl⟩⟩
  have hΦ : Function.Bijective Φ := by
    constructor
    · rintro ⟨⟨y, hy⟩, ⟨δ, hδ⟩⟩ ⟨⟨y', hy'⟩, ⟨δ', hδ'⟩⟩ hEq
      have h1 : MulAut.conj y * fieldActor σ δ = MulAut.conj y' * fieldActor σ δ' :=
        congrArg Subtype.val hEq
      have hδδ : δ = δ' := by
        have h2 := congrArg (theta σ hf hK hσ) h1
        rwa [theta_conj_fieldActor, theta_conj_fieldActor] at h2
      subst hδδ
      have h3 := conj_injective σ (mul_right_cancel h1)
      subst h3
      rfl
    · rintro ⟨α, hα⟩
      obtain ⟨y, hy, δ, hδ, rfl⟩ := (h α).1 hα
      exact ⟨(⟨y, hy⟩, ⟨δ, hδ⟩), rfl⟩
  rw [← Nat.card_eq_of_bijective Φ hΦ, Nat.card_prod]

end Count

section Normalizer

variable {C : Type} [Group C]

theorem conj_mem_autStab_iff (P : Subgroup C) (y : C) :
    (MulAut.conj y : MulAut C) ∈ autStab P ↔ y ∈ Subgroup.normalizer (P : Set C) := by
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro h x
    simpa [MulAut.conj_apply] using h x
  · intro h x
    simpa [MulAut.conj_apply] using h x

theorem normalizer_eq_of_isCoatom [IsSimpleGroup C] {P : Subgroup C} (hP : IsCoatom P)
    (hbot : P ≠ ⊥) : Subgroup.normalizer (P : Set C) = P := by
  rcases hP.le_iff.1 (Subgroup.le_normalizer (H := P)) with h | h
  · exfalso
    have hn : P.Normal := Subgroup.normalizer_eq_top_iff.1 h
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal P with h' | h'
    · exact hbot h'
    · exact hP.1 h'
  · exact h

end Normalizer

end CFSG.Quasithin.H13.F431.D4q.Out
