module

public import CFSG.Quasithin.EmptyFaithful.S146zUC2Orbit
public import CFSG.Quasithin.EmptyFaithful.S146zUF1Def
public import CFSG.Quasithin.EmptyFaithful.S146zUC2Strong

public section

namespace CFSG.Quasithin.S146zU.UF2

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

section Pair

variable {V : Type} [CommGroup V] [Finite V] {Γ L₁ L₂ : Subgroup (MulAut V)} {τ : MulAut V}

theorem pair_card_mul_card_fixV_le (P : PairPkg Γ L₁ L₂ τ) (hV : ∀ v : V, v ^ 2 = 1)
    {A : Subgroup (MulAut V)} (hAΓ : A ≤ Γ) (hA1 : A ≠ ⊥) (hA2 : IsElemAbelian2 A) :
    Nat.card ↥A * Nat.card ↥(fixV A) ≤ Nat.card V :=
  UC2.card_mul_card_fixV_le hV P.twoNat P.comm P.ffJ_eq hAΓ hA1 hA2

theorem pair_isFFStarOffender_of_card_eq (P : PairPkg Γ L₁ L₂ τ) (hV : ∀ v : V, v ^ 2 = 1)
    {A : Subgroup (MulAut V)} (hAΓ : A ≤ Γ) (hA1 : A ≠ ⊥) (hA2 : IsElemAbelian2 A)
    (hcard : Nat.card V = Nat.card ↥A * Nat.card ↥(fixV A)) : IsFFStarOffender Γ A := by
  refine ⟨hAΓ, hA1, hA2, fun B hB => ?_⟩
  by_cases hB0 : B = ⊥
  · subst hB0
    rw [B1.card_bot_mul_card_fixV]
    exact hcard.le
  · exact (pair_card_mul_card_fixV_le P hV (hB.trans hAΓ) hB0
      (B6.isElemAbelian2_mono hA2 hB)).trans hcard.le

theorem pair_four_mul_card_stabilizer_le (P : PairPkg Γ L₁ L₂ τ) {A : Subgroup (MulAut V)}
    (hA : IsFFStarOffender Γ A) {s : V} (hs : s ∉ fixV A) :
    4 * Nat.card ↥(A ⊓ MulAction.stabilizer (MulAut V) s) ≤ Nat.card ↥A :=
  UC2.four_mul_card_stabilizer_le P.twoNat P.comm P.card₁ P.card₂ P.ffJ_eq hA hs

theorem pair_card_commV_ge_four (P : PairPkg Γ L₁ L₂ τ) {A : Subgroup (MulAut V)}
    (hAΓ : A ≤ Γ) (hA : A ≠ ⊥) : 4 ≤ Nat.card ↥(commV A) :=
  UC2.card_commV_ge_four P.twoNat P.comm P.card₁ P.card₂ P.norm P.cen hAΓ hA

end Pair

section Commutators

variable {F : Type} [CommGroup F] [Finite F]

theorem exists_two_comm (hF : ∀ f : F, f ^ 2 = 1) {B : Subgroup (MulAut F)}
    (h4 : 4 ≤ Nat.card ↥(commV B)) :
    ∃ x₁ ∈ B, ∃ f₁ : F, ∃ x₂ ∈ B, ∃ f₂ : F,
      x₁ f₁ * f₁⁻¹ ≠ 1 ∧ x₂ f₂ * f₂⁻¹ ≠ 1 ∧ x₁ f₁ * f₁⁻¹ ≠ x₂ f₂ * f₂⁻¹ := by
  by_contra hno
  have hno' : ∀ x₁ ∈ B, ∀ f₁ : F, ∀ x₂ ∈ B, ∀ f₂ : F, x₁ f₁ * f₁⁻¹ ≠ 1 → x₂ f₂ * f₂⁻¹ ≠ 1 →
      x₁ f₁ * f₁⁻¹ = x₂ f₂ * f₂⁻¹ := by
    intro x₁ hx₁ f₁ x₂ hx₂ f₂ h1 h2
    by_contra h3
    exact hno ⟨x₁, hx₁, f₁, x₂, hx₂, f₂, h1, h2, h3⟩
  obtain ⟨c, hc⟩ : ∃ c : F, ∀ x ∈ B, ∀ f : F, x f * f⁻¹ = 1 ∨ x f * f⁻¹ = c := by
    by_cases hex : ∃ x ∈ B, ∃ f : F, x f * f⁻¹ ≠ 1
    · obtain ⟨x₀, hx₀, f₀, hc₀⟩ := hex
      refine ⟨x₀ f₀ * f₀⁻¹, fun x hx f => ?_⟩
      by_cases hw : x f * f⁻¹ = 1
      · exact Or.inl hw
      · exact Or.inr (hno' x hx f x₀ hx₀ f₀ hw hc₀)
    · exact ⟨1, fun x hx f => Or.inl (by_contra fun h => hex ⟨x, hx, f, h⟩)⟩
  have hle : commV B ≤ Subgroup.zpowers c := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨x, hx, v, rfl⟩
    rcases hc x hx v with h | h
    · rw [h]
      exact one_mem _
    · rw [h]
      exact Subgroup.mem_zpowers c
  have h2 : Nat.card ↥(commV B) ≤ 2 := by
    refine (Subgroup.card_le_of_le hle).trans ?_
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hF c))
  omega

end Commutators

end CFSG.Quasithin.S146zU.UF2
