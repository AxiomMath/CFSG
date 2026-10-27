module

public import CFSG.LocalAnalysis.StandardType.GGTwE6LeviSplit

public section

namespace CFSG.StandardType.TwE6RootKill

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.HardMathSupport.Timmesfeld.CrossChar


theorem exists_conj_le_levi_of_twNormTwo {K : Type} [Field K] [Finite K] [CharP K 2]
    {σ : K ≃+* K} {q : ℕ} (hK : Nat.card K = q ^ 2) (hσq : ∀ c, σ c = c ^ q)
    {A : Subgroup (ModGL TwistTag.E6.tag K)} (hAI : A ≤ twistedE6InndiagGL K σ)
    (hodd : Odd (Nat.card A)) (hU : TwNormTwo K σ A) :
    ∃ h ∈ twistedE6RootGroup K σ, ∃ J : Set (Fin TwistTag.E6.foldedTag.rank), J ≠ Set.univ ∧
      ∀ x ∈ A, h * x * h⁻¹ ∈
        graphFixedParabolicLevi TwistTag.E6 K σ.toRingHom J ⊔ twistedE6DiagGL K σ := by
  obtain ⟨U, hUC, hU1, hU2, hAU⟩ := hU
  have h2 : ringChar K = 2 := ringChar.eq K 2
  have hp : (ringChar K).Prime := by
    rw [h2]
    exact Nat.prime_two
  have hσ : σ ^ TwistTag.E6.order = 1 := by
    have ho : TwistTag.E6.order = 2 := rfl
    rw [ho]
    ext c
    have : Fintype K := Fintype.ofFinite K
    have hcard : Fintype.card K = q ^ 2 := by rw [← Nat.card_eq_fintype_card, hK]
    change σ (σ c) = c
    rw [hσq (σ c), hσq c, ← pow_mul, ← sq, ← hcard, FiniteField.pow_card]
  have hAN : ∀ x ∈ A, x ∈ Subgroup.normalizer (U : Set (ModGL TwistTag.E6.tag K)) := by
    intro x hx
    refine Subgroup.mem_normalizer_iff.2 fun u => ⟨fun hu => hAU x hx u hu, fun hu => ?_⟩
    have e : x⁻¹ * (x * u * x⁻¹) * x⁻¹⁻¹ = u := by group
    rw [← e]
    exact hAU x⁻¹ (inv_mem hx) _ hu
  obtain ⟨g₀, hg₀, J, hJ, hP⟩ : ∃ g₀ ∈ twistedE6RootGroup K σ,
      ∃ J : Set (Fin TwistTag.E6.foldedTag.rank), J ≠ Set.univ ∧
        ∀ x ∈ twistedE6InndiagGL K σ,
          x ∈ Subgroup.normalizer (U : Set (ModGL TwistTag.E6.tag K)) →
            g₀⁻¹ * x * g₀ ∈ graphFixedParabolic TwistTag.E6 K σ.toRingHom J ⊔
              twistedE6DiagGL K σ :=
    exists_conj_mem_parabolic_sup_torus K σ hσ hp U hUC (by rw [h2]; exact hU2) hU1
  obtain ⟨A₀, hA₀⟩ : ∃ A₀ : Subgroup (ModGL TwistTag.E6.tag K),
      A₀ = A.map (MulAut.conj g₀⁻¹).toMonoidHom := ⟨_, rfl⟩
  have hA₀P : A₀ ≤ graphFixedParabolic TwistTag.E6 K σ.toRingHom J ⊔ twistedE6DiagGL K σ := by
    rw [hA₀]
    rintro _ ⟨x, hx, rfl⟩
    change g₀⁻¹ * x * g₀⁻¹⁻¹ ∈ _
    rw [inv_inv]
    exact hP x (hAI hx) (hAN x hx)
  have hA₀odd : Odd (Nat.card A₀) := by
    rw [hA₀, Subgroup.card_map_of_injective (f := (MulAut.conj g₀⁻¹).toMonoidHom)
      (MulAut.conj g₀⁻¹).injective]
    exact hodd
  obtain ⟨y, hyQ, hyL⟩ := exists_conj_le_levi_sup_torus K σ J hA₀odd hA₀P
  refine ⟨y * g₀⁻¹, mul_mem
    (graphFixedParabolicRadical_le_graphFixedRootGroup TwistTag.E6 K σ.toRingHom J hyQ)
    (inv_mem hg₀), J, hJ, fun x hx => ?_⟩
  have e : y * g₀⁻¹ * x * (y * g₀⁻¹)⁻¹ = y * (g₀⁻¹ * x * g₀⁻¹⁻¹) * y⁻¹ := by group
  rw [e]
  exact hyL _ (by rw [hA₀]; exact ⟨x, hx, rfl⟩)

theorem exists_leviCochar_inv {K L : Type} [Field K] [Finite K] [Field L] (j : K →+* L) {q : ℕ}
    (hK : Nat.card K = q ^ 2) (h3 : 3 ∣ q + 1) {J : Set (Fin TwistTag.E6.foldedTag.rank)}
    (hJ : J ≠ Set.univ) {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ q) :
    ∃ ζ : Lˣ, leviCochar L J ζ ^ 3 = 1 ∧ leviCochar L J ζ ≠ 1 ∧
      twistHom TwistTag.E6 L Fr (leviCochar L J ζ) = (leviCochar L J ζ)⁻¹ := by
  obtain ⟨ζK, hζK⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 (by
    rw [Nat.card_units, hK]
    exact (h3.mul_right _).trans (dvd_of_eq (Nat.sq_sub_sq q 1).symm))
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Lˣ, orderOf ζ = 3 :=
    ⟨_, (orderOf_injective _ (Units.map_injective (f := j.toMonoidHom) j.injective) ζK).trans hζK⟩
  have hζ3 : ζ ^ 3 = 1 := by
    rw [← hζ]
    exact pow_orderOf_eq_one ζ
  refine ⟨ζ, by rw [← map_pow, hζ3, map_one], leviCochar_ne_one hJ fun h1 => ?_, ?_⟩
  · rw [h1, orderOf_one] at hζ
    omega
  · obtain ⟨m, hm⟩ := h3
    rw [twistHom_leviCochar Fr hFr J ζ, ← map_inv]
    congr 1
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_succ, hm, pow_mul, hζ3, one_pow]

end CFSG.StandardType.TwE6RootKill

end
