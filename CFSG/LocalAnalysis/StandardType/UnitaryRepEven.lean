module

public import CFSG.LocalAnalysis.StandardType.UnitaryCoreEven
public import CFSG.LocalAnalysis.StandardType.UnitaryBaseChange

public section

namespace CFSG.StandardType

namespace UnitaryRep

open Matrix

theorem eq_one_of_commute_even {F : Type} [Field F] [CharP F 2] (σ : F ≃+* F) {ζ : F} (hζ1 : ζ ≠ 1)
    (hζ3 : ζ ^ 3 = 1) (hσζ : σ ζ = ζ) {Γ : Type*} [Group Γ] [Finite Γ]
    (h5 : HasOrderFiveData Γ) (h7 : HasOrderSevenData Γ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (hι : Fintype.card ι ≤ 9) {G : Matrix ι ι F} (hG : IsUnit G) (ρ : Γ →* Matrix ι ι F)
    (hρ : ∀ g, (ρ g)ᵀ * G * (ρ g).map σ = G) {A B : Matrix ι ι F} (hA3 : A ^ 3 = 1)
    (hB3 : B ^ 3 = 1) (hAB : A * B = B * A) (hAG : Aᵀ * G * A.map σ = G)
    (hBG : Bᵀ * G * B.map σ = G) (hAc : ∀ g, ρ g * A = A * ρ g) (hBc : ∀ g, ρ g * B = B * ρ g)
    (hnc : ∀ i j : ℕ, ¬ (3 ∣ i ∧ 3 ∣ j) → ∀ e : F, A ^ i * B ^ j ≠ e • 1) (g : Γ) : ρ g = 1 := by
  classical
  obtain ⟨σ', hσ'⟩ := UnitaryAlg.exists_ringEquiv_extension σ
  have hσ3 : ∀ η : AlgebraicClosure F, η ^ 3 = 1 → σ' η = η :=
    fun η hη => UnitaryAlg.apply_eq_self_of_pow_three hσ' hζ1 hζ3 hσζ hη
  let f : F →+* AlgebraicClosure F := algebraMap F (AlgebraicClosure F)
  have hA3' : (A.map f) ^ 3 = 1 := by
    rw [← Matrix.map_pow, hA3]
    exact Matrix.map_one f (map_zero f) (map_one f)
  have hB3' : (B.map f) ^ 3 = 1 := by
    rw [← Matrix.map_pow, hB3]
    exact Matrix.map_one f (map_zero f) (map_one f)
  have hAB' : A.map f * B.map f = B.map f * A.map f := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, hAB]
  have hAG' : (A.map f)ᵀ * G.map f * (A.map f).map σ' = G.map f := by
    rw [UnitaryBaseChange.map_form hσ' A G, hAG]
  have hBG' : (B.map f)ᵀ * G.map f * (B.map f).map σ' = G.map f := by
    rw [UnitaryBaseChange.map_form hσ' B G, hBG]
  have hAc' : ∀ g, UnitaryBaseChange.baseChangeHom ρ g * A.map f =
      A.map f * UnitaryBaseChange.baseChangeHom ρ g := by
    intro g
    rw [UnitaryBaseChange.baseChangeHom_apply, ← Matrix.map_mul, ← Matrix.map_mul, hAc g]
  have hBc' : ∀ g, UnitaryBaseChange.baseChangeHom ρ g * B.map f =
      B.map f * UnitaryBaseChange.baseChangeHom ρ g := by
    intro g
    rw [UnitaryBaseChange.baseChangeHom_apply, ← Matrix.map_mul, ← Matrix.map_mul, hBc g]
  have hG' : IsUnit (G.map f) := by
    simpa using hG.map (RingHom.mapMatrix f)
  have hnc' : ∀ i j : ℕ, ¬ (3 ∣ i ∧ 3 ∣ j) → ∀ e : AlgebraicClosure F,
      (A.map f) ^ i * (B.map f) ^ j ≠ e • 1 := by
    intro i j hij e
    have hmap : (A.map f) ^ i * (B.map f) ^ j = (A ^ i * B ^ j).map f := by
      rw [Matrix.map_mul, Matrix.map_pow, Matrix.map_pow]
    rw [hmap]
    exact UnitaryBaseChange.map_ne_smul_one (hnc i j hij) e
  have hcore : UnitaryBaseChange.baseChangeHom ρ g = 1 :=
    UnitaryCore.eq_one_of_commute_even h5 h7 σ' hσ3 hι hG'
      (UnitaryBaseChange.baseChangeHom ρ) (UnitaryBaseChange.baseChangeHom_form hσ' ρ hρ)
      hA3' hB3' hAB' hAG' hBG' hAc' hBc' hnc' g
  exact (UnitaryBaseChange.baseChangeHom_eq_one_iff ρ g).mp hcore

end UnitaryRep

end CFSG.StandardType
