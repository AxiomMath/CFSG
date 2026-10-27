module

public import CFSG.LocalAnalysis.StandardType.UnitaryCoreOdd
public import CFSG.LocalAnalysis.StandardType.UnitaryBaseChange

public section

namespace CFSG.StandardType

namespace UnitaryRep

open Matrix

theorem eq_one_of_commute_odd {F : Type} [Field F] [CharP F 2] (σ : F ≃+* F) {ζ : F} (hζ1 : ζ ≠ 1)
    (hζ3 : ζ ^ 3 = 1) (hσζ : σ ζ = ζ⁻¹) {Γ : Type*} [Group Γ] [Finite Γ]
    (h5 : HasOrderFiveData Γ) (h7 : HasOrderSevenData Γ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (hι : Fintype.card ι ≤ 6) {G : Matrix ι ι F} (hG : IsUnit G) (ρ : Γ →* Matrix ι ι F)
    (hρ : ∀ g, (ρ g)ᵀ * G * (ρ g).map σ = G) {A : Matrix ι ι F} {c : F} (hc : c ≠ 0)
    (hA3 : A ^ 3 = c • 1) (hAG : Aᵀ * G * A.map σ = G) (hcomm : ∀ g, ρ g * A = A * ρ g)
    (hnc : ∀ e : F, A ≠ e • 1) (g : Γ) : ρ g = 1 := by
  classical
  obtain ⟨σ', hσ'⟩ := UnitaryAlg.exists_ringEquiv_extension σ
  have hσ3 : ∀ η : AlgebraicClosure F, η ^ 3 = 1 → σ' η = η⁻¹ :=
    fun η hη => UnitaryAlg.apply_eq_inv_of_pow_three hσ' hζ1 hζ3 hσζ hη
  obtain ⟨d, hd⟩ :=
    IsAlgClosed.exists_pow_nat_eq (algebraMap F (AlgebraicClosure F) c) (by norm_num : 0 < 3)
  have hc0 : algebraMap F (AlgebraicClosure F) c ≠ 0 := by
    intro h
    exact hc ((algebraMap F (AlgebraicClosure F)).injective (by rw [h, map_zero]))
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hc0 (by rw [← hd]; simp)
  have hσ'' : (A.map (algebraMap F (AlgebraicClosure F))).map σ' =
      (A.map σ).map (algebraMap F (AlgebraicClosure F)) := by
    ext i j
    simp only [Matrix.map_apply]
    exact hσ' (A i j)
  have hcore : (A.map (algebraMap F (AlgebraicClosure F)))ᵀ *
        G.map (algebraMap F (AlgebraicClosure F)) *
        (A.map σ).map (algebraMap F (AlgebraicClosure F)) =
      G.map (algebraMap F (AlgebraicClosure F)) := by
    rw [← hσ'', UnitaryBaseChange.map_form hσ' A G, hAG]
  let A' : Matrix ι ι (AlgebraicClosure F) := d⁻¹ • A.map (algebraMap F (AlgebraicClosure F))
  have hA'3 : A' ^ 3 = 1 := by
    have h1 : (A.map (algebraMap F (AlgebraicClosure F))) ^ 3 =
        algebraMap F (AlgebraicClosure F) c • (1 : Matrix ι ι (AlgebraicClosure F)) := by
      rw [← Matrix.map_pow A (algebraMap F (AlgebraicClosure F)) 3, hA3,
        Matrix.map_smul' (algebraMap F (AlgebraicClosure F)) c (1 : Matrix ι ι F)
          (fun a b => map_mul _ a b),
        Matrix.map_one (algebraMap F (AlgebraicClosure F)) (map_zero _) (map_one _)]
    show (d⁻¹ • A.map (algebraMap F (AlgebraicClosure F))) ^ 3 = 1
    rw [smul_pow, inv_pow d 3, hd, h1, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have hG' : IsUnit (G.map (algebraMap F (AlgebraicClosure F))) :=
    IsUnit.map (RingHom.mapMatrix (algebraMap F (AlgebraicClosure F))) hG
  have hA'map : (d⁻¹ • A.map (algebraMap F (AlgebraicClosure F))).map σ' =
      σ' d⁻¹ • (A.map σ).map (algebraMap F (AlgebraicClosure F)) := by
    rw [Matrix.map_smul' σ' d⁻¹ (A.map (algebraMap F (AlgebraicClosure F)))
      (fun a b => map_mul σ' a b), hσ'']
  have hA'G : A'ᵀ * G.map (algebraMap F (AlgebraicClosure F)) * A'.map σ' =
      (d⁻¹ * σ' d⁻¹) • G.map (algebraMap F (AlgebraicClosure F)) := by
    show (d⁻¹ • A.map (algebraMap F (AlgebraicClosure F)))ᵀ *
          G.map (algebraMap F (AlgebraicClosure F)) *
          (d⁻¹ • A.map (algebraMap F (AlgebraicClosure F))).map σ' =
        (d⁻¹ * σ' d⁻¹) • G.map (algebraMap F (AlgebraicClosure F))
    rw [Matrix.transpose_smul, hA'map]
    calc (d⁻¹ • (A.map (algebraMap F (AlgebraicClosure F)))ᵀ) *
            G.map (algebraMap F (AlgebraicClosure F)) *
            (σ' d⁻¹ • (A.map σ).map (algebraMap F (AlgebraicClosure F)))
        = (d⁻¹ • ((A.map (algebraMap F (AlgebraicClosure F)))ᵀ *
              G.map (algebraMap F (AlgebraicClosure F)))) *
            (σ' d⁻¹ • (A.map σ).map (algebraMap F (AlgebraicClosure F))) := by
          rw [smul_mul]
      _ = σ' d⁻¹ • ((d⁻¹ • ((A.map (algebraMap F (AlgebraicClosure F)))ᵀ *
              G.map (algebraMap F (AlgebraicClosure F)))) *
            (A.map σ).map (algebraMap F (AlgebraicClosure F))) := by
          rw [Matrix.mul_smul]
      _ = σ' d⁻¹ • (d⁻¹ • (((A.map (algebraMap F (AlgebraicClosure F)))ᵀ *
              G.map (algebraMap F (AlgebraicClosure F))) *
            (A.map σ).map (algebraMap F (AlgebraicClosure F)))) := by
          rw [smul_mul]
      _ = (σ' d⁻¹ * d⁻¹) • (((A.map (algebraMap F (AlgebraicClosure F)))ᵀ *
              G.map (algebraMap F (AlgebraicClosure F))) *
            (A.map σ).map (algebraMap F (AlgebraicClosure F))) := by
          rw [smul_smul]
      _ = (d⁻¹ * σ' d⁻¹) • G.map (algebraMap F (AlgebraicClosure F)) := by
          rw [mul_comm (σ' d⁻¹) d⁻¹, hcore]
  have hcomm' : ∀ g : Γ, UnitaryBaseChange.baseChangeHom ρ g * A' =
      A' * UnitaryBaseChange.baseChangeHom ρ g := by
    intro g
    have hmapcomm : (ρ g).map (algebraMap F (AlgebraicClosure F)) *
        A.map (algebraMap F (AlgebraicClosure F)) =
        A.map (algebraMap F (AlgebraicClosure F)) *
        (ρ g).map (algebraMap F (AlgebraicClosure F)) := by
      have h := congrArg (fun M : Matrix ι ι F =>
        M.map (algebraMap F (AlgebraicClosure F))) (hcomm g)
      rwa [Matrix.map_mul, Matrix.map_mul] at h
    show UnitaryBaseChange.baseChangeHom ρ g *
          (d⁻¹ • A.map (algebraMap F (AlgebraicClosure F))) =
        (d⁻¹ • A.map (algebraMap F (AlgebraicClosure F))) *
          UnitaryBaseChange.baseChangeHom ρ g
    rw [UnitaryBaseChange.baseChangeHom_apply, Matrix.mul_smul, smul_mul, hmapcomm]
  have hnc' : ∀ e' : AlgebraicClosure F, A' ≠ e' • 1 := by
    intro e' he'
    change d⁻¹ • A.map (algebraMap F (AlgebraicClosure F)) = e' • 1 at he'
    have hscaled : A.map (algebraMap F (AlgebraicClosure F)) = (d * e') • 1 := by
      have h := congrArg (fun M : Matrix ι ι (AlgebraicClosure F) => d • M) he'
      rw [smul_smul, mul_inv_cancel₀ hd0, one_smul, smul_smul] at h
      exact h
    exact UnitaryBaseChange.map_ne_smul_one hnc (d * e') hscaled
  have hbase : UnitaryBaseChange.baseChangeHom ρ g = 1 :=
    UnitaryCore.eq_one_of_commute_odd h5 h7 σ' hσ3 hι hG' (UnitaryBaseChange.baseChangeHom ρ)
      (UnitaryBaseChange.baseChangeHom_form hσ' ρ hρ) hA'3 hA'G hcomm' hnc' g
  exact (UnitaryBaseChange.baseChangeHom_eq_one_iff ρ g).mp hbase

end UnitaryRep

end CFSG.StandardType
