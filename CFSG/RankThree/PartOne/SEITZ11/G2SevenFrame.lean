module

public import CFSG.RankThree.Chevalley.SteinbergCFOddG2QPlusCentralizers
public import CFSG.LieType.Chevalley.OrthogonalFixedOrbitMaps

public section

namespace CFSG.RankThree.PartOne.SEITZ11.G2Seven

open Matrix CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.Classical CFSG.RankThree.QuadraticSL2 CFSG.LocalAnalysis.ComponentInitial

section Frame

variable {L : Type} [Field L] (σ : L ≃+* L) {z : ModGL Tag.G2 L}

theorem exists_shape (hσσ : ∀ c, σ (σ c) = c) (hz : z ∈ monomialSubgroup Tag.G2 L)
    (hw : ∀ v : Fin Tag.G2.rank → ℤ, weylQuotientHom Tag.G2 L ⟨z, hz⟩ • v = -v)
    (hzz : ∀ y, twistedEntrywise z (σ : L →+* L) (twistedEntrywise z (σ : L →+* L) y) = y)
    {α : Fin Tag.G2.rank → ℤ} (hα : IsRoot Tag.G2 α) :
    ∃ κ : L, κ ≠ 0 ∧ σ κ = κ ∧ ∀ A : SL2 L,
      (A : Matrix (Fin 2) (Fin 2) L) 1 1 = σ ((A : Matrix (Fin 2) (Fin 2) L) 0 0) →
      (A : Matrix (Fin 2) (Fin 2) L) 1 0 = κ * σ ((A : Matrix (Fin 2) (Fin 2) L) 0 1) →
      twistedEntrywise z (σ : L →+* L) (rootSL2 Tag.G2 L α A) = rootSL2 Tag.G2 L α A := by
  obtain ⟨a, b, hu, hl⟩ := exists_twistedEntrywise_rootSL2 hz hw σ hα
  obtain ⟨M, hM⟩ := exists_semilinearConj_rootSL2 hz hw σ hα
  have hinj : Function.Injective (rootSL2 Tag.G2 L α) :=
    rootSL2_injective_of_field (τ := Tag.G2) (K := L) α
  have hTu : ∀ c, semilinearConj M σ (uSL c) = vSL (a * σ c) := fun c => by
    have h1 := hM (uSL c)
    rw [hu c] at h1
    exact hinj h1
  have hTl : ∀ c, semilinearConj M σ (vSL c) = uSL (b * σ c) := fun c => by
    have h1 := hM (vSL c)
    rw [hl c] at h1
    exact hinj h1
  obtain ⟨hab, M', hM', hT⟩ := sl2_semilinear_exchanged_root_compatibility σ a b
    (semilinearConj M σ) hTu hTl
  have hbσ : (b : L) * σ a = 1 := by
    have h := hzz (rootSL2 Tag.G2 L α (uSL 1))
    rw [hu, hl] at h
    have h01 := congrArg (fun X : SL2 L => (X : Matrix (Fin 2) (Fin 2) L) 0 1) (hinj h)
    simpa [uSL] using h01
  have hσa : σ a = a := by
    have h1 : ((a : Lˣ) : L) * b = 1 := by rw [← Units.val_mul, hab, Units.val_one]
    have h2 : (b : L) * σ a = 1 := hbσ
    have h3 : (b : L) * (σ a - a) = 0 := by linear_combination h2 - h1
    have hb0 : (b : L) ≠ 0 := b.ne_zero
    exact sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_left hb0)
  refine ⟨a, a.ne_zero, hσa, fun A h11 h10 => ?_⟩
  rw [← hM A]
  congr 1
  refine Subtype.ext ?_
  rw [hT A]
  have hMi : (M' : Matrix (Fin 2) (Fin 2) L) * (↑M'⁻¹ : Matrix (Fin 2) (Fin 2) L) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hcomm : (M' : Matrix (Fin 2) (Fin 2) L) *
      (Matrix.SpecialLinearGroup.map (σ : L →+* L) A : Matrix (Fin 2) (Fin 2) L) =
        (A : Matrix (Fin 2) (Fin 2) L) * (M' : Matrix (Fin 2) (Fin 2) L) := by
    rw [hM']
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.SpecialLinearGroup.map_apply_coe, h11, h10,
        hσσ, hσa, mul_comm]
  calc (M' : Matrix (Fin 2) (Fin 2) L) *
        (Matrix.SpecialLinearGroup.map (σ : L →+* L) A : Matrix (Fin 2) (Fin 2) L) *
          (↑M'⁻¹ : Matrix (Fin 2) (Fin 2) L)
      = (A : Matrix (Fin 2) (Fin 2) L) * ((M' : Matrix (Fin 2) (Fin 2) L) *
          (↑M'⁻¹ : Matrix (Fin 2) (Fin 2) L)) := by rw [hcomm, Matrix.mul_assoc]
    _ = A := by rw [hMi, Matrix.mul_one]

theorem rootSL2_shape_mem {Γ : Subgroup (ModGL Tag.G2 L)}
    (hΓ : Γ = adjointGroup Tag.G2 L ⊓
      (twistedEntrywise z (σ : L →+* L)).eqLocus (MonoidHom.id _))
    {α : Fin Tag.G2.rank → ℤ} {A : SL2 L}
    (hfix : twistedEntrywise z (σ : L →+* L) (rootSL2 Tag.G2 L α A) = rootSL2 Tag.G2 L α A) :
    rootSL2 Tag.G2 L α A ∈ Γ := by
  rw [hΓ]
  exact ⟨rootSL2_mem_adjointGroup α A, hfix⟩

end Frame

end CFSG.RankThree.PartOne.SEITZ11.G2Seven
