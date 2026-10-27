module

public import CFSG.GH74.GLS.IVK.Lifted.Lem119V
public import CFSG.GH74.GLS.IVK.Lifted.SqR

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Matrix
open scoped MatrixGroups

variable {F : Type} [Field F] [Finite F]

theorem mem_range_conj_of_odd_of_trace
    (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    (α : MulAut (SpecialLinearGroup (Fin 2) F))
    (hα : Odd (orderOf α))
    (htrace : ∀ x : SpecialLinearGroup (Fin 2) F,
      Matrix.trace ((α x : SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) =
      Matrix.trace ((x : SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F)) :
    α ∈ (MulAut.conj : SpecialLinearGroup (Fin 2) F →*
      MulAut (SpecialLinearGroup (Fin 2) F)).range := by
  classical
  have htrace_surj : ∀ a : F, ∃ x : SpecialLinearGroup (Fin 2) F,
      Matrix.trace ((x : SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) = a := by
    intro a
    refine ⟨⟨!![a, -1; 1, 0], ?_⟩, ?_⟩
    · simp [Matrix.det_fin_two]
    · simp [Matrix.trace_fin_two]
  have hσ : (CFSG.GH74.GLS.IVK.Lifted.gammaOf hodd h3 α).right = 1 := by
    apply RingEquiv.ext
    intro a
    obtain ⟨x, hx⟩ := htrace_surj a
    have hte := CFSG.GH74.GLS.IVK.Lifted.trace_aut_eq hodd h3 α x
    have hte' : Matrix.trace ((α x : SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) =
        (CFSG.GH74.GLS.IVK.Lifted.gammaOf hodd h3 α).right
          (Matrix.trace ((x : SpecialLinearGroup (Fin 2) F) :
            Matrix (Fin 2) (Fin 2) F)) := by
      simpa [Matrix.trace_fin_two] using hte
    have htr : Matrix.trace ((α x : SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) =
        Matrix.trace ((x : SpecialLinearGroup (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F) := htrace x
    calc
      (CFSG.GH74.GLS.IVK.Lifted.gammaOf hodd h3 α).right a =
          (CFSG.GH74.GLS.IVK.Lifted.gammaOf hodd h3 α).right
            (Matrix.trace ((x : SpecialLinearGroup (Fin 2) F) :
              Matrix (Fin 2) (Fin 2) F)) := by rw [← hx]
      _ = Matrix.trace ((α x : SpecialLinearGroup (Fin 2) F) :
            Matrix (Fin 2) (Fin 2) F) := hte'.symm
      _ = Matrix.trace ((x : SpecialLinearGroup (Fin 2) F) :
            Matrix (Fin 2) (Fin 2) F) := htr
      _ = a := hx
  have hα2σ : (CFSG.GH74.GLS.IVK.Lifted.gammaOf hodd h3 (α * α)).right = 1 := by
    rw [CFSG.GH74.GLS.IVK.Lifted.gammaOf_mul_right, hσ, mul_one]
  have hα2_inner : α * α ∈
      (MulAut.conj : SpecialLinearGroup (Fin 2) F →*
        MulAut (SpecialLinearGroup (Fin 2) F)).range :=
    CFSG.GH74.GLS.IVK.Lifted.sq_mem_inn_of_field hodd h3 α hα2σ
  have hα2pow : α ^ 2 ∈
      (MulAut.conj : SpecialLinearGroup (Fin 2) F →*
        MulAut (SpecialLinearGroup (Fin 2) F)).range := by
    simpa [pow_two] using hα2_inner
  have hα_zpowers : α ∈ Subgroup.zpowers (α ^ 2) := by
    rw [mem_zpowers_pow_iff]
    exact Nat.coprime_iff_gcd_eq_one.mp ((Nat.coprime_two_right.mpr hα).symm)
  exact (Subgroup.zpowers_le.mpr hα2pow) hα_zpowers

theorem exists_inner_normalizer_aut_of_trace
    (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    {n : ℕ}
    (φ : SpecialLinearGroup (Fin 2) F →* SpecialLinearGroup (Fin n) F)
    (hφ : Function.Injective φ)
    {a b : F} (ha : a ≠ 0)
    (htrace : ∀ x : SpecialLinearGroup (Fin 2) F,
      Matrix.trace ((φ x : SpecialLinearGroup (Fin n) F) :
        Matrix (Fin n) (Fin n) F) =
      a * Matrix.trace ((x : SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) + b)
    {g : SpecialLinearGroup (Fin n) F}
    (hgN : g ∈ Subgroup.normalizer (φ.range : Set (SpecialLinearGroup (Fin n) F)))
    (hgodd : Odd (orderOf g)) :
    ∃ y : SpecialLinearGroup (Fin 2) F,
      ∀ x : SpecialLinearGroup (Fin 2) F,
        g * φ x * g⁻¹ = φ y * φ x * (φ y)⁻¹ := by
  classical
  let H := φ.range
  let e : SpecialLinearGroup (Fin 2) F ≃* H := MonoidHom.ofInjective hφ
  let act : MulAut H := H.normalizerMonoidHom ⟨g, hgN⟩
  let α : MulAut (SpecialLinearGroup (Fin 2) F) := e.trans (act.trans e.symm)
  have hact_dvd : orderOf act ∣ orderOf g := by
    simpa [Subgroup.orderOf_mk] using
      orderOf_map_dvd H.normalizerMonoidHom ⟨g, hgN⟩
  have hact_odd : Odd (orderOf act) := Odd.of_dvd_nat hgodd hact_dvd
  have hα_eq : α = (MulAut.congr e).symm act := by
    exact (MulAut.congr_symm_apply e act).symm
  have hα_order : orderOf α = orderOf act := by
    rw [hα_eq]
    exact MulEquiv.orderOf_eq ((MulAut.congr e).symm) act
  have hα_odd : Odd (orderOf α) := by
    rw [hα_order]
    exact hact_odd
  have hα_apply : ∀ x : SpecialLinearGroup (Fin 2) F, e (α x) = act (e x) := by
    intro x
    simp [α]
  have hφ_alpha : ∀ x : SpecialLinearGroup (Fin 2) F,
      (φ (α x) : SpecialLinearGroup (Fin n) F) = g * φ x * g⁻¹ := by
    intro x
    have h := congrArg Subtype.val (hα_apply x)
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h
    have h1 : ((e (α x) : H) : SpecialLinearGroup (Fin n) F) = φ (α x) :=
      MonoidHom.ofInjective_apply hφ
    have h2 : ((e x : H) : SpecialLinearGroup (Fin n) F) = φ x :=
      MonoidHom.ofInjective_apply hφ
    rw [h1, h2] at h
    simpa using h
  have hconj_trace : ∀ x : SpecialLinearGroup (Fin 2) F,
      Matrix.trace (((g * φ x * g⁻¹ : SpecialLinearGroup (Fin n) F) :
        Matrix (Fin n) (Fin n) F)) =
      Matrix.trace ((φ x : SpecialLinearGroup (Fin n) F) :
        Matrix (Fin n) (Fin n) F) := by
    intro x
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.trace_mul_cycle,
      ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, one_mul]
  have hα_trace : ∀ x : SpecialLinearGroup (Fin 2) F,
      Matrix.trace ((α x : SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) =
      Matrix.trace ((x : SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) := by
    intro x
    have h1 : Matrix.trace ((φ (α x) : SpecialLinearGroup (Fin n) F) :
        Matrix (Fin n) (Fin n) F) =
        a * Matrix.trace ((α x : SpecialLinearGroup (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F) + b := htrace (α x)
    have h2 : Matrix.trace ((φ (α x) : SpecialLinearGroup (Fin n) F) :
        Matrix (Fin n) (Fin n) F) =
        a * Matrix.trace ((x : SpecialLinearGroup (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F) + b := by
      rw [hφ_alpha x, hconj_trace x]
      exact htrace x
    have h3 : a * Matrix.trace ((α x : SpecialLinearGroup (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F) + b =
        a * Matrix.trace ((x : SpecialLinearGroup (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F) + b := h1.symm.trans h2
    have h4 : a * Matrix.trace ((α x : SpecialLinearGroup (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F) =
        a * Matrix.trace ((x : SpecialLinearGroup (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F) := by
      simpa using congrArg (fun z : F => z - b) h3
    exact mul_left_cancel₀ ha h4
  obtain ⟨y, hy⟩ :=
    mem_range_conj_of_odd_of_trace hodd h3 α hα_odd hα_trace
  refine ⟨y, fun x => ?_⟩
  calc
    g * φ x * g⁻¹ = (φ (α x) : SpecialLinearGroup (Fin n) F) :=
      (hφ_alpha x).symm
    _ = φ ((MulAut.conj y) x) := by rw [← hy]
    _ = φ y * φ x * (φ y)⁻¹ := by
      rw [MulAut.conj_apply, map_mul, map_mul, map_inv]

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
