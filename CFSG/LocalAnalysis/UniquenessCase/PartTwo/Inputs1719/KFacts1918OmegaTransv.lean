module

public import CFSG.LocalAnalysis.GLTheoremB.BlockDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.LocalAnalysis.GLTheoremB

variable {ι : Type} [Fintype ι] [DecidableEq ι]

private theorem exists_transvection_data {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (g : LinearMap.GeneralLinearGroup (ZMod 2) W) (φ : W →ₗ[ZMod 2] W)
    (hφg : ∀ x, (g : W →ₗ[ZMod 2] W) x = x + φ x) (hφφ : ∀ x, φ (φ x) = 0)
    (hrank : Module.finrank (ZMod 2) (LinearMap.range φ) = 1) :
    ∃ (v : W) (f : W →ₗ[ZMod 2] ZMod 2), v ≠ 0 ∧ f ≠ 0 ∧ f v = 0 ∧
      ∀ x, (g : W →ₗ[ZMod 2] W) x = x + f x • v := by
  classical
  obtain ⟨⟨u, hu⟩, hu0, hspan⟩ := finrank_eq_one_iff'.mp hrank
  have hu0' : u ≠ 0 := fun h => hu0 (Subtype.ext h)
  have hrange : ∀ x, φ x ∈ Submodule.span (ZMod 2) {u} := by
    intro x
    obtain ⟨c, hc⟩ := hspan ⟨φ x, LinearMap.mem_range_self φ x⟩
    have h1 : c • u = φ x := congrArg Subtype.val hc
    rw [← h1]
    exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self u)
  set e := LinearEquiv.toSpanNonzeroSingleton (ZMod 2) W u hu0' with he
  set f : W →ₗ[ZMod 2] ZMod 2 := e.symm.toLinearMap.comp (φ.codRestrict _ hrange) with hf
  have hφf : ∀ x, φ x = f x • u := by
    intro x
    have h1 : e (f x) = ⟨φ x, hrange x⟩ := by
      rw [hf, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
      rfl
    have h2 := congrArg Subtype.val h1
    rw [he, LinearEquiv.toSpanNonzeroSingleton_apply] at h2
    exact h2.symm
  obtain ⟨x₀, hx₀⟩ := LinearMap.mem_range.mp hu
  have hfx₀ : f x₀ ≠ 0 := fun h => hu0' (by rw [← hx₀, hφf, h, zero_smul])
  refine ⟨u, f, hu0', fun h => hfx₀ (by rw [h]; rfl), ?_, ?_⟩
  · have h3 := hφφ x₀
    rw [hx₀, hφf] at h3
    rcases smul_eq_zero.mp h3 with h | h
    · exact h
    · exact absurd h hu0'
  · intro x
    rw [hφg x, hφf]

theorem isTransvection_of_rank_sub_one_eq_one {g : GL ι (ZMod 2)} (hg : g * g = 1)
    (hr : ((g : Matrix ι ι (ZMod 2)) - 1).rank = 1) : IsTransvection g := by
  classical
  let T : LinearMap.GeneralLinearGroup (ZMod 2) (ι → ZMod 2) :=
    Matrix.GeneralLinearGroup.toLin g
  have hT : T * T = 1 := by
    simp only [T]
    rw [← map_mul, hg, map_one]
  let φ : (ι → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2) :=
    ((g : Matrix ι ι (ZMod 2)) - 1).mulVecLin
  have hcoe : (T : (ι → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2)) =
      Matrix.mulVecLin (g : Matrix ι ι (ZMod 2)) :=
    Matrix.GeneralLinearGroup.coe_toLin (A := g)
  have hφ_apply : ∀ x, φ x = (T : (ι → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2)) x - x := by
    intro x
    rw [hcoe]
    simp only [φ, Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.one_mulVec]
  have hφg : ∀ x, (T : (ι → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2)) x = x + φ x := by
    intro x
    rw [hφ_apply x]
    abel
  have hTT : ∀ x, (T : (ι → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2))
      ((T : (ι → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2)) x) = x := fun x => by
    rw [← Module.End.mul_apply, ← Units.val_mul, hT, Units.val_one, Module.End.one_apply]
  have h2 : ∀ y : ι → ZMod 2, y + y = 0 := fun y => by
    rw [← two_smul (ZMod 2) y, show (2 : ZMod 2) = 0 from rfl, zero_smul]
  have hφφ : ∀ x, φ (φ x) = 0 := by
    intro x
    rw [hφ_apply x, map_sub, hφ_apply ((T : (ι → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2)) x),
      hφ_apply x, hTT]
    calc (x - (T : (ι → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2)) x)
          - ((T : (ι → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2)) x - x)
        = (x + x) - ((T : (ι → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2)) x
            + (T : (ι → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2)) x) := by abel
      _ = 0 := by rw [h2, h2]; exact sub_self 0
  have hrankφ : Module.finrank (ZMod 2) (LinearMap.range φ) = 1 := by
    rw [show φ = ((g : Matrix ι ι (ZMod 2)) - 1).mulVecLin from rfl]
    simpa only [Matrix.rank] using hr
  obtain ⟨v, f, hv, hf, hfv, hgx⟩ :=
    @exists_transvection_data (ι → ZMod 2) _
      (@Pi.module ι (fun _ => ZMod 2) (ZMod 2) _ _ (fun _ => Semiring.toModule)) T φ hφg hφφ
      hrankφ
  refine ⟨v, f, hv, hf, hfv, ?_⟩
  intro x
  have happ : (T : (ι → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2)) x =
      Matrix.mulVec (g : Matrix ι ι (ZMod 2)) x := by
    rw [hcoe]
    rfl
  calc Matrix.mulVec (g : Matrix ι ι (ZMod 2)) x
      = (T : (ι → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2)) x := happ.symm
    _ = x + f.toFun x • v := hgx x

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
