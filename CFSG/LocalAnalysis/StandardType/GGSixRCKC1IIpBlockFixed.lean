module

public import CFSG.LocalAnalysis.StandardType.GGSixRCK1416Defs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm

public section

namespace CFSG.StandardType.RCKC1

open CFSG.StandardType.ClassicalPosition

theorem blockOn_glBlockCentralizer_of_mul_eq_self {U ι F : Type} [Group U] [Fintype ι]
    [DecidableEq ι] [Field F] (j : U →* GL ι F) {s : GL ι F} {e : Matrix ι ι F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' {s})) e)
    (hse : (s : Matrix ι ι F) * e = e) :
    BlockOn (fun u v => (j u : Matrix ι ι F).mulVec v)
      (LinearMap.range (Matrix.toLin' e)) (LinearMap.ker (Matrix.toLin' e))
      (glBlockCentralizer j {s} e) := by
  classical
  let W : Submodule F (ι → F) := LinearMap.range (Matrix.toLin' e)
  let E : Submodule F (ι → F) := LinearMap.ker (Matrix.toLin' e)
  have hcomm_se : Commute (s : Matrix ι ι F) e :=
    Algebra.commute_of_mem_adjoin_of_forall_mem_commute (a := (s : Matrix ι ι F)) he.1 (by
      intro b hb
      obtain ⟨s', hs', rfl⟩ := hb
      rw [Set.mem_singleton_iff] at hs'
      subst hs'
      exact Commute.refl _)
  have hse' : e * (s : Matrix ι ι F) = (s : Matrix ι ι F) * e := hcomm_se.eq.symm
  have htoLin : Matrix.toLin' e * Matrix.toLin' e = Matrix.toLin' e := by
    change Matrix.toLin' e ∘ₗ Matrix.toLin' e = Matrix.toLin' e
    rw [← Matrix.toLin'_mul, he.2.1.eq]
  have hcompl : IsCompl W E := LinearMap.IsIdempotentElem.isCompl htoLin
  have hSW : ∀ w : ι → F, w ∈ W → (s : Matrix ι ι F).mulVec w = w := by
    intro w hw
    change w ∈ LinearMap.range (Matrix.toLin' e) at hw
    rw [LinearMap.mem_range] at hw
    obtain ⟨y, hy⟩ := hw
    rw [← hy, Matrix.toLin'_apply, Matrix.mulVec_mulVec y (s : Matrix ι ι F) e, hse]
  have hSE : ∀ x : ι → F, x ∈ E → (s : Matrix ι ι F).mulVec x ∈ E := by
    intro x hx
    change Matrix.toLin' e x = 0 at hx
    change Matrix.toLin' e ((s : Matrix ι ι F).mulVec x) = 0
    rw [Matrix.toLin'_apply]
    calc e.mulVec ((s : Matrix ι ι F).mulVec x)
        = (e * (s : Matrix ι ι F)).mulVec x :=
          Matrix.mulVec_mulVec x e (s : Matrix ι ι F)
      _ = ((s : Matrix ι ι F) * e).mulVec x := by rw [hse']
      _ = (s : Matrix ι ι F).mulVec (e.mulVec x) :=
          (Matrix.mulVec_mulVec x (s : Matrix ι ι F) e).symm
      _ = 0 := by
          rw [show e.mulVec x = 0 from by rwa [← Matrix.toLin'_apply], Matrix.mulVec_zero]
  have hsubE : ∀ v : ι → F, (1 - e).mulVec v ∈ E := by
    intro v
    change Matrix.toLin' e ((1 - e).mulVec v) = 0
    rw [Matrix.toLin'_apply]
    calc e.mulVec ((1 - e).mulVec v) = (e * (1 - e)).mulVec v :=
          Matrix.mulVec_mulVec v e (1 - e)
      _ = 0 := by
          rw [Matrix.mul_sub, Matrix.mul_one, he.2.1.eq, sub_self]
          exact Matrix.zero_mulVec v
  refine ⟨hcompl, ?_⟩
  intro u
  let U : Matrix ι ι F := ↑(j u)
  constructor
  · intro hu
    rw [glBlockCentralizer, Subgroup.mem_comap, Subgroup.mem_inf] at hu
    obtain ⟨hcent, hfix⟩ := hu
    have hcent' : U * (s : Matrix ι ι F) = (s : Matrix ι ι F) * U := by
      have h := congrArg (fun g : GL ι F => (g : Matrix ι ι F))
        (Subgroup.mem_centralizer_singleton_iff.mp hcent)
      simpa [Units.val_mul, U] using h
    have hUe : U * e = e * U := by
      have h1 : Commute U e :=
        Algebra.commute_of_mem_adjoin_of_forall_mem_commute (a := U) he.1 (by
          intro b hb
          obtain ⟨s', hs', rfl⟩ := hb
          rw [Set.mem_singleton_iff] at hs'
          subst hs'
          exact hcent')
      exact h1.eq
    constructor
    · intro w hw
      change w ∈ LinearMap.range (Matrix.toLin' e) at hw
      change U.mulVec w ∈ LinearMap.range (Matrix.toLin' e)
      rw [LinearMap.mem_range] at hw ⊢
      obtain ⟨y, hy⟩ := hw
      refine ⟨U.mulVec y, ?_⟩
      calc Matrix.toLin' e (U.mulVec y)
          = e.mulVec (U.mulVec y) := Matrix.toLin'_apply e _
        _ = (e * U).mulVec y := Matrix.mulVec_mulVec y e U
        _ = (U * e).mulVec y := by rw [hUe]
        _ = U.mulVec (e.mulVec y) := (Matrix.mulVec_mulVec y U e).symm
        _ = U.mulVec w := by rw [← Matrix.toLin'_apply e y, hy]
    · intro x hx
      change Matrix.toLin' e x = 0 at hx
      change U.mulVec x = x
      have hfix' : U * (1 - e) = 1 - e := hfix
      have hx' : (1 - e).mulVec x = x := by
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.toLin'_apply e x, hx, sub_zero]
      calc U.mulVec x = U.mulVec ((1 - e).mulVec x) := by rw [hx']
        _ = (U * (1 - e)).mulVec x := Matrix.mulVec_mulVec x U (1 - e)
        _ = (1 - e).mulVec x := by rw [hfix']
        _ = x := hx'
  · intro hu
    obtain ⟨hW, hE⟩ := hu
    have hW' : ∀ w : ι → F, w ∈ W → U.mulVec w ∈ W := by
      intro w hw
      exact hW w hw
    have hE' : ∀ x : ι → F, x ∈ E → U.mulVec x = x := by
      intro x hx
      exact hE x hx
    have hUfix : U * (1 - e) = 1 - e := by
      apply Matrix.mulVec_injective
      funext v
      rw [← Matrix.mulVec_mulVec]
      exact hE' ((1 - e).mulVec v) (hsubE v)
    have hUS : U * (s : Matrix ι ι F) = (s : Matrix ι ι F) * U := by
      apply Matrix.mulVec_injective
      funext v
      have hv : v ∈ W ⊔ E := by
        rw [hcompl.sup_eq_top]
        exact Submodule.mem_top
      obtain ⟨w, hw, x, hx, rfl⟩ := Submodule.mem_sup.mp hv
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      calc U.mulVec ((s : Matrix ι ι F).mulVec (w + x))
          = U.mulVec ((s : Matrix ι ι F).mulVec w +
              (s : Matrix ι ι F).mulVec x) := by rw [Matrix.mulVec_add]
        _ = U.mulVec (w + (s : Matrix ι ι F).mulVec x) := by rw [hSW w hw]
        _ = U.mulVec w + U.mulVec ((s : Matrix ι ι F).mulVec x) := by rw [Matrix.mulVec_add]
        _ = U.mulVec w + (s : Matrix ι ι F).mulVec x := by rw [hE' _ (hSE x hx)]
        _ = (s : Matrix ι ι F).mulVec (U.mulVec w) + (s : Matrix ι ι F).mulVec x := by
            rw [hSW _ (hW' w hw)]
        _ = (s : Matrix ι ι F).mulVec (U.mulVec w + x) := by rw [← Matrix.mulVec_add]
        _ = (s : Matrix ι ι F).mulVec (U.mulVec w + U.mulVec x) := by rw [hE' x hx]
        _ = (s : Matrix ι ι F).mulVec (U.mulVec (w + x)) := by
            conv_rhs => rw [Matrix.mulVec_add]
    rw [glBlockCentralizer, Subgroup.mem_comap, Subgroup.mem_inf]
    refine ⟨?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      apply Units.ext
      rw [Units.val_mul, Units.val_mul]
      exact hUS
    · change U * (1 - e) = 1 - e
      exact hUfix

theorem polar_eq_zero_of_formAdj_eq_self {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (Q : QuadraticForm F (ι → F))
    (hQ : IsUnit (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)).det)
    {e : Matrix ι ι F} (he : IsIdempotentElem e)
    (hadj : formAdj (RingHom.id F) (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)) e = e) :
    ∀ w ∈ LinearMap.range (Matrix.toLin' e), ∀ x ∈ LinearMap.ker (Matrix.toLin' e),
      QuadraticMap.polar Q w x = 0 := by
  intro w hw x hx
  let G : Matrix ι ι F := LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)
  have hww : w = e.mulVec w := by
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hw
    rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, he.eq]
  have hx' : e.mulVec x = 0 := by
    have h := LinearMap.mem_ker.mp hx
    rwa [Matrix.toLin'_apply] at h
  have htrans : Matrix.transpose e * G = G * e := by
    have h1 : G⁻¹ * Matrix.transpose e * G = e := by
      simpa [G, formAdj, Matrix.map_id] using hadj
    have h2 : G * e = Matrix.transpose e * G := by
      calc G * e = G * (G⁻¹ * Matrix.transpose e * G) := by rw [h1]
        _ = (G * G⁻¹) * Matrix.transpose e * G := by simp only [Matrix.mul_assoc]
        _ = 1 * Matrix.transpose e * G := by rw [Matrix.mul_nonsing_inv (A := G) hQ]
        _ = Matrix.transpose e * G := by rw [Matrix.one_mul]
    exact h2.symm
  have hpolar : QuadraticMap.polar Q (e.mulVec w) x = (e.mulVec w) ⬝ᵥ (G.mulVec x) := by
    have hG : G = LinearMap.BilinForm.toMatrix' (QuadraticMap.polarBilin Q) := rfl
    rw [hG, ← Matrix.toBilin'_apply'
      (LinearMap.BilinForm.toMatrix' (QuadraticMap.polarBilin Q)) (e.mulVec w) x,
      Matrix.toBilin'_toMatrix', QuadraticMap.polarBilin_apply_apply]
  rw [hww]
  calc QuadraticMap.polar Q (e.mulVec w) x
      = (e.mulVec w) ⬝ᵥ (G.mulVec x) := hpolar
    _ = Matrix.vecMul (G.mulVec x) e ⬝ᵥ w := by rw [dotProduct_comm, Matrix.dotProduct_mulVec]
    _ = (Matrix.mulVec (Matrix.transpose e) (G.mulVec x)) ⬝ᵥ w := by
          rw [show Matrix.vecMul (G.mulVec x) e =
              Matrix.mulVec (Matrix.transpose e) (G.mulVec x) from by
            simpa using Matrix.vecMul_transpose (A := Matrix.transpose e) (x := G.mulVec x)]
    _ = (Matrix.mulVec (Matrix.transpose e * G) x) ⬝ᵥ w := by
          rw [Matrix.mulVec_mulVec (v := x) (M := Matrix.transpose e) (N := G)]
    _ = (Matrix.mulVec (G * e) x) ⬝ᵥ w := by rw [htrans]
    _ = (Matrix.mulVec G (Matrix.mulVec e x)) ⬝ᵥ w := by
          rw [← Matrix.mulVec_mulVec (v := x) (M := G) (N := e)]
    _ = 0 := by rw [hx', Matrix.mulVec_zero, zero_dotProduct]

end CFSG.StandardType.RCKC1
