module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExtPlaneLeaf
public import CFSG.LocalAnalysis.StandardType.GGQ2ExtCoverFrame
public import CFSG.LocalAnalysis.StandardType.GGWAutModelNorm
public import TauCeti.LinearAlgebra.Matrix.Cartan.Classical

public section

namespace CFSG.StandardType.GGQ2Frame

open CFSG CFSG.Assembly Module PlaneRaw

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

theorem extInner_A1_signed (hNb : NbrChainSigned) {kd : PlaneKind} (hkd : kd ≠ .orthogonal 0)
    {t : ℕ} (ht : 4 ≤ t) {vx z : V t} {ℓ j k : Code t} {U : Submodule F (V t)}
    (h : ExtShapeA1 vx ℓ U j z k) : ExtInnerAt (planeEntry kd t) z k := by
  obtain ⟨a, c, s, s', hac, hs, hs', hvx, hz, hℓ, hj, hk, hU⟩ := h
  obtain ⟨W, f, hcart, hweyl, hker⟩ := hNb t ht c
  have hspan : Submodule.span F {z} = Submodule.span F {(Pi.single c 1 : V t)} := by
    rw [hz]
    exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hs') _
  have hdet : W.cartan.det = 2 := by
    have hsub : W.cartan.submatrix f f = CartanMatrix.B (t - 1) := Matrix.ext fun p q => hcart p q
    rw [← Matrix.det_submatrix_equiv_self f W.cartan, hsub]
    exact CartanMatrix.B_det (by omega)
  refine ⟨W, ⟨?_, ?_⟩, ?_, t - 1, CartanMatrix.B (t - 1), f, hcart, ggQ2WeylInner_B (by omega)⟩
  · show W.toLin.weyl = PlaneRaw.normalizerOf kd t k
    rw [hweyl, hk, normalizerOf_zero_erase_signed hkd ht c]
  · intro v
    exact (hker v).trans (Iff.of_eq (congrArg (fun S => v ∈ S) hspan.symm))
  · rw [hdet]
    decide

theorem extInner_A1_even (hNe : NbrChainEvenSigned) {t : ℕ} (ht : 5 ≤ t) (hodd : Odd (t - 1))
    {vx z : V t} {ℓ j k : Code t} {U : Submodule F (V t)} (h : ExtShapeA1 vx ℓ U j z k) :
    ExtInnerAt (planeEntry (.orthogonal 0) t) z k := by
  obtain ⟨a, c, s, s', hac, hs, hs', hvx, hz, hℓ, hj, hk, hU⟩ := h
  obtain ⟨W, f, hcart, hweyl, hker⟩ := hNe t ht c
  have h5 : 5 ≤ t - 1 := by
    obtain ⟨m, hm⟩ := hodd
    omega
  have hspan : Submodule.span F {z} = Submodule.span F {(Pi.single c 1 : V t)} := by
    rw [hz]
    exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hs') _
  have hdet : W.cartan.det = 4 := by
    have hsub : W.cartan.submatrix f f = CartanMatrix.D (t - 1) := Matrix.ext fun p q => hcart p q
    rw [← Matrix.det_submatrix_equiv_self f W.cartan, hsub]
    exact CartanMatrix.D_det (by omega)
  refine ⟨W, ⟨?_, ?_⟩, ?_, t - 1, CartanMatrix.D (t - 1), f, hcart, ggQ2WeylInner_D_odd h5 hodd⟩
  · show W.toLin.weyl = PlaneRaw.normalizerOf (.orthogonal 0) t k
    rw [hweyl, hk, normalizerOf_zero_even]
  · intro v
    exact (hker v).trans (Iff.of_eq (congrArg (fun S => v ∈ S) hspan.symm))
  · rw [hdet]
    decide

end

end CFSG.StandardType.GGQ2Frame
