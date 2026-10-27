module

public import CFSG.LocalAnalysis.StandardType.GGA11FrameDefs

public section

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.A8Coord Matrix
open scoped BigOperators

namespace CFSG.StandardType.A11

noncomputable section

private def a11ga_form : LinearMap.BilinForm (ZMod 2) GGSL9V :=
  ∑ i : Fin 3,
    (Algebra.traceForm (ZMod 2) (GaloisField 2 3)).comp (LinearMap.proj i) (LinearMap.proj i)

private theorem a11ga_form_apply (x y : GGSL9V) :
    a11ga_form x y = ∑ i, Algebra.traceForm (ZMod 2) (GaloisField 2 3) (x i) (y i) := by
  simp [a11ga_form, LinearMap.BilinForm.comp_apply]

private theorem a11ga_form_comm (x y : GGSL9V) : a11ga_form x y = a11ga_form y x := by
  rw [a11ga_form_apply, a11ga_form_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.traceForm_apply, Algebra.traceForm_apply, mul_comm]

private theorem a11ga_form_single (x : GGSL9V) (k : Fin 3) (w : GaloisField 2 3) :
    a11ga_form x (Pi.single k w) =
      Algebra.traceForm (ZMod 2) (GaloisField 2 3) (x k) w := by
  rw [a11ga_form_apply]
  rw [Finset.sum_eq_single k (fun i _ hi => by rw [Pi.single_eq_of_ne hi]; simp)
    (fun hk => absurd (Finset.mem_univ k) hk)]
  simp

private theorem a11ga_form_sepLeft : a11ga_form.SeparatingLeft := by
  intro x hx
  funext k
  have ht : ∀ w : GaloisField 2 3,
      Algebra.traceForm (ZMod 2) (GaloisField 2 3) (x k) w = 0 := by
    intro w
    have h := hx (Pi.single k w)
    rwa [a11ga_form_single] at h
  exact (traceForm_nondegenerate (ZMod 2) (GaloisField 2 3)).1 (x k) ht

private theorem a11ga_form_nondegenerate : a11ga_form.Nondegenerate :=
  ⟨a11ga_form_sepLeft, fun y hy =>
    a11ga_form_sepLeft y fun z => by rw [a11ga_form_comm y z]; exact hy z⟩

private def a11ga_adjLin (φ : Module.End (ZMod 2) GGSL9V) : Module.End (ZMod 2) GGSL9V :=
  a11ga_form.leftAdjointOfNondegenerate a11ga_form_nondegenerate φ

private theorem a11ga_isAdjoint_adjLin (φ : Module.End (ZMod 2) GGSL9V) :
    LinearMap.IsAdjointPair a11ga_form a11ga_form (a11ga_adjLin φ) φ :=
  a11ga_form.isAdjointPairLeftAdjointOfNondegenerate a11ga_form_nondegenerate φ

private theorem a11ga_adjLin_mul (φ ψ : Module.End (ZMod 2) GGSL9V) :
    a11ga_adjLin (φ * ψ) = a11ga_adjLin ψ * a11ga_adjLin φ := by
  apply LinearMap.BilinForm.isAdjointPair_unique_of_nondegenerate a11ga_form
    a11ga_form_nondegenerate (φ * ψ)
  · exact a11ga_isAdjoint_adjLin (φ * ψ)
  · exact (a11ga_isAdjoint_adjLin ψ).mul (a11ga_isAdjoint_adjLin φ)

private theorem a11ga_adjLin_one : a11ga_adjLin (1 : Module.End (ZMod 2) GGSL9V) = 1 := by
  apply LinearMap.BilinForm.isAdjointPair_unique_of_nondegenerate a11ga_form
    a11ga_form_nondegenerate 1
  · exact a11ga_isAdjoint_adjLin 1
  · exact LinearMap.isAdjointPair_one

private theorem a11ga_isAdjoint_swap (φ : Module.End (ZMod 2) GGSL9V) :
    LinearMap.IsAdjointPair a11ga_form a11ga_form φ (a11ga_adjLin φ) := by
  intro x y
  have h := a11ga_isAdjoint_adjLin φ y x
  rw [a11ga_form_comm (φ x) y, ← h, a11ga_form_comm (a11ga_adjLin φ y) x]

private theorem a11ga_adjLin_adjLin (φ : Module.End (ZMod 2) GGSL9V) :
    a11ga_adjLin (a11ga_adjLin φ) = φ := by
  apply LinearMap.BilinForm.isAdjointPair_unique_of_nondegenerate a11ga_form
    a11ga_form_nondegenerate (a11ga_adjLin φ)
  · exact a11ga_isAdjoint_adjLin (a11ga_adjLin φ)
  · exact a11ga_isAdjoint_swap φ

private def a11ga_adjEquiv (g : GLV) : GLV :=
  LinearEquiv.ofLinearMap (a11ga_adjLin g.toLinearMap) (a11ga_adjLin (g⁻¹).toLinearMap)
    (by
      show a11ga_adjLin g.toLinearMap * a11ga_adjLin (g⁻¹).toLinearMap = LinearMap.id
      rw [← a11ga_adjLin_mul (g⁻¹).toLinearMap g.toLinearMap,
        ← LinearEquiv.coe_toLinearMap_mul, inv_mul_cancel]
      exact a11ga_adjLin_one)
    (by
      show a11ga_adjLin (g⁻¹).toLinearMap * a11ga_adjLin g.toLinearMap = LinearMap.id
      rw [← a11ga_adjLin_mul g.toLinearMap (g⁻¹).toLinearMap,
        ← LinearEquiv.coe_toLinearMap_mul, mul_inv_cancel]
      exact a11ga_adjLin_one)

private theorem a11ga_adjEquiv_toLinearMap (g : GLV) :
    (a11ga_adjEquiv g).toLinearMap = a11ga_adjLin g.toLinearMap := rfl

private theorem a11ga_adjEquiv_inv_toLinearMap (g : GLV) :
    ((a11ga_adjEquiv g)⁻¹).toLinearMap = a11ga_adjLin (g⁻¹).toLinearMap := rfl

private theorem a11ga_adjEquiv_inv (g : GLV) :
    (a11ga_adjEquiv g)⁻¹ = a11ga_adjEquiv g⁻¹ := by
  apply LinearEquiv.toLinearMap_injective
  rw [a11ga_adjEquiv_inv_toLinearMap, a11ga_adjEquiv_toLinearMap]

private theorem a11ga_adjEquiv_mul (g h : GLV) :
    a11ga_adjEquiv (g * h) = a11ga_adjEquiv h * a11ga_adjEquiv g := by
  apply LinearEquiv.toLinearMap_injective
  show a11ga_adjLin ((g * h).toLinearMap) =
    a11ga_adjLin h.toLinearMap * a11ga_adjLin g.toLinearMap
  rw [LinearEquiv.coe_toLinearMap_mul, a11ga_adjLin_mul]

private theorem a11ga_adjEquiv_invol (g : GLV) : a11ga_adjEquiv (a11ga_adjEquiv g) = g := by
  apply LinearEquiv.toLinearMap_injective
  rw [a11ga_adjEquiv_toLinearMap, a11ga_adjEquiv_toLinearMap, a11ga_adjLin_adjLin]

private theorem a11ga_tC_isAdjoint (c : Fin 3 → ZMod 7) :
    LinearMap.IsAdjointPair a11ga_form a11ga_form (tC c).toLinearMap (tC c).toLinearMap := by
  intro x y
  rw [a11ga_form_apply, a11ga_form_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.traceForm_apply, Algebra.traceForm_apply]
  congr 1
  change ggSL9TorusCoord (Multiplicative.ofAdd c) x i * y i =
    x i * ggSL9TorusCoord (Multiplicative.ofAdd c) y i
  rw [ggSL9TorusCoord_apply, ggSL9TorusCoord_apply]
  ring

private theorem a11ga_adjLin_tC (c : Fin 3 → ZMod 7) :
    a11ga_adjLin (tC c).toLinearMap = (tC c).toLinearMap := by
  apply LinearMap.BilinForm.isAdjointPair_unique_of_nondegenerate a11ga_form
    a11ga_form_nondegenerate (tC c).toLinearMap
  · exact a11ga_isAdjoint_adjLin (tC c).toLinearMap
  · exact a11ga_tC_isAdjoint c

private theorem a11ga_adjEquiv_tC (c : Fin 3 → ZMod 7) : a11ga_adjEquiv (tC c) = tC c := by
  apply LinearEquiv.toLinearMap_injective
  rw [a11ga_adjEquiv_toLinearMap, a11ga_adjLin_tC]

private theorem a11ga_tC_inv (c : Fin 3 → ZMod 7) : (tC c)⁻¹ = tC (-c) := by
  change (ggSL9TorusCoord (Multiplicative.ofAdd c))⁻¹ =
    ggSL9TorusCoord (Multiplicative.ofAdd (-c))
  rw [← map_inv, ofAdd_neg]
  try rfl

private def a11ga_gamma : MulAut GLV where
  toFun g := a11ga_adjEquiv (g⁻¹)
  invFun g := a11ga_adjEquiv (g⁻¹)
  left_inv g := by
    show a11ga_adjEquiv ((a11ga_adjEquiv (g⁻¹))⁻¹) = g
    rw [a11ga_adjEquiv_inv (g⁻¹), inv_inv, a11ga_adjEquiv_invol]
  right_inv g := by
    show a11ga_adjEquiv ((a11ga_adjEquiv (g⁻¹))⁻¹) = g
    rw [a11ga_adjEquiv_inv (g⁻¹), inv_inv, a11ga_adjEquiv_invol]
  map_mul' g h := by
    show a11ga_adjEquiv ((g * h)⁻¹) =
      a11ga_adjEquiv (g⁻¹) * a11ga_adjEquiv (h⁻¹)
    rw [mul_inv_rev g h, a11ga_adjEquiv_mul]

theorem a11GraphAutInput_holds : ∃ γ : MulAut GLV, ∀ c : Fin 3 → ZMod 7, γ (tC c) = tC (-c) := by
  refine ⟨a11ga_gamma, fun c => ?_⟩
  show a11ga_gamma (tC c) = tC (-c)
  change a11ga_adjEquiv ((tC c)⁻¹) = tC (-c)
  rw [← a11ga_adjEquiv_inv (tC c), a11ga_adjEquiv_tC c]
  exact a11ga_tC_inv c

end

end CFSG.StandardType.A11

end
