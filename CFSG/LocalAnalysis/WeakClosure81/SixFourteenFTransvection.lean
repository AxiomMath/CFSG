module

public import CFSG.Milestones.ASVolI.H1
public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenN2F4General
public import CFSG.Quasithin.Background.D2Coprime
public import CFSG.GroupTheory.FixVConj
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenN2F4Module
public import CFSG.Quasithin.Background.A1cModuleCoprime
public import CFSG.Quasithin.Background.A3Structure312Facts
public import CFSG.Quasithin.Vol2.Ch4Sec4L443E12Map
public import CFSG.Quasithin.Vol2.Ch4Sec4L443E13Eq
public import CFSG.Quasithin.Vol2.Ch4Sec4L443EIn

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.ASVolI.ChH

variable {F M : Type*} [Field F] [AddCommGroup M] [Module F M]

@[expose] def IsFTransvectionOn (F M : Type*) [Field F] [AddCommGroup M] [Module F M]
    (t : MulAut (Multiplicative M)) : Prop :=
  ∃ g : M ≃ₗ[F] M, linToMulAut F M g = t ∧
    Module.finrank F (LinearMap.range (g.toLinearMap - LinearMap.id)) = 1 ∧
    (g.toLinearMap - LinearMap.id) ∘ₗ (g.toLinearMap - LinearMap.id) = 0

theorem linToMulAut_ofAdd (g : M ≃ₗ[F] M) (m : M) :
    linToMulAut F M g (Multiplicative.ofAdd m) =
      Multiplicative.ofAdd (g.toLinearMap m) := rfl

@[expose] def fixVSub (t : MulAut (Multiplicative M)) : Submodule F M :=
  Submodule.span F {m | Multiplicative.ofAdd m ∈ fixV (Subgroup.zpowers t)}

theorem fixVSub_linToMulAut (g : M ≃ₗ[F] M) :
    fixVSub (F := F) (linToMulAut F M g) = LinearMap.ker (g.toLinearMap - LinearMap.id) := by
  set u : M →ₗ[F] M := g.toLinearMap - LinearMap.id with hu
  have hker : LinearMap.ker (g.toLinearMap - LinearMap.id) = LinearMap.ker u := by rw [hu]
  rw [hker]
  apply le_antisymm
  · unfold fixVSub
    rw [Submodule.span_le]
    intro m hm
    rw [Set.mem_setOf_eq, mem_fixV_zpowers_iff, linToMulAut_ofAdd] at hm
    refine LinearMap.mem_ker.mpr ?_
    rw [show u m = g.toLinearMap m - m from rfl]
    exact sub_eq_zero.mpr (Multiplicative.ofAdd.injective hm)
  · intro m hm
    rw [LinearMap.mem_ker] at hm
    refine Submodule.subset_span ?_
    rw [Set.mem_setOf_eq, mem_fixV_zpowers_iff, linToMulAut_ofAdd]
    have h : g.toLinearMap m = m := by
      rw [show u m = g.toLinearMap m - m from rfl] at hm
      exact sub_eq_zero.mp hm
    rw [h]

variable {t : MulAut (Multiplicative M)}

theorem IsFTransvectionOn.fixV_finrank [FiniteDimensional F M]
    (h : IsFTransvectionOn F M t) :
    Module.finrank F (fixVSub (F := F) t) = Module.finrank F M - 1 := by
  obtain ⟨g, rfl, hrank, -⟩ := h
  rw [fixVSub_linToMulAut]
  have hrn := LinearMap.finrank_range_add_finrank_ker (g.toLinearMap - LinearMap.id)
  rw [hrank] at hrn
  omega

theorem IsFTransvectionOn.involutive (h : IsFTransvectionOn F M t) (h2 : (2 : F) = 0) :
    t * t = 1 := by
  obtain ⟨g, rfl, hrank, hsq⟩ := h
  set u : M →ₗ[F] M := g.toLinearMap - LinearMap.id with hu
  have hu2 : ∀ y : M, u (u y) = 0 := fun y => by
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using
      congrArg (fun f : M →ₗ[F] M => f y) hsq
  have hgx : ∀ y : M, g.toLinearMap y = y + u y := fun y => by
    rw [show u y = g.toLinearMap y - y from rfl]
    abel
  have h2u : ∀ y : M, u y + u y = 0 := fun y => by
    have h : (2 : F) • (u y) = 0 := by rw [h2, zero_smul]
    rwa [two_smul] at h
  have hgg : g * g = 1 := by
    apply LinearEquiv.ext
    intro x
    calc (g * g) x = g.toLinearMap (g.toLinearMap x) := LinearEquiv.mul_apply g g x
      _ = g.toLinearMap (x + u x) := by rw [hgx x]
      _ = g.toLinearMap x + g.toLinearMap (u x) := by rw [map_add]
      _ = (x + u x) + (u x + u (u x)) := by rw [hgx x, hgx (u x)]
      _ = x := by rw [hu2 x, add_zero, add_assoc, h2u x, add_zero]
  rw [← map_mul, hgg]
  exact map_one (f := linToMulAut F M)

end CFSG.LocalAnalysis.WeakClosure81
