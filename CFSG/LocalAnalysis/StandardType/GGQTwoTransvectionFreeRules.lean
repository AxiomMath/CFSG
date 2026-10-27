module

public import CFSG.LocalAnalysis.StandardType.GGQTwoReflLin

public section

namespace CFSG.StandardType.QTwoLin

theorem zero_pair_iff_of_transvectionFree {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [CharP K 3] {H : Subgroup (V ≃ₗ[K] V)}
    (hH : TransvectionFree H) {r s : V ≃ₗ[K] V} (hr : r ∈ H) (hs : s ∈ H)
    {u w : V} {φ ψ : Module.Dual K V} (hφu : φ u = 2) (hψw : ψ w = 2)
    (hrf : ∀ v, r v = v - φ v • u) (hsf : ∀ v, s v = v - ψ v • w) :
    φ w = 0 ↔ ψ u = 0 := by
  have hr' : r = Module.reflection hφu :=
    LinearEquiv.ext fun v => by rw [hrf v, Module.reflection_apply]
  have hs' : s = Module.reflection hψw :=
    LinearEquiv.ext fun v => by rw [hsf v, Module.reflection_apply]
  constructor
  · intro hφw
    by_contra hψu
    have htv := transvection_of_pair (K := K) (c := u) (h := w)
      (φ := φ) (α := ψ) hφu hψw hφw hψu
    refine hH ((r * s) ^ 2) (H.pow_mem (H.mul_mem hr hs) 2) ?_
    simpa only [hr', hs'] using htv
  · intro hψu
    by_contra hφw
    have htv := transvection_of_pair (K := K) (c := w) (h := u)
      (φ := ψ) (α := φ) hψw hφu hψu hφw
    refine hH ((s * r) ^ 2) (H.pow_mem (H.mul_mem hs hr) 2) ?_
    simpa only [hr', hs'] using htv

theorem eq_form_of_same_root_of_transvectionFree {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [CharP K 3] {H : Subgroup (V ≃ₗ[K] V)}
    (hH : TransvectionFree H) {r s : V ≃ₗ[K] V} (hr : r ∈ H) (hs : s ∈ H)
    {u : V} {φ ψ : Module.Dual K V} (hφu : φ u = 2) (hψu : ψ u = 2)
    (hrf : ∀ v, r v = v - φ v • u) (hsf : ∀ v, s v = v - ψ v • u) :
    φ = ψ := by
  have hr' : r = Module.reflection hφu :=
    LinearEquiv.ext fun v => by rw [hrf v, Module.reflection_apply]
  have hs' : s = Module.reflection hψu :=
    LinearEquiv.ext fun v => by rw [hsf v, Module.reflection_apply]
  by_contra hne
  have htv := transvection_of_same_centre (K := K) (c := u) (φ := φ) (φ' := ψ)
    hφu hψu hne
  refine hH (s * r) (H.mul_mem hs hr) ?_
  simpa only [hr', hs'] using htv

end CFSG.StandardType.QTwoLin
