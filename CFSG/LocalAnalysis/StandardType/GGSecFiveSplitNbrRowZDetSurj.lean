module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowZDet

public section

namespace CFSG.StandardType

private theorem ggDetLin_of_surjective {p : ℕ} [Fact p.Prime] {H H' : Type} [CommGroup H]
    [CommGroup H'] [Finite H] [Module (ZMod p) (Additive H)] [Module (ZMod p) (Additive H')]
    {π : H →* H'} (hπ : Function.Surjective π) {c : MulAut H} {a : MulAut H'}
    (hca : ∀ x : H, π (c x) = a (π x)) (hfix : ∀ v ∈ π.ker, c v = v) :
    ggDetLin (p := p) c = ggDetLin (p := p) a := by
  let f : Additive H →ₗ[ZMod p] Additive H' :=
    AddMonoidHom.toZModLinearMap p (MonoidHom.toAdditive π)
  have hf : Function.Surjective f := fun y => by
    obtain ⟨x, hx⟩ := hπ (Additive.toMul y)
    exact ⟨Additive.ofMul x, congrArg Additive.ofMul hx⟩
  let T : Additive H →ₗ[ZMod p] Additive H :=
    ((ggLinAut (p := p) c : Additive H ≃ₗ[ZMod p] Additive H) : Additive H →ₗ[ZMod p] Additive H)
  let S : Additive H' →ₗ[ZMod p] Additive H' :=
    ((ggLinAut (p := p) a : Additive H' ≃ₗ[ZMod p] Additive H') :
      Additive H' →ₗ[ZMod p] Additive H')
  have hTS : ∀ x, f (T x) = S (f x) := fun x => congrArg Additive.ofMul (hca (Additive.toMul x))
  have he : LinearMap.ker f ≤ (LinearMap.ker f).comap T := fun x hx => by
    rw [Submodule.mem_comap, LinearMap.mem_ker, hTS, LinearMap.mem_ker.mp hx, map_zero]
  have hres : T.restrict he = LinearMap.id := by
    ext ⟨x, hx⟩
    refine congrArg Additive.ofMul (hfix (Additive.toMul x) ?_)
    exact (MonoidHom.mem_ker).mpr (Additive.ofMul.injective (LinearMap.mem_ker.mp hx))
  have hconj : ((f.quotKerEquivOfSurjective hf : _ →ₗ[ZMod p] _) ∘ₗ
      (LinearMap.ker f).mapQ (LinearMap.ker f) T he ∘ₗ
      ((f.quotKerEquivOfSurjective hf).symm : _ →ₗ[ZMod p] _)) = S := by
    refine LinearMap.ext fun y => ?_
    obtain ⟨x, rfl⟩ := hf y
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearMap.quotKerEquivOfSurjective_symm_apply]
    rw [Submodule.mapQ_apply, LinearMap.quotKerEquivOfSurjective_apply_mk, hTS]
  refine Units.ext ?_
  rw [ggDetLin, MonoidHom.comp_apply, ggDetLin, MonoidHom.comp_apply, LinearEquiv.coe_det,
    LinearEquiv.coe_det]
  show LinearMap.det T = LinearMap.det S
  rw [LinearMap.det_eq_det_mul_det (LinearMap.ker f) T he, hres, LinearMap.det_id, one_mul,
    ← hconj, LinearMap.det_conj]

theorem ggDetAut_of_surjective (p : ℕ) (hP : p.Prime) {H H' : Type} [Group H] [Group H']
    [Finite H] (hc : ∀ a b : H, a * b = b * a) (hp : ∀ a : H, a ^ p = 1)
    (hc' : ∀ a b : H', a * b = b * a) (hp' : ∀ a : H', a ^ p = 1) {π : H →* H'}
    (hπ : Function.Surjective π) {c : MulAut H} {a : MulAut H'}
    (hca : ∀ x : H, π (c x) = a (π x)) (hfix : ∀ v ∈ π.ker, c v = v) :
    ggDetAut p hP hc hp c = ggDetAut p hP hc' hp' a := by
  haveI : Fact p.Prime := ⟨hP⟩
  letI : CommGroup H := { (inferInstance : Group H) with mul_comm := hc }
  letI : CommGroup H' := { (inferInstance : Group H') with mul_comm := hc' }
  letI : Module (ZMod p) (Additive H) := AddCommGroup.zmodModule (n := p) fun a => by
    have h : (Additive.toMul a) ^ p = 1 := hp _
    rw [← ofMul_toMul a, ← ofMul_pow, h, ofMul_one]
  letI : Module (ZMod p) (Additive H') := AddCommGroup.zmodModule (n := p) fun a => by
    have h : (Additive.toMul a) ^ p = 1 := hp' _
    rw [← ofMul_toMul a, ← ofMul_pow, h, ofMul_one]
  show ggDetLin (p := p) (H := H) c = ggDetLin (p := p) (H := H') a
  exact ggDetLin_of_surjective (p := p) hπ hca hfix

end CFSG.StandardType

end
