module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleRestrict
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

namespace CFSG.StandardType

private lemma l05nC2b_res_injective
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    [Module.Finite (ZMod p) V] (U : Submodule (ZMod p) V)
    (hdim : Module.finrank (ZMod p) V ≤ Module.finrank (ZMod p) U + 1)
    (A : Subgroup (V ≃ₗ[ZMod p] V)) (hA : ∀ a ∈ A, ∀ w, a w - w ∈ U)
    (hnt : ∀ a ∈ A, ¬ (Module.finrank (ZMod p) (ggLinMove a) = 1 ∧
      ∀ w, a (a w - w) = a w - w))
    (r : ↥A →* (↥U ≃ₗ[ZMod p] ↥U))
    (hr : ∀ (a : ↥A) (u : ↥U),
      ((r a u : ↥U) : V) = (a : V ≃ₗ[ZMod p] V) u) :
    Function.Injective r := by
  have hker : ∀ a : ↥A, r a = 1 → a = 1 := by
    intro a hra
    have hfix : ∀ u ∈ U, (a : V ≃ₗ[ZMod p] V) u = u := by
      intro u hu
      let uu : ↥U := ⟨u, hu⟩
      have h1 : ((r a uu : ↥U) : V) = u := by
        rw [hra]; rfl
      have h2 := hr a uu
      rw [h1] at h2
      exact h2.symm
    let N : V →ₗ[ZMod p] V := (a : V ≃ₗ[ZMod p] V).toLinearMap - LinearMap.id
    have hNker : U ≤ LinearMap.ker N := by
      intro u hu
      rw [LinearMap.mem_ker]
      change (a : V ≃ₗ[ZMod p] V) u - u = 0
      rw [hfix u hu, sub_self]
    have hNrange : LinearMap.range N ≤ U := by
      rintro y ⟨w, rfl⟩
      change (a : V ≃ₗ[ZMod p] V) w - w ∈ U
      exact hA (a : V ≃ₗ[ZMod p] V) a.2 w
    have hkerdim : Module.finrank (ZMod p) U ≤ Module.finrank (ZMod p) (LinearMap.ker N) :=
      Submodule.finrank_mono hNker
    have hrank := LinearMap.finrank_range_add_finrank_ker N
    have hrange_le : Module.finrank (ZMod p) (LinearMap.range N) ≤ 1 := by
      omega
    have hrange : LinearMap.range N = ⊥ := by
      rcases Nat.eq_zero_or_pos (Module.finrank (ZMod p) (LinearMap.range N)) with h0 | hpos
      · exact Submodule.finrank_eq_zero.mp h0
      · exfalso
        have h1 : Module.finrank (ZMod p) (LinearMap.range N) = 1 := by omega
        apply hnt (a : V ≃ₗ[ZMod p] V) a.2
        refine ⟨?_, ?_⟩
        · rw [ggLinMove]; exact h1
        · intro w
          have hNw : N w ∈ U := hNrange (LinearMap.mem_range_self N w)
          have hz : N (N w) = 0 := LinearMap.mem_ker.mp (hNker hNw)
          rw [LinearMap.sub_apply, LinearMap.id_apply] at hz
          exact sub_eq_zero.mp hz
    have hN0 : N = 0 := by
      rw [← LinearMap.range_eq_bot]
      exact hrange
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    have hv : N v = 0 := by rw [hN0]; rfl
    change (a : V ≃ₗ[ZMod p] V) v - v = 0 at hv
    exact sub_eq_zero.mp hv
  intro a b hab
  have h1 : r (a * b⁻¹) = 1 := by
    rw [map_mul, map_inv, hab, mul_inv_cancel]
  have h2 : a * b⁻¹ = 1 := hker (a * b⁻¹) h1
  calc a = (a * b⁻¹) * b := by simp [mul_assoc]
    _ = 1 * b := by rw [h2]
    _ = b := by simp

private lemma l05nC2b_refl_restrict
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    [Module.Finite (ZMod p) V] (U : Submodule (ZMod p) V)
    (A : Subgroup (V ≃ₗ[ZMod p] V))
    (r : ↥A →* (↥U ≃ₗ[ZMod p] ↥U))
    (hr : ∀ (a : ↥A) (u : ↥U),
      ((r a u : ↥U) : V) = (a : V ≃ₗ[ZMod p] V) u)
    (hinj : Function.Injective r)
    (a : ↥A) (ha : GGLinRefl (a : V ≃ₗ[ZMod p] V)) :
    GGLinRefl (r a) := by
  have haA : a * a = 1 := by
    apply Subtype.ext
    simpa [Subgroup.coe_mul] using ha.1
  have hinv : r a * r a = 1 := by
    rw [← map_mul, haA, map_one]
  have hmap_le : Submodule.map U.subtype (ggLinMove (r a)) ≤
      ggLinMove (a : V ≃ₗ[ZMod p] V) := by
    rintro y ⟨u, hu, rfl⟩
    rw [ggLinMove] at hu
    rcases hu with ⟨v, hv⟩
    rw [← hv]
    refine LinearMap.mem_range.mpr ⟨(v : V), ?_⟩
    change (a : V ≃ₗ[ZMod p] V) (v : V) - (v : V) =
      ((U.subtype ((r a).toLinearMap v - v)) : V)
    rw [map_sub]
    change (a : V ≃ₗ[ZMod p] V) (v : V) - (v : V) =
      (((r a) v : ↥U) : V) - ((v : ↥U) : V)
    rw [hr a v]
  have hle : Module.finrank (ZMod p) (ggLinMove (r a)) ≤
      Module.finrank (ZMod p) (ggLinMove (a : V ≃ₗ[ZMod p] V)) := by
    rw [← Submodule.finrank_map_subtype_eq U (ggLinMove (r a))]
    exact Submodule.finrank_mono hmap_le
  have hMne : ggLinMove (r a) ≠ ⊥ := by
    intro hbot
    have hM0 : (r a).toLinearMap - LinearMap.id = 0 := by
      rw [← LinearMap.range_eq_bot]
      exact hbot
    have hra1 : r a = 1 := by
      apply LinearEquiv.ext
      intro u
      have h := LinearMap.congr_fun hM0 u
      simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.zero_apply] at h
      exact sub_eq_zero.mp h
    have ha1 : a = 1 := hinj (hra1.trans (map_one r).symm)
    have hco : (a : V ≃ₗ[ZMod p] V) = 1 := by
      rw [ha1]; rfl
    have hz : ggLinMove (1 : V ≃ₗ[ZMod p] V) = ⊥ := by
      rw [ggLinMove]
      exact LinearMap.range_eq_bot.mpr (by simp)
    have hzero : Module.finrank (ZMod p) (ggLinMove (a : V ≃ₗ[ZMod p] V)) = 0 := by
      rw [hco, hz]
      simp
    have hfin : Module.finrank (ZMod p) (ggLinMove (a : V ≃ₗ[ZMod p] V)) = 1 := ha.2
    rw [hzero] at hfin
    exact Nat.zero_ne_one hfin
  have hpos : 0 < Module.finrank (ZMod p) (ggLinMove (r a)) :=
    Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hMne)
  have hle1 : Module.finrank (ZMod p) (ggLinMove (r a)) ≤ 1 := hle.trans (le_of_eq ha.2)
  refine ⟨hinv, ?_⟩
  omega

theorem ggRC_restrict_equiv {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] [Module.Finite (ZMod p) V] (U : Submodule (ZMod p) V)
    (hdim : Module.finrank (ZMod p) V ≤ Module.finrank (ZMod p) U + 1)
    (A : Subgroup (V ≃ₗ[ZMod p] V)) (hA : ∀ a ∈ A, ∀ w, a w - w ∈ U)
    (hnt : ∀ a ∈ A, ¬ (Module.finrank (ZMod p) (ggLinMove a) = 1 ∧
      ∀ w, a (a w - w) = a w - w)) :
    ∃ (AU : Subgroup (U ≃ₗ[ZMod p] U)) (e : A ≃* AU),
      (∀ (a : A) (u : U), (((e a : U ≃ₗ[ZMod p] U) u : U) : V) = (a : V ≃ₗ[ZMod p] V) u) ∧
      ∀ a : A, GGLinRefl (a : V ≃ₗ[ZMod p] V) → GGLinRefl ((e a : AU) : U ≃ₗ[ZMod p] U) := by
  have hU : ∀ a ∈ A, ∀ u ∈ U, a u ∈ U := by
    intro a ha u hu
    have h := hA a ha u
    have h' : a u = (a u - u) + u := (sub_add_cancel (a u) u).symm
    rw [h']
    exact U.add_mem h hu
  obtain ⟨r, hr⟩ := ggLin_restrict_exists A U hU
  have hinj : Function.Injective r :=
    l05nC2b_res_injective U hdim A hA hnt r hr
  let AU : Subgroup (U ≃ₗ[ZMod p] U) := r.range
  let e : A ≃* AU := MonoidHom.ofInjective (f := r) hinj
  refine ⟨AU, e, ?_, ?_⟩
  · intro a u
    have hcoe : ((e a : AU) : U ≃ₗ[ZMod p] U) = r a :=
      MonoidHom.ofInjective_apply (f := r) hinj
    rw [hcoe]
    exact hr a u
  · intro a ha
    have hcoe : ((e a : AU) : U ≃ₗ[ZMod p] U) = r a :=
      MonoidHom.ofInjective_apply (f := r) hinj
    rw [hcoe]
    exact l05nC2b_refl_restrict U A r hr hinj a ha

end CFSG.StandardType

end
