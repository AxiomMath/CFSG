module

public import CFSG.Quasithin.EmptyFaithful.SzN31CntLinB

public section

namespace CFSG.Quasithin.G92

open CFSG.Quasithin.SzN31 CFSG.Quasithin.SzN31.CntLin

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem commSp_le_fixSp {c : V ≃ₗ[ZMod 2] V} (hcc : c * c = 1) {T : Submodule (ZMod 2) V}
    (hcT : ∀ t ∈ T, c t ∈ T) : commSp V c T ≤ fixSp V c T := by
  intro v hv
  obtain ⟨s, hs, rfl⟩ := mem_commSp.1 hv
  refine mem_fixSp.2 ⟨sub_mem (hcT s hs) hs, ?_⟩
  have hcs : c (c s) = s := by
    rw [← LinearEquiv.mul_apply, hcc]
    rfl
  rw [map_sub, hcs]
  have := zmod2_neg (c s - s)
  rw [neg_sub] at this
  exact this

theorem two_mul_finrank_commSp_le [Finite V] {c : V ≃ₗ[ZMod 2] V} (hcc : c * c = 1)
    {T : Submodule (ZMod 2) V} (hcT : ∀ t ∈ T, c t ∈ T) :
    2 * Module.finrank (ZMod 2) (commSp V c T) ≤ Module.finrank (ZMod 2) T := by
  haveI : Module.Finite (ZMod 2) T := Module.Finite.of_finite
  set f : T →ₗ[ZMod 2] V := ((c : V →ₗ[ZMod 2] V) - 1).domRestrict T with hf
  have hrk := LinearMap.finrank_range_add_finrank_ker f
  have hrange : LinearMap.range f = commSp V c T := by
    rw [hf, LinearMap.range_domRestrict]
    rfl
  have hker : Module.finrank (ZMod 2) (LinearMap.ker f) =
      Module.finrank (ZMod 2) (fixSp V c T) := by
    have : (LinearMap.ker f).map T.subtype = fixSp V c T := by
      ext v
      simp only [Submodule.mem_map, LinearMap.mem_ker, hf, LinearMap.domRestrict_apply,
        LinearMap.sub_apply, LinearMap.coe_coe, Module.End.one_apply, sub_eq_zero, fixSp,
        Submodule.mem_inf, Submodule.coe_subtype]
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ⟨t.2, ht⟩
      · rintro ⟨hvT, hv⟩
        exact ⟨⟨v, hvT⟩, hv, rfl⟩
    rw [← this]
    exact (Submodule.finrank_map_subtype_eq T _).symm
  have hle : Module.finrank (ZMod 2) (commSp V c T) ≤ Module.finrank (ZMod 2) (fixSp V c T) :=
    Submodule.finrank_mono (commSp_le_fixSp hcc hcT)
  rw [hrange, hker] at hrk
  omega

theorem invol_trivial [Finite V] {x c : V ≃ₗ[ZMod 2] V} {p : ℕ} (hp : p.Prime) (hxp : x ^ p = 1)
    (hcc : c * c = 1) (hcx : c * x = x * c) (T : Submodule (ZMod 2) V)
    (hxT : ∀ t ∈ T, x t ∈ T) (hcT : ∀ t ∈ T, c t ∈ T) (hfp : ∀ t ∈ T, x t = t → t = 0)
    (hk : ∀ k : ℕ, 1 ≤ k → 2 * k ≤ Module.finrank (ZMod 2) T → ¬ p ∣ 2 ^ k - 1) :
    ∀ t ∈ T, c t = t := by
  have hR_x : ∀ v ∈ commSp V c T, x v ∈ commSp V c T := commSp_invariant hcx.symm hxT
  have hRT : commSp V c T ≤ T := commSp_le hcT
  have hfpR : ∀ v ∈ commSp V c T, x v = v → v = 0 := fun v hv hxv => hfp v (hRT hv) hxv
  have hdvd := cyclic_dvd_two_pow hp x hxp (commSp V c T) hR_x hfpR
  have h2 := two_mul_finrank_commSp_le hcc hcT
  have hbot : commSp V c T = ⊥ := by
    by_contra hne
    haveI : Module.Finite (ZMod 2) (commSp V c T) := Module.Finite.of_finite
    have hpos : 1 ≤ Module.finrank (ZMod 2) (commSp V c T) :=
      Submodule.one_le_finrank_iff.2 hne
    exact hk _ hpos h2 hdvd
  intro t ht
  have hmem : c t - t ∈ commSp V c T := mem_commSp.2 ⟨t, ht, rfl⟩
  rw [hbot, Submodule.mem_bot, sub_eq_zero] at hmem
  exact hmem

theorem no_dvd_three {n : ℕ} (hn : n ≤ 3) : ∀ k : ℕ, 1 ≤ k → 2 * k ≤ n → ¬ 3 ∣ 2 ^ k - 1 := by
  intro k hk1 hk2
  have : k = 1 := by omega
  subst this
  decide

theorem no_dvd_five {n : ℕ} (hn : n ≤ 7) : ∀ k : ℕ, 1 ≤ k → 2 * k ≤ n → ¬ 5 ∣ 2 ^ k - 1 := by
  intro k hk1 hk2
  have : k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases this with rfl | rfl | rfl <;> decide

end CFSG.Quasithin.G92
