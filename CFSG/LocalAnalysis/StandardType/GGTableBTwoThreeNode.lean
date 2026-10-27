module

public import CFSG.LocalAnalysis.StandardType.GGTableBTwoThreeRank

public section

namespace CFSG.StandardType.TwoThree

open Module

variable {K : Type*} [Field K] [CharP K 2] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem exists_minimal_node (hK : Nat.card K = 2) (X : Subgroup (Module.End K V)ˣ)
    (hcomm : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) (hexp : ∀ x ∈ X, x ^ 3 = 1) (hX : X ≠ ⊥) :
    ∃ g ∈ X, g ≠ 1 ∧
      (∀ x ∈ X, (∀ w, (g : Module.End K V) w = w → (x : Module.End K V) w = w) →
        x ∈ Subgroup.zpowers g) ∧
      Nat.card X ^ 2 * 3 ^ finrank K (LinearMap.range ((g : Module.End K V) - 1)) ≤
        9 * 3 ^ finrank K V ∧
      Even (finrank K (LinearMap.range ((g : Module.End K V) - 1))) ∧
      ∀ g' ∈ X, g' ≠ 1 → finrank K (LinearMap.range ((g : Module.End K V) - 1)) ≤
        finrank K (LinearMap.range ((g' : Module.End K V) - 1)) := by
  classical
  have := finite_units_end (K := K) (V := V)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hval3 : ∀ x ∈ X, (x : Module.End K V) ^ 3 = 1 := fun x hx => by
    rw [← Units.val_pow_eq_pow_val, hexp x hx, Units.val_one]
  have hcommE : ∀ x ∈ X, ∀ y ∈ X, (x : Module.End K V) * y = y * x := fun x hx y hy => by
    rw [← Units.val_mul, ← Units.val_mul, hcomm x hx y hy]
  have hex : ∃ n, ∃ g ∈ X, g ≠ 1 ∧
      finrank K (LinearMap.range ((g : Module.End K V) - 1)) = n := by
    obtain ⟨⟨g, hg⟩, hg1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hX
    exact ⟨_, g, hg, fun h => hg1 (Subtype.ext h), rfl⟩
  obtain ⟨g, hgX, hg1, hgm⟩ := Nat.find_spec hex
  have hmin : ∀ g' ∈ X, g' ≠ 1 →
      Nat.find hex ≤ finrank K (LinearMap.range ((g' : Module.End K V) - 1)) :=
    fun g' hg' hg'1 => Nat.find_min' hex ⟨g', hg', hg'1, rfl⟩
  set m := Nat.find hex with hm
  set g' : Module.End K V := (g : Module.End K V) with hg'
  set U := LinearMap.range (g' - 1) with hUdef
  set W := LinearMap.ker (g' - 1) with hWdef
  have hg3 : g' ^ 3 = 1 := hval3 g hgX
  have hmemW : ∀ w, w ∈ W ↔ g' w = w := fun w => by
    rw [hWdef, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
  have hUW : U ⊓ W = ⊥ := by
    have h := inf_ker_map_eq_bot hg3 ⊤
    rwa [top_inf_eq, Submodule.map_top, inf_comm] at h
  have hrn : finrank K U + finrank K W = finrank K V := LinearMap.finrank_range_add_finrank_ker _
  have hcomm1 : ∀ x ∈ X, (x : Module.End K V) * (g' - 1) = (g' - 1) * x := fun x hx => by
    rw [mul_sub, sub_mul, mul_one, one_mul, hcommE x hx g hgX]
  have hinvU : ∀ x ∈ X, ∀ u ∈ U, (x : Module.End K V) u ∈ U := by
    rintro x hx _ ⟨v, rfl⟩
    exact ⟨(x : Module.End K V) v, by rw [← Module.End.mul_apply, ← Module.End.mul_apply,
      hcomm1 x hx]⟩
  have hinvW : ∀ x ∈ X, ∀ w ∈ W, (x : Module.End K V) w ∈ W := by
    intro x hx w hw
    rw [hWdef, LinearMap.mem_ker] at hw ⊢
    rw [← Module.End.mul_apply, ← hcomm1 x hx, Module.End.mul_apply, hw, map_zero]
  have hfp : ∀ u ∈ U, g' u = u → u = 0 := fun u hu h => by
    have : u ∈ U ⊓ W := ⟨hu, (hmemW u).mpr h⟩
    rwa [hUW, Submodule.mem_bot] at this
  have hUbot : U ≠ ⊥ := by
    intro hU0
    apply hg1
    apply Units.ext
    apply LinearMap.ext
    intro v
    have hv : (g' - 1) v ∈ U := LinearMap.mem_range_self _ v
    rw [hU0, Submodule.mem_bot, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hv
    exact hv
  set Z := X ⊓ fixG W with hZdef
  have hgZ : Subgroup.zpowers g ≤ Z := by
    rw [Subgroup.zpowers_le]
    exact ⟨hgX, fun w hw => (hmemW w).mp hw⟩
  have hcardg : Nat.card (Subgroup.zpowers g) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (hexp g hgX) hg1]
  have hZg : Z = Subgroup.zpowers g := by
    refine le_antisymm (fun y hyZ => ?_) hgZ
    by_contra hyg
    obtain ⟨k, -, u, hu, hu0, hyu⟩ := exists_fixed_of_commute (hcommE g hgX y hyZ.1) hg3
      (hval3 y hyZ.1) (hinvU g hgX) (hinvU y hyZ.1) hfp hUbot
    set z := (g ^ k)⁻¹ * y with hz
    have hzZ : z ∈ Z := Z.mul_mem (Z.inv_mem (Z.pow_mem (hgZ (Subgroup.mem_zpowers g)) k)) hyZ
    have hz1 : z ≠ 1 := by
      intro h
      apply hyg
      have hy : y = g ^ k := by
        rw [hz, inv_mul_eq_one] at h
        exact h.symm
      rw [hy]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers g) k
    have hzu : (z : Module.End K V) u = u := by
      rw [hz, Units.val_mul, Module.End.mul_apply, hyu, ← val_pow_apply, val_inv_apply_apply]
    have hker : W ⊔ Submodule.span K {u} ≤ LinearMap.ker ((z : Module.End K V) - 1) := by
      refine sup_le ?_ ?_
      · intro w hw
        rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, hzZ.2 w hw, sub_self]
      · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker,
          LinearMap.sub_apply, Module.End.one_apply, hzu, sub_self]
    have hWu : W ⊓ Submodule.span K {u} = ⊥ := by
      rw [eq_bot_iff]
      rintro v ⟨hvW, hvu⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hvu
      have h1 : c • u ∈ U ⊓ W := ⟨U.smul_mem c hu, hvW⟩
      rwa [hUW] at h1
    have hdimWu : finrank K (W ⊔ Submodule.span K {u} : Submodule K V) = finrank K W + 1 := by
      have h1 := Submodule.finrank_sup_add_finrank_inf_eq W (Submodule.span K {u})
      rwa [hWu, finrank_bot, add_zero, finrank_span_singleton hu0] at h1
    have hrnz := LinearMap.finrank_range_add_finrank_ker ((z : Module.End K V) - 1)
    have hkle := Submodule.finrank_mono hker
    have h1 := hmin z hzZ.1 hz1
    omega
  have hW := card_sq_le hK _ W rfl X hcomm hexp hinvW
  rw [← hZdef, hZg, hcardg] at hW
  refine ⟨g, hgX, hg1, fun x hx hxw => ?_, ?_, hgm ▸ even_finrank_of_fpf hK hg3 (hinvU g hgX) hfp,
    fun g'' hg'' hg''1 => hgm ▸ hmin g'' hg'' hg''1⟩
  · have hxZ : x ∈ Z := ⟨hx, fun w hw => hxw w ((hmemW w).mp hw)⟩
    rwa [hZg] at hxZ
  · calc Nat.card X ^ 2 * 3 ^ finrank K U ≤ 3 ^ finrank K W * 3 ^ 2 * 3 ^ finrank K U :=
          Nat.mul_le_mul_right _ hW
      _ = 9 * 3 ^ finrank K V := by rw [← hrn]; ring

end CFSG.StandardType.TwoThree
