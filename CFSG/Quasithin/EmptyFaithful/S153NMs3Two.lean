module

import CFSG.Quasithin.Background.FFC4Case2
public import CFSG.Quasithin.Background.FFC4Res

public section

namespace CFSG.Quasithin.S153N

open CFSG.Open hiding StatedSL StatedSp
open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

variable {W : Type} [CommGroup W]

private def punctPerm (U : Type*) [Group U] : MulAut U →* Equiv.Perm {v : U // v ≠ 1} where
  toFun a := Equiv.Perm.subtypePerm a.toEquiv (by intro v; simp)
  map_one' := by ext v; rfl
  map_mul' := by intro a b; ext v; rfl

private theorem punctPerm_injective (U : Type*) [Group U] : Function.Injective (punctPerm U) := by
  intro a b hab
  ext v
  by_cases hv : v = 1
  · simp [hv]
  · exact congrArg Subtype.val (DFunLike.congr_fun hab ⟨v, hv⟩)

theorem card_eq_six_of_case2 {J : Subgroup (MulAut W)} (hc2 : B56Case2 J) : Nat.card ↥J = 6 := by
  obtain ⟨⟨e⟩, -, -⟩ := hc2
  rw [Nat.card_congr e.toEquiv, FFC.card_perm_three]

theorem ne_bot_of_case2 {J : Subgroup (MulAut W)} (hc2 : B56Case2 J) : J ≠ ⊥ := by
  intro h
  have h6 := card_eq_six_of_case2 hc2
  rw [h, Subgroup.card_bot] at h6
  omega

theorem exists_apply_eq_of_case2 [Finite W] {J : Subgroup (MulAut W)} (hc2 : B56Case2 J)
    {u y : W} (hu : u ∈ commV J) (hy : y ∈ commV J) (hu1 : u ≠ 1) (hy1 : y ≠ 1) :
    ∃ g ∈ J, g u = y := by
  classical
  have hJ6 := card_eq_six_of_case2 hc2
  obtain ⟨-, ⟨hsup, -⟩, hc4⟩ := hc2
  have hU4 : Nat.card ↥(commV J) = 4 := by simpa using hc4
  have hUinv : ∀ g ∈ J, ∀ x ∈ commV J, g x ∈ commV J := FFC.commV_invariant_self J
  have hfaith : ∀ g ∈ J, (∀ x ∈ commV J, g x = x) → g = 1 := by
    intro g hg hx
    ext v
    have hv : v ∈ commV J ⊔ fixV J := by rw [hsup]; trivial
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.1 hv
    rw [map_mul, hx y hy, hz g hg]
    rfl
  have hstab : J ≤ stabSub (commV J) := FFC.le_stabSub_of_invariant hUinv
  have : Fintype ↥(commV J) := Fintype.ofFinite _
  have hX3 : Fintype.card {v : ↥(commV J) // v ≠ 1} = 3 := by
    rw [Fintype.card_subtype_compl]
    have hone : Fintype.card {v : ↥(commV J) // v = 1} = 1 := by simp
    rw [hone, ← Nat.card_eq_fintype_card, hU4]
  have hperm6 : Nat.card (Equiv.Perm {v : ↥(commV J) // v ≠ 1}) = 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, hX3]
    decide
  let f : ↥J →* Equiv.Perm {v : ↥(commV J) // v ≠ 1} :=
    (punctPerm ↥(commV J)).comp (FFC.resG hstab)
  have hfinj : Function.Injective f :=
    (punctPerm_injective _).comp (FFC.resG_injective hstab hfaith)
  have hfbij : Function.Bijective f := hfinj.bijective_of_nat_card_le (by rw [hJ6, hperm6])
  let x : {v : ↥(commV J) // v ≠ 1} := ⟨⟨u, hu⟩, fun h => hu1 (congrArg Subtype.val h)⟩
  let y' : {v : ↥(commV J) // v ≠ 1} := ⟨⟨y, hy⟩, fun h => hy1 (congrArg Subtype.val h)⟩
  obtain ⟨g, hg⟩ := hfbij.2 (Equiv.swap x y')
  refine ⟨(g : MulAut W), g.2, ?_⟩
  have hx : (f g) x = y' := by rw [hg, Equiv.swap_apply_left]
  exact congrArg (fun p : {v : ↥(commV J) // v ≠ 1} => ((p : ↥(commV J)) : W)) hx

theorem ncard_image_of_case2 [Finite W] {J : Subgroup (MulAut W)} (hc2 : B56Case2 J) {w : W}
    (hw : w ∉ fixV J) :
    ((fun g : MulAut W => g w) '' (J : Set (MulAut W))).ncard = 3 := by
  have hU4 : Nat.card ↥(commV J) = 4 := by simpa using hc2.2.2
  have hsup : commV J ⊔ fixV J = ⊤ := hc2.2.1.1
  have hUinv : ∀ g ∈ J, ∀ x ∈ commV J, g x ∈ commV J := FFC.commV_invariant_self J
  have hwmem : w ∈ commV J ⊔ fixV J := by rw [hsup]; trivial
  obtain ⟨u, hu, z, hz, rfl⟩ := Subgroup.mem_sup.1 hwmem
  have hu1 : u ≠ 1 := by
    rintro rfl
    exact hw (by simpa using hz)
  have hset : (fun g : MulAut W => g (u * z)) '' (J : Set (MulAut W)) =
      (fun x : W => x * z) '' (((commV J : Subgroup W) : Set W) \ {1}) := by
    ext x
    constructor
    · rintro ⟨g, hgJ, rfl⟩
      refine ⟨g u, ⟨hUinv g hgJ u hu, ?_⟩, ?_⟩
      · intro h
        apply hu1
        have h' : g u = g 1 := by rw [map_one]; exact h
        exact g.injective h'
      · show g u * z = g (u * z)
        rw [map_mul, hz g hgJ]
    · rintro ⟨y, ⟨hy, hy1⟩, rfl⟩
      obtain ⟨g, hgJ, hgu⟩ := exists_apply_eq_of_case2 hc2 hu hy hu1 hy1
      refine ⟨g, hgJ, ?_⟩
      show g (u * z) = y * z
      rw [map_mul, hgu, hz g hgJ]
  rw [hset, Set.ncard_image_of_injective _ (mul_left_injective z),
    Set.ncard_sdiff_singleton_of_mem (one_mem _)]
  have h4 : ((commV J : Subgroup W) : Set W).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact hU4
  omega

theorem not_isStrongFFModule_of_case2 [Finite W] {J : Subgroup (MulAut W)} (hc2 : B56Case2 J) :
    ¬ IsStrongFFModule J := by
  rintro ⟨A, hAJ, hA1, hA2, hlt⟩
  have hJ6 := card_eq_six_of_case2 hc2
  have hAdvd : Nat.card ↥A ∣ 6 := hJ6 ▸ Subgroup.card_dvd_of_le hAJ
  obtain ⟨k, hk⟩ := hA2.isPGroup.exists_card_eq
  have hk1 : k ≤ 1 := by
    by_contra h
    have h2 : 2 ^ 2 ∣ 2 ^ k := Nat.pow_dvd_pow 2 (by omega)
    rw [hk] at hAdvd
    have h3 := h2.trans hAdvd
    omega
  have hAcard : Nat.card ↥A ≤ 2 := by
    rw [hk]
    calc 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
      _ = 2 := by norm_num
  obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA1
  have hne : fixV A ≠ ⊤ := by
    intro htop
    have h1 : (a : MulAut W) = 1 := by
      ext v
      have hv : v ∈ fixV A := htop ▸ Subgroup.mem_top v
      exact mem_fixV.1 hv a a.2
    exact ha1 (Subtype.ext h1)
  have hidx1 : (fixV A).index ≠ 1 := fun h => hne (Subgroup.index_eq_one.1 h)
  have hidx0 : (fixV A).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hidx : 2 ≤ (fixV A).index := by omega
  have h2 : 2 * Nat.card ↥(fixV A) ≤ Nat.card W := by
    rw [B1.card_eq_index_mul A]
    exact Nat.mul_le_mul_right _ hidx
  have h3 : Nat.card ↥A * Nat.card ↥(fixV A) ≤ 2 * Nat.card ↥(fixV A) :=
    Nat.mul_le_mul_right _ hAcard
  omega

end CFSG.Quasithin.S153N
