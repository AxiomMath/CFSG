module

public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup

variable {G Q : Type} [Group G] [Group Q]

private lemma spUCited_eq_one_of_two_pow [Finite G] (π : G →* Q)
    (hodd : ¬ 2 ∣ Nat.card π.ker) {x : G} (hx : x ∈ π.ker) {n : ℕ}
    (hpow : x ^ 2 ^ n = 1) : x = 1 := by
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hpow)
  have hdvdk : orderOf x ∣ Nat.card π.ker := Subgroup.orderOf_dvd_natCard π.ker hx
  have hi0 : i = 0 := by
    by_contra hne
    have h2 : 2 ∣ orderOf x := by
      rw [hi]
      exact dvd_pow_self 2 hne
    exact hodd (h2.trans hdvdk)
  exact orderOf_eq_one_iff.mp (by rw [hi, hi0, pow_zero])

private lemma spUCited_inf_ker_eq_bot [Finite G] (π : G →* Q) (hodd : ¬ 2 ∣ Nat.card π.ker)
    {X : Subgroup G} (hX : IsPGroup 2 X) : X ⊓ π.ker = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxX, hxK⟩ := hx
  obtain ⟨n, hn⟩ := hX ⟨x, hxX⟩
  exact spUCited_eq_one_of_two_pow π hodd hxK (by simpa using congrArg Subtype.val hn)

theorem spUCited_map_inf_of_ker_le (π : G →* Q) {A B : Subgroup G} (hB : π.ker ≤ B) :
    (A ⊓ B).map π = A.map π ⊓ B.map π := by
  refine le_antisymm (Subgroup.map_inf_le A B π) ?_
  intro z hz
  rw [Subgroup.mem_inf] at hz
  obtain ⟨hzA, hzB⟩ := hz
  obtain ⟨x, hxA, rfl⟩ := Subgroup.mem_map.mp hzA
  obtain ⟨y, hyB, hy⟩ := Subgroup.mem_map.mp hzB
  have hker : x⁻¹ * y ∈ π.ker := by
    show π (x⁻¹ * y) = 1
    rw [map_mul, map_inv, hy, inv_mul_cancel]
  have hxB : x ∈ B := by
    have hmem : (x⁻¹ * y)⁻¹ ∈ B := B.inv_mem (hB hker)
    have hx : x = y * (x⁻¹ * y)⁻¹ := by group
    rw [hx]
    exact B.mul_mem hyB hmem
  exact Subgroup.mem_map_of_mem π (show x ∈ A ⊓ B from ⟨hxA, hxB⟩)

theorem spUCited_card_map_of_isPGroup [Finite G] (π : G →* Q) (hodd : ¬ 2 ∣ Nat.card π.ker)
    {X : Subgroup G} (hX : IsPGroup 2 X) : Nat.card (X.map π) = Nat.card X := by
  have hbot : X ⊓ π.ker = ⊥ := spUCited_inf_ker_eq_bot π hodd hX
  let f : X → X.map π := fun x => ⟨π x, Subgroup.mem_map_of_mem π x.2⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have hval : π (x : G) = π (y : G) := congrArg Subtype.val hxy
    have hmem : (x : G)⁻¹ * (y : G) ∈ X ⊓ π.ker := by
      refine ⟨X.mul_mem (X.inv_mem x.2) y.2, ?_⟩
      show π ((x : G)⁻¹ * (y : G)) = 1
      rw [map_mul, map_inv, hval, inv_mul_cancel]
    rw [hbot] at hmem
    have h1 : (x : G)⁻¹ * (y : G) = 1 := Subgroup.mem_bot.mp hmem
    calc (x : G) = (x : G) * ((x : G)⁻¹ * (y : G)) := by rw [h1, mul_one]
      _ = (y : G) := by rw [mul_inv_cancel_left]
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)).symm

theorem spUCited_normalizer_map_of_ker [Finite G] (π : G →* Q) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center G) (hodd : ¬ 2 ∣ Nat.card π.ker) {X : Subgroup G}
    (hX : IsPGroup 2 X) :
    (Subgroup.normalizer (X : Set G)).map π =
      Subgroup.normalizer ((X.map π : Subgroup Q) : Set Q) := by
  apply le_antisymm (Subgroup.le_normalizer_map π)
  intro y hy
  obtain ⟨g, rfl⟩ := hπ y
  have hkey : ∀ g : G, π g ∈ Subgroup.normalizer ((X.map π : Subgroup Q) : Set Q) →
      ∀ x : G, x ∈ X → g * x * g⁻¹ ∈ X := by
    intro g hg x hx
    have hmem : π (g * x * g⁻¹) ∈ X.map π := by
      have hgx : π g * π x * (π g)⁻¹ ∈ X.map π :=
        (Subgroup.mem_normalizer_iff.mp hg (π x)).mp (Subgroup.mem_map_of_mem π hx)
      simpa only [map_mul, map_inv] using hgx
    have hsup : g * x * g⁻¹ ∈ X ⊔ π.ker := by
      rw [← Subgroup.comap_map_eq π X]
      exact hmem
    obtain ⟨x', hx', k, hk, hxk⟩ := Subgroup.mem_sup_of_normal_right.mp hsup
    obtain ⟨a, ha⟩ := hX ⟨x, hx⟩
    obtain ⟨b, hb⟩ := hX ⟨x', hx'⟩
    have hxa : x ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
    have hx'b : x' ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
    have hxN : x ^ 2 ^ max a b = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp
        ((orderOf_dvd_of_pow_eq_one hxa).trans (pow_dvd_pow 2 (le_max_left a b)))
    have hx'N : x' ^ 2 ^ max a b = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp
        ((orderOf_dvd_of_pow_eq_one hx'b).trans (pow_dvd_pow 2 (le_max_right a b)))
    have hcomm : Commute x' k := Subgroup.mem_center_iff.mp (hker hk) x'
    have hkN : k ^ 2 ^ max a b = 1 := by
      have h1 : (g * x * g⁻¹) ^ 2 ^ max a b = 1 := by
        rw [conj_pow, hxN, mul_one, mul_inv_cancel]
      rw [← hxk, hcomm.mul_pow, hx'N, one_mul] at h1
      exact h1
    have hk1 : k = 1 := spUCited_eq_one_of_two_pow π hodd hk hkN
    rw [← hxk, hk1, mul_one]
    exact hx'
  have hgN : g ∈ Subgroup.normalizer (X : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hkey g hy x hx
    · intro hx
      have hginv : π g⁻¹ ∈ Subgroup.normalizer ((X.map π : Subgroup Q) : Set Q) := by
        simpa only [map_inv] using Subgroup.inv_mem _ hy
      have hres := hkey g⁻¹ hginv (g * x * g⁻¹) hx
      have heq : g⁻¹ * (g * x * g⁻¹) * (g⁻¹)⁻¹ = x := by group
      rwa [heq] at hres
  exact Subgroup.mem_map_of_mem π hgN

theorem spUCited_comap_normalizer_map [Finite G] (π : G →* Q) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center G) (hodd : ¬ 2 ∣ Nat.card π.ker) {X : Subgroup G}
    (hX : IsPGroup 2 X) :
    (Subgroup.normalizer ((X.map π : Subgroup Q) : Set Q)).comap π =
      Subgroup.normalizer (X : Set G) := by
  rw [← spUCited_normalizer_map_of_ker π hπ hker hodd hX, Subgroup.comap_map_eq,
    sup_eq_left.mpr (hker.trans (Subgroup.center_le_normalizer (X : Set G)))]

end CFSG.LocalAnalysis.WeakClosure81

end
