module

public import CFSG.RankThree.PartTwo.Sec21.FF84LemmaHCert
public import Mathlib.GroupTheory.FixedPointFree

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.LemmaH

open Equiv

variable {K S : Type} [Group K] [Group S]

theorem burnside_triple [Finite S] {φ : MulAut S} (hφ3 : φ ^ 3 = 1)
    (hfix : ∀ v, φ v = v → v = 1) (g : S) : g * φ g * φ (φ g) = 1 := by
  have h3 : ∀ y, φ (φ (φ y)) = y := fun y => by
    have := congrArg (fun f : MulAut S => f y) hφ3
    simpa [pow_succ, MulAut.mul_apply] using this
  have hit : (⇑φ)^[3] = _root_.id := by
    funext y
    simp [h3]
  have := MonoidHom.FixedPointFree.prod_pow_eq_one (φ := φ) hfix hit g
  simpa [List.range_succ, mul_assoc] using this

@[expose] def Fpf (ρ : K →* MulAut S) : Prop :=
  ∀ y : K, y ^ 3 = 1 → y ≠ 1 → ∀ u : S, ρ y u = u → u = 1

structure InvAb (ρ : K →* MulAut S) (A : Subgroup S) : Prop where
  comm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a
  inv : ∀ k : K, ∀ a ∈ A, ρ k a ∈ A

abbrev commGroupOf {A : Subgroup S} (hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) : CommGroup ↥A :=
  { (inferInstance : Group ↥A) with mul_comm := fun a b => Subtype.ext (hc a a.2 b b.2) }

theorem triple_eq_one [Finite S] {ρ : K →* MulAut S} (hρ : Fpf ρ) (y c : K) (hy3 : y ^ 3 = 1)
    (hy1 : y ≠ 1) (a : S) :
    ρ c a * ρ (y * c) a * ρ (y * y * c) a = 1 := by
  have h3 : ρ y ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
  have := burnside_triple h3 (hρ y hy3 hy1) (ρ c a)
  simpa [mul_assoc] using this

theorem pow_six_eq_one [Finite S] (e : K ≃* A5) {ρ : K →* MulAut S} (hρ : Fpf ρ)
    {A : Subgroup S} (hA : InvAb ρ A) : ∀ a ∈ A, a ^ 6 = 1 := by
  intro a ha
  letI : CommGroup ↥A := commGroupOf hA.comm
  let w : A5 → ↥A := fun g => ⟨ρ (e.symm g) a, hA.inv _ a ha⟩
  have hw : ∀ t ∈ cert6, w t.2.2 * w (t.2.1 * t.2.2) * w (t.2.1 * t.2.1 * t.2.2) = 1 := by
    intro t ht
    obtain ⟨h3, h1⟩ := cert6_order t ht
    apply Subtype.ext
    have := triple_eq_one hρ (e.symm t.2.1) (e.symm t.2.2) (by rw [← map_pow, h3, map_one])
      (fun h => h1 (e.symm.injective (by rw [h, map_one]))) a
    simpa [w] using this
  have key := prod_cert w cert6 hw
  simp_rw [cert6_cnt] at key
  rw [Finset.prod_eq_single (1 : A5)] at key
  · have h1 : w 1 = ⟨a, ha⟩ := by
      apply Subtype.ext
      simp [w]
    rw [h1] at key
    have := congrArg Subtype.val key
    simpa using this
  · intro g _ hg
    simp [hg]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem fixed_five_eq_one [Finite S] (e : K ≃* A5) {ρ : K →* MulAut S} (hρ : Fpf ρ)
    {A : Subgroup S} (hA : InvAb ρ A) (hA2 : ∀ a ∈ A, a * a = 1) :
    ∀ u ∈ A, ρ (e.symm z5) u = u → u = 1 := by
  intro u hu hfix
  letI : CommGroup ↥A := commGroupOf hA.comm
  let w : A5 → ↥A := fun g => ⟨ρ (e.symm g) u, hA.inv _ u hu⟩
  have hw : ∀ t ∈ cert5, w t.2.2 * w (t.2.1 * t.2.2) * w (t.2.1 * t.2.1 * t.2.2) = 1 := by
    intro t ht
    obtain ⟨h3, h1⟩ := cert5_order t ht
    apply Subtype.ext
    have := triple_eq_one hρ (e.symm t.2.1) (e.symm t.2.2) (by rw [← map_pow, h3, map_one])
      (fun h => h1 (e.symm.injective (by rw [h, map_one]))) u
    simpa [w] using this
  have key := prod_cert w cert5 hw
  have hsq : ∀ g : A5, w g ^ (2 : ℤ) = 1 := by
    intro g
    apply Subtype.ext
    simpa [pow_two] using hA2 _ (hA.inv _ u hu)
  have hmod : ∀ g : A5, w g ^ cnt cert5 g =
      w g ^ (if g = 1 ∨ g = z5 ∨ g = z5 ^ 2 ∨ g = z5 ^ 3 ∨ g = z5 ^ 4 then (1 : ℤ) else 0) := by
    intro g
    have h1 := Int.emod_add_mul_ediv (cnt cert5 g) 2
    rw [cert5_cnt g] at h1
    rw [← h1, zpow_add, zpow_mul, hsq, one_zpow, mul_one]
  simp_rw [hmod] at key
  have hpow : ∀ g : A5, w g ^ (if g = 1 ∨ g = z5 ∨ g = z5 ^ 2 ∨ g = z5 ^ 3 ∨ g = z5 ^ 4
      then (1 : ℤ) else 0) = if g = 1 ∨ g = z5 ∨ g = z5 ^ 2 ∨ g = z5 ^ 3 ∨ g = z5 ^ 4
        then w g else 1 := by
    intro g
    split_ifs <;> simp
  simp_rw [hpow] at key
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one] at key
  have hfil : Finset.univ.filter (fun g : A5 => g = 1 ∨ g = z5 ∨ g = z5 ^ 2 ∨ g = z5 ^ 3 ∨
      g = z5 ^ 4) = {1, z5, z5 ^ 2, z5 ^ 3, z5 ^ 4} := by
    ext g
    simp
  rw [hfil] at key
  have hn1 : (1 : A5) ∉ ({z5, z5 ^ 2, z5 ^ 3, z5 ^ 4} : Finset A5) := by decide
  have hn2 : z5 ∉ ({z5 ^ 2, z5 ^ 3, z5 ^ 4} : Finset A5) := by decide
  have hn3 : z5 ^ 2 ∉ ({z5 ^ 3, z5 ^ 4} : Finset A5) := by decide
  have hn4 : z5 ^ 3 ∉ ({z5 ^ 4} : Finset A5) := by decide
  rw [Finset.prod_insert hn1, Finset.prod_insert hn2, Finset.prod_insert hn3,
    Finset.prod_insert hn4, Finset.prod_singleton] at key
  have key' := congrArg Subtype.val key
  have hz : ∀ n : ℕ, ρ (e.symm z5 ^ n) u = u := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, map_mul, MulAut.mul_apply, hfix, ih]
  have hzp : ∀ n : ℕ, ρ (e.symm (z5 ^ n)) u = u := fun n => by rw [map_pow]; exact hz n
  simp only [Subgroup.coe_mul, w, hzp, hfix, map_one, MulAut.one_apply] at key'
  have h5 : u * u * u * u * u = 1 := by simpa [mul_assoc] using key'
  have hu2 := hA2 u hu
  calc u = u * u * u * u * u := by
        rw [hu2, one_mul, hu2, one_mul]
    _ = 1 := h5
