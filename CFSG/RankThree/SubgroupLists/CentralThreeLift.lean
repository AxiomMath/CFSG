module

public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.RankThree.SubgroupLists

open scoped commutatorElement

variable {G : Type*} [Group G] {Z : Subgroup G}

theorem eq_one_of_pow_three_of_pow {z : G} (hz3 : z ^ 3 = 1) {n : ℕ} (hn : Nat.Coprime n 3)
    (hzn : z ^ n = 1) : z = 1 := by
  have h := Nat.Coprime.gcd_eq_one hn
  have hd : orderOf z ∣ Nat.gcd n 3 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hzn)
    (orderOf_dvd_of_pow_eq_one hz3)
  rw [h, Nat.dvd_one, orderOf_eq_one_iff] at hd
  exact hd

variable [Z.Normal]

theorem exists_lift_pow_eq_one (hZc : Z ≤ Subgroup.center G) (hZ3 : ∀ z ∈ Z, z ^ 3 = 1)
    {n : ℕ} (hn : Nat.Coprime n 3) (s : G ⧸ Z) (hs : s ^ n = 1) :
    ∃ x : G, (x : G ⧸ Z) = s ∧ x ^ n = 1 := by
  obtain ⟨x₀, rfl⟩ := QuotientGroup.mk_surjective s
  have hz' : x₀ ^ n ∈ Z := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hs]
  obtain ⟨z, hz, hzx⟩ : ∃ z ∈ Z, x₀ ^ n = z := ⟨_, hz', rfl⟩
  have hz3 := hZ3 z hz
  have hn3 : ¬ 3 ∣ n := fun h => by
    have := Nat.Coprime.coprime_dvd_right h hn.symm
    norm_num at this
  obtain ⟨a, ha⟩ : ∃ a : ℕ, a * n % 3 = 1 := by
    rcases (show n % 3 = 1 ∨ n % 3 = 2 by omega) with h | h
    · exact ⟨1, by omega⟩
    · exact ⟨2, by omega⟩
  have hza : z ^ (a * n) = z := by
    rw [← Nat.div_add_mod (a * n) 3, ha, pow_add, pow_mul, hz3, one_pow, one_mul, pow_one]
  have hcomm : Commute x₀ ((z⁻¹) ^ a) := by
    have : Commute x₀ z := Subgroup.mem_center_iff.mp (hZc hz) x₀
    exact (this.inv_right).pow_right a
  refine ⟨x₀ * (z⁻¹) ^ a, ?_, ?_⟩
  · rw [QuotientGroup.mk_mul, QuotientGroup.mk_pow, QuotientGroup.mk_inv,
      (QuotientGroup.eq_one_iff z).mpr hz, inv_one, one_pow, mul_one]
  · rw [hcomm.mul_pow, hzx, ← pow_mul, inv_pow, hza, mul_inv_cancel]

theorem isConj_of_isConj_mk (hZc : Z ≤ Subgroup.center G) (hZ3 : ∀ z ∈ Z, z ^ 3 = 1)
    {n : ℕ} (hn : Nat.Coprime n 3) {x y : G} (hx : x ^ n = 1) (hy : y ^ n = 1)
    (h : IsConj (x : G ⧸ Z) (y : G ⧸ Z)) : IsConj x y := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
  have hz : y⁻¹ * (g * x * g⁻¹) ∈ Z := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hc, inv_mul_cancel]
  set z := y⁻¹ * (g * x * g⁻¹) with hzdef
  have hgx : g * x * g⁻¹ = y * z := by rw [hzdef, mul_inv_cancel_left]
  have hzc : Commute y z := Subgroup.mem_center_iff.mp (hZc hz) y
  have hzn : z ^ n = 1 := by
    have h1 : (g * x * g⁻¹) ^ n = 1 := by rw [conj_pow, hx, mul_one, mul_inv_cancel]
    rw [hgx, hzc.mul_pow, hy, one_mul] at h1
    exact h1
  have hz1 := eq_one_of_pow_three_of_pow (hZ3 z hz) hn hzn
  refine isConj_iff.mpr ⟨g, ?_⟩
  rw [hgx, hz1, mul_one]

theorem commute_of_commute_mk (hZc : Z ≤ Subgroup.center G) (hZ3 : ∀ z ∈ Z, z ^ 3 = 1)
    {n : ℕ} (hn : Nat.Coprime n 3) {x y : G} (hx : x ^ n = 1)
    (h : (x : G ⧸ Z) * (y : G ⧸ Z) = (y : G ⧸ Z) * (x : G ⧸ Z)) : x * y = y * x := by
  have hz : x⁻¹ * (y * x * y⁻¹) ∈ Z := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, ← h, mul_assoc,
      mul_inv_cancel, mul_one, inv_mul_cancel]
  set z := x⁻¹ * (y * x * y⁻¹) with hzdef
  have hyx : y * x * y⁻¹ = x * z := by rw [hzdef, mul_inv_cancel_left]
  have hzc : Commute x z := Subgroup.mem_center_iff.mp (hZc hz) x
  have hzn : z ^ n = 1 := by
    have h1 : (y * x * y⁻¹) ^ n = 1 := by rw [conj_pow, hx, mul_one, mul_inv_cancel]
    rw [hyx, hzc.mul_pow, hx, one_mul] at h1
    exact h1
  have hz1 := eq_one_of_pow_three_of_pow (hZ3 z hz) hn hzn
  rw [hz1, mul_one] at hyx
  calc x * y = y * x * y⁻¹ * y := by rw [hyx]
    _ = y * x := by group

theorem map_commutator_comap (L : Subgroup (G ⧸ Z)) [Group.IsPerfect L] :
    (⁅L.comap (QuotientGroup.mk' Z), L.comap (QuotientGroup.mk' Z)⁆).map (QuotientGroup.mk' Z) =
      L := by
  rw [Subgroup.map_commutator, Subgroup.map_comap_eq_self_of_surjective
    (QuotientGroup.mk'_surjective Z), Subgroup.commutator_eq_self]

theorem isPerfect_commutator_comap (hZc : Z ≤ Subgroup.center G) (L : Subgroup (G ⧸ Z))
    [Group.IsPerfect L] :
    Group.IsPerfect (⁅L.comap (QuotientGroup.mk' Z), L.comap (QuotientGroup.mk' Z)⁆ :
      Subgroup G) := by
  set M := L.comap (QuotientGroup.mk' Z) with hM
  set D := ⁅M, M⁆ with hD
  rw [Subgroup.isPerfect_iff]
  refine le_antisymm (Subgroup.commutator_le_self _) ?_
  have hDD : (⁅D, D⁆).map (QuotientGroup.mk' Z) = L := by
    rw [Subgroup.map_commutator, map_commutator_comap, Subgroup.commutator_eq_self]
  have hsplit : ∀ m ∈ M, ∃ d ∈ ⁅D, D⁆, ∃ z ∈ Z, m = d * z := by
    intro m hm
    have hmL : (QuotientGroup.mk' Z m) ∈ L := hm
    rw [← hDD] at hmL
    obtain ⟨d, hd, hdm⟩ := hmL
    refine ⟨d, hd, d⁻¹ * m, ?_, by group⟩
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    change (QuotientGroup.mk' Z d)⁻¹ * QuotientGroup.mk' Z m = 1
    rw [hdm, inv_mul_cancel]
  rw [hD, Subgroup.commutator_le]
  intro m₁ hm₁ m₂ hm₂
  obtain ⟨d₁, hd₁, z₁, hz₁, rfl⟩ := hsplit m₁ hm₁
  obtain ⟨d₂, hd₂, z₂, hz₂, rfl⟩ := hsplit m₂ hm₂
  have hc₁ : z₁ * d₂ = d₂ * z₁ := (Subgroup.mem_center_iff.mp (hZc hz₁) d₂).symm
  have hc₂ : z₂ * d₁ = d₁ * z₂ := (Subgroup.mem_center_iff.mp (hZc hz₂) d₁).symm
  have hc₁₂ : z₁ * z₂ = z₂ * z₁ := (Subgroup.mem_center_iff.mp (hZc hz₁) z₂).symm
  have heq : ⁅d₁ * z₁, d₂ * z₂⁆ = ⁅d₁, d₂⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    calc d₁ * z₁ * (d₂ * z₂) * (d₁ * z₁)⁻¹ * (d₂ * z₂)⁻¹
        = d₁ * (z₁ * d₂) * z₂ * z₁⁻¹ * d₁⁻¹ * z₂⁻¹ * d₂⁻¹ := by group
      _ = d₁ * (d₂ * z₁) * z₂ * z₁⁻¹ * d₁⁻¹ * z₂⁻¹ * d₂⁻¹ := by rw [hc₁]
      _ = d₁ * d₂ * (z₁ * z₂) * z₁⁻¹ * d₁⁻¹ * z₂⁻¹ * d₂⁻¹ := by group
      _ = d₁ * d₂ * (z₂ * z₁) * z₁⁻¹ * d₁⁻¹ * z₂⁻¹ * d₂⁻¹ := by rw [hc₁₂]
      _ = d₁ * d₂ * (z₂ * d₁⁻¹) * z₂⁻¹ * d₂⁻¹ := by group
      _ = d₁ * d₂ * (d₁⁻¹ * z₂) * z₂⁻¹ * d₂⁻¹ := by
          rw [show z₂ * d₁⁻¹ = d₁⁻¹ * z₂ by
            calc z₂ * d₁⁻¹ = d₁⁻¹ * (d₁ * z₂) * d₁⁻¹ := by group
              _ = d₁⁻¹ * (z₂ * d₁) * d₁⁻¹ := by rw [hc₂]
              _ = d₁⁻¹ * z₂ := by group]
      _ = d₁ * d₂ * d₁⁻¹ * d₂⁻¹ := by group
  rw [heq]
  exact Subgroup.commutator_mem_commutator (Subgroup.commutator_le_self _ hd₁)
    (Subgroup.commutator_le_self _ hd₂)

end CFSG.RankThree.SubgroupLists
