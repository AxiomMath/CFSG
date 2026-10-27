module

public import CFSG.LocalAnalysis.SectionRank.Sporadic.ON
public import CFSG.RankThree.PartTwo.Sec4.Vocabulary

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148V

theorem pow_three_mul_of_central {G : Type*} [Group G] {u v k : G}
    (hk : ∀ g : G, g * k = k * g) (huv : v * u = k * (u * v)) :
    (u * v) ^ 3 = k ^ 3 * (u ^ 3 * v ^ 3) := by
  have hkl1 : ∀ g x : G, g * (k * x) = k * (g * x) := fun g x => by
    rw [← mul_assoc g k x, hk g, mul_assoc k g x]
  have hkl : ∀ g x : G, g * (k ^ 2 * x) = k ^ 2 * (g * x) := fun g x => by
    rw [← mul_assoc g (k ^ 2) x, ((show Commute g k from hk g).pow_right 2).eq,
      mul_assoc (k ^ 2) g x]
  have h1 : v * u * v = k * (u * v ^ 2) := by
    rw [huv]
    simp only [pow_two, mul_assoc]
  have h2 : v ^ 2 * u = k ^ 2 * (u * v ^ 2) := by
    calc v ^ 2 * u = v * (v * u) := by simp only [pow_two, mul_assoc]
      _ = v * (k * (u * v)) := by rw [huv]
      _ = k * (v * (u * v)) := hkl1 v (u * v)
      _ = k * (v * u * v) := by simp only [mul_assoc]
      _ = k * (k * (u * v ^ 2)) := by rw [h1]
      _ = k ^ 2 * (u * v ^ 2) := by simp only [pow_two, mul_assoc]
  calc (u * v) ^ 3 = u * (v * u * v) * u * v := by simp only [pow_three, mul_assoc]
    _ = u * (k * (u * v ^ 2)) * u * v := by rw [h1]
    _ = k * (u * (u * v ^ 2)) * u * v := by rw [hkl1 u (u * v ^ 2)]
    _ = k * (u * (u * v ^ 2) * u * v) := by simp only [mul_assoc]
    _ = k * (u * u * (v ^ 2 * u) * v) := by simp only [mul_assoc]
    _ = k * (u * u * (k ^ 2 * (u * v ^ 2)) * v) := by rw [h2]
    _ = k * (k ^ 2 * (u * u * (u * v ^ 2) * v)) := by
      rw [hkl (u * u) (u * v ^ 2)]
      simp only [mul_assoc]
    _ = k ^ 3 * (u ^ 3 * v ^ 3) := by simp only [pow_two, pow_three, mul_assoc]

theorem mul_pow_two_eq_of_mul_eq {G : Type*} [Group G] {x y : G} (h : x * y = y * x) :
    x * y ^ 2 = y ^ 2 * x :=
  ((show Commute x y from h).pow_right 2).eq

theorem pow_three_mul_of_commutator_mem_center {G : Type*} [Group G] {u v : G}
    (hc : u * v * u⁻¹ * v⁻¹ ∈ Subgroup.center G) (h3 : (u * v * u⁻¹ * v⁻¹) ^ 3 = 1) :
    (u * v) ^ 3 = u ^ 3 * v ^ 3 := by
  have hk : ∀ g : G, g * (u * v * u⁻¹ * v⁻¹)⁻¹ = (u * v * u⁻¹ * v⁻¹)⁻¹ * g :=
    Subgroup.mem_center_iff.mp (inv_mem hc)
  have huv : v * u = (u * v * u⁻¹ * v⁻¹)⁻¹ * (u * v) := by group
  rw [pow_three_mul_of_central hk huv, inv_pow, h3, inv_one, one_mul]

theorem pow_three_eq_one_of_mem_of_card_eq_three {W : Type*} [Group W] {Z : Subgroup W}
    (hZ : Nat.card Z = 3) {z : W} (hz : z ∈ Z) : z ^ 3 = 1 := by
  have h := orderOf_dvd_natCard (⟨z, hz⟩ : Z)
  rw [hZ] at h
  have h3 : (⟨z, hz⟩ : Z) ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.mp h
  simpa using congrArg Subtype.val h3

theorem mem_zpowers_of_card_eq_three {W : Type*} [Group W] {Z : Subgroup W}
    (hZ : Nat.card Z = 3) {z : W} (hz : z ∈ Z) (hz1 : z ≠ 1) {w : W} (hw : w ∈ Z) :
    w ∈ Subgroup.zpowers z := by
  have hfin : Finite Z := Nat.finite_of_card_ne_zero (by rw [hZ]; norm_num)
  have h3 : z ^ 3 = 1 := pow_three_eq_one_of_mem_of_card_eq_three hZ hz
  have hord : orderOf z = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one h3) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hz1
    · exact h
  have hle : Subgroup.zpowers z ≤ Z := Subgroup.zpowers_le.mpr hz
  have hcard : Nat.card Z ≤ Nat.card (Subgroup.zpowers z) :=
    le_of_eq (by rw [hZ, Nat.card_zpowers, hord])
  have heq : Subgroup.zpowers z = Z := Subgroup.eq_of_le_of_card_ge hle hcard
  rw [heq]
  exact hw

theorem zpow_eq_one_or_eq_or_eq_sq {G : Type*} [Group G] {z : G} (h3 : z ^ 3 = 1)
    (hz1 : z ≠ 1) (m : ℤ) : z ^ m = 1 ∨ z ^ m = z ∨ z ^ m = z ^ 2 := by
  have hord : orderOf z = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one h3) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hz1
    · exact h
  have hm : z ^ (m % 3) = z ^ m := by
    have := zpow_mod_orderOf z m
    rw [hord] at this
    exact_mod_cast this
  have hr : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
  rcases hr with h | h | h
  · left
    rw [← hm, h, zpow_zero]
  · right; left
    rw [← hm, h, zpow_one]
  · right; right
    rw [← hm, h]
    simp

theorem exists_noncentral_of_isTripleCover_ON {W : Type*} [Group W]
    (h : CFSG.RankThree.PartTwo.Sec4.IsTripleCover W CFSG.Blueprint.NativeSporadic.ON) :
    ∃ x : W, x ^ 3 = 1 ∧ x ∉ Subgroup.center W := by
  obtain ⟨hZ, ⟨e⟩⟩ := h
  obtain ⟨f, hker, hsurj⟩ : ∃ f : W →* CFSG.Blueprint.NativeSporadic.ON,
      (∀ w, f w = 1 ↔ w ∈ Subgroup.center W) ∧ Function.Surjective f := by
    refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center W)), fun w => ?_, fun y => ?_⟩
    · exact e.map_eq_one_iff.trans (QuotientGroup.eq_one_iff w)
    · obtain ⟨q, rfl⟩ := e.surjective y
      obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨w, rfl⟩
  have hcen : ∀ w ∈ Subgroup.center W, w ^ 3 = 1 := fun w hw =>
    pow_three_eq_one_of_mem_of_card_eq_three hZ hw
  obtain ⟨E, hE, hEcard⟩ := CFSG.SectionRank.ON_elementary_three_rank_four
  obtain ⟨hEc, hEp⟩ := hE
  have hEfin : Finite E := Nat.finite_of_card_ne_zero (by rw [hEcard]; norm_num)
  have hEnt : Nontrivial E := by
    rw [← Finite.one_lt_card_iff_nontrivial, hEcard]
    norm_num
  obtain ⟨⟨a₀, ha₀E⟩, ha₀1'⟩ := exists_ne (1 : E)
  have ha₀1 : a₀ ≠ 1 := fun h' => ha₀1' (Subtype.ext h')
  have ha₀3 : a₀ ^ 3 = 1 := hEp a₀ ha₀E
  have hord : orderOf a₀ = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one ha₀3) with h' | h'
    · exact absurd (orderOf_eq_one_iff.mp h') ha₀1
    · exact h'
  have hZa : Finite (Subgroup.zpowers a₀) :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hord]; norm_num)
  obtain ⟨b₀, hb₀E, hb₀⟩ : ∃ y ∈ E, y ∉ Subgroup.zpowers a₀ := by
    by_contra hcon
    have hle : E ≤ Subgroup.zpowers a₀ := by
      intro y hy
      by_contra hy'
      exact hcon ⟨y, hy, hy'⟩
    have hle' := Subgroup.card_le_of_le hle
    rw [hEcard, Nat.card_zpowers, hord] at hle'
    norm_num at hle'
  have hb₀3 : b₀ ^ 3 = 1 := hEp b₀ hb₀E
  have hb₀1 : b₀ ≠ 1 := fun h' => hb₀ (by rw [h']; exact Subgroup.one_mem _)
  have hcomm_ab : a₀ * b₀ = b₀ * a₀ := by
    have h : (⟨a₀, ha₀E⟩ : E) * ⟨b₀, hb₀E⟩ = (⟨b₀, hb₀E⟩ : E) * ⟨a₀, ha₀E⟩ :=
      hEc.is_comm.comm _ _
    have h2 := congrArg Subtype.val h
    rw [Subgroup.coe_mul, Subgroup.coe_mul] at h2
    exact h2
  obtain ⟨a, ha⟩ := hsurj a₀
  obtain ⟨b, hb⟩ := hsurj b₀
  have hzc : a ^ 3 ∈ Subgroup.center W := (hker _).mp (by rw [map_pow, ha, ha₀3])
  have hbc : b ^ 3 ∈ Subgroup.center W := (hker _).mp (by rw [map_pow, hb, hb₀3])
  have hcomm_mem : ∀ u v : W, f u * f v = f v * f u →
      u * v * u⁻¹ * v⁻¹ ∈ Subgroup.center W := by
    intro u v huv
    refine (hker _).mp ?_
    simp only [map_mul, map_inv]
    rw [huv]
    group
  by_cases hA : a ^ 3 = 1
  · exact ⟨a, hA, fun hmem => ha₀1 (ha.symm.trans ((hker a).mpr hmem))⟩
  by_cases hB : b ^ 3 = 1
  · exact ⟨b, hB, fun hmem => hb₀1 (hb.symm.trans ((hker b).mpr hmem))⟩
  have hbz : b ^ 3 ∈ Subgroup.zpowers (a ^ 3) :=
    mem_zpowers_of_card_eq_three hZ hzc hA hbc
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hbz
  rcases zpow_eq_one_or_eq_or_eq_sq (hcen _ hzc) hA m with hm1 | hm2 | hm3
  · exact absurd (hm.symm.trans hm1) hB
  ·
    have hb3 : b ^ 3 = a ^ 3 := hm.symm.trans hm2
    have hc2 : a * b ^ 2 * a⁻¹ * (b ^ 2)⁻¹ ∈ Subgroup.center W := by
      apply hcomm_mem a (b ^ 2)
      rw [map_pow, ha, hb]
      exact mul_pow_two_eq_of_mul_eq hcomm_ab
    have hcube : (a * b ^ 2) ^ 3 = a ^ 3 * (b ^ 2) ^ 3 :=
      pow_three_mul_of_commutator_mem_center hc2 (hcen _ hc2)
    have hsq : (b ^ 2) ^ 3 = (a ^ 3) ^ 2 := by
      rw [show (b ^ 2) ^ 3 = (b ^ 3) ^ 2 by group, hb3]
    refine ⟨a * b ^ 2, ?_, fun hmem => ?_⟩
    · rw [hcube, hsq]
      calc a ^ 3 * (a ^ 3) ^ 2 = (a ^ 3) ^ 3 := by group
        _ = 1 := hcen _ hzc
    · have h1 := (hker _).mpr hmem
      rw [map_mul, map_pow, ha, hb] at h1
      have hinv : b₀ ^ 2 = a₀⁻¹ := eq_inv_of_mul_eq_one_right h1
      have hbb : b₀ = a₀⁻¹ ^ 2 := by
        calc b₀ = (b₀ ^ 2) ^ 2 := by
              rw [show (b₀ ^ 2) ^ 2 = b₀ ^ 3 * b₀ by group, hb₀3, one_mul]
          _ = a₀⁻¹ ^ 2 := by rw [hinv]
      apply hb₀
      rw [hbb]
      exact pow_mem (inv_mem (Subgroup.mem_zpowers a₀)) 2
  ·
    have hb3 : b ^ 3 = (a ^ 3) ^ 2 := hm.symm.trans hm3
    have hc1 : a * b * a⁻¹ * b⁻¹ ∈ Subgroup.center W := by
      apply hcomm_mem a b
      rw [ha, hb]
      exact hcomm_ab
    have hcube : (a * b) ^ 3 = a ^ 3 * b ^ 3 :=
      pow_three_mul_of_commutator_mem_center hc1 (hcen _ hc1)
    refine ⟨a * b, ?_, fun hmem => ?_⟩
    · rw [hcube, hb3]
      calc a ^ 3 * (a ^ 3) ^ 2 = (a ^ 3) ^ 3 := by group
        _ = 1 := hcen _ hzc
    · have h1 := (hker _).mpr hmem
      rw [map_mul, ha, hb] at h1
      have hinv : b₀ = a₀⁻¹ := eq_inv_of_mul_eq_one_right h1
      apply hb₀
      rw [hinv]
      exact inv_mem (Subgroup.mem_zpowers a₀)

end CFSG.RankThree.PartTwo.Sec4.Ronan148V
