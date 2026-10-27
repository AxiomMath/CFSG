module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.Commutator.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec15.LiebeckA6

local notation "A6" => alternatingGroup (Fin 6)

private theorem perm_pow_nine : ∀ y : Equiv.Perm (Fin 6), y ^ 9 = 1 → y ^ 3 = 1 := by
  decide +kernel

private theorem perm_pow_six : ∀ y : Equiv.Perm (Fin 6), y.sign = 1 → y ^ 6 = 1 →
    y ^ 2 = 1 ∨ y ^ 3 = 1 := by
  decide +kernel

private theorem perm_pow_ten : ∀ y : Equiv.Perm (Fin 6), y.sign = 1 → y ^ 10 = 1 →
    y ^ 2 = 1 ∨ y ^ 5 = 1 := by
  decide +kernel

private theorem card_A6 : Nat.card A6 = 360 := by
  rw [nat_card_alternatingGroup]
  norm_num [Nat.factorial]

private theorem coe_pow_eq_one {n : ℕ} {y : A6} :
    (y : Equiv.Perm (Fin 6)) ^ n = 1 ↔ y ^ n = 1 := by
  rw [← Subgroup.coe_pow]
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

private theorem orderOf_ne_six (y : A6) : orderOf y ≠ 6 := by
  intro h
  have hy : (y : Equiv.Perm (Fin 6)).sign = 1 := Equiv.Perm.mem_alternatingGroup.1 y.2
  have h6 : y ^ 6 = 1 := by
    have := pow_orderOf_eq_one y
    rwa [h] at this
  rcases perm_pow_six _ hy (coe_pow_eq_one.2 h6) with h2 | h3
  · have hd := orderOf_dvd_of_pow_eq_one (coe_pow_eq_one.1 h2)
    rw [h] at hd
    norm_num at hd
  · have hd := orderOf_dvd_of_pow_eq_one (coe_pow_eq_one.1 h3)
    rw [h] at hd
    norm_num at hd

private theorem orderOf_ne_ten (y : A6) : orderOf y ≠ 10 := by
  intro h
  have hy : (y : Equiv.Perm (Fin 6)).sign = 1 := Equiv.Perm.mem_alternatingGroup.1 y.2
  have h10 : y ^ 10 = 1 := by
    have := pow_orderOf_eq_one y
    rwa [h] at this
  rcases perm_pow_ten _ hy (coe_pow_eq_one.2 h10) with h2 | h5
  · have hd := orderOf_dvd_of_pow_eq_one (coe_pow_eq_one.1 h2)
    rw [h] at hd
    norm_num at hd
  · have hd := orderOf_dvd_of_pow_eq_one (coe_pow_eq_one.1 h5)
    rw [h] at hd
    norm_num at hd

private theorem not_commute_orderOf_three_or_five {t g : A6} (ht : orderOf t = 2)
    (hc : Commute g t) (hg : orderOf g = 3 ∨ orderOf g = 5) : False := by
  have hco : (orderOf g).Coprime (orderOf t) := by
    rw [ht]
    rcases hg with h | h <;> rw [h] <;> norm_num
  have hy := hc.orderOf_mul_eq_mul_orderOf_of_coprime hco
  rcases hg with h | h
  · exact orderOf_ne_six (g * t) (by rw [hy, h, ht])
  · exact orderOf_ne_ten (g * t) (by rw [hy, h, ht])

private theorem exists_pow_orderOf_two {z : A6} (hz1 : z ≠ 1) {k : ℕ} (hk : z ^ 2 ^ k = 1) :
    ∃ j : ℕ, orderOf (z ^ j) = 2 := by
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hk)
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hz1 (orderOf_eq_one_iff.1 (by rw [hm, pow_zero]))
  have h2 : 2 ∣ orderOf z := by
    rw [hm]
    exact dvd_pow_self 2 hm0
  exact ⟨orderOf z / 2, orderOf_pow_orderOf_div (orderOf_pos z).ne' h2⟩

private theorem not_commute_two_power {g z : A6} (hg : orderOf g = 3 ∨ orderOf g = 5)
    (hc : Commute g z) {k : ℕ} (hz1 : z ≠ 1) (hk : z ^ 2 ^ k = 1) : False := by
  obtain ⟨j, hj⟩ := exists_pow_orderOf_two hz1 hk
  exact not_commute_orderOf_three_or_five hj (hc.pow_right j) hg

theorem pow_three_eq_one_of_isPGroup {x : alternatingGroup (Fin 6)}
    (hx : IsPGroup 3 (Subgroup.zpowers x)) : x ^ 3 = 1 := by
  obtain ⟨k, hk⟩ := hx ⟨x, Subgroup.mem_zpowers x⟩
  have hk' : x ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hk')
  have h360 : orderOf x ∣ 360 := card_A6 ▸ orderOf_dvd_natCard x
  have hj2 : j ≤ 2 := by
    by_contra hc
    have h27 : 3 ^ 3 ∣ orderOf x := by
      rw [hj]
      exact pow_dvd_pow 3 (by omega)
    have h27' : 3 ^ 3 ∣ 360 := h27.trans h360
    norm_num at h27'
  have h9 : x ^ 9 = 1 := by
    have h : orderOf x ∣ 3 ^ 2 := by
      rw [hj]
      exact pow_dvd_pow 3 hj2
    simpa using orderOf_dvd_iff_pow_eq_one.1 h
  exact coe_pow_eq_one.1 (perm_pow_nine _ (coe_pow_eq_one.2 h9))

private theorem card_two_group {R : Subgroup A6} (hR : IsPGroup 2 R) (hR1 : R ≠ ⊥) :
    Nat.card R = 2 ∨ Nat.card R = 4 ∨ Nat.card R = 8 := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hR
  have hdvd : Nat.card R ∣ 360 := card_A6 ▸ Subgroup.card_subgroup_dvd_card R
  have hn3 : n ≤ 3 := by
    by_contra hc
    have h16 : 2 ^ 4 ∣ 360 := (pow_dvd_pow 2 (by omega)).trans (hn ▸ hdvd)
    norm_num at h16
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hR1 ((Subgroup.eq_bot_iff_card _).2 (by rw [hn, pow_zero]))
  interval_cases n <;> norm_num at hn <;> omega

private theorem exists_pow_two_eq_one {R : Subgroup A6} (hR : IsPGroup 2 R) {r : A6}
    (hr : r ∈ R) : ∃ k : ℕ, r ^ 2 ^ k = 1 := by
  obtain ⟨k, hk⟩ := hR ⟨r, hr⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

private noncomputable def conjNontriv (W : Subgroup A6) {g : A6}
    (hg : g ∈ Subgroup.normalizer (W : Set A6)) : Equiv.Perm ↥((W : Set A6) \ {1}) :=
  Equiv.subtypeEquiv (MulAut.conj g).toEquiv fun a => by
    have h1 : g * a * g⁻¹ = 1 ↔ a = 1 := by
      constructor
      · intro h
        rw [mul_inv_eq_one] at h
        exact mul_left_cancel (h.trans (mul_one g).symm)
      · rintro rfl
        simp
    show a ∈ (W : Set A6) \ {1} ↔ g * a * g⁻¹ ∈ (W : Set A6) \ {1}
    rw [Set.mem_diff, Set.mem_diff, Set.mem_singleton_iff, Set.mem_singleton_iff]
    exact and_congr (Subgroup.mem_set_normalizer_iff.1 hg a) (not_congr h1.symm)

private theorem conjNontriv_apply (W : Subgroup A6) {g : A6}
    (hg : g ∈ Subgroup.normalizer (W : Set A6)) (a : ↥((W : Set A6) \ {1})) :
    ((conjNontriv W hg a : ↥((W : Set A6) \ {1})) : A6) = g * (a : A6) * g⁻¹ :=
  rfl

private theorem conjNontriv_pow_apply (W : Subgroup A6) {g : A6}
    (hg : g ∈ Subgroup.normalizer (W : Set A6)) (n : ℕ) (a : ↥((W : Set A6) \ {1})) :
    (((conjNontriv W hg) ^ n) a : A6) = g ^ n * (a : A6) * (g ^ n)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show conjNontriv W hg ^ (n + 1) = conjNontriv W hg * conjNontriv W hg ^ n from
      pow_succ' _ _, Equiv.Perm.mul_apply, conjNontriv_apply, ih]
    group

private theorem conjNontriv_pow (W : Subgroup A6) {g : A6}
    (hg : g ∈ Subgroup.normalizer (W : Set A6)) {p : ℕ} (hgp : g ^ p = 1) :
    (conjNontriv W hg) ^ p = 1 := by
  refine Equiv.ext fun a => Subtype.ext ?_
  rw [conjNontriv_pow_apply, hgp]
  simp

private theorem card_nontriv (W : Subgroup A6) :
    Nat.card ↥((W : Set A6) \ {1}) = Nat.card W - 1 := by
  have h1 : Nat.card ↥((W : Set A6) \ {1}) = ((W : Set A6) \ {1}).ncard :=
    Nat.card_coe_set_eq _
  have h2 : Nat.card W = (W : Set A6).ncard := Nat.card_coe_set_eq _
  rw [h1, h2, Set.ncard_diff_singleton_of_mem (SetLike.mem_coe.2 W.one_mem)]

private theorem prime_dvd_card_sub_one {W : Subgroup A6} {g : A6}
    (hg : g ∈ Subgroup.normalizer (W : Set A6)) {p : ℕ} [Fact p.Prime] (hgp : g ^ p = 1)
    (hfix : ∀ a ∈ W, a ≠ 1 → g * a * g⁻¹ ≠ a) : p ∣ Nat.card W - 1 := by
  classical
  have : Fintype ↥((W : Set A6) \ {1}) := Fintype.ofFinite _
  have hmod := Equiv.Perm.card_compl_support_modEq (p := p) (n := 1)
    (σ := conjNontriv W hg) (by rw [pow_one]; exact conjNontriv_pow W hg hgp)
  have hsupp : (conjNontriv W hg).supportᶜ = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro a ha
    rw [Finset.mem_compl, Equiv.Perm.mem_support, not_not] at ha
    have h1 : g * (a : A6) * g⁻¹ = a := by
      rw [← conjNontriv_apply W hg a, ha]
    have ha' := (Set.mem_diff _).1 a.2
    exact hfix (a : A6) ha'.1 ha'.2 h1
  rw [hsupp, Finset.card_empty] at hmod
  have hdvd : p ∣ Fintype.card ↥((W : Set A6) \ {1}) := Nat.modEq_zero_iff_dvd.1 hmod.symm
  rw [← Nat.card_eq_fintype_card, card_nontriv] at hdvd
  exact hdvd

private theorem exists_fixed_of_not_dvd {W : Subgroup A6} {g : A6}
    (hg : g ∈ Subgroup.normalizer (W : Set A6)) {p : ℕ} [Fact p.Prime] (hgp : g ^ p = 1)
    (hnd : ¬ p ∣ Nat.card W - 1) : ∃ a ∈ W, a ≠ 1 ∧ g * a * g⁻¹ = a := by
  by_contra h
  exact hnd (prime_dvd_card_sub_one hg hgp fun a ha ha1 hfa => h ⟨a, ha, ha1, hfa⟩)

theorem card_eq_four_of_le_normalizer {R : Subgroup (alternatingGroup (Fin 6))}
    {x : alternatingGroup (Fin 6)} (hR : IsPGroup 2 R) (hR1 : R ≠ ⊥) (hx : orderOf x = 3)
    (hxR : x ∈ Subgroup.normalizer (R : Set (alternatingGroup (Fin 6)))) :
    Nat.card R = 4 ∧ (∀ r ∈ R, r ^ 2 = 1) ∧ ∀ r ∈ R, r ≠ 1 → x * r * x⁻¹ ≠ r := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx3 : x ^ 3 = 1 := by
    rw [← hx]
    exact pow_orderOf_eq_one x
  have hfix : ∀ r ∈ R, r ≠ 1 → x * r * x⁻¹ ≠ r := by
    intro r hr hr1 heq
    obtain ⟨k, hk⟩ := exists_pow_two_eq_one hR hr
    have hc : Commute x r := by
      show x * r = r * x
      calc x * r = x * r * x⁻¹ * x := by group
        _ = r * x := by rw [heq]
    exact not_commute_two_power (Or.inl hx) hc hr1 hk
  have hcard := card_two_group hR hR1
  have h3 : 3 ∣ Nat.card R - 1 := prime_dvd_card_sub_one hxR hx3 hfix
  have hR4 : Nat.card R = 4 := by omega
  refine ⟨hR4, fun r hr => ?_, hfix⟩
  by_contra hr2
  have hrR : orderOf (⟨r, hr⟩ : R) ∣ Nat.card R := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, hR4] at hrR
  have h4 : orderOf r = 4 := by
    have hle : orderOf r ≤ 4 := Nat.le_of_dvd (by norm_num) hrR
    have hpos : 0 < orderOf r := orderOf_pos r
    have hpow : orderOf r ∣ 2 → False := fun h2 => hr2 (orderOf_dvd_iff_pow_eq_one.1 h2)
    have h1 : orderOf r ≠ 1 := fun h => hpow (by simp [h])
    have h2 : orderOf r ≠ 2 := fun h => hpow (by simp [h])
    have h3 : orderOf r ≠ 3 := fun h => by
      rw [h] at hrR
      norm_num at hrR
    omega
  have hzp : Subgroup.zpowers r = R :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hr)
      (le_of_eq (by rw [Nat.card_zpowers, h4, hR4]))
  have hconj : x * r * x⁻¹ ∈ Subgroup.zpowers r := by
    rw [hzp]
    exact (Subgroup.mem_set_normalizer_iff.1 hxR r).1 hr
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hconj
  have hsq : (r ^ j) ^ 2 = 1 ∨ (r ^ j) ^ 2 = r ^ 2 := by
    have e : (r ^ j) ^ 2 = r ^ (j * 2) := by
      rw [← zpow_natCast, ← zpow_mul]
      norm_num
    have hm := zpow_mod_orderOf r (j * 2)
    have h4' : ((orderOf r : ℕ) : ℤ) = 4 := by
      rw [h4]
      norm_num
    rw [h4'] at hm
    rw [e, ← hm]
    rcases (by omega : j * 2 % 4 = 0 ∨ j * 2 % 4 = 2) with h | h
    · left
      rw [h, zpow_zero]
    · right
      rw [h]
      norm_num
  have hconj2 : x * r ^ 2 * x⁻¹ = (x * r * x⁻¹) ^ 2 := by
    rw [pow_two, pow_two]
    group
  rw [← hj] at hconj2
  rcases hsq with h1 | h1
  · rw [h1] at hconj2
    apply hr2
    calc r ^ 2 = x⁻¹ * (x * r ^ 2 * x⁻¹) * x := by group
      _ = 1 := by rw [hconj2]; group
  · rw [h1] at hconj2
    exact hfix (r ^ 2) (pow_mem hr 2) hr2 hconj2

theorem eq_of_card_twelve {K K₀ W : Subgroup (alternatingGroup (Fin 6))} (hK₀ : K₀ ≤ K)
    (h12 : Nat.card K₀ = 12) (h9 : ¬ 9 ∣ Nat.card K)
    (hgen : K ≤ Subgroup.closure {k | k ∈ K ∧ orderOf k = 3})
    (hW : IsPGroup 2 W) (hW1 : W ≠ ⊥) (hWK : W ≤ K)
    (hKW : K ≤ Subgroup.normalizer (W : Set (alternatingGroup (Fin 6)))) : K = K₀ := by
  have hWcard := card_two_group hW hW1
  have h5 : ¬ 5 ∣ Nat.card K := by
    intro h5
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    obtain ⟨g', hg'⟩ := exists_prime_orderOf_dvd_card' 5 h5
    have hg5 : orderOf (g' : A6) = 5 := by rw [Subgroup.orderOf_coe, hg']
    have hgW : (g' : A6) ∈ Subgroup.normalizer (W : Set A6) := hKW g'.2
    have hgp : (g' : A6) ^ 5 = 1 := by
      have := pow_orderOf_eq_one (g' : A6)
      rwa [hg5] at this
    obtain ⟨w, hwW, hw1, hgw⟩ := exists_fixed_of_not_dvd (p := 5) hgW hgp (by omega)
    have hc : Commute (g' : A6) w := by
      show (g' : A6) * w = w * g'
      calc (g' : A6) * w = (g' : A6) * w * (g' : A6)⁻¹ * (g' : A6) := by group
        _ = w * g' := by rw [hgw]
    obtain ⟨k, hk⟩ := exists_pow_two_eq_one hW hwW
    exact not_commute_two_power (Or.inr hg5) hc hw1 hk
  have hK360 : Nat.card K ∣ 360 := card_A6 ▸ Subgroup.card_subgroup_dvd_card K
  have h12K : 12 ∣ Nat.card K := h12 ▸ Subgroup.card_dvd_of_le hK₀
  have hKlt : Nat.card K < 361 := Nat.lt_succ_of_le (Nat.le_of_dvd (by norm_num) hK360)
  have hK24 : Nat.card K = 12 ∨ Nat.card K = 24 := by
    have key : ∀ n ∈ Nat.divisors 360, 12 ∣ n → ¬ 5 ∣ n → ¬ 9 ∣ n → n = 12 ∨ n = 24 := by
      decide +kernel
    exact key _ (Nat.mem_divisors.2 ⟨hK360, by norm_num⟩) h12K h5 h9
  rcases hK24 with hK12 | hK24
  · exact (Subgroup.eq_of_le_of_card_ge hK₀ (le_of_eq (by rw [hK12, h12]))).symm
  exfalso
  have hidx : (K₀.subgroupOf K).index = 2 := by
    have h1 := Subgroup.index_mul_card (K₀.subgroupOf K)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK₀).toEquiv, h12, hK24] at h1
    omega
  have : (K₀.subgroupOf K).Normal := Subgroup.normal_of_index_eq_two hidx
  have hk3 : ∀ k ∈ K, orderOf k = 3 → k ∈ K₀ := by
    intro k hk hk3
    set k' : K := ⟨k, hk⟩
    have hk'3 : k' ^ 3 = 1 := by
      apply Subtype.ext
      show k ^ 3 = 1
      rw [← hk3]
      exact pow_orderOf_eq_one k
    have h1 : orderOf (QuotientGroup.mk' (K₀.subgroupOf K) k') ∣ 3 := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← map_pow, hk'3, map_one]
    have h2 : orderOf (QuotientGroup.mk' (K₀.subgroupOf K) k') ∣ 2 := by
      have h := orderOf_dvd_natCard (QuotientGroup.mk' (K₀.subgroupOf K) k')
      rwa [← Subgroup.index_eq_card, hidx] at h
    have h3 : orderOf (QuotientGroup.mk' (K₀.subgroupOf K) k') = 1 := by
      have h := Nat.dvd_gcd h1 h2
      have hg : Nat.gcd 3 2 = 1 := by norm_num
      rw [hg] at h
      exact Nat.dvd_one.1 h
    rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at h3
    exact h3
  have hS : {k | k ∈ K ∧ orderOf k = 3} ⊆ (K₀ : Set A6) := by
    intro k hk
    exact hk3 k hk.1 hk.2
  have hsub : K ≤ K₀ := hgen.trans ((Subgroup.closure_le K₀).2 hS)
  have hle := Subgroup.card_le_of_le hsub
  omega

end CFSG.RankThree.PartTwo.Sec15.LiebeckA6

end
