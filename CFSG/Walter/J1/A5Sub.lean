module

public import CFSG.Walter.J1.A5
public import CFSG.Walter.J1.Tools
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star

public section

namespace CFSG.Walter.J1

namespace A5Sub

variable {G : Type*} [Group G] {F : Subgroup G} (e : F ≃* alternatingGroup (Fin 5))
include e

@[expose] noncomputable def ι : alternatingGroup (Fin 5) →* G :=
  F.subtype.comp e.symm.toMonoidHom

theorem ι_injective : Function.Injective (ι e) :=
  F.subtype_injective.comp e.symm.injective

theorem ι_apply {x : G} (hx : x ∈ F) : ι e (e ⟨x, hx⟩) = x := by
  simp [ι]

theorem ι_mem (a : alternatingGroup (Fin 5)) : ι e a ∈ F := (e.symm a).2

theorem ι_eq_iff {a b : alternatingGroup (Fin 5)} : ι e a = ι e b ↔ a = b :=
  (ι_injective e).eq_iff

theorem exists_ι {x : G} (hx : x ∈ F) : ∃ a, ι e a = x := ⟨_, ι_apply e hx⟩

theorem ι_eq_one_iff {a : alternatingGroup (Fin 5)} : ι e a = 1 ↔ a = 1 := by
  rw [← map_one (ι e), ι_eq_iff]

theorem card_eq : Nat.card F = 60 := by
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  rfl

theorem pow_eq_one {x : G} (hx : x ∈ F) : x ^ 2 = 1 ∨ x ^ 3 = 1 ∨ x ^ 5 = 1 := by
  obtain ⟨a, rfl⟩ := exists_ι e hx
  simp only [← map_pow, ι_eq_one_iff]
  exact A5.pow_eq_one a

theorem mem_zpowers_of_commute_three {x y : G} (hx : x ∈ F) (hy : y ∈ F) (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) (hxy : x * y = y * x) : y ∈ Subgroup.zpowers x := by
  obtain ⟨a, rfl⟩ := exists_ι e hx
  obtain ⟨b, rfl⟩ := exists_ι e hy
  rw [← map_pow, ι_eq_one_iff] at hx3
  rw [Ne, ι_eq_one_iff] at hx1
  rw [← map_mul, ← map_mul, ι_eq_iff] at hxy
  rcases A5.centralizer_three a b ⟨hx3, hx1, hxy⟩ with h | h | h <;> subst h
  · simp
  · exact Subgroup.mem_zpowers _
  · rw [map_pow]
    exact Subgroup.npow_mem_zpowers _ 2

theorem mem_zpowers_of_commute_five {x y : G} (hx : x ∈ F) (hy : y ∈ F) (hx5 : x ^ 5 = 1)
    (hx1 : x ≠ 1) (hxy : x * y = y * x) : y ∈ Subgroup.zpowers x := by
  obtain ⟨a, rfl⟩ := exists_ι e hx
  obtain ⟨b, rfl⟩ := exists_ι e hy
  rw [← map_pow, ι_eq_one_iff] at hx5
  rw [Ne, ι_eq_one_iff] at hx1
  rw [← map_mul, ← map_mul, ι_eq_iff] at hxy
  rcases A5.centralizer_five a b ⟨hx5, hx1, hxy⟩ with h | h | h | h | h <;> subst h
  · simp
  · exact Subgroup.mem_zpowers _
  all_goals rw [map_pow]; exact Subgroup.npow_mem_zpowers _ _

theorem sq_eq_one_of_commute {x y : G} (hx : x ∈ F) (hy : y ∈ F) (hx2 : x ^ 2 = 1)
    (hx1 : x ≠ 1) (hxy : x * y = y * x) : y ^ 2 = 1 := by
  obtain ⟨a, rfl⟩ := exists_ι e hx
  obtain ⟨b, rfl⟩ := exists_ι e hy
  rw [← map_pow, ι_eq_one_iff] at hx2
  rw [Ne, ι_eq_one_iff] at hx1
  rw [← map_mul, ← map_mul, ι_eq_iff] at hxy
  rw [← map_pow, ι_eq_one_iff]
  exact A5.centralizer_two a b ⟨hx2, hx1, hxy⟩

theorem exists_inv {x : G} (hx : x ∈ F) (hx1 : x ≠ 1) (hodd : x ^ 15 = 1) :
    ∃ y ∈ F, y ^ 2 = 1 ∧ y ≠ 1 ∧ y * x * y⁻¹ = x⁻¹ := by
  obtain ⟨a, rfl⟩ := exists_ι e hx
  rw [← map_pow, ι_eq_one_iff] at hodd
  rw [Ne, ι_eq_one_iff] at hx1
  obtain ⟨b, hb2, hb1, hb⟩ := A5.exists_inv a ⟨hx1, hodd⟩
  refine ⟨ι e b, ι_mem e b, ?_, ?_, ?_⟩
  · rw [← map_pow, hb2, map_one]
  · rwa [Ne, ι_eq_one_iff]
  · rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, hb]

theorem conj_not_mem_zpowers {x y : G} (hx : x ∈ F) (hy : y ∈ F) (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) (hy5 : y ^ 5 = 1) (hy1 : y ≠ 1) :
    x * y * x⁻¹ ∉ Subgroup.zpowers y := by
  obtain ⟨a, rfl⟩ := exists_ι e hx
  obtain ⟨b, rfl⟩ := exists_ι e hy
  rw [← map_pow, ι_eq_one_iff] at hx3 hy5
  rw [Ne, ι_eq_one_iff] at hx1 hy1
  obtain ⟨h1, h2, h3, h4⟩ := A5.three_five a b ⟨hx3, hx1, hy5, hy1⟩
  rintro ⟨k, hk⟩
  have hk' : b ^ k = a * b * a⁻¹ := by
    rw [← ι_eq_iff e, map_zpow, map_mul, map_mul, map_inv]
    exact hk
  have h5 : b ^ (5 : ℤ) = 1 := by exact_mod_cast hy5
  rw [zpow_eq_zpow_emod k h5] at hk'
  have hnn : 0 ≤ k % 5 := Int.emod_nonneg _ (by norm_num)
  have hlt : k % 5 < 5 := Int.emod_lt_of_pos _ (by norm_num)
  obtain ⟨n, hn⟩ : ∃ n : ℕ, k % 5 = n := ⟨(k % 5).toNat, (Int.toNat_of_nonneg hnn).symm⟩
  rw [hn, zpow_natCast] at hk'
  have hn5 : n < 5 := by omega
  interval_cases n
  · rw [pow_zero] at hk'
    apply hy1
    have h0 : a * b * a⁻¹ = 1 := hk'.symm
    rw [mul_inv_eq_one, mul_eq_left] at h0
    exact h0
  · exact h1 (by rw [← hk', pow_one])
  · exact h2 hk'.symm
  · exact h3 hk'.symm
  · exact h4 hk'.symm

theorem four_group {a b : G} (ha : a ∈ F) (hb : b ∈ F) (ha2 : a ^ 2 = 1) (hb2 : b ^ 2 = 1)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) (hc : a * b = b * a) :
    ∃ c ∈ F, c ^ 3 = 1 ∧ c * a * c⁻¹ = b ∧ c * b * c⁻¹ = a * b := by
  obtain ⟨a', rfl⟩ := exists_ι e ha
  obtain ⟨b', rfl⟩ := exists_ι e hb
  rw [← map_pow, ι_eq_one_iff] at ha2 hb2
  rw [Ne, ι_eq_one_iff] at ha1 hb1
  rw [Ne, ι_eq_iff] at hab
  rw [← map_mul, ← map_mul, ι_eq_iff] at hc
  obtain ⟨c, hc3, hca, hcb⟩ := A5.four_group a' b' ⟨ha2, hb2, ha1, hb1, hab, hc⟩
  refine ⟨ι e c, ι_mem e c, ?_, ?_, ?_⟩
  · rw [← map_pow, hc3, map_one]
  · rw [← map_inv, ← map_mul, ← map_mul, hca]
  · rw [← map_inv, ← map_mul, ← map_mul, hcb, map_mul]

theorem ncard_involutions : {x : G | x ∈ F ∧ x ^ 2 = 1 ∧ x ≠ 1}.ncard = 15 := by
  classical
  have h := A5.card_involutions
  have himage : {x : G | x ∈ F ∧ x ^ 2 = 1 ∧ x ≠ 1} =
      ι e '' {a : alternatingGroup (Fin 5) | a ^ 2 = 1 ∧ a ≠ 1} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · rintro ⟨hx, hx2, hx1⟩
      obtain ⟨a, rfl⟩ := exists_ι e hx
      refine ⟨a, ⟨?_, ?_⟩, rfl⟩
      · rwa [← map_pow, ι_eq_one_iff] at hx2
      · rwa [Ne, ι_eq_one_iff] at hx1
    · rintro ⟨a, ⟨ha2, ha1⟩, rfl⟩
      refine ⟨ι_mem e a, ?_, ?_⟩
      · rw [← map_pow, ha2, map_one]
      · rwa [Ne, ι_eq_one_iff]
  rw [himage, Set.ncard_image_of_injective _ (ι_injective e)]
  rw [Set.ncard_eq_toFinset_card']
  convert h using 2
  ext a
  simp

theorem isSimpleGroup : IsSimpleGroup F :=
  have : IsSimpleGroup (alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (by simp)
  e.isSimpleGroup

theorem card_ne_fifteen {K : Subgroup G} (hK : K ≤ F) : Nat.card K ≠ 15 := by
  intro h15
  have : IsSimpleGroup F := isSimpleGroup e
  set K' := K.subgroupOf F
  have hK' : Nat.card K' = 15 := by
    rw [← h15]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK).toEquiv
  have hidx : K'.index = 4 := by
    have := K'.index_mul_card
    rw [hK', card_eq e] at this
    omega
  have : K'.FiniteIndex := ⟨by rw [hidx]; norm_num⟩
  have hdvd := Subgroup.index_normalCore_dvd_factorial_index K'
  rw [hidx] at hdvd
  rcases (Subgroup.normalCore_normal K').eq_bot_or_eq_top with hb | ht
  · rw [hb, Subgroup.index_bot, card_eq e] at hdvd
    revert hdvd
    decide
  · have hle := Subgroup.normalCore_le K'
    rw [ht, top_le_iff] at hle
    rw [hle, Subgroup.index_top] at hidx
    omega

theorem card_odd {K : Subgroup G} (hK : K ≤ F) (hodd : Odd (Nat.card K)) :
    Nat.card K = 1 ∨ Nat.card K = 3 ∨ Nat.card K = 5 := by
  have hdvd : Nat.card K ∣ 60 := card_eq e ▸ Subgroup.card_dvd_of_le hK
  have h15 := card_ne_fifteen e hK
  have hle : Nat.card K ≤ 60 := Nat.le_of_dvd (by norm_num) hdvd
  obtain ⟨k, hk⟩ := hodd
  interval_cases hc : Nat.card K <;> omega

theorem sq_eq_one_of_pow {x : G} (hx : x ∈ F) {n : ℕ} (hn : x ^ 2 ^ n = 1) : x ^ 2 = 1 := by
  have h2 : orderOf x ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
  rcases pow_eq_one e hx with h | h | h
  · exact h
  · have h3 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one h
    have : orderOf x = 1 := Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.coprime_dvd_left h3 (Nat.Coprime.pow_right n (by norm_num))) h2
    rw [orderOf_eq_one_iff.mp this, one_pow]
  · have h5 : orderOf x ∣ 5 := orderOf_dvd_of_pow_eq_one h
    have : orderOf x = 1 := Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.coprime_dvd_left h5 (Nat.Coprime.pow_right n (by norm_num))) h2
    rw [orderOf_eq_one_iff.mp this, one_pow]

theorem card_dvd_four_of_isPGroup {P : Subgroup G} (hP : P ≤ F) (hP2 : IsPGroup 2 P) :
    Nat.card P ∣ 4 := by
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [card_eq e]; norm_num)
  have : Finite P := Finite.of_injective _ (Subgroup.inclusion_injective hP)
  obtain ⟨n, hn⟩ := hP2.exists_card_eq
  have hdvd : Nat.card P ∣ 60 := card_eq e ▸ Subgroup.card_dvd_of_le hP
  rw [hn] at hdvd ⊢
  have hn2 : n ≤ 2 := by
    by_contra hlt
    have : 2 ^ 3 ∣ 60 := (pow_dvd_pow 2 (by omega)).trans hdvd
    revert this
    decide
  exact pow_dvd_pow 2 hn2

theorem inf_centralizer_eq {V : Subgroup G} (hV : V ≤ F) (hV4 : Nat.card V = 4) :
    F ⊓ Subgroup.centralizer (V : Set G) = V := by
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [card_eq e]; norm_num)
  have : Finite V := Nat.finite_of_card_ne_zero (by rw [hV4]; norm_num)
  have hV2 : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by rw [hV4]; norm_num)
  have hsq : ∀ x ∈ V, x ^ 2 = 1 := by
    intro x hx
    obtain ⟨k, hk⟩ := hV2 ⟨x, hx⟩
    have hk' := congrArg Subtype.val hk
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at hk'
    exact sq_eq_one_of_pow e (hV hx) hk'
  have hVab : V ≤ Subgroup.centralizer (V : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 := hsq _ (V.mul_mem hy hx)
    have hx' := hsq x hx
    have hy' := hsq y hy
    rw [pow_two] at h1 hx' hy'
    rw [eq_inv_of_mul_eq_one_left h1, mul_inv_rev, inv_eq_of_mul_eq_one_right hx',
      inv_eq_of_mul_eq_one_right hy']
  obtain ⟨v, hvV, hv1⟩ : ∃ v ∈ V, v ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : V = ⊥ := (Subgroup.eq_bot_iff_forall V).mpr hcon
    rw [this, Subgroup.card_bot] at hV4
    omega
  set C := F ⊓ Subgroup.centralizer (V : Set G)
  have hVC : V ≤ C := le_inf hV hVab
  have : Finite C := Finite.of_injective _ (Subgroup.inclusion_injective (inf_le_left : C ≤ F))
  have hC2 : IsPGroup 2 C := by
    intro x
    refine ⟨1, ?_⟩
    apply Subtype.ext
    have hxF : (x : G) ∈ F := x.2.1
    have hxv : v * x = x * v := Subgroup.mem_centralizer_iff.mp x.2.2 v hvV
    have := sq_eq_one_of_commute e (hV hvV) hxF (hsq v hvV) hv1 hxv
    simpa using this
  have hCdvd := card_dvd_four_of_isPGroup e inf_le_left hC2
  have hle : Nat.card C ≤ 4 := Nat.le_of_dvd (by norm_num) hCdvd
  exact (Subgroup.eq_of_le_of_card_ge hVC (by rw [hV4]; exact hle)).symm

theorem pow_three_or_five {y : G} (hy : y ∈ F) (hodd : Odd (orderOf y)) :
    y ^ 3 = 1 ∨ y ^ 5 = 1 := by
  rcases pow_eq_one e hy with h | h | h
  · left
    have h2 : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one h
    have : orderOf y = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h1 | h1
      · exact h1
      · rw [h1] at hodd
        exact absurd hodd (by decide)
    rw [orderOf_eq_one_iff.mp this, one_pow]
  · exact Or.inl h
  · exact Or.inr h

theorem conj_eq_inv {y v : G} (hy : y ∈ F) (hv : v ∈ F) (hy1 : y ≠ 1) (hodd : Odd (orderOf y))
    (hv2 : v ^ 2 = 1) (hv1 : v ≠ 1) (hvy : v * y * v⁻¹ ∈ Subgroup.zpowers y) :
    v * y * v⁻¹ = y⁻¹ := by
  have h35 := pow_three_or_five e hy hodd
  obtain ⟨k, hk⟩ := hvy
  have hk' : y ^ k = v * y * v⁻¹ := hk
  have hdisj : v * y * v⁻¹ = 1 ∨ v * y * v⁻¹ = y ∨ v * y * v⁻¹ = y ^ 2 ∨ v * y * v⁻¹ = y ^ 3 ∨
      v * y * v⁻¹ = y ^ 4 := by
    have key : ∀ n : ℤ, 0 < n → n ≤ 5 → y ^ n = 1 → ∃ j : ℕ, j < 5 ∧ y ^ k = y ^ j := by
      intro n hn0 hn5 hn
      rw [zpow_eq_zpow_emod k hn]
      have hnn : 0 ≤ k % n := Int.emod_nonneg _ (by omega)
      have hlt : k % n < n := Int.emod_lt_of_pos _ hn0
      refine ⟨(k % n).toNat, by omega, ?_⟩
      rw [← zpow_natCast, Int.toNat_of_nonneg hnn]
    obtain ⟨j, hj5, hj⟩ : ∃ j : ℕ, j < 5 ∧ y ^ k = y ^ j := by
      rcases h35 with h3 | h5
      · exact key 3 (by norm_num) (by norm_num) (by exact_mod_cast h3)
      · exact key 5 (by norm_num) (by norm_num) (by exact_mod_cast h5)
    rw [← hk', hj]
    interval_cases j <;> simp
  obtain ⟨a, rfl⟩ := exists_ι e hy
  obtain ⟨b, rfl⟩ := exists_ι e hv
  have h15 : a ^ 15 = 1 := by
    rw [← ι_eq_one_iff e, map_pow]
    rcases h35 with h3 | h5
    · rw [show (15 : ℕ) = 3 * 5 by norm_num, pow_mul, h3, one_pow]
    · rw [show (15 : ℕ) = 5 * 3 by norm_num, pow_mul, h5, one_pow]
  rw [Ne, ι_eq_one_iff] at hy1 hv1
  rw [← map_pow, ι_eq_one_iff] at hv2
  simp only [← map_inv, ← map_mul, ← map_pow, ← map_one (ι e), ι_eq_iff] at hdisj ⊢
  exact A5.conj_inv a b ⟨hy1, h15, hv2, hv1, hdisj⟩

theorem eq_bot_of_normalized {L : Subgroup G} (hL : L ≤ F) (hodd : Odd (Nat.card L))
    {a b : G} (ha : a ∈ F) (hb : b ∈ F) (ha2 : a ^ 2 = 1) (hb2 : b ^ 2 = 1) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) (hab : a ≠ b) (hc : a * b = b * a)
    (haL : a ∈ Subgroup.normalizer (L : Set G)) (hbL : b ∈ Subgroup.normalizer (L : Set G)) :
    L = ⊥ := by
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [card_eq e]; norm_num)
  have : Finite L := Finite.of_injective _ (Subgroup.inclusion_injective hL)
  by_contra hne
  obtain ⟨y, hyL, hy1⟩ : ∃ y ∈ L, y ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hne ((Subgroup.eq_bot_iff_forall L).mpr hcon)
  have hyodd : Odd (orderOf y) := Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard L hyL)
  have hLy : L = Subgroup.zpowers y := by
    have hcard := card_odd e hL hodd
    have hdvd : orderOf y ∣ Nat.card L := Subgroup.orderOf_dvd_natCard L hyL
    have hne1 : orderOf y ≠ 1 := fun h1 => hy1 (orderOf_eq_one_iff.mp h1)
    have hord : orderOf y = Nat.card L := by
      rcases hcard with h1 | h3 | h5
      · rw [h1] at hdvd
        exact absurd (Nat.dvd_one.mp hdvd) hne1
      · rw [h3] at hdvd ⊢
        rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
        · exact absurd h hne1
        · exact h
      · rw [h5] at hdvd ⊢
        rcases (Nat.dvd_prime Nat.prime_five).mp hdvd with h | h
        · exact absurd h hne1
        · exact h
    refine (Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hyL) ?_).symm
    rw [Nat.card_zpowers, hord]
  have hay : a * y * a⁻¹ = y⁻¹ := conj_eq_inv e (hL hyL) ha hy1 hyodd ha2 ha1 (by
    rw [← hLy]
    exact (Subgroup.mem_normalizer_iff.mp haL y).mp hyL)
  have hby : b * y * b⁻¹ = y⁻¹ := conj_eq_inv e (hL hyL) hb hy1 hyodd hb2 hb1 (by
    rw [← hLy]
    exact (Subgroup.mem_normalizer_iff.mp hbL y).mp hyL)
  have hab1 : a * b ≠ 1 := by
    intro h1
    apply hab
    have hb' : b = a⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [hb']
    rw [pow_two] at ha2
    exact (inv_eq_of_mul_eq_one_right ha2).symm
  have habF : a * b ∈ F := F.mul_mem ha hb
  have hab2 : (a * b) ^ 2 = 1 := by
    rw [pow_two] at ha2 hb2 ⊢
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hc]
      _ = 1 := by rw [← mul_assoc, ha2, one_mul, hb2]
  have hcy : a * b * y = y * (a * b) := by
    have : (a * b) * y * (a * b)⁻¹ = y := by
      calc (a * b) * y * (a * b)⁻¹ = a * (b * y * b⁻¹) * a⁻¹ := by group
        _ = a * y⁻¹ * a⁻¹ := by rw [hby]
        _ = (a * y * a⁻¹)⁻¹ := by group
        _ = y := by rw [hay, inv_inv]
    calc a * b * y = ((a * b) * y * (a * b)⁻¹) * (a * b) := by group
      _ = y * (a * b) := by rw [this]
  have hy2 := sq_eq_one_of_commute e habF (hL hyL) hab2 hab1 hcy
  have h2 : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one hy2
  rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h1 | h1
  · exact hy1 (orderOf_eq_one_iff.mp h1)
  · rw [h1] at hyodd
    exact absurd hyodd (by decide)

theorem exists_conj_eq {X Y : Subgroup G} (hX : X ≤ F) (hY : Y ≤ F) {p : ℕ}
    (hp : p = 3 ∨ p = 5) (hXp : Nat.card X = p) (hYp : Nat.card Y = p) :
    ∃ f ∈ F, X.map (MulAut.conj f).toMonoidHom = Y := by
  have hpp : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  obtain ⟨x, hxX, hx1⟩ := exists_ne_one_of_card hXp hpp.one_lt
  obtain ⟨y, hyY, hy1⟩ := exists_ne_one_of_card hYp hpp.one_lt
  have hXx := eq_zpowers_of_card_prime hpp hXp hxX hx1
  have hYy := eq_zpowers_of_card_prime hpp hYp hyY hy1
  have hxp : x ^ p = 1 := by
    have : Finite X := Nat.finite_of_card_ne_zero (by rw [hXp]; exact hpp.ne_zero)
    have h1 := pow_card_eq_one' (G := X) (x := ⟨x, hxX⟩)
    rw [hXp] at h1
    simpa using congrArg Subtype.val h1
  have hyp : y ^ p = 1 := by
    have : Finite Y := Nat.finite_of_card_ne_zero (by rw [hYp]; exact hpp.ne_zero)
    have h1 := pow_card_eq_one' (G := Y) (x := ⟨y, hyY⟩)
    rw [hYp] at h1
    simpa using congrArg Subtype.val h1
  obtain ⟨a, rfl⟩ := exists_ι e (hX hxX)
  obtain ⟨b, rfl⟩ := exists_ι e (hY hyY)
  rw [← map_pow, ι_eq_one_iff] at hxp hyp
  rw [Ne, ι_eq_one_iff] at hx1 hy1
  have key : ∀ c : alternatingGroup (Fin 5), (c * a * c⁻¹ = b ∨ c * a * c⁻¹ = b ^ 2) →
      ∃ f ∈ F, X.map (MulAut.conj f).toMonoidHom = Y := by
    intro c hc
    refine ⟨ι e c, ι_mem e c, ?_⟩
    rw [hXx, hYy, MonoidHom.map_zpowers]
    change Subgroup.zpowers (ι e c * ι e a * (ι e c)⁻¹) = _
    rw [← map_inv, ← map_mul, ← map_mul]
    rcases hc with hc | hc
    · rw [hc]
    · rw [hc, map_pow]
      apply le_antisymm
      · rw [Subgroup.zpowers_le]
        exact Subgroup.npow_mem_zpowers _ 2
      · rw [Subgroup.zpowers_le]
        rcases hp with rfl | rfl
        · have h3 : ι e b ^ 3 = 1 := by rw [← map_pow, hyp, map_one]
          have h4 : (ι e b ^ 2) ^ 2 = ι e b := by
            rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, h3, one_mul, pow_one]
          have hmem := Subgroup.npow_mem_zpowers (ι e b ^ 2) 2
          rwa [h4] at hmem
        · have h5 : ι e b ^ 5 = 1 := by rw [← map_pow, hyp, map_one]
          have h6 : (ι e b ^ 2) ^ 3 = ι e b := by
            rw [← pow_mul, show 2 * 3 = 5 + 1 by norm_num, pow_add, h5, one_mul, pow_one]
          have hmem := Subgroup.npow_mem_zpowers (ι e b ^ 2) 3
          rwa [h6] at hmem
  rcases hp with rfl | rfl
  · obtain ⟨c, hc⟩ := A5.conj_three a b ⟨hxp, hx1, hyp, hy1⟩
    exact key c (Or.inl hc)
  · obtain ⟨c, hc⟩ := A5.conj_five a b ⟨hxp, hx1, hyp, hy1⟩
    exact key c hc

theorem mem_normalizer_three {c f g : G} (hc : c ∈ F) (hf : f ∈ F) (hg : g ∈ F)
    (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) (hf2 : f ^ 2 = 1) (hf1 : f ≠ 1) (hfc : f * c * f⁻¹ = c⁻¹)
    (hgc : g * c * g⁻¹ = c ∨ g * c * g⁻¹ = c ^ 2) :
    g = 1 ∨ g = c ∨ g = c ^ 2 ∨ g = f ∨ g = c * f ∨ g = c ^ 2 * f := by
  obtain ⟨x, rfl⟩ := exists_ι e hc
  obtain ⟨y, rfl⟩ := exists_ι e hf
  obtain ⟨z, rfl⟩ := exists_ι e hg
  rw [← map_pow, ι_eq_one_iff] at hc3 hf2
  rw [Ne, ι_eq_one_iff] at hc1 hf1
  simp only [← map_inv, ← map_mul, ← map_pow, ι_eq_iff, ← map_one (ι e)] at hfc hgc ⊢
  exact A5.normalizer_three x ⟨hc3, hc1⟩ y ⟨hf2, hf1, hfc⟩ z hgc

end A5Sub

end CFSG.Walter.J1
