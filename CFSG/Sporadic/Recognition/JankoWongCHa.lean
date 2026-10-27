module

public import CFSG.Sporadic.Recognition.JankoWongLemma9

public section

namespace CFSG.Sporadic.Recognition.JankoWong

open Equiv Equiv.Perm Subgroup

@[expose] def permFive1 : Perm (Fin 8) := swap 3 4 * swap 4 5 * swap 5 6 * swap 6 7

@[expose] def permFive2 : Perm (Fin 8) := swap 3 7 * swap 7 4 * swap 4 5 * swap 5 6

theorem permFive1_pow_five : permFive1 ^ 5 = 1 := by unfold permFive1; decide

theorem permFive2_pow_five : permFive2 ^ 5 = 1 := by unfold permFive2; decide

theorem permFive1_ne_one : permFive1 ≠ 1 := by unfold permFive1; decide

theorem permFive2_ne_one : permFive2 ≠ 1 := by unfold permFive2; decide

theorem sign_permFive1 : sign permFive1 = 1 := by
  unfold permFive1
  rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_mul, Equiv.Perm.sign_mul,
    sign_swap (show (3 : Fin 8) ≠ 4 by decide), sign_swap (show (4 : Fin 8) ≠ 5 by decide),
    sign_swap (show (5 : Fin 8) ≠ 6 by decide), sign_swap (show (6 : Fin 8) ≠ 7 by decide)]
  decide

theorem sign_permFive2 : sign permFive2 = 1 := by
  unfold permFive2
  rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_mul, Equiv.Perm.sign_mul,
    sign_swap (show (3 : Fin 8) ≠ 7 by decide), sign_swap (show (7 : Fin 8) ≠ 4 by decide),
    sign_swap (show (4 : Fin 8) ≠ 5 by decide), sign_swap (show (5 : Fin 8) ≠ 6 by decide)]
  decide

theorem permFive1_comm_permA3 : permFive1 * permA3 = permA3 * permFive1 := by
  unfold permFive1 permA3; decide

theorem permFive2_comm_permA3 : permFive2 * permA3 = permA3 * permFive2 := by
  unfold permFive2 permA3; decide

theorem cycleType_permFive12 : (permFive1 * permFive2).cycleType = {2, 2} := by
  refine cycleType_type22_of_card ?_ ?_
  · unfold permFive1 permFive2; decide
  · unfold permFive1 permFive2; decide

theorem permFive1_conj_decomp : ∀ i j i' j' : Fin 3,
    permFive1 * (permA3 ^ (i : ℕ) * permB3 ^ (j : ℕ)) * permFive1⁻¹ =
      permA3 ^ (i' : ℕ) * permB3 ^ (j' : ℕ) → j = 0 := by
  unfold permFive1 permA3 permB3; decide

theorem factorization_five_360 : (360 : ℕ).factorization 5 = 1 := by
  have h : (360 : ℕ) = 5 * 72 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_self (by norm_num : Nat.Prime 5)]
  have h72 : (72 : ℕ).factorization 5 = 0 := Nat.factorization_eq_zero_of_not_dvd (by norm_num)
  simp [h72]

namespace IsCover8

variable {E : Type*} [Group E] {ρ : E →* Perm (Fin 8)} {z : E}

theorem exists_lift_pow_eq_one_of_odd (h : IsCover8 ρ z) {p : Perm (Fin 8)} (hp : sign p = 1)
    {n : ℕ} (hn : Odd n) (hpn : p ^ n = 1) : ∃ c : E, ρ c = p ∧ c ^ n = 1 := by
  obtain ⟨d, hd⟩ := h.exists_lift hp
  have hdn : ρ (d ^ n) = 1 := by rw [map_pow, hd, hpn]
  rcases h.mem_ker_iff.mp hdn with h1 | h1
  · exact ⟨d, hd, h1⟩
  · refine ⟨d * z, by rw [h.rho_mul_z, hd], ?_⟩
    have hzn : z ^ n = z := by
      obtain ⟨k, rfl⟩ := hn
      rw [pow_succ, pow_mul, h.sq_eq_one, one_pow, one_mul]
    rw [Commute.mul_pow (h.mul_z_comm d) n, h1, hzn, h.z_mul_z]

end IsCover8

theorem mem_of_normalized_of_orderOf_prime {M : Type*} [Group M] [Finite M] {p : ℕ} [Fact p.Prime]
    {T N : Subgroup M} (hT : (Nat.card T).factorization p = 1) (hNT : N ≤ T)
    (hn : ∀ t ∈ T, ∀ w ∈ N, t * w * t⁻¹ ∈ N) {y r : M} (hy : y ∈ N) (hyo : orderOf y = p)
    (hrT : r ∈ T) (hro : orderOf r = p) : r ∈ N := by
  have hyT : y ∈ T := hNT hy
  have hyc : Nat.card (zpowers (⟨y, hyT⟩ : T)) = p ^ (Nat.card T).factorization p := by
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hyo, hT, pow_one]
  have hrc : Nat.card (zpowers (⟨r, hrT⟩ : T)) = p ^ (Nat.card T).factorization p := by
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hro, hT, pow_one]
  obtain ⟨g, hg⟩ := sylow_conj_mem (Sylow.ofCard _ hyc) (Sylow.ofCard _ hrc)
  have h1 : (⟨r, hrT⟩ : T) ∈ ((Sylow.ofCard _ hrc : Sylow p T) : Subgroup T) := by
    rw [Sylow.coe_ofCard]; exact Subgroup.mem_zpowers _
  have h2 := (hg _).mp h1
  rw [Sylow.coe_ofCard] at h2
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h2
  have h3 : (g : M)⁻¹ * r * g = y ^ k := by
    have := congrArg Subtype.val hk
    simpa using this.symm
  have h4 : (g : M)⁻¹ * r * g ∈ N := by rw [h3]; exact Subgroup.zpow_mem _ hy k
  have h5 := hn g g.2 _ h4
  have h6 : (g : M) * ((g : M)⁻¹ * r * g) * (g : M)⁻¹ = r := by group
  rwa [h6] at h5

theorem le_of_normalized_of_isPGroup {M : Type*} [Group M] [Finite M] {p : ℕ} [Fact p.Prime]
    {T N A : Subgroup M} (hA : Nat.card A = p ^ (Nat.card T).factorization p) (hAT : A ≤ T)
    (hNT : N ≤ T) (hn : ∀ t ∈ T, ∀ w ∈ N, t * w * t⁻¹ ∈ N) (hNp : IsPGroup p N) : N ≤ A := by
  have hN'n : (N.subgroupOf T).Normal :=
    ⟨fun n hn' g => Subgroup.mem_subgroupOf.mpr (hn g g.2 n (Subgroup.mem_subgroupOf.mp hn'))⟩
  have hN'p : IsPGroup p ↥(N.subgroupOf T) :=
    hNp.of_equiv (Subgroup.subgroupOfEquivOfLe hNT).symm
  have hA' : Nat.card (A.subgroupOf T) = p ^ (Nat.card T).factorization p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAT).toEquiv, hA]
  have hle := hN'p.le_sylow_of_normal (Sylow.ofCard _ hA')
  rw [Sylow.coe_ofCard] at hle
  intro w hw
  exact Subgroup.mem_subgroupOf.mp (hle (Subgroup.mem_subgroupOf.mpr hw : (⟨w, hNT hw⟩ : T) ∈
    N.subgroupOf T))

namespace Setup

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {S : Setup G} (c : Ctx S)

theorem exists_five_elements_aux : ∃ r₁ r₂ : S.H, S.ρ r₁ = permFive1 ∧ S.ρ r₂ = permFive2 ∧
    orderOf r₁ = 5 ∧ orderOf r₂ = 5 ∧ r₁ * c.a = c.a * r₁ ∧ r₂ * c.a = c.a * r₂ ∧
      (r₁ * r₂) ^ 2 = zIn S.z := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨r₁, hρ₁, h₁⟩ := S.cover.exists_lift_pow_eq_one_of_odd sign_permFive1
    (⟨2, by norm_num⟩ : Odd 5) permFive1_pow_five
  obtain ⟨r₂, hρ₂, h₂⟩ := S.cover.exists_lift_pow_eq_one_of_odd sign_permFive2
    (⟨2, by norm_num⟩ : Odd 5) permFive2_pow_five
  refine ⟨r₁, r₂, hρ₁, hρ₂, ?_, ?_, ?_, ?_, ?_⟩
  · exact orderOf_eq_prime h₁ (fun e => permFive1_ne_one (by rw [← hρ₁, e, map_one]))
  · exact orderOf_eq_prime h₂ (fun e => permFive2_ne_one (by rw [← hρ₂, e, map_one]))
  · exact S.cover.commute_of_cube c.ha3 (by rw [c.ha, hρ₁]; exact permFive1_comm_permA3)
  · exact S.cover.commute_of_cube c.ha3 (by rw [c.ha, hρ₂]; exact permFive2_comm_permA3)
  · exact S.cover.sq_eq_z_of_type22 (by rw [map_mul, hρ₁, hρ₂]; exact cycleType_permFive12)

theorem exists_five_elements : ∃ r₁ r₂ : S.H, orderOf r₁ = 5 ∧ orderOf r₂ = 5 ∧
    r₁ * c.a = c.a * r₁ ∧ r₂ * c.a = c.a * r₂ ∧ (r₁ * r₂) ^ 2 = zIn S.z := by
  obtain ⟨r₁, r₂, -, -, h1, h2, h3, h4, h5⟩ := c.exists_five_elements_aux
  exact ⟨r₁, r₂, h1, h2, h3, h4, h5⟩

theorem odd_normal_le_zpowers_a {W : Subgroup S.H} (hW : W ≤ centralizer ({c.a} : Set S.H))
    (hn : ∀ t ∈ centralizer ({c.a} : Set S.H), ∀ w ∈ W, t * w * t⁻¹ ∈ W)
    (hodd : Odd (Nat.card W)) : W ≤ zpowers c.a := by
  obtain ⟨r₁, r₂, hρ₁, -, ho₁, ho₂, hc₁, hc₂, hr₁₂⟩ := c.exists_five_elements_aux
  have hT360 : Nat.card (centralizer ({c.a} : Set S.H)) = 360 :=
    S.cover.card_centralizer_type3 c.ha3 (by rw [c.ha]; exact cycleType_permA3)
  have hr₁T : r₁ ∈ centralizer ({c.a} : Set S.H) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hc₁
  have hr₂T : r₂ ∈ centralizer ({c.a} : Set S.H) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hc₂
  have h5T : (Nat.card (centralizer ({c.a} : Set S.H))).factorization 5 = 1 := by
    rw [hT360]; exact factorization_five_360
  have h3T : (Nat.card (centralizer ({c.a} : Set S.H))).factorization 3 = 2 := by
    rw [hT360]; exact factorization_three_360
  have h5 : ¬ 5 ∣ Nat.card W := by
    intro h5
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := W) 5 h5
    have hyo : orderOf (y : S.H) = 5 := by rw [Subgroup.orderOf_coe]; exact hy
    have hr₁W : r₁ ∈ W := mem_of_normalized_of_orderOf_prime h5T hW hn y.2 hyo hr₁T ho₁
    have hr₂W : r₂ ∈ W := mem_of_normalized_of_orderOf_prime h5T hW hn y.2 hyo hr₂T ho₂
    have hzW : zIn S.z ∈ W := by
      rw [← hr₁₂]; exact W.pow_mem (W.mul_mem hr₁W hr₂W) 2
    have h2 : orderOf (⟨zIn S.z, hzW⟩ : W) ∣ Nat.card W := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, S.cover.orderOf_z] at h2
    obtain ⟨k, hk⟩ := hodd
    omega
  have h9 : Nat.card W ∣ 3 ^ 2 := by
    have hdvd : Nat.card W ∣ 360 := hT360 ▸ Subgroup.card_dvd_of_le hW
    have hc8 : Nat.Coprime (Nat.card W) 8 := by
      have := Nat.Coprime.pow_right 3 (Nat.coprime_two_right.mpr hodd)
      simpa using this
    have hc5 : Nat.Coprime (Nat.card W) 5 :=
      ((Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 5)).mpr h5).symm
    have h45 : Nat.card W ∣ 45 :=
      hc8.dvd_of_dvd_mul_left (by rw [show (8 : ℕ) * 45 = 360 by norm_num]; exact hdvd)
    exact hc5.dvd_of_dvd_mul_right (by rw [show (3 : ℕ) ^ 2 * 5 = 45 by norm_num]; exact h45)
  have hW3 : IsPGroup 3 W := by
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h9
    exact IsPGroup.of_card hm
  have hPcomm := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (G := c.P)
    (by rw [c.hP9]; norm_num)
  have hPT : c.P ≤ centralizer ({c.a} : Set S.H) := fun p hp => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := hPcomm.is_comm.comm ⟨p, hp⟩ ⟨c.a, c.haP⟩
    exact congrArg Subtype.val this
  have hWP : W ≤ c.P := le_of_normalized_of_isPGroup (p := 3)
    (by rw [c.hP9, h3T]; norm_num) hPT hW hn hW3
  intro w hw
  obtain ⟨i, j, hi, hj, rfl⟩ := c.P_decomp w (hWP hw)
  obtain ⟨i', j', hi', hj', he⟩ := c.P_decomp _ (hWP (hn r₁ hr₁T _ hw))
  have h2 := congrArg S.ρ he
  simp only [map_mul, map_pow, map_inv, c.ha, c.hb, hρ₁] at h2
  have hj0 : j = 0 := by
    have := permFive1_conj_decomp ⟨i, hi⟩ ⟨j, hj⟩ ⟨i', hi'⟩ ⟨j', hj'⟩ h2
    simpa using congrArg Fin.val this
  subst hj0
  rw [pow_zero, mul_one]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers c.a) i

end Ctx

end Setup

end CFSG.Sporadic.Recognition.JankoWong
