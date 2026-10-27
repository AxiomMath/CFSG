module

public import CFSG.Sporadic.Recognition.JankoWongLemma11
public import CFSG.Sporadic.Recognition.JankoWongLemma12
public import CFSG.Sporadic.Recognition.JankoWongKleinGen

public section

namespace CFSG.Sporadic.Recognition.JankoWong

open Equiv Equiv.Perm Subgroup CFSG.GH74 CFSG.GH74.GLS
open scoped Pointwise

theorem permD_conj_permA3 : permD * permA3 * permD⁻¹ = permB3⁻¹ := by
  unfold permD permA3 permB3; decide

theorem permD_conj_permB3 : permD * permB3 * permD⁻¹ = permA3⁻¹ := by
  unfold permD permA3 permB3; decide

theorem card_inf_centralizer_conj_of_normalizes {G : Type*} [Group G] {A : Subgroup G} {g : G}
    (hg : ∀ y ∈ A, g * y * g⁻¹ ∈ A) (hg' : ∀ y ∈ A, g⁻¹ * y * g ∈ A) (v : G) :
    Nat.card (A ⊓ centralizer ({g * v * g⁻¹} : Set G) : Subgroup G) =
      Nat.card (A ⊓ centralizer ({v} : Set G) : Subgroup G) := by
  refine Nat.card_congr
    { toFun := fun y => ⟨g⁻¹ * y.1 * g, ?_⟩
      invFun := fun y => ⟨g * y.1 * g⁻¹, ?_⟩
      left_inv := fun y => by apply Subtype.ext; show g * (g⁻¹ * y.1 * g) * g⁻¹ = y.1; group
      right_inv := fun y => by apply Subtype.ext; show g⁻¹ * (g * y.1 * g⁻¹) * g = y.1; group }
  · obtain ⟨y, hyA, hyv⟩ := y
    have hyv' := Subgroup.mem_centralizer_singleton_iff.mp hyv
    refine ⟨hg' y hyA, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    calc g⁻¹ * y * g * v = g⁻¹ * (y * (g * v * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * v * g⁻¹) * y) * g := by rw [hyv']
      _ = v * (g⁻¹ * y * g) := by group
  · obtain ⟨y, hyA, hyv⟩ := y
    have hyv' := Subgroup.mem_centralizer_singleton_iff.mp hyv
    refine ⟨hg y hyA, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    calc g * y * g⁻¹ * (g * v * g⁻¹) = g * (y * v) * g⁻¹ := by group
      _ = g * (v * y) * g⁻¹ := by rw [hyv']
      _ = (g * v * g⁻¹) * (g * y * g⁻¹) := by group

theorem mem_normalizer_of_normalizes {G : Type*} [Group G] {H : Subgroup G} {g : G}
    (hg : ∀ y ∈ H, g * y * g⁻¹ ∈ H) (hg' : ∀ y ∈ H, g⁻¹ * y * g ∈ H) :
    ∀ y ∈ Subgroup.normalizer (H : Set G), g * y * g⁻¹ ∈ Subgroup.normalizer (H : Set G) := by
  intro y hy
  rw [Subgroup.mem_normalizer_iff] at hy ⊢
  intro h
  have e : (g * y * g⁻¹) * h * (g * y * g⁻¹)⁻¹ = g * (y * (g⁻¹ * h * g) * y⁻¹) * g⁻¹ := by group
  rw [e]
  constructor
  · intro hh
    exact hg _ ((hy _).mp (hg' h hh))
  · intro hh
    have h1 : y * (g⁻¹ * h * g) * y⁻¹ ∈ H := by
      have := hg' _ hh
      have e2 : g⁻¹ * (g * (y * (g⁻¹ * h * g) * y⁻¹) * g⁻¹) * g = y * (g⁻¹ * h * g) * y⁻¹ := by
        group
      rwa [e2] at this
    have h2 : g⁻¹ * h * g ∈ H := (hy _).mpr h1
    have := hg _ h2
    have e3 : g * (g⁻¹ * h * g) * g⁻¹ = h := by group
    rwa [e3] at this

theorem commutative_of_card_center_ge {Q : Type*} [Group Q] [Finite Q] (hQ : Nat.card Q = 81)
    (hZ : 27 ≤ Nat.card (Subgroup.center Q)) : ∀ a b : Q, a * b = b * a := by
  have hdvd : Nat.card (Subgroup.center Q) ∣ 81 := hQ ▸ Subgroup.card_subgroup_dvd_card _
  have hmul := Subgroup.card_mul_index (Subgroup.center Q)
  rw [hQ] at hmul
  have hle : Nat.card (Subgroup.center Q) ≤ 81 := Nat.le_of_dvd (by norm_num) hdvd
  have hidx : (Subgroup.center Q).index = 1 ∨ (Subgroup.center Q).index = 3 := by
    have hpos : 0 < (Subgroup.center Q).index := by
      rcases Nat.eq_zero_or_pos (Subgroup.center Q).index with h | h
      · rw [h] at hmul; omega
      · exact h
    have : (Subgroup.center Q).index ≤ 3 := by
      by_contra hlt
      push Not at hlt
      nlinarith
    interval_cases h : (Subgroup.center Q).index
    · left; rfl
    · exfalso; omega
    · right; rfl
  have hcyc : IsCyclic (Q ⧸ Subgroup.center Q) := by
    have hcard : Nat.card (Q ⧸ Subgroup.center Q) = (Subgroup.center Q).index := rfl
    rcases hidx with h | h
    · have : Subsingleton (Q ⧸ Subgroup.center Q) :=
        (Nat.card_eq_one_iff_unique.mp (by rw [hcard, h])).1
      infer_instance
    · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact isCyclic_of_prime_card (p := 3) (by rw [hcard, h])
  have := MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
    (QuotientGroup.mk' (Subgroup.center Q)) (by rw [QuotientGroup.ker_mk'])
  exact this.is_comm.comm

theorem eq_nine_of_dvd_of_lt {n : ℕ} (h9 : 9 ∣ n) (h81 : n ∣ 81) (hlt : n < 27) : n = 9 := by
  have h0 : 0 < n := Nat.pos_of_dvd_of_pos h81 (by norm_num)
  interval_cases n <;> omega

theorem ge_27_of_dvd_of_ne {n : ℕ} (h9 : 9 ∣ n) (h81 : n ∣ 81) (hne : n ≠ 9) : 27 ≤ n := by
  by_contra hlt
  exact hne (eq_nine_of_dvd_of_lt h9 h81 (by omega))

theorem exists_three_element_normalizing {G : Type*} [Group G] [Finite G] {A : Subgroup G}
    (hA : IsPGroup 3 A) {m : ℕ} (hm : 3 ^ m ∣ Nat.card G) (hlt : Nat.card A < 3 ^ m) :
    ∃ Q : Subgroup G, IsPGroup 3 Q ∧ A ≤ Q ∧ ∃ g ∈ Q, g ∉ A ∧ g ∈ normalizer (A : Set G) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hQ⟩ := hA.exists_le_sylow
  have hQcard : 3 ^ m ≤ Nat.card Q := by
    rw [Q.card_eq_multiplicity]
    have hne : Nat.card G ≠ 0 := Nat.card_pos.ne'
    have h3 : m ≤ (Nat.card G).factorization 3 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hne).mp hm
    exact Nat.pow_le_pow_right (by norm_num) h3
  have hQ3 : IsPGroup 3 ↥(Q : Subgroup G) := Q.isPGroup'
  have : Group.IsNilpotent ↥(Q : Subgroup G) := hQ3.isNilpotent
  have hNC : NormalizerCondition ↥(Q : Subgroup G) := Group.normalizerCondition_of_isNilpotent
  set H₀ : Subgroup ↥(Q : Subgroup G) := A.subgroupOf Q with hH₀
  have hlt' : H₀ < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    have : Nat.card H₀ = Nat.card ↥(Q : Subgroup G) := by
      rw [htop]; exact Nat.card_congr (Subgroup.topEquiv).toEquiv
    rw [hH₀, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ).toEquiv] at this
    omega
  obtain ⟨g₀, hg₀N, hg₀H⟩ := IsConcreteLE.exists_of_lt (hNC H₀ hlt')
  refine ⟨Q, hQ3, hQ, (g₀ : G), g₀.2, fun hmem => hg₀H (Subgroup.mem_subgroupOf.mpr hmem), ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have hhQ : h ∈ (Q : Subgroup G) := hQ hh
    have := (Subgroup.mem_normalizer_iff.mp hg₀N ⟨h, hhQ⟩).mp (Subgroup.mem_subgroupOf.mpr hh)
    exact Subgroup.mem_subgroupOf.mp this
  · intro hh
    have hhQ : h ∈ (Q : Subgroup G) := by
      have h1 : (g₀ : G) * h * (g₀ : G)⁻¹ ∈ (Q : Subgroup G) := hQ hh
      have := (Q : Subgroup G).mul_mem ((Q : Subgroup G).mul_mem ((Q : Subgroup G).inv_mem g₀.2)
        h1) g₀.2
      simpa [mul_assoc] using this
    have := (Subgroup.mem_normalizer_iff.mp hg₀N ⟨h, hhQ⟩).mpr (Subgroup.mem_subgroupOf.mpr hh)
    exact Subgroup.mem_subgroupOf.mp this

theorem perm8_pow_three_of_pow_three_pow {σ : Perm (Fin 8)} {n : ℕ} (h : σ ^ (3 ^ n) = 1) :
    σ ^ 3 = 1 := by
  classical
  have hdvd : orderOf σ ∣ 3 ^ n := orderOf_dvd_of_pow_eq_one h
  have hall : ∀ c ∈ σ.cycleType, c ∣ 3 := by
    intro c hc
    have h1 : c ∣ orderOf σ := by
      rw [← Equiv.Perm.lcm_cycleType]
      exact Multiset.dvd_lcm hc
    have h2 : c ∣ 3 ^ n := h1.trans hdvd
    obtain ⟨k, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h2
    have h3 : 2 ≤ 3 ^ k := Equiv.Perm.two_le_of_mem_cycleType hc
    have h4 : 3 ^ k ≤ 8 := by
      have h5 := Multiset.le_sum_of_mem hc
      rw [Equiv.Perm.sum_cycleType] at h5
      calc 3 ^ k ≤ σ.support.card := h5
        _ ≤ Fintype.card (Fin 8) := Finset.card_le_univ _
        _ = 8 := by simp
    rcases k with _ | _ | k
    · norm_num at h3
    · exact dvd_refl _
    · exfalso
      have : 3 ^ 2 ≤ 3 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  have : orderOf σ ∣ 3 := by
    rw [← Equiv.Perm.lcm_cycleType]
    exact Multiset.lcm_dvd.mpr hall
  exact orderOf_dvd_iff_pow_eq_one.mp this


namespace Setup

variable {G : Type} [Group G] [Finite G]

theorem pow_three_of_pow_three_pow_H (S : Setup G) {y : S.H} {n : ℕ} (hy : y ^ (3 ^ n) = 1) :
    y ^ 3 = 1 := by
  have h1 : (S.ρ y) ^ 3 = 1 := by
    apply perm8_pow_three_of_pow_three_pow (n := n)
    rw [← map_pow, hy, map_one]
  rcases S.cover.mem_ker_iff.mp (show S.ρ (y ^ 3) = 1 by rw [map_pow]; exact h1) with e | e
  · exact e
  · exfalso
    rcases n with _ | n
    · have hy1 : y = 1 := by simpa using hy
      rw [hy1, one_pow] at e
      exact S.cover.ne_one e.symm
    · have hodd : Odd (3 ^ n) := Odd.pow (by decide)
      obtain ⟨k, hk⟩ := hodd
      have : y ^ (3 ^ (n + 1)) = zIn S.z := by
        rw [pow_succ', pow_mul, e, hk, pow_succ, pow_mul, S.zIn_sq, one_pow, one_mul]
      rw [this] at hy
      exact S.cover.ne_one hy

theorem pow_three_of_commute_involution (S : Setup G) {v y : G} (hv : v ^ 2 = 1) (hv1 : v ≠ 1)
    (hyv : y * v = v * y) {n : ℕ} (hn : y ^ (3 ^ n) = 1) : y ^ 3 = 1 := by
  obtain ⟨g, hg⟩ := isConj_iff.mp (S.oneClass S.z v S.order_z (orderOf_eq_prime hv hv1))
  have hmem := S.mem_H_of_commute hg hyv
  have hconj : ∀ m : ℕ, (g⁻¹ * y * g) ^ m = g⁻¹ * y ^ m * g := fun m => by
    simpa using conj_pow (a := g⁻¹) (b := y) (i := m)
  have h1 : (⟨g⁻¹ * y * g, hmem⟩ : S.H) ^ (3 ^ n) = 1 := by
    apply Subtype.ext
    show (g⁻¹ * y * g) ^ (3 ^ n) = 1
    rw [hconj, hn]; group
  have h2 := S.pow_three_of_pow_three_pow_H h1
  have h3 := congrArg Subtype.val h2
  have h4 : (g⁻¹ * y * g) ^ 3 = 1 := by simpa using h3
  rw [hconj] at h4
  calc y ^ 3 = g * (g⁻¹ * y ^ 3 * g) * g⁻¹ := by group
    _ = 1 := by rw [h4]; group

namespace Ctx

variable {S : Setup G} (c : Ctx S)

theorem d_conj_a : c.d * c.a * c.d⁻¹ = c.b⁻¹ := by
  have h3 : (c.d * c.a * c.d⁻¹) ^ 3 = 1 := by
    have : (c.d * c.a * c.d⁻¹) ^ 3 = c.d * c.a ^ 3 * c.d⁻¹ := by simp [pow_succ, mul_assoc]
    rw [this, c.ha3]; simp
  have h3' : (c.b⁻¹) ^ 3 = 1 := by rw [inv_pow, c.hb3, inv_one]
  refine S.cover.eq_of_cube_one h3 h3' ?_
  rw [map_mul, map_mul, map_inv, map_inv, c.hd, c.ha, c.hb]
  exact permD_conj_permA3

theorem d_conj_b : c.d * c.b * c.d⁻¹ = c.a⁻¹ := by
  have h3 : (c.d * c.b * c.d⁻¹) ^ 3 = 1 := by
    have : (c.d * c.b * c.d⁻¹) ^ 3 = c.d * c.b ^ 3 * c.d⁻¹ := by simp [pow_succ, mul_assoc]
    rw [this, c.hb3]; simp
  have h3' : (c.a⁻¹) ^ 3 = 1 := by rw [inv_pow, c.ha3, inv_one]
  refine S.cover.eq_of_cube_one h3 h3' ?_
  rw [map_mul, map_mul, map_inv, map_inv, c.hd, c.ha, c.hb]
  exact permD_conj_permB3

theorem d_normalizes_P : ∀ p ∈ c.P, c.d * p * c.d⁻¹ ∈ c.P := by
  intro p hp
  obtain ⟨i, j, -, -, rfl⟩ := Ctx.P_decomp c p hp
  have : c.d * (c.a ^ i * c.b ^ j) * c.d⁻¹ = (c.b⁻¹) ^ i * (c.a⁻¹) ^ j := by
    calc c.d * (c.a ^ i * c.b ^ j) * c.d⁻¹
        = (c.d * c.a * c.d⁻¹) ^ i * (c.d * c.b * c.d⁻¹) ^ j := by
          rw [conj_pow, conj_pow]; group
      _ = (c.b⁻¹) ^ i * (c.a⁻¹) ^ j := by rw [c.d_conj_a, c.d_conj_b]
  rw [this]
  exact c.P.mul_mem (c.P.pow_mem (c.P.inv_mem c.hbP) i) (c.P.pow_mem (c.P.inv_mem c.haP) j)

theorem card_CO_z_t (h81 : Nat.card c.OG = 81) :
    Nat.card (c.CO S.z) = 9 ∧ Nat.card (c.CO (c.t : G)) = 9 := by
  have hmul := c.card_OG_mul_nine'
  rw [h81] at hmul
  rcases eq_three_or_nine c.card_CO_z.1 c.card_CO_z.2 with ha | ha <;>
    rcases eq_three_or_nine c.card_CO_t.1 c.card_CO_t.2 with hb | hb <;>
    rw [ha, hb] at hmul <;> omega

@[expose] def PG : Subgroup G := c.P.map S.H.subtype

theorem card_PG : Nat.card c.PG = 9 := by
  rw [PG, Subgroup.card_map_of_injective S.H.subtype_injective, c.hP9]

theorem CO_z_eq_PG (h81 : Nat.card c.OG = 81) : c.CO S.z = c.PG := by
  have hle : c.CO S.z ≤ c.PG := by
    rintro y ⟨hyO, hyz⟩
    have hz := Subgroup.mem_centralizer_singleton_iff.mp hyz
    have hyC : y ∈ c.Cg := c.OG_le_Cg hyO
    have hys : y * c.s = c.s * y := Subgroup.mem_centralizer_singleton_iff.mp hyC
    have hyH : y ∈ S.H := Subgroup.mem_centralizer_singleton_iff.mpr hz
    have hyHx : (⟨y, hyH⟩ : S.H) * c.x = c.x * (⟨y, hyH⟩ : S.H) := Subtype.ext hys
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (⟨y, hyH⟩ : S.H) ^ (3 ^ n) = 1 := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.mp c.isPGroup_three_OG ⟨y, hyO⟩
      refine ⟨n, ?_⟩
      have h1 : (⟨y, hyO⟩ : c.OG) ^ (3 ^ n) = 1 := by rw [← hn]; exact pow_orderOf_eq_one _
      apply Subtype.ext
      have := congrArg (fun w : c.OG => (w : G)) h1
      simpa using this
    exact ⟨_, c.mem_P_of_three_power hyHx hn, rfl⟩
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [(c.card_CO_z_t h81).1, c.card_PG])

theorem PG_le_OG (h81 : Nat.card c.OG = 81) : c.PG ≤ c.OG := by
  rw [← c.CO_z_eq_PG h81]; exact inf_le_left

theorem PG_normalizes_z : (∀ y ∈ c.PG, S.z * y * S.z⁻¹ ∈ c.PG) ∧
    (∀ y ∈ c.PG, S.z⁻¹ * y * S.z ∈ c.PG) := by
  have hcomm : ∀ y ∈ c.PG, S.z * y = y * S.z := by
    rintro _ ⟨p, hp, rfl⟩
    exact (Subgroup.mem_centralizer_singleton_iff.mp p.2).symm
  refine ⟨fun y hy => ?_, fun y hy => ?_⟩
  · rw [hcomm y hy]; simpa using hy
  · have h1 := hcomm y hy
    have e : S.z⁻¹ * y * S.z = y := by
      calc S.z⁻¹ * y * S.z = S.z⁻¹ * (y * S.z) := by group
        _ = S.z⁻¹ * (S.z * y) := by rw [h1]
        _ = y := by group
    rw [e]; exact hy

theorem PG_normalizes_of_involution {g : G} (hgsq : g * g = 1)
    (hg : ∀ p ∈ c.P, ∃ p' ∈ c.P, ((p' : S.H) : G) = g * (p : G) * g⁻¹) :
    (∀ y ∈ c.PG, g * y * g⁻¹ ∈ c.PG) ∧ (∀ y ∈ c.PG, g⁻¹ * y * g ∈ c.PG) := by
  have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hgsq
  have h1 : ∀ y ∈ c.PG, g * y * g⁻¹ ∈ c.PG := by
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨p', hp', hp'e⟩ := hg p hp
    exact ⟨p', hp', hp'e⟩
  exact ⟨h1, fun y hy => by
    have h := h1 y hy
    rw [hginv] at h ⊢
    exact h⟩

theorem PG_normalizes_t : (∀ y ∈ c.PG, (c.t : G) * y * (c.t : G)⁻¹ ∈ c.PG) ∧
    (∀ y ∈ c.PG, (c.t : G)⁻¹ * y * (c.t : G) ∈ c.PG) :=
  c.PG_normalizes_of_involution c.tG_sq (fun p hp => ⟨c.t * p * c.t⁻¹, c.t_normalizes_P p hp, rfl⟩)

theorem PG_normalizes_d : (∀ y ∈ c.PG, (c.d : G) * y * (c.d : G)⁻¹ ∈ c.PG) ∧
    (∀ y ∈ c.PG, (c.d : G)⁻¹ * y * (c.d : G) ∈ c.PG) :=
  c.PG_normalizes_of_involution c.dG_sq (fun p hp => ⟨c.d * p * c.d⁻¹, c.d_normalizes_P p hp, rfl⟩)

@[expose] def NNP : Subgroup G := c.OG ⊓ normalizer (c.PG : Set G)

theorem NNP_norm_of {g : G} (hgNg : g ∈ c.Ng)
    (hn : (∀ y ∈ c.PG, g * y * g⁻¹ ∈ c.PG) ∧ (∀ y ∈ c.PG, g⁻¹ * y * g ∈ c.PG)) :
    (∀ y ∈ c.NNP, g * y * g⁻¹ ∈ c.NNP) ∧ (∀ y ∈ c.NNP, g⁻¹ * y * g ∈ c.NNP) := by
  refine ⟨fun y hy => ⟨c.OG_normalized g hgNg y hy.1,
    mem_normalizer_of_normalizes hn.1 hn.2 y hy.2⟩, fun y hy => ⟨?_, ?_⟩⟩
  · have := c.OG_normalized g⁻¹ ((c.Ng).inv_mem hgNg) y hy.1
    simpa using this
  · have := mem_normalizer_of_normalizes (g := g⁻¹) (H := c.PG) (by simpa using hn.2)
      (by simpa using hn.1) y hy.2
    simpa using this

theorem PG_lt_NNP (h81 : Nat.card c.OG = 81) : c.PG < c.NNP := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPGO := c.PG_le_OG h81
  have hnil : Group.IsNilpotent ↥c.OG := c.isPGroup_three_OG.isNilpotent
  have hNC : NormalizerCondition ↥c.OG := Group.normalizerCondition_of_isNilpotent
  set H₀ : Subgroup ↥c.OG := c.PG.subgroupOf c.OG with hH₀
  have hlt : H₀ < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    have : Nat.card H₀ = Nat.card ↥c.OG := by
      rw [htop]; exact Nat.card_congr (Subgroup.topEquiv).toEquiv
    rw [hH₀, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPGO).toEquiv, c.card_PG, h81] at this
    omega
  obtain ⟨g₀, hg₀N, hg₀H⟩ := IsConcreteLE.exists_of_lt (hNC H₀ hlt)
  have hgPG : (g₀ : G) ∉ c.PG := fun hmem => hg₀H (Subgroup.mem_subgroupOf.mpr hmem)
  have hgN : (g₀ : G) ∈ normalizer (c.PG : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have hhO : h ∈ c.OG := hPGO hh
      have := (Subgroup.mem_normalizer_iff.mp hg₀N ⟨h, hhO⟩).mp (Subgroup.mem_subgroupOf.mpr hh)
      exact Subgroup.mem_subgroupOf.mp this
    · intro hh
      have hhO : h ∈ c.OG := by
        have h1 : (g₀ : G) * h * (g₀ : G)⁻¹ ∈ c.OG := hPGO hh
        have := c.OG.mul_mem (c.OG.mul_mem (c.OG.inv_mem g₀.2) h1) g₀.2
        simpa [mul_assoc] using this
      have := (Subgroup.mem_normalizer_iff.mp hg₀N ⟨h, hhO⟩).mpr (Subgroup.mem_subgroupOf.mpr hh)
      exact Subgroup.mem_subgroupOf.mp this
  have hle : c.PG ≤ c.NNP := le_inf hPGO Subgroup.le_normalizer
  refine lt_of_le_of_ne hle ?_
  intro heq
  apply hgPG
  rw [heq]
  exact ⟨g₀.2, hgN⟩

theorem s_mem_PG : c.s ∈ c.PG := ⟨c.x, c.P.mul_mem c.haP c.hbP, rfl⟩

theorem card_NNP (h81 : Nat.card c.OG = 81) : Nat.card c.NNP = 81 := by
  have hz2 := z_sq (S := S)
  have ht2 := c.tG_sq'
  have hPGO := c.PG_le_OG h81
  have hNNPO : c.NNP ≤ c.OG := inf_le_left
  have hNp : IsPGroup 3 c.NNP := c.isPGroup_three_OG.to_le hNNPO
  have hzn := c.NNP_norm_of (c.cg_le_ng c.z_mem_cg) c.PG_normalizes_z
  have htn := c.NNP_norm_of (c.cg_le_ng c.tC_mem) c.PG_normalizes_t
  have hdn := c.NNP_norm_of c.d_mem_ng c.PG_normalizes_d
  have hPGNNP : c.PG ≤ c.NNP := le_inf hPGO Subgroup.le_normalizer
  have hsNNP : zpowers c.s ≤ c.NNP := (Subgroup.zpowers_le.mpr c.s_mem_PG).trans hPGNNP
  have hscomm : ∀ y ∈ c.NNP, c.s * y = y * c.s := fun y hy =>
    (Subgroup.mem_centralizer_singleton_iff.mp (c.OG_le_Cg (hNNPO hy))).symm
  have h := card_mul_sq_eq_prod_centralizers_of_klein (C := G) (A := c.NNP) (Z := zpowers c.s)
    hNp hz2 ht2 c.t_comm_z.symm hzn.1 htn.1 hsNNP
    (fun z' hz' y hy => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz'
      exact (Commute.zpow_left (show Commute c.s y from hscomm y hy) k).eq)
    (fun z' hz' => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz'
      exact ⟨(Commute.zpow_right (show Commute S.z c.s from c.z_comm_s) k).eq,
        (Commute.zpow_right (show Commute (c.t : G) c.s from c.t_comm_s) k).eq⟩)
    (fun y hy h1 h2 => c.mem_zpowers_s_of_commute (hNNPO hy) h1.symm h2.symm)
  rw [Nat.card_zpowers, c.orderOf_s] at h
  have hCAz : c.NNP ⊓ centralizer ({S.z} : Set G) = c.PG := by
    refine le_antisymm (fun y hy => ?_) (le_inf hPGNNP ?_)
    · rw [← c.CO_z_eq_PG h81]; exact ⟨hNNPO hy.1, hy.2⟩
    · rintro _ ⟨p, hp, rfl⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp p.2)
  have hconj := card_inf_centralizer_conj_of_normalizes (A := c.NNP) hdn.1 hdn.2 (c.t : G)
  rw [c.d_conj_t] at hconj
  have hb3 : 3 ∣ Nat.card ↥(c.NNP ⊓ centralizer ({(c.t : G)} : Set G)) := by
    have hz : zpowers c.s ≤ c.NNP ⊓ centralizer ({(c.t : G)} : Set G) := by
      rw [Subgroup.zpowers_le]
      exact ⟨hsNNP (Subgroup.mem_zpowers c.s),
        Subgroup.mem_centralizer_singleton_iff.mpr c.t_comm_s.symm⟩
    have := Subgroup.card_dvd_of_le hz
    rwa [Nat.card_zpowers, c.orderOf_s] at this
  have hb9 : Nat.card ↥(c.NNP ⊓ centralizer ({(c.t : G)} : Set G)) ∣ 9 := by
    have hle : c.NNP ⊓ centralizer ({(c.t : G)} : Set G) ≤ c.CO (c.t : G) :=
      inf_le_inf hNNPO le_rfl
    have := Subgroup.card_dvd_of_le hle
    rwa [(c.card_CO_z_t h81).2] at this
  have hgt : 9 < Nat.card c.NNP := by
    have hlt := c.PG_lt_NNP h81
    have h1 : Nat.card c.PG ≤ Nat.card c.NNP := Subgroup.card_le_of_le hPGNNP
    rw [c.card_PG] at h1
    rcases Nat.eq_or_lt_of_le h1 with h2 | h2
    · exfalso
      have : c.PG = c.NNP := Subgroup.eq_of_le_of_card_ge hPGNNP (by rw [c.card_PG]; omega)
      rw [this] at hlt
      exact lt_irrefl _ hlt
    · exact h2
  rw [hCAz, c.card_PG, hconj] at h
  rcases eq_three_or_nine hb3 hb9 with hb | hb
  · rw [hb] at h; omega
  · rw [hb] at h; omega

theorem OG_le_normalizer_PG (h81 : Nat.card c.OG = 81) :
    c.OG ≤ normalizer (c.PG : Set G) := by
  have heq : c.NNP = c.OG :=
    Subgroup.eq_of_le_of_card_ge (inf_le_left : c.NNP ≤ c.OG) (by rw [c.card_NNP h81, h81])
  intro y hy
  have : y ∈ c.NNP := by rw [heq]; exact hy
  exact this.2

theorem three_power_of_mem_OG {y : G} (hy : y ∈ c.OG) : ∃ n : ℕ, y ^ (3 ^ n) = 1 := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.mp c.isPGroup_three_OG ⟨y, hy⟩
  refine ⟨n, ?_⟩
  have h1 : (⟨y, hy⟩ : c.OG) ^ (3 ^ n) = 1 := by rw [← hn]; exact pow_orderOf_eq_one _
  simpa using congrArg (fun w : c.OG => (w : G)) h1

theorem commute_ab_of_normalizes_PG {g : G} (hg3 : ∃ n : ℕ, g ^ (3 ^ n) = 1)
    (hgN : g ∈ normalizer (c.PG : Set G)) :
    g * (c.a : G) = (c.a : G) * g ∧ g * (c.b : G) = (c.b : G) * g := by
  have hnorm : ∀ p ∈ c.P, ∃ p' ∈ c.P, ((p' : S.H) : G) = g * (p : G) * g⁻¹ := by
    intro p hp
    have hpPG : ((p : S.H) : G) ∈ c.PG := ⟨p, hp, rfl⟩
    have := (Subgroup.mem_normalizer_iff.mp hgN _).mp hpPG
    obtain ⟨p', hp', hp'e⟩ := this
    exact ⟨p', hp', hp'e⟩
  have hfix := c.conj_fixes_Xs hg3 (fun x hx => c.conj_mem_Xs hnorm hx)
  have ha := hfix (c.a : G) (Or.inl rfl)
  have hb := hfix (c.b : G) (Or.inr (Or.inr (Or.inl rfl)))
  constructor
  · calc g * (c.a : G) = (g * (c.a : G) * g⁻¹) * g := by group
      _ = (c.a : G) * g := by rw [ha]
  · calc g * (c.b : G) = (g * (c.b : G) * g⁻¹) * g := by group
      _ = (c.b : G) * g := by rw [hb]

theorem OG_centralizes_a (h81 : Nat.card c.OG = 81) :
    ∀ g ∈ c.OG, g * (c.a : G) = (c.a : G) * g ∧ g * (c.b : G) = (c.b : G) * g := fun _ hg =>
  c.commute_ab_of_normalizes_PG (c.three_power_of_mem_OG hg) (c.OG_le_normalizer_PG h81 hg)

theorem OG_comm_PG (h81 : Nat.card c.OG = 81) : ∀ y ∈ c.PG, ∀ w ∈ c.OG, w * y = y * w := by
  rintro _ ⟨p, hp, rfl⟩ w hw
  obtain ⟨i, j, -, -, rfl⟩ := c.P_decomp p hp
  obtain ⟨ha, hb⟩ := c.OG_centralizes_a h81 w hw
  have hwa : Commute w (c.a : G) := ha
  have hwb : Commute w (c.b : G) := hb
  have := ((hwa.pow_right i).mul_right (hwb.pow_right j)).eq
  simpa using this

@[expose] def ZG : Subgroup G := (Subgroup.center ↥c.OG).map c.OG.subtype

theorem mem_ZG_iff {y : G} : y ∈ c.ZG ↔ y ∈ c.OG ∧ ∀ w ∈ c.OG, w * y = y * w := by
  constructor
  · rintro ⟨y', hy', rfl⟩
    refine ⟨y'.2, fun w hw => ?_⟩
    have := Subgroup.mem_center_iff.mp hy' ⟨w, hw⟩
    exact congrArg Subtype.val this
  · rintro ⟨hy, hc⟩
    refine ⟨⟨y, hy⟩, Subgroup.mem_center_iff.mpr (fun w => ?_), rfl⟩
    exact Subtype.ext (hc w w.2)

theorem card_ZG : Nat.card c.ZG = Nat.card (Subgroup.center ↥c.OG) :=
  Subgroup.card_map_of_injective c.OG.subtype_injective

theorem ZG_le_OG : c.ZG ≤ c.OG := fun _ hy => (c.mem_ZG_iff.mp hy).1

theorem PG_le_ZG (h81 : Nat.card c.OG = 81) : c.PG ≤ c.ZG := fun y hy =>
  c.mem_ZG_iff.mpr ⟨c.PG_le_OG h81 hy, c.OG_comm_PG h81 y hy⟩

theorem card_ZG_dvd (h81 : Nat.card c.OG = 81) : Nat.card c.ZG ∣ 81 :=
  h81 ▸ Subgroup.card_dvd_of_le c.ZG_le_OG

theorem nine_dvd_card_ZG (h81 : Nat.card c.OG = 81) : 9 ∣ Nat.card c.ZG := by
  rw [← c.card_PG]; exact Subgroup.card_dvd_of_le (c.PG_le_ZG h81)

theorem OG_comm_of_card_ZG (h81 : Nat.card c.OG = 81) (h27 : 27 ≤ Nat.card c.ZG) :
    ∀ y ∈ c.OG, ∀ w ∈ c.OG, y * w = w * y := by
  have hQ : Nat.card ↥c.OG = 81 := h81
  have := commutative_of_card_center_ge hQ (by rw [← c.card_ZG]; exact h27)
  intro y hy w hw
  exact congrArg Subtype.val (this ⟨y, hy⟩ ⟨w, hw⟩)

theorem mem_normalizer_ZG {g : G} (hg : g ∈ normalizer (c.OG : Set G)) :
    g ∈ normalizer (c.ZG : Set G) := by
  have hfwd : ∀ g : G, g ∈ normalizer (c.OG : Set G) → ∀ y ∈ c.ZG, g * y * g⁻¹ ∈ c.ZG := by
    intro g hg y hy
    obtain ⟨hyO, hyc⟩ := c.mem_ZG_iff.mp hy
    have hginv : g⁻¹ ∈ normalizer (c.OG : Set G) := (normalizer (c.OG : Set G)).inv_mem hg
    refine c.mem_ZG_iff.mpr ⟨(Subgroup.mem_normalizer_iff.mp hg y).mp hyO, fun w hw => ?_⟩
    have hw' : g⁻¹ * w * g ∈ c.OG := by
      have := (Subgroup.mem_normalizer_iff.mp hginv w).mp hw
      simpa using this
    have h1 := hyc _ hw'
    calc w * (g * y * g⁻¹) = g * ((g⁻¹ * w * g) * y) * g⁻¹ := by group
      _ = g * (y * (g⁻¹ * w * g)) * g⁻¹ := by rw [h1]
      _ = g * y * g⁻¹ * w := by group
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact hfwd g hg h
  · intro hh
    have := hfwd g⁻¹ ((normalizer (c.OG : Set G)).inv_mem hg) _ hh
    have e : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
    rwa [e] at this

theorem t_not_comm_a : (c.a : G) * (c.t : G) ≠ (c.t : G) * (c.a : G) := by
  intro h
  have h1 : c.a * c.t = c.t * c.a := Subtype.ext h
  have h2 := congrArg S.ρ h1
  rw [map_mul, map_mul, c.ha, c.ht] at h2
  exact permT_not_comm_permA3 h2.symm

theorem exists_Ng_conj_z_t (hN : ¬ CFSG.HasNormalPComplement 2 ↥c.Cg) :
    ∃ g ∈ c.Ng, g * S.z * g⁻¹ = (c.t : G) := by
  obtain ⟨x, hx⟩ := c.exists_conj_z_of_not_hasNormalPComplement hN
  rcases hx with hx | hx
  · exact ⟨x, c.cg_le_ng x.2, hx⟩
  · refine ⟨(c.d : G) * x, c.Ng.mul_mem c.d_mem_ng (c.cg_le_ng x.2), ?_⟩
    have h1 : (c.d : G) * S.z * (c.d : G)⁻¹ = S.z := by
      calc (c.d : G) * S.z * (c.d : G)⁻¹ = S.z * (c.d : G) * (c.d : G)⁻¹ := by rw [c.d_comm_z]
        _ = S.z := by group
    have hz : S.z * S.z = 1 := by rw [← pow_two]; exact z_sq (S := S)
    calc (c.d : G) * x * S.z * ((c.d : G) * x)⁻¹
        = (c.d : G) * ((x : G) * S.z * (x : G)⁻¹) * (c.d : G)⁻¹ := by group
      _ = (c.d : G) * (S.z * (c.t : G)) * (c.d : G)⁻¹ := by rw [hx]
      _ = ((c.d : G) * S.z * (c.d : G)⁻¹) * ((c.d : G) * (c.t : G) * (c.d : G)⁻¹) := by group
      _ = S.z * (S.z * (c.t : G)) := by rw [h1, c.d_conj_t]
      _ = (S.z * S.z) * (c.t : G) := by group
      _ = (c.t : G) := by rw [hz, one_mul]

theorem CO_t_le_ZG (h81 : Nat.card c.OG = 81) {g : G} (hg : g ∈ c.Ng)
    (hgt : g * S.z * g⁻¹ = (c.t : G)) : c.CO (c.t : G) ≤ c.ZG := by
  rintro y ⟨hyO, hyt⟩
  have hyt' := Subgroup.mem_centralizer_singleton_iff.mp hyt
  have hginv : g⁻¹ ∈ c.Ng := c.Ng.inv_mem hg
  have hy' : g⁻¹ * y * g ∈ c.PG := by
    rw [← c.CO_z_eq_PG h81]
    refine ⟨?_, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    · have := c.OG_normalized g⁻¹ hginv y hyO
      simpa using this
    · have ht : g⁻¹ * (c.t : G) * g = S.z := by rw [← hgt]; group
      calc g⁻¹ * y * g * S.z = g⁻¹ * y * (g * S.z * g⁻¹) * g := by group
        _ = g⁻¹ * (y * (c.t : G)) * g := by rw [hgt]; group
        _ = g⁻¹ * ((c.t : G) * y) * g := by rw [hyt']
        _ = S.z * (g⁻¹ * y * g) := by rw [← ht]; group
  refine c.mem_ZG_iff.mpr ⟨hyO, fun w hw => ?_⟩
  have hw' : g⁻¹ * w * g ∈ c.OG := by
    have := c.OG_normalized g⁻¹ hginv w hw
    simpa using this
  have hcomm := c.OG_comm_PG h81 _ hy' _ hw'
  calc w * y = g * ((g⁻¹ * w * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * y * g) * (g⁻¹ * w * g)) * g⁻¹ := by rw [hcomm]
    _ = y * w := by group

theorem OG_comm_of_not_hasNormalPComplement (h81 : Nat.card c.OG = 81)
    (hN : ¬ CFSG.HasNormalPComplement 2 ↥c.Cg) : ∀ y ∈ c.OG, ∀ w ∈ c.OG, y * w = w * y := by
  obtain ⟨g, hg, hgt⟩ := c.exists_Ng_conj_z_t hN
  have hCt := c.CO_t_le_ZG h81 hg hgt
  have hPZ := c.PG_le_ZG h81
  refine c.OG_comm_of_card_ZG h81 (ge_27_of_dvd_of_ne (c.nine_dvd_card_ZG h81)
    (c.card_ZG_dvd h81) (fun h9 => ?_))
  have hPZeq : c.PG = c.ZG := Subgroup.eq_of_le_of_card_ge hPZ (by rw [h9, c.card_PG])
  have hCtP : c.CO (c.t : G) = c.PG := by
    refine Subgroup.eq_of_le_of_card_ge (hPZeq ▸ hCt) ?_
    rw [(c.card_CO_z_t h81).2, c.card_PG]
  have haP : (c.a : G) ∈ c.PG := ⟨c.a, c.haP, rfl⟩
  rw [← hCtP] at haP
  exact c.t_not_comm_a (Subgroup.mem_centralizer_singleton_iff.mp haP.2)

theorem OG_comm_of_hasNormalPComplement
    (h81 : Nat.card c.OG = 81) (hN : CFSG.HasNormalPComplement 2 ↥c.Cg) :
    ∀ y ∈ c.OG, ∀ w ∈ c.OG, y * w = w * y := by
  by_contra hnc
  have hZlt : Nat.card c.ZG < 27 := by
    by_contra hge
    push Not at hge
    exact hnc (c.OG_comm_of_card_ZG h81 hge)
  have hZ9 := eq_nine_of_dvd_of_lt (c.nine_dvd_card_ZG h81) (c.card_ZG_dvd h81) hZlt
  have hZPG : c.PG = c.ZG :=
    Subgroup.eq_of_le_of_card_ge (c.PG_le_ZG h81) (by rw [hZ9, c.card_PG])
  obtain ⟨Q, hQ, hOQ, g, hgQ, hgO, hgN⟩ := exists_three_element_normalizing
    c.isPGroup_three_OG (m := 6) S.three_pow_six_dvd_card (by rw [h81]; norm_num)
  have hgZ : g ∈ normalizer (c.PG : Set G) := by
    rw [hZPG]; exact c.mem_normalizer_ZG hgN
  have hg3 : ∃ n : ℕ, g ^ (3 ^ n) = 1 := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.mp hQ ⟨g, hgQ⟩
    refine ⟨n, ?_⟩
    have h1 : (⟨g, hgQ⟩ : Q) ^ (3 ^ n) = 1 := by rw [← hn]; exact pow_orderOf_eq_one _
    simpa using congrArg (fun w : Q => (w : G)) h1
  obtain ⟨hga, hgb⟩ := c.commute_ab_of_normalizes_PG hg3 hgZ
  have hgC : g ∈ c.Cg := by
    rw [c.mem_cg_iff]
    show g * ((c.a * c.b : S.H) : G) * g⁻¹ = ((c.a * c.b : S.H) : G)
    calc g * ((c.a * c.b : S.H) : G) * g⁻¹ = g * (c.a : G) * (c.b : G) * g⁻¹ := by
          simp [mul_assoc]
      _ = (c.a : G) * g * (c.b : G) * g⁻¹ := by rw [hga]
      _ = (c.a : G) * (g * (c.b : G)) * g⁻¹ := by group
      _ = (c.a : G) * ((c.b : G) * g) * g⁻¹ := by rw [hgb]
      _ = ((c.a * c.b : S.H) : G) := by simp [mul_assoc]
  set R : Subgroup G := Subgroup.closure ((c.OG : Set G) ∪ {g}) with hR
  have hRQ : R ≤ Q := by
    rw [hR, Subgroup.closure_le]
    rintro y (hy | hy)
    · exact hOQ hy
    · rw [Set.mem_singleton_iff.mp hy]; exact hgQ
  have hRC : R ≤ c.Cg := by
    rw [hR, Subgroup.closure_le]
    rintro y (hy | hy)
    · exact c.OG_le_Cg hy
    · rw [Set.mem_singleton_iff.mp hy]; exact hgC
  have hRp : IsPGroup 3 R := hQ.to_le hRQ
  have hOR : c.OG ≤ R := fun y hy => Subgroup.subset_closure (Or.inl hy)
  have hgR : g ∈ R := Subgroup.subset_closure (Or.inr rfl)
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hRp
  have h81R : 81 ∣ Nat.card R := by rw [← h81]; exact Subgroup.card_dvd_of_le hOR
  have hne : Nat.card R ≠ 81 := fun e => hgO (by
    have heq : c.OG = R := Subgroup.eq_of_le_of_card_ge hOR (by rw [e, h81])
    rw [heq]; exact hgR)
  have h243 : 243 ∣ Nat.card R := by
    rw [hm] at h81R hne ⊢
    have hm4 : 4 ≤ m := by
      by_contra hlt
      push Not at hlt
      interval_cases m <;> norm_num at h81R
    have hm5 : 5 ≤ m := by
      by_contra hlt
      push Not at hlt
      have : m = 4 := by omega
      rw [this] at hne
      norm_num at hne
    calc 243 = 3 ^ 5 := by norm_num
      _ ∣ 3 ^ m := pow_dvd_pow 3 hm5
  have h243C : 243 ∣ Nat.card c.Cg := h243.trans (Subgroup.card_dvd_of_le hRC)
  obtain ⟨XG, hXGO, -, hCcard, -⟩ := c.exists_odd_complement hN
  have h243X : 243 ∣ Nat.card XG := by
    rw [hCcard] at h243C
    exact (show Nat.Coprime 243 4 by norm_num).dvd_of_dvd_mul_left h243C
  have hXG81 : Nat.card XG ∣ 81 := h81 ▸ Subgroup.card_dvd_of_le hXGO
  have h1 := Nat.le_of_dvd (by norm_num) hXG81
  have h2 := Nat.le_of_dvd Nat.card_pos h243X
  omega

theorem OG_comm :
    ∀ y ∈ c.OG, ∀ w ∈ c.OG, y * w = w * y := by
  have h81 := c.card_OG_eq_81
  by_cases hN : CFSG.HasNormalPComplement 2 ↥c.Cg
  · exact c.OG_comm_of_hasNormalPComplement h81 hN
  · exact c.OG_comm_of_not_hasNormalPComplement h81 hN

theorem OG_pow_three :
    ∀ y ∈ c.OG, y ^ 3 = 1 := by
  have hz2 := z_sq (S := S)
  have ht2 := c.tG_sq'
  have hzt : Commute S.z (c.t : G) := c.t_comm_z.symm
  have hzt2 : (S.z * (c.t : G)) ^ 2 = 1 := by
    rw [hzt.mul_pow, hz2, ht2, one_mul]
  have hzt1 : S.z * (c.t : G) ≠ 1 := fun e => by
    have h1 : (c.t : G) = S.z⁻¹ := eq_inv_of_mul_eq_one_right e
    have h2 : S.z⁻¹ = S.z := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hz2)
    exact c.t_ne_z (Subtype.ext (h1.trans h2))
  have hcube : ∀ {v : G}, v ^ 2 = 1 → v ≠ 1 → ∀ y ∈ c.OG ⊓ centralizer ({v} : Set G),
      y ^ 3 = 1 := by
    intro v hv hv1 y hy
    obtain ⟨n, hn⟩ := c.three_power_of_mem_OG hy.1
    exact S.pow_three_of_commute_involution hv hv1
      (Subgroup.mem_centralizer_singleton_iff.mp hy.2) hn
  exact pow_three_eq_one_of_klein_comm c.isPGroup_three_OG c.OG_comm hz2 ht2 hzt.eq
    (fun y hy => c.OG_normalized S.z (c.cg_le_ng c.z_mem_cg) y hy)
    (fun y hy => c.OG_normalized (c.t : G) (c.cg_le_ng c.tC_mem) y hy)
    (hcube hz2 (z_ne_one' (S := S))) (hcube ht2 c.tG_ne_one) (hcube hzt2 hzt1)

theorem centralizer_OG_le :
    ∀ g : G, (∀ y ∈ c.OG, y * g = g * y) → g ∈ c.OG := by
  have h81 := c.card_OG_eq_81
  intro g hg
  set K : Subgroup G := centralizer (c.OG : Set G) with hK
  have hgK : g ∈ K := Subgroup.mem_centralizer_iff.mpr hg
  have hKC : K ≤ c.Cg := fun k hk => c.mem_cg_iff.mpr (by
    have hs := Subgroup.mem_centralizer_iff.mp hk c.s (c.zpowers_le_OG (Subgroup.mem_zpowers c.s))
    calc k * c.s * k⁻¹ = (c.s * k) * k⁻¹ := by rw [hs]
      _ = c.s := by group)
  have hKodd : Odd (Nat.card K) := by
    by_contra hev
    have h2 : 2 ∣ Nat.card K := by
      rw [Nat.not_odd_iff_even] at hev
      exact even_iff_two_dvd.mp hev
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := K) 2 h2
    have hw2 : (w : G) ^ 2 = 1 := by
      have := congrArg (fun x : K => (x : G)) (hw ▸ pow_orderOf_eq_one w)
      simpa using this
    have hw1 : (w : G) ≠ 1 := fun e => by
      have : w = 1 := Subtype.ext e
      rw [this, orderOf_one] at hw
      omega
    have hwc : ∀ y ∈ c.OG, y * (w : G) = (w : G) * y := Subgroup.mem_centralizer_iff.mp w.2
    have hws : (w : G) * c.s = c.s * (w : G) :=
      (hwc c.s (c.zpowers_le_OG (Subgroup.mem_zpowers c.s))).symm
    have hCO : c.CO (w : G) = c.OG := inf_eq_left.mpr (fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hwc y hy))
    have := (c.card_CO_dvd_nine hw2 hw1 hws).2
    rw [hCO, h81] at this
    omega
  have hKnorm : ∀ n ∈ c.Ng, ∀ k ∈ K, n * k * n⁻¹ ∈ K := by
    intro n hn k hk
    rw [hK, Subgroup.mem_centralizer_iff] at hk ⊢
    intro y hy
    have hy' : n⁻¹ * y * n ∈ c.OG := by
      have := c.OG_normalized n⁻¹ (c.Ng.inv_mem hn) y hy
      simpa using this
    have h1 := hk _ hy'
    calc y * (n * k * n⁻¹) = n * ((n⁻¹ * y * n) * k) * n⁻¹ := by group
      _ = n * (k * (n⁻¹ * y * n)) * n⁻¹ := by rw [h1]
      _ = n * k * n⁻¹ * y := by group
  exact c.le_OG_of_odd_normal (fun k hk => c.cg_le_ng (hKC hk)) hKnorm hKodd hgK

end Ctx





end Setup

end CFSG.Sporadic.Recognition.JankoWong
