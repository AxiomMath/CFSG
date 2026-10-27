module

public import CFSG.RankThree.PartTwo.Sec11.FixedPoints

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

namespace Item1133Proof

variable {G : Type*} [Group G]

theorem conj_mem_of_mem_closure {S : Set G} {K : Subgroup G} {y : G}
    (hS : ∀ s ∈ S, y * s * y⁻¹ ∈ K) {z : G} (hz : z ∈ Subgroup.closure S) :
    y * z * y⁻¹ ∈ K := by
  induction hz using Subgroup.closure_induction with
  | mem s hs => exact hS s hs
  | one => simp
  | mul z w _ _ hz hw =>
    have e : y * (z * w) * y⁻¹ = (y * z * y⁻¹) * (y * w * y⁻¹) := by group
    rw [e]
    exact K.mul_mem hz hw
  | inv z _ hz =>
    have e : y * z⁻¹ * y⁻¹ = (y * z * y⁻¹)⁻¹ := by group
    rw [e]
    exact K.inv_mem hz

theorem commutator_mem_of_mem_closure {S : Set G} {D : Subgroup G} {y : G}
    (hN : Subgroup.closure S ≤ Subgroup.normalizer (D : Set G)) (hS : ∀ s ∈ S, ⁅y, s⁆ ∈ D)
    {z : G} (hz : z ∈ Subgroup.closure S) : ⁅y, z⁆ ∈ D := by
  have hconj : ∀ w ∈ Subgroup.closure S, ∀ v ∈ D, w * v * w⁻¹ ∈ D := fun w hw v hv =>
    (Subgroup.mem_normalizer_iff.mp (hN hw) v).mp hv
  induction hz using Subgroup.closure_induction with
  | mem s hs => exact hS s hs
  | one => simp
  | mul z w hz' _ hz hw =>
    have e : ⁅y, z * w⁆ = ⁅y, z⁆ * (z * ⁅y, w⁆ * z⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact D.mul_mem hz (hconj z hz' _ hw)
  | inv z hz' hz =>
    have e : ⁅y, z⁻¹⁆ = z⁻¹ * ⁅y, z⁆⁻¹ * z⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact hconj z⁻¹ (inv_mem hz') _ (D.inv_mem hz)

theorem le_normalizer_of_commutator_le {P N : Subgroup G} (hNP : N ≤ P) (hPP : ⁅P, P⁆ ≤ N) :
    P ≤ Subgroup.normalizer (N : Set G) := by
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · intro hn
    have e : y * n * y⁻¹ = ⁅y, n⁆ * n := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact N.mul_mem (hPP (Subgroup.commutator_mem_commutator hy (hNP hn))) hn
  · intro hn
    have e : n = ⁅y⁻¹, y * n * y⁻¹⁆ * (y * n * y⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact N.mul_mem (hPP (Subgroup.commutator_mem_commutator (P.inv_mem hy) (hNP hn))) hn

theorem commute_of_mem_zpowers {y z w : G} (h : y * z = z * y) (hw : w ∈ Subgroup.zpowers z) :
    y * w = w * y := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  exact ((show Commute y z from h).zpow_right k).eq

theorem mem_normalizer_zpowers_of_commute {y d : G} (h : y * d = d * y) :
    y ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G) := by
  have hc : Commute y d := h
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [(hc.zpow_right k).eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers d k
  · intro hz
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
    have e : z = d ^ k := by
      have e1 : z = y⁻¹ * (y * z * y⁻¹) * y := by group
      rw [e1, ← hk, (hc.inv_left.zpow_right k).eq, inv_mul_cancel_right]
    rw [e]
    exact Subgroup.zpow_mem_zpowers d k

theorem zpow_three_eq_one {c : G} (hc3 : c ^ 3 = 1) : c ^ (3 : ℤ) = 1 := by
  rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, hc3]

theorem mem_zpowers_zpow {c : G} (hc3 : c ^ (3 : ℤ) = 1) {i : ℤ} (hi : c ^ i ≠ 1) :
    c ∈ Subgroup.zpowers (c ^ i) := by
  have hi3 : i % 3 ≠ 0 := by
    intro h0
    apply hi
    rw [zpow_eq_zpow_emod i hc3, h0, zpow_zero]
  have hii : (i * i) % 3 = 1 := by
    have : i % 3 = 1 ∨ i % 3 = 2 := by omega
    rcases this with h | h <;> rw [Int.mul_emod, h] <;> norm_num
  rw [Subgroup.mem_zpowers_iff]
  exact ⟨i, by rw [← zpow_mul, zpow_eq_zpow_emod (i * i) hc3, hii, zpow_one]⟩

theorem zpow_eq_one_of_mem {c : G} {K : Subgroup G} (hc3 : c ^ 3 = 1) (hcK : c ∉ K) {i : ℤ}
    (hi : c ^ i ∈ K) : c ^ i = 1 := by
  by_contra h
  exact hcK (Subgroup.zpowers_le.mpr hi (mem_zpowers_zpow (zpow_three_eq_one hc3) h))

theorem eq_of_mul_eq {U w δ X : G} (e : U * w = δ * (X * w) * w) : w = (δ * X)⁻¹ * U := by
  calc w = (δ * X)⁻¹ * (δ * (X * w) * w * w⁻¹) := by group
    _ = (δ * X)⁻¹ * (U * w * w⁻¹) := by rw [e]
    _ = (δ * X)⁻¹ * U := by group

theorem exists_fixed_of_two_pow [Finite G] {N : Subgroup G} {u w : G} {k : ℕ}
    (hu : u ^ 2 ^ k = 1) (hN : ¬ 2 ∣ Nat.card N)
    (hinv : ∀ y, w⁻¹ * y ∈ N → w⁻¹ * (u * y * u⁻¹) ∈ N) :
    ∃ y, w⁻¹ * y ∈ N ∧ u * y * u⁻¹ = y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let σ₀ : {y : G // w⁻¹ * y ∈ N} → {y : G // w⁻¹ * y ∈ N} :=
    fun y => ⟨u * y.1 * u⁻¹, hinv y.1 y.2⟩
  have hσ₀ : Function.Injective σ₀ := by
    intro y z hyz
    apply Subtype.ext
    have h := congrArg Subtype.val hyz
    simpa [σ₀] using h
  let σ : Equiv.Perm {y : G // w⁻¹ * y ∈ N} :=
    Equiv.ofBijective σ₀ (Finite.injective_iff_bijective.mp hσ₀)
  have hσpow : ∀ (n : ℕ) (y : {y : G // w⁻¹ * y ∈ N}),
      ((σ ^ n) y).1 = u ^ n * y.1 * (u ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro y; simp
    | succ n ih =>
      intro y
      rw [pow_succ, Equiv.Perm.mul_apply, ih (σ y)]
      change u ^ n * (u * y.1 * u⁻¹) * (u ^ n)⁻¹ = u ^ (n + 1) * y.1 * (u ^ (n + 1))⁻¹
      rw [pow_succ]
      group
  have hσ : σ ^ 2 ^ k = 1 := by
    apply Equiv.ext
    intro y
    apply Subtype.ext
    rw [hσpow, hu]
    simp
  have : Fintype {y : G // w⁻¹ * y ∈ N} := Fintype.ofFinite _
  have hcard : ¬ 2 ∣ Fintype.card {y : G // w⁻¹ * y ∈ N} := by
    rw [Fintype.card_eq_nat_card]
    have e : {y : G // w⁻¹ * y ∈ N} ≃ N :=
      { toFun := fun y => ⟨w⁻¹ * y.1, y.2⟩
        invFun := fun n => ⟨w * n.1, by simp⟩
        left_inv := fun y => by ext; simp
        right_inv := fun n => by ext; simp }
    rw [Nat.card_congr e]
    exact hN
  obtain ⟨y, hy⟩ := Equiv.Perm.exists_fixed_point_of_prime hcard hσ
  exact ⟨y.1, y.2, congrArg Subtype.val hy⟩

theorem not_le_closure_pair [Finite G] {A : Subgroup G} (h27 : Nat.card A = 27) {y z : G}
    (hyz : y * z = z * y) (hy : y ^ 3 = 1) (hz : z ^ 3 = 1) :
    ¬ A ≤ Subgroup.closure {y, z} := by
  intro hle
  have h1 := Subgroup.card_le_of_le hle
  have h2 := card_closure_pair_le_nine hyz hy hz
  omega

structure Config (A P : Subgroup G) (c a d x g u : G) : Prop where
  card_A : Nat.card A = 27
  pow_three : ∀ y ∈ A, y ^ 3 = 1
  mul_comm_A : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y
  closure_eq : A = Subgroup.closure {c, a, d}
  isPGroup : IsPGroup 3 P
  le_P : A ≤ P
  x_mem : x ∈ P
  g_mem : g ∈ P
  le_closure : P ≤ Subgroup.closure {c, a, x, g}
  d_mem_zpowers : d ∈ Subgroup.zpowers x
  orderOf_x : orderOf x = 9
  commutator_x_a : ⁅x, a⁆ ∈ Subgroup.zpowers d
  c_x : c * x = x * c
  g_a : g * a = a * g
  g_pow : ∃ k : ℕ, g ^ 3 ^ k = 1
  conj_g_c : g * c * g⁻¹ ∈ Subgroup.closure {c, d}
  g_c : g * c ≠ c * g
  commutator_eq : ⁅P, P⁆ = Subgroup.closure {a, d}
  u_mem_A : u ∈ Subgroup.normalizer (A : Set G)
  u_mem_P : u ∈ Subgroup.normalizer (P : Set G)
  u_pow : ∃ k : ℕ, u ^ 2 ^ k = 1
  centralizer_eq : P ⊓ Subgroup.centralizer {u} = Subgroup.closure {a, g}

namespace Config

variable {A P : Subgroup G} {c a d x g u : G}

theorem c_mem (h : Config A P c a d x g u) : c ∈ A := by
  rw [h.closure_eq]
  exact Subgroup.subset_closure (by simp)

theorem a_mem (h : Config A P c a d x g u) : a ∈ A := by
  rw [h.closure_eq]
  exact Subgroup.subset_closure (by simp)

theorem d_mem (h : Config A P c a d x g u) : d ∈ A := by
  rw [h.closure_eq]
  exact Subgroup.subset_closure (by simp)

theorem d_not_mem [Finite G] (h : Config A P c a d x g u) : d ∉ Subgroup.zpowers a := by
  intro hd
  refine not_le_closure_pair h.card_A (h.mul_comm_A c h.c_mem a h.a_mem) (h.pow_three c h.c_mem)
    (h.pow_three a h.a_mem) ?_
  rw [h.closure_eq, Subgroup.closure_le]
  simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe]
  exact ⟨Subgroup.subset_closure (by simp), Subgroup.subset_closure (by simp),
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) hd⟩

theorem a_not_mem [Finite G] (h : Config A P c a d x g u) : a ∉ Subgroup.zpowers d := by
  intro ha
  refine not_le_closure_pair h.card_A (h.mul_comm_A c h.c_mem d h.d_mem) (h.pow_three c h.c_mem)
    (h.pow_three d h.d_mem) ?_
  rw [h.closure_eq, Subgroup.closure_le]
  simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe]
  exact ⟨Subgroup.subset_closure (by simp),
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) ha,
    Subgroup.subset_closure (by simp)⟩

theorem c_not_mem [Finite G] (h : Config A P c a d x g u) : c ∉ Subgroup.closure {a, d} := by
  intro hc
  refine not_le_closure_pair h.card_A (h.mul_comm_A a h.a_mem d h.d_mem) (h.pow_three a h.a_mem)
    (h.pow_three d h.d_mem) ?_
  rw [h.closure_eq, Subgroup.closure_le]
  simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe]
  exact ⟨hc, Subgroup.subset_closure (by simp), Subgroup.subset_closure (by simp)⟩

theorem x_d (h : Config A P c a d x g u) : x * d = d * x :=
  commute_of_mem_zpowers rfl h.d_mem_zpowers

theorem u_a (h : Config A P c a d x g u) : u * a = a * u := by
  have ha : a ∈ P ⊓ Subgroup.centralizer {u} := by
    rw [h.centralizer_eq]
    exact Subgroup.subset_closure (by simp)
  exact (Subgroup.mem_centralizer_singleton_iff.mp ha.2).symm

theorem u_g (h : Config A P c a d x g u) : u * g = g * u := by
  have hg : g ∈ P ⊓ Subgroup.centralizer {u} := by
    rw [h.centralizer_eq]
    exact Subgroup.subset_closure (by simp)
  exact (Subgroup.mem_centralizer_singleton_iff.mp hg.2).symm

theorem mem_closure_of_fixed (h : Config A P c a d x g u) {y : G} (hy : y ∈ P)
    (hfix : u * y * u⁻¹ = y) : y ∈ Subgroup.closure {a, g} := by
  rw [← h.centralizer_eq]
  refine ⟨hy, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
  calc y * u = (u * y * u⁻¹) * u := by rw [hfix]
    _ = u * y := by group

theorem conj_u_mem_commutator (h : Config A P c a d x g u) {z : G} (hz : z ∈ ⁅P, P⁆) :
    u * z * u⁻¹ ∈ ⁅P, P⁆ := by
  rw [Subgroup.commutator_def] at hz
  refine conj_mem_of_mem_closure ?_ hz
  rintro _ ⟨p, hp, q, hq, rfl⟩
  have e : u * ⁅p, q⁆ * u⁻¹ = ⁅u * p * u⁻¹, u * q * u⁻¹⁆ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact Subgroup.commutator_mem_commutator ((Subgroup.mem_normalizer_iff.mp h.u_mem_P p).mp hp)
    ((Subgroup.mem_normalizer_iff.mp h.u_mem_P q).mp hq)

theorem commutator_g_c_mem [Finite G] (h : Config A P c a d x g u) :
    ⁅g, c⁆ ∈ Subgroup.zpowers d := by
  have hcd : c * d = d * c := h.mul_comm_A c h.c_mem d h.d_mem
  have hP : ⁅g, c⁆ ∈ Subgroup.closure {a, d} := by
    rw [← h.commutator_eq]
    exact Subgroup.commutator_mem_commutator h.g_mem (h.le_P h.c_mem)
  have hcd' : ⁅g, c⁆ ∈ Subgroup.closure {c, d} := by
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ h.conj_g_c (Subgroup.inv_mem _ (Subgroup.subset_closure (by simp)))
  obtain ⟨i, j, hij⟩ := Sec12.exists_zpow_mul_zpow_of_mem_closure_pair hcd hcd'
  have hci : c ^ i ∈ Subgroup.closure {a, d} := by
    have e : c ^ i = ⁅g, c⁆ * (d ^ j)⁻¹ := by rw [hij, mul_inv_cancel_right]
    rw [e]
    exact Subgroup.mul_mem _ hP (Subgroup.inv_mem _ (Subgroup.zpow_mem _
      (Subgroup.subset_closure (by simp)) j))
  rw [hij, zpow_eq_one_of_mem (h.pow_three c h.c_mem) h.c_not_mem hci, one_mul]
  exact Subgroup.zpow_mem_zpowers d j

theorem g_d [Finite G] (h : Config A P c a d x g u) : g * d = d * g := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ha3 := h.pow_three a h.a_mem
  have hd3 := h.pow_three d h.d_mem
  have had : a * d = d * a := h.mul_comm_A a h.a_mem d h.d_mem
  have hdPP : d ∈ ⁅P, P⁆ := by
    rw [h.commutator_eq]
    exact Subgroup.subset_closure (by simp)
  have hud : u * d * u⁻¹ ∈ Subgroup.closure {a, d} := by
    have := h.conj_u_mem_commutator hdPP
    rwa [h.commutator_eq] at this
  obtain ⟨p, q, hpq⟩ := Sec12.exists_zpow_mul_zpow_of_mem_closure_pair had hud
  rw [zpow_eq_zpow_emod q (zpow_three_eq_one hd3)] at hpq
  have hq0 : 0 ≤ q % 3 := Int.emod_nonneg _ (by norm_num)
  have hq3 : q % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
  have hua := h.u_a
  have hufix : ∀ z ∈ Subgroup.zpowers a, u * z * u⁻¹ = z := fun z hz => by
    rw [commute_of_mem_zpowers hua hz, mul_inv_cancel_right]
  interval_cases hq : q % 3
  ·
    exfalso
    apply h.d_not_mem
    rw [zpow_zero, mul_one] at hpq
    have e1 : u * d * u⁻¹ = u * a ^ p * u⁻¹ := by
      rw [hpq, hufix _ (Subgroup.zpow_mem_zpowers a p)]
    rw [mul_left_cancel (mul_right_cancel e1)]
    exact Subgroup.zpow_mem_zpowers a p
  ·
    rw [zpow_one] at hpq
    obtain ⟨k, hk⟩ := h.u_pow
    have ha1 : a ≠ 1 := fun ha1 => h.a_not_mem (ha1 ▸ Subgroup.one_mem _)
    have hN : ¬ 2 ∣ Nat.card (Subgroup.zpowers a) := by
      rw [Nat.card_zpowers, orderOf_eq_prime ha3 ha1]
      norm_num
    have hinv : ∀ y, d⁻¹ * y ∈ Subgroup.zpowers a →
        d⁻¹ * (u * y * u⁻¹) ∈ Subgroup.zpowers a := by
      intro y hy
      have e : d⁻¹ * (u * y * u⁻¹) = (d⁻¹ * (u * d * u⁻¹)) * (u * (d⁻¹ * y) * u⁻¹) := by group
      have hda : d⁻¹ * a ^ p = a ^ p * d⁻¹ :=
        (((show Commute d a from had.symm).inv_left).zpow_right p).eq
      have hda' : d⁻¹ * (a ^ p * d) = a ^ p := by
        rw [← mul_assoc, hda, inv_mul_cancel_right]
      rw [e, hufix _ hy, hpq, hda']
      exact Subgroup.mul_mem _ (Subgroup.zpow_mem_zpowers a p) hy
    obtain ⟨y, hy, hfix⟩ := exists_fixed_of_two_pow hk hN hinv
    have hyP : y ∈ P := by
      have e : y = d * (d⁻¹ * y) := by group
      rw [e]
      exact P.mul_mem (h.le_P h.d_mem) (h.le_P (Subgroup.zpowers_le.mpr h.a_mem hy))
    have hyC := h.mem_closure_of_fixed hyP hfix
    have hdC : d ∈ Subgroup.closure {a, g} := by
      have e : d = y * (d⁻¹ * y)⁻¹ := by group
      rw [e]
      exact Subgroup.mul_mem _ hyC (Subgroup.inv_mem _
        (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) hy))
    have hle : Subgroup.closure ({a, g} : Set G) ≤ Subgroup.centralizer {g} := by
      rw [Subgroup.closure_le]
      simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe]
      exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr h.g_a.symm,
        Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hdC)).symm
  ·
    obtain ⟨k, hk⟩ := h.g_pow
    have hgdPP : g * d * g⁻¹ ∈ Subgroup.closure {a, d} := by
      have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_commutator P P h.g_mem) d).mp hdPP
      rwa [h.commutator_eq] at this
    have hα := Sec12.conj_mul_inv_mem_zpowers_of_mem_closure had ha3 hd3 h.d_not_mem h.g_a hk
      hgdPP
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hα
    have h1 : u * (g * d * g⁻¹ * d⁻¹) * u⁻¹ = g * d * g⁻¹ * d⁻¹ := hufix _ hα
    have hgd : g * d * g⁻¹ = a ^ m * d := by
      rw [hm]
      group
    have hgap : g * a ^ p * g⁻¹ = a ^ p := by
      rw [((show Commute g a from h.g_a).zpow_right p).eq, mul_inv_cancel_right]
    have hda : d * a ^ m = a ^ m * d := ((show Commute a d from had).zpow_left m).eq.symm
    have hug' : u * g * u⁻¹ = g := by rw [h.u_g, mul_inv_cancel_right]
    have h2 : u * (g * d * g⁻¹ * d⁻¹) * u⁻¹ = a ^ m * a ^ m := by
      have e : u * (g * d * g⁻¹ * d⁻¹) * u⁻¹ =
          (u * g * u⁻¹) * (u * d * u⁻¹) * (u * g * u⁻¹)⁻¹ * (u * d * u⁻¹)⁻¹ := by group
      rw [e, hug', hpq, zpow_two]
      have e2 : g * (a ^ p * (d * d)) * g⁻¹ * (a ^ p * (d * d))⁻¹ =
          (g * a ^ p * g⁻¹) * (g * d * g⁻¹) * (g * d * g⁻¹) * d⁻¹ * d⁻¹ * (a ^ p)⁻¹ := by
        group
      rw [e2, hgap, hgd]
      have e3 : a ^ p * (a ^ m * d) * (a ^ m * d) * d⁻¹ * d⁻¹ * (a ^ p)⁻¹ =
          a ^ p * a ^ m * (d * a ^ m) * d⁻¹ * (a ^ p)⁻¹ := by group
      rw [e3, hda]
      group
    have h3 : a ^ m * a ^ m = a ^ m * 1 := by rw [← h2, h1, hm, mul_one]
    have h4 : g * d * g⁻¹ * d⁻¹ = 1 := by rw [← hm]; exact mul_left_cancel h3
    calc g * d = (g * d * g⁻¹ * d⁻¹) * (d * g) := by group
      _ = d * g := by rw [h4, one_mul]

theorem commutator_g_mem [Finite G] (h : Config A P c a d x g u) {y : G}
    (hy : y ∈ Subgroup.closure {c, a, d, g}) : ⁅g, y⁆ ∈ Subgroup.zpowers d := by
  refine commutator_mem_of_mem_closure ?_ ?_ hy
  · rw [Subgroup.closure_le]
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe]
    exact ⟨mem_normalizer_zpowers_of_commute (h.mul_comm_A c h.c_mem d h.d_mem),
      mem_normalizer_zpowers_of_commute (h.mul_comm_A a h.a_mem d h.d_mem),
      mem_normalizer_zpowers_of_commute rfl, mem_normalizer_zpowers_of_commute h.g_d⟩
  · intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz | hz | hz <;> rw [hz]
    · exact h.commutator_g_c_mem
    · rw [commutatorElement_eq_one_iff_mul_comm.mpr h.g_a]
      exact Subgroup.one_mem _
    · rw [commutatorElement_eq_one_iff_mul_comm.mpr h.g_d]
      exact Subgroup.one_mem _
    · rw [commutatorElement_self]
      exact Subgroup.one_mem _

theorem conj_u_mem_zpowers [Finite G] (h : Config A P c a d x g u) {z : G}
    (hz : z ∈ Subgroup.zpowers d) : u * z * u⁻¹ ∈ Subgroup.zpowers d := by
  have hgc1 : ⁅g, c⁆ ≠ 1 := fun h1 => h.g_c (commutatorElement_eq_one_iff_mul_comm.mp h1)
  have hdgc : d ∈ Subgroup.zpowers ⁅g, c⁆ := by
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp h.commutator_g_c_mem
    rw [← hj] at hgc1 ⊢
    exact mem_zpowers_zpow (zpow_three_eq_one (h.pow_three d h.d_mem)) hgc1
  have hug' : u * g * u⁻¹ = g := by rw [h.u_g, mul_inv_cancel_right]
  have hu_gc : u * ⁅g, c⁆ * u⁻¹ ∈ Subgroup.zpowers d := by
    have e : u * ⁅g, c⁆ * u⁻¹ = ⁅u * g * u⁻¹, u * c * u⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e, hug']
    have hcA : u * c * u⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp h.u_mem_A c).mp h.c_mem
    refine h.commutator_g_mem ?_
    have hA : A ≤ Subgroup.closure {c, a, d, g} := by
      rw [h.closure_eq]
      exact Subgroup.closure_mono (by
        intro w hw
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw ⊢
        tauto)
    exact hA hcA
  have hz' : z ∈ Subgroup.zpowers ⁅g, c⁆ := Subgroup.zpowers_le.mpr hdgc hz
  rw [Subgroup.zpowers_eq_closure] at hz'
  refine conj_mem_of_mem_closure ?_ hz'
  rintro _ rfl
  exact hu_gc

theorem x_pow_three_mem [Finite G] (h : Config A P c a d x g u) :
    x ^ (3 : ℤ) ∈ Subgroup.zpowers d := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h.d_mem_zpowers
  have hd3 := h.pow_three d h.d_mem
  have h9 : ((orderOf x : ℕ) : ℤ) ∣ k * 3 := by
    rw [orderOf_dvd_iff_zpow_eq_one, zpow_mul, hk]
    exact zpow_three_eq_one hd3
  rw [h.orderOf_x] at h9
  push_cast at h9
  obtain ⟨m, rfl⟩ : (3 : ℤ) ∣ k := by omega
  have hdm : (x ^ (3 : ℤ)) ^ m = d := by rw [← zpow_mul, hk]
  have hx9 : (x ^ (3 : ℤ)) ^ (3 : ℤ) = 1 := by
    rw [← zpow_mul, show (3 : ℤ) * 3 = ((9 : ℕ) : ℤ) by norm_num, zpow_natCast, ← h.orderOf_x,
      pow_orderOf_eq_one]
  have hd1 : d ≠ 1 := fun hd1 => h.d_not_mem (hd1 ▸ Subgroup.one_mem _)
  rw [← hdm] at hd1 ⊢
  exact mem_zpowers_zpow hx9 hd1

theorem commutator_x_g_mem [Finite G] (h : Config A P c a d x g u) :
    ⁅x, g⁆ ∈ Subgroup.zpowers d := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨N, hN⟩ : ∃ N : Subgroup G, N = Subgroup.closure {c, a, d, g} := ⟨_, rfl⟩
  have hcN : c ∈ N := by rw [hN]; exact Subgroup.subset_closure (by simp)
  have haN : a ∈ N := by rw [hN]; exact Subgroup.subset_closure (by simp)
  have hdN : d ∈ N := by rw [hN]; exact Subgroup.subset_closure (by simp)
  have hgN : g ∈ N := by rw [hN]; exact Subgroup.subset_closure (by simp)
  have hAN : A ≤ N := by
    rw [h.closure_eq, Subgroup.closure_le]
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe]
    exact ⟨hcN, haN, hdN⟩
  have hNP : N ≤ P := by
    rw [hN, Subgroup.closure_le]
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe]
    exact ⟨h.le_P h.c_mem, h.le_P h.a_mem, h.le_P h.d_mem, h.g_mem⟩
  have hPPN : ⁅P, P⁆ ≤ N := by
    rw [h.commutator_eq, Subgroup.closure_le]
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe]
    exact ⟨haN, hdN⟩
  have hDN : Subgroup.zpowers d ≤ N := Subgroup.zpowers_le.mpr hdN
  have hNg : ∀ n ∈ N, ⁅n, g⁆ ∈ Subgroup.zpowers d := by
    intro n hn
    rw [← commutatorElement_inv]
    rw [hN] at hn
    exact Subgroup.inv_mem _ (h.commutator_g_mem hn)
  have hconjN : ∀ v : G, v ∈ Subgroup.normalizer (A : Set G) → v * a = a * v →
      v * g = g * v → ∀ n ∈ N, v * n * v⁻¹ ∈ N := by
    intro v hvA hva hvg n hn
    rw [hN] at hn
    refine conj_mem_of_mem_closure ?_ hn
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hy | hy | hy | hy <;> rw [hy]
    · exact hAN ((Subgroup.mem_normalizer_iff.mp hvA c).mp h.c_mem)
    · rw [hva, mul_inv_cancel_right]
      exact haN
    · exact hAN ((Subgroup.mem_normalizer_iff.mp hvA d).mp h.d_mem)
    · rw [hvg, mul_inv_cancel_right]
      exact hgN
  have huN := hconjN u h.u_mem_A h.u_a h.u_g
  have huN' := hconjN u⁻¹ (inv_mem h.u_mem_A) (Commute.inv_left h.u_a).eq
    (Commute.inv_left h.u_g).eq
  have hug' : u * g * u⁻¹ = g := by rw [h.u_g, mul_inv_cancel_right]
  have hxN : Subgroup.zpowers x ≤ Subgroup.normalizer (N : Set G) :=
    Subgroup.zpowers_le.mpr (le_normalizer_of_commutator_le hNP hPPN h.x_mem)
  have hPxN : P ≤ Subgroup.zpowers x ⊔ N := by
    refine h.le_closure.trans ?_
    rw [Subgroup.closure_le]
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe]
    exact ⟨Subgroup.mem_sup_right hcN, Subgroup.mem_sup_right haN,
      Subgroup.mem_sup_left (Subgroup.mem_zpowers x), Subgroup.mem_sup_right hgN⟩
  have huxP : u * x * u⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp h.u_mem_P x).mp h.x_mem
  have hmem : u * x * u⁻¹ ∈ ((Subgroup.zpowers x ⊔ N : Subgroup G) : Set G) := hPxN huxP
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hxN] at hmem
  obtain ⟨y, hy, n, hn, hyn⟩ := Set.mem_mul.mp hmem
  obtain ⟨t, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have ht : x ^ t = x ^ (t % 3) * (x ^ (3 : ℤ)) ^ (t / 3) := by
    rw [← zpow_mul, ← zpow_add]
    congr 1
    omega
  have hux : u * x * u⁻¹ = x ^ (t % 3) * ((x ^ (3 : ℤ)) ^ (t / 3) * n) := by
    rw [← hyn, ht, mul_assoc]
  have hn' : (x ^ (3 : ℤ)) ^ (t / 3) * n ∈ N :=
    N.mul_mem (N.zpow_mem (hDN h.x_pow_three_mem) _) hn
  generalize (x ^ (3 : ℤ)) ^ (t / 3) * n = n' at hux hn'
  have ht0 : 0 ≤ t % 3 := Int.emod_nonneg _ (by norm_num)
  have ht3 : t % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
  have hxNg : x ∈ N → ⁅x, g⁆ ∈ Subgroup.zpowers d := fun hx => hNg x hx
  obtain ⟨k, hk⟩ := h.u_pow
  have hNodd : ¬ 2 ∣ Nat.card N := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (h.isPGroup.to_le hNP)
    rw [hm]
    intro h2
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2
    omega
  interval_cases hτ : t % 3
  ·
    apply hxNg
    rw [zpow_zero, one_mul] at hux
    have e : x = u⁻¹ * (u * x * u⁻¹) * u⁻¹⁻¹ := by group
    rw [e, hux]
    exact huN' n' hn'
  ·
    apply hxNg
    rw [zpow_one] at hux
    have hinv : ∀ y, x⁻¹ * y ∈ N → x⁻¹ * (u * y * u⁻¹) ∈ N := by
      intro y hy
      have e : x⁻¹ * (u * y * u⁻¹) = (x⁻¹ * (u * x * u⁻¹)) * (u * (x⁻¹ * y) * u⁻¹) := by group
      rw [e, hux, inv_mul_cancel_left]
      exact N.mul_mem hn' (huN _ hy)
    obtain ⟨y, hy, hfix⟩ := exists_fixed_of_two_pow hk hNodd hinv
    have hyP : y ∈ P := by
      have e : y = x * (x⁻¹ * y) := by group
      rw [e]
      exact P.mul_mem h.x_mem (hNP hy)
    have hagN : Subgroup.closure ({a, g} : Set G) ≤ N := by
      rw [Subgroup.closure_le]
      simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe]
      exact ⟨haN, hgN⟩
    have hyN : y ∈ N := hagN (h.mem_closure_of_fixed hyP hfix)
    have e : x = y * (x⁻¹ * y)⁻¹ := by group
    rw [e]
    exact N.mul_mem hyN (N.inv_mem hy)
  ·
    have hwPP : ⁅x, g⁆ ∈ Subgroup.closure {a, d} := by
      rw [← h.commutator_eq]
      exact Subgroup.commutator_mem_commutator h.x_mem h.g_mem
    have hadD : Subgroup.closure ({a, d} : Set G) ≤
        Subgroup.normalizer (Subgroup.zpowers d : Set G) := by
      rw [Subgroup.closure_le]
      simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe]
      exact ⟨mem_normalizer_zpowers_of_commute (h.mul_comm_A a h.a_mem d h.d_mem),
        mem_normalizer_zpowers_of_commute rfl⟩
    have hxw : ⁅x, ⁅x, g⁆⁆ ∈ Subgroup.zpowers d := by
      refine commutator_mem_of_mem_closure hadD ?_ hwPP
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with hz | hz <;> rw [hz]
      · exact h.commutator_x_a
      · rw [commutatorElement_eq_one_iff_mul_comm.mpr h.x_d]
        exact Subgroup.one_mem _
    have huw : ⁅u, ⁅x, g⁆⁆ ∈ Subgroup.zpowers d := by
      refine commutator_mem_of_mem_closure hadD ?_ hwPP
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with hz | hz <;> rw [hz]
      · rw [commutatorElement_eq_one_iff_mul_comm.mpr h.u_a]
        exact Subgroup.one_mem _
      · rw [commutatorElement_def]
        exact Subgroup.mul_mem _ (h.conj_u_mem_zpowers (Subgroup.mem_zpowers d))
          (Subgroup.inv_mem _ (Subgroup.mem_zpowers d))
    have hx2D : x ^ (2 : ℤ) * ⁅n', g⁆ * (x ^ (2 : ℤ))⁻¹ ∈ Subgroup.zpowers d :=
      (Subgroup.mem_normalizer_iff.mp (mem_normalizer_zpowers_of_commute
        ((show Commute x d from h.x_d).zpow_left 2).eq) _).mp (hNg n' hn')
    have e : ⁅u, ⁅x, g⁆⁆ * ⁅x, g⁆ =
        (x ^ (2 : ℤ) * ⁅n', g⁆ * (x ^ (2 : ℤ))⁻¹) * (⁅x, ⁅x, g⁆⁆ * ⁅x, g⁆) * ⁅x, g⁆ := by
      have e1 : ⁅u, ⁅x, g⁆⁆ * ⁅x, g⁆ = ⁅u * x * u⁻¹, u * g * u⁻¹⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e1, hux, hug']
      simp only [commutatorElement_def]
      group
    rw [eq_of_mul_eq e]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mul_mem _ hx2D hxw)) huw

theorem false_of [Finite G] (h : Config A P c a d x g u) : False := by
  have hxg := h.commutator_x_g_mem
  have hgc := h.commutator_g_c_mem
  have hcomm : ∀ y z : G, y * z = z * y → ⁅y, z⁆ ∈ Subgroup.zpowers d := fun y z hyz => by
    rw [commutatorElement_eq_one_iff_mul_comm.mpr hyz]
    exact Subgroup.one_mem _
  have hsym : ∀ y z : G, ⁅y, z⁆ ∈ Subgroup.zpowers d → ⁅z, y⁆ ∈ Subgroup.zpowers d :=
    fun y z hyz => by
      rw [← commutatorElement_inv]
      exact Subgroup.inv_mem _ hyz
  have hca : c * a = a * c := h.mul_comm_A c h.c_mem a h.a_mem
  have hle : ⁅P, P⁆ ≤ Subgroup.zpowers d := by
    refine (Subgroup.commutator_mono h.le_closure h.le_closure).trans
      (commutator_closure_le ?_ ?_)
    · rw [Subgroup.closure_le]
      simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe]
      exact ⟨mem_normalizer_zpowers_of_commute (h.mul_comm_A c h.c_mem d h.d_mem),
        mem_normalizer_zpowers_of_commute (h.mul_comm_A a h.a_mem d h.d_mem),
        mem_normalizer_zpowers_of_commute h.x_d, mem_normalizer_zpowers_of_commute h.g_d⟩
    · intro y hy z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy hz
      rcases hy with hy | hy | hy | hy <;> rcases hz with hz | hz | hz | hz <;> rw [hy, hz] <;>
        first
        | exact hcomm _ _ rfl
        | exact hcomm _ _ hca
        | exact hcomm _ _ hca.symm
        | exact hcomm _ _ h.c_x
        | exact hcomm _ _ h.c_x.symm
        | exact hcomm _ _ h.g_a
        | exact hcomm _ _ h.g_a.symm
        | exact h.commutator_x_a
        | exact hsym _ _ h.commutator_x_a
        | exact hxg
        | exact hsym _ _ hxg
        | exact hgc
        | exact hsym _ _ hgc
  have ha : a ∈ ⁅P, P⁆ := by
    rw [h.commutator_eq]
    exact Subgroup.subset_closure (by simp)
  exact h.a_not_mem (hle ha)

end Config

end Item1133Proof

section Main


theorem Item1133Proof.le_R {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G}
    {L : Subgroup G} {a : G} {R : Subgroup G} (h : Sec9.Hyp91 G A c L a R) : A ≤ R := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set K := Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓ Subgroup.normalizer (A : Set G)
  have hAe := h.mem_partTwoF.1
  have hAK : A ≤ K := fun y hy =>
    ⟨Item1133Proof.mem_normalizer_zpowers_of_commute
      (congrArg Subtype.val (hAe.1.is_comm.comm ⟨y, hy⟩ ⟨c, h.mem_A⟩)), Subgroup.le_normalizer hy⟩
  have hA3 : IsPGroup 3 A := fun y => ⟨1, Subtype.ext (by simpa using hAe.2 y y.2)⟩
  have hN : (Subgroup.comap K.subtype A).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAK).mpr inf_le_right
  obtain ⟨Q, hQ⟩ := h.isSylowOf_inf
  have hle := @IsPGroup.le_sylow_of_normal 3 K _ _ hN (hA3.comap_subtype (K := K)) Q
  intro y hy
  have h1 : (⟨y, hAK hy⟩ : K) ∈ (Q : Subgroup K) := hle (Subgroup.mem_subgroupOf.mpr hy)
  have h2 : y ∈ (Q : Subgroup K).map K.subtype := ⟨_, h1, rfl⟩
  rw [hQ] at h2
  exact h2.1

theorem Item1133Proof.config_of_sec11Final {G : Type} [Group G] [Finite G] {A : Subgroup G}
    {c : G} {L : Subgroup G} {a : G} {R Y : Subgroup G} {d x s r g u : G}
    (h : Sec11Final G A c L a R Y d x s r g)
    (hu : u ∈ Subgroup.normalizer (A : Set G) ⊓
      Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G))
    (hu2 : ∃ k : ℕ, u ^ 2 ^ k = 1)
    (hCu : sec11P R g ⊓ Subgroup.centralizer ({u} : Set G) = Subgroup.closure {a, g}) :
    Item1133Proof.Config A (sec11P R g) c a d x g u := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD : Sec11Data G A c L a R Y d x s r g := h.toSec11Data
  have hAR : A ≤ R := Item1133Proof.le_R hD.toHyp91
  have hRP : R ≤ sec11P R g := le_sup_left
  have hAexp : ∀ y ∈ A, y ^ 3 = 1 := h.mem_partTwoF.1.2
  have hAcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (h.mem_partTwoF.1.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have hdAL : d ∈ A ⊓ L := by
    rw [h.inf_eq]
    exact Subgroup.mem_zpowers d
  have hxRL : x ∈ R ⊓ L := by
    rw [h.inf_L_eq]
    exact Subgroup.mem_zpowers x
  have hsc : s ∈ Subgroup.zpowers c := by
    rw [← h.zpowers_s_eq]
    exact Subgroup.mem_zpowers s
  have hcx : c * x = x * c := by
    have hc3 : orderOf c = 3 := orderOf_eq_prime (hAexp c h.mem_A) h.ne_one
    obtain ⟨k, hk⟩ := h.isSylowOf.isPGroup ⟨x, hxRL.1⟩
    have hxk : x ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact (Sec12.commute_of_conj_mem_zpowers hc3 ((Subgroup.mem_normalizer_iff.mp
      (h.isSylowOf.le hxRL.1) c).mp (Subgroup.mem_zpowers c)) hxk).symm
  have hsC : s ∈ Subgroup.closure ({c, a, x, g} : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) hsc
  have hPle : sec11P R g ≤ Subgroup.closure {c, a, x, g} := by
    show R ⊔ Subgroup.zpowers g ≤ _
    refine sup_le ?_ ?_
    · rw [h.R_eq, Subgroup.closure_le]
      simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe]
      refine ⟨?_, Subgroup.subset_closure (by simp), hsC⟩
      have hr : r ∈ Subgroup.closure ({a, s} : Set G) := by
        rw [← h.closure_eq_closure]
        exact Subgroup.subset_closure (by simp)
      refine (Subgroup.closure_le _).mpr ?_ hr
      simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe]
      exact ⟨Subgroup.subset_closure (by simp), hsC⟩
    · rw [Subgroup.zpowers_le]
      exact Subgroup.subset_closure (by simp)
  have hAP : A ≤ sec11P R g := hAR.trans hRP
  have hxA : x ∈ Subgroup.normalizer (A : Set G) := by
    refine Item1133Proof.le_normalizer_of_commutator_le hAP ?_ (hRP hxRL.1)
    rw [h.commutator_eq, Subgroup.closure_le]
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe]
    exact ⟨h.a_mem, hdAL.1⟩
  have hxa : ⁅x, a⁆ ∈ Subgroup.zpowers d := by
    rw [← h.inf_eq, commutatorElement_def]
    refine ⟨A.mul_mem ((Subgroup.mem_normalizer_iff.mp hxA a).mp h.a_mem) (A.inv_mem h.a_mem),
      ?_⟩
    have haL : a ∈ Subgroup.normalizer (L : Set G) := hD.toHyp91.toHyp81.a_mem_normalizer
    have h1 : a * x⁻¹ * a⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp haL x⁻¹).mp (L.inv_mem hxRL.2)
    have e : x * a * x⁻¹ * a⁻¹ = x * (a * x⁻¹ * a⁻¹) := by group
    rw [e]
    exact L.mul_mem hxRL.2 h1
  have hgc1 : g * c ≠ c * g := fun hgc =>
    h.g_not_mem (Item1133Proof.mem_normalizer_zpowers_of_commute hgc)
  exact
    { card_A := h.card_eq
      pow_three := hAexp
      mul_comm_A := hAcomm
      closure_eq := h.closure_eq
      isPGroup := hD.isPGroup_sec11P
      le_P := hAP
      x_mem := hRP hxRL.1
      g_mem := Subgroup.mem_sup_right (Subgroup.mem_zpowers g)
      le_closure := hPle
      d_mem_zpowers := by
        rw [← h.inf_L_eq]
        exact ⟨hAR hdAL.1, hdAL.2⟩
      orderOf_x := h.orderOf_x
      commutator_x_a := hxa
      c_x := hcx
      g_a := h.g_comm
      g_pow := h.pow_eq_one
      conj_g_c := h.conj_mem
      g_c := hgc1
      commutator_eq := h.commutator_eq
      u_mem_A := hu.1
      u_mem_P := hu.2
      u_pow := hu2
      centralizer_eq := hCu }

theorem item1133 : Item1133 := by
  intro G _ _ A c L a R Y d x s r g hf u hu hu2 hCu
  exact (Item1133Proof.config_of_sec11Final hf hu hu2 hCu).false_of.elim

end Main

end CFSG.RankThree.PartTwo.Sec11
