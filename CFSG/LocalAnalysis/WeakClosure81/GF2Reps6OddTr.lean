module

public import CFSG.Quasithin.Background.CommVBasics
public import CFSG.GroupTheory.ThompsonAxBFaithful
public import CFSG.HardMathSupport.Aschbacher.SymplecticType.ActionCommutator
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch6

open CFSG.Quasithin Subgroup

variable {V : Type*} [CommGroup V]

theorem false_of_fixes_fixV_pow [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {r : MulAut V}
    (hm : Even (orderOf r)) (h4 : 4 ≤ orderOf r)
    (hfix : ∀ v : V, (r ^ (orderOf r / 2)) v = v → r v = v) : False := by
  have : Finite (MulAut V) := Finite.of_injective _ DFunLike.coe_injective
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set m := orderOf r with hmdef
  have hm0 : m ≠ 0 := (orderOf_pos r).ne'
  obtain ⟨k, m', hodd, hmul⟩ := Nat.exists_eq_two_pow_mul_odd hm0
  set y := r ^ (2 ^ k) with hydef
  have hdvd : 2 ^ k ∣ m := by
    rw [hmul]
    exact dvd_mul_right _ _
  have hordy : orderOf y = m' := by
    rw [hydef, orderOf_pow_of_dvd (by positivity) hdvd, ← hmdef, hmul,
      Nat.mul_div_right m' (by positivity)]
  have hyodd : Odd (orderOf y) := by rw [hordy]; exact hodd
  set z := r ^ (m / 2) with hzdef
  have hzsq : z * z = 1 := by
    rw [hzdef, ← pow_add]
    obtain ⟨t, ht⟩ := hm
    have hm2t : m = 2 * t := by omega
    have hhalf : m / 2 + m / 2 = m := by
      have hm2 : m / 2 = t := by rw [hm2t, Nat.mul_div_right t (by norm_num)]
      omega
    rw [hhalf, hmdef, pow_orderOf_eq_one]
  have hzord : orderOf z = 2 := by
    refine orderOf_eq_prime (by rw [pow_two]; exact hzsq) ?_
    rw [hzdef]
    refine pow_ne_one_of_lt_orderOf (x := r) (n := m / 2) ?_ ?_
    · omega
    · rw [← hmdef]
      omega
  have hQ : IsPGroup 2 (Subgroup.zpowers z) := by
    refine IsPGroup.of_card_dvd_pow (p := 2) (n := 1) ?_
    rw [Nat.card_zpowers, hzord]
    norm_num
  have hcomm : ∀ q ∈ Subgroup.zpowers z, y * q = q * y := by
    intro q hq
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
    have hyz : y = r ^ ((2 ^ k : ℕ) : ℤ) := by rw [hydef, zpow_natCast]
    have hzz : z = r ^ ((m / 2 : ℕ) : ℤ) := by rw [hzdef, zpow_natCast]
    calc y * z ^ i = r ^ ((2 ^ k : ℕ) : ℤ) * r ^ (((m / 2 : ℕ) : ℤ) * i) := by
          rw [hyz, hzz, zpow_mul]
      _ = r ^ (((m / 2 : ℕ) : ℤ) * i) * r ^ ((2 ^ k : ℕ) : ℤ) := by
          rw [← zpow_add, ← zpow_add]
          congr 1
          ring
      _ = z ^ i * y := by rw [hyz, hzz, zpow_mul]
  have hfixy : ∀ v ∈ fixV (Subgroup.zpowers z), y v = v := by
    intro v hv
    have hzv : z v = v := (mem_fixV.mp hv) z (Subgroup.mem_zpowers z)
    have hrv : r v = v := hfix v hzv
    have hpow : ∀ n : ℕ, (r ^ n) v = v := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [pow_succ, MulAut.mul_apply, hrv, ih]
    rw [hydef]
    exact hpow (2 ^ k)
  have hVp : IsPGroup 2 V := fun v => ⟨1, by rw [pow_one, hV v]⟩
  have hy1 : y = 1 :=
    CFSG.GroupTheory.eq_one_of_forall_fixed_of_coprime hVp hQ
      (Nat.coprime_two_right.2 hyodd) (fun q hq => (hcomm q hq).symm)
      (fun v hv => hfixy v (mem_fixV.mpr hv))
  have hm' : m' = 1 := by
    have h := hordy
    rw [hy1, orderOf_one] at h
    exact h.symm
  have hmpow : m = 2 ^ k := by rw [hmul, hm', mul_one]
  have hk2 : 2 ≤ k := by
    by_contra hk
    have hk01 : k = 0 ∨ k = 1 := by omega
    rcases hk01 with rfl | rfl
    · rw [hmpow] at h4
      norm_num at h4
    · rw [hmpow] at h4
      norm_num at h4
  have h4m : 4 ∣ m := by
    rw [hmpow]
    simpa using Nat.pow_dvd_pow 2 hk2
  have h4ord : 4 ∣ orderOf r := by rwa [← hmdef]
  set w := r ^ (m / 4) with hwdef
  have hword : orderOf w = 4 := by
    rw [hwdef]
    exact orderOf_pow_orderOf_div (x := r) (orderOf_pos r).ne' h4ord
  have hw2 : w ^ 2 = z := by
    have hquarter : m / 2 = 2 * (m / 4) := by
      calc m / 2 = (4 * (m / 4)) / 2 := by rw [Nat.mul_div_cancel' h4m]
        _ = 4 / 2 * (m / 4) := Nat.mul_div_right_comm (by norm_num : 2 ∣ 4) (m / 4)
        _ = 2 * (m / 4) := by norm_num
    rw [hwdef, hzdef, pow_two, ← pow_add]
    congr 1
    omega
  have hC : {v : V | w v = v} = {v : V | (w ^ 2) v = v} := by
    ext v
    constructor
    · intro hv
      change (w ^ 2) v = v
      rw [pow_two, MulAut.mul_apply, hv, hv]
    · intro hv
      rw [hw2] at hv
      have hrv : r v = v := hfix v hv
      have hpow : ∀ n : ℕ, (r ^ n) v = v := by
        intro n
        induction n with
        | zero => rfl
        | succ n ih => rw [pow_succ, MulAut.mul_apply, hrv, ih]
      rw [hwdef]
      exact hpow (m / 4)
  have hbot :=
    CFSG.HardMathSupport.Aschbacher.SymplecticType.actionCommutator_eq_bot_of_fixed_points_eq
      V hV w ⟨2, by rw [hword]; norm_num⟩ hC
  have hw1 : w = 1 := by
    ext v
    have hmem : v⁻¹ * w v ∈
        CFSG.HardMathSupport.Aschbacher.SymplecticType.actionCommutator V {w} :=
      Subgroup.subset_closure ⟨w, by simp, v, rfl⟩
    rw [hbot] at hmem
    have h1 : v⁻¹ * w v = 1 := Subgroup.mem_bot.1 hmem
    have h2 : w v = v := (inv_mul_eq_one.1 h1).symm
    simpa using h2
  rw [hw1, orderOf_one] at hword
  norm_num at hword

theorem fixes_of_inf_commV_eq_bot {a z : MulAut V}
    (h : commV (zpowers a) ⊓ commV (zpowers (a * z)) = ⊥) {v : V} (hv : z v = v) : a v = v := by
  have h1 : a v * v⁻¹ ∈ commV (zpowers a) :=
    Subgroup.subset_closure ⟨a, Subgroup.mem_zpowers a, v, rfl⟩
  have h2 : a v * v⁻¹ ∈ commV (zpowers (a * z)) := by
    refine Subgroup.subset_closure ⟨a * z, Subgroup.mem_zpowers (a * z), v, ?_⟩
    rw [MulAut.mul_apply, hv]
  have hmem : a v * v⁻¹ ∈ (⊥ : Subgroup V) := by
    rw [← h]
    exact Subgroup.mem_inf.2 ⟨h1, h2⟩
  exact mul_inv_eq_one.1 (Subgroup.mem_bot.1 hmem)

theorem false_of_inf_commV_eq_bot [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {a b : MulAut V}
    (hm : Even (orderOf (a * b))) (h4 : 4 ≤ orderOf (a * b))
    (ha : commV (zpowers a) ⊓ commV (zpowers (a * (a * b) ^ (orderOf (a * b) / 2))) = ⊥)
    (hb : commV (zpowers b) ⊓ commV (zpowers (b * (a * b) ^ (orderOf (a * b) / 2))) = ⊥) :
    False := by
  refine false_of_fixes_fixV_pow (V := V) hV hm h4 ?_
  intro v hv
  have hav : a v = v := fixes_of_inf_commV_eq_bot (V := V) ha hv
  have hbv : b v = v := fixes_of_inf_commV_eq_bot (V := V) hb hv
  calc (a * b) v = a (b v) := rfl
    _ = a v := by rw [hbv]
    _ = v := hav

theorem exists_conj_mul_pow_half {G : Type*} [Group G] {a b : G} (ha : a ^ 2 = 1)
    (hb : b ^ 2 = 1) (hm : Even (orderOf (a * b))) :
    ∃ k : ℤ, a * (a * b) ^ (orderOf (a * b) / 2) = (a * b) ^ k * a * ((a * b) ^ k)⁻¹ ∨
      a * (a * b) ^ (orderOf (a * b) / 2) = (a * b) ^ k * b * ((a * b) ^ k)⁻¹ := by
  set r := a * b with hr
  set m := orderOf r with hmdef
  have hme : Even m := by simpa [hmdef] using hm
  have ha' : a * a = 1 := by simpa [pow_two] using ha
  have hb' : b * b = 1 := by simpa [pow_two] using hb
  have hra : a * r * a⁻¹ = r⁻¹ := by
    rw [hr, mul_inv_rev, inv_eq_of_mul_eq_one_right ha',
      inv_eq_of_mul_eq_one_right hb']
    calc a * (a * b) * a = (a * a) * b * a := by group
      _ = b * a := by rw [ha', one_mul]
  have hrb : b * r * b⁻¹ = r⁻¹ := by
    rw [hr, mul_inv_rev, inv_eq_of_mul_eq_one_right ha',
      inv_eq_of_mul_eq_one_right hb']
    calc b * (a * b) * b = b * a * (b * b) := by group
      _ = b * a := by rw [hb', mul_one]
  have hconja : ∀ j : ℤ, a * r ^ j = r ^ (-j) * a := by
    intro j
    have h := conj_zpow (a := a) (b := r) (i := j)
    rw [hra, inv_zpow'] at h
    calc a * r ^ j = (a * r ^ j * a⁻¹) * a := by group
      _ = r ^ (-j) * a := by rw [← h]
  have hconjb : ∀ j : ℤ, b * r ^ j = r ^ (-j) * b := by
    intro j
    have h := conj_zpow (a := b) (b := r) (i := j)
    rw [hrb, inv_zpow'] at h
    calc b * r ^ j = (b * r ^ j * b⁻¹) * b := by group
      _ = r ^ (-j) * b := by rw [← h]
  have hza : ∀ j : ℤ, r ^ j * a = a * r ^ (-j) := by
    intro j
    simpa using (hconja (-j)).symm
  have hzb : ∀ j : ℤ, r ^ j * b = b * r ^ (-j) := by
    intro j
    simpa using (hconjb (-j)).symm
  have hzsq : (r ^ (m / 2)) * (r ^ (m / 2)) = 1 := by
    rw [← pow_add]
    have hhalf : m / 2 + m / 2 = m := by
      obtain ⟨t, ht⟩ := hme
      have hm2t : m = 2 * t := by omega
      have hm2 : m / 2 = t := by rw [hm2t, Nat.mul_div_right t (by norm_num)]
      omega
    rw [hhalf, hmdef, pow_orderOf_eq_one]
  have hzinv : r ^ (-((m / 2 : ℕ) : ℤ)) = r ^ (m / 2) := by
    rw [zpow_neg, zpow_natCast]
    exact inv_eq_of_mul_eq_one_right hzsq
  by_cases h4 : 4 ∣ m
  · have hquarter : m / 2 = 2 * (m / 4) := by
      calc m / 2 = (4 * (m / 4)) / 2 := by rw [Nat.mul_div_cancel' h4]
        _ = 4 / 2 * (m / 4) := Nat.mul_div_right_comm (by norm_num : 2 ∣ 4) (m / 4)
        _ = 2 * (m / 4) := by norm_num
    refine ⟨((m / 4 : ℕ) : ℤ), Or.inl ?_⟩
    have hk : (2 : ℤ) * ((m / 4 : ℕ) : ℤ) = ((m / 2 : ℕ) : ℤ) := by
      rw [hquarter]
      push_cast
      ring
    rw [hza, ← zpow_neg, mul_assoc, ← zpow_add]
    have hexp : -((m / 4 : ℕ) : ℤ) + -((m / 4 : ℕ) : ℤ) =
        -((m / 2 : ℕ) : ℤ) := by
      rw [← hk]
      ring
    rw [hexp, hzinv]
  · obtain ⟨t, ht⟩ := hme
    have hm2t : m = 2 * t := by omega
    have htodd : Odd t := by
      by_contra hto
      have hte : Even t := Nat.not_odd_iff_even.mp hto
      obtain ⟨u, hu⟩ := hte
      exact h4 (by use u; omega)
    have hm2 : m / 2 = t := by rw [hm2t, Nat.mul_div_right t (by norm_num)]
    have ht_eq : t / 2 * 2 + 1 = t := Nat.div_two_mul_two_add_one_of_odd htodd
    have ht_succ : 2 * (t / 2 + 1) = t + 1 := by
      rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm 2 (t / 2)]
      omega
    have hk_eq : (t + 1) / 2 = t / 2 + 1 := by
      rw [← ht_succ]
      exact Nat.mul_div_right (t / 2 + 1) (by norm_num)
    have h2k_nat : 2 * ((t + 1) / 2) - 1 = t := by
      rw [hk_eq]
      omega
    have h2k_int : (2 : ℤ) * (((t + 1) / 2 : ℕ) : ℤ) - 1 = (t : ℤ) := by
      have hsucc : 2 * ((t + 1) / 2) = t + 1 := by omega
      have h := congrArg (fun n : ℕ => (n : ℤ)) hsucc
      push_cast at h
      omega
    have hk : (2 : ℤ) * (((m / 2 + 1) / 2 : ℕ) : ℤ) - 1 = ((m / 2 : ℕ) : ℤ) := by
      rw [hm2]
      exact h2k_int
    refine ⟨(((m / 2 + 1) / 2 : ℕ) : ℤ), Or.inr ?_⟩
    rw [hzb, ← zpow_neg, mul_assoc, ← zpow_add]
    have hb_eq : b = a * r := by
      rw [hr]
      calc b = (a * a) * b := by rw [ha', one_mul]
        _ = a * (a * b) := by group
    rw [hb_eq, mul_assoc, mul_self_zpow]
    have hexp : -(((m / 2 + 1) / 2 : ℕ) : ℤ) +
        -(((m / 2 + 1) / 2 : ℕ) : ℤ) + 1 = -((m / 2 : ℕ) : ℤ) := by
      omega
    rw [hexp, hzinv]

theorem odd_or_le_two_of_inf_commV_eq_bot [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {G : Subgroup (MulAut V)} {a : MulAut V} (haG : a ∈ G) (ha : a ^ 2 = 1)
    (hdisj : ∀ h ∈ G, h * a * h⁻¹ * a = a * (h * a * h⁻¹) → h * a * h⁻¹ ≠ a →
      commV (zpowers a) ⊓ commV (zpowers (h * a * h⁻¹)) = ⊥)
    {g : MulAut V} (hg : g ∈ G) :
    Odd (orderOf (a * (g * a * g⁻¹))) ∨ orderOf (a * (g * a * g⁻¹)) ≤ 2 := by
  by_contra hcon
  have hodd : ¬ Odd (orderOf (a * (g * a * g⁻¹))) := fun ho => hcon (Or.inl ho)
  have hle : ¬ orderOf (a * (g * a * g⁻¹)) ≤ 2 := fun hl => hcon (Or.inr hl)
  set b := g * a * g⁻¹ with hbdef
  set m := orderOf (a * b) with hmdef
  have hodd' : ¬ Odd m := by simpa [hmdef, hbdef] using hodd
  have hle' : ¬ m ≤ 2 := by simpa [hmdef, hbdef] using hle
  have hme : Even m := Nat.not_odd_iff_even.mp hodd'
  have ha' : a * a = 1 := by simpa [pow_two] using ha
  have hb' : b * b = 1 := by
    rw [hbdef]
    calc (g * a * g⁻¹) * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
      _ = 1 := by rw [ha']; simp
  have hbG : b ∈ G := by
    rw [hbdef]
    exact G.mul_mem (G.mul_mem hg haG) (G.inv_mem hg)
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · exact absurd (by rw [h0]; norm_num) hle'
    · exact hpos
  have hm4 : 4 ≤ m := by
    obtain ⟨t, ht⟩ := hme
    have hm2t : m = 2 * t := by omega
    omega
  set z := (a * b) ^ (m / 2) with hzdef
  have hzsq : z * z = 1 := by
    rw [hzdef, ← pow_add]
    obtain ⟨t, ht⟩ := hme
    have hm2t : m = 2 * t := by omega
    have hhalf : m / 2 + m / 2 = m := by
      have hm2t' : m / 2 = t := by rw [hm2t, Nat.mul_div_right t (by norm_num)]
      omega
    rw [hhalf, hmdef, pow_orderOf_eq_one]
  have hz1 : z ≠ 1 := by
    rw [hzdef]
    refine pow_ne_one_of_lt_orderOf (x := a * b) (n := m / 2) ?_ ?_
    · omega
    · rw [← hmdef]
      omega
  have hzord : orderOf z = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hzsq) hz1
  have hra : a * (a * b) * a⁻¹ = (a * b)⁻¹ := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ha',
      inv_eq_of_mul_eq_one_right hb']
    calc a * (a * b) * a = (a * a) * b * a := by group
      _ = b * a := by rw [ha', one_mul]
  have hrb : b * (a * b) * b⁻¹ = (a * b)⁻¹ := by
    calc b * (a * b) * b⁻¹ = b * a := by group
      _ = (a * b)⁻¹ := by
        rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ha',
          inv_eq_of_mul_eq_one_right hb']
  have hconja : ∀ j : ℤ, a * (a * b) ^ j = (a * b) ^ (-j) * a := by
    intro j
    have h := conj_zpow (a := a) (b := a * b) (i := j)
    rw [hra, inv_zpow'] at h
    calc a * (a * b) ^ j = (a * (a * b) ^ j * a⁻¹) * a := by group
      _ = (a * b) ^ (-j) * a := by rw [← h]
  have hconjb : ∀ j : ℤ, b * (a * b) ^ j = (a * b) ^ (-j) * b := by
    intro j
    have h := conj_zpow (a := b) (b := a * b) (i := j)
    rw [hrb, inv_zpow'] at h
    calc b * (a * b) ^ j = (b * (a * b) ^ j * b⁻¹) * b := by group
      _ = (a * b) ^ (-j) * b := by rw [← h]
  have haz : a * z = z * a := by
    have hzz : z = (a * b) ^ ((m / 2 : ℕ) : ℤ) := by rw [hzdef, zpow_natCast]
    calc a * z = a * (a * b) ^ ((m / 2 : ℕ) : ℤ) := by rw [hzz]
      _ = (a * b) ^ (-((m / 2 : ℕ) : ℤ)) * a := hconja _
      _ = ((a * b) ^ ((m / 2 : ℕ) : ℤ))⁻¹ * a := by rw [zpow_neg]
      _ = z⁻¹ * a := by rw [← hzz]
      _ = z * a := by rw [inv_eq_of_mul_eq_one_right hzsq]
  have hbz : b * z = z * b := by
    have hzz : z = (a * b) ^ ((m / 2 : ℕ) : ℤ) := by rw [hzdef, zpow_natCast]
    calc b * z = b * (a * b) ^ ((m / 2 : ℕ) : ℤ) := by rw [hzz]
      _ = (a * b) ^ (-((m / 2 : ℕ) : ℤ)) * b := hconjb _
      _ = ((a * b) ^ ((m / 2 : ℕ) : ℤ))⁻¹ * b := by rw [zpow_neg]
      _ = z⁻¹ * b := by rw [← hzz]
      _ = z * b := by rw [inv_eq_of_mul_eq_one_right hzsq]
  have hazne : a * z ≠ a := by
    intro h
    exact hz1 (mul_left_cancel (h.trans (mul_one a).symm))
  have hbzne : b * z ≠ b := by
    intro h
    exact hz1 (mul_left_cancel (h.trans (mul_one b).symm))
  have hdisja : commV (zpowers a) ⊓ commV (zpowers (a * z)) = ⊥ := by
    obtain ⟨k, hk | hk⟩ :=
      exists_conj_mul_pow_half (G := MulAut V) ha (by rw [pow_two]; exact hb')
        (by rw [← hmdef]; exact hme)
    · have hkG : (a * b) ^ k ∈ G := G.zpow_mem (G.mul_mem haG hbG) k
      have hcomm : ((a * b) ^ k * a * ((a * b) ^ k)⁻¹) * a =
          a * ((a * b) ^ k * a * ((a * b) ^ k)⁻¹) := by
        rw [← hk]
        calc (a * z) * a = a * (z * a) := by group
          _ = a * (a * z) := by rw [haz]
      have hne : (a * b) ^ k * a * ((a * b) ^ k)⁻¹ ≠ a := by
        rw [← hk]
        exact hazne
      have hres := hdisj ((a * b) ^ k) hkG hcomm hne
      rwa [← hk] at hres
    · have hkG : (a * b) ^ k * g ∈ G :=
        G.mul_mem (G.zpow_mem (G.mul_mem haG hbG) k) hg
      have heq : ((a * b) ^ k * g) * a * ((a * b) ^ k * g)⁻¹ =
          (a * b) ^ k * b * ((a * b) ^ k)⁻¹ := by
        rw [hbdef]
        group
      have hcomm : ((a * b) ^ k * g) * a * ((a * b) ^ k * g)⁻¹ * a =
          a * (((a * b) ^ k * g) * a * ((a * b) ^ k * g)⁻¹) := by
        rw [heq, ← hk]
        calc (a * z) * a = a * (z * a) := by group
          _ = a * (a * z) := by rw [haz]
      have hne : ((a * b) ^ k * g) * a * ((a * b) ^ k * g)⁻¹ ≠ a := by
        rw [heq, ← hk]
        exact hazne
      have hres := hdisj ((a * b) ^ k * g) hkG hcomm hne
      rw [heq, ← hk] at hres
      exact hres
  have hbainv : (a * b) * (b * a) = 1 := by
    calc (a * b) * (b * a) = a * (b * b) * a := by group
      _ = a * 1 * a := by rw [hb']
      _ = a * a := by rw [mul_one]
      _ = 1 := ha'
  have hba : b * a = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right hbainv).symm
  have hordba : orderOf (b * a) = m := by rw [hba, orderOf_inv, hmdef]
  have hzba : (b * a) ^ (orderOf (b * a) / 2) = z := by
    rw [hordba, hba, inv_pow, ← hzdef, inv_eq_of_mul_eq_one_right hzsq]
  have transport : ∀ (q gq : MulAut V), q ∈ G → gq ∈ G →
      b * z = q * (gq * a * gq⁻¹) * q⁻¹ →
      commV (zpowers b) ⊓ commV (zpowers (b * z)) = ⊥ := by
    intro q gq hq hgq heq
    have h0G : g⁻¹ * q * gq ∈ G :=
      G.mul_mem (G.mul_mem (G.inv_mem hg) hq) hgq
    have hconj : (g⁻¹ * q * gq) * a * (g⁻¹ * q * gq)⁻¹ = g⁻¹ * (b * z) * g := by
      rw [heq]
      group
    have hbga : g⁻¹ * b * g = a := by rw [hbdef]; group
    have hbz_comm : (b * z) * b = b * (b * z) := by
      have hleft : (b * z) * b = z * (b * b) := by rw [hbz, mul_assoc]
      have hright : b * (b * z) = z * (b * b) := by
        calc b * (b * z) = b * (z * b) := by rw [hbz]
          _ = (b * z) * b := by rw [← mul_assoc]
          _ = (z * b) * b := by rw [hbz]
          _ = z * (b * b) := by rw [mul_assoc]
      rw [hleft, hright]
    have hcomm : (g⁻¹ * q * gq) * a * (g⁻¹ * q * gq)⁻¹ * a =
        a * ((g⁻¹ * q * gq) * a * (g⁻¹ * q * gq)⁻¹) := by
      rw [hconj]
      calc (g⁻¹ * (b * z) * g) * a
          = (g⁻¹ * (b * z) * g) * (g⁻¹ * b * g) := by rw [hbga]
        _ = g⁻¹ * ((b * z) * b) * g := by group
        _ = g⁻¹ * (b * (b * z)) * g := by rw [hbz_comm]
        _ = (g⁻¹ * b * g) * (g⁻¹ * (b * z) * g) := by group
        _ = a * (g⁻¹ * (b * z) * g) := by rw [hbga]
    have hne : (g⁻¹ * q * gq) * a * (g⁻¹ * q * gq)⁻¹ ≠ a := by
      rw [hconj]
      intro h
      apply hbzne
      have := congrArg (fun x : MulAut V => g * x * g⁻¹) h
      simpa [hbdef, mul_assoc] using this
    have hinf := hdisj (g⁻¹ * q * gq) h0G hcomm hne
    have hmap := congrArg (fun S : Subgroup V => S.map g.toMonoidHom) hinf
    rw [Subgroup.map_inf_eq _ _ g.toMonoidHom g.injective, Subgroup.map_bot] at hmap
    rw [hconj] at hmap
    rw [← commV_zpowers_conj_eq a g,
      ← commV_zpowers_conj_eq (g⁻¹ * (b * z) * g) g] at hmap
    have hga : g * a * g⁻¹ = b := by rw [hbdef]
    have hgz : g * (g⁻¹ * (b * z) * g) * g⁻¹ = b * z := by group
    simpa [hga, hgz] using hmap
  have hdisjb : commV (zpowers b) ⊓ commV (zpowers (b * z)) = ⊥ := by
    obtain ⟨k, hk | hk⟩ :=
      exists_conj_mul_pow_half (G := MulAut V) (by rw [pow_two]; exact hb') ha
        (by rw [hordba]; exact hme)
    · rw [hzba] at hk
      have hqG : (b * a) ^ k ∈ G := G.zpow_mem (G.mul_mem hbG haG) k
      exact transport ((b * a) ^ k) g hqG hg (by rw [← hbdef]; exact hk)
    · rw [hzba] at hk
      have hqG : (b * a) ^ k ∈ G := G.zpow_mem (G.mul_mem hbG haG) k
      exact transport ((b * a) ^ k) 1 hqG G.one_mem (by simpa using hk)
  exact false_of_inf_commV_eq_bot (V := V) hV hme hm4 hdisja hdisjb

end CFSG.LocalAnalysis.WeakClosure81.Asch6

end
