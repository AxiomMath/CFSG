module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Quasithin.H13.S126Y

variable {Y : Type*} [Group Y]

theorem pow_eq_pow_mod_five {y : Y} (hy : y ^ 5 = 1) (n : ℕ) : y ^ n = y ^ (n % 5) := by
  conv_lhs => rw [← Nat.mod_add_div n 5, pow_add, pow_mul, hy, one_pow, mul_one]

theorem fix_of_card_five [Finite Y] (W : Subgroup Y) (hW : Nat.card W = 5) (τ : MulAut Y)
    (hτW : ∀ w ∈ W, τ w ∈ W) (hτ3 : τ ^ 3 = 1) : ∀ w ∈ W, τ w = w := by
  have hW5 : ∀ w ∈ W, w ^ 5 = 1 := fun w hw => by
    have := pow_card_eq_one' (G := ↥W) (x := ⟨w, hw⟩)
    rw [hW] at this
    simpa using congrArg Subtype.val this
  intro w hw
  by_cases hw1 : w = 1
  · rw [hw1, map_one]
  have hcyc : IsCyclic ↥W := isCyclic_of_prime_card (p := 5) (hp := ⟨by norm_num⟩) hW
  have hord : orderOf w = 5 := by
    have h1 : orderOf w ∣ 5 := orderOf_dvd_of_pow_eq_one (hW5 w hw)
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hw1
    · exact h
  have hgen : W = Subgroup.zpowers w := by
    refine (Subgroup.eq_of_le_of_card_ge ?_ ?_).symm
    · rw [Subgroup.zpowers_le]
      exact hw
    · rw [hW, Nat.card_zpowers, hord]
  have hτw : τ w ∈ Subgroup.zpowers w := hgen ▸ hτW w hw
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hτw
  obtain ⟨m, hm⟩ : ∃ m : ℕ, τ w = w ^ m := by
    refine ⟨(k % 5).toNat, ?_⟩
    rw [← hk, ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))]
    exact zpow_eq_zpow_emod' k (hW5 w hw)
  have hτn : ∀ n : ℕ, τ (w ^ n) = w ^ (m * n) := fun n => by rw [map_pow, hm, pow_mul]
  have h3 : (τ ^ 3) w = w ^ (m * (m * m)) := by
    simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply]
    rw [hm, hτn, hτn]
  rw [hτ3, MulAut.one_apply] at h3
  have h4 : w ^ (m * (m * m) % 5) = w ^ 1 := by
    rw [← pow_eq_pow_mod_five (hW5 w hw), ← h3, pow_one]
  have hm5 : m % 5 = 1 := by
    have h5 := pow_injOn_Iio_orderOf (x := w)
    rw [hord] at h5
    have := h5 (Set.mem_Iio.mpr (Nat.mod_lt _ (by norm_num))) (Set.mem_Iio.mpr (by norm_num)) h4
    have hmm : m * (m * m) % 5 = (m % 5) * ((m % 5) * (m % 5)) % 5 := by
      simp [Nat.mul_mod]
    rw [hmm] at this
    have key : ∀ r : ℕ, r < 5 → r * (r * r) % 5 = 1 → r = 1 := by decide
    exact key _ (Nat.mod_lt _ (by norm_num)) this
  rw [hm, pow_eq_pow_mod_five (hW5 w hw), hm5, pow_one]

theorem card_eq_five_of [Finite Y] (hcard : Nat.card Y = 25) {W : Subgroup Y} (hbot : W ≠ ⊥)
    (htop : W ≠ ⊤) : Nat.card W = 5 := by
  have hdvd : Nat.card W ∣ 5 ^ 2 := by
    have := Subgroup.card_subgroup_dvd_card W
    rw [hcard] at this
    exact this
  obtain ⟨k, hk, hWk⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 5)).mp hdvd
  have hk0 : k ≠ 0 := fun h0 => hbot (Subgroup.card_eq_one.mp (by rw [hWk, h0, pow_zero]))
  have hk2 : k ≠ 2 := fun h2 => htop (Subgroup.card_eq_iff_eq_top W |>.mp
    (by rw [hWk, h2, hcard]; norm_num))
  have : k = 1 := by omega
  rw [hWk, this, pow_one]

theorem inv_of_comm [Finite Y] (hcomm : ∀ a b : Y, a * b = b * a) (hcard : Nat.card Y = 25)
    (hexp : ∀ y : Y, y ^ 5 = 1) (τ σ : MulAut Y) (hτ3 : τ ^ 3 = 1) (hσ2 : σ ^ 2 = 1)
    (hτσ : τ * σ = σ * τ) (hτ : ∃ y, τ y ≠ y) (hσ : ∃ y, σ y ≠ y) : ∀ y, σ y = y⁻¹ := by
  have hσσ : ∀ y, σ (σ y) = y := fun y => by
    rw [← MulAut.mul_apply, ← pow_two, hσ2, MulAut.one_apply]
  have hτσy : ∀ y, τ (σ y) = σ (τ y) := fun y => by
    rw [← MulAut.mul_apply, hτσ, MulAut.mul_apply]
  let Wp : Subgroup Y :=
    { carrier := {y | σ y = y}
      one_mem' := map_one σ
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [map_mul, ha, hb]
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_ofPred_eq] at ha ⊢
        rw [map_inv, ha] }
  let Wm : Subgroup Y :=
    { carrier := {y | σ y = y⁻¹}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [map_mul, ha, hb, mul_inv_rev, hcomm]
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_ofPred_eq] at ha ⊢
        rw [map_inv, ha] }
  have hWp : ∀ y, y ∈ Wp ↔ σ y = y := fun y => Iff.rfl
  have hWm : ∀ y, y ∈ Wm ↔ σ y = y⁻¹ := fun y => Iff.rfl
  have hone : ∀ y, y ∈ Wp → y ∈ Wm → y = 1 := by
    intro y hp hm
    rw [hWp] at hp
    rw [hWm, hp] at hm
    have h2 : y * y = 1 := by rw [mul_eq_one_iff_eq_inv]; exact hm
    calc y = y * y ^ 5 := by rw [hexp, mul_one]
      _ = (y * y) * (y * y) * (y * y) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := by rw [h2, one_mul, one_mul]
  have hdec : ∀ y, ∃ a ∈ Wp, ∃ b ∈ Wm, y = a * b := by
    intro y
    refine ⟨(y * σ y) ^ 3, ?_, (y * (σ y)⁻¹) ^ 3, ?_, ?_⟩
    · rw [hWp, map_pow, map_mul, hσσ, hcomm (σ y) y]
    · rw [hWm, map_pow, map_mul, map_inv, hσσ, ← inv_pow, mul_inv_rev, inv_inv]
    · rw [← (Commute.mul_pow (hcomm _ _) 3)]
      have e : y * σ y * (y * (σ y)⁻¹) = y * y := by
        calc y * σ y * (y * (σ y)⁻¹) = y * (σ y * y) * (σ y)⁻¹ := by group
          _ = y * (y * σ y) * (σ y)⁻¹ := by rw [hcomm (σ y) y]
          _ = y * y := by group
      rw [e]
      calc y = y * y ^ 5 := by rw [hexp, mul_one]
        _ = (y * y) ^ 3 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  have hτWp : ∀ y ∈ Wp, τ y ∈ Wp := fun y hy => by
    rw [hWp] at hy ⊢
    rw [← hτσy, hy]
  have hτWm : ∀ y ∈ Wm, τ y ∈ Wm := fun y hy => by
    rw [hWm] at hy ⊢
    rw [← hτσy, hy, map_inv]
  by_contra hnot
  push Not at hnot
  obtain ⟨y₁, hy₁⟩ := hnot
  obtain ⟨y₂, hy₂⟩ := hσ
  have hpbot : Wp ≠ ⊥ := by
    intro hb
    obtain ⟨a, ha, b, hb', rfl⟩ := hdec y₁
    have : a = 1 := by rw [hb] at ha; exact ha
    rw [this, one_mul] at hy₁
    exact hy₁ hb'
  have hmbot : Wm ≠ ⊥ := by
    intro hb
    obtain ⟨a, ha, b, hb', rfl⟩ := hdec y₂
    have : b = 1 := by rw [hb] at hb'; exact hb'
    rw [this, mul_one] at hy₂
    exact hy₂ ha
  have hptop : Wp ≠ ⊤ := by
    intro ht
    obtain ⟨b, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hmbot
    exact hb1 (Subtype.ext (hone b (ht ▸ Subgroup.mem_top _) b.2))
  have hmtop : Wm ≠ ⊤ := by
    intro ht
    obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hpbot
    exact ha1 (Subtype.ext (hone a a.2 (ht ▸ Subgroup.mem_top _)))
  have hfp := fix_of_card_five Wp (card_eq_five_of hcard hpbot hptop) τ hτWp hτ3
  have hfm := fix_of_card_five Wm (card_eq_five_of hcard hmbot hmtop) τ hτWm hτ3
  obtain ⟨y, hy⟩ := hτ
  obtain ⟨a, ha, b, hb, rfl⟩ := hdec y
  exact hy (by rw [map_mul, hfp a ha, hfm b hb])

theorem zpowers_eq_of_mem [Finite Y] {z c : Y} (hz5 : orderOf z = 5) (hc : c ∈ Subgroup.zpowers z)
    (hc1 : c ≠ 1) : Subgroup.zpowers c = Subgroup.zpowers z := by
  have hc5 : c ^ 5 = 1 := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hz5, pow_orderOf_eq_one,
      one_zpow]
  have hco : orderOf c = 5 := by
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp (orderOf_dvd_of_pow_eq_one hc5) with
      h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hc1
    · exact h
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hc) ?_
  rw [Nat.card_zpowers, Nat.card_zpowers, hz5, hco]

theorem exists_conj_mul [Finite Y] {z : Y} (hzc : ∀ x, z * x = x * z) (hz5 : orderOf z = 5)
    (hcomm : ∀ a b : Y, a * b * a⁻¹ * b⁻¹ ∈ Subgroup.zpowers z) {y : Y}
    (hy : ¬ ∀ x, y * x = x * y) (j : ℕ) : ∃ x : Y, x * y * x⁻¹ = z ^ j * y := by
  push Not at hy
  obtain ⟨x₀, hx₀⟩ := hy
  have hc := hcomm x₀ y
  generalize hcdef : x₀ * y * x₀⁻¹ * y⁻¹ = c at hc
  have hc1 : c ≠ 1 := by
    intro h1
    apply hx₀
    rw [← hcdef] at h1
    calc y * x₀ = (x₀ * y * x₀⁻¹ * y⁻¹)⁻¹ * (x₀ * y) := by group
      _ = x₀ * y := by rw [h1, inv_one, one_mul]
  have hcc : ∀ x, c * x = x * c := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    intro x
    exact ((Commute.zpow_left (show Commute z x from hzc x) k)).eq
  have hconj : ∀ n : ℕ, x₀ ^ n * y * (x₀ ^ n)⁻¹ = c ^ n * y := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hx : x₀ * y * x₀⁻¹ = c * y := by rw [← hcdef]; group
      calc x₀ ^ (n + 1) * y * (x₀ ^ (n + 1))⁻¹ = x₀ * (x₀ ^ n * y * (x₀ ^ n)⁻¹) * x₀⁻¹ := by
            rw [pow_succ']
            group
        _ = x₀ * (c ^ n * y) * x₀⁻¹ := by rw [ih]
        _ = c ^ n * (x₀ * y * x₀⁻¹) := by
            rw [show x₀ * (c ^ n * y) * x₀⁻¹ = (x₀ * c ^ n) * y * x₀⁻¹ by group,
              ← (Commute.pow_left (show Commute c x₀ from hcc x₀) n).eq]
            group
        _ = c ^ (n + 1) * y := by rw [hx, pow_succ]; group
  have hzj : z ^ j ∈ Subgroup.zpowers c := by
    rw [zpowers_eq_of_mem hz5 hc hc1]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers z) j
  have hfin : IsOfFinOrder c := by
    have hc5 : c ^ 5 = 1 := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hz5,
        pow_orderOf_eq_one, one_zpow]
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨5, by norm_num, hc5⟩
  obtain ⟨m, hm⟩ := (hfin.mem_powers_iff_mem_zpowers).mpr hzj
  exact ⟨x₀ ^ m, by rw [hconj]; exact congrArg (· * y) hm⟩

theorem eq_of_triv_mod [Finite Y] {z : Y} (hzc : ∀ x, z * x = x * z) (hz5 : orderOf z = 5)
    (hcomm : ∀ a b : Y, a * b * a⁻¹ * b⁻¹ ∈ Subgroup.zpowers z) (hnab : ∃ a b : Y, a * b ≠ b * a)
    (σ : MulAut Y) (hσ2 : σ ^ 2 = 1) (hmod : ∀ y, y⁻¹ * σ y ∈ Subgroup.zpowers z) :
    ∀ y, σ y = y := by
  have hcen : ∀ c ∈ Subgroup.zpowers z, ∀ x, c * x = x * c := by
    intro c hc x
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    exact ((Commute.zpow_left (show Commute z x from hzc x) k)).eq
  have hσy : ∀ y, σ y = y * (y⁻¹ * σ y) := fun y => by group
  have key : ∀ (a b u w : Y), u ∈ Subgroup.zpowers z → w ∈ Subgroup.zpowers z →
      a * u * (b * w) * (a * u)⁻¹ * (b * w)⁻¹ = a * b * a⁻¹ * b⁻¹ := by
    intro a b u w hu hw
    have hu' := hcen u hu
    have hw' := hcen w hw
    calc a * u * (b * w) * (a * u)⁻¹ * (b * w)⁻¹ =
        a * (u * b) * w * u⁻¹ * a⁻¹ * w⁻¹ * b⁻¹ := by group
      _ = a * (b * u) * w * u⁻¹ * a⁻¹ * w⁻¹ * b⁻¹ := by rw [hu' b]
      _ = a * b * (u * w * u⁻¹) * a⁻¹ * w⁻¹ * b⁻¹ := by group
      _ = a * b * w * a⁻¹ * w⁻¹ * b⁻¹ := by rw [hu' w, mul_inv_cancel_right]
      _ = a * b * (w * a⁻¹) * w⁻¹ * b⁻¹ := by group
      _ = a * b * (a⁻¹ * w) * w⁻¹ * b⁻¹ := by rw [hw' a⁻¹]
      _ = a * b * a⁻¹ * b⁻¹ := by group
  have hσc : ∀ a b : Y, σ (a * b * a⁻¹ * b⁻¹) = a * b * a⁻¹ * b⁻¹ := by
    intro a b
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hσy a, hσy b]
    exact key a b _ _ (hmod a) (hmod b)
  obtain ⟨a, b, hab⟩ := hnab
  have hc1 : a * b * a⁻¹ * b⁻¹ ≠ 1 := by
    intro h1
    apply hab
    calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
      _ = b * a := by rw [h1, one_mul]
  have hzc0 : z ∈ Subgroup.zpowers (a * b * a⁻¹ * b⁻¹) := by
    rw [zpowers_eq_of_mem hz5 (hcomm a b) hc1]
    exact Subgroup.mem_zpowers z
  have hσz : ∀ c ∈ Subgroup.zpowers z, σ c = c := by
    have hz : σ z = z := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hzc0
      rw [← hk, map_zpow, hσc]
    intro c hc
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    rw [map_zpow, hz]
  intro y
  have hzy := hmod y
  generalize hzdef : y⁻¹ * σ y = zy at hzy
  have hσy' : σ y = y * zy := by rw [← hzdef]; group
  have h2 : (σ ^ 2) y = y * (zy * zy) := by
    rw [pow_two, MulAut.mul_apply, hσy', map_mul, hσy', hσz zy hzy, mul_assoc]
  rw [hσ2, MulAut.one_apply] at h2
  have hzz : zy * zy = 1 := by
    have := congrArg (fun x => y⁻¹ * x) h2
    simpa using this.symm
  have hz5' : zy ^ 5 = 1 := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hzy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hz5,
      pow_orderOf_eq_one, one_zpow]
  have hzy1 : zy = 1 := by
    calc zy = zy ^ 5 * (zy * zy)⁻¹ * (zy * zy)⁻¹ := by group
      _ = 1 := by rw [hz5', hzz, inv_one, one_mul, one_mul]
  rw [hσy', hzy1, mul_one]

@[expose] def e25Hom {K : Type*} [Group K] (y z : K) (hy : y ^ 5 = 1) (hz : z ^ 5 = 1)
    (hyz : y * z = z * y) : Multiplicative (ZMod 5 × ZMod 5) →* K where
  toFun g := y ^ (Multiplicative.toAdd g).1.val * z ^ (Multiplicative.toAdd g).2.val
  map_one' := by simp
  map_mul' g g' := by
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, ZMod.val_add]
    rw [← pow_eq_pow_mod_five hy, ← pow_eq_pow_mod_five hz, pow_add, pow_add]
    have hc : Commute (z ^ (Multiplicative.toAdd g).2.val) (y ^ (Multiplicative.toAdd g').1.val) :=
      (Commute.pow_pow (show Commute z y from hyz.symm) _ _)
    calc y ^ (Multiplicative.toAdd g).1.val * y ^ (Multiplicative.toAdd g').1.val *
          (z ^ (Multiplicative.toAdd g).2.val * z ^ (Multiplicative.toAdd g').2.val) =
        y ^ (Multiplicative.toAdd g).1.val *
          (y ^ (Multiplicative.toAdd g').1.val * z ^ (Multiplicative.toAdd g).2.val) *
          z ^ (Multiplicative.toAdd g').2.val := by group
      _ = y ^ (Multiplicative.toAdd g).1.val *
          (z ^ (Multiplicative.toAdd g).2.val * y ^ (Multiplicative.toAdd g').1.val) *
          z ^ (Multiplicative.toAdd g').2.val := by rw [hc.eq]
      _ = _ := by group

theorem e25Hom_apply {K : Type*} [Group K] {y z : K} (hy : y ^ 5 = 1) (hz : z ^ 5 = 1)
    (hyz : y * z = z * y) (g : Multiplicative (ZMod 5 × ZMod 5)) :
    e25Hom y z hy hz hyz g =
      y ^ (Multiplicative.toAdd g).1.val * z ^ (Multiplicative.toAdd g).2.val :=
  rfl

end CFSG.Quasithin.H13.S126Y
