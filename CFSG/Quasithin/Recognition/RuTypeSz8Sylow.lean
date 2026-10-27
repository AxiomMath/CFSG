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

namespace CFSG.Quasithin.RuType

section Aut

variable {G : Type*} [Group G]

@[expose] def conjAutN (Y : Subgroup G) (g : Subgroup.normalizer (Y : Set G)) : MulAut Y where
  toFun y := ⟨g * y * (g : G)⁻¹, (Subgroup.mem_normalizer_iff.mp g.2 y).mp y.2⟩
  invFun y := ⟨(g : G)⁻¹ * y * g, by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem g.2) y).mp y.2
    simpa using this⟩
  left_inv y := Subtype.ext (by simp only; group)
  right_inv y := Subtype.ext (by simp only; group)
  map_mul' y y' := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

@[expose] def autNHom (Y : Subgroup G) : Subgroup.normalizer (Y : Set G) →* MulAut Y where
  toFun := conjAutN Y
  map_one' := MulEquiv.ext fun y => Subtype.ext (by simp [conjAutN])
  map_mul' g h := MulEquiv.ext fun y => Subtype.ext (by
    simp only [conjAutN, MulEquiv.coe_mk, Equiv.coe_fn_mk, MulAut.mul_apply, Subgroup.coe_mul,
      mul_inv_rev]
    group)

theorem autNHom_apply (Y : Subgroup G) (g : Subgroup.normalizer (Y : Set G)) (y : Y) :
    ((autNHom Y g y : Y) : G) = g * y * (g : G)⁻¹ := rfl

theorem mem_ker_autNHom {Y : Subgroup G} {g : Subgroup.normalizer (Y : Set G)} :
    g ∈ (autNHom Y).ker ↔ ∀ y ∈ Y, (g : G) * y = y * g := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h y hy
    have := congrArg (fun f : MulAut Y => ((f ⟨y, hy⟩ : Y) : G)) h
    simp only [autNHom_apply, MulAut.one_apply] at this
    calc (g : G) * y = ((g : G) * y * (g : G)⁻¹) * g := by group
      _ = y * g := by rw [this]
  · intro h
    apply MulEquiv.ext
    intro y
    apply Subtype.ext
    rw [autNHom_apply, h y y.2, mul_inv_cancel_right]
    rfl

theorem exists_card_normalizer [Finite G] (Y : Subgroup G) :
    ∃ r, r ∣ Nat.card (MulAut Y) ∧
      Nat.card (Subgroup.normalizer (Y : Set G)) =
        Nat.card (Subgroup.centralizer (Y : Set G)) * r := by
  refine ⟨Nat.card (autNHom Y).range, Subgroup.card_subgroup_dvd_card _, ?_⟩
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (autNHom Y).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (autNHom Y)).toEquiv] at h1
  rw [h1, mul_comm]
  congr 1
  refine Nat.card_congr
    { toFun := fun g => ⟨((g : Subgroup.normalizer (Y : Set G)) : G), ?_⟩
      invFun := fun c => ⟨⟨c, Subgroup.centralizer_le_normalizer _ c.2⟩, ?_⟩
      left_inv := fun g => rfl
      right_inv := fun c => rfl }
  · rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (mem_ker_autNHom.mp g.2 y hy).symm
  · rw [mem_ker_autNHom]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp c.2 y hy).symm

end Aut

namespace Sz8Sylow

variable {X : Type*} [Group X] [Finite X]

theorem odd_card_of_no_inv (C : Subgroup X) (h : ∀ u ∈ C, u ^ 2 = 1 → u = 1) :
    Odd (Nat.card C) := by
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  intro h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := C) 2 h2
  have h1 := h u u.2 (by
    have := congrArg Subtype.val (pow_orderOf_eq_one u)
    rw [hu] at this
    simpa using this)
  have : u = 1 := Subtype.ext h1
  rw [this, orderOf_one] at hu
  norm_num at hu

theorem card_sylow_of_prime {p : ℕ} [hp : Fact p.Prime] (P : Sylow p X) (m : ℕ)
    (hX : Nat.card X = p * m) (hm : ¬ p ∣ m) : Nat.card P = p := by
  rw [P.card_eq_multiplicity, hX, Nat.factorization_mul hp.out.ne_zero (by
    rintro rfl; exact hm (dvd_zero p))]
  simp [Nat.Prime.factorization_self hp.out, Nat.factorization_eq_zero_of_not_dvd hm]

theorem centralizer_no_inv {p : ℕ} [hp : Fact p.Prime] (P : Sylow p X) (hP : Nat.card P = p)
    (hinv : ∀ u y : X, u ^ 2 = 1 → u ≠ 1 → orderOf y = p → u * y ≠ y * u) :
    ∀ u ∈ Subgroup.centralizer (P : Set X), u ^ 2 = 1 → u = 1 := by
  intro u hu hu2
  by_contra hu1
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := P) p (by rw [hP])
  apply hinv u y hu2 hu1 (by rw [Subgroup.orderOf_coe]; exact hy)
  exact (Subgroup.mem_centralizer_iff.mp hu y y.2).symm

theorem normalizer_thirteen (hX : Nat.card X = 29120)
    (hinv : ∀ u y : X, u ^ 2 = 1 → u ≠ 1 → orderOf y = 13 → u * y ≠ y * u) (P : Sylow 13 X) :
    Nat.card (Subgroup.normalizer ((P : Subgroup X) : Set X)) = 52 ∧
      Subgroup.centralizer ((P : Subgroup X) : Set X) = P := by
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have hP : Nat.card P = 13 := card_sylow_of_prime P 2240 (by rw [hX]) (by norm_num)
  obtain ⟨r, hr, hN⟩ := exists_card_normalizer (P : Subgroup X)
  have hcyc : IsCyclic P := isCyclic_of_prime_card hP
  rw [IsCyclic.card_mulAut, hP, Nat.totient_prime (by norm_num)] at hr
  have hCodd := odd_card_of_no_inv _ (centralizer_no_inv P hP hinv)
  have hmod := card_sylow_modEq_one 13 X
  rw [Sylow.card_eq_index_normalizer P] at hmod
  have hidx := (Subgroup.normalizer ((P : Subgroup X) : Set X)).card_mul_index
  rw [hX] at hidx
  have h13 : 13 ∣ Nat.card (Subgroup.normalizer ((P : Subgroup X) : Set X)) := by
    have := Subgroup.card_dvd_of_le (Subgroup.le_normalizer (H := (P : Subgroup X)))
    rwa [hP] at this
  have h8 : ¬ 8 ∣ Nat.card (Subgroup.normalizer ((P : Subgroup X) : Set X)) := by
    rw [hN]
    intro h
    have hcop : Nat.Coprime 8 (Nat.card (Subgroup.centralizer ((P : Subgroup X) : Set X))) :=
      Nat.Coprime.pow_left 3 (Nat.coprime_two_left.mpr hCodd) |> fun h => by simpa using h
    have := hcop.dvd_of_dvd_mul_left h
    have := Nat.le_of_dvd (by norm_num) (this.trans hr)
    have h12 : ¬ 8 ∣ 12 := by norm_num
    exact h12 ((hcop.dvd_of_dvd_mul_left h).trans hr)
  have hdvd : Nat.card (Subgroup.normalizer ((P : Subgroup X) : Set X)) ∣ 29120 :=
    ⟨_, hidx.symm⟩
  have key : ∀ d ∈ Nat.divisors 29120, 13 ∣ d → ¬ 8 ∣ d → 29120 / d % 13 = 1 → d = 52 := by
    decide +kernel
  have hNc : Nat.card (Subgroup.normalizer ((P : Subgroup X) : Set X)) = 52 := by
    refine key _ (Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩) h13 h8 ?_
    have hpos : 0 < Nat.card (Subgroup.normalizer ((P : Subgroup X) : Set X)) := Nat.card_pos
    rw [← hidx, Nat.mul_div_cancel_left _ hpos]
    exact hmod
  refine ⟨hNc, ?_⟩
  have hPC : (P : Subgroup X) ≤ Subgroup.centralizer ((P : Subgroup X) : Set X) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have := hcyc
    exact congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨y, hy⟩ : P) ⟨x, hx⟩) |>
      fun h => by simpa using h
  have hCdvd : Nat.card (Subgroup.centralizer ((P : Subgroup X) : Set X)) ∣ 52 := by
    rw [← hNc, hN]
    exact dvd_mul_right _ _
  have hC13 : 13 ∣ Nat.card (Subgroup.centralizer ((P : Subgroup X) : Set X)) := by
    have := Subgroup.card_dvd_of_le hPC
    rwa [hP] at this
  have hCc : Nat.card (Subgroup.centralizer ((P : Subgroup X) : Set X)) = 13 := by
    have key2 : ∀ d ∈ Nat.divisors 52, 13 ∣ d → d % 2 = 1 → d = 13 := by decide +kernel
    exact key2 _ (Nat.mem_divisors.mpr ⟨hCdvd, by norm_num⟩) hC13 (Nat.odd_iff.mp hCodd)
  exact (Subgroup.eq_of_le_of_card_ge hPC (by rw [hCc, hP])).symm

theorem normalizer_seven (hX : Nat.card X = 29120)
    (hinv : ∀ u y : X, u ^ 2 = 1 → u ≠ 1 → orderOf y = 7 → u * y ≠ y * u)
    (h713 : ∀ y y' : X, orderOf y = 7 → orderOf y' = 13 → y * y' ≠ y' * y) (P : Sylow 7 X) :
    Nat.card (Subgroup.normalizer ((P : Subgroup X) : Set X)) = 14 ∧
      Subgroup.centralizer ((P : Subgroup X) : Set X) = P := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hP : Nat.card P = 7 := card_sylow_of_prime P 4160 (by rw [hX]) (by norm_num)
  obtain ⟨r, hr, hN⟩ := exists_card_normalizer (P : Subgroup X)
  have hcyc : IsCyclic P := isCyclic_of_prime_card hP
  rw [IsCyclic.card_mulAut, hP, Nat.totient_prime (by norm_num)] at hr
  have hCodd := odd_card_of_no_inv _ (centralizer_no_inv P hP hinv)
  have hmod := card_sylow_modEq_one 7 X
  rw [Sylow.card_eq_index_normalizer P] at hmod
  have hidx := (Subgroup.normalizer ((P : Subgroup X) : Set X)).card_mul_index
  rw [hX] at hidx
  have h7 : 7 ∣ Nat.card (Subgroup.normalizer ((P : Subgroup X) : Set X)) := by
    have := Subgroup.card_dvd_of_le (Subgroup.le_normalizer (H := (P : Subgroup X)))
    rwa [hP] at this
  have hcop4 : Nat.Coprime 4 (Nat.card (Subgroup.centralizer ((P : Subgroup X) : Set X))) := by
    have := Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hCodd)
    simpa using this
  have h4 : ¬ 4 ∣ Nat.card (Subgroup.normalizer ((P : Subgroup X) : Set X)) := by
    rw [hN]
    intro h
    have h6 : ¬ 4 ∣ 6 := by norm_num
    exact h6 ((hcop4.dvd_of_dvd_mul_left h).trans hr)
  have hdvd : Nat.card (Subgroup.normalizer ((P : Subgroup X) : Set X)) ∣ 29120 :=
    ⟨_, hidx.symm⟩
  have key : ∀ d ∈ Nat.divisors 29120, 7 ∣ d → ¬ 4 ∣ d → 29120 / d % 7 = 1 →
      d = 14 ∨ d = 455 := by
    decide +kernel
  have hpos : 0 < Nat.card (Subgroup.normalizer ((P : Subgroup X) : Set X)) := Nat.card_pos
  have hcases := key _ (Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩) h7 h4 (by
    rw [← hidx, Nat.mul_div_cancel_left _ hpos]
    exact hmod)
  have hPC : (P : Subgroup X) ≤ Subgroup.centralizer ((P : Subgroup X) : Set X) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨y, hy⟩ : P) ⟨x, hx⟩) |>
      fun h => by simpa using h
  have hC7 : 7 ∣ Nat.card (Subgroup.centralizer ((P : Subgroup X) : Set X)) := by
    have := Subgroup.card_dvd_of_le hPC
    rwa [hP] at this
  have hNc : Nat.card (Subgroup.normalizer ((P : Subgroup X) : Set X)) = 14 := by
    rcases hcases with h | h
    · exact h
    · exfalso
      rw [hN] at h
      have hr1 : r = 1 := by
        have hrodd : ¬ 2 ∣ r := fun h2 => by
          have : 2 ∣ 455 := h ▸ (dvd_mul_of_dvd_right h2 _)
          norm_num at this
        have hr3 : ¬ 3 ∣ r := fun h3 => by
          have : 3 ∣ 455 := h ▸ (dvd_mul_of_dvd_right h3 _)
          norm_num at this
        have key3 : ∀ d ∈ Nat.divisors 6, ¬ 2 ∣ d → ¬ 3 ∣ d → d = 1 := by decide +kernel
        exact key3 r (Nat.mem_divisors.mpr ⟨hr, by norm_num⟩) hrodd hr3
      rw [hr1, mul_one] at h
      have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
      obtain ⟨y', hy'⟩ := exists_prime_orderOf_dvd_card'
        (G := Subgroup.centralizer ((P : Subgroup X) : Set X)) 13 (by rw [h]; norm_num)
      obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := P) 7 (by rw [hP])
      apply h713 y y' (by rw [Subgroup.orderOf_coe]; exact hy)
        (by rw [Subgroup.orderOf_coe]; exact hy')
      exact Subgroup.mem_centralizer_iff.mp y'.2 y y.2
  refine ⟨hNc, ?_⟩
  have hCdvd : Nat.card (Subgroup.centralizer ((P : Subgroup X) : Set X)) ∣ 14 := by
    rw [← hNc, hN]
    exact dvd_mul_right _ _
  have hCc : Nat.card (Subgroup.centralizer ((P : Subgroup X) : Set X)) = 7 := by
    have key2 : ∀ d ∈ Nat.divisors 14, 7 ∣ d → d % 2 = 1 → d = 7 := by decide +kernel
    exact key2 _ (Nat.mem_divisors.mpr ⟨hCdvd, by norm_num⟩) hC7 (Nat.odd_iff.mp hCodd)
  exact (Subgroup.eq_of_le_of_card_ge hPC (by rw [hCc, hP])).symm

end Sz8Sylow

end CFSG.Quasithin.RuType
