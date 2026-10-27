module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.Nilpotent
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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Quasithin.C64Dihedral

variable {G : Type} [Group G]

structure NFData (E : Subgroup G) (s ρ : G) : Prop where
  sq : ∀ x ∈ E, x ^ 2 = 1
  comm : ∀ x ∈ E, ∀ x' ∈ E, x * x' = x' * x
  s2 : s * s = 1
  sE : ∀ x ∈ E, s * x = x * s
  ρE : ∀ x ∈ E, ρ * x = x * ρ
  sρ : s * ρ * s = ρ⁻¹

namespace NFData

variable {E : Subgroup G} {s ρ : G} (d : NFData E s ρ)
include d

theorem s_inv : s⁻¹ = s := inv_eq_of_mul_eq_one_right d.s2

theorem s_zpow_s (i : ℤ) : s * ρ ^ i * s = ρ ^ (-i) := by
  have h : s * ρ ^ i * s⁻¹ = (s * ρ * s⁻¹) ^ i := (conj_zpow).symm
  rw [d.s_inv, d.sρ, inv_zpow'] at h
  exact h

theorem zpow_mul_s (i : ℤ) : ρ ^ i * s = s * ρ ^ (-i) := by
  rw [← d.s_zpow_s i, ← mul_assoc, ← mul_assoc, d.s2, one_mul]

theorem zpow_comm (i : ℤ) (x : G) (hx : x ∈ E) : ρ ^ i * x = x * ρ ^ i :=
  (Commute.zpow_left (d.ρE x hx) i).eq

@[expose] def nf : Subgroup G where
  carrier := {x | ∃ e ∈ E, ∃ i : ℤ, x = e * ρ ^ i ∨ x = e * s * ρ ^ i}
  one_mem' := ⟨1, E.one_mem, 0, Or.inl (by simp)⟩
  mul_mem' := by
    rintro x y ⟨e, he, i, rfl | rfl⟩ ⟨e', he', j, rfl | rfl⟩
    · refine ⟨e * e', E.mul_mem he he', i + j, Or.inl ?_⟩
      calc e * ρ ^ i * (e' * ρ ^ j) = e * (ρ ^ i * e') * ρ ^ j := by group
        _ = e * (e' * ρ ^ i) * ρ ^ j := by rw [d.zpow_comm i e' he']
        _ = e * e' * ρ ^ (i + j) := by rw [zpow_add]; group
    · refine ⟨e * e', E.mul_mem he he', j - i, Or.inr ?_⟩
      calc e * ρ ^ i * (e' * s * ρ ^ j) = e * (ρ ^ i * e') * s * ρ ^ j := by group
        _ = e * (e' * ρ ^ i) * s * ρ ^ j := by rw [d.zpow_comm i e' he']
        _ = e * e' * (ρ ^ i * s) * ρ ^ j := by group
        _ = e * e' * (s * ρ ^ (-i)) * ρ ^ j := by rw [d.zpow_mul_s i]
        _ = e * e' * s * ρ ^ (j - i) := by rw [sub_eq_neg_add, zpow_add]; group
    · refine ⟨e * e', E.mul_mem he he', i + j, Or.inr ?_⟩
      calc e * s * ρ ^ i * (e' * ρ ^ j) = e * s * (ρ ^ i * e') * ρ ^ j := by group
        _ = e * s * (e' * ρ ^ i) * ρ ^ j := by rw [d.zpow_comm i e' he']
        _ = e * (s * e') * ρ ^ i * ρ ^ j := by group
        _ = e * (e' * s) * ρ ^ i * ρ ^ j := by rw [d.sE e' he']
        _ = e * e' * s * ρ ^ (i + j) := by rw [zpow_add]; group
    · refine ⟨e * e', E.mul_mem he he', j - i, Or.inl ?_⟩
      calc e * s * ρ ^ i * (e' * s * ρ ^ j) = e * s * (ρ ^ i * e') * s * ρ ^ j := by group
        _ = e * s * (e' * ρ ^ i) * s * ρ ^ j := by rw [d.zpow_comm i e' he']
        _ = e * (s * e') * ρ ^ i * s * ρ ^ j := by group
        _ = e * (e' * s) * ρ ^ i * s * ρ ^ j := by rw [d.sE e' he']
        _ = e * e' * (s * ρ ^ i * s) * ρ ^ j := by group
        _ = e * e' * ρ ^ (-i) * ρ ^ j := by rw [d.s_zpow_s i]
        _ = e * e' * ρ ^ (j - i) := by rw [sub_eq_neg_add, zpow_add]; group
  inv_mem' := by
    rintro x ⟨e, he, i, rfl | rfl⟩
    · refine ⟨e⁻¹, E.inv_mem he, -i, Or.inl ?_⟩
      calc (e * ρ ^ i)⁻¹ = ρ ^ (-i) * e⁻¹ := by group
        _ = e⁻¹ * ρ ^ (-i) := d.zpow_comm (-i) e⁻¹ (E.inv_mem he)
    · refine ⟨e⁻¹, E.inv_mem he, i, Or.inr ?_⟩
      calc (e * s * ρ ^ i)⁻¹ = (ρ ^ (-i) * s) * s⁻¹ * s⁻¹ * e⁻¹ := by group
        _ = (s * ρ ^ i) * s⁻¹ * s⁻¹ * e⁻¹ := by rw [d.zpow_mul_s (-i), neg_neg]
        _ = s * ρ ^ i * e⁻¹ := by rw [d.s_inv, mul_assoc (s * ρ ^ i), d.s2, mul_one]
        _ = s * (e⁻¹ * ρ ^ i) := by rw [mul_assoc, d.zpow_comm i e⁻¹ (E.inv_mem he)]
        _ = (s * e⁻¹) * ρ ^ i := by group
        _ = e⁻¹ * s * ρ ^ i := by rw [d.sE e⁻¹ (E.inv_mem he)]

theorem sup_closure_eq : E ⊔ Subgroup.closure {s, ρ} = d.nf := by
  refine le_antisymm (sup_le (fun x hx => ⟨x, hx, 0, Or.inl (by simp)⟩) ?_) ?_
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact ⟨1, E.one_mem, 0, Or.inr (by simp)⟩
    · exact ⟨1, E.one_mem, 1, Or.inl (by simp)⟩
  · rintro x ⟨e, he, i, rfl | rfl⟩
    · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left he)
        (Subgroup.mem_sup_right (Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) i))
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left he)
        (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))))
        (Subgroup.mem_sup_right (Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) i))

theorem sq_eq {x : G} (hx : x ∈ d.nf) : ∃ i : ℤ, x ^ 2 = ρ ^ (2 * i) := by
  obtain ⟨e, he, i, rfl | rfl⟩ := hx
  · refine ⟨i, ?_⟩
    calc (e * ρ ^ i) ^ 2 = e * (ρ ^ i * e) * ρ ^ i := by rw [pow_two]; group
      _ = (e * e) * (ρ ^ i * ρ ^ i) := by rw [d.zpow_comm i e he]; group
      _ = ρ ^ (2 * i) := by
        rw [← pow_two, d.sq e he, one_mul, two_mul, zpow_add]
  · refine ⟨0, ?_⟩
    rw [mul_zero, zpow_zero]
    calc (e * s * ρ ^ i) ^ 2 = e * s * (ρ ^ i * e) * s * ρ ^ i := by rw [pow_two]; group
      _ = e * (s * e) * (ρ ^ i * s) * ρ ^ i := by rw [d.zpow_comm i e he]; group
      _ = e * (e * s) * (s * ρ ^ (-i)) * ρ ^ i := by rw [d.sE e he, d.zpow_mul_s i]
      _ = (e * e) * (s * s) * (ρ ^ (-i) * ρ ^ i) := by group
      _ = 1 := by
        rw [← pow_two, d.sq e he, d.s2, ← zpow_add, neg_add_cancel, zpow_zero, mul_one,
          mul_one]

theorem comm_of_mem_E {x : G} (hx : x ∈ E) {y : G} (hy : y ∈ d.nf) : x * y = y * x := by
  obtain ⟨e, he, i, rfl | rfl⟩ := hy
  · rw [← mul_assoc, d.comm x hx e he, mul_assoc, ← d.zpow_comm i x hx, mul_assoc]
  · have h1 : x * s = s * x := (d.sE x hx).symm
    calc x * (e * s * ρ ^ i) = e * (x * s) * ρ ^ i := by
          rw [← mul_assoc, ← mul_assoc, d.comm x hx e he]; group
      _ = e * s * (x * ρ ^ i) := by rw [h1]; group
      _ = e * s * ρ ^ i * x := by rw [← d.zpow_comm i x hx]; group

end NFData

theorem comm_of_mul_comm {e g y : G} (heg : g * e = e * g) (h : e * y * g = g * (e * y)) :
    y * g = g * y := by
  have h1 : e * (y * g) = e * (g * y) := by
    rw [← mul_assoc, h, ← mul_assoc, heg, mul_assoc]
  exact mul_left_cancel h1

structure DihData (E : Subgroup G) (s t u : G) (k : ℕ) : Prop where
  sq : ∀ x ∈ E, x ^ 2 = 1
  comm : ∀ x ∈ E, ∀ x' ∈ E, x * x' = x' * x
  s2 : s * s = 1
  t2 : t * t = 1
  sE : ∀ x ∈ E, s * x = x * s
  tE : ∀ x ∈ E, t * x = x * t
  pow : (s * t) ^ (2 ^ (k + 1)) = u
  uE : u ∈ E
  u1 : u ≠ 1

namespace DihData

variable {E : Subgroup G} {s t u : G} {k : ℕ} (d : DihData E s t u k)
include d

theorem s_inv : s⁻¹ = s := inv_eq_of_mul_eq_one_right d.s2

theorem t_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right d.t2

theorem u2 : u * u = 1 := by
  have := d.sq u d.uE
  rwa [pow_two] at this

theorem nfData : NFData E s (s * t) where
  sq := d.sq
  comm := d.comm
  s2 := d.s2
  sE := d.sE
  ρE := fun x hx => by rw [mul_assoc, d.tE x hx, ← mul_assoc, d.sE x hx, mul_assoc]
  sρ := by rw [mul_inv_rev, d.s_inv, d.t_inv, ← mul_assoc, d.s2, one_mul]

theorem sup_closure_eq : E ⊔ Subgroup.closure {s, t} = d.nfData.nf := by
  rw [← d.nfData.sup_closure_eq]
  congr 1
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact Subgroup.subset_closure (by simp)
    · have h1 : s * (s * x) ∈ Subgroup.closure {s, s * x} :=
        Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
      rwa [← mul_assoc, d.s2, one_mul] at h1
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))

theorem rho_pow_two_pow : (s * t) ^ (2 ^ (k + 2)) = 1 := by
  rw [pow_succ 2 (k + 1), pow_mul, d.pow, pow_two, d.u2]

theorem orderOf_rho : orderOf (s * t) = 2 ^ (k + 2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime_pow (by rw [d.pow]; exact d.u1) d.rho_pow_two_pow

theorem zpow_two_pow : (s * t) ^ ((2 : ℤ) ^ (k + 1)) = u := by
  rw [← d.pow]
  exact_mod_cast zpow_natCast (s * t) (2 ^ (k + 1))

theorem zpow_mem_E_iff (m : ℤ) : (s * t) ^ m ∈ E ↔ ((2 : ℤ) ^ (k + 1)) ∣ m := by
  constructor
  · intro hm
    have h1 : s * (s * t) ^ m = (s * t) ^ m * s := d.sE _ hm
    have h2 : (s * t) ^ (2 * m) = 1 := by
      have h3 : (s * t) ^ (-m) = (s * t) ^ m := by
        rw [← d.nfData.s_zpow_s m, h1, mul_assoc, d.s2, mul_one]
      have h4 : (s * t) ^ (2 * m) = (s * t) ^ m * (s * t) ^ m := by
        rw [two_mul, zpow_add]
      rw [h4]
      nth_rewrite 1 [← h3]
      rw [← zpow_add, neg_add_cancel, zpow_zero]
    rw [← orderOf_dvd_iff_zpow_eq_one, d.orderOf_rho] at h2
    have h5 : ((2 : ℤ) ^ (k + 2)) ∣ 2 * m := by exact_mod_cast h2
    rw [pow_succ', mul_comm] at h5
    exact (mul_dvd_mul_iff_right (by norm_num : (2 : ℤ) ≠ 0)).1 (by
      rw [mul_comm m]
      exact h5)
  · rintro ⟨q, rfl⟩
    rw [zpow_mul, d.zpow_two_pow]
    exact E.zpow_mem d.uE q

theorem zpow_two_mul_eq_one_iff (m : ℤ) :
    (s * t) ^ (2 * m) = 1 ↔ ((2 : ℤ) ^ (k + 1)) ∣ m := by
  rw [← orderOf_dvd_iff_zpow_eq_one, d.orderOf_rho]
  push_cast
  rw [pow_succ, mul_comm 2 m]
  exact mul_dvd_mul_iff_right two_ne_zero

theorem u_zpow (q : ℤ) : u ^ q = 1 ∨ u ^ q = u := by
  rcases Int.even_or_odd q with ⟨r, rfl⟩ | ⟨r, rfl⟩
  · left
    rw [← two_mul, zpow_mul, zpow_two, d.u2, one_zpow]
  · right
    rw [zpow_add, zpow_mul, zpow_two, d.u2, one_zpow, one_mul, zpow_one]

theorem eq_u_of_sq {i : ℤ} (h1 : ((s * t) ^ (2 * i)) ^ 2 = 1) (h2 : (s * t) ^ (2 * i) ≠ 1) :
    (s * t) ^ (2 * i) = u := by
  have h3 : (s * t) ^ (2 * (2 * i)) = 1 := by
    rw [← h1, ← zpow_natCast, ← zpow_mul]
    congr 1
    push_cast
    ring
  rw [d.zpow_two_mul_eq_one_iff] at h3
  have h4 : ((2 : ℤ) ^ k) ∣ i := by
    rw [pow_succ, mul_comm 2 i] at h3
    exact (mul_dvd_mul_iff_right two_ne_zero).1 h3
  obtain ⟨q, rfl⟩ := h4
  have e : (s * t) ^ (2 * (2 ^ k * q)) = u ^ q := by
    rw [← d.zpow_two_pow, ← zpow_mul]
    congr 1
    ring
  rw [e] at h2 ⊢
  rcases d.u_zpow q with h5 | h5
  · exact absurd h5 h2
  · exact h5

theorem conj_u {g : G}
    (hg : g ∈ Subgroup.normalizer ((E ⊔ Subgroup.closure {s, t} : Subgroup G) : Set G)) :
    g * u * g⁻¹ = u := by
  have hu : u = ((s * t) ^ (2 ^ k)) ^ 2 := by
    rw [← d.pow, ← pow_mul, ← pow_succ]
  have hmem : (s * t) ^ (2 ^ k) ∈ E ⊔ Subgroup.closure {s, t} := by
    rw [d.sup_closure_eq]
    exact ⟨1, E.one_mem, (2 ^ k : ℕ), Or.inl (by rw [one_mul, zpow_natCast])⟩
  have h1 := (Subgroup.mem_normalizer_iff.1 hg _).1 hmem
  rw [d.sup_closure_eq] at h1
  obtain ⟨i, hi⟩ := d.nfData.sq_eq h1
  have e : g * u * g⁻¹ = (g * (s * t) ^ (2 ^ k) * g⁻¹) ^ 2 := by
    rw [hu, pow_two, pow_two]
    group
  rw [e, hi]
  refine d.eq_u_of_sq ?_ ?_
  · rw [← hi, ← e, pow_two]
    calc g * u * g⁻¹ * (g * u * g⁻¹) = g * (u * u) * g⁻¹ := by group
      _ = 1 := by rw [d.u2]; group
  · rw [← hi, ← e]
    intro h3
    apply d.u1
    calc u = g⁻¹ * (g * u * g⁻¹) * g := by group
      _ = 1 := by rw [h3]; group

theorem mem_E_of_comm {x : G} (hx : x ∈ E ⊔ Subgroup.closure {s, t}) (hs : x * s = s * x)
    (ht : x * t = t * x) : x ∈ E := by
  have nf := d.nfData
  rw [d.sup_closure_eq] at hx
  obtain ⟨e, he, i, rfl | rfl⟩ := hx
  ·
    have h2 : (s * t) ^ i * s = s * (s * t) ^ i := comm_of_mul_comm (d.sE e he) hs
    rw [nf.zpow_mul_s i] at h2
    have h4 := mul_left_cancel h2
    have h1 : (s * t) ^ (2 * i) = 1 := by
      rw [two_mul, zpow_add]
      nth_rewrite 1 [← h4]
      rw [← zpow_add, neg_add_cancel, zpow_zero]
    rw [d.zpow_two_mul_eq_one_iff, ← d.zpow_mem_E_iff] at h1
    exact E.mul_mem he h1
  · exfalso
    have hs' : e * (s * (s * t) ^ i) * s = s * (e * (s * (s * t) ^ i)) := by
      rw [← mul_assoc e s]
      exact hs
    have ht' : e * (s * (s * t) ^ i) * t = t * (e * (s * (s * t) ^ i)) := by
      rw [← mul_assoc e s]
      exact ht
    have h2 := comm_of_mul_comm (d.sE e he) hs'
    have h3 := comm_of_mul_comm (d.tE e he) ht'
    have h4 : (s * t) ^ (-i) = (s * t) ^ i := by
      rw [← nf.s_zpow_s i, h2, ← mul_assoc, d.s2, one_mul]
    have h1 : (s * t) ^ (2 * i) = 1 := by
      rw [two_mul, zpow_add]
      nth_rewrite 1 [← h4]
      rw [← zpow_add, neg_add_cancel, zpow_zero]
    have h5 : s * (s * t) ^ i * t = (s * t) ^ (1 - i) := by
      calc s * (s * t) ^ i * t = s * (s * t) ^ i * (s * s) * t := by rw [d.s2, mul_one]
        _ = (s * (s * t) ^ i * s) * (s * t) ^ (1 : ℤ) := by rw [zpow_one]; group
        _ = (s * t) ^ (-i) * (s * t) ^ (1 : ℤ) := by rw [nf.s_zpow_s i]
        _ = (s * t) ^ (1 - i) := by rw [← zpow_add]; ring_nf
    have h6 : t * (s * (s * t) ^ i) = (s * t) ^ (i - 1) := by
      calc t * (s * (s * t) ^ i) = (s * s) * t * (s * (s * t) ^ i) := by rw [d.s2, one_mul]
        _ = (s * (s * t) * s) * (s * t) ^ i := by group
        _ = (s * t) ^ (-1 : ℤ) * (s * t) ^ i := by rw [nf.sρ, zpow_neg_one]
        _ = (s * t) ^ (i - 1) := by rw [← zpow_add]; ring_nf
    have h7 : (s * t) ^ (1 - i) = (s * t) ^ (i - 1) := by
      rw [← h5, ← h6]
      exact h3
    have h8 : (s * t) ^ (2 * (1 - i)) = 1 := by
      rw [two_mul, zpow_add]
      nth_rewrite 1 [h7]
      rw [← zpow_add]
      ring_nf
      exact zpow_zero (s * t)
    rw [d.zpow_two_mul_eq_one_iff] at h1 h8
    have h9 : ((2 : ℤ) ^ (k + 1)) ∣ 1 := by
      have := dvd_add h1 h8
      rwa [add_sub_cancel] at this
    have h10 : (2 : ℤ) ∣ 1 := (dvd_pow_self 2 (Nat.succ_ne_zero k)).trans h9
    omega

theorem comm_of_mem_E {x : G} (hx : x ∈ E) {y : G} (hy : y ∈ E ⊔ Subgroup.closure {s, t}) :
    x * y = y * x := by
  rw [d.sup_closure_eq] at hy
  exact d.nfData.comm_of_mem_E hx hy

theorem conj_mem_E {g : G}
    (hg : g ∈ Subgroup.normalizer ((E ⊔ Subgroup.closure {s, t} : Subgroup G) : Set G))
    {x : G} (hx : x ∈ E) : g * x * g⁻¹ ∈ E := by
  have hP : ∀ y ∈ E ⊔ Subgroup.closure {s, t}, g * x * g⁻¹ * y = y * (g * x * g⁻¹) := by
    intro y hy
    have h1 : g⁻¹ * y * g ∈ E ⊔ Subgroup.closure {s, t} := by
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem hg) y).1 hy
      simpa using this
    have h2 := d.comm_of_mem_E hx h1
    calc g * x * g⁻¹ * y = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by rw [h2]
      _ = y * (g * x * g⁻¹) := by group
  have hmem : g * x * g⁻¹ ∈ E ⊔ Subgroup.closure {s, t} :=
    (Subgroup.mem_normalizer_iff.1 hg x).1 (Subgroup.mem_sup_left hx)
  exact d.mem_E_of_comm hmem (hP s (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))))
    (hP t (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))))

theorem mul_zpow_pow {e : G} (he : e ∈ E) (i n : ℤ) :
    (e * (s * t) ^ i) ^ n = e ^ n * (s * t) ^ (i * n) := by
  rw [(Commute.zpow_right (d.nfData.ρE e he).symm i).mul_zpow, ← zpow_mul]

theorem refl_of_sq {x : G} (hx : x ∈ E ⊔ Subgroup.closure {s, t}) (h2 : x * x = 1)
    (hxE : x ∉ E) : ∃ e ∈ E, ∃ i : ℤ, x = e * s * (s * t) ^ i := by
  rw [d.sup_closure_eq] at hx
  obtain ⟨e, he, i, rfl | rfl⟩ := hx
  · exfalso
    apply hxE
    have h3 : (s * t) ^ (2 * i) = 1 := by
      have h4 := d.mul_zpow_pow he i 2
      rw [zpow_two, h2, zpow_two, ← pow_two, d.sq e he, one_mul, mul_comm i] at h4
      exact h4.symm
    rw [d.zpow_two_mul_eq_one_iff, ← d.zpow_mem_E_iff] at h3
    exact E.mul_mem he h3
  · exact ⟨e, he, i, rfl⟩

theorem pow_two_pow_E {e : G} (he : e ∈ E) : e ^ (2 ^ (k + 1)) = 1 := by
  rw [pow_succ, pow_mul', d.sq e he, one_pow]

theorem rho_conj {g : G}
    (hg : g ∈ Subgroup.normalizer ((E ⊔ Subgroup.closure {s, t} : Subgroup G) : Set G)) :
    ∃ e ∈ E, ∃ m : ℤ, Odd m ∧ g * (s * t) * g⁻¹ = e * (s * t) ^ m := by
  have hρ : s * t ∈ E ⊔ Subgroup.closure {s, t} :=
    Subgroup.mem_sup_right (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp)))
  have h1 := (Subgroup.mem_normalizer_iff.1 hg _).1 hρ
  have hpow : (g * (s * t) * g⁻¹) ^ (2 ^ (k + 1)) = u := by
    rw [conj_pow, d.pow, d.conj_u hg]
  rw [d.sup_closure_eq] at h1
  obtain ⟨e, he, m, h2 | h2⟩ := h1
  · refine ⟨e, he, m, ?_, h2⟩
    by_contra hm
    rw [Int.not_odd_iff_even] at hm
    obtain ⟨r, rfl⟩ := hm
    apply d.u1
    rw [← hpow, h2, ← zpow_natCast, d.mul_zpow_pow he, zpow_natCast, d.pow_two_pow_E he,
      one_mul]
    have e1 : (r + r) * ((2 ^ (k + 1) : ℕ) : ℤ) = (2 ^ (k + 2) : ℕ) * r := by
      push_cast
      ring
    rw [e1, zpow_mul, zpow_natCast, d.rho_pow_two_pow, one_zpow]
  · exfalso
    apply d.u1
    have h3 : (e * s * (s * t) ^ m) ^ 2 = 1 := by
      have := d.nfData.sq_eq (show e * s * (s * t) ^ m ∈ d.nfData.nf from ⟨e, he, m, Or.inr rfl⟩)
      obtain ⟨j, hj⟩ := this
      calc (e * s * (s * t) ^ m) ^ 2 = e * s * ((s * t) ^ m * e) * s * (s * t) ^ m := by
            rw [pow_two]; group
        _ = e * (s * e) * ((s * t) ^ m * s) * (s * t) ^ m := by
            rw [d.nfData.zpow_comm m e he]; group
        _ = e * (e * s) * (s * (s * t) ^ (-m)) * (s * t) ^ m := by
            rw [d.sE e he, d.nfData.zpow_mul_s m]
        _ = (e * e) * (s * s) * ((s * t) ^ (-m) * (s * t) ^ m) := by group
        _ = 1 := by
          rw [← pow_two, d.sq e he, d.s2, ← zpow_add, neg_add_cancel, zpow_zero, one_mul,
            one_mul]
    rw [← hpow, h2, pow_succ, mul_comm, pow_mul, h3, one_pow]

theorem rho_sq_ne_one : (s * t) * (s * t) ≠ 1 := by
  intro h
  apply d.u1
  rw [← d.pow, pow_succ', pow_mul, pow_two, h, one_pow]

theorem s_not_mem : s ∉ E := by
  intro h
  apply d.rho_sq_ne_one
  have h1 : t * s = s * t := d.tE s h
  calc s * t * (s * t) = s * (t * s) * t := by group
    _ = s * (s * t) * t := by rw [h1]
    _ = 1 := by rw [← mul_assoc, d.s2, one_mul, d.t2]

theorem t_not_mem : t ∉ E := by
  intro h
  apply d.rho_sq_ne_one
  have h1 : s * t = t * s := d.sE t h
  calc s * t * (s * t) = s * t * (t * s) := by rw [h1]
    _ = 1 := by rw [mul_assoc, ← mul_assoc t t, d.t2, one_mul, d.s2]

theorem u_zpow_odd {j : ℤ} (hj : Odd j) : u ^ j = u := by
  obtain ⟨r, rfl⟩ := hj
  rw [zpow_add, zpow_mul, zpow_two, d.u2, one_zpow, one_mul, zpow_one]

end DihData

section Tower

variable [Finite G]

theorem normalizes_of_conj_mem {S : Subgroup G} {g : G} (h : ∀ x ∈ S, g * x * g⁻¹ ∈ S) :
    g ∈ Subgroup.normalizer (S : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hle : S.map (MulAut.conj g).toMonoidHom ≤ S := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem exists_mem_normalizer_not_mem {H K : Subgroup G} (hK : IsPGroup 2 K) (hHK : H < K) :
    ∃ g ∈ K, g ∈ Subgroup.normalizer (H : Set G) ∧ g ∉ H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent K := hK.isNilpotent
  set W := H.subgroupOf K with hWdef
  have hW : W ≠ ⊤ := by
    intro h
    apply hHK.not_ge
    intro x hx
    have : (⟨x, hx⟩ : K) ∈ W := by rw [h]; trivial
    exact this
  have hlt : W < Subgroup.normalizer (W : Set K) := by
    apply lt_of_le_of_ne Subgroup.le_normalizer
    intro heq
    exact hW (normalizerCondition_iff_only_full_group_self_normalizing.mp
      Group.normalizerCondition_of_isNilpotent W heq.symm)
  obtain ⟨⟨g, hgK⟩, hgN, hgW⟩ := IsConcreteLE.exists_of_lt hlt
  refine ⟨g, hgK, ?_, hgW⟩
  rw [Subgroup.mem_normalizer_iff] at hgN ⊢
  intro h
  constructor
  · intro hh
    exact (hgN ⟨h, hHK.le hh⟩).1 hh
  · intro hh
    have hhK : h ∈ K := by
      have := K.mul_mem (K.mul_mem (K.inv_mem hgK) (hHK.le hh)) hgK
      simpa [mul_assoc] using this
    exact (hgN ⟨h, hhK⟩).2 hh

omit [Finite G] in
theorem mem_sup_zpowers {E : Subgroup G} {x : G} (hx2 : x * x = 1)
    (hxE : ∀ e ∈ E, x * e = e * x) {y : G} (hy : y ∈ E ⊔ Subgroup.zpowers x) :
    ∃ e ∈ E, y = e ∨ y = e * x := by
  let S : Subgroup G :=
    { carrier := {y | ∃ e ∈ E, y = e ∨ y = e * x}
      one_mem' := ⟨1, E.one_mem, Or.inl rfl⟩
      mul_mem' := by
        rintro a b ⟨e, he, ha⟩ ⟨e', he', hb⟩
        rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha, hb]
        · exact ⟨e * e', E.mul_mem he he', Or.inl rfl⟩
        · exact ⟨e * e', E.mul_mem he he', Or.inr (by group)⟩
        · exact ⟨e * e', E.mul_mem he he', Or.inr (by rw [mul_assoc, hxE e' he']; group)⟩
        · refine ⟨e * e', E.mul_mem he he', Or.inl ?_⟩
          calc e * x * (e' * x) = e * (x * e') * x := by group
            _ = e * e' * (x * x) := by rw [hxE e' he']; group
            _ = e * e' := by rw [hx2, mul_one]
      inv_mem' := by
        rintro a ⟨e, he, ha⟩
        rcases ha with ha | ha <;> rw [ha]
        · exact ⟨e⁻¹, E.inv_mem he, Or.inl rfl⟩
        · refine ⟨e⁻¹, E.inv_mem he, Or.inr ?_⟩
          have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
          rw [mul_inv_rev, hxinv, hxE e⁻¹ (E.inv_mem he)] }
  have hle : E ⊔ Subgroup.zpowers x ≤ S := sup_le (fun e he => ⟨e, he, Or.inl rfl⟩)
    (Subgroup.zpowers_le.2 ⟨1, E.one_mem, Or.inr (one_mul x).symm⟩)
  exact hle hy

omit [Finite G] in
theorem sup_zpowers_elemAb {E : Subgroup G} {x : G} (hEsq : ∀ e ∈ E, e ^ 2 = 1)
    (hEc : ∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e) (hx2 : x * x = 1)
    (hxE : ∀ e ∈ E, x * e = e * x) :
    (∀ y ∈ E ⊔ Subgroup.zpowers x, y * y = 1) ∧
      ∀ y ∈ E ⊔ Subgroup.zpowers x, ∀ y' ∈ E ⊔ Subgroup.zpowers x, y * y' = y' * y := by
  have he2 : ∀ e ∈ E, e * e = 1 := fun e he => by
    have := hEsq e he
    rwa [pow_two] at this
  refine ⟨fun y hy => ?_, fun y hy y' hy' => ?_⟩
  · obtain ⟨e, he, h⟩ := mem_sup_zpowers hx2 hxE hy
    rcases h with h | h <;> rw [h]
    · exact he2 e he
    · calc e * x * (e * x) = e * (x * e) * x := by group
        _ = (e * e) * (x * x) := by rw [hxE e he]; group
        _ = 1 := by rw [he2 e he, hx2, one_mul]
  · obtain ⟨e, he, h⟩ := mem_sup_zpowers hx2 hxE hy
    obtain ⟨e', he', h'⟩ := mem_sup_zpowers hx2 hxE hy'
    have hc := hEc e he e' he'
    have hx1 := hxE e he
    have hx2' := hxE e' he'
    rcases h with h | h <;> rcases h' with h' | h' <;> rw [h, h']
    · exact hc
    · calc e * (e' * x) = e' * e * x := by rw [← mul_assoc, hc]
        _ = e' * x * e := by rw [mul_assoc, ← hx1, mul_assoc]
    · calc e * x * e' = e * e' * x := by rw [mul_assoc, hx2', mul_assoc]
        _ = e' * (e * x) := by rw [hc, mul_assoc]
    · calc e * x * (e' * x) = e * e' * (x * x) := by
            rw [mul_assoc e, ← mul_assoc x, hx2']
            group
        _ = e' * e * (x * x) := by rw [hc]
        _ = e' * (x * e) * x := by rw [hx1]; group
        _ = e' * x * (e * x) := by group

theorem two_mul_card_le {E : Subgroup G} {x : G} (hxE' : x ∉ E) :
    2 * Nat.card E ≤ Nat.card ↥(E ⊔ Subgroup.zpowers x) := by
  classical
  let f : ↥E × Bool → ↥(E ⊔ Subgroup.zpowers x) := fun p =>
    if p.2 then ⟨(p.1 : G) * x, Subgroup.mul_mem _ (Subgroup.mem_sup_left p.1.2)
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))⟩
    else ⟨p.1, Subgroup.mem_sup_left p.1.2⟩
  have hf : Function.Injective f := by
    rintro ⟨a, _ | _⟩ ⟨b, _ | _⟩ hab <;> simp only [f, Bool.false_eq_true, ↓reduceIte,
      Subtype.mk.injEq] at hab
    · rw [Subtype.ext hab]
    · exfalso
      apply hxE'
      have : x = (b : G)⁻¹ * a := by rw [hab]; group
      rw [this]
      exact E.mul_mem (E.inv_mem b.2) a.2
    · exfalso
      apply hxE'
      have : x = (a : G)⁻¹ * b := by rw [← hab]; group
      rw [this]
      exact E.mul_mem (E.inv_mem a.2) b.2
    · rw [Subtype.ext (mul_right_cancel hab)]
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool, mul_comm] at this

structure Tower (Sig E R : Subgroup G) (s t : G) : Prop where
  RP : R ≤ E ⊔ Subgroup.closure {s, t}
  PS : E ⊔ Subgroup.closure {s, t} ≤ Sig
  N : Sig ⊓ Subgroup.normalizer ((E ⊔ Subgroup.zpowers s : Subgroup G) : Set G) = R

namespace Tower

variable {Sig E R : Subgroup G} {s t u : G} {k : ℕ} (T : Tower Sig E R s t)
  (d : DihData E s t u k)
include T d

theorem frattini {n e : G} (hnS : n ∈ Sig)
    (hnN : n ∈ Subgroup.normalizer ((E ⊔ Subgroup.closure {s, t} : Subgroup G) : Set G))
    (he : e ∈ E) {i : ℤ} (hns : n * s * n⁻¹ = e * s * (s * t) ^ (2 * i)) :
    n ∈ E ⊔ Subgroup.closure {s, t} := by
  have nf := d.nfData
  have hρP : (s * t) ^ i ∈ E ⊔ Subgroup.closure {s, t} :=
    Subgroup.zpow_mem _ (Subgroup.mem_sup_right (Subgroup.mul_mem _
      (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)))) i
  set g := (s * t) ^ i * n with hg
  have hgS : g ∈ Sig := Sig.mul_mem (T.PS hρP) hnS
  have hgQ : g ∈ Subgroup.normalizer ((E ⊔ Subgroup.zpowers s : Subgroup G) : Set G) := by
    apply normalizes_of_conj_mem
    have hle : E ⊔ Subgroup.zpowers s ≤
        (E ⊔ Subgroup.zpowers s).comap (MulAut.conj g).toMonoidHom := by
      refine sup_le (fun x hx => ?_) (Subgroup.zpowers_le.2 ?_)
      · show g * x * g⁻¹ ∈ E ⊔ Subgroup.zpowers s
        have h1 := d.conj_mem_E hnN hx
        have e1 : g * x * g⁻¹ = (s * t) ^ i * (n * x * n⁻¹) * ((s * t) ^ i)⁻¹ := by
          rw [hg]
          group
        rw [e1, nf.zpow_comm i _ h1, mul_assoc, mul_inv_cancel, mul_one]
        exact Subgroup.mem_sup_left h1
      · show g * s * g⁻¹ ∈ E ⊔ Subgroup.zpowers s
        have e1 : g * s * g⁻¹ = e * s := by
          have e2 : -i + 2 * i + -i = 0 := by ring
          calc g * s * g⁻¹ = (s * t) ^ i * (n * s * n⁻¹) * ((s * t) ^ i)⁻¹ := by
                rw [hg]
                group
            _ = (s * t) ^ i * (e * s * (s * t) ^ (2 * i)) * (s * t) ^ (-i) := by
                rw [hns, zpow_neg]
            _ = ((s * t) ^ i * e) * s * (s * t) ^ (2 * i) * (s * t) ^ (-i) := by group
            _ = e * ((s * t) ^ i * s) * (s * t) ^ (2 * i) * (s * t) ^ (-i) := by
                rw [nf.zpow_comm i e he]
                group
            _ = e * (s * (s * t) ^ (-i)) * (s * t) ^ (2 * i) * (s * t) ^ (-i) := by
                rw [nf.zpow_mul_s i]
            _ = e * s * ((s * t) ^ (-i) * (s * t) ^ (2 * i) * (s * t) ^ (-i)) := by group
            _ = e * s := by rw [← zpow_add, ← zpow_add, e2, zpow_zero, mul_one]
        rw [e1]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left he)
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers s))
    intro x hx
    exact hle hx
  have hgR : g ∈ R := by
    rw [← T.N]
    exact ⟨hgS, hgQ⟩
  have h1 := Subgroup.mul_mem _ (Subgroup.inv_mem _ hρP) (T.RP hgR)
  rw [hg, ← mul_assoc, inv_mul_cancel, one_mul] at h1
  exact h1

theorem odd_of_not_mem {n : G} (hnS : n ∈ Sig)
    (hnN : n ∈ Subgroup.normalizer ((E ⊔ Subgroup.closure {s, t} : Subgroup G) : Set G))
    (hnP : n ∉ E ⊔ Subgroup.closure {s, t}) :
    ∃ e ∈ E, ∃ j : ℤ, Odd j ∧ n * s * n⁻¹ = e * s * (s * t) ^ j := by
  have hsP : s ∈ E ⊔ Subgroup.closure {s, t} :=
    Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have h1 : n * s * n⁻¹ ∈ E ⊔ Subgroup.closure {s, t} := (Subgroup.mem_normalizer_iff.1 hnN s).1 hsP
  have h2 : n * s * n⁻¹ * (n * s * n⁻¹) = 1 := by
    calc n * s * n⁻¹ * (n * s * n⁻¹) = n * (s * s) * n⁻¹ := by group
      _ = 1 := by rw [d.s2]; group
  have h3 : n * s * n⁻¹ ∉ E := by
    intro h
    apply d.s_not_mem
    have := d.conj_mem_E (inv_mem hnN) h
    rwa [show n⁻¹ * (n * s * n⁻¹) * n⁻¹⁻¹ = s by group] at this
  obtain ⟨e, he, j, hj⟩ := d.refl_of_sq h1 h2 h3
  refine ⟨e, he, j, ?_, hj⟩
  by_contra hodd
  rw [Int.not_odd_iff_even] at hodd
  obtain ⟨r, rfl⟩ := hodd
  exact hnP (T.frattini d hnS hnN he (i := r) (by rw [hj, two_mul]))

theorem inv_mul_mem {n n' : G} (hnS : n ∈ Sig)
    (hnN : n ∈ Subgroup.normalizer ((E ⊔ Subgroup.closure {s, t} : Subgroup G) : Set G))
    (hnP : n ∉ E ⊔ Subgroup.closure {s, t}) (hn'S : n' ∈ Sig)
    (hn'N : n' ∈ Subgroup.normalizer ((E ⊔ Subgroup.closure {s, t} : Subgroup G) : Set G))
    (hn'P : n' ∉ E ⊔ Subgroup.closure {s, t}) : n⁻¹ * n' ∈ E ⊔ Subgroup.closure {s, t} := by
  have nf := d.nfData
  have hmS : n⁻¹ ∈ Sig := Sig.inv_mem hnS
  have hmN := inv_mem hnN
  have hmP : n⁻¹ ∉ E ⊔ Subgroup.closure {s, t} := fun h => hnP (by simpa using inv_mem h)
  obtain ⟨f, hf, l, hl, hls⟩ := T.odd_of_not_mem d hmS hmN hmP
  obtain ⟨g, hg, q, hq, hqρ⟩ := d.rho_conj hmN
  obtain ⟨e', he', j, hj, hjs⟩ := T.odd_of_not_mem d hn'S hn'N hn'P
  have he'' := d.conj_mem_E hmN he'
  have hgj : g ^ j ∈ E := E.zpow_mem hg j
  have key : (n⁻¹ * n') * s * (n⁻¹ * n')⁻¹ =
      (n⁻¹ * e' * n⁻¹⁻¹ * f * g ^ j) * s * (s * t) ^ (l + q * j) := by
    calc (n⁻¹ * n') * s * (n⁻¹ * n')⁻¹ = n⁻¹ * (n' * s * n'⁻¹) * n⁻¹⁻¹ := by group
      _ = n⁻¹ * (e' * s * (s * t) ^ j) * n⁻¹⁻¹ := by rw [hjs]
      _ = (n⁻¹ * e' * n⁻¹⁻¹) * (n⁻¹ * s * n⁻¹⁻¹) * (n⁻¹ * (s * t) * n⁻¹⁻¹) ^ j := by
          rw [conj_zpow]
          group
      _ = (n⁻¹ * e' * n⁻¹⁻¹) * (f * s * (s * t) ^ l) * (g * (s * t) ^ q) ^ j := by
          rw [hls, hqρ]
      _ = (n⁻¹ * e' * n⁻¹⁻¹) * (f * s * (s * t) ^ l) * (g ^ j * (s * t) ^ (q * j)) := by
          rw [d.mul_zpow_pow hg]
      _ = (n⁻¹ * e' * n⁻¹⁻¹) * f * (s * ((s * t) ^ l * g ^ j)) * (s * t) ^ (q * j) := by group
      _ = (n⁻¹ * e' * n⁻¹⁻¹) * f * ((s * g ^ j) * (s * t) ^ l) * (s * t) ^ (q * j) := by
          rw [nf.zpow_comm l _ hgj]
          group
      _ = (n⁻¹ * e' * n⁻¹⁻¹ * f * g ^ j) * s * (s * t) ^ (l + q * j) := by
          rw [d.sE _ hgj, zpow_add]
          group
  have heven : Even (l + q * j) := by
    have : Odd (q * j) := hq.mul hj
    exact hl.add_odd this
  obtain ⟨r, hr⟩ := heven
  refine T.frattini d (Sig.mul_mem hmS hn'S) (Subgroup.mul_mem _ hmN hn'N)
    (E.mul_mem (E.mul_mem he'' hf) hgj) (i := r) ?_
  rw [key, hr, two_mul]

theorem caseI {y : G} (hyS : y ∈ Sig)
    (hyN : y ∈ Subgroup.normalizer ((E ⊔ Subgroup.closure {s, t} : Subgroup G) : Set G))
    (hyP : y ∉ E ⊔ Subgroup.closure {s, t}) (hy2 : y * y = 1) (hyE : ∀ x ∈ E, y * x = x * y) :
    DihData E s y u (k + 1) ∧ E ⊔ Subgroup.closure {s, t} < E ⊔ Subgroup.closure {s, y} := by
  obtain ⟨e, he, j, hj, hjs⟩ := T.odd_of_not_mem d hyS hyN hyP
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hsq : (s * y) ^ 2 = e * (s * t) ^ j := by
    calc (s * y) ^ 2 = s * (y * s * y⁻¹) := by rw [pow_two, hyinv]; group
      _ = s * (e * s * (s * t) ^ j) := by rw [hjs]
      _ = (s * e) * s * (s * t) ^ j := by group
      _ = e * (s * s) * (s * t) ^ j := by rw [d.sE e he]; group
      _ = e * (s * t) ^ j := by rw [d.s2, mul_one]
  have hpow : (s * y) ^ (2 ^ (k + 1 + 1)) = u := by
    rw [pow_succ', pow_mul, hsq, ← zpow_natCast, d.mul_zpow_pow he, zpow_natCast,
      d.pow_two_pow_E he, one_mul]
    have e1 : j * ((2 ^ (k + 1) : ℕ) : ℤ) = (2 : ℤ) ^ (k + 1) * j := by
      push_cast
      ring
    rw [e1, zpow_mul, d.zpow_two_pow, d.u_zpow_odd hj]
  have d' : DihData E s y u (k + 1) :=
    { sq := d.sq, comm := d.comm, s2 := d.s2, t2 := hy2, sE := d.sE, tE := hyE, pow := hpow,
      uE := d.uE, u1 := d.u1 }
  refine ⟨d', lt_of_le_of_ne (sup_le le_sup_left ?_) ?_⟩
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
    ·
      have hρj : (s * x) ^ j ∈ E ⊔ Subgroup.closure {s, y} := by
        have h1 : (s * x) ^ j = e⁻¹ * (s * y) ^ 2 := by rw [hsq]; group
        rw [h1]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (E.inv_mem he))
          (Subgroup.pow_mem _ (Subgroup.mem_sup_right (Subgroup.mul_mem _
            (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)))) 2)
      have hcop : IsCoprime j ((2 : ℤ) ^ (k + 2)) := by
        obtain ⟨r, rfl⟩ := hj
        exact IsCoprime.pow_right ⟨1, -r, by ring⟩
      obtain ⟨a, b, hab⟩ := hcop
      have hρ : s * x = ((s * x) ^ j) ^ a := by
        have h1 : (s * x) ^ ((2 : ℤ) ^ (k + 2)) = 1 := by
          rw [← d.rho_pow_two_pow]
          exact_mod_cast zpow_natCast (s * x) (2 ^ (k + 2))
        calc s * x = (s * x) ^ (a * j + b * (2 : ℤ) ^ (k + 2)) := by rw [hab, zpow_one]
          _ = ((s * x) ^ j) ^ a * ((s * x) ^ ((2 : ℤ) ^ (k + 2))) ^ b := by
              rw [zpow_add, mul_comm a j, zpow_mul, mul_comm b, zpow_mul]
          _ = ((s * x) ^ j) ^ a := by rw [h1, one_zpow, mul_one]
      have h2 : s * x ∈ E ⊔ Subgroup.closure {s, y} := by
        rw [hρ]
        exact Subgroup.zpow_mem _ hρj a
      have h3 : x = s * (s * x) := by rw [← mul_assoc, d.s2, one_mul]
      rw [h3]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))) h2
  · intro heq
    apply hyP
    rw [heq]
    exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))

theorem not_comm_refl {a f : G} (haS : a ∈ Sig)
    (haN : a ∈ Subgroup.normalizer ((E ⊔ Subgroup.closure {s, t} : Subgroup G) : Set G))
    (haP : a ∉ E ⊔ Subgroup.closure {s, t}) (hf : f ∈ E) (i : ℤ) :
    a * (f * s * (s * t) ^ i) ≠ (f * s * (s * t) ^ i) * a := by
  have nf := d.nfData
  intro hcomm
  obtain ⟨e, he, j, hj, hjs⟩ := T.odd_of_not_mem d haS haN haP
  obtain ⟨g, hg, q, hq, hqρ⟩ := d.rho_conj haN
  have hf₁ := d.conj_mem_E haN hf
  have hgi : g ^ i ∈ E := E.zpow_mem hg i
  set c := a * f * a⁻¹ * e * g ^ i with hc
  have hcE : c ∈ E := E.mul_mem (E.mul_mem hf₁ he) hgi
  have key : a * (f * s * (s * t) ^ i) * a⁻¹ = c * s * (s * t) ^ (j + q * i) := by
    calc a * (f * s * (s * t) ^ i) * a⁻¹
        = (a * f * a⁻¹) * (a * s * a⁻¹) * (a * (s * t) * a⁻¹) ^ i := by rw [conj_zpow]; group
      _ = (a * f * a⁻¹) * (e * s * (s * t) ^ j) * (g * (s * t) ^ q) ^ i := by rw [hjs, hqρ]
      _ = (a * f * a⁻¹) * (e * s * (s * t) ^ j) * (g ^ i * (s * t) ^ (q * i)) := by
          rw [d.mul_zpow_pow hg]
      _ = (a * f * a⁻¹) * e * (s * ((s * t) ^ j * g ^ i)) * (s * t) ^ (q * i) := by group
      _ = (a * f * a⁻¹) * e * ((s * g ^ i) * (s * t) ^ j) * (s * t) ^ (q * i) := by
          rw [nf.zpow_comm j _ hgi]
          group
      _ = c * s * (s * t) ^ (j + q * i) := by
          rw [d.sE _ hgi, zpow_add, hc]
          group
  have h1 : c * s * (s * t) ^ (j + q * i) = f * s * (s * t) ^ i := by
    rw [← key, hcomm]
    group
  have h2 : (s * t) ^ (j + q * i - i) = c⁻¹ * f := by
    have h3 : s * (s * t) ^ (j + q * i - i) = s * (c⁻¹ * f) := by
      calc s * (s * t) ^ (j + q * i - i)
          = c⁻¹ * (c * s * (s * t) ^ (j + q * i)) * (s * t) ^ (-i) := by
            rw [sub_eq_add_neg, zpow_add]
            group
        _ = c⁻¹ * (f * s * (s * t) ^ i) * (s * t) ^ (-i) := by rw [h1]
        _ = (c⁻¹ * f) * s * ((s * t) ^ i * (s * t) ^ (-i)) := by group
        _ = (c⁻¹ * f) * s := by rw [← zpow_add, add_neg_cancel, zpow_zero, mul_one]
        _ = s * (c⁻¹ * f) := (d.sE _ (E.mul_mem (E.inv_mem hcE) hf)).symm
    exact mul_left_cancel h3
  have h4 : (s * t) ^ (j + q * i - i) ∈ E := by
    rw [h2]
    exact E.mul_mem (E.inv_mem hcE) hf
  rw [d.zpow_mem_E_iff] at h4
  have h5 : (2 : ℤ) ∣ j + q * i - i := (dvd_pow_self 2 (Nat.succ_ne_zero k)).trans h4
  have h6 : Odd (j + q * i - i) := by
    have e1 : j + q * i - i = j + (q - 1) * i := by ring
    rw [e1]
    exact hj.add_even ((hq.sub_odd odd_one).mul_right i)
  exact (Int.not_even_iff_odd.2 h6) (even_iff_two_dvd.2 h5)

theorem le_of_elemAb
    (hII : ∀ y ∈ Sig, y ∈ Subgroup.normalizer ((E ⊔ Subgroup.closure {s, t} : Subgroup G) :
      Set G) → y ∉ E ⊔ Subgroup.closure {s, t} → y * y = 1 → ¬ ∀ x ∈ E, y * x = x * y)
    {A : Subgroup G} (hAS : A ≤ Sig)
    (hAN : A ≤ Subgroup.normalizer ((E ⊔ Subgroup.closure {s, t} : Subgroup G) : Set G))
    (hA2 : ∀ a ∈ A, a * a = 1) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hcard : 2 * Nat.card E ≤ Nat.card A) : A ≤ E ⊔ Subgroup.closure {s, t} := by
  classical
  by_contra hle
  obtain ⟨a', ha'A, ha'P⟩ := Set.not_subset.1 hle
  have hAP : A ⊓ (E ⊔ Subgroup.closure {s, t}) ≤ E := by
    rintro x ⟨hxA, hxP⟩
    by_contra hxE
    obtain ⟨f, hf, i, rfl⟩ := d.refl_of_sq hxP (hA2 _ hxA) hxE
    exact T.not_comm_refl d (hAS ha'A) (hAN ha'A) ha'P hf i (hAc a' ha'A _ hxA)
  have hcard2 : Nat.card A ≤ 2 * Nat.card ↥(A ⊓ (E ⊔ Subgroup.closure {s, t})) := by
    let f : ↥A → ↥(A ⊓ (E ⊔ Subgroup.closure {s, t})) × Bool := fun x =>
      if hx : (x : G) ∈ E ⊔ Subgroup.closure {s, t} then (⟨x, x.2, hx⟩, false)
      else (⟨a'⁻¹ * x, A.mul_mem (A.inv_mem ha'A) x.2,
        T.inv_mul_mem d (hAS ha'A) (hAN ha'A) ha'P (hAS x.2) (hAN x.2) hx⟩, true)
    have hf : Function.Injective f := by
      intro x y hxy
      by_cases hx : (x : G) ∈ E ⊔ Subgroup.closure {s, t} <;>
        by_cases hy : (y : G) ∈ E ⊔ Subgroup.closure {s, t} <;>
        simp only [f, hx, hy, ↓reduceDIte, Prod.mk.injEq, reduceCtorEq, and_false,
          and_true] at hxy
      · exact Subtype.ext (congrArg
          (fun z : ↥(A ⊓ (E ⊔ Subgroup.closure {s, t})) => (z : G)) hxy)
      · exact Subtype.ext (mul_left_cancel (congrArg
          (fun z : ↥(A ⊓ (E ⊔ Subgroup.closure {s, t})) => (z : G)) hxy))
    have := Nat.card_le_card_of_injective f hf
    rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool,
      mul_comm] at this
  have h1 : Nat.card ↥(A ⊓ (E ⊔ Subgroup.closure {s, t})) ≤ Nat.card E :=
    Subgroup.card_le_of_le hAP
  have hEq : A ⊓ (E ⊔ Subgroup.closure {s, t}) = E :=
    Subgroup.eq_of_le_of_card_ge hAP (by omega)
  refine hII a' (hAS ha'A) (hAN ha'A) ha'P (hA2 a' ha'A) fun x hx => ?_
  have hx' : x ∈ A ⊓ (E ⊔ Subgroup.closure {s, t}) := by
    rw [hEq]
    exact hx
  exact hAc a' ha'A x hx'.1

theorem normalizes_of_caseII
    (hII : ∀ y ∈ Sig, y ∈ Subgroup.normalizer ((E ⊔ Subgroup.closure {s, t} : Subgroup G) :
      Set G) → y ∉ E ⊔ Subgroup.closure {s, t} → y * y = 1 → ¬ ∀ x ∈ E, y * x = x * y)
    {g : G}
    (hgN : g ∈ Subgroup.normalizer ((Sig ⊓ Subgroup.normalizer
      ((E ⊔ Subgroup.closure {s, t} : Subgroup G) : Set G) : Subgroup G) : Set G)) :
    g ∈ Subgroup.normalizer ((E ⊔ Subgroup.closure {s, t} : Subgroup G) : Set G) := by
  set P := E ⊔ Subgroup.closure {s, t} with hP
  set N := Sig ⊓ Subgroup.normalizer (P : Set G) with hN
  have hPN : P ≤ N := le_inf T.PS Subgroup.le_normalizer
  have key : ∀ x : G, x ∈ P → x * x = 1 → x ∉ E → (∀ e ∈ E, x * e = e * x) →
      ∀ y ∈ E ⊔ Subgroup.zpowers x, g * y * g⁻¹ ∈ P := by
    intro x hxP hx2 hxE' hxE
    obtain ⟨hsq, hcomm⟩ := sup_zpowers_elemAb d.sq d.comm hx2 hxE
    set A := (E ⊔ Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom with hA
    have hAN' : A ≤ N := by
      rintro _ ⟨y, hy, rfl⟩
      have hyN : y ∈ N := hPN ((sup_le le_sup_left (Subgroup.zpowers_le.2 hxP)) hy)
      exact (Subgroup.mem_normalizer_iff.1 hgN y).1 hyN
    have hle := T.le_of_elemAb d hII (hAN'.trans inf_le_left) (hAN'.trans inf_le_right)
      (by
        rintro _ ⟨y, hy, rfl⟩
        show g * y * g⁻¹ * (g * y * g⁻¹) = 1
        calc g * y * g⁻¹ * (g * y * g⁻¹) = g * (y * y) * g⁻¹ := by group
          _ = 1 := by rw [hsq y hy]; group)
      (by
        rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩
        show g * y * g⁻¹ * (g * y' * g⁻¹) = g * y' * g⁻¹ * (g * y * g⁻¹)
        calc g * y * g⁻¹ * (g * y' * g⁻¹) = g * (y * y') * g⁻¹ := by group
          _ = g * (y' * y) * g⁻¹ := by rw [hcomm y hy y' hy']
          _ = g * y' * g⁻¹ * (g * y * g⁻¹) := by group)
      (by
        rw [hA, Subgroup.card_map_of_injective (MulAut.conj g).injective]
        exact two_mul_card_le hxE')
    intro y hy
    exact hle ⟨y, hy, rfl⟩
  have hsP : s ∈ P := Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have htP : t ∈ P := Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have ks := key s hsP d.s2 d.s_not_mem (fun e he => d.sE e he)
  have kt := key t htP d.t2 d.t_not_mem (fun e he => d.tE e he)
  apply normalizes_of_conj_mem
  have hle : P ≤ P.comap (MulAut.conj g).toMonoidHom := by
    refine sup_le (fun e he => ks e (Subgroup.mem_sup_left he)) ?_
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact ks x (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
    · exact kt x (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
  intro x hx
  exact hle hx

end Tower

theorem le_centralizer_of_tower {Sig E R : Subgroup G} {s u : G} (hS : IsPGroup 2 Sig) :
    ∀ (m : ℕ) (t : G) (k : ℕ), Tower Sig E R s t → DihData E s t u k →
      Nat.card Sig - Nat.card ↥(E ⊔ Subgroup.closure {s, t}) = m →
      Sig ≤ Subgroup.centralizer ({u} : Set G) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro t k T d hm
  set P := E ⊔ Subgroup.closure {s, t} with hP
  by_cases hI : ∃ y ∈ Sig, y ∈ Subgroup.normalizer (P : Set G) ∧ y ∉ P ∧ y * y = 1 ∧
      ∀ x ∈ E, y * x = x * y
  · obtain ⟨y, hyS, hyN, hyP, hy2, hyE⟩ := hI
    obtain ⟨d', hlt⟩ := T.caseI d hyS hyN hyP hy2 hyE
    have T' : Tower Sig E R s y :=
      { RP := T.RP.trans hlt.le
        PS := sup_le (le_sup_left.trans T.PS) (by
          rw [Subgroup.closure_le]
          rintro x (rfl | rfl)
          · exact T.PS (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp)))
          · exact hyS)
        N := T.N }
    have h1 : Nat.card P < Nat.card ↥(E ⊔ Subgroup.closure {s, y}) :=
      Subgroup.card_lt_of_lt hlt
    have h2 : Nat.card ↥(E ⊔ Subgroup.closure {s, y}) ≤ Nat.card Sig :=
      Subgroup.card_le_of_le T'.PS
    exact ih _ (by omega) y (k + 1) T' d' rfl
  · push Not at hI
    have hNS : Sig ≤ Subgroup.normalizer (P : Set G) := by
      by_contra hne
      have hlt : Sig ⊓ Subgroup.normalizer (P : Set G) < Sig :=
        lt_of_le_of_ne inf_le_left fun h => hne (h ▸ inf_le_right)
      obtain ⟨g, hgS, hgN, hgNP⟩ := exists_mem_normalizer_not_mem hS hlt
      exact hgNP ⟨hgS, T.normalizes_of_caseII d (fun y hyS hyN hyP hy2 hyE =>
        absurd hyE (by
          obtain ⟨x, hx, hxy⟩ := hI y hyS hyN hyP hy2
          exact fun h => hxy (h x hx))) hgN⟩
    intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := d.conj_u (hNS hg)
    calc g * u = (g * u * g⁻¹) * g := by group
      _ = u * g := by rw [this]

theorem le_centralizer_of_normalizer_eq {Sig E : Subgroup G} (hS : IsPGroup 2 Sig)
    {s t : G} (hEsq : ∀ x ∈ E, x ^ 2 = 1) (hEc : ∀ x ∈ E, ∀ x' ∈ E, x * x' = x' * x)
    (hs : s * s = 1) (ht : t * t = 1) (hsE : ∀ x ∈ E, s * x = x * s)
    (htE : ∀ x ∈ E, t * x = x * t) (hu : (s * t) ^ 2 ∈ E) (hu1 : (s * t) ^ 2 ≠ 1)
    (hRS : E ⊔ Subgroup.closure {s, t} ≤ Sig)
    (hN : Sig ⊓ Subgroup.normalizer ((E ⊔ Subgroup.zpowers s : Subgroup G) : Set G) =
      E ⊔ Subgroup.closure {s, t}) :
    Sig ≤ Subgroup.centralizer ({(s * t) ^ 2} : Set G) := by
  have d : DihData E s t ((s * t) ^ 2) 0 :=
    { sq := hEsq, comm := hEc, s2 := hs, t2 := ht, sE := hsE, tE := htE, pow := by simp,
      uE := hu, u1 := hu1 }
  have T : Tower Sig E (E ⊔ Subgroup.closure {s, t}) s t :=
    { RP := le_rfl, PS := hRS, N := hN }
  exact le_centralizer_of_tower hS _ t 0 T d rfl

end Tower

end CFSG.Quasithin.C64Dihedral
