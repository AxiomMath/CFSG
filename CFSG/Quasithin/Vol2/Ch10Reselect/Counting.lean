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
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
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

namespace CFSG.Quasithin.Vol2.Ch10Reselect

private theorem rearr_three {G : Type*} [Group G] {A B C A' B' C' : G}
    (h1 : B * A' = A' * B) (h2 : C * A' = A' * C) (h3 : C * B' = B' * C) :
    A * B * C * (A' * B' * C') = A * A' * (B * B') * (C * C') := by
  calc A * B * C * (A' * B' * C') = A * B * (C * A') * (B' * C') := by simp only [mul_assoc]
    _ = A * B * (A' * C) * (B' * C') := by rw [h2]
    _ = A * (B * A') * C * (B' * C') := by simp only [mul_assoc]
    _ = A * (A' * B) * C * (B' * C') := by rw [h1]
    _ = A * A' * B * (C * B') * C' := by simp only [mul_assoc]
    _ = A * A' * B * (B' * C) * C' := by rw [h3]
    _ = A * A' * (B * B') * (C * C') := by simp only [mul_assoc]

private theorem pow_val_add' {G : Type*} [Group G] {r : ℕ} [NeZero r] {g : G}
    (hg : orderOf g = r) (x y : ZMod r) : g ^ (x + y).val = g ^ x.val * g ^ y.val := by
  have key := pow_mod_orderOf g (x.val + y.val)
  rw [hg] at key
  rw [ZMod.val_add, key, pow_add]

theorem exists_orderOf_eq_mem_centralizer {G : Type*} [Group G] [Finite G] {r : ℕ} [Fact r.Prime]
    {P H : Subgroup G} (hP : IsPGroup r P) (hPH : P ≤ Subgroup.normalizer (H : Set G))
    (hdiv : r ∣ Nat.card H) :
    ∃ h ∈ H, orderOf h = r ∧ ∀ x ∈ P, x * h = h * x := by
  letI : MulAction P H :=
    { smul := fun x h => ⟨(x : G) * (h : G) * (x : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hPH x.2) (h : G)).mp h.2⟩
      one_smul := fun h => Subtype.ext (by
        show ((1 : P) : G) * (h : G) * ((1 : P) : G)⁻¹ = (h : G)
        simp)
      mul_smul := fun x y h => Subtype.ext (by
        show ((x * y : P) : G) * (h : G) * ((x * y : P) : G)⁻¹ =
          (x : G) * ((y : G) * (h : G) * (y : G)⁻¹) * (x : G)⁻¹
        simp only [Subgroup.coe_mul, mul_inv_rev, mul_assoc]) }
  have hsmul : ∀ (x : P) (h : H), ((x • h : H) : G) = (x : G) * (h : G) * (x : G)⁻¹ :=
    fun _ _ => rfl
  have hmem : ∀ h : H,
      h ∈ MulAction.fixedPoints P H ↔ (h : G) ∈ Subgroup.centralizer (P : Set G) := by
    intro h
    rw [MulAction.mem_fixedPoints, Subgroup.mem_centralizer_iff]
    constructor
    · intro hf y hy
      have h1 := congrArg Subtype.val (hf ⟨y, hy⟩)
      rw [hsmul] at h1
      exact mul_inv_eq_iff_eq_mul.mp h1
    · intro hc x
      apply Subtype.ext
      rw [hsmul]
      exact mul_inv_eq_iff_eq_mul.mpr (hc (x : G) x.2)
  let K : Subgroup G := H ⊓ Subgroup.centralizer (P : Set G)
  have hcardK : Nat.card K = Nat.card (MulAction.fixedPoints P H) := by
    refine Nat.card_congr
      { toFun := fun g => ⟨⟨(g : G), (Subgroup.mem_inf.mp g.2).1⟩,
          (hmem ⟨(g : G), (Subgroup.mem_inf.mp g.2).1⟩).mpr (Subgroup.mem_inf.mp g.2).2⟩
        invFun := fun h => ⟨(h.1 : G), Subgroup.mem_inf.mpr ⟨h.1.2, (hmem h.1).mp h.2⟩⟩
        left_inv := fun g => rfl
        right_inv := fun h => rfl }
  have hmod := IsPGroup.card_modEq_card_fixedPoints hP H
  have hdvdF : r ∣ Nat.card (MulAction.fixedPoints P H) :=
    Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr hdiv))
  have hdvdK : r ∣ Nat.card K := by
    rw [hcardK]
    exact hdvdF
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' r hdvdK
  refine ⟨(x : G), (Subgroup.mem_inf.mp x.2).1, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, hx]
  · exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp x.2).2

theorem exists_elemAbelian_card_pow_three {G : Type*} [Group G] [Finite G] {r : ℕ} [Fact r.Prime]
    {a b c : G} (ha : orderOf a = r) (hb : orderOf b = r) (hc : orderOf c = r)
    (hab : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b)
    (hind : ∀ i j k : ℕ, a ^ i * b ^ j * c ^ k = 1 → r ∣ i ∧ r ∣ j ∧ r ∣ k) :
    ∃ E : Subgroup G, E ≤ Subgroup.closure ({a, b, c} : Set G) ∧ a ∈ E ∧ b ∈ E ∧ c ∈ E ∧
      IsMulCommutative E ∧ (∀ x ∈ E, x ^ r = 1) ∧ Nat.card E = r ^ 3 := by
  have hab' : Commute a b := hab
  have hac' : Commute a c := hac
  have hbc' : Commute b c := hbc
  have hmul : ∀ x y z x' y' z' : ZMod r,
      a ^ (x + x').val * b ^ (y + y').val * c ^ (z + z').val =
        a ^ x.val * b ^ y.val * c ^ z.val * (a ^ x'.val * b ^ y'.val * c ^ z'.val) := by
    intro x y z x' y' z'
    rw [pow_val_add' ha, pow_val_add' hb, pow_val_add' hc]
    exact (rearr_three (hab'.pow_pow x'.val y.val).symm.eq (hac'.pow_pow x'.val z.val).symm.eq
      (hbc'.pow_pow y'.val z.val).symm.eq).symm
  let φ : Multiplicative (ZMod r × ZMod r × ZMod r) →* G :=
    { toFun := fun v => a ^ (Multiplicative.toAdd v).1.val * b ^ (Multiplicative.toAdd v).2.1.val *
        c ^ (Multiplicative.toAdd v).2.2.val
      map_one' := by simp
      map_mul' := fun v w => by
        simp only [toAdd_mul, Prod.fst_add, Prod.snd_add]
        exact hmul _ _ _ _ _ _ }
  have hφ : ∀ v : Multiplicative (ZMod r × ZMod r × ZMod r),
      φ v = a ^ (Multiplicative.toAdd v).1.val * b ^ (Multiplicative.toAdd v).2.1.val *
        c ^ (Multiplicative.toAdd v).2.2.val := fun v => rfl
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro v hv
    rw [hφ] at hv
    obtain ⟨h1, h2, h3⟩ := hind _ _ _ hv
    have e1 : (Multiplicative.toAdd v).1 = 0 :=
      (ZMod.val_eq_zero _).mp (Nat.eq_zero_of_dvd_of_lt h1 (ZMod.val_lt _))
    have e2 : (Multiplicative.toAdd v).2.1 = 0 :=
      (ZMod.val_eq_zero _).mp (Nat.eq_zero_of_dvd_of_lt h2 (ZMod.val_lt _))
    have e3 : (Multiplicative.toAdd v).2.2 = 0 :=
      (ZMod.val_eq_zero _).mp (Nat.eq_zero_of_dvd_of_lt h3 (ZMod.val_lt _))
    rw [← toAdd_eq_zero]
    exact Prod.ext e1 (Prod.ext e2 e3)
  refine ⟨φ.range, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro x ⟨v, rfl⟩
    rw [hφ]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _))
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
  · exact MonoidHom.mem_range.mpr ⟨Multiplicative.ofAdd (1, 0, 0), by simp [hφ, ZMod.val_one]⟩
  · exact MonoidHom.mem_range.mpr ⟨Multiplicative.ofAdd (0, 1, 0), by simp [hφ, ZMod.val_one]⟩
  · exact MonoidHom.mem_range.mpr ⟨Multiplicative.ofAdd (0, 0, 1), by simp [hφ, ZMod.val_one]⟩
  · refine ⟨⟨fun x y => ?_⟩⟩
    obtain ⟨v, hv⟩ := MonoidHom.mem_range.mp x.2
    obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp y.2
    apply Subtype.ext
    show (x : G) * (y : G) = (y : G) * (x : G)
    rw [← hv, ← hw, ← map_mul, ← map_mul, mul_comm v w]
  · intro x hx
    obtain ⟨v, hv⟩ := MonoidHom.mem_range.mp hx
    have hz : ∀ z : ZMod r, r • z = 0 := fun z => by
      rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    have hvr : v ^ r = 1 := by
      rw [← toAdd_eq_zero, toAdd_pow]
      exact Prod.ext (hz _) (Prod.ext (hz _) (hz _))
    rw [← hv, ← map_pow, hvr, map_one]
  · have hbij : Function.Bijective φ.rangeRestrict :=
      ⟨fun u v huv => hinj (congrArg Subtype.val huv), MonoidHom.rangeRestrict_surjective φ⟩
    rw [← Nat.card_congr (Equiv.ofBijective _ hbij),
      ← Nat.card_congr (Multiplicative.ofAdd (α := ZMod r × ZMod r × ZMod r))]
    rw [Nat.card_prod, Nat.card_prod, Nat.card_zmod]
    ring

end CFSG.Quasithin.Vol2.Ch10Reselect
