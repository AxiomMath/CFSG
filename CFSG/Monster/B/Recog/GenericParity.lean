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

namespace CFSG.Monster.B.Recog

theorem card_modEq_card_fixedBy {G α : Type*} [Group G] [MulAction G α] [Finite α] {t : G}
    (ht : t ^ 2 = 1) : Nat.card α ≡ Nat.card (MulAction.fixedBy α t) [MOD 2] := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 (Subgroup.zpowers t) := by
    rcases (Nat.dvd_prime Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one ht) with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
  have hfix : MulAction.fixedPoints (Subgroup.zpowers t) α = MulAction.fixedBy α t := by
    ext a
    simp only [MulAction.mem_fixedPoints, MulAction.mem_fixedBy]
    refine ⟨fun h => h ⟨t, Subgroup.mem_zpowers t⟩, fun h k => ?_⟩
    have : Subgroup.zpowers t ≤ MulAction.stabilizer G a :=
      Subgroup.zpowers_le.2 (MulAction.mem_stabilizer_iff.2 h)
    exact MulAction.mem_stabilizer_iff.1 (this k.2)
  have := h2.card_modEq_card_fixedPoints α
  rwa [hfix] at this

theorem card_carrier_conjClasses {G : Type*} [Group G] [Finite G] (x : G) :
    Nat.card (ConjClasses.mk x).carrier = (Subgroup.centralizer {x}).index := by
  rw [← ConjAct.orbit_eq_carrier_conjClasses, Nat.card_coe_set_eq, ← MulAction.index_stabilizer]
  have h₁ := Subgroup.card_mul_index (MulAction.stabilizer (ConjAct G) x)
  have h₂ := Subgroup.card_mul_index (Subgroup.centralizer {x})
  rw [← Subgroup.nat_card_centralizer_nat_card_stabilizer,
    Nat.card_congr ConjAct.ofConjAct.toEquiv, ← h₂] at h₁
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h₁

theorem card_conj_commute_modEq_index {G : Type*} [Group G] [Finite G] {d : G} (hd : d ^ 2 = 1)
    (x : G) :
    Nat.card {y : G // IsConj x y ∧ d * y = y * d} ≡ (Subgroup.centralizer {x}).index [MOD 2] := by
  have h := card_modEq_card_fixedBy (α := MulAction.orbit (ConjAct G) x)
    (t := ConjAct.toConjAct d) (by rw [← map_pow, hd, map_one])
  have hO : Nat.card (MulAction.orbit (ConjAct G) x) = (Subgroup.centralizer {x}).index := by
    rw [← card_carrier_conjClasses, ConjAct.orbit_eq_carrier_conjClasses]
  have hF : Nat.card (MulAction.fixedBy (MulAction.orbit (ConjAct G) x) (ConjAct.toConjAct d)) =
      Nat.card {y : G // IsConj x y ∧ d * y = y * d} := by
    refine Nat.card_congr
      { toFun := fun a => ⟨a.1.1, (ConjAct.mem_orbit_conjAct.1 a.1.2).symm, ?_⟩
        invFun := fun b => ⟨⟨b.1, ConjAct.mem_orbit_conjAct.2 b.2.1.symm⟩, ?_⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    · have := congrArg Subtype.val (MulAction.mem_fixedBy.1 a.2)
      rw [MulAction.orbit.coe_smul, ConjAct.toConjAct_smul] at this
      calc d * a.1.1 = d * a.1.1 * d⁻¹ * d := by group
        _ = a.1.1 * d := by rw [this]
    · refine MulAction.mem_fixedBy.2 (Subtype.ext ?_)
      rw [MulAction.orbit.coe_smul, ConjAct.toConjAct_smul]
      change d * b.1 * d⁻¹ = b.1
      rw [b.2.2, mul_inv_cancel_right]
  rw [hO, hF] at h
  exact h.symm

theorem not_dvd_index_centralizer_iff {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) {x : G} (hx : ∃ k, orderOf x = p ^ k) :
    ¬ p ∣ (Subgroup.centralizer {x}).index ↔
      ∃ g : G, g * x * g⁻¹ ∈ (S : Subgroup G) ⊓ Subgroup.centralizer (S : Set G) := by
  constructor
  · intro hp
    rw [Subgroup.index_eq_card] at hp
    obtain ⟨q, hq⟩ := S.isPGroup'.nonempty_fixed_point_of_prime_not_dvd_card _ hp
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
    have hcomm : ∀ s ∈ (S : Subgroup G), s * (h * x * h⁻¹) = (h * x * h⁻¹) * s := by
      intro s hs
      have := hq ⟨s⁻¹, (S : Subgroup G).inv_mem hs⟩
      rw [Subgroup.mk_smul, MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq,
        mul_inv_rev, inv_inv, Subgroup.mem_centralizer_singleton_iff] at this
      calc s * (h * x * h⁻¹) = h * (h⁻¹ * s * h * x) * h⁻¹ := by group
        _ = h * (x * (h⁻¹ * s * h)) * h⁻¹ := by rw [this]
        _ = h * x * h⁻¹ * s := by group
    have hC : h * x * h⁻¹ ∈ Subgroup.centralizer (S : Set G) :=
      Subgroup.mem_centralizer_iff.2 hcomm
    refine ⟨h, ?_, hC⟩
    obtain ⟨k, hk⟩ := hx
    have hy : IsPGroup p (Subgroup.zpowers (h * x * h⁻¹)) := IsPGroup.of_card (n := k) (by
      rw [Nat.card_zpowers, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hk])
    have hle : Subgroup.zpowers (h * x * h⁻¹) ≤ Subgroup.normalizer (S : Set G) :=
      Subgroup.zpowers_le.2 (Subgroup.centralizer_le_normalizer _ hC)
    have hmax := S.is_maximal' (S.isPGroup'.to_sup_of_normal_left' hy hle) le_sup_left
    rw [← hmax]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  · rintro ⟨g, -, hgC⟩
    have hle : ((g⁻¹ • S : Sylow p G) : Subgroup G) ≤ Subgroup.centralizer {x} := by
      change (S : Subgroup G).map (MulAut.conj g⁻¹).toMonoidHom ≤ _
      rw [Subgroup.map_le_iff_le_comap]
      intro s hs
      simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
        Subgroup.mem_centralizer_singleton_iff]
      have := Subgroup.mem_centralizer_iff.1 hgC s hs
      calc g⁻¹ * s * g * x = g⁻¹ * (s * (g * x * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * x * g⁻¹) * s) * g := by rw [this]
        _ = x * (g⁻¹ * s * g) := by group
    exact fun h => (g⁻¹ • S).not_dvd_index (h.trans (Subgroup.index_dvd_of_le hle))

theorem odd_card_conjClass_iff {G : Type*} [Group G] [Finite G] (S : Sylow 2 G) {x : G}
    (hx : ∃ k, orderOf x = 2 ^ k) :
    Odd (Nat.card (ConjClasses.mk x).carrier) ↔
      ∃ g : G, g * x * g⁻¹ ∈ (S : Subgroup G) ⊓ Subgroup.centralizer (S : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [card_carrier_conjClasses, ← not_dvd_index_centralizer_iff S hx, ← even_iff_two_dvd,
    Nat.not_even_iff_odd]

end CFSG.Monster.B.Recog
