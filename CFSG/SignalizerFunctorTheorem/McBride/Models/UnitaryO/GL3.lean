module

public import Mathlib.Algebra.Group.Pi.Units
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
public import Mathlib.FieldTheory.Finite.Extension
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
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
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.SignalizerFunctorTheorem.McBride.UnitaryO

section Sylow

variable {G : Type*} [Group G] [Finite G]

theorem isMulCommutative_of_isPGroup_of_not_dvd_index {r : ℕ} [Fact r.Prime]
    (A : Subgroup G) [IsMulCommutative A] (hA : ¬ r ∣ A.index) {P : Subgroup G}
    (hP : IsPGroup r P) : IsMulCommutative P := by
  obtain ⟨S, hPS⟩ := hP.exists_le_sylow
  obtain ⟨T⟩ := (inferInstance : Nonempty (Sylow r A))
  have hT' : IsPGroup r ((T : Subgroup A).map A.subtype) := T.isPGroup'.map A.subtype
  have hidx : ¬ r ∣ ((T : Subgroup A).map A.subtype).index := by
    rw [Subgroup.index_map_subtype]
    exact Nat.Prime.not_dvd_mul Fact.out T.not_dvd_index hA
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G (hT'.toSylow hidx) S
  have hS : (S : Subgroup G) =
      ((T : Subgroup A).map A.subtype).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  have : IsMulCommutative (S : Subgroup G) := by
    rw [hS]
    infer_instance
  exact isMulCommutative_anti hPS

theorem not_dvd_index_of_card_eq_mul {r : ℕ} {H : Subgroup G} {m : ℕ}
    (h : Nat.card G = Nat.card H * m) (hm : ¬ r ∣ m) : ¬ r ∣ H.index := by
  have h1 : H.index = m :=
    Nat.eq_of_mul_eq_mul_left Nat.card_pos (H.card_mul_index.trans h)
  rwa [h1]

end Sylow

section Torus

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]

noncomputable def unitsToGL (b : Module.Basis (Fin 3) K A) : Aˣ →* GL (Fin 3) K :=
  Units.map (Algebra.leftMulMatrix b).toMonoidHom

theorem unitsToGL_injective (b : Module.Basis (Fin 3) K A) : Function.Injective (unitsToGL b) :=
  Units.map_injective (Algebra.leftMulMatrix_injective b)

theorem exists_isMulCommutative_card_eq [Module.Finite K A] (h : Module.finrank K A = 3) :
    ∃ H : Subgroup (GL (Fin 3) K), IsMulCommutative H ∧ Nat.card H = Nat.card Aˣ := by
  let b := Module.finBasisOfFinrankEq K A h
  refine ⟨(unitsToGL b).range, inferInstance, ?_⟩
  exact (Nat.card_congr (MonoidHom.ofInjective (unitsToGL_injective b)).toEquiv).symm

end Torus

section Orders

theorem card_units_pi_fin_three (K : Type*) [Field K] :
    Nat.card (Fin 3 → K)ˣ = (Nat.card K - 1) ^ 3 := by
  rw [Nat.card_congr MulEquiv.piUnits.toEquiv, Nat.card_pi, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, Nat.card_units]

variable (K : Type*) [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]

theorem card_units_extension (n : ℕ) [NeZero n] :
    Nat.card (FiniteField.Extension K p n)ˣ = Nat.card K ^ n - 1 := by
  rw [Nat.card_units, FiniteField.natCard_extension]

theorem card_units_prod_extension_two :
    Nat.card (FiniteField.Extension K p 2 × K)ˣ = (Nat.card K ^ 2 - 1) * (Nat.card K - 1) := by
  rw [Nat.card_congr MulEquiv.prodUnits.toEquiv, Nat.card_prod, card_units_extension,
    Nat.card_units]

end Orders

section Main

variable {K : Type*} [Field K] [Finite K]

theorem card_GL_three : ∃ a : ℕ, Nat.card K = a + 1 ∧
    Nat.card (GL (Fin 3) K) = a ^ 3 * (a + 1) ^ 3 * ((a + 2) * ((a + 1) ^ 2 + (a + 1) + 1)) := by
  have hQ : 2 ≤ Nat.card K := Finite.one_lt_card
  obtain ⟨a, ha⟩ : ∃ a, Nat.card K = a + 1 := ⟨Nat.card K - 1, by omega⟩
  refine ⟨a, ha, ?_⟩
  have := Fintype.ofFinite K
  rw [Matrix.card_GL_field, Fin.prod_univ_three, Fintype.card_eq_nat_card, ha]
  have h1 : (a + 1) ^ 3 - (a + 1) ^ 0 = a * ((a + 1) ^ 2 + (a + 1) + 1) :=
    Nat.sub_eq_of_eq_add (by ring)
  have h2 : (a + 1) ^ 3 - (a + 1) ^ 1 = (a + 1) * (a * (a + 2)) :=
    Nat.sub_eq_of_eq_add (by ring)
  have h3 : (a + 1) ^ 3 - (a + 1) ^ 2 = (a + 1) ^ 2 * a :=
    Nat.sub_eq_of_eq_add (by ring)
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two]
  rw [h1, h2, h3]
  ring

theorem isMulCommutative_of_isPGroup_gl3 {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r)
    (hrK : ¬ r ∣ Nat.card K) {P : Subgroup (GL (Fin 3) K)} (hP : IsPGroup r P) :
    IsMulCommutative P := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨p, hp⟩ := CharP.exists K
  have : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  obtain ⟨a, ha, hN⟩ := card_GL_three (K := K)
  rw [ha] at hrK
  have hT : (a + 1) ^ 2 + (a + 1) + 1 = a * (a + 3) + 3 := by ring
  have hT' : (a + 1) ^ 2 + (a + 1) + 1 = (a + 1) * (a + 2) + 1 := by ring
  have hr3 : ¬ r ∣ 3 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  have hr2 : ¬ r ∣ 2 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  have hr1 : ¬ r ∣ 1 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  have hQ : ¬ r ∣ a + 1 := hrK
  by_cases h1 : r ∣ a
  ·
    obtain ⟨H, hH, hcard⟩ := exists_isMulCommutative_card_eq (K := K) (A := Fin 3 → K)
      (Module.finrank_fin_fun K)
    rw [card_units_pi_fin_three, ha, Nat.add_sub_cancel] at hcard
    refine isMulCommutative_of_isPGroup_of_not_dvd_index H
      (not_dvd_index_of_card_eq_mul (m := (a + 1) ^ 3 * ((a + 2) * ((a + 1) ^ 2 + (a + 1) + 1)))
        (by rw [hN, hcard]; ring) ?_) hP
    intro hd
    rcases (Nat.Prime.dvd_mul hr).mp hd with h | h
    · exact hQ (hr.dvd_of_dvd_pow h)
    · rcases (Nat.Prime.dvd_mul hr).mp h with h | h
      · exact hr2 ((Nat.dvd_add_right h1).mp h)
      · rw [hT] at h
        exact hr3 ((Nat.dvd_add_right (Dvd.dvd.mul_right h1 _)).mp h)
  by_cases h2 : r ∣ a + 2
  ·
    have : Module.finrank K (FiniteField.Extension K p 2 × K) = 3 := by
      rw [Module.finrank_prod, FiniteField.finrank_extension, Module.finrank_self]
    obtain ⟨H, hH, hcard⟩ := exists_isMulCommutative_card_eq this
    have e1 : (a + 1) ^ 2 - 1 = a * (a + 2) := Nat.sub_eq_of_eq_add (by ring)
    rw [card_units_prod_extension_two K p, ha, Nat.add_sub_cancel, e1] at hcard
    refine isMulCommutative_of_isPGroup_of_not_dvd_index H
      (not_dvd_index_of_card_eq_mul (m := a * (a + 1) ^ 3 * ((a + 1) ^ 2 + (a + 1) + 1))
        (by rw [hN, hcard]; ring) ?_) hP
    intro hd
    rcases (Nat.Prime.dvd_mul hr).mp hd with h | h
    · rcases (Nat.Prime.dvd_mul hr).mp h with h | h
      · exact h1 h
      · exact hQ (hr.dvd_of_dvd_pow h)
    · rw [hT'] at h
      have h' : r ∣ (a + 1) * (a + 2) := Dvd.dvd.mul_left h2 _
      exact hr1 ((Nat.dvd_add_right h').mp h)
  by_cases h3 : r ∣ (a + 1) ^ 2 + (a + 1) + 1
  ·
    have : Module.finrank K (FiniteField.Extension K p 3) = 3 :=
      FiniteField.finrank_extension K p 3
    obtain ⟨H, hH, hcard⟩ := exists_isMulCommutative_card_eq this
    have e1 : (a + 1) ^ 3 - 1 = a * ((a + 1) ^ 2 + (a + 1) + 1) :=
      Nat.sub_eq_of_eq_add (by ring)
    rw [card_units_extension K p 3, ha, e1] at hcard
    refine isMulCommutative_of_isPGroup_of_not_dvd_index H
      (not_dvd_index_of_card_eq_mul (m := a ^ 2 * (a + 1) ^ 3 * (a + 2))
        (by rw [hN, hcard]; ring) ?_) hP
    intro hd
    rcases (Nat.Prime.dvd_mul hr).mp hd with h | h
    · rcases (Nat.Prime.dvd_mul hr).mp h with h | h
      · exact h1 (hr.dvd_of_dvd_pow h)
      · exact hQ (hr.dvd_of_dvd_pow h)
    · exact h2 h
  ·
    refine isMulCommutative_of_isPGroup_of_not_dvd_index (⊥ : Subgroup (GL (Fin 3) K))
      (not_dvd_index_of_card_eq_mul (m := Nat.card (GL (Fin 3) K))
        (by rw [Subgroup.card_bot, one_mul]) ?_) hP
    rw [hN]
    intro hd
    rcases (Nat.Prime.dvd_mul hr).mp hd with h | h
    · rcases (Nat.Prime.dvd_mul hr).mp h with h | h
      · exact h1 (hr.dvd_of_dvd_pow h)
      · exact hQ (hr.dvd_of_dvd_pow h)
    · rcases (Nat.Prime.dvd_mul hr).mp h with h | h
      · exact h2 h
      · exact h3 h

end Main

end CFSG.SignalizerFunctorTheorem.McBride.UnitaryO
