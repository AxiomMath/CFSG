module

public import CFSG.GroupTheory.PCore.Construction
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
public import Mathlib.Order.CompletePartialOrder
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

namespace CFSG.Quasithin.Vol2.Ch10Reselect

open scoped commutatorElement

private lemma gl_comm_mul {G : Type*} [Group G] (k x y : G) :
    ⁅k, x * y⁆ = ⁅k, x⁆ * (x * ⁅k, y⁆ * x⁻¹) := by
  simp only [commutatorElement_def]
  group

private lemma gl_comm_inv {G : Type*} [Group G] (k x : G) :
    ⁅k, x⁻¹⁆ = x⁻¹ * ⁅k, x⁆⁻¹ * x := by
  simp only [commutatorElement_def]
  group

theorem commutator_mem_sup {G : Type*} [Group G] {C P Q : Subgroup G} {k : G}
    (hP : P ≤ Subgroup.normalizer (C : Set G)) (hQ : Q ≤ Subgroup.normalizer (C : Set G))
    (h1 : ∀ x ∈ P, ⁅k, x⁆ ∈ C) (h2 : ∀ x ∈ Q, ⁅k, x⁆ ∈ C) :
    ∀ x ∈ P ⊔ Q, ⁅k, x⁆ ∈ C := by
  let T : Subgroup G :=
    { carrier := {x | x ∈ Subgroup.normalizer (C : Set G) ∧ ⁅k, x⁆ ∈ C}
      mul_mem' := by
        rintro x y ⟨hx, hxC⟩ ⟨hy, hyC⟩
        refine ⟨Subgroup.mul_mem _ hx hy, ?_⟩
        rw [gl_comm_mul k x y]
        exact C.mul_mem hxC ((Subgroup.mem_normalizer_iff.mp hx _).mp hyC)
      one_mem' := ⟨Subgroup.one_mem _, by rw [commutatorElement_one_right]; exact C.one_mem⟩
      inv_mem' := by
        rintro x ⟨hx, hxC⟩
        refine ⟨Subgroup.inv_mem _ hx, ?_⟩
        rw [gl_comm_inv k x]
        have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx) _).mp (C.inv_mem hxC)
        rwa [inv_inv] at h }
  have hPT : P ≤ T := fun x hx => ⟨hP hx, h1 x hx⟩
  have hQT : Q ≤ T := fun x hx => ⟨hQ hx, h2 x hx⟩
  intro x hx
  obtain ⟨-, hxC⟩ := sup_le hPT hQT hx
  exact hxC

theorem commutator_mem_of_sup_of_abelian {G : Type*} [Group G] {A U U' C : Subgroup G}
    [IsMulCommutative ↥A] {k : G} (hk : k ∈ Subgroup.normalizer (A : Set G))
    (hkC : k ∈ Subgroup.normalizer (C : Set G)) (hUA : U ≤ A) (hU'A : U' ≤ A) (hCA : C ≤ A)
    (hA : U ⊔ U' ⊔ C = A) (hU : ∀ u ∈ U, ⁅k, u⁆ ∈ C) (hU' : ∀ u ∈ U', ⁅k, u⁆ ∈ C) :
    ∀ a ∈ A, ⁅k, a⁆ ∈ C := by
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨x, hx⟩ : ↥A) ⟨y, hy⟩)
  have hcommA : ∀ y ∈ A, ⁅k, y⁆ ∈ A := by
    intro y hy
    have h := (Subgroup.mem_normalizer_iff.mp hk y).mp hy
    rw [commutatorElement_def]
    exact A.mul_mem h (A.inv_mem hy)
  let T : Subgroup G :=
    { carrier := {x | x ∈ A ∧ ⁅k, x⁆ ∈ C}
      mul_mem' := by
        rintro x y ⟨hx, hxC⟩ ⟨hy, hyC⟩
        refine ⟨A.mul_mem hx hy, ?_⟩
        have hc : x * ⁅k, y⁆ = ⁅k, y⁆ * x := hcomm x hx _ (hcommA y hy)
        have hconj : x * ⁅k, y⁆ * x⁻¹ = ⁅k, y⁆ := by
          rw [hc, mul_inv_cancel_right]
        rw [gl_comm_mul k x y, hconj]
        exact C.mul_mem hxC hyC
      one_mem' := ⟨A.one_mem, by rw [commutatorElement_one_right]; exact C.one_mem⟩
      inv_mem' := by
        rintro x ⟨hx, hxC⟩
        refine ⟨A.inv_mem hx, ?_⟩
        have hc : x * ⁅k, x⁆⁻¹ = ⁅k, x⁆⁻¹ * x := hcomm x hx _ (A.inv_mem (hcommA x hx))
        have hid : x⁻¹ * ⁅k, x⁆⁻¹ * x = ⁅k, x⁆⁻¹ := by
          rw [mul_assoc, ← hc, inv_mul_cancel_left]
        rw [gl_comm_inv k x, hid]
        exact C.inv_mem hxC }
  have hUT : U ≤ T := fun u hu => ⟨hUA hu, hU u hu⟩
  have hU'T : U' ≤ T := fun u hu => ⟨hU'A hu, hU' u hu⟩
  have hCT : C ≤ T := fun c hc => by
    refine ⟨hCA hc, ?_⟩
    rw [commutatorElement_def]
    exact C.mul_mem ((Subgroup.mem_normalizer_iff.mp hkC c).mp hc) (C.inv_mem hc)
  have hAT : A ≤ T := by
    rw [← hA]
    exact sup_le (sup_le hUT hU'T) hCT
  intro a ha
  obtain ⟨-, haC⟩ := hAT ha
  exact haC

theorem mem_sup_of_le_normalizer {G : Type*} [Group G] {H K : Subgroup G}
    (h : H ≤ Subgroup.normalizer (K : Set G)) {x : G} (hx : x ∈ H ⊔ K) :
    ∃ a ∈ H, ∃ c ∈ K, x = a * c := by
  let T : Subgroup G :=
    { carrier := {x | ∃ a ∈ H, ∃ c ∈ K, x = a * c}
      mul_mem' := by
        rintro _ _ ⟨a, ha, c, hc, rfl⟩ ⟨a', ha', c', hc', rfl⟩
        have hc'' : a'⁻¹ * c * a'⁻¹⁻¹ ∈ K :=
          (Subgroup.mem_normalizer_iff.mp (h (H.inv_mem ha')) c).mp hc
        rw [inv_inv] at hc''
        exact ⟨a * a', H.mul_mem ha ha', a'⁻¹ * c * a' * c', K.mul_mem hc'' hc', by group⟩
      one_mem' := ⟨1, H.one_mem, 1, K.one_mem, (mul_one 1).symm⟩
      inv_mem' := by
        rintro _ ⟨a, ha, c, hc, rfl⟩
        exact ⟨a⁻¹, H.inv_mem ha, a * c⁻¹ * a⁻¹,
          (Subgroup.mem_normalizer_iff.mp (h ha) c⁻¹).mp (K.inv_mem hc), by group⟩ }
  have hHT : H ≤ T := fun x hx => ⟨x, hx, 1, K.one_mem, (mul_one x).symm⟩
  have hKT : K ≤ T := fun x hx => ⟨1, H.one_mem, x, hx, (one_mul x).symm⟩
  obtain ⟨a, ha, c, hc, hxac⟩ := sup_le hHT hKT hx
  exact ⟨a, ha, c, hc, hxac⟩

theorem exists_odd_prime_dvd_of_ne_two_pow {n : ℕ} (hn : 0 < n) (h : ∀ j : ℕ, n ≠ 2 ^ j) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ n := by
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn.ne'
  have hm1 : m ≠ 1 := by
    rintro rfl
    exact h k (mul_one _)
  refine ⟨m.minFac, Nat.minFac_prime hm1, ?_, Dvd.dvd.mul_left (Nat.minFac_dvd m) _⟩
  intro h2
  have h2m : 2 ∣ m := h2 ▸ Nat.minFac_dvd m
  exact Odd.not_two_dvd_nat hm h2m

theorem card_eq_of_ker_eq {G H₁ H₂ : Type*} [Group G] [Finite G] [Group H₁] [Group H₂]
    (f₁ : G →* H₁) (f₂ : G →* H₂) (h₁ : Function.Surjective f₁) (h₂ : Function.Surjective f₂)
    (hker : f₁.ker = f₂.ker) : Nat.card H₁ = Nat.card H₂ := by
  calc Nat.card H₁ = Nat.card (G ⧸ f₁.ker) :=
        (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f₁ h₁).toEquiv).symm
    _ = Nat.card (G ⧸ f₂.ker) := congrArg (fun N : Subgroup G => Nat.card (G ⧸ N)) hker
    _ = Nat.card H₂ := Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f₂ h₂).toEquiv

theorem pCore_quotient_eq_bot {E : Type*} [Group E] [Finite E] (C : Subgroup E) [C.Normal]
    (h : ∀ N : Subgroup E, N.Normal → (∀ x ∈ N, ∃ k : ℕ, x ^ (2 ^ k) ∈ C) → N ≤ C) :
    CFSG.pCore 2 (E ⧸ C) = ⊥ := by
  rw [CFSG.pCore_eq_iSup, eq_bot_iff]
  apply iSup_le
  intro M
  apply iSup_le
  intro hM
  apply iSup_le
  intro hMp
  have hNn : (M.comap (QuotientGroup.mk' C)).Normal :=
    Subgroup.Normal.comap hM (QuotientGroup.mk' C)
  have hNC : M.comap (QuotientGroup.mk' C) ≤ C := by
    apply h _ hNn
    intro x hx
    obtain ⟨k, hk⟩ := hMp ⟨QuotientGroup.mk' C x, hx⟩
    refine ⟨k, ?_⟩
    have hk' : QuotientGroup.mk' C (x ^ (2 ^ k)) = 1 := by
      rw [map_pow]
      have h' := congrArg Subtype.val hk
      simpa using h'
    exact (QuotientGroup.eq_one_iff _).mp hk'
  intro m hm
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective m
  rw [Subgroup.mem_bot]
  exact (QuotientGroup.eq_one_iff x).mpr (hNC (show x ∈ M.comap (QuotientGroup.mk' C) from hm))

theorem orderOf_pow_prime_pow_pred {G : Type*} [Group G] {r : ℕ} [Fact r.Prime] {x : G} {j : ℕ}
    (hj : 1 ≤ j) (hx : orderOf x = r ^ j) : orderOf (x ^ (r ^ (j - 1))) = r := by
  have hr : r.Prime := Fact.out
  have hdvd : r ^ (j - 1) ∣ orderOf x := by
    rw [hx]
    exact pow_dvd_pow r (Nat.sub_le j 1)
  rw [orderOf_pow_of_dvd (pow_ne_zero _ hr.ne_zero) hdvd, hx,
    Nat.pow_div (show j - 1 ≤ j by omega) hr.pos]
  rw [show j - (j - 1) = 1 by omega, pow_one]

end CFSG.Quasithin.Vol2.Ch10Reselect
