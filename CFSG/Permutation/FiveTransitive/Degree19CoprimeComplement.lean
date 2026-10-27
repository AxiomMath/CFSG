module

public import CFSG.Permutation.FiveTransitive.Degree19SevenFiniteChecks
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

namespace CFSG

namespace FiveTransitive.Degree19

open MulAction Subgroup
open scoped Pointwise

private theorem small_divisor_eq_of_mod_five
    (n d : ℕ)
    (hn : n = 2 ∨ n = 3 ∨ n = 8 ∨ n = 27)
    (hd : d ∣ n)
    (hmod : n % 5 = d % 5) :
    d = n := by
  rcases hn with rfl | rfl | rfl | rfl
  all_goals
    have hdle : d ≤ _ :=
      Nat.le_of_dvd (by norm_num) hd
    interval_cases d <;> norm_num at *

@[expose] def fixedPointsSubgroup
    (T R : Type) [Group T] [Group R]
    [MulDistribMulAction T R] :
    Subgroup R where
  carrier := MulAction.fixedPoints T R
  one_mem' := by
    change ∀ t : T, t • (1 : R) = 1
    exact fun t => smul_one t
  mul_mem' := by
    intro a b ha hb
    change ∀ t : T, t • (a * b) = a * b
    intro t
    rw [smul_mul', ha t, hb t]
  inv_mem' := by
    intro a ha
    change ∀ t : T, t • a⁻¹ = a⁻¹
    intro t
    rw [smul_inv', ha t]

theorem five_group_action_on_small_group_is_trivial
    (T R : Type) [Group T] [Group R]
    [Fintype T] [Fintype R]
    [MulDistribMulAction T R]
    (hT : IsPGroup 5 T)
    (hRcard :
      Nat.card R = 2 ∨ Nat.card R = 3 ∨
        Nat.card R = 8 ∨ Nat.card R = 27) :
    ∀ t : T, ∀ r : R, t • r = r := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let F : Subgroup R :=
    fixedPointsSubgroup T R
  have hFset :
      (F : Set R) = MulAction.fixedPoints T R :=
    rfl
  let eF :
      F ≃ MulAction.fixedPoints T R :=
    Set.equivOfEq hFset
  have hmod :
      Nat.card R % 5 = Nat.card F % 5 := by
    have h :=
      hT.card_modEq_card_fixedPoints R
    change
      Nat.card R % 5 =
        Nat.card (MulAction.fixedPoints T R) % 5 at h
    calc
      Nat.card R % 5 =
          Nat.card (MulAction.fixedPoints T R) % 5 :=
        h
      _ = Nat.card F % 5 :=
        congrArg (fun n => n % 5)
          (Nat.card_congr eF).symm
  have hdiv : Nat.card F ∣ Nat.card R :=
    Subgroup.card_subgroup_dvd_card F
  have hFcard : Nat.card F = Nat.card R :=
    small_divisor_eq_of_mod_five
      (Nat.card R) (Nat.card F) hRcard hdiv hmod
  have hFtop : F = ⊤ :=
    Subgroup.eq_top_of_card_eq F hFcard
  intro t r
  have hr : r ∈ F := by
    rw [hFtop]
    exact Subgroup.mem_top r
  exact hr t

private theorem exists_fixed_point_of_five_group_action
    (T α : Type) [Group T] [Fintype T]
    [Fintype α] [MulAction T α]
    (hT : IsPGroup 5 T)
    (hnotFive : ¬5 ∣ Nat.card α) :
    ∃ a : α, ∀ t : T, t • a = a := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨a, ha⟩ :=
    hT.nonempty_fixed_point_of_prime_not_dvd_card
      α hnotFive
  exact ⟨a, ha⟩

private theorem fixed_sylow_small_action_is_trivial
    (T Q : Type) [Group T] [Group Q]
    [Fintype T] [Fintype Q]
    [MulDistribMulAction T Q]
    (hT : IsPGroup 5 T)
    {p : ℕ} [Fact p.Prime]
    (R : Sylow p Q)
    (hRfixed : ∀ t : T, t • R = R)
    (hRcard :
      Nat.card R = 2 ∨ Nat.card R = 3 ∨
        Nat.card R = 8 ∨ Nat.card R = 27) :
    ∀ t : T, ∀ r : R, t • (r : Q) = r := by
  classical
  let rsmul : SMul T R :=
    { smul := fun t r =>
        (⟨t • (r : Q), by
          have hr :
              t • (r : Q) ∈
                (t • R : Sylow p Q) := by
            exact Subgroup.smul_mem_pointwise_smul
              (r : Q) t (R : Subgroup Q) r.prop
          rwa [hRfixed t] at hr⟩ : R) }
  letI : SMul T R := rsmul
  letI : MulDistribMulAction T R :=
    Subtype.coe_injective.mulDistribMulAction
      (R : Subgroup Q).subtype (fun _ _ => rfl)
  have htr :=
    five_group_action_on_small_group_is_trivial
      T R hT hRcard
  intro t r
  exact congrArg Subtype.val (htr t r)

private theorem normal_complement_le_centralizer_of_sylow_cards
    {K : Type} [Group K] [Fintype K]
    (T : Sylow 5 K)
    (Q : Subgroup K) [Q.Normal]
    (a b : ℕ)
    (haCases : a = 2 ∨ a = 8)
    (hbCases : b = 3 ∨ b = 27)
    (hQcard : Nat.card Q = a * b)
    (hTwo : ∀ A : Sylow 2 Q, Nat.card A = a)
    (hThree : ∀ B : Sylow 3 Q, Nat.card B = b) :
    Q ≤ Subgroup.centralizer (T : Set K) := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  letI : MulDistribMulAction T Q :=
    MulDistribMulAction.compHom Q
      ((MulAut.conjNormal (H := Q)).comp
        (T : Subgroup K).subtype)
  have haPos : 0 < a := by
    rcases haCases with rfl | rfl <;> norm_num
  have hbPos : 0 < b := by
    rcases hbCases with rfl | rfl <;> norm_num
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  let A₀ : Sylow 2 Q := Sylow.nonempty.some
  have hA₀index : A₀.index = b := by
    have hindexCard := A₀.index_mul_card
    rw [hTwo A₀, hQcard] at hindexCard
    have hcancel :
        a * A₀.index = a * b := by
      simpa [Nat.mul_comm] using hindexCard
    exact Nat.mul_left_cancel haPos hcancel
  have hcardSylowTwoDvd :
      Nat.card (Sylow 2 Q) ∣ b := by
    rw [← hA₀index]
    exact A₀.card_dvd_index
  have hfiveNotDvdB : ¬5 ∣ b := by
    rcases hbCases with rfl | rfl <;> norm_num
  have hfiveNotDvdSylowTwo :
      ¬5 ∣ Nat.card (Sylow 2 Q) :=
    fun h =>
      hfiveNotDvdB (h.trans hcardSylowTwoDvd)
  obtain ⟨A, hAfixed⟩ :=
    exists_fixed_point_of_five_group_action
      T (Sylow 2 Q) T.2 hfiveNotDvdSylowTwo
  have hAcard : Nat.card A = a :=
    hTwo A
  have hAsmall :
      Nat.card A = 2 ∨ Nat.card A = 3 ∨
        Nat.card A = 8 ∨ Nat.card A = 27 := by
    rcases haCases with ha | ha
    · exact Or.inl (hAcard.trans ha)
    · exact Or.inr (Or.inr
        (Or.inl (hAcard.trans ha)))
  have hAtrivial :
      ∀ t : T, ∀ x : A, t • (x : Q) = x :=
    fixed_sylow_small_action_is_trivial
      T Q T.2 A hAfixed hAsmall
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let B₀ : Sylow 3 Q := Sylow.nonempty.some
  have hB₀index : B₀.index = a := by
    have hindexCard := B₀.index_mul_card
    rw [hThree B₀, hQcard] at hindexCard
    have hcancel :
        b * B₀.index = b * a := by
      simpa [Nat.mul_comm] using hindexCard
    exact Nat.mul_left_cancel hbPos hcancel
  have hcardSylowThreeDvd :
      Nat.card (Sylow 3 Q) ∣ a := by
    rw [← hB₀index]
    exact B₀.card_dvd_index
  have hfiveNotDvdA : ¬5 ∣ a := by
    rcases haCases with rfl | rfl <;> norm_num
  have hfiveNotDvdSylowThree :
      ¬5 ∣ Nat.card (Sylow 3 Q) :=
    fun h =>
      hfiveNotDvdA (h.trans hcardSylowThreeDvd)
  obtain ⟨B, hBfixed⟩ :=
    exists_fixed_point_of_five_group_action
      T (Sylow 3 Q) T.2 hfiveNotDvdSylowThree
  have hBcard : Nat.card B = b :=
    hThree B
  have hBsmall :
      Nat.card B = 2 ∨ Nat.card B = 3 ∨
        Nat.card B = 8 ∨ Nat.card B = 27 := by
    rcases hbCases with hb | hb
    · exact Or.inr (Or.inl
        (hBcard.trans hb))
    · exact Or.inr (Or.inr
        (Or.inr (hBcard.trans hb)))
  have hBtrivial :
      ∀ t : T, ∀ x : B, t • (x : Q) = x :=
    fixed_sylow_small_action_is_trivial
      T Q T.2 B hBfixed hBsmall
  let C : Subgroup Q :=
    (Subgroup.centralizer (T : Set K)).comap
      Q.subtype
  have hAleC : (A : Subgroup Q) ≤ C := by
    intro x hx
    change (x : K) ∈
      Subgroup.centralizer (T : Set K)
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    let tT : T := ⟨t, ht⟩
    let xA : A := ⟨x, hx⟩
    have hfixQ := hAtrivial tT xA
    have hfixK := congrArg Q.subtype hfixQ
    change
      (tT : K) * (xA : Q) * (tT : K)⁻¹ =
        (xA : Q) at hfixK
    calc
      t * (x : K) =
          (t * (x : K) * t⁻¹) * t := by
        group
      _ = (x : K) * t := by
        simpa only [tT, xA] using
          congrArg (fun y : K => y * t) hfixK
  have hBleC : (B : Subgroup Q) ≤ C := by
    intro x hx
    change (x : K) ∈
      Subgroup.centralizer (T : Set K)
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    let tT : T := ⟨t, ht⟩
    let xB : B := ⟨x, hx⟩
    have hfixQ := hBtrivial tT xB
    have hfixK := congrArg Q.subtype hfixQ
    change
      (tT : K) * (xB : Q) * (tT : K)⁻¹ =
        (xB : Q) at hfixK
    calc
      t * (x : K) =
          (t * (x : K) * t⁻¹) * t := by
        group
      _ = (x : K) * t := by
        simpa only [tT, xB] using
          congrArg (fun y : K => y * t) hfixK
  have hABcoprime :
      Nat.Coprime (Nat.card A) (Nat.card B) := by
    rw [hAcard, hBcard]
    rcases haCases with rfl | rfl <;>
      rcases hbCases with rfl | rfl <;>
      norm_num
  let AB : Subgroup Q :=
    (A : Subgroup Q) ⊔ (B : Subgroup Q)
  have hprodDvdSup :
      Nat.card A * Nat.card B ∣
        Nat.card AB :=
    hABcoprime.mul_dvd_of_dvd_of_dvd
      (Subgroup.card_dvd_of_le (show
        (A : Subgroup Q) ≤ AB by
          dsimp only [AB]
          exact le_sup_left))
      (Subgroup.card_dvd_of_le (show
        (B : Subgroup Q) ≤ AB by
          dsimp only [AB]
          exact le_sup_right))
  have hQcardDvdSup :
      Nat.card Q ∣
        Nat.card AB := by
    rw [hQcard, ← hAcard, ← hBcard]
    exact hprodDvdSup
  have hSupCardDvdQ :
      Nat.card AB ∣
        Nat.card Q :=
    Subgroup.card_subgroup_dvd_card _
  have hSupCard :
      Nat.card AB =
        Nat.card Q :=
    Nat.dvd_antisymm hSupCardDvdQ hQcardDvdSup
  have hSupTop :
      AB = ⊤ :=
    Subgroup.eq_top_of_card_eq _ hSupCard
  have htopLeC : (⊤ : Subgroup Q) ≤ C := by
    rw [← hSupTop]
    dsimp only [AB]
    exact sup_le hAleC hBleC
  intro q hq
  let qQ : Q := ⟨q, hq⟩
  exact htopLeC (Subgroup.mem_top qQ)

private theorem normal_complement_le_centralizer_of_card_six_or_two_sixteen
    {K : Type} [Group K] [Fintype K]
    (T : Sylow 5 K)
    (Q : Subgroup K) [Q.Normal]
    (hQcard : Nat.card Q = 6 ∨ Nat.card Q = 216) :
    Q ≤ Subgroup.centralizer (T : Set K) := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rcases hQcard with hQcard | hQcard
  · refine normal_complement_le_centralizer_of_sylow_cards
      T Q 2 3 (Or.inl rfl) (Or.inl rfl) ?_ ?_ ?_
    · simpa using hQcard
    · intro A
      rw [A.card_eq_multiplicity, hQcard]
      rw [show 6 = 2 ^ 1 * 3 ^ 1 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply,
        (show Nat.Prime 2 by norm_num).factorization_pow,
        (show Nat.Prime 3 by norm_num).factorization_pow]
      norm_num
    · intro B
      rw [B.card_eq_multiplicity, hQcard]
      rw [show 6 = 2 ^ 1 * 3 ^ 1 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply,
        (show Nat.Prime 2 by norm_num).factorization_pow,
        (show Nat.Prime 3 by norm_num).factorization_pow]
      norm_num
  · refine normal_complement_le_centralizer_of_sylow_cards
      T Q 8 27 (Or.inr rfl) (Or.inr rfl) ?_ ?_ ?_
    · simpa using hQcard
    · intro A
      rw [A.card_eq_multiplicity, hQcard]
      rw [show 216 = 2 ^ 3 * 3 ^ 3 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply,
        (show Nat.Prime 2 by norm_num).factorization_pow,
        (show Nat.Prime 3 by norm_num).factorization_pow]
      norm_num
    · intro B
      rw [B.card_eq_multiplicity, hQcard]
      rw [show 216 = 2 ^ 3 * 3 ^ 3 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply,
        (show Nat.Prime 2 by norm_num).factorization_pow,
        (show Nat.Prime 3 by norm_num).factorization_pow]
      norm_num

theorem no_self_normalizing_sylow_five_with_small_normal_complement
    {K : Type} [Group K] [Fintype K]
    (T : Sylow 5 K)
    (Q : Subgroup K) [Q.Normal]
    (hTcard : Nat.card T = 5)
    (hnormalizer :
      Nat.card (Subgroup.normalizer (T : Set K)) = 5)
    (hcomplement : IsComplement' Q T)
    (hQcard : Nat.card Q = 6 ∨ Nat.card Q = 216) :
    False := by
  have hQcentralizer :
      Q ≤ Subgroup.centralizer (T : Set K) :=
    normal_complement_le_centralizer_of_card_six_or_two_sixteen
      T Q hQcard
  have hQnormalizer :
      Q ≤ Subgroup.normalizer (T : Set K) :=
    hQcentralizer.trans
      (Subgroup.centralizer_le_normalizer (T : Set K))
  have hTnormalizer :
      (T : Subgroup K) ≤
        Subgroup.normalizer (T : Set K) :=
    Subgroup.le_normalizer
  have hnormalizerTop :
      Subgroup.normalizer (T : Set K) = ⊤ := by
    apply top_unique
    rw [← hcomplement.sup_eq_top]
    exact sup_le hQnormalizer hTnormalizer
  have hKcard : Nat.card K = 5 := by
    calc
      Nat.card K =
          Nat.card (⊤ : Subgroup K) := by
        simp
      _ =
          Nat.card
            (Subgroup.normalizer (T : Set K)) := by
        rw [hnormalizerTop]
      _ = 5 := hnormalizer
  have hcardMul := hcomplement.card_mul
  rw [hTcard, hKcard] at hcardMul
  rcases hQcard with hQcard | hQcard
  · rw [hQcard] at hcardMul
    norm_num at hcardMul
  · rw [hQcard] at hcardMul
    norm_num at hcardMul

end FiveTransitive.Degree19

end CFSG
