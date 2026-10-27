module

public import CFSG.Permutation.FiveTransitive.Degree19LongPrimeNormalizers
public import CFSG.Permutation.FiveTransitive.Degree19Arithmetic
public import CFSG.Permutation.FiveTransitive.Degree19FiveNormalizer
public import CFSG.Permutation.FiveTransitive.Degree19StabilizerFactor

public section

namespace CFSG

namespace FiveTransitive.Degree19

open MulAction SubMulAction Subgroup

theorem five_point_stabilizer_card_eq_two_or_seventy_two
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 19)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    Nat.card (fixingSubgroup P s) = 2 ∨
      Nat.card (fixingSubgroup P s) = 72 := by
  classical
  let H : Subgroup P := fixingSubgroup P s
  let h := Nat.card H
  have hdiv : h ∣ 497664 :=
    five_point_stabilizer_card_dvd_four_hundred_ninety_seven_thousand
      X P hcard h5 hnotAlt s hs
  have hP5 : MulAction.IsMultiplyPretransitive P X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨q, hq⟩ :=
      h5 a b a.injective b.injective
    refine ⟨q, ?_⟩
    ext i
    exact hq i
  have hfixIndex := hP5.index_of_fixingSubgroup_mul hs
  rw [Nat.card_eq_fintype_card, hcard] at hfixIndex
  norm_num at hfixIndex
  have hHindex : H.index = 1395360 := by
    change (fixingSubgroup P s).index = 1395360
    omega
  have hHindexCard := H.index_mul_card
  have hPcard : Nat.card P = 1395360 * h := by
    rw [hHindex] at hHindexCard
    exact hHindexCard.symm
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let S₅ : Sylow 5 P := Sylow.nonempty.some
  have hfive :=
    sylow_five_normalizer_card_eq_one_twenty
      X P hcard h5 hnotAlt s hs S₅
  have hmodFive : (3 * h) % 5 = 1 := by
    exact hfive.2
  letI : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  let S₁₇ : Sylow 17 P := Sylow.nonempty.some
  have hS₁₇card : Nat.card S₁₇ = 17 :=
    sylow_long_prime_card_eq_prime
      P h hPcard hdiv (Or.inl rfl) S₁₇
  let C₁₇ : Subgroup P :=
    Subgroup.centralizer (S₁₇ : Set P)
  let N₁₇ : Subgroup P :=
    Subgroup.normalizer (S₁₇ : Set P)
  let r₁₇ := C₁₇.relIndex N₁₇
  have hseventeen :
      r₁₇ ∣ 16 ∧
        0 < r₁₇ ∧
        N₁₇.index % 17 = 1 ∧
        r₁₇ * N₁₇.index * 17 = Nat.card P := by
    simpa only [C₁₇, N₁₇, r₁₇] using
      long_prime_normalizer_constraints
        X P h5 hnotAlt (p := 17) (f := 2)
          (by norm_num) (by norm_num) (by norm_num)
          (by omega) S₁₇ hS₁₇card
  have hfixedSeventeen
      (a : Degree15.NonidentitySylowElements 17 P) :
      Fintype.card
          (MulAction.fixedBy X
            (Degree15.nonidentitySylowElementVal 17 P a)) = 2 := by
    rcases a with ⟨T, u⟩
    change
      Fintype.card
          (MulAction.fixedBy X ((u.1 : T) : P)) = 2
    have hTcard : Nat.card T = 17 :=
      Degree15.sylow_card_eq_of_card_eq
        S₁₇ hS₁₇card T
    have huorderT : orderOf u.1 = 17 :=
      Degree15.orderOf_eq_prime_of_card_eq_prime
        hTcard u.2
    let g : Equiv.Perm X := ((u.1 : T) : P)
    have hgorder : orderOf g = 17 := by
      calc
        orderOf g = orderOf ((u.1 : T) : P) :=
          Subgroup.orderOf_coe _
        _ = orderOf u.1 :=
          Subgroup.orderOf_coe _
        _ = 17 := huorderT
    have hgcycle : g.IsCycle :=
      Equiv.Perm.isCycle_of_prime_order' (by
        rw [hgorder]
        norm_num) (by
          rw [hcard, hgorder]
          norm_num)
    have hgsupport : g.support.card = 17 := by
      rw [← hgcycle.orderOf, hgorder]
    rw [Degree15.card_fixedBy_subgroup_perm, hcard]
    change 19 - g.support.card = 2
    rw [hgsupport]
  have hP2 : MulAction.IsMultiplyPretransitive P X 2 := by
    letI : MulAction.IsMultiplyPretransitive P X 5 := hP5
    exact MulAction.isMultiplyPretransitive_of_le
      (G := P) (α := X) (m := 2) (n := 5)
        (by omega) (by
          rw [Nat.card_eq_fintype_card, hcard]
          omega)
  have hseventeenBoundRaw :
      N₁₇.index * (17 - 1) *
          (2 : ℕ).descFactorial 2 ≤ Nat.card P := by
    simpa only [N₁₇] using
      nonidentity_sylow_fixed_embedding_bound
        X P (p := 17) (m := 2) (f := 2)
          (by norm_num) S₁₇ hS₁₇card (by omega)
          hfixedSeventeen hP2
  have hseventeenBound :
      N₁₇.index * 32 ≤ Nat.card P := by
    norm_num [Nat.descFactorial] at hseventeenBoundRaw
    rw [Nat.card_eq_fintype_card]
    nlinarith
  have hr₁₇Lower : 2 ≤ r₁₇ := by
    have hindexPos : 0 < N₁₇.index :=
      Nat.pos_of_ne_zero
        Subgroup.index_ne_zero_of_finite
    nlinarith [hseventeenBound,
      hseventeen.2.2.2]
  have hseventeenDivided :
      r₁₇ * N₁₇.index = 82080 * h := by
    rw [hPcard] at hseventeen
    nlinarith [hseventeen.2.2.2]
  have hmodSeventeen :
      (4 * h) % 17 = r₁₇ % 17 := by
    calc
      (4 * h) % 17 = (82080 * h) % 17 := by
        simp [Nat.mul_mod]
      _ = (r₁₇ * N₁₇.index) % 17 :=
        congrArg (fun n => n % 17)
          hseventeenDivided.symm
      _ = r₁₇ % 17 := by
        rw [Nat.mul_mod, hseventeen.2.2.1]
        simp
  letI : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  let S₁₉ : Sylow 19 P := Sylow.nonempty.some
  have hS₁₉card : Nat.card S₁₉ = 19 :=
    sylow_long_prime_card_eq_prime
      P h hPcard hdiv (Or.inr rfl) S₁₉
  let C₁₉ : Subgroup P :=
    Subgroup.centralizer (S₁₉ : Set P)
  let N₁₉ : Subgroup P :=
    Subgroup.normalizer (S₁₉ : Set P)
  let r₁₉ := C₁₉.relIndex N₁₉
  have hnineteen :
      r₁₉ ∣ 18 ∧
        0 < r₁₉ ∧
        N₁₉.index % 19 = 1 ∧
        r₁₉ * N₁₉.index * 19 = Nat.card P := by
    simpa only [C₁₉, N₁₉, r₁₉] using
      long_prime_normalizer_constraints
        X P h5 hnotAlt (p := 19) (f := 0)
          (by norm_num) (by norm_num) (by norm_num)
          (by omega) S₁₉ hS₁₉card
  have hnineteenDivided :
      r₁₉ * N₁₉.index = 73440 * h := by
    rw [hPcard] at hnineteen
    nlinarith [hnineteen.2.2.2]
  have hmodNineteen :
      (5 * h) % 19 = r₁₉ % 19 := by
    calc
      (5 * h) % 19 = (73440 * h) % 19 := by
        simp [Nat.mul_mod]
      _ = (r₁₉ * N₁₉.index) % 19 :=
        congrArg (fun n => n % 19)
          hnineteenDivided.symm
      _ = r₁₉ % 19 := by
        rw [Nat.mul_mod, hnineteen.2.2.1]
        simp
  have hr₁₇Mem : r₁₇ ∈ Nat.divisors 16 :=
    Nat.mem_divisors.mpr
      ⟨hseventeen.1, by norm_num⟩
  let r₁₇' : SeventeenNormalizerRatio :=
    ⟨r₁₇, hr₁₇Mem⟩
  have hr₁₇Cases :=
    seventeen_normalizer_ratio_cases r₁₇' hr₁₇Lower
  change
    r₁₇ = 2 ∨ r₁₇ = 4 ∨
      r₁₇ = 8 ∨ r₁₇ = 16 at hr₁₇Cases
  have hmodSeventeenCases :
      (4 * h) % 17 = 2 ∨
        (4 * h) % 17 = 4 ∨
        (4 * h) % 17 = 8 ∨
        (4 * h) % 17 = 16 := by
    rcases hr₁₇Cases with hr | hr | hr | hr
    all_goals rw [hmodSeventeen, hr]
    all_goals norm_num
  have hr₁₉Mem : r₁₉ ∈ Nat.divisors 18 :=
    Nat.mem_divisors.mpr
      ⟨hnineteen.1, by norm_num⟩
  let r₁₉' : NineteenNormalizerRatio :=
    ⟨r₁₉, hr₁₉Mem⟩
  have hr₁₉Cases :=
    nineteen_normalizer_ratio_cases r₁₉'
  change
    r₁₉ = 1 ∨ r₁₉ = 2 ∨ r₁₉ = 3 ∨
      r₁₉ = 6 ∨ r₁₉ = 9 ∨
      r₁₉ = 18 at hr₁₉Cases
  have hmodNineteenCases :
      (5 * h) % 19 = 1 ∨
        (5 * h) % 19 = 2 ∨
        (5 * h) % 19 = 3 ∨
        (5 * h) % 19 = 6 ∨
        (5 * h) % 19 = 9 ∨
        (5 * h) % 19 = 18 := by
    rcases hr₁₉Cases with hr | hr | hr | hr | hr | hr
    all_goals rw [hmodNineteen, hr]
    all_goals norm_num
  obtain ⟨a, ha, b, hb, hpower⟩ :=
    exists_two_three_power_of_dvd_four_hundred_ninety_seven_thousand
      hdiv
  let a' : Fin 12 := ⟨a, by omega⟩
  let b' : Fin 6 := ⟨b, by omega⟩
  have harithmetic :=
    stabilizer_factor_arithmetic a' b'
  dsimp [stabilizerFactorArithmeticPredicate,
    a', b'] at harithmetic
  have hpowerCases :
      2 ^ a * 3 ^ b = 2 ∨
        2 ^ a * 3 ^ b = 72 :=
    harithmetic
      (by simpa [← hpower] using hmodFive)
      (by simpa [← hpower] using
        hmodSeventeenCases)
      (by simpa [← hpower] using
        hmodNineteenCases)
  change h = 2 ∨ h = 72
  rwa [hpower]

end FiveTransitive.Degree19

end CFSG
