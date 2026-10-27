module

public import CFSG.RankThree.PartTwo.Sec21.Hering214EThmA
public import CFSG.RankThree.PartTwo.Sec21.Item21Statements
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44Basic
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.Blueprint
open Item211Res2Proof Hering214Even

namespace Hering214Even

@[expose] def MultiplierOdd (X : Type) [Group X] : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (Z : Subgroup K) [Z.Normal], Group.IsPerfect K →
    Z ≤ Subgroup.center K → Nonempty (K ⧸ Z ≃* X) → Odd (Nat.card Z)

@[expose] def Item214EvenThetaFacts : Prop :=
  ∀ (X : Type) [Group X] [Finite X],
    (Nonempty (X ≃* NativeSporadic.M22) ∨ Nonempty (X ≃* NativeSporadic.HS) ∨
      Nonempty (X ≃* NativeSporadic.J2) ∨ Nonempty (X ≃* NativeSporadic.Ru) ∨
      StatedClassicalModel X .PSL 4 2 1 ∨ ChevalleyExceptionalModel X .G2 2 2) →
    EvenThetaFacts X

@[expose] def Item214EvenMultOdd : Prop :=
  ∀ (X : Type) [Group X] [Finite X],
    (Nonempty (X ≃* NativeSporadic.M23) ∨ Nonempty (X ≃* NativeSporadic.M24) ∨
      Nonempty (X ≃* NativeSporadic.He) ∨ Nonempty (X ≃* NativeSporadic.J4) ∨
      StatedClassicalModel X .PSL 5 2 1 ∨
      (∃ n : ℕ, 4 ≤ n ∧ Even n ∧ ChevalleyExceptionalModel X .G2 2 n) ∨
      (∃ n : ℕ, 0 < n ∧ Even n ∧ ChevalleyExceptionalModel X .trialityD4 2 n) ∨
      (∃ n : ℕ, 0 < n ∧ Even n ∧
        (Nonempty (X ≃* projSp 2 (GaloisField 2 n)) ∨ Nonempty (X ≃* projSU 4 2 n))) ∨
      Nonempty (X ≃* projSU 5 2 2)) →
    MultiplierOdd X

@[expose] def Item214EvenTypeC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → Even (Nat.card (aschbacherSolvableCore 3 L)) →
    (∃ n : ℕ, 0 < n ∧ Even n ∧
      ((Nonempty (lBar L ≃* projSL 3 (GaloisField 2 n)) ∧ Sec4.IsTypeCOn A L) ∨
        (Nonempty (lBar L ≃* SL3 n) ∧ IsTypeCOnBarSL A L))) →
    Nat.card A = 3 ^ 3 → ∃ U' ∈ fourGroupsMinus E, U' ≤ L

end Hering214Even

theorem exists_fourGroupsMinus_of_even_pair (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6)
    (h211 : Item211) (h213 : Item213) (hA : Item214EvenThetaFacts) (hK0 : Item214EvenMultOdd)
    (hB : Item214EvenTypeC) {G : Type} [Group G] [Finite G] {A E U : Subgroup G} {c : G}
    {L : Subgroup G} (hpair : Sec21Pair G A E U c L)
    (hnotU4 : ¬ ∃ n : ℕ, 1 < n ∧ Odd n ∧ Nonempty (lBar L ≃* projSU 4 2 n))
    (hnotdec : ¬ (U ∈ fourGroupsMinus E ∧ ∀ e ∈ E, ∃ x ∈ E ⊓ Subgroup.centralizer (U : Set G),
      ∃ y ∈ E ⊓ L, e = x * y))
    (h81 : Nat.card A ≠ 3 ^ 4) (heven : Even (Nat.card (aschbacherSolvableCore 3 L)))
    (h1 : Sec4.IsHeisCentral ↥(Sec13.lBarA c L A) (lBar L) →
      Sec4.IsTripleCover (lBar L) NativeSporadic.M22 → Nat.card A = 3 ^ 3 →
      CFSG.Assembly.IsElemAbelian 3 (starOf A L) → Nat.card (starOf A L) = 9 →
      ∃ U' ∈ fourGroupsMinus E, U' ≤ L) :
    ∃ U' ∈ fourGroupsMinus E, U' ≤ L := by
  have hPF := Item211LieProof.pairFacts h45 h66 hpair
  have hq := h213 G A E U c L hpair
  haveI : Group.IsPerfect ↥L := hq.1
  have hθc : aschbacherSolvableCore 3 ↥L ≤ Subgroup.center ↥L := by
    obtain ⟨hTs, hTch, -⟩ := solvable_prime_complement_core_characterization (H := ↥L)
      Nat.prime_three
    have : (aschbacherSolvableCore 3 ↥L).Normal := Subgroup.normal_of_characteristic _
    haveI : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hq.2.1
    exact Sec4.Census.le_of_isSolvable_of_normal inferInstance hTs
  have h3 := hpair.standing.toTheoremFourHyp.localRank_three.le
  have hThmA : (Nonempty (lBar L ≃* NativeSporadic.M22) ∨ Nonempty (lBar L ≃* NativeSporadic.HS) ∨
      Nonempty (lBar L ≃* NativeSporadic.J2) ∨ Nonempty (lBar L ≃* NativeSporadic.Ru) ∨
      StatedClassicalModel (lBar L) .PSL 4 2 1 ∨
      ChevalleyExceptionalModel (lBar L) .G2 2 2) → ∃ U' ∈ fourGroupsMinus E, U' ≤ L :=
    fun h => (false_of_even_of_facts hPF h3 hθc hnotdec heven (hA _ h)).elim
  have hOdd : Odd (Nat.card (aschbacherSolvableCore 3 L)) → ∃ U' ∈ fourGroupsMinus E, U' ≤ L :=
    fun h => (Nat.not_even_iff_odd.mpr h heven).elim
  have hK0' : (Nonempty (lBar L ≃* NativeSporadic.M23) ∨ Nonempty (lBar L ≃* NativeSporadic.M24) ∨
      Nonempty (lBar L ≃* NativeSporadic.He) ∨ Nonempty (lBar L ≃* NativeSporadic.J4) ∨
      StatedClassicalModel (lBar L) .PSL 5 2 1 ∨
      (∃ n : ℕ, 4 ≤ n ∧ Even n ∧ ChevalleyExceptionalModel (lBar L) .G2 2 n) ∨
      (∃ n : ℕ, 0 < n ∧ Even n ∧ ChevalleyExceptionalModel (lBar L) .trialityD4 2 n) ∨
      (∃ n : ℕ, 0 < n ∧ Even n ∧
        (Nonempty (lBar L ≃* projSp 2 (GaloisField 2 n)) ∨
          Nonempty (lBar L ≃* projSU 4 2 n))) ∨
      Nonempty (lBar L ≃* projSU 5 2 2)) → ∃ U' ∈ fourGroupsMinus E, U' ≤ L := by
    intro h
    obtain ⟨-, hTch, -⟩ := solvable_prime_complement_core_characterization (H := ↥L)
      Nat.prime_three
    haveI : (aschbacherSolvableCore 3 ↥L).Normal := Subgroup.normal_of_characteristic _
    exact hOdd (hK0 _ h ↥L (aschbacherSolvableCore 3 ↥L) inferInstance hθc ⟨MulEquiv.refl _⟩)
  rcases h211 G A E U c L hpair with ⟨hH, hT, hA27, hS, hS9⟩ | ⟨h, -⟩ | ⟨h | h, -⟩ |
      ⟨h | h, -⟩ | ⟨h, -⟩ | ⟨h | h, -⟩ | ⟨h7, hA27, -⟩ | ⟨⟨n, hn, he, h | h⟩, -⟩ |
      ⟨⟨n, hn, he, h | h⟩ | h, -⟩ | ⟨-, hA81, -⟩ | ⟨-, hA81, -⟩ | ⟨h | h, -⟩ | ⟨-, hA81, -⟩
  · exact h1 hH hT hA27 hS hS9
  · exact hThmA (Or.inl h)
  · exact hK0' (Or.inl h)
  · exact hThmA (Or.inr (Or.inl h))
  · exact hK0' (Or.inr (Or.inl h))
  · exact hK0' (Or.inr (Or.inr (Or.inl h)))
  · exact hThmA (Or.inr (Or.inr (Or.inl h)))
  · exact hThmA (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact hK0' (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact hB G A E U c L hpair heven h7 hA27
  ·
    rcases Nat.lt_or_ge n 4 with hn4 | hn4
    · have hn2 : n = 2 := by obtain ⟨k, rfl⟩ := he; omega
      subst hn2
      exact hThmA (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
    · exact hK0' (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn4, he, h⟩))))))
  · exact hK0' (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn, he, h⟩)))))))
  · exact hK0' (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨n, hn, he, Or.inl h⟩))))))))
  · exact hK0' (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨n, hn, he, Or.inr h⟩))))))))
  · exact hK0' (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))
  · exact absurd hA81 h81
  · exact absurd hA81 h81
  · exact hThmA (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact hK0' (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact absurd hA81 h81

end CFSG.RankThree.PartTwo.Sec21
