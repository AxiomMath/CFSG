module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixOrderThree
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinOddCoreParity
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSevenFiberBound
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinCosetRepresentative
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseJNCoset
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

/-!
The source restriction (7) is the only group-theoretic input needed to
exclude fibres of size at least five.  This module performs the transport
from a positive `b_n` to a representative in `J_n`, applies restriction (6),
and feeds the resulting order-three odd subgroup into restriction (7).
-/

public theorem firstCase_klein_high_fiber_vanish_of_restrictionSeven
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat))
    (h7 : ∀ (n : ℕ) (y : G) (X : Subgroup G),
      4 ≤ n → y ∈ firstCaseJ c n → X ≠ ⊥ → X ≤ c.Hhat →
      Nat.Coprime 2 (Nat.card X) →
      (∀ x : G, x ∈ X → x ∈ invertedElements c.Hhat y) →
      Even (Nat.card (Subgroup.centralizer (X : Set G))) →
      Even (Nat.card ((Subgroup.normalizer (X : Set G) ⊓ c.Hhat : Subgroup G))) →
      Nat.card c.U = Nat.card X ∧ Nat.card X = 3 ∧ n = 4 ∧
        (let D := c.Hhat ⊓ conjugateSubgroup c.Hhat y
         let N := D ⊓ (twoCoreOf c.Hhat ⊔ c.U)
         (N.subgroupOf D).index = 6)) :
    ∀ n : ℕ, 5 ≤ n → cosetInvolution_b c.Hhat n = 0 := by
  classical
  intro n hn
  by_contra hbn
  have hJn_pos : 0 < Nat.card {x : G // x ∈ firstCaseJ c n} := by
    rw [firstCase_J_n_card]
    have hnpos : 0 < n := by omega
    exact Nat.mul_pos hnpos (Nat.pos_of_ne_zero hbn)
  obtain ⟨y, hyJ⟩ := (Nat.card_pos_iff.mp hJn_pos).1
  have hyJ' : IsInvolution y ∧ y ∉ c.Hhat ∧
      firstCaseCosetInvolutions c y = n := by
    simpa [firstCaseJ] using hyJ
  have hy : IsInvolution y := hyJ'.1
  have hyH : y ∉ c.Hhat := hyJ'.2.1
  have hcoset : firstCaseCosetInvolutions c y = n := hyJ'.2.2
  have hI : 4 ≤ Nat.card {x : G // x ∈ invertedElements c.Hhat y} := by
    rw [← firstCase_klein_coset_involution_card_eq c hy hyH, hcoset]
    omega
  obtain ⟨s, x, hsI, hsD, hsy,
      hbranch⟩ := firstCase_klein_restrictionSix_order_three
    hmin c hfirst hklein hy hyH hI
  rcases hbranch with hfy | hfsy
  · let D : Subgroup G := c.Hhat ⊓ conjugateSubgroup c.Hhat y
    let X : Subgroup G := Subgroup.zpowers x
    have hone : (1 : G) ∈ invertedElements
        (oddCoreOf (c.Hhat ⊓ conjugateSubgroup c.Hhat y : Subgroup G)) y := by
      exact ⟨(oddCoreOf (c.Hhat ⊓ conjugateSubgroup c.Hhat y : Subgroup G)).one_mem,
        by simp⟩
    have hfib_ne : Nat.card {z : G // z ∈ invertedElements
        (oddCoreOf (c.Hhat ⊓ conjugateSubgroup c.Hhat y : Subgroup G)) y} ≠ 1 := by
      intro hcard
      obtain ⟨z0, hz0⟩ := (Nat.card_eq_one_iff_exists.mp hcard)
      have hx_eq : (⟨x, hfy.2.2.2⟩ : {z : G // z ∈ invertedElements
          (oddCoreOf (c.Hhat ⊓ conjugateSubgroup c.Hhat y : Subgroup G)) y}) = z0 :=
        hz0 _
      have h1_eq : (⟨1, hone⟩ : {z : G // z ∈ invertedElements
          (oddCoreOf (c.Hhat ⊓ conjugateSubgroup c.Hhat y : Subgroup G)) y}) = z0 :=
        hz0 _
      have : x = 1 := congrArg Subtype.val (hx_eq.trans h1_eq.symm)
      exact hfy.2.1 this
    obtain ⟨_, hXne, hXle, hXodd, hXinv, hC, hN⟩ :=
      firstCase_klein_oddCore_parity c hy hyH hsI hsD hsy
        hfy.1 hfy.2.1 hfy.2.2.1 hfy.2.2.2
        (firstCase_klein_oddCore_inverted_card_three
          hmin c hfirst hklein hy hyH
          (firstCase_klein_restrictionSix_index_eq
            hmin c hfirst hklein hy hyH hI) hfib_ne)
    have hn4 := firstCase_klein_restrictionSeven_fiber_eq_four c h7
      (by omega) hyJ hXne hXle hXodd hXinv hC hN
    omega
  · let w : G := s * y
    have hsH : s ∈ c.Hhat := (show c.Hhat ⊓ conjugateSubgroup c.Hhat y ≤ c.Hhat
      from inf_le_left) hsD
    have hwJ : w ∈ firstCaseJ c n :=
      firstCase_klein_coset_representative_mem_J c hsH hyJ hsy hsI
    have hwI : IsInvolution w := by
      refine ⟨?_, ?_⟩
      · intro hw1
        apply hyH
        have hyEq : y = s⁻¹ * w := by simp [w]
        rw [hyEq, hw1]
        exact c.Hhat.mul_mem (c.Hhat.inv_mem hsH) (by simp)
      · dsimp [w]
        have hs2 : s * s = 1 := by simpa [pow_two] using hsI.2
        have hy2 : y * y = 1 := by simpa [pow_two] using hy.2
        calc
          (s * y) ^ 2 = s * (y * s) * y := by simp [pow_two, mul_assoc]
          _ = s * (s * y) * y := by rw [hsy]
          _ = (s * s) * (y * y) := by group
          _ = 1 := by rw [hs2, hy2]; simp
    have hwH : w ∉ c.Hhat := by
      intro hw
      apply hyH
      have hyEq : y = s⁻¹ * w := by simp [w]
      rw [hyEq]
      exact c.Hhat.mul_mem (c.Hhat.inv_mem hsH) hw
    have hconjEq : conjugateSubgroup c.Hhat w =
        conjugateSubgroup c.Hhat y := by
      dsimp [w, conjugateSubgroup]
      rw [hsy]
      exact map_conj_mul_right_eq_of_mem_normalizer y
        ⟨s, Subgroup.le_normalizer hsH⟩
    have hI_w : 4 ≤ Nat.card {z : G // z ∈ invertedElements c.Hhat w} := by
      rw [← firstCase_klein_coset_involution_card_eq c hwI hwH]
      have hcardw := firstCase_klein_coset_representative_card_eq c hsH hy hsy hsI hyH
      rw [hcardw]
      omega
    have hidx_w :
        let D := c.Hhat ⊓ conjugateSubgroup c.Hhat w
        let N := D ⊓ (twoCoreOf c.Hhat ⊔ c.U)
        (N.subgroupOf D).index = 6 := by
      have hwidx := firstCase_klein_restrictionSix_index_eq
        (y := w) hmin c hfirst hklein hwI hwH hI_w
      simpa [hconjEq] using hwidx
    have hfy' : x ∈ oddCoreOf
        (c.Hhat ⊓ conjugateSubgroup c.Hhat w : Subgroup G) ∧
        x ≠ 1 ∧ orderOf x = 3 ∧
        x ∈ invertedElements
          (oddCoreOf (c.Hhat ⊓ conjugateSubgroup c.Hhat w : Subgroup G)) w := by
      simpa [hconjEq, w] using hfsy
    have hone' : (1 : G) ∈ invertedElements
        (oddCoreOf (c.Hhat ⊓ conjugateSubgroup c.Hhat w : Subgroup G)) w := by
      exact ⟨(oddCoreOf (c.Hhat ⊓ conjugateSubgroup c.Hhat w : Subgroup G)).one_mem,
        by simp⟩
    have hfib_ne' : Nat.card {z : G // z ∈ invertedElements
        (oddCoreOf (c.Hhat ⊓ conjugateSubgroup c.Hhat w : Subgroup G)) w} ≠ 1 := by
      intro hcard
      obtain ⟨z0, hz0⟩ := (Nat.card_eq_one_iff_exists.mp hcard)
      have hx_eq : (⟨x, hfy'.2.2.2⟩ : {z : G // z ∈ invertedElements
          (oddCoreOf (c.Hhat ⊓ conjugateSubgroup c.Hhat w : Subgroup G)) w}) = z0 :=
        hz0 _
      have h1_eq : (⟨1, hone'⟩ : {z : G // z ∈ invertedElements
          (oddCoreOf (c.Hhat ⊓ conjugateSubgroup c.Hhat w : Subgroup G)) w}) = z0 :=
        hz0 _
      have : x = 1 := congrArg Subtype.val (hx_eq.trans h1_eq.symm)
      exact hfy'.2.1 this
    have hsDw : s ∈ (c.Hhat ⊓ conjugateSubgroup c.Hhat w) := by
      rw [hconjEq]
      exact hsD
    obtain ⟨_, hXne, hXle, hXodd, hXinv, hC, hN⟩ :=
      firstCase_klein_oddCore_parity c hwI hwH hsI hsDw
        (by
          change s * (s * y) = (s * y) * s
          have hs2 : s * s = 1 := by simpa [pow_two] using hsI.2
          calc
            s * (s * y) = (s * s) * y := by group
            _ = y := by rw [hs2]; simp
            _ = y * (s * s) := by rw [hs2]; simp
            _ = (y * s) * s := by group
            _ = (s * y) * s := by rw [hsy])
        hfy'.1 hfy'.2.1 hfy'.2.2.1 hfy'.2.2.2
        (firstCase_klein_oddCore_inverted_card_three
          hmin c hfirst hklein hwI hwH hidx_w hfib_ne')
    have hn4 := firstCase_klein_restrictionSeven_fiber_eq_four c h7
      (by omega) hwJ hXne hXle hXodd hXinv hC hN
    omega

end CFSG.GorensteinWalter
