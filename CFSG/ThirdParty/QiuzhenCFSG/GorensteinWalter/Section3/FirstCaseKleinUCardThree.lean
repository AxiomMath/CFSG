module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinHighFiber
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinCountDerived
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSevenCardThree
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinOddCoreParity
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinOddCoreFiberCard
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixOrderThree
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
# `|U| = 3` from the counting equations

Identity (8) and (9) give `b₄ ≠ 0`.  A contributing `J₄`-coset then
supplies, through restriction (6), an inverted order-three subgroup `X`
whose centralizer and `Ĥ`-normalizer have even order (the parity witness).
Restriction (7) then forces `|U| = 3`.
-/

public theorem firstCase_klein_U_card_three_of_count
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat))
    (K : Subgroup G) (b0 b1 b2 b3 b4 : ℕ)
    (hKHall : IsHallIn K c.FU) (hKne : K ≠ ⊥)
    (hJn : ∀ n : ℕ, n ≤ 4 →
      Nat.card {x : G // x ∈ firstCaseJ c n} =
        n * firstCaseBn b0 b1 b2 b3 b4 n)
    (h8 : 3 * b4 + b2 = 6 * (Nat.card K) ^ 2)
    (h9 : 6 * Nat.card K + b4 = 3 * b0 + 2 * b1 + b2) :
    Nat.card c.U = 3 := by
  classical
  have hKge2 : 2 ≤ Nat.card K := by
    have hKcardpos : 0 < Nat.card K := Nat.card_pos
    have hKcardne : Nat.card K ≠ 1 := by
      intro hcard
      apply hKne
      exact Subgroup.eq_bot_of_card_eq K hcard
    omega
  have h4ne : b4 ≠ 0 :=
    firstCase_klein_b4_ne_zero_of_equations (Nat.card K) b0 b1 b2 b4 h8 h9 hKge2
  have hb4 : cosetInvolution_b c.Hhat 4 = b4 := by
    have hJ4card : Nat.card {x : G // x ∈ firstCaseJ c 4} =
        4 * cosetInvolution_b c.Hhat 4 := firstCase_J_n_card c 4
    have hJ4b : Nat.card {x : G // x ∈ firstCaseJ c 4} =
        4 * firstCaseBn b0 b1 b2 b3 b4 4 := by
      simpa using hJn 4 (by norm_num)
    have hb4' : 4 * cosetInvolution_b c.Hhat 4 = 4 * b4 := by
      rw [← hJ4card, hJ4b]
      rfl
    omega
  have hb4ne0 : cosetInvolution_b c.Hhat 4 ≠ 0 := by
    rw [hb4]
    exact h4ne
  have hJ4pos : 0 < Nat.card {x : G // x ∈ firstCaseJ c 4} := by
    rw [firstCase_J_n_card c 4]
    exact Nat.mul_pos (by norm_num) (Nat.pos_of_ne_zero hb4ne0)
  obtain ⟨y, hyJ⟩ := (Nat.card_pos_iff.mp hJ4pos).1
  have hyJ' : IsInvolution y ∧ y ∉ c.Hhat ∧
      firstCaseCosetInvolutions c y = 4 := by
    simpa [firstCaseJ] using hyJ
  have hy : IsInvolution y := hyJ'.1
  have hyH : y ∉ c.Hhat := hyJ'.2.1
  have hcoset : firstCaseCosetInvolutions c y = 4 := hyJ'.2.2
  have hI : 4 ≤ Nat.card {x : G // x ∈ invertedElements c.Hhat y} := by
    rw [← firstCase_klein_coset_involution_card_eq c hy hyH, hcoset]
  obtain ⟨s, x, hsI, hsD, hsy, hbranch⟩ :=
    firstCase_klein_restrictionSix_order_three hmin c hfirst hklein hy hyH hI
  rcases hbranch with hfy | hfsy
  · let D : Subgroup G := c.Hhat ⊓ conjugateSubgroup c.Hhat y
    have hone : (1 : G) ∈ invertedElements (oddCoreOf D) y :=
      ⟨(oddCoreOf D).one_mem, by simp⟩
    have hfib_ne : Nat.card {z : G // z ∈ invertedElements (oddCoreOf D) y} ≠ 1 := by
      intro hcard
      obtain ⟨z0, hz0⟩ := (Nat.card_eq_one_iff_exists.mp hcard)
      have hx_eq : (⟨x, hfy.2.2.2⟩ : {z : G // z ∈ invertedElements (oddCoreOf D) y}) = z0 :=
        hz0 _
      have h1_eq : (⟨1, hone⟩ : {z : G // z ∈ invertedElements (oddCoreOf D) y}) = z0 :=
        hz0 _
      have : x = 1 := congrArg Subtype.val (hx_eq.trans h1_eq.symm)
      exact hfy.2.1 this
    obtain ⟨X, hXne, hXle, hXodd, hXinv, hC, hN⟩ :=
      firstCase_klein_oddCore_parity c hy hyH hsI hsD hsy
        hfy.1 hfy.2.1 hfy.2.2.1 hfy.2.2.2
        (firstCase_klein_oddCore_inverted_card_three
          hmin c hfirst hklein hy hyH
          (firstCase_klein_restrictionSix_index_eq
            hmin c hfirst hklein hy hyH hI) hfib_ne)
    exact (firstCase_klein_restrictionSeven_card_three
      hmin c hfirst hklein hyJ (by norm_num : 4 ≤ 4)
      hXne hXle hXodd hXinv hC hN).1
  · let w : G := s * y
    have hsH : s ∈ c.Hhat :=
      (show c.Hhat ⊓ conjugateSubgroup c.Hhat y ≤ c.Hhat from inf_le_left) hsD
    have hwJ : w ∈ firstCaseJ c 4 :=
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
        (oddCoreOf (c.Hhat ⊓ conjugateSubgroup c.Hhat w : Subgroup G)) w :=
      ⟨(oddCoreOf (c.Hhat ⊓ conjugateSubgroup c.Hhat w : Subgroup G)).one_mem,
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
    obtain ⟨X, hXne, hXle, hXodd, hXinv, hC, hN⟩ :=
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
    exact (firstCase_klein_restrictionSeven_card_three
      hmin c hfirst hklein hwJ (by norm_num : 4 ≤ 4)
      hXne hXle hXodd hXinv hC hN).1

end CFSG.GorensteinWalter
