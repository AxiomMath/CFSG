module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixOrderThree
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinOddCoreParity
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinOddCoreFiberCard
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixIndex
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinCosetRepresentative
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseJNCoset
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseCountData
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

/-!
# Restriction-(7) witness for a `J₄`-element

Every element of `J₄` supplies, through restriction (6), an inverted
order-three subgroup whose centralizer and `Ĥ`-normalizer have even order.
These are exactly the parity witnesses consumed by restriction (7).
-/

public theorem firstCase_klein_restrictionSeven_witness_of_mem_J_four
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat))
    {y : G} (hyJ : y ∈ firstCaseJ c 4) :
    ∃ w : G, w ∈ firstCaseJ c 4 ∧
      cosetInvolution_proj c.Hhat w = cosetInvolution_proj c.Hhat y ∧
      ∃ X : Subgroup G,
        X ≠ ⊥ ∧ X ≤ c.Hhat ∧ Nat.Coprime 2 (Nat.card X) ∧
        (∀ x : G, x ∈ X → x ∈ invertedElements c.Hhat w) ∧
        Even (Nat.card (Subgroup.centralizer (X : Set G))) ∧
        Even (Nat.card ((Subgroup.normalizer (X : Set G) ⊓ c.Hhat : Subgroup G))) := by
  classical
  have hyJ' : IsInvolution y ∧ y ∉ c.Hhat ∧
      firstCaseCosetInvolutions c y = 4 := by
    change y ∈ firstCaseJ c 4
    exact hyJ
  have hy : IsInvolution y := hyJ'.1
  have hyH : y ∉ c.Hhat := hyJ'.2.1
  have hcoset : firstCaseCosetInvolutions c y = 4 := hyJ'.2.2
  have hI : 4 ≤ Nat.card {x : G // x ∈ invertedElements c.Hhat y} := by
    rw [← firstCase_klein_coset_involution_card_eq c hy hyH, hcoset]
  obtain ⟨s, x, hsI, hsD, hsy, hbranch⟩ :=
    firstCase_klein_restrictionSix_order_three hmin c hfirst hklein hy hyH hI
  rcases hbranch with hfy | hfsy
  · let D : Subgroup G := c.Hhat ⊓ conjugateSubgroup c.Hhat y
    have hone : (1 : G) ∈ invertedElements
        (oddCoreOf (c.Hhat ⊓ conjugateSubgroup c.Hhat y : Subgroup G)) y :=
      ⟨(oddCoreOf (c.Hhat ⊓ conjugateSubgroup c.Hhat y : Subgroup G)).one_mem,
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
    obtain ⟨X, hXne, hXle, hXodd, hXinv, hC, hN⟩ :=
      firstCase_klein_oddCore_parity c hy hyH hsI hsD hsy
        hfy.1 hfy.2.1 hfy.2.2.1 hfy.2.2.2
        (firstCase_klein_oddCore_inverted_card_three
          hmin c hfirst hklein hy hyH
          (firstCase_klein_restrictionSix_index_eq
            hmin c hfirst hklein hy hyH hI) hfib_ne)
    exact ⟨y, hyJ, rfl, X, hXne, hXle, hXodd, hXinv, hC, hN⟩
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
    have hproj : cosetInvolution_proj c.Hhat w =
        cosetInvolution_proj c.Hhat y := by
      dsimp [w, cosetInvolution_proj]
      apply (QuotientGroup.eq (s := c.Hhat)).mpr
      have hmem : ((s * y)⁻¹)⁻¹ * y⁻¹ ∈ c.Hhat := by
        rw [show ((s * y)⁻¹)⁻¹ * y⁻¹ = s from (by group)]
        exact hsH
      simpa using hmem
    exact ⟨w, hwJ, hproj, X, hXne, hXle, hXodd, hXinv, hC, hN⟩

end CFSG.GorensteinWalter
