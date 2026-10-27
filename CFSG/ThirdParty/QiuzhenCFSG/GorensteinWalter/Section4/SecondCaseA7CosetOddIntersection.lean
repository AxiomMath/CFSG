module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7OddCoreEqF
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7AmbientModel
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PrimeThreeNormalizerInvertedCoset
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenOddSubgroupOrderBound
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.InvertedElementsLeInfConjugate
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CosetInvolutionCount
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-! # Outside involution cosets with odd intersection in the A7 case -/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

open scoped Pointwise

/-- If `M ∩ M^y` has odd order, then the coset `M y` contains at most
twenty-one involutions. -/
public theorem secondCase_a7_coset_involutions_card_le_21_of_odd_intersection
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (hA7 : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃*
      alternatingGroup (Fin 7)))
    (hmodel : d.model = ComponentQuotientModel.alternating hA7)
    (od : SecondCaseA7OmegaData c w d)
    {y : G} (hy : IsInvolution y) (hyM : y ∉ w.M)
    (hDodd : Odd (Nat.card
      (w.M ⊓ conjugateSubgroup w.M y : Subgroup G))) :
    Nat.card {x : G // IsInvolution x ∧
      x ∈ (w.M : Set G) * ({y} : Set G)} ≤ 21 := by
  classical
  let M : Subgroup G := w.M
  let D : Subgroup G := M ⊓ conjugateSubgroup M y
  let O : Subgroup M := pPrimeCore 2 M
  let : O.Normal := by
    dsimp [O]
    infer_instance
  let q : M →* M ⧸ O := QuotientGroup.mk' O
  let D0 : Subgroup M := D.subgroupOf M
  let Dbar : Subgroup (M ⧸ O) := D0.map q
  let eQ : (M ⧸ O) ≃* alternatingGroup (Fin 7) :=
    (secondCase_a7_ambient_quotient_model hmin c w d hA7 hmodel).some
  let X : Subgroup (alternatingGroup (Fin 7)) := Dbar.map eQ.toMonoidHom
  have hD0card : Nat.card D0 = Nat.card D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show D ≤ M from inf_le_left)).toEquiv
  have hDbarOdd : Odd (Nat.card Dbar) := by
    apply Odd.of_dvd_nat
    · simpa [D] using hDodd
    · have hdiv := Subgroup.card_map_dvd D0 q
      change Nat.card Dbar ∣ Nat.card D
      rw [← hD0card]
      exact hdiv
  have hXcard : Nat.card X = Nat.card Dbar := by
    exact Subgroup.card_map_of_injective eQ.injective
  have hXodd : Odd (Nat.card X) := by
    rw [hXcard]
    exact hDbarOdd
  have hXle : Nat.card X ≤ 21 :=
    aSeven_odd_subgroup_card_le_21 X hXodd
  let Inv := {x : G // x ∈ invertedElements M y}
  have inv_mem_D (x : Inv) : x.1 ∈ D := by
    simpa [D] using invertedElements_subset_inf_conjugateSubgroup M y x.2
  let f : Inv → X := fun x =>
    let xM : M := ⟨x.1, x.2.1⟩
    ⟨eQ (q xM), Subgroup.mem_map.mpr
      ⟨q xM, Subgroup.mem_map.mpr
        ⟨xM, Subgroup.mem_subgroupOf.mpr (inv_mem_D x), rfl⟩, rfl⟩⟩
  have hfInj : Function.Injective f := by
    intro x z hf
    apply Subtype.ext
    let xM : M := ⟨x.1, x.2.1⟩
    let zM : M := ⟨z.1, z.2.1⟩
    have heqQ : q xM = q zM := by
      apply eQ.injective
      exact congrArg Subtype.val hf
    have hqone : q (xM * zM⁻¹) = 1 := by
      change q xM * (q zM)⁻¹ = 1
      rw [heqQ]
      simp
    have hmemO : xM * zM⁻¹ ∈ O :=
      (QuotientGroup.eq_one_iff (xM * zM⁻¹)).mp hqone
    have hprodF : x.1 * z.1⁻¹ ∈ od.F := by
      rw [← secondCase_a7_oddCore_eq_F hmin c w d hA7 hmodel od]
      exact Subgroup.mem_map.mpr ⟨xM * zM⁻¹, hmemO, rfl⟩
    exact inverted_elements_eq_of_mul_inv_mem_card_three_normalizer
      M od.F od.F_card od.F_normalizer hy hyM x.2 z.2 hprodF
  have hInvLe : Nat.card Inv ≤ Nat.card X :=
    Nat.card_le_card_of_injective f hfInj
  let Punct := {i : G // i ∈ invertedIn M y ∧ i ≠ y}
  let forget : Punct → Inv := fun i =>
    ⟨i.1, by
      rw [← invertedIn_eq_invertedElements M y]
      exact i.2.1⟩
  have hforget : Function.Injective forget := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun z : Inv => (z : G)) hab
  calc
    Nat.card {x : G // IsInvolution x ∧
        x ∈ (w.M : Set G) * ({y} : Set G)} = Nat.card Punct := by
      simpa [M, Punct] using involution_coset_fiber_card M hy
    _ ≤ Nat.card Inv := Nat.card_le_card_of_injective forget hforget
    _ ≤ Nat.card X := hInvLe
    _ ≤ 21 := hXle

end CFSG.GorensteinWalter
