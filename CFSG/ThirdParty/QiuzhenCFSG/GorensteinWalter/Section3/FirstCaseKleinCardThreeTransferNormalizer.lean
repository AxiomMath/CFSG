module


public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSevenTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinNormalizer
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

/-! The even-centralizer transfer sends an inverted subgroup of order three
onto `U` once `|U|=3`, and hence identifies its ambient normalizer. -/

public theorem firstCase_klein_card_three_transfer_normalizer
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat))
    {n : ℕ} {y : G} {X : Subgroup G}
    (hyJ : y ∈ firstCaseJ c n)
    (hXne : X ≠ ⊥) (hXle : X ≤ c.Hhat)
    (hXcard : Nat.card X = 3)
    (hXinv : ∀ x : G, x ∈ X → x ∈ invertedElements c.Hhat y)
    (hC_even : Even (Nat.card (Subgroup.centralizer (X : Set G))))
    (hUcard : Nat.card c.U = 3) :
    ∃ g : G, g ∉ c.Hhat ∧ conjugateSubgroup X g = c.U ∧
      Subgroup.normalizer (X : Set G) = conjugateSubgroup c.Hhat g⁻¹ := by
  have hXodd : Nat.Coprime 2 (Nat.card X) := by rw [hXcard]; norm_num
  obtain ⟨g, L, hLHall, _hLne, hXgL, hgnot, _hNXg, _hFUcentXg⟩ :=
    firstCase_klein_restrictionSeven_transfer hmin c hfirst hklein
      hyJ hXne hXle hXodd hXinv hC_even
  have hXgcard : Nat.card (conjugateSubgroup X g) = 3 := by
    calc
      Nat.card (conjugateSubgroup X g) = Nat.card X := by
        exact Nat.card_congr
          (Subgroup.equivMapOfInjective X (MulAut.conj g).toMonoidHom
            (MulAut.conj g).injective).toEquiv.symm
      _ = 3 := hXcard
  have hXgleU : conjugateSubgroup X g ≤ c.U :=
    hXgL.trans (hLHall.1.trans (fittingSubgroupOf_le c.U))
  have hXgU : conjugateSubgroup X g = c.U := by
    apply Subgroup.eq_of_le_of_card_ge hXgleU
    rw [hXgcard, hUcard]
  have hVne : twoCoreOf c.Hhat ≠ ⊥ := by
    intro hbot
    have hfour := (firstCase_klein_V_klein c hklein).card_four
    rw [hbot] at hfour
    simp at hfour
  have hUne : c.U ≠ ⊥ := (lemma_2_2 hmin c).2
  have hNormU : Subgroup.normalizer (c.U : Set G) = c.Hhat :=
    theorem26_normalizer_U_eq_Hhat hmin c hVne hUne
  have hmapN :
      conjugateSubgroup (Subgroup.normalizer (X : Set G)) g = c.Hhat := by
    change (Subgroup.normalizer (X : Set G)).map
      (MulAut.conj g).toMonoidHom = _
    rw [Subgroup.map_normalizer_eq_of_bijective X (MulAut.conj g).bijective]
    change Subgroup.normalizer (conjugateSubgroup X g : Set G) = c.Hhat
    rw [hXgU, hNormU]
  have hnormEq : Subgroup.normalizer (X : Set G) =
      conjugateSubgroup c.Hhat g⁻¹ := by
    apply le_antisymm
    · intro z hz
      have hzg : g * z * g⁻¹ ∈ c.Hhat := by
        rw [← hmapN]
        exact Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
      exact Subgroup.mem_map.mpr ⟨g * z * g⁻¹, hzg, by
        simpa [MulAut.conj_apply] using
          (show g⁻¹ * (g * z * g⁻¹) * g = z by group)⟩
    · intro z hz
      rcases Subgroup.mem_map.mp hz with ⟨h, hh, hhz⟩
      have hzg : g * z * g⁻¹ ∈ c.Hhat := by
        have heq : g * z * g⁻¹ = h := by
          have heq0 : g⁻¹ * h * g = z := by
            simpa [MulAut.conj_apply] using hhz
          calc
            g * z * g⁻¹ = g * (g⁻¹ * h * g) * g⁻¹ := by rw [heq0]
            _ = h := by group
        rw [heq]
        exact hh
      rcases Subgroup.mem_map.mp (show g * z * g⁻¹ ∈
          conjugateSubgroup (Subgroup.normalizer (X : Set G)) g from by
        rw [hmapN]
        exact hzg) with ⟨w, hw, hweq⟩
      have hwz : w = z := by
        simpa [MulAut.conj_apply] using
          (congrArg (fun q : G => g⁻¹ * q * g) hweq)
      simpa [hwz] using hw
  exact ⟨g, hgnot, hXgU, hnormEq⟩

end CFSG.GorensteinWalter
