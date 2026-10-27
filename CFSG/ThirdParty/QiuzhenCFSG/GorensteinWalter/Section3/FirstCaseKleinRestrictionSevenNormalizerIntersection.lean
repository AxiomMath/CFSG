module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSevenConjugateU
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinNormalizer
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

/-! After restriction (7)'s card-three transfer, the normalizer of the
original inverted subgroup is the transported copy of `Ĥ`. -/

public theorem firstCase_klein_restrictionSeven_normalizer_intersection
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat))
    {n : ℕ} {y : G} {X : Subgroup G}
    (hyJ : y ∈ firstCaseJ c n)
    (hn : 4 ≤ n)
    (hXne : X ≠ ⊥) (hXle : X ≤ c.Hhat)
    (hXodd : Nat.Coprime 2 (Nat.card X))
    (hXinv : ∀ x : G, x ∈ X → x ∈ invertedElements c.Hhat y)
    (hC_even : Even (Nat.card (Subgroup.centralizer (X : Set G))))
    (hN_even : Even (Nat.card
      ((Subgroup.normalizer (X : Set G) ⊓ c.Hhat : Subgroup G)))) :
    ∃ g : G, g ∉ c.Hhat ∧
      conjugateSubgroup X g = c.U ∧
      (c.Hhat ⊓ conjugateSubgroup c.Hhat g⁻¹ : Subgroup G) =
        (Subgroup.normalizer (X : Set G) ⊓ c.Hhat : Subgroup G) := by
  obtain ⟨g, hgnot, hXgU⟩ :=
    firstCase_klein_restrictionSeven_conjugate_X_eq_U
      hmin c hfirst hklein hyJ hn hXne hXle hXodd hXinv hC_even hN_even
  have hmapN :
      conjugateSubgroup (Subgroup.normalizer (X : Set G)) g =
        Subgroup.normalizer (conjugateSubgroup X g : Set G) := by
    change (Subgroup.normalizer (X : Set G)).map
        (MulAut.conj g).toMonoidHom = _
    exact Subgroup.map_normalizer_eq_of_bijective X
      (MulAut.conj g).bijective
  have hVne : twoCoreOf c.Hhat ≠ ⊥ := by
    intro hbot
    have hfour := (firstCase_klein_V_klein c hklein).card_four
    rw [hbot] at hfour
    simp at hfour
  have hUne : c.U ≠ ⊥ := (lemma_2_2 hmin c).2
  have hNormU : Subgroup.normalizer (c.U : Set G) = c.Hhat :=
    theorem26_normalizer_U_eq_Hhat hmin c hVne hUne
  have hnormMap :
      conjugateSubgroup (Subgroup.normalizer (X : Set G)) g = c.Hhat := by
    rw [hmapN, hXgU, hNormU]
  have hnormEq : Subgroup.normalizer (X : Set G) =
      conjugateSubgroup c.Hhat g⁻¹ := by
    apply le_antisymm
    · intro z hz
      have hzg : g * z * g⁻¹ ∈ c.Hhat := by
        rw [← hnormMap]
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
        rw [hnormMap]
        exact hzg) with ⟨w, hw, hweq⟩
      have hwz : w = z := by
        simpa [MulAut.conj_apply] using
          (congrArg (fun q : G => g⁻¹ * q * g) hweq)
      simpa [hwz] using hw
  refine ⟨g, hgnot, hXgU, ?_⟩
  ext z
  constructor
  · intro hz
    exact ⟨by rw [hnormEq]; exact hz.2, hz.1⟩
  · intro hz
    exact ⟨hz.2, by rw [← hnormEq]; exact hz.1⟩

end CFSG.GorensteinWalter
