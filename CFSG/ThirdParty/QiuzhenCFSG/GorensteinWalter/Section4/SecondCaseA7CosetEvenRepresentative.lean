module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7InvolutionsInComponent
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.InvolutionCosetConjugationCard
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseEvenNormalizedInvolution
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.InvolutionNormalizerInfConjugate
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseFactorization
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-! # A centralizing representative for an even outside coset -/

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

/-- If `M ∩ M^y` has even order, conjugation inside `M` replaces `y` by an
outside involution in `H = C_G(t)` without changing the number of involutions
in the represented right coset. -/
public theorem secondCase_a7_exists_centralizing_coset_representative_of_even_intersection
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (hA7 : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃*
      alternatingGroup (Fin 7)))
    (hmodel : d.model = ComponentQuotientModel.alternating hA7)
    {y : G} (hy : IsInvolution y) (hyM : y ∉ w.M)
    (hDeven : Even (Nat.card
      (w.M ⊓ conjugateSubgroup w.M y : Subgroup G))) :
    ∃ z : G, IsInvolution z ∧ z ∉ w.M ∧ z ∈ c.H ∧
      Nat.card {x : G // IsInvolution x ∧
        x ∈ (w.M : Set G) * ({y} : Set G)} =
      Nat.card {x : G // IsInvolution x ∧
        x ∈ (w.M : Set G) * ({z} : Set G)} := by
  let D : Subgroup G := w.M ⊓ conjugateSubgroup w.M y
  have hy2 : y * y = 1 := by simpa [pow_two] using hy.2
  have hyN : y ∈ Subgroup.normalizer (D : Set G) := by
    simpa [D] using
      involution_mem_normalizer_inf_conjugateSubgroup w.M hy2
  obtain ⟨s, hsI, hsD, hsy⟩ :=
    exists_centralizing_involution_of_even_normalized D hy hyN (by
      simpa [D] using hDeven)
  have hsM : s ∈ w.M := hsD.1
  have hsE : s ∈ d.E :=
    secondCase_a7_involutions_in_component hmin c w d hA7 hmodel s hsM hsI
  obtain ⟨g, hgE, hgst⟩ := secondCase_involutions_fused w d s hsE hsI
  have hgM : g ∈ w.M := d.E_component.1 hgE
  let z : G := g * y * g⁻¹
  have hzI : IsInvolution z := by
    constructor
    · intro hz1
      apply hy.1
      have h := congrArg (fun q : G => g⁻¹ * q * g) hz1
      simpa [z, mul_assoc] using h
    · calc
        z ^ 2 = g * (y ^ 2) * g⁻¹ := by
          simp only [z, pow_two]
          group
        _ = 1 := by rw [hy.2]; simp
  have hzM : z ∉ w.M := by
    intro hz
    apply hyM
    have hginvM : g⁻¹ ∈ w.M := w.M.inv_mem hgM
    have hmem : g⁻¹ * z * g ∈ w.M :=
      w.M.mul_mem (w.M.mul_mem hginvM hz) hgM
    simpa [z, mul_assoc] using hmem
  have hzcomm : z * c.t = c.t * z := by
    calc
      z * c.t = (g * y * g⁻¹) * (g * s * g⁻¹) := by rw [hgst]
      _ = g * (y * s) * g⁻¹ := by group
      _ = g * (s * y) * g⁻¹ := by rw [hsy]
      _ = (g * s * g⁻¹) * (g * y * g⁻¹) := by group
      _ = c.t * z := by rw [hgst]
  have hzH : z ∈ c.H := by
    rw [c.H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
    exact hzcomm
  refine ⟨z, hzI, hzM, hzH, ?_⟩
  simpa [z] using involution_coset_fiber_card_conjugate w.M (y := y) hgM

end CFSG.GorensteinWalter
