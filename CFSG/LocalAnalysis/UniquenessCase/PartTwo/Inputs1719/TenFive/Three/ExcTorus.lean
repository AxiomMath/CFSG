module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.ExcRootData
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.ExcRoot
public import CFSG.ClassicalInvolution.Balance.LayerGenerationShortAdjoint

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)
open CFSG.ClassicalInvolution.Balance (rootDiagAut_xPar rootChar_single_eq)


theorem exists_rootDiag_inv_extraGood {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3) (b : Fin τ.rank → Kˣ)
    (hb : ∀ i, b i = 1 ∨ b i = -1) (hb1 : b ≠ 1) :
    ∃ x : adjointGroup τ K, orderOf x = 3 ∧ rootDiagAut τ K b x = x⁻¹ ∧ IsExtraGood x := by
  have : CharP K 3 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_three le_rfl (by rw [hK, pow_one])
  obtain ⟨i, hbi⟩ := Function.ne_iff.mp hb1
  have hbi' : b i = -1 := by
    rcases hb i with h | h
    · exact absurd h hbi
    · exact h
  refine ⟨xPar (rootOperatorFamily τ) (Pi.single i 1) 1, ?_, ?_, ?_⟩
  · exact orderOf_xPar Nat.prime_three (isRoot_single τ i) one_ne_zero
  · have hc : ((b i : Kˣ) : K) * 1 = -1 := by
      rw [hbi']
      simp
    rw [rootDiagAut_xPar b (isRoot_single τ i) 1, rootChar_single_eq, hc]
    exact (xPar_neg (F := rootOperatorFamily τ) (Pi.single i 1) 1).symm
  · exact isExtraGood_xPar_single hτ hK i 1

theorem exists_inv_extraGood_of_involution {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3) (z : adjointGroup τ K)
    (hz : z * z = 1) (hz1 : z ≠ 1) :
    ∃ x : adjointGroup τ K, orderOf x = 3 ∧ z * x * z⁻¹ = x⁻¹ ∧ IsExtraGood x := by
  classical
  have hKodd : Odd (Nat.card K) := by
    rw [hK]
    decide
  obtain ⟨g, b, hb, hgz⟩ :=
    CFSG.ClassicalInvolution.ModelFacts.exists_conj_eq_rootDiagUnit_of_involution
      (Or.inr hτ) hKodd z hz
  set w : adjointGroup τ K := g * z * g⁻¹ with hw_def
  have hw : (w : ModGL τ K) = rootDiagUnit τ b := hgz
  have hz_eq : z = g⁻¹ * w * g := by
    rw [hw_def]
    group
  have hb1 : b ≠ 1 := by
    intro hb1'
    apply hz1
    have hw1 : w = 1 := by
      apply Subtype.ext
      rw [hw, hb1', rootDiagUnit_one]
      simp
    rw [hz_eq, hw1]
    group
  have hτ4 : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by tauto
  obtain ⟨x, hxo, hxi, hxg⟩ := exists_rootDiag_inv_extraGood hτ4 hK b hb hb1
  have hconj_x : w * x * w⁻¹ = x⁻¹ := by
    rw [← hxi]
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_rootDiagAut]
    rw [hw]
  refine ⟨g⁻¹ * x * g, ?_, ?_, ?_⟩
  · have hconj : g⁻¹ * x * g = (MulAut.conj g⁻¹) x := by
      simp
    rw [hconj, MulEquiv.orderOf_eq, hxo]
  · calc z * (g⁻¹ * x * g) * z⁻¹
        = g⁻¹ * (w * x * w⁻¹) * g := by
          rw [hz_eq]
          group
      _ = g⁻¹ * x⁻¹ * g := by rw [hconj_x]
      _ = (g⁻¹ * x * g)⁻¹ := by group
  · have hmap := IsExtraGood.map (f := (MulAut.conj g⁻¹).toMonoidHom)
      (MulAut.conj g⁻¹).injective hxg
    have hy : (MulAut.conj g⁻¹).toMonoidHom x = g⁻¹ * x * g := by
      simp
    rwa [hy] at hmap

theorem exists_inv_extraGood_of_conj_involution {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3) (g : adjointGroup τ K)
    (hσ : orderOf (MulAut.conj g) = 2) :
    ∃ x : adjointGroup τ K, orderOf x = 3 ∧ MulAut.conj g x = x⁻¹ ∧ IsExtraGood x := by
  have hsq : MulAut.conj (g * g) = 1 := by
    rw [map_mul, ← pow_two, ← hσ]
    exact pow_orderOf_eq_one _
  have hg2 : g * g = 1 :=
    mulAut_conj_injective_of_center_eq_bot (center_adjointGroup_eq_bot (τ := τ) (K := K))
      (hsq.trans (map_one (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K))).symm)
  have hg1 : g ≠ 1 := by
    intro hg
    rw [hg, map_one, orderOf_one] at hσ
    omega
  obtain ⟨x, hx, hinv, hgood⟩ := exists_inv_extraGood_of_involution hτ hK g hg2 hg1
  exact ⟨x, hx, by simpa [MulAut.conj_apply] using hinv, hgood⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three
