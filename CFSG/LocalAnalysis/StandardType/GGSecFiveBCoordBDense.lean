module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBDenseDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBJoinDefs
public import Certificates.Certificate117
import CFSG.LocalAnalysis.StandardType.GGQTwoSpinEndpoint
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBOm
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSpSp
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSp

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType CFSG.LieType.Universal
open scoped MatrixGroups

theorem GGSecFiveBCoordBUniCell.ggG0_eq (hJ : BMaxJoinInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {n : ℕ}
    (e : (CoxeterMatrix.B n).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦))
    (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) (CoxeterMatrix.B n) e) (hn : 2 ≤ n)
    (hRM : ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦)
    {f : ℕ} {K : Subgroup G} {i0 : Fin n} (hc : GGSecFiveBCoordBUniCell p Bs L 𝒦 n f K i0) :
    ggG0 p B x L D J = L ⊔ K := by
  obtain ⟨-, -, -, hK, -, -, eta', h𝒦, hLeta, hKeta⟩ := hc
  refine ggG0_eq_sup_of_ggAutomizerJoin_eq hJ hR e hP hn hRM hK ?_
  apply Subgroup.map_injective (f := (MulAut.congr eta').toMonoidHom) (MulAut.congr eta').injective
  rw [h𝒦]
  simp only [ggAutomizerJoin, Finset.iSup_singleton, Subgroup.map_sup, hLeta, hKeta]
  rw [sup_comm]
  exact aPermutationFull_sup_bCoordinateBlock p hn i0

section Inputs

theorem ggSecFiveBCoordBOffSpSpOmOn_of_dense {S : ℕ → ℕ → LargeEvenLabel → Prop}
    (hD : GGSecFiveBCoordBDenseNbrOn S) (hU : GGSecFiveBCoordBUniInput) (hJ : BMaxJoinInput)
    (hS : GGSecFiveBCoordBSparseOn S) : GGSecFiveBCoordBOffSpSpOmOn S := by
  intro G _ _ p B Bs x L D J 𝒦 hR hT1 n e hP hn eta i0 h𝒦 hL hLab hB hRM hG0 hdense hsparse hom
  by_cases hd : ∃ K : Subgroup G, GGSecFiveBCoordBDenseNbr p Bs 𝒦 n eta K
  · obtain ⟨K, hK⟩ := hd
    obtain ⟨f, hc | hc | hc⟩ :=
      hD G p B Bs x L D J 𝒦 hR hT1 n e hP hn eta i0 h𝒦 hL hLab hB hRM hG0 K hK
    · exact absurd ⟨f, K, hc⟩ hdense
    · exact absurd ⟨f, K, hc⟩ hom
    · have hf : 2 ≤ f := hc.1
      have hLK := hc.ggG0_eq hJ hR e hP (by omega) hRM
      obtain ⟨ψ, hψ, hψr⟩ := hU G p B Bs x L D J 𝒦 hR hT1 n e hP hn eta i0 h𝒦 hL
        (largeEvenMarking_mono (fun _ _ _ _ _ _ h' => ⟨h'.1.1, h'.2⟩) hLab) hB hRM hG0 f K hc
      exact ggSecFiveData_of_psi_POmegaPlus ⟨Nat.prime_two, by omega, by omega⟩
        (by rw [bnRank]; omega) ψ hψ (hψr.trans hLK.symm)
  · exact hS G p B Bs x L D J 𝒦 hR hT1 n e hP hn eta i0 h𝒦 hL hLab hB hRM hG0 hdense hsparse hom hd

end Inputs

section Split

theorem ggSecFiveBCoordBOffSpSpLargeInput_of_dense (hC : GGSecFiveBCoordBOmChartInput)
    (hD : GGSecFiveBCoordBDenseNbrLargeInput) (hU : GGSecFiveBCoordBUniInput)
    (hJ : BMaxJoinInput) (hS : GGSecFiveBCoordBSparseLargeInput) :
    GGSecFiveBCoordBOffSpSpLargeInput :=
  ggSecFiveBCoordBOffSpSpLargeInput_of_om hC (ggSecFiveBCoordBOffSpSpOmOn_of_dense hD hU hJ hS) hJ

end Split

end CFSG.StandardType

end
