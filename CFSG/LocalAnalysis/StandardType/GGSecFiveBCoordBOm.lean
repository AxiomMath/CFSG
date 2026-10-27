module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBOmDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBJoinDefs
public import Certificates.Certificate117
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermLin
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSp
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSpSp

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType CFSG.LieType.Universal
open scoped MatrixGroups

theorem GGSecFiveBCoordBOmCell.ggG0_eq (hJ : BMaxJoinInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {n : ℕ}
    (e : (CoxeterMatrix.B n).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦))
    (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) (CoxeterMatrix.B n) e) (hn : 2 ≤ n)
    (hRM : ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦)
    {f : ℕ} {K : Subgroup G} {i0 : Fin n} (hc : GGSecFiveBCoordBOmCell p Bs L 𝒦 n f K i0) :
    ggG0 p B x L D J = L ⊔ K := by
  obtain ⟨-, hK, -, -, eta', h𝒦, hLeta, hKeta⟩ := hc
  refine ggG0_eq_sup_of_ggAutomizerJoin_eq hJ hR e hP hn hRM hK ?_
  apply Subgroup.map_injective (f := (MulAut.congr eta').toMonoidHom) (MulAut.congr eta').injective
  rw [h𝒦]
  simp only [ggAutomizerJoin, Finset.iSup_singleton, Subgroup.map_sup, hLeta, hKeta]
  rw [sup_comm]
  exact aPermutationFull_sup_bCoordinateBlock p hn i0

section Split

theorem ggSecFiveBCoordBOffSpSpOn_of_om {S : ℕ → ℕ → LargeEvenLabel → Prop}
    (hC : GGSecFiveBCoordBOmChartInput) (hO : GGSecFiveBCoordBOffSpSpOmOn S)
    (hJ : BMaxJoinInput) : GGSecFiveBCoordBOffSpSpOn S := by
  intro G _ _ p B Bs x L D J 𝒦 hR hT1 n e hP hn eta i0 h𝒦 hL hLab hB hRM hG0 hdense hsparse
  by_cases hcell : ∃ (f : ℕ) (K : Subgroup G), GGSecFiveBCoordBOmCell p Bs L 𝒦 n f K i0
  · obtain ⟨f, K, hc⟩ := hcell
    have hLK := hc.ggG0_eq hJ hR e hP (by omega) hRM
    obtain ⟨r, rfl, σ, κ, hσ, hσK, hκ, hκL, hagree, hcross⟩ :=
      hC G p B Bs x L D J 𝒦 hR hT1 n e hP hn eta i0 h𝒦 hL
        (largeEvenMarking_mono (fun _ _ _ _ _ _ h' => ⟨h'.1.1, h'.2⟩) hLab) hB hRM hG0 f K hc
    exact ggSecFiveData_of_omCharts (by omega) hc.1 σ hσ κ hκ hagree hcross
      (by rw [hLK, hσK, hκL, sup_comm])
  · exact hO G p B Bs x L D J 𝒦 hR hT1 n e hP hn eta i0 h𝒦 hL hLab hB hRM hG0 hdense hsparse hcell

theorem ggSecFiveBCoordBOffSpSpLargeInput_of_om (hC : GGSecFiveBCoordBOmChartInput)
    (hO : GGSecFiveBCoordBOffSpSpOmLargeInput) (hJ : BMaxJoinInput) :
    GGSecFiveBCoordBOffSpSpLargeInput :=
  ggSecFiveBCoordBOffSpSpOn_of_om hC hO hJ

end Split

end CFSG.StandardType

end
