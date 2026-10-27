module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSpDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBJoinDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBBstar
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSp

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open scoped MatrixGroups

theorem GGSecFiveBCoordBSpCell.ggG0_eq (hJ : BMaxJoinInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {n : ℕ}
    (e : (CoxeterMatrix.B n).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦))
    (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) (CoxeterMatrix.B n) e) (hn : 2 ≤ n)
    (hRM : ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦)
    {f : ℕ} {K : Subgroup G} {i0 : Fin n} (hc : GGSecFiveBCoordBSpCell p Bs L 𝒦 n f K i0) :
    ggG0 p B x L D J = L ⊔ K := by
  obtain ⟨-, hK, -, -, eta', h𝒦, hLeta, hKeta⟩ := hc
  have hEq : ggAutomizerJoin L Bs {K} = ggAutomizerJoin L Bs 𝒦 := by
    apply Subgroup.map_injective (f := (MulAut.congr eta').toMonoidHom) (MulAut.congr eta').injective
    rw [h𝒦]
    simp only [ggAutomizerJoin, Finset.iSup_singleton, Subgroup.map_sup, hLeta, hKeta]
    rw [sup_comm]
    exact aPermutationFull_sup_bCoordinateBlock p hn i0
  have hR' : GGSecFiveRouteCfg p B Bs x L D J {K} := by
    refine ⟨hR.1, hR.2.1, hR.2.2.1, ⟨by simp, fun K' hK' => ?_⟩, ?_, fun 𝒦' h1 h2 => ?_⟩
    · rw [Finset.mem_singleton.1 hK']
      exact hR.2.2.2.1.2 K hK
    · rw [hEq]
      exact hR.2.2.2.2.1
    · rw [hEq]
      exact hR.2.2.2.2.2 𝒦' h1 h2
  have hM : GGIsWeylMatrixB (CoxeterMatrix.B n) :=
    ⟨n, Equiv.refl _, by omega, CoxeterMatrix.ext (Matrix.ext fun _ _ => rfl)⟩
  obtain ⟨e', hP'⟩ : ∃ e' : (CoxeterMatrix.B n).Group ≃* ↥(ggAutomizerJoin L Bs {K}),
      GGCoxeterPres p (ggAutomizerJoin L Bs {K}) (CoxeterMatrix.B n) e' := by
    rw [hEq]
    exact ⟨e, hP⟩
  have h := hJ G p B Bs x L D J {K} hR' (Fin n) (CoxeterMatrix.B n) e' hP' hM fun y K' hK' => by
    rw [hEq]
    exact hRM y K' hK'
  simpa only [Finset.iSup_singleton] using h

section Split


theorem ggSecFiveBCoordBDataInput_of_split (hBs : GGSecFiveBCoordBBstarInput)
    (hPr : GGSecFiveBCoordBProperInput) (hC : GGSecFiveBCoordBSpChartInput)
    (hO : GGSecFiveBCoordBOffSpInput) (hJ : BMaxJoinInput) : GGSecFiveBCoordBDataInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR hT1 n e hP hn eta i0 h𝒦 hL hLab hRM hG0
  by_cases hB : B = Bs
  · by_cases hcell : ∃ (f : ℕ) (K : Subgroup G), GGSecFiveBCoordBSpCell p Bs L 𝒦 n f K i0
    · obtain ⟨f, K, hc⟩ := hcell
      have hLK := hc.ggG0_eq hJ hR e hP (by omega) hRM
      obtain ⟨r, rfl, σ, κ, hσ, hσK, hκ, hκL, hagree, hcross⟩ :=
        hC G p B Bs x L D J 𝒦 hR hT1 n e hP hn eta i0 h𝒦 hL hLab hB hRM hG0 f K hc
      exact ggSecFiveData_of_spCharts (by omega) hc.1 σ hσ κ hκ hagree hcross
        (by rw [hLK, hσK, hκL, sup_comm])
    · exact hO G p B Bs x L D J 𝒦 hR hT1 n e hP hn eta i0 h𝒦 hL hLab hB hRM hG0 hcell
  · exact hPr G p B Bs x L D J 𝒦 hR hT1 n e hP hn eta i0 h𝒦 hL
      ((hBs G p B Bs x L D J 𝒦 hR n hn eta hLab).resolve_left hB) hB hRM hG0

end Split

section Bstar


theorem ggSecFiveBCoordBBstarInput_holds : GGSecFiveBCoordBBstarInput :=
  fun _ _ _ _ _ _ _ _ _ _ _ hR _ hn eta hM => ggSecFiveBCoordB_eq_bstar_or hR hn eta hM

end Bstar

end CFSG.StandardType

end
