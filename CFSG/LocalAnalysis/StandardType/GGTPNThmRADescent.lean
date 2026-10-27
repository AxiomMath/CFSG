module

public import CFSG.LocalAnalysis.StandardType.GGTPNDefs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeSplitR
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeRComp
public import CFSG.LocalAnalysis.StandardType.GGTPNThmUClauses
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FSeitzB2
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
public import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FFix
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FSeitzB1
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs16
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsElim
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.Assembly
public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4S.Inputs
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ker_proj_eq_center {X : Type} [Group X] {R : Type} [Group R]
    (θ : X ⧸ Subgroup.center X ≃* R) :
    (TablePThreeKG.proj θ).ker = Subgroup.center X := by
  rw [show TablePThreeKG.proj θ =
      (θ : X ⧸ Subgroup.center X →* R).comp
        (QuotientGroup.mk' (Subgroup.center X)) from rfl,
    MonoidHom.ker_comp_of_injective (QuotientGroup.mk' (Subgroup.center X))
      (θ : X ⧸ Subgroup.center X →* R) θ.injective,
    QuotientGroup.ker_mk']

theorem ggTPNComponent_map_proj_congr {X : Type} [Group X] [Finite X]
    (hX : commutator X = ⊤) {σ : MulAut X} {J : Subgroup X}
    (hJ : IsComponentOf J (ggAutFixedSubgroup σ))
    {R : Type} [Group R] (θ : X ⧸ Subgroup.center X ≃* R) :
    IsComponentOf (J.map (TablePThreeKG.proj θ)) (ggAutFixedSubgroup (ggInducedAut θ σ)) ∧
    Nonempty (↥J ⧸ Subgroup.center ↥J ≃*
      ↥(J.map (TablePThreeKG.proj θ)) ⧸ Subgroup.center ↥(J.map (TablePThreeKG.proj θ))) := by
  have hcomp := TablePThreeKG.leafRComp_holds X hX R θ σ
  refine ⟨hcomp.1 J hJ, ?_⟩
  have hker : ((TablePThreeKG.proj θ).subgroupMap J).ker ≤ Subgroup.center ↥J := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx1 : TablePThreeKG.proj θ (x : X) = 1 := by
      have h1 := congrArg Subtype.val hx
      rw [MonoidHom.subgroupMap_apply_coe] at h1
      simpa using h1
    have hxX : (x : X) ∈ Subgroup.center X := by
      rw [← ker_proj_eq_center θ]
      exact MonoidHom.mem_ker.mpr hx1
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    simpa using (Subgroup.mem_center_iff.mp hxX) (y : X)
  exact CFSG.LocalAnalysis.GLTheoremA.Y10F.quotEquiv_of_perfect_central
    ((TablePThreeKG.proj θ).subgroupMap J)
    ((TablePThreeKG.proj θ).subgroupMap_surjective J) ⟨hJ.2.2.1⟩ hker

theorem ggTPNOnlyComp_map_proj {p : ℕ} [Fact p.Prime] {X : Type} [Group X] [Finite X]
    (hX : commutator X = ⊤) {σ : MulAut X} {J : Subgroup X}
    (hJ : IsComponentOf J (ggAutFixedSubgroup σ)) (h8 : GGTPNOnlyComp p σ J)
    {R : Type} [Group R] (θ : X ⧸ Subgroup.center X ≃* R) :
    IsComponentOf (J.map (TablePThreeKG.proj θ)) (ggAutFixedSubgroup (ggInducedAut θ σ)) ∧
    (∀ Q : Subgroup R, IsComponentOf Q (ggAutFixedSubgroup (ggInducedAut θ σ)) →
      p ∣ Nat.card Q → Q = J.map (TablePThreeKG.proj θ)) ∧
    Nonempty (↥J ⧸ Subgroup.center ↥J ≃*
      ↥(J.map (TablePThreeKG.proj θ)) ⧸ Subgroup.center ↥(J.map (TablePThreeKG.proj θ))) := by
  have hcomp := TablePThreeKG.leafRComp_holds X hX R θ σ
  obtain ⟨hJbar, hequiv⟩ := ggTPNComponent_map_proj_congr hX hJ θ
  refine ⟨hJbar, ?_, hequiv⟩
  intro Q hQ hpQ
  obtain ⟨J', hJ', hJ'Q⟩ := hcomp.2 Q hQ
  have hpJ' : p ∣ Nat.card J' := by
    refine dvd_trans hpQ ?_
    rw [← hJ'Q]
    exact Subgroup.card_map_dvd J' (TablePThreeKG.proj θ)
  have hJJ' : J' = J := eq_of_isComponentOf_of_ggTPNOnlyComp h8 hJ' hpJ'
  rw [← hJ'Q, hJJ']

end CFSG.StandardType

end
