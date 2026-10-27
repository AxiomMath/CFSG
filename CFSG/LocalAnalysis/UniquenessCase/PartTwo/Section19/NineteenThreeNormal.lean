module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.VZeroSmall17
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSevenA
public import CFSG.Quasithin.Vol2.Ch3Sec3Comp
public import CFSG.Quasithin.Background.E3Weak
public import CFSG.Quasithin.Background.B6Basic
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22e
public import CFSG.LocalAnalysis.StronglyEmbedded.PSubgroups
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.NineThreeSylData
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSixBorel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSixE
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSixteen
public import CFSG.Quasithin.Vol2.Ch1Faithful
public import CFSG.Quasithin.Vol2.Ch3Sec3StatementsB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_wClos_zero_of_forall_commutator_le (D : Data G) {V₀ J : Subgroup G}
    (hJA : ∀ A ∈ E3.gammaSet V₀ 0 D.T, ⁅J, A⁆ ≤ pCoreOf 2 D.M) :
    J ≤ normalizer (E3.wClos V₀ 0 D.T : Set G) := by
  have hOT : pCoreOf 2 D.M ≤ D.T := uc22p22e_pCoreOf_le_T D
  have hconjT : ∀ j ∈ J, ∀ A ∈ E3.gammaSet V₀ 0 D.T, conjSubgroup A j ≤ D.T := by
    intro j hj A hA x hx
    rw [mem_conjSubgroup_iff] at hx
    have hxa : x = ⁅j⁻¹, j * x * j⁻¹⁆ * (j * x * j⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [hxa]
    exact D.T.mul_mem (hOT (hJA A hA (Subgroup.commutator_mem_commutator (J.inv_mem hj) hx)))
      (hA.1 hx)
  have hle : ∀ j ∈ J, conjSubgroup (E3.wClos V₀ 0 D.T) j ≤ E3.wClos V₀ 0 D.T := by
    intro j hj
    rw [E3.conjSubgroup_le_iff_le_inv]
    refine E3.wClos_le_of_forall fun A hA => ?_
    rw [E3.le_conjSubgroup_iff_inv_le, inv_inv]
    exact E3.le_wClos ⟨hconjT j hj A hA, E3.gammaMember_conj j hA.2⟩
  intro j hj
  refine conjSubgroup_eq_iff_mem_normalizer.1 (le_antisymm (hle j hj) ?_)
  rw [E3.le_conjSubgroup_iff_inv_le]
  exact hle j⁻¹ (J.inv_mem hj)

theorem le_normalizer_wClos_zero_of_commutator_ne (D : Data G) {V₀ V : Subgroup G}
    (h : Hyp125 D V₀ V) (hne : V₀ ≠ ⊥) {J : Subgroup G} (hJ : J ∈ calC D.M)
    (hJV : ⁅J, V₀⁆ ≠ ⊥) : J ≤ normalizer (E3.wClos V₀ 0 D.T : Set G) := by
  have hV : InCalV D.M V₀ := S17.hyp125_inCalV h hne
  have hTI : CFSG.CGT.Timmesfeld75.IsTI V₀ := S17.hyp125_isTI h hne
  have hN : normalizer (V₀ : Set G) = D.M := normalizer_eq_of_inCalV D hV
  have hCn : D.M ≤ normalizer ((D.M ⊓ centralizer (V₀ : Set G) : Subgroup G) : Set G) := by
    have h1 : D.M ≤ normalizer (centralizer (V₀ : Set G) : Set G) :=
      CFSG.Quasithin.B6.le_normalizer_centralizer hN.ge
    intro m hm
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hm, h1 hm⟩
  have hcomm : ⁅J, D.M ⊓ centralizer (V₀ : Set G)⁆ ≤ pCoreOf 2 D.M := by
    rcases CFSG.Quasithin.H13.Ch3Sec3.le_or_commutator_le_pCoreOf hJ.1 hJ.2.1 hJ.2.2
        inf_le_left hCn with hle | hle
    · exact absurd (Subgroup.commutator_eq_bot_iff_le_centralizer.2 (hle.trans inf_le_right))
        hJV
    · exact hle
  have hWC : E3.wClos V₀ 0 D.T ≤ D.M ⊓ centralizer (V₀ : Set G) := by
    rw [TwelveSeven.wClos_zero_eq_inf_centralizer D hV hTI]
    exact (E3.wClos_le 0 _).trans (inf_le_inf_right _ D.sylowM.le)
  exact le_normalizer_wClos_zero_of_forall_commutator_le D fun A hA =>
    (Subgroup.commutator_mono le_rfl ((E3.le_wClos hA).trans hWC)).trans hcomm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
