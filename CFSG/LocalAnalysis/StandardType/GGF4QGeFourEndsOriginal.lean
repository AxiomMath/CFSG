module

public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourEndsCover
public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourEndsA3
public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourEndsA3Lin
public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourEndsA3Uni
import CFSG.LocalAnalysis.StandardType.GGTypeANbrLabels
import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpStdAssembly

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly

theorem ggF4Ends_labelIso_n_eq_of_rank_three {lab lab' : LargeEvenLabel}
    (h : GGLabelIso lab lab') (hr : lab'.rank = 3) : lab.n = lab'.n := by
  rcases h with rfl | ⟨-, -, -, h4⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨h, -⟩
  · rfl
  · exact h4
  · rw [h]
  · rw [h]
  · rw [h]
  · rw [h]
  · rw [h] at hr
    simp at hr
  · rw [h] at hr
    simp at hr

section Original


theorem ggF4Ends_original_label_A3 (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hT : GGNoTransvection p Bs) (hcard : Nat.card Bs = p ^ 4)
    (hq : ¬ GGInnerDiagOnLabel GGLabQTwo p Bs L)
    (hA3 : GGWeylOfType p (CoxeterMatrix.A 3) (ggAutomizer L Bs)) :
    ∃ f, 2 ≤ f ∧
      ((p ∣ 2 ^ f - 1 ∧ GGHasLabel ⟨.A, 3, f⟩ (L ⧸ Subgroup.center L)) ∨
        (p ∣ 2 ^ f + 1 ∧ GGHasLabel ⟨.twA, 3, f⟩ (L ⧸ Subgroup.center L))) := by
  obtain ⟨hperf, labs, hlabs, hraw⟩ := ggF4Ends_original_torCov hcfg hT hcard hq
  obtain ⟨R, _, I, F, -, -, θ, ⟨⟨-, hn⟩, -⟩, -⟩ := largeEvenRawDatum_exists hraw
  have hHs : GGHasLabel labs (L ⧸ Subgroup.center L) :=
    largeEvenRawDatum_mono (fun R _ I F hQ => by
      obtain ⟨-, -, θ, -⟩ := hQ
      exact ⟨θ⟩) hraw
  have hM : GGInnerDiagOnLabel GGTBTorCov p Bs L :=
    ⟨hperf, labs, hlabs, largeEvenRawDatum_mono (fun R _ I F hQ => by
      obtain ⟨hs, hna, θ, hP⟩ := hQ
      exact ⟨hs, hna, θ, hP.1.2, hP.2⟩) hraw⟩
  obtain ⟨f, hf1, hlab⟩ := ggF4H1_toral_label hcfg hM hA3
  rcases hlab with ⟨hp, hHr⟩ | ⟨hp, hHr⟩
  · have hΛ : LargeEvenInLambda2 (⟨.A, 3, f⟩ : LargeEvenLabel) :=
      ⟨hf1, by norm_num, fun h => absurd h (by norm_num)⟩
    have hnf : labs.n = f := ggF4Ends_labelIso_n_eq_of_rank_three
      (hRig labs _ (L ⧸ Subgroup.center L) hlabs hΛ hHs hHr) rfl
    exact ⟨f, hnf ▸ hn, Or.inl ⟨hp, hHr⟩⟩
  · have hΛ : LargeEvenInLambda2 (⟨.twA, 3, f⟩ : LargeEvenLabel) :=
      ⟨hf1, by norm_num, fun h => absurd h (by norm_num)⟩
    have hnf : labs.n = f := ggF4Ends_labelIso_n_eq_of_rank_three
      (hRig labs _ (L ⧸ Subgroup.center L) hlabs hΛ hHs hHr) rfl
    exact ⟨f, hnf ▸ hn, Or.inr ⟨hp, hHr⟩⟩

theorem ggF4QGeFourEnds_originalRow
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) (hTPn : GGNbrTablePNbrInputNarrow)
    (hA8 : GGForkA8NotReflInput) (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hq : ¬ GGInnerDiagOnLabel GGLabQTwo p Bs L) {y : G} {K : Subgroup G}
    (hNb : GGNbr p B x D J y K) (hRC : GGSecFiveRouteCfg p B Bs x L D J {K})
    (hT1 : ¬ GGSecFiveTier1Region p B Bs x L D J)
    (hWK : GGWeylOfType p CoxeterMatrix.F₄ (ggAutomizer L Bs ⊔ ggAutomizer K Bs)) :
    (∃ f, 2 ≤ f ∧ p ∣ 2 ^ f - 1 ∧ GGCentralImage .PSp 3 f L) ∨
      (∃ f, 2 ≤ f ∧ p ∣ 2 ^ f - 1 ∧ GGCentralImage .POmegaMinus 4 f L) ∨
        (∃ f, 2 ≤ f ∧ p ∣ 2 ^ f + 1 ∧ GGCentralImage .POmegaMinus 4 f L) := by
  obtain ⟨hAB, hcard, -, -⟩ :=
    ggF4QGeFourEnds_bstar_types hX hTCJ hRig hTBF hWI hNb hRC hT1 hWK
  have hR := hRC.1
  have hNT : GGNoTransvection p Bs := hR.2.2.2.1
  rcases hAB with hA3 | hB3
  · exfalso
    apply ggF4Ends_no_order_three_of_A3 hX hTCJ hRig hTBF hWI hTPn hA8 hraw hiso hNb hRC hWK hA3
    obtain ⟨f, hf, ⟨hp, hlab⟩ | ⟨hp, hlab⟩⟩ :=
      ggF4Ends_original_label_A3 hRig hR.1 hNT hcard hq hA3
    · have hΛ : LargeEvenInLambda2 (⟨.A, 3, f⟩ : LargeEvenLabel) :=
        ⟨le_trans (by norm_num : 1 ≤ 2) hf, by norm_num, fun h => absurd h (by norm_num)⟩
      have hH : GGResHyp p B Bs x L D J y K :=
        ⟨hR.1, hR.2.1, hR.2.2.1, hR.2.2.2.1, hNb, hRC.2.1 y K hNb, Or.inr hRC.2.1⟩
      exact ggF4Ends_exists_order_three_linear ggInnerDiagMpInput_holds hLB hH hR.2.2.1.1
        (statedClassicalModel_of_hasLabel_typeA hΛ hlab) hp
    · exact ggF4Ends_exists_order_three_unitary hRig hLB hRC hf hp hlab hNb
  · exact ggF4Ends_originalRow_of_B3 hRig hR.1 hNT hcard hq hB3

end Original

end CFSG.StandardType

end
