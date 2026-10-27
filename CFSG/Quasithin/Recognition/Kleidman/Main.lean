module

public import CFSG.Quasithin.Recognition.Kleidman.Letters
public import CFSG.Quasithin.Recognition.Kleidman.Assembly
public import CFSG.Quasithin.Recognition.ModelBridgesJ3
public import CFSG.Quasithin.EmptyFaithful.SzI47Stubs
public import CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition.J3Case
public import CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition.DichotomyCases
public import CFSG.Quasithin.Recognition.Kleidman.ThreeLocalCentralizerAnalysis.J2Model
public import CFSG.Sporadic.Bridge.J3Surj
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.Quasithin.Kleidman

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition
open CFSG.Quasithin.Kleidman.ThreeLocal

theorem i47J3_holds : I47J3 := by
  intro G _ _ hs _ z h hone
  have : IsSimpleGroup G := hs
  obtain ⟨e, hrel, hH, he3, he6, he0C, he0⟩ := IsTypeH2.exists_letters h hone
  obtain ⟨r, hr, hre⟩ := CFSG.Quasithin.IsTypeH2.exists_mem_dichotomyRelators h hone hrel he0C he0
  have hset : {i : Fin 7 | i.val < 6} = {i : Fin 7 | i.val ≠ 6} := by
    ext i
    simp only [Set.mem_ofPred_eq]
    have := i.2
    omega
  have he1 : ∃ i, e i ≠ 1 := ⟨3, by rw [he3]; exact h.ne_one⟩
  have hrel' : ∀ k, ∀ r' ∈ j3WordsRest ++ [wRelator 4 k], wRelator 4 k = r →
      FreeGroup.lift e (FreeGroup.mk r') = 1 := by
    intro k r' hr' hk
    rcases List.mem_append.mp hr' with hr' | hr'
    · exact hrel r' hr'
    · rw [List.mem_singleton.mp hr', hk]
      exact hre
  rcases dichotomy_cases e hrel hr hre with hcol | h40 | h41
  ·
    exfalso
    rw [hset, hH] at hcol
    exact he6 hcol
  ·
    exfalso
    have := CFSG.Sporadic.J2.isSimpleGroup_J2
    have : Finite CFSG.Blueprint.NativeSporadic.J2 := CFSG.Sporadic.J2.fam_j2_simplicity.1
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := J2Model.j2_five_klein
    simp only [J2Model.j2Tau_eq, J2Model.j2Tau2_eq, J2Model.j2F_eq] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    refine IsTypeH2.false_of_rels_klein_five h hone (j3WordsRest ++ [wRelator 4 0]) ?_
      (fun r' hr' => hrel' 0 r' hr' h40.symm) he1 J2Model.j2Tuple_rels J2Model.closure_j2Tuple
      (FreeGroup.mk J2Model.tauWord) (FreeGroup.mk J2Model.tau2Word) (FreeGroup.mk J2Model.fWord)
      h1 h4 h2 h5 h6 h3 h7 h8 h9 h10
    intro ρ hρ
    rw [CFSG.Sporadic.J2.card_J2]
    exact card_closure_le_rels40 ρ hρ
  ·
    obtain ⟨φ⟩ := nonempty_mulEquiv_J3Model_of_letters h e he3 hH he6
      (fun r' hr' => hrel' 1 r' hr' h41.symm)
    exact ⟨φ.trans (CFSG.Sporadic.Bridge.J3.nativeEquiv.symm.trans
      quasithinJ3MulEquivNative.symm)⟩

end CFSG.Quasithin.Kleidman
