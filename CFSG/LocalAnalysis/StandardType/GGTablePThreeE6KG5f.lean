module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TorsionLabel
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6Labels
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeSplit
import CFSG.LocalAnalysis.StandardType.GGLabelRigid

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem rawDatum_elim_const' {lab : LargeEvenLabel} {Q : Prop}
    (h : LargeEvenRawDatum lab (fun _ _ _ _ => Q)) : Q := by
  obtain ⟨t, l, n⟩ := lab
  cases t
  all_goals dsimp only [LargeEvenRawDatum, LargeEvenRecipeLinear, LargeEvenRecipeUnitary,
    LargeEvenRecipeSymplectic, LargeEvenRecipeOmegaPlus, LargeEvenRecipeOmegaMinus,
    LargeEvenRecipeChevalley, LargeEvenRecipeTwisted, LargeEvenRecipeSuzuki,
    LargeEvenRecipeG2Derived, LargeEvenRecipeTwF4Inherited] at h
  all_goals try split_ifs at h
  all_goals first
    | (obtain ⟨K, i1, i2, hK, b, c, hbc, hq⟩ := h
       exact hq)
    | (obtain ⟨K, i1, i2, hK, hq⟩ := h
       exact hq)

private theorem e6CompLabel_rank_ne_one_of_tag_A {q : ℕ} {lab : LargeEvenLabel}
    (h : E6CompLabel q lab) (ht : lab.tag = .A) : lab.rank ≠ 1 := by
  rintro hr
  unfold E6CompLabel at h
  rcases h with ⟨-, hr5, -⟩ | ⟨htD, hr4, -⟩ | ⟨htri, -⟩ | ⟨hr2, -, -⟩
  · omega
  · rcases htD with hD | hD <;> rw [ht] at hD <;> simp at hD
  · rw [ht] at htri; simp at htri
  · omega

private theorem e6CompLabel_false_of_tag_twD_rank_two {q : ℕ} {lab : LargeEvenLabel}
    (h : E6CompLabel q lab) (ht : lab.tag = .twD) (hr : lab.rank = 2) : False := by
  unfold E6CompLabel at h
  rcases h with ⟨-, hr5, -⟩ | ⟨-, hr4, -⟩ | ⟨htri, -⟩ | ⟨hr2, -, h3⟩
  · omega
  · omega
  · rw [ht] at htri; simp at htri
  · rcases h3 with ⟨-, htA⟩ | ⟨-, htA⟩ <;> rw [ht] at htA <;> simp at htA

private theorem false_of_ggLabelIso_aOne_e6CompLabel {q : ℕ} {labA lab' : LargeEvenLabel}
    (hIso : GGLabelIso labA lab') (hAt : labA.tag = .A) (hAr : labA.rank = 1)
    (hL : E6CompLabel q lab') : False := by
  rcases hIso with h | h | h | h | h | h | h | h
  · rw [← h] at hL
    exact e6CompLabel_rank_ne_one_of_tag_A hL hAt hAr
  · rcases h.1 with hb | hb <;> rw [hAt] at hb <;> simp at hb
  · have ht : labA.tag = .D := congrArg LargeEvenLabel.tag h.1
    rw [hAt] at ht; simp at ht
  · have hr : labA.rank = 3 := congrArg LargeEvenLabel.rank h.1
    omega
  · have ht : labA.tag = .twD := congrArg LargeEvenLabel.tag h.1
    rw [hAt] at ht; simp at ht
  · have ht : labA.tag = .twA := congrArg LargeEvenLabel.tag h.1
    rw [hAt] at ht; simp at ht
  · have ht : labA.tag = .twD := congrArg LargeEvenLabel.tag h.1
    rw [hAt] at ht; simp at ht
  · have ht' : lab'.tag = .twD := congrArg LargeEvenLabel.tag h.1
    have hr' : lab'.rank = 2 := congrArg LargeEvenLabel.rank h.1
    exact e6CompLabel_false_of_tag_twD_rank_two hL ht' hr'

section Cert

theorem kg5f_E6eps
    {X : Type} [Group X] [Finite X] (hX : commutator X = ⊤)
    {A : Subgroup (MulAut X)} {δ : MulAut X} {J : Subgroup X}
    (hD : DatumOn (fun t => t = .E6 ∨ t = .twE6) X A δ J)
    (hq : LargeEvenMarking X fun lab _ _ _ _ _ => 2 ≤ lab.n) :
    ¬ LargeEvenMarking J (fun lab _ _ _ _ _ => lab.tag = .A ∧ lab.rank = 1) := by
  intro hJ
  have hδmem : δ ∈ A := hD.1.1.2.1
  have hδ3 : δ ^ 3 = 1 := hD.1.1.1.2 δ hδmem
  have hδne1 : δ ≠ 1 := hD.1.1.2.2.1
  have hcomp : IsComponentOf J (ggAutFixedSubgroup δ) := hD.1.1.2.2.2.1
  have huniq : ∀ Q : Subgroup X, IsComponentOf Q (ggAutFixedSubgroup δ) → Q = J := hD.2.1
  have hdat : GGTorsionDatum (fun lab => lab.tag = .E6 ∨ lab.tag = .twE6) 3 δ J := by
    refine ⟨Nat.prime_three, by norm_num, hδ3, hδne1, hcomp, ?_⟩
    refine largeEvenMarking_mono
      (P := fun lab _ _ I _ θ => (lab.tag = .E6 ∨ lab.tag = .twE6) ∧
        (LargeEvenSplit 3 lab ∧ GGInducedInn A θ I)) ?_ hD.2.2.2
    intro lab R _ I F θ h
    exact ⟨h.1, h.2.2 δ hδmem⟩
  obtain ⟨-, lab0, hlab0, hraw0⟩ := ggTorsion_E6eps_unique_label hdat hq huniq
  have hconcl : (lab0.tag = .E6 ∨ lab0.tag = .twE6) ∧
      ∃ lab' : LargeEvenLabel, LargeEvenInLambda2 lab' ∧
        GGHasLabel lab' (J ⧸ Subgroup.center J) ∧ E6CompLabel (2 ^ lab0.n) lab' :=
    rawDatum_elim_const'
      (largeEvenRawDatum_mono
        (Q' := fun _ _ _ _ => (lab0.tag = .E6 ∨ lab0.tag = .twE6) ∧
          ∃ lab' : LargeEvenLabel, LargeEvenInLambda2 lab' ∧
            GGHasLabel lab' (J ⧸ Subgroup.center J) ∧ E6CompLabel (2 ^ lab0.n) lab')
        (fun R _ I F h => h.2.2.choose_spec) hraw0)
  obtain ⟨-, lab', hlab', hHas', hE6Comp⟩ := hconcl
  obtain ⟨-, labA, hlabA, hrawA⟩ := hJ
  have hHasA : GGHasLabel labA (J ⧸ Subgroup.center J) := by
    refine largeEvenRawDatum_mono ?_ hrawA
    rintro R _ I F ⟨-, -, θ, -⟩
    exact ⟨θ⟩
  have hAprop : labA.tag = .A ∧ labA.rank = 1 :=
    rawDatum_elim_const'
      (largeEvenRawDatum_mono (fun R _ I F h => h.2.2.elim fun _ hh => hh) hrawA)
  have hrigid : GGLabelRigidInput := ggLabelRigidInput_holds
  have hIso : GGLabelIso labA lab' :=
    hrigid labA lab' (J ⧸ Subgroup.center J) hlabA hlab' hHasA hHas'
  exact false_of_ggLabelIso_aOne_e6CompLabel hIso hAprop.1 hAprop.2 hE6Comp

end Cert

end CFSG.StandardType.TablePThreeKG

end
