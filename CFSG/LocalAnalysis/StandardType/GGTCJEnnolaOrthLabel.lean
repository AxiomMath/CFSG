module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrEnnola
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GField
public import CFSG.LocalAnalysis.StandardType.GGTCJEnnolaOrthComp
import CFSG.Assembly.Subnormal
import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnOrthMark
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinDict
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniLabel
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldOrthDict
import CFSG.Open.StatedAPI
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119

public section

namespace CFSG.StandardType.TCJ

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.Y10F
  CFSG.LocalAnalysis.GLTheoremA.Y10GField
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

private theorem canonLabel_eq_self_of_famOrth {lab : GLALabel} (hFam : FamOrth lab) :
    canonLabel lab = lab := by
  rcases hFam with ⟨ht, hr⟩ | ⟨ht, hr2, hr3⟩
  · simp [canonLabel, ht, hr]
  · simp [canonLabel, ht, hr2, hr3]

private theorem hasLabel_of_innDiagKind {S : Type} [Group S] {labK : GLALabel} {α : MulAut S}
    (h : InnDiagKind S labK α) : HasLabel S (fun l : GLALabel => l = labK) :=
  CFSG.StandardType.Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ hl => hl.1) h

theorem tcjOrth_ennola_n_eq_of_ggLabelRigidInput (hRig : GGLabelRigidInput) (S : Type)
    [Group S] [Finite S] (p : ℕ) (α : MulAut S) (J : Subgroup S) (labK labJ : GLALabel)
    (hrow : ggRowP_EOmP p labK ∨ ggRowP_EOmM p labK) (hp : p.Prime) (hp2 : p ≠ 2)
    (hcen : Subgroup.center S = ⊥) (hin : InnDiagKind S labK α) (hα : α ^ p = 1)
    (hlabJ : HasLabel ↥J (fun l : GLALabel => l = labJ))
    (hJ : CFSG.Assembly.IsComponentOf J (fixSubgroup α)) : (canonLabel labJ).n = labK.n := by
  have hFam : FamOrth labK := by
    rcases hrow with ⟨ht, h4, -, -⟩ | ⟨ht, h5, -, -⟩
    · exact Or.inl ⟨ht, by omega⟩
    · exact Or.inr ⟨ht, by omega, by omega⟩
  have hc := canonLabel_eq_self_of_famOrth hFam
  have hS := hasLabel_of_innDiagKind hin
  obtain ⟨hmodel, a, rfl⟩ := Y10GInnOrthMark.innDiagKind_orth_data hcen hFam hin
  rw [hc] at hmodel
  have hap : a ^ p = 1 := by
    have hz : a ^ p ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro z
      have h := DFunLike.congr_fun (show MulAut.conj (a ^ p) = 1 by rw [map_pow, hα]) z
      rw [MulAut.conj_apply, MulAut.one_apply] at h
      exact (mul_inv_eq_iff_eq_mul.mp h).symm
    rw [hcen] at hz
    exact Subgroup.mem_bot.mp hz
  let eS : S ⧸ Subgroup.center S ≃* S :=
    (QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot
  have hdict := Y10GFldOrth.orthLabelDict_of_ggLabelRigidInput hRig S labK labK.rank labK.n hS
  obtain ⟨t, ht, hG, hpq⟩ : ∃ t : StatedLieTag,
      (t = .POmegaPlus ∧ Even labK.rank ∨ t = .POmegaMinus ∧ Odd labK.rank) ∧
        StatedClassicalModel S t labK.rank 2 labK.n ∧ p ∣ 2 ^ labK.n + 1 := by
    rcases hrow with ⟨htag, -, hev, hpq⟩ | ⟨htag, -, hodd, hpq⟩
    · refine ⟨_, Or.inl ⟨rfl, hev⟩, hmodel.resolve_right fun hM => ?_, hpq⟩
      have h := congrArg CFSG.Assembly.LargeEvenLabel.tag
        (hc.symm.trans (hdict.2 (StatedAPI.statedClassicalModel_of_mulEquiv eS.symm hM)))
      simp [htag] at h
    · refine ⟨_, Or.inr ⟨rfl, hodd⟩, hmodel.resolve_left fun hM => ?_, hpq⟩
      have h := congrArg CFSG.Assembly.LargeEvenLabel.tag
        (hc.symm.trans (hdict.1 (StatedAPI.statedClassicalModel_of_mulEquiv eS.symm hM)))
      simp [htag] at h
  rcases tcjOrth_quotCenter_cases_ennola ht hG hp hp2 hpq a hap
      ((CFSG.Assembly.isComponentOf_iff_open).mp hJ) with
    ⟨b, E, _, _, hb, hE, hφ⟩ | ⟨b, E, _, _, τ, hτ, hb, hτk, hE, hφ⟩ | ⟨s, hM | hM⟩
  · rw [Y10GInnLin.linLabelDict_of_ggLabelRigidInput hRig _ labJ b labK.n E hb hE hlabJ hφ]
  · rw [Y10GInnUni.uniLabelDict_of_ggLabelRigidInput hRig _ labJ b labK.n E τ hτ hb hτk hE hlabJ
      hφ]
  · rw [(Y10GFldOrth.orthLabelDict_of_ggLabelRigidInput hRig _ labJ s _ hlabJ).1 hM]
  · rw [(Y10GFldOrth.orthLabelDict_of_ggLabelRigidInput hRig _ labJ s _ hlabJ).2 hM]

theorem tcjOrth_innDiagAllEnnolaOrth_of_ggLabelRigidInput (hRig : GGLabelRigidInput)
    (S : Type) [Group S] [Finite S] (p : ℕ) (α : MulAut S) (J : Subgroup S)
    (labK labJ : GLALabel) (hFam : FamOrth labK) (hp : p.Prime) (hp2 : p ≠ 2)
    (hrow : ggRowP_Ennola p labK) (hcen : Subgroup.center S = ⊥) (hin : InnDiagKind S labK α)
    (hα : α ^ p = 1) (hlabJ : HasLabel ↥J (fun l : GLALabel => l = labJ))
    (hJ : CFSG.Assembly.IsComponentOf J (fixSubgroup α)) :
    ∃ k : ℕ, Odd k ∧ (canonLabel labJ).n = k * (canonLabel labK).n := by
  have hOm : ggRowP_EOmP p labK ∨ ggRowP_EOmM p labK := by
    have hD : labK.tag = .D ∨ labK.tag = .twD ∧ labK.rank ≠ 3 := by
      rcases hFam with ⟨ht, -⟩ | ⟨ht, -, hr⟩
      exacts [Or.inl ht, Or.inr ⟨ht, hr⟩]
    rcases hrow with (⟨⟨h1, -⟩ | ⟨h1, h2⟩, -⟩ | h | h | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩) |
      ⟨⟨h1, -⟩, -⟩
    all_goals first
      | exact Or.inl h
      | exact Or.inr h
      | (exfalso; rcases hD with hD | ⟨hD, hr⟩ <;> simp_all)
  refine ⟨1, odd_one, ?_⟩
  rw [one_mul, canonLabel_eq_self_of_famOrth hFam]
  exact tcjOrth_ennola_n_eq_of_ggLabelRigidInput hRig S p α J labK labJ hOm hp hp2 hcen hin hα
    hlabJ hJ

end CFSG.StandardType.TCJ

end
