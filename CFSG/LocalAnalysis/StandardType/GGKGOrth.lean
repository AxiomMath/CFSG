module

public import CFSG.LocalAnalysis.StandardType.GGKGTag
public import CFSG.LocalAnalysis.StandardType.GGKGOrthExport
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FDynClassical

public section

namespace CFSG.StandardType.KG

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.Y10GField CFSG.LocalAnalysis.GLTheoremA.Y10F
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

theorem kg_false_of_porth
    {X : Type} [Group X] {k f s m : ℕ} (hk : 3 ≤ k) (hC : GGHasLabel ⟨.C, k, f⟩ X)
    (hM : StatedClassicalModel X .POmegaPlus s 2 m ∨ StatedClassicalModel X .POmegaMinus s 2 m) :
    False := by
  rcases hM with hM | hM
  · have hs : 4 ≤ s := hM.1.2.2
    have hm : 1 ≤ m := hM.1.2.1
    have h' : GGHasLabel (⟨.D, s, m⟩ : LargeEvenLabel) X := by
      simp only [GGHasLabel, LargeEvenRawDatum]
      split_ifs with h3
      · omega
      · exact recipeOmegaPlus_of_statedClassicalModel hM
    have hl' : LargeEvenInLambda2 (⟨.D, s, m⟩ : LargeEvenLabel) := by
      refine ⟨hm, ?_⟩
      show 3 ≤ s
      omega
    rcases (kg_rigid_C hk hC hl' h').1 with htag | htag <;> simp at htag
  · have hs : 4 ≤ s := hM.1.2.2
    have hm : 1 ≤ m := hM.1.2.1
    have h' : GGHasLabel (⟨.twD, s, m⟩ : LargeEvenLabel) X := by
      simp only [GGHasLabel, LargeEvenRawDatum]
      split_ifs with h2 h3
      · omega
      · omega
      · exact recipeOmegaMinus_of_statedClassicalModel hM
    have hl' : LargeEvenInLambda2 (⟨.twD, s, m⟩ : LargeEvenLabel) := by
      refine ⟨hm, ?_⟩
      show 2 ≤ s
      omega
    rcases (kg_rigid_C hk hC hl' h').1 with htag | htag <;> simp at htag

open CFSG.LocalAnalysis.GLTheoremA.Y10GInnOrthModel in
theorem kgOrth_holds :
    KGSimpleOn FamOrth := by
  intro p hp hp2 S _ _ lab α K hF hlab hcen hin hαp hα1 hK k f hk hlabK
  exfalso
  have hfix : ggFixSub α = fixSubgroup α := by ext x; rfl
  rw [hfix] at hK
  have hKo : CFSG.Open.IsComponentOf K (fixSubgroup α) :=
    (CFSG.Assembly.isComponentOf_iff_open).mp hK
  classical
  obtain ⟨hmodel, a, rfl⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnOrthMark.innDiagKind_orth_data hcen hF hin
  have hap : a ^ p = 1 :=
    CFSG.LocalAnalysis.GLTheoremA.CanonTriL.pow_eq_one_of_conj_pow_eq_one hcen hαp
  obtain ⟨t, ht, hG⟩ : ∃ t : StatedLieTag, (t = .POmegaPlus ∨ t = .POmegaMinus) ∧
      StatedClassicalModel S t lab.rank 2 (canonLabel lab).n := by
    rcases hmodel with hG | hG
    · exact ⟨_, Or.inl rfl, hG⟩
    · exact ⟨_, Or.inr rfl, hG⟩
  obtain ⟨X, inst, -, hXLie, hfac, g, hg, hker⟩ :=
    kgOrth_lieFactor hp hp2 ht hG a hap K hKo
  letI := inst
  obtain ⟨eJ⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.center_quot_equiv_of_surjective
      hXLie.perfect g hg hker
  unfold KGOrthFactor at hfac
  rcases hfac with hSL | hSU | hOm
  · obtain ⟨b, kk, E, _, _, hb, hE, -, hφ⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.linCase_of_factor eJ hSL
    exact kg_false_of_quot_sl hKo.2.2 hb hE hφ hk hlabK
  · obtain ⟨b, kk, E, _, _, τ, hτ, hb, hτk, hcardE, -, hφ⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.uniCase_of_factor eJ hSU
    exact kg_false_of_quot_su hKo.2.2 τ hτ hb hτk hcardE hφ hk hlabK
  · obtain ⟨K', _, _, V, _, _, _, Q, hK'card, _, hQ, hd, hT, hφ⟩ := hOm
    obtain ⟨eX⟩ := hφ
    obtain ⟨sc, hsc⟩ :=
      exists_statedClassicalModel_quotCenter_orthDerived hK'card hQ hd hT eX
    rcases hsc with hplus | hminus
    · exact kg_false_of_porth hk hlabK
        (Or.inl (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv eJ.symm hplus))
    · exact kg_false_of_porth hk hlabK
        (Or.inr (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv eJ.symm hminus))

end CFSG.StandardType.KG
