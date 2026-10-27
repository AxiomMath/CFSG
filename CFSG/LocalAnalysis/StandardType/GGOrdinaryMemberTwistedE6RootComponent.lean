module
public import CFSG.LocalAnalysis.StandardType.GGOrdinaryMemberTwistedE6Lang
public import CFSG.LocalAnalysis.StandardType.GGReverseMarking
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGSixRCKSmallChainS12
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeRetE7Shape
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePairTwE6
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimple
public noncomputable section
set_option autoImplicit false
namespace CFSG.StandardType
open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.RootAut
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LocalAnalysis.GLTheoremA.S265C.DynE
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Adjoint
  CFSG.StandardType.GGFinModel CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.Phan
  CFSG.ClassicalInvolution.Phan.PhanE CFSG.RankThree.PartOne.KE6
open CFSG.Open (StatedLieTag)

private theorem statedLieTag_eq_twistedE6_of_hasLabel {X : Type} [Group X]
    (hqs : CFSG.IsQuasisimple X) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (htag : lab.tag = .twE6)
    (hhas : GGHasLabel lab (X ⧸ Subgroup.center X)) {t : CFSG.Open.StatedLieTag} {n f : ℕ}
    (hmodel : LieModel (X ⧸ Subgroup.center X) t n 2 f) : t = .twistedE6 := by
  obtain ⟨lab', hlab', hhas', R, _, I, F, theta, hparams⟩ :=
    largeEvenMarking_exists_hasLabel
      (largeEvenMarking_of_lieModel_centerQuot hqs.1.commutator_eq_top hmodel)
  have hiso := ggLabelRigidInput_holds lab lab' (X ⧸ Subgroup.center X) hlab hlab' hhas hhas'
  have heq : lab = lab' := by
    rcases lab with ⟨tag, rank, g⟩
    cases htag
    simpa [GGLabelIso] using hiso
  rw [← heq] at hparams
  exact hparams.1.symm.trans (by simp [markTag, htag])

theorem outerE6_rootComponent_of_E7_hasLabel {F : Type} [Field F] [IsAlgClosed F] [CharP F 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (S : LangSetup Tag.E7 F 5)
    {a : Fin Tag.E7.rank → Fˣ} (hT : rootDiagUnit .E7 a ∈ S.D.torus)
    (hap : ∀ j, a j ^ p = 1) (h1 : rootDiagUnit .E7 a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hqs : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (htag : lab.tag = .twE6)
    (hhas : GGHasLabel lab (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))) :
    compRank (componentRoots (rootCharHom a) i) = 6 ∧
      (componentRoots (rootCharHom a) i).ncard = 72 ∧
      ¬ twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin Tag.E7.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)]) := by
  have hpF : (p : F) ≠ 0 := by
    intro h
    have hdiv := (CharP.cast_eq_zero_iff F 2 p).mp h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp hdiv).symm
  have hTp :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.rootDiagUnit_pow_eq_one_of_forall hap
  have hsep : ∀ P : CFSG.Open.StatedLieTag → Prop, ¬ P .twistedE6 →
      TagLieType P (ringChar F) ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) → False := by
    rintro P hP ⟨t, n, f, ht, hmodel⟩
    rw [ringChar.eq F 2] at hmodel
    have htag' := statedLieTag_eq_twistedE6_of_hasLabel hqs hlab htag hhas hmodel
    exact hP (htag' ▸ ht)
  have hA : ¬ (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)) := by
    intro hA
    exact hsep (fun t => t = .PSL ∨ t = .PSU) (by simp)
      (tagLie_rationalComponent_typeA S hp hT hap h1 i hA hqs)
  have hout : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E7.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]) := by
    intro hinner
    exact hsep IsInnerDETag (by simp [IsInnerDETag])
      (tagLie_inner_nonA_E7 S hp hpF hT hTp i hA hinner)
  obtain ⟨v, mu, x, c, -, hc, -, hlen, -, hrank, hncard⟩ :=
    exists_cand_of_class kacE7 facts_E7 e7_tree e7_adj e7_check e7_lt e7_card S hp hpF hTp i
  have hshape := e7_shape c hc hlen
  rw [← hncard, ← hrank] at hshape
  rcases hshape with hA' | hD' | hE'
  · exact (hA hA').elim
  · exact (hsep (fun t => t = .POmegaMinus ∨ t = .trialityD4) (by simp)
      (RCKSmall.rck_tagLie_rationalComponent_outerD S hp hT hap h1 i hD' hout)).elim
  · have hle : compRank (componentRoots (rootCharHom a) i) ≤ 7 := by
      rw [hrank]
      exact hlen
    have h67 : compRank (componentRoots (rootCharHom a) i) = 6 ∨
        compRank (componentRoots (rootCharHom a) i) = 7 := by omega
    rcases h67 with h6 | h7
    · exact ⟨h6, by simpa [eRootCount, h6] using hE'.2, hout⟩
    · have h126 : (componentRoots (rootCharHom a) i).ncard = 126 := by
        simpa [eRootCount, h7] using hE'.2
      have hkind := RCKRP.rckRetE7_twistKind S.ρ (rootCharHom a) i h7 h126
      exact (hout (twistInner_of_twistKind_eq_innerT S rootAutIsWeyl_holds hT i hkind)).elim

variable {G : Type} [Group G] [Finite G]

omit
    [Finite G] in
theorem exists_label_of_native_E7_component_image
    (P : ℕ → LargeEvenLabel → Prop) {p : ℕ} {Bs L : Subgroup G}
    (hmark : GGInnerDiagOnLabel P p Bs L)
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (lambda : e7Data_valid.minGroup K →* G)
    (hker : lambda.ker ≤ Subgroup.center (e7Data_valid.minGroup K))
    (M : Subgroup (e7Data_valid.minGroup K)) (hML : M.map lambda = L)
    (S : LangSetup Tag.E7 (AlgebraicClosure K) 5)
    (a : Fin Tag.E7.rank → (AlgebraicClosure K)ˣ)
    (iota : adjointGroup .E7 K →* ModGL .E7 (AlgebraicClosure K))
    (hinj : Function.Injective iota) (i : KernelComponent (rootCharHom a))
    (hMR : M.map (iota.comp (CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint K).toMonoidHom) =
      rationalComponent S.ρ S.Γ (rootCharHom a) i) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ P p lab ∧
      GGHasLabel lab (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  have hZ : Subgroup.center (e7Data_valid.minGroup K) = ⊥ :=
    CFSG.SeitzReduction.E8Pilot.center_minGroup_e7_eq_bot
  have hker0 : lambda.ker = ⊥ := le_antisymm (by simpa only [hZ] using hker) bot_le
  have hlinj : Function.Injective lambda := (MonoidHom.ker_eq_bot_iff lambda).mp hker0
  let theta := CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint K
  let alpha : e7Data_valid.minGroup K →* ModGL .E7 (AlgebraicClosure K) :=
    iota.comp theta.toMonoidHom
  have hainj : Function.Injective alpha := hinj.comp theta.injective
  let eML : M ≃* L := (Subgroup.equivMapOfInjective M lambda hlinj).trans
    (MulEquiv.subgroupCongr hML)
  let eMR : M ≃* rationalComponent S.ρ S.Γ (rootCharHom a) i :=
    (Subgroup.equivMapOfInjective M alpha hainj).trans (MulEquiv.subgroupCongr hMR)
  let eLR : L ≃* rationalComponent S.ρ S.Γ (rootCharHom a) i := eML.symm.trans eMR
  let eQ := QuotientGroup.congr _ _ eLR (Subgroup.map_center_eq eLR)
  obtain ⟨lab, hlab, hhas, R, _, I, F, thetaL, hP⟩ := largeEvenMarking_exists_hasLabel hmark
  refine ⟨lab, hlab, hP.1, ?_⟩
  unfold GGHasLabel at hhas ⊢
  exact largeEvenRawDatum_mono (fun _ _ _ _ ⟨e⟩ => ⟨eQ.symm.trans e⟩) hhas

end CFSG.StandardType
