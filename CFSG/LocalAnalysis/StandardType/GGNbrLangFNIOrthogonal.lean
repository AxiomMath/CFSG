module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNIOne
public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNILinMark
public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNIVacClassical
public import CFSG.LocalAnalysis.StandardType.GGAssemblyThreeHypSix
public import CFSG.LocalAnalysis.StandardType.GGNbrGraphFieldLinear
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldLinear
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownLinearProj
public import CFSG.LocalAnalysis.StandardType.GGE0LiftGeneric
public import CFSG.LocalAnalysis.StandardType.GGE0PSLComp
public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNILinBlock
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShCompTransport
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherGraphFieldInvolution
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution
public import CFSG.HardMathSupport.Solomon.Proving.PSL2CentSolvableProof
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5LayerGroup
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonInnBridge
public import CFSG.HardMathSupport.Dickson.I271.ChevPBal
public import CFSG.HardMathSupport.Dickson.I271.I202Full
public import CFSG.HardMathSupport.Dickson.I271.Support.OuterStep
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3LInput
public import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltMain
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Derivation
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Input252
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6D62
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E66
public import CFSG.Holt.Fixed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.KD76c
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I1132
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KDSU3Holds
public import CFSG.LocalAnalysis.GLTheoremA.PartI.RankTwoDown
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultSporadic
public import CFSG.LocalAnalysis.GLTheoremA.S4.YS02Holds
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyU3Top
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Engine
public import CFSG.LocalAnalysis.RankThreeTheoremC.InvariantTwoBalanceThree
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Transitive
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294Inputs
public import CFSG.LocalAnalysis.RankThreeTheoremC.PlaneTransvection
public import CFSG.Quasithin.Background.C1PackS15212C
public import CFSG.Quasithin.Background.F918H5
public import CFSG.Quasithin.Background.GoldschmidtS146RBend1
public import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructFieldExt
public import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructPGL
public import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructSimple
public import CFSG.Quasithin.EmptyFaithful.S14610Q1
public import CFSG.Quasithin.EmptyFaithful.S14610Top
public import CFSG.Quasithin.EmptyFaithful.S146F4
public import CFSG.Quasithin.EmptyFaithful.S152Y15
public import CFSG.Quasithin.EmptyFaithful.S152Y19
public import CFSG.Quasithin.EmptyFaithful.S153E59A
public import CFSG.Quasithin.Recognition.ModelBridges
public import CFSG.Quasithin.Vol2.Ch1EightFourChar2
public import CFSG.Quasithin.Vol2.Ch3Sec3InspF618Tools
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3315R
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3323B
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3324X
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3329
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3330
public import CFSG.RankThree.PartTwo.Sec11.Data
public import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
public import CFSG.RankThree.PartTwo.Sec14.Item143N
public import CFSG.RankThree.PartTwo.Sec15.Item157
public import CFSG.RankThree.PartTwo.Sec16.Item163ProofR
public import CFSG.RankThree.PartTwo.Sec16.Item164Proof
public import CFSG.RankThree.PartTwo.Sec16.Item169HJ
public import CFSG.RankThree.PartTwo.Sec17.Item1724Two
public import CFSG.RankThree.PartTwo.Sec17.Item17TailSteps
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers142
public import CFSG.RankThree.PartTwo.Sec6.Statements
public import CFSG.RankThree.S4Free.SuzukiEight
public import Certificates.Certificate8166

public section

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.LocalAnalysis.ComponentInitial
open LinearFlag

private theorem hOne_neg_of_rawImage {R : Type} [Group R] {F : Set (MulAut R)}
    {p : ℕ} {f : MulAut R} (hcenter : Subgroup.center R = ⊥)
    {R' : Type} [Group R'] {I' F' : Set (MulAut R')} (e : R ≃* R')
    (hF : F' = MulAut.congr e '' F)
    (hsimple : IsSimpleGroup R') (hna : ∃ a b : R', a * b ≠ b * a)
    (hinn : GGRawInnField p R' I' F') (hf : f ∈ F) (hord : orderOf f = p) :
    ¬ ∃ φ ∈ Subgroup.closure I',
      LargeEvenInduces
        ((CFSG.LocalAnalysis.GLTheoremA.CanonInn.quotCenterEquivOfBot hcenter).trans e)
        (fun j k : R => k = f j) φ := by
  rintro ⟨φ, hφcl, hind⟩
  obtain ⟨hmul, hinv, hconj, hFnot⟩ := hinn hsimple hna
  have hone : (1 : MulAut R') ∈ I' := by simpa using hconj 1
  let H' : Subgroup (MulAut R') :=
    { carrier := I', one_mem' := hone
      mul_mem' := fun ha hb => hmul _ ha _ hb
      inv_mem' := fun ha => hinv _ ha }
  have hclosure : Subgroup.closure I' ≤ H' := by
    rw [Subgroup.closure_le]
    exact fun x hx => by simpa [H'] using hx
  have hf' : MulAut.congr e f ∈ F' := by
    rw [hF]
    exact Set.mem_image_of_mem (MulAut.congr e) hf
  have hord' : orderOf (MulAut.congr e f) = p := by
    rw [(MulAut.congr e).orderOf_eq f, hord]
  have hφeq : φ = MulAut.congr e f := by
    ext r'
    obtain ⟨r, rfl⟩ := e.surjective r'
    have h := hind r (f r) rfl
    have h' : φ (e r) = e (f r) := by
      simpa [MulEquiv.trans_apply, CFSG.LocalAnalysis.GLTheoremA.CanonInn.quotCenterEquivOfBot_mk]
        using h
    have hcongr : MulAut.congr e f (e r) = e (f r) := by
      simp [MulAut.congr, MulEquiv.trans_apply]
    rw [hcongr]
    exact h'
  have hf'cl : MulAut.congr e f ∈ Subgroup.closure I' := by
    rw [← hφeq]
    exact hφcl
  have hf'I : MulAut.congr e f ∈ I' := by
    simpa [H'] using hclosure hf'cl
  exact hFnot (MulAut.congr e f) hf' hord' hf'I

theorem kgFieldRestriction_hOne_of_rawSelf {lab : LargeEvenLabel}
    {R : Type} [Group R] {F : Set (MulAut R)} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hlab : LargeEvenInLambda2 lab)
    (htag : lab.tag = .D ∨ lab.tag = .twD)
    (hself : LargeEvenRawDatum lab (fun R' _ _ F' =>
      ∃ e : R ≃* R', F' = MulAut.congr e '' F)) :
    ∀ f ∈ F, orderOf f = p →
      ∀ J : Subgroup R,
        IsComponentOf J (MonoidHom.eqLocus ((1 : MulAut R) : R →* R) (MonoidHom.id R)) →
        ∀ f' : MulAut J, (∀ j : J, (f' j : R) = f j) →
          GGMarkingAll (K := J) fun _ _ _ I' _ θ' => kgInducedAut θ' f' ∉ I' := by
  have hS : KGFNIClassicalLabel lab := by
    rcases htag with h | h <;> simp [KGFNIClassicalLabel, h]
  have hboth : LargeEvenLabelAll lab (fun R' _ I' F' =>
      (IsSimpleGroup R' ∧ ∃ a b : R', a * b ≠ b * a) ∧ GGRawInnField p R' I' F') :=
    largeEvenLabelAll_and (kgfni_rawSimple_classical lab hlab hS)
      (ggRawInnFieldInput_holds p hp hp2 lab hlab)
  have hrawBoth := hboth _ hself
  have hrawBoth' := hrawBoth
  obtain ⟨R', _, I', F', hPred⟩ := largeEvenRawDatum_exists hrawBoth'
  obtain ⟨hQ, hrest⟩ := hPred
  obtain ⟨e, hF⟩ := hQ
  obtain ⟨hP, hinn'⟩ := hrest
  obtain ⟨hsimple', hna'⟩ := hP
  have hsimpleR : IsSimpleGroup R := (MulEquiv.isSimpleGroup_congr e).mpr hsimple'
  have hnaR : ∃ a b : R, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hna'
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  have hcenterR : Subgroup.center R = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center R) with hbot | htop
    · exact hbot
    · exfalso
      obtain ⟨a, b, hab⟩ := hnaR
      exact hab (Subgroup.mem_center_iff.mp (htop ▸ Subgroup.mem_top a) b).symm
  have hcommR : commutator R = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator R) with hbot | htop
    · have hcomm : IsMulCommutative R := (commutator_eq_bot_iff R).mp hbot
      obtain ⟨a, b, hab⟩ := hnaR
      exact absurd (hcomm.is_comm.comm a b) hab
    · exact htop
  intro f hf hord J hJ f' hf'
  have hmark : LargeEvenMarking R (fun _ _ _ I _ θ =>
      ¬ ∃ φ ∈ Subgroup.closure I, LargeEvenInduces θ (fun j k : R => k = f j) φ) := by
    refine ⟨hcommR, lab, hlab, ?_⟩
    refine (largeEvenRawDatum_legacy lab _).mp ?_
    refine largeEvenRawDatum_mono ?_ hrawBoth
    rintro R'' _ I'' F'' ⟨⟨e'', hF''⟩, ⟨hsimple'', hna''⟩, hinn''⟩
    exact ⟨hsimple'', hna'',
      ⟨(CFSG.LocalAnalysis.GLTheoremA.CanonInn.quotCenterEquivOfBot hcenterR).trans e'',
        hOne_neg_of_rawImage hcenterR e'' hF'' hsimple'' hna'' hinn'' hf hord⟩⟩
  letI : IsSimpleGroup R := hsimpleR
  exact kgFieldRestriction_hOne hmark hJ f' hf'

theorem kgFieldRestrictionOn_twD_two :
    KGFieldRestrictionOn (fun p lab =>
      lab.tag = .twD ∧ lab.rank = 2 ∧ p ∣ lab.n) := by
  intro p lab hp hp2 hlab _ht3 hrow
  obtain ⟨t, r, n⟩ := lab
  obtain ⟨ht, hr, _hdvd⟩ := hrow
  subst ht
  subst hr
  have hn : 1 ≤ n := hlab.1
  intro Q hraw
  dsimp only [LargeEvenRawDatum] at hraw ⊢
  dsimp only [LargeEvenRecipeLinear] at hraw ⊢
  obtain ⟨K, hF, hfin, hK, hQ⟩ := hraw
  letI := hF
  haveI := hfin
  let H := LargeEvenSLGroup (Fin 2) K
  let R := LargeEvenProj H
  let I := LargeEvenMatConjImage (LargeEvenProjMk H) Set.univ
  let F := LargeEvenMatFieldImage (LargeEvenProjMk H)
  have hcongr_refl : ∀ {X : Type} [Group X],
      MulAut.congr (MulEquiv.refl X) = MulEquiv.refl (MulAut X) := by
    intro X _
    ext f x
    simp [MulAut.congr, MulEquiv.trans_apply]
  have hself : LargeEvenRawDatum ⟨.twD, 2, n⟩ (fun R' _ _ F' =>
      ∃ e : R ≃* R', F' = MulAut.congr e '' F) := by
    dsimp only [LargeEvenRawDatum, LargeEvenRecipeLinear]
    exact ⟨K, inferInstance, inferInstance, hK,
      ⟨MulEquiv.refl R, by rw [hcongr_refl]; exact (Set.image_id F).symm⟩⟩
  refine ⟨K, inferInstance, inferInstance, hK, hQ, ?_⟩
  change KGFieldRestrictionCont p R I F
  intro f hf hord h hI hhp hcomm J hJ f' hf'
  by_cases h1 : h = 1
  · subst h1
    exact kgFieldRestriction_hOne_of_rawSelf hp hp2 hlab (Or.inr rfl) hself
      f hf hord J hJ f' hf'
  · exfalso
    have hK' : Nat.card K = 2 ^ (2 * n) := by
      rw [hK]
      conv_lhs => rw [← pow_mul, Nat.mul_comm]
    have hcop : (Nat.card Kˣ).Coprime 2 := by
      rw [Nat.card_units, hK']
      exact Nat.coprime_two_right.mpr (ggOdd_two_pow_sub_one (by omega))
    have hIinn : I ⊆ LargeEvenInnSet R := by
      dsimp only [I, R, H]
      exact matConjImage_gl_subset_inn (K := K) (d := 2) hcop
    obtain ⟨r, hr⟩ := hIinn hI
    have hr' : h = MulAut.conj r := hr.symm
    have hr1 : r ≠ 1 := by
      intro hrm
      apply h1
      rw [hr', hrm, map_one]
    have hfix : MonoidHom.eqLocus (h : R →* R) (MonoidHom.id R) =
        Subgroup.centralizer ({r} : Set R) := by
      rw [hr']
      ext x
      change (MulAut.conj r : R →* R) x = (MonoidHom.id R) x ↔
        x ∈ Subgroup.centralizer ({r} : Set R)
      rw [Subgroup.mem_centralizer_singleton_iff]
      simp only [MonoidHom.id_apply]
      constructor
      · intro hx
        have hx' : r * x * r⁻¹ = x := by simpa using hx
        calc x * r = (r * x * r⁻¹) * r := (congrArg (fun y => y * r) hx').symm
          _ = r * x := by group
      · intro hx
        have hx' : x * r = r * x := by simpa using hx
        calc r * x * r⁻¹ = (x * r) * r⁻¹ := by rw [← hx']
          _ = x := by group
    have hJ' : IsComponentOf J (Subgroup.centralizer ({r} : Set R)) := hfix ▸ hJ
    let e : R ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
      NbrGraphLinear.recipeEquivTwo K
    have hne : e r ≠ 1 := fun he =>
      hr1 (e.injective (he.trans (map_one e).symm))
    have hmap : (Subgroup.centralizer ({r} : Set R)).map e.toMonoidHom =
        Subgroup.centralizer
          ({e r} : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)) := by
      apply le_antisymm
      · simpa using Subgroup.map_centralizer_le_centralizer_image {r} e.toMonoidHom
      · intro y hy
        obtain ⟨x, rfl⟩ := e.surjective y
        refine Subgroup.mem_map_of_mem e.toMonoidHom ?_
        rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
        exact e.injective (by simpa using hy)
    have hSolvImage : Group.IsSolvable
        ↥((Subgroup.centralizer ({r} : Set R)).map e.toMonoidHom) := by
      rw [hmap]
      exact CFSG.HardMathSupport.Solomon.Proving.psl2CentSolvable_holds K (e r) hne
    let eC := Subgroup.equivMapOfInjective
      (Subgroup.centralizer ({r} : Set R)) e.toMonoidHom e.injective
    have hSolv : Group.IsSolvable ↥(Subgroup.centralizer ({r} : Set R)) :=
      Group.isSolvable_of_isSolvable_injective (f := eC.toMonoidHom) eC.injective
    exact CFSG.StandardType.Line63.H5.false_of_isComponentOf_of_isSolvable hSolv hJ'

theorem kgFieldRestrictionOn_D_three :
    KGFieldRestrictionOn (fun p lab =>
      lab.tag = .D ∧ lab.rank = 3 ∧ p ∣ lab.n) := by
  intro p lab hp hp2 hlab _ht3 hrow
  obtain ⟨t, r, n⟩ := lab
  obtain ⟨ht, hr, _hdvd⟩ := hrow
  subst ht
  subst hr
  have hn : 1 ≤ n := hlab.1
  intro Q hraw
  dsimp only [LargeEvenRawDatum] at hraw ⊢
  dsimp only [LargeEvenRecipeLinear] at hraw ⊢
  obtain ⟨K, hF, hfin, hK, hQ⟩ := hraw
  refine ⟨K, hF, hfin, hK, hQ, ?_⟩
  intro f hf hord h hI hhp hcomm J hJ f' hf'
  exact kgFieldRestriction_of_oneMarking f'
    (fniLin_oneMarking (N := 4) (n := n) (p := p) (by norm_num) hn hp hp2 hK hf hord hI hhp
      hcomm ((CFSG.Assembly.isComponentOf_iff_open).1 hJ) f' hf')

end CFSG.StandardType
