module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNIRestr
public import CFSG.LocalAnalysis.StandardType.GGMarkingAllInduces
public import CFSG.LocalAnalysis.StandardType.GGTwistedF4DiagRaw
public import CFSG.LocalAnalysis.StandardType.GGExclNoIso
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45ConfigIso
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphismsCongr
public import CFSG.RankThree.PartTwo.Sec19.SimsC198Descent
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonInnBridge
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.HardMathSupport.Solomon.LocalBalance.ScpQuot
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Layer
public import CFSG.LocalAnalysis.EvenBN.Common.CommutatorFixed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsSetup
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.LocalAnalysis.GLTheoremA.S12.Bridge
public import CFSG.LocalAnalysis.GLTheoremA.S12.Prop123
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Proof
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem kgfni_not_induces_rawImage {R : Type} [Group R] {F : Set (MulAut R)}
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
  exact hFnot (MulAut.congr e f) hf' hord' (by simpa [H'] using hclosure hf'cl)

theorem kgInducedAut_induces {X : Type*} [Group X] {R : Type} [Group R]
    (θ : X ⧸ Subgroup.center X ≃* R) (α : MulAut X) :
    LargeEvenInduces θ (fun j k : X => k = α j) (kgInducedAut θ α) := by
  intro l l' hl
  subst hl
  exact ggInducedAut_apply θ α l

theorem largeEvenMarking_not_induces_of_not_inner {X : Type} [Group X]
    (hX : Group.IsPerfect X) (f : MulAut X)
    (hf : f ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner X)
    (hmark : LargeEvenMarking X (fun _ R _ I _ _ => I = LargeEvenInnSet R)) :
    LargeEvenMarking X (fun _ R _ I _ θ =>
      ¬ ∃ φ ∈ Subgroup.closure I,
        LargeEvenInduces θ (fun j k : X => k = f j) φ) := by
  refine largeEvenMarking_mono ?_ hmark
  intro lab R _ I F θ hI
  rintro ⟨φ, hφcl, hind⟩
  have hIinner : I =
      (CFSG.ComponentClassification.OuterAutomorphisms.inner R : Set (MulAut R)) := by
    rw [hI]
    rfl
  have hclosure : Subgroup.closure I =
      CFSG.ComponentClassification.OuterAutomorphisms.inner R := by
    rw [hIinner, Subgroup.closure_eq]
  have hφinner : φ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner R := by
    rw [← hclosure]
    exact hφcl
  have hφeq : φ = kgInducedAut θ f := by
    ext r
    obtain ⟨q, rfl⟩ := θ.surjective r
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    exact (hind x (f x) rfl).trans (kgInducedAut_induces θ f x (f x) rfl).symm
  have hkg : kgInducedAut θ f ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner R := by
    simpa [hφeq] using hφinner
  have hstd : CFSG.StandardType.centerQuotAut X f ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner
        (X ⧸ Subgroup.center X) := by
    refine (CFSG.ComponentClassification.OuterAutomorphisms.congr_mem_inner_iff θ
      (CFSG.StandardType.centerQuotAut X f)).mp ?_
    simpa [kgInducedAut] using hkg
  have hcenter : CFSG.StandardType.centerQuotAut X f =
      CFSG.RankThree.PartTwo.Sec19.SimsC198.centerQuotAut X f := by
    ext q
    induction q using QuotientGroup.induction_on
    rfl
  have hdonor : CFSG.RankThree.PartTwo.Sec19.SimsC198.centerQuotAut X f ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner
        (X ⧸ Subgroup.center X) := by
    simpa [hcenter] using hstd
  exact hf (CFSG.RankThree.PartTwo.Sec19.SimsC198.mem_inner_of_centerQuotAut hX hdonor)


theorem kgFieldRestriction_of_oneMarking {J : Type} [Group J] (f' : MulAut J)
    (h : LargeEvenMarking J fun _ _ _ I _ θ =>
      ¬ ∃ φ ∈ Subgroup.closure I, LargeEvenInduces θ (fun j k : J => k = f' j) φ) :
    GGMarkingAll (K := J) fun _ _ _ I _ θ => kgInducedAut θ f' ∉ I := by
  refine ggMarkingAll_mono (fun lab R _ I F θ hnot hmem => hnot ⟨kgInducedAut θ f',
    Subgroup.subset_closure hmem, kgInducedAut_induces θ f'⟩)
    (SCFourCover.ggMarkingAll_not_induces ggRawInnFieldInput_holds
      (ggRawInndiagIsoInput_of_rest (ggRawInndiagIsoRestInput_of_round5 ggRawInndiagIsoRound5_holds)) h)

theorem kgFieldRestriction_of_oneMarking_congr {X Y : Type} [Group X] [Group Y]
    (e : X ≃* Y) (f : MulAut X) (g : MulAut Y)
    (hfg : ∀ x : X, e (f x) = g (e x))
    (hmark : LargeEvenMarking Y fun _ _ _ I _ θ =>
      ¬ ∃ φ ∈ Subgroup.closure I, LargeEvenInduces θ (fun j k : Y => k = g j) φ) :
    GGMarkingAll (K := X) fun _ _ _ I _ θ => kgInducedAut θ f ∉ I := by
  apply kgFieldRestriction_of_oneMarking f
  refine largeEvenMarking_congr e ?_ hmark
  intro lab R _ I F θ hθ
  rintro ⟨φ, hφ, hind⟩
  have hrel : ∀ x x' : X, (x' = f x) ↔ (e x' = g (e x)) := by
    intro x x'
    rw [← hfg x]
    exact e.injective.eq_iff.symm
  exact hθ ⟨φ, hφ,
    (largeEvenInduces_congr_equiv e θ (fun j k : X => k = f j)
      (fun j k : Y => k = g j) hrel φ).1 hind⟩

theorem kgFieldRestriction_hOne {R : Type} [Group R] [IsSimpleGroup R]
    {f : MulAut R}
    (hmark : LargeEvenMarking R fun _ _ _ I _ θ =>
      ¬ ∃ φ ∈ Subgroup.closure I, LargeEvenInduces θ (fun j k : R => k = f j) φ)
    {J : Subgroup R}
    (hJ : IsComponentOf J (MonoidHom.eqLocus ((1 : MulAut R) : R →* R) (MonoidHom.id R)))
    (f' : MulAut J) (hf' : ∀ j : J, (f' j : R) = f j) :
    GGMarkingAll (K := J) fun _ _ _ I _ θ => kgInducedAut θ f' ∉ I := by
  have htopEq : MonoidHom.eqLocus ((1 : MulAut R) : R →* R) (MonoidHom.id R) = ⊤ := by
    rw [show ((1 : MulAut R) : R →* R) = MonoidHom.id R from rfl, MonoidHom.eqLocus_same]
  have hJsub : IsSubnormal J ⊤ := htopEq ▸ hJ.2.1
  have hJtop : J = ⊤ := by
    rcases hJsub.eq_bot_or_top (G := R) with hbot | htop
    · exfalso
      have hNontriv : Nontrivial (↥J ⧸ Subgroup.center ↥J) := hJ.2.2.2.toNontrivial
      have hJnt : Nontrivial ↥J :=
        @Function.Surjective.nontrivial ↥J (↥J ⧸ Subgroup.center ↥J) hNontriv _
          (QuotientGroup.mk'_surjective (Subgroup.center ↥J))
      exact (Subgroup.nontrivial_iff_ne_bot J).mp hJnt hbot
    · exact htop
  subst hJtop
  let e : ↥(⊤ : Subgroup R) ≃* R := Subgroup.topEquiv
  exact kgFieldRestriction_of_oneMarking_congr e f' f hf' hmark

theorem kgFieldRestriction_hOne_of_rawImage {lab : LargeEvenLabel}
    {R : Type} [Group R] {F : Set (MulAut R)} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hlab : LargeEvenInLambda2 lab)
    (hsimple : LargeEvenLabelAll lab fun R' _ _ _ =>
      IsSimpleGroup R' ∧ ∃ a b : R', a * b ≠ b * a)
    (hself : LargeEvenRawDatum lab fun R' _ _ F' => ∃ e : R ≃* R', F' = MulAut.congr e '' F) :
    ∀ f ∈ F, orderOf f = p →
      ∀ J : Subgroup R,
        IsComponentOf J (MonoidHom.eqLocus ((1 : MulAut R) : R →* R) (MonoidHom.id R)) →
        ∀ f' : MulAut J, (∀ j : J, (f' j : R) = f j) →
          GGMarkingAll (K := J) fun _ _ _ I' _ θ' => kgInducedAut θ' f' ∉ I' := by
  have hboth := largeEvenLabelAll_and hsimple (ggRawInnFieldInput_holds p hp hp2 lab hlab) _ hself
  obtain ⟨R', _, _, _, ⟨e, _⟩, ⟨hsimple', hna'⟩, _⟩ := largeEvenRawDatum_exists hboth
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
    refine ⟨hcommR, lab, hlab, (largeEvenRawDatum_legacy lab _).mp ?_⟩
    refine largeEvenRawDatum_mono ?_ hboth
    rintro R'' _ I'' F'' ⟨⟨e'', hF''⟩, ⟨hsimple'', hna''⟩, hinn''⟩
    exact ⟨hsimple'', hna'',
      ⟨(CFSG.LocalAnalysis.GLTheoremA.CanonInn.quotCenterEquivOfBot hcenterR).trans e'',
        kgfni_not_induces_rawImage hcenterR e'' hF'' hsimple'' hna'' hinn'' hf hord⟩⟩
  letI : IsSimpleGroup R := hsimpleR
  exact kgFieldRestriction_hOne hmark hJ f' hf'

end CFSG.StandardType
