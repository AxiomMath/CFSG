module

public import CFSG.LocalAnalysis.StandardType.GGE0E6InnNormal
public import CFSG.LocalAnalysis.StandardType.GGE0ModelFrameOn
public import CFSG.LocalAnalysis.StandardType.GGE0ExcNoSuzukiReeAt
public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151PCompAction
public import CFSG.LocalAnalysis.StandardType.GGE0ExcAdjNormal
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeAssemblyHolds
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeInnAutRest
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeInnAutLinear
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeInnAutUnitary
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXQuasi
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FU9LabHolds
public import CFSG.LocalAnalysis.GLTheoremA.S10.CaseGamma
public import CFSG.LocalAnalysis.StandardType.GGOutTwoCommInnerHolds
public import CFSG.LocalAnalysis.StandardType.GGRawAutRestCore
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1315b
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.Parity
public import CFSG.LocalAnalysis.StandardType.GGExclNoIso
public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.LocalAnalysis.StandardType.GGReverseMarking
public import CFSG.LocalAnalysis.StandardType.GGE0MarkBridge
public import CFSG.LocalAnalysis.StandardType.GGLangExhaust
public import CFSG.LocalAnalysis.GLTheoremA.S10.CatDistinctShapes
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeE6KernelExit
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.E6BadLift
public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151DiagDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeD4ThreeHolds
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeE6KernelExitFacts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcAdj
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcInnerD4FixMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamChar2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeSpModel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeSpModelPairedMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeOrthPairMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeSpBlock
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeCompDescIndSymp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeOrthModelAnalysis
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeOrthCatCatalogue
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeOrthAsmPlus
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeOrthAsmMinus
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamTriAct
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamTriLang
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamTriMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeLinStatedInner
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeReeF4LargeRFHolds
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeTwSmall
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeUniInner
public import CFSG.Quasithin.Background.B3ThreeModel
public import CFSG.Quasithin.Background.B3ThreeStruct
public import CFSG.Quasithin.Background.G2Omega4PlusModule
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2CompO
public import CFSG.Quasithin.EmptyFaithful.R3c19B
public import CFSG.Quasithin.EmptyFaithful.S143FF
public import CFSG.Quasithin.EmptyFaithful.S143Final
public import CFSG.Quasithin.EmptyFaithful.S143HD
public import CFSG.Quasithin.EmptyFaithful.S143IG
public import CFSG.Quasithin.EmptyFaithful.S143JB
public import CFSG.Quasithin.EmptyFaithful.S143KO
public import CFSG.Quasithin.EmptyFaithful.S143KP
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15421
public import CFSG.RankThree.PartOne.N143.HighEvenU

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Open

open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA (chevQuotHom chevAut chevAut_chevQuotHom)
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.MI
open CFSG.LocalAnalysis.GLTheoremA.T171Sh
open CFSG.LocalAnalysis.GLTheoremA.T263.DX
open CFSG.GroupActions
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom onCenterQuotient
  onCenterQuotient_apply_mk centerQuotientHom_congr)
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived Outer inner
  mem_innAutDerived_congr inner_map_congr congr_mem_inner_iff)
open CFSG.LocalAnalysis.GLTheoremA.S265C.DynE

theorem shapeAct_mem_normalizer_commutator_self {G : Type*} [Group G] {H : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) :
    g ∈ Subgroup.normalizer ((⁅H, H⁆ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hg ⊢
  rw [Subgroup.map_commutator, hg]

theorem shapeAct_chevStTag_of_markTag {lab : LargeEvenLabel} {t : StatedLieTag}
    (ht : markTag lab = t) (hB2 : t ≠ .twistedB2) (hF4 : t ≠ .twistedF4)
    (hTits : t ≠ .Tits) : GGChevStTag lab := by
  obtain ⟨tag, r, n⟩ := lab
  cases tag <;> simp only [markTag, GGChevStTag] at ht ⊢
  all_goals first
    | decide
    | exact (hB2 ht.symm).elim
    | exact (hF4 ht.symm).elim
    | exact (hTits ht.symm).elim

theorem shapeAct_tag_ne_of_ade {t : StatedLieTag} (ht : IsADETag t ∨ t = .trialityD4) :
    t ≠ .Tits ∧ t ≠ .twistedB2 ∧ t ≠ .twistedF4 := by
  rcases ht with ht | rfl
  · rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨by decide, by decide, by decide⟩
  · exact ⟨by decide, by decide, by decide⟩

theorem shapeAct_largeEvenMarking_chevSt
    {Γ : Type} [Group Γ] {J : Subgroup Γ}
    (hperf : commutator ↥J = ⊤) {t : StatedLieTag} {n f : ℕ}
    (hLM : CFSG.Blueprint.LieModel (↥J ⧸ Subgroup.center ↥J) t n 2 f)
    (htB2 : t ≠ .twistedB2) (htF4 : t ≠ .twistedF4) (htTits : t ≠ .Tits) :
    LargeEvenMarking ↥J (fun lab _ _ _ _ _ => GGChevStTag lab) :=
  largeEvenMarking_mono
    (fun lab _ _ _ _ _ h => shapeAct_chevStTag_of_markTag h.1 htB2 htF4 htTits)
    (CFSG.StandardType.largeEvenMarking_of_lieModel_centerQuot hperf hLM)

theorem shapeAct_innDiagOn
    {Γ : Type} [Group Γ] [Finite Γ] {p : ℕ} (hp : p.Prime)
    {J : Subgroup Γ} {a : Γ} (haJ : a ∈ Subgroup.normalizer (J : Set Γ))
    (hJq : CFSG.Open.IsQuasisimple ↥J)
    (hdvdZ : p ∣ Nat.card (↥J ⧸ Subgroup.center ↥J))
    {t : StatedLieTag} {n f : ℕ}
    (hLM : CFSG.Blueprint.LieModel (PSimple p J) t n 2 f)
    (hcase : ¬ (t = .POmegaPlus ∧ n = 4) ∨ indAut p J a haJ ∈ inner (PSimple p J))
    (htits : t ≠ .Tits)
    (hmem : indAut p J a haJ ∈ innAutDerived (PSimple p J)) :
    InnDiagOn p (Subgroup.zpowers a) J := by
  have hJq_nat : CFSG.IsQuasisimple ↥J :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥J).1 hJq
  have hdvdZ' : p ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) := hdvdZ
  have hq : CFSG.IsQuasisimple (PQuot p J) :=
    CFSG.LocalAnalysis.GLTheoremA.T263.DX.isQuasisimple_pQuot_of_dvd hp hJq_nat hdvdZ'
  rcases hcase with hnot | hinn
  · exact CFSG.LocalAnalysis.GLTheoremA.T171Sh.innDiagOn_of_lieModel
      haJ hq hLM hnot htits hmem
  · exact CFSG.LocalAnalysis.GLTheoremA.T171Sh.KExit.innDiagOn_of_lieModel_of_inner
      haJ hq hLM htits hinn

theorem shapeAct_centerQuot_mem_transport {G H : Type} [Group G] [Group H]
    (e : G ≃* H) {α : MulAut G} {β : MulAut H} (hαβ : MulAut.congr e α = β)
    (h : centerQuotientHom H β ∈ innAutDerived (H ⧸ Subgroup.center H)) :
    centerQuotientHom G α ∈ innAutDerived (G ⧸ Subgroup.center G) :=
  (mem_innAutDerived_congr (QuotientGroup.congr (Subgroup.center G) (Subgroup.center H) e
    (Subgroup.map_center_eq e))).mp (by
      rw [centerQuotientHom_congr e α, hαβ]
      exact h)

theorem shapeAct_centerQuot_mem_inner_transport {G H : Type} [Group G] [Group H]
    (e : G ≃* H) {α : MulAut G} {β : MulAut H} (hαβ : MulAut.congr e α = β)
    (h : centerQuotientHom H β ∈ inner (H ⧸ Subgroup.center H)) :
    centerQuotientHom G α ∈ inner (G ⧸ Subgroup.center G) :=
  (congr_mem_inner_iff (QuotientGroup.congr (Subgroup.center G) (Subgroup.center H) e
    (Subgroup.map_center_eq e)) (centerQuotientHom G α)).mp (by
      rw [centerQuotientHom_congr e α, hαβ]
      exact h)

theorem shapeAct_lieModel_centerQuot_transport {G H : Type} [Group G] [Group H]
    (e : G ≃* H) {t : StatedLieTag} {n f : ℕ}
    (hLM : CFSG.Blueprint.LieModel (H ⧸ Subgroup.center H) t n 2 f) :
    CFSG.Blueprint.LieModel (G ⧸ Subgroup.center G) t n 2 f :=
  CFSG.Blueprint.LieModel.of_mulEquiv
    (QuotientGroup.congr (Subgroup.center G) (Subgroup.center H) e
      (Subgroup.map_center_eq e)).symm hLM

theorem shapeAct_map_le_normalizer_iff {H G : Type} [Group H] [Group G] (f : H →* G)
    (hf : Function.Injective f) (E X : Subgroup H) :
    E.map f ≤ Subgroup.normalizer (X.map f : Set G) ↔
      E ≤ Subgroup.normalizer (X : Set H) := by
  constructor
  · intro h
    calc E ≤ ((E.map f).comap f) := by
          intro x hx
          exact Subgroup.mem_map_of_mem f hx
      _ ≤ (Subgroup.normalizer ((X.map f : Subgroup G) : Set G)).comap f :=
          Subgroup.comap_mono h
      _ ≤ Subgroup.normalizer (((X.map f : Subgroup G).comap f) : Set H) :=
          Subgroup.le_normalizer_comap f
      _ = Subgroup.normalizer (X : Set H) := by
          rw [Subgroup.comap_map_eq_self_of_injective hf X]
  · intro h
    calc E.map f ≤ (Subgroup.normalizer (X : Set H)).map f := Subgroup.map_mono h
      _ ≤ Subgroup.normalizer ((X.map f : Subgroup G) : Set G) :=
        Subgroup.le_normalizer_map f

theorem shapeAct_congr_subgroupStabRestrict {G H : Type} [Group G] [Group H]
    {J : Subgroup G} {R : Subgroup H} (e : ↥J ≃* ↥R) {a : G} {b : H}
    (haJ : a ∈ Subgroup.normalizer (J : Set G))
    (hbR : b ∈ Subgroup.normalizer (R : Set H))
    (hact : ∀ y : ↥J,
      e (subgroupStabRestrict J ⟨MulAut.conj a,
          Subgroup.mem_normalizer_iff_map_conj_eq.mp haJ⟩ y) =
        subgroupStabRestrict R ⟨MulAut.conj b,
          Subgroup.mem_normalizer_iff_map_conj_eq.mp hbR⟩ (e y)) :
    MulAut.congr e (subgroupStabRestrict J ⟨MulAut.conj a,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp haJ⟩) =
      subgroupStabRestrict R ⟨MulAut.conj b,
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hbR⟩ := by
  ext x
  rw [MulAut.congr_apply]
  simpa using hact (e.symm x)

theorem shapeAct_card_ne_360
    {X : Type} [Group X] {t : StatedLieTag} {n f : ℕ}
    (hLM : CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X) t n 2 f) :
    Nat.card (X ⧸ Subgroup.center X) ≠ 360 :=
  CFSG.Quasithin.H13.EvenOrd.card_ne_of_evenLieType
    CFSG.Quasithin.H13.EvenOrd.excl_360 ⟨t, n, f, hLM.admissible, hLM⟩

end CFSG.StandardType

end
