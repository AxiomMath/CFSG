module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2HighestRootLong
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2GeoSp
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortSp
public import CFSG.RankThree.GF2n.Tim79aClassicalSp
public import CFSG.Timmesfeld.Transvection.ModelSpRadical
public import CFSG.ClassicalInvolution.ModelFacts.Families
public import CFSG.Sporadic.Th.Max3.Data
public import CFSG.CGT.T75E.Lemma26
public import CFSG.CGT.Timmesfeld75.Sec3TenCaseA
public import CFSG.CGT.Timmesfeld75.Sec4CaseIBasic
public import CFSG.CGT.Timmesfeld75.Sec4CaseIIIFour
public import CFSG.CGT.Timmesfeld75.Sec4CaseIJFamily
public import CFSG.CGT.Timmesfeld75.Sec4CaseIJIdent
public import CFSG.CGT.Timmesfeld75.Sec4CaseIPGroup
public import CFSG.CGT.Timmesfeld75.Sec4CaseIPartition4
public import CFSG.CGT.Timmesfeld75.Sec4Three
public import CFSG.CGT.Timmesfeld75.Sec5FiveEng
public import CFSG.CGT.Timmesfeld75.Step511Card
public import CFSG.CGT.Timmesfeld75.Step57Reduction
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.ClassicalGroups.Linear.TwoCentres
public import CFSG.Combinatorics.AperiodicCentralInvolution
public import CFSG.Combinatorics.AperiodicFiveOfSix
public import CFSG.Combinatorics.AperiodicOppositeComponents
public import CFSG.Combinatorics.AperiodicSixteenGraphDistances
public import CFSG.Combinatorics.OuterLayerPredecessors
public import CFSG.GH74.Uniqueness.Bender.OddCentralizer
public import CFSG.GH74.Uniqueness.Bender.Unitary
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.Asc76BenderFacts
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupFacts
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3GoldschmidtFacts
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvUnitary
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderAutE4Unitary
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderONan
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.RankThree.GF2n.Tim79aCase1End
public import CFSG.RankThree.GF2n.Tim79aCentreClause
public import CFSG.RankThree.GF2n.Tim79aIdentU3
public import CFSG.RankThree.GF2n.Tim79aSec2
public import CFSG.RankThree.GF2n.Tim79aWCQInputs
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Defs
public import CFSG.Sporadic.Th.Max3.Involutions
public import Certificates.Certificate10089Base
public import Certificates.Certificate10091Base
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.StandardType.LieKnownR2.PSp

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic
  CFSG.LieType.Universal.Symplectic.SpExtras CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.LieType.Steinberg CFSG.LieType.HighestRoot CFSG.LieType.TitsSimplicity
  CFSG.ClassicalInvolution.ModelFacts CFSG.StandardType.ClassicalPosition
  CFSG.Timmesfeld.ARS.CaseM TauCeti.GLSymplecticFin
open scoped commutatorElement Matrix

private abbrev l10scsp_J (n : ℕ) (F : Type) [Field F] :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F :=
  Matrix.fromBlocks 0 1 (-1) 0

private theorem l10scsp_vecMul_J {n : ℕ} {F : Type} [Field F] [CharP F 2]
    (v : Fin n ⊕ Fin n → F) :
    v ᵥ* (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) v := by
  have hJ : (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)ᵀ =
      Matrix.fromBlocks 0 1 (-1) 0 := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Matrix.fromBlocks, Matrix.one_apply, CharTwo.neg_eq, eq_comm]
  have h := Matrix.vecMul_transpose (Matrix.fromBlocks 0 1 (-1) 0 :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) v
  rwa [hJ] at h

private theorem l10scsp_transv_mul {n : ℕ} {F : Type} [Field F]
    (c d : F) (W : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) (hW : W * W = 0) :
    (1 + c • W) * (1 + d • W) = 1 + (c + d) • W := by
  have h1 : (1 + c • W) * (1 + d • W) = 1 + c • W + d • W := by
    rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul,
      Matrix.smul_mul, hW, smul_zero, smul_add, smul_zero, add_zero]
  rw [h1, add_assoc, ← add_smul]

private theorem l10scsp_mem_matTransvGroup_iff {n : ℕ} {F : Type} [Field F] [CharP F 2]
    (v : Fin n ⊕ Fin n → F) (g : GL (Fin n ⊕ Fin n) F) :
    g ∈ matTransvGroup v (l10scsp_J n F *ᵥ v) ↔
      ∃ c : F, (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
        1 + c • Matrix.vecMulVec v (l10scsp_J n F *ᵥ v) := by
  have hφv : (l10scsp_J n F *ᵥ v) ⬝ᵥ v = 0 := by
    rw [dotProduct_comm]
    change CFSG.Timmesfeld.ARS.CaseM.spForm v v = 0
    exact CFSG.Timmesfeld.ARS.CaseM.spForm_self v
  have hWsq : Matrix.vecMulVec v (l10scsp_J n F *ᵥ v) *
      Matrix.vecMulVec v (l10scsp_J n F *ᵥ v) = 0 := by
    rw [Matrix.vecMulVec_mul_vecMulVec, hφv, zero_smul]
    simp
  constructor
  · intro hg
    induction hg using Subgroup.closure_induction with
    | mem y hy => exact hy
    | one => exact ⟨0, by simp⟩
    | mul y z _ _ ihy ihz =>
        obtain ⟨c, hc⟩ := ihy
        obtain ⟨d, hd⟩ := ihz
        refine ⟨c + d, ?_⟩
        rw [Units.val_mul, hc, hd, l10scsp_transv_mul c d _ hWsq]
    | inv y _ ihy =>
        obtain ⟨c, hc⟩ := ihy
        have hyy : y * y = 1 := by
          apply Units.ext
          rw [Units.val_mul, hc, l10scsp_transv_mul c c _ hWsq,
            CharTwo.add_self_eq_zero, zero_smul, add_zero, Units.val_one]
        refine ⟨c, ?_⟩
        rw [inv_eq_of_mul_eq_one_right hyy]
        exact hc
  · rintro ⟨c, hc⟩
    exact Subgroup.subset_closure ⟨c, hc⟩

private theorem l10scsp_isTransGroup_of_map_eq {n : ℕ} {F : Type} [Field F] [CharP F 2]
    {v : Fin n ⊕ Fin n → F} {X : Subgroup (StatedSp n F)}
    (h : X.map (StatedSp n F).subtype = matTransvGroup v (l10scsp_J n F *ᵥ v)) :
    CFSG.Timmesfeld.ARS.CaseM.IsTransGroup v X := by
  have hmem : ∀ x : StatedSp n F,
      (StatedSp n F).subtype x ∈ X.map (StatedSp n F).subtype ↔ x ∈ X := by
    intro x
    constructor
    · intro hx
      obtain ⟨y, hy, hyx⟩ :=
        show ∃ y ∈ X, (StatedSp n F).subtype y = (StatedSp n F).subtype x from hx
      simpa only [Subtype.ext hyx] using hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  refine ⟨fun x => ?_, fun c => ?_⟩
  · rw [← hmem x, h, l10scsp_mem_matTransvGroup_iff]
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_⟩
      change ((StatedSp n F).subtype x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
        CFSG.Timmesfeld.ARS.CaseM.spTrans v c
      rw [hc]
      simp only [CFSG.Timmesfeld.ARS.CaseM.spTrans, CFSG.Timmesfeld.ARS.CaseM.spNil,
        CFSG.Timmesfeld.ARS.CaseM.spGram, l10scsp_vecMul_J, l10scsp_J]
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_⟩
      change mat n F x = 1 + c • Matrix.vecMulVec v (l10scsp_J n F *ᵥ v)
      rw [hc]
      simp only [CFSG.Timmesfeld.ARS.CaseM.spTrans, CFSG.Timmesfeld.ARS.CaseM.spNil,
        CFSG.Timmesfeld.ARS.CaseM.spGram, l10scsp_vecMul_J, l10scsp_J]
  · exact CFSG.Timmesfeld.Transvection.ModelRank.exists_mat_eq_spTrans v c

private theorem l10scsp_coreFour_statedSp {n : ℕ} {F : Type} [Field F] [CharP F 2] [Finite F]
    {β : Fin (Symplectic.rootDatum n F).rank → ℤ}
    (hβ : β ∈ (Symplectic.rootDatum n F).roots)
    (hl : GGLongRoot (Symplectic.rootDatum n F) β) (u : StatedSp n F)
    {Rr Q : Subgroup (StatedSp n F)}
    (hRr : Rr = ((Symplectic.rootDatum n F).rootGroup β).map (MulAut.conj u).toMonoidHom)
    (hQ : Q = pCoreOf 2 (Subgroup.normalizer (Rr : Set (StatedSp n F)))) :
    ⁅Q, Q⁆ ≤ Rr ∧ Q ≤ Subgroup.centralizer (Rr : Set (StatedSp n F)) := by
  obtain ⟨v, w, hvw, hRv, hRw⟩ :=
    Geo.exists_matTransvGroup_eq_conj_rootGroup_Sp n F hβ hl u
  have hRrmap : Rr.map (StatedSp n F).subtype =
      matTransvGroup v (l10scsp_J n F *ᵥ v) := by
    rw [hRr]
    simp only [l10scsp_J]
    exact hRv
  have hT : CFSG.Timmesfeld.ARS.CaseM.IsTransGroup v Rr :=
    l10scsp_isTransGroup_of_map_eq hRrmap
  have hv : v ≠ 0 := by
    intro hv0
    rw [hv0] at hvw
    simp only [Pi.zero_apply, zero_dotProduct] at hvw
    exact one_ne_zero hvw.symm
  have hQ' : Q = CFSG.Timmesfeld.Transvection.ModelRank.spRad v := by
    rw [hQ]
    exact CFSG.RankThree.GF2n.Tim79a.spCoreStmt_holds n F hv hT
  refine ⟨?_, ?_⟩
  · rw [hQ', Subgroup.commutator_le]
    intro g hg h hh
    rw [commutatorElement_def]
    have hgh : g * h = h * g :=
      CFSG.Timmesfeld.Transvection.ModelRank.spRadCommStmt_holds (n := n) (F := F)
        hv g hg h hh
    rw [hgh]
    simpa using Rr.one_mem
  · rw [hQ']
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨c, hc⟩ := (hT.1 y).1 hy
    have hga : mat n F g *ᵥ v = v := hg.1
    have hconj : g * y * g⁻¹ = y := by
      apply SpExtras.mat_injective
      rw [mat_conj_of_mat_eq hc g, hga, hc]
    calc y * g = (g * y * g⁻¹) * g := by rw [hconj]
      _ = g * y := by group

private theorem l10scsp_theta_maxHeight {n : ℕ} (hn0 : 0 < n)
    {θ : Fin n → ℤ}
    (hθstd : toStd n θ = stdVec (RootSubgroupIndex.positiveLong ⟨0, hn0⟩)) :
    ∀ δ ∈ roots (isFiniteType_cartanC n) ∅, ht δ ≤ ht θ := by
  intro δ hδ
  obtain ⟨r, hr⟩ := SpExtras.exists_stdVec_of_mem_roots hδ
  have h1 : 2 * ht δ = lv n (stdVec r) := by
    rw [SpExtras.two_mul_ht (n := n) δ, hr]
  have h2 := GGRootSp.lv_stdVec_le r
  have h3 : 2 * ht θ = 2 * (2 * n - 1) := by
    rw [SpExtras.two_mul_ht, hθstd, stdVec, map_nsmul, lv_single, nsmul_eq_mul]
    push_cast
    ring_nf
  linarith

private theorem l10scsp_maxHeight_eq {n : ℕ} (hn0 : 0 < n)
    {θ : Fin n → ℤ} (hθmem : θ ∈ roots (isFiniteType_cartanC n) ∅)
    (hθstd : toStd n θ = stdVec (RootSubgroupIndex.positiveLong ⟨0, hn0⟩))
    {γ₀ : Fin n → ℤ} (hγ₀ : γ₀ ∈ roots (isFiniteType_cartanC n) ∅)
    (hmax₀ : ∀ δ ∈ roots (isFiniteType_cartanC n) ∅, ht δ ≤ ht γ₀) :
    γ₀ = θ := by
  have hmaxθ := l10scsp_theta_maxHeight hn0 hθstd
  obtain ⟨r₀, hr₀⟩ := SpExtras.exists_stdVec_of_mem_roots hγ₀
  have hθ2 : 2 * ht θ = 2 * (2 * n - 1) := by
    rw [SpExtras.two_mul_ht, hθstd, stdVec, map_nsmul, lv_single, nsmul_eq_mul]
    push_cast
    ring_nf
  have hle : ht θ ≤ ht γ₀ := hmax₀ θ hθmem
  have h4 : 4 * (n : ℤ) - 4 < lv n (stdVec r₀) := by
    have hγ2 : 2 * ht γ₀ = lv n (stdVec r₀) := by
      rw [SpExtras.two_mul_ht (n := n) γ₀, hr₀]
    linarith
  by_cases hn2 : 2 ≤ n
  · have hstd := GGRootSp.stdVec_eq_of_lv_lt hn2 r₀ h4
    apply SpExtras.toStd_inj
    rw [← hr₀, hstd, hθstd]
  · have hn1 : n = 1 := by omega
    subst hn1
    have hstd : stdVec r₀ = stdVec (RootSubgroupIndex.positiveLong ⟨0, hn0⟩) := by
      cases r₀ with
      | positiveLong i =>
          have hi : i = (⟨0, hn0⟩ : Fin 1) := Fin.ext (by have := i.isLt; omega)
          rw [hi]
      | negativeLong i =>
          exfalso
          rw [stdVec, map_neg, map_nsmul, lv_single, nsmul_eq_mul] at h4
          have hi : (i : ℤ) = 0 := by have := i.isLt; omega
          omega
      | difference i j hij =>
          exact absurd (Fin.ext (by have := i.isLt; have := j.isLt; omega)) hij
      | positiveSum i j hij =>
          exact absurd (Fin.lt_def.1 hij) (by have := i.isLt; have := j.isLt; omega)
      | negativeSum i j hij =>
          exact absurd (Fin.lt_def.1 hij) (by have := i.isLt; have := j.isLt; omega)
    apply SpExtras.toStd_inj
    rw [← hr₀, hstd, hθstd]

private theorem l10scsp_highest_sp {n : ℕ} {F : Type} [Field F]
    {β : Fin (Symplectic.rootDatum n F).rank → ℤ}
    (hl : GGLongRoot (Symplectic.rootDatum n F) β) :
    (Symplectic.rootDatum n F).divisible = ∅ ∧
      IsIrreducible (Symplectic.rootDatum n F).cartan ∧
      ∃ r : Fin (Symplectic.rootDatum n F).rank → ℤ,
        IsHighestRoot (Symplectic.rootDatum n F) r ∧
        ∀ γ₀ ∈ (Symplectic.rootDatum n F).roots,
          (∀ δ ∈ (Symplectic.rootDatum n F).roots, ht δ ≤ ht γ₀) → γ₀ = r := by
  have hn0 : 0 < n := by
    obtain ⟨w, γ₀, hγ₀, -, -⟩ := hl
    obtain ⟨r, -⟩ := SpExtras.exists_stdVec_of_mem_roots hγ₀
    rcases r with i | i | ⟨i, _, _⟩ | ⟨i, _, _⟩ | ⟨i, _, _⟩ <;> exact i.pos
  obtain ⟨θ, hθmem, hθstd⟩ :=
    GGRootSp.exists_root_toStd_eq (n := n) (.positiveLong ⟨0, hn0⟩)
  have hmaxθ := l10scsp_theta_maxHeight hn0 hθstd
  obtain ⟨r, hr⟩ := CFSG.LieType.HighestRoot.exists_isHighestRoot
    (D := Symplectic.rootDatum n F) (isIrreducible_cartanC hn0) rfl hn0
  have hreq : r = θ :=
    l10scsp_maxHeight_eq hn0 hθmem hθstd hr.mem_roots
      (fun δ hδ => le_trans (hmaxθ δ hδ) (hr.height_le θ hθmem))
  subst r
  refine ⟨rfl, isIrreducible_cartanC hn0, θ, hr, ?_⟩
  intro γ₀ hγ₀ hmax₀
  exact l10scsp_maxHeight_eq hn0 hθmem hθstd hγ₀ hmax₀

private theorem l10scsp_highest
    {n f : ℕ} {β : Fin (ggU .PSp n f).D.rank → ℤ} (hl : GGLongRoot (ggU .PSp n f).D β) :
    (ggU .PSp n f).D.divisible = ∅ ∧ IsIrreducible (ggU .PSp n f).D.cartan ∧
      ∃ r : Fin (ggU .PSp n f).D.rank → ℤ, IsHighestRoot (ggU .PSp n f).D r ∧
        ∀ γ₀ ∈ (ggU .PSp n f).D.roots,
          (∀ δ ∈ (ggU .PSp n f).D.roots, ht δ ≤ ht γ₀) → γ₀ = r := by
  exact l10scsp_highest_sp (F := GaloisField 2 f) hl

theorem coreOne_PSp_long
    {n f : ℕ}
    {β : Fin (ggU .PSp n f).D.rank → ℤ} (hl : GGLongRoot (ggU .PSp n f).D β)
    (u : (ggU .PSp n f).K) {Rr Rm Q : Subgroup (ggU .PSp n f).K}
    (hRr : Rr = ggRootSub (ggU .PSp n f).D (MonoidHom.id (ggU .PSp n f).K) β u)
    (hRm : Rm = ggRootSub (ggU .PSp n f).D (MonoidHom.id (ggU .PSp n f).K) (-β) u)
    (hQ : Q = pCoreOf 2 (Subgroup.normalizer (Rr : Set (ggU .PSp n f).K))) :
    Q ⊔ (Rr ⊔ Rm) = ⊤ := by
  obtain ⟨hdiv, hirr, r, hr, hmax⟩ := l10scsp_highest (f := f) hl
  exact coreOne_long_of
    (Symplectic.isCTGroupDatum (n := n) (F := GaloisField 2 f))
    (Symplectic.steinbergExtras n (GaloisField 2 f))
    hdiv hirr
    (fun γ hγ => GGRootSp.isPGroup_rootGroup hγ)
    hr hmax hl u hRr hRm hQ

theorem coreFour_PSp_long
    {n f : ℕ}
    {β : Fin (ggU .PSp n f).D.rank → ℤ} (hl : GGLongRoot (ggU .PSp n f).D β)
    (u : (ggU .PSp n f).K) {Rr Q : Subgroup (ggU .PSp n f).K}
    (hRr : Rr = ggRootSub (ggU .PSp n f).D (MonoidHom.id (ggU .PSp n f).K) β u)
    (hQ : Q = pCoreOf 2 (Subgroup.normalizer (Rr : Set (ggU .PSp n f).K))) :
    ⁅Q, Q⁆ ≤ Rr ∧ Q ≤ Subgroup.centralizer (Rr : Set (ggU .PSp n f).K) := by
  have hβ : β ∈ (ggU .PSp n f).D.roots := by
    obtain ⟨w, γ₀, hγ₀, -, hβeq⟩ := hl
    rw [hβeq]
    exact weylAction_mem_roots hγ₀ w
  refine l10scsp_coreFour_statedSp (F := GaloisField 2 f) hβ hl u ?_ hQ
  rw [hRr]
  simp only [ggRootSub, Subgroup.map_id]
  rfl

end CFSG.StandardType.LieKnownR2.PSp