module

public import CFSG.LocalAnalysis.StandardType.GGSixPositionDefs
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.SymmetricGroup
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoPSLRoot
public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenA3TypeDet
public import CFSG.LocalAnalysis.GLTheoremA.S11.Lemma117
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.Dihedral.DihedralFusionPrefixes
public import CFSG.Goldschmidt.Basic
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
public import CFSG.Holt.Fixed
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107
public import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma35
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.Open.SplitBNPair
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
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B2FactorizationResidual
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.H13.StatementsL1
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch10StatementsInputs
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.RankThree.PartTwo.Sec20.OneSteps
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.StandardType.ClassicalPosition

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos
open Matrix

private lemma bmPSL_blockDegree_eq_one {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {A : Subalgebra F (Matrix ι ι F)} {e : Matrix ι ι F} (he : IsPrimIdemIn A e)
    (hdeg : blockDegree A e < 2) : blockDegree A e = 1 := by
  let M : Submodule F (Matrix ι ι F) :=
    (Subalgebra.toSubmodule A).map (LinearMap.mulRight F e)
  have heM : e ∈ M :=
    ⟨1, by simpa using A.one_mem, by rw [LinearMap.mulRight_apply, one_mul]⟩
  have hne : (⟨e, heM⟩ : M) ≠ 0 := by
    intro h
    exact he.2.2.1 (by simpa using congrArg Subtype.val h)
  haveI : Nontrivial M := ⟨⟨⟨e, heM⟩, 0, hne⟩⟩
  have hpos : 0 < Module.finrank F M := Module.finrank_pos_iff.mpr inferInstance
  have hlt : Module.finrank F M < 2 := hdeg
  change Module.finrank F M = 1
  omega

private lemma bmPSL_mul_e_eq_smul {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {A : Subalgebra F (Matrix ι ι F)} {e : Matrix ι ι F} (he : IsPrimIdemIn A e)
    (hdeg : blockDegree A e < 2) :
    ∀ a ∈ A, ∃ c : F, a * e = c • e := by
  have hdeg1 : blockDegree A e = 1 := bmPSL_blockDegree_eq_one he hdeg
  let M : Submodule F (Matrix ι ι F) :=
    (Subalgebra.toSubmodule A).map (LinearMap.mulRight F e)
  have hfin : Module.finrank F M = 1 := hdeg1
  have heM : e ∈ M :=
    ⟨1, by simpa using A.one_mem, by rw [LinearMap.mulRight_apply, one_mul]⟩
  have hspan : M = F ∙ e :=
    eq_span_singleton_of_mem_of_finrank_eq_one hfin heM he.2.2.1
  intro a ha
  have hae : a * e ∈ M :=
    ⟨a, ha, by rw [LinearMap.mulRight_apply]⟩
  rw [hspan] at hae
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hae
  exact ⟨c, hc.symm⟩

private lemma bmPSL_commute_of_mem_adjoin {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {S : Set (GL ι F)} (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') {s : GL ι F} (hs : s ∈ S)
    {a : Matrix ι ι F} (ha : a ∈ Algebra.adjoin F (Units.val '' S)) :
    (s : Matrix ι ι F) * a = a * (s : Matrix ι ι F) := by
  have h : Commute (s : Matrix ι ι F) a :=
    Algebra.commute_of_mem_adjoin_of_forall_mem_commute ha (by
      rintro b ⟨s', hs', rfl⟩
      exact congrArg (fun u : GL ι F => (u : Matrix ι ι F)) (hS s hs s' hs'))
  exact h.eq

private lemma bmPSL_toMatrix_reindex {ι ι' V F : Type} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι'] [Field F] [AddCommGroup V] [Module F V]
    (b : Module.Basis ι F V) (e : ι ≃ ι') (f : V →ₗ[F] V) :
    LinearMap.toMatrix (b.reindex e) (b.reindex e) f =
      Matrix.reindex e e (LinearMap.toMatrix b b f) := by
  ext i j
  simp [LinearMap.toMatrix_apply, Module.Basis.repr_reindex, Matrix.reindex_apply]

private lemma bmPSL_toLin_mul_self {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {e : Matrix ι ι F} (he : IsIdempotentElem e) :
    Matrix.toLin' e * Matrix.toLin' e = Matrix.toLin' e := by
  change Matrix.toLin' e ∘ₗ Matrix.toLin' e = Matrix.toLin' e
  rw [← Matrix.toLin'_mul, he.eq]

lemma bmPSL_exists_conj_diag {m : ℕ} {F : Type} [Field F]
    {e : Matrix (Fin (m + 1)) (Fin (m + 1)) F} (he : IsIdempotentElem e) :
    ∃ (r r' : ℕ) (eidx : Fin r ⊕ Fin r' ≃ Fin (m + 1))
      (P Pinv : Matrix (Fin (m + 1)) (Fin (m + 1)) F),
      P * Pinv = 1 ∧ Pinv * P = 1 ∧
      Pinv * Matrix.reindex eidx eidx
        (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) F)
          (0 : Matrix (Fin r) (Fin r') F) (0 : Matrix (Fin r') (Fin r) F)
          (0 : Matrix (Fin r') (Fin r') F)) * P = e ∧
      r = Module.finrank F (LinearMap.range (Matrix.toLin' e)) ∧
      r' = (m + 1) - r ∧ (e ≠ 0 → 0 < r) := by
  classical
  let V : Type := Fin (m + 1) → F
  let E : V →ₗ[F] V := Matrix.toLin' e
  have hE : E * E = E := bmPSL_toLin_mul_self he
  let p : Submodule F V := LinearMap.range E
  let q : Submodule F V := LinearMap.ker E
  have hpq : IsCompl p q := LinearMap.IsIdempotentElem.isCompl hE
  let r : ℕ := Module.finrank F p
  let r' : ℕ := (m + 1) - r
  have hfin : Module.finrank F p + Module.finrank F q = m + 1 := by
    have h := LinearMap.finrank_range_add_finrank_ker E
    have hV : Module.finrank F V = m + 1 := by simp [V]
    change Module.finrank F p + Module.finrank F q = Module.finrank F V at h
    rw [hV] at h
    exact h
  have hdim : Module.finrank F q = r' := by
    dsimp [r, r']
    omega
  let bp : Module.Basis (Fin r) F p := Module.finBasis F p
  let bq : Module.Basis (Fin r') F q := Module.finBasisOfFinrankEq (R := F) (M := q) hdim
  let bprod : Module.Basis (Fin r ⊕ Fin r') F (p × q) := bp.prod bq
  let bV : Module.Basis (Fin r ⊕ Fin r') F V :=
    bprod.map (Submodule.prodEquivOfIsCompl p q hpq)
  have hsum : r + r' = m + 1 := by
    dsimp [r, r']
    omega
  let eidx : Fin r ⊕ Fin r' ≃ Fin (m + 1) :=
    finSumFinEquiv.trans (finCongr hsum)
  let D0 : Matrix (Fin r ⊕ Fin r') (Fin r ⊕ Fin r') F := Matrix.fromBlocks 1 0 0 0
  let b0 : Module.Basis (Fin (m + 1)) F V := Pi.basisFun F (Fin (m + 1))
  let bFin : Module.Basis (Fin (m + 1)) F V := bV.reindex eidx
  have hbFin : bFin = bV.reindex eidx := rfl
  let P : Matrix (Fin (m + 1)) (Fin (m + 1)) F := bFin.toMatrix b0
  let Pinv : Matrix (Fin (m + 1)) (Fin (m + 1)) F := b0.toMatrix bFin
  have hPP : P * Pinv = 1 := Module.Basis.toMatrix_mul_toMatrix_flip bFin b0
  have hPinvP : Pinv * P = 1 := Module.Basis.toMatrix_mul_toMatrix_flip b0 bFin
  have hbV_inl : ∀ a : Fin r, bV (Sum.inl a) = (bp a : V) := by
    intro a
    simp [bV, bprod, Module.Basis.map_apply, Module.Basis.prod_apply,
      Submodule.coe_prodEquivOfIsCompl]
  have hbV_inr : ∀ b : Fin r', bV (Sum.inr b) = (bq b : V) := by
    intro b
    simp [bV, bprod, Module.Basis.map_apply, Module.Basis.prod_apply,
      Submodule.coe_prodEquivOfIsCompl]
  have hE_range : ∀ x ∈ p, E x = x :=
    fun x hx => (LinearMap.IsIdempotentElem.mem_range_iff hE).mp hx
  have hE_ker : ∀ x ∈ q, E x = 0 := fun x hx => (LinearMap.mem_ker).mp hx
  have hD : LinearMap.toMatrix bV bV E = D0 := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · rw [LinearMap.toMatrix_apply]
      rw [show E (bV (Sum.inl j)) = bV (Sum.inl j) by
        rw [hbV_inl]; exact hE_range (bp j) (bp j).2]
      rw [Module.Basis.repr_self_apply]
      by_cases h : i = j
      · subst h; simp [D0, Matrix.fromBlocks, Matrix.of_apply, Matrix.one_apply]
      · have hji : j ≠ i := fun hh => h hh.symm
        simp [h, hji, D0, Matrix.fromBlocks, Matrix.of_apply, Matrix.one_apply]
    · rw [LinearMap.toMatrix_apply]
      rw [show E (bV (Sum.inr j)) = 0 by
        rw [hbV_inr]; exact hE_ker (bq j) (bq j).2]
      simp [D0, Matrix.fromBlocks, Matrix.of_apply]
    · rw [LinearMap.toMatrix_apply]
      rw [show E (bV (Sum.inl j)) = bV (Sum.inl j) by
        rw [hbV_inl]; exact hE_range (bp j) (bp j).2]
      rw [Module.Basis.repr_self]
      simp [D0, Matrix.fromBlocks, Matrix.of_apply]
    · rw [LinearMap.toMatrix_apply]
      rw [show E (bV (Sum.inr j)) = 0 by
        rw [hbV_inr]; exact hE_ker (bq j) (bq j).2]
      simp [D0, Matrix.fromBlocks, Matrix.of_apply]
  have hDfin : LinearMap.toMatrix bFin bFin E =
      Matrix.reindex eidx eidx
        (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) F)
          (0 : Matrix (Fin r) (Fin r') F) (0 : Matrix (Fin r') (Fin r) F)
          (0 : Matrix (Fin r') (Fin r') F)) := by
    simpa [hbFin, hD, D0] using bmPSL_toMatrix_reindex bV eidx E
  have hmatE : LinearMap.toMatrix b0 b0 E = e := by
    have h : Matrix.toLin b0 b0 e = E := by
      dsimp [E]
      rw [Matrix.toLin_eq_toLin']
    rw [← h]
    exact LinearMap.toMatrix_toLin b0 b0 e
  have hcb := basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix b0 bFin b0 bFin E
  rw [hDfin, hmatE] at hcb
  refine ⟨r, r', eidx, P, Pinv, hPP, hPinvP, ?_, rfl, rfl, ?_⟩
  · simpa [P, Pinv] using hcb
  · intro he0
    by_contra hpos
    have hr0 : r = 0 := Nat.eq_zero_of_not_pos hpos
    have hpbot : p = ⊥ := by
      rw [← Submodule.finrank_eq_zero]
      simpa [r] using hr0
    have hE0 : E = 0 := by
      rw [← LinearMap.range_eq_bot, ← hpbot]
    have heq : e = 0 := by
      ext i j
      have h := congrFun (congrArg (fun f : V →ₗ[F] V => f (Pi.single j 1)) hE0) i
      rw [Matrix.toLin'_apply, Matrix.mulVec_single_one] at h
      rw [LinearMap.zero_apply, Pi.zero_apply] at h
      simpa [Matrix.col_apply] using h
    exact he0 heq

private lemma bmPSL_block_diag_mul {r r' : ℕ} {F : Type} [Field F]
    {A : Matrix (Fin r ⊕ Fin r') (Fin r ⊕ Fin r') F}
    (h : A * Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) F)
        (0 : Matrix (Fin r) (Fin r') F) (0 : Matrix (Fin r') (Fin r) F)
        (0 : Matrix (Fin r') (Fin r') F) =
      Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) F)
        (0 : Matrix (Fin r) (Fin r') F) (0 : Matrix (Fin r') (Fin r) F)
        (0 : Matrix (Fin r') (Fin r') F) * A) :
    ∃ x : Matrix (Fin r) (Fin r) F, ∃ y : Matrix (Fin r') (Fin r') F,
      A = Matrix.fromBlocks x 0 0 y := by
  let x : Matrix (Fin r) (Fin r) F := A.toBlocks₁₁
  let y : Matrix (Fin r') (Fin r') F := A.toBlocks₂₂
  refine ⟨x, y, ?_⟩
  have h' := h
  rw [← Matrix.fromBlocks_toBlocks A] at h'
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply] at h'
  simp only [mul_zero, add_zero, zero_mul, zero_add, one_mul] at h'
  rw [Matrix.fromBlocks_inj] at h'
  obtain ⟨-, h12, h21, -⟩ := h'
  have h12' : A.toBlocks₁₂ = 0 := by simpa using h12.symm
  have h21' : A.toBlocks₂₁ = 0 := by simpa using h21
  nth_rewrite 1 [← Matrix.fromBlocks_toBlocks A]
  rw [h12', h21']

private lemma bmPSL_block_diag {m r r' : ℕ} {F : Type} [Field F]
    {e D : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    {P Pinv : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    (eidx : Fin r ⊕ Fin r' ≃ Fin (m + 1))
    (hPP : P * Pinv = 1) (hPinvP : Pinv * P = 1)
    (hconv : Pinv * D * P = e)
    (hD : D = Matrix.reindex eidx eidx
      (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) F)
        (0 : Matrix (Fin r) (Fin r') F) (0 : Matrix (Fin r') (Fin r) F)
        (0 : Matrix (Fin r') (Fin r') F)))
    {g : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    (hgcomm : g * e = e * g)
    (hgfix : g * (1 - e) = 1 - e) :
    ∃ x : Matrix (Fin r) (Fin r) F, ∃ y : Matrix (Fin r') (Fin r') F,
      P * g * Pinv = Matrix.reindex eidx eidx (Matrix.fromBlocks x 0 0 y) ∧ y = 1 := by
  classical
  let D0 : Matrix (Fin r ⊕ Fin r') (Fin r ⊕ Fin r') F :=
    Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) F)
      (0 : Matrix (Fin r) (Fin r') F) (0 : Matrix (Fin r') (Fin r) F)
      (0 : Matrix (Fin r') (Fin r') F)
  let Dfin : Matrix (Fin (m + 1)) (Fin (m + 1)) F := Matrix.reindex eidx eidx D0
  have hD' : D = Dfin := hD
  have hDe : D = P * e * Pinv := by
    have h := congrArg (fun X : Matrix (Fin (m + 1)) (Fin (m + 1)) F =>
      P * X * Pinv) hconv
    calc D = (P * Pinv) * D * (P * Pinv) := by rw [hPP]; simp
      _ = P * (Pinv * D * P) * Pinv := by noncomm_ring
      _ = P * e * Pinv := h
  have hcomm : (P * g * Pinv) * D = D * (P * g * Pinv) := by
    rw [hDe]
    calc (P * g * Pinv) * (P * e * Pinv)
        = P * g * (Pinv * P) * e * Pinv := by noncomm_ring
      _ = P * g * e * Pinv := by rw [hPinvP]; noncomm_ring
      _ = P * (g * e) * Pinv := by noncomm_ring
      _ = P * (e * g) * Pinv := by rw [hgcomm]
      _ = P * e * (Pinv * P) * g * Pinv := by rw [hPinvP]; noncomm_ring
      _ = P * e * Pinv * (P * g * Pinv) := by noncomm_ring
  let h : Matrix (Fin (m + 1)) (Fin (m + 1)) F := P * g * Pinv
  let hα : Matrix (Fin r ⊕ Fin r') (Fin r ⊕ Fin r') F :=
    Matrix.reindex eidx.symm eidx.symm h
  have hcommα : hα * D0 = D0 * hα := by
    have h' := congrArg (Matrix.reindexAlgEquiv F F eidx.symm) hcomm
    simp only [map_mul] at h'
    simpa [hα, h, D0, Dfin, hD', Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply,
      Equiv.symm_apply_apply, Equiv.apply_symm_apply] using h'
  obtain ⟨x, y, hxy⟩ := bmPSL_block_diag_mul hcommα
  have hblock : h = Matrix.reindex eidx eidx (Matrix.fromBlocks x 0 0 y) := by
    have h' := congrArg (Matrix.reindex eidx eidx) hxy
    simpa [hα, h, D0] using h'
  have hone : (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F) - e =
      Pinv * (1 - Dfin) * P := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, ← hD', hconv, hPinvP]
  have hfix : h * (1 - Dfin) = 1 - Dfin := by
    let X : Matrix (Fin (m + 1)) (Fin (m + 1)) F := 1 - Dfin
    have hX : X = 1 - Dfin := rfl
    have honeX : 1 - e = Pinv * X * P := by rw [hX]; exact hone
    have hfixX : h * X = X := by
      calc h * X = P * g * Pinv * X := rfl
        _ = P * g * Pinv * X * (P * Pinv) := by rw [hPP]; simp
        _ = P * g * (Pinv * X * P) * Pinv := by noncomm_ring
        _ = P * g * (1 - e) * Pinv := by rw [← honeX]
        _ = P * (g * (1 - e)) * Pinv := by simp only [Matrix.mul_assoc]
        _ = P * (1 - e) * Pinv := by rw [hgfix]
        _ = P * (Pinv * X * P) * Pinv := by rw [honeX]
        _ = (P * Pinv) * X * (P * Pinv) := by noncomm_ring
        _ = X := by rw [hPP]; simp
    simpa [hX] using hfixX
  have h1D : (1 : Matrix (Fin r ⊕ Fin r') (Fin r ⊕ Fin r') F) - D0 =
      Matrix.fromBlocks (0 : Matrix (Fin r) (Fin r) F)
        (0 : Matrix (Fin r) (Fin r') F) (0 : Matrix (Fin r') (Fin r) F)
        (1 : Matrix (Fin r') (Fin r') F) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [D0, Matrix.fromBlocks, Matrix.of_apply, Matrix.one_apply, sub_eq_zero]
  have hy : y = 1 := by
    have hfixα : hα * (1 - D0) = 1 - D0 := by
      have h' := congrArg (Matrix.reindexAlgEquiv F F eidx.symm) hfix
      rw [map_mul, map_sub, map_one] at h'
      simpa [hα, h, D0, Dfin, hD', Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply,
        Equiv.symm_apply_apply, Equiv.apply_symm_apply] using h'
    rw [hxy, h1D, Matrix.fromBlocks_multiply] at hfixα
    simp only [mul_zero, add_zero, zero_mul, zero_add, one_mul, mul_one] at hfixα
    rw [Matrix.fromBlocks_inj] at hfixα
    simpa using hfixα.2.2.2
  exact ⟨x, y, hblock, hy⟩

lemma bmPSL_det_reindex_self {α β F : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] [CommRing F] (e : α ≃ β) (A : Matrix α α F) :
    (Matrix.reindex e e A).det = A.det := by
  rw [Matrix.det_reindex]
  simp

@[expose] noncomputable def bmPSL_embedMat {m r r' : ℕ} {F : Type} [Field F]
    (eidx : Fin r ⊕ Fin r' ≃ Fin (m + 1))
    (P Pinv : Matrix (Fin (m + 1)) (Fin (m + 1)) F)
    (x : Matrix (Fin r) (Fin r) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F :=
  Pinv * Matrix.reindex eidx eidx
    (Matrix.fromBlocks x (0 : Matrix (Fin r) (Fin r') F)
      (0 : Matrix (Fin r') (Fin r) F) (1 : Matrix (Fin r') (Fin r') F)) * P

lemma bmPSL_block_diag_comm {m r r' : ℕ} {F : Type} [Field F]
    {e D : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    {P Pinv : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    (eidx : Fin r ⊕ Fin r' ≃ Fin (m + 1))
    (hPP : P * Pinv = 1) (hPinvP : Pinv * P = 1)
    (hconv : Pinv * D * P = e)
    (hD : D = Matrix.reindex eidx eidx
      (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) F)
        (0 : Matrix (Fin r) (Fin r') F) (0 : Matrix (Fin r') (Fin r) F)
        (0 : Matrix (Fin r') (Fin r') F)))
    {g : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    (hgcomm : g * e = e * g) :
    ∃ x : Matrix (Fin r) (Fin r) F, ∃ y : Matrix (Fin r') (Fin r') F,
      P * g * Pinv = Matrix.reindex eidx eidx (Matrix.fromBlocks x 0 0 y) := by
  classical
  let D0 : Matrix (Fin r ⊕ Fin r') (Fin r ⊕ Fin r') F :=
    Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) F)
      (0 : Matrix (Fin r) (Fin r') F) (0 : Matrix (Fin r') (Fin r) F)
      (0 : Matrix (Fin r') (Fin r') F)
  let Dfin : Matrix (Fin (m + 1)) (Fin (m + 1)) F := Matrix.reindex eidx eidx D0
  have hD' : D = Dfin := hD
  have hDe : D = P * e * Pinv := by
    have h := congrArg (fun X : Matrix (Fin (m + 1)) (Fin (m + 1)) F =>
      P * X * Pinv) hconv
    calc D = (P * Pinv) * D * (P * Pinv) := by rw [hPP]; simp
      _ = P * (Pinv * D * P) * Pinv := by noncomm_ring
      _ = P * e * Pinv := h
  have hcomm : (P * g * Pinv) * D = D * (P * g * Pinv) := by
    rw [hDe]
    calc (P * g * Pinv) * (P * e * Pinv)
        = P * g * (Pinv * P) * e * Pinv := by noncomm_ring
      _ = P * g * e * Pinv := by rw [hPinvP]; noncomm_ring
      _ = P * (g * e) * Pinv := by noncomm_ring
      _ = P * (e * g) * Pinv := by rw [hgcomm]
      _ = P * e * (Pinv * P) * g * Pinv := by rw [hPinvP]; noncomm_ring
      _ = P * e * Pinv * (P * g * Pinv) := by noncomm_ring
  let h : Matrix (Fin (m + 1)) (Fin (m + 1)) F := P * g * Pinv
  let hα : Matrix (Fin r ⊕ Fin r') (Fin r ⊕ Fin r') F :=
    Matrix.reindex eidx.symm eidx.symm h
  have hcommα : hα * D0 = D0 * hα := by
    have h' := congrArg (Matrix.reindexAlgEquiv F F eidx.symm) hcomm
    simp only [map_mul] at h'
    simpa [hα, h, D0, Dfin, hD', Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply,
      Equiv.symm_apply_apply, Equiv.apply_symm_apply] using h'
  obtain ⟨x, y, hxy⟩ := bmPSL_block_diag_mul hcommα
  have hblock : h = Matrix.reindex eidx eidx (Matrix.fromBlocks x 0 0 y) := by
    have h' := congrArg (Matrix.reindex eidx eidx) hxy
    simpa [hα, h, D0] using h'
  exact ⟨x, y, hblock⟩

private lemma bmPSL_embedMat_one {m r r' : ℕ} {F : Type} [Field F]
    {eidx : Fin r ⊕ Fin r' ≃ Fin (m + 1)}
    {P Pinv : Matrix (Fin (m + 1)) (Fin (m + 1)) F} (hPinvP : Pinv * P = 1) :
    bmPSL_embedMat eidx P Pinv (1 : Matrix (Fin r) (Fin r) F) = 1 := by
  unfold bmPSL_embedMat
  rw [Matrix.fromBlocks_one]
  change Pinv * (Matrix.reindexAlgEquiv F F eidx) 1 * P = 1
  rw [map_one, Matrix.mul_one, hPinvP]

private lemma bmPSL_embedMat_mul {m r r' : ℕ} {F : Type} [Field F]
    {eidx : Fin r ⊕ Fin r' ≃ Fin (m + 1)}
    {P Pinv : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    (hPP : P * Pinv = 1) (x y : Matrix (Fin r) (Fin r) F) :
    bmPSL_embedMat eidx P Pinv (x * y) =
      bmPSL_embedMat eidx P Pinv x * bmPSL_embedMat eidx P Pinv y := by
  have hblock : Matrix.fromBlocks (x * y) (0 : Matrix (Fin r) (Fin r') F)
      (0 : Matrix (Fin r') (Fin r) F) (1 : Matrix (Fin r') (Fin r') F) =
      Matrix.fromBlocks x (0 : Matrix (Fin r) (Fin r') F)
        (0 : Matrix (Fin r') (Fin r) F) (1 : Matrix (Fin r') (Fin r') F) *
      Matrix.fromBlocks y (0 : Matrix (Fin r) (Fin r') F)
        (0 : Matrix (Fin r') (Fin r) F) (1 : Matrix (Fin r') (Fin r') F) := by
    rw [Matrix.fromBlocks_multiply]
    simp
  unfold bmPSL_embedMat
  rw [hblock]
  change Pinv * (Matrix.reindexAlgEquiv F F eidx)
      (Matrix.fromBlocks x 0 0 1 * Matrix.fromBlocks y 0 0 1) * P =
    (Pinv * (Matrix.reindexAlgEquiv F F eidx) (Matrix.fromBlocks x 0 0 1) * P) *
      (Pinv * (Matrix.reindexAlgEquiv F F eidx) (Matrix.fromBlocks y 0 0 1) * P)
  rw [map_mul]
  calc Pinv * ((Matrix.reindexAlgEquiv F F eidx) (Matrix.fromBlocks x 0 0 1) *
        (Matrix.reindexAlgEquiv F F eidx) (Matrix.fromBlocks y 0 0 1)) * P
      = (Pinv * (Matrix.reindexAlgEquiv F F eidx) (Matrix.fromBlocks x 0 0 1)) *
          (P * Pinv) *
          ((Matrix.reindexAlgEquiv F F eidx) (Matrix.fromBlocks y 0 0 1) * P) := by
        rw [hPP]; noncomm_ring
    _ = (Pinv * (Matrix.reindexAlgEquiv F F eidx) (Matrix.fromBlocks x 0 0 1) * P) *
          (Pinv * (Matrix.reindexAlgEquiv F F eidx) (Matrix.fromBlocks y 0 0 1) * P) := by
        noncomm_ring

private lemma bmPSL_embedMat_det {m r r' : ℕ} {F : Type} [Field F]
    {eidx : Fin r ⊕ Fin r' ≃ Fin (m + 1)}
    {P Pinv : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    (hPP : P * Pinv = 1) (x : Matrix (Fin r) (Fin r) F) :
    (bmPSL_embedMat eidx P Pinv x).det = x.det := by
  unfold bmPSL_embedMat
  rw [Matrix.det_mul, Matrix.det_mul]
  rw [bmPSL_det_reindex_self]
  rw [Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, mul_one]
  have hdet : P.det * Pinv.det = 1 := by
    rw [← Matrix.det_mul, hPP, Matrix.det_one]
  calc Pinv.det * x.det * P.det = x.det * (P.det * Pinv.det) := by ring
    _ = x.det := by rw [hdet, mul_one]

@[expose] noncomputable def bmPSL_embedHom {m r r' : ℕ} {F : Type} [Field F]
    (eidx : Fin r ⊕ Fin r' ≃ Fin (m + 1))
    (P Pinv : Matrix (Fin (m + 1)) (Fin (m + 1)) F)
    (hPP : P * Pinv = 1) (hPinvP : Pinv * P = 1) :
    Matrix.SpecialLinearGroup (Fin r) F →*
      Matrix.SpecialLinearGroup (Fin (m + 1)) F where
  toFun x :=
    ⟨bmPSL_embedMat eidx P Pinv (x : Matrix (Fin r) (Fin r) F), by
      rw [bmPSL_embedMat_det hPP]
      exact x.2⟩
  map_one' := by
    apply Subtype.ext
    exact bmPSL_embedMat_one hPinvP
  map_mul' x y := by
    apply Subtype.ext
    exact bmPSL_embedMat_mul hPP (x : Matrix (Fin r) (Fin r) F)
      (y : Matrix (Fin r) (Fin r) F)

private lemma bmPSL_embedHom_coe {m r r' : ℕ} {F : Type} [Field F]
    {eidx : Fin r ⊕ Fin r' ≃ Fin (m + 1)}
    {P Pinv : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    {hPP : P * Pinv = 1} {hPinvP : Pinv * P = 1}
    (x : Matrix.SpecialLinearGroup (Fin r) F) :
    ((bmPSL_embedHom eidx P Pinv hPP hPinvP x :
      Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      bmPSL_embedMat eidx P Pinv (x : Matrix (Fin r) (Fin r) F) := rfl

private lemma bmPSL_one_sub {m r r' : ℕ} {F : Type} [Field F]
    {e D : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    {P Pinv : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    (eidx : Fin r ⊕ Fin r' ≃ Fin (m + 1))
    (hconv : Pinv * D * P = e) (hPinvP : Pinv * P = 1)
    (_hD : D = Matrix.reindex eidx eidx
      (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) F)
        (0 : Matrix (Fin r) (Fin r') F) (0 : Matrix (Fin r') (Fin r) F)
        (0 : Matrix (Fin r') (Fin r') F))) :
    (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F) - e = Pinv * (1 - D) * P := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hconv, hPinvP]

private lemma bmPSL_Dx_mul_one_sub {r r' : ℕ} {F : Type} [Field F]
    (x : Matrix (Fin r) (Fin r) F) :
    Matrix.fromBlocks x (0 : Matrix (Fin r) (Fin r') F)
        (0 : Matrix (Fin r') (Fin r) F) (1 : Matrix (Fin r') (Fin r') F) *
      (1 - Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) F)
        (0 : Matrix (Fin r) (Fin r') F) (0 : Matrix (Fin r') (Fin r) F)
        (0 : Matrix (Fin r') (Fin r') F)) =
      1 - Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) F)
        (0 : Matrix (Fin r) (Fin r') F) (0 : Matrix (Fin r') (Fin r) F)
        (0 : Matrix (Fin r') (Fin r') F) := by
  have h1D : (1 : Matrix (Fin r ⊕ Fin r') (Fin r ⊕ Fin r') F) -
      Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) F)
        (0 : Matrix (Fin r) (Fin r') F) (0 : Matrix (Fin r') (Fin r) F)
        (0 : Matrix (Fin r') (Fin r') F) =
      Matrix.fromBlocks (0 : Matrix (Fin r) (Fin r) F)
        (0 : Matrix (Fin r) (Fin r') F) (0 : Matrix (Fin r') (Fin r) F)
        (1 : Matrix (Fin r') (Fin r') F) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Matrix.fromBlocks, Matrix.of_apply, Matrix.one_apply, sub_eq_zero]
  rw [h1D, Matrix.fromBlocks_multiply]
  simp

private lemma bmPSL_scalar_mul_D0 {r r' : ℕ} {F : Type} [Field F]
    {a : Matrix (Fin r) (Fin r) F} {b : Matrix (Fin r') (Fin r') F} {c : F}
    (h : Matrix.fromBlocks a (0 : Matrix (Fin r) (Fin r') F)
        (0 : Matrix (Fin r') (Fin r) F) b *
      Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) F)
        (0 : Matrix (Fin r) (Fin r') F) (0 : Matrix (Fin r') (Fin r) F)
        (0 : Matrix (Fin r') (Fin r') F) =
      c • Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) F)
        (0 : Matrix (Fin r) (Fin r') F) (0 : Matrix (Fin r') (Fin r) F)
        (0 : Matrix (Fin r') (Fin r') F)) :
    a = c • (1 : Matrix (Fin r) (Fin r) F) := by
  have h' := h
  rw [Matrix.fromBlocks_multiply] at h'
  simp only [mul_zero, add_zero, zero_mul, zero_add, one_mul, mul_one] at h'
  have hR : c • Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) F)
      (0 : Matrix (Fin r) (Fin r') F) (0 : Matrix (Fin r') (Fin r) F)
      (0 : Matrix (Fin r') (Fin r') F) =
      Matrix.fromBlocks (c • (1 : Matrix (Fin r) (Fin r) F))
        (0 : Matrix (Fin r) (Fin r') F) (0 : Matrix (Fin r') (Fin r) F)
        (0 : Matrix (Fin r') (Fin r') F) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Matrix.fromBlocks, Matrix.smul_apply]
  rw [hR, Matrix.fromBlocks_inj] at h'
  simpa using h'.1

private lemma bmPSL_embedMat_centralizes {m r r' : ℕ} {F : Type} [Field F]
    {S : Set (GL (Fin (m + 1)) F)}
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    (hdeg : blockDegree (Algebra.adjoin F (Units.val '' S)) e < 2)
    {eidx : Fin r ⊕ Fin r' ≃ Fin (m + 1)}
    {P Pinv : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    (hPP : P * Pinv = 1) (hPinvP : Pinv * P = 1)
    {D : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    (hconv : Pinv * D * P = e)
    (hD : D = Matrix.reindex eidx eidx
      (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) F)
        (0 : Matrix (Fin r) (Fin r') F) (0 : Matrix (Fin r') (Fin r) F)
        (0 : Matrix (Fin r') (Fin r') F)))
    {s : GL (Fin (m + 1)) F} (hs : s ∈ S)
    (x : Matrix (Fin r) (Fin r) F) :
    (s : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
        bmPSL_embedMat eidx P Pinv x =
      bmPSL_embedMat eidx P Pinv x * (s : Matrix (Fin (m + 1)) (Fin (m + 1)) F) := by
  classical
  let D0 : Matrix (Fin r ⊕ Fin r') (Fin r ⊕ Fin r') F :=
    Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) F)
      (0 : Matrix (Fin r) (Fin r') F) (0 : Matrix (Fin r') (Fin r) F)
      (0 : Matrix (Fin r') (Fin r') F)
  let Dfin : Matrix (Fin (m + 1)) (Fin (m + 1)) F := Matrix.reindex eidx eidx D0
  let Dx : Matrix (Fin (m + 1)) (Fin (m + 1)) F :=
    Matrix.reindex eidx eidx (Matrix.fromBlocks x (0 : Matrix (Fin r) (Fin r') F)
      (0 : Matrix (Fin r') (Fin r) F) (1 : Matrix (Fin r') (Fin r') F))
  have hD' : D = Dfin := hD
  have hsA : (s : Matrix (Fin (m + 1)) (Fin (m + 1)) F) ∈
      Algebra.adjoin F (Units.val '' S) :=
    Algebra.subset_adjoin (Set.mem_image_of_mem Units.val hs)
  have hse : (s : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * e =
      e * (s : Matrix (Fin (m + 1)) (Fin (m + 1)) F) :=
    bmPSL_commute_of_mem_adjoin hS hs he.1
  obtain ⟨c, hc⟩ := bmPSL_mul_e_eq_smul he hdeg
    (s : Matrix (Fin (m + 1)) (Fin (m + 1)) F) hsA
  obtain ⟨a, b, hblock_s⟩ := bmPSL_block_diag_comm eidx hPP hPinvP hconv hD hse
  let Hs : Matrix (Fin (m + 1)) (Fin (m + 1)) F :=
    P * (s : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * Pinv
  have hDfin_e : Dfin = P * e * Pinv := by
    have h := congrArg (fun X : Matrix (Fin (m + 1)) (Fin (m + 1)) F =>
      P * X * Pinv) hconv
    calc Dfin = (P * Pinv) * Dfin * (P * Pinv) := by rw [hPP]; simp
      _ = P * (Pinv * Dfin * P) * Pinv := by noncomm_ring
      _ = P * e * Pinv := by rw [← hD']; exact h
  have hHsD : Hs * Dfin = c • Dfin := by
    rw [hDfin_e]
    calc (P * (s : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * Pinv) *
          (P * e * Pinv)
        = P * ((s : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * e) * Pinv := by
          calc (P * (s : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * Pinv) *
                (P * e * Pinv)
              = P * (s : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
                  (Pinv * P) * e * Pinv := by noncomm_ring
            _ = P * ((s : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * e) * Pinv := by
                rw [hPinvP]; noncomm_ring
      _ = P * (c • e) * Pinv := by rw [hc]
      _ = c • (P * e * Pinv) := by rw [Matrix.mul_smul, Matrix.smul_mul]
  let Hsα : Matrix (Fin r ⊕ Fin r') (Fin r ⊕ Fin r') F :=
    Matrix.reindex eidx.symm eidx.symm Hs
  have hHsα : Hsα = Matrix.fromBlocks a (0 : Matrix (Fin r) (Fin r') F)
      (0 : Matrix (Fin r') (Fin r) F) b := by
    have h' := congrArg (Matrix.reindexAlgEquiv F F eidx.symm) hblock_s
    simp only [map_mul] at h'
    simpa [Hsα, Hs, D0, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply,
      Equiv.symm_apply_apply, Equiv.apply_symm_apply] using h'
  have hHsαD : Hsα * D0 = c • D0 := by
    have h' := congrArg (Matrix.reindexAlgEquiv F F eidx.symm) hHsD
    simp only [map_mul, map_smul] at h'
    simpa [Hsα, D0, Dfin, hD', Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply,
      Equiv.symm_apply_apply, Equiv.apply_symm_apply] using h'
  have ha : a = c • (1 : Matrix (Fin r) (Fin r) F) := by
    apply bmPSL_scalar_mul_D0 (b := b) (c := c)
    rwa [hHsα] at hHsαD
  let Dxα : Matrix (Fin r ⊕ Fin r') (Fin r ⊕ Fin r') F :=
    Matrix.fromBlocks x (0 : Matrix (Fin r) (Fin r') F)
      (0 : Matrix (Fin r') (Fin r) F) (1 : Matrix (Fin r') (Fin r') F)
  have hcommα : Hsα * Dxα = Dxα * Hsα := by
    rw [hHsα, ha]
    change Matrix.fromBlocks (c • (1 : Matrix (Fin r) (Fin r) F))
        (0 : Matrix (Fin r) (Fin r') F) (0 : Matrix (Fin r') (Fin r) F) b *
      Matrix.fromBlocks x (0 : Matrix (Fin r) (Fin r') F)
        (0 : Matrix (Fin r') (Fin r) F) (1 : Matrix (Fin r') (Fin r') F) =
      Matrix.fromBlocks x (0 : Matrix (Fin r) (Fin r') F)
        (0 : Matrix (Fin r') (Fin r) F) (1 : Matrix (Fin r') (Fin r') F) *
      Matrix.fromBlocks (c • (1 : Matrix (Fin r) (Fin r) F))
        (0 : Matrix (Fin r) (Fin r') F) (0 : Matrix (Fin r') (Fin r) F) b
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [mul_zero, add_zero, zero_mul, zero_add, one_mul, mul_one]
    rw [Matrix.fromBlocks_inj]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one]
    · simp
    · simp
    · simp
  have hcommFin : Hs * Dx = Dx * Hs := by
    have h' := congrArg (Matrix.reindexAlgEquiv F F eidx) hcommα
    simp only [map_mul] at h'
    simpa [Hsα, Dxα, Hs, Dx, D0, Dfin, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply,
      Equiv.symm_apply_apply, Equiv.apply_symm_apply] using h'
  have hs_eq : (s : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = Pinv * Hs * P := by
    calc (s : Matrix (Fin (m + 1)) (Fin (m + 1)) F)
        = (Pinv * P) * (s : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * (Pinv * P) := by
          rw [hPinvP]; simp
      _ = Pinv * (P * (s : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * Pinv) * P := by
          noncomm_ring
  unfold bmPSL_embedMat
  change (s : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * (Pinv * Dx * P) =
    (Pinv * Dx * P) * (s : Matrix (Fin (m + 1)) (Fin (m + 1)) F)
  rw [hs_eq]
  calc (Pinv * Hs * P) * (Pinv * Dx * P)
      = Pinv * Hs * Dx * P := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc P Pinv (Dx * P), hPP, Matrix.one_mul]
    _ = Pinv * Dx * Hs * P := by
        rw [Matrix.mul_assoc Pinv Hs Dx, hcommFin, ← Matrix.mul_assoc Pinv Dx Hs]
    _ = (Pinv * Dx * P) * (Pinv * Hs * P) := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc P Pinv (Hs * P), hPP, Matrix.one_mul]

private lemma bmPSL_embedMat_fix {m r r' : ℕ} {F : Type} [Field F]
    {e D : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    {P Pinv : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    (eidx : Fin r ⊕ Fin r' ≃ Fin (m + 1))
    (hPP : P * Pinv = 1) (hPinvP : Pinv * P = 1)
    (hconv : Pinv * D * P = e)
    (hD : D = Matrix.reindex eidx eidx
      (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) F)
        (0 : Matrix (Fin r) (Fin r') F) (0 : Matrix (Fin r') (Fin r) F)
        (0 : Matrix (Fin r') (Fin r') F)))
    (x : Matrix (Fin r) (Fin r) F) :
    bmPSL_embedMat eidx P Pinv x * (1 - e) = 1 - e := by
  let D0 : Matrix (Fin r ⊕ Fin r') (Fin r ⊕ Fin r') F :=
    Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) F)
      (0 : Matrix (Fin r) (Fin r') F) (0 : Matrix (Fin r') (Fin r) F)
      (0 : Matrix (Fin r') (Fin r') F)
  let Dfin : Matrix (Fin (m + 1)) (Fin (m + 1)) F := Matrix.reindex eidx eidx D0
  have hD' : D = Dfin := hD
  let Dx : Matrix (Fin (m + 1)) (Fin (m + 1)) F :=
    Matrix.reindex eidx eidx (Matrix.fromBlocks x (0 : Matrix (Fin r) (Fin r') F)
      (0 : Matrix (Fin r') (Fin r) F) (1 : Matrix (Fin r') (Fin r') F))
  let X : Matrix (Fin (m + 1)) (Fin (m + 1)) F := 1 - Dfin
  have hDx0 := bmPSL_Dx_mul_one_sub (r := r) (r' := r') x
  have hDx : Dx * X = X := by
    have h' := congrArg (Matrix.reindexAlgEquiv F F eidx) hDx0
    simp only [map_mul, map_sub, map_one] at h'
    simpa [Dx, X, D0, Dfin, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply,
      Equiv.symm_apply_apply, Equiv.apply_symm_apply] using h'
  have hone : (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F) - e = Pinv * X * P := by
    have h := bmPSL_one_sub eidx hconv hPinvP hD'
    simpa [X, Dfin, hD', Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply,
      Equiv.symm_apply_apply, Equiv.apply_symm_apply] using h
  have hfix : (Pinv * Dx * P) * (Pinv * X * P) = Pinv * X * P := by
    calc (Pinv * Dx * P) * (Pinv * X * P)
        = Pinv * Dx * X * P := by
          calc (Pinv * Dx * P) * (Pinv * X * P)
              = (Pinv * Dx) * (P * Pinv) * (X * P) := by noncomm_ring
            _ = Pinv * Dx * X * P := by rw [hPP]; noncomm_ring
      _ = Pinv * X * P := by
          rw [Matrix.mul_assoc Pinv Dx X, hDx]
  unfold bmPSL_embedMat
  rw [hone]
  change (Pinv * Dx * P) * (Pinv * X * P) = Pinv * X * P
  exact hfix

private lemma bmPSL_mem_range_of_block {m r r' : ℕ} {F : Type} [Field F]
    {S : Set (GL (Fin (m + 1)) F)}
    {e : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    {eidx : Fin r ⊕ Fin r' ≃ Fin (m + 1)}
    {P Pinv : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    {hPP : P * Pinv = 1} {hPinvP : Pinv * P = 1}
    {D : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    (hconv : Pinv * D * P = e)
    (hD : D = Matrix.reindex eidx eidx
      (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) F)
        (0 : Matrix (Fin r) (Fin r') F) (0 : Matrix (Fin r') (Fin r) F)
        (0 : Matrix (Fin r') (Fin r') F)))
    {g : Matrix.SpecialLinearGroup (Fin (m + 1)) F}
    (hg : g ∈ glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e) :
    g ∈ (bmPSL_embedHom eidx P Pinv hPP hPinvP).range := by
  rw [glBlockCentralizer, Subgroup.mem_comap, Subgroup.mem_inf] at hg
  obtain ⟨hcent, hfix⟩ := hg
  have hcent' : Commute ((g : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F) e := by
    refine Algebra.commute_of_mem_adjoin_of_forall_mem_commute he.1 ?_
    rintro b ⟨s, hs, rfl⟩
    exact (congrArg (fun u : GL (Fin (m + 1)) F =>
      (u : Matrix (Fin (m + 1)) (Fin (m + 1)) F))
      ((Subgroup.mem_centralizer_iff.mp hcent) s hs)).symm
  have hcomm : ((g : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F) * e =
      e * ((g : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F) := hcent'.eq
  have hfix' : ((g : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F) * (1 - e) = 1 - e := hfix
  obtain ⟨x, y, hblock, hy⟩ := bmPSL_block_diag eidx hPP hPinvP hconv hD hcomm hfix'
  rw [hy] at hblock
  have hg_eq : ((g : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F) = bmPSL_embedMat eidx P Pinv x := by
    calc ((g : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) F)
        = (Pinv * P) * ((g : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
            Matrix (Fin (m + 1)) (Fin (m + 1)) F) * (Pinv * P) := by
          rw [hPinvP]; simp
      _ = Pinv * (P * ((g : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
            Matrix (Fin (m + 1)) (Fin (m + 1)) F) * Pinv) * P := by noncomm_ring
      _ = Pinv * (Matrix.reindex eidx eidx
            (Matrix.fromBlocks x (0 : Matrix (Fin r) (Fin r') F)
              (0 : Matrix (Fin r') (Fin r) F) (1 : Matrix (Fin r') (Fin r') F))) * P := by
          rw [hblock]
      _ = bmPSL_embedMat eidx P Pinv x := by rfl
  have hxdet : x.det = 1 := by
    have hdet := congrArg Matrix.det hblock
    rw [Matrix.det_mul, Matrix.det_mul, bmPSL_det_reindex_self,
      Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, mul_one] at hdet
    have hdetPP : P.det * Pinv.det = 1 := by
      rw [← Matrix.det_mul, hPP, Matrix.det_one]
    rw [← hdet]
    calc P.det * ((g : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) F).det * Pinv.det
        = ((g : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
            Matrix (Fin (m + 1)) (Fin (m + 1)) F).det * (P.det * Pinv.det) := by ring
      _ = 1 := by rw [hdetPP, mul_one, g.2]
  let xg : Matrix.SpecialLinearGroup (Fin r) F := ⟨x, hxdet⟩
  refine ⟨xg, ?_⟩
  apply Subtype.ext
  change ((bmPSL_embedHom eidx P Pinv hPP hPinvP xg :
    Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
    ((g : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F)
  rw [bmPSL_embedHom_coe]
  change bmPSL_embedMat eidx P Pinv x = ((g : Matrix.SpecialLinearGroup
    (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F)
  exact hg_eq.symm

private noncomputable def bmPSL_blockMonoidHom (r r' : ℕ) (F : Type) [Field F] :
    Matrix (Fin r) (Fin r) F →* Matrix (Fin r ⊕ Fin r') (Fin r ⊕ Fin r') F where
  toFun x := Matrix.fromBlocks x (0 : Matrix (Fin r) (Fin r') F)
    (0 : Matrix (Fin r') (Fin r) F) (1 : Matrix (Fin r') (Fin r') F)
  map_one' := by rw [Matrix.fromBlocks_one]
  map_mul' x y := by
    rw [Matrix.fromBlocks_multiply]
    simp

private def bmPSL_liftVec {r r' : ℕ} {F : Type} [Zero F] (w : Fin r → F) :
    Fin r ⊕ Fin r' → F := Sum.elim w (0 : Fin r' → F)

private def bmPSL_reindexVec {m r r' : ℕ} {F : Type}
    (eidx : Fin r ⊕ Fin r' ≃ Fin (m + 1)) (w : Fin r ⊕ Fin r' → F) :
    Fin (m + 1) → F := fun i => w (eidx.symm i)

private lemma bmPSL_block_fromBlocks_transvection {r r' : ℕ} {F : Type} [Field F]
    (u w : Fin r → F) (c : F) :
    Matrix.fromBlocks ((1 + c • Matrix.vecMulVec u w : Matrix (Fin r) (Fin r) F))
        (0 : Matrix (Fin r) (Fin r') F) (0 : Matrix (Fin r') (Fin r) F)
        (1 : Matrix (Fin r') (Fin r') F) =
      (1 + c • Matrix.vecMulVec (bmPSL_liftVec (r' := r') u)
        (bmPSL_liftVec (r' := r') w) :
        Matrix (Fin r ⊕ Fin r') (Fin r ⊕ Fin r') F) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.fromBlocks, bmPSL_liftVec, Matrix.vecMulVec, Matrix.one_apply,
      Matrix.add_apply, Matrix.smul_apply]

private lemma bmPSL_reindex_transvection {m r r' : ℕ} {F : Type} [Field F]
    (eidx : Fin r ⊕ Fin r' ≃ Fin (m + 1)) (u w : Fin r → F) (c : F) :
    Matrix.reindex eidx eidx
      (1 + c • Matrix.vecMulVec (bmPSL_liftVec (r' := r') u)
        (bmPSL_liftVec (r' := r') w) :
        Matrix (Fin r ⊕ Fin r') (Fin r ⊕ Fin r') F) =
      (1 + c • Matrix.vecMulVec
        (bmPSL_reindexVec eidx (bmPSL_liftVec (r' := r') u))
        (bmPSL_reindexVec eidx (bmPSL_liftVec (r' := r') w)) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F) := by
  ext i j
  simp [Matrix.reindex_apply, bmPSL_reindexVec, Matrix.vecMulVec, Matrix.add_apply,
    Matrix.smul_apply, Matrix.one_apply]

private noncomputable def bmPSL_blockGL {m r r' : ℕ} {F : Type} [Field F]
    (eidx : Fin r ⊕ Fin r' ≃ Fin (m + 1)) :
    GL (Fin r) F →* GL (Fin (m + 1)) F :=
  Units.map ((Matrix.reindexAlgEquiv F F eidx).toMonoidHom.comp
    (bmPSL_blockMonoidHom r r' F))

private lemma bmPSL_reindexVec_dot {m r r' : ℕ} {F : Type} [Field F]
    (eidx : Fin r ⊕ Fin r' ≃ Fin (m + 1)) (u w : Fin r → F) :
    bmPSL_reindexVec eidx (bmPSL_liftVec (r' := r') u) ⬝ᵥ
      bmPSL_reindexVec eidx (bmPSL_liftVec (r' := r') w) = u ⬝ᵥ w := by
  simp only [dotProduct, bmPSL_reindexVec]
  rw [Equiv.sum_comp eidx.symm (fun x : Fin r ⊕ Fin r' =>
    bmPSL_liftVec (r' := r') u x * bmPSL_liftVec (r' := r') w x)]
  simp [bmPSL_liftVec]

private lemma bmPSL_dot_conj {n : ℕ} {F : Type} [Field F]
    (P Pinv : Matrix (Fin n) (Fin n) F) (hPP : P * Pinv = 1) (a b : Fin n → F) :
    (b ᵥ* P) ⬝ᵥ (Pinv *ᵥ a) = b ⬝ᵥ a := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hPP, Matrix.vecMul_one]

private noncomputable def bmPSL_embedGL {m r r' : ℕ} {F : Type} [Field F]
    (eidx : Fin r ⊕ Fin r' ≃ Fin (m + 1))
    (P Pinv : Matrix (Fin (m + 1)) (Fin (m + 1)) F)
    (hPP : P * Pinv = 1) (hPinvP : Pinv * P = 1) :
    GL (Fin r) F →* GL (Fin (m + 1)) F :=
  (MulAut.conj (Units.mk Pinv P hPinvP hPP)).toMonoidHom.comp (bmPSL_blockGL eidx)

private lemma bmPSL_embedGL_coe {m r r' : ℕ} {F : Type} [Field F]
    {eidx : Fin r ⊕ Fin r' ≃ Fin (m + 1)}
    {P Pinv : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    {hPP : P * Pinv = 1} {hPinvP : Pinv * P = 1}
    (x : GL (Fin r) F) :
    ((bmPSL_embedGL eidx P Pinv hPP hPinvP x : GL (Fin (m + 1)) F) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      bmPSL_embedMat eidx P Pinv (x : Matrix (Fin r) (Fin r) F) := by
  rfl

private lemma bmPSL_vecMulVec_eq_zero {m n : ℕ} {F : Type} [Field F]
    {a : Fin m → F} {b : Fin n → F} (h : Matrix.vecMulVec a b = 0) : a = 0 ∨ b = 0 := by
  by_cases ha : a = 0
  · exact Or.inl ha
  · right
    have hex : ∃ i, a i ≠ 0 := by
      by_contra h
      push Not at h
      exact ha (funext h)
    obtain ⟨i, hi⟩ := hex
    funext j
    have h' := congrFun (congrFun h i) j
    simpa [Matrix.vecMulVec_apply, hi] using h'

private lemma bmPSL_toBlocks_vecMulVec {r r' : ℕ} {F : Type} [Field F]
    (V Φ : Fin r ⊕ Fin r' → F) :
    Matrix.vecMulVec V Φ =
      Matrix.fromBlocks
        (Matrix.vecMulVec (fun i => V (Sum.inl i)) (fun j => Φ (Sum.inl j)))
        (Matrix.vecMulVec (fun i => V (Sum.inl i)) (fun j => Φ (Sum.inr j)))
        (Matrix.vecMulVec (fun i => V (Sum.inr i)) (fun j => Φ (Sum.inl j)))
        (Matrix.vecMulVec (fun i => V (Sum.inr i)) (fun j => Φ (Sum.inr j))) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> rfl

private def bmPSL_reindexVec' {m r r' : ℕ} {F : Type}
    (eidx : Fin r ⊕ Fin r' ≃ Fin (m + 1)) (w : Fin (m + 1) → F) :
    Fin r ⊕ Fin r' → F := fun i => w (eidx i)

private lemma bmPSL_reindex_vecMulVec {m r r' : ℕ} {F : Type} [Field F]
    (eidx : Fin r ⊕ Fin r' ≃ Fin (m + 1)) (a b : Fin (m + 1) → F) :
    Matrix.reindex eidx.symm eidx.symm (Matrix.vecMulVec a b) =
      Matrix.vecMulVec (bmPSL_reindexVec' eidx a) (bmPSL_reindexVec' eidx b) := by
  ext i j
  simp [Matrix.reindex_apply, Matrix.vecMulVec, bmPSL_reindexVec']

private lemma bmPSL_reindex_symm_reindex {m r r' : ℕ} {F : Type} 
    (eidx : Fin r ⊕ Fin r' ≃ Fin (m + 1))
    (M : Matrix (Fin r ⊕ Fin r') (Fin r ⊕ Fin r') F) :
    Matrix.reindex eidx.symm eidx.symm (Matrix.reindex eidx eidx M) = M := by
  ext i j
  simp [Matrix.reindex_apply]

private lemma bmPSL_exists_vec_dot_eq_one {r : ℕ} {F : Type} [Field F]
    {ψ : Fin r → F} (hψ : ψ ≠ 0) :
    ∃ w' : Fin r → F, ψ ⬝ᵥ w' = 1 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hψ
  refine ⟨(ψ i)⁻¹ • Pi.single i 1, ?_⟩
  rw [dotProduct_smul, smul_eq_mul, dotProduct_single, mul_one, inv_mul_cancel₀ hi]

private lemma bmPSL_exists_dual_pair {r : ℕ} {F : Type} [Field F]
    (w ψ w' : Fin r → F) (hw : w ≠ 0) (hψw : ψ ⬝ᵥ w = 0) (hψw' : ψ ⬝ᵥ w' = 1) :
    ∃ ψ' : Fin r → F, ψ' ⬝ᵥ w = 1 ∧ ψ' ⬝ᵥ w' = 0 := by
  have hw' : w ∉ Submodule.span F {w'} := by
    intro h
    rw [Submodule.mem_span_singleton] at h
    obtain ⟨c, hc⟩ := h
    have hcψ : ψ ⬝ᵥ w = c * (ψ ⬝ᵥ w') := by
      rw [← hc, dotProduct_smul, smul_eq_mul]
    rw [hψw, hψw'] at hcψ
    have hc0 : c = 0 := by simpa using hcψ.symm
    rw [hc0, zero_smul] at hc
    exact hw hc.symm
  obtain ⟨h, hh, hker⟩ :=
    Submodule.exists_le_ker_of_notMem (p := Submodule.span F {w'}) hw'
  have hw'ker : h w' = 0 := hker (Submodule.mem_span_singleton_self w')
  let v : Fin r → F := (dotProductEquiv F (Fin r)).symm h
  have hv : ∀ x, v ⬝ᵥ x = h x := by
    intro x
    change (dotProductEquiv F (Fin r) v) x = h x
    rw [LinearEquiv.apply_symm_apply]
  refine ⟨(h w)⁻¹ • v, ?_, ?_⟩
  · rw [smul_dotProduct, hv, smul_eq_mul, inv_mul_cancel₀ hh]
  · rw [smul_dotProduct, hv, hw'ker, smul_zero]

private lemma bmPSL_transv_le_embedGL_support {m r r' : ℕ} {F : Type} [Field F]
    {eidx : Fin r ⊕ Fin r' ≃ Fin (m + 1)}
    {P Pinv : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    (hPP : P * Pinv = 1) (hPinvP : Pinv * P = 1)
    {v φ : Fin (m + 1) → F} (hv : v ≠ 0) (hφ : φ ≠ 0) (hdot : φ ⬝ᵥ v = 0)
    (hle : matTransvGroup v φ ≤ (bmPSL_embedGL eidx P Pinv hPP hPinvP).range) :
    ∃ w ψ : Fin r → F, w ≠ 0 ∧ ψ ≠ 0 ∧ ψ ⬝ᵥ w = 0 ∧
      v = Pinv *ᵥ bmPSL_reindexVec eidx (bmPSL_liftVec w) ∧
      φ = bmPSL_reindexVec eidx (bmPSL_liftVec ψ) ᵥ* P := by
  let A : Matrix (Fin (m + 1)) (Fin (m + 1)) F := Matrix.vecMulVec v φ
  have hAA : A * A = 0 := by
    rw [show A = Matrix.vecMulVec v φ from rfl, Matrix.vecMulVec_mul]
    rw [show φ ᵥ* Matrix.vecMulVec v φ = (φ ⬝ᵥ v) • φ by
      ext j
      simp [Matrix.vecMul_apply, Matrix.vecMulVec_apply, dotProduct, Finset.mul_sum,
        mul_assoc, mul_comm, mul_left_comm]]
    rw [hdot, zero_smul]
    ext i j
    simp [Matrix.vecMulVec]
  let g : GL (Fin (m + 1)) F :=
    Units.mk (1 + A) (1 - A)
      (by
        calc (1 + A) * (1 - A) = 1 - A * A := by noncomm_ring
          _ = 1 := by rw [hAA]; simp)
      (by
        calc (1 - A) * (1 + A) = 1 - A * A := by noncomm_ring
          _ = 1 := by rw [hAA]; simp)
  have hgA : (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = 1 + A := rfl
  have hg_mem : g ∈ matTransvGroup v φ := by
    refine Subgroup.subset_closure ⟨1, ?_⟩
    rw [hgA]
    simp [A]
  obtain ⟨x, hx⟩ := hle hg_mem
  have hxmat : bmPSL_embedMat eidx P Pinv (x : Matrix (Fin r) (Fin r) F) =
      (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) := by
    have h' := congrArg (fun u : GL (Fin (m + 1)) F =>
      (u : Matrix (Fin (m + 1)) (Fin (m + 1)) F)) hx
    simpa [bmPSL_embedGL_coe] using h'
  have hconj : P * (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * Pinv =
      1 + Matrix.vecMulVec (P *ᵥ v) (φ ᵥ* Pinv) := by
    rw [hgA]
    change P * (1 + Matrix.vecMulVec v φ) * Pinv =
      1 + Matrix.vecMulVec (P *ᵥ v) (φ ᵥ* Pinv)
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_vecMulVec,
      Matrix.vecMulVec_mul, hPP]
  have hP : P * (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * Pinv =
      Matrix.reindex eidx eidx (Matrix.fromBlocks (x : Matrix (Fin r) (Fin r) F)
        (0 : Matrix (Fin r) (Fin r') F) (0 : Matrix (Fin r') (Fin r) F)
        (1 : Matrix (Fin r') (Fin r') F)) := by
    rw [← hxmat]
    unfold bmPSL_embedMat
    calc P * (Pinv * Matrix.reindex eidx eidx
            (Matrix.fromBlocks (x : Matrix (Fin r) (Fin r) F)
              (0 : Matrix (Fin r) (Fin r') F) (0 : Matrix (Fin r') (Fin r) F)
              (1 : Matrix (Fin r') (Fin r') F)) * P) * Pinv
        = (P * Pinv) * Matrix.reindex eidx eidx
            (Matrix.fromBlocks (x : Matrix (Fin r) (Fin r) F)
              (0 : Matrix (Fin r) (Fin r') F) (0 : Matrix (Fin r') (Fin r) F)
              (1 : Matrix (Fin r') (Fin r') F)) * (P * Pinv) := by
            noncomm_ring
      _ = Matrix.reindex eidx eidx (Matrix.fromBlocks (x : Matrix (Fin r) (Fin r) F)
            (0 : Matrix (Fin r) (Fin r') F) (0 : Matrix (Fin r') (Fin r) F)
            (1 : Matrix (Fin r') (Fin r') F)) := by
            rw [hPP]; simp
  let V : Fin r ⊕ Fin r' → F := bmPSL_reindexVec' eidx (P *ᵥ v)
  let Φ : Fin r ⊕ Fin r' → F := bmPSL_reindexVec' eidx (φ ᵥ* Pinv)
  have hsum : 1 + Matrix.vecMulVec V Φ =
      Matrix.fromBlocks (x : Matrix (Fin r) (Fin r) F)
        (0 : Matrix (Fin r) (Fin r') F) (0 : Matrix (Fin r') (Fin r) F)
        (1 : Matrix (Fin r') (Fin r') F) := by
    have h := hconj.symm.trans hP
    have h' := congrArg (Matrix.reindexAlgEquiv F F eidx.symm) h
    simp only [map_add, map_one] at h'
    simp only [Matrix.reindexAlgEquiv_apply] at h'
    rw [bmPSL_reindex_vecMulVec] at h'
    rw [bmPSL_reindex_symm_reindex] at h'
    simpa [V, Φ] using h'
  let V1 : Fin r → F := fun i => V (Sum.inl i)
  let V2 : Fin r' → F := fun i => V (Sum.inr i)
  let Φ1 : Fin r → F := fun j => Φ (Sum.inl j)
  let Φ2 : Fin r' → F := fun j => Φ (Sum.inr j)
  have hVΦ : Matrix.vecMulVec V Φ =
      Matrix.fromBlocks (Matrix.vecMulVec V1 Φ1) (Matrix.vecMulVec V1 Φ2)
        (Matrix.vecMulVec V2 Φ1) (Matrix.vecMulVec V2 Φ2) := by
    simpa [V1, V2, Φ1, Φ2] using bmPSL_toBlocks_vecMulVec V Φ
  have hblock : Matrix.fromBlocks (1 + Matrix.vecMulVec V1 Φ1) (Matrix.vecMulVec V1 Φ2)
        (Matrix.vecMulVec V2 Φ1) (1 + Matrix.vecMulVec V2 Φ2) =
      Matrix.fromBlocks (x : Matrix (Fin r) (Fin r) F)
        (0 : Matrix (Fin r) (Fin r') F) (0 : Matrix (Fin r') (Fin r) F)
        (1 : Matrix (Fin r') (Fin r') F) := by
    rw [← hsum, hVΦ]
    rw [show (1 : Matrix (Fin r ⊕ Fin r') (Fin r ⊕ Fin r') F) =
        Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) F)
          (0 : Matrix (Fin r) (Fin r') F) (0 : Matrix (Fin r') (Fin r) F)
          (1 : Matrix (Fin r') (Fin r') F) from Matrix.fromBlocks_one.symm,
      Matrix.fromBlocks_add]
    simp
  have h12 : Matrix.vecMulVec V1 Φ2 = 0 := (Matrix.fromBlocks_inj.mp hblock).2.1
  have h21 : Matrix.vecMulVec V2 Φ1 = 0 := (Matrix.fromBlocks_inj.mp hblock).2.2.1
  have h22 : Matrix.vecMulVec V2 Φ2 = 0 := by
    have h := (Matrix.fromBlocks_inj.mp hblock).2.2.2
    simpa using h
  have hVne : V ≠ 0 := by
    intro hV0
    apply hv
    have hVeq : bmPSL_reindexVec eidx V = P *ᵥ v := by
      ext i
      simp [V, bmPSL_reindexVec', bmPSL_reindexVec]
    have h : P *ᵥ v = 0 := by
      rw [← hVeq, hV0]
      rfl
    have h' := congrArg (fun w => Pinv *ᵥ w) h
    simpa [Matrix.mulVec_mulVec, hPinvP, Matrix.one_mulVec] using h'
  have hΦne : Φ ≠ 0 := by
    intro hΦ0
    apply hφ
    have hΦeq : bmPSL_reindexVec eidx Φ = φ ᵥ* Pinv := by
      ext i
      simp [Φ, bmPSL_reindexVec', bmPSL_reindexVec]
    have h : φ ᵥ* Pinv = 0 := by
      rw [← hΦeq, hΦ0]
      rfl
    have h' := congrArg (fun w => w ᵥ* P) h
    simpa [Matrix.vecMul_vecMul, hPinvP, Matrix.vecMul_one] using h'
  have hV2zero : V2 = 0 := by
    by_contra hV2
    have hΦ2zero : Φ2 = 0 := by
      rcases bmPSL_vecMulVec_eq_zero h22 with hV2' | hΦ2
      · exact absurd hV2' hV2
      · exact hΦ2
    have hΦ1zero : Φ1 = 0 := by
      rcases bmPSL_vecMulVec_eq_zero h21 with hV2' | hΦ1
      · exact absurd hV2' hV2
      · exact hΦ1
    apply hΦne
    ext i
    rcases i with i | i
    · simpa [Φ1] using congrFun hΦ1zero i
    · simpa [Φ2] using congrFun hΦ2zero i
  have hΦ2zero : Φ2 = 0 := by
    by_contra hΦ2
    have hV1zero : V1 = 0 := by
      rcases bmPSL_vecMulVec_eq_zero h12 with hV1 | hΦ2'
      · exact hV1
      · exact absurd hΦ2' hΦ2
    apply hVne
    ext i
    rcases i with i | i
    · simpa [V1] using congrFun hV1zero i
    · simpa [V2] using congrFun hV2zero i
  have hV1ne : V1 ≠ 0 := by
    intro hV1
    apply hVne
    ext i
    rcases i with i | i
    · simpa [V1] using congrFun hV1 i
    · simpa [V2] using congrFun hV2zero i
  have hΦ1ne : Φ1 ≠ 0 := by
    intro hΦ1
    apply hΦne
    ext i
    rcases i with i | i
    · simpa [Φ1] using congrFun hΦ1 i
    · simpa [Φ2] using congrFun hΦ2zero i
  have hdot' : Φ1 ⬝ᵥ V1 = 0 := by
    have hVeq : bmPSL_reindexVec eidx V = P *ᵥ v := by
      ext i
      simp [V, bmPSL_reindexVec', bmPSL_reindexVec]
    have hΦeq : bmPSL_reindexVec eidx Φ = φ ᵥ* Pinv := by
      ext i
      simp [Φ, bmPSL_reindexVec', bmPSL_reindexVec]
    have hliftV : V = bmPSL_liftVec (r' := r') V1 := by
      ext i
      rcases i with i | i
      · rfl
      · simpa [V1, V2, bmPSL_liftVec] using congrFun hV2zero i
    have hliftΦ : Φ = bmPSL_liftVec (r' := r') Φ1 := by
      ext i
      rcases i with i | i
      · rfl
      · simpa [Φ1, Φ2, bmPSL_liftVec] using congrFun hΦ2zero i
    rw [← bmPSL_reindexVec_dot eidx Φ1 V1]
    rw [← bmPSL_dot_conj P Pinv hPP]
    rw [← hliftV, ← hliftΦ, hVeq, hΦeq, Matrix.vecMul_vecMul, hPinvP,
      Matrix.vecMul_one, Matrix.mulVec_mulVec, hPinvP, Matrix.one_mulVec]
    exact hdot
  have hv_eq : v = Pinv *ᵥ bmPSL_reindexVec eidx (bmPSL_liftVec (r' := r') V1) := by
    have hVeq : bmPSL_reindexVec eidx V = P *ᵥ v := by
      ext i
      simp [V, bmPSL_reindexVec', bmPSL_reindexVec]
    have hliftV : V = bmPSL_liftVec (r' := r') V1 := by
      ext i
      rcases i with i | i
      · rfl
      · simpa [V1, V2, bmPSL_liftVec] using congrFun hV2zero i
    have h : bmPSL_reindexVec eidx (bmPSL_liftVec (r' := r') V1) = P *ᵥ v := by
      rw [← hVeq, ← hliftV]
    have h' := congrArg (fun w => Pinv *ᵥ w) h
    simpa [Matrix.mulVec_mulVec, hPinvP, Matrix.one_mulVec] using h'.symm
  have hφ_eq : φ = bmPSL_reindexVec eidx (bmPSL_liftVec (r' := r') Φ1) ᵥ* P := by
    have hΦeq : bmPSL_reindexVec eidx Φ = φ ᵥ* Pinv := by
      ext i
      simp [Φ, bmPSL_reindexVec', bmPSL_reindexVec]
    have hliftΦ : Φ = bmPSL_liftVec (r' := r') Φ1 := by
      ext i
      rcases i with i | i
      · rfl
      · simpa [Φ1, Φ2, bmPSL_liftVec] using congrFun hΦ2zero i
    have h : bmPSL_reindexVec eidx (bmPSL_liftVec (r' := r') Φ1) = φ ᵥ* Pinv := by
      rw [← hΦeq, ← hliftΦ]
    have h' := congrArg (fun w => w ᵥ* P) h
    have h'' : bmPSL_reindexVec eidx (bmPSL_liftVec (r' := r') Φ1) ᵥ* P = φ := by
      simpa [Matrix.vecMul_vecMul, hPinvP, Matrix.vecMul_one] using h'
    exact h''.symm
  exact ⟨V1, Φ1, hV1ne, hΦ1ne, hdot', hv_eq, hφ_eq⟩

private lemma bmPSL_embedMat_transvection {m r r' : ℕ} {F : Type} [Field F]
    {eidx : Fin r ⊕ Fin r' ≃ Fin (m + 1)}
    {P Pinv : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    (hPinvP : Pinv * P = 1) (u w : Fin r → F) (c : F) :
    bmPSL_embedMat eidx P Pinv
      (1 + c • Matrix.vecMulVec u w : Matrix (Fin r) (Fin r) F) =
      1 + c • Matrix.vecMulVec
        (Pinv *ᵥ bmPSL_reindexVec eidx (bmPSL_liftVec (r' := r') u))
        (bmPSL_reindexVec eidx (bmPSL_liftVec (r' := r') w) ᵥ* P) := by
  unfold bmPSL_embedMat
  rw [bmPSL_block_fromBlocks_transvection, bmPSL_reindex_transvection]
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, hPinvP]
  congr 1
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]

private lemma bmPSL_embedGL_matTransvGroup {m r r' : ℕ} {F : Type} [Field F]
    {eidx : Fin r ⊕ Fin r' ≃ Fin (m + 1)}
    {P Pinv : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    (hPP : P * Pinv = 1) (hPinvP : Pinv * P = 1) (u w : Fin r → F) :
    (matTransvGroup u w).map (bmPSL_embedGL eidx P Pinv hPP hPinvP) =
      matTransvGroup
        (Pinv *ᵥ bmPSL_reindexVec eidx (bmPSL_liftVec (r' := r') u))
        (bmPSL_reindexVec eidx (bmPSL_liftVec (r' := r') w) ᵥ* P) := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap, matTransvGroup, Subgroup.closure_le]
    intro g hg
    obtain ⟨c, hc⟩ := hg
    change bmPSL_embedGL eidx P Pinv hPP hPinvP g ∈
      matTransvGroup
        (Pinv *ᵥ bmPSL_reindexVec eidx (bmPSL_liftVec (r' := r') u))
        (bmPSL_reindexVec eidx (bmPSL_liftVec (r' := r') w) ᵥ* P)
    refine Subgroup.subset_closure ⟨c, ?_⟩
    rw [bmPSL_embedGL_coe, hc, bmPSL_embedMat_transvection hPinvP]
  · rw [matTransvGroup, Subgroup.closure_le]
    intro g hg
    obtain ⟨c, hc⟩ := hg
    change ∃ x : GL (Fin r) F, x ∈ matTransvGroup u w ∧
      bmPSL_embedGL eidx P Pinv hPP hPinvP x = g
    let h : Matrix (Fin r) (Fin r) F := 1 + c • Matrix.vecMulVec u w
    have hdet : h.det ≠ 0 := by
      have hgdet : (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F).det ≠ 0 :=
        (Matrix.GeneralLinearGroup.det g).ne_zero
      have hval : ((g : GL (Fin (m + 1)) F) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
          bmPSL_embedMat eidx P Pinv h := by
        rw [hc, bmPSL_embedMat_transvection hPinvP]
      rw [hval, bmPSL_embedMat_det hPP] at hgdet
      exact hgdet
    let x : GL (Fin r) F := Matrix.GeneralLinearGroup.mkOfDetNeZero h hdet
    refine ⟨x, ?_, ?_⟩
    · refine Subgroup.subset_closure ⟨c, ?_⟩
      rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
    · apply Units.ext
      rw [bmPSL_embedGL_coe, Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
      rw [hc, bmPSL_embedMat_transvection hPinvP]

private lemma bmPSL_embedMat_injective {m r r' : ℕ} {F : Type} [Field F]
    {eidx : Fin r ⊕ Fin r' ≃ Fin (m + 1)}
    {P Pinv : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    (hPP : P * Pinv = 1) (_hPinvP : Pinv * P = 1) :
    Function.Injective (bmPSL_embedMat eidx P Pinv) := by
  intro x y hxy
  let Dx : Matrix (Fin (m + 1)) (Fin (m + 1)) F := Matrix.reindex eidx eidx
    (Matrix.fromBlocks x (0 : Matrix (Fin r) (Fin r') F)
      (0 : Matrix (Fin r') (Fin r) F) (1 : Matrix (Fin r') (Fin r') F))
  let Dy : Matrix (Fin (m + 1)) (Fin (m + 1)) F := Matrix.reindex eidx eidx
    (Matrix.fromBlocks y (0 : Matrix (Fin r) (Fin r') F)
      (0 : Matrix (Fin r') (Fin r) F) (1 : Matrix (Fin r') (Fin r') F))
  have h : Dx = Dy := by
    have h' := congrArg (fun M : Matrix (Fin (m + 1)) (Fin (m + 1)) F =>
      P * M * Pinv) hxy
    have h'' : P * (Pinv * Dx * P) * Pinv = P * (Pinv * Dy * P) * Pinv := by
      simpa [bmPSL_embedMat, Dx, Dy] using h'
    calc Dx = (P * Pinv) * Dx * (P * Pinv) := by rw [hPP]; simp
      _ = P * (Pinv * Dx * P) * Pinv := by noncomm_ring
      _ = P * (Pinv * Dy * P) * Pinv := h''
      _ = Dy := by
          calc P * (Pinv * Dy * P) * Pinv = (P * Pinv) * Dy * (P * Pinv) := by
                noncomm_ring
            _ = Dy := by rw [hPP]; simp
  have h' := congrArg (Matrix.reindexAlgEquiv F F eidx.symm) h
  have h'' : Matrix.fromBlocks x (0 : Matrix (Fin r) (Fin r') F)
      (0 : Matrix (Fin r') (Fin r) F) (1 : Matrix (Fin r') (Fin r') F) =
      Matrix.fromBlocks y (0 : Matrix (Fin r) (Fin r') F)
        (0 : Matrix (Fin r') (Fin r) F) (1 : Matrix (Fin r') (Fin r') F) := by
    simpa [Dx, Dy, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply,
      Equiv.symm_apply_apply, Equiv.apply_symm_apply] using h'
  rw [Matrix.fromBlocks_inj] at h''
  exact h''.1

lemma bmPSL_embedHom_injective {m r r' : ℕ} {F : Type} [Field F]
    {eidx : Fin r ⊕ Fin r' ≃ Fin (m + 1)}
    {P Pinv : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    {hPP : P * Pinv = 1} {hPinvP : Pinv * P = 1} :
    Function.Injective (bmPSL_embedHom eidx P Pinv hPP hPinvP) := by
  intro x y hxy
  apply Subtype.ext
  apply bmPSL_embedMat_injective hPP hPinvP
  have h := congrArg (fun z : Matrix.SpecialLinearGroup (Fin (m + 1)) F =>
    (z : Matrix (Fin (m + 1)) (Fin (m + 1)) F)) hxy
  simpa [bmPSL_embedHom_coe] using h

private lemma bmPSL_solvable_SL_two_of_card_two {F : Type} [Field F] [Finite F]
    (hcard : Nat.card F = 2) :
    Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) F) := by
  haveI : Fintype F := Fintype.ofFinite F
  have hF : Fintype.card F = 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  obtain ⟨e⟩ := TauCeti.nonempty_mulEquiv_permFinThree hF
  haveI : Group.IsSolvable (Equiv.Perm (Fin 3)) :=
    Equiv.Perm.isSolvable (by norm_num)
  have hGL : Group.IsSolvable (GL (Fin 2) F) :=
    Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact Group.isSolvable_of_isSolvable_injective
    (f := Matrix.SpecialLinearGroup.toGL) Matrix.SpecialLinearGroup.toGL_injective

private lemma bmPSL_toGL_comp_embedHom {m r r' : ℕ} {F : Type} [Field F]
    {eidx : Fin r ⊕ Fin r' ≃ Fin (m + 1)}
    {P Pinv : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    {hPP : P * Pinv = 1} {hPinvP : Pinv * P = 1} :
    Matrix.SpecialLinearGroup.toGL.comp (bmPSL_embedHom eidx P Pinv hPP hPinvP) =
      (bmPSL_embedGL eidx P Pinv hPP hPinvP).comp
        Matrix.SpecialLinearGroup.toGL := by
  apply MonoidHom.ext
  intro x
  apply Units.ext
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, bmPSL_embedGL_coe]
  change ((bmPSL_embedHom eidx P Pinv hPP hPinvP x :
    Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
    bmPSL_embedMat eidx P Pinv ((Matrix.SpecialLinearGroup.toGL x :
      GL (Fin r) F) : Matrix (Fin r) (Fin r) F)
  rw [bmPSL_embedHom_coe]
  rfl

private lemma bmPSL_map_conj_range_of_mem {G : Type} [Group G] {H : Subgroup G} {h : G}
    (hh : h ∈ H) : H.map (MulAut.conj h).toMonoidHom = H := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact H.mul_mem (H.mul_mem hh hx) (H.inv_mem hh)
  · intro x hx
    refine ⟨h⁻¹ * x * h, H.mul_mem (H.mul_mem (H.inv_mem hh) hx) hh, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

lemma bmPSL_center_embed {m r r' : ℕ} {F : Type} [Field F]
    {eidx : Fin r ⊕ Fin r' ≃ Fin (m + 1)}
    {P Pinv : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    {hPP : P * Pinv = 1} {hPinvP : Pinv * P = 1}
    {y : Matrix.SpecialLinearGroup (Fin r) F}
    (hy : bmPSL_embedHom eidx P Pinv hPP hPinvP y ∈
      Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F)) :
    y ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin r) F) := by
  rw [Subgroup.mem_center_iff] at hy ⊢
  intro z
  have h := hy (bmPSL_embedHom eidx P Pinv hPP hPinvP z)
  have h' : bmPSL_embedHom eidx P Pinv hPP hPinvP (z * y) =
      bmPSL_embedHom eidx P Pinv hPP hPinvP (y * z) := by
    simpa only [map_mul] using h
  exact (bmPSL_embedHom_injective (hPP := hPP) (hPinvP := hPinvP)) h'

private lemma bmPSL_embed_mem {m r r' : ℕ} {F : Type} [Field F]
    {S : Set (GL (Fin (m + 1)) F)}
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    (hdeg : blockDegree (Algebra.adjoin F (Units.val '' S)) e < 2)
    {eidx : Fin r ⊕ Fin r' ≃ Fin (m + 1)}
    {P Pinv : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    (hPP : P * Pinv = 1) (hPinvP : Pinv * P = 1)
    {D : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    (hconv : Pinv * D * P = e)
    (hD : D = Matrix.reindex eidx eidx
      (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) F)
        (0 : Matrix (Fin r) (Fin r') F) (0 : Matrix (Fin r') (Fin r) F)
        (0 : Matrix (Fin r') (Fin r') F)))
    (x : Matrix.SpecialLinearGroup (Fin r) F) :
    bmPSL_embedHom eidx P Pinv hPP hPinvP x ∈
      glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e := by
  rw [glBlockCentralizer, Subgroup.mem_comap, Subgroup.mem_inf]
  constructor
  · rw [Subgroup.mem_centralizer_iff]
    intro s hs
    apply Units.ext
    change (s : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
        bmPSL_embedMat eidx P Pinv (x : Matrix (Fin r) (Fin r) F) =
      bmPSL_embedMat eidx P Pinv (x : Matrix (Fin r) (Fin r) F) *
        (s : Matrix (Fin (m + 1)) (Fin (m + 1)) F)
    exact bmPSL_embedMat_centralizes hS he hdeg hPP hPinvP hconv hD hs
      (x : Matrix (Fin r) (Fin r) F)
  · change bmPSL_embedMat eidx P Pinv (x : Matrix (Fin r) (Fin r) F) * (1 - e) = 1 - e
    exact bmPSL_embedMat_fix eidx hPP hPinvP hconv hD
      (x : Matrix (Fin r) (Fin r) F)

lemma bmPSL_embedHom_range_eq {m r r' : ℕ} {F : Type} [Field F]
    {S : Set (GL (Fin (m + 1)) F)}
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    (hdeg : blockDegree (Algebra.adjoin F (Units.val '' S)) e < 2)
    {eidx : Fin r ⊕ Fin r' ≃ Fin (m + 1)}
    {P Pinv : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    (hPP : P * Pinv = 1) (hPinvP : Pinv * P = 1)
    {D : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    (hconv : Pinv * D * P = e)
    (hD : D = Matrix.reindex eidx eidx
      (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) F)
        (0 : Matrix (Fin r) (Fin r') F) (0 : Matrix (Fin r') (Fin r) F)
        (0 : Matrix (Fin r') (Fin r') F))) :
    (bmPSL_embedHom eidx P Pinv hPP hPinvP).range =
      glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    exact bmPSL_embed_mem hS he hdeg hPP hPinvP hconv hD x
  · intro g hg
    exact bmPSL_mem_range_of_block he hconv hD hg

private lemma bmPSL_conj_comp {G H : Type} [Group G] [Group H] (f : G →* H) (u : G) :
    (MulAut.conj (f u)).toMonoidHom.comp f =
      f.comp (MulAut.conj u).toMonoidHom := by
  ext x
  simp [MulAut.conj_apply, map_mul]

theorem exists_blockModel_PSL_rank
    (m f : ℕ) (S : Set (GL (Fin (m + 1)) (GaloisField 2 f)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 2)
    {J' : Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f))}
    (hJe : IsComponentOf J' ⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
      glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆) :
    ∃ (k : ℕ) (ι : (ggU .PSL (k + 1) f).K →* (ggU .PSL (m + 1) f).K)
      (β₀ : Fin (ggU .PSL (k + 1) f).D.rank → ℤ) (v φ v' φ' : Fin (m + 1) → GaloisField 2 f),
      GGLongRoot (ggU .PSL (k + 1) f).D β₀ ∧
      (∀ y, ι y ∈ Subgroup.center (ggU .PSL (m + 1) f).K →
        y ∈ Subgroup.center (ggU .PSL (k + 1) f).K) ∧ ι.range = J' ∧
      φ ⬝ᵥ v = 0 ∧ φ' ⬝ᵥ v' = 0 ∧ φ ⬝ᵥ v' = 1 ∧ φ' ⬝ᵥ v = 1 ∧
      (((ggU .PSL (k + 1) f).D.rootGroup β₀).map ι).map Matrix.SpecialLinearGroup.toGL =
        matTransvGroup v φ ∧
      (((ggU .PSL (k + 1) f).D.rootGroup (-β₀)).map ι).map Matrix.SpecialLinearGroup.toGL =
        matTransvGroup v' φ' ∧
      k + 1 = Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.toLin' e)) ∧
      J' = glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e ∧
      β₀ ∈ (ggU .PSL (k + 1) f).D.roots := by
  classical
  have hidem : IsIdempotentElem e := he.2.1
  obtain ⟨r, r', eidx, P, Pinv, hPP, hPinvP, hconv, hrfin, _, hrpos⟩ :=
    bmPSL_exists_conj_diag (m := m) (F := GaloisField 2 f) hidem
  let D : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f) :=
    Matrix.reindex eidx eidx
      (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) (GaloisField 2 f))
        (0 : Matrix (Fin r) (Fin r') (GaloisField 2 f))
        (0 : Matrix (Fin r') (Fin r) (GaloisField 2 f))
        (0 : Matrix (Fin r') (Fin r') (GaloisField 2 f)))
  have hD : D = Matrix.reindex eidx eidx
      (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) (GaloisField 2 f))
        (0 : Matrix (Fin r) (Fin r') (GaloisField 2 f))
        (0 : Matrix (Fin r') (Fin r) (GaloisField 2 f))
        (0 : Matrix (Fin r') (Fin r') (GaloisField 2 f))) := rfl
  have hconvD : Pinv * D * P = e := hconv
  have hrange := bmPSL_embedHom_range_eq (S := S) hS he hdeg hPP hPinvP hconvD hD
  have he0 : e ≠ 0 := he.2.2.1
  have hrnz : r ≠ 0 := by
    intro h
    have := hrpos he0
    omega
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hrnz
  by_cases hk0 : k = 0
  · subst hk0
    haveI : Subsingleton
        (Matrix.SpecialLinearGroup (Fin 1) (GaloisField 2 f)) :=
      Matrix.SpecialLinearGroup.subsingleton_of_subsingleton
    have hbot_range :
        (bmPSL_embedHom eidx P Pinv hPP hPinvP).range = ⊥ := by
      apply le_antisymm
      · rintro x ⟨a, rfl⟩
        rw [Subsingleton.elim a 1, map_one]
        exact Subgroup.mem_bot.mpr rfl
      · exact bot_le
    have hbot : glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e = ⊥ := by
      rw [← hrange, hbot_range]
    have hcommbot :
        ⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
          glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆ = ⊥ := by
      rw [hbot]
      simp
    have hle : J' ≤ (⊥ : Subgroup
        (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f))) := by
      simpa [hcommbot] using hJe.1
    have hJbot : J' = ⊥ := le_bot_iff.mp hle
    haveI : Subsingleton J' := by
      rw [hJbot]
      infer_instance
    obtain ⟨-, hsimpleJ⟩ := hJe.2.2
    haveI : Nontrivial (J' ⧸ Subgroup.center J') := hsimpleJ.toNontrivial
    haveI : Nontrivial J' :=
      Function.Surjective.nontrivial (QuotientGroup.mk'_surjective (Subgroup.center J'))
    exfalso
    exact (not_subsingleton_iff_nontrivial.mpr
      (inferInstance : Nontrivial J')) (inferInstance : Subsingleton J')
  · have hk : 1 ≤ k := Nat.pos_of_ne_zero hk0
    obtain ⟨hperfJ, hsimpleJ⟩ := hJe.2.2
    by_cases hsmall : k = 1 ∧ Nat.card (GaloisField 2 f) = 2
    · obtain ⟨hk1, hcard⟩ := hsmall
      subst hk1
      haveI : Group.IsSolvable
          (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) :=
        bmPSL_solvable_SL_two_of_card_two hcard
      haveI hRangeSol : Group.IsSolvable
          (bmPSL_embedHom eidx P Pinv hPP hPinvP).range :=
        Group.isSolvable_of_surjective
          (f := (MonoidHom.ofInjective
            (bmPSL_embedHom_injective (hPP := hPP) (hPinvP := hPinvP))).toMonoidHom)
          (MonoidHom.ofInjective
            (bmPSL_embedHom_injective (hPP := hPP) (hPinvP := hPinvP))).surjective
      have hGsol : Group.IsSolvable
          (glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e) :=
        hrange ▸ hRangeSol
      haveI : Group.IsSolvable
          (glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e) := hGsol
      haveI hCommSol : Group.IsSolvable
          ↥(⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
            glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆) :=
        Group.isSolvable_of_isSolvable_injective
          (f := Subgroup.inclusion
            (Subgroup.commutator_le_self _))
          (fun _ _ h => (Subgroup.inclusion_inj _).mp h)
      haveI : Group.IsSolvable J' :=
        Group.isSolvable_of_isSolvable_injective
          (f := Subgroup.inclusion hJe.1)
          (fun _ _ h => (Subgroup.inclusion_inj hJe.1).mp h)
      haveI : Nontrivial (J' ⧸ Subgroup.center J') := hsimpleJ.toNontrivial
      haveI : Nontrivial J' :=
        Function.Surjective.nontrivial (QuotientGroup.mk'_surjective (Subgroup.center J'))
      haveI : Group.IsPerfect J' := Group.IsPerfect.mk hperfJ
      exfalso
      exact (Group.IsPerfect.not_isSolvable J') inferInstance
    · have hQ : CFSG.Assembly.IsQuasisimple
          (Matrix.SpecialLinearGroup (Fin (k + 1)) (GaloisField 2 f)) := by
        apply CFSG.StandardType.isQuasisimple_specialLinear
        · simpa [Fintype.card_fin] using Nat.succ_le_succ hk
        · by_cases hk1 : k = 1
          · right
            intro hcard
            exact hsmall ⟨hk1, hcard⟩
          · left
            simp [Fintype.card_fin]
            omega
      have hQrange : CFSG.Assembly.IsQuasisimple
          (bmPSL_embedHom eidx P Pinv hPP hPinvP).range :=
        CFSG.Assembly.IsQuasisimple.of_mulEquiv
          (MonoidHom.ofInjective
            (bmPSL_embedHom_injective (hPP := hPP) (hPinvP := hPinvP))).symm hQ
      have hQGe : CFSG.Assembly.IsQuasisimple
          (glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e) :=
        hrange ▸ hQrange
      have hQGeOpen : CFSG.Open.IsQuasisimple
          (glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e) :=
        (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).mp hQGe
      have hperfGe :
          ⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
            glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆ =
            glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e := by
        haveI : Group.IsPerfect
            (glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e) :=
          Group.IsPerfect.mk hQGe.1
        exact Subgroup.commutator_eq_self
      have hJeq : J' =
          glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e := by
        apply CFSG.LocalAnalysis.GLTheoremA.S11.y10xF_eq_of_subnormal hQGeOpen
          (by simpa [hperfGe] using hJe.1)
        · exact (CFSG.ComponentClassification.AssemblyBPredicates.isSubnormal_iff_open
            _ _).mp (by simpa [hperfGe] using hJe.2.1)
        · exact ⟨hperfJ, hsimpleJ⟩
      have h0last : (0 : Fin (k + 1)) ≠ Fin.last k := by
        intro h
        have := congrArg Fin.val h
        simp at this
        omega
      let e0 : Fin (k + 1) → GaloisField 2 f := Pi.single 0 1
      let elast : Fin (k + 1) → GaloisField 2 f := Pi.single (Fin.last k) 1
      have h1 : elast ⬝ᵥ e0 = 0 := by
        simp [elast, e0, dotProduct, Pi.single_apply, h0last, Ne.symm h0last]
      have h2 : e0 ⬝ᵥ elast = 0 := by
        simp [elast, e0, dotProduct, Pi.single_apply, h0last, Ne.symm h0last]
      have h3 : elast ⬝ᵥ elast = 1 := by
        simp [elast, dotProduct, Pi.single_apply]
      have h4 : e0 ⬝ᵥ e0 = 1 := by
        simp [e0, dotProduct, Pi.single_apply]
      obtain ⟨β, hβroot, hlong, u, huX, huXneg⟩ :=
        exists_conj_rootGroup_eq_matTransvGroup_PSL k (GaloisField 2 f) hk
          e0 elast elast e0 h1 h2 h3 h4
      let U : Fin (m + 1) → GaloisField 2 f :=
        bmPSL_reindexVec eidx (bmPSL_liftVec (r' := r') e0)
      let V : Fin (m + 1) → GaloisField 2 f :=
        bmPSL_reindexVec eidx (bmPSL_liftVec (r' := r') elast)
      let v : Fin (m + 1) → GaloisField 2 f := Pinv *ᵥ U
      let φ : Fin (m + 1) → GaloisField 2 f := V ᵥ* P
      let v' : Fin (m + 1) → GaloisField 2 f := Pinv *ᵥ V
      let φ' : Fin (m + 1) → GaloisField 2 f := U ᵥ* P
      have hdot1 : φ ⬝ᵥ v = 0 := by
        dsimp [φ, v]
        rw [bmPSL_dot_conj P Pinv hPP, bmPSL_reindexVec_dot]
        exact h1
      have hdot2 : φ' ⬝ᵥ v' = 0 := by
        dsimp [φ', v']
        rw [bmPSL_dot_conj P Pinv hPP, bmPSL_reindexVec_dot]
        exact h2
      have hdot3 : φ ⬝ᵥ v' = 1 := by
        dsimp [φ, v']
        rw [bmPSL_dot_conj P Pinv hPP, bmPSL_reindexVec_dot]
        exact h3
      have hdot4 : φ' ⬝ᵥ v = 1 := by
        dsimp [φ', v]
        rw [bmPSL_dot_conj P Pinv hPP, bmPSL_reindexVec_dot]
        exact h4
      let uEmb : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f) :=
        bmPSL_embedHom eidx P Pinv hPP hPinvP u
      let ι : Matrix.SpecialLinearGroup (Fin (k + 1)) (GaloisField 2 f) →*
          Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f) :=
        (MulAut.conj uEmb).toMonoidHom.comp
          (bmPSL_embedHom eidx P Pinv hPP hPinvP)
      have hιrange : ι.range = J' := by
        have hιrange' : ι.range =
            (bmPSL_embedHom eidx P Pinv hPP hPinvP).range := by
          dsimp [ι]
          rw [MonoidHom.range_comp]
          exact bmPSL_map_conj_range_of_mem (by exact ⟨u, rfl⟩)
        rw [hιrange', hrange, hJeq]
      have hcenter : ∀ y, ι y ∈ Subgroup.center
          (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)) →
          y ∈ Subgroup.center
            (Matrix.SpecialLinearGroup (Fin (k + 1)) (GaloisField 2 f)) := by
        intro y hy
        have hy' : bmPSL_embedHom eidx P Pinv hPP hPinvP y ∈
            Subgroup.center
              (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)) := by
          have hconj : bmPSL_embedHom eidx P Pinv hPP hPinvP y =
              uEmb⁻¹ * ι y * uEmb := by
            dsimp [ι]
            group
          rw [hconj]
          rw [Subgroup.mem_center_iff] at hy ⊢
          intro g
          have h := hy (uEmb * g * uEmb⁻¹)
          simpa [mul_assoc] using congrArg (fun z => uEmb⁻¹ * z * uEmb) h
        exact bmPSL_center_embed (hPP := hPP) (hPinvP := hPinvP) hy'
      have hroot1 : (((SpecialLinear.rootDatum k
            (GaloisField 2 f)).rootGroup β).map ι).map
            Matrix.SpecialLinearGroup.toGL = matTransvGroup v φ := by
        let H : Subgroup
            (Matrix.SpecialLinearGroup (Fin (k + 1)) (GaloisField 2 f)) :=
          (SpecialLinear.rootDatum k (GaloisField 2 f)).rootGroup β |>.map
            (MulAut.conj u).toMonoidHom
        have hH : H.map Matrix.SpecialLinearGroup.toGL =
            matTransvGroup e0 elast := huX
        have hmap : ((SpecialLinear.rootDatum k
            (GaloisField 2 f)).rootGroup β).map ι =
            H.map (bmPSL_embedHom eidx P Pinv hPP hPinvP) := by
          dsimp [H, ι, uEmb]
          change Subgroup.map ((MulAut.conj
              (bmPSL_embedHom eidx P Pinv hPP hPinvP u)).toMonoidHom.comp
              (bmPSL_embedHom eidx P Pinv hPP hPinvP))
            ((SpecialLinear.rootDatum k (GaloisField 2 f)).rootGroup β) =
            Subgroup.map (bmPSL_embedHom eidx P Pinv hPP hPinvP)
              (Subgroup.map (MulAut.conj u).toMonoidHom
                ((SpecialLinear.rootDatum k (GaloisField 2 f)).rootGroup β))
          rw [bmPSL_conj_comp]
          rw [Subgroup.map_map]
        rw [hmap]
        calc (H.map (bmPSL_embedHom eidx P Pinv hPP hPinvP)).map
              Matrix.SpecialLinearGroup.toGL
            = H.map (Matrix.SpecialLinearGroup.toGL.comp
                (bmPSL_embedHom eidx P Pinv hPP hPinvP)) := by
              rw [Subgroup.map_map]
          _ = H.map ((bmPSL_embedGL eidx P Pinv hPP hPinvP).comp
                Matrix.SpecialLinearGroup.toGL) := by
              rw [bmPSL_toGL_comp_embedHom]
          _ = (H.map Matrix.SpecialLinearGroup.toGL).map
                (bmPSL_embedGL eidx P Pinv hPP hPinvP) := by
              exact (Subgroup.map_map H (bmPSL_embedGL eidx P Pinv hPP hPinvP)
                Matrix.SpecialLinearGroup.toGL).symm
          _ = (matTransvGroup e0 elast).map
                (bmPSL_embedGL eidx P Pinv hPP hPinvP) := by
              rw [hH]
          _ = matTransvGroup v φ := by
              dsimp [v, φ]
              exact bmPSL_embedGL_matTransvGroup hPP hPinvP e0 elast
      have hroot2 : (((SpecialLinear.rootDatum k
            (GaloisField 2 f)).rootGroup (-β)).map ι).map
            Matrix.SpecialLinearGroup.toGL = matTransvGroup v' φ' := by
        let H : Subgroup
            (Matrix.SpecialLinearGroup (Fin (k + 1)) (GaloisField 2 f)) :=
          (SpecialLinear.rootDatum k (GaloisField 2 f)).rootGroup (-β) |>.map
            (MulAut.conj u).toMonoidHom
        have hH : H.map Matrix.SpecialLinearGroup.toGL =
            matTransvGroup elast e0 := huXneg
        have hmap : ((SpecialLinear.rootDatum k
            (GaloisField 2 f)).rootGroup (-β)).map ι =
            H.map (bmPSL_embedHom eidx P Pinv hPP hPinvP) := by
          dsimp [H, ι, uEmb]
          change Subgroup.map ((MulAut.conj
              (bmPSL_embedHom eidx P Pinv hPP hPinvP u)).toMonoidHom.comp
              (bmPSL_embedHom eidx P Pinv hPP hPinvP))
            ((SpecialLinear.rootDatum k (GaloisField 2 f)).rootGroup (-β)) =
            Subgroup.map (bmPSL_embedHom eidx P Pinv hPP hPinvP)
              (Subgroup.map (MulAut.conj u).toMonoidHom
                ((SpecialLinear.rootDatum k (GaloisField 2 f)).rootGroup (-β)))
          rw [bmPSL_conj_comp]
          rw [Subgroup.map_map]
        rw [hmap]
        calc (H.map (bmPSL_embedHom eidx P Pinv hPP hPinvP)).map
              Matrix.SpecialLinearGroup.toGL
            = H.map (Matrix.SpecialLinearGroup.toGL.comp
                (bmPSL_embedHom eidx P Pinv hPP hPinvP)) := by
              rw [Subgroup.map_map]
          _ = H.map ((bmPSL_embedGL eidx P Pinv hPP hPinvP).comp
                Matrix.SpecialLinearGroup.toGL) := by
              rw [bmPSL_toGL_comp_embedHom]
          _ = (H.map Matrix.SpecialLinearGroup.toGL).map
                (bmPSL_embedGL eidx P Pinv hPP hPinvP) := by
              exact (Subgroup.map_map H (bmPSL_embedGL eidx P Pinv hPP hPinvP)
                Matrix.SpecialLinearGroup.toGL).symm
          _ = (matTransvGroup elast e0).map
                (bmPSL_embedGL eidx P Pinv hPP hPinvP) := by
              rw [hH]
          _ = matTransvGroup v' φ' := by
              dsimp [v', φ']
              exact bmPSL_embedGL_matTransvGroup hPP hPinvP elast e0
      refine ⟨k, ι, β, v, φ, v', φ', ?_, hcenter, hιrange, hdot1, hdot2,
        hdot3, hdot4, ?_, ?_, hrfin, hJeq, hβroot⟩
      · change GGLongRoot (SpecialLinear.rootDatum k (GaloisField 2 f)) β
        exact hlong
      · change ((((SpecialLinear.rootDatum k
            (GaloisField 2 f)).rootGroup β).map ι).map
            Matrix.SpecialLinearGroup.toGL) = matTransvGroup v φ
        exact hroot1
      · change ((((SpecialLinear.rootDatum k
            (GaloisField 2 f)).rootGroup (-β)).map ι).map
            Matrix.SpecialLinearGroup.toGL) = matTransvGroup v' φ'
        exact hroot2

theorem exists_blockModel_PSL
    (m f : ℕ) (S : Set (GL (Fin (m + 1)) (GaloisField 2 f)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') 
    {e : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 2)
    {J' : Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f))}
    (hJe : IsComponentOf J' ⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
      glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆) :
    ∃ (k : ℕ) (ι : (ggU .PSL (k + 1) f).K →* (ggU .PSL (m + 1) f).K)
      (β₀ : Fin (ggU .PSL (k + 1) f).D.rank → ℤ) (v φ v' φ' : Fin (m + 1) → GaloisField 2 f),
      GGLongRoot (ggU .PSL (k + 1) f).D β₀ ∧
      (∀ y, ι y ∈ Subgroup.center (ggU .PSL (m + 1) f).K →
        y ∈ Subgroup.center (ggU .PSL (k + 1) f).K) ∧ ι.range = J' ∧
      φ ⬝ᵥ v = 0 ∧ φ' ⬝ᵥ v' = 0 ∧ φ ⬝ᵥ v' = 1 ∧ φ' ⬝ᵥ v = 1 ∧
      (((ggU .PSL (k + 1) f).D.rootGroup β₀).map ι).map Matrix.SpecialLinearGroup.toGL =
        matTransvGroup v φ ∧
      (((ggU .PSL (k + 1) f).D.rootGroup (-β₀)).map ι).map Matrix.SpecialLinearGroup.toGL =
        matTransvGroup v' φ' := by
  obtain ⟨k, ι, β₀, v, φ, v', φ', h1, h2, h3, h4, h5, h6, h7, h8, h9, -, -, -⟩ :=
    exists_blockModel_PSL_rank m f S hS he hdeg hJe
  exact ⟨k, ι, β₀, v, φ, v', φ', h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem exists_blockModelClosure_PSL_rank
    (m f : ℕ) (S : Set (GL (Fin (m + 1)) (GaloisField 2 f)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 2)
    {J' : Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f))}
    (hJe : IsComponentOf J' ⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
      glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆) :
    ∃ (k : ℕ) (ι : (ggU .PSL (k + 1) f).K →* (ggU .PSL (m + 1) f).K),
      (∀ y, ι y ∈ Subgroup.center (ggU .PSL (m + 1) f).K → y ∈ Subgroup.center (ggU .PSL (k + 1)
          f).K) ∧
      ι.range = J' ∧
      (∀ v₀ φ₀ : Fin (m + 1) → GaloisField 2 f, v₀ ≠ 0 → φ₀ ≠ 0 → φ₀ ⬝ᵥ v₀ = 0 → matTransvGroup v₀
          φ₀ ≤ J'.map Matrix.SpecialLinearGroup.toGL →
        ∃ (β : Fin (ggU .PSL (k + 1) f).D.rank → ℤ) (u : (ggU .PSL (k + 1) f).K), β ∈ (ggU .PSL (k
            + 1) f).D.roots ∧ GGLongRoot (ggU .PSL (k + 1) f).D β ∧
          ((((ggU .PSL (k + 1) f).D.rootGroup β).map (MulAut.conj u).toMonoidHom).map ι).map
              Matrix.SpecialLinearGroup.toGL = matTransvGroup v₀ φ₀) ∧
      k + 1 = Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.toLin' e)) := by
  classical
  have hidem : IsIdempotentElem e := he.2.1
  obtain ⟨r, r', eidx, P, Pinv, hPP, hPinvP, hconv, hrfin, _, hrpos⟩ :=
    bmPSL_exists_conj_diag (m := m) (F := GaloisField 2 f) hidem
  let D : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f) :=
    Matrix.reindex eidx eidx
      (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) (GaloisField 2 f))
        (0 : Matrix (Fin r) (Fin r') (GaloisField 2 f))
        (0 : Matrix (Fin r') (Fin r) (GaloisField 2 f))
        (0 : Matrix (Fin r') (Fin r') (GaloisField 2 f)))
  have hD : D = Matrix.reindex eidx eidx
      (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) (GaloisField 2 f))
        (0 : Matrix (Fin r) (Fin r') (GaloisField 2 f))
        (0 : Matrix (Fin r') (Fin r) (GaloisField 2 f))
        (0 : Matrix (Fin r') (Fin r') (GaloisField 2 f))) := rfl
  have hconvD : Pinv * D * P = e := hconv
  have hrange := bmPSL_embedHom_range_eq (S := S) hS he hdeg hPP hPinvP hconvD hD
  have he0 : e ≠ 0 := he.2.2.1
  have hrnz : r ≠ 0 := by
    intro h
    have := hrpos he0
    omega
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hrnz
  by_cases hk0 : k = 0
  · subst hk0
    haveI : Subsingleton
        (Matrix.SpecialLinearGroup (Fin 1) (GaloisField 2 f)) :=
      Matrix.SpecialLinearGroup.subsingleton_of_subsingleton
    have hbot_range :
        (bmPSL_embedHom eidx P Pinv hPP hPinvP).range = ⊥ := by
      apply le_antisymm
      · rintro x ⟨a, rfl⟩
        rw [Subsingleton.elim a 1, map_one]
        exact Subgroup.mem_bot.mpr rfl
      · exact bot_le
    have hbot : glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e = ⊥ := by
      rw [← hrange, hbot_range]
    have hcommbot :
        ⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
          glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆ = ⊥ := by
      rw [hbot]
      simp
    have hle : J' ≤ (⊥ : Subgroup
        (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f))) := by
      simpa [hcommbot] using hJe.1
    have hJbot : J' = ⊥ := le_bot_iff.mp hle
    haveI : Subsingleton J' := by
      rw [hJbot]
      infer_instance
    obtain ⟨-, hsimpleJ⟩ := hJe.2.2
    haveI : Nontrivial (J' ⧸ Subgroup.center J') := hsimpleJ.toNontrivial
    haveI : Nontrivial J' :=
      Function.Surjective.nontrivial (QuotientGroup.mk'_surjective (Subgroup.center J'))
    exfalso
    exact (not_subsingleton_iff_nontrivial.mpr
      (inferInstance : Nontrivial J')) (inferInstance : Subsingleton J')
  · have hk : 1 ≤ k := Nat.pos_of_ne_zero hk0
    obtain ⟨hperfJ, hsimpleJ⟩ := hJe.2.2
    by_cases hsmall : k = 1 ∧ Nat.card (GaloisField 2 f) = 2
    · obtain ⟨hk1, hcard⟩ := hsmall
      subst hk1
      haveI : Group.IsSolvable
          (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) :=
        bmPSL_solvable_SL_two_of_card_two hcard
      haveI hRangeSol : Group.IsSolvable
          (bmPSL_embedHom eidx P Pinv hPP hPinvP).range :=
        Group.isSolvable_of_surjective
          (f := (MonoidHom.ofInjective
            (bmPSL_embedHom_injective (hPP := hPP) (hPinvP := hPinvP))).toMonoidHom)
          (MonoidHom.ofInjective
            (bmPSL_embedHom_injective (hPP := hPP) (hPinvP := hPinvP))).surjective
      have hGsol : Group.IsSolvable
          (glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e) :=
        hrange ▸ hRangeSol
      haveI : Group.IsSolvable
          (glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e) := hGsol
      haveI hCommSol : Group.IsSolvable
          ↥(⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
            glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆) :=
        Group.isSolvable_of_isSolvable_injective
          (f := Subgroup.inclusion
            (Subgroup.commutator_le_self _))
          (fun _ _ h => (Subgroup.inclusion_inj _).mp h)
      haveI : Group.IsSolvable J' :=
        Group.isSolvable_of_isSolvable_injective
          (f := Subgroup.inclusion hJe.1)
          (fun _ _ h => (Subgroup.inclusion_inj hJe.1).mp h)
      haveI : Nontrivial (J' ⧸ Subgroup.center J') := hsimpleJ.toNontrivial
      haveI : Nontrivial J' :=
        Function.Surjective.nontrivial (QuotientGroup.mk'_surjective (Subgroup.center J'))
      haveI : Group.IsPerfect J' := Group.IsPerfect.mk hperfJ
      exfalso
      exact (Group.IsPerfect.not_isSolvable J') inferInstance
    · have hQ : CFSG.Assembly.IsQuasisimple
          (Matrix.SpecialLinearGroup (Fin (k + 1)) (GaloisField 2 f)) := by
        apply CFSG.StandardType.isQuasisimple_specialLinear
        · simpa [Fintype.card_fin] using Nat.succ_le_succ hk
        · by_cases hk1 : k = 1
          · right
            intro hcard
            exact hsmall ⟨hk1, hcard⟩
          · left
            simp [Fintype.card_fin]
            omega
      have hQrange : CFSG.Assembly.IsQuasisimple
          (bmPSL_embedHom eidx P Pinv hPP hPinvP).range :=
        CFSG.Assembly.IsQuasisimple.of_mulEquiv
          (MonoidHom.ofInjective
            (bmPSL_embedHom_injective (hPP := hPP) (hPinvP := hPinvP))).symm hQ
      have hQGe : CFSG.Assembly.IsQuasisimple
          (glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e) :=
        hrange ▸ hQrange
      have hQGeOpen : CFSG.Open.IsQuasisimple
          (glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e) :=
        (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).mp hQGe
      have hperfGe :
          ⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
            glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆ =
            glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e := by
        haveI : Group.IsPerfect
            (glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e) :=
          Group.IsPerfect.mk hQGe.1
        exact Subgroup.commutator_eq_self
      have hJeq : J' =
          glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e := by
        apply CFSG.LocalAnalysis.GLTheoremA.S11.y10xF_eq_of_subnormal hQGeOpen
          (by simpa [hperfGe] using hJe.1)
        · exact (CFSG.ComponentClassification.AssemblyBPredicates.isSubnormal_iff_open
            _ _).mp (by simpa [hperfGe] using hJe.2.1)
        · exact ⟨hperfJ, hsimpleJ⟩

      refine ⟨k, bmPSL_embedHom eidx P Pinv hPP hPinvP, ?_, ?_, ?_, hrfin⟩
      · exact fun y hy => bmPSL_center_embed (hPP := hPP) (hPinvP := hPinvP) hy
      · exact hrange.trans hJeq.symm
      · intro v₀ φ₀ hv hφ hdot hle
        have hle' : matTransvGroup v₀ φ₀ ≤
            (bmPSL_embedGL eidx P Pinv hPP hPinvP).range := by
          intro x hx
          obtain ⟨j, hj, rfl⟩ := hle hx
          have hj' : j ∈ (bmPSL_embedHom eidx P Pinv hPP hPinvP).range := by
            rw [hrange, hJeq.symm]
            exact hj
          obtain ⟨z, rfl⟩ := hj'
          refine ⟨Matrix.SpecialLinearGroup.toGL z, ?_⟩
          exact (congrArg (fun f => f z)
            (bmPSL_toGL_comp_embedHom (hPP := hPP) (hPinvP := hPinvP))).symm
        obtain ⟨w, ψ, hw, hψ, hψw, hv_eq, hφ_eq⟩ :=
          bmPSL_transv_le_embedGL_support hPP hPinvP hv hφ hdot hle'
        obtain ⟨w', hψw'⟩ := bmPSL_exists_vec_dot_eq_one hψ
        obtain ⟨ψ', hψ'w, hψ'w'⟩ := bmPSL_exists_dual_pair w ψ w' hw hψw hψw'
        obtain ⟨β, hβroot, hlong, u, huX, _⟩ :=
          exists_conj_rootGroup_eq_matTransvGroup_PSL k (GaloisField 2 f) hk
            w ψ w' ψ' hψw hψ'w' hψw' hψ'w
        refine ⟨β, u, hβroot, hlong, ?_⟩
        let H : Subgroup
            (Matrix.SpecialLinearGroup (Fin (k + 1)) (GaloisField 2 f)) :=
          ((SpecialLinear.rootDatum k (GaloisField 2 f)).rootGroup β).map
            (MulAut.conj u).toMonoidHom
        have hH : H.map Matrix.SpecialLinearGroup.toGL = matTransvGroup w ψ := huX
        change ((H.map (bmPSL_embedHom eidx P Pinv hPP hPinvP)).map
            Matrix.SpecialLinearGroup.toGL) = matTransvGroup v₀ φ₀
        calc (H.map (bmPSL_embedHom eidx P Pinv hPP hPinvP)).map
              Matrix.SpecialLinearGroup.toGL
            = H.map (Matrix.SpecialLinearGroup.toGL.comp
                (bmPSL_embedHom eidx P Pinv hPP hPinvP)) := by
              rw [Subgroup.map_map]
          _ = H.map ((bmPSL_embedGL eidx P Pinv hPP hPinvP).comp
                Matrix.SpecialLinearGroup.toGL) := by
              rw [bmPSL_toGL_comp_embedHom]
          _ = (H.map Matrix.SpecialLinearGroup.toGL).map
                (bmPSL_embedGL eidx P Pinv hPP hPinvP) := by
              exact (Subgroup.map_map H (bmPSL_embedGL eidx P Pinv hPP hPinvP)
                Matrix.SpecialLinearGroup.toGL).symm
          _ = (matTransvGroup w ψ).map
                (bmPSL_embedGL eidx P Pinv hPP hPinvP) := by
              rw [hH]
          _ = matTransvGroup v₀ φ₀ := by
              rw [bmPSL_embedGL_matTransvGroup]
              rw [← hv_eq, ← hφ_eq]

