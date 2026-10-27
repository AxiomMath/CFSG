module

public import CFSG.LocalAnalysis.StandardType.GGOuterInvFieldTags
public import CFSG.LocalAnalysis.StandardType.GGE0Frame
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockDefs
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockDict
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockGUOrder
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockDecomp
public import CFSG.Blueprint.SourceClassicalTransportOrthogonal
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256q
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaPlusFourShape
public import CFSG.RankThree.PartOne.S11d.OrthCaseN
public import CFSG.RankThree.PartOne.S11d.OrthSplitAbs
public import CFSG.RankThree.PartOne.KC.OrthogonalCommutatorBridge
public import CFSG.RankThree.GF2n.Smith81.OrthE1KFLinear
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3ProofModelL3
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoDualPair
public import CFSG.LocalAnalysis.StandardType.GGStructSOnePrimeRootCountOmega
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs141d2
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.StepA2
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockOmegaDecomp
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockOmegaIsoOneLinear
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockOmegaIsoUnitary
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.ClassicalGroups.SpecialLinear.InvariantForms
public import CFSG.ClassicalGroups.SpecialLinear.NaturalDualSum
public import CFSG.GroupTheory.HuppertProduct.Quotient
public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalClassical
public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalRows
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.SpTwo
public import CFSG.HardMathSupport.Solomon.Coordinator.L5Conj
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294KDOutTwE6
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaMinusPiecesEmbed
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualFRHigher
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualLeviGlue
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotUniqueGen
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtX1512DeltaA
public import CFSG.RankThree.GF2n.Smith81.EStmt
public import CFSG.RankThree.GF2n.Smith81.OrthE2Layer
public import CFSG.RankThree.GF2n.Smith81.TiLane
public import CFSG.RankThree.GF2n.Smith81.TiLemmaC
public import CFSG.RankThree.GF2n.Stroth80.Consumers
public import CFSG.RankThree.GF2n.Stroth80.Sec1110ModuleDual
public import CFSG.RankThree.GF2n.Stroth80.Sec11Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec310Main
public import CFSG.RankThree.GF2n.Stroth80.Sec45
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec5OmegaPoints
public import CFSG.RankThree.GF2n.Stroth80.Sec6Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec7EndDefs
public import CFSG.RankThree.GF2n.Stroth80.Sec7OmegaSign
public import CFSG.RankThree.GF2n.Stroth80.SpHomTrivial
public import CFSG.RankThree.GF2n.SupIndepDecomp
public import CFSG.RankThree.GF2n.Tim79CentC
public import CFSG.RankThree.GF2n.Tim79CentL
public import CFSG.RankThree.GF2n.Tim79Mod
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Gaschutz
public import Certificates.Certificate9530

public section

namespace CFSG.StandardType.ClassicalBlocks

open CFSG CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.StandardType.ClassicalPosition
  CFSG.StandardType.ClassicalBlocks Matrix
open Polynomial CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonal
open Classical

private abbrev ggOmW2_A {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] (b : GL ι K) :
    Subalgebra K (Matrix ι ι K) :=
  Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))

private abbrev ggOmW2_G {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Φ : QuadraticForm K (ι → K)) : Matrix ι ι K :=
  LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)

private abbrev ggOmW2_GramIso {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (G : Matrix ι ι K) (s : GL ι K) : Prop :=
  Matrix.transpose ((s : Matrix ι ι K).map (RingHom.id K)) * G * (s : Matrix ι ι K) = G

private lemma ggOmW2_eigDimOn_add {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {b e e' : Matrix ι ι K} (he : IsIdempotentElem e) (he' : IsIdempotentElem e')
    (hbe : b * e = e * b) (hbe' : b * e' = e' * b)
    (horth : e * e' = 0) (horth' : e' * e = 0) (l : AlgebraicClosure K) :
    eigDimOn b (e + e') l = eigDimOn b e l + eigDimOn b e' l := by
  classical
  let k := AlgebraicClosure K
  let φ : K →+* k := algebraMap K k
  let T : Module.End k (ι → k) := Matrix.toLin' (b.map φ)
  let E : Submodule k (ι → k) := Module.End.eigenspace T l
  let p : Module.End k (ι → k) := Matrix.toLin' (e.map φ)
  let q : Module.End k (ι → k) := Matrix.toLin' (e'.map φ)
  have hp : p * p = p := by
    show Matrix.toLin' (e.map φ) * Matrix.toLin' (e.map φ) = Matrix.toLin' (e.map φ)
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.map_mul, he.eq]
  have hq : q * q = q := by
    show Matrix.toLin' (e'.map φ) * Matrix.toLin' (e'.map φ) = Matrix.toLin' (e'.map φ)
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.map_mul, he'.eq]
  have hpq : p * q = 0 := by
    show Matrix.toLin' (e.map φ) * Matrix.toLin' (e'.map φ) = 0
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.map_mul, horth,
      Matrix.map_zero φ (map_zero φ)]
    simp
  have hqp : q * p = 0 := by
    show Matrix.toLin' (e'.map φ) * Matrix.toLin' (e.map φ) = 0
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.map_mul, horth',
      Matrix.map_zero φ (map_zero φ)]
    simp
  have hpT : p * T = T * p := by
    show Matrix.toLin' (e.map φ) * Matrix.toLin' (b.map φ) =
      Matrix.toLin' (b.map φ) * Matrix.toLin' (e.map φ)
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.toLin'_mul,
      ← Matrix.map_mul, ← Matrix.map_mul, hbe]
  have hqT : q * T = T * q := by
    show Matrix.toLin' (e'.map φ) * Matrix.toLin' (b.map φ) =
      Matrix.toLin' (b.map φ) * Matrix.toLin' (e'.map φ)
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.toLin'_mul,
      ← Matrix.map_mul, ← Matrix.map_mul, hbe']
  have hpmap : ∀ v ∈ E, p v ∈ E := by
    intro v hv
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    calc T (p v) = (T * p) v := (Module.End.mul_apply T p v).symm
      _ = (p * T) v := by rw [hpT]
      _ = p (T v) := Module.End.mul_apply p T v
      _ = p (l • v) := by rw [hv]
      _ = l • p v := p.map_smul l v
  have hqmap : ∀ v ∈ E, q v ∈ E := by
    intro v hv
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    calc T (q v) = (T * q) v := (Module.End.mul_apply T q v).symm
      _ = (q * T) v := by rw [hqT]
      _ = q (T v) := Module.End.mul_apply q T v
      _ = q (l • v) := by rw [hv]
      _ = l • q v := q.map_smul l v
  have hmain : E ⊓ LinearMap.range (p + q) =
      (E ⊓ LinearMap.range p) ⊔ (E ⊓ LinearMap.range q) := by
    apply le_antisymm
    · intro v hv
      obtain ⟨hvE, hvr⟩ := hv
      obtain ⟨w, rfl⟩ := hvr
      have hpw : p ((p + q) w) = p w := by
        rw [← Module.End.mul_apply, mul_add, hp, hpq, add_zero]
      have hqw : q ((p + q) w) = q w := by
        rw [← Module.End.mul_apply, mul_add, hqp, hq, zero_add]
      have hsplit : (p + q) w = p ((p + q) w) + q ((p + q) w) := by
        rw [hpw, hqw, LinearMap.add_apply]
      rw [hsplit]
      refine Submodule.add_mem _ (Submodule.mem_sup_left ⟨hpmap _ hvE, ⟨(p + q) w, ?_⟩⟩)
        (Submodule.mem_sup_right ⟨hqmap _ hvE, ⟨(p + q) w, ?_⟩⟩)
      · rfl
      · rfl
    · have hrp : LinearMap.range p ≤ LinearMap.range (p + q) := by
        rintro v ⟨w, rfl⟩
        exact ⟨p w, by
          rw [LinearMap.add_apply, ← Module.End.mul_apply q p w, hqp, LinearMap.zero_apply,
            add_zero, ← Module.End.mul_apply p p w, hp]⟩
      have hrq : LinearMap.range q ≤ LinearMap.range (p + q) := by
        rintro v ⟨w, rfl⟩
        exact ⟨q w, by
          rw [LinearMap.add_apply, ← Module.End.mul_apply p q w, hpq, LinearMap.zero_apply,
            zero_add, ← Module.End.mul_apply q q w, hq]⟩
      exact sup_le (le_inf inf_le_left (inf_le_right.trans hrp))
        (le_inf inf_le_left (inf_le_right.trans hrq))
  have hdisj : Disjoint (E ⊓ LinearMap.range p) (E ⊓ LinearMap.range q) := by
    rw [disjoint_iff_inf_le]
    intro v hv
    have hvp : v ∈ LinearMap.range p := hv.1.2
    have hvq : v ∈ LinearMap.range q := hv.2.2
    obtain ⟨x, hx⟩ := hvp
    obtain ⟨y, hy⟩ := hvq
    rw [Submodule.mem_bot, ← hx]
    have h1 : q (p x) = p x := by
      have hpx : p x = q y := by rw [hx, ← hy]
      rw [hpx, ← Module.End.mul_apply, hq]
    have h2 : q (p x) = 0 := by
      rw [← Module.End.mul_apply, hqp, LinearMap.zero_apply]
    rw [← h1, h2]
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq (E ⊓ LinearMap.range p)
    (E ⊓ LinearMap.range q)
  rw [hdisj.eq_bot, finrank_bot, add_zero] at hsup
  have hmap : (e + e').map φ = e.map φ + e'.map φ := Matrix.map_add φ φ.map_add e e'
  have hlin : Matrix.toLin' ((e + e').map φ) = p + q := by
    rw [hmap]
    exact map_add Matrix.toLin' _ _
  unfold eigDimOn
  rw [hlin, hmain]
  exact hsup

private lemma ggOmW2_finrank_range_add {k V : Type} [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (p q : Module.End k V) (hp : p * p = p) (hq : q * q = q)
    (hpq : p * q = 0) (hqp : q * p = 0) :
    Module.finrank k (LinearMap.range (p + q)) =
      Module.finrank k (LinearMap.range p) + Module.finrank k (LinearMap.range q) := by
  have hrange : LinearMap.range (p + q) = LinearMap.range p ⊔ LinearMap.range q := by
    apply le_antisymm
    · rintro v ⟨w, rfl⟩
      rw [LinearMap.add_apply]
      exact Submodule.add_mem _
        (Submodule.mem_sup_left (show p w ∈ LinearMap.range p from ⟨w, rfl⟩))
        (Submodule.mem_sup_right (show q w ∈ LinearMap.range q from ⟨w, rfl⟩))
    · apply sup_le
      · rintro v ⟨w, rfl⟩
        refine ⟨p w, ?_⟩
        rw [LinearMap.add_apply, ← Module.End.mul_apply q p w, hqp, LinearMap.zero_apply,
          add_zero, ← Module.End.mul_apply p p w, hp]
      · rintro v ⟨w, rfl⟩
        refine ⟨q w, ?_⟩
        rw [LinearMap.add_apply, ← Module.End.mul_apply p q w, hpq, LinearMap.zero_apply,
          zero_add, ← Module.End.mul_apply q q w, hq]
  have hbot : LinearMap.range p ⊓ LinearMap.range q = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_bot]
    obtain ⟨x, hx⟩ := hv.1
    obtain ⟨y, hy⟩ := hv.2
    have h1 : q (p x) = p x := by
      have hpx : p x = q y := by rw [hx, ← hy]
      rw [hpx, ← Module.End.mul_apply, hq]
    have h2 : q (p x) = 0 := by
      rw [← Module.End.mul_apply, hqp, LinearMap.zero_apply]
    rw [← hx, ← h1, h2]
  rw [hrange]
  have h := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range p) (LinearMap.range q)
  rw [hbot, finrank_bot, add_zero] at h
  exact h

private lemma ggOmW2_finrank_range_add_matrix {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {e e' : Matrix ι ι K} (he : IsIdempotentElem e) (he' : IsIdempotentElem e')
    (horth : e * e' = 0) (horth' : e' * e = 0) :
    Module.finrank K (LinearMap.range (Matrix.toLin' (e + e'))) =
      Module.finrank K (LinearMap.range (Matrix.toLin' e)) +
        Module.finrank K (LinearMap.range (Matrix.toLin' e')) := by
  have hp : Matrix.toLin' e * Matrix.toLin' e = Matrix.toLin' e := by
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, he.eq]
  have hq : Matrix.toLin' e' * Matrix.toLin' e' = Matrix.toLin' e' := by
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, he'.eq]
  have hpq : Matrix.toLin' e * Matrix.toLin' e' = 0 := by
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, horth]
    exact map_zero Matrix.toLin'
  have hqp : Matrix.toLin' e' * Matrix.toLin' e = 0 := by
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, horth']
    exact map_zero Matrix.toLin'
  have hsum : Matrix.toLin' (e + e') = Matrix.toLin' e + Matrix.toLin' e' := map_add _ _ _
  rw [hsum]
  exact ggOmW2_finrank_range_add _ _ hp hq hpq hqp

private lemma ggOmW2_map_pow {ι K L : Type} [Fintype ι] [DecidableEq ι] [Semiring K]
    [Semiring L] (φ : K →+* L) (M : Matrix ι ι K) (n : ℕ) :
    (M ^ n).map φ = (M.map φ) ^ n := by
  have h := map_pow (RingHom.mapMatrix φ) M n
  simpa only [RingHom.mapMatrix_apply] using h

private lemma ggOmW2_isSemisimple {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (M : Matrix ι ι K) (n : ℕ) (hn : (n : AlgebraicClosure K) ≠ 0) (hM : M ^ n = 1) :
    Module.End.IsSemisimple (Matrix.toLin' (M.map (algebraMap K (AlgebraicClosure K)))) := by
  have hfpow : (Matrix.toLin' (M.map (algebraMap K (AlgebraicClosure K)))) ^ n = 1 := by
    have h1 : (M ^ n).map (algebraMap K (AlgebraicClosure K)) = 1 := by
      rw [hM]
      exact map_one (RingHom.mapMatrix (algebraMap K (AlgebraicClosure K)))
    rw [← Matrix.toLin'_pow, ← ggOmW2_map_pow, h1]
    exact map_one (Matrix.toLinAlgEquiv' (R := AlgebraicClosure K) (n := ι))
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    (p := (Polynomial.X : Polynomial (AlgebraicClosure K)) ^ n - 1) ?_ ?_
  · exact (Polynomial.X_pow_sub_one_separable_iff.mpr hn).squarefree
  · simpa [Polynomial.aeval_X, hfpow]

private lemma ggOmW2_eigDim_eq_rootMultiplicity {ι K : Type} [Fintype ι] [DecidableEq ι]
    [Field K] (M : Matrix ι ι K) (n : ℕ) (hn : (n : AlgebraicClosure K) ≠ 0)
    (hM : M ^ n = 1) (l : AlgebraicClosure K) :
    eigDim M l = ((M.charpoly).map (algebraMap K (AlgebraicClosure K))).rootMultiplicity l := by
  have hf : Module.End.IsSemisimple
      (Matrix.toLin' (M.map (algebraMap K (AlgebraicClosure K)))) :=
    ggOmW2_isSemisimple M n hn hM
  have hchar : (Matrix.toLin' (M.map (algebraMap K (AlgebraicClosure K)))).charpoly =
      (M.charpoly).map (algebraMap K (AlgebraicClosure K)) := by
    rw [Matrix.charpoly_toLin', Matrix.charpoly_map]
  unfold eigDim
  rw [← hchar, ← LinearMap.finrank_maxGenEigenspace_eq,
    Module.End.IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace
      (Module.End.IsSemisimple.isFinitelySemisimple hf) l]

private lemma ggOmW2_eigDim_ne_zero_iff_mem_roots {ι K : Type} [Fintype ι] [DecidableEq ι]
    [Field K] (b : Matrix ι ι K) {n : ℕ} (hn : (n : AlgebraicClosure K) ≠ 0)
    (hM : b ^ n = 1) {l : AlgebraicClosure K} :
    eigDim b l ≠ 0 ↔ l ∈ (b.charpoly.map (algebraMap K (AlgebraicClosure K))).roots := by
  classical
  have hp : ((b.charpoly).map (algebraMap K (AlgebraicClosure K))) ≠ 0 :=
    ((Matrix.charpoly_monic b).map (algebraMap K (AlgebraicClosure K))).ne_zero
  rw [ggOmW2_eigDim_eq_rootMultiplicity b n hn hM l, Polynomial.mem_roots hp]
  exact ⟨fun h => (Polynomial.rootMultiplicity_pos hp).mp (Nat.pos_of_ne_zero h),
    fun h => (Polynomial.rootMultiplicity_pos hp).mpr h |>.ne'⟩

private lemma ggOmW2_eigDimOn_le_eigDim {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (b e : Matrix ι ι K) (l : AlgebraicClosure K) : eigDimOn b e l ≤ eigDim b l := by
  unfold eigDimOn eigDim
  exact Submodule.finrank_mono inf_le_left

private lemma ggOmW2_matrix_pow_orderOf {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (b : GL ι K) : (b : Matrix ι ι K) ^ orderOf b = 1 := by
  rw [← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one]

private lemma ggOmW2_cast_orderOf_ne_zero {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [CharP K 2] {b : GL ι K} (hodd : Odd (orderOf b)) :
    (orderOf b : AlgebraicClosure K) ≠ 0 := by
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  intro h0
  have h2 : (2 : ℕ) ∣ orderOf b :=
    (CharP.cast_eq_zero_iff (AlgebraicClosure K) 2 (orderOf b)).mp h0
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

private lemma ggOmW2_finrank_range_toLin'_ne_zero {K : Type} [Field K] {m : Type}
    [Fintype m] [DecidableEq m] {e : Matrix m m K} (he : e ≠ 0) :
    Module.finrank K (LinearMap.range (Matrix.toLin' e)) ≠ 0 := by
  intro h0
  haveI : Subsingleton ↥(LinearMap.range (Matrix.toLin' e)) := (Module.finrank_zero_iff).mp h0
  have hbot : LinearMap.range (Matrix.toLin' e) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    exact congrArg Subtype.val (Subsingleton.elim
      (⟨v, hv⟩ : ↥(LinearMap.range (Matrix.toLin' e))) ⟨0, Submodule.zero_mem _⟩)
  rw [LinearMap.range_eq_bot] at hbot
  exact he (Matrix.toLin'.injective (hbot.trans (map_zero Matrix.toLin').symm))

private lemma ggOmW2_rank_eq_finrank_range_toLin' {F : Type} [Field F] {m n : Type}
    [Fintype m] [Fintype n] [DecidableEq n] (M : Matrix m n F) :
    M.rank = Module.finrank F (LinearMap.range (Matrix.toLin' M)) := by
  rw [Matrix.rank_eq_finrank_range_toLin M (Pi.basisFun F m) (Pi.basisFun F n),
    Matrix.toLin_eq_toLin']

private lemma ggOmW2_rank_fromBlocks_one_zero {F : Type} [Field F] {r s : ℕ} :
    (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) F) 0 0
      (0 : Matrix (Fin s) (Fin s) F)).rank = r := by
  classical
  have h : (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) F) 0 0
      (0 : Matrix (Fin s) (Fin s) F)) =
      diagonal (Sum.elim (fun _ : Fin r => (1 : F)) (fun _ : Fin s => (0 : F))) := by
    rw [← Matrix.fromBlocks_diagonal, Matrix.diagonal_one, Matrix.diagonal_zero]
  rw [h, Matrix.rank_diagonal, Fintype.card_subtype, Finset.card_filter, Fintype.sum_sum_type]
  simp

private lemma ggOmW2_rank_map_eq {F E : Type} [Field F] [Field E] {m : Type} [Fintype m]
    [DecidableEq m] (f : F →+* E) (M : Matrix m m F) : (M.map f).rank = M.rank := by
  classical
  obtain ⟨V, U, e, hV, hU, h⟩ := Matrix.exists_rank_normal_form M
  have hVf : IsUnit (V.map f).det := (isUnit_iff_isUnit_det _).mp (hV.map f.mapMatrix)
  have hUf : IsUnit (U.map f).det := (isUnit_iff_isUnit_det _).mp (hU.map f.mapMatrix)
  have hE : (M.map f).rank = ((V.map f) * (M.map f) * (U.map f)).rank := by
    rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hUf,
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ hVf]
  have h1 : (V * M * U).map f = ((Matrix.fromBlocks
      (1 : Matrix (Fin M.rank) (Fin M.rank) F) 0 0
      (0 : Matrix (Fin (Fintype.card m - M.rank)) (Fin (Fintype.card m - M.rank)) F)).submatrix
        e e).map f := by rw [h]
  simp only [Matrix.map_mul, ← Matrix.submatrix_map, Matrix.fromBlocks_map,
    Matrix.map_one _ (map_zero f) (map_one f), Matrix.map_zero _ (map_zero f)] at h1
  rw [hE, h1, Matrix.rank_submatrix]
  exact ggOmW2_rank_fromBlocks_one_zero

private lemma ggOmW2_finrank_range_map {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (e : Matrix ι ι K) :
    Module.finrank (AlgebraicClosure K)
        (LinearMap.range (Matrix.toLin' (e.map (algebraMap K (AlgebraicClosure K))))) =
      Module.finrank K (LinearMap.range (Matrix.toLin' e)) := by
  rw [← ggOmW2_rank_eq_finrank_range_toLin' (e.map (algebraMap K (AlgebraicClosure K))),
    ← ggOmW2_rank_eq_finrank_range_toLin' e]
  exact ggOmW2_rank_map_eq (algebraMap K (AlgebraicClosure K)) e

private noncomputable def ggOmW2_R {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (b : Matrix ι ι K) : Finset (AlgebraicClosure K) :=
  haveI := Classical.decEq (AlgebraicClosure K)
  ((b.charpoly.map (algebraMap K (AlgebraicClosure K))).roots.toFinset).erase 1

private lemma ggOmW2_blockExp_true_eq {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (b : Matrix ι ι K) :
    blockExp true b = (eigDim b 1 / 2) * (eigDim b 1 / 2 - 1) +
      (∑ l ∈ ggOmW2_R b, eigDim b l * (eigDim b l - 1) / 2) / 2 := by
  classical
  simp only [blockExp, ggOmW2_R]
  simp

private lemma ggOmW2_eigDimOn_eq_zero_of_b_mul_eq {ι K : Type} [Fintype ι] [DecidableEq ι]
    [Field K] [Finite K] [CharP K 2] {b : GL ι K} (hodd : Odd (orderOf b))
    {e : Matrix ι ι K}
    (he : IsPrimIdemIn (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) e)
    (h1 : (b : Matrix ι ι K) * e = e) {l : AlgebraicClosure K} (hl : l ≠ 1) :
    eigDimOn (b : Matrix ι ι K) e l = 0 := by
  classical
  have hd := (eigDimOn_one_of_isPrimIdemIn (K := K) hodd he).1 h1
  have hd' : Module.finrank (AlgebraicClosure K)
        ↥(Module.End.eigenspace
          (Matrix.toLin' ((b : Matrix ι ι K).map (algebraMap K (AlgebraicClosure K)))) 1 ⊓
          LinearMap.range (Matrix.toLin' (e.map (algebraMap K (AlgebraicClosure K))))) =
      Module.finrank (AlgebraicClosure K)
        ↥(LinearMap.range (Matrix.toLin' (e.map (algebraMap K (AlgebraicClosure K))))) := by
    unfold eigDimOn at hd
    rw [hd, ggOmW2_finrank_range_map e]
  have hrange : LinearMap.range (Matrix.toLin' (e.map (algebraMap K (AlgebraicClosure K)))) ≤
      Module.End.eigenspace
        (Matrix.toLin' ((b : Matrix ι ι K).map (algebraMap K (AlgebraicClosure K)))) 1 := by
    have heq : Module.End.eigenspace
          (Matrix.toLin' ((b : Matrix ι ι K).map (algebraMap K (AlgebraicClosure K)))) 1 ⊓
          LinearMap.range (Matrix.toLin' (e.map (algebraMap K (AlgebraicClosure K)))) =
        LinearMap.range (Matrix.toLin' (e.map (algebraMap K (AlgebraicClosure K)))) :=
      Submodule.eq_of_le_of_finrank_eq inf_le_right hd'
    exact heq ▸ inf_le_left
  unfold eigDimOn
  have hbot : Module.End.eigenspace
        (Matrix.toLin' ((b : Matrix ι ι K).map (algebraMap K (AlgebraicClosure K)))) l ⊓
        LinearMap.range (Matrix.toLin' (e.map (algebraMap K (AlgebraicClosure K)))) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    obtain ⟨hvE, hvR⟩ := hv
    have hv1 : v ∈ Module.End.eigenspace
        (Matrix.toLin' ((b : Matrix ι ι K).map (algebraMap K (AlgebraicClosure K)))) 1 :=
      hrange hvR
    rw [Module.End.mem_eigenspace_iff] at hv1
    have hvE' : Matrix.toLin' ((b : Matrix ι ι K).map (algebraMap K (AlgebraicClosure K))) v =
        l • v := Module.End.mem_eigenspace_iff.mp hvE
    have h0 : (l - 1) • v = 0 := by
      rw [sub_smul, one_smul, ← hvE', hv1, one_smul, sub_self]
    rcases smul_eq_zero.mp h0 with h | h
    · exact absurd (sub_eq_zero.mp h) hl
    · exact h
  rw [hbot, finrank_bot]

private lemma ggOmW2_G_isUnit {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) :
    IsUnit (ggOmW2_G Φ).det := by
  have hEqB : Matrix.toLinearMap₂' K (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      = QuadraticMap.polarBilin Φ := by
    rw [show LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)
      = LinearMap.BilinForm.toMatrix' (QuadraticMap.polarBilin Φ) from rfl]
    exact Matrix.toLinearMap₂'_toMatrix' _
  have hJnd : (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)).Nondegenerate := by
    refine ⟨Matrix.separatingLeft_def.mpr fun v hv => ?_,
      Matrix.separatingRight_def.mpr fun w hw => ?_⟩
    · apply hΦ.1 v
      intro w
      have h := hv w
      rwa [← Matrix.toLinearMap₂'_apply' (M := LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)),
        hEqB] at h
    · apply hΦ.2 w
      intro v
      have h := hw v
      rwa [← Matrix.toLinearMap₂'_apply' (M := LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)),
        hEqB] at h
  exact isUnit_iff_ne_zero.mpr (Matrix.nondegenerate_iff_det_ne_zero.mp hJnd)

private lemma ggOmW2_G_transpose {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Φ : QuadraticForm K (ι → K)) :
    Matrix.transpose ((ggOmW2_G Φ).map (RingHom.id K)) = ggOmW2_G Φ := by
  unfold ggOmW2_G
  rw [show (⇑(RingHom.id K) : K → K) = id from rfl, Matrix.map_id]
  ext i j
  rw [Matrix.transpose_apply, LinearMap.toMatrix₂'_apply, LinearMap.toMatrix₂'_apply]
  exact QuadraticMap.polar_comm Φ (Pi.single j 1) (Pi.single i 1)

private lemma ggOmW2_gram {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Φ : QuadraticForm K (ι → K)) {b : GL ι K} (hb : b ∈ StatedOmega ⇑Φ) :
    ggOmW2_GramIso (ggOmW2_G Φ) b := by
  have hg : ∀ v : ι → K, Φ ((b : Matrix ι ι K) *ᵥ v) = Φ v :=
    fun v => CFSG.RankThree.GF2n.Smith81.Smith23E1.KFLin.isometry_of_mem_statedOmega hb v
  have h := CFSG.RankThree.GF2n.Smith81.Smith23E1.KFLin.gram_invariant (Q := Φ) hg
  simpa [ggOmW2_GramIso, ggOmW2_G,
    CFSG.RankThree.GF2n.Smith81.Smith23E1.KFLin.polarGram_eq_toMatrix₂',
    Matrix.map_id] using h

private lemma ggOmW2_commute {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (b : GL ι K) {x y : Matrix ι ι K} (hx : x ∈ ggOmW2_A b) (hy : y ∈ ggOmW2_A b) :
    x * y = y * x := by
  let A : Subalgebra K (Matrix ι ι K) := ggOmW2_A b
  have hcommP : (Units.val '' ({b} : Set (GL ι K)) :
      Set (Matrix ι ι K)).Pairwise Commute := by
    rintro x ⟨s, hs, rfl⟩ y ⟨t, ht, rfl⟩ _
    rw [Set.mem_singleton_iff] at hs ht
    subst hs
    subst ht
    exact Commute.refl _
  letI : CommRing A := Algebra.adjoinCommRingOfComm K hcommP
  have h := mul_comm (⟨x, hx⟩ : A) (⟨y, hy⟩ : A)
  exact congrArg Subtype.val h

private lemma ggOmW2_formAdj_mem {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Finite K]
    {G : Matrix ι ι K} (hG : IsUnit G.det) {b : GL ι K} (hgram : ggOmW2_GramIso G b)
    {a : Matrix ι ι K} (ha : a ∈ ggOmW2_A b) :
    formAdj (RingHom.id K) G a ∈ ggOmW2_A b := by
  refine CFSG.StandardType.ClassicalPosition.Geo.formAdj_mem_adjoin (RingHom.id K)
    hG (S := {b}) ?_ ha
  intro s hs
  rw [Set.mem_singleton_iff] at hs
  rw [hs]
  exact hgram

private lemma ggOmW2_formAdj_idem {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {G : Matrix ι ι K} (hG : IsUnit G.det) {e : Matrix ι ι K}
    (he : IsIdempotentElem e) : IsIdempotentElem (formAdj (RingHom.id K) G e) := by
  have h : formAdj (RingHom.id K) G (e * e) =
      formAdj (RingHom.id K) G e * formAdj (RingHom.id K) G e :=
    CFSG.StandardType.ClassicalPosition.Geo.formAdj_mul (RingHom.id K) hG e e
  rw [isIdempotentElem_iff] at he ⊢
  rw [he] at h
  exact h.symm

private lemma ggOmW2_formAdj_zero {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (G : Matrix ι ι K) : formAdj (RingHom.id K) G 0 = 0 := by
  simp [formAdj]

private lemma ggOmW2_formAdj_invol {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {G : Matrix ι ι K} (hG : IsUnit G.det)
    (hgsym : Matrix.transpose (G.map (RingHom.id K)) = G) (a : Matrix ι ι K) :
    formAdj (RingHom.id K) G (formAdj (RingHom.id K) G a) = a :=
  CFSG.StandardType.ClassicalPosition.Geo.formAdj_formAdj (RingHom.id K) (fun x => rfl) hG hgsym a

private lemma ggOmW2_formAdj_prim {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Finite K]
    {G : Matrix ι ι K} (hG : IsUnit G.det)
    (hgsym : Matrix.transpose (G.map (RingHom.id K)) = G) {b : GL ι K}
    (hgram : ggOmW2_GramIso G b) {e : Matrix ι ι K} (he : IsPrimIdemIn (ggOmW2_A b) e) :
    IsPrimIdemIn (ggOmW2_A b) (formAdj (RingHom.id K) G e) := by
  have hmem := ggOmW2_formAdj_mem hG hgram he.1
  have hidem := ggOmW2_formAdj_idem hG he.2.1
  have hne : formAdj (RingHom.id K) G e ≠ 0 := by
    intro h0
    have h := congrArg (formAdj (RingHom.id K) G) h0
    rw [ggOmW2_formAdj_invol hG hgsym e, ggOmW2_formAdj_zero] at h
    exact he.2.2.1 h
  refine ⟨hmem, hidem, hne, ?_⟩
  intro f hfA hfid hfe
  have hfmem := ggOmW2_formAdj_mem hG hgram hfA
  have hfidem := ggOmW2_formAdj_idem hG hfid
  have hkey : formAdj (RingHom.id K) G f * e = formAdj (RingHom.id K) G f := by
    have h : e * formAdj (RingHom.id K) G f = formAdj (RingHom.id K) G f := by
      have h := congrArg (formAdj (RingHom.id K) G) hfe
      rw [CFSG.StandardType.ClassicalPosition.Geo.formAdj_mul (RingHom.id K) hG f
        (formAdj (RingHom.id K) G e),
        ggOmW2_formAdj_invol hG hgsym e] at h
      exact h
    exact (ggOmW2_commute b hfmem he.1).trans h
  rcases he.2.2.2 (formAdj (RingHom.id K) G f) hfmem hfidem hkey with h0 | hee
  · left
    have h := congrArg (formAdj (RingHom.id K) G) h0
    rw [ggOmW2_formAdj_invol hG hgsym f, ggOmW2_formAdj_zero] at h
    exact h
  · right
    have h := congrArg (formAdj (RingHom.id K) G) hee
    rw [ggOmW2_formAdj_invol hG hgsym f] at h
    exact h

private lemma ggOmW2_prim_orthogonal {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (b : GL ι K) {e e' : Matrix ι ι K} (he : IsPrimIdemIn (ggOmW2_A b) e)
    (he' : IsPrimIdemIn (ggOmW2_A b) e') (hne : e ≠ e') : e * e' = 0 := by
  have hA : ∀ x ∈ ggOmW2_A b, ∀ y ∈ ggOmW2_A b, x * y = y * x :=
    fun x hx y hy => ggOmW2_commute b hx hy
  have hfA : e * e' ∈ ggOmW2_A b := (ggOmW2_A b).mul_mem he.1 he'.1
  have hfid : IsIdempotentElem (e * e') := by
    rw [isIdempotentElem_iff]
    calc (e * e') * (e * e') = e * (e' * (e * e')) := by rw [mul_assoc]
      _ = e * ((e' * e) * e') := by rw [mul_assoc]
      _ = e * ((e * e') * e') := by rw [hA e' he'.1 e he.1]
      _ = e * (e * (e' * e')) := by rw [mul_assoc]
      _ = (e * e) * (e' * e') := by rw [mul_assoc]
      _ = e * e' := by rw [he.2.1.eq, he'.2.1.eq]
  have hfe : (e * e') * e = e * e' := by
    rw [mul_assoc, hA e' he'.1 e he.1, ← mul_assoc, he.2.1.eq]
  have hfe' : (e * e') * e' = e * e' := by
    rw [mul_assoc, he'.2.1.eq]
  rcases he.2.2.2 (e * e') hfA hfid hfe with h0 | hee
  · exact h0
  · rcases he'.2.2.2 (e * e') hfA hfid hfe' with h0 | hee'
    · exact h0
    · exact absurd (hee.symm.trans hee') hne

private lemma ggOmW2_isUnit_det_inv {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {G : Matrix ι ι K} (hG : IsUnit G.det) : IsUnit (G⁻¹).det :=
  (Matrix.isUnit_iff_isUnit_det (G⁻¹)).mp (by
    rw [isUnit_iff_exists_inv]
    exact ⟨G, Matrix.nonsing_inv_mul G hG⟩)

private lemma ggOmW2_finrank_range_formAdj {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {G : Matrix ι ι K} (hG : IsUnit G.det) (e : Matrix ι ι K) :
    Module.finrank K (LinearMap.range (Matrix.toLin' (formAdj (RingHom.id K) G e))) =
      Module.finrank K (LinearMap.range (Matrix.toLin' e)) := by
  have hmid : e.map (RingHom.id K) = e := by
    ext i j
    rfl
  rw [← ggOmW2_rank_eq_finrank_range_toLin' (formAdj (RingHom.id K) G e),
    ← ggOmW2_rank_eq_finrank_range_toLin' e]
  unfold formAdj
  rw [hmid, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hG,
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ (ggOmW2_isUnit_det_inv hG),
    Matrix.rank_transpose]

private noncomputable def ggOmW2_formAdjLin {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (G : Matrix ι ι K) : Matrix ι ι K →ₗ[K] Matrix ι ι K where
  toFun := formAdj (RingHom.id K) G
  map_add' := fun a b => CFSG.StandardType.ClassicalPosition.Geo.formAdj_add _ _ _ _
  map_smul' := fun c a => by
    rw [CFSG.StandardType.ClassicalPosition.Geo.formAdj_smul]

private noncomputable def ggOmW2_formAdjEquiv {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {G : Matrix ι ι K} (hG : IsUnit G.det)
    (hgsym : Matrix.transpose (G.map (RingHom.id K)) = G) :
    Matrix ι ι K ≃ₗ[K] Matrix ι ι K :=
  LinearEquiv.ofBijective (ggOmW2_formAdjLin G) (by
    constructor
    · intro a b hab
      have h := congrArg (formAdj (RingHom.id K) G) hab
      rw [show ggOmW2_formAdjLin G a = formAdj (RingHom.id K) G a from rfl,
        show ggOmW2_formAdjLin G b = formAdj (RingHom.id K) G b from rfl] at h
      rwa [ggOmW2_formAdj_invol hG hgsym a, ggOmW2_formAdj_invol hG hgsym b] at h
    · intro a
      exact ⟨formAdj (RingHom.id K) G a, ggOmW2_formAdj_invol hG hgsym a⟩)

private lemma ggOmW2_blockDegree_formAdj {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Finite K] {G : Matrix ι ι K} (hG : IsUnit G.det)
    (hgsym : Matrix.transpose (G.map (RingHom.id K)) = G) {b : GL ι K}
    (hgram : ggOmW2_GramIso G b) {e : Matrix ι ι K} (he : e ∈ ggOmW2_A b) :
    blockDegree (ggOmW2_A b) (formAdj (RingHom.id K) G e) = blockDegree (ggOmW2_A b) e := by
  let F : Matrix ι ι K ≃ₗ[K] Matrix ι ι K :=
    { toFun := formAdj (RingHom.id K) G
      invFun := formAdj (RingHom.id K) G
      map_add' := fun a b =>
        CFSG.StandardType.ClassicalPosition.Geo.formAdj_add (RingHom.id K) G a b
      map_smul' := fun c a =>
        CFSG.StandardType.ClassicalPosition.Geo.formAdj_smul (RingHom.id K) G c a
      left_inv := fun a => ggOmW2_formAdj_invol hG hgsym a
      right_inv := fun a => ggOmW2_formAdj_invol hG hgsym a }
  have hmemE : formAdj (RingHom.id K) G e ∈ ggOmW2_A b :=
    ggOmW2_formAdj_mem hG hgram he
  have hS : (Subalgebra.toSubmodule (ggOmW2_A b)).map
        (LinearMap.mulRight K (formAdj (RingHom.id K) G e)) =
      ((Subalgebra.toSubmodule (ggOmW2_A b)).map (LinearMap.mulRight K e)).map
        F.toLinearMap := by
    ext x
    simp only [Submodule.mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨formAdj (RingHom.id K) G a * e,
        ⟨formAdj (RingHom.id K) G a, ggOmW2_formAdj_mem hG hgram ha, rfl⟩, ?_⟩
      show F (formAdj (RingHom.id K) G a * e) = a * formAdj (RingHom.id K) G e
      change formAdj (RingHom.id K) G (formAdj (RingHom.id K) G a * e) =
        a * formAdj (RingHom.id K) G e
      rw [CFSG.StandardType.ClassicalPosition.Geo.formAdj_mul (RingHom.id K) hG,
        ggOmW2_formAdj_invol hG hgsym a]
      exact ggOmW2_commute b hmemE ha
    · rintro ⟨y, ⟨a, ha, rfl⟩, rfl⟩
      refine ⟨formAdj (RingHom.id K) G a, ggOmW2_formAdj_mem hG hgram ha, ?_⟩
      show formAdj (RingHom.id K) G a * formAdj (RingHom.id K) G e =
        F (a * e)
      change formAdj (RingHom.id K) G a * formAdj (RingHom.id K) G e =
        formAdj (RingHom.id K) G (a * e)
      rw [CFSG.StandardType.ClassicalPosition.Geo.formAdj_mul (RingHom.id K) hG]
      exact ggOmW2_commute b (ggOmW2_formAdj_mem hG hgram ha) hmemE
  unfold blockDegree
  rw [hS]
  exact LinearEquiv.finrank_map_eq F _

private lemma ggOmW2_exists_prim {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] {G : Matrix ι ι K} (hG : IsUnit G.det)
    (hgsym : Matrix.transpose (G.map (RingHom.id K)) = G) {b : GL ι K}
    (hgram : ggOmW2_GramIso G b) {ε : Matrix ι ι K}
    (hε : IsPrimAdjIdemIn (RingHom.id K) G (ggOmW2_A b) ε) :
    ∃ e, IsPrimIdemIn (ggOmW2_A b) e ∧ e * ε = e ∧
      (e = ε ∨ (e ≠ ε ∧ formAdj (RingHom.id K) G e ≠ e ∧
        ε = e + formAdj (RingHom.id K) G e)) := by
  refine exists_isPrimIdemIn_of_isPrimAdjIdemIn (RingHom.id K) (fun x => rfl) hG hgsym
    (S := {b}) ?_ ?_ hε
  · intro s hs s' hs'
    rw [Set.mem_singleton_iff] at hs hs'
    rw [hs, hs']
  · intro s hs
    rw [Set.mem_singleton_iff] at hs
    rw [hs]
    exact hgram

private lemma ggOmW2c_formAdj_formAdj_mem {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {G : Matrix ι ι K} (hG : IsUnit G.det) {b : GL ι K}
    (hgram : ggOmW2_GramIso G b) {a : Matrix ι ι K} (ha : a ∈ ggOmW2_A b) :
    formAdj (RingHom.id K) G (formAdj (RingHom.id K) G a) = a := by
  refine Algebra.adjoin_induction
    (p := fun x _ => formAdj (RingHom.id K) G (formAdj (RingHom.id K) G x) = x)
    ?_ ?_ ?_ ?_ ha
  · rintro x ⟨s, hs, rfl⟩
    rw [Set.mem_singleton_iff] at hs
    rw [hs]
    have hfs : formAdj (RingHom.id K) G (b : Matrix ι ι K) =
        ((b⁻¹ : GL ι K) : Matrix ι ι K) :=
      CFSG.StandardType.ClassicalPosition.Geo.formAdj_eq_inv_of_isometry (RingHom.id K) hG b hgram
    have hprod : formAdj (RingHom.id K) G ((b⁻¹ : GL ι K) : Matrix ι ι K) *
        formAdj (RingHom.id K) G (b : Matrix ι ι K) = 1 := by
      rw [← CFSG.StandardType.ClassicalPosition.Geo.formAdj_mul (RingHom.id K) hG
        (b : Matrix ι ι K) ((b⁻¹ : GL ι K) : Matrix ι ι K)]
      rw [show (b : Matrix ι ι K) * ((b⁻¹ : GL ι K) : Matrix ι ι K) = 1 from by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]]
      exact CFSG.StandardType.ClassicalPosition.Geo.formAdj_one (RingHom.id K) hG
    rw [hfs] at hprod
    rw [hfs]
    calc formAdj (RingHom.id K) G ((b⁻¹ : GL ι K) : Matrix ι ι K)
        = formAdj (RingHom.id K) G ((b⁻¹ : GL ι K) : Matrix ι ι K) * 1 :=
          (mul_one _).symm
      _ = formAdj (RingHom.id K) G ((b⁻¹ : GL ι K) : Matrix ι ι K) *
            (((b⁻¹ : GL ι K) : Matrix ι ι K) * (b : Matrix ι ι K)) := by
            rw [show ((b⁻¹ : GL ι K) : Matrix ι ι K) * (b : Matrix ι ι K) = 1 from by
              rw [← Units.val_mul, inv_mul_cancel, Units.val_one]]
      _ = (formAdj (RingHom.id K) G ((b⁻¹ : GL ι K) : Matrix ι ι K) *
            ((b⁻¹ : GL ι K) : Matrix ι ι K)) * (b : Matrix ι ι K) := by rw [mul_assoc]
      _ = 1 * (b : Matrix ι ι K) := by rw [hprod]
      _ = (b : Matrix ι ι K) := one_mul _
  · intro r
    rw [Algebra.algebraMap_eq_smul_one]
    rw [CFSG.StandardType.ClassicalPosition.Geo.formAdj_smul,
      CFSG.StandardType.ClassicalPosition.Geo.formAdj_one (RingHom.id K) hG]
    rw [CFSG.StandardType.ClassicalPosition.Geo.formAdj_smul,
      CFSG.StandardType.ClassicalPosition.Geo.formAdj_one (RingHom.id K) hG]
    rfl
  · intro x y _ _ hx hy
    rw [CFSG.StandardType.ClassicalPosition.Geo.formAdj_add,
      CFSG.StandardType.ClassicalPosition.Geo.formAdj_add, hx, hy]
  · intro x y _ _ hx hy
    rw [CFSG.StandardType.ClassicalPosition.Geo.formAdj_mul (RingHom.id K) hG,
      CFSG.StandardType.ClassicalPosition.Geo.formAdj_mul (RingHom.id K) hG, hx, hy]

private lemma ggOmW2_b_mul_formAdj_iff {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Finite K] {G : Matrix ι ι K} (hG : IsUnit G.det) {b : GL ι K}
    (hgram : ggOmW2_GramIso G b) {e : Matrix ι ι K} (he : e ∈ ggOmW2_A b) :
    (b : Matrix ι ι K) * formAdj (RingHom.id K) G e = formAdj (RingHom.id K) G e ↔
      (b : Matrix ι ι K) * e = e := by
  have hbA : (b : Matrix ι ι K) ∈ ggOmW2_A b := Algebra.subset_adjoin (by simp)
  have hmemE : formAdj (RingHom.id K) G e ∈ ggOmW2_A b :=
    ggOmW2_formAdj_mem hG hgram he
  have hfinv : formAdj (RingHom.id K) G (b : Matrix ι ι K) =
      ((b⁻¹ : GL ι K) : Matrix ι ι K) :=
    CFSG.StandardType.ClassicalPosition.Geo.formAdj_eq_inv_of_isometry (RingHom.id K) hG b hgram
  constructor
  · intro h
    have h1 := congrArg (formAdj (RingHom.id K) G) h
    rw [CFSG.StandardType.ClassicalPosition.Geo.formAdj_mul (RingHom.id K) hG
        (b : Matrix ι ι K) (formAdj (RingHom.id K) G e),
      ggOmW2c_formAdj_formAdj_mem hG hgram he, hfinv] at h1
    have h3 : e * (b : Matrix ι ι K) = e := by
      calc e * (b : Matrix ι ι K) =
          (e * ((b⁻¹ : GL ι K) : Matrix ι ι K)) * (b : Matrix ι ι K) := by rw [h1]
        _ = e * (((b⁻¹ : GL ι K) : Matrix ι ι K) * (b : Matrix ι ι K)) := by rw [mul_assoc]
        _ = e * 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
        _ = e := mul_one e
    rw [ggOmW2_commute b hbA he]
    exact h3
  · intro h
    have h1 := congrArg (formAdj (RingHom.id K) G) h
    rw [CFSG.StandardType.ClassicalPosition.Geo.formAdj_mul (RingHom.id K) hG
      (b : Matrix ι ι K) e, hfinv] at h1
    have h3 : formAdj (RingHom.id K) G e * (b : Matrix ι ι K) =
        formAdj (RingHom.id K) G e := by
      calc formAdj (RingHom.id K) G e * (b : Matrix ι ι K) =
          (formAdj (RingHom.id K) G e *
            ((b⁻¹ : GL ι K) : Matrix ι ι K)) * (b : Matrix ι ι K) := by rw [h1]
        _ = formAdj (RingHom.id K) G e *
              (((b⁻¹ : GL ι K) : Matrix ι ι K) * (b : Matrix ι ι K)) := by rw [mul_assoc]
        _ = formAdj (RingHom.id K) G e * 1 := by
              rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
        _ = formAdj (RingHom.id K) G e := mul_one _
    rw [ggOmW2_commute b hbA hmemE]
    exact h3

private lemma ggOmW2_eigDimOn_one_prim {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Finite K] [CharP K 2] {b : GL ι K} (hodd : Odd (orderOf b))
    {e : Matrix ι ι K} (he : IsPrimIdemIn (ggOmW2_A b) e) :
    eigDimOn (b : Matrix ι ι K) e 1 =
      if (b : Matrix ι ι K) * e = e then
        Module.finrank K (LinearMap.range (Matrix.toLin' e)) else 0 := by
  classical
  by_cases h : (b : Matrix ι ι K) * e = e
  · rw [if_pos h]
    exact (eigDimOn_one_of_isPrimIdemIn (K := K) hodd he).1 h
  · rw [if_neg h]
    exact (eigDimOn_one_of_isPrimIdemIn (K := K) hodd he).2 h

private lemma ggOmW2_eigDimOn_primAdj_one {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] [CharP K 2] {G : Matrix ι ι K} (hG : IsUnit G.det)
    (hgsym : Matrix.transpose (G.map (RingHom.id K)) = G) {b : GL ι K}
    (hgram : ggOmW2_GramIso G b) (hodd : Odd (orderOf b)) {ε : Matrix ι ι K}
    (hε : IsPrimAdjIdemIn (RingHom.id K) G (ggOmW2_A b) ε) :
    eigDimOn (b : Matrix ι ι K) ε 1 =
      if (b : Matrix ι ι K) * ε = ε then
        Module.finrank K (LinearMap.range (Matrix.toLin' ε)) else 0 := by
  classical
  obtain ⟨e, he, _heε, hcase⟩ := ggOmW2_exists_prim hG hgsym hgram hε
  have heAdjPrim := ggOmW2_formAdj_prim hG hgsym hgram he
  have hbA : (b : Matrix ι ι K) ∈ ggOmW2_A b :=
    Algebra.subset_adjoin (by simp)
  have hbe : (b : Matrix ι ι K) * e =
      e * (b : Matrix ι ι K) := ggOmW2_commute b hbA he.1
  have hbeAdj : (b : Matrix ι ι K) *
        formAdj (RingHom.id K) G e =
      formAdj (RingHom.id K) G e *
        (b : Matrix ι ι K) := ggOmW2_commute b hbA heAdjPrim.1
  rcases hcase with hcase | ⟨hne, hneadj, hεeq⟩
  · rw [← hcase]
    exact ggOmW2_eigDimOn_one_prim hodd he
  · have horth : e * formAdj (RingHom.id K) G e = 0 :=
      ggOmW2_prim_orthogonal b he heAdjPrim (Ne.symm hneadj)
    have horth' : formAdj (RingHom.id K) G e * e = 0 :=
      ggOmW2_prim_orthogonal b heAdjPrim he hneadj
    have hbε : ((b : Matrix ι ι K) *
          (e + formAdj (RingHom.id K) G e) =
          e + formAdj (RingHom.id K) G e) ↔
        (b : Matrix ι ι K) * e = e := by
      constructor
      · intro h
        have h1 : e * ((b : Matrix ι ι K) *
            (e + formAdj (RingHom.id K) G e)) =
            e * (e + formAdj (RingHom.id K) G e) := by rw [h]
        have h1a : e * ((b : Matrix ι ι K) * e) =
            (b : Matrix ι ι K) * e := by
          rw [← mul_assoc, ← hbe, mul_assoc, he.2.1.eq]
        have h1b : e * ((b : Matrix ι ι K) *
            formAdj (RingHom.id K) G e) = 0 := by
          rw [← mul_assoc, ← hbe, mul_assoc, horth, mul_zero]
        have hR : e * (e + formAdj (RingHom.id K) G e) = e := by
          rw [mul_add, he.2.1.eq, horth, add_zero]
        have hL : e * ((b : Matrix ι ι K) *
            (e + formAdj (RingHom.id K) G e)) =
            (b : Matrix ι ι K) * e := by
          rw [mul_add, mul_add, h1a, h1b, add_zero]
        rw [hL, hR] at h1
        exact h1
      · intro h
        rw [mul_add, h, (ggOmW2_b_mul_formAdj_iff hG hgram he.1).2 h]
    have hadd : eigDimOn (b : Matrix ι ι K)
          (e + formAdj (RingHom.id K) G e) 1 =
        eigDimOn (b : Matrix ι ι K) e 1 +
          eigDimOn (b : Matrix ι ι K)
            (formAdj (RingHom.id K) G e) 1 :=
      ggOmW2_eigDimOn_add he.2.1 heAdjPrim.2.1 hbe hbeAdj horth horth' 1
    rw [hεeq, hadd, ggOmW2_eigDimOn_one_prim hodd he,
      ggOmW2_eigDimOn_one_prim hodd heAdjPrim]
    by_cases h : (b : Matrix ι ι K) * e = e
    · have hAdj : (b : Matrix ι ι K) *
          formAdj (RingHom.id K) G e =
          formAdj (RingHom.id K) G e :=
        (ggOmW2_b_mul_formAdj_iff hG hgram he.1).2 h
      rw [if_pos h, if_pos hAdj, if_pos (hbε.2 h)]
      exact (ggOmW2_finrank_range_add_matrix he.2.1 heAdjPrim.2.1 horth horth').symm
    · have hAdj : ¬ ((b : Matrix ι ι K) *
          formAdj (RingHom.id K) G e =
          formAdj (RingHom.id K) G e) :=
        fun hc => h ((ggOmW2_b_mul_formAdj_iff hG hgram he.1).1 hc)
      rw [if_neg h, if_neg hAdj, if_neg (fun hc => h (hbε.1 hc))]

private lemma ggOmW2_unique_one_block {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] [CharP K 2] {G : Matrix ι ι K} (hG : IsUnit G.det)
    (hgsym : Matrix.transpose (G.map (RingHom.id K)) = G) {b : GL ι K}
    (hgram : ggOmW2_GramIso G b) (hodd : Odd (orderOf b))
    {P : Finset (Matrix ι ι K)}
    (hP : ∀ ε ∈ P, IsPrimAdjIdemIn (RingHom.id K) G (ggOmW2_A b) ε)
    (hPorth : ∀ ε ∈ P, ∀ ε' ∈ P, ε ≠ ε' → ε * ε' = 0)
    {ε ε' : Matrix ι ι K} (hε : ε ∈ P) (hε' : ε' ∈ P)
    (h1 : (b : Matrix ι ι K) * ε = ε) (h1' : (b : Matrix ι ι K) * ε' = ε') : ε = ε' := by
  classical
  by_contra hne
  obtain ⟨e, he, heε, _⟩ := ggOmW2_exists_prim hG hgsym hgram (hP ε hε)
  obtain ⟨e', he', he'ε', _⟩ := ggOmW2_exists_prim hG hgsym hgram (hP ε' hε')
  have hbA : (b : Matrix ι ι K) ∈ ggOmW2_A b :=
    Algebra.subset_adjoin (by simp)
  have he1 : (b : Matrix ι ι K) * e = e := by
    calc (b : Matrix ι ι K) * e =
        (b : Matrix ι ι K) * (e * ε) := by rw [heε]
      _ = ((b : Matrix ι ι K) * e) * ε := by rw [mul_assoc]
      _ = (e * (b : Matrix ι ι K)) * ε := by rw [ggOmW2_commute b hbA he.1]
      _ = e * ((b : Matrix ι ι K) * ε) := by rw [mul_assoc]
      _ = e * ε := by rw [h1]
      _ = e := heε
  have he1' : (b : Matrix ι ι K) * e' = e' := by
    calc (b : Matrix ι ι K) * e' =
        (b : Matrix ι ι K) * (e' * ε') := by rw [he'ε']
      _ = ((b : Matrix ι ι K) * e') * ε' := by rw [mul_assoc]
      _ = (e' * (b : Matrix ι ι K)) * ε' := by rw [ggOmW2_commute b hbA he'.1]
      _ = e' * ((b : Matrix ι ι K) * ε') := by rw [mul_assoc]
      _ = e' * ε' := by rw [h1']
      _ = e' := he'ε'
  have hee' : e ≠ e' := by
    intro heq
    have heε' : e * ε' = e := by rw [heq, he'ε']
    have h0 : e = 0 := by
      calc e = e * ε := heε.symm
        _ = (e * ε') * ε := by rw [heε']
        _ = e * (ε' * ε) := by rw [mul_assoc]
        _ = e * 0 := by rw [hPorth ε' hε' ε hε (Ne.symm hne)]
        _ = 0 := mul_zero e
    exact he.2.2.1 h0
  have horth : e * e' = 0 := ggOmW2_prim_orthogonal b he he' hee'
  have hpos : eigDimOn (b : Matrix ι ι K) e 1 ≠ 0 := by
    rw [(eigDimOn_one_of_isPrimIdemIn (K := K) hodd he).1 he1]
    exact ggOmW2_finrank_range_toLin'_ne_zero he.2.2.1
  have hpos' : eigDimOn (b : Matrix ι ι K) e' 1 ≠ 0 := by
    rw [(eigDimOn_one_of_isPrimIdemIn (K := K) hodd he').1 he1']
    exact ggOmW2_finrank_range_toLin'_ne_zero he'.2.2.1
  rcases eigDimOn_eq_zero_or_of_mul_eq_zero he he' horth 1 with h0 | h0
  · exact hpos h0
  · exact hpos' h0

private lemma ggOmW2_eigDim_one {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] [CharP K 2] {G : Matrix ι ι K} (hG : IsUnit G.det)
    (hgsym : Matrix.transpose (G.map (RingHom.id K)) = G) {b : GL ι K}
    (hgram : ggOmW2_GramIso G b) (hodd : Odd (orderOf b))
    {P : Finset (Matrix ι ι K)}
    (hP : ∀ ε ∈ P, IsPrimAdjIdemIn (RingHom.id K) G (ggOmW2_A b) ε)
    (hPorth : ∀ ε ∈ P, ∀ ε' ∈ P, ε ≠ ε' → ε * ε' = 0)
    (hPsum : ∑ ε ∈ P, ε = 1) :
    eigDim (b : Matrix ι ι K) 1 = ∑ ε ∈ P,
      if (b : Matrix ι ι K) * ε = ε then
        Module.finrank K (LinearMap.range (Matrix.toLin' ε)) else 0 := by
  have hbA : (b : Matrix ι ι K) ∈ ggOmW2_A b :=
    Algebra.subset_adjoin (by simp)
  have hPcomm : ∀ ε ∈ P, IsIdempotentElem ε ∧
      Commute (b : Matrix ι ι K) ε := by
    intro ε hε
    exact ⟨(hP ε hε).2.1, ggOmW2_commute b hbA (hP ε hε).1⟩
  rw [eigDim_eq_sum_eigDimOn (b := (b : Matrix ι ι K))
    hPcomm hPorth hPsum 1]
  exact Finset.sum_congr rfl fun ε hε =>
    ggOmW2_eigDimOn_primAdj_one hG hgsym hgram hodd (hP ε hε)

private lemma ggOmW2_blockDegree_pos {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {b : GL ι K} {e : Matrix ι ι K} (he0 : e ≠ 0) :
    0 < blockDegree (ggOmW2_A b) e := by
  have hmem : e ∈ (Subalgebra.toSubmodule (ggOmW2_A b)).map (LinearMap.mulRight K e) :=
    ⟨1, (ggOmW2_A b).one_mem, by rw [LinearMap.mulRight_apply, one_mul]⟩
  have hne : (Subalgebra.toSubmodule (ggOmW2_A b)).map (LinearMap.mulRight K e) ≠ ⊥ := by
    intro h
    rw [h] at hmem
    exact he0 (by simpa using hmem)
  unfold blockDegree
  refine Module.finrank_pos_iff.mpr ⟨⟨e, hmem⟩, ⟨0, Submodule.zero_mem _⟩, ?_⟩
  intro h
  exact he0 (Subtype.ext_iff.mp h)

private lemma ggOmW2_block_data {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] [CharP K 2] (G : Matrix ι ι K) (b : GL ι K) (hodd : Odd (orderOf b))
    (hG : IsUnit G.det) (hgsym : Matrix.transpose (G.map (RingHom.id K)) = G)
    (hgram : ggOmW2_GramIso G b) {ε : Matrix ι ι K}
    (hε : IsPrimAdjIdemIn (RingHom.id K) G (ggOmW2_A b) ε)
    (h1 : (b : Matrix ι ι K) * ε ≠ ε) :
    ∃ (e : Matrix ι ι K) (R : Finset (AlgebraicClosure K)) (m : ℕ),
      IsPrimIdemIn (ggOmW2_A b) e ∧ e * ε = e ∧
      (e = ε ∨ (e ≠ ε ∧ formAdj (RingHom.id K) G e ≠ e ∧
        ε = e + formAdj (RingHom.id K) G e)) ∧
      (∀ l, eigDimOn (b : Matrix ι ι K) ε l = if l ∈ R then m else 0) ∧
      R.card * m = Module.finrank K (LinearMap.range (Matrix.toLin' ε)) ∧
      1 ∉ R ∧ 0 < m ∧
      (e = ε → R.card = blockDegree (ggOmW2_A b) e) ∧
      (e ≠ ε → R.card = 2 * blockDegree (ggOmW2_A b) e) := by
  classical
  obtain ⟨e, he, heε, hcase⟩ := ggOmW2_exists_prim hG hgsym hgram hε
  obtain ⟨R, m, hRcard, hRm, hRon, hRoff⟩ :=
    exists_blockRoots_of_isPrimIdemIn (K := K) hodd he
  have heAdj : IsPrimIdemIn (ggOmW2_A b) (formAdj (RingHom.id K) G e) :=
    ggOmW2_formAdj_prim hG hgsym hgram he
  obtain ⟨R', m', hR'card, hR'm', hR'on, hR'off⟩ :=
    exists_blockRoots_of_isPrimIdemIn (K := K) hodd heAdj
  have hbDegPos : 0 < blockDegree (ggOmW2_A b) e :=
    ggOmW2_blockDegree_pos he.2.2.1
  have hrankEq : Module.finrank K (LinearMap.range (Matrix.toLin' e)) =
      Module.finrank K (LinearMap.range
        (Matrix.toLin' (formAdj (RingHom.id K) G e))) :=
    (ggOmW2_finrank_range_formAdj hG e).symm
  have hdegEq : blockDegree (ggOmW2_A b) (formAdj (RingHom.id K) G e) =
      blockDegree (ggOmW2_A b) e := ggOmW2_blockDegree_formAdj hG hgsym hgram he.1
  have hmEq : m = m' := by
    have h1 : blockDegree (ggOmW2_A b) e * m =
        Module.finrank K (LinearMap.range (Matrix.toLin' e)) := by
      rw [← hRcard]; exact hRm
    have h2 : blockDegree (ggOmW2_A b) e * m' =
        Module.finrank K (LinearMap.range (Matrix.toLin' e)) := by
      have hRcard' : R.card = R'.card := by rw [hRcard, ← hdegEq, ← hR'card]
      rw [← hRcard, hRcard', hR'm', ← hrankEq]
    exact Nat.mul_left_cancel hbDegPos (h1.trans h2.symm)
  have hmPos : 0 < m := by
    by_contra h
    have hm0 : m = 0 := Nat.eq_zero_of_not_pos h
    have h2 : Module.finrank K (LinearMap.range (Matrix.toLin' e)) = 0 := by
      rw [← hRm, hm0, mul_zero]
    exact ggOmW2_finrank_range_toLin'_ne_zero he.2.2.1 h2
  have hcombine : ∀ (e₀ : Matrix ι ι K)
      (S : Finset (AlgebraicClosure K)) (t : ℕ),
      (∀ l ∈ S, eigDimOn (b : Matrix ι ι K) e₀ l = t) →
      (∀ l ∉ S, eigDimOn (b : Matrix ι ι K) e₀ l = 0) →
      ∀ l, eigDimOn (b : Matrix ι ι K) e₀ l =
        if l ∈ S then t else 0 := by
    intro e₀ S t hon hoff l
    by_cases hl : l ∈ S
    · rw [if_pos hl]; exact hon l hl
    · rw [if_neg hl]; exact hoff l hl
  have hRcomb := hcombine e R m hRon hRoff
  have hR'comb := hcombine (formAdj (RingHom.id K) G e) R' m' hR'on hR'off
  rcases hcase with hcase | ⟨hne, hneadj, hεeq⟩
  · refine ⟨e, R, m, he, heε, Or.inl hcase, ?_, ?_, ?_, hmPos, ?_, ?_⟩
    · intro l
      rw [← hcase]
      exact hRcomb l
    · rw [← hcase, hRm]
    · intro hmem
      have hb1 : (b : Matrix ι ι K) * e = e := by
        by_contra hbne
        have h0 := (eigDimOn_one_of_isPrimIdemIn (K := K) hodd he).2 hbne
        rw [hRon 1 hmem] at h0
        exact hmPos.ne' h0
      exact h1 (by rw [← hcase]; exact hb1)
    · intro _; rw [hRcard]
    · intro hne'; exact absurd hcase hne'
  · have horth : e * formAdj (RingHom.id K) G e = 0 :=
      ggOmW2_prim_orthogonal b he heAdj (Ne.symm hneadj)
    have horth' : formAdj (RingHom.id K) G e * e = 0 :=
      ggOmW2_prim_orthogonal b heAdj he hneadj
    have hdisj : Disjoint R R' := by
      rw [Finset.disjoint_iff_ne]
      intro a ha b hb hab
      subst hab
      have h0 := eigDimOn_eq_zero_or_of_mul_eq_zero he heAdj horth a
      rcases h0 with h0 | h0
      · rw [hRon a ha] at h0; exact hmPos.ne' h0
      · rw [hR'on a hb] at h0; exact hmPos.ne' (hmEq.trans h0)
    refine ⟨e, R ∪ R', m, he, heε, Or.inr ⟨hne, hneadj, hεeq⟩, ?_, ?_, ?_, hmPos, ?_, ?_⟩
    · intro l
      rw [hεeq, ggOmW2_eigDimOn_add he.2.1 heAdj.2.1
        (ggOmW2_commute b (Algebra.subset_adjoin (by simp)) he.1)
        (ggOmW2_commute b (Algebra.subset_adjoin (by simp)) heAdj.1) horth horth' l]
      rw [hRcomb l, hR'comb l, ← hmEq]
      by_cases hl : l ∈ R
      · rw [if_pos hl, if_pos (Finset.mem_union_left _ hl),
          if_neg (Finset.disjoint_left.mp hdisj hl)]
        ring
      · by_cases hl' : l ∈ R'
        · rw [if_neg hl, if_pos hl', if_pos (Finset.mem_union_right _ hl'), zero_add]
        · rw [if_neg hl, if_neg hl',
            if_neg (fun h => (Finset.mem_union.mp h).elim hl hl'), add_zero]
    · have hR'm : R'.card * m = Module.finrank K (LinearMap.range
          (Matrix.toLin' (formAdj (RingHom.id K) G e))) := by
        rw [hmEq, hR'm']
      rw [Finset.card_union_of_disjoint hdisj, add_mul, hRm, hR'm,
        ← ggOmW2_finrank_range_add_matrix he.2.1 heAdj.2.1 horth horth', hεeq]
    · intro hmem
      rw [Finset.mem_union] at hmem
      have hb1 : (b : Matrix ι ι K) * e = e := by
        by_contra hbne
        rcases hmem with hmem | hmem
        · have h0 := (eigDimOn_one_of_isPrimIdemIn (K := K) hodd he).2 hbne
          rw [hRon 1 hmem] at h0; exact hmPos.ne' h0
        · have hbne' : (b : Matrix ι ι K) *
              formAdj (RingHom.id K) G e ≠
              formAdj (RingHom.id K) G e :=
            fun hc => hbne ((ggOmW2_b_mul_formAdj_iff hG hgram he.1).1 hc)
          have h0 := (eigDimOn_one_of_isPrimIdemIn (K := K) hodd heAdj).2 hbne'
          rw [hR'on 1 hmem] at h0
          exact hmPos.ne' (hmEq.trans h0)
      have hb2 : (b : Matrix ι ι K) *
          formAdj (RingHom.id K) G e =
          formAdj (RingHom.id K) G e :=
        (ggOmW2_b_mul_formAdj_iff hG hgram he.1).2 hb1
      exact h1 (by rw [hεeq, mul_add, hb1, hb2])
    · intro h; exact absurd h hne
    · intro _
      rw [Finset.card_union_of_disjoint hdisj, hRcard, hR'card, hdegEq]
      ring

private lemma ggOmW2_one_block_prim {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] [CharP K 2] {G : Matrix ι ι K} (hG : IsUnit G.det)
    (hgsym : Matrix.transpose (G.map (RingHom.id K)) = G) {b : GL ι K}
    (hgram : ggOmW2_GramIso G b) (hodd : Odd (orderOf b)) {ε : Matrix ι ι K}
    (hε : IsPrimAdjIdemIn (RingHom.id K) G (ggOmW2_A b) ε)
    (h1 : (b : Matrix ι ι K) * ε = ε) :
    IsPrimIdemIn (ggOmW2_A b) ε := by
  obtain ⟨e, he, heε, hcase⟩ := ggOmW2_exists_prim hG hgsym hgram hε
  have hbA : (b : Matrix ι ι K) ∈ ggOmW2_A b :=
    Algebra.subset_adjoin (by simp)
  have hbe : (b : Matrix ι ι K) * e = e := by
    calc (b : Matrix ι ι K) * e =
        (b : Matrix ι ι K) * (e * ε) := by rw [heε]
      _ = ((b : Matrix ι ι K) * e) * ε := by rw [mul_assoc]
      _ = (e * (b : Matrix ι ι K)) * ε := by rw [ggOmW2_commute b hbA he.1]
      _ = e * ((b : Matrix ι ι K) * ε) := by rw [mul_assoc]
      _ = e * ε := by rw [h1]
      _ = e := heε
  rcases hcase with hcase | ⟨hne, hneadj, _⟩
  · rw [hcase] at he
    exact he
  · exfalso
    have heAdj := ggOmW2_formAdj_prim hG hgsym hgram he
    have hbeAdj : (b : Matrix ι ι K) *
        formAdj (RingHom.id K) G e = formAdj (RingHom.id K) G e :=
      (ggOmW2_b_mul_formAdj_iff hG hgram he.1).2 hbe
    have hpos : eigDimOn (b : Matrix ι ι K) e 1 ≠ 0 := by
      rw [(eigDimOn_one_of_isPrimIdemIn (K := K) hodd he).1 hbe]
      exact ggOmW2_finrank_range_toLin'_ne_zero he.2.2.1
    have hpos' : eigDimOn (b : Matrix ι ι K)
        (formAdj (RingHom.id K) G e) 1 ≠ 0 := by
      rw [(eigDimOn_one_of_isPrimIdemIn (K := K) hodd heAdj).1 hbeAdj]
      exact ggOmW2_finrank_range_toLin'_ne_zero heAdj.2.2.1
    have horth : e * formAdj (RingHom.id K) G e = 0 :=
      ggOmW2_prim_orthogonal b he heAdj (Ne.symm hneadj)
    rcases eigDimOn_eq_zero_or_of_mul_eq_zero he heAdj horth 1 with h0 | h0
    · exact hpos h0
    · exact hpos' h0

private theorem ggOmW2_factorization_two_card_GL {E : Type} [Field E] [Fintype E] {m g : ℕ}
    (hE : Fintype.card E = 2 ^ g) :
    (Nat.card (GL (Fin m) E)).factorization 2 = g * (m * (m - 1) / 2) := by
  have hg : 1 ≤ g := by
    have h2 : 1 < Fintype.card E := Fintype.one_lt_card
    rw [hE] at h2
    by_contra hg0
    have : g = 0 := by omega
    rw [this] at h2
    simp at h2
  exact CFSG.LocalAnalysis.EvenBN.U5.CaseBParts.l3ao_v2_card_GL (F := E) (e := g)
    (by rw [Nat.card_eq_fintype_card, hE]) hg m

private lemma ggOmW2b_factorization_two_of_eq {N a u : ℕ} (hN : N = 2 ^ a * u) (hu : Odd u) :
    N.factorization 2 = a := by
  subst hN
  have hu0 : u ≠ 0 := fun h => by
    rw [h] at hu
    exact (by decide : ¬ Odd 0) hu
  rw [Nat.factorization_mul (pow_ne_zero _ two_ne_zero) hu0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hu.not_two_dvd_nat, add_zero]

private lemma ggOmW2b_finite_linearEquiv {K W : Type} [Field K] [Finite K] [AddCommGroup W]
    [Module K W] [FiniteDimensional K W] : Finite (W ≃ₗ[K] W) := by
  have : Finite W := Module.finite_of_finite K
  exact Finite.of_injective (fun e : W ≃ₗ[K] W => (e : W → W))
    fun _ _ h => LinearEquiv.ext (congrFun h)

private lemma ggOmW2b_odd_orderOf_of_dicksonHom_eq_one {K W : Type} [Field K] [Finite K]
    [CharP K 2] [AddCommGroup W] [Module K W] [FiniteDimensional K W] (R : QuadraticForm K W)
    (hR : (QuadraticMap.polarBilin R).Nondegenerate) (hle : Module.finrank K W ≤ 2)
    {g : ↥(TauCeti.QuadraticMap.orthogonalGroup R)}
    (hδ : CFSG.RankThree.OrthogonalInvolutions.dicksonHom R hR g = 1) :
    Odd (orderOf g) := by
  by_contra h
  have heven : Even (orderOf g) := Nat.not_odd_iff_even.mp h
  obtain ⟨k, hk⟩ := heven
  have hk2 : orderOf g = 2 * k := by omega
  haveI : Finite (W ≃ₗ[K] W) := ggOmW2b_finite_linearEquiv
  haveI : Finite ↥(TauCeti.QuadraticMap.orthogonalGroup R) :=
    Finite.of_injective (fun x => (x : W ≃ₗ[K] W)) fun _ _ h => Subtype.ext h
  have hpos : 0 < orderOf g := orderOf_pos_iff.mpr (isOfFinOrder_of_finite g)
  have hkne : k ≠ 0 := by omega
  have hlt : k < orderOf g := by omega
  have hgn : g ^ k ≠ 1 := pow_ne_one_of_lt_orderOf hkne hlt
  have hδk : CFSG.RankThree.OrthogonalInvolutions.dicksonHom R hR (g ^ k) = 1 := by
    rw [map_pow, hδ, one_pow]
  have hg2 : (g ^ k) ^ 2 = 1 := by
    rw [← pow_mul, show k * 2 = 2 * k by omega, ← hk2]
    exact pow_orderOf_eq_one g
  have h1 : g ^ k = 1 :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256q.twoElt_eq_one_of_dickson_of_finrank_le_two
      hR hle hδk 1 (by simpa using hg2)
  exact hgn h1

private theorem ggOmW2_factorization_two_card_statedOmega {ι K : Type} [Fintype ι] [DecidableEq ι]
    [Field K] [Fintype K] [CharP K 2] {f n : ℕ} (hf : Fintype.card K = 2 ^ f)
    (Q : QuadraticForm K (ι → K)) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hn : Fintype.card ι = 2 * n)
    (hne : ¬ (Fintype.card K = 2 ∧ n = 2 ∧
      ∃ S : Submodule K (ι → K), Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0)) :
    (Nat.card ↥(StatedOmega ⇑Q)).factorization 2 = f * (n * (n - 1)) := by
  have hbridge : Nat.card ↥(StatedOmega ⇑Q) = Nat.card ↥(orthDerived Q) := by
    rw [CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap (Q := Q) (Q₀ := ⇑Q) rfl,
      show ∀ H : Subgroup ((ι → K) ≃ₗ[K] (ι → K)),
          H.comap (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).toMonoidHom =
            H.map (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).symm.toMonoidHom from
        fun H => Subgroup.comap_equiv_eq_map_symm
          (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K) H]
    exact Nat.card_congr (Subgroup.equivMapOfInjective _ _
      (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).symm.injective).symm.toEquiv
  have hf1 : 1 ≤ f := by
    by_contra h
    have h0 : f = 0 := by omega
    rw [h0, pow_zero] at hf
    have h2 : 1 < Fintype.card K := Fintype.one_lt_card
    omega
  have hfin : Module.finrank K (ι → K) = 2 * n := by
    rw [Module.finrank_fintype_fun_eq_card, hn]
  rcases (show n ≤ 1 ∨ 2 ≤ n by omega) with hn01 | hn2
  · have hodd_card : Odd (Nat.card ↥(orthDerived Q)) := by
      have hodd_elem : ∀ g : ↥(orthDerived Q), Odd (orderOf g) := by
        intro g
        have hgω : (g : (ι → K) ≃ₗ[K] (ι → K)) ∈
            CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hQ :=
          CFSG.RankThree.PartOne.FieldFix.orthDerived_le_omegaGroup hQ g.2
        have hgO : (g : (ι → K) ≃ₗ[K] (ι → K)) ∈
            TauCeti.QuadraticMap.orthogonalGroup Q :=
          Subgroup.commutator_le_self (TauCeti.QuadraticMap.orthogonalGroup Q) g.2
        have hgoker : (⟨(g : (ι → K) ≃ₗ[K] (ι → K)), hgO⟩ :
            ↥(TauCeti.QuadraticMap.orthogonalGroup Q)) ∈
            (CFSG.RankThree.OrthogonalInvolutions.dicksonHom Q hQ).ker := by
          rw [CFSG.RankThree.OrthogonalInvolutions.dicksonHom_ker, Subgroup.mem_subgroupOf]
          exact hgω
        have hδ : CFSG.RankThree.OrthogonalInvolutions.dicksonHom Q hQ
            ⟨(g : (ι → K) ≃ₗ[K] (ι → K)), hgO⟩ = 1 := MonoidHom.mem_ker.mpr hgoker
        have hle : Module.finrank K (ι → K) ≤ 2 := by rw [hfin]; omega
        have hoddO := ggOmW2b_odd_orderOf_of_dicksonHom_eq_one Q hQ hle hδ
        have hord : orderOf (⟨(g : (ι → K) ≃ₗ[K] (ι → K)), hgO⟩ :
            ↥(TauCeti.QuadraticMap.orthogonalGroup Q)) = orderOf g := by
          rw [← Subgroup.orderOf_coe (⟨(g : (ι → K) ≃ₗ[K] (ι → K)), hgO⟩ :
            ↥(TauCeti.QuadraticMap.orthogonalGroup Q))]
          exact Subgroup.orderOf_coe g
        rwa [hord] at hoddO
      by_contra h
      have heven : Even (Nat.card ↥(orthDerived Q)) := Nat.not_odd_iff_even.mp h
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥(orthDerived Q)) 2
        (even_iff_two_dvd.mp heven)
      have := hodd_elem g
      rw [hg] at this
      exact (by decide : ¬ Odd 2) this
    rw [hbridge, Nat.factorization_eq_zero_of_not_dvd hodd_card.not_two_dvd_nat]
    interval_cases n <;> simp
  · have h3 : 3 ≤ Module.finrank K (ι → K) := by rw [hfin]; omega
    have hnexc : ¬ CFSG.RankThree.PartOne.KCOrthogonal.SmallFixedException Q := by
      intro h
      rcases h with ⟨h3dim, hq3⟩ | ⟨⟨h4dim, hS⟩, hq23⟩
      · rw [hfin] at h3dim
        omega
      · rcases hq23 with hq2 | hq3
        · have hn2' : n = 2 := by
            rw [hfin] at h4dim
            omega
          exact hne ⟨by rw [← Nat.card_eq_fintype_card]; exact hq2, hn2', hS⟩
        · have h2 := FiniteField.cast_card_eq_zero K
          rw [Fintype.card_eq_nat_card, hq3] at h2
          have h3' : ((3 : ℕ) : K) = 1 := by
            have : ((2 : ℕ) : K) = 0 := CharP.cast_eq_zero K 2
            rw [show (3 : ℕ) = 2 + 1 by norm_num, Nat.cast_add, this, zero_add, Nat.cast_one]
          rw [h3'] at h2
          exact one_ne_zero h2
    have hΩ : CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hQ ≤ orthDerived Q :=
      CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs141d.omegaGroup_le_orthDerived_of_listed
        Q hQ h3 hnexc
    have hn1 : 1 ≤ n := by omega
    have hK : Nat.card K = 2 ^ f := by rw [Nat.card_eq_fintype_card]; exact hf
    have hdim' : Module.finrank K (ι → K) = 2 * ((n - 1) + 1) := by
      rw [hfin]; omega
    have hnm : (n - 1) + 1 = n := by omega
    rw [hbridge]
    by_cases hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q
    · obtain ⟨r, hr, hrd⟩ :=
        (CFSG.Timmesfeld.Orders.profile_ordD (n := n) (f := f) hn1 hf1).two
      have hcard := CFSG.StandardType.card_orthDerived_eq_ordD Q hQ hdim' hΩ hplus
      rw [hcard, hnm, hK]
      exact ggOmW2b_factorization_two_of_eq hrd hr
    · obtain ⟨r, hr, hrd⟩ :=
        (CFSG.Timmesfeld.Orders.profile_ordTwistedD (n := n) (f := f) hn1 hf1).two
      have hcard := CFSG.StandardType.card_orthDerived_eq_ordTwistedD Q hQ hdim' hΩ hplus
      rw [hcard, hnm, hK]
      exact ggOmW2b_factorization_two_of_eq hrd hr

private lemma ggOmW2_selfDual_blockDegree_even {ι K : Type} [Fintype ι] [DecidableEq ι]
    [Field K] [Fintype K] [CharP K 2] {G : Matrix ι ι K} {b : GL ι K}
    (hG : IsUnit G.det) (hgsym : Matrix.transpose (G.map (RingHom.id K)) = G)
    (hgram : ggOmW2_GramIso G b) (hodd : Odd (orderOf b)) {ε : Matrix ι ι K}
    (he : IsPrimIdemIn (ggOmW2_A b) ε)
    (hadj : formAdj (RingHom.id K) G ε = ε) (h1 : (b : Matrix ι ι K) * ε ≠ ε) :
    ∃ d : ℕ, blockDegree (ggOmW2_A b) ε = 2 * d := by
  have hS : ∀ s ∈ ({b} : Set (GL ι K)), ∀ s' ∈ ({b} : Set (GL ι K)), Commute s s' := by
    intro s hs s' hs'
    rw [Set.mem_singleton_iff] at hs hs'
    rw [hs, hs']
  have hoddS : ∀ s ∈ ({b} : Set (GL ι K)), Odd (orderOf s) := by
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    rw [hs]
    exact hodd
  have hSU : ∀ s ∈ ({b} : Set (GL ι K)),
      Matrix.transpose ((s : Matrix ι ι K).map (RingHom.id K)) * G * (s : Matrix ι ι K) = G := by
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    rw [hs]
    exact hgram
  have hSG : ∀ s ∈ ({b} : Set (GL ι K)),
      Matrix.transpose (s : Matrix ι ι K) * G * (s : Matrix ι ι K) = G := by
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    rw [hs]
    simpa [ggOmW2_GramIso, Matrix.map_id] using hgram
  rcases blockDegree_eq_one_or_even_of_formAdj_eq hG hS hoddS hSG he hadj with hdeg | heven
  · exfalso
    obtain ⟨c, hcne, hce, hce'⟩ :=
      CFSG.StandardType.ClassicalPosition.Geo.exists_eigen_of_dualPair (RingHom.id K)
        (fun x => rfl) hG hgsym hSU hS he hdeg (s := b) (by simp)
    rw [hadj] at hce'
    have hscalar : c • ε = c⁻¹ • ε := hce.symm.trans hce'
    have hsub : (c - c⁻¹) • ε = 0 := by rw [sub_smul, hscalar, sub_self]
    have hczero : c - c⁻¹ = 0 := by
      rcases smul_eq_zero.mp hsub with h | h
      · exact h
      · exact absurd h he.2.2.1
    have hc : c * c = 1 := by
      have hceq : c = c⁻¹ := sub_eq_zero.mp hczero
      nth_rewrite 2 [hceq]
      exact mul_inv_cancel₀ hcne
    have hc1 : c = 1 := by
      rcases (mul_self_eq_one_iff.mp hc) with h | h
      · exact h
      · rwa [CharTwo.neg_eq] at h
    exact h1 (hce.trans (by rw [hc1, one_smul]))
  · obtain ⟨d, hd⟩ := heven
    exact ⟨d, by rw [hd]; ring⟩

private lemma ggOmW2d_finset_eq_of_eigDimOn {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {b e : Matrix ι ι K} (R R' : Finset (AlgebraicClosure K)) (m m' : ℕ)
    (hR : ∀ l, eigDimOn b e l = if l ∈ R then m else 0) (hm : 0 < m)
    (hR' : ∀ l, eigDimOn b e l = if l ∈ R' then m' else 0) (hm' : 0 < m') :
    R = R' := by
  classical
  have hmem : ∀ (S : Finset (AlgebraicClosure K)) (k : ℕ), 0 < k →
      (∀ l, eigDimOn b e l = if l ∈ S then k else 0) →
      (∀ l, l ∈ S ↔ eigDimOn b e l ≠ 0) := by
    intro S k hk hSk l
    rw [hSk l]
    constructor
    · intro hl h0
      rw [if_pos hl] at h0
      exact hk.ne' h0
    · intro hne
      by_contra hl
      rw [if_neg hl] at hne
      exact hne rfl
  exact Finset.ext fun l => (hmem R m hm hR l).trans (hmem R' m' hm' hR' l).symm

private theorem ggOmW2_ROf_even {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (b : GL ι K) (hb : b ∈ StatedOmega ⇑Φ)
    (hodd : Odd (orderOf b)) {P : Finset (Matrix ι ι K)}
    (hPprim : ∀ ε ∈ P, IsPrimAdjIdemIn (RingHom.id K) (ggOmW2_G Φ) (ggOmW2_A b) ε)
    (ROf : Matrix ι ι K → Finset (AlgebraicClosure K)) (mOf : Matrix ι ι K → ℕ)
    (hOf : ∀ ε ∈ P, ∀ l, eigDimOn (b : Matrix ι ι K) ε l =
      if l ∈ ROf ε then mOf ε else 0)
    (hOf_pos : ∀ ε ∈ P, (b : Matrix ι ι K) * ε ≠ ε → 0 < mOf ε)
    {ε : Matrix ι ι K} (hε : ε ∈ P) (h1 : (b : Matrix ι ι K) * ε ≠ ε) :
    (ROf ε).card = 2 * ((ROf ε).card / 2) := by
  classical
  have hG : IsUnit (ggOmW2_G Φ).det := ggOmW2_G_isUnit Φ hΦ
  have hgsym : Matrix.transpose ((ggOmW2_G Φ).map (RingHom.id K)) = ggOmW2_G Φ :=
    ggOmW2_G_transpose Φ
  have hgram : ggOmW2_GramIso (ggOmW2_G Φ) b := ggOmW2_gram Φ hb
  obtain ⟨e, R, m, he, heε, hcase, hOfR, hRm, h1R, hmPos, hcard, h2deg⟩ :=
    ggOmW2_block_data (ggOmW2_G Φ) b hodd hG hgsym hgram (hPprim ε hε) h1
  have hROf : ROf ε = R :=
    ggOmW2d_finset_eq_of_eigDimOn (ROf ε) R (mOf ε) m (hOf ε hε)
      (hOf_pos ε hε h1) hOfR hmPos
  rw [hROf]
  rcases hcase with hcase | ⟨hne, hneadj, hεeq⟩
  · obtain ⟨d', hd'⟩ := ggOmW2_selfDual_blockDegree_even hG hgsym hgram hodd
      (hcase ▸ he) (hPprim ε hε).2.2.2.1 h1
    have hbd : R.card = blockDegree (ggOmW2_A b) ε := by
      simpa only [hcase] using hcard hcase
    rw [hbd, hd', Nat.mul_div_cancel_left d' (by norm_num : 0 < 2)]
  · rw [h2deg hne, Nat.mul_div_cancel_left (blockDegree (ggOmW2_A b) e) (by norm_num : 0 < 2)]

private theorem ggOmW2_blockExp_eq_true {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] [CharP K 2] (G : Matrix ι ι K) (b : GL ι K) (hodd : Odd (orderOf b))
    (hG : IsUnit G.det) (hgsym : Matrix.transpose (G.map (RingHom.id K)) = G)
    (hgram : ggOmW2_GramIso G b) {P : Finset (Matrix ι ι K)}
    (hPprim : ∀ ε ∈ P, IsPrimAdjIdemIn (RingHom.id K) G (ggOmW2_A b) ε)
    (hPorth : ∀ ε ∈ P, ∀ ε' ∈ P, ε ≠ ε' → ε * ε' = 0)
    (hPsum : ∑ ε ∈ P, ε = 1)
    (ROf : Matrix ι ι K → Finset (AlgebraicClosure K)) (mOf : Matrix ι ι K → ℕ)
    (hOf : ∀ ε ∈ P, ∀ l, eigDimOn (b : Matrix ι ι K) ε l =
      if l ∈ ROf ε then mOf ε else 0)
    (hOf_one : ∀ ε ∈ P, (b : Matrix ι ι K) * ε ≠ ε → 1 ∉ ROf ε)
    (hOf_pos : ∀ ε ∈ P, (b : Matrix ι ι K) * ε ≠ ε → 0 < mOf ε)
    (hOf_even : ∀ ε ∈ P, (b : Matrix ι ι K) * ε ≠ ε →
      (ROf ε).card = 2 * ((ROf ε).card / 2)) :
    blockExp true (b : Matrix ι ι K) =
      (eigDim (b : Matrix ι ι K) 1 / 2) * (eigDim (b : Matrix ι ι K) 1 / 2 - 1) +
      ∑ ε ∈ P.filter (fun ε => (b : Matrix ι ι K) * ε ≠ ε),
        (ROf ε).card / 2 * (mOf ε * (mOf ε - 1) / 2) := by
  classical
  have hbA : (b : Matrix ι ι K) ∈ ggOmW2_A b := Algebra.subset_adjoin (by simp)
  have hpart : ggOmW2_R (b : Matrix ι ι K) =
      (P.filter (fun ε => (b : Matrix ι ι K) * ε ≠ ε)).biUnion ROf := by
    apply Finset.ext
    intro l
    simp only [Finset.mem_biUnion, Finset.mem_filter]
    constructor
    · intro hl
      rw [ggOmW2_R, Finset.mem_erase, Multiset.mem_toFinset] at hl
      obtain ⟨hl1, hlroot⟩ := hl
      have hd : eigDim (b : Matrix ι ι K) l ≠ 0 :=
        (ggOmW2_eigDim_ne_zero_iff_mem_roots (b : Matrix ι ι K)
          (ggOmW2_cast_orderOf_ne_zero hodd) (ggOmW2_matrix_pow_orderOf b)).mpr hlroot
      have hPcomm : ∀ ε ∈ P, IsIdempotentElem ε ∧
          Commute (b : Matrix ι ι K) ε := by
        intro ε hε
        exact ⟨(hPprim ε hε).2.1, ggOmW2_commute b hbA (hPprim ε hε).1⟩
      have hsum := eigDim_eq_sum_eigDimOn (b := (b : Matrix ι ι K)) hPcomm hPorth hPsum l
      have hex : ∃ ε ∈ P, eigDimOn (b : Matrix ι ι K) ε l ≠ 0 := by
        by_contra h
        push Not at h
        rw [hsum] at hd
        exact hd (Finset.sum_eq_zero fun ε hε => h ε hε)
      obtain ⟨ε, hεP, hεne⟩ := hex
      have hbne : (b : Matrix ι ι K) * ε ≠ ε := by
        intro h1
        exact hεne (ggOmW2_eigDimOn_eq_zero_of_b_mul_eq hodd
          (ggOmW2_one_block_prim hG hgsym hgram hodd (hPprim ε hεP) h1) h1 hl1)
      refine ⟨ε, ⟨hεP, hbne⟩, ?_⟩
      by_contra hlR
      exact hεne (by rw [hOf ε hεP l, if_neg hlR])
    · rintro ⟨ε, ⟨hεP, hbne⟩, hlR⟩
      have hne0 : eigDimOn (b : Matrix ι ι K) ε l ≠ 0 := by
        rw [hOf ε hεP l, if_pos hlR]
        exact (hOf_pos ε hεP hbne).ne'
      have hd : eigDim (b : Matrix ι ι K) l ≠ 0 := by
        intro h0
        exact hne0 (le_antisymm
          (h0 ▸ ggOmW2_eigDimOn_le_eigDim (b : Matrix ι ι K) ε l)
          (Nat.zero_le _))
      rw [ggOmW2_R, Finset.mem_erase, Multiset.mem_toFinset]
      refine ⟨?_, (ggOmW2_eigDim_ne_zero_iff_mem_roots (b : Matrix ι ι K)
        (ggOmW2_cast_orderOf_ne_zero hodd) (ggOmW2_matrix_pow_orderOf b)).mp hd⟩
      intro hl1
      exact hOf_one ε hεP hbne (hl1 ▸ hlR)
  have hpiece : ∀ ε (hε : ε ∈ P) (h1 : (b : Matrix ι ι K) * ε ≠ ε)
      (a : AlgebraicClosure K), a ∈ ROf ε →
      ∃ p, IsPrimIdemIn (ggOmW2_A b) p ∧ p * ε = p ∧
        eigDimOn (b : Matrix ι ι K) p a ≠ 0 := by
    intro ε hε h1 a ha
    obtain ⟨e₀, _, _, hprim, heε, hcase, _, _, _, _, _, _⟩ :=
      ggOmW2_block_data G b hodd hG hgsym hgram (hPprim ε hε) h1
    have hne : eigDimOn (b : Matrix ι ι K) ε a ≠ 0 := by
      rw [hOf ε hε a, if_pos ha]
      exact (hOf_pos ε hε h1).ne'
    rcases hcase with hcase | ⟨hne', hneadj, hεeq⟩
    · refine ⟨e₀, hprim, heε, ?_⟩
      rwa [← hcase] at hne
    · have heAdj := ggOmW2_formAdj_prim hG hgsym hgram hprim
      have hadd := ggOmW2_eigDimOn_add hprim.2.1 heAdj.2.1
        (ggOmW2_commute b hbA hprim.1) (ggOmW2_commute b hbA heAdj.1)
        (ggOmW2_prim_orthogonal b hprim heAdj (Ne.symm hneadj))
        (ggOmW2_prim_orthogonal b heAdj hprim hneadj) a
      rw [hεeq, hadd] at hne
      by_cases h0 : eigDimOn (b : Matrix ι ι K) e₀ a ≠ 0
      · exact ⟨e₀, hprim, heε, h0⟩
      · push Not at h0
        refine ⟨formAdj (RingHom.id K) G e₀, heAdj, ?_, ?_⟩
        · calc formAdj (RingHom.id K) G e₀ * ε
              = formAdj (RingHom.id K) G e₀ * (e₀ + formAdj (RingHom.id K) G e₀) := by
                rw [hεeq]
            _ = formAdj (RingHom.id K) G e₀ * e₀ +
                  formAdj (RingHom.id K) G e₀ * formAdj (RingHom.id K) G e₀ := by
                rw [mul_add]
            _ = 0 + formAdj (RingHom.id K) G e₀ := by
                rw [ggOmW2_prim_orthogonal b heAdj hprim hneadj, heAdj.2.1.eq]
            _ = formAdj (RingHom.id K) G e₀ := zero_add _
        · intro hc
          exact hne (by rw [h0, hc, add_zero])
  have hdisjR : ∀ ε (hε : ε ∈ P) (h1 : (b : Matrix ι ι K) * ε ≠ ε)
      ε' (hε' : ε' ∈ P) (h1' : (b : Matrix ι ι K) * ε' ≠ ε'),
      ε ≠ ε' → Disjoint (ROf ε) (ROf ε') := by
    intro ε hε h1 ε' hε' h1' hne
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb hab
    subst hab
    obtain ⟨p, hp, hpε, hpa⟩ := hpiece ε hε h1 a ha
    obtain ⟨p', hp', hp'ε', hp'a⟩ := hpiece ε' hε' h1' a hb
    have hpp' : p * p' = 0 := by
      refine ggOmW2_prim_orthogonal b hp hp' ?_
      intro hpeq
      have hpε' : p * ε' = p := by rw [hpeq, hp'ε']
      have h0 : p = 0 := by
        calc p = p * ε' := hpε'.symm
          _ = (p * ε) * ε' := by rw [hpε]
          _ = p * (ε * ε') := by rw [mul_assoc]
          _ = p * 0 := by rw [hPorth ε hε ε' hε' hne]
          _ = 0 := mul_zero p
      exact hp.2.2.1 h0
    rcases eigDimOn_eq_zero_or_of_mul_eq_zero hp hp' hpp' a with h0 | h0
    · exact hpa h0
    · exact hp'a h0
  have hval : ∀ ε (hε : ε ∈ P) (h1 : (b : Matrix ι ι K) * ε ≠ ε)
      (l : AlgebraicClosure K), l ∈ ROf ε →
      eigDim (b : Matrix ι ι K) l = mOf ε := by
    intro ε hε h1 l hl
    have hl1 : l ≠ 1 := fun h => hOf_one ε hε h1 (h ▸ hl)
    have hPcomm : ∀ ε' ∈ P, IsIdempotentElem ε' ∧
        Commute (b : Matrix ι ι K) ε' := by
      intro ε' hε'
      exact ⟨(hPprim ε' hε').2.1, ggOmW2_commute b hbA (hPprim ε' hε').1⟩
    rw [eigDim_eq_sum_eigDimOn (b := (b : Matrix ι ι K)) hPcomm hPorth hPsum l]
    refine (Finset.sum_eq_single ε ?_ (fun hnot => absurd hε hnot)).trans ?_
    · intro ε' hε' hne'
      rw [hOf ε' hε' l]
      by_cases hl' : l ∈ ROf ε'
      · rw [if_pos hl']
        by_cases h1' : (b : Matrix ι ι K) * ε' = ε'
        · have hzero := ggOmW2_eigDimOn_eq_zero_of_b_mul_eq hodd
            (ggOmW2_one_block_prim hG hgsym hgram hodd (hPprim ε' hε') h1') h1' hl1
          have hstep : eigDimOn (b : Matrix ι ι K) ε' l = mOf ε' := by
            rw [hOf ε' hε' l, if_pos hl']
          rw [← hstep]
          exact hzero
        · exact absurd hl' (Finset.disjoint_left.mp
            (hdisjR ε hε h1 ε' hε' h1' (Ne.symm hne')) hl)
      · rw [if_neg hl']
    · rw [hOf ε hε l, if_pos hl]
  have hsum1 : ∑ l ∈ ggOmW2_R (b : Matrix ι ι K),
        eigDim (b : Matrix ι ι K) l * (eigDim (b : Matrix ι ι K) l - 1) / 2 =
      ∑ ε ∈ P.filter (fun ε => (b : Matrix ι ι K) * ε ≠ ε),
        (ROf ε).card * (mOf ε * (mOf ε - 1) / 2) := by
    rw [hpart, Finset.sum_biUnion]
    · apply Finset.sum_congr rfl
      intro ε hε
      rw [Finset.sum_congr rfl (fun l hl => by
          rw [hval ε (Finset.mem_filter.mp hε).1 (Finset.mem_filter.mp hε).2 l hl]),
        Finset.sum_const, smul_eq_mul]
    · intro ε hε ε' hε' hne
      exact hdisjR ε (Finset.mem_filter.mp hε).1 (Finset.mem_filter.mp hε).2
        ε' (Finset.mem_filter.mp hε').1 (Finset.mem_filter.mp hε').2 hne
  have hdiv : (∑ ε ∈ P.filter (fun ε => (b : Matrix ι ι K) * ε ≠ ε),
        (ROf ε).card * (mOf ε * (mOf ε - 1) / 2)) / 2 =
      ∑ ε ∈ P.filter (fun ε => (b : Matrix ι ι K) * ε ≠ ε),
        (ROf ε).card / 2 * (mOf ε * (mOf ε - 1) / 2) := by
    have h1 : ∀ ε ∈ P.filter (fun ε => (b : Matrix ι ι K) * ε ≠ ε),
        (ROf ε).card * (mOf ε * (mOf ε - 1) / 2) =
          2 * ((ROf ε).card / 2 * (mOf ε * (mOf ε - 1) / 2)) := by
      intro ε hε
      have heven := hOf_even ε (Finset.mem_filter.mp hε).1 (Finset.mem_filter.mp hε).2
      calc (ROf ε).card * (mOf ε * (mOf ε - 1) / 2)
          = 2 * ((ROf ε).card / 2) * (mOf ε * (mOf ε - 1) / 2) := by
            conv_lhs => rw [heven]
        _ = 2 * ((ROf ε).card / 2 * (mOf ε * (mOf ε - 1) / 2)) := by ring
    rw [Finset.sum_congr rfl h1, ← Finset.mul_sum,
      Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  rw [ggOmW2_blockExp_true_eq, hsum1, hdiv]

private theorem ggOmW2_block_order {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι)
    {f : ℕ} (hf : Fintype.card K = 2 ^ f) (b : GL ι K) (hb : b ∈ StatedOmega ⇑Φ)
    (hodd : Odd (orderOf b)) {P : Finset (Matrix ι ι K)}
    (hPprim : ∀ ε ∈ P, IsPrimAdjIdemIn (RingHom.id K) (ggOmW2_G Φ) (ggOmW2_A b) ε)
    (ROf : Matrix ι ι K → Finset (AlgebraicClosure K)) (mOf : Matrix ι ι K → ℕ)
    (hOf : ∀ ε ∈ P, ∀ l, eigDimOn (b : Matrix ι ι K) ε l =
      if l ∈ ROf ε then mOf ε else 0)
    (hOf_pos : ∀ ε ∈ P, (b : Matrix ι ι K) * ε ≠ ε → 0 < mOf ε)
    (hOf_mul : ∀ ε ∈ P, (b : Matrix ι ι K) * ε ≠ ε →
      (ROf ε).card * mOf ε = Module.finrank K (LinearMap.range (Matrix.toLin' ε)))
    (hOf_even : ∀ ε ∈ P, (b : Matrix ι ι K) * ε ≠ ε →
      (ROf ε).card = 2 * ((ROf ε).card / 2)) :
    ∀ ε ∈ P, (Nat.card ↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε)).factorization 2 =
      f * (if (b : Matrix ι ι K) * ε = ε then
        (Module.finrank K (LinearMap.range (Matrix.toLin' ε)) / 2) *
          (Module.finrank K (LinearMap.range (Matrix.toLin' ε)) / 2 - 1)
        else (ROf ε).card / 2 * (mOf ε * (mOf ε - 1) / 2)) := by
  classical
  have hG : IsUnit (ggOmW2_G Φ).det := ggOmW2_G_isUnit Φ hΦ
  have hgsym : Matrix.transpose ((ggOmW2_G Φ).map (RingHom.id K)) = ggOmW2_G Φ :=
    ggOmW2_G_transpose Φ
  have hgram : ggOmW2_GramIso (ggOmW2_G Φ) b := ggOmW2_gram Φ hb
  intro ε hε
  by_cases h1 : (b : Matrix ι ι K) * ε = ε
  · rw [if_pos h1]
    obtain ⟨ι₁, instF, instD, Q₁, hcardι₁, hΦ₁, hbranch⟩ :=
      blockGroup_iso_Omega_one Φ hΦ h8 b hb hodd (hPprim ε hε) h1
    letI := instF
    letI := instD
    obtain ⟨Φ₁, hΦ₁eq, hΦ₁nd⟩ := hΦ₁
    have heven : Even (Fintype.card ι₁) := by
      rw [← Module.finrank_fintype_fun_eq_card (R := K)]
      exact CFSG.ComponentClassification.UnbalancedCatalog.even_finrank_of_charTwo Φ₁ hΦ₁nd
    have hn : Fintype.card ι₁ = 2 * (Fintype.card ι₁ / 2) :=
      (Nat.two_mul_div_two_of_even heven).symm
    rcases hbranch with ⟨⟨eG⟩, hne⟩ | ⟨hK2, hcard4, hsolv, hpadic⟩
    · have hcardΩ : Nat.card ↥(StatedOmega Q₁) = Nat.card ↥(StatedOmega ⇑Φ₁) := by
        rw [← hΦ₁eq]
      have hne' : ¬ (Fintype.card K = 2 ∧ Fintype.card ι₁ / 2 = 2 ∧
          ∃ S : Submodule K (ι₁ → K), Module.finrank K S = 2 ∧ ∀ x ∈ S, ⇑Φ₁ x = 0) := by
        rintro ⟨hK2', hn2, S, hS, hS0⟩
        refine hne ⟨hK2', ?_, S, hS, fun x hx => by rw [← hΦ₁eq]; exact hS0 x hx⟩
        rw [hn, hn2]
      have hfac := ggOmW2_factorization_two_card_statedOmega (K := K) (ι := ι₁)
        (f := f) (n := Fintype.card ι₁ / 2) hf Φ₁ hΦ₁nd hn hne'
      rw [Nat.card_congr eG.toEquiv, hcardΩ, hfac, hcardι₁]
    · have hfac2 :
          (Nat.card ↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε)).factorization 2 = 2 := by
        rw [← Nat.multiplicity_eq_factorization Nat.prime_two, ← Nat.padicValNat_def]
        exact hpadic
      rw [hfac2]
      have hf1 : f = 1 := by
        have h2 : 2 ^ f = 2 ^ 1 := by rw [← hf, hK2]; norm_num
        exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) h2
      have hdim : Module.finrank K (LinearMap.range (Matrix.toLin' ε)) = 4 := by
        rw [← hcardι₁, hcard4]
      rw [hf1, hdim]
  · rw [if_neg h1]
    obtain ⟨e, R, m, he, heε, hcase, hOfR, hRm, h1R, hmPos, hcard, h2deg⟩ :=
      ggOmW2_block_data (ggOmW2_G Φ) b hodd hG hgsym hgram (hPprim ε hε) h1
    have hROf : ROf ε = R :=
      ggOmW2d_finset_eq_of_eigDimOn (ROf ε) R (mOf ε) m (hOf ε hε)
        (hOf_pos ε hε h1) hOfR hmPos
    rcases hcase with hcase | ⟨hne, hneadj, hεeq⟩
    · obtain ⟨d, mb, E, instFE, instFinE, hd1, hcardE, hdim, hdeg, ⟨eG⟩⟩ :=
        blockGroup_iso_Omega_unitary Φ hΦ h8 b hb hodd (hPprim ε hε) (hcase ▸ he) h1
      letI := instFE
      letI := instFinE
      have hd2 : (ROf ε).card = 2 * d := by
        rw [hROf, hcard hcase, hcase, hdeg]
      have hd : d = (ROf ε).card / 2 := by
        have h2 : 2 * d = 2 * ((ROf ε).card / 2) := by
          rw [← hd2]; exact hOf_even ε hε h1
        exact Nat.mul_left_cancel (by norm_num : 0 < 2) h2
      have hm : mb = mOf ε := by
        have h2 : 2 * d * mb = 2 * d * mOf ε := by
          rw [hdim, ← hOf_mul ε hε h1, hd2]
        exact Nat.mul_left_cancel (by omega : 0 < 2 * d) h2
      have hE : Fintype.card E = (2 ^ (f * d)) ^ 2 := by
        rw [hcardE, hf]; ring_nf
      have hK : Fintype.card K ^ d = 2 ^ (f * d) := by rw [hf]; ring_nf
      rw [Nat.card_congr eG.toEquiv, hK,
        factorization_two_card_GUFull (m := mb) (g := f * d) hE, hd, hm]
      ring
    · obtain ⟨d, mb, E, instFE, instFinE, hd1, hcardE, hdim, hdeg, ⟨eG⟩⟩ :=
        blockGroup_iso_Omega_linear Φ hΦ h8 b hb hodd (hPprim ε hε) he
          (ggOmW2_formAdj_prim hG hgsym hgram he) (Ne.symm hneadj) hεeq
      letI := instFE
      letI := instFinE
      have hd2 : (ROf ε).card = 2 * d := by
        rw [hROf, h2deg hne, hdeg]
      have hd : d = (ROf ε).card / 2 := by
        have h2 : 2 * d = 2 * ((ROf ε).card / 2) := by
          rw [← hd2]; exact hOf_even ε hε h1
        exact Nat.mul_left_cancel (by norm_num : 0 < 2) h2
      have hm : mb = mOf ε := by
        have h2 : 2 * d * mb = 2 * d * mOf ε := by
          rw [hdim, ← hOf_mul ε hε h1, hd2]
        exact Nat.mul_left_cancel (by omega : 0 < 2 * d) h2
      have hE : Fintype.card E = 2 ^ (f * d) := by
        rw [hcardE, hf]; ring_nf
      rw [Nat.card_congr eG.toEquiv,
        ggOmW2_factorization_two_card_GL (m := mb) (g := f * d) hE, hd, hm]
      ring

private theorem ggOmW2_fixed_block_dim_le {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (b : GL ι K) (hb : b ∈ StatedOmega ⇑Φ)
    (hodd : Odd (orderOf b)) {P : Finset (Matrix ι ι K)}
    (hPprim : ∀ ε ∈ P, IsPrimAdjIdemIn (RingHom.id K) (ggOmW2_G Φ) (ggOmW2_A b) ε)
    (hPorth : ∀ ε ∈ P, ∀ ε' ∈ P, ε ≠ ε' → ε * ε' = 0)
    (ROf : Matrix ι ι K → Finset (AlgebraicClosure K)) (mOf : Matrix ι ι K → ℕ)
    (hblockExp : blockExp true (b : Matrix ι ι K) =
      (eigDim (b : Matrix ι ι K) 1 / 2) * (eigDim (b : Matrix ι ι K) 1 / 2 - 1) +
      ∑ ε ∈ P.filter (fun ε => (b : Matrix ι ι K) * ε ≠ ε),
        (ROf ε).card / 2 * (mOf ε * (mOf ε - 1) / 2))
    (heig1 : eigDim (b : Matrix ι ι K) 1 =
      ∑ ε ∈ P, if (b : Matrix ι ι K) * ε = ε then
        Module.finrank K (LinearMap.range (Matrix.toLin' ε)) else 0)
    (h0 : blockExp true (b : Matrix ι ι K) = 0) :
    ∀ ε ∈ P, (b : Matrix ι ι K) * ε = ε →
      Module.finrank K (LinearMap.range (Matrix.toLin' ε)) ≤ 3 := by
  intro ε hε h1
  have hG : IsUnit (ggOmW2_G Φ).det := ggOmW2_G_isUnit Φ hΦ
  have hgsym : Matrix.transpose ((ggOmW2_G Φ).map (RingHom.id K)) = ggOmW2_G Φ :=
    ggOmW2_G_transpose Φ
  have hgram : ggOmW2_GramIso (ggOmW2_G Φ) b := ggOmW2_gram Φ hb
  have hzero : (eigDim (b : Matrix ι ι K) 1 / 2) *
        (eigDim (b : Matrix ι ι K) 1 / 2 - 1) +
      ∑ ε' ∈ P.filter (fun ε' => (b : Matrix ι ι K) * ε' ≠ ε'),
        (ROf ε').card / 2 * (mOf ε' * (mOf ε' - 1) / 2) = 0 := by
    rw [hblockExp] at h0
    exact h0
  have hA : (eigDim (b : Matrix ι ι K) 1 / 2) *
      (eigDim (b : Matrix ι ι K) 1 / 2 - 1) = 0 := (Nat.add_eq_zero.mp hzero).1
  have hdim : eigDim (b : Matrix ι ι K) 1 ≤ 3 := by
    have hhalf : eigDim (b : Matrix ι ι K) 1 / 2 ≤ 1 := by
      rcases Nat.eq_zero_or_pos (eigDim (b : Matrix ι ι K) 1 / 2) with hz | hp
      · omega
      · rcases Nat.mul_eq_zero.mp hA with h2 | h2 <;> omega
    omega
  have hsingle : ∑ ε' ∈ P, (if (b : Matrix ι ι K) * ε' = ε' then
        Module.finrank K (LinearMap.range (Matrix.toLin' ε')) else 0) =
      (if (b : Matrix ι ι K) * ε = ε then
        Module.finrank K (LinearMap.range (Matrix.toLin' ε)) else 0) := by
    refine Finset.sum_eq_single ε ?_ ?_
    · intro ε' hε' hne'
      by_cases h1' : (b : Matrix ι ι K) * ε' = ε'
      · rw [if_pos h1']
        exact absurd
          (ggOmW2_unique_one_block hG hgsym hgram hodd hPprim hPorth hε' hε h1' h1) hne'
      · rw [if_neg h1']
    · intro hnot; exact absurd hε hnot
  have heq : Module.finrank K (LinearMap.range (Matrix.toLin' ε)) =
      eigDim (b : Matrix ι ι K) 1 := by
    rw [heig1, hsingle, if_pos h1]
  omega

private theorem ggOmW2f_mOf_eq_one {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {G : Matrix ι ι K} {b : GL ι K} {P : Finset (Matrix ι ι K)}
    (hPprim : ∀ ε ∈ P, IsPrimAdjIdemIn (RingHom.id K) G (ggOmW2_A b) ε)
    (ROf : Matrix ι ι K → Finset (AlgebraicClosure K)) (mOf : Matrix ι ι K → ℕ)
    (hOf_pos : ∀ ε ∈ P, (b : Matrix ι ι K) * ε ≠ ε → 0 < mOf ε)
    (hOf_mul : ∀ ε ∈ P, (b : Matrix ι ι K) * ε ≠ ε →
      (ROf ε).card * mOf ε = Module.finrank K (LinearMap.range (Matrix.toLin' ε)))
    (hOf_even : ∀ ε ∈ P, (b : Matrix ι ι K) * ε ≠ ε →
      (ROf ε).card = 2 * ((ROf ε).card / 2))
    (hblockExp : blockExp true (b : Matrix ι ι K) =
      (eigDim (b : Matrix ι ι K) 1 / 2) * (eigDim (b : Matrix ι ι K) 1 / 2 - 1) +
      ∑ ε ∈ P.filter (fun ε => (b : Matrix ι ι K) * ε ≠ ε),
        (ROf ε).card / 2 * (mOf ε * (mOf ε - 1) / 2))
    (h0 : blockExp true (b : Matrix ι ι K) = 0) :
    ∀ ε ∈ P, (b : Matrix ι ι K) * ε ≠ ε → mOf ε = 1 := by
  have hsum0 : ∑ ε ∈ P.filter (fun ε => (b : Matrix ι ι K) * ε ≠ ε),
        (ROf ε).card / 2 * (mOf ε * (mOf ε - 1) / 2) = 0 := by
    rw [hblockExp] at h0
    exact (Nat.add_eq_zero.mp h0).2
  intro ε hε h1
  have hterm : (ROf ε).card / 2 * (mOf ε * (mOf ε - 1) / 2) = 0 :=
    (Finset.sum_eq_zero_iff.mp hsum0) ε (Finset.mem_filter.mpr ⟨hε, h1⟩)
  have hhalf : (ROf ε).card / 2 ≠ 0 := by
    intro hc
    have h0c : (ROf ε).card = 0 := by rw [hOf_even ε hε h1, hc, mul_zero]
    have hm := hOf_mul ε hε h1
    rw [h0c, zero_mul] at hm
    exact ggOmW2_finrank_range_toLin'_ne_zero (hPprim ε hε).2.2.1 hm.symm
  have hmul0 : mOf ε * (mOf ε - 1) / 2 = 0 := by
    rcases Nat.mul_eq_zero.mp hterm with h | h
    · exact absurd h hhalf
    · exact h
  have hle : mOf ε ≤ 1 := by
    by_contra h
    push Not at h
    have h2 : 2 ≤ mOf ε * (mOf ε - 1) := by
      have h1' : 1 ≤ mOf ε - 1 := by omega
      calc 2 = 2 * 1 := by norm_num
        _ ≤ mOf ε * (mOf ε - 1) := Nat.mul_le_mul h h1'
    have h3 : 1 ≤ mOf ε * (mOf ε - 1) / 2 := by omega
    omega
  have hpos := hOf_pos ε hε h1
  omega

private theorem ggOmW2f_statedOmega_abelian {K : Type} [Field K] [CharP K 2]
    {ι : Type} [Fintype ι] [DecidableEq ι] (Q : (ι → K) → K)
    (hQ : ∃ Φ : QuadraticForm K (ι → K),
      ⇑Φ = Q ∧ (QuadraticMap.polarBilin Φ).Nondegenerate)
    (hcard : Fintype.card ι ≤ 3) :
    ∀ a b : ↥(StatedOmega Q), a * b = b * a := by
  obtain ⟨Φ, hΦeq, hΦ⟩ := hQ
  have hIsAlt : (QuadraticMap.polarBilin Φ).IsAlt := by
    intro x
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self,
      ← Nat.cast_smul_eq_nsmul K 2 (Φ x), CharP.cast_eq_zero K 2, zero_smul]
  have hEven : Even (Fintype.card ι) := by
    rw [← Module.finrank_fintype_fun_eq_card K]
    exact LinearMap.BilinForm.IsAlt.even_finrank hIsAlt hΦ
  have hcomm : ∀ g ∈ orthDerived Φ, ∀ g' ∈ orthDerived Φ, g * g' = g' * g := by
    intro g hg g' hg'
    by_cases h2 : Module.finrank K (ι → K) = 2
    · exact commute_of_dicksonHom_eq_one hΦ h2 (orthDerived_le_orthogonalGroup hg)
        (orthDerived_le_orthogonalGroup hg')
        (dicksonHom_eq_one_of_mem_orthDerived hΦ hg)
        (dicksonHom_eq_one_of_mem_orthDerived hΦ hg')
    · have hle : Module.finrank K (ι → K) ≤ 1 := by
        rw [Module.finrank_fintype_fun_eq_card K] at h2 ⊢
        rcases hEven with ⟨k, hk⟩
        omega
      have hg1 := dicksonHom_eq_one_of_mem_orthDerived hΦ hg
      have e1 : g = 1 := by
        simpa using eq_one_of_dicksonHom_eq_one_of_finrank_le_one hΦ hle hg1
      rw [e1, one_mul, mul_one]
  have hmem : ∀ a : ↥(StatedOmega Q),
      CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K (a : GL ι K) ∈ orthDerived Φ := by
    intro a
    have h1 : (a : GL ι K) ∈ (orthDerived Φ).comap
        (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).toMonoidHom := by
      rw [← CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap hΦeq]
      exact a.2
    exact Subgroup.mem_comap.mp h1
  intro a b
  refine Subtype.ext ?_
  apply (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).injective
  show CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K ((a : GL ι K) * (b : GL ι K)) =
    CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K ((b : GL ι K) * (a : GL ι K))
  rw [map_mul, map_mul]
  exact hcomm _ (hmem a) _ (hmem b)

private theorem ggOmW2_blocks_abelian {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι)
    (b : GL ι K) (hb : b ∈ StatedOmega ⇑Φ)
    (hodd : Odd (orderOf b)) {P : Finset (Matrix ι ι K)}
    (hPprim : ∀ ε ∈ P, IsPrimAdjIdemIn (RingHom.id K) (ggOmW2_G Φ) (ggOmW2_A b) ε)
    (hPorth : ∀ ε ∈ P, ∀ ε' ∈ P, ε ≠ ε' → ε * ε' = 0)
    (ROf : Matrix ι ι K → Finset (AlgebraicClosure K)) (mOf : Matrix ι ι K → ℕ)
    (hOf : ∀ ε ∈ P, ∀ l, eigDimOn (b : Matrix ι ι K) ε l =
      if l ∈ ROf ε then mOf ε else 0)
    (hOf_pos : ∀ ε ∈ P, (b : Matrix ι ι K) * ε ≠ ε → 0 < mOf ε)
    (hOf_mul : ∀ ε ∈ P, (b : Matrix ι ι K) * ε ≠ ε →
      (ROf ε).card * mOf ε = Module.finrank K (LinearMap.range (Matrix.toLin' ε)))
    (hOf_even : ∀ ε ∈ P, (b : Matrix ι ι K) * ε ≠ ε →
      (ROf ε).card = 2 * ((ROf ε).card / 2))
    (hblockExp : blockExp true (b : Matrix ι ι K) =
      (eigDim (b : Matrix ι ι K) 1 / 2) * (eigDim (b : Matrix ι ι K) 1 / 2 - 1) +
      ∑ ε ∈ P.filter (fun ε => (b : Matrix ι ι K) * ε ≠ ε),
        (ROf ε).card / 2 * (mOf ε * (mOf ε - 1) / 2))
    (heig1 : eigDim (b : Matrix ι ι K) 1 =
      ∑ ε ∈ P, if (b : Matrix ι ι K) * ε = ε then
        Module.finrank K (LinearMap.range (Matrix.toLin' ε)) else 0)
    (h0 : blockExp true (b : Matrix ι ι K) = 0) :
    ∀ ε ∈ P, ∀ x ∈ glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε,
      ∀ y ∈ glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε, x * y = y * x := by
  intro ε hε x hx y hy
  have hG : IsUnit (ggOmW2_G Φ).det := ggOmW2_G_isUnit Φ hΦ
  have hgsym : Matrix.transpose ((ggOmW2_G Φ).map (RingHom.id K)) = ggOmW2_G Φ :=
    ggOmW2_G_transpose Φ
  have hgram : ggOmW2_GramIso (ggOmW2_G Φ) b := ggOmW2_gram Φ hb
  by_cases h1 : (b : Matrix ι ι K) * ε = ε
  · have hdimle : Module.finrank K (LinearMap.range (Matrix.toLin' ε)) ≤ 3 :=
      ggOmW2_fixed_block_dim_le Φ hΦ b hb hodd hPprim hPorth ROf mOf
        hblockExp heig1 h0 ε hε h1
    obtain ⟨ι₁, _, _, Q₁, hcard₁, hΦ₁ex, hdisj⟩ :=
      blockGroup_iso_Omega_one Φ hΦ h8 b hb hodd (hPprim ε hε) h1
    have hcardle : Fintype.card ι₁ ≤ 3 := hcard₁.trans_le hdimle
    have hab : ∀ a b : ↥(StatedOmega Q₁), a * b = b * a :=
      ggOmW2f_statedOmega_abelian Q₁ hΦ₁ex hcardle
    rcases hdisj with ⟨⟨eG⟩, _⟩ | ⟨_, hcard4, _, _⟩
    · have hcomm : ∀ a b : ↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε),
          a * b = b * a := by
        intro a b
        exact eG.injective (by
          rw [map_mul, map_mul]
          exact hab (eG a) (eG b))
      exact Subtype.ext (congrArg (fun z :
        ↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε) =>
          ((z : ↥(StatedOmega ⇑Φ)) : GL ι K)) (hcomm ⟨x, hx⟩ ⟨y, hy⟩))
    · omega
  · have hm1 : ∀ ε ∈ P, (b : Matrix ι ι K) * ε ≠ ε → mOf ε = 1 :=
      ggOmW2f_mOf_eq_one (G := ggOmW2_G Φ) hPprim ROf mOf hOf_pos hOf_mul hOf_even hblockExp h0
    obtain ⟨e, R, m, he, _heε, hcase, hOfR, hRm, _h1R, hmPos, hcard, h2deg⟩ :=
      ggOmW2_block_data (ggOmW2_G Φ) b hodd hG hgsym hgram (hPprim ε hε) h1
    have hRmem : ∀ l, l ∈ ROf ε ↔ l ∈ R := by
      intro l
      constructor
      · intro hl
        by_contra hnot
        have h2l := hOfR l
        rw [if_neg hnot, hOf ε hε l, if_pos hl] at h2l
        exact (hOf_pos ε hε h1).ne' h2l
      · intro hl
        by_contra hnot
        have h2l := hOfR l
        rw [if_pos hl, hOf ε hε l, if_neg hnot] at h2l
        exact hmPos.ne' h2l.symm
    have hROf : ROf ε = R := Finset.ext hRmem
    have hm_eq : m = mOf ε := by
      have hcard_ne : R.card ≠ 0 := by
        intro hc
        have hm := hRm
        rw [hc, zero_mul] at hm
        exact ggOmW2_finrank_range_toLin'_ne_zero (hPprim ε hε).2.2.1 hm.symm
      obtain ⟨l, hl⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hcard_ne)
      have h1l : eigDimOn (b : Matrix ι ι K) ε l = m := by rw [hOfR l, if_pos hl]
      have h2l : eigDimOn (b : Matrix ι ι K) ε l = mOf ε := by
        rw [hOf ε hε l, if_pos (by rw [hROf]; exact hl)]
      rw [h1l] at h2l
      exact h2l
    rcases hcase with hcase | ⟨hne, hneadj, hεeq⟩
    · obtain ⟨d, mm, E, _instF, _instFin, h1d, _hcardE, hdim, hdeg, ⟨eG⟩⟩ :=
        blockGroup_iso_Omega_unitary Φ hΦ h8 b hb hodd (hPprim ε hε) (hcase ▸ he) h1
      have hd2 : (ROf ε).card = 2 * d := by rw [hROf, hcard hcase, hcase, hdeg]
      have hm1' : mm = 1 := by
        have h2 : 2 * d * mm = 2 * d * 1 := by
          rw [hdim, ← hRm, hm_eq, hm1 ε hε h1, ← hROf, hd2]
        exact Nat.mul_left_cancel (by omega : 0 < 2 * d) h2
      rw [hm1'] at eG
      have hGU1 : ∀ a b : ↥(GUFull 1 (Fintype.card K ^ d) E), a * b = b * a := by
        intro a b
        have hGL1 : ∀ p q : GL (Fin 1) E, p * q = q * p := by
          intro p q
          refine Units.ext ?_
          ext i j
          fin_cases i
          fin_cases j
          simp [Matrix.mul_apply, mul_comm]
        exact Subtype.ext (hGL1 a.1 b.1)
      have hcomm : ∀ a b : ↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε),
          a * b = b * a := by
        intro a b
        exact eG.injective (by
          rw [map_mul, map_mul]
          exact hGU1 (eG a) (eG b))
      exact Subtype.ext (congrArg (fun z :
        ↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε) =>
          ((z : ↥(StatedOmega ⇑Φ)) : GL ι K)) (hcomm ⟨x, hx⟩ ⟨y, hy⟩))
    · obtain ⟨d, mm, E, _instF, _instFin, h1d, _hcardE, hdim, hdeg, ⟨eG⟩⟩ :=
        blockGroup_iso_Omega_linear Φ hΦ h8 b hb hodd (hPprim ε hε) he
          (ggOmW2_formAdj_prim hG hgsym hgram he) (Ne.symm hneadj) hεeq
      have hd2 : (ROf ε).card = 2 * d := by rw [hROf, h2deg hne, hdeg]
      have hm1' : mm = 1 := by
        have h2 : 2 * d * mm = 2 * d * 1 := by
          rw [hdim, ← hRm, hm_eq, hm1 ε hε h1, ← hROf, hd2]
        exact Nat.mul_left_cancel (by omega : 0 < 2 * d) h2
      rw [hm1'] at eG
      have hGL1 : ∀ p q : GL (Fin 1) E, p * q = q * p := by
        intro p q
        refine Units.ext ?_
        ext i j
        fin_cases i
        fin_cases j
        simp [Matrix.mul_apply, mul_comm]
      have hcomm : ∀ a b : ↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε),
          a * b = b * a := by
        intro a b
        exact eG.injective (by
          rw [map_mul, map_mul]
          exact hGL1 (eG a) (eG b))
      exact Subtype.ext (congrArg (fun z :
        ↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε) =>
          ((z : ↥(StatedOmega ⇑Φ)) : GL ι K)) (hcomm ⟨x, hx⟩ ⟨y, hy⟩))

theorem two_part_centralizer_Omega {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] [CharP K 2] {f : ℕ} (hf : Fintype.card K = 2 ^ f)
    (Φ : QuadraticForm K (ι → K)) (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (h8 : 8 ≤ Fintype.card ι) (b : GL ι K) (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b)) :
    (Nat.card ↥((Subgroup.centralizer {b}).comap (StatedOmega ⇑Φ).subtype)).factorization 2 =
      f * blockExp true (b : Matrix ι ι K) := by
  classical
  obtain ⟨P, hPprim, hPorth, hPsum, hPcommBlock, hPsup, hPcard⟩ :=
    centralizer_block_decomp_Omega Φ hΦ h8 b hb hodd
  have hG : IsUnit (ggOmW2_G Φ).det := ggOmW2_G_isUnit Φ hΦ
  have hgsym : Matrix.transpose ((ggOmW2_G Φ).map (RingHom.id K)) = ggOmW2_G Φ :=
    ggOmW2_G_transpose Φ
  have hgram : ggOmW2_GramIso (ggOmW2_G Φ) b := ggOmW2_gram Φ hb
  have hbA : (b : Matrix ι ι K) ∈ ggOmW2_A b := Algebra.subset_adjoin (by simp)
  let ROf (ε : Matrix ι ι K) : Finset (AlgebraicClosure K) :=
    if hε : ε ∈ P then
      if h1 : (b : Matrix ι ι K) * ε = ε then {1}
      else Classical.choose
        (Classical.choose_spec (ggOmW2_block_data (ggOmW2_G Φ) b hodd hG hgsym hgram
          (hPprim ε hε) h1))
    else ∅
  let mOf (ε : Matrix ι ι K) : ℕ :=
    if hε : ε ∈ P then
      if h1 : (b : Matrix ι ι K) * ε = ε then
        Module.finrank K (LinearMap.range (Matrix.toLin' ε))
      else Classical.choose
        (Classical.choose_spec (Classical.choose_spec
          (ggOmW2_block_data (ggOmW2_G Φ) b hodd hG hgsym hgram (hPprim ε hε) h1)))
    else 0
  have hOf : ∀ ε (hε : ε ∈ P), ∀ l, eigDimOn (b : Matrix ι ι K) ε l =
      if l ∈ ROf ε then mOf ε else 0 := by
    intro ε hε l
    simp only [ROf, mOf, dif_pos hε]
    by_cases h1 : (b : Matrix ι ι K) * ε = ε
    · simp only [dif_pos h1]
      by_cases hl : l = 1
      · subst hl
        rw [if_pos (Finset.mem_singleton_self 1)]
        exact (ggOmW2_eigDimOn_primAdj_one hG hgsym hgram hodd (hPprim ε hε)).trans (if_pos h1)
      · rw [if_neg (fun h => hl (Finset.mem_singleton.mp h))]
        exact ggOmW2_eigDimOn_eq_zero_of_b_mul_eq hodd
          (ggOmW2_one_block_prim hG hgsym hgram hodd (hPprim ε hε) h1) h1 hl
    · simp only [dif_neg h1]
      exact (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
        (ggOmW2_block_data (ggOmW2_G Φ) b hodd hG hgsym hgram (hPprim ε hε) h1)))).2.2.2.1 l
  have hOf_one : ∀ ε (hε : ε ∈ P),
      (b : Matrix ι ι K) * ε ≠ ε → 1 ∉ ROf ε := by
    intro ε hε h1
    simp only [ROf, dif_pos hε, dif_neg h1]
    exact (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
      (ggOmW2_block_data (ggOmW2_G Φ) b hodd hG hgsym hgram (hPprim ε hε) h1)))).2.2.2.2.2.1
  have hOf_pos : ∀ ε (hε : ε ∈ P),
      (b : Matrix ι ι K) * ε ≠ ε → 0 < mOf ε := by
    intro ε hε h1
    simp only [mOf, dif_pos hε, dif_neg h1]
    exact (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
      (ggOmW2_block_data (ggOmW2_G Φ) b hodd hG hgsym hgram (hPprim ε hε) h1)))).2.2.2.2.2.2.1
  have hOf_mul : ∀ ε (hε : ε ∈ P),
      (b : Matrix ι ι K) * ε ≠ ε →
      (ROf ε).card * mOf ε = Module.finrank K (LinearMap.range (Matrix.toLin' ε)) := by
    intro ε hε h1
    simp only [ROf, mOf, dif_pos hε, dif_neg h1]
    exact (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
      (ggOmW2_block_data (ggOmW2_G Φ) b hodd hG hgsym hgram (hPprim ε hε) h1)))).2.2.2.2.1
  have hOf_even : ∀ ε (hε : ε ∈ P), (b : Matrix ι ι K) * ε ≠ ε →
      (ROf ε).card = 2 * ((ROf ε).card / 2) := by
    intro ε hε h1
    exact ggOmW2_ROf_even Φ hΦ b hb hodd hPprim ROf mOf hOf hOf_pos
      hε h1
  have heig1 : eigDim (b : Matrix ι ι K) 1 = ∑ ε ∈ P,
      if (b : Matrix ι ι K) * ε = ε then
        Module.finrank K (LinearMap.range (Matrix.toLin' ε)) else 0 :=
    ggOmW2_eigDim_one hG hgsym hgram hodd hPprim hPorth hPsum
  have hblockExp : blockExp true (b : Matrix ι ι K) =
      (eigDim (b : Matrix ι ι K) 1 / 2) * (eigDim (b : Matrix ι ι K) 1 / 2 - 1) +
      ∑ ε ∈ P.filter (fun ε => (b : Matrix ι ι K) * ε ≠ ε),
        (ROf ε).card / 2 * (mOf ε * (mOf ε - 1) / 2) :=
    ggOmW2_blockExp_eq_true (ggOmW2_G Φ) b hodd hG hgsym hgram hPprim hPorth hPsum ROf mOf hOf
      hOf_one hOf_pos hOf_even
  have hblock := ggOmW2_block_order Φ hΦ h8 hf b hb hodd hPprim ROf mOf hOf
    hOf_pos hOf_mul hOf_even
  have horder :
      (Nat.card ↥((Subgroup.centralizer {b}).comap (StatedOmega ⇑Φ).subtype)).factorization 2 =
      f * ((eigDim (b : Matrix ι ι K) 1 / 2) * (eigDim (b : Matrix ι ι K) 1 / 2 - 1) +
        ∑ ε ∈ P.filter (fun ε => (b : Matrix ι ι K) * ε ≠ ε),
          (ROf ε).card / 2 * (mOf ε * (mOf ε - 1) / 2)) := by
    have hcardprod :
        (Nat.card ↥((Subgroup.centralizer {b}).comap (StatedOmega ⇑Φ).subtype)).factorization 2 =
        ∑ ε ∈ P,
          (Nat.card ↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε)).factorization 2 := by
      rw [hPcard, Nat.factorization_prod (fun ε _ => by
        haveI : Nonempty ↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε) :=
          ⟨⟨1, (glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε).one_mem⟩⟩
        exact Nat.card_pos.ne')]
      simp only [Finsupp.coe_finset_sum, Finset.sum_apply]
    have hsum : ∑ ε ∈ P, (if (b : Matrix ι ι K) * ε = ε then
            (Module.finrank K (LinearMap.range (Matrix.toLin' ε)) / 2) *
              (Module.finrank K (LinearMap.range (Matrix.toLin' ε)) / 2 - 1)
            else (ROf ε).card / 2 * (mOf ε * (mOf ε - 1) / 2)) =
        (eigDim (b : Matrix ι ι K) 1 / 2) * (eigDim (b : Matrix ι ι K) 1 / 2 - 1) +
          ∑ ε ∈ P.filter (fun ε => (b : Matrix ι ι K) * ε ≠ ε),
            (ROf ε).card / 2 * (mOf ε * (mOf ε - 1) / 2) := by
      rw [← Finset.sum_filter_add_sum_filter_not P
        (fun ε => (b : Matrix ι ι K) * ε = ε)
        (fun ε => if (b : Matrix ι ι K) * ε = ε then
          (Module.finrank K (LinearMap.range (Matrix.toLin' ε)) / 2) *
            (Module.finrank K (LinearMap.range (Matrix.toLin' ε)) / 2 - 1)
          else (ROf ε).card / 2 * (mOf ε * (mOf ε - 1) / 2))]
      congr 1
      · rw [Finset.sum_congr rfl (fun ε hε => if_pos (Finset.mem_filter.mp hε).2)]
        have hf1 : eigDim (b : Matrix ι ι K) 1 =
            ∑ ε ∈ P.filter (fun ε => (b : Matrix ι ι K) * ε = ε),
              Module.finrank K (LinearMap.range (Matrix.toLin' ε)) := by
          rw [heig1, ← Finset.sum_filter]
        rw [hf1]
        rcases Finset.eq_empty_or_nonempty
          (P.filter (fun ε => (b : Matrix ι ι K) * ε = ε)) with h | ⟨ε₁, hε₁⟩
        · rw [h, Finset.sum_empty, Finset.sum_empty]
          norm_num
        · have hsingle : P.filter (fun ε =>
              (b : Matrix ι ι K) * ε = ε) = {ε₁} := by
            refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hε₁, ?_⟩
            intro ε hε
            exact ggOmW2_unique_one_block hG hgsym hgram hodd hPprim hPorth
              (Finset.mem_filter.mp hε).1 (Finset.mem_filter.mp hε₁).1
              (Finset.mem_filter.mp hε).2 (Finset.mem_filter.mp hε₁).2
          rw [hsingle, Finset.sum_singleton, Finset.sum_singleton]
      · rw [Finset.sum_congr rfl (fun ε hε => if_neg (Finset.mem_filter.mp hε).2)]
    rw [hcardprod]
    rw [Finset.sum_congr rfl hblock]
    rw [← Finset.mul_sum, hsum]
  rw [hblockExp]
  exact horder

theorem commutative_centralizer_of_blockExp_eq_zero_Omega {ι K : Type} [Fintype ι]
    [DecidableEq ι] [Field K] [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι)
    (b : GL ι K) (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b))
    (h0 : blockExp true (b : Matrix ι ι K) = 0) :
    ∀ x ∈ (Subgroup.centralizer {b}).comap (StatedOmega ⇑Φ).subtype,
      ∀ y ∈ (Subgroup.centralizer {b}).comap (StatedOmega ⇑Φ).subtype, x * y = y * x := by
  classical
  obtain ⟨P, hPprim, hPorth, hPsum, hPcommBlock, hPsup, hPcard⟩ :=
    centralizer_block_decomp_Omega Φ hΦ h8 b hb hodd
  have hG : IsUnit (ggOmW2_G Φ).det := ggOmW2_G_isUnit Φ hΦ
  have hgsym : Matrix.transpose ((ggOmW2_G Φ).map (RingHom.id K)) = ggOmW2_G Φ :=
    ggOmW2_G_transpose Φ
  have hgram : ggOmW2_GramIso (ggOmW2_G Φ) b := ggOmW2_gram Φ hb
  have hbA : (b : Matrix ι ι K) ∈ ggOmW2_A b := Algebra.subset_adjoin (by simp)
  let ROf (ε : Matrix ι ι K) : Finset (AlgebraicClosure K) :=
    if hε : ε ∈ P then
      if h1 : (b : Matrix ι ι K) * ε = ε then {1}
      else Classical.choose
        (Classical.choose_spec (ggOmW2_block_data (ggOmW2_G Φ) b hodd hG hgsym hgram
          (hPprim ε hε) h1))
    else ∅
  let mOf (ε : Matrix ι ι K) : ℕ :=
    if hε : ε ∈ P then
      if h1 : (b : Matrix ι ι K) * ε = ε then
        Module.finrank K (LinearMap.range (Matrix.toLin' ε))
      else Classical.choose
        (Classical.choose_spec (Classical.choose_spec
          (ggOmW2_block_data (ggOmW2_G Φ) b hodd hG hgsym hgram (hPprim ε hε) h1)))
    else 0
  have hOf : ∀ ε (hε : ε ∈ P), ∀ l, eigDimOn (b : Matrix ι ι K) ε l =
      if l ∈ ROf ε then mOf ε else 0 := by
    intro ε hε l
    simp only [ROf, mOf, dif_pos hε]
    by_cases h1 : (b : Matrix ι ι K) * ε = ε
    · simp only [dif_pos h1]
      by_cases hl : l = 1
      · subst hl
        rw [if_pos (Finset.mem_singleton_self 1)]
        exact (ggOmW2_eigDimOn_primAdj_one hG hgsym hgram hodd (hPprim ε hε)).trans (if_pos h1)
      · rw [if_neg (fun h => hl (Finset.mem_singleton.mp h))]
        exact ggOmW2_eigDimOn_eq_zero_of_b_mul_eq hodd
          (ggOmW2_one_block_prim hG hgsym hgram hodd (hPprim ε hε) h1) h1 hl
    · simp only [dif_neg h1]
      exact (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
        (ggOmW2_block_data (ggOmW2_G Φ) b hodd hG hgsym hgram (hPprim ε hε) h1)))).2.2.2.1 l
  have hOf_one : ∀ ε (hε : ε ∈ P),
      (b : Matrix ι ι K) * ε ≠ ε → 1 ∉ ROf ε := by
    intro ε hε h1
    simp only [ROf, dif_pos hε, dif_neg h1]
    exact (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
      (ggOmW2_block_data (ggOmW2_G Φ) b hodd hG hgsym hgram (hPprim ε hε) h1)))).2.2.2.2.2.1
  have hOf_pos : ∀ ε (hε : ε ∈ P),
      (b : Matrix ι ι K) * ε ≠ ε → 0 < mOf ε := by
    intro ε hε h1
    simp only [mOf, dif_pos hε, dif_neg h1]
    exact (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
      (ggOmW2_block_data (ggOmW2_G Φ) b hodd hG hgsym hgram (hPprim ε hε) h1)))).2.2.2.2.2.2.1
  have hOf_mul : ∀ ε (hε : ε ∈ P),
      (b : Matrix ι ι K) * ε ≠ ε →
      (ROf ε).card * mOf ε = Module.finrank K (LinearMap.range (Matrix.toLin' ε)) := by
    intro ε hε h1
    simp only [ROf, mOf, dif_pos hε, dif_neg h1]
    exact (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
      (ggOmW2_block_data (ggOmW2_G Φ) b hodd hG hgsym hgram (hPprim ε hε) h1)))).2.2.2.2.1
  have hOf_even : ∀ ε (hε : ε ∈ P), (b : Matrix ι ι K) * ε ≠ ε →
      (ROf ε).card = 2 * ((ROf ε).card / 2) := by
    intro ε hε h1
    exact ggOmW2_ROf_even Φ hΦ b hb hodd hPprim ROf mOf hOf hOf_pos
      hε h1
  have heig1 : eigDim (b : Matrix ι ι K) 1 = ∑ ε ∈ P,
      if (b : Matrix ι ι K) * ε = ε then
        Module.finrank K (LinearMap.range (Matrix.toLin' ε)) else 0 :=
    ggOmW2_eigDim_one hG hgsym hgram hodd hPprim hPorth hPsum
  have hblockExp : blockExp true (b : Matrix ι ι K) =
      (eigDim (b : Matrix ι ι K) 1 / 2) * (eigDim (b : Matrix ι ι K) 1 / 2 - 1) +
      ∑ ε ∈ P.filter (fun ε => (b : Matrix ι ι K) * ε ≠ ε),
        (ROf ε).card / 2 * (mOf ε * (mOf ε - 1) / 2) :=
    ggOmW2_blockExp_eq_true (ggOmW2_G Φ) b hodd hG hgsym hgram hPprim hPorth hPsum ROf mOf hOf
      hOf_one hOf_pos hOf_even
  have habel : ∀ ε ∈ P, ∀ x ∈ glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε,
      ∀ y ∈ glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε, x * y = y * x :=
    ggOmW2_blocks_abelian Φ hΦ h8 b hb hodd hPprim hPorth ROf mOf hOf hOf_pos
      hOf_mul hOf_even hblockExp heig1 h0
  have hCcomm : ∀ x ∈ (Subgroup.centralizer {b}).comap (StatedOmega ⇑Φ).subtype,
      ∀ y ∈ (Subgroup.centralizer {b}).comap (StatedOmega ⇑Φ).subtype, x * y = y * x := by
    intro x hx y hy
    rw [← hPsup] at hx hy
    let H : Matrix ι ι K → Subgroup (StatedOmega ⇑Φ) :=
      fun ε => glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε
    have hx' : x ∈ ⨆ ε ∈ P, H ε := hx
    have hy' : y ∈ ⨆ ε ∈ P, H ε := hy
    have hmem : ∀ y ∈ (⨆ ε ∈ P, H ε), x * y = y * x := by
      refine Subgroup.iSup_induction' (fun ε => ⨆ (_ : ε ∈ P), H ε)
        (C := fun x _ => ∀ y ∈ (⨆ ε ∈ P, H ε), x * y = y * x) ?_ ?_ ?_ hx'
      · intro i x hx
        refine Subgroup.iSup_induction' (fun (_ : i ∈ P) => H i)
          (C := fun x _ => ∀ y ∈ (⨆ ε ∈ P, H ε), x * y = y * x) ?_ ?_ ?_ hx
        · intro hi x hx
          intro y hy
          refine Subgroup.iSup_induction' (fun ε => ⨆ (_ : ε ∈ P), H ε)
            (C := fun y _ => x * y = y * x) ?_ ?_ ?_ hy
          · intro j y hy
            refine Subgroup.iSup_induction' (fun (_ : j ∈ P) => H j)
              (C := fun y _ => x * y = y * x) ?_ ?_ ?_ hy
            · intro hj y hy
              by_cases heq : i = j
              · subst heq; exact habel i hi x hx y hy
              · exact hPcommBlock i hi j hj heq x hx y hy
            · rw [mul_one, one_mul]
            · intro y1 y2 hy1 hy2 ih1 ih2
              rw [← mul_assoc, ih1, mul_assoc, ih2, mul_assoc]
          · rw [mul_one, one_mul]
          · intro y1 y2 hy1 hy2 ih1 ih2
            rw [← mul_assoc, ih1, mul_assoc, ih2, mul_assoc]
        · intro y hy; rw [one_mul, mul_one]
        · intro x1 x2 hx1 hx2 ih1 ih2 y hy
          rw [mul_assoc, ih2 y hy, ← mul_assoc, ih1 y hy, mul_assoc]
      · intro y hy; rw [one_mul, mul_one]
      · intro x1 x2 hx1 hx2 ih1 ih2 y hy
        rw [mul_assoc, ih2 y hy, ← mul_assoc, ih1 y hy, mul_assoc]
    exact hmem y hy'
  exact hCcomm

end CFSG.StandardType.ClassicalBlocks
