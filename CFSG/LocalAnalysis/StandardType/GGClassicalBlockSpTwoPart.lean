module

public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockDefs
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockGUOrder
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockSpDecomp
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockSpIsoOneLinear
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockSpIsoUnitary
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockDict
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockDecomp
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoAdj
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.StepA2
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3ProofModelL3
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14SpAMain
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
public import CFSG.LieType.Steinberg.CentralExt.SpinPlusCentrallyClosed
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIIL3Rigid
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotAlignCores
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR7Split
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SmallJ
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTwistedFusion
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphLinearEnd
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphLinearGlobal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphOmegaGlobal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphOmegaNeighbour
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphUnitaryEnd
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphUnitaryPower
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14BlShape
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14Partner
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerModel
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerSp
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14Transfer
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotOmegaRowUniqueStep
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotParamMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRecognizeFieldFour
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotAlignImagesSwap
public import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
public import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
public import Certificates.Certificate7233Base

public section

namespace CFSG.StandardType.ClassicalBlocks

open CFSG CFSG.Open CFSG.StandardType CFSG.StandardType.ClassicalPosition Matrix

private theorem ggJSt1_factorization_two_card_GL {E : Type} [Field E] [Fintype E] {m g : ℕ}
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

private theorem ggJSt1_factorization_two_card_statedSp {K : Type} [Field K] [Fintype K] {n f : ℕ}
    (hK : Fintype.card K = 2 ^ f) :
    (Nat.card ↥(StatedSp n K)).factorization 2 = f * (n * n) := by
  have h := CFSG.SeitzReduction.SymplecticPilot.factorization_two_card_statedSp (K := K) (f := f)
    (by rw [Nat.card_eq_fintype_card, hK]) n
  rw [h]
  ring

open Classical

private abbrev ggJSt1_A {K : Type} [Field K] {n : ℕ} (b : GL (Fin n ⊕ Fin n) K) :
    Subalgebra K (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) :=
  Algebra.adjoin K (Units.val '' ({b} : Set (GL (Fin n ⊕ Fin n) K)))

private abbrev ggJSt1_G (K : Type) [Field K] (n : ℕ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  Matrix.fromBlocks 0 1 (-1) 0

private abbrev ggJSt1_Ginv (K : Type) [Field K] (n : ℕ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  Matrix.fromBlocks 0 (-1) 1 0

private lemma ggJSt1_isUnit_det_G (K : Type) [Field K] (n : ℕ) :
    IsUnit (ggJSt1_G K n).det := by
  refine (Matrix.isUnit_iff_isUnit_det (ggJSt1_G K n)).mp ?_
  rw [isUnit_iff_exists_inv]
  refine ⟨ggJSt1_Ginv K n, ?_⟩
  rw [ggJSt1_G, ggJSt1_Ginv, Matrix.fromBlocks_multiply]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.one_apply]

private lemma ggJSt1_G_transpose (K : Type) [Field K] [CharP K 2] (n : ℕ) :
    Matrix.transpose (ggJSt1_G K n) = ggJSt1_G K n := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [ggJSt1_G, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, CharTwo.neg_eq, Matrix.one_apply,
      eq_comm]

private lemma ggJSt1_gram {K : Type} [Field K] {n : ℕ} (b : GL (Fin n ⊕ Fin n) K)
    (hb : b ∈ StatedSp n K) :
    Matrix.transpose ((b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K).map (RingHom.id K)) *
      ggJSt1_G K n * (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = ggJSt1_G K n := by
  simpa [ggJSt1_G, Matrix.map_id] using (CFSG.Open.StatedAPI.mem_statedSp_iff.mp hb)

private lemma ggJSt1_commute {K : Type} [Field K] {n : ℕ} (b : GL (Fin n ⊕ Fin n) K)
    {x y : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K} (hx : x ∈ ggJSt1_A b)
    (hy : y ∈ ggJSt1_A b) : x * y = y * x := by
  let A : Subalgebra K (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) := ggJSt1_A b
  have hcommP : (Units.val '' ({b} : Set (GL (Fin n ⊕ Fin n) K)) :
      Set (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)).Pairwise Commute := by
    rintro x ⟨s, hs, rfl⟩ y ⟨t, ht, rfl⟩ _
    rw [Set.mem_singleton_iff] at hs ht
    subst hs
    subst ht
    exact Commute.refl _
  letI : CommRing A := Algebra.adjoinCommRingOfComm K hcommP
  have h := mul_comm (⟨x, hx⟩ : A) (⟨y, hy⟩ : A)
  exact congrArg Subtype.val h

private lemma ggJSt1_formAdj_mem {K : Type} [Field K] [Finite K] {n : ℕ}
    (b : GL (Fin n ⊕ Fin n) K) (hb : b ∈ StatedSp n K)
    {a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K} (ha : a ∈ ggJSt1_A b) :
    formAdj (RingHom.id K) (ggJSt1_G K n) a ∈ ggJSt1_A b := by
  refine CFSG.StandardType.ClassicalPosition.Geo.formAdj_mem_adjoin (RingHom.id K)
    (ggJSt1_isUnit_det_G K n) (S := {b}) ?_ ha
  intro s hs
  rw [Set.mem_singleton_iff] at hs
  rw [hs]
  exact ggJSt1_gram b hb

private lemma ggJSt1_formAdj_formAdj {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (b : GL (Fin n ⊕ Fin n) K) (hb : b ∈ StatedSp n K)
    {a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K} (ha : a ∈ ggJSt1_A b) :
    formAdj (RingHom.id K) (ggJSt1_G K n) (formAdj (RingHom.id K) (ggJSt1_G K n) a) = a := by
  refine CFSG.StandardType.ClassicalPosition.Geo.formAdj_formAdj (RingHom.id K) (fun x => rfl)
    (ggJSt1_isUnit_det_G K n) ?_ a
  have hmid : (ggJSt1_G K n).map (RingHom.id K) = ggJSt1_G K n := by
    ext i j
    rfl
  rw [hmid]
  exact ggJSt1_G_transpose K n

private lemma ggJSt1_formAdj_idem {K : Type} [Field K] {n : ℕ}
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K} (he : IsIdempotentElem e) :
    IsIdempotentElem (formAdj (RingHom.id K) (ggJSt1_G K n) e) := by
  have hG := ggJSt1_isUnit_det_G K n
  have h : formAdj (RingHom.id K) (ggJSt1_G K n) (e * e) =
      formAdj (RingHom.id K) (ggJSt1_G K n) e * formAdj (RingHom.id K) (ggJSt1_G K n) e :=
    CFSG.StandardType.ClassicalPosition.Geo.formAdj_mul (RingHom.id K) hG e e
  rw [isIdempotentElem_iff] at he ⊢
  rw [he] at h
  exact h.symm

private lemma ggJSt1_formAdj_zero {K : Type} [Field K] {n : ℕ} :
    formAdj (RingHom.id K) (ggJSt1_G K n) 0 = 0 := by
  simp [formAdj]

private lemma ggJSt1_formAdj_prim {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (b : GL (Fin n ⊕ Fin n) K) (hb : b ∈ StatedSp n K)
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K} (he : IsPrimIdemIn (ggJSt1_A b) e) :
    IsPrimIdemIn (ggJSt1_A b) (formAdj (RingHom.id K) (ggJSt1_G K n) e) := by
  have hG := ggJSt1_isUnit_det_G K n
  have hmem := ggJSt1_formAdj_mem b hb he.1
  have hidem := ggJSt1_formAdj_idem he.2.1
  have hne : formAdj (RingHom.id K) (ggJSt1_G K n) e ≠ 0 := by
    intro h0
    have h := congrArg (formAdj (RingHom.id K) (ggJSt1_G K n)) h0
    rw [ggJSt1_formAdj_formAdj b hb he.1, ggJSt1_formAdj_zero] at h
    exact he.2.2.1 h
  refine ⟨hmem, hidem, hne, ?_⟩
  intro f hfA hfid hfe
  have hfmem := ggJSt1_formAdj_mem b hb hfA
  have hfidem := ggJSt1_formAdj_idem hfid
  have hkey : formAdj (RingHom.id K) (ggJSt1_G K n) f * e =
      formAdj (RingHom.id K) (ggJSt1_G K n) f := by
    have h : e * formAdj (RingHom.id K) (ggJSt1_G K n) f =
        formAdj (RingHom.id K) (ggJSt1_G K n) f := by
      have h := congrArg (formAdj (RingHom.id K) (ggJSt1_G K n)) hfe
      rw [CFSG.StandardType.ClassicalPosition.Geo.formAdj_mul (RingHom.id K) hG f
        (formAdj (RingHom.id K) (ggJSt1_G K n) e),
        ggJSt1_formAdj_formAdj b hb he.1] at h
      exact h
    exact (ggJSt1_commute b hfmem he.1).trans h
  rcases he.2.2.2 (formAdj (RingHom.id K) (ggJSt1_G K n) f) hfmem hfidem hkey with h0 | hee
  · left
    have h := congrArg (formAdj (RingHom.id K) (ggJSt1_G K n)) h0
    rw [ggJSt1_formAdj_formAdj b hb hfA, ggJSt1_formAdj_zero] at h
    exact h
  · right
    have h := congrArg (formAdj (RingHom.id K) (ggJSt1_G K n)) hee
    rw [ggJSt1_formAdj_formAdj b hb hfA] at h
    exact h

private lemma ggJSt1_prim_orthogonal {K : Type} [Field K] {n : ℕ}
    (b : GL (Fin n ⊕ Fin n) K)
    {e e' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    (he : IsPrimIdemIn (ggJSt1_A b) e) (he' : IsPrimIdemIn (ggJSt1_A b) e')
    (hne : e ≠ e') : e * e' = 0 := by
  have hA : ∀ x ∈ ggJSt1_A b, ∀ y ∈ ggJSt1_A b, x * y = y * x :=
    fun x hx y hy => ggJSt1_commute b hx hy
  have hfA : e * e' ∈ ggJSt1_A b := (ggJSt1_A b).mul_mem he.1 he'.1
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

private lemma ggJSt1_isUnit_det_Ginv (K : Type) [Field K] (n : ℕ) :
    IsUnit ((ggJSt1_G K n)⁻¹).det :=
  (Matrix.isUnit_iff_isUnit_det ((ggJSt1_G K n)⁻¹)).mp (by
    rw [isUnit_iff_exists_inv]
    exact ⟨ggJSt1_G K n, Matrix.nonsing_inv_mul _ (ggJSt1_isUnit_det_G K n)⟩)

private lemma ggJSt1_rank_eq_finrank_range_toLin' {F : Type} [Field F] {m n : Type}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (M : Matrix m n F) :
    M.rank = Module.finrank F (LinearMap.range (Matrix.toLin' M)) := by
  rw [Matrix.rank_eq_finrank_range_toLin M (Pi.basisFun F m) (Pi.basisFun F n),
    Matrix.toLin_eq_toLin']

private lemma ggJSt1_finrank_range_formAdj {K : Type} [Field K] {n : ℕ}
    (e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) :
    Module.finrank K
        (LinearMap.range (Matrix.toLin' (formAdj (RingHom.id K) (ggJSt1_G K n) e))) =
      Module.finrank K (LinearMap.range (Matrix.toLin' e)) := by
  have hmid : e.map (RingHom.id K) = e := by
    ext i j
    rfl
  rw [← ggJSt1_rank_eq_finrank_range_toLin' (formAdj (RingHom.id K) (ggJSt1_G K n) e),
    ← ggJSt1_rank_eq_finrank_range_toLin' e]
  unfold formAdj
  rw [hmid, Matrix.rank_mul_eq_left_of_isUnit_det _ _ (ggJSt1_isUnit_det_G K n),
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ (ggJSt1_isUnit_det_Ginv K n),
    Matrix.rank_transpose]

private noncomputable def ggJSt1_formAdjLin (K : Type) [Field K] [CharP K 2] (n : ℕ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K →ₗ[K]
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K where
  toFun := formAdj (RingHom.id K) (ggJSt1_G K n)
  map_add' := fun a b => CFSG.StandardType.ClassicalPosition.Geo.formAdj_add _ _ _ _
  map_smul' := fun c a => by
    rw [CFSG.StandardType.ClassicalPosition.Geo.formAdj_smul]

private lemma ggJSt1_formAdj_invol (K : Type) [Field K] [CharP K 2] (n : ℕ)
    (a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) :
    formAdj (RingHom.id K) (ggJSt1_G K n) (formAdj (RingHom.id K) (ggJSt1_G K n) a) = a :=
  CFSG.StandardType.ClassicalPosition.Geo.formAdj_formAdj (RingHom.id K) (fun x => rfl)
    (ggJSt1_isUnit_det_G K n) (by
      have hmid : (ggJSt1_G K n).map (RingHom.id K) = ggJSt1_G K n := by
        ext i j
        rfl
      rw [hmid]
      exact ggJSt1_G_transpose K n) a

private noncomputable def ggJSt1_formAdjEquiv (K : Type) [Field K] [CharP K 2] (n : ℕ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K ≃ₗ[K]
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  LinearEquiv.ofBijective (ggJSt1_formAdjLin K n) (by
    constructor
    · intro a b hab
      have h := congrArg (formAdj (RingHom.id K) (ggJSt1_G K n)) hab
      rw [show ggJSt1_formAdjLin K n a = formAdj (RingHom.id K) (ggJSt1_G K n) a from rfl,
        show ggJSt1_formAdjLin K n b = formAdj (RingHom.id K) (ggJSt1_G K n) b from rfl]
        at h
      rwa [ggJSt1_formAdj_invol K n a, ggJSt1_formAdj_invol K n b] at h
    · intro a
      exact ⟨formAdj (RingHom.id K) (ggJSt1_G K n) a, ggJSt1_formAdj_invol K n a⟩)

private lemma ggJSt1_blockDegree_formAdj {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (b : GL (Fin n ⊕ Fin n) K) (hb : b ∈ StatedSp n K)
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K} (he : e ∈ ggJSt1_A b) :
    blockDegree (ggJSt1_A b) (formAdj (RingHom.id K) (ggJSt1_G K n) e) =
      blockDegree (ggJSt1_A b) e := by
  have hmemE : formAdj (RingHom.id K) (ggJSt1_G K n) e ∈ ggJSt1_A b :=
    ggJSt1_formAdj_mem b hb he
  have hS : (Subalgebra.toSubmodule (ggJSt1_A b)).map
        (LinearMap.mulRight K (formAdj (RingHom.id K) (ggJSt1_G K n) e)) =
      ((Subalgebra.toSubmodule (ggJSt1_A b)).map (LinearMap.mulRight K e)).map
        (ggJSt1_formAdjEquiv K n).toLinearMap := by
    ext x
    simp only [Submodule.mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨formAdj (RingHom.id K) (ggJSt1_G K n) a * e,
        ⟨formAdj (RingHom.id K) (ggJSt1_G K n) a, ggJSt1_formAdj_mem b hb ha, rfl⟩, ?_⟩
      show formAdj (RingHom.id K) (ggJSt1_G K n) (formAdj (RingHom.id K) (ggJSt1_G K n) a * e) =
        a * formAdj (RingHom.id K) (ggJSt1_G K n) e
      rw [CFSG.StandardType.ClassicalPosition.Geo.formAdj_mul (RingHom.id K)
        (ggJSt1_isUnit_det_G K n), ggJSt1_formAdj_invol K n a]
      exact ggJSt1_commute b hmemE ha
    · rintro ⟨y, ⟨a, ha, rfl⟩, rfl⟩
      refine ⟨formAdj (RingHom.id K) (ggJSt1_G K n) a, ggJSt1_formAdj_mem b hb ha, ?_⟩
      show formAdj (RingHom.id K) (ggJSt1_G K n) a *
          formAdj (RingHom.id K) (ggJSt1_G K n) e =
        formAdj (RingHom.id K) (ggJSt1_G K n) (a * e)
      rw [CFSG.StandardType.ClassicalPosition.Geo.formAdj_mul (RingHom.id K)
        (ggJSt1_isUnit_det_G K n)]
      exact ggJSt1_commute b (ggJSt1_formAdj_mem b hb ha) hmemE
  unfold blockDegree
  rw [hS]
  exact LinearEquiv.finrank_map_eq (ggJSt1_formAdjEquiv K n) _

private lemma ggJSt1_eigDimOn_add {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
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

private lemma ggJSt1_finrank_range_add {k V : Type} [Field k] [AddCommGroup V] [Module k V]
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

private lemma ggJSt1_finrank_range_add_matrix {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
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
  exact ggJSt1_finrank_range_add _ _ hp hq hpq hqp

private lemma ggJSt1_exists_prim {K : Type} [Field K] [Fintype K] [CharP K 2] {n : ℕ}
    (b : GL (Fin n ⊕ Fin n) K) (hb : b ∈ StatedSp n K)
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    (hε : IsPrimAdjIdemIn (RingHom.id K) (ggJSt1_G K n) (ggJSt1_A b) ε) :
    ∃ e, IsPrimIdemIn (ggJSt1_A b) e ∧ e * ε = e ∧
      (e = ε ∨ (e ≠ ε ∧ formAdj (RingHom.id K) (ggJSt1_G K n) e ≠ e ∧
        ε = e + formAdj (RingHom.id K) (ggJSt1_G K n) e)) := by
  refine exists_isPrimIdemIn_of_isPrimAdjIdemIn (RingHom.id K) (fun x => rfl)
    (ggJSt1_isUnit_det_G K n) ?_ (S := {b}) ?_ ?_ hε
  · have hmid : (ggJSt1_G K n).map (RingHom.id K) = ggJSt1_G K n := by
      ext i j
      rfl
    rw [hmid]
    exact ggJSt1_G_transpose K n
  · intro s hs s' hs'
    rw [Set.mem_singleton_iff] at hs hs'
    rw [hs, hs']
  · intro s hs
    rw [Set.mem_singleton_iff] at hs
    rw [hs]
    exact ggJSt1_gram b hb

private lemma ggJSt1_b_mul_formAdj_iff {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (b : GL (Fin n ⊕ Fin n) K) (hb : b ∈ StatedSp n K)
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K} (he : e ∈ ggJSt1_A b) :
    (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *
        formAdj (RingHom.id K) (ggJSt1_G K n) e =
        formAdj (RingHom.id K) (ggJSt1_G K n) e ↔
      (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * e = e := by
  have hG := ggJSt1_isUnit_det_G K n
  have hbA : (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) ∈ ggJSt1_A b :=
    Algebra.subset_adjoin (by simp)
  have hmemE : formAdj (RingHom.id K) (ggJSt1_G K n) e ∈ ggJSt1_A b :=
    ggJSt1_formAdj_mem b hb he
  have hfinv : formAdj (RingHom.id K) (ggJSt1_G K n)
      (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
      ((b⁻¹ : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) :=
    CFSG.StandardType.ClassicalPosition.Geo.formAdj_eq_inv_of_isometry (RingHom.id K) hG b
      (by simpa using ggJSt1_gram b hb)
  constructor
  · intro h
    have h1 := congrArg (formAdj (RingHom.id K) (ggJSt1_G K n)) h
    rw [CFSG.StandardType.ClassicalPosition.Geo.formAdj_mul (RingHom.id K) hG
        (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
        (formAdj (RingHom.id K) (ggJSt1_G K n) e),
      ggJSt1_formAdj_formAdj b hb he, hfinv] at h1
    have h3 : e * (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = e := by
      calc e * (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
          (e * ((b⁻¹ : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)) *
            (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) := by rw [h1]
        _ = e * (((b⁻¹ : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *
              (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)) := by rw [mul_assoc]
        _ = e * 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
        _ = e := mul_one e
    rw [ggJSt1_commute b hbA he]
    exact h3
  · intro h
    have h1 := congrArg (formAdj (RingHom.id K) (ggJSt1_G K n)) h
    rw [CFSG.StandardType.ClassicalPosition.Geo.formAdj_mul (RingHom.id K) hG
        (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) e, hfinv] at h1
    have h3 : formAdj (RingHom.id K) (ggJSt1_G K n) e *
        (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
        formAdj (RingHom.id K) (ggJSt1_G K n) e := by
      calc formAdj (RingHom.id K) (ggJSt1_G K n) e *
            (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
          (formAdj (RingHom.id K) (ggJSt1_G K n) e *
            ((b⁻¹ : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)) *
              (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) := by rw [h1]
        _ = formAdj (RingHom.id K) (ggJSt1_G K n) e *
              (((b⁻¹ : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *
                (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)) := by rw [mul_assoc]
        _ = formAdj (RingHom.id K) (ggJSt1_G K n) e * 1 := by
              rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
        _ = formAdj (RingHom.id K) (ggJSt1_G K n) e := mul_one _
    rw [ggJSt1_commute b hbA hmemE]
    exact h3

private lemma ggJSt1_eigDimOn_one_prim {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    {b : GL (Fin n ⊕ Fin n) K} (hodd : Odd (orderOf b))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K} (he : IsPrimIdemIn (ggJSt1_A b) e) :
    eigDimOn (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) e 1 =
      if (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * e = e then
        Module.finrank K (LinearMap.range (Matrix.toLin' e)) else 0 := by
  classical
  by_cases h : (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * e = e
  · rw [if_pos h]
    exact (eigDimOn_one_of_isPrimIdemIn (K := K) hodd he).1 h
  · rw [if_neg h]
    exact (eigDimOn_one_of_isPrimIdemIn (K := K) hodd he).2 h

private lemma ggJSt1_eigDimOn_primAdj_one {K : Type} [Field K] [Fintype K] [CharP K 2] {n : ℕ}
    (b : GL (Fin n ⊕ Fin n) K) (hb : b ∈ StatedSp n K) (hodd : Odd (orderOf b))
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    (hε : IsPrimAdjIdemIn (RingHom.id K) (ggJSt1_G K n) (ggJSt1_A b) ε) :
    eigDimOn (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) ε 1 =
      if (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε = ε then
        Module.finrank K (LinearMap.range (Matrix.toLin' ε)) else 0 := by
  classical
  obtain ⟨e, he, _heε, hcase⟩ := ggJSt1_exists_prim b hb hε
  have heAdjPrim := ggJSt1_formAdj_prim b hb he
  have hbA : (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) ∈ ggJSt1_A b :=
    Algebra.subset_adjoin (by simp)
  have hbe : (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * e =
      e * (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) := ggJSt1_commute b hbA he.1
  have hbeAdj : (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *
        formAdj (RingHom.id K) (ggJSt1_G K n) e =
      formAdj (RingHom.id K) (ggJSt1_G K n) e *
        (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) := ggJSt1_commute b hbA heAdjPrim.1
  rcases hcase with hcase | ⟨hne, hneadj, hεeq⟩
  · rw [← hcase]
    exact ggJSt1_eigDimOn_one_prim hodd he
  · have horth : e * formAdj (RingHom.id K) (ggJSt1_G K n) e = 0 :=
      ggJSt1_prim_orthogonal b he heAdjPrim (Ne.symm hneadj)
    have horth' : formAdj (RingHom.id K) (ggJSt1_G K n) e * e = 0 :=
      ggJSt1_prim_orthogonal b heAdjPrim he hneadj
    have hbε : ((b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *
          (e + formAdj (RingHom.id K) (ggJSt1_G K n) e) =
          e + formAdj (RingHom.id K) (ggJSt1_G K n) e) ↔
        (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * e = e := by
      constructor
      · intro h
        have h1 : e * ((b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *
            (e + formAdj (RingHom.id K) (ggJSt1_G K n) e)) =
            e * (e + formAdj (RingHom.id K) (ggJSt1_G K n) e) := by rw [h]
        have h1a : e * ((b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * e) =
            (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * e := by
          rw [← mul_assoc, ← hbe, mul_assoc, he.2.1.eq]
        have h1b : e * ((b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *
            formAdj (RingHom.id K) (ggJSt1_G K n) e) = 0 := by
          rw [← mul_assoc, ← hbe, mul_assoc, horth, mul_zero]
        have hR : e * (e + formAdj (RingHom.id K) (ggJSt1_G K n) e) = e := by
          rw [mul_add, he.2.1.eq, horth, add_zero]
        have hL : e * ((b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *
            (e + formAdj (RingHom.id K) (ggJSt1_G K n) e)) =
            (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * e := by
          rw [mul_add, mul_add, h1a, h1b, add_zero]
        rw [hL, hR] at h1
        exact h1
      · intro h
        rw [mul_add, h, (ggJSt1_b_mul_formAdj_iff b hb he.1).2 h]
    have hadd : eigDimOn (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
          (e + formAdj (RingHom.id K) (ggJSt1_G K n) e) 1 =
        eigDimOn (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) e 1 +
          eigDimOn (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
            (formAdj (RingHom.id K) (ggJSt1_G K n) e) 1 :=
      ggJSt1_eigDimOn_add he.2.1 heAdjPrim.2.1 hbe hbeAdj horth horth' 1
    rw [hεeq, hadd, ggJSt1_eigDimOn_one_prim hodd he,
      ggJSt1_eigDimOn_one_prim hodd heAdjPrim]
    by_cases h : (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * e = e
    · have hAdj : (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *
          formAdj (RingHom.id K) (ggJSt1_G K n) e =
          formAdj (RingHom.id K) (ggJSt1_G K n) e :=
        (ggJSt1_b_mul_formAdj_iff b hb he.1).2 h
      rw [if_pos h, if_pos hAdj, if_pos (hbε.2 h)]
      exact (ggJSt1_finrank_range_add_matrix he.2.1 heAdjPrim.2.1 horth horth').symm
    · have hAdj : ¬ ((b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *
          formAdj (RingHom.id K) (ggJSt1_G K n) e =
          formAdj (RingHom.id K) (ggJSt1_G K n) e) :=
        fun hc => h ((ggJSt1_b_mul_formAdj_iff b hb he.1).1 hc)
      rw [if_neg h, if_neg hAdj, if_neg (fun hc => h (hbε.1 hc))]

private noncomputable def ggJSt1_R {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (b : Matrix ι ι K) : Finset (AlgebraicClosure K) :=
  haveI := Classical.decEq (AlgebraicClosure K)
  ((b.charpoly.map (algebraMap K (AlgebraicClosure K))).roots.toFinset).erase 1

private lemma ggJSt1_blockExp_eq {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (b : Matrix ι ι K) :
    blockExp false b = (eigDim b 1 / 2) ^ 2 +
      (∑ l ∈ ggJSt1_R b, eigDim b l * (eigDim b l - 1) / 2) / 2 := by
  classical
  simp only [blockExp, ggJSt1_R]
  simp

private lemma ggJSt1_map_pow {ι K L : Type} [Fintype ι] [DecidableEq ι] [Semiring K]
    [Semiring L] (φ : K →+* L) (M : Matrix ι ι K) (n : ℕ) :
    (M ^ n).map φ = (M.map φ) ^ n := by
  have h := map_pow (RingHom.mapMatrix φ) M n
  simpa only [RingHom.mapMatrix_apply] using h

private lemma ggJSt1_isSemisimple {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (M : Matrix ι ι K) (n : ℕ) (hn : (n : AlgebraicClosure K) ≠ 0) (hM : M ^ n = 1) :
    Module.End.IsSemisimple (Matrix.toLin' (M.map (algebraMap K (AlgebraicClosure K)))) := by
  have hfpow : (Matrix.toLin' (M.map (algebraMap K (AlgebraicClosure K)))) ^ n = 1 := by
    have h1 : (M ^ n).map (algebraMap K (AlgebraicClosure K)) = 1 := by
      rw [hM]
      exact map_one (RingHom.mapMatrix (algebraMap K (AlgebraicClosure K)))
    rw [← Matrix.toLin'_pow, ← ggJSt1_map_pow, h1]
    exact map_one (Matrix.toLinAlgEquiv' (R := AlgebraicClosure K) (n := ι))
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    (p := (Polynomial.X : Polynomial (AlgebraicClosure K)) ^ n - 1) ?_ ?_
  · exact (Polynomial.X_pow_sub_one_separable_iff.mpr hn).squarefree
  · simpa [Polynomial.aeval_X, hfpow]

private lemma ggJSt1_eigDim_eq_rootMultiplicity {ι K : Type} [Fintype ι] [DecidableEq ι]
    [Field K] (M : Matrix ι ι K) (n : ℕ) (hn : (n : AlgebraicClosure K) ≠ 0)
    (hM : M ^ n = 1) (l : AlgebraicClosure K) :
    eigDim M l = ((M.charpoly).map (algebraMap K (AlgebraicClosure K))).rootMultiplicity l := by
  have hf : Module.End.IsSemisimple
      (Matrix.toLin' (M.map (algebraMap K (AlgebraicClosure K)))) :=
    ggJSt1_isSemisimple M n hn hM
  have hchar : (Matrix.toLin' (M.map (algebraMap K (AlgebraicClosure K)))).charpoly =
      (M.charpoly).map (algebraMap K (AlgebraicClosure K)) := by
    rw [Matrix.charpoly_toLin', Matrix.charpoly_map]
  unfold eigDim
  rw [← hchar, ← LinearMap.finrank_maxGenEigenspace_eq,
    Module.End.IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace
      (Module.End.IsSemisimple.isFinitelySemisimple hf) l]

private lemma ggJSt1_eigDim_ne_zero_iff_mem_roots {ι K : Type} [Fintype ι] [DecidableEq ι]
    [Field K] (b : Matrix ι ι K) {n : ℕ} (hn : (n : AlgebraicClosure K) ≠ 0)
    (hM : b ^ n = 1) {l : AlgebraicClosure K} :
    eigDim b l ≠ 0 ↔ l ∈ (b.charpoly.map (algebraMap K (AlgebraicClosure K))).roots := by
  classical
  have hp : ((b.charpoly).map (algebraMap K (AlgebraicClosure K))) ≠ 0 :=
    ((Matrix.charpoly_monic b).map (algebraMap K (AlgebraicClosure K))).ne_zero
  rw [ggJSt1_eigDim_eq_rootMultiplicity b n hn hM l, Polynomial.mem_roots hp]
  exact ⟨fun h => (Polynomial.rootMultiplicity_pos hp).mp (Nat.pos_of_ne_zero h),
    fun h => (Polynomial.rootMultiplicity_pos hp).mpr h |>.ne'⟩

private lemma ggJSt1_eigDimOn_le_eigDim {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (b e : Matrix ι ι K) (l : AlgebraicClosure K) : eigDimOn b e l ≤ eigDim b l := by
  unfold eigDimOn eigDim
  exact Submodule.finrank_mono inf_le_left

private lemma ggJSt1_matrix_pow_orderOf {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (b : GL ι K) : (b : Matrix ι ι K) ^ orderOf b = 1 := by
  rw [← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one]

private lemma ggJSt1_cast_orderOf_ne_zero {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [CharP K 2] {b : GL ι K} (hodd : Odd (orderOf b)) :
    (orderOf b : AlgebraicClosure K) ≠ 0 := by
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  intro h0
  have h2 : (2 : ℕ) ∣ orderOf b :=
    (CharP.cast_eq_zero_iff (AlgebraicClosure K) 2 (orderOf b)).mp h0
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

private lemma ggJSt1_finrank_range_toLin'_ne_zero {K : Type} [Field K] {m : Type}
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

private lemma ggJSt1_unique_one_block {K : Type} [Field K] [Fintype K] [CharP K 2] {n : ℕ}
    (b : GL (Fin n ⊕ Fin n) K) (hb : b ∈ StatedSp n K) (hodd : Odd (orderOf b))
    {P : Finset (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)}
    (hP : ∀ ε ∈ P, IsPrimAdjIdemIn (RingHom.id K) (ggJSt1_G K n) (ggJSt1_A b) ε)
    (hPorth : ∀ ε ∈ P, ∀ ε' ∈ P, ε ≠ ε' → ε * ε' = 0)
    {ε ε' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K} (hε : ε ∈ P) (hε' : ε' ∈ P)
    (h1 : (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε = ε)
    (h1' : (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε' = ε') : ε = ε' := by
  classical
  by_contra hne
  obtain ⟨e, he, heε, _⟩ := ggJSt1_exists_prim b hb (hP ε hε)
  obtain ⟨e', he', he'ε', _⟩ := ggJSt1_exists_prim b hb (hP ε' hε')
  have hbA : (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) ∈ ggJSt1_A b :=
    Algebra.subset_adjoin (by simp)
  have he1 : (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * e = e := by
    calc (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * e =
        (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * (e * ε) := by rw [heε]
      _ = ((b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * e) * ε := by rw [mul_assoc]
      _ = (e * (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)) * ε := by
            rw [ggJSt1_commute b hbA he.1]
      _ = e * ((b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε) := by rw [mul_assoc]
      _ = e * ε := by rw [h1]
      _ = e := heε
  have he1' : (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * e' = e' := by
    calc (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * e' =
        (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * (e' * ε') := by rw [he'ε']
      _ = ((b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * e') * ε' := by rw [mul_assoc]
      _ = (e' * (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)) * ε' := by
            rw [ggJSt1_commute b hbA he'.1]
      _ = e' * ((b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε') := by rw [mul_assoc]
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
  have horth : e * e' = 0 := ggJSt1_prim_orthogonal b he he' hee'
  have hpos : eigDimOn (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) e 1 ≠ 0 := by
    rw [(eigDimOn_one_of_isPrimIdemIn (K := K) hodd he).1 he1]
    exact ggJSt1_finrank_range_toLin'_ne_zero he.2.2.1
  have hpos' : eigDimOn (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) e' 1 ≠ 0 := by
    rw [(eigDimOn_one_of_isPrimIdemIn (K := K) hodd he').1 he1']
    exact ggJSt1_finrank_range_toLin'_ne_zero he'.2.2.1
  rcases eigDimOn_eq_zero_or_of_mul_eq_zero he he' horth 1 with h0 | h0
  · exact hpos h0
  · exact hpos' h0

private lemma ggJSt1_eigDim_one {K : Type} [Field K] [Fintype K] [CharP K 2] {n : ℕ}
    (b : GL (Fin n ⊕ Fin n) K) (hb : b ∈ StatedSp n K) (hodd : Odd (orderOf b))
    {P : Finset (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)}
    (hP : ∀ ε ∈ P, IsPrimAdjIdemIn (RingHom.id K) (ggJSt1_G K n) (ggJSt1_A b) ε)
    (hPorth : ∀ ε ∈ P, ∀ ε' ∈ P, ε ≠ ε' → ε * ε' = 0)
    (hPsum : ∑ ε ∈ P, ε = 1) :
    eigDim (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) 1 =
      ∑ ε ∈ P, if (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε = ε then
        Module.finrank K (LinearMap.range (Matrix.toLin' ε)) else 0 := by
  have hbA : (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) ∈ ggJSt1_A b :=
    Algebra.subset_adjoin (by simp)
  have hPcomm : ∀ ε ∈ P, IsIdempotentElem ε ∧
      Commute (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) ε := by
    intro ε hε
    exact ⟨(hP ε hε).2.1, ggJSt1_commute b hbA (hP ε hε).1⟩
  rw [eigDim_eq_sum_eigDimOn (b := (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K))
    hPcomm hPorth hPsum 1]
  exact Finset.sum_congr rfl fun ε hε => ggJSt1_eigDimOn_primAdj_one b hb hodd (hP ε hε)

private lemma ggJSt1_blockDegree_pos {K : Type} [Field K] {n : ℕ}
    {b : GL (Fin n ⊕ Fin n) K} {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    (he : e ∈ ggJSt1_A b) (he0 : e ≠ 0) :
    0 < blockDegree (ggJSt1_A b) e := by
  have hmem : e ∈ (Subalgebra.toSubmodule (ggJSt1_A b)).map (LinearMap.mulRight K e) :=
    ⟨1, (ggJSt1_A b).one_mem, by rw [LinearMap.mulRight_apply, one_mul]⟩
  have hne : (Subalgebra.toSubmodule (ggJSt1_A b)).map (LinearMap.mulRight K e) ≠ ⊥ := by
    intro h
    rw [h] at hmem
    exact he0 (by simpa using hmem)
  unfold blockDegree
  refine Module.finrank_pos_iff.mpr ⟨⟨e, hmem⟩, ⟨0, Submodule.zero_mem _⟩, ?_⟩
  intro h
  exact he0 (Subtype.ext_iff.mp h)

private lemma ggJSt1_block_data {K : Type} [Field K] [Fintype K] [CharP K 2] {n : ℕ}
    (b : GL (Fin n ⊕ Fin n) K) (hb : b ∈ StatedSp n K) (hodd : Odd (orderOf b))
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    (hε : IsPrimAdjIdemIn (RingHom.id K) (ggJSt1_G K n) (ggJSt1_A b) ε)
    (h1 : (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε ≠ ε) :
    ∃ (e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (R : Finset (AlgebraicClosure K))
      (m : ℕ),
      IsPrimIdemIn (ggJSt1_A b) e ∧ e * ε = e ∧
      (e = ε ∨ (e ≠ ε ∧ formAdj (RingHom.id K) (ggJSt1_G K n) e ≠ e ∧
        ε = e + formAdj (RingHom.id K) (ggJSt1_G K n) e)) ∧
      (∀ l, eigDimOn (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) ε l =
        if l ∈ R then m else 0) ∧
      R.card * m = Module.finrank K (LinearMap.range (Matrix.toLin' ε)) ∧
      1 ∉ R ∧ 0 < m ∧
      (e = ε → R.card = blockDegree (ggJSt1_A b) e) ∧
      (e ≠ ε → R.card = 2 * blockDegree (ggJSt1_A b) e) := by
  classical
  obtain ⟨e, he, heε, hcase⟩ := ggJSt1_exists_prim b hb hε
  obtain ⟨R, m, hRcard, hRm, hRon, hRoff⟩ :=
    exists_blockRoots_of_isPrimIdemIn (K := K) hodd he
  have heAdj : IsPrimIdemIn (ggJSt1_A b) (formAdj (RingHom.id K) (ggJSt1_G K n) e) :=
    ggJSt1_formAdj_prim b hb he
  obtain ⟨R', m', hR'card, hR'm', hR'on, hR'off⟩ :=
    exists_blockRoots_of_isPrimIdemIn (K := K) hodd heAdj
  have hbDegPos : 0 < blockDegree (ggJSt1_A b) e :=
    ggJSt1_blockDegree_pos he.1 he.2.2.1
  have hrankEq : Module.finrank K (LinearMap.range (Matrix.toLin' e)) =
      Module.finrank K (LinearMap.range
        (Matrix.toLin' (formAdj (RingHom.id K) (ggJSt1_G K n) e))) :=
    (ggJSt1_finrank_range_formAdj e).symm
  have hdegEq : blockDegree (ggJSt1_A b) (formAdj (RingHom.id K) (ggJSt1_G K n) e) =
      blockDegree (ggJSt1_A b) e := ggJSt1_blockDegree_formAdj b hb he.1
  have hmEq : m = m' := by
    have h1 : blockDegree (ggJSt1_A b) e * m =
        Module.finrank K (LinearMap.range (Matrix.toLin' e)) := by
      rw [← hRcard]; exact hRm
    have h2 : blockDegree (ggJSt1_A b) e * m' =
        Module.finrank K (LinearMap.range (Matrix.toLin' e)) := by
      have hRcard' : R.card = R'.card := by rw [hRcard, ← hdegEq, ← hR'card]
      rw [← hRcard, hRcard', hR'm', ← hrankEq]
    exact Nat.mul_left_cancel hbDegPos (h1.trans h2.symm)
  have hmPos : 0 < m := by
    by_contra h
    have hm0 : m = 0 := Nat.eq_zero_of_not_pos h
    have h2 : Module.finrank K (LinearMap.range (Matrix.toLin' e)) = 0 := by
      rw [← hRm, hm0, mul_zero]
    exact ggJSt1_finrank_range_toLin'_ne_zero he.2.2.1 h2
  have hcombine : ∀ (e₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
      (S : Finset (AlgebraicClosure K)) (t : ℕ),
      (∀ l ∈ S, eigDimOn (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) e₀ l = t) →
      (∀ l ∉ S, eigDimOn (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) e₀ l = 0) →
      ∀ l, eigDimOn (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) e₀ l =
        if l ∈ S then t else 0 := by
    intro e₀ S t hon hoff l
    by_cases hl : l ∈ S
    · rw [if_pos hl]; exact hon l hl
    · rw [if_neg hl]; exact hoff l hl
  have hRcomb := hcombine e R m hRon hRoff
  have hR'comb := hcombine (formAdj (RingHom.id K) (ggJSt1_G K n) e) R' m' hR'on hR'off
  rcases hcase with hcase | ⟨hne, hneadj, hεeq⟩
  · refine ⟨e, R, m, he, heε, Or.inl hcase, ?_, ?_, ?_, hmPos, ?_, ?_⟩
    · intro l
      rw [← hcase]
      exact hRcomb l
    · rw [← hcase, hRm]
    · intro hmem
      have hb1 : (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * e = e := by
        by_contra hbne
        have h0 := (eigDimOn_one_of_isPrimIdemIn (K := K) hodd he).2 hbne
        rw [hRon 1 hmem] at h0
        exact hmPos.ne' h0
      exact h1 (by rw [← hcase]; exact hb1)
    · intro _; rw [hRcard]
    · intro hne'; exact absurd hcase hne'
  · have horth : e * formAdj (RingHom.id K) (ggJSt1_G K n) e = 0 :=
      ggJSt1_prim_orthogonal b he heAdj (Ne.symm hneadj)
    have horth' : formAdj (RingHom.id K) (ggJSt1_G K n) e * e = 0 :=
      ggJSt1_prim_orthogonal b heAdj he hneadj
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
      rw [hεeq, ggJSt1_eigDimOn_add he.2.1 heAdj.2.1
        (ggJSt1_commute b (Algebra.subset_adjoin (by simp)) he.1)
        (ggJSt1_commute b (Algebra.subset_adjoin (by simp)) heAdj.1) horth horth' l]
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
          (Matrix.toLin' (formAdj (RingHom.id K) (ggJSt1_G K n) e))) := by
        rw [hmEq, hR'm']
      rw [Finset.card_union_of_disjoint hdisj, add_mul, hRm, hR'm,
        ← ggJSt1_finrank_range_add_matrix he.2.1 heAdj.2.1 horth horth', hεeq]
    · intro hmem
      rw [Finset.mem_union] at hmem
      have hb1 : (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * e = e := by
        by_contra hbne
        rcases hmem with hmem | hmem
        · have h0 := (eigDimOn_one_of_isPrimIdemIn (K := K) hodd he).2 hbne
          rw [hRon 1 hmem] at h0; exact hmPos.ne' h0
        · have hbne' : (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *
              formAdj (RingHom.id K) (ggJSt1_G K n) e ≠
              formAdj (RingHom.id K) (ggJSt1_G K n) e :=
            fun hc => hbne ((ggJSt1_b_mul_formAdj_iff b hb he.1).1 hc)
          have h0 := (eigDimOn_one_of_isPrimIdemIn (K := K) hodd heAdj).2 hbne'
          rw [hR'on 1 hmem] at h0
          exact hmPos.ne' (hmEq.trans h0)
      have hb2 : (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *
          formAdj (RingHom.id K) (ggJSt1_G K n) e =
          formAdj (RingHom.id K) (ggJSt1_G K n) e :=
        (ggJSt1_b_mul_formAdj_iff b hb he.1).2 hb1
      exact h1 (by rw [hεeq, mul_add, hb1, hb2])
    · intro h; exact absurd h hne
    · intro _
      rw [Finset.card_union_of_disjoint hdisj, hRcard, hR'card, hdegEq]
      ring

private lemma ggJSt1_rank_fromBlocks_one_zero {F : Type} [Field F] {r s : ℕ} :
    (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) F) 0 0
      (0 : Matrix (Fin s) (Fin s) F)).rank = r := by
  classical
  have h : (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) F) 0 0
      (0 : Matrix (Fin s) (Fin s) F)) =
      diagonal (Sum.elim (fun _ : Fin r => (1 : F)) (fun _ : Fin s => (0 : F))) := by
    rw [← Matrix.fromBlocks_diagonal, Matrix.diagonal_one, Matrix.diagonal_zero]
  rw [h, Matrix.rank_diagonal, Fintype.card_subtype, Finset.card_filter, Fintype.sum_sum_type]
  simp

private lemma ggJSt1_rank_map_eq {F E : Type} [Field F] [Field E] {m : Type} [Fintype m]
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
  exact ggJSt1_rank_fromBlocks_one_zero

private lemma ggJSt1_finrank_range_map {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (e : Matrix ι ι K) :
    Module.finrank (AlgebraicClosure K)
        (LinearMap.range (Matrix.toLin' (e.map (algebraMap K (AlgebraicClosure K))))) =
      Module.finrank K (LinearMap.range (Matrix.toLin' e)) := by
  rw [← ggJSt1_rank_eq_finrank_range_toLin' (e.map (algebraMap K (AlgebraicClosure K))),
    ← ggJSt1_rank_eq_finrank_range_toLin' e]
  exact ggJSt1_rank_map_eq (algebraMap K (AlgebraicClosure K)) e

private lemma ggJSt1_eigDimOn_eq_zero_of_b_mul_eq {ι K : Type} [Fintype ι] [DecidableEq ι]
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
    rw [hd, ggJSt1_finrank_range_map e]
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

private lemma ggJSt1_one_block_prim {K : Type} [Field K] [Fintype K] [CharP K 2] {n : ℕ}
    (b : GL (Fin n ⊕ Fin n) K) (hb : b ∈ StatedSp n K) (hodd : Odd (orderOf b))
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    (hε : IsPrimAdjIdemIn (RingHom.id K) (ggJSt1_G K n) (ggJSt1_A b) ε)
    (h1 : (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε = ε) :
    IsPrimIdemIn (ggJSt1_A b) ε := by
  obtain ⟨e, he, heε, hcase⟩ := ggJSt1_exists_prim b hb hε
  have hbA : (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) ∈ ggJSt1_A b :=
    Algebra.subset_adjoin (by simp)
  have hbe : (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * e = e := by
    calc (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * e =
        (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * (e * ε) := by rw [heε]
      _ = ((b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * e) * ε := by rw [mul_assoc]
      _ = (e * (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)) * ε := by
            rw [ggJSt1_commute b hbA he.1]
      _ = e * ((b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε) := by rw [mul_assoc]
      _ = e * ε := by rw [h1]
      _ = e := heε
  rcases hcase with hcase | ⟨hne, hneadj, _⟩
  · rw [hcase] at he
    exact he
  · exfalso
    have heAdj := ggJSt1_formAdj_prim b hb he
    have hbeAdj : (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *
        formAdj (RingHom.id K) (ggJSt1_G K n) e = formAdj (RingHom.id K) (ggJSt1_G K n) e :=
      (ggJSt1_b_mul_formAdj_iff b hb he.1).2 hbe
    have hpos : eigDimOn (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) e 1 ≠ 0 := by
      rw [(eigDimOn_one_of_isPrimIdemIn (K := K) hodd he).1 hbe]
      exact ggJSt1_finrank_range_toLin'_ne_zero he.2.2.1
    have hpos' : eigDimOn (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
        (formAdj (RingHom.id K) (ggJSt1_G K n) e) 1 ≠ 0 := by
      rw [(eigDimOn_one_of_isPrimIdemIn (K := K) hodd heAdj).1 hbeAdj]
      exact ggJSt1_finrank_range_toLin'_ne_zero heAdj.2.2.1
    have horth : e * formAdj (RingHom.id K) (ggJSt1_G K n) e = 0 :=
      ggJSt1_prim_orthogonal b he heAdj (Ne.symm hneadj)
    rcases eigDimOn_eq_zero_or_of_mul_eq_zero he heAdj horth 1 with h0 | h0
    · exact hpos h0
    · exact hpos' h0

theorem two_part_centralizer_Sp {K : Type} [Field K] [Fintype K] [CharP K 2] {n f : ℕ}
    (hf : Fintype.card K = 2 ^ f) (b : GL (Fin n ⊕ Fin n) K) (hb : b ∈ StatedSp n K)
    (hodd : Odd (orderOf b)) :
    (Nat.card ↥((Subgroup.centralizer {b}).comap (StatedSp n K).subtype)).factorization 2 =
      f * blockExp false (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) := by
  classical
  obtain ⟨P, hPprim, hPorth, hPsum, hPcommBlock, hPsup, hPcard⟩ :=
    centralizer_block_decomp_Sp b hb hodd
  have hbA : (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) ∈ ggJSt1_A b :=
    Algebra.subset_adjoin (by simp)
  let ROf (ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) : Finset (AlgebraicClosure K) :=
    if hε : ε ∈ P then
      if h1 : (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε = ε then {1}
      else Classical.choose
        (Classical.choose_spec (ggJSt1_block_data b hb hodd (hPprim ε hε) h1))
    else ∅
  let mOf (ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) : ℕ :=
    if hε : ε ∈ P then
      if h1 : (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε = ε then
        Module.finrank K (LinearMap.range (Matrix.toLin' ε))
      else Classical.choose
        (Classical.choose_spec
          (Classical.choose_spec (ggJSt1_block_data b hb hodd (hPprim ε hε) h1)))
    else 0
  have hOf : ∀ ε (hε : ε ∈ P), ∀ l, eigDimOn (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) ε l =
      if l ∈ ROf ε then mOf ε else 0 := by
    intro ε hε l
    simp only [ROf, mOf, dif_pos hε]
    by_cases h1 : (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε = ε
    · simp only [dif_pos h1]
      by_cases hl : l = 1
      · subst hl
        rw [if_pos (Finset.mem_singleton_self 1)]
        exact (ggJSt1_eigDimOn_primAdj_one b hb hodd (hPprim ε hε)).trans (if_pos h1)
      · rw [if_neg (fun h => hl (Finset.mem_singleton.mp h))]
        exact ggJSt1_eigDimOn_eq_zero_of_b_mul_eq hodd
          (ggJSt1_one_block_prim b hb hodd (hPprim ε hε) h1) h1 hl
    · simp only [dif_neg h1]
      exact (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
        (ggJSt1_block_data b hb hodd (hPprim ε hε) h1)))).2.2.2.1 l
  have hOf_one : ∀ ε (hε : ε ∈ P),
      (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε ≠ ε → 1 ∉ ROf ε := by
    intro ε hε h1
    simp only [ROf, dif_pos hε, dif_neg h1]
    exact (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
      (ggJSt1_block_data b hb hodd (hPprim ε hε) h1)))).2.2.2.2.2.1
  have hOf_pos : ∀ ε (hε : ε ∈ P),
      (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε ≠ ε → 0 < mOf ε := by
    intro ε hε h1
    simp only [mOf, dif_pos hε, dif_neg h1]
    exact (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
      (ggJSt1_block_data b hb hodd (hPprim ε hε) h1)))).2.2.2.2.2.2.1
  have hOf_mul : ∀ ε (hε : ε ∈ P),
      (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε ≠ ε →
      (ROf ε).card * mOf ε = Module.finrank K (LinearMap.range (Matrix.toLin' ε)) := by
    intro ε hε h1
    simp only [ROf, mOf, dif_pos hε, dif_neg h1]
    exact (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
      (ggJSt1_block_data b hb hodd (hPprim ε hε) h1)))).2.2.2.2.1
  have hpart : ggJSt1_R (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
      (P.filter (fun ε => (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε ≠ ε)).biUnion
        ROf := by
    apply Finset.ext
    intro l
    simp only [Finset.mem_biUnion, Finset.mem_filter]
    constructor
    · intro hl
      rw [ggJSt1_R, Finset.mem_erase, Multiset.mem_toFinset] at hl
      obtain ⟨hl1, hlroot⟩ := hl
      have hd : eigDim (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) l ≠ 0 :=
        (ggJSt1_eigDim_ne_zero_iff_mem_roots (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
          (ggJSt1_cast_orderOf_ne_zero hodd) (ggJSt1_matrix_pow_orderOf b)).mpr hlroot
      have hPcomm : ∀ ε ∈ P, IsIdempotentElem ε ∧
          Commute (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) ε := by
        intro ε hε
        exact ⟨(hPprim ε hε).2.1, ggJSt1_commute b hbA (hPprim ε hε).1⟩
      have hsum := eigDim_eq_sum_eigDimOn (b := (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K))
        hPcomm hPorth hPsum l
      have hex : ∃ ε ∈ P, eigDimOn (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) ε l ≠ 0 := by
        by_contra h
        push_neg at h
        rw [hsum] at hd
        exact hd (Finset.sum_eq_zero fun ε hε => h ε hε)
      obtain ⟨ε, hεP, hεne⟩ := hex
      have hbne : (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε ≠ ε := by
        intro h1
        have hlR : l ∈ ROf ε := by
          by_contra hlR
          exact hεne (by rw [hOf ε hεP l, if_neg hlR])
        simp only [ROf, dif_pos hεP, dif_pos h1] at hlR
        exact hl1 (Finset.mem_singleton.mp hlR)
      refine ⟨ε, ⟨hεP, hbne⟩, ?_⟩
      by_contra hlR
      exact hεne (by rw [hOf ε hεP l, if_neg hlR])
    · rintro ⟨ε, ⟨hεP, hbne⟩, hlR⟩
      have hne0 : eigDimOn (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) ε l ≠ 0 := by
        rw [hOf ε hεP l, if_pos hlR]
        exact (hOf_pos ε hεP hbne).ne'
      have hd : eigDim (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) l ≠ 0 := by
        intro h0
        exact hne0 (le_antisymm
          (h0 ▸ ggJSt1_eigDimOn_le_eigDim (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) ε l)
          (Nat.zero_le _))
      rw [ggJSt1_R, Finset.mem_erase, Multiset.mem_toFinset]
      refine ⟨?_, (ggJSt1_eigDim_ne_zero_iff_mem_roots
        (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
        (ggJSt1_cast_orderOf_ne_zero hodd) (ggJSt1_matrix_pow_orderOf b)).mp hd⟩
      intro hl1
      exact hOf_one ε hεP hbne (hl1 ▸ hlR)
  have hOf_even : ∀ ε (hε : ε ∈ P),
      (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε ≠ ε →
      (ROf ε).card = 2 * ((ROf ε).card / 2) := by
    intro ε hε h1
    have hspec := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
      (ggJSt1_block_data b hb hodd (hPprim ε hε) h1)))
    have hROf : ROf ε = Classical.choose (Classical.choose_spec
        (ggJSt1_block_data b hb hodd (hPprim ε hε) h1)) := by
      simp only [ROf, dif_pos hε, dif_neg h1]
    rw [hROf]
    rcases hspec.2.2.1 with hcase | ⟨hne, hneadj, hεeq⟩
    · obtain ⟨d, m', E, instF, instFin, h1d, hcardE, hdm, hdeg, ⟨eG⟩⟩ :=
        blockGroup_iso_Sp_unitary b hb hodd (hPprim ε hε) (hcase ▸ hspec.1) h1
      have hc : (Classical.choose (Classical.choose_spec
          (ggJSt1_block_data b hb hodd (hPprim ε hε) h1))).card =
          blockDegree (ggJSt1_A b) ε := by
        rw [hspec.2.2.2.2.2.2.2.1 hcase, hcase]
      rw [hc, hdeg]
      omega
    · obtain ⟨d, m', E, instF, instFin, h1d, hcardE, hdm, hdeg, ⟨eG⟩⟩ :=
        blockGroup_iso_Sp_linear b hb hodd (hPprim ε hε) hspec.1
          (ggJSt1_formAdj_prim b hb hspec.1) (Ne.symm hneadj) hεeq
      rw [hspec.2.2.2.2.2.2.2.2 hne]
      omega
  have hpiece : ∀ ε (hε : ε ∈ P) (h1 : (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε ≠ ε)
      (a : AlgebraicClosure K), a ∈ ROf ε →
      ∃ p, IsPrimIdemIn (ggJSt1_A b) p ∧ p * ε = p ∧
        eigDimOn (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) p a ≠ 0 := by
    intro ε hε h1 a ha
    have hspec := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
      (ggJSt1_block_data b hb hodd (hPprim ε hε) h1)))
    have hROf : ROf ε = Classical.choose (Classical.choose_spec
        (ggJSt1_block_data b hb hodd (hPprim ε hε) h1)) := by
      simp only [ROf, dif_pos hε, dif_neg h1]
    have hne : eigDimOn (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) ε a ≠ 0 := by
      rw [hspec.2.2.2.1 a, if_pos (by rwa [← hROf])]
      exact hspec.2.2.2.2.2.2.1.ne'
    rcases hspec.2.2.1 with hcase | ⟨hne', hneadj, hεeq⟩
    · refine ⟨Classical.choose (ggJSt1_block_data b hb hodd (hPprim ε hε) h1),
        hspec.1, hspec.2.1, ?_⟩
      rwa [← hcase] at hne
    · have heAdj := ggJSt1_formAdj_prim b hb hspec.1
      have hadd := ggJSt1_eigDimOn_add hspec.1.2.1 heAdj.2.1
        (ggJSt1_commute b hbA hspec.1.1) (ggJSt1_commute b hbA heAdj.1)
        (ggJSt1_prim_orthogonal b hspec.1 heAdj (Ne.symm hneadj))
        (ggJSt1_prim_orthogonal b heAdj hspec.1 hneadj) a
      rw [hεeq, hadd] at hne
      by_cases h0 : eigDimOn (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
          (Classical.choose (ggJSt1_block_data b hb hodd (hPprim ε hε) h1)) a ≠ 0
      · exact ⟨_, hspec.1, hspec.2.1, h0⟩
      · push_neg at h0
        refine ⟨formAdj (RingHom.id K) (ggJSt1_G K n)
          (Classical.choose (ggJSt1_block_data b hb hodd (hPprim ε hε) h1)), heAdj, ?_, ?_⟩
        · have hεadj : formAdj (RingHom.id K) (ggJSt1_G K n) ε = ε := (hPprim ε hε).2.2.2.1
          have hmem : Classical.choose (ggJSt1_block_data b hb hodd (hPprim ε hε) h1) ∈
              ggJSt1_A b := hspec.1.1
          have heq : formAdj (RingHom.id K) (ggJSt1_G K n)
                (Classical.choose (ggJSt1_block_data b hb hodd (hPprim ε hε) h1) * ε) =
              formAdj (RingHom.id K) (ggJSt1_G K n)
                (Classical.choose (ggJSt1_block_data b hb hodd (hPprim ε hε) h1)) := by
            rw [hspec.2.1]
          rw [CFSG.StandardType.ClassicalPosition.Geo.formAdj_mul (RingHom.id K)
            (ggJSt1_isUnit_det_G K n), hεadj] at heq
          rw [ggJSt1_commute b (ggJSt1_formAdj_mem b hb hspec.1.1) (hPprim ε hε).1]
          exact heq
        · intro hc
          exact hne (by rw [h0, hc, add_zero])
  have hdisjR : ∀ ε (hε : ε ∈ P) (h1 : (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε ≠ ε)
      ε' (hε' : ε' ∈ P) (h1' : (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε' ≠ ε'),
      ε ≠ ε' → Disjoint (ROf ε) (ROf ε') := by
    intro ε hε h1 ε' hε' h1' hne
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb hab
    subst hab
    obtain ⟨p, hp, hpε, hpa⟩ := hpiece ε hε h1 a ha
    obtain ⟨p', hp', hp'ε', hp'a⟩ := hpiece ε' hε' h1' a hb
    have hpp' : p * p' = 0 := by
      refine ggJSt1_prim_orthogonal b hp hp' ?_
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
  have heig1 : eigDim (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) 1 =
      ∑ ε ∈ P, if (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε = ε then
        Module.finrank K (LinearMap.range (Matrix.toLin' ε)) else 0 :=
    ggJSt1_eigDim_one b hb hodd hPprim hPorth hPsum
  have hblockExp : blockExp false (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
      (eigDim (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) 1 / 2) ^ 2 +
        ∑ ε ∈ P.filter (fun ε => (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε ≠ ε),
          (ROf ε).card / 2 * (mOf ε * (mOf ε - 1) / 2) := by
    have hval : ∀ ε (hε : ε ∈ P) (h1 : (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε ≠ ε)
        (l : AlgebraicClosure K), l ∈ ROf ε →
        eigDim (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) l = mOf ε := by
      intro ε hε h1 l hl
      have hPcomm : ∀ ε' ∈ P, IsIdempotentElem ε' ∧
          Commute (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) ε' := by
        intro ε' hε'
        exact ⟨(hPprim ε' hε').2.1, ggJSt1_commute b hbA (hPprim ε' hε').1⟩
      rw [eigDim_eq_sum_eigDimOn (b := (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K))
        hPcomm hPorth hPsum l]
      refine (Finset.sum_eq_single ε ?_ (fun hnot => absurd hε hnot)).trans ?_
      · intro ε' hε' hne'
        rw [hOf ε' hε' l]
        by_cases h1' : (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε' = ε'
        · rw [if_neg]
          intro hl'
          have hR : ROf ε' = ({1} : Finset (AlgebraicClosure K)) := by
            simp only [ROf, dif_pos hε', dif_pos h1']
          have hl1 : l = 1 := Finset.mem_singleton.mp (hR ▸ hl')
          exact hOf_one ε hε h1 (hl1 ▸ hl)
        · rw [if_neg]
          intro hl'
          exact (Finset.disjoint_left.mp (hdisjR ε hε h1 ε' hε' h1' (Ne.symm hne')) hl) hl'
      · rw [hOf ε hε l, if_pos hl]
    have hsum1 : ∑ l ∈ ggJSt1_R (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K),
          eigDim (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) l *
            (eigDim (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) l - 1) / 2 =
        ∑ ε ∈ P.filter (fun ε => (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε ≠ ε),
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
    have hdiv : (∑ ε ∈ P.filter (fun ε => (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε ≠ ε),
          (ROf ε).card * (mOf ε * (mOf ε - 1) / 2)) / 2 =
        ∑ ε ∈ P.filter (fun ε => (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε ≠ ε),
          (ROf ε).card / 2 * (mOf ε * (mOf ε - 1) / 2) := by
      have h1 : ∀ ε ∈ P.filter (fun ε => (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε ≠ ε),
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
    rw [ggJSt1_blockExp_eq, hsum1, hdiv]
  have horder :
      (Nat.card ↥((Subgroup.centralizer {b}).comap (StatedSp n K).subtype)).factorization 2 =
      f * ((eigDim (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) 1 / 2) ^ 2 +
        ∑ ε ∈ P.filter (fun ε => (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε ≠ ε),
          (ROf ε).card / 2 * (mOf ε * (mOf ε - 1) / 2)) := by
    have hcardprod :
        (Nat.card ↥((Subgroup.centralizer {b}).comap (StatedSp n K).subtype)).factorization 2 =
        ∑ ε ∈ P, (Nat.card ↥(glBlockCentralizer (StatedSp n K).subtype {b} ε)).factorization 2 := by
      rw [hPcard, Nat.factorization_prod (fun ε _ => by
        haveI : Nonempty ↥(glBlockCentralizer (StatedSp n K).subtype {b} ε) :=
          ⟨⟨1, (glBlockCentralizer (StatedSp n K).subtype {b} ε).one_mem⟩⟩
        exact Nat.card_pos.ne')]
      simp only [Finsupp.coe_finset_sum, Finset.sum_apply]
    have hblock : ∀ ε (hε : ε ∈ P),
        (Nat.card ↥(glBlockCentralizer (StatedSp n K).subtype {b} ε)).factorization 2 =
          f * (if (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε = ε then
            (Module.finrank K (LinearMap.range (Matrix.toLin' ε)) / 2) ^ 2
            else (ROf ε).card / 2 * (mOf ε * (mOf ε - 1) / 2)) := by
      intro ε hε
      by_cases h1 : (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε = ε
      · rw [if_pos h1]
        obtain ⟨n₁, hn₁, ⟨eG⟩⟩ := blockGroup_iso_Sp_one b hb hodd (hPprim ε hε) h1
        rw [Nat.card_congr eG.toEquiv,
          ggJSt1_factorization_two_card_statedSp (K := K) (n := n₁) (f := f) hf]
        congr 1
        rw [← hn₁, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
        ring
      · rw [if_neg h1]
        set e := Classical.choose (ggJSt1_block_data b hb hodd (hPprim ε hε) h1) with hedef
        set R := Classical.choose (Classical.choose_spec
          (ggJSt1_block_data b hb hodd (hPprim ε hε) h1)) with hRdef
        set m := Classical.choose (Classical.choose_spec (Classical.choose_spec
          (ggJSt1_block_data b hb hodd (hPprim ε hε) h1))) with hmdef
        obtain ⟨he, heε, hcase, hOfR, hRm, h1R, hmPos, hcard, h2deg⟩ :=
          Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
            (ggJSt1_block_data b hb hodd (hPprim ε hε) h1)))
        have hROf : ROf ε = R := by
          rw [hRdef]
          simp only [ROf, dif_pos hε, dif_neg h1]
        rcases hcase with hcase | ⟨hne, hneadj, hεeq⟩
        · obtain ⟨d, m, E, instF, instFin, h1d, hcardE, hdim, hdeg, ⟨eG⟩⟩ :=
            blockGroup_iso_Sp_unitary b hb hodd (hPprim ε hε) (hcase ▸ he) h1
          have hd2 : (ROf ε).card = 2 * d := by
            rw [hROf, hcard hcase, hcase, hdeg]
          have hd : d = (ROf ε).card / 2 := by
            have h2 : 2 * d = 2 * ((ROf ε).card / 2) := by
              rw [← hd2]; exact hOf_even ε hε h1
            exact Nat.mul_left_cancel (by norm_num : 0 < 2) h2
          have hm : m = mOf ε := by
            have h2 : 2 * d * m = 2 * d * mOf ε := by
              rw [hdim, ← hOf_mul ε hε h1, hd2]
            exact Nat.mul_left_cancel (by omega : 0 < 2 * d) h2
          have hE : Fintype.card E = (2 ^ (f * d)) ^ 2 := by
            rw [hcardE, hf]
            ring_nf
          have hK : Fintype.card K ^ d = 2 ^ (f * d) := by
            rw [hf]
            ring_nf
          rw [Nat.card_congr eG.toEquiv, hK,
            factorization_two_card_GUFull (m := m) (g := f * d) hE, hd, hm]
          ring
        · obtain ⟨d, m, E, instF, instFin, h1d, hcardE, hdim, hdeg, ⟨eG⟩⟩ :=
            blockGroup_iso_Sp_linear b hb hodd (hPprim ε hε) he
              (ggJSt1_formAdj_prim b hb he) (Ne.symm hneadj) hεeq
          have hd2 : (ROf ε).card = 2 * d := by
            rw [hROf, h2deg hne, hdeg]
          have hd : d = (ROf ε).card / 2 := by
            have h2 : 2 * d = 2 * ((ROf ε).card / 2) := by
              rw [← hd2]; exact hOf_even ε hε h1
            exact Nat.mul_left_cancel (by norm_num : 0 < 2) h2
          have hm : m = mOf ε := by
            have h2 : 2 * d * m = 2 * d * mOf ε := by
              rw [hdim, ← hOf_mul ε hε h1, hd2]
            exact Nat.mul_left_cancel (by omega : 0 < 2 * d) h2
          have hE : Fintype.card E = 2 ^ (f * d) := by
            rw [hcardE, hf]
            ring_nf
          rw [Nat.card_congr eG.toEquiv,
            ggJSt1_factorization_two_card_GL (m := m) (g := f * d) hE, hd, hm]
          ring
    have hsum : ∑ ε ∈ P, (if (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε = ε then
            (Module.finrank K (LinearMap.range (Matrix.toLin' ε)) / 2) ^ 2
            else (ROf ε).card / 2 * (mOf ε * (mOf ε - 1) / 2)) =
        (eigDim (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) 1 / 2) ^ 2 +
          ∑ ε ∈ P.filter (fun ε => (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε ≠ ε),
            (ROf ε).card / 2 * (mOf ε * (mOf ε - 1) / 2) := by
      rw [← Finset.sum_filter_add_sum_filter_not P
        (fun ε => (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε = ε)
        (fun ε => if (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε = ε then
          (Module.finrank K (LinearMap.range (Matrix.toLin' ε)) / 2) ^ 2
          else (ROf ε).card / 2 * (mOf ε * (mOf ε - 1) / 2))]
      congr 1
      · rw [Finset.sum_congr rfl (fun ε hε => if_pos (Finset.mem_filter.mp hε).2)]
        have hf1 : eigDim (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) 1 =
            ∑ ε ∈ P.filter (fun ε => (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε = ε),
              Module.finrank K (LinearMap.range (Matrix.toLin' ε)) := by
          rw [heig1, ← Finset.sum_filter]
        rw [hf1]
        rcases Finset.eq_empty_or_nonempty
          (P.filter (fun ε => (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε = ε)) with
          h | ⟨ε₁, hε₁⟩
        · rw [h, Finset.sum_empty, Finset.sum_empty]
          norm_num
        · have hsingle : P.filter (fun ε =>
              (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε = ε) = {ε₁} := by
            refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hε₁, ?_⟩
            intro ε hε
            exact ggJSt1_unique_one_block b hb hodd hPprim hPorth (Finset.mem_filter.mp hε).1
              (Finset.mem_filter.mp hε₁).1 (Finset.mem_filter.mp hε).2 (Finset.mem_filter.mp hε₁).2
          rw [hsingle, Finset.sum_singleton, Finset.sum_singleton]
      · rw [Finset.sum_congr rfl (fun ε hε => if_neg (Finset.mem_filter.mp hε).2)]
    rw [hcardprod]
    rw [Finset.sum_congr rfl hblock]
    rw [← Finset.mul_sum, hsum]
  rw [hblockExp]
  exact horder

theorem commutative_centralizer_of_blockExp_eq_zero_Sp {K : Type} [Field K] [Fintype K]
    [CharP K 2] {n : ℕ} (b : GL (Fin n ⊕ Fin n) K) (hb : b ∈ StatedSp n K)
    (hodd : Odd (orderOf b))
    (h0 : blockExp false (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = 0) :
    ∀ x ∈ (Subgroup.centralizer {b}).comap (StatedSp n K).subtype,
      ∀ y ∈ (Subgroup.centralizer {b}).comap (StatedSp n K).subtype, x * y = y * x := by
  classical
  obtain ⟨P, hPprim, hPorth, hPsum, hPcommBlock, hPsup, hPcard⟩ :=
    centralizer_block_decomp_Sp b hb hodd
  have hbA : (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) ∈ ggJSt1_A b :=
    Algebra.subset_adjoin (by simp)
  let ROf (ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) : Finset (AlgebraicClosure K) :=
    if hε : ε ∈ P then
      if h1 : (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε = ε then {1}
      else Classical.choose
        (Classical.choose_spec (ggJSt1_block_data b hb hodd (hPprim ε hε) h1))
    else ∅
  let mOf (ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) : ℕ :=
    if hε : ε ∈ P then
      if h1 : (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε = ε then
        Module.finrank K (LinearMap.range (Matrix.toLin' ε))
      else Classical.choose
        (Classical.choose_spec
          (Classical.choose_spec (ggJSt1_block_data b hb hodd (hPprim ε hε) h1)))
    else 0
  have hOf : ∀ ε (hε : ε ∈ P), ∀ l, eigDimOn (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) ε l =
      if l ∈ ROf ε then mOf ε else 0 := by
    intro ε hε l
    simp only [ROf, mOf, dif_pos hε]
    by_cases h1 : (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε = ε
    · simp only [dif_pos h1]
      by_cases hl : l = 1
      · subst hl
        rw [if_pos (Finset.mem_singleton_self 1)]
        exact (ggJSt1_eigDimOn_primAdj_one b hb hodd (hPprim ε hε)).trans (if_pos h1)
      · rw [if_neg (fun h => hl (Finset.mem_singleton.mp h))]
        exact ggJSt1_eigDimOn_eq_zero_of_b_mul_eq hodd
          (ggJSt1_one_block_prim b hb hodd (hPprim ε hε) h1) h1 hl
    · simp only [dif_neg h1]
      exact (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
        (ggJSt1_block_data b hb hodd (hPprim ε hε) h1)))).2.2.2.1 l
  have hOf_one : ∀ ε (hε : ε ∈ P),
      (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε ≠ ε → 1 ∉ ROf ε := by
    intro ε hε h1
    simp only [ROf, dif_pos hε, dif_neg h1]
    exact (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
      (ggJSt1_block_data b hb hodd (hPprim ε hε) h1)))).2.2.2.2.2.1
  have hOf_pos : ∀ ε (hε : ε ∈ P),
      (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε ≠ ε → 0 < mOf ε := by
    intro ε hε h1
    simp only [mOf, dif_pos hε, dif_neg h1]
    exact (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
      (ggJSt1_block_data b hb hodd (hPprim ε hε) h1)))).2.2.2.2.2.2.1
  have hOf_mul : ∀ ε (hε : ε ∈ P),
      (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε ≠ ε →
      (ROf ε).card * mOf ε = Module.finrank K (LinearMap.range (Matrix.toLin' ε)) := by
    intro ε hε h1
    simp only [ROf, mOf, dif_pos hε, dif_neg h1]
    exact (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
      (ggJSt1_block_data b hb hodd (hPprim ε hε) h1)))).2.2.2.2.1
  have hpart : ggJSt1_R (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
      (P.filter (fun ε => (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε ≠ ε)).biUnion
        ROf := by
    apply Finset.ext
    intro l
    simp only [Finset.mem_biUnion, Finset.mem_filter]
    constructor
    · intro hl
      rw [ggJSt1_R, Finset.mem_erase, Multiset.mem_toFinset] at hl
      obtain ⟨hl1, hlroot⟩ := hl
      have hd : eigDim (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) l ≠ 0 :=
        (ggJSt1_eigDim_ne_zero_iff_mem_roots (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
          (ggJSt1_cast_orderOf_ne_zero hodd) (ggJSt1_matrix_pow_orderOf b)).mpr hlroot
      have hPcomm : ∀ ε ∈ P, IsIdempotentElem ε ∧
          Commute (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) ε := by
        intro ε hε
        exact ⟨(hPprim ε hε).2.1, ggJSt1_commute b hbA (hPprim ε hε).1⟩
      have hsum := eigDim_eq_sum_eigDimOn (b := (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K))
        hPcomm hPorth hPsum l
      have hex : ∃ ε ∈ P, eigDimOn (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) ε l ≠ 0 := by
        by_contra h
        push_neg at h
        rw [hsum] at hd
        exact hd (Finset.sum_eq_zero fun ε hε => h ε hε)
      obtain ⟨ε, hεP, hεne⟩ := hex
      have hbne : (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε ≠ ε := by
        intro h1
        have hlR : l ∈ ROf ε := by
          by_contra hlR
          exact hεne (by rw [hOf ε hεP l, if_neg hlR])
        simp only [ROf, dif_pos hεP, dif_pos h1] at hlR
        exact hl1 (Finset.mem_singleton.mp hlR)
      refine ⟨ε, ⟨hεP, hbne⟩, ?_⟩
      by_contra hlR
      exact hεne (by rw [hOf ε hεP l, if_neg hlR])
    · rintro ⟨ε, ⟨hεP, hbne⟩, hlR⟩
      have hne0 : eigDimOn (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) ε l ≠ 0 := by
        rw [hOf ε hεP l, if_pos hlR]
        exact (hOf_pos ε hεP hbne).ne'
      have hd : eigDim (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) l ≠ 0 := by
        intro h0
        exact hne0 (le_antisymm
          (h0 ▸ ggJSt1_eigDimOn_le_eigDim (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) ε l)
          (Nat.zero_le _))
      rw [ggJSt1_R, Finset.mem_erase, Multiset.mem_toFinset]
      refine ⟨?_, (ggJSt1_eigDim_ne_zero_iff_mem_roots
        (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
        (ggJSt1_cast_orderOf_ne_zero hodd) (ggJSt1_matrix_pow_orderOf b)).mp hd⟩
      intro hl1
      exact hOf_one ε hεP hbne (hl1 ▸ hlR)
  have hOf_even : ∀ ε (hε : ε ∈ P),
      (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε ≠ ε →
      (ROf ε).card = 2 * ((ROf ε).card / 2) := by
    intro ε hε h1
    have hspec := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
      (ggJSt1_block_data b hb hodd (hPprim ε hε) h1)))
    have hROf : ROf ε = Classical.choose (Classical.choose_spec
        (ggJSt1_block_data b hb hodd (hPprim ε hε) h1)) := by
      simp only [ROf, dif_pos hε, dif_neg h1]
    rw [hROf]
    rcases hspec.2.2.1 with hcase | ⟨hne, hneadj, hεeq⟩
    · obtain ⟨d, m', E, instF, instFin, h1d, hcardE, hdm, hdeg, ⟨eG⟩⟩ :=
        blockGroup_iso_Sp_unitary b hb hodd (hPprim ε hε) (hcase ▸ hspec.1) h1
      have hc : (Classical.choose (Classical.choose_spec
          (ggJSt1_block_data b hb hodd (hPprim ε hε) h1))).card =
          blockDegree (ggJSt1_A b) ε := by
        rw [hspec.2.2.2.2.2.2.2.1 hcase, hcase]
      rw [hc, hdeg]
      omega
    · obtain ⟨d, m', E, instF, instFin, h1d, hcardE, hdm, hdeg, ⟨eG⟩⟩ :=
        blockGroup_iso_Sp_linear b hb hodd (hPprim ε hε) hspec.1
          (ggJSt1_formAdj_prim b hb hspec.1) (Ne.symm hneadj) hεeq
      rw [hspec.2.2.2.2.2.2.2.2 hne]
      omega
  have hpiece : ∀ ε (hε : ε ∈ P) (h1 : (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε ≠ ε)
      (a : AlgebraicClosure K), a ∈ ROf ε →
      ∃ p, IsPrimIdemIn (ggJSt1_A b) p ∧ p * ε = p ∧
        eigDimOn (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) p a ≠ 0 := by
    intro ε hε h1 a ha
    have hspec := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
      (ggJSt1_block_data b hb hodd (hPprim ε hε) h1)))
    have hROf : ROf ε = Classical.choose (Classical.choose_spec
        (ggJSt1_block_data b hb hodd (hPprim ε hε) h1)) := by
      simp only [ROf, dif_pos hε, dif_neg h1]
    have hne : eigDimOn (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) ε a ≠ 0 := by
      rw [hspec.2.2.2.1 a, if_pos (by rwa [← hROf])]
      exact hspec.2.2.2.2.2.2.1.ne'
    rcases hspec.2.2.1 with hcase | ⟨hne', hneadj, hεeq⟩
    · refine ⟨Classical.choose (ggJSt1_block_data b hb hodd (hPprim ε hε) h1),
        hspec.1, hspec.2.1, ?_⟩
      rwa [← hcase] at hne
    · have heAdj := ggJSt1_formAdj_prim b hb hspec.1
      have hadd := ggJSt1_eigDimOn_add hspec.1.2.1 heAdj.2.1
        (ggJSt1_commute b hbA hspec.1.1) (ggJSt1_commute b hbA heAdj.1)
        (ggJSt1_prim_orthogonal b hspec.1 heAdj (Ne.symm hneadj))
        (ggJSt1_prim_orthogonal b heAdj hspec.1 hneadj) a
      rw [hεeq, hadd] at hne
      by_cases h0 : eigDimOn (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
          (Classical.choose (ggJSt1_block_data b hb hodd (hPprim ε hε) h1)) a ≠ 0
      · exact ⟨_, hspec.1, hspec.2.1, h0⟩
      · push_neg at h0
        refine ⟨formAdj (RingHom.id K) (ggJSt1_G K n)
          (Classical.choose (ggJSt1_block_data b hb hodd (hPprim ε hε) h1)), heAdj, ?_, ?_⟩
        · have hεadj : formAdj (RingHom.id K) (ggJSt1_G K n) ε = ε := (hPprim ε hε).2.2.2.1
          have hmem : Classical.choose (ggJSt1_block_data b hb hodd (hPprim ε hε) h1) ∈
              ggJSt1_A b := hspec.1.1
          have heq : formAdj (RingHom.id K) (ggJSt1_G K n)
                (Classical.choose (ggJSt1_block_data b hb hodd (hPprim ε hε) h1) * ε) =
              formAdj (RingHom.id K) (ggJSt1_G K n)
                (Classical.choose (ggJSt1_block_data b hb hodd (hPprim ε hε) h1)) := by
            rw [hspec.2.1]
          rw [CFSG.StandardType.ClassicalPosition.Geo.formAdj_mul (RingHom.id K)
            (ggJSt1_isUnit_det_G K n), hεadj] at heq
          rw [ggJSt1_commute b (ggJSt1_formAdj_mem b hb hspec.1.1) (hPprim ε hε).1]
          exact heq
        · intro hc
          exact hne (by rw [h0, hc, add_zero])
  have hdisjR : ∀ ε (hε : ε ∈ P) (h1 : (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε ≠ ε)
      ε' (hε' : ε' ∈ P) (h1' : (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε' ≠ ε'),
      ε ≠ ε' → Disjoint (ROf ε) (ROf ε') := by
    intro ε hε h1 ε' hε' h1' hne
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb hab
    subst hab
    obtain ⟨p, hp, hpε, hpa⟩ := hpiece ε hε h1 a ha
    obtain ⟨p', hp', hp'ε', hp'a⟩ := hpiece ε' hε' h1' a hb
    have hpp' : p * p' = 0 := by
      refine ggJSt1_prim_orthogonal b hp hp' ?_
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
  have heig1 : eigDim (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) 1 =
      ∑ ε ∈ P, if (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε = ε then
        Module.finrank K (LinearMap.range (Matrix.toLin' ε)) else 0 :=
    ggJSt1_eigDim_one b hb hodd hPprim hPorth hPsum
  have hblockExp : blockExp false (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
      (eigDim (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) 1 / 2) ^ 2 +
        ∑ ε ∈ P.filter (fun ε => (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε ≠ ε),
          (ROf ε).card / 2 * (mOf ε * (mOf ε - 1) / 2) := by
    have hval : ∀ ε (hε : ε ∈ P) (h1 : (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε ≠ ε)
        (l : AlgebraicClosure K), l ∈ ROf ε →
        eigDim (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) l = mOf ε := by
      intro ε hε h1 l hl
      have hPcomm : ∀ ε' ∈ P, IsIdempotentElem ε' ∧
          Commute (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) ε' := by
        intro ε' hε'
        exact ⟨(hPprim ε' hε').2.1, ggJSt1_commute b hbA (hPprim ε' hε').1⟩
      rw [eigDim_eq_sum_eigDimOn (b := (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K))
        hPcomm hPorth hPsum l]
      refine (Finset.sum_eq_single ε ?_ (fun hnot => absurd hε hnot)).trans ?_
      · intro ε' hε' hne'
        rw [hOf ε' hε' l]
        by_cases h1' : (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε' = ε'
        · rw [if_neg]
          intro hl'
          have hR : ROf ε' = ({1} : Finset (AlgebraicClosure K)) := by
            simp only [ROf, dif_pos hε', dif_pos h1']
          have hl1 : l = 1 := Finset.mem_singleton.mp (hR ▸ hl')
          exact hOf_one ε hε h1 (hl1 ▸ hl)
        · rw [if_neg]
          intro hl'
          exact (Finset.disjoint_left.mp (hdisjR ε hε h1 ε' hε' h1' (Ne.symm hne')) hl) hl'
      · rw [hOf ε hε l, if_pos hl]
    have hsum1 : ∑ l ∈ ggJSt1_R (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K),
          eigDim (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) l *
            (eigDim (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) l - 1) / 2 =
        ∑ ε ∈ P.filter (fun ε => (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε ≠ ε),
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
    have hdiv : (∑ ε ∈ P.filter (fun ε => (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε ≠ ε),
          (ROf ε).card * (mOf ε * (mOf ε - 1) / 2)) / 2 =
        ∑ ε ∈ P.filter (fun ε => (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε ≠ ε),
          (ROf ε).card / 2 * (mOf ε * (mOf ε - 1) / 2) := by
      have h1 : ∀ ε ∈ P.filter (fun ε => (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε ≠ ε),
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
    rw [ggJSt1_blockExp_eq, hsum1, hdiv]
  have hzero : (eigDim (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) 1 / 2) ^ 2 +
      ∑ ε ∈ P.filter (fun ε => (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε ≠ ε),
        (ROf ε).card / 2 * (mOf ε * (mOf ε - 1) / 2) = 0 := by
    rw [← hblockExp]
    exact h0
  have hfirst : (eigDim (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) 1 / 2) ^ 2 = 0 :=
    (Nat.add_eq_zero.mp hzero).1
  have hsum0 : ∑ ε ∈ P.filter (fun ε => (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε ≠ ε),
        (ROf ε).card / 2 * (mOf ε * (mOf ε - 1) / 2) = 0 := (Nat.add_eq_zero.mp hzero).2
  have hhalf : ∀ ε (hε : ε ∈ P), (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε ≠ ε →
      (ROf ε).card / 2 ≠ 0 := by
    intro ε hε h1 hc
    have h0c : (ROf ε).card = 0 := by rw [hOf_even ε hε h1, hc, mul_zero]
    have hm := hOf_mul ε hε h1
    rw [h0c, zero_mul] at hm
    exact ggJSt1_finrank_range_toLin'_ne_zero (hPprim ε hε).2.2.1 hm.symm
  have hm1 : ∀ ε (hε : ε ∈ P), (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε ≠ ε →
      mOf ε = 1 := by
    intro ε hε h1
    have hterm : (ROf ε).card / 2 * (mOf ε * (mOf ε - 1) / 2) = 0 :=
      (Finset.sum_eq_zero_iff.mp hsum0) ε (Finset.mem_filter.mpr ⟨hε, h1⟩)
    have hmul0 : mOf ε * (mOf ε - 1) / 2 = 0 := by
      rcases Nat.mul_eq_zero.mp hterm with h | h
      · exact absurd h (hhalf ε hε h1)
      · exact h
    have hle : mOf ε ≤ 1 := by
      by_contra h
      push_neg at h
      have h2 : 2 ≤ mOf ε * (mOf ε - 1) := by
        have h1' : 1 ≤ mOf ε - 1 := by omega
        calc 2 = 2 * 1 := by norm_num
          _ ≤ mOf ε * (mOf ε - 1) := Nat.mul_le_mul h h1'
      have h3 : 1 ≤ mOf ε * (mOf ε - 1) / 2 := by omega
      omega
    have hpos := hOf_pos ε hε h1
    omega
  have hno1 : ∀ ε (hε : ε ∈ P), (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε ≠ ε := by
    intro ε hε h1
    have heq : eigDim (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) 1 =
        Module.finrank K (LinearMap.range (Matrix.toLin' ε)) := by
      have hsingle : ∑ ε' ∈ P, (if (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε' = ε' then
            Module.finrank K (LinearMap.range (Matrix.toLin' ε')) else 0) =
          (if (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε = ε then
            Module.finrank K (LinearMap.range (Matrix.toLin' ε)) else 0) :=
        Finset.sum_eq_single ε
          (fun ε' hε' hne' => by
            by_cases h1' : (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε' = ε'
            · rw [if_pos h1']
              exact absurd (ggJSt1_unique_one_block b hb hodd hPprim hPorth hε' hε h1' h1) hne'
            · rw [if_neg h1'])
          (fun hnot => absurd hε hnot)
      rw [heig1, hsingle, if_pos h1]
    obtain ⟨n₁, hn₁, ⟨eG⟩⟩ := blockGroup_iso_Sp_one b hb hodd (hPprim ε hε) h1
    have hlt : eigDim (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) 1 < 2 := by
      have h0' : eigDim (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) 1 / 2 = 0 :=
        sq_eq_zero_iff.mp hfirst
      omega
    rw [heq, ← hn₁] at hlt
    have hz : n₁ = 0 := by omega
    rw [hz, mul_zero] at hn₁
    exact ggJSt1_finrank_range_toLin'_ne_zero (hPprim ε hε).2.2.1 (by omega)
  have habel : ∀ ε (hε : ε ∈ P),
      ∀ x ∈ glBlockCentralizer (StatedSp n K).subtype {b} ε,
      ∀ y ∈ glBlockCentralizer (StatedSp n K).subtype {b} ε, x * y = y * x := by
    intro ε hε x hx y hy
    have h1 := hno1 ε hε
    set e := Classical.choose (ggJSt1_block_data b hb hodd (hPprim ε hε) h1) with hedef
    set R := Classical.choose (Classical.choose_spec
      (ggJSt1_block_data b hb hodd (hPprim ε hε) h1)) with hRdef
    obtain ⟨he, heε, hcase, hOfR, hRm, h1R, hmPos, hcard, h2deg⟩ :=
      Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
        (ggJSt1_block_data b hb hodd (hPprim ε hε) h1)))
    have hROf : ROf ε = R := by
      rw [hRdef]
      simp only [ROf, dif_pos hε, dif_neg h1]
    rcases hcase with hcase | ⟨hne, hneadj, hεeq⟩
    · obtain ⟨d, mm, E, instF, instFin, h1d, hcardE, hdim, hdeg, ⟨eG⟩⟩ :=
        blockGroup_iso_Sp_unitary b hb hodd (hPprim ε hε) (hcase ▸ he) h1
      have hd2 : (ROf ε).card = 2 * d := by
        rw [hROf, hcard hcase, hcase, hdeg]
      have hm1' : mm = 1 := by
        have h2 : 2 * d * mm = 2 * d * 1 := by
          rw [hdim, ← hOf_mul ε hε h1, hm1 ε hε h1, hd2]
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
      have hcomm : ∀ a b : ↥(glBlockCentralizer (StatedSp n K).subtype {b} ε),
          a * b = b * a := by
        intro a b
        exact eG.injective (by rw [map_mul, map_mul, hGU1 (eG a) (eG b)])
      exact Subtype.ext (congrArg (fun z : ↥(glBlockCentralizer (StatedSp n K).subtype {b} ε) =>
        ((z : ↥(StatedSp n K)) : GL (Fin n ⊕ Fin n) K)) (hcomm ⟨x, hx⟩ ⟨y, hy⟩))
    · obtain ⟨d, mm, E, instF, instFin, h1d, hcardE, hdim, hdeg, ⟨eG⟩⟩ :=
        blockGroup_iso_Sp_linear b hb hodd (hPprim ε hε) he
          (ggJSt1_formAdj_prim b hb he) (Ne.symm hneadj) hεeq
      have hd2 : (ROf ε).card = 2 * d := by
        rw [hROf, h2deg hne, hdeg]
      have hm1' : mm = 1 := by
        have h2 : 2 * d * mm = 2 * d * 1 := by
          rw [hdim, ← hOf_mul ε hε h1, hm1 ε hε h1, hd2]
        exact Nat.mul_left_cancel (by omega : 0 < 2 * d) h2
      rw [hm1'] at eG
      have hGL1 : ∀ p q : GL (Fin 1) E, p * q = q * p := by
        intro p q
        refine Units.ext ?_
        ext i j
        fin_cases i
        fin_cases j
        simp [Matrix.mul_apply, mul_comm]
      have hcomm : ∀ a b : ↥(glBlockCentralizer (StatedSp n K).subtype {b} ε),
          a * b = b * a := by
        intro a b
        exact eG.injective (by rw [map_mul, map_mul, hGL1 (eG a) (eG b)])
      exact Subtype.ext (congrArg (fun z : ↥(glBlockCentralizer (StatedSp n K).subtype {b} ε) =>
        ((z : ↥(StatedSp n K)) : GL (Fin n ⊕ Fin n) K)) (hcomm ⟨x, hx⟩ ⟨y, hy⟩))
  have hCcomm : ∀ x ∈ (Subgroup.centralizer {b}).comap (StatedSp n K).subtype,
      ∀ y ∈ (Subgroup.centralizer {b}).comap (StatedSp n K).subtype, x * y = y * x := by
    intro x hx y hy
    rw [← hPsup] at hx hy
    let H : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K → Subgroup (StatedSp n K) :=
      fun ε => glBlockCentralizer (StatedSp n K).subtype {b} ε
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
