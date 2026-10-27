module

public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockDefs
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockOmegaDict
public import CFSG.LocalAnalysis.StandardType.GGOuterInvFieldTags
public import CFSG.LocalAnalysis.StandardType.GGE0Frame
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockDecomp
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoAdj
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.ReducedAlgebra
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.TraceTransfer
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockSpIsoUnitary
public import CFSG.RankThree.PartOne.KC.OrthogonalSelfDualBlock
public import CFSG.RankThree.PartOne.KC.OrthogonalFixedDickson
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryIsometrySpaces
public import CFSG.RankThree.PartOne.AUTSL.OmegaDickson
public import CFSG.ClassicalGroups.Orthogonal.Matrix
public import CFSG.GroupTheory.WeirSylow.UniqueE27Orthogonal
public import CFSG.HardMathSupport.Dickson.Bal207.SemilinCoord
public import CFSG.HardMathSupport.Dickson.Bal207.OrthSU38Torus
public import CFSG.HardMathSupport.Dickson.Bal207.Glue
public import CFSG.HardMathSupport.Dickson.Bal207.OrthSU38Comp
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal209F4
public import CFSG.RankThree.PartOne.S15K.FixedWitt
public import CFSG.RankThree.PartOne.S15K.LayerModel

public section

namespace CFSG.StandardType.ClassicalBlocks

open CFSG CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.StandardType.ClassicalPosition Matrix
open CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.Classical CFSG.RankThree.OrthogonalInvolutions
open Polynomial
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2
open CFSG.RankThree.PartOne.KCUnitary
open CFSG.HardMathSupport.Dickson.Bal207.FirstClaim

private def ggJSo3_IsPrimIdemInEnd {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (A : Subalgebra K (Module.End K V)) (e : Module.End K V) : Prop :=
  e ∈ A ∧ IsIdempotentElem e ∧ e ≠ 0 ∧
    ∀ e' ∈ A, IsIdempotentElem e' → e' * e = e' → e' = 0 ∨ e' = e

private lemma ggJSo3_isPrimIdemIn_map_toLin {K : Type} [Field K] {ι : Type} [Fintype ι]
    [DecidableEq ι] (A : Subalgebra K (Matrix ι ι K)) (ε : Matrix ι ι K)
    (h : IsPrimIdemIn A ε) :
    ggJSo3_IsPrimIdemInEnd (A.map (Matrix.toLinAlgEquiv' (R := K) (n := ι)))
      (Matrix.toLinAlgEquiv' ε) := by
  obtain ⟨hmem, hid, hne, hprim⟩ := h
  refine ⟨Subalgebra.mem_map.mpr ⟨ε, hmem, rfl⟩, ?_, ?_, ?_⟩
  · show Matrix.toLinAlgEquiv' ε * Matrix.toLinAlgEquiv' ε = Matrix.toLinAlgEquiv' ε
    rw [← map_mul, hid.eq]
  · intro h0
    apply hne
    apply (Matrix.toLinAlgEquiv' (R := K) (n := ι)).injective
    rw [h0, map_zero]
  · intro e' he'A hid' he'e
    rw [Subalgebra.mem_map] at he'A
    obtain ⟨e₀, he₀A, rfl⟩ := he'A
    have he'e' : e₀ * ε = e₀ := by
      apply (Matrix.toLinAlgEquiv' (R := K) (n := ι)).injective
      rw [map_mul]
      exact he'e
    have hid0 : IsIdempotentElem e₀ := by
      apply (Matrix.toLinAlgEquiv' (R := K) (n := ι)).injective
      rw [map_mul]
      exact hid'.eq
    rcases hprim e₀ he₀A hid0 he'e' with h | h
    · left; rw [h, map_zero]
    · right; exact congrArg (Matrix.toLinAlgEquiv' (R := K) (n := ι)) h

private lemma ggJSo3_eq_primaryProjection_of_adjoin {K V : Type} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {x : Module.End K V}
    (hsq : Squarefree (minpoly K x)) {e : Module.End K V}
    (heA : e ∈ Algebra.adjoin K ({x} : Set (Module.End K V)))
    (heid : IsIdempotentElem e) (he0 : e ≠ 0)
    (hprim : ∀ g ∈ Algebra.adjoin K ({x} : Set (Module.End K V)),
      IsIdempotentElem g → g * e = g → g = 0 ∨ g = e) :
    ∃ a ∈ primaryFactors x, e = primaryProjection x a := by
  classical
  let A : Subalgebra K (Module.End K V) := Algebra.adjoin K ({x} : Set (Module.End K V))
  have hAcomm : A ≤ commutant x := by
    intro z hz
    refine Algebra.adjoin_le ?_ hz
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact Iff.mpr (mem_commutant x) (Commute.refl x)
  have hcentral : ∀ g ∈ A, ∀ b : commutant x, b.1 * g = g * b.1 := by
    intro g hg b
    refine Algebra.adjoin_induction (p := fun g _ => b.1 * g = g * b.1) ?_ ?_ ?_ ?_ hg
    · intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact (Iff.mp (mem_commutant x) b.2).eq
    · intro c
      rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
    · intro y z hy hz ihy ihz
      rw [mul_add, add_mul, ihy, ihz]
    · intro y z hy hz ihy ihz
      calc b.1 * (y * z) = (b.1 * y) * z := (mul_assoc _ _ _).symm
        _ = (y * b.1) * z := by rw [ihy]
        _ = y * (b.1 * z) := mul_assoc _ _ _
        _ = y * (z * b.1) := by rw [ihz]
        _ = (y * z) * b.1 := (mul_assoc _ _ _).symm
  have hcomm : ∀ g ∈ A, ∀ h ∈ A, g * h = h * g := by
    intro g hg h hh
    exact ((hcentral g hg ⟨h, hAcomm hh⟩).symm)
  have hpaA : ∀ a ∈ primaryFactors x, primaryProjection x a ∈ A := by
    intro a ha
    change primaryProjection x a ∈ Algebra.adjoin K ({x} : Set (Module.End K V))
    rw [Algebra.adjoin_singleton_eq_range_aeval]
    exact ⟨primaryIdempotent x a, rfl⟩
  have hpa_prim : ∀ a ∈ primaryFactors x,
      ∀ g ∈ A, IsIdempotentElem g → g * primaryProjection x a = g →
        g = 0 ∨ g = primaryProjection x a := by
    intro a ha g hgA hgid hga
    have hpc := (isPrimitiveCentralIdempotent_iff hsq (primaryProjectionR x a)).mpr
      ⟨a, ha, rfl⟩
    let gR : commutant x := ⟨g, hAcomm hgA⟩
    have hgmem : gR ∈ Subalgebra.center K (commutant x) := by
      rw [Subalgebra.mem_center_iff]
      intro b
      exact Subtype.ext (hcentral g hgA b)
    have hgidR : IsIdempotentElem gR := Subtype.ext hgid.eq
    have hgmul : gR * primaryProjectionR x a = gR := Subtype.ext hga
    rcases hpc.2.2.2 gR hgmem hgidR hgmul with h | h
    · left
      exact congrArg Subtype.val h
    · right
      exact congrArg Subtype.val h
  have hdecomp : e = ∑ a ∈ primaryFactors x, e * primaryProjection x a := by
    calc e = e * 1 := (mul_one e).symm
      _ = e * (∑ a ∈ primaryFactors x, primaryProjection x a) := by rw [sum_primaryProjection hsq]
      _ = ∑ a ∈ primaryFactors x, e * primaryProjection x a := by rw [Finset.mul_sum]
  have hterm : ∀ a ∈ primaryFactors x,
      e * primaryProjection x a = 0 ∨ e * primaryProjection x a = e := by
    intro a ha
    have hmem : e * primaryProjection x a ∈ A := A.mul_mem heA (hpaA a ha)
    have hid : IsIdempotentElem (e * primaryProjection x a) := by
      have h1 : e * e = e := heid.eq
      have h2 : primaryProjection x a * primaryProjection x a = primaryProjection x a :=
        primaryProjection_mul_self hsq ha
      have h3 : e * primaryProjection x a = primaryProjection x a * e :=
        hcomm e heA (primaryProjection x a) (hpaA a ha)
      show (e * primaryProjection x a) * (e * primaryProjection x a) = e * primaryProjection x a
      calc (e * primaryProjection x a) * (e * primaryProjection x a)
          = e * (primaryProjection x a * (e * primaryProjection x a)) := mul_assoc _ _ _
        _ = e * (primaryProjection x a * (primaryProjection x a * e)) := by rw [h3]
        _ = e * ((primaryProjection x a * primaryProjection x a) * e) := by
              rw [mul_assoc, ← mul_assoc]
        _ = e * (primaryProjection x a * e) := by rw [h2]
        _ = e * (e * primaryProjection x a) := by rw [← h3]
        _ = (e * e) * primaryProjection x a := (mul_assoc _ _ _).symm
        _ = e * primaryProjection x a := by rw [h1]
    have hEe : (e * primaryProjection x a) * e = e * primaryProjection x a := by
      rw [hcomm (e * primaryProjection x a) hmem e heA, ← mul_assoc, heid.eq]
    exact hprim (e * primaryProjection x a) hmem hid hEe
  have hex : ∃ a ∈ primaryFactors x, e * primaryProjection x a = e := by
    by_contra h
    push Not at h
    have hz : ∀ a ∈ primaryFactors x, e * primaryProjection x a = 0 := fun a ha =>
      (hterm a ha).resolve_right (h a ha)
    apply he0
    rw [hdecomp, Finset.sum_eq_zero hz]
  obtain ⟨a, ha, hae⟩ := hex
  exact ⟨a, ha, (hpa_prim a ha e heA heid hae).resolve_left he0⟩

private lemma ggJSo3_toLin'_eq_toLinAlgEquiv' {K : Type} [Field K] {ι : Type} [Fintype ι]
    [DecidableEq ι] (M : Matrix ι ι K) :
    (Matrix.toLin' M : (ι → K) →ₗ[K] ι → K) = Matrix.toLinAlgEquiv' M := by
  ext v
  rfl

private lemma ggJSo3_squarefree_minpoly {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [CharP K 2] (b : GL ι K) (hodd : Odd (orderOf b)) :
    Squarefree (minpoly K (Matrix.toLin' (b : Matrix ι ι K))) := by
  classical
  have hb1 : (Matrix.toLin' (b : Matrix ι ι K)) ^ orderOf b = 1 := by
    have h : Matrix.toLinAlgEquiv' ((b : Matrix ι ι K) ^ orderOf b) = 1 := by
      rw [← Units.val_pow_eq_pow_val, pow_orderOf_eq_one b, Units.val_one, map_one]
    have h2 : (Matrix.toLinAlgEquiv' (b : Matrix ι ι K) : Module.End K (ι → K)) ^ orderOf b
        = 1 := by
      rw [← map_pow]
      exact h
    rwa [← ggJSo3_toLin'_eq_toLinAlgEquiv'] at h2
  have hoK : ((orderOf b : ℕ) : K) ≠ 0 := by
    intro h0
    exact hodd.not_two_dvd_nat ((CharP.cast_eq_zero_iff K 2 (orderOf b)).mp h0)
  have hsqp : Squarefree (Polynomial.X ^ orderOf b - 1 : Polynomial K) := by
    have h := Polynomial.separable_X_pow_sub_C (1 : K) hoK one_ne_zero
    simpa using h.squarefree
  refine squarefree_minpoly_of_aeval_eq_zero hsqp ?_
  rw [map_sub, map_pow, aeval_X, map_one, sub_eq_zero]
  exact hb1

private lemma ggJSo3_exists_primaryProjection {ι K : Type} [Fintype ι] [DecidableEq ι]
    [Field K] [CharP K 2] (b : GL ι K)
    (hodd : Odd (orderOf b)) {ε : Matrix ι ι K}
    (hp : IsPrimIdemIn (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε) :
    ∃ h ∈ primaryFactors (Matrix.toLin' (b : Matrix ι ι K)),
      (Matrix.toLin' ε : Module.End K (ι → K)) =
        primaryProjection (Matrix.toLin' (b : Matrix ι ι K)) h := by
  classical
  let A : Subalgebra K (Matrix ι ι K) :=
    Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))
  have hprimE := ggJSo3_isPrimIdemIn_map_toLin A ε hp
  have hmapA : A.map (Matrix.toLinAlgEquiv' (R := K) (n := ι)) =
      Algebra.adjoin K ({Matrix.toLinAlgEquiv' (b : Matrix ι ι K)} :
        Set (Module.End K (ι → K))) := by
    rw [AlgHom.map_adjoin]
    congr 1
    ext y
    constructor
    · rintro ⟨z, ⟨u, hu, rfl⟩, rfl⟩
      rw [Set.mem_singleton_iff] at hu
      subst hu
      exact rfl
    · intro hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact ⟨(b : Matrix ι ι K), ⟨b, rfl, rfl⟩, rfl⟩
  rw [hmapA] at hprimE
  have hsq : Squarefree (minpoly K (Matrix.toLin' (b : Matrix ι ι K))) :=
    ggJSo3_squarefree_minpoly b hodd
  obtain ⟨h, hh, heq⟩ := ggJSo3_eq_primaryProjection_of_adjoin hsq hprimE.1 hprimE.2.1
    hprimE.2.2.1 hprimE.2.2.2
  refine ⟨h, hh, ?_⟩
  rwa [ggJSo3_toLin'_eq_toLinAlgEquiv'] at heq

private lemma ggJSo3_primaryProjection_ne_zero {K V : Type} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {x : Module.End K V}
    (hsq : Squarefree (minpoly K x)) {a : K[X]} (ha : a ∈ primaryFactors x) :
    primaryProjection x a ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (primaryComponent_ne_bot hsq ha)
  have h := primaryProjection_of_mem hsq ha hv
  simp [h0] at h
  exact hv0 h.symm

private lemma ggJSo3_oddOrderIsometry {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (b : GL ι K)
    (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b)) :
    OddOrderIsometry Φ (orderOf b) (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K b) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := hb
    rw [statedOmega_eq_comap (Q := Φ) (Q₀ := ⇑Φ) rfl, Subgroup.mem_comap] at h
    exact CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup (Q := Φ) h
  · show (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K b) ^ orderOf b = 1
    rw [← MulEquiv.orderOf_eq (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K) b]
    exact pow_orderOf_eq_one (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K b)
  · intro h0
    have h2 : 2 ∣ orderOf b := (CharP.cast_eq_zero_iff K 2 (orderOf b)).mp h0
    exact hodd.not_two_dvd_nat h2
  · intro v hv
    exact hΦ.1 v hv

theorem selfDual_primaryProjection_of_prim_adjoint
    {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (b : GL ι K)
    (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b)) {ε : Matrix ι ι K}
    (hε : IsPrimAdjIdemIn (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε)
    {h : K[X]} (hh : h ∈ primaryFactors (Matrix.toLin' (b : Matrix ι ι K)))
    (hae : (Matrix.toLin' ε : Module.End K (ι → K)) =
      primaryProjection (Matrix.toLin' (b : Matrix ι ι K)) h) :
    reciprocalPolynomial h = h := by
  classical
  let x : (ι → K) ≃ₗ[K] (ι → K) := CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K b
  have hx : OddOrderIsometry Φ (orderOf b) x := ggJSo3_oddOrderIsometry Φ hΦ b hb hodd
  have hxeq : x.toLinearMap = Matrix.toLin' (b : Matrix ι ι K) :=
    ggOmegaBlk_toLinEquiv_toLinearMap b
  have hh' : h ∈ primaryFactors x.toLinearMap := by rw [hxeq]; exact hh
  have haeAlg : Matrix.toLinAlgEquiv' ε = primaryProjection x.toLinearMap h := by
    rw [ggOmegaBlk_toLinAlgEquiv'_eq_toLin', hae, hxeq]
  have hrec : Matrix.toLinAlgEquiv' (formAdj (RingHom.id K)
      (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)) ε) =
      primaryProjection x.toLinearMap (reciprocalPolynomial h) :=
    ggOmegaBlk_matrix_adjoint_primaryProjection Φ hΦ hx hh' haeAlg
  have hproj : primaryProjection x.toLinearMap (reciprocalPolynomial h) =
      primaryProjection x.toLinearMap h := by
    rw [← hrec, hε.2.2.2.1, haeAlg]
  by_contra hne
  have hne' : h ≠ reciprocalPolynomial h := fun hh' => hne hh'.symm
  have hzero := ggOmegaBlk_primaryProjection_mul_eq_zero hx.squarefree_minpoly hh'
    (hx.reciprocalPolynomial_mem hh') hne'
  rw [hproj, primaryProjection_mul_self hx.squarefree_minpoly hh'] at hzero
  exact ggJSo3_primaryProjection_ne_zero hx.squarefree_minpoly hh' hzero

lemma ggJSo3_ne_one {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [CharP K 2] (b : GL ι K) (hodd : Odd (orderOf b))
    {ε : Matrix ι ι K} {h : K[X]}
    (hh : h ∈ primaryFactors (Matrix.toLin' (b : Matrix ι ι K)))
    (hae : (Matrix.toLin' ε : Module.End K (ι → K)) =
      primaryProjection (Matrix.toLin' (b : Matrix ι ι K)) h)
    (h1 : (b : Matrix ι ι K) * ε ≠ ε) : h ≠ X - 1 := by
  intro ha1
  apply h1
  have hsq := ggJSo3_squarefree_minpoly b hodd
  have haeAlg : Matrix.toLinAlgEquiv' ε =
      primaryProjection (Matrix.toLinAlgEquiv' (b : Matrix ι ι K)) h := by
    rw [← ggJSo3_toLin'_eq_toLinAlgEquiv', ← ggJSo3_toLin'_eq_toLinAlgEquiv']
    exact hae
  have hxpa : Matrix.toLinAlgEquiv' (b : Matrix ι ι K) *
      primaryProjection (Matrix.toLinAlgEquiv' (b : Matrix ι ι K)) h
      = primaryProjection (Matrix.toLinAlgEquiv' (b : Matrix ι ι K)) h := by
    apply LinearMap.ext
    intro v
    have hX1 : (X - 1 : K[X]) ∈ primaryFactors (Matrix.toLinAlgEquiv' (b : Matrix ι ι K)) := by
      rw [← ggJSo3_toLin'_eq_toLinAlgEquiv']
      exact ha1 ▸ hh
    have hv := primaryProjection_mem hsq hX1 v
    rw [mem_primaryComponent_X_sub_one] at hv
    rw [ha1, Module.End.mul_apply]
    exact hv
  have hbε : (b : Matrix ι ι K) * ε = ε := by
    apply (Matrix.toLinAlgEquiv' (R := K) (n := ι)).injective
    rw [map_mul, haeAlg]
    exact hxpa
  exact hbε

private lemma ggJSo3_GUFull_eq_primeFormUnitary {E : Type} [Field E] {m p f Q : ℕ}
    (h : UnitaryFieldData p f E) (hbar : ∀ x : E, h.bar x = x ^ Q) :
    GUFull m Q E = primeFormUnitary h (idGram E m) := by
  apply le_antisymm
  · rw [GUFull, Subgroup.closure_le]
    intro A hA
    rw [Set.mem_setOf_eq] at hA
    change A ∈ primeFormUnitary h (idGram E m)
    rw [mem_primeFormUnitary]
    have hmap : (A : Matrix (Fin m) (Fin m) E).map h.bar =
        (A : Matrix (Fin m) (Fin m) E).map (· ^ Q) := by
      ext i j
      simp only [Matrix.map_apply, hbar]
    rw [hmap]
    simpa only [idGram, Units.val_one, Matrix.mul_one] using hA
  · intro A hA
    refine Subgroup.subset_closure ?_
    rw [Set.mem_setOf_eq]
    have hA' := (mem_primeFormUnitary.mp hA)
    have hmap : (A : Matrix (Fin m) (Fin m) E).map h.bar =
        (A : Matrix (Fin m) (Fin m) E).map (· ^ Q) := by
      ext i j
      simp only [Matrix.map_apply, hbar]
    rw [idGram, Units.val_one, Matrix.mul_one] at hA'
    rwa [hmap] at hA'

noncomputable def sesqUnitaryGroupCoordinateEquiv
    {E W : Type} [Field E] [AddCommGroup W] [Module E W] {m : ℕ}
    {p f : ℕ} (h : UnitaryFieldData p f E) {B : W →ₛₗ[h.bar] W →ₗ[E] E}
    (e : Module.Basis (Fin m) E W) {G : Matrix (Fin m) (Fin m) E}
    (he : ∀ i j, B (e i) (e j) = G i j) :
    ↥(sesqUnitaryGroup B) ≃* ↥(primeFormUnitary h G) := by
  have hiff : ∀ M : GL (Fin m) E,
      Matrix.GeneralLinearGroup.toLin' e M ∈ sesqUnitaryGroup B ↔
        M ∈ primeFormUnitary h G := by
    intro M
    rw [mem_sesqUnitaryGroup, mem_primeFormUnitary]
    constructor
    · intro hiso
      rw [← gramForm_isometry_iff h G M]
      intro u v
      have huv := hiso (e.equivFun.symm u) (e.equivFun.symm v)
      simpa only [CFSG.RankThree.CentralLift.form_eq_gramForm h e he,
        CFSG.RankThree.CentralLift.equivFun_toLin'_basis_apply,
        LinearEquiv.apply_symm_apply] using huv
    · intro hM x y
      rw [CFSG.RankThree.CentralLift.form_eq_gramForm h e he,
        CFSG.RankThree.CentralLift.form_eq_gramForm h e he,
        CFSG.RankThree.CentralLift.equivFun_toLin'_basis_apply,
        CFSG.RankThree.CentralLift.equivFun_toLin'_basis_apply]
      exact (gramForm_isometry_iff h G M).mpr hM _ _
  let Ψ := Matrix.GeneralLinearGroup.toLin' e
  have hEq : (primeFormUnitary h G).map Ψ.toMonoidHom = sesqUnitaryGroup B := by
    ext g
    constructor
    · rintro ⟨M, hM, rfl⟩
      exact (hiff M).2 hM
    · intro hg
      refine ⟨Ψ.symm g, (hiff _).1 ?_, ?_⟩
      · change Ψ (Ψ.symm g) ∈ sesqUnitaryGroup B
        rwa [MulEquiv.apply_symm_apply]
      · exact Ψ.apply_symm_apply g
  exact ((Ψ.subgroupMap (primeFormUnitary h G)).trans (MulEquiv.subgroupCongr hEq)).symm

@[simp] theorem sesqUnitaryGroupCoordinateEquiv_apply
    {E W : Type} [Field E] [AddCommGroup W] [Module E W] {m : ℕ}
    {p f : ℕ} (h : UnitaryFieldData p f E) {B : W →ₛₗ[h.bar] W →ₗ[E] E}
    (e : Module.Basis (Fin m) E W) {G : Matrix (Fin m) (Fin m) E}
    (he : ∀ i j, B (e i) (e j) = G i j) (g : ↥(sesqUnitaryGroup B)) :
    ((sesqUnitaryGroupCoordinateEquiv h e he g : ↥(primeFormUnitary h G)) :
        GL (Fin m) E) =
      (Matrix.GeneralLinearGroup.toLin' e).symm
        (g : LinearMap.GeneralLinearGroup E W) := by
  rfl

theorem exists_selfDual_supportedBlock_coordinateEquiv_hermitian
    {K V : Type} [Field K] [Fintype K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x) (hp2 : Odd p)
    {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hself : h = reciprocalPolynomial h) :
    letI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
    ∃ (d m ℓ f : ℕ) (hU : UnitaryFieldData ℓ (f * d) (AdjoinRoot h))
      (H : primaryComponent x.toLinearMap h → primaryComponent x.toLinearMap h →
        AdjoinRoot h)
      (B : primaryComponent x.toLinearMap h →ₛₗ[hU.bar]
        primaryComponent x.toLinearMap h →ₗ[AdjoinRoot h] AdjoinRoot h),
      1 ≤ d ∧
      Nat.card K = ℓ ^ f ∧
      Nat.card (AdjoinRoot h) = (Nat.card K ^ d) ^ 2 ∧
      Module.finrank K (AdjoinRoot h) = 2 * d ∧
      2 * d * m = Module.finrank K (primaryComponent x.toLinearMap h) ∧
      h.natDegree = 2 * d ∧
      (∀ u w : primaryComponent x.toLinearMap h, B u w = H u w) ∧
      (∀ (u w : primaryComponent x.toLinearMap h) (c : AdjoinRoot h),
        Algebra.trace K (AdjoinRoot h) (H u w * c) =
          QuadraticMap.polar ⇑Q (u : V) ((c • w : primaryComponent x.toLinearMap h) : V)) ∧
      (∀ z : AdjoinRoot h, hU.bar z = z ^ (Nat.card K ^ d)) ∧
      ∃ (b : Module.Basis (Fin m) (AdjoinRoot h) (primaryComponent x.toLinearMap h))
        (e : ↥(supportedBlock Q x h) ≃*
          ↥(GUFull m (Nat.card K ^ d) (AdjoinRoot h))),
        (∀ i j : Fin m, B (b i) (b j) = if i = j then 1 else 0) ∧
        ∀ g : ↥(supportedBlock Q x h),
          (e g : GL (Fin m) (AdjoinRoot h)) =
            (Matrix.GeneralLinearGroup.toLin' b).symm (blockGL Q x h g) := by
  classical
  letI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have hirr := irreducible_of_mem_primaryFactors hh
  haveI : Finite (AdjoinRoot h) := finite_adjoinRoot_of_fact h
  haveI : Fintype (AdjoinRoot h) := Fintype.ofFinite _
  obtain ⟨d, H, hdeg, hroot, hH, hadd1, hadd2, hleft, hright, hsymm⟩ :=
    hx.exists_selfDual_hermitian hp2 hh hne1 hself
  have hd : Module.finrank K (AdjoinRoot h) = 2 * d := by
    rw [(AdjoinRoot.powerBasis hirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hdeg]
  obtain ⟨ℓ, f, hU, hq, hbar⟩ := exists_unitaryFieldData K (AdjoinRoot h) hd
  have hbar' : ∀ z, frobPow K (AdjoinRoot h) d z = hU.bar z := fun z => by
    rw [hbar, frobPow_apply]
  let B : primaryComponent x.toLinearMap h →ₛₗ[hU.bar]
      primaryComponent x.toLinearMap h →ₗ[AdjoinRoot h] AdjoinRoot h :=
    LinearMap.mk₂'ₛₗ hU.bar (RingHom.id _) H hadd1
      (fun c u w => by rw [hleft, smul_eq_mul, hbar']) hadd2
      (fun c u w => by rw [hright, smul_eq_mul, RingHom.id_apply])
  have hBH : ∀ u w, B u w = H u w := fun u w => rfl
  have hBsymm : B.IsSymm := ⟨fun u w => by rw [hBH, hBH, hsymm u w, hbar']⟩
  have hBl : B.SeparatingLeft := by
    intro u hu
    refine Subtype.ext (hx.eq_zero_of_polar_selfdual hh hself u.2 fun w hw => ?_)
    have h1 := hH u ⟨w, hw⟩ 1
    rw [mul_one, one_smul] at h1
    have h2 : H u ⟨w, hw⟩ = 0 := by rw [← hBH]; exact hu _
    rw [h2, map_zero] at h1
    exact h1.symm
  have hrange : (blockGL Q x h).range = sesqUnitaryGroup B := by
    ext γ
    rw [hx.mem_range_blockGL_selfDual_iff hh hne1 hself H hH, mem_sesqUnitaryGroup]
    exact Iff.rfl
  let e₁ : ↥(supportedBlock Q x h) ≃* ↥(sesqUnitaryGroup B) :=
    (MonoidHom.ofInjective (hx.blockGL_injective hh)).trans (MulEquiv.subgroupCongr hrange)
  have he₁ : ∀ g : ↥(supportedBlock Q x h),
      (e₁ g : BlockGL x h) = blockGL Q x h g := fun g => rfl
  let m : ℕ := Module.finrank (AdjoinRoot h) (primaryComponent x.toLinearMap h)
  obtain ⟨b, hb⟩ := hU.exists_orthonormal_basis (B := B) hBsymm hBl
  have hbG : ∀ i j : Fin m, B (b i) (b j) = (idGram (AdjoinRoot h) m) i j := by
    intro i j
    rw [hb i j, idGram, Units.val_one, Matrix.one_apply]
  let eU : ↥(sesqUnitaryGroup B) ≃*
      ↥(primeFormUnitary hU (idGram (AdjoinRoot h) m)) :=
    sesqUnitaryGroupCoordinateEquiv hU b hbG
  have hbarQ : ∀ z : AdjoinRoot h, hU.bar z = z ^ (Nat.card K ^ d) := by
    intro z
    rw [← hbar', frobPow_apply, Nat.card_eq_fintype_card]
  have hd1 : 1 ≤ d := by
    have hpos : 0 < h.natDegree := Irreducible.natDegree_pos hirr
    omega
  have hcardE : Nat.card (AdjoinRoot h) = (Nat.card K ^ d) ^ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := AdjoinRoot h), hd,
      Nat.card_eq_fintype_card]
    rw [show (Fintype.card K ^ d) ^ 2 = Fintype.card K ^ (d * 2) by rw [pow_mul]]
    congr 1
    ring
  have hdim : 2 * d * m = Module.finrank K (primaryComponent x.toLinearMap h) := by
    have h := Module.finrank_mul_finrank K (AdjoinRoot h) (primaryComponent x.toLinearMap h)
    rw [hd] at h
    rw [h]
  let e : ↥(supportedBlock Q x h) ≃*
      ↥(GUFull m (Nat.card K ^ d) (AdjoinRoot h)) :=
    e₁.trans (eU.trans (MulEquiv.subgroupCongr
      (ggJSo3_GUFull_eq_primeFormUnitary hU hbarQ).symm))
  have hbB : ∀ i j : Fin m, B (b i) (b j) = if i = j then 1 else 0 := by
    intro i j
    rw [hbG, idGram, Units.val_one, Matrix.one_apply]
  refine ⟨d, m, ℓ, f, hU, H, B, hd1, hq, hcardE, hd, hdim, hdeg, hBH, hH,
    hbarQ, b, e, hbB, ?_⟩
  intro g
  change ((eU (e₁ g) : ↥(primeFormUnitary hU (idGram (AdjoinRoot h) m))) :
      GL (Fin m) (AdjoinRoot h)) =
    (Matrix.GeneralLinearGroup.toLin' b).symm (blockGL Q x h g)
  rw [sesqUnitaryGroupCoordinateEquiv_apply, he₁]

theorem exists_selfDual_supportedBlock_coordinateEquiv
    {K V : Type} [Field K] [Fintype K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x) (hp2 : Odd p)
    {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hself : h = reciprocalPolynomial h) :
    letI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
    ∃ (d m ℓ f : ℕ) (hU : UnitaryFieldData ℓ (f * d) (AdjoinRoot h)),
      1 ≤ d ∧
      Nat.card K = ℓ ^ f ∧
      Nat.card (AdjoinRoot h) = (Nat.card K ^ d) ^ 2 ∧
      Module.finrank K (AdjoinRoot h) = 2 * d ∧
      2 * d * m = Module.finrank K (primaryComponent x.toLinearMap h) ∧
      h.natDegree = 2 * d ∧
      ∃ (b : Module.Basis (Fin m) (AdjoinRoot h) (primaryComponent x.toLinearMap h))
        (e : ↥(supportedBlock Q x h) ≃*
          ↥(GUFull m (Nat.card K ^ d) (AdjoinRoot h))),
        ∀ g : ↥(supportedBlock Q x h),
          (e g : GL (Fin m) (AdjoinRoot h)) =
            (Matrix.GeneralLinearGroup.toLin' b).symm (blockGL Q x h g) := by
  obtain ⟨d, m, ℓ, f, hU, _H, _B, hd1, hq, hcard, hd, hdim, hdeg,
    _hBH, _htr, _hbar, b, e, _hbB, he⟩ :=
    exists_selfDual_supportedBlock_coordinateEquiv_hermitian hx hp2 hh hne1 hself
  exact ⟨d, m, ℓ, f, hU, hd1, hq, hcard, hd, hdim, hdeg, b, e, he⟩

theorem exists_selfDual_supportedBlock_unitary_action
    {K V : Type} [Field K] [Fintype K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x) (hp2 : Odd p)
    {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hself : h = reciprocalPolynomial h)
    {σ : K ≃+* K} {S : V ≃+ V}
    (hS : ∀ (c : K) (v : V), S (c • v) = σ c • S v)
    (hSx : ∀ v, S (x v) = x (S v))
    (hSQ : ∀ v, Q (S v) = σ (Q v))
    (hσ : σ ≠ 1)
    (hhσ : h.map (σ : K →+* K) = h) :
    letI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
    ∃ (d m ℓ f : ℕ) (hU : UnitaryFieldData ℓ (f * d) (AdjoinRoot h))
      (b : Module.Basis (Fin m) (AdjoinRoot h) (primaryComponent x.toLinearMap h))
      (e : ↥(supportedBlock Q x h) ≃*
        ↥(GUFull m (Nat.card K ^ d) (AdjoinRoot h)))
      (B : ↥(GUFull m (Nat.card K ^ d) (AdjoinRoot h)))
      (τ : AdjoinRoot h ≃+* AdjoinRoot h),
      1 ≤ d ∧
      Nat.card K = ℓ ^ f ∧
      Nat.card (AdjoinRoot h) = (Nat.card K ^ d) ^ 2 ∧
      Module.finrank K (AdjoinRoot h) = 2 * d ∧
      2 * d * m = Module.finrank K (primaryComponent x.toLinearMap h) ∧
      h.natDegree = 2 * d ∧
      (∀ c : K, hU.bar (algebraMap K (AdjoinRoot h) c) =
        algebraMap K (AdjoinRoot h) c) ∧
      (∀ z : AdjoinRoot h, hU.bar z = z ^ (Nat.card K ^ d)) ∧
      τ = CFSG.HardMathSupport.Dickson.Bal207.FirstClaim.extAut h σ hhσ ∧
      (∀ g g' : ↥(supportedBlock Q x h),
        (∀ v : V, (g' : V ≃ₗ[K] V) v = S ((g : V ≃ₗ[K] V) (S.symm v))) →
        (e g' : GL (Fin m) (AdjoinRoot h)) =
          (B : GL (Fin m) (AdjoinRoot h)) *
            Matrix.GeneralLinearGroup.map (τ : AdjoinRoot h →+* AdjoinRoot h)
              (e g : GL (Fin m) (AdjoinRoot h)) *
            (B : GL (Fin m) (AdjoinRoot h))⁻¹) ∧
      τ ≠ 1 ∧
      CFSG.RankThree.PartOne.KCOrthogonal.fixedSubfieldAut K (AdjoinRoot h) d τ ≠ 1 := by
  classical
  letI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  obtain ⟨d, m, ℓ, f, hU, H, Bform, hd1, hq, hcard, hd, hdim, hdeg,
    hBH, htr, hbar, b, e, hbB, he⟩ :=
    exists_selfDual_supportedBlock_coordinateEquiv_hermitian hx hp2 hh hne1 hself
  haveI : Finite K := Finite.of_fintype K
  let T : primaryComponent x.toLinearMap h ≃+ primaryComponent x.toLinearMap h :=
    CFSG.HardMathSupport.Dickson.Bal207.OrthFix.semilinRestrict (S := S) (xe := x)
      hS hSx hhσ
  have hTsmul : ∀ (c : AdjoinRoot h) (v : primaryComponent x.toLinearMap h),
      T (c • v) = CFSG.HardMathSupport.Dickson.Bal207.FirstClaim.extAut h σ hhσ c • T v :=
    CFSG.HardMathSupport.Dickson.Bal207.OrthFix.semilinRestrict_smul (S := S) (xe := x)
      hS hSx hhσ
  have hTorth : ∀ i j : Fin m,
      Bform (T (b i)) (T (b j)) = if i = j then 1 else 0 := by
    intro i j
    rw [hBH (T (b i)) (T (b j))]
    rw [CFSG.HardMathSupport.Dickson.Bal207.OrthFix.herm_semilinRestrict_finite
      (Q := Q) hS hSx hSQ hhσ htr (b i) (b j),
      ← hBH (b i) (b j), hbB i j]
    by_cases hij : i = j <;> simp [hij]
  have hBmat : ((semMat b T).map hU.bar)ᵀ * semMat b T = 1 :=
    semMat_unitary b hU hbB hTorth
  have hBmem : ((semMatUnit b T hTsmul : GL (Fin m) (AdjoinRoot h)) :
      GL (Fin m) (AdjoinRoot h)) ∈ GUFull m (Nat.card K ^ d) (AdjoinRoot h) := by
    rw [ggJSo3_GUFull_eq_primeFormUnitary hU hbar]
    rw [mem_primeFormUnitary]
    rw [coe_semMatUnit]
    simpa [idGram] using hBmat
  let B : ↥(GUFull m (Nat.card K ^ d) (AdjoinRoot h)) :=
    ⟨semMatUnit b T hTsmul, hBmem⟩
  let τ : AdjoinRoot h ≃+* AdjoinRoot h :=
    CFSG.HardMathSupport.Dickson.Bal207.FirstClaim.extAut h σ hhσ
  have hτeq : τ = CFSG.HardMathSupport.Dickson.Bal207.FirstClaim.extAut h σ hhσ := rfl
  have hsquare : ∀ g g' : ↥(supportedBlock Q x h),
      (∀ v : V, (g' : V ≃ₗ[K] V) v = S ((g : V ≃ₗ[K] V) (S.symm v))) →
      (e g' : GL (Fin m) (AdjoinRoot h)) =
        (B : GL (Fin m) (AdjoinRoot h)) *
          Matrix.GeneralLinearGroup.map (τ : AdjoinRoot h →+* AdjoinRoot h)
            (e g : GL (Fin m) (AdjoinRoot h)) *
          (B : GL (Fin m) (AdjoinRoot h))⁻¹ := by
    intro g g' hgg'
    have hggT : ∀ w : primaryComponent x.toLinearMap h,
        ((blockGL Q x h g' : BlockGL x h) : Module.End (AdjoinRoot h)
          (primaryComponent x.toLinearMap h)) w =
          T (((blockGL Q x h g : BlockGL x h) : Module.End (AdjoinRoot h)
            (primaryComponent x.toLinearMap h)) (T.symm w)) :=
      CFSG.HardMathSupport.Dickson.Bal207.OrthFix.blockGL_semilinRestrict_square
        (Q := Q) (x := x) hS hSx hhσ (g := g) (g' := g') hgg'
    have hcoord := toLin'_symm_conj_semilin (b := b) (S := T) (τ := τ)
      hTsmul (blockGL Q x h g) (blockGL Q x h g') hggT
    rw [he g', he g]
    simpa [B] using hcoord
  have hbarK : ∀ c : K, hU.bar (algebraMap K (AdjoinRoot h) c) =
      algebraMap K (AdjoinRoot h) c := by
    intro c
    rw [hbar, ← map_pow, Nat.card_eq_fintype_card]
    congr 1
    exact FiniteField.pow_card_pow d c
  have hτne : τ ≠ 1 := by
    intro h1
    exact hσ ((extAut_eq_one_iff (g := h) hhσ).mp h1)
  have hfixed : CFSG.RankThree.PartOne.KCOrthogonal.fixedSubfieldAut K (AdjoinRoot h) d τ ≠ 1 :=
    CFSG.RankThree.PartOne.KCOrthogonal.fixedSubfieldAut_ne_one K (AdjoinRoot h) d σ τ
      (fun c => extAut_of hhσ c) hσ
  refine ⟨d, m, ℓ, f, hU, b, e, B, τ, hd1, hq, hcard, hd, hdim, hdeg, hbarK, hbar,
    hτeq, ?_, hτne, hfixed⟩
  exact hsquare

private lemma ggJSo3_ker_selfDual {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {x : Module.End K V} (hsq : Squarefree (minpoly K x))
    {h : K[X]} (hh : h ∈ primaryFactors x) (hself : h = reciprocalPolynomial h) :
    LinearMap.ker (primaryProjection x h) = othersSpace x h := by
  apply le_antisymm
  · intro v hv
    rw [LinearMap.mem_ker] at hv
    have hsum : v = ∑ k ∈ primaryFactors x, primaryProjection x k v := by
      have := LinearMap.congr_fun (sum_primaryProjection hsq) v
      rw [LinearMap.sum_apply, Module.End.one_apply] at this
      exact this.symm
    rw [hsum]
    refine Submodule.sum_mem _ fun k hk => ?_
    have hmem := primaryProjection_mem hsq hk v
    by_cases hkh : k = h
    · subst hkh
      rw [hv]
      exact Submodule.zero_mem _
    · exact Submodule.mem_iSup_of_mem k (Submodule.mem_iSup_of_mem
        ⟨hk, hkh, by rw [← hself]; exact hkh⟩ hmem)
  · intro v hv
    rw [LinearMap.mem_ker]
    unfold othersSpace at hv
    refine Submodule.iSup_induction _ (motive := fun v => primaryProjection x h v = 0) hv
      (fun k w hw => ?_) (by simp) (fun a b ha hb => by rw [map_add, ha, hb, add_zero])
    refine Submodule.iSup_induction _ (motive := fun w => primaryProjection x h w = 0) hw
      (fun hk w hw => ?_) (by simp) (fun a b ha hb => by rw [map_add, ha, hb, add_zero])
    exact primaryProjection_of_mem_ne hsq hh hk.1 hk.2.1 hw

private lemma ggJSo3_range_one_sub_selfDual {K : Type} [Field K] {ι : Type}
    [Fintype ι] [DecidableEq ι] {Φ : QuadraticForm K (ι → K)}
    {p : ℕ} {x : (ι → K) ≃ₗ[K] (ι → K)} (hx : OddOrderIsometry Φ p x)
    {h : K[X]} (hh : h ∈ primaryFactors x.toLinearMap) (hself : h = reciprocalPolynomial h)
    {ε : Matrix ι ι K}
    (ht : Matrix.toLinAlgEquiv' ε = primaryProjection x.toLinearMap h) :
    LinearMap.range (Matrix.toLin' (1 - ε)) = othersSpace x.toLinearMap h := by
  have hsq := hx.squarefree_minpoly
  have hp : IsIdempotentElem (Matrix.toLin' ε) := by
    rw [← ggOmegaBlk_toLinAlgEquiv'_eq_toLin', ht]
    exact primaryProjection_mul_self hsq hh
  have hker : LinearMap.ker (Matrix.toLin' ε) = othersSpace x.toLinearMap h := by
    rw [← ggOmegaBlk_toLinAlgEquiv'_eq_toLin', ht]
    exact ggJSo3_ker_selfDual hsq hh hself
  rw [ggOmegaBlk_toLin_one_sub, ← LinearMap.IsIdempotentElem.ker_eq_range_one_sub hp, hker]

theorem map_glBlockCentralizer_eq_supportedBlock_selfDual
    {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Fintype K] [CharP K 2]
    (Φ : QuadraticForm K (ι → K)) (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (h8 : 8 ≤ Fintype.card ι) (b : GL ι K)
    {ε e : Matrix ι ι K} {h : K[X]}
    (hx : OddOrderIsometry Φ (orderOf b) (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K b))
    (hp2 : Odd (orderOf b))
    (hh : h ∈ primaryFactors (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K b).toLinearMap)
    (hae : Matrix.toLinAlgEquiv' e = primaryProjection
      (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K b).toLinearMap h)
    (hself : h = reciprocalPolynomial h) (hne1 : h ≠ X - 1)
    (hεe : ε = e) :
    (glBlockCentralizer (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε).map
      ((CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).toMonoidHom.comp
        (StatedOmega ⇑Φ).subtype) =
      supportedBlock Φ (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K b) h := by
  have htoLinε : Matrix.toLinAlgEquiv' ε = primaryProjection
      (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K b).toLinearMap h := by
    rw [hεe]; exact hae
  have hsub : supportedBlock Φ (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K b) h
      ≤ orthDerived Φ :=
    ggOmegaBlk_supportedBlock_le_orthDerived Φ hΦ h8 hx hp2 hh hne1
  ext g
  constructor
  · intro hg
    rw [Subgroup.mem_map] at hg
    obtain ⟨u, hu, hgu⟩ := hg
    have hu' : ((u : ↥(StatedOmega ⇑Φ)) : GL ι K) ∈
        Subgroup.centralizer ({b} : Set (GL ι K)) ⊓ glFixing (1 - ε) :=
      Subgroup.mem_comap.mp hu
    have hcent : ((u : ↥(StatedOmega ⇑Φ)) : GL ι K) ∈
        Subgroup.centralizer ({b} : Set (GL ι K)) := (Subgroup.mem_inf.mp hu').1
    have hfix : ((u : ↥(StatedOmega ⇑Φ)) : GL ι K) ∈ glFixing (1 - ε) :=
      (Subgroup.mem_inf.mp hu').2
    have hbb : ((u : ↥(StatedOmega ⇑Φ)) : GL ι K) * b =
        b * ((u : ↥(StatedOmega ⇑Φ)) : GL ι K) :=
      (Subgroup.mem_centralizer_singleton_iff).mp hcent
    rw [mem_supportedBlock]
    constructor
    · rw [mem_isometryCentralizer]
      constructor
      · intro v
        have hom : toLinEquiv ι K ((u : ↥(StatedOmega ⇑Φ)) : GL ι K) ∈ orthDerived Φ := by
          have h : ((u : ↥(StatedOmega ⇑Φ)) : GL ι K) ∈
              (orthDerived Φ).comap (toLinEquiv ι K).toMonoidHom := by
            rw [← statedOmega_eq_comap (Q := Φ) (Q₀ := ⇑Φ) rfl]
            exact u.2
          exact Subgroup.mem_comap.mp h
        have hO := CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup
          (Q := Φ) hom
        have hv := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hO v
        rw [← hgu]
        exact hv
      · intro v
        have hcomm2 : toLinEquiv ι K ((u : ↥(StatedOmega ⇑Φ)) : GL ι K) *
            toLinEquiv ι K b = toLinEquiv ι K b *
              toLinEquiv ι K ((u : ↥(StatedOmega ⇑Φ)) : GL ι K) := by
          rw [← map_mul, ← map_mul, hbb]
        have hv := congrArg (fun e : (ι → K) ≃ₗ[K] (ι → K) => e v) hcomm2
        rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply] at hv
        rw [← hgu]
        exact hv
    · intro v hv
      have hfix' : ∀ w, Matrix.toLin' (((u : ↥(StatedOmega ⇑Φ)) : GL ι K) : Matrix ι ι K)
          (Matrix.toLin' (1 - ε) w) = Matrix.toLin' (1 - ε) w :=
        (ggOmegaBlk_mem_glFixing_iff (((u : ↥(StatedOmega ⇑Φ)) : GL ι K)) (1 - ε)).mp hfix
      rw [← ggJSo3_range_one_sub_selfDual hx hh hself htoLinε] at hv
      obtain ⟨w, rfl⟩ := hv
      rw [← hgu]
      change Matrix.toLin' (((u : ↥(StatedOmega ⇑Φ)) : GL ι K) : Matrix ι ι K)
        (Matrix.toLin' (1 - ε) w) = Matrix.toLin' (1 - ε) w
      exact hfix' w
  · intro hg
    rw [Subgroup.mem_map]
    have hg' := hg
    rw [mem_supportedBlock] at hg'
    obtain ⟨hcent, hfixx⟩ := hg'
    have hcommv : ∀ v, g (toLinEquiv ι K b v) = toLinEquiv ι K b (g v) :=
      (mem_isometryCentralizer.mp hcent).2
    have hgΩ : g ∈ orthDerived Φ := hsub hg
    let w : GL ι K := (toLinEquiv ι K).symm g
    have hwg : toLinEquiv ι K w = g := MulEquiv.apply_symm_apply _ _
    have hwStated : w ∈ StatedOmega ⇑Φ := by
      rw [statedOmega_eq_comap (Q := Φ) (Q₀ := ⇑Φ) rfl, Subgroup.mem_comap]
      change toLinEquiv ι K w ∈ orthDerived Φ
      rwa [hwg]
    refine ⟨⟨w, hwStated⟩, ?_, ?_⟩
    · rw [glBlockCentralizer, Subgroup.mem_comap, Subgroup.mem_inf]
      constructor
      · rw [Subgroup.mem_centralizer_singleton_iff]
        apply (toLinEquiv ι K).injective
        rw [map_mul, map_mul]
        change toLinEquiv ι K w * toLinEquiv ι K b =
          toLinEquiv ι K b * toLinEquiv ι K w
        rw [hwg]
        apply LinearEquiv.ext
        intro v
        rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
        exact hcommv v
      · rw [ggOmegaBlk_mem_glFixing_iff]
        intro z
        have hzmem : Matrix.toLin' (1 - ε) z ∈ LinearMap.range (Matrix.toLin' (1 - ε)) :=
          ⟨z, rfl⟩
        have hgz : g (Matrix.toLin' (1 - ε) z) = Matrix.toLin' (1 - ε) z :=
          hfixx _ (by rwa [ggJSo3_range_one_sub_selfDual hx hh hself htoLinε] at hzmem)
        change Matrix.toLin' w (Matrix.toLin' (1 - ε) z) = Matrix.toLin' (1 - ε) z
        rw [← ggOmegaBlk_toLinEquiv_toLinearMap w, hwg]
        exact hgz
    · exact hwg

@[expose] noncomputable def glBlockCentralizerEquivSupportedBlock_selfDual
    {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Fintype K] [CharP K 2]
    (Φ : QuadraticForm K (ι → K)) (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (h8 : 8 ≤ Fintype.card ι) (b : GL ι K)
    {ε e : Matrix ι ι K} {h : K[X]}
    (hx : OddOrderIsometry Φ (orderOf b) (toLinEquiv ι K b))
    (hp2 : Odd (orderOf b))
    (hh : h ∈ primaryFactors (toLinEquiv ι K b).toLinearMap)
    (hae : Matrix.toLinAlgEquiv' e = primaryProjection (toLinEquiv ι K b).toLinearMap h)
    (hself : h = reciprocalPolynomial h) (hne1 : h ≠ X - 1)
    (hεe : ε = e) :
    ↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε) ≃*
      ↥(supportedBlock Φ (toLinEquiv ι K b) h) :=
  (Subgroup.equivMapOfInjective _
    ((toLinEquiv ι K).toMonoidHom.comp (StatedOmega ⇑Φ).subtype)
    (fun x y hxy => Subtype.ext ((toLinEquiv ι K).injective hxy))).trans
    (MulEquiv.subgroupCongr
      (map_glBlockCentralizer_eq_supportedBlock_selfDual Φ hΦ h8 b hx hp2 hh hae hself hne1 hεe))

@[simp] theorem glBlockCentralizerEquivSupportedBlock_selfDual_apply
    {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Fintype K] [CharP K 2]
    (Φ : QuadraticForm K (ι → K)) (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (h8 : 8 ≤ Fintype.card ι) (b : GL ι K)
    {ε e : Matrix ι ι K} {h : K[X]}
    (hx : OddOrderIsometry Φ (orderOf b) (toLinEquiv ι K b))
    (hp2 : Odd (orderOf b))
    (hh : h ∈ primaryFactors (toLinEquiv ι K b).toLinearMap)
    (hae : Matrix.toLinAlgEquiv' e = primaryProjection (toLinEquiv ι K b).toLinearMap h)
    (hself : h = reciprocalPolynomial h) (hne1 : h ≠ X - 1)
    (hεe : ε = e)
    (u : ↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε)) :
    ((glBlockCentralizerEquivSupportedBlock_selfDual Φ hΦ h8 b hx hp2 hh hae hself hne1 hεe u :
        ↥(supportedBlock Φ (toLinEquiv ι K b) h)) : (ι → K) ≃ₗ[K] (ι → K)) =
      toLinEquiv ι K (((u : ↥(glBlockCentralizer
        (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε)) : ↥(StatedOmega ⇑Φ)) : GL ι K) := by
  rfl

private lemma ggJSo3_blockDegree_eq_natDegree {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [CharP K 2] (b : GL ι K) (hodd : Odd (orderOf b))
    {a : K[X]} (ha : a ∈ primaryFactors (Matrix.toLin' (b : Matrix ι ι K)))
    {e : Matrix ι ι K}
    (hae : Matrix.toLinAlgEquiv' e = primaryProjection (Matrix.toLin' (b : Matrix ι ι K)) a) :
    blockDegree (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) e = a.natDegree := by
  classical
  haveI : Fact (Irreducible a) := ⟨irreducible_of_mem_primaryFactors ha⟩
  have hsq : Squarefree (minpoly K (Matrix.toLin' (b : Matrix ι ι K))) :=
    ggJSo3_squarefree_minpoly b hodd
  let bm : Matrix ι ι K := (b : Matrix ι ι K)
  let A : Subalgebra K (Matrix ι ι K) :=
    Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))
  let x : Module.End K (ι → K) := Matrix.toLin' (b : Matrix ι ι K)
  let P : Module.End K (ι → K) := primaryProjection x a
  let εa : K[X] := primaryIdempotent x a
  let T : K[X] →ₗ[K] Matrix ι ι K :=
    (LinearMap.mulRight K e).comp (aeval bm).toLinearMap
  have hT : ∀ f : K[X], T f = aeval bm f * e := by
    intro f
    change (LinearMap.mulRight K e) (aeval bm f) = aeval bm f * e
    exact LinearMap.mulRight_apply K e (aeval bm f)
  have hA : A = Algebra.adjoin K ({bm} : Set (Matrix ι ι K)) := by
    change Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K))) = _
    rw [Set.image_singleton]
  have hφβ : Matrix.toLinAlgEquiv' bm = x := ggOmegaBlk_toLinAlgEquiv'_eq_toLin' bm
  have hTφ : ∀ f : K[X], Matrix.toLinAlgEquiv' (T f) = aeval x f * P := by
    intro f
    rw [hT f, map_mul, hae, ← aeval_algHom_apply, hφβ]
  have hmul_iff : ∀ f : K[X], minpoly K x ∣ f * εa ↔ a ∣ f := by
    intro f
    constructor
    · intro h
      have h1 : a ∣ f * εa := dvd_trans (mem_primaryFactors.mp ha).2.2 h
      have h2 : a ∣ f * (1 - εa) := by
        convert dvd_mul_of_dvd_right (dvd_neg.mpr (primaryIdempotent_spec hsq ha).1) f
          using 1
        ring
      have h3 : a ∣ f * εa + f * (1 - εa) := dvd_add h1 h2
      convert h3 using 1
      ring
    · intro h
      obtain ⟨g, rfl⟩ := h
      rw [show a * g * εa = g * (a * εa) by ring]
      exact dvd_mul_of_dvd_right (primaryIdempotent_spec hsq ha).2.2 g
  have habs : ∀ f : K[X], T f = 0 ↔ a ∣ f := by
    intro f
    constructor
    · intro hf
      have hφ : aeval x f * P = 0 := by
        have h := hTφ f
        rw [hf, map_zero] at h
        exact h.symm
      have hmem : aeval x (f * εa) = 0 := by
        rw [aeval_mul]
        change aeval x f * primaryProjection x a = 0
        exact hφ
      exact (hmul_iff f).1 (minpoly.dvd K x hmem)
    · intro hf
      obtain ⟨g, rfl⟩ := hf
      have hdvd : minpoly K x ∣ (a * g) * εa := by
        rw [show (a * g) * εa = g * (a * εa) by ring]
        exact dvd_mul_of_dvd_right (primaryIdempotent_spec hsq ha).2.2 g
      have hzero : aeval x ((a * g) * εa) = 0 := by
        obtain ⟨q, hq⟩ := hdvd
        rw [hq, map_mul, minpoly.aeval, zero_mul]
      have hφ : aeval x (a * g) * P = 0 := by
        rw [show P = aeval x εa from rfl, ← aeval_mul]
        exact hzero
      apply Matrix.toLinAlgEquiv'.injective
      rw [hTφ (a * g), hφ, map_zero]
  have hker : LinearMap.ker T = (Ideal.span {a}).restrictScalars K := by
    ext f
    rw [LinearMap.mem_ker]
    change T f = 0 ↔ f ∈ Ideal.span {a}
    rw [Ideal.mem_span_singleton]
    exact habs f
  have hrange : LinearMap.range T =
      (Subalgebra.toSubmodule A).map (LinearMap.mulRight K e) := by
    ext y
    constructor
    · rintro ⟨f, rfl⟩
      refine ⟨aeval bm f, ?_, ?_⟩
      · rw [hA]
        change aeval bm f ∈ Algebra.adjoin K ({bm} : Set (Matrix ι ι K))
        rw [Algebra.adjoin_singleton_eq_range_aeval]
        exact ⟨f, rfl⟩
      · rw [hT f]
        exact LinearMap.mulRight_apply K e (aeval bm f)
    · rintro ⟨z, hz, rfl⟩
      rw [hA, Algebra.adjoin_singleton_eq_range_aeval] at hz
      obtain ⟨f, rfl⟩ := hz
      refine ⟨f, ?_⟩
      rw [hT f]
      exact (LinearMap.mulRight_apply K e (aeval bm f)).symm
  have hdeg : blockDegree A e = a.natDegree := by
    show Module.finrank K ((Subalgebra.toSubmodule A).map (LinearMap.mulRight K e)) =
      a.natDegree
    rw [← hrange, ← (LinearMap.quotKerEquivRange T).finrank_eq, hker]
    show Module.finrank K (AdjoinRoot a) = a.natDegree
    exact finrank_adjoinRoot
  exact hdeg

theorem blockGroup_iso_Omega_unitary {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι)
    (b : GL ι K) (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b))
    {ε : Matrix ι ι K}
    (hε : IsPrimAdjIdemIn (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε)
    (hp : IsPrimIdemIn (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε)
    (h1 : (b : Matrix ι ι K) * ε ≠ ε) :
    ∃ (d m : ℕ) (E : Type) (_ : Field E) (_ : Fintype E), 1 ≤ d ∧
      Fintype.card E = (Fintype.card K ^ d) ^ 2 ∧
      2 * d * m = Module.finrank K (LinearMap.range (Matrix.toLin' ε)) ∧
      blockDegree (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε = 2 * d ∧
      Nonempty (↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε) ≃*
        ↥(GUFull m (Fintype.card K ^ d) E)) := by
  classical
  let x : (ι → K) ≃ₗ[K] (ι → K) := CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K b
  have hx : OddOrderIsometry Φ (orderOf b) x := ggJSo3_oddOrderIsometry Φ hΦ b hb hodd
  have hxeq : x.toLinearMap = Matrix.toLin' (b : Matrix ι ι K) :=
    ggOmegaBlk_toLinEquiv_toLinearMap b
  obtain ⟨h, hh, hae⟩ := ggJSo3_exists_primaryProjection b hodd hp
  have hh' : h ∈ primaryFactors x.toLinearMap := by rw [hxeq]; exact hh
  have haeAlg : Matrix.toLinAlgEquiv' ε = primaryProjection x.toLinearMap h := by
    rw [ggOmegaBlk_toLinAlgEquiv'_eq_toLin', hae, hxeq]
  have hself : h = reciprocalPolynomial h :=
    (selfDual_primaryProjection_of_prim_adjoint Φ hΦ b hb hodd hε hh hae).symm
  have hne1 : h ≠ X - 1 := ggJSo3_ne_one b hodd hh hae h1
  have hrange : LinearMap.range (Matrix.toLin' ε) = primaryComponent x.toLinearMap h := by
    rw [← ggOmegaBlk_toLinAlgEquiv'_eq_toLin', haeAlg]
    apply le_antisymm
    · rintro y ⟨v, rfl⟩
      exact primaryProjection_mem hx.squarefree_minpoly hh' v
    · intro y hy
      exact ⟨y, primaryProjection_of_mem hx.squarefree_minpoly hh' hy⟩
  letI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh'⟩
  let E : Type := AdjoinRoot h
  haveI : Finite E := finite_adjoinRoot_of_fact h
  haveI : Fintype E := Fintype.ofFinite _
  obtain ⟨d, m, _ℓ, _f, _hU, hd1, _hq, hcardN, _hd, hdim, hdeg, _b, eG, _heG⟩ :=
    exists_selfDual_supportedBlock_coordinateEquiv hx hodd hh' hne1 hself
  have hcard : Fintype.card E = (Fintype.card K ^ d) ^ 2 := by
    rw [Fintype.card_eq_nat_card, hcardN, Nat.card_eq_fintype_card]
  have hae' : Matrix.toLinAlgEquiv' ε =
      primaryProjection (Matrix.toLin' (b : Matrix ι ι K)) h := by
    rw [ggOmegaBlk_toLinAlgEquiv'_eq_toLin', hae]
  have hblockDegree : blockDegree (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε =
      2 * d := by
    rw [ggJSo3_blockDegree_eq_natDegree b hodd hh hae']
    exact hdeg
  let eMap : ↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε) ≃*
      ↥(supportedBlock Φ x h) :=
    glBlockCentralizerEquivSupportedBlock_selfDual Φ hΦ h8 b hx hodd hh' haeAlg hself hne1 rfl
  have hdim' : 2 * d * m = Module.finrank K (LinearMap.range (Matrix.toLin' ε)) := by
    rw [hrange]
    exact hdim
  refine ⟨d, m, E, inferInstance, inferInstance, hd1, hcard, hdim', hblockDegree, ?_⟩
  let oldGU := GUFull m (Nat.card K ^ d) (AdjoinRoot h)
  let newGU := GUFull m (Fintype.card K ^ d) E
  have hgu : oldGU = newGU := by
    dsimp [oldGU, newGU, E]
    rw [Nat.card_eq_fintype_card]
  let eG' : ↥(supportedBlock Φ x h) ≃* ↥(newGU) :=
    eG.trans (MulEquiv.subgroupCongr hgu)
  exact ⟨eMap.trans (by simpa only [newGU] using eG')⟩

end CFSG.StandardType.ClassicalBlocks
