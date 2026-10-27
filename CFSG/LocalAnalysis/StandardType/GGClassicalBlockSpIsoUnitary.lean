module

public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockDefs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockDecomp
public import CFSG.RankThree.Classical.SteinbergBJSymplecticCrossPrimeBlocks
public import CFSG.ClassicalGroups.UnitaryFlag.GramForm
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeForm
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeModel
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeOrbits
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.StandardType.ClassicalBlocks

open CFSG CFSG.Open CFSG.StandardType CFSG.StandardType.ClassicalPosition Matrix
open Polynomial
open CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCUnitary
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KCUnitaryModel

private def ggJS2_IsPrimIdemInEnd {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (A : Subalgebra K (Module.End K V)) (e : Module.End K V) : Prop :=
  e ∈ A ∧ IsIdempotentElem e ∧ e ≠ 0 ∧
    ∀ e' ∈ A, IsIdempotentElem e' → e' * e = e' → e' = 0 ∨ e' = e

private lemma ggJS2_isPrimIdemIn_map_toLin {K : Type} [Field K] {ι : Type} [Fintype ι]
    [DecidableEq ι] (A : Subalgebra K (Matrix ι ι K)) (ε : Matrix ι ι K)
    (h : IsPrimIdemIn A ε) :
    ggJS2_IsPrimIdemInEnd (A.map (Matrix.toLinAlgEquiv' (R := K) (n := ι)))
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

private lemma ggJS2_eq_primaryProjection_of_adjoin {K V : Type} [Field K] [AddCommGroup V]
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

private abbrev ggJS2_M (n : ℕ) (K : Type) : Type :=
  Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K

private abbrev ggJS2_V (n : ℕ) (K : Type) : Type := Fin n ⊕ Fin n → K

private abbrev ggJS2_J (n : ℕ) (K : Type) [Field K] : ggJS2_M n K :=
  Matrix.fromBlocks 0 1 (-1) 0

private lemma ggJS2_J_mul_self (n : ℕ) (K : Type) [Field K] :
    ggJS2_J n K * ggJS2_J n K = -1 := by
  unfold ggJS2_J
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.zero_mul, zero_add, add_zero,
    Matrix.mul_neg, Matrix.neg_mul, neg_zero]
  rw [show (-1 : ggJS2_M n K) = Matrix.fromBlocks (-1) 0 0 (-1) by
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
    simp]

private lemma ggJS2_J_mul_neg_J (n : ℕ) (K : Type) [Field K] :
    ggJS2_J n K * (-(ggJS2_J n K)) = 1 := by
  rw [Matrix.mul_neg, ggJS2_J_mul_self, neg_neg]

private lemma ggJS2_neg_J_mul_J (n : ℕ) (K : Type) [Field K] :
    (-(ggJS2_J n K)) * ggJS2_J n K = 1 := by
  rw [Matrix.neg_mul, ggJS2_J_mul_self, neg_neg]

private lemma ggJS2_J_isUnit_det (n : ℕ) (K : Type) [Field K] :
    IsUnit (ggJS2_J n K).det :=
  (Matrix.isUnit_iff_isUnit_det (ggJS2_J n K)).mp
    (isUnit_iff_exists.mpr ⟨-(ggJS2_J n K), ggJS2_J_mul_neg_J n K, ggJS2_neg_J_mul_J n K⟩)

private lemma ggJS2_J_mul_inv (n : ℕ) (K : Type) [Field K] :
    ggJS2_J n K * (ggJS2_J n K)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (ggJS2_J_isUnit_det n K)

private lemma ggJS2_toBilin_adj (n : ℕ) (K : Type) [Field K]
    (a : ggJS2_M n K) (x y : ggJS2_V n K) :
    (Matrix.toBilin' (ggJS2_J n K)) (Matrix.toLin' a x) y =
      (Matrix.toBilin' (ggJS2_J n K)) x
        (Matrix.toLin' (formAdj (RingHom.id K) (ggJS2_J n K) a) y) := by
  rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply', Matrix.toLin'_apply, Matrix.toLin'_apply,
    formAdj]
  rw [show a.map (RingHom.id K) = a from by ext i j; rfl]
  have h1 : (ggJS2_J n K)⁻¹ *ᵥ (Matrix.transpose a *ᵥ ((ggJS2_J n K) *ᵥ y)) =
      ((ggJS2_J n K)⁻¹ * Matrix.transpose a * ggJS2_J n K) *ᵥ y := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  rw [← h1]
  have h2 : (ggJS2_J n K) *ᵥ ((ggJS2_J n K)⁻¹ *ᵥ
      (Matrix.transpose a *ᵥ ((ggJS2_J n K) *ᵥ y))) =
      Matrix.transpose a *ᵥ ((ggJS2_J n K) *ᵥ y) := by
    rw [Matrix.mulVec_mulVec, ggJS2_J_mul_inv, Matrix.one_mulVec]
  rw [h2]
  exact (dotProduct_comm _ _).trans
    (Matrix.dotProduct_transpose_mulVec a x ((ggJS2_J n K) *ᵥ y)).symm

private lemma ggJS2_formAdj_eq_adj {K : Type} [Field K] [CharP K 2] {n : ℕ}
    (b : GL (Fin n ⊕ Fin n) K) (hb : b ∈ StatedSp n K)
    (H : AltPrimaryData (spForm n K) (spLin n K ⟨b, hb⟩))
    (a : ggJS2_M n K) :
    Matrix.toLinAlgEquiv' (formAdj (RingHom.id K) (ggJS2_J n K) a) =
      H.adj (Matrix.toLinAlgEquiv' a) := by
  refine (H.adj_unique ?_).symm
  intro v w
  exact ggJS2_toBilin_adj n K a v w

private lemma ggJS2_toLinAlgEquiv'_eq_toLin' {K : Type} [Field K] {ι : Type}
    [Fintype ι] [DecidableEq ι] (M : Matrix ι ι K) :
    Matrix.toLinAlgEquiv' M = Matrix.toLin' M := by
  apply LinearMap.ext
  intro v
  rw [Matrix.toLinAlgEquiv'_apply, Matrix.toLin'_apply]

private lemma ggJS2_primaryProjection_mul_eq_zero {K V : Type} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {x : Module.End K V} (hsq : Squarefree (minpoly K x))
    {a b : K[X]} (ha : a ∈ primaryFactors x) (hb : b ∈ primaryFactors x) (hab : a ≠ b) :
    primaryProjection x a * primaryProjection x b = 0 := by
  apply LinearMap.ext
  intro v
  rw [Module.End.mul_apply, LinearMap.zero_apply]
  exact primaryProjection_of_mem_ne hsq ha hb (Ne.symm hab) (primaryProjection_mem hsq hb v)

private lemma ggJS2_primaryProjection_ne_zero {K V : Type} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {x : Module.End K V} (hsq : Squarefree (minpoly K x))
    {a : K[X]} (ha : a ∈ primaryFactors x) : primaryProjection x a ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (primaryComponent_ne_bot hsq ha)
  have h := primaryProjection_of_mem hsq ha hv
  simp [h0] at h
  exact hv0 h.symm

lemma ggJS2_reciprocal_of_selfDual {K : Type} [Field K] [Fintype K] [CharP K 2] {n : ℕ}
    (b : GL (Fin n ⊕ Fin n) K) (hb : b ∈ StatedSp n K) (hodd : Odd (orderOf b))
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    (hε : IsPrimAdjIdemIn (RingHom.id K)
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL (Fin n ⊕ Fin n) K)))) ε)
    {a : K[X]} (ha : a ∈ primaryFactors (spEnd ⟨b, hb⟩))
    (hae : (Matrix.toLin' ε : Module.End K (Fin n ⊕ Fin n → K)) =
      primaryProjection (spEnd ⟨b, hb⟩) a) :
    reciprocalPolynomial a = a := by
  have hpK : ((orderOf b : ℕ) : K) ≠ 0 := by
    intro h0
    exact hodd.not_two_dvd_nat ((CharP.cast_eq_zero_iff K 2 (orderOf b)).mp h0)
  have hpow : (⟨b, hb⟩ : StatedSp n K) ^ orderOf b = 1 :=
    Subtype.ext (pow_orderOf_eq_one b)
  have H : AltPrimaryData (spForm n K) (spLin n K ⟨b, hb⟩) := altPrimaryData_spLin hpK hpow
  have hsq : Squarefree (minpoly K (spEnd ⟨b, hb⟩)) := H.squarefree
  have hadj : H.adj (primaryProjection (spEnd ⟨b, hb⟩) a) =
      primaryProjection (spEnd ⟨b, hb⟩) a := by
    have h : Matrix.toLinAlgEquiv' (formAdj (RingHom.id K)
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) ε) =
        Matrix.toLinAlgEquiv' ε := by rw [hε.2.2.2.1]
    rw [ggJS2_formAdj_eq_adj b hb H ε] at h
    rw [ggJS2_toLinAlgEquiv'_eq_toLin', hae] at h
    exact h
  have hp : primaryProjection (spEnd ⟨b, hb⟩) (reciprocalPolynomial a) =
      primaryProjection (spEnd ⟨b, hb⟩) a := by
    rw [← AltPrimaryData.adj_primaryProjection H ha]
    exact hadj
  by_contra hne
  have hzero := ggJS2_primaryProjection_mul_eq_zero hsq ha (H.reciprocal_mem ha) (Ne.symm hne)
  rw [hp, primaryProjection_mul_self hsq ha] at hzero
  exact ggJS2_primaryProjection_ne_zero hsq ha hzero

lemma ggJS2_toLin'_eq_toLinAlgEquiv' {K : Type} [Field K] {ι : Type} [Fintype ι]
    [DecidableEq ι] (M : Matrix ι ι K) :
    (Matrix.toLin' M : (ι → K) →ₗ[K] ι → K) = Matrix.toLinAlgEquiv' M := by
  ext v
  rfl

lemma ggJS2_exists_primaryProjection {K : Type} [Field K] [Fintype K] [CharP K 2] {n : ℕ}
    (b : GL (Fin n ⊕ Fin n) K) (hb : b ∈ StatedSp n K) (hodd : Odd (orderOf b))
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    (hp : IsPrimIdemIn (Algebra.adjoin K (Units.val '' ({b} : Set (GL (Fin n ⊕ Fin n) K)))) ε) :
    ∃ a ∈ primaryFactors (spEnd ⟨b, hb⟩),
      (Matrix.toLin' ε : Module.End K (Fin n ⊕ Fin n → K)) =
        primaryProjection (spEnd ⟨b, hb⟩) a := by
  have hpK : ((orderOf b : ℕ) : K) ≠ 0 := by
    intro h0
    exact hodd.not_two_dvd_nat ((CharP.cast_eq_zero_iff K 2 (orderOf b)).mp h0)
  have hpow : (⟨b, hb⟩ : StatedSp n K) ^ orderOf b = 1 :=
    Subtype.ext (pow_orderOf_eq_one b)
  have H : AltPrimaryData (spForm n K) (spLin n K ⟨b, hb⟩) := altPrimaryData_spLin hpK hpow
  let A : Subalgebra K (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) :=
    Algebra.adjoin K (Units.val '' ({b} : Set (GL (Fin n ⊕ Fin n) K)))
  have hprimE := ggJS2_isPrimIdemIn_map_toLin A ε hp
  have hmapA : A.map (Matrix.toLinAlgEquiv' (R := K) (n := Fin n ⊕ Fin n)) =
      Algebra.adjoin K ({spEnd ⟨b, hb⟩} :
        Set (Module.End K (Fin n ⊕ Fin n → K))) := by
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
      exact ⟨(b : Matrix _ _ K), ⟨b, rfl, rfl⟩, rfl⟩
  rw [hmapA] at hprimE
  obtain ⟨a, ha, heq⟩ :=
    ggJS2_eq_primaryProjection_of_adjoin H.squarefree hprimE.1 hprimE.2.1 hprimE.2.2.1
      hprimE.2.2.2
  refine ⟨a, ha, ?_⟩
  rw [ggJS2_toLin'_eq_toLinAlgEquiv']
  exact heq

lemma ggJS2_GUFull_eq_primeFormUnitary {E : Type} [Field E] {m p f Q : ℕ}
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

private lemma ggJS2_mem_glFixing_iff {K : Type} [Field K] {ι : Type} [Fintype ι]
    [DecidableEq ι] (u : GL ι K) (P : Matrix ι ι K) :
    u ∈ glFixing P ↔
      ∀ v, Matrix.toLin' (u : Matrix ι ι K) (Matrix.toLin' P v) = Matrix.toLin' P v := by
  constructor
  · intro h v
    rw [← Matrix.toLin'_mul_apply (u : Matrix ι ι K) P v, h]
  · intro h
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    rw [Matrix.toLin'_mul_apply, h v]

private lemma ggJS2_one_sub_primaryProjection_eq_sum
    {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {x : Module.End K V} (hsq : Squarefree (minpoly K x)) {a : K[X]}
    (ha : a ∈ primaryFactors x) [DecidableEq K[X]] :
    (1 : Module.End K V) - primaryProjection x a =
      ∑ c ∈ (primaryFactors x).erase a, primaryProjection x c := by
  classical
  have h := Finset.sum_erase_add (primaryFactors x) (primaryProjection x) ha
  have hs := sum_primaryProjection hsq
  rw [← h] at hs
  rw [← hs]
  abel

lemma ggJS2_glBlockCentralizer_eq_spSupported
    {K : Type} [Field K] [CharP K 2] {n : ℕ}
    (b : GL (Fin n ⊕ Fin n) K) (hb : b ∈ StatedSp n K) (hodd : Odd (orderOf b))
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    {a : K[X]} (ha : a ∈ primaryFactors (spEnd ⟨b, hb⟩))
    (hae : Matrix.toLinAlgEquiv' ε = primaryProjection (spEnd ⟨b, hb⟩) a) :
    glBlockCentralizer (StatedSp n K).subtype ({b} : Set (GL (Fin n ⊕ Fin n) K)) ε =
      spSupported ⟨b, hb⟩ {a} := by
  classical
  let β : StatedSp n K := ⟨b, hb⟩
  have hpK : ((orderOf b : ℕ) : K) ≠ 0 := by
    intro h0
    exact hodd.not_two_dvd_nat ((CharP.cast_eq_zero_iff K 2 (orderOf b)).mp h0)
  have hpow : β ^ orderOf b = 1 := Subtype.ext (pow_orderOf_eq_one b)
  have H : AltPrimaryData (spForm n K) (spLin n K β) := altPrimaryData_spLin hpK hpow
  have hsq : Squarefree (minpoly K (spEnd β)) := H.squarefree
  let F : Finset K[X] := primaryFactors (spEnd β)
  let S : Finset K[X] := F.erase a
  have hsum : (1 : Module.End K (Fin n ⊕ Fin n → K)) - primaryProjection (spEnd β) a =
      ∑ c ∈ S, primaryProjection (spEnd β) c :=
    ggJS2_one_sub_primaryProjection_eq_sum hsq ha
  have hsubε : Matrix.toLin' (1 - ε) = 1 - Matrix.toLin' ε := by
    apply LinearMap.ext
    intro v
    rw [Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.one_mulVec, LinearMap.sub_apply,
      Module.End.one_apply, Matrix.toLin'_apply]
  have hQ : Matrix.toLin' (1 - ε) = ∑ c ∈ S, primaryProjection (spEnd β) c := by
    rw [hsubε, ← ggJS2_toLinAlgEquiv'_eq_toLin' ε, hae]
    exact hsum
  ext g
  have hspEnd : spEnd g = Matrix.toLin'
      ((g : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) := by
    apply LinearMap.ext
    intro v
    rw [Matrix.toLin'_apply]
    rfl
  have hcenter : (g : GL (Fin n ⊕ Fin n) K) ∈
      Subgroup.centralizer ({(b : GL (Fin n ⊕ Fin n) K)} : Set (GL (Fin n ⊕ Fin n) K)) ↔
      g * β = β * g := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg
      (fun z : StatedSp n K => (z : GL (Fin n ⊕ Fin n) K)) h⟩
  have hfix : (g : GL (Fin n ⊕ Fin n) K) ∈ glFixing (1 - ε) ↔
      ∀ v, spEnd g (Matrix.toLin' (1 - ε) v) = Matrix.toLin' (1 - ε) v := by
    rw [ggJS2_mem_glFixing_iff]
    constructor
    · intro h v
      rw [hspEnd]
      exact h v
    · intro h v
      rw [← hspEnd]
      exact h v
  rw [mem_spSupported, glBlockCentralizer, Subgroup.mem_comap, Subgroup.mem_inf]
  change ((g : GL (Fin n ⊕ Fin n) K) ∈
      Subgroup.centralizer ({(b : GL (Fin n ⊕ Fin n) K)} : Set (GL (Fin n ⊕ Fin n) K)) ∧
      (g : GL (Fin n ⊕ Fin n) K) ∈ glFixing (1 - ε)) ↔
    g * β = β * g ∧ ∀ k ∈ primaryFactors (spEnd β), k ∉ ({a} : Set K[X]) →
      ∀ v ∈ primaryComponent (spEnd β) k, spEnd g v = v
  rw [hcenter, hfix]
  constructor
  · rintro ⟨hc, hfixv⟩
    refine ⟨hc, fun k hk hkS v hv => ?_⟩
    have hkmemS : k ∈ S := by
      have hka : k ≠ a := fun h => hkS (by simp [h])
      exact Finset.mem_erase.mpr ⟨hka, hk⟩
    have hsumk : (∑ c ∈ S, primaryProjection (spEnd β) c v) = v := by
      rw [Finset.sum_eq_single k]
      · exact primaryProjection_of_mem hsq hk hv
      · intro c hcS hck
        exact primaryProjection_of_mem_ne hsq
          (Finset.mem_of_mem_erase hcS) hk (Ne.symm hck) hv
      · intro hknot
        exact absurd hkmemS hknot
    calc spEnd g v = spEnd g (Matrix.toLin' (1 - ε) v) := by
          rw [hQ, LinearMap.sum_apply, hsumk]
      _ = Matrix.toLin' (1 - ε) v := hfixv v
      _ = v := by rw [hQ, LinearMap.sum_apply, hsumk]
  · rintro ⟨hc, hfixK⟩
    refine ⟨hc, fun v => ?_⟩
    rw [hQ, LinearMap.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun c hcS => ?_
    have hcF : c ∈ primaryFactors (spEnd β) := Finset.mem_of_mem_erase hcS
    have hca : c ≠ a := (Finset.mem_erase.mp hcS).1
    exact hfixK c hcF (by simp [hca]) _ (primaryProjection_mem hsq hcF v)

private lemma ggJS2_squarefree_minpoly_spEnd {K : Type} [Field K] [CharP K 2] {n : ℕ}
    (b : StatedSp n K) (hodd : Odd (orderOf b)) :
    Squarefree (minpoly K (spEnd b)) := by
  classical
  have hb1 : b ^ orderOf b = 1 := pow_orderOf_eq_one b
  have hoK : ((orderOf b : ℕ) : K) ≠ 0 := by
    intro h
    exact hodd.not_two_dvd_nat ((CharP.cast_eq_zero_iff K 2 (orderOf b)).mp h)
  have hsqp : Squarefree (Polynomial.X ^ orderOf b - 1 : Polynomial K) := by
    have h := Polynomial.separable_X_pow_sub_C (1 : K) hoK one_ne_zero
    simpa using h.squarefree
  refine squarefree_minpoly_of_aeval_eq_zero hsqp ?_
  rw [map_sub, map_pow, aeval_X, map_one, sub_eq_zero]
  change (((spLin n K b : LinearMap.GeneralLinearGroup K (Fin n ⊕ Fin n → K))) :
      Module.End K (Fin n ⊕ Fin n → K)) ^ orderOf b = 1
  rw [← Units.val_pow_eq_pow_val, ← map_pow, hb1, map_one, Units.val_one]

private lemma ggJS2_blockDegree_eq_natDegree {K : Type} [Field K] [CharP K 2] {n : ℕ}
    (β : StatedSp n K) (hodd : Odd (orderOf β))
    {a : K[X]} (ha : a ∈ primaryFactors (spEnd β))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    (hae : Matrix.toLinAlgEquiv' e = primaryProjection (spEnd β) a) :
    blockDegree (Algebra.adjoin K (Units.val '' ({(β : GL (Fin n ⊕ Fin n) K)} :
      Set (GL (Fin n ⊕ Fin n) K)))) e = a.natDegree := by
  classical
  haveI : Fact (Irreducible a) := ⟨irreducible_of_mem_primaryFactors ha⟩
  have hsq : Squarefree (minpoly K (spEnd β)) := ggJS2_squarefree_minpoly_spEnd β hodd
  let bm : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K := (β : GL (Fin n ⊕ Fin n) K)
  let A : Subalgebra K (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) :=
    Algebra.adjoin K (Units.val '' ({(β : GL (Fin n ⊕ Fin n) K)} : Set (GL (Fin n ⊕ Fin n) K)))
  let x : Module.End K (Fin n ⊕ Fin n → K) := spEnd β
  let P : Module.End K (Fin n ⊕ Fin n → K) := primaryProjection x a
  let εa : K[X] := primaryIdempotent x a
  let T : K[X] →ₗ[K] Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
    (LinearMap.mulRight K e).comp (aeval bm).toLinearMap
  have hT : ∀ f : K[X], T f = aeval bm f * e := by
    intro f
    change (LinearMap.mulRight K e) (aeval bm f) = aeval bm f * e
    exact LinearMap.mulRight_apply K e (aeval bm f)
  have hA : A = Algebra.adjoin K ({bm} : Set (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)) := by
    change Algebra.adjoin K (Units.val '' ({(β : GL (Fin n ⊕ Fin n) K)} :
      Set (GL (Fin n ⊕ Fin n) K))) = _
    rw [Set.image_singleton]
  have hφβ : Matrix.toLinAlgEquiv' bm = x := by
    rw [ggJS2_toLinAlgEquiv'_eq_toLin']
    apply LinearMap.ext
    intro v
    rw [Matrix.toLin'_apply]
    exact (spEnd_apply β v).symm
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
        change aeval bm f ∈ Algebra.adjoin K ({bm} : Set (Matrix (Fin n ⊕ Fin n)
          (Fin n ⊕ Fin n) K))
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

lemma ggJS2_sesqUnitaryGroup_mulEquiv_primeForm
    {E W : Type} [Field E] [AddCommGroup W] [Module E W] {m : ℕ}
    {p f : ℕ} (h : UnitaryFieldData p f E) {B : W →ₛₗ[h.bar] W →ₗ[E] E}
    (e : Module.Basis (Fin m) E W) {G : Matrix (Fin m) (Fin m) E}
    (he : ∀ i j, B (e i) (e j) = G i j) :
    Nonempty (sesqUnitaryGroup B ≃* primeFormUnitary h G) := by
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
  exact ⟨((Ψ.subgroupMap (primeFormUnitary h G)).trans (MulEquiv.subgroupCongr hEq)).symm⟩

theorem blockGroup_iso_Sp_unitary {K : Type} [Field K] [Fintype K] [CharP K 2] {n : ℕ}
    (b : GL (Fin n ⊕ Fin n) K) (hb : b ∈ StatedSp n K) (hodd : Odd (orderOf b))
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    (hε : IsPrimAdjIdemIn (RingHom.id K)
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL (Fin n ⊕ Fin n) K)))) ε)
    (hp : IsPrimIdemIn (Algebra.adjoin K (Units.val '' ({b} : Set (GL (Fin n ⊕ Fin n) K)))) ε)
    (h1 : (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε ≠ ε) :
    ∃ (d m : ℕ) (E : Type) (_ : Field E) (_ : Fintype E), 1 ≤ d ∧
      Fintype.card E = (Fintype.card K ^ d) ^ 2 ∧
      2 * d * m = Module.finrank K (LinearMap.range (Matrix.toLin' ε)) ∧
      blockDegree (Algebra.adjoin K (Units.val '' ({b} : Set (GL (Fin n ⊕ Fin n) K)))) ε =
        2 * d ∧
      Nonempty (↥(glBlockCentralizer (StatedSp n K).subtype {b} ε) ≃*
        ↥(GUFull m (Fintype.card K ^ d) E)) := by
  classical
  let β : StatedSp n K := ⟨b, hb⟩
  have hoddβ : Odd (orderOf β) := by
    change Odd (orderOf (⟨b, hb⟩ : StatedSp n K))
    rw [Subgroup.orderOf_mk b hb]
    exact hodd
  have H : AltPrimaryData (spForm n K) (spLin n K β) := by
    refine altPrimaryData_spLin ?_ (Subtype.ext (pow_orderOf_eq_one b))
    intro h0
    exact hodd.not_two_dvd_nat ((CharP.cast_eq_zero_iff K 2 (orderOf b)).mp h0)
  have hsq : Squarefree (minpoly K (spEnd β)) := H.squarefree
  obtain ⟨a, ha, hae'⟩ := ggJS2_exists_primaryProjection b hb hodd hp
  have hrec : reciprocalPolynomial a = a := ggJS2_reciprocal_of_selfDual b hb hodd hε ha hae'
  have haeAlg : Matrix.toLinAlgEquiv' ε = primaryProjection (spEnd β) a := by
    rw [ggJS2_toLinAlgEquiv'_eq_toLin']
    exact hae'
  have hane1 : a ≠ X - 1 := by
    intro ha1
    apply h1
    have hxpa : (spEnd β : Module.End K (Fin n ⊕ Fin n → K)) *
        primaryProjection (spEnd β) a = primaryProjection (spEnd β) a := by
      apply LinearMap.ext
      intro v
      have hX1 : (X - 1 : K[X]) ∈ primaryFactors (spEnd β) := ha1 ▸ ha
      have hv := primaryProjection_mem hsq hX1 v
      rw [mem_primaryComponent_X_sub_one] at hv
      rw [ha1, Module.End.mul_apply]
      exact hv
    have hbε : (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε = ε := by
      apply (Matrix.toLinAlgEquiv' (R := K) (n := Fin n ⊕ Fin n)).injective
      rw [map_mul, haeAlg]
      exact hxpa
    exact hbε
  have hsq2 : AdjoinRoot.root a ^ 2 ≠ 1 := by
    intro h2
    have hroot : AdjoinRoot.root a ^ orderOf β = 1 := by
      have hdvd : a ∣ (Polynomial.X ^ orderOf β - 1 : Polynomial K) := by
        refine (mem_primaryFactors.mp ha).2.2.trans ?_
        refine minpoly.dvd K (spEnd β) ?_
        rw [map_sub, map_pow, aeval_X, map_one, sub_eq_zero]
        change ((spLin n K β : LinearMap.GeneralLinearGroup K (Fin n ⊕ Fin n → K)) :
          Module.End K (Fin n ⊕ Fin n → K)) ^ orderOf β = 1
        rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_orderOf_eq_one β, map_one, Units.val_one]
      have h := AdjoinRoot.mk_eq_zero.mpr hdvd
      rw [map_sub, map_pow, AdjoinRoot.mk_X, map_one, sub_eq_zero] at h
      exact h
    have hdvd2 : orderOf (AdjoinRoot.root a) ∣ 2 := orderOf_dvd_of_pow_eq_one h2
    have hdvdN : orderOf (AdjoinRoot.root a) ∣ orderOf β := orderOf_dvd_of_pow_eq_one hroot
    have hcop : Nat.Coprime 2 (orderOf β) := Nat.coprime_two_left.mpr hoddβ
    have hdvd1 : orderOf (AdjoinRoot.root a) ∣ 1 := by
      have h := Nat.dvd_gcd hdvd2 hdvdN
      rwa [hcop.gcd_eq_one] at h
    have hroot1 : AdjoinRoot.root a = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd1)
    have hdvdX : a ∣ (Polynomial.X - 1 : Polynomial K) := by
      apply AdjoinRoot.mk_eq_zero.mp
      rw [map_sub, AdjoinRoot.mk_X, map_one, hroot1, sub_self]
    exact hane1 (eq_of_monic_of_associated (monic_of_mem_primaryFactors ha)
      CFSG.RankThree.Classical.monic_X_sub_one
      ((irreducible_of_mem_primaryFactors ha).associated_of_dvd
        CFSG.RankThree.Classical.irreducible_X_sub_one hdvdX))
  haveI : Fact (Irreducible a) := ⟨irreducible_of_mem_primaryFactors ha⟩
  have h0 : a.coeff 0 ≠ 0 := H.coeff_zero_ne ha
  obtain ⟨d, hd, hσd⟩ := exists_rootInv_eq_pow h0 hrec hsq2
  let E : Type := AdjoinRoot a
  let m : ℕ := Module.finrank E (primaryComponent (spEnd β) a)
  haveI : Finite E := Module.finite_of_finite K
  haveI : Fintype E := Fintype.ofFinite E
  have han : a.natDegree = 2 * d := by rw [← finrank_adjoinRoot, hd]
  have hd1 : 1 ≤ d := by
    have hpos : 0 < a.natDegree := Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors ha)
    omega
  have hcardE : Fintype.card E = (Fintype.card K ^ d) ^ 2 := by
    rw [Fintype.card_eq_nat_card, Module.natCard_eq_pow_finrank (K := K), hd,
      Nat.card_eq_fintype_card, ← pow_mul]
    congr 1
    ring
  have hdim : 2 * d * m = Module.finrank K (LinearMap.range (Matrix.toLin' ε)) := by
    have hrange : LinearMap.range (Matrix.toLin' ε) = primaryComponent (spEnd β) a := by
      rw [hae']
      apply le_antisymm
      · rintro y ⟨v, rfl⟩
        exact primaryProjection_mem hsq ha v
      · intro y hy
        exact ⟨y, primaryProjection_of_mem hsq ha hy⟩
    rw [hrange, finrank_primaryComponent (spEnd β) a, han]
  have hblockDegree : blockDegree (Algebra.adjoin K
      (Units.val '' ({b} : Set (GL (Fin n ⊕ Fin n) K)))) ε = 2 * d := by
    rw [ggJS2_blockDegree_eq_natDegree β hoddβ ha haeAlg]
    exact han
  have hsub : glBlockCentralizer (StatedSp n K).subtype ({b} : Set (GL (Fin n ⊕ Fin n) K)) ε =
      spSupported β {a} := ggJS2_glBlockCentralizer_eq_spSupported b hb hodd ha haeAlg
  obtain ⟨p, hchar, f, hpprime, hKcard⟩ := FiniteField.card' (K := K)
  have hfpos : 0 < (f : ℕ) := f.pos
  have hE : UnitaryFieldData p ((f : ℕ) * d) E := by
    refine ⟨hpprime, Nat.mul_pos hfpos hd1, ?_⟩
    show Nat.card E = p ^ (2 * ((f : ℕ) * d))
    rw [Module.natCard_eq_pow_finrank (K := K), hd, Nat.card_eq_fintype_card, hKcard,
      ← pow_mul]
    congr 1
    ring
  have hbar : ∀ z : E, hE.bar z = rootInv h0 hrec z := by
    intro z
    rw [UnitaryFieldData.bar_apply, hσd z, Nat.card_eq_fintype_card, hKcard, ← pow_mul]
  obtain ⟨η, hη0, hη⟩ := exists_ne_zero_neg (rootInv h0 hrec) (rootInv_rootInv h0 hrec)
    (rootInv_ne_one h0 hrec hsq2)
  have hηbar : hE.bar η = -η := by rw [hbar, hη]
  have hsymm := H.altHermForm_isSymm ha hrec hE.bar hbar hηbar
  have hsep := H.altHermForm_separatingLeft ha hrec hE.bar hbar hη0
  obtain ⟨e, he⟩ := hE.exists_orthonormal_basis hsymm hsep
  have heG : ∀ i j : Fin m, H.altHermForm ha hrec hE.bar hbar η (e i) (e j) =
      (idGram E m) i j := by
    intro i j
    rw [he i j, idGram, Units.val_one, Matrix.one_apply]
  obtain ⟨eU⟩ := ggJS2_sesqUnitaryGroup_mulEquiv_primeForm hE e heG
  have hbarQ : ∀ z : E, hE.bar z = z ^ (Fintype.card K ^ d) := by
    intro z
    rw [hbar z, hσd z, Nat.card_eq_fintype_card]
  have hL := supportedUnitary_le_sesq β {a}
  let eG : ↥(glBlockCentralizer (StatedSp n K).subtype {b} ε) ≃*
      ↥(GUFull m (Fintype.card K ^ d) E) :=
    (MulEquiv.subgroupCongr hsub).trans
      ((comapSpLinEquiv (supportedUnitary (spForm n K) (spLin n K β) {a}) hL).trans
        ((H.selfDualEquiv ha hrec hE.bar hbar hη0).trans
          (eU.trans (MulEquiv.subgroupCongr
            (ggJS2_GUFull_eq_primeFormUnitary hE hbarQ).symm))))
  exact ⟨d, m, E, inferInstance, inferInstance, hd1, hcardE, hdim, hblockDegree, ⟨eG⟩⟩

end CFSG.StandardType.ClassicalBlocks
