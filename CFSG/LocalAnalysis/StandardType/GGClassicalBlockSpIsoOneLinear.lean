module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockDecomp
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBStated
public import CFSG.RankThree.Classical.SteinbergBJSymplecticPrimaryCentralizer
public import CFSG.RankThree.Classical.SteinbergBJSymplecticCrossPrimeBlocks
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.StandardType.ClassicalBlocks

open CFSG CFSG.Open CFSG.StandardType CFSG.StandardType.ClassicalPosition Matrix
open CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
open Polynomial
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)

abbrev ggJS1_M (n : ℕ) (K : Type) : Type :=
  Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K

abbrev ggJS1_V (n : ℕ) (K : Type) : Type :=
  Fin n ⊕ Fin n → K

abbrev ggJS1_J (n : ℕ) (K : Type) [Field K] : ggJS1_M n K :=
  Matrix.fromBlocks 0 1 (-1) 0

abbrev ggJS1_B (n : ℕ) (K : Type) [Field K] :
    LinearMap.BilinForm K (ggJS1_V n K) :=
  Matrix.toBilin' (ggJS1_J n K)

abbrev ggJS1_matrixLinIso {n : ℕ} {K : Type} [Field K] :
    GL (Fin n ⊕ Fin n) K ≃* (ggJS1_V n K ≃ₗ[K] ggJS1_V n K) :=
  CFSG.ComponentClassification.CatalogueBSymplecticB.matrixLinIso

abbrev ggJS1_Iso {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) : Subgroup (V ≃ₗ[K] V) :=
  TauCeti.BilinForm.isometryGroup B

lemma ggJS1_B_isAlt (n : ℕ) (K : Type) [Field K] : (ggJS1_B n K).IsAlt :=
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.pairedSympForm_isAlt

lemma ggJS1_B_nondegenerate (n : ℕ) (K : Type) [Field K] :
    (ggJS1_B n K).Nondegenerate :=
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.pairedSympForm_nondegenerate

private lemma ggJS1_J_mul_self (n : ℕ) (K : Type) [Field K] :
    ggJS1_J n K * ggJS1_J n K = -1 := by
  unfold ggJS1_J
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.zero_mul, zero_add, add_zero,
    Matrix.mul_neg, Matrix.neg_mul, neg_zero]
  rw [show (-1 : ggJS1_M n K) = Matrix.fromBlocks (-1) 0 0 (-1) by
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
    simp]

private lemma ggJS1_J_mul_neg_J (n : ℕ) (K : Type) [Field K] :
    ggJS1_J n K * (-(ggJS1_J n K)) = 1 := by
  rw [Matrix.mul_neg, ggJS1_J_mul_self, neg_neg]

private lemma ggJS1_neg_J_mul_J (n : ℕ) (K : Type) [Field K] :
    (-(ggJS1_J n K)) * ggJS1_J n K = 1 := by
  rw [Matrix.neg_mul, ggJS1_J_mul_self, neg_neg]

private lemma ggJS1_J_isUnit_det (n : ℕ) (K : Type) [Field K] :
    IsUnit (ggJS1_J n K).det :=
  (Matrix.isUnit_iff_isUnit_det (ggJS1_J n K)).mp
    (isUnit_iff_exists.mpr ⟨-(ggJS1_J n K), ggJS1_J_mul_neg_J n K, ggJS1_neg_J_mul_J n K⟩)

private lemma ggJS1_J_mul_inv (n : ℕ) (K : Type) [Field K] :
    ggJS1_J n K * (ggJS1_J n K)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (ggJS1_J_isUnit_det n K)

private lemma ggJS1_eps_mul_one_sub {ι K : Type} [Fintype ι] [DecidableEq ι] [Ring K]
    {ε : Matrix ι ι K} (h : IsIdempotentElem ε) : ε * (1 - ε) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, h.eq, sub_self]

private lemma ggJS1_toBilin_adj (n : ℕ) (K : Type) [Field K]
    (a : ggJS1_M n K) (x y : ggJS1_V n K) :
    (Matrix.toBilin' (ggJS1_J n K)) (Matrix.toLin' a x) y =
      (Matrix.toBilin' (ggJS1_J n K)) x
        (Matrix.toLin' (formAdj (RingHom.id K) (ggJS1_J n K) a) y) := by
  rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply', Matrix.toLin'_apply, Matrix.toLin'_apply,
    formAdj]
  rw [show a.map (RingHom.id K) = a from by ext i j; rfl]
  have h1 : (ggJS1_J n K)⁻¹ *ᵥ (Matrix.transpose a *ᵥ ((ggJS1_J n K) *ᵥ y)) =
      ((ggJS1_J n K)⁻¹ * Matrix.transpose a * ggJS1_J n K) *ᵥ y := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  rw [← h1]
  have h2 : (ggJS1_J n K) *ᵥ ((ggJS1_J n K)⁻¹ *ᵥ
      (Matrix.transpose a *ᵥ ((ggJS1_J n K) *ᵥ y))) =
      Matrix.transpose a *ᵥ ((ggJS1_J n K) *ᵥ y) := by
    rw [Matrix.mulVec_mulVec, ggJS1_J_mul_inv, Matrix.one_mulVec]
  rw [h2]
  exact (dotProduct_comm _ _).trans
    (Matrix.dotProduct_transpose_mulVec a x ((ggJS1_J n K) *ᵥ y)).symm

lemma ggJS1_B_range_ker (n : ℕ) (K : Type) [Field K]
    (ε : ggJS1_M n K) (hεid : IsIdempotentElem ε)
    (hεadj : formAdj (RingHom.id K) (ggJS1_J n K) ε = ε) :
    ∀ x ∈ (Matrix.toLin' ε).range, ∀ y ∈ (Matrix.toLin' ε).ker,
      (Matrix.toBilin' (ggJS1_J n K)) x y = 0 := by
  intro x hx y hy
  obtain ⟨x', rfl⟩ := hx
  rw [ggJS1_toBilin_adj n K ε x' y, hεadj, LinearMap.mem_ker.mp hy]
  simp

private lemma ggJS1_inv_comm {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (m : GL ι K) {ε : Matrix ι ι K}
    (hm : (m : Matrix ι ι K) * ε = ε * (m : Matrix ι ι K)) :
    (((m⁻¹ : GL ι K)) : Matrix ι ι K) * ε = ε * (((m⁻¹ : GL ι K)) : Matrix ι ι K) := by
  have hmm : (m : Matrix ι ι K) * (((m⁻¹ : GL ι K)) : Matrix ι ι K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hm'm : (((m⁻¹ : GL ι K)) : Matrix ι ι K) * (m : Matrix ι ι K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  calc (((m⁻¹ : GL ι K)) : Matrix ι ι K) * ε
      = (((m⁻¹ : GL ι K)) : Matrix ι ι K) * ε *
          ((m : Matrix ι ι K) * (((m⁻¹ : GL ι K)) : Matrix ι ι K)) := by
        rw [hmm, Matrix.mul_one]
    _ = (((m⁻¹ : GL ι K)) : Matrix ι ι K) * (ε * (m : Matrix ι ι K)) *
          (((m⁻¹ : GL ι K)) : Matrix ι ι K) := by simp only [Matrix.mul_assoc]
    _ = (((m⁻¹ : GL ι K)) : Matrix ι ι K) * ((m : Matrix ι ι K) * ε) *
          (((m⁻¹ : GL ι K)) : Matrix ι ι K) := by rw [← hm]
    _ = ε * (((m⁻¹ : GL ι K)) : Matrix ι ι K) := by
        rw [← Matrix.mul_assoc (((m⁻¹ : GL ι K)) : Matrix ι ι K)
              (m : Matrix ι ι K) ε, hm'm, Matrix.one_mul]

lemma ggJS1_mem_adjoin_comm {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {S : Set (GL ι K)} {g : Matrix ι ι K}
    (hg : ∀ s ∈ S, (s : Matrix ι ι K) * g = g * (s : Matrix ι ι K))
    {ε : Matrix ι ι K} (hε : ε ∈ Algebra.adjoin K (Units.val '' S)) :
    g * ε = ε * g := by
  have hAle : Algebra.adjoin K (Units.val '' S) ≤
      Subalgebra.centralizer K ({g} : Set (Matrix ι ι K)) := by
    refine Algebra.adjoin_le ?_
    rintro y ⟨s, hs, rfl⟩
    change (s : Matrix ι ι K) ∈ Subalgebra.centralizer K ({g} : Set (Matrix ι ι K))
    rw [Subalgebra.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact (hg s hs).symm
  exact (Subalgebra.mem_centralizer_iff K).mp (hAle hε) g (Set.mem_singleton g)

lemma ggJS1_map_range_eq_toLin' {n : ℕ} {K : Type} [Field K]
    {ε : ggJS1_M n K} (u : GL (Fin n ⊕ Fin n) K)
    (hcomm : (u : ggJS1_M n K) * ε = ε * (u : ggJS1_M n K)) :
    Submodule.map (Matrix.toLin' (u : ggJS1_M n K)) (Matrix.toLin' ε).range =
      (Matrix.toLin' ε).range := by
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    obtain ⟨y', rfl⟩ := hy
    refine ⟨Matrix.toLin' (u : ggJS1_M n K) y', ?_⟩
    rw [← Matrix.toLin'_mul_apply ε (u : ggJS1_M n K) y',
      ← Matrix.toLin'_mul_apply (u : ggJS1_M n K) ε y', hcomm]
  · intro x hx
    have hinv : Submodule.map
        (Matrix.toLin' (((u⁻¹ : GL (Fin n ⊕ Fin n) K)) : ggJS1_M n K))
        (Matrix.toLin' ε).range ≤ (Matrix.toLin' ε).range := by
      rintro x ⟨y, hy, rfl⟩
      obtain ⟨y', rfl⟩ := hy
      refine ⟨Matrix.toLin' (((u⁻¹ : GL (Fin n ⊕ Fin n) K)) : ggJS1_M n K) y', ?_⟩
      rw [← Matrix.toLin'_mul_apply ε (((u⁻¹ : GL (Fin n ⊕ Fin n) K)) : ggJS1_M n K) y',
        ← Matrix.toLin'_mul_apply (((u⁻¹ : GL (Fin n ⊕ Fin n) K)) : ggJS1_M n K) ε y',
        ggJS1_inv_comm u hcomm]
    have hx' : Matrix.toLin' (((u⁻¹ : GL (Fin n ⊕ Fin n) K)) : ggJS1_M n K) x ∈
        (Matrix.toLin' ε).range := hinv ⟨x, hx, rfl⟩
    refine ⟨Matrix.toLin' (((u⁻¹ : GL (Fin n ⊕ Fin n) K)) : ggJS1_M n K) x, hx', ?_⟩
    rw [← Matrix.toLin'_mul_apply (u : ggJS1_M n K)
        (((u⁻¹ : GL (Fin n ⊕ Fin n) K)) : ggJS1_M n K) x,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.toLin'_apply, Matrix.one_mulVec]

theorem blockGroup_iso_Sp_one {K : Type} [Field K] [Fintype K] [CharP K 2] {n : ℕ}
    (b : GL (Fin n ⊕ Fin n) K) (hb : b ∈ StatedSp n K) (hodd : Odd (orderOf b))
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    (hε : IsPrimAdjIdemIn (RingHom.id K)
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL (Fin n ⊕ Fin n) K)))) ε)
    (h1 : (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε = ε) :
    ∃ n₁ : ℕ, 2 * n₁ = Module.finrank K (LinearMap.range (Matrix.toLin' ε)) ∧
      Nonempty (↥(glBlockCentralizer (StatedSp n K).subtype {b} ε) ≃* ↥(StatedSp n₁ K)) := by
  classical
  let p : ggJS1_V n K →ₗ[K] ggJS1_V n K := Matrix.toLin' ε
  let W : Submodule K (ggJS1_V n K) := p.range
  let Z : Submodule K (ggJS1_V n K) := p.ker
  let B : LinearMap.BilinForm K (ggJS1_V n K) := ggJS1_B n K
  let G : Subgroup (StatedSp n K) :=
    glBlockCentralizer (StatedSp n K).subtype ({b} : Set (GL (Fin n ⊕ Fin n) K)) ε
  have hεid : IsIdempotentElem ε := hε.2.1
  have hεadj : formAdj (RingHom.id K) (ggJS1_J n K) ε = ε := hε.2.2.2.1
  have hp : IsIdempotentElem p := by
    apply LinearMap.ext
    intro x
    rw [Module.End.mul_apply]
    show Matrix.toLin' ε (Matrix.toLin' ε x) = Matrix.toLin' ε x
    rw [← Matrix.toLin'_mul_apply ε ε x, hεid.eq]
  have hcompl : IsCompl W Z := LinearMap.IsIdempotentElem.isCompl hp
  have hB_alt : B.IsAlt := ggJS1_B_isAlt n K
  have hB_nd : B.Nondegenerate := ggJS1_B_nondegenerate n K
  have hBWZ : ∀ x ∈ W, ∀ y ∈ Z, B x y = 0 := ggJS1_B_range_ker n K ε hεid hεadj
  have hWZsymm : ∀ x ∈ Z, ∀ y ∈ W, B x y = 0 := by
    intro x hx y hy
    have h := hB_alt.neg_eq x y
    rw [hBWZ y hy x hx] at h
    exact neg_eq_zero.mp h
  have hndW : (B.restrict W).Nondegenerate := by
    rw [LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    have hx0 : (B.restrict W) x = 0 := LinearMap.mem_ker.mp hx
    apply Subtype.ext
    have hBx : B (x : ggJS1_V n K) = 0 := by
      apply LinearMap.ext
      intro y
      have hy : y ∈ W ⊔ Z := by rw [hcompl.sup_eq_top]; exact Submodule.mem_top
      obtain ⟨w, hw, z, hz, rfl⟩ := Submodule.mem_sup.mp hy
      rw [map_add]
      have h1w : B (x : ggJS1_V n K) w = 0 := by
        have := LinearMap.congr_fun hx0 ⟨w, hw⟩
        simpa [LinearMap.BilinForm.restrict_apply] using this
      have h2z : B (x : ggJS1_V n K) z = 0 := hBWZ (x : ggJS1_V n K) x.2 z hz
      rw [h1w, h2z, add_zero]
      simp
    have hxV : (x : ggJS1_V n K) ∈ LinearMap.ker B := LinearMap.mem_ker.mpr hBx
    have hker := LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot.mp hB_nd
    rw [hker] at hxV
    simpa using hxV
  have hB_altW : (B.restrict W).IsAlt := fun x => hB_alt.self_eq_zero (x : ggJS1_V n K)
  have hcoe : ∀ u : GL (Fin n ⊕ Fin n) K,
      (↑(ggJS1_matrixLinIso u) : ggJS1_V n K →ₗ[K] ggJS1_V n K) =
        Matrix.toLin' (u : ggJS1_M n K) := by
    intro u
    apply LinearMap.ext
    intro v
    rw [Matrix.toLin'_apply]
    exact CFSG.ComponentClassification.CatalogueBSymplecticB.matrixLinIso_apply u v
  have hmem_G : ∀ u : ↥G, u.val.val ∈
        Subgroup.centralizer ({b} : Set (GL (Fin n ⊕ Fin n) K)) ∧
      u.val.val ∈ glFixing (1 - ε) := by
    intro u
    exact Subgroup.mem_inf.mp (Subgroup.mem_comap.mp u.property)
  have hu_comm : ∀ u : ↥G, (u.val.val : ggJS1_M n K) * ε = ε * (u.val.val : ggJS1_M n K) := by
    intro u
    have hcent : u.val.val ∈
        Subgroup.centralizer ({b} : Set (GL (Fin n ⊕ Fin n) K)) := (hmem_G u).1
    have hb_u : b * u.val.val = u.val.val * b :=
      Subgroup.mem_centralizer_iff.mp hcent b (by simp)
    have hbM : (b : ggJS1_M n K) * (u.val.val : ggJS1_M n K) =
        (u.val.val : ggJS1_M n K) * (b : ggJS1_M n K) := by
      simpa only [Units.val_mul] using
        congrArg (fun w : GL (Fin n ⊕ Fin n) K => (w : ggJS1_M n K)) hb_u
    exact ggJS1_mem_adjoin_comm (S := ({b} : Set (GL (Fin n ⊕ Fin n) K)))
      (g := (u.val.val : ggJS1_M n K)) (fun s hs => by
        rw [Set.mem_singleton_iff] at hs
        subst hs
        exact hbM) hε.1
  have hfixZ : ∀ u : ↥G, ∀ z : Z,
      (ggJS1_matrixLinIso u.val.val) (z : ggJS1_V n K) = (z : ggJS1_V n K) := by
    intro u z
    have hgl : (u.val.val : ggJS1_M n K) * (1 - ε) = 1 - ε := (hmem_G u).2
    have htoLin_sub : Matrix.toLin' (1 - ε) = 1 - p := by
      apply LinearMap.ext
      intro v
      rw [Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.one_mulVec, LinearMap.sub_apply,
        Module.End.one_apply, Matrix.toLin'_apply]
    have hz : (z : ggJS1_V n K) ∈ (Matrix.toLin' (1 - ε)).range := by
      have hz' : (z : ggJS1_V n K) ∈ (1 - p).range := by
        rw [← LinearMap.IsIdempotentElem.ker_eq_range_one_sub hp]
        exact z.2
      rwa [← htoLin_sub] at hz'
    obtain ⟨v, hv⟩ := hz
    rw [← hv]
    change Matrix.toLin' (u.val.val : ggJS1_M n K) ((Matrix.toLin' (1 - ε)) v) =
      (Matrix.toLin' (1 - ε)) v
    rw [← Matrix.toLin'_mul_apply (u.val.val : ggJS1_M n K) (1 - ε) v, hgl]
  have hmap : ∀ u : ↥G, Submodule.map
      (↑(ggJS1_matrixLinIso u.val.val) : ggJS1_V n K →ₗ[K] ggJS1_V n K) W = W := by
    intro u
    rw [hcoe u.val.val]
    exact ggJS1_map_range_eq_toLin' u.val.val (hu_comm u)
  have hiso_mem : ∀ u : ↥G, (ggJS1_matrixLinIso u.val.val).ofSubmodules W W (hmap u) ∈
      ggJS1_Iso (B.restrict W) := by
    intro u
    rw [TauCeti.BilinForm.mem_isometryGroup_iff]
    intro x y
    have hiso := (CFSG.ComponentClassification.CatalogueBSymplecticB.mem_statedSp_iff_isometry
      u.val.val).mp u.val.property
    rw [TauCeti.BilinForm.mem_isometryGroup_iff] at hiso
    simp only [LinearMap.BilinForm.restrict_apply, LinearEquiv.ofSubmodules_apply]
    exact hiso (x : ggJS1_V n K) (y : ggJS1_V n K)
  let toIso : ↥G →* ↥(ggJS1_Iso (B.restrict W)) :=
    { toFun := fun u =>
        ⟨(ggJS1_matrixLinIso u.val.val).ofSubmodules W W (hmap u), hiso_mem u⟩
      map_one' := by
        apply Subtype.ext
        apply LinearEquiv.ext
        intro x
        apply Subtype.ext
        rw [LinearEquiv.ofSubmodules_apply]
        simp
      map_mul' := by
        intro u v
        apply Subtype.ext
        apply LinearEquiv.ext
        intro x
        apply Subtype.ext
        change (ggJS1_matrixLinIso (u.val.val * v.val.val)) (x : ggJS1_V n K) =
          (ggJS1_matrixLinIso u.val.val) ((ggJS1_matrixLinIso v.val.val) (x : ggJS1_V n K))
        rw [map_mul]
        rfl }
  have hinj : Function.Injective toIso := by
    intro u v huv
    apply Subtype.ext
    apply Subtype.ext
    apply ggJS1_matrixLinIso.injective
    apply LinearEquiv.ext
    intro x
    have huvW : ∀ w : W, (ggJS1_matrixLinIso u.val.val) (w : ggJS1_V n K) =
        (ggJS1_matrixLinIso v.val.val) (w : ggJS1_V n K) := by
      intro w
      have h := congrArg
        (fun e : ↥(ggJS1_Iso (B.restrict W)) => ((e.val) w : ggJS1_V n K)) huv
      change (ggJS1_matrixLinIso u.val.val) (w : ggJS1_V n K) =
        (ggJS1_matrixLinIso v.val.val) (w : ggJS1_V n K) at h
      exact h
    have hx : x ∈ W ⊔ Z := by rw [hcompl.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨w, hw, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add, map_add, huvW ⟨w, hw⟩, hfixZ u ⟨z, hz⟩, hfixZ v ⟨z, hz⟩]
  have hsurj : Function.Surjective toIso := by
    intro h
    let WZ : (↥W × ↥Z) ≃ₗ[K] ggJS1_V n K := Submodule.prodEquivOfIsCompl W Z hcompl
    let hprod : (↥W × ↥Z) ≃ₗ[K] (↥W × ↥Z) :=
      LinearEquiv.prodCongr h.val (LinearEquiv.refl K ↥Z)
    let uV : ggJS1_V n K ≃ₗ[K] ggJS1_V n K := WZ.symm.trans (hprod.trans WZ)
    have huV_left : ∀ w : W, uV (w : ggJS1_V n K) = (h.val w : ggJS1_V n K) := by
      intro w
      show WZ (hprod (WZ.symm (w : ggJS1_V n K))) = (h.val w : ggJS1_V n K)
      have hs : WZ.symm (w : ggJS1_V n K) = (w, 0) := by
        apply WZ.injective
        rw [WZ.apply_symm_apply, Submodule.coe_prodEquivOfIsCompl']
        simp
      rw [hs]
      have hpw : hprod (w, 0) = (h.val w, 0) := by
        simp [hprod, LinearEquiv.prodCongr_apply]
      rw [hpw, Submodule.coe_prodEquivOfIsCompl']
      simp
    have huV_right : ∀ z : Z, uV (z : ggJS1_V n K) = (z : ggJS1_V n K) := by
      intro z
      show WZ (hprod (WZ.symm (z : ggJS1_V n K))) = (z : ggJS1_V n K)
      have hs : WZ.symm (z : ggJS1_V n K) = (0, z) := by
        apply WZ.injective
        rw [WZ.apply_symm_apply, Submodule.coe_prodEquivOfIsCompl']
        simp
      rw [hs]
      have hpz : hprod (0, z) = (0, z) := by
        simp [hprod, LinearEquiv.prodCongr_apply]
      rw [hpz, Submodule.coe_prodEquivOfIsCompl']
      simp
    have huV_iso : ∀ x y, B (uV x) (uV y) = B x y := by
      intro x y
      have hx : x ∈ W ⊔ Z := by rw [hcompl.sup_eq_top]; exact Submodule.mem_top
      have hy : y ∈ W ⊔ Z := by rw [hcompl.sup_eq_top]; exact Submodule.mem_top
      obtain ⟨xW, hxW, xZ, hxZ, rfl⟩ := Submodule.mem_sup.mp hx
      obtain ⟨yW, hyW, yZ, hyZ, rfl⟩ := Submodule.mem_sup.mp hy
      rw [map_add, map_add, map_add, map_add, huV_left ⟨xW, hxW⟩, huV_right ⟨xZ, hxZ⟩,
        huV_left ⟨yW, hyW⟩, huV_right ⟨yZ, hyZ⟩]
      have hhW : (h.val ⟨xW, hxW⟩ : ggJS1_V n K) ∈ W := (h.val ⟨xW, hxW⟩).2
      have hhW' : (h.val ⟨yW, hyW⟩ : ggJS1_V n K) ∈ W := (h.val ⟨yW, hyW⟩).2
      have hiso_h : B (h.val ⟨xW, hxW⟩ : ggJS1_V n K) (h.val ⟨yW, hyW⟩ : ggJS1_V n K) =
          B xW yW := by
        have := (TauCeti.BilinForm.mem_isometryGroup_iff.mp h.property) ⟨xW, hxW⟩ ⟨yW, hyW⟩
        simpa [LinearMap.BilinForm.restrict_apply] using this
      simp only [map_add, LinearMap.add_apply]
      rw [hBWZ _ hhW _ hyZ, hWZsymm _ hxZ _ hhW', hBWZ _ hxW _ hyZ, hWZsymm _ hxZ _ hyW,
        hiso_h]
    let g : GL (Fin n ⊕ Fin n) K := ggJS1_matrixLinIso.symm uV
    have hgu : ggJS1_matrixLinIso g = uV := MulEquiv.apply_symm_apply ggJS1_matrixLinIso uV
    have hcoe_g : (Matrix.toLin' (g : ggJS1_M n K) : ggJS1_V n K →ₗ[K] ggJS1_V n K) =
        (uV : ggJS1_V n K →ₗ[K] ggJS1_V n K) := by
      rw [← hcoe g, hgu]
    have hgStated : g ∈ StatedSp n K := by
      rw [CFSG.ComponentClassification.CatalogueBSymplecticB.mem_statedSp_iff_isometry, hgu]
      exact TauCeti.BilinForm.mem_isometryGroup_iff.mpr huV_iso
    have hgFixing : (g : ggJS1_M n K) * (1 - ε) = 1 - ε := by
      apply Matrix.toLin'.injective
      apply LinearMap.ext
      intro v
      rw [Matrix.toLin'_mul_apply, hcoe_g, Matrix.toLin'_apply]
      have hvZ : (1 - ε) *ᵥ v ∈ Z := by
        rw [show Z = (Matrix.toLin' ε).ker from rfl, LinearMap.mem_ker, Matrix.toLin'_apply,
          Matrix.mulVec_mulVec, ggJS1_eps_mul_one_sub hεid, Matrix.zero_mulVec]
      exact huV_right ⟨_, hvZ⟩
    have hb_comm_eps : (b : ggJS1_M n K) * ε = ε * (b : ggJS1_M n K) :=
      ggJS1_mem_adjoin_comm (fun s hs => by
        rw [Set.mem_singleton_iff] at hs
        subst hs
        rfl) hε.1
    have hb_fix_W : ∀ w : W, (ggJS1_matrixLinIso b) (w : ggJS1_V n K) =
        (w : ggJS1_V n K) := by
      intro w
      obtain ⟨w', hw'⟩ := LinearMap.mem_range.mp w.2
      rw [← hw']
      change Matrix.toLin' (b : ggJS1_M n K) (Matrix.toLin' ε w') = Matrix.toLin' ε w'
      rw [← Matrix.toLin'_mul_apply (b : ggJS1_M n K) ε w', h1]
    have hb_pres_W : ∀ w : W, (ggJS1_matrixLinIso b) (w : ggJS1_V n K) ∈ W := by
      intro w
      rw [hb_fix_W w]
      exact w.2
    have hcomm_p : ∀ x : ggJS1_V n K, p ((ggJS1_matrixLinIso b) x) =
        (ggJS1_matrixLinIso b) (p x) := by
      intro x
      change Matrix.toLin' ε (Matrix.toLin' (b : ggJS1_M n K) x) =
        Matrix.toLin' (b : ggJS1_M n K) (Matrix.toLin' ε x)
      rw [← Matrix.toLin'_mul_apply ε (b : ggJS1_M n K) x, ← hb_comm_eps,
        Matrix.toLin'_mul_apply (b : ggJS1_M n K) ε x]
    have hb_pres_Z : ∀ z : Z, (ggJS1_matrixLinIso b) (z : ggJS1_V n K) ∈ Z := by
      intro z
      change p ((ggJS1_matrixLinIso b) (z : ggJS1_V n K)) = 0
      rw [hcomm_p, LinearMap.mem_ker.mp z.2, map_zero]
    have hb_uV : (ggJS1_matrixLinIso b) * uV = uV * (ggJS1_matrixLinIso b) := by
      apply LinearEquiv.ext
      intro x
      have hx : x ∈ W ⊔ Z := by rw [hcompl.sup_eq_top]; exact Submodule.mem_top
      obtain ⟨w, hw, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
      simp only [map_add]
      rw [huV_left ⟨w, hw⟩, huV_right ⟨z, hz⟩, hb_fix_W ⟨w, hw⟩,
        hb_fix_W ⟨h.val ⟨w, hw⟩, (h.val ⟨w, hw⟩).2⟩,
        huV_right ⟨(ggJS1_matrixLinIso b) (z : ggJS1_V n K), hb_pres_Z ⟨z, hz⟩⟩,
        huV_left ⟨w, hw⟩]
    have hgCentral : g ∈ Subgroup.centralizer ({b} : Set (GL (Fin n ⊕ Fin n) K)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      rw [Set.mem_singleton_iff] at hs
      subst hs
      apply ggJS1_matrixLinIso.injective
      rw [map_mul, map_mul, hgu]
      exact hb_uV
    let gs : StatedSp n K := ⟨g, hgStated⟩
    have hgG : gs ∈ G := by
      change (StatedSp n K).subtype gs ∈
        (Subgroup.centralizer ({b} : Set (GL (Fin n ⊕ Fin n) K)) ⊓ glFixing (1 - ε))
      exact Subgroup.mem_inf.mpr ⟨hgCentral, hgFixing⟩
    refine ⟨⟨gs, hgG⟩, ?_⟩
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    apply Subtype.ext
    change (ggJS1_matrixLinIso g) (x : ggJS1_V n K) = (h.val x : ggJS1_V n K)
    rw [hgu]
    exact huV_left x
  have hEquiv : ↥G ≃* ↥(ggJS1_Iso (B.restrict W)) :=
    MulEquiv.ofBijective toIso ⟨hinj, hsurj⟩
  obtain ⟨m, hdim, ⟨e⟩⟩ :=
    CFSG.ComponentClassification.CatalogueBAlternatingIsometry.exists_isometryEquiv_symplectic
      (B.restrict W) hB_altW hndW
  refine ⟨m, ?_, ?_⟩
  · show 2 * m = Module.finrank K (LinearMap.range (Matrix.toLin' ε))
    rw [hdim]
  · exact ⟨hEquiv.trans (e.trans (MulEquiv.subgroupCongr
      (CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic (n := m) (K := K))).symm)⟩

private lemma ggJS1_squarefree_minpoly_spEnd {K : Type} [Field K] [CharP K 2] {n : ℕ}
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

private lemma ggJS1_altPrimaryData {K : Type} [Field K] [CharP K 2] {n : ℕ}
    (b : StatedSp n K) (hodd : Odd (orderOf b)) :
    AltPrimaryData (spForm n K) (spLin n K b) where
  alt := spForm_isAlt
  sep := spForm_nondegenerate.1
  isom := spLin_mem b
  squarefree := ggJS1_squarefree_minpoly_spEnd b hodd

private lemma ggJS1_adjoin_commute_commutant {K V : Type} [Field K] [AddCommGroup V]
    [Module K V] (x : Module.End K V) :
    ∀ z ∈ Algebra.adjoin K ({x} : Set (Module.End K V)),
      ∀ w ∈ commutant x, z * w = w * z := by
  intro z hz
  refine Algebra.adjoin_induction (p := fun z _ => ∀ w ∈ commutant x, z * w = w * z)
    ?_ ?_ ?_ ?_ hz
  · intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    intro w hw
    rw [Subalgebra.mem_centralizer_iff] at hw
    exact hw x (Set.mem_singleton x)
  · intro c w _
    exact (Algebra.commute_algebraMap_left c w).eq
  · intro y z hy hz ihy ihz w hw
    rw [add_mul, mul_add, ihy w hw, ihz w hw]
  · intro y z hy hz ihy ihz w hw
    rw [mul_assoc, ihz w hw, ← mul_assoc, ihy w hw, mul_assoc]

private lemma ggJS1_primaryProjection_mem_adjoin {K V : Type} [Field K] [AddCommGroup V]
    [Module K V] (x : Module.End K V) (a : K[X]) :
    primaryProjection x a ∈ Algebra.adjoin K ({x} : Set (Module.End K V)) := by
  unfold primaryProjection
  exact ((primaryIdempotent x a).aeval x :
    Algebra.adjoin K ({x} : Set (Module.End K V))).2

private lemma ggJS1_primaryProjection_idem {K V : Type} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {x : Module.End K V} (hsq : Squarefree (minpoly K x))
    {a : K[X]} (ha : a ∈ primaryFactors x) : IsIdempotentElem (primaryProjection x a) :=
  primaryProjection_mul_self hsq ha

private lemma ggJS1_adjoin_le_commutant {K V : Type} [Field K] [AddCommGroup V]
    [Module K V] (x : Module.End K V) :
    Algebra.adjoin K ({x} : Set (Module.End K V)) ≤ commutant x := by
  refine Algebra.adjoin_le ?_
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  rw [hy]
  exact (mem_commutant x).mpr (Commute.refl x)

private lemma ggJS1_formAdj_eq_adj {K : Type} [Field K] [CharP K 2] {n : ℕ}
    (β : StatedSp n K) (hodd : Odd (orderOf β))
    (a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) :
    Matrix.toLinAlgEquiv' (formAdj (RingHom.id K) (ggJS1_J n K) a) =
      (ggJS1_altPrimaryData β hodd).adj (Matrix.toLinAlgEquiv' a) := by
  refine ((ggJS1_altPrimaryData β hodd).adj_unique ?_).symm
  intro v w
  exact ggJS1_toBilin_adj n K a v w

private lemma ggJS1_primaryProjection_mul_eq_zero {K V : Type} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {x : Module.End K V} (hsq : Squarefree (minpoly K x))
    {a b : K[X]} (ha : a ∈ primaryFactors x) (hb : b ∈ primaryFactors x) (hab : a ≠ b) :
    primaryProjection x a * primaryProjection x b = 0 := by
  apply LinearMap.ext
  intro v
  rw [Module.End.mul_apply, LinearMap.zero_apply]
  exact primaryProjection_of_mem_ne hsq ha hb (Ne.symm hab) (primaryProjection_mem hsq hb v)

private lemma ggJS1_isPrimIdem_map {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (φ : Matrix ι ι K ≃ₐ[K] Module.End K (ι → K))
    {A : Subalgebra K (Matrix ι ι K)} {e : Matrix ι ι K} (he : IsPrimIdemIn A e) :
    ∀ e' ∈ A.map φ, IsIdempotentElem e' → e' * (φ e) = e' → e' = 0 ∨ e' = φ e := by
  intro e' he' hid' he'e
  rw [Subalgebra.mem_map] at he'
  obtain ⟨a, ha, hφa⟩ := he'
  rw [← hφa] at hid' he'e ⊢
  have haid : IsIdempotentElem a := by
    rw [isIdempotentElem_iff] at hid' ⊢
    exact φ.injective (by rw [map_mul]; exact hid')
  have hae : a * e = a := by
    apply φ.injective
    rw [map_mul]
    exact he'e
  rcases he.2.2.2 a ha haid hae with h0 | heq
  · left; rw [h0, map_zero]
  · right; rw [heq]; rfl

lemma ggJS1_prim_idem_eq_primaryProjection {K : Type} [Field K] [CharP K 2] {n : ℕ}
    (b : StatedSp n K) (hodd : Odd (orderOf b))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    (he : IsPrimIdemIn (Algebra.adjoin K
      (Units.val '' ({(b : GL (Fin n ⊕ Fin n) K)} : Set (GL (Fin n ⊕ Fin n) K)))) e) :
    ∃ a ∈ primaryFactors (spEnd b), Matrix.toLinAlgEquiv' e = primaryProjection (spEnd b) a := by
  classical
  have hsq := ggJS1_squarefree_minpoly_spEnd b hodd
  let φ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K ≃ₐ[K]
      Module.End K (Fin n ⊕ Fin n → K) := Matrix.toLinAlgEquiv'
  let A : Subalgebra K (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) :=
    Algebra.adjoin K (Units.val '' ({(b : GL (Fin n ⊕ Fin n) K)} : Set (GL (Fin n ⊕ Fin n) K)))
  let A' : Subalgebra K (Module.End K (Fin n ⊕ Fin n → K)) := Algebra.adjoin K {spEnd b}
  have hφb : φ ((b : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
      spEnd b := rfl
  have hA' : A.map φ = A' := by
    rw [AlgHom.map_adjoin]
    simp only [A, A', Set.image_singleton, AlgEquiv.coe_toAlgHom, hφb]
  have heA : φ e ∈ A' := by
    rw [← hA']
    exact ⟨e, he.1, rfl⟩
  have heidem : IsIdempotentElem (φ e) := by
    rw [isIdempotentElem_iff]
    rw [← map_mul, he.2.1.eq]
  have hene : φ e ≠ 0 := by
    intro h
    exact he.2.2.1 (φ.injective (by rw [h, map_zero]))
  have he_comm : φ e ∈ commutant (spEnd b) := ggJS1_adjoin_le_commutant (spEnd b) heA
  have hprim : ∀ e' ∈ A', IsIdempotentElem e' → e' * (φ e) = e' → e' = 0 ∨ e' = φ e := by
    rw [← hA']
    exact ggJS1_isPrimIdem_map φ he
  have hsum : ∑ a ∈ primaryFactors (spEnd b), primaryProjection (spEnd b) a = 1 :=
    sum_primaryProjection hsq
  have heq_sum : φ e = ∑ a ∈ primaryFactors (spEnd b),
      φ e * primaryProjection (spEnd b) a := by
    rw [← Finset.mul_sum, hsum, mul_one]
  have hterm : ∀ a ∈ primaryFactors (spEnd b),
      φ e * primaryProjection (spEnd b) a = 0 ∨
        φ e * primaryProjection (spEnd b) a = φ e := by
    intro a ha
    have hPmem : primaryProjection (spEnd b) a ∈ A' := ggJS1_primaryProjection_mem_adjoin _ a
    have hPidem : IsIdempotentElem (primaryProjection (spEnd b) a) :=
      ggJS1_primaryProjection_idem hsq ha
    have htmem : φ e * primaryProjection (spEnd b) a ∈ A' := A'.mul_mem heA hPmem
    have hcomm : primaryProjection (spEnd b) a * φ e =
        φ e * primaryProjection (spEnd b) a := by
      have h := mul_comm' (⟨primaryProjection (spEnd b) a, hPmem⟩ : ↥A')
        (⟨φ e, heA⟩ : ↥A')
      exact congrArg Subtype.val h
    have htidem : IsIdempotentElem (φ e * primaryProjection (spEnd b) a) :=
      IsIdempotentElem.mul_of_commute hcomm.symm heidem hPidem
    have hte : (φ e * primaryProjection (spEnd b) a) * φ e =
        φ e * primaryProjection (spEnd b) a := by
      rw [mul_assoc, hcomm, ← mul_assoc, heidem.eq]
    exact hprim _ htmem htidem hte
  obtain ⟨a₀, ha₀, ha₀e⟩ : ∃ a ∈ primaryFactors (spEnd b),
      φ e * primaryProjection (spEnd b) a = φ e := by
    by_contra hcon
    push Not at hcon
    have hall : ∀ a ∈ primaryFactors (spEnd b), φ e * primaryProjection (spEnd b) a = 0 :=
      fun a ha => (hterm a ha).resolve_right (hcon a ha)
    rw [Finset.sum_eq_zero hall] at heq_sum
    exact hene heq_sum
  have hpc : IsPrimitiveCentralIdempotent K (primaryProjectionR (spEnd b) a₀) :=
    (isPrimitiveCentralIdempotent_iff hsq _).mpr ⟨a₀, ha₀, rfl⟩
  have hg_center : (⟨φ e, he_comm⟩ : commutant (spEnd b)) ∈
      Subalgebra.center K (commutant (spEnd b)) := by
    rw [Subalgebra.mem_center_iff]
    intro z
    apply Subtype.ext
    change (z : Module.End K _) * φ e = φ e * (z : Module.End K _)
    exact (ggJS1_adjoin_commute_commutant (spEnd b) (φ e) heA (z : Module.End K _) z.2).symm
  have hg_idem : IsIdempotentElem (⟨φ e, he_comm⟩ : commutant (spEnd b)) := by
    rw [isIdempotentElem_iff]
    apply Subtype.ext
    exact heidem.eq
  have hg_mul : (⟨φ e, he_comm⟩ : commutant (spEnd b)) * primaryProjectionR (spEnd b) a₀ =
      ⟨φ e, he_comm⟩ := by
    apply Subtype.ext
    exact ha₀e
  rcases hpc.2.2.2 _ hg_center hg_idem hg_mul with h0 | heq
  · exact absurd (congrArg Subtype.val h0) hene
  · exact ⟨a₀, ha₀, congrArg Subtype.val heq⟩

private lemma ggJS1_toLinAlgEquiv'_eq_toLin' {K : Type} [Field K] {ι : Type}
    [Fintype ι] [DecidableEq ι] (M : Matrix ι ι K) :
    Matrix.toLinAlgEquiv' M = Matrix.toLin' M := by
  apply LinearMap.ext
  intro v
  rw [Matrix.toLinAlgEquiv'_apply, Matrix.toLin'_apply]

private lemma ggJS1_mem_glFixing_iff {K : Type} [Field K] {ι : Type} [Fintype ι]
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

private lemma ggJS1_adj_add {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {B : LinearMap.BilinForm K V}
    {x : LinearMap.GeneralLinearGroup K V} (H : AltPrimaryData B x)
    (r s : Module.End K V) : H.adj (r + s) = H.adj r + H.adj s :=
  H.adj_unique fun v w => by
    calc B ((r + s) v) w = B (r v + s v) w := by rw [LinearMap.add_apply]
      _ = (B (r v) + B (s v)) w := by rw [map_add]
      _ = B (r v) w + B (s v) w := by rw [LinearMap.add_apply]
      _ = B v (H.adj r w) + B v (H.adj s w) := by rw [H.adj_spec, H.adj_spec]
      _ = B v (H.adj r w + H.adj s w) := (map_add (B v) _ _).symm
      _ = B v ((H.adj r + H.adj s) w) := by rw [LinearMap.add_apply]

private lemma ggJS1_one_sub_add_primaryProjection_eq_sum
    {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {x : Module.End K V} (hsq : Squarefree (minpoly K x)) {a b : K[X]}
    (ha : a ∈ primaryFactors x) (hb : b ∈ primaryFactors x) (hab : a ≠ b)
    [DecidableEq K[X]] :
    (1 : Module.End K V) - (primaryProjection x a + primaryProjection x b) =
      ∑ c ∈ ((primaryFactors x).erase a).erase b, primaryProjection x c := by
  classical
  have hb' : b ∈ (primaryFactors x).erase a := Finset.mem_erase.mpr ⟨hab.symm, hb⟩
  have h1 := Finset.sum_erase_add (primaryFactors x) (primaryProjection x) ha
  have h2 := Finset.sum_erase_add ((primaryFactors x).erase a) (primaryProjection x) hb'
  have h3 : (∑ c ∈ ((primaryFactors x).erase a).erase b, primaryProjection x c) +
      (primaryProjection x a + primaryProjection x b) = 1 := by
    rw [add_comm (primaryProjection x a) (primaryProjection x b), ← add_assoc, h2, h1]
    exact sum_primaryProjection hsq
  exact ((eq_sub_iff_add_eq).mpr h3).symm

lemma ggJS1_glBlockCentralizer_eq_spSupported
    {K : Type} [Field K] [CharP K 2] {n : ℕ}
    (β : StatedSp n K) (hodd : Odd (orderOf β))
    {ε e e' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    {a : K[X]} (ha : a ∈ primaryFactors (spEnd β))
    (hane : a ≠ reciprocalPolynomial a)
    (hae : Matrix.toLinAlgEquiv' e = primaryProjection (spEnd β) a)
    (ha'e : Matrix.toLinAlgEquiv' e' =
      primaryProjection (spEnd β) (reciprocalPolynomial a))
    (hεsum : ε = e + e') :
    glBlockCentralizer (StatedSp n K).subtype
        ({(β : GL (Fin n ⊕ Fin n) K)} : Set (GL (Fin n ⊕ Fin n) K)) ε =
      spSupported β {a, reciprocalPolynomial a} := by
  classical
  have hsq := ggJS1_squarefree_minpoly_spEnd β hodd
  have H := ggJS1_altPrimaryData β hodd
  have hb := H.reciprocal_mem ha
  let F : Finset K[X] := primaryFactors (spEnd β)
  let S : Finset K[X] := (F.erase a).erase (reciprocalPolynomial a)
  have hsum : (1 : Module.End K (Fin n ⊕ Fin n → K)) -
      (primaryProjection (spEnd β) a +
        primaryProjection (spEnd β) (reciprocalPolynomial a)) =
      ∑ c ∈ S, primaryProjection (spEnd β) c :=
    ggJS1_one_sub_add_primaryProjection_eq_sum hsq ha hb hane
  have hQ : Matrix.toLin' (1 - ε) = ∑ c ∈ S, primaryProjection (spEnd β) c := by
    have hadd : Matrix.toLin' ε = Matrix.toLin' e + Matrix.toLin' e' := by
      rw [hεsum]
      exact Matrix.toLin'.map_add e e'
    have hsubε : Matrix.toLin' (1 - ε) = 1 - Matrix.toLin' ε := by
      apply LinearMap.ext
      intro v
      rw [Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.one_mulVec, LinearMap.sub_apply,
        Module.End.one_apply, Matrix.toLin'_apply]
    rw [hsubε, hadd, ← ggJS1_toLinAlgEquiv'_eq_toLin' e,
      ← ggJS1_toLinAlgEquiv'_eq_toLin' e', hae, ha'e]
    exact hsum
  ext g
  have hspEnd : spEnd g = Matrix.toLin'
      ((g : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) := by
    apply LinearMap.ext
    intro v
    rw [Matrix.toLin'_apply]
    rfl
  have hcenter : (g : GL (Fin n ⊕ Fin n) K) ∈
      Subgroup.centralizer ({(β : GL (Fin n ⊕ Fin n) K)} : Set (GL (Fin n ⊕ Fin n) K)) ↔
      g * β = β * g := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg
      (fun z : StatedSp n K => (z : GL (Fin n ⊕ Fin n) K)) h⟩
  have hfix : (g : GL (Fin n ⊕ Fin n) K) ∈ glFixing (1 - ε) ↔
      ∀ v, spEnd g (Matrix.toLin' (1 - ε) v) = Matrix.toLin' (1 - ε) v := by
    rw [ggJS1_mem_glFixing_iff]
    constructor
    · intro h v
      rw [hspEnd]
      exact h v
    · intro h v
      rw [← hspEnd]
      exact h v
  rw [mem_spSupported, glBlockCentralizer, Subgroup.mem_comap, Subgroup.mem_inf]
  change ((g : GL (Fin n ⊕ Fin n) K) ∈
      Subgroup.centralizer ({(β : GL (Fin n ⊕ Fin n) K)} : Set (GL (Fin n ⊕ Fin n) K)) ∧
      (g : GL (Fin n ⊕ Fin n) K) ∈ glFixing (1 - ε)) ↔
    g * β = β * g ∧ ∀ k ∈ primaryFactors (spEnd β), k ∉ {a, reciprocalPolynomial a} →
      ∀ v ∈ primaryComponent (spEnd β) k, spEnd g v = v
  rw [hcenter, hfix]
  constructor
  · rintro ⟨hc, hfixv⟩
    refine ⟨hc, fun k hk hkS v hv => ?_⟩
    have hkmemS : k ∈ S := by
      have hka : k ≠ a := fun h => hkS (by simp [h])
      have hkb : k ≠ reciprocalPolynomial a := fun h => hkS (by simp [h])
      exact Finset.mem_erase.mpr ⟨hkb, Finset.mem_erase.mpr ⟨hka, hk⟩⟩
    have hsumk : (∑ c ∈ S, primaryProjection (spEnd β) c v) = v := by
      rw [Finset.sum_eq_single k]
      · exact primaryProjection_of_mem hsq hk hv
      · intro c hcS hck
        exact primaryProjection_of_mem_ne hsq
          (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hcS)) hk (Ne.symm hck) hv
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
    have hcF : c ∈ primaryFactors (spEnd β) :=
      Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hcS)
    have hca : c ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hcS).2).1
    have hcb : c ≠ reciprocalPolynomial a := (Finset.mem_erase.mp hcS).1
    exact hfixK c hcF (by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hca, hcb⟩) _ (primaryProjection_mem hsq hcF v)

lemma ggJS1_reciprocal_of_prim_pair
    {K : Type} [Field K] [CharP K 2] {n : ℕ}
    (β : StatedSp n K) (hodd : Odd (orderOf β))
    {A : Subalgebra K (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)}
    {ε e e' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    {a a' : K[X]}
    (ha : a ∈ primaryFactors (spEnd β)) (ha' : a' ∈ primaryFactors (spEnd β))
    (hae : Matrix.toLinAlgEquiv' e = primaryProjection (spEnd β) a)
    (ha'e : Matrix.toLinAlgEquiv' e' = primaryProjection (spEnd β) a')
    (hεsum : ε = e + e') (hene : e ≠ e') (he0 : e ≠ 0) (he'0 : e' ≠ 0)
    (heA : e ∈ A) (heid : IsIdempotentElem e)
    (hεprim : ∀ f ∈ A, IsIdempotentElem f → formAdj (RingHom.id K) (ggJS1_J n K) f = f →
      f * ε = f → f = 0 ∨ f = ε)
    (hεadj : formAdj (RingHom.id K) (ggJS1_J n K) ε = ε) :
    a' = reciprocalPolynomial a ∧ a ≠ reciprocalPolynomial a := by
  classical
  have hsq := ggJS1_squarefree_minpoly_spEnd β hodd
  have H := ggJS1_altPrimaryData β hodd
  have hb := H.reciprocal_mem ha
  have hb' := H.reciprocal_mem ha'
  have hφε : Matrix.toLinAlgEquiv' ε =
      primaryProjection (spEnd β) a + primaryProjection (spEnd β) a' := by
    rw [hεsum, map_add, hae, ha'e]
  have ha_ne : a ≠ a' := by
    intro h
    exact hene (Matrix.toLinAlgEquiv'.injective (by rw [hae, ha'e, h]))
  have hadj : H.adj (Matrix.toLinAlgEquiv' ε) = Matrix.toLinAlgEquiv' ε := by
    have h := congrArg Matrix.toLinAlgEquiv' hεadj
    rw [ggJS1_formAdj_eq_adj β hodd ε] at h
    exact h
  have heq : primaryProjection (spEnd β) a + primaryProjection (spEnd β) a' =
      primaryProjection (spEnd β) (reciprocalPolynomial a) +
        primaryProjection (spEnd β) (reciprocalPolynomial a') := by
    have h : H.adj (primaryProjection (spEnd β) a + primaryProjection (spEnd β) a') =
        primaryProjection (spEnd β) (reciprocalPolynomial a) +
          primaryProjection (spEnd β) (reciprocalPolynomial a') := by
      rw [ggJS1_adj_add H (primaryProjection (spEnd β) a)
        (primaryProjection (spEnd β) a'), AltPrimaryData.adj_primaryProjection H ha,
        AltPrimaryData.adj_primaryProjection H ha']
    have h2 : H.adj (primaryProjection (spEnd β) a + primaryProjection (spEnd β) a') =
        primaryProjection (spEnd β) a + primaryProjection (spEnd β) a' := by
      rw [← hφε]
      exact hadj
    rw [← h2]
    exact h
  have hP_ne : primaryProjection (spEnd β) a ≠ 0 := by
    intro h0
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (primaryComponent_ne_bot hsq ha)
    have h := primaryProjection_of_mem hsq ha hv
    simp [h0] at h
    exact hv0 h.symm
  have hane : a ≠ reciprocalPolynomial a := by
    intro haa
    have hadj_a : H.adj (primaryProjection (spEnd β) a) = primaryProjection (spEnd β) a := by
      rw [AltPrimaryData.adj_primaryProjection H ha]
      exact congrArg (fun t : K[X] => primaryProjection (spEnd β) t) haa.symm
    have hadj_e : H.adj (Matrix.toLinAlgEquiv' e) = Matrix.toLinAlgEquiv' e := by
      rw [hae, hadj_a]
    have hfe : formAdj (RingHom.id K) (ggJS1_J n K) e = e := by
      apply Matrix.toLinAlgEquiv'.injective
      rw [ggJS1_formAdj_eq_adj β hodd e]
      exact hadj_e
    have hee' : e * e' = 0 := by
      apply Matrix.toLinAlgEquiv'.injective
      rw [map_mul, hae, ha'e, map_zero]
      exact ggJS1_primaryProjection_mul_eq_zero hsq ha ha' ha_ne
    have heε : e * ε = e := by
      rw [hεsum, mul_add, heid.eq, hee', add_zero]
    rcases hεprim e heA heid hfe heε with h0 | hεe
    · exact he0 h0
    · have h : e + (0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = e + e' := by
        rw [add_zero]
        exact hεe.trans hεsum
      exact he'0 (add_left_cancel h).symm
  refine ⟨?_, hane⟩
  have hPaa : primaryProjection (spEnd β) a *
      primaryProjection (spEnd β) (reciprocalPolynomial a) = 0 :=
    ggJS1_primaryProjection_mul_eq_zero hsq ha hb hane
  have horth : primaryProjection (spEnd β) a * primaryProjection (spEnd β) a' = 0 :=
    ggJS1_primaryProjection_mul_eq_zero hsq ha ha' ha_ne
  have hmul : primaryProjection (spEnd β) a = primaryProjection (spEnd β) a *
      primaryProjection (spEnd β) (reciprocalPolynomial a') := by
    have h := congrArg (fun T : Module.End K (Fin n ⊕ Fin n → K) =>
      primaryProjection (spEnd β) a * T) heq
    have hL : primaryProjection (spEnd β) a * (primaryProjection (spEnd β) a +
        primaryProjection (spEnd β) a') = primaryProjection (spEnd β) a := by
      rw [mul_add, primaryProjection_mul_self hsq ha, horth, add_zero]
    have hR : primaryProjection (spEnd β) a *
        (primaryProjection (spEnd β) (reciprocalPolynomial a) +
          primaryProjection (spEnd β) (reciprocalPolynomial a')) =
        primaryProjection (spEnd β) a * primaryProjection (spEnd β) (reciprocalPolynomial a) +
        primaryProjection (spEnd β) a *
          primaryProjection (spEnd β) (reciprocalPolynomial a') :=
      mul_add _ _ _
    rw [hL, hR, hPaa, zero_add] at h
    exact h
  by_cases hP : a = reciprocalPolynomial a'
  · calc a' = reciprocalPolynomial (reciprocalPolynomial a') :=
        (H.reciprocal_reciprocal ha').symm
      _ = reciprocalPolynomial a := by rw [← hP]
  · have hzero : primaryProjection (spEnd β) a *
        primaryProjection (spEnd β) (reciprocalPolynomial a') = 0 :=
      ggJS1_primaryProjection_mul_eq_zero hsq ha hb' hP
    rw [hzero] at hmul
    exact absurd hmul hP_ne

private lemma ggJS1_blockDegree_eq_natDegree {K : Type} [Field K] [CharP K 2] {n : ℕ}
    (β : StatedSp n K) (hodd : Odd (orderOf β))
    {a : K[X]} (ha : a ∈ primaryFactors (spEnd β))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    (hae : Matrix.toLinAlgEquiv' e = primaryProjection (spEnd β) a) :
    blockDegree (Algebra.adjoin K (Units.val '' ({(β : GL (Fin n ⊕ Fin n) K)} :
      Set (GL (Fin n ⊕ Fin n) K)))) e = a.natDegree := by
  classical
  haveI : Fact (Irreducible a) := ⟨irreducible_of_mem_primaryFactors ha⟩
  have hsq : Squarefree (minpoly K (spEnd β)) := ggJS1_squarefree_minpoly_spEnd β hodd
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
    rw [ggJS1_toLinAlgEquiv'_eq_toLin']
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

private lemma ggJS1_linear_strong {K : Type} [Field K] [Fintype K] [CharP K 2] {n : ℕ}
    (b : GL (Fin n ⊕ Fin n) K) (hb : b ∈ StatedSp n K) (hodd : Odd (orderOf b))
    {ε e e' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    (hε : IsPrimAdjIdemIn (RingHom.id K)
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL (Fin n ⊕ Fin n) K)))) ε)
    (he : IsPrimIdemIn (Algebra.adjoin K (Units.val '' ({b} : Set (GL (Fin n ⊕ Fin n) K)))) e)
    (he' : IsPrimIdemIn (Algebra.adjoin K (Units.val '' ({b} : Set (GL (Fin n ⊕ Fin n) K)))) e')
    (hne : e ≠ e') (hεe : ε = e + e') :
    ∃ (d m : ℕ) (E : Type) (_ : Field E) (_ : Fintype E), 1 ≤ d ∧
      Fintype.card E = Fintype.card K ^ d ∧
      2 * d * m = Module.finrank K (LinearMap.range (Matrix.toLin' ε)) ∧
      blockDegree (Algebra.adjoin K (Units.val '' ({b} : Set (GL (Fin n ⊕ Fin n) K)))) e = d ∧
      Nonempty (↥(glBlockCentralizer (StatedSp n K).subtype {b} ε) ≃* GL (Fin m) E) := by
  classical
  let β : StatedSp n K := ⟨b, hb⟩
  have hoddβ : Odd (orderOf β) := by
    change Odd (orderOf (⟨b, hb⟩ : StatedSp n K))
    rw [Subgroup.orderOf_mk b hb]
    exact hodd
  have H : AltPrimaryData (spForm n K) (spLin n K β) := ggJS1_altPrimaryData β hoddβ
  have hsq : Squarefree (minpoly K (spEnd β)) := ggJS1_squarefree_minpoly_spEnd β hoddβ
  obtain ⟨a, ha, hae⟩ := ggJS1_prim_idem_eq_primaryProjection β hoddβ he
  obtain ⟨a', ha', ha'e⟩ := ggJS1_prim_idem_eq_primaryProjection β hoddβ he'
  have hεadj : formAdj (RingHom.id K) (ggJS1_J n K) ε = ε := hε.2.2.2.1
  obtain ⟨hrec, hane⟩ := ggJS1_reciprocal_of_prim_pair β hoddβ ha ha' hae ha'e hεe hne
    he.2.2.1 he'.2.2.1 he.1 he.2.1 hε.2.2.2.2 hεadj
  haveI : Fact (Irreducible a) := ⟨irreducible_of_mem_primaryFactors ha⟩
  let E : Type := AdjoinRoot a
  let d : ℕ := a.natDegree
  let m : ℕ := Module.finrank E (primaryComponent (spEnd β) a)
  haveI : Finite E := Module.finite_of_finite K
  haveI : Fintype E := Fintype.ofFinite E
  have hsub : glBlockCentralizer (StatedSp n K).subtype ({b} : Set (GL (Fin n ⊕ Fin n) K)) ε =
      spSupported β {a, reciprocalPolynomial a} :=
    ggJS1_glBlockCentralizer_eq_spSupported β hoddβ ha hane hae
      (by rw [← hrec]; exact ha'e) hεe
  have htoLin_eps : Matrix.toLin' ε =
      primaryProjection (spEnd β) a + primaryProjection (spEnd β) (reciprocalPolynomial a) := by
    have hadd : Matrix.toLin' ε = Matrix.toLin' e + Matrix.toLin' e' := by
      rw [hεe]
      exact Matrix.toLin'.map_add e e'
    rw [hadd, ← ggJS1_toLinAlgEquiv'_eq_toLin' e, ← ggJS1_toLinAlgEquiv'_eq_toLin' e',
      hae, ha'e, hrec]
  have hrange : LinearMap.range (Matrix.toLin' ε) =
      primaryComponent (spEnd β) a ⊔ primaryComponent (spEnd β) (reciprocalPolynomial a) := by
    rw [htoLin_eps]
    apply le_antisymm
    · rintro y ⟨v, rfl⟩
      rw [LinearMap.add_apply]
      exact Submodule.add_mem_sup (primaryProjection_mem hsq ha v)
        (primaryProjection_mem hsq (H.reciprocal_mem ha) v)
    · intro y hy
      refine ⟨y, ?_⟩
      obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hy
      rw [LinearMap.add_apply, map_add, map_add, primaryProjection_of_mem hsq ha hu,
        primaryProjection_of_mem_ne hsq ha (H.reciprocal_mem ha) (Ne.symm hane) hw,
        primaryProjection_of_mem_ne hsq (H.reciprocal_mem ha) ha hane hu,
        primaryProjection_of_mem hsq (H.reciprocal_mem ha) hw, add_zero, zero_add]
  have hfin : Module.finrank K (LinearMap.range (Matrix.toLin' ε)) =
      Module.finrank K (primaryComponent (spEnd β) a) +
      Module.finrank K (primaryComponent (spEnd β) (reciprocalPolynomial a)) := by
    rw [hrange, ← Submodule.finrank_sup_add_finrank_inf_eq]
    have hinf : primaryComponent (spEnd β) a ⊓
        primaryComponent (spEnd β) (reciprocalPolynomial a) = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro v hv
      obtain ⟨hv1, hv2⟩ := Submodule.mem_inf.mp hv
      have h1 := primaryProjection_of_mem hsq ha hv1
      have h2 := primaryProjection_of_mem hsq (H.reciprocal_mem ha) hv2
      have hzero : primaryProjection (spEnd β) a v = 0 := by
        rw [← h2, ← Module.End.mul_apply,
          ggJS1_primaryProjection_mul_eq_zero hsq ha (H.reciprocal_mem ha) hane,
          LinearMap.zero_apply]
      rw [h1] at hzero
      exact hzero
    rw [hinf]
    simp
  have hfa : Module.finrank K (primaryComponent (spEnd β) a) = d * m := by
    rw [finrank_primaryComponent (spEnd β) a]
  have hfr : Module.finrank K (primaryComponent (spEnd β) (reciprocalPolynomial a)) = d * m := by
    rw [H.finrank_reciprocal ha, hfa]
  have hdim : 2 * d * m = Module.finrank K (LinearMap.range (Matrix.toLin' ε)) := by
    rw [hfin, hfa, hfr]
    ring
  have hd : 1 ≤ d := by
    show 1 ≤ a.natDegree
    have hpos : 0 < a.natDegree := Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors ha)
    omega
  have hcard : Fintype.card E = Fintype.card K ^ d := by
    rw [Fintype.card_eq_nat_card, Module.natCard_eq_pow_finrank (K := K),
      finrank_adjoinRoot, Nat.card_eq_fintype_card]
  have hL := supportedUnitary_le_sesq β {a, reciprocalPolynomial a}
  let eG : ↥(glBlockCentralizer (StatedSp n K).subtype ({b} : Set (GL (Fin n ⊕ Fin n) K)) ε) ≃*
      GL (Fin m) E :=
    (MulEquiv.subgroupCongr hsub).trans
      ((comapSpLinEquiv (supportedUnitary (spForm n K) (spLin n K β)
        {a, reciprocalPolynomial a}) hL).trans ((H.pairedEquiv ha hane).trans
        (Units.mapEquiv (LinearMap.toMatrixAlgEquiv
          (Module.finBasis E (primaryComponent (spEnd β) a))).toMulEquiv)))
  have hblockdeg : blockDegree (Algebra.adjoin K
      (Units.val '' ({b} : Set (GL (Fin n ⊕ Fin n) K)))) e = d := by
    show blockDegree (Algebra.adjoin K
      (Units.val '' ({b} : Set (GL (Fin n ⊕ Fin n) K)))) e = a.natDegree
    exact ggJS1_blockDegree_eq_natDegree β hoddβ ha hae
  exact ⟨d, m, E, inferInstance, inferInstance, hd, hcard, hdim, hblockdeg, ⟨eG⟩⟩

private lemma ggJS1_linear_old {K : Type} [Field K] [Fintype K] [CharP K 2] {n : ℕ}
    (b : GL (Fin n ⊕ Fin n) K) (hb : b ∈ StatedSp n K) (hodd : Odd (orderOf b))
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    (hε : IsPrimAdjIdemIn (RingHom.id K)
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL (Fin n ⊕ Fin n) K)))) ε)
    (hp : ∃ e e' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K,
      IsPrimIdemIn (Algebra.adjoin K (Units.val '' ({b} : Set (GL (Fin n ⊕ Fin n) K)))) e ∧
      IsPrimIdemIn (Algebra.adjoin K (Units.val '' ({b} : Set (GL (Fin n ⊕ Fin n) K)))) e' ∧
      e ≠ e' ∧ ε = e + e') :
    ∃ (d m : ℕ) (E : Type) (_ : Field E) (_ : Fintype E), 1 ≤ d ∧
      Fintype.card E = Fintype.card K ^ d ∧
      2 * d * m = Module.finrank K (LinearMap.range (Matrix.toLin' ε)) ∧
      Nonempty (↥(glBlockCentralizer (StatedSp n K).subtype {b} ε) ≃* GL (Fin m) E) := by
  obtain ⟨e, e', he, he', hne, hεe⟩ := hp
  obtain ⟨d, m, E, hE, hF, hd, hcard, hdim, -, hiso⟩ :=
    ggJS1_linear_strong b hb hodd hε he he' hne hεe
  exact ⟨d, m, E, hE, hF, hd, hcard, hdim, hiso⟩

theorem blockGroup_iso_Sp_linear {K : Type} [Field K] [Fintype K] [CharP K 2] {n : ℕ}
    (b : GL (Fin n ⊕ Fin n) K) (hb : b ∈ StatedSp n K) (hodd : Odd (orderOf b))
    {ε e e' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    (hε : IsPrimAdjIdemIn (RingHom.id K)
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL (Fin n ⊕ Fin n) K)))) ε)
    (he : IsPrimIdemIn (Algebra.adjoin K (Units.val '' ({b} : Set (GL (Fin n ⊕ Fin n) K)))) e)
    (he' : IsPrimIdemIn (Algebra.adjoin K (Units.val '' ({b} : Set (GL (Fin n ⊕ Fin n) K)))) e')
    (hne : e ≠ e') (hεe : ε = e + e') :
    ∃ (d m : ℕ) (E : Type) (_ : Field E) (_ : Fintype E), 1 ≤ d ∧
      Fintype.card E = Fintype.card K ^ d ∧
      2 * d * m = Module.finrank K (LinearMap.range (Matrix.toLin' ε)) ∧
      blockDegree (Algebra.adjoin K (Units.val '' ({b} : Set (GL (Fin n ⊕ Fin n) K)))) e = d ∧
      Nonempty (↥(glBlockCentralizer (StatedSp n K).subtype {b} ε) ≃* GL (Fin m) E) :=
  ggJS1_linear_strong b hb hodd hε he he' hne hεe

end CFSG.StandardType.ClassicalBlocks
