module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelSelfDualTwoPSp
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelSelfDualTwoOmega
public import CFSG.RankThree.PartOne.CTP.SpinCenterEven
public import CFSG.RankThree.GF2n.Smith81.Orth28Omega
public import CFSG.ClassicalGroups.Orthogonal.RootGroupNormalizer
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting

public section

namespace CFSG.StandardType.ClassicalPosition

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos

private noncomputable def bmstm_reindexGL {F : Type} [Field F] {N N' : Type} [Fintype N]
    [DecidableEq N]
    [Fintype N'] [DecidableEq N'] (σ : N ≃ N') : GL N F ≃* GL N' F :=
  Units.mapEquiv (Matrix.reindexAlgEquiv F F σ).toMulEquiv

private theorem bmstm_reindex_mul {F : Type} [Field F] {N N' : Type} [Fintype N] [DecidableEq N]
    [Fintype N'] [DecidableEq N'] (σ : N ≃ N') (A B : Matrix N N F) :
    Matrix.reindex σ σ (A * B) = Matrix.reindex σ σ A * Matrix.reindex σ σ B := by
  change (Matrix.reindexAlgEquiv F F σ) (A * B) =
    (Matrix.reindexAlgEquiv F F σ) A * (Matrix.reindexAlgEquiv F F σ) B
  rw [map_mul]

private theorem bmstm_reindex_transpose {F : Type} [Field F] {N N' : Type} [Fintype N]
    [DecidableEq N] [Fintype N'] [DecidableEq N'] (σ : N ≃ N') (A : Matrix N N F) :
    Matrix.transpose (Matrix.reindex σ σ A) = Matrix.reindex σ σ (Matrix.transpose A) := by
  ext i j
  simp [Matrix.reindex_apply, Matrix.transpose_apply]

private theorem bmstm_reindex_mulVec {F : Type} [Semiring F] {N N' : Type} [Fintype N]
    [DecidableEq N] [Fintype N'] [DecidableEq N'] (σ : N ≃ N') (A : Matrix N N F) (v : N' → F) :
    Matrix.mulVec (Matrix.reindex σ σ A) v = (Matrix.mulVec A (v ∘ σ)) ∘ σ.symm := by
  funext i
  show (∑ j : N', A (σ.symm i) (σ.symm j) * v j) = ∑ k : N, A (σ.symm i) k * v (σ k)
  have h := (Equiv.sum_comp σ (fun j : N' => A (σ.symm i) (σ.symm j) * v j)).symm
  simpa using h

private theorem bmstm_reindex_mulVec' {F : Type} [Semiring F] {N N' : Type} [Fintype N]
    [DecidableEq N] [Fintype N'] [DecidableEq N'] (σ : N ≃ N') (G : Matrix N N F) (b : N → F) :
    (Matrix.mulVec G b) ∘ σ.symm = Matrix.mulVec (Matrix.reindex σ σ G) (b ∘ σ.symm) := by
  have h := bmstm_reindex_mulVec σ G (b ∘ σ.symm)
  rw [show (b ∘ σ.symm) ∘ σ = b from by ext x; simp] at h
  exact h.symm

private theorem bmstm_reindex_vecMulVec {F : Type} [Semiring F] {N N' : Type} [Fintype N]
    [DecidableEq N] [Fintype N'] [DecidableEq N'] (σ : N ≃ N') (a b : N → F) :
    Matrix.reindex σ σ (Matrix.vecMulVec a b) =
      Matrix.vecMulVec (a ∘ σ.symm) (b ∘ σ.symm) := by
  ext i j
  simp [Matrix.reindex_apply, Matrix.vecMulVec_apply]

private theorem bmstm_formAdj_reindex {F : Type} [Field F] {N N' : Type} [Fintype N]
    [DecidableEq N] [Fintype N'] [DecidableEq N'] (σ : N ≃ N') (G e : Matrix N N F) :
    formAdj (RingHom.id F) (Matrix.reindex σ σ G) (Matrix.reindex σ σ e) =
      Matrix.reindex σ σ (formAdj (RingHom.id F) G e) := by
  simp only [formAdj,
    show (⇑(RingHom.id F) : F → F) = id from rfl, Matrix.map_id]
  rw [Matrix.transpose_reindex, Matrix.inv_reindex]
  rw [← bmstm_reindex_mul σ G⁻¹ (Matrix.transpose e),
    ← bmstm_reindex_mul σ (G⁻¹ * Matrix.transpose e) G]

private lemma bmstm_isPrimIdemIn_map {F : Type} [Field F] {N N' : Type} [Fintype N]
    [DecidableEq N] [Fintype N'] [DecidableEq N'] (ψ : Matrix N N F ≃ₐ[F] Matrix N' N' F)
    (A : Subalgebra F (Matrix N N F)) (e : Matrix N N F) :
    IsPrimIdemIn (A.map ψ) (ψ e) ↔ IsPrimIdemIn A e := by
  constructor
  · rintro ⟨hmem, hidem, hne, hmin⟩
    obtain ⟨a, ha, hae⟩ := Subalgebra.mem_map.mp hmem
    have heA : e ∈ A := by
      have : a = e := ψ.injective hae
      rwa [this] at ha
    refine ⟨heA, ?_, ?_, ?_⟩
    · show e * e = e
      apply ψ.injective
      rw [map_mul, hidem.eq]
    · intro h0
      exact hne (by rw [h0, map_zero])
    · intro e' he'A he'idem he'e
      have h1 : ψ e' ∈ A.map ψ := Subalgebra.mem_map.mpr ⟨e', he'A, rfl⟩
      have h2 : IsIdempotentElem (ψ e') := by
        show ψ e' * ψ e' = ψ e'
        rw [← map_mul, he'idem.eq]
      have h3 : ψ e' * ψ e = ψ e' := by rw [← map_mul, he'e]
      rcases hmin (ψ e') h1 h2 h3 with h | h
      · left; apply ψ.injective; rw [h, map_zero]
      · right; apply ψ.injective; exact h
  · rintro ⟨hmem, hidem, hne, hmin⟩
    refine ⟨Subalgebra.mem_map.mpr ⟨e, hmem, rfl⟩, ?_, ?_, ?_⟩
    · show ψ e * ψ e = ψ e
      rw [← map_mul, hidem.eq]
    · intro h0
      exact hne (ψ.injective (by rw [h0, map_zero]))
    · intro e' he' hidem' he'e
      obtain ⟨a, ha, hae⟩ := Subalgebra.mem_map.mp he'
      subst hae
      have h_idem : IsIdempotentElem a := by
        show a * a = a
        apply ψ.injective
        rw [map_mul]
        simpa using hidem'.eq
      have h_ae : a * e = a := by
        apply ψ.injective
        rw [map_mul]
        simpa using he'e
      rcases hmin a ha h_idem h_ae with h | h
      · left; simpa using congrArg ψ h
      · right; simpa using congrArg ψ h

private lemma bmstm_blockDegree_map {F : Type} [Field F] {N N' : Type} [Fintype N]
    [DecidableEq N] [Fintype N'] [DecidableEq N'] (ψ : Matrix N N F ≃ₐ[F] Matrix N' N' F)
    (A : Subalgebra F (Matrix N N F)) (e : Matrix N N F) :
    blockDegree (A.map ψ) (ψ e) = blockDegree A e := by
  unfold blockDegree
  have hcomp : (Subalgebra.toSubmodule (A.map ψ)).map (LinearMap.mulRight F (ψ e)) =
      ((Subalgebra.toSubmodule A).map (LinearMap.mulRight F e)).map ψ.toLinearMap := by
    have hM : Subalgebra.toSubmodule (A.map ψ) = (Subalgebra.toSubmodule A).map ψ.toLinearMap := by
      rw [Subalgebra.map_toSubmodule]
      rfl
    rw [hM]
    rw [← Submodule.map_comp ψ.toLinearMap (LinearMap.mulRight F (ψ e)) (Subalgebra.toSubmodule A),
      ← Submodule.map_comp (LinearMap.mulRight F e) ψ.toLinearMap (Subalgebra.toSubmodule A)]
    congr 1
    ext a
    simp [LinearMap.mulRight_apply, map_mul]
  rw [hcomp, LinearEquiv.finrank_map_eq]

private lemma bmstm_isComponentOf_map {X Y : Type} [Group X] [Group Y] (φ : X ≃* Y)
    {L K : Subgroup X} (h : IsComponentOf L K) :
    IsComponentOf (L.map φ.toMonoidHom) (K.map φ.toMonoidHom) :=
  ⟨Subgroup.map_mono h.1, h.2.1.map φ.toMonoidHom,
    CFSG.Assembly.IsQuasisimple.of_mulEquiv (MulEquiv.subgroupMap φ L).symm h.2.2⟩

private theorem bmstm_reindex_comp_symm {F : Type} [Field F] {N N' : Type} [Fintype N]
    [DecidableEq N] [Fintype N'] [DecidableEq N'] (σ : N ≃ N') (A : Matrix N N F) :
    Matrix.reindex σ.symm σ.symm (Matrix.reindex σ σ A) = A := by
  ext i j
  simp [Matrix.reindex_apply]

private lemma bmstm_mem_centralizer_map {F : Type} [Field F] {N N' : Type} [Fintype N]
    [DecidableEq N] [Fintype N'] [DecidableEq N'] (φ : GL N F ≃* GL N' F)
    (S : Set (GL N F)) (w : GL N F) :
    φ w ∈ Subgroup.centralizer (φ '' S) ↔ w ∈ Subgroup.centralizer S := by
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h s hs
    apply φ.injective
    rw [map_mul, map_mul]
    exact h (φ s) ⟨s, hs, rfl⟩
  · rintro h s' ⟨s, hs, rfl⟩
    rw [← map_mul, ← map_mul, h s hs]

private lemma bmstm_glFixing_map {F : Type} [Field F] {N N' : Type} [Fintype N]
    [DecidableEq N] [Fintype N'] [DecidableEq N'] (ψ : Matrix N N F ≃ₐ[F] Matrix N' N' F)
    (φ : GL N F ≃* GL N' F) (hφ : ∀ A, ((φ A : GL N' F) : Matrix N' N' F) = ψ A)
    (e : Matrix N N F) (w : GL N F) :
    φ w ∈ glFixing (1 - ψ e) ↔ w ∈ glFixing (1 - e) := by
  change ((φ w : GL N' F) : Matrix N' N' F) * (1 - ψ e) = 1 - ψ e ↔
    (w : Matrix N N F) * (1 - e) = 1 - e
  rw [hφ w]
  constructor
  · intro h
    apply ψ.injective
    rw [map_mul, map_sub, map_one, h]
  · intro h
    have h' := congrArg ψ h
    rw [map_mul, map_sub, map_one] at h'
    exact h'

private lemma bmstm_glBlockCentralizer_map {F : Type} [Field F] {N N' : Type} [Fintype N]
    [DecidableEq N] [Fintype N'] [DecidableEq N'] (ψ : Matrix N N F ≃ₐ[F] Matrix N' N' F)
    (φ : GL N F ≃* GL N' F) (hφ : ∀ A, ((φ A : GL N' F) : Matrix N' N' F) = ψ A)
    (H : Subgroup (GL N F)) (S : Set (GL N F)) (e : Matrix N N F) :
    glBlockCentralizer (H.map (φ : GL N F →* GL N' F)).subtype (φ '' S) (ψ e) =
      (glBlockCentralizer H.subtype S e).map (MulEquiv.subgroupMap φ H).toMonoidHom := by
  refine Subgroup.ext fun u => ?_
  rw [Subgroup.mem_map_equiv]
  have hw : ((H.map (φ : GL N F →* GL N' F)).subtype u : GL N' F) =
      φ (H.subtype ((MulEquiv.subgroupMap φ H).symm u)) := by
    have h1 : (MulEquiv.subgroupMap φ H) ((MulEquiv.subgroupMap φ H).symm u) = u :=
      MulEquiv.apply_symm_apply _ _
    conv_lhs => rw [← h1]
    rfl
  simp only [glBlockCentralizer, Subgroup.mem_comap, Subgroup.mem_inf]
  rw [hw]
  exact and_congr (bmstm_mem_centralizer_map φ S _) (bmstm_glFixing_map ψ φ hφ e _)

private lemma bmstm_reindex_vecMulVec_mulVec {F : Type} [Field F] {N N' : Type} [Fintype N]
    [DecidableEq N] [Fintype N'] [DecidableEq N'] (σ : N ≃ N') (G : Matrix N N F)
    (a b : N → F) :
    (Matrix.reindexAlgEquiv F F σ) (Matrix.vecMulVec a (Matrix.mulVec G b)) =
      Matrix.vecMulVec (a ∘ σ.symm) (Matrix.mulVec (Matrix.reindex σ σ G) (b ∘ σ.symm)) := by
  rw [Matrix.reindexAlgEquiv_apply, bmstm_reindex_vecMulVec, bmstm_reindex_mulVec']

private lemma bmstm_reindex_symm_vecMulVec_mulVec {F : Type} [Field F] {N N' : Type} [Fintype N]
    [DecidableEq N] [Fintype N'] [DecidableEq N'] (σ : N ≃ N') (G : Matrix N N F)
    (a b : N → F) :
    (Matrix.reindexAlgEquiv F F σ.symm)
        (Matrix.vecMulVec (a ∘ σ.symm) (Matrix.mulVec (Matrix.reindex σ σ G) (b ∘ σ.symm))) =
      Matrix.vecMulVec a (Matrix.mulVec G b) := by
  rw [Matrix.reindexAlgEquiv_apply, bmstm_reindex_vecMulVec]
  simp only [Equiv.symm_symm]
  rw [show (a ∘ σ.symm) ∘ σ = a from by ext x; simp,
    show ((Matrix.reindex σ σ G).mulVec (b ∘ σ.symm)) ∘ σ = Matrix.mulVec G b from by
      rw [← bmstm_reindex_mulVec' σ G b]; ext x; simp]

private lemma bmstm_altSiegelGroup_map {F : Type} [Field F] {N N' : Type} [Fintype N]
    [DecidableEq N] [Fintype N'] [DecidableEq N'] (σ : N ≃ N') (G : Matrix N N F)
    (a₁ a₂ : N → F) :
    (altSiegelGroup G a₁ a₂).map (bmstm_reindexGL σ).toMonoidHom =
      altSiegelGroup (Matrix.reindex σ σ G) (a₁ ∘ σ.symm) (a₂ ∘ σ.symm) := by
  unfold altSiegelGroup
  rw [MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨g₀, ⟨c, hc⟩, rfl⟩
    refine ⟨c, ?_⟩
    have hcoe : (((bmstm_reindexGL σ).toMonoidHom g₀ : GL N' F) : Matrix N' N' F) =
        (Matrix.reindexAlgEquiv F F σ) (g₀ : Matrix N N F) := rfl
    rw [hcoe, hc, map_add, map_one, map_smul, map_add,
      bmstm_reindex_vecMulVec_mulVec σ G a₁ a₂, bmstm_reindex_vecMulVec_mulVec σ G a₂ a₁]
  · rintro ⟨c, hc⟩
    refine ⟨(bmstm_reindexGL σ).symm g, ?_, by simp⟩
    refine ⟨c, ?_⟩
    have hcoe : (((bmstm_reindexGL σ).symm g : GL N F) : Matrix N N F) =
        (Matrix.reindexAlgEquiv F F σ).symm (g : Matrix N' N' F) := rfl
    rw [hcoe, Matrix.reindexAlgEquiv_symm, hc, map_add, map_one, map_smul, map_add,
      bmstm_reindex_symm_vecMulVec_mulVec σ G a₁ a₂,
      bmstm_reindex_symm_vecMulVec_mulVec σ G a₂ a₁]

private lemma bmstm_mem_center_map {X Y : Type} [Group X] [Group Y] (φ : X ≃* Y) {x : X} :
    φ x ∈ Subgroup.center Y ↔ x ∈ Subgroup.center X := by
  rw [Subgroup.mem_center_iff, Subgroup.mem_center_iff]
  constructor
  · intro h y
    apply φ.injective
    rw [map_mul, map_mul]
    exact h (φ y)
  · intro h y
    obtain ⟨y', rfl⟩ := φ.surjective y
    rw [← map_mul, ← map_mul]
    exact congrArg φ (h y')

private lemma bmstm_dotProduct_reindex {F : Type} [Field F] {N N' : Type} [Fintype N]
    [DecidableEq N] [Fintype N'] [DecidableEq N'] (σ : N ≃ N') (G : Matrix N N F)
    (a b : N → F) :
    (a ∘ σ.symm) ⬝ᵥ Matrix.mulVec (Matrix.reindex σ σ G) (b ∘ σ.symm) =
      a ⬝ᵥ Matrix.mulVec G b := by
  rw [← bmstm_reindex_mulVec']
  exact Equiv.sum_comp σ.symm (fun j => a j * Matrix.mulVec G b j)

private noncomputable def bmstm_e1 (n : ℕ) (hn : 1 ≤ n) : Fin (n - 1) ⊕ Fin 1 ≃ Fin n :=
  (finSumFinEquiv (m := n - 1) (n := 1)).trans (finCongr (by omega))

private noncomputable def bmstm_sigma (n : ℕ) (hn : 1 ≤ n) : (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) ≃
    (Fin n ⊕ Fin n) :=
  let A := Fin (n - 1)
  let B := Fin (n - 1)
  let C := Fin 1
  let D := Fin 1
  let g : Fin 2 ≃ C ⊕ D := (finSumFinEquiv (m := 1) (n := 1)).symm
  let step1 : A ⊕ (B ⊕ Fin 2) ≃ A ⊕ (B ⊕ (C ⊕ D)) :=
    Equiv.sumCongr (Equiv.refl A) (Equiv.sumCongr (Equiv.refl B) g)
  let shuffle : A ⊕ (B ⊕ (C ⊕ D)) ≃ (A ⊕ C) ⊕ (B ⊕ D) :=
    (((Equiv.sumCongr (Equiv.refl A) (Equiv.sumAssoc B C D).symm).trans
      (Equiv.sumCongr (Equiv.refl A) (Equiv.sumCongr (Equiv.sumComm B C) (Equiv.refl D)))).trans
      (Equiv.sumCongr (Equiv.refl A) (Equiv.sumAssoc C B D))).trans
      (Equiv.sumAssoc A C (B ⊕ D)).symm
  let step3 : (A ⊕ C) ⊕ (B ⊕ D) ≃ Fin n ⊕ Fin n :=
    Equiv.sumCongr (bmstm_e1 n hn) (bmstm_e1 n hn)
  step1.trans (shuffle.trans step3)

private noncomputable def bmstm_D (n f : ℕ) :
    Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
      (GaloisField 2 f) :=
  Matrix.diagonal fun x =>
    if x = Sum.inr (Sum.inr (1 : Fin 2)) then (minusCoeffs 2 f).1 else 1

private lemma bmstm_diag_mul {F : Type} [Field F] {ι : Type} [Fintype ι] [DecidableEq ι]
    (d : ι → F) (M : Matrix ι ι F) :
    Matrix.diagonal d * M * Matrix.diagonal d = Matrix.of (fun u v => d u * M u v * d v) := by
  ext u v
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.of_apply]
  rw [Finset.sum_eq_single v]
  · rw [if_pos rfl]
    rw [Finset.sum_eq_single u]
    · rw [if_pos rfl]
    · intro b _ hb; simp [if_neg (Ne.symm hb)]
    · intro h; exact absurd (Finset.mem_univ u) h
  · intro b _ hb; simp [if_neg hb]
  · intro h; exact absurd (Finset.mem_univ v) h

private lemma bmstm_e1_inj (n : ℕ) (hn : 1 ≤ n) {a b : Fin (n - 1) ⊕ Fin 1} :
    bmstm_e1 n hn a = bmstm_e1 n hn b ↔ a = b := (bmstm_e1 n hn).injective.eq_iff

private lemma bmstm_fin2_eq (u : Fin 2) : u = 0 ∨ u = 1 := by
  fin_cases u <;> simp

private lemma bmstm_sigma_inl (n : ℕ) (hn : 1 ≤ n) (i : Fin (n - 1)) :
    bmstm_sigma n hn (Sum.inl i) = Sum.inl (bmstm_e1 n hn (Sum.inl i)) := rfl

private lemma bmstm_sigma_inr_inl (n : ℕ) (hn : 1 ≤ n) (i : Fin (n - 1)) :
    bmstm_sigma n hn (Sum.inr (Sum.inl i)) = Sum.inr (bmstm_e1 n hn (Sum.inl i)) := rfl

private lemma bmstm_sigma_inr_inr_zero (n : ℕ) (hn : 1 ≤ n) :
    bmstm_sigma n hn (Sum.inr (Sum.inr (0 : Fin 2))) =
      Sum.inl (bmstm_e1 n hn (Sum.inr (0 : Fin 1))) := rfl

private lemma bmstm_sigma_inr_inr_one (n : ℕ) (hn : 1 ≤ n) :
    bmstm_sigma n hn (Sum.inr (Sum.inr (1 : Fin 2))) =
      Sum.inr (bmstm_e1 n hn (Sum.inr (0 : Fin 1))) := rfl

private lemma bmstm_J_inl_inr {n f : ℕ} (x y : Fin n) :
    (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
      (Sum.inl x) (Sum.inr y) = if x = y then 1 else 0 := by
  simp [Matrix.fromBlocks, Matrix.one_apply]

private lemma bmstm_J_inr_inl {n f : ℕ} (x y : Fin n) :
    (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
      (Sum.inr x) (Sum.inl y) = if x = y then -1 else 0 := by
  simp only [Matrix.fromBlocks, Matrix.of_apply, Sum.elim_inr, Sum.elim_inl]
  rw [Matrix.neg_apply, Matrix.one_apply]
  by_cases h : x = y <;> simp [h]

private lemma bmstm_J_inl_inl {n f : ℕ} (x y : Fin n) :
    (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
      (Sum.inl x) (Sum.inl y) = 0 := by
  simp [Matrix.fromBlocks]

private lemma bmstm_J_inr_inr {n f : ℕ} (x y : Fin n) :
    (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
      (Sum.inr x) (Sum.inr y) = 0 := by
  simp [Matrix.fromBlocks]

private lemma bmstm_G1_apply (n f : ℕ) (hn : 1 ≤ n) (u v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) :
    (Matrix.reindex (bmstm_sigma n hn).symm (bmstm_sigma n hn).symm
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)))
        u v =
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
        (bmstm_sigma n hn u) (bmstm_sigma n hn v) := by
  simp [Matrix.reindex_apply, Matrix.submatrix_apply]

private lemma bmstm_gram_polarMatrix (n f : ℕ) :
    LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin
          (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) =
      Matrix.of (fun u v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 =>
        QuadraticMap.polar
          (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)
          (Pi.single u 1) (Pi.single v 1)) := by
  ext u v
  rw [LinearMap.toMatrix₂'_apply, QuadraticMap.polarBilin_apply_apply, Matrix.of_apply]

private lemma bmstm_gram_scaleMatrix (n f : ℕ) (hn : 1 ≤ n) :
    Matrix.transpose (bmstm_D n f) *
        Matrix.reindex (bmstm_sigma n hn).symm (bmstm_sigma n hn).symm
          (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *
        bmstm_D n f =
      Matrix.of (fun u v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 =>
        (if u = Sum.inr (Sum.inr (1 : Fin 2)) then (minusCoeffs 2 f).1 else 1) *
          (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
            (bmstm_sigma n hn u) (bmstm_sigma n hn v) *
          (if v = Sum.inr (Sum.inr (1 : Fin 2)) then (minusCoeffs 2 f).1 else 1)) := by
  have hD : Matrix.transpose (bmstm_D n f) = bmstm_D n f := by
    ext a b
    simp only [Matrix.transpose_apply, bmstm_D, Matrix.diagonal_apply]
    by_cases h : a = b
    · subst h; simp
    · rw [if_neg (Ne.symm h), if_neg h]
  rw [hD]
  simp only [bmstm_D]
  rw [bmstm_diag_mul]
  ext u v
  simp only [Matrix.of_apply]
  rw [bmstm_G1_apply]

private lemma bmstm_gram_entries_inl (n f : ℕ) (hn : 1 ≤ n) (i : Fin (n - 1))
    (v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) :
    (if (Sum.inl i : Fin (n - 1) ⊕ (Fin (n - 1) ⊕ Fin 2)) = Sum.inr (Sum.inr (1 : Fin 2)) then
        (minusCoeffs 2 f).1 else 1) *
        (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
          (bmstm_sigma n hn (Sum.inl i)) (bmstm_sigma n hn v) *
        (if v = Sum.inr (Sum.inr (1 : Fin 2)) then (minusCoeffs 2 f).1 else 1) =
      QuadraticMap.polar
        (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)
        (Pi.single (Sum.inl i) 1) (Pi.single v 1) := by
  have hdi : (if (Sum.inl i : Fin (n - 1) ⊕ (Fin (n - 1) ⊕ Fin 2)) =
      Sum.inr (Sum.inr (1 : Fin 2)) then (minusCoeffs 2 f).1 else 1) = 1 := by
    rw [if_neg (by simp)]
  rw [hdi, one_mul]
  rcases v with j | (j | z)
  · have hdv : (if (Sum.inl j : Fin (n - 1) ⊕ (Fin (n - 1) ⊕ Fin 2)) =
        Sum.inr (Sum.inr (1 : Fin 2)) then (minusCoeffs 2 f).1 else 1) = 1 := by
      rw [if_neg (by simp)]
    rw [hdv, mul_one, bmstm_sigma_inl, bmstm_sigma_inl, bmstm_J_inl_inl]
    rw [Spin.polar_quadMinus]; simp [Pi.single_apply]
  · have hdv : (if (Sum.inr (Sum.inl j) : Fin (n - 1) ⊕ (Fin (n - 1) ⊕ Fin 2)) =
        Sum.inr (Sum.inr (1 : Fin 2)) then (minusCoeffs 2 f).1 else 1) = 1 := by
      rw [if_neg (by simp)]
    rw [hdv, mul_one, bmstm_sigma_inl, bmstm_sigma_inr_inl, bmstm_J_inl_inr]
    rw [Spin.polar_quadMinus]; simp [Pi.single_apply, bmstm_e1_inj, Sum.inl.injEq, eq_comm]
  · rcases bmstm_fin2_eq z with rfl | rfl
    · have hdv : (if (Sum.inr (Sum.inr (0 : Fin 2)) : Fin (n - 1) ⊕ (Fin (n - 1) ⊕ Fin 2)) =
          Sum.inr (Sum.inr (1 : Fin 2)) then (minusCoeffs 2 f).1 else 1) = 1 := by
        rw [if_neg (by simp)]
      rw [hdv, mul_one, bmstm_sigma_inl, bmstm_sigma_inr_inr_zero, bmstm_J_inl_inl]
      rw [Spin.polar_quadMinus]; simp [Pi.single_apply]
    · have hdv : (if (Sum.inr (Sum.inr (1 : Fin 2)) : Fin (n - 1) ⊕ (Fin (n - 1) ⊕ Fin 2)) =
          Sum.inr (Sum.inr (1 : Fin 2)) then (minusCoeffs 2 f).1 else 1) =
          (minusCoeffs 2 f).1 := by
        rw [if_pos rfl]
      rw [hdv, bmstm_sigma_inl, bmstm_sigma_inr_inr_one, bmstm_J_inl_inr]
      rw [Spin.polar_quadMinus]; simp [Pi.single_apply, bmstm_e1_inj, Sum.inl.injEq]

private lemma bmstm_neg_one_eq_one (f : ℕ) : (-1 : GaloisField 2 f) = 1 := by
  rw [neg_eq_iff_add_eq_zero]
  exact CharTwo.add_self_eq_zero 1

private lemma bmstm_gram_entries_inr_inl (n f : ℕ) (hn : 1 ≤ n) (i : Fin (n - 1))
    (v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) :
    (if (Sum.inr (Sum.inl i) : Fin (n - 1) ⊕ (Fin (n - 1) ⊕ Fin 2)) = Sum.inr (Sum.inr (1 : Fin 2))
        then (minusCoeffs 2 f).1 else 1) *
        (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
          (bmstm_sigma n hn (Sum.inr (Sum.inl i))) (bmstm_sigma n hn v) *
        (if v = Sum.inr (Sum.inr (1 : Fin 2)) then (minusCoeffs 2 f).1 else 1) =
      QuadraticMap.polar
        (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)
        (Pi.single (Sum.inr (Sum.inl i)) 1) (Pi.single v 1) := by
  have hdi : (if (Sum.inr (Sum.inl i) : Fin (n - 1) ⊕ (Fin (n - 1) ⊕ Fin 2)) =
      Sum.inr (Sum.inr (1 : Fin 2)) then (minusCoeffs 2 f).1 else 1) = 1 := by
    rw [if_neg (by simp)]
  rw [hdi, one_mul]
  rcases v with j | (j | z)
  · have hdv : (if (Sum.inl j : Fin (n - 1) ⊕ (Fin (n - 1) ⊕ Fin 2)) =
        Sum.inr (Sum.inr (1 : Fin 2)) then (minusCoeffs 2 f).1 else 1) = 1 := by
      rw [if_neg (by simp)]
    rw [hdv, mul_one, bmstm_sigma_inr_inl, bmstm_sigma_inl, bmstm_J_inr_inl]
    rw [Spin.polar_quadMinus]
    simp [Pi.single_apply, bmstm_e1_inj, Sum.inl.injEq, Sum.inr.injEq, eq_comm,
      bmstm_neg_one_eq_one]
  · have hdv : (if (Sum.inr (Sum.inl j) : Fin (n - 1) ⊕ (Fin (n - 1) ⊕ Fin 2)) =
        Sum.inr (Sum.inr (1 : Fin 2)) then (minusCoeffs 2 f).1 else 1) = 1 := by
      rw [if_neg (by simp)]
    rw [hdv, mul_one, bmstm_sigma_inr_inl, bmstm_sigma_inr_inl, bmstm_J_inr_inr]
    rw [Spin.polar_quadMinus]; simp [Pi.single_apply]
  · rcases bmstm_fin2_eq z with rfl | rfl
    · have hdv : (if (Sum.inr (Sum.inr (0 : Fin 2)) : Fin (n - 1) ⊕ (Fin (n - 1) ⊕ Fin 2)) =
          Sum.inr (Sum.inr (1 : Fin 2)) then (minusCoeffs 2 f).1 else 1) = 1 := by
        rw [if_neg (by simp)]
      rw [hdv, mul_one, bmstm_sigma_inr_inl, bmstm_sigma_inr_inr_zero, bmstm_J_inr_inl]
      rw [Spin.polar_quadMinus]
      simp [Pi.single_apply, bmstm_e1_inj, Sum.inl.injEq, Sum.inr.injEq]
    · have hdv : (if (Sum.inr (Sum.inr (1 : Fin 2)) : Fin (n - 1) ⊕ (Fin (n - 1) ⊕ Fin 2)) =
          Sum.inr (Sum.inr (1 : Fin 2)) then (minusCoeffs 2 f).1 else 1) =
          (minusCoeffs 2 f).1 := by
        rw [if_pos rfl]
      rw [hdv, bmstm_sigma_inr_inl, bmstm_sigma_inr_inr_one, bmstm_J_inr_inr]
      rw [Spin.polar_quadMinus]; simp [Pi.single_apply]

private lemma bmstm_gram_entries_inr_inr (n f : ℕ) (hn : 1 ≤ n) (z : Fin 2)
    (v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) :
    (if (Sum.inr (Sum.inr z) : Fin (n - 1) ⊕ (Fin (n - 1) ⊕ Fin 2)) = Sum.inr (Sum.inr (1 : Fin 2))
        then (minusCoeffs 2 f).1 else 1) *
        (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
          (bmstm_sigma n hn (Sum.inr (Sum.inr z))) (bmstm_sigma n hn v) *
        (if v = Sum.inr (Sum.inr (1 : Fin 2)) then (minusCoeffs 2 f).1 else 1) =
      QuadraticMap.polar
        (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)
        (Pi.single (Sum.inr (Sum.inr z)) 1) (Pi.single v 1) := by
  rcases bmstm_fin2_eq z with rfl | rfl
  · have hdz : (if (Sum.inr (Sum.inr (0 : Fin 2)) : Fin (n - 1) ⊕ (Fin (n - 1) ⊕ Fin 2)) = Sum.inr
      (Sum.inr (1 : Fin 2)) then (minusCoeffs 2 f).1 else 1) = 1 := by
      rw [if_neg (by simp)]
    rw [hdz, one_mul]
    rcases v with j | (j | w)
    · have hdv : (if (Sum.inl j : Fin (n - 1) ⊕ (Fin (n - 1) ⊕ Fin 2)) = Sum.inr (Sum.inr (1 : Fin
        2)) then (minusCoeffs 2 f).1 else 1) = 1 := by rw [if_neg (by simp)]
      rw [hdv, mul_one, bmstm_sigma_inr_inr_zero, bmstm_sigma_inl, bmstm_J_inl_inl]
      rw [Spin.polar_quadMinus]; simp [Pi.single_apply, CharTwo.two_eq_zero, CharTwo.two_eq_zero]
    · have hdv : (if (Sum.inr (Sum.inl j) : Fin (n - 1) ⊕ (Fin (n - 1) ⊕ Fin 2)) = Sum.inr (Sum.inr
        (1 : Fin 2)) then (minusCoeffs 2 f).1 else 1) = 1 := by rw [if_neg (by simp)]
      rw [hdv, mul_one, bmstm_sigma_inr_inr_zero, bmstm_sigma_inr_inl, bmstm_J_inl_inr]
      rw [Spin.polar_quadMinus]
      simp [Pi.single_apply, CharTwo.two_eq_zero, bmstm_e1_inj, Sum.inl.injEq, Sum.inr.injEq]
    · rcases bmstm_fin2_eq w with rfl | rfl
      · have hdv : (if (Sum.inr (Sum.inr (0 : Fin 2)) : Fin (n - 1) ⊕ (Fin (n - 1) ⊕ Fin 2)) =
          Sum.inr (Sum.inr (1 : Fin 2)) then (minusCoeffs 2 f).1 else 1) = 1 := by
            rw [if_neg (by simp)]
        rw [hdv, mul_one, bmstm_sigma_inr_inr_zero, bmstm_J_inl_inl]
        rw [Spin.polar_quadMinus]; simp [Pi.single_apply, CharTwo.two_eq_zero, CharTwo.two_eq_zero]
      · have hdv : (if (Sum.inr (Sum.inr (1 : Fin 2)) : Fin (n - 1) ⊕ (Fin (n - 1) ⊕ Fin 2)) =
          Sum.inr (Sum.inr (1 : Fin 2)) then (minusCoeffs 2 f).1 else 1) = (minusCoeffs 2 f).1 := by
          rw [if_pos rfl]
        rw [hdv, bmstm_sigma_inr_inr_zero, bmstm_sigma_inr_inr_one, bmstm_J_inl_inr]
        rw [Spin.polar_quadMinus]; simp [Pi.single_apply, CharTwo.two_eq_zero, bmstm_e1_inj]
  · have hdz : (if (Sum.inr (Sum.inr (1 : Fin 2)) : Fin (n - 1) ⊕ (Fin (n - 1) ⊕ Fin 2)) = Sum.inr
      (Sum.inr (1 : Fin 2)) then (minusCoeffs 2 f).1 else 1) = (minusCoeffs 2 f).1 := by
      rw [if_pos rfl]
    rw [hdz]
    rcases v with j | (j | w)
    · have hdv : (if (Sum.inl j : Fin (n - 1) ⊕ (Fin (n - 1) ⊕ Fin 2)) = Sum.inr (Sum.inr (1 : Fin
        2)) then (minusCoeffs 2 f).1 else 1) = 1 := by rw [if_neg (by simp)]
      rw [hdv, mul_one, bmstm_sigma_inr_inr_one, bmstm_sigma_inl, bmstm_J_inr_inl]
      rw [Spin.polar_quadMinus]
      simp [Pi.single_apply, CharTwo.two_eq_zero, bmstm_e1_inj, Sum.inl.injEq, Sum.inr.injEq,
          bmstm_neg_one_eq_one]
    · have hdv : (if (Sum.inr (Sum.inl j) : Fin (n - 1) ⊕ (Fin (n - 1) ⊕ Fin 2)) = Sum.inr (Sum.inr
        (1 : Fin 2)) then (minusCoeffs 2 f).1 else 1) = 1 := by rw [if_neg (by simp)]
      rw [hdv, mul_one, bmstm_sigma_inr_inr_one, bmstm_sigma_inr_inl, bmstm_J_inr_inr]
      rw [Spin.polar_quadMinus]; simp [Pi.single_apply, CharTwo.two_eq_zero, CharTwo.two_eq_zero]
    · rcases bmstm_fin2_eq w with rfl | rfl
      · have hdv : (if (Sum.inr (Sum.inr (0 : Fin 2)) : Fin (n - 1) ⊕ (Fin (n - 1) ⊕ Fin 2)) =
          Sum.inr (Sum.inr (1 : Fin 2)) then (minusCoeffs 2 f).1 else 1) = 1 := by
            rw [if_neg (by simp)]
        rw [hdv, mul_one, bmstm_sigma_inr_inr_one, bmstm_sigma_inr_inr_zero, bmstm_J_inr_inl]
        rw [Spin.polar_quadMinus]
        simp [Pi.single_apply, CharTwo.two_eq_zero, bmstm_e1_inj, bmstm_neg_one_eq_one]
      · have hdv : (if (Sum.inr (Sum.inr (1 : Fin 2)) : Fin (n - 1) ⊕ (Fin (n - 1) ⊕ Fin 2)) =
          Sum.inr (Sum.inr (1 : Fin 2)) then (minusCoeffs 2 f).1 else 1) = (minusCoeffs 2 f).1 := by
          rw [if_pos rfl]
        rw [hdv, bmstm_sigma_inr_inr_one, bmstm_J_inr_inr]
        rw [Spin.polar_quadMinus]; simp [Pi.single_apply, CharTwo.two_eq_zero, CharTwo.two_eq_zero]

private lemma bmstm_gram_std (n f : ℕ) (hn : 4 ≤ n) :
    LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin
          (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) =
      Matrix.transpose (bmstm_D n f) *
        Matrix.reindex (bmstm_sigma n (by omega)).symm (bmstm_sigma n (by omega)).symm
          (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *
        bmstm_D n f := by
  rw [bmstm_gram_polarMatrix, bmstm_gram_scaleMatrix (hn := by omega)]
  ext u v
  simp only [Matrix.of_apply]
  rcases u with i | (i | z)
  · exact (bmstm_gram_entries_inl n f (by omega) i v).symm
  · exact (bmstm_gram_entries_inr_inl n f (by omega) i v).symm
  · exact (bmstm_gram_entries_inr_inr n f (by omega) z v).symm

private lemma bmstm_gram (n f : ℕ) (hn : 4 ≤ n) :
    LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin
          (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) =
      Matrix.transpose (bmstm_D n f) *
        Matrix.reindex (bmstm_sigma n (by omega)).symm (bmstm_sigma n (by omega)).symm
          (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *
        bmstm_D n f :=
  bmstm_gram_std n f hn

private noncomputable def bmstm_isometryGroup {F : Type} [Field F] {ι : Type} [Fintype ι]
    [DecidableEq ι] (G : Matrix ι ι F) : Subgroup (GL ι F) where
  carrier := {A | Matrix.transpose (A : Matrix ι ι F) * G * (A : Matrix ι ι F) = G}
  mul_mem' := by
    intro A B hA hB
    show Matrix.transpose ((A * B : GL ι F) : Matrix ι ι F) * G *
      ((A * B : GL ι F) : Matrix ι ι F) = G
    rw [Units.val_mul, Matrix.transpose_mul]
    calc Matrix.transpose (B : Matrix ι ι F) * Matrix.transpose (A : Matrix ι ι F) * G *
          ((A : Matrix ι ι F) * (B : Matrix ι ι F))
        = Matrix.transpose (B : Matrix ι ι F) *
            (Matrix.transpose (A : Matrix ι ι F) * G * (A : Matrix ι ι F)) *
            (B : Matrix ι ι F) := by simp only [Matrix.mul_assoc]
      _ = G := by rw [hA, hB]
  one_mem' := by
    show Matrix.transpose ((1 : GL ι F) : Matrix ι ι F) * G * ((1 : GL ι F) : Matrix ι ι F) = G
    rw [Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
  inv_mem' := by
    intro A hA
    show Matrix.transpose ((A⁻¹ : GL ι F) : Matrix ι ι F) * G *
      ((A⁻¹ : GL ι F) : Matrix ι ι F) = G
    calc Matrix.transpose ((A⁻¹ : GL ι F) : Matrix ι ι F) * G * ((A⁻¹ : GL ι F) : Matrix ι ι F)
        = Matrix.transpose ((A⁻¹ : GL ι F) : Matrix ι ι F) *
            (Matrix.transpose (A : Matrix ι ι F) * G * (A : Matrix ι ι F)) *
            ((A⁻¹ : GL ι F) : Matrix ι ι F) := by rw [hA]
      _ = G := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel,
            Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]

private noncomputable def bmstm_G (n f : ℕ) :
    Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
      (GaloisField 2 f) :=
  LinearMap.toMatrix₂' (GaloisField 2 f)
    (QuadraticMap.polarBilin
      (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2))

private noncomputable def bmstm_H (n f : ℕ) (hn : 4 ≤ n) :
    Subgroup (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (GaloisField 2 f)) :=
  bmstm_isometryGroup (bmstm_G n f)

private lemma bmstm_hH (n f : ℕ) (hn : 4 ≤ n) (A : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
    (GaloisField 2 f)) :
    A ∈ bmstm_H n f hn ↔
      Matrix.transpose (A : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕
          Fin 2) (GaloisField 2 f)) * (LinearMap.toMatrix₂' (GaloisField 2 f)
              (QuadraticMap.polarBilin (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
                  (minusCoeffs 2 f).2))) *
        (A : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
            (GaloisField 2 f)) = (LinearMap.toMatrix₂' (GaloisField 2 f) (QuadraticMap.polarBilin
                (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2))) := by
  exact Iff.rfl

private lemma bmstm_dotProduct_reindex_pull {F : Type} [Field F] {N N' : Type} [Fintype N]
    [DecidableEq N] [Fintype N'] [DecidableEq N'] (σ : N ≃ N') (G : Matrix N N F)
    (a b : N' → F) :
    (a ∘ σ) ⬝ᵥ Matrix.mulVec G (b ∘ σ) =
      a ⬝ᵥ Matrix.mulVec (Matrix.reindex σ σ G) b := by
  have h := bmstm_dotProduct_reindex σ.symm (Matrix.reindex σ σ G) a b
  simpa [bmstm_reindex_comp_symm] using h

private lemma bmstm_map_subtype_subgroup {F : Type} [Field F] {N N' : Type} [Fintype N]
    [DecidableEq N] [Fintype N'] [DecidableEq N'] (σ : N ≃ N') (H : Subgroup (GL N F))
    (X : Subgroup ↥H) :
    Subgroup.map (bmstm_reindexGL σ).toMonoidHom (Subgroup.map H.subtype X) =
      Subgroup.map (H.map (bmstm_reindexGL σ).toMonoidHom).subtype
        (Subgroup.map (MulEquiv.subgroupMap (bmstm_reindexGL σ) H).toMonoidHom X) := by
  rw [Subgroup.map_map X (bmstm_reindexGL σ).toMonoidHom H.subtype,
    Subgroup.map_map X (H.map (bmstm_reindexGL σ).toMonoidHom).subtype
      (MulEquiv.subgroupMap (bmstm_reindexGL σ) H).toMonoidHom]
  rfl

private lemma bmstm_isometryGroup_map {F : Type} [Field F] {N N' : Type} [Fintype N]
    [DecidableEq N] [Fintype N'] [DecidableEq N'] (σ : N ≃ N') (G : Matrix N N F) :
    (bmstm_isometryGroup G).map (bmstm_reindexGL σ).toMonoidHom =
      bmstm_isometryGroup (Matrix.reindex σ σ G) := by
  apply le_antisymm
  · rintro B ⟨A, hA, rfl⟩
    show Matrix.transpose (((bmstm_reindexGL σ) A : GL N' F) : Matrix N' N' F) *
        Matrix.reindex σ σ G * (((bmstm_reindexGL σ) A : GL N' F) : Matrix N' N' F) =
      Matrix.reindex σ σ G
    rw [show (((bmstm_reindexGL σ) A : GL N' F) : Matrix N' N' F) =
        Matrix.reindex σ σ (A : Matrix N N F) from rfl,
      bmstm_reindex_transpose, ← bmstm_reindex_mul, ← bmstm_reindex_mul, hA]
  · rintro B hB
    refine ⟨(bmstm_reindexGL σ).symm B, ?_, by simp⟩
    show Matrix.transpose (((bmstm_reindexGL σ).symm B : GL N F) : Matrix N N F) * G *
        (((bmstm_reindexGL σ).symm B : GL N F) : Matrix N N F) = G
    have hcoe : (((bmstm_reindexGL σ).symm B : GL N F) : Matrix N N F) =
        Matrix.reindex σ.symm σ.symm (B : Matrix N' N' F) := rfl
    rw [hcoe]
    have h' := congrArg (fun M => Matrix.reindex σ.symm σ.symm M) hB
    rwa [bmstm_reindex_mul, bmstm_reindex_mul, ← bmstm_reindex_transpose,
      bmstm_reindex_comp_symm] at h'

private lemma bmstm_hnd (n f : ℕ) :
    (QuadraticMap.polarBilin (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2
        f).2)).Nondegenerate :=
  Spin.nondegenerate_polarBilin_quadMinus_of_finite n (GaloisField 2 f) (minusCoeffs_irr 2 f)

private lemma bmstm_hinj (n f : ℕ) : Function.Injective (Spin.spinMatrix (Spin.quadMinus n
    (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  exact Spin.ker_spinMatrix_quadMinus_eq_bot (minusCoeffs_irr 2 f) CharTwo.two_eq_zero

theorem range_spinAction_quadMinus_eq_omegaGroup (n f : ℕ) (hn : 4 ≤ n) :
    (Spin.spinAction (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2
        f).2)).range =
      CFSG.RankThree.OrthogonalInvolutions.omegaGroup (Spin.quadMinus n (GaloisField 2 f)
          (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)
          (Spin.nondegenerate_polarBilin_quadMinus_of_finite n (GaloisField 2 f)
            (minusCoeffs_irr 2 f)) := by
  rw [Spin.range_spinAction_quadMinus hn (minusCoeffs_irr 2 f)]
  refine le_antisymm (CFSG.ClassicalGroups.Orthogonal.elementaryGroup_le_omegaGroup _) ?_
  refine CFSG.RankThree.GF2n.Smith81.omegaGroup_le_elementaryGroup_of_four_le _ ?_
  simp [Module.finrank_pi, Fintype.card_sum]
  omega

private lemma bmstm_hcent (n f : ℕ) (hn : 4 ≤ n) :
    Subgroup.center ↥(spinGroup (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs
        2 f).2)) = ⊥ :=
  CFSG.RankThree.PartOne.CTP.center_spinGroup_quadMinus_eq_bot hn (minusCoeffs_irr 2 f)

private lemma bmstm_minusCoeffs_fst_ne_zero (f : ℕ) : (minusCoeffs 2 f).1 ≠ 0 := by
  intro hβ
  obtain ⟨s, hs⟩ := isSquare_of_charTwo' (minusCoeffs 2 f).2
  apply minusCoeffs_irr 2 f s
  rw [hβ]
  rw [hs]
  ring_nf
  simp [CharTwo.two_eq_zero]

private noncomputable def bmstm_Dunit (n f : ℕ) :
    GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (GaloisField 2 f) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (bmstm_D n f) (by
    rw [bmstm_D, Matrix.det_diagonal]
    rw [Finset.prod_eq_single (Sum.inr (Sum.inr (1 : Fin 2)))]
    · simp [bmstm_minusCoeffs_fst_ne_zero]
    · intro b _ hb; rw [if_neg hb]
    · intro h; exact absurd (Finset.mem_univ _) h)

private lemma bmstm_H_perm (n f : ℕ) (hn : 4 ≤ n) :
    CFSG.Open.StatedSp n (GaloisField 2 f) =
      ((CFSG.Open.StatedSp n (GaloisField 2 f)).map
        (bmstm_reindexGL (bmstm_sigma n (by omega))).symm.toMonoidHom).map
        (bmstm_reindexGL (bmstm_sigma n (by omega))).toMonoidHom := by
  rw [Subgroup.map_map]
  have h : (bmstm_reindexGL (bmstm_sigma n (by omega))).toMonoidHom.comp
      ((bmstm_reindexGL (bmstm_sigma n (by omega))).symm.toMonoidHom) =
      MonoidHom.id (GL (Fin n ⊕ Fin n) (GaloisField 2 f)) := by
    ext x; simp
  rw [h, Subgroup.map_id]

private lemma bmstm_statedSp_eq_isometryGroup (n f : ℕ) :
    CFSG.Open.StatedSp n (GaloisField 2 f) = bmstm_isometryGroup (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) := by
  ext A
  rw [CFSG.Open.StatedAPI.mem_statedSp_iff]
  exact Iff.rfl

private lemma bmstm_H_reindex_symm (n f : ℕ) (hn : 4 ≤ n) :
    (CFSG.Open.StatedSp n (GaloisField 2 f)).map
        (bmstm_reindexGL (bmstm_sigma n (by omega))).symm.toMonoidHom =
      bmstm_isometryGroup
        (Matrix.reindex (bmstm_sigma n (by
          omega)).symm (bmstm_sigma n (by
            omega)).symm (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
                (GaloisField 2 f))) := by
  rw [bmstm_statedSp_eq_isometryGroup n f]
  exact bmstm_isometryGroup_map (bmstm_sigma n (by omega)).symm
    (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))

private lemma bmstm_conj_coe {F : Type} [Field F] {N : Type} [Fintype N] [DecidableEq N]
    (D A : GL N F) :
    ((MulAut.conj D A : GL N F) : Matrix N N F) =
      (D : Matrix N N F) * (A : Matrix N N F) * ((D : Matrix N N F))⁻¹ := by
  simp [MulAut.conj_apply]

private lemma bmstm_transpose_inv_mul_self {F : Type} [Field F] {N : Type} [Fintype N]
    [DecidableEq N] (D : GL N F) :
    Matrix.transpose (((D⁻¹ : GL N F) : Matrix N N F)) *
      Matrix.transpose (D : Matrix N N F) = 1 := by
  rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]

private lemma bmstm_transpose_inv_coe {F : Type} [Field F] {N : Type} [Fintype N]
    [DecidableEq N] (D : GL N F) :
    Matrix.transpose (((D : Matrix N N F))⁻¹) =
      Matrix.transpose (((D⁻¹ : GL N F) : Matrix N N F)) := by
  rw [Matrix.GeneralLinearGroup.coe_inv D]

private lemma bmstm_transpose_conj_mul {F : Type} [Field F] {N : Type} [Fintype N]
    [DecidableEq N] (D A : GL N F) :
    Matrix.transpose ((D : Matrix N N F) * (A : Matrix N N F) * ((D : Matrix N N F))⁻¹) =
      Matrix.transpose (((D⁻¹ : GL N F) : Matrix N N F)) *
        Matrix.transpose (A : Matrix N N F) * Matrix.transpose (D : Matrix N N F) := by
  rw [Matrix.transpose_mul, Matrix.transpose_mul, bmstm_transpose_inv_coe D, Matrix.mul_assoc]

private lemma bmstm_scale_cancel {F : Type} [Field F] {N : Type} [Fintype N]
    [DecidableEq N] (D : GL N F) (G : Matrix N N F) (A : GL N F)
    (hA : Matrix.transpose (A : Matrix N N F) *
      (Matrix.transpose (D : Matrix N N F) * G * (D : Matrix N N F)) *
      (A : Matrix N N F) =
      Matrix.transpose (D : Matrix N N F) * G * (D : Matrix N N F)) :
    Matrix.transpose (((D⁻¹ : GL N F) : Matrix N N F)) *
      (Matrix.transpose (A : Matrix N N F) *
        (Matrix.transpose (D : Matrix N N F) * G * (D : Matrix N N F)) *
        (A : Matrix N N F)) * ((D : Matrix N N F))⁻¹ = G := by
  calc Matrix.transpose (((D⁻¹ : GL N F) : Matrix N N F)) *
        (Matrix.transpose (A : Matrix N N F) *
          (Matrix.transpose (D : Matrix N N F) * G * (D : Matrix N N F)) *
          (A : Matrix N N F)) * ((D : Matrix N N F))⁻¹
      = Matrix.transpose (((D⁻¹ : GL N F) : Matrix N N F)) *
          (Matrix.transpose (D : Matrix N N F) * G * (D : Matrix N N F)) *
          ((D : Matrix N N F))⁻¹ := by rw [hA]
    _ = (Matrix.transpose (((D⁻¹ : GL N F) : Matrix N N F)) *
          Matrix.transpose (D : Matrix N N F)) * G *
          ((D : Matrix N N F) * ((D : Matrix N N F))⁻¹) := by noncomm_ring
    _ = 1 * G * ((D : Matrix N N F) * ((D : Matrix N N F))⁻¹) := by
        rw [bmstm_transpose_inv_mul_self D]
    _ = 1 * G * 1 := by rw [← Matrix.GeneralLinearGroup.coe_inv D, Units.mul_inv D]
    _ = G := by rw [Matrix.one_mul, Matrix.mul_one]

private lemma bmstm_isometryGroup_scale_forward {F : Type} [Field F] {N : Type} [Fintype N]
    [DecidableEq N] (D : GL N F) (G : Matrix N N F) (A : GL N F)
    (hA : A ∈ bmstm_isometryGroup
      (Matrix.transpose (D : Matrix N N F) * G * (D : Matrix N N F))) :
    MulAut.conj D A ∈ bmstm_isometryGroup G := by
  show Matrix.transpose ((MulAut.conj D A : GL N F) : Matrix N N F) * G *
      ((MulAut.conj D A : GL N F) : Matrix N N F) = G
  rw [bmstm_conj_coe D A, bmstm_transpose_conj_mul D A]
  rw [show Matrix.transpose (((D⁻¹ : GL N F) : Matrix N N F)) *
      Matrix.transpose (A : Matrix N N F) * Matrix.transpose (D : Matrix N N F) * G *
      ((D : Matrix N N F) * (A : Matrix N N F) * ((D : Matrix N N F))⁻¹) =
      Matrix.transpose (((D⁻¹ : GL N F) : Matrix N N F)) *
      (Matrix.transpose (A : Matrix N N F) *
        (Matrix.transpose (D : Matrix N N F) * G * (D : Matrix N N F)) *
        (A : Matrix N N F)) * ((D : Matrix N N F))⁻¹ from by noncomm_ring]
  exact bmstm_scale_cancel D G A hA

private lemma bmstm_transpose_mul_inv {F : Type} [Field F] {N : Type} [Fintype N]
    [DecidableEq N] (D : GL N F) :
    Matrix.transpose (D : Matrix N N F) *
      Matrix.transpose (((D⁻¹ : GL N F) : Matrix N N F)) = 1 := by
  rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]

private lemma bmstm_inv_mul_self {F : Type} [Field F] {N : Type} [Fintype N]
    [DecidableEq N] (D : GL N F) :
    ((D : Matrix N N F))⁻¹ * (D : Matrix N N F) = 1 := by
  rw [← Matrix.GeneralLinearGroup.coe_inv D]
  exact Units.inv_mul D

private lemma bmstm_conj_scale_form {F : Type} [Field F] {N : Type} [Fintype N]
    [DecidableEq N] (D A : GL N F) (G : Matrix N N F) :
    Matrix.transpose ((D : Matrix N N F) * (A : Matrix N N F) * ((D : Matrix N N F))⁻¹) * G *
      ((D : Matrix N N F) * (A : Matrix N N F) * ((D : Matrix N N F))⁻¹) =
    Matrix.transpose (((D⁻¹ : GL N F) : Matrix N N F)) *
      (Matrix.transpose (A : Matrix N N F) *
        (Matrix.transpose (D : Matrix N N F) * G * (D : Matrix N N F)) *
        (A : Matrix N N F)) * ((D : Matrix N N F))⁻¹ := by
  rw [bmstm_transpose_conj_mul D A]
  noncomm_ring

private lemma bmstm_scale_uncancel {F : Type} [Field F] {N : Type} [Fintype N]
    [DecidableEq N] (D : GL N F) (G : Matrix N N F) (A : GL N F)
    (h : Matrix.transpose (((D⁻¹ : GL N F) : Matrix N N F)) *
      (Matrix.transpose (A : Matrix N N F) *
        (Matrix.transpose (D : Matrix N N F) * G * (D : Matrix N N F)) *
        (A : Matrix N N F)) * ((D : Matrix N N F))⁻¹ = G) :
    Matrix.transpose (A : Matrix N N F) *
      (Matrix.transpose (D : Matrix N N F) * G * (D : Matrix N N F)) *
      (A : Matrix N N F) = Matrix.transpose (D : Matrix N N F) * G * (D : Matrix N N F) := by
  have h3 : Matrix.transpose (D : Matrix N N F) *
      Matrix.transpose (((D⁻¹ : GL N F) : Matrix N N F)) = 1 := bmstm_transpose_mul_inv D
  have h4 : ((D : Matrix N N F))⁻¹ * (D : Matrix N N F) = 1 := bmstm_inv_mul_self D
  have key := congrArg (fun M => Matrix.transpose (D : Matrix N N F) * M *
    (D : Matrix N N F)) h
  conv_rhs => rw [← key]
  rw [show Matrix.transpose (D : Matrix N N F) *
      (Matrix.transpose (((D⁻¹ : GL N F) : Matrix N N F)) *
        (Matrix.transpose (A : Matrix N N F) *
          (Matrix.transpose (D : Matrix N N F) * G * (D : Matrix N N F)) *
          (A : Matrix N N F)) * ((D : Matrix N N F))⁻¹) * (D : Matrix N N F) =
      (Matrix.transpose (D : Matrix N N F) *
        Matrix.transpose (((D⁻¹ : GL N F) : Matrix N N F))) *
        (Matrix.transpose (A : Matrix N N F) *
          (Matrix.transpose (D : Matrix N N F) * G * (D : Matrix N N F)) *
          (A : Matrix N N F)) *
        (((D : Matrix N N F))⁻¹ * (D : Matrix N N F)) from by
    simp only [Matrix.mul_assoc]]
  rw [h3, h4, Matrix.one_mul, Matrix.mul_one]

private lemma bmstm_isometryGroup_scale_backward {F : Type} [Field F] {N : Type} [Fintype N]
    [DecidableEq N] (D : GL N F) (G : Matrix N N F) (A : GL N F)
    (hA : MulAut.conj D A ∈ bmstm_isometryGroup G) :
    A ∈ bmstm_isometryGroup (Matrix.transpose (D : Matrix N N F) * G * (D : Matrix N N F)) := by
  show Matrix.transpose (A : Matrix N N F) *
      (Matrix.transpose (D : Matrix N N F) * G * (D : Matrix N N F)) *
      (A : Matrix N N F) = Matrix.transpose (D : Matrix N N F) * G * (D : Matrix N N F)
  have hA' : Matrix.transpose ((MulAut.conj D A : GL N F) : Matrix N N F) * G *
      ((MulAut.conj D A : GL N F) : Matrix N N F) = G := hA
  rw [bmstm_conj_coe D A, bmstm_conj_scale_form D A G] at hA'
  exact bmstm_scale_uncancel D G A hA'

private lemma bmstm_isometryGroup_scale_iff {F : Type} [Field F] {N : Type} [Fintype N]
    [DecidableEq N] (D : GL N F) (G : Matrix N N F) (A : GL N F) :
    A ∈ bmstm_isometryGroup (Matrix.transpose (D : Matrix N N F) * G * (D : Matrix N N F)) ↔
      MulAut.conj D A ∈ bmstm_isometryGroup G := by
  exact ⟨bmstm_isometryGroup_scale_forward D G A, bmstm_isometryGroup_scale_backward D G A⟩

private lemma bmstm_conj_inv_conj_apply {G : Type} [Group G] (D A : G) :
    MulAut.conj D⁻¹ (MulAut.conj D A) = A := by
  rw [MulAut.conj_apply, MulAut.conj_apply]
  group

private lemma bmstm_conj_conj_inv_apply {G : Type} [Group G] (D B : G) :
    MulAut.conj D (MulAut.conj D⁻¹ B) = B := by
  rw [MulAut.conj_apply, MulAut.conj_apply]
  group

private lemma bmstm_mem_map_conj_inv {F : Type} [Field F] {N : Type} [Fintype N]
    [DecidableEq N] (D : GL N F) (G : Matrix N N F) (A : GL N F) :
    A ∈ (bmstm_isometryGroup G).map (MulAut.conj D⁻¹).toMonoidHom ↔
      MulAut.conj D A ∈ bmstm_isometryGroup G := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨B, hB, hBA⟩
    rw [← hBA]
    change MulAut.conj D (MulAut.conj D⁻¹ B) ∈ bmstm_isometryGroup G
    rw [bmstm_conj_conj_inv_apply D B]
    exact hB
  · intro hA
    exact ⟨MulAut.conj D A, hA, bmstm_conj_inv_conj_apply D A⟩

private lemma bmstm_isometryGroup_scale {F : Type} [Field F] {N : Type} [Fintype N]
    [DecidableEq N] (D : GL N F) (G : Matrix N N F) :
    bmstm_isometryGroup (Matrix.transpose (D : Matrix N N F) * G * (D : Matrix N N F)) =
      (bmstm_isometryGroup G).map (MulAut.conj D⁻¹).toMonoidHom := by
  ext A
  rw [bmstm_mem_map_conj_inv D G A]
  exact bmstm_isometryGroup_scale_iff D G A

private lemma bmstm_Dunit_coe (n f : ℕ) :
    ((bmstm_Dunit n f : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (GaloisField 2 f)) :
      Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
        (GaloisField 2 f)) = bmstm_D n f := rfl

private lemma bmstm_H_scale (n f : ℕ) (hn : 4 ≤ n) :
    bmstm_H n f hn =
      ((CFSG.Open.StatedSp n (GaloisField 2 f)).map
        (bmstm_reindexGL (bmstm_sigma n (by omega))).symm.toMonoidHom).map
        (MulAut.conj (bmstm_Dunit n f)⁻¹).toMonoidHom := by
  rw [bmstm_H, bmstm_G, bmstm_gram n f hn, ← bmstm_Dunit_coe n f]
  rw [bmstm_isometryGroup_scale (bmstm_Dunit n f)
    (Matrix.reindex (bmstm_sigma n (by omega)).symm (bmstm_sigma n (by omega)).symm
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)))]
  congr 1
  exact (bmstm_H_reindex_symm n f hn).symm

private lemma bmstm_mul_inv_self {F : Type} [Field F] {N : Type} [Fintype N]
    [DecidableEq N] (D : GL N F) :
    (D : Matrix N N F) * ((D : Matrix N N F))⁻¹ = 1 := by
  rw [← Matrix.GeneralLinearGroup.coe_inv D]
  exact Units.mul_inv D

private lemma bmstm_conjAlg_left_inv {F : Type} [Field F] {N : Type} [Fintype N]
    [DecidableEq N] (D : GL N F) (M : Matrix N N F) :
    ((D : Matrix N N F))⁻¹ * ((D : Matrix N N F) * M * ((D : Matrix N N F))⁻¹) *
      (D : Matrix N N F) = M := by
  rw [show ((D : Matrix N N F))⁻¹ * ((D : Matrix N N F) * M * ((D : Matrix N N F))⁻¹) *
      (D : Matrix N N F) =
      (((D : Matrix N N F))⁻¹ * (D : Matrix N N F)) * M *
        (((D : Matrix N N F))⁻¹ * (D : Matrix N N F)) from by noncomm_ring]
  rw [bmstm_inv_mul_self D, Matrix.one_mul, Matrix.mul_one]

private lemma bmstm_conjAlg_right_inv {F : Type} [Field F] {N : Type} [Fintype N]
    [DecidableEq N] (D : GL N F) (M : Matrix N N F) :
    (D : Matrix N N F) * (((D : Matrix N N F))⁻¹ * M * (D : Matrix N N F)) *
      ((D : Matrix N N F))⁻¹ = M := by
  rw [show (D : Matrix N N F) * (((D : Matrix N N F))⁻¹ * M * (D : Matrix N N F)) *
      ((D : Matrix N N F))⁻¹ =
      ((D : Matrix N N F) * ((D : Matrix N N F))⁻¹) * M *
        ((D : Matrix N N F) * ((D : Matrix N N F))⁻¹) from by noncomm_ring]
  rw [bmstm_mul_inv_self D, Matrix.one_mul, Matrix.mul_one]

private lemma bmstm_conjAlg_mul {F : Type} [Field F] {N : Type} [Fintype N]
    [DecidableEq N] (D : GL N F) (M P : Matrix N N F) :
    (D : Matrix N N F) * (M * P) * ((D : Matrix N N F))⁻¹ =
      ((D : Matrix N N F) * M * ((D : Matrix N N F))⁻¹) *
        ((D : Matrix N N F) * P * ((D : Matrix N N F))⁻¹) := by
  have h : ((D : Matrix N N F) * M * ((D : Matrix N N F))⁻¹) *
      ((D : Matrix N N F) * P * ((D : Matrix N N F))⁻¹) =
      (D : Matrix N N F) * M * (((D : Matrix N N F))⁻¹ * (D : Matrix N N F)) * P *
        ((D : Matrix N N F))⁻¹ := by noncomm_ring
  rw [h, bmstm_inv_mul_self D, Matrix.mul_one]
  noncomm_ring

private lemma bmstm_conjAlg_add {F : Type} [Field F] {N : Type} [Fintype N]
    [DecidableEq N] (D : GL N F) (M P : Matrix N N F) :
    (D : Matrix N N F) * (M + P) * ((D : Matrix N N F))⁻¹ =
      (D : Matrix N N F) * M * ((D : Matrix N N F))⁻¹ +
        (D : Matrix N N F) * P * ((D : Matrix N N F))⁻¹ := by
  rw [Matrix.mul_add, Matrix.add_mul]

private lemma bmstm_conjAlg_commutes {F : Type} [Field F] {N : Type} [Fintype N]
    [DecidableEq N] (D : GL N F) (c : F) :
    (D : Matrix N N F) * (algebraMap F (Matrix N N F) c) * ((D : Matrix N N F))⁻¹ =
      algebraMap F (Matrix N N F) c := by
  rw [← Algebra.commutes (R := F) (A := Matrix N N F) c (D : Matrix N N F),
    Matrix.mul_assoc, bmstm_mul_inv_self D, Matrix.mul_one]

private noncomputable def bmstm_conjAlg {F : Type} [Field F] {N : Type} [Fintype N]
    [DecidableEq N] (D : GL N F) : Matrix N N F ≃ₐ[F] Matrix N N F where
  toFun M := (D : Matrix N N F) * M * ((D : Matrix N N F))⁻¹
  invFun M := ((D : Matrix N N F))⁻¹ * M * (D : Matrix N N F)
  left_inv M := bmstm_conjAlg_left_inv D M
  right_inv M := bmstm_conjAlg_right_inv D M
  map_mul' M P := bmstm_conjAlg_mul D M P
  map_add' M P := bmstm_conjAlg_add D M P
  commutes' c := bmstm_conjAlg_commutes D c

private lemma bmstm_conjAlg_formAdj {F : Type} [Field F] {N : Type} [Fintype N]
    [DecidableEq N] (D : GL N F) (G e : Matrix N N F) :
    formAdj (RingHom.id F) (Matrix.transpose (D : Matrix N N F) * G * (D : Matrix N N F))
        (((D : Matrix N N F))⁻¹ * e * (D : Matrix N N F)) =
      ((D : Matrix N N F))⁻¹ * formAdj (RingHom.id F) G e * (D : Matrix N N F) := by
  have h1 : (Matrix.transpose (D : Matrix N N F))⁻¹ *
      Matrix.transpose (D : Matrix N N F) = 1 := by
    rw [← Matrix.transpose_nonsing_inv (D : Matrix N N F), ← Matrix.transpose_mul,
      ← Matrix.GeneralLinearGroup.coe_inv D, Units.mul_inv, Matrix.transpose_one]
  have h2 : Matrix.transpose (((D : Matrix N N F))⁻¹) *
      Matrix.transpose (D : Matrix N N F) = 1 := by
    rw [← Matrix.GeneralLinearGroup.coe_inv D, ← Matrix.transpose_mul, Units.mul_inv,
      Matrix.transpose_one]
  simp only [formAdj, show (⇑(RingHom.id F) : F → F) = id from rfl, Matrix.map_id]
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.transpose_mul, Matrix.transpose_mul]
  rw [show ((D : Matrix N N F))⁻¹ * (G⁻¹ * (Matrix.transpose (D : Matrix N N F))⁻¹) *
      (Matrix.transpose (D : Matrix N N F) *
        (Matrix.transpose (e : Matrix N N F) * Matrix.transpose (((D : Matrix N N F))⁻¹))) *
      (Matrix.transpose (D : Matrix N N F) * G * (D : Matrix N N F)) =
      ((D : Matrix N N F))⁻¹ * G⁻¹ *
        ((Matrix.transpose (D : Matrix N N F))⁻¹ * Matrix.transpose (D : Matrix N N F)) *
        Matrix.transpose (e : Matrix N N F) *
        (Matrix.transpose (((D : Matrix N N F))⁻¹) * Matrix.transpose (D : Matrix N N F)) *
        G * (D : Matrix N N F) from by noncomm_ring,
    h1, h2, Matrix.mul_one]
  noncomm_ring

private lemma bmstm_conjAlg_blockDegree {F : Type} [Field F] {N : Type} [Fintype N]
    [DecidableEq N] (D : GL N F) (A : Subalgebra F (Matrix N N F)) (e : Matrix N N F) :
    blockDegree (A.map (bmstm_conjAlg D)) (bmstm_conjAlg D e) = blockDegree A e := by
  exact bmstm_blockDegree_map (bmstm_conjAlg D) A e

private lemma bmstm_conjAlg_glBlockCentralizer {F : Type} [Field F] {N : Type} [Fintype N]
    [DecidableEq N] (D : GL N F) (H : Subgroup (GL N F)) (S : Set (GL N F))
    (e : Matrix N N F) :
    glBlockCentralizer (H.map (MulAut.conj D⁻¹ : GL N F →* GL N F)).subtype
        (MulAut.conj D⁻¹ '' S) (bmstm_conjAlg D⁻¹ e) =
      (glBlockCentralizer H.subtype S e).map
        (MulEquiv.subgroupMap (MulAut.conj D⁻¹) H).toMonoidHom :=
  bmstm_glBlockCentralizer_map (bmstm_conjAlg D⁻¹) (MulAut.conj D⁻¹)
    (fun A => by simp [bmstm_conjAlg, MulAut.conj_apply]) H S e

private lemma bmstm_conj_vecMulVec {F : Type} [Field F] {N : Type} [Fintype N] [DecidableEq N]
    (D : GL N F) (a u : N → F) :
    ((D : Matrix N N F))⁻¹ * Matrix.vecMulVec a u * (D : Matrix N N F) =
      Matrix.vecMulVec (Matrix.mulVec ((D : Matrix N N F))⁻¹ a)
        (Matrix.vecMul u (D : Matrix N N F)) := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]

private lemma bmstm_conjAlg_vecMulVec_mulVec {F : Type} [Field F] {N : Type} [Fintype N]
    [DecidableEq N] (D : GL N F) (G : Matrix N N F) (a b : N → F) :
    (bmstm_conjAlg D⁻¹) (Matrix.vecMulVec a (Matrix.mulVec G b)) =
      Matrix.vecMulVec (Matrix.mulVec ((D : Matrix N N F))⁻¹ a)
        (Matrix.mulVec (Matrix.transpose (D : Matrix N N F) * G * (D : Matrix N N F))
          (Matrix.mulVec ((D : Matrix N N F))⁻¹ b)) := by
  have hD : (bmstm_conjAlg D⁻¹) (Matrix.vecMulVec a (Matrix.mulVec G b)) =
      ((D : Matrix N N F))⁻¹ * Matrix.vecMulVec a (Matrix.mulVec G b) *
        (D : Matrix N N F) := by
    simp [bmstm_conjAlg, Matrix.GeneralLinearGroup.coe_inv]
  rw [hD, bmstm_conj_vecMulVec]
  congr 1
  rw [← Matrix.mulVec_transpose]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  congr 1
  congr 1
  rw [Matrix.mulVec_mulVec, bmstm_mul_inv_self D, Matrix.one_mulVec]

private lemma bmstm_conj_vecMulVec' {F : Type} [Field F] {N : Type} [Fintype N] [DecidableEq N]
    (D : GL N F) (a u : N → F) :
    (D : Matrix N N F) * Matrix.vecMulVec a u * ((D : Matrix N N F))⁻¹ =
      Matrix.vecMulVec (Matrix.mulVec (D : Matrix N N F) a)
        (Matrix.vecMul u ((D : Matrix N N F))⁻¹) := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]

private lemma bmstm_transpose_inv_mul_self' {F : Type} [Field F] {N : Type} [Fintype N]
    [DecidableEq N] (D : GL N F) :
    (Matrix.transpose (D : Matrix N N F))⁻¹ * Matrix.transpose (D : Matrix N N F) = 1 := by
  rw [← Matrix.transpose_nonsing_inv (D : Matrix N N F), ← Matrix.transpose_mul,
    ← Matrix.GeneralLinearGroup.coe_inv D, Units.mul_inv, Matrix.transpose_one]

private lemma bmstm_transpose_inv_mulVec {F : Type} [Field F] {N : Type} [Fintype N]
    [DecidableEq N] (D : GL N F) (v : N → F) :
    Matrix.mulVec (Matrix.transpose (D : Matrix N N F))⁻¹
      (Matrix.mulVec (Matrix.transpose (D : Matrix N N F)) v) = v := by
  rw [Matrix.mulVec_mulVec, bmstm_transpose_inv_mul_self' D, Matrix.one_mulVec]

private lemma bmstm_transpose_inv_mulVec_mulVec {F : Type} [Field F] {N : Type} [Fintype N]
    [DecidableEq N] (D : GL N F) (G : Matrix N N F) (b : N → F) :
    Matrix.mulVec (Matrix.transpose (D : Matrix N N F))⁻¹
      (Matrix.mulVec (Matrix.transpose (D : Matrix N N F) * G * (D : Matrix N N F)) b) =
      Matrix.mulVec G (Matrix.mulVec (D : Matrix N N F) b) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  exact bmstm_transpose_inv_mulVec D
    (Matrix.mulVec G (Matrix.mulVec (D : Matrix N N F) b))

private lemma bmstm_conjAlg_symm_vecMulVec_mulVec {F : Type} [Field F] {N : Type} [Fintype N]
    [DecidableEq N] (D : GL N F) (G : Matrix N N F) (a b : N → F) :
    (bmstm_conjAlg D) (Matrix.vecMulVec a
        (Matrix.mulVec (Matrix.transpose (D : Matrix N N F) * G * (D : Matrix N N F)) b)) =
      Matrix.vecMulVec (Matrix.mulVec (D : Matrix N N F) a)
        (Matrix.mulVec G (Matrix.mulVec (D : Matrix N N F) b)) := by
  have hD : (bmstm_conjAlg D) (Matrix.vecMulVec a
      (Matrix.mulVec (Matrix.transpose (D : Matrix N N F) * G * (D : Matrix N N F)) b)) =
      (D : Matrix N N F) * Matrix.vecMulVec a
        (Matrix.mulVec (Matrix.transpose (D : Matrix N N F) * G * (D : Matrix N N F)) b) *
        ((D : Matrix N N F))⁻¹ := by
    simp [bmstm_conjAlg, Matrix.GeneralLinearGroup.coe_inv]
  rw [hD, bmstm_conj_vecMulVec' D a
    (Matrix.mulVec (Matrix.transpose (D : Matrix N N F) * G * (D : Matrix N N F)) b)]
  congr 1
  rw [← Matrix.mulVec_transpose, Matrix.transpose_nonsing_inv]
  exact bmstm_transpose_inv_mulVec_mulVec D G b

private lemma bmstm_conjAlg_altSiegelGen_forward {F : Type} [Field F] {N : Type} [Fintype N]
    [DecidableEq N] (D : GL N F) (G : Matrix N N F) (a₁ a₂ : N → F) :
    ∀ g ∈ {g : GL N F | ∃ c : F, (g : Matrix N N F) =
        1 + c • (Matrix.vecMulVec a₁ (Matrix.mulVec G a₂) +
          Matrix.vecMulVec a₂ (Matrix.mulVec G a₁))},
      MulAut.conj D⁻¹ g ∈ {g : GL N F | ∃ c : F, (g : Matrix N N F) =
        1 + c • (Matrix.vecMulVec (Matrix.mulVec ((D : Matrix N N F))⁻¹ a₁)
            (Matrix.mulVec (Matrix.transpose (D : Matrix N N F) * G * (D : Matrix N N F))
              (Matrix.mulVec ((D : Matrix N N F))⁻¹ a₂)) +
          Matrix.vecMulVec (Matrix.mulVec ((D : Matrix N N F))⁻¹ a₂)
            (Matrix.mulVec (Matrix.transpose (D : Matrix N N F) * G * (D : Matrix N N F))
              (Matrix.mulVec ((D : Matrix N N F))⁻¹ a₁)))} := by
  rintro g ⟨c, hc⟩
  refine ⟨c, ?_⟩
  have hcoe : (((MulAut.conj D⁻¹) g : GL N F) : Matrix N N F) =
      (bmstm_conjAlg D⁻¹) (g : Matrix N N F) := by
    simp [bmstm_conjAlg, MulAut.conj_apply, Matrix.GeneralLinearGroup.coe_inv]
  rw [hcoe, hc]
  simp only [map_add, map_one, map_smul]
  rw [bmstm_conjAlg_vecMulVec_mulVec D G a₁ a₂,
    bmstm_conjAlg_vecMulVec_mulVec D G a₂ a₁]

private lemma bmstm_conjAlg_symm_coe {F : Type} [Field F] {N : Type} [Fintype N]
    [DecidableEq N] (D : GL N F) (g : GL N F) :
    (((MulAut.conj D⁻¹).symm g : GL N F) : Matrix N N F) =
      (bmstm_conjAlg D) (g : Matrix N N F) := by
  rw [show (MulAut.conj D⁻¹).symm = MulAut.conj D from by
    ext x; simp [MulAut.conj_apply]]
  simp [bmstm_conjAlg, MulAut.conj_apply, Matrix.GeneralLinearGroup.coe_inv]

private lemma bmstm_conjAlg_one_add_smul {F : Type} [Field F] {N : Type} [Fintype N]
    [DecidableEq N] (D : GL N F) (X : Matrix N N F) (c : F) :
    (bmstm_conjAlg D) (1 + c • X) = 1 + c • (bmstm_conjAlg D) X := by
  rw [map_add, map_one, map_smul]

private lemma bmstm_conjAlg_sum_vecMulVec {F : Type} [Field F] {N : Type} [Fintype N]
    [DecidableEq N] (D : GL N F) (G : Matrix N N F) (a₁ a₂ : N → F) :
    (bmstm_conjAlg D) (Matrix.vecMulVec (Matrix.mulVec ((D : Matrix N N F))⁻¹ a₁)
          (Matrix.mulVec (Matrix.transpose (D : Matrix N N F) * G * (D : Matrix N N F))
            (Matrix.mulVec ((D : Matrix N N F))⁻¹ a₂)) +
        Matrix.vecMulVec (Matrix.mulVec ((D : Matrix N N F))⁻¹ a₂)
          (Matrix.mulVec (Matrix.transpose (D : Matrix N N F) * G * (D : Matrix N N F))
            (Matrix.mulVec ((D : Matrix N N F))⁻¹ a₁))) =
      Matrix.vecMulVec a₁ (Matrix.mulVec G a₂) + Matrix.vecMulVec a₂ (Matrix.mulVec G a₁) := by
  rw [map_add,
    bmstm_conjAlg_symm_vecMulVec_mulVec D G (Matrix.mulVec ((D : Matrix N N F))⁻¹ a₁)
      (Matrix.mulVec ((D : Matrix N N F))⁻¹ a₂),
    bmstm_conjAlg_symm_vecMulVec_mulVec D G (Matrix.mulVec ((D : Matrix N N F))⁻¹ a₂)
      (Matrix.mulVec ((D : Matrix N N F))⁻¹ a₁)]
  simp only [Matrix.mulVec_mulVec, bmstm_mul_inv_self D, Matrix.one_mulVec]

private lemma bmstm_conjAlg_symm_gen {F : Type} [Field F] {N : Type} [Fintype N]
    [DecidableEq N] (D : GL N F) (G : Matrix N N F) (a₁ a₂ : N → F) (c : F) :
    (bmstm_conjAlg D) (1 + c • (Matrix.vecMulVec (Matrix.mulVec ((D : Matrix N N F))⁻¹ a₁)
          (Matrix.mulVec (Matrix.transpose (D : Matrix N N F) * G * (D : Matrix N N F))
            (Matrix.mulVec ((D : Matrix N N F))⁻¹ a₂)) +
        Matrix.vecMulVec (Matrix.mulVec ((D : Matrix N N F))⁻¹ a₂)
          (Matrix.mulVec (Matrix.transpose (D : Matrix N N F) * G * (D : Matrix N N F))
            (Matrix.mulVec ((D : Matrix N N F))⁻¹ a₁)))) =
      1 + c • (Matrix.vecMulVec a₁ (Matrix.mulVec G a₂) +
        Matrix.vecMulVec a₂ (Matrix.mulVec G a₁)) := by
  rw [bmstm_conjAlg_one_add_smul, bmstm_conjAlg_sum_vecMulVec D G a₁ a₂]

private lemma bmstm_conjAlg_altSiegelGen_backward {F : Type} [Field F] {N : Type} [Fintype N]
    [DecidableEq N] (D : GL N F) (G : Matrix N N F) (a₁ a₂ : N → F) :
    ∀ g ∈ {g : GL N F | ∃ c : F, (g : Matrix N N F) =
        1 + c • (Matrix.vecMulVec (Matrix.mulVec ((D : Matrix N N F))⁻¹ a₁)
            (Matrix.mulVec (Matrix.transpose (D : Matrix N N F) * G * (D : Matrix N N F))
              (Matrix.mulVec ((D : Matrix N N F))⁻¹ a₂)) +
          Matrix.vecMulVec (Matrix.mulVec ((D : Matrix N N F))⁻¹ a₂)
            (Matrix.mulVec (Matrix.transpose (D : Matrix N N F) * G * (D : Matrix N N F))
              (Matrix.mulVec ((D : Matrix N N F))⁻¹ a₁)))},
      (MulAut.conj D⁻¹).symm g ∈ {g : GL N F | ∃ c : F, (g : Matrix N N F) =
        1 + c • (Matrix.vecMulVec a₁ (Matrix.mulVec G a₂) +
          Matrix.vecMulVec a₂ (Matrix.mulVec G a₁))} := by
  rintro g ⟨c, hc⟩
  refine ⟨c, ?_⟩
  rw [bmstm_conjAlg_symm_coe D g, hc, bmstm_conjAlg_symm_gen D G a₁ a₂ c]

private lemma bmstm_conjAlg_altSiegelGroup {F : Type} [Field F] {N : Type} [Fintype N]
    [DecidableEq N] (D : GL N F) (G : Matrix N N F) (a₁ a₂ : N → F) :
    (altSiegelGroup G a₁ a₂).map (MulAut.conj D⁻¹).toMonoidHom =
      altSiegelGroup (Matrix.transpose (D : Matrix N N F) * G * (D : Matrix N N F))
        (Matrix.mulVec ((D : Matrix N N F))⁻¹ a₁)
        (Matrix.mulVec ((D : Matrix N N F))⁻¹ a₂) := by
  unfold altSiegelGroup
  rw [MonoidHom.map_closure]
  congr 1
  ext g'
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact bmstm_conjAlg_altSiegelGen_forward D G a₁ a₂ g hg
  · intro hg'
    refine ⟨(MulAut.conj D⁻¹).symm g', bmstm_conjAlg_altSiegelGen_backward D G a₁ a₂ g' hg', ?_⟩
    exact (MulAut.conj D⁻¹).apply_symm_apply g'

private lemma bmstm_conjAlg_dotProduct {F : Type} [Field F] {N : Type} [Fintype N]
    [DecidableEq N] (D : GL N F) (G : Matrix N N F) (a b : N → F) :
    Matrix.mulVec ((D : Matrix N N F))⁻¹ a ⬝ᵥ
        Matrix.mulVec (Matrix.transpose (D : Matrix N N F) * G * (D : Matrix N N F))
          (Matrix.mulVec ((D : Matrix N N F))⁻¹ b) =
      a ⬝ᵥ Matrix.mulVec G b := by
  have h1 : (Matrix.transpose (D : Matrix N N F) * G * (D : Matrix N N F)) *
      ((D : Matrix N N F))⁻¹ = Matrix.transpose (D : Matrix N N F) * G := by
    rw [Matrix.mul_assoc, bmstm_mul_inv_self D, Matrix.mul_one]
  rw [Matrix.mulVec_mulVec, h1, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose, Matrix.mulVec_mulVec, bmstm_mul_inv_self D, Matrix.one_mulVec]

private lemma bmstm_conjAlg_map_adjoin {F : Type} [Field F] {N : Type} [Fintype N]
    [DecidableEq N] (D : GL N F) (S : Set (GL N F)) :
    Algebra.adjoin F (Units.val '' (MulAut.conj D⁻¹ '' S)) =
      (Algebra.adjoin F (Units.val '' S)).map (bmstm_conjAlg D⁻¹) := by
  apply le_antisymm
  · rw [Algebra.adjoin_le_iff]
    rintro x ⟨u, ⟨s, hs, rfl⟩, rfl⟩
    exact Subalgebra.mem_map.mpr ⟨(s : Matrix N N F), Algebra.subset_adjoin ⟨s, hs, rfl⟩,
      by simp [bmstm_conjAlg, MulAut.conj_apply, Matrix.GeneralLinearGroup.coe_inv]⟩
  · rw [Subalgebra.map_le, Algebra.adjoin_le_iff]
    rintro x ⟨s, hs, rfl⟩
    exact Algebra.subset_adjoin ⟨MulAut.conj D⁻¹ s, ⟨s, hs, rfl⟩,
      by simp [bmstm_conjAlg, MulAut.conj_apply, Matrix.GeneralLinearGroup.coe_inv]⟩

private lemma bmstm_conjAlg_dotProduct' {F : Type} [Field F] {N : Type} [Fintype N]
    [DecidableEq N] (D : GL N F) (G : Matrix N N F) (a b : N → F) :
    Matrix.mulVec (D : Matrix N N F) a ⬝ᵥ Matrix.mulVec G (Matrix.mulVec (D : Matrix N N F) b) =
      a ⬝ᵥ Matrix.mulVec (Matrix.transpose (D : Matrix N N F) * G * (D : Matrix N N F)) b := by
  convert (bmstm_conjAlg_dotProduct D⁻¹ (Matrix.transpose (D : Matrix N N F) * G * (D : Matrix N N
      F)) a b).trans rfl using 1 <;>
    simp [Matrix.GeneralLinearGroup.coe_inv, inv_inv, Matrix.transpose_nonsing_inv,
      Matrix.mul_assoc]

private lemma bmstm_conjAlg_altSiegelGroup' {F : Type} [Field F] {N : Type} [Fintype N]
    [DecidableEq N] (D : GL N F) (G : Matrix N N F) (a₁ a₂ : N → F) :
    (altSiegelGroup G (Matrix.mulVec (D : Matrix N N F) a₁) (Matrix.mulVec (D : Matrix N N F)
        a₂)).map
        (MulAut.conj D⁻¹).toMonoidHom =
      altSiegelGroup (Matrix.transpose (D : Matrix N N F) * G * (D : Matrix N N F)) a₁ a₂ := by
  rw [bmstm_conjAlg_altSiegelGroup D G (Matrix.mulVec (D : Matrix N N F) a₁)
    (Matrix.mulVec (D : Matrix N N F) a₂)]
  congr 1 <;> rw [Matrix.mulVec_mulVec, bmstm_inv_mul_self D, Matrix.one_mulVec]

private lemma bmstm_transpose_inv_conj_gram_left {F : Type} [Field F] {N : Type} [Fintype N]
    [DecidableEq N] (D : GL N F) (G : Matrix N N F) :
    (Matrix.transpose (D : Matrix N N F))⁻¹ * (Matrix.transpose (D : Matrix N N F) * G) = G := by
  rw [← Matrix.mul_assoc, bmstm_transpose_inv_mul_self' D, Matrix.one_mul]

private lemma bmstm_transpose_inv_conj_gram_right {F : Type} [Field F] {N : Type} [Fintype N]
    [DecidableEq N] (D : GL N F) (G : Matrix N N F) :
    (G * (D : Matrix N N F)) * ((D : Matrix N N F))⁻¹ = G := by
  rw [Matrix.mul_assoc, bmstm_mul_inv_self D, Matrix.mul_one]

private lemma bmstm_transpose_inv_conj_gram {F : Type} [Field F] {N : Type} [Fintype N]
    [DecidableEq N] (D : GL N F) (G : Matrix N N F) :
    Matrix.transpose ((D : Matrix N N F))⁻¹ *
        (Matrix.transpose (D : Matrix N N F) * G * (D : Matrix N N F)) * ((D : Matrix N N F))⁻¹ = G
            := by
  rw [Matrix.transpose_nonsing_inv, ← Matrix.mul_assoc,
    bmstm_transpose_inv_conj_gram_left D G, bmstm_transpose_inv_conj_gram_right D G]

private lemma bmstm_conj_symm_eq_conj_inv {F : Type} [Field F] {N : Type} [Fintype N]
    [DecidableEq N] (D : GL N F) :
    (MulAut.conj D).symm = MulAut.conj D⁻¹ := by
  ext x
  simp [MulAut.conj_apply]

private lemma bmstm_conj_apply_conj_inv {F : Type} [Field F] {N : Type} [Fintype N]
    [DecidableEq N] (D : GL N F) (x : GL N F) :
    (MulAut.conj D) ((MulAut.conj D⁻¹) x) = x := by
  rw [← bmstm_conj_symm_eq_conj_inv D]
  exact MulEquiv.apply_symm_apply (MulAut.conj D) x

private lemma bmstm_conj_comp_conj_inv {F : Type} [Field F] {N : Type} [Fintype N]
    [DecidableEq N] (D : GL N F) :
    (MulAut.conj D).toMonoidHom.comp (MulAut.conj D⁻¹).toMonoidHom = MonoidHom.id (GL N F) := by
  exact MonoidHom.ext fun x => bmstm_conj_apply_conj_inv D x

private lemma bmstm_map_conj_conj_inv {F : Type} [Field F] {N : Type} [Fintype N]
    [DecidableEq N] (D : GL N F) (H : Subgroup (GL N F)) :
    (H.map (MulAut.conj D⁻¹).toMonoidHom).map (MulAut.conj D).toMonoidHom = H := by
  rw [Subgroup.map_map, bmstm_conj_comp_conj_inv D, Subgroup.map_id]

private lemma bmstm_conjAlg_mulVec_ne_zero {F : Type} [Field F] {N : Type} [Fintype N]
    [DecidableEq N] (D : GL N F) {v : N → F} (hv : v ≠ 0) :
    Matrix.mulVec ((D : Matrix N N F))⁻¹ v ≠ 0 := by
  intro h0
  apply hv
  have h := congrArg (Matrix.mulVec (D : Matrix N N F)) h0
  simpa [Matrix.mulVec_mulVec, bmstm_mul_inv_self D, Matrix.one_mulVec] using h

private lemma bmstm_mulVecLin_injective {F : Type} [Field F] {N : Type} [Fintype N]
    [DecidableEq N] (D : GL N F) :
    Function.Injective (Matrix.mulVecLin ((D : Matrix N N F))⁻¹) := by
  intro x y hxy
  have h := congrArg (Matrix.mulVec (D : Matrix N N F)) hxy
  simpa only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, bmstm_mul_inv_self D,
    Matrix.one_mulVec] using h

private lemma bmstm_mulVecLin_sum_smul {F : Type} [Field F] {N : Type} [Fintype N]
    [DecidableEq N] (D : GL N F) (v w : N → F) (c : Fin 2 → F) :
    Matrix.mulVec ((D : Matrix N N F))⁻¹ (∑ i, c i • ![v, w] i) =
      ∑ i, c i • ![Matrix.mulVec ((D : Matrix N N F))⁻¹ v,
        Matrix.mulVec ((D : Matrix N N F))⁻¹ w] i := by
  rw [← Matrix.mulVecLin_apply, map_sum]
  congr 1
  ext i
  rw [map_smul, Matrix.mulVecLin_apply]
  congr 1
  fin_cases i <;> rfl

private lemma bmstm_conjAlg_linearIndependent {F : Type} [Field F] {N : Type} [Fintype N]
    [DecidableEq N] (D : GL N F) {v w : N → F}
    (h : LinearIndependent F ![v, w]) :
    LinearIndependent F ![Matrix.mulVec ((D : Matrix N N F))⁻¹ v,
      Matrix.mulVec ((D : Matrix N N F))⁻¹ w] := by
  rw [Fintype.linearIndependent_iff] at h ⊢
  intro c hc
  apply h c
  have h0 : (Matrix.mulVecLin ((D : Matrix N N F))⁻¹) (∑ i, c i • ![v, w] i) =
      (Matrix.mulVecLin ((D : Matrix N N F))⁻¹) 0 := by
    simpa only [Matrix.mulVecLin_apply, map_zero] using
      (bmstm_mulVecLin_sum_smul D v w c).trans hc
  simpa only [Matrix.mulVecLin_apply] using bmstm_mulVecLin_injective D h0

private lemma bmstm_map_subtype_subgroup' {F : Type} [Field F] {N : Type} [Fintype N]
    [DecidableEq N] (φ : GL N F ≃* GL N F) (H : Subgroup (GL N F))
    (X : Subgroup ↥H) :
    Subgroup.map (φ : GL N F →* GL N F) (Subgroup.map H.subtype X) =
      Subgroup.map (H.map (φ : GL N F →* GL N F)).subtype
        (Subgroup.map (MulEquiv.subgroupMap φ H).toMonoidHom X) := by
  rw [Subgroup.map_map X (φ : GL N F →* GL N F) H.subtype,
    Subgroup.map_map X (H.map (φ : GL N F →* GL N F)).subtype
      (MulEquiv.subgroupMap φ H).toMonoidHom]
  rfl

private lemma bmstmx_rank_reindex {F : Type} [Field F] {N N' : Type} [Fintype N] [DecidableEq N]
    [Fintype N'] [DecidableEq N'] (σ : N ≃ N') (e : Matrix N N F) :
    Module.finrank F (LinearMap.range (Matrix.mulVecLin ((Matrix.reindexAlgEquiv F F σ) e))) =
      Module.finrank F (LinearMap.range (Matrix.mulVecLin e)) := by
  rw [Matrix.reindexAlgEquiv_apply]
  exact Matrix.rank_reindex σ σ e

private lemma bmstmx_rank_conjAlg {F : Type} [Field F] {N : Type} [Fintype N] [DecidableEq N]
    (D : GL N F) (e : Matrix N N F) :
    Module.finrank F (LinearMap.range (Matrix.mulVecLin (bmstm_conjAlg D⁻¹ e))) =
      Module.finrank F (LinearMap.range (Matrix.mulVecLin e)) := by
  change (bmstm_conjAlg D⁻¹ e).rank = e.rank
  rw [show bmstm_conjAlg D⁻¹ e = ((D : Matrix N N F))⁻¹ * e * (D : Matrix N N F) from by
    simp [bmstm_conjAlg]]
  have hD : IsUnit (D : Matrix N N F).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit D)
  have hDi : IsUnit (((D : Matrix N N F))⁻¹).det := by
    rw [← Matrix.GeneralLinearGroup.coe_inv]
    exact (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit D⁻¹)
  rw [Matrix.rank_mul_eq_left_of_isUnit_det (D : Matrix N N F) (((D : Matrix N N F))⁻¹ * e) hD,
    Matrix.rank_mul_eq_right_of_isUnit_det ((D : Matrix N N F))⁻¹ e hDi]

private theorem bmstmx_psp_model
    (n f : ℕ) :
    BMSTPSpModelExplicit f (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n)
        (Fin n ⊕ Fin n) (GaloisField 2 f)) (CFSG.Open.StatedSp n (GaloisField 2 f)) := by
  intro S hSU hS hodd e he hadj hdeg₁ hdeg₂ J' hJe
  exact exists_blockModel_selfDualTwo_PSp_explicit_inj n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe

private theorem bmstmx_psp_closure
    (n f : ℕ) :
    BMSTPSpClosureExplicit f (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n)
        (Fin n ⊕ Fin n) (GaloisField 2 f)) (CFSG.Open.StatedSp n (GaloisField 2 f)) := by
  intro S hSU hS hodd e he hadj hdeg₁ hdeg₂ J' hJe
  exact exists_blockModelClosure_selfDualTwo_PSp_explicit n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe

private theorem bmstmx_model_reindex
    {f : ℕ} {N N' : Type} [Fintype N] [DecidableEq N] [Fintype N'] [DecidableEq N']
    (σ : N ≃ N') (G : Matrix N N (GaloisField 2 f)) (G' : Matrix N' N' (GaloisField 2 f))
    (hG : G' = Matrix.reindex σ σ G)
    (H : Subgroup (GL N (GaloisField 2 f))) (H' : Subgroup (GL N' (GaloisField 2 f)))
    (hH : H' = H.map (bmstm_reindexGL σ).toMonoidHom)
    (h' : BMSTPSpModelExplicit f G' H') : BMSTPSpModelExplicit f G H := by
  rw [hG, hH] at h'
  intro S hSU hS hodd e he hadj hdeg₁ hdeg₂ J' hJe
  let ψ : Matrix N N (GaloisField 2 f) ≃ₐ[GaloisField 2 f] Matrix N' N' (GaloisField 2 f) :=
    Matrix.reindexAlgEquiv (GaloisField 2 f) (GaloisField 2 f) σ
  let φ : GL N (GaloisField 2 f) ≃* GL N' (GaloisField 2 f) := bmstm_reindexGL σ
  let H'' : Subgroup (GL N' (GaloisField 2 f)) :=
    H.map (φ : GL N (GaloisField 2 f) →* GL N' (GaloisField 2 f))
  let φH : ↥H ≃* ↥H'' := MulEquiv.subgroupMap φ H
  let S' : Set (GL N' (GaloisField 2 f)) := φ '' S
  let e' : Matrix N' N' (GaloisField 2 f) := ψ e
  let J'' : Subgroup ↥H'' := J'.map φH.toMonoidHom
  have hSU' : ∀ s' ∈ S', s' ∈ H'' := by
    rintro s' ⟨s, hs, rfl⟩
    exact Subgroup.mem_map.mpr ⟨s, hSU s hs, rfl⟩
  have hS' : ∀ s' ∈ S', ∀ s'' ∈ S', Commute s' s'' := by
    rintro s' ⟨s, hs, rfl⟩ s'' ⟨s'', hs'', rfl⟩
    exact (hS s hs s'' hs'').map (φ : GL N (GaloisField 2 f) →* GL N' (GaloisField 2 f))
  have hodd' : ∀ s' ∈ S', Odd (orderOf s') := by
    rintro s' ⟨s, hs, rfl⟩
    rw [φ.orderOf_eq]
    exact hodd s hs
  have hAdjoin : Algebra.adjoin (GaloisField 2 f) (Units.val '' S') =
      (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)).map ψ := by
    apply le_antisymm
    · rw [Algebra.adjoin_le_iff]
      rintro x ⟨u, ⟨s, hs, rfl⟩, rfl⟩
      exact Subalgebra.mem_map.mpr ⟨(s : Matrix N N (GaloisField 2 f)),
        Algebra.subset_adjoin ⟨s, hs, rfl⟩, rfl⟩
    · rw [Subalgebra.map_le, Algebra.adjoin_le_iff]
      rintro x ⟨s, hs, rfl⟩
      exact Algebra.subset_adjoin ⟨φ s, ⟨s, hs, rfl⟩, rfl⟩
  have he' : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) e' := by
    rw [hAdjoin]
    exact (bmstm_isPrimIdemIn_map ψ (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e).mpr he
  have hadj' : formAdj (RingHom.id (GaloisField 2 f)) (Matrix.reindex σ σ G) e' = e' := by
    change formAdj (RingHom.id (GaloisField 2 f)) (Matrix.reindex σ σ G) (Matrix.reindex σ σ e) =
      Matrix.reindex σ σ e
    rw [bmstm_formAdj_reindex, hadj]
  have hdeg₁' : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) e' := by
    rw [hAdjoin, bmstm_blockDegree_map]
    exact hdeg₁
  have hdeg₂' : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) e' < 4 := by
    rw [hAdjoin, bmstm_blockDegree_map]
    exact hdeg₂
  have hgl : glBlockCentralizer H''.subtype S' e' =
      (glBlockCentralizer H.subtype S e).map φH.toMonoidHom :=
    bmstm_glBlockCentralizer_map ψ φ (fun _ => rfl) H S e
  have hJe' : IsComponentOf J'' ⁅glBlockCentralizer H''.subtype S' e',
      glBlockCentralizer H''.subtype S' e'⁆ := by
    rw [hgl]
    have h := bmstm_isComponentOf_map φH hJe
    rwa [Subgroup.map_commutator] at h
  obtain ⟨r, ι', β₀, hrk, hlong, hcent, hrange, hinj', a₁', a₂', b₁', b₂',
    hd1, hd2, hd3, hroot1, hroot2⟩ := h' S' hSU' hS' hodd' he' hadj' hdeg₁' hdeg₂' hJe'
  let ι : (ggU .PSU r (max f 1)).K →* ↥H := φH.symm.toMonoidHom.comp ι'
  refine ⟨r, ι, β₀, ?_, hlong, ?_, ?_, ⟨φH.symm.injective.comp hinj'.1, hinj'.2⟩,
    a₁' ∘ σ, a₂' ∘ σ, b₁' ∘ σ, b₂' ∘ σ,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrk]
    exact bmstmx_rank_reindex σ e
  · intro y hy
    apply hcent y
    have hι : φH (ι y) = ι' y := φH.apply_symm_apply (ι' y)
    rw [← hι]
    exact (bmstm_mem_center_map φH).mpr hy
  · apply Subgroup.map_injective (f := φH.toMonoidHom) φH.injective
    dsimp only [ι]
    rw [MonoidHom.range_comp φH.symm.toMonoidHom ι', Subgroup.map_map,
      show φH.toMonoidHom.comp φH.symm.toMonoidHom = MonoidHom.id ↥H'' from by ext x; simp,
      Subgroup.map_id]
    exact hrange.trans (by rw [show J'' = J'.map φH.toMonoidHom from rfl])
  · exact (bmstm_dotProduct_reindex_pull σ G a₁' b₁').trans hd1
  · exact (bmstm_dotProduct_reindex_pull σ G a₂' b₂').trans hd2
  · refine ⟨?_, ?_, ?_, ?_⟩
    · exact (bmstm_dotProduct_reindex_pull σ G a₁' a₂').trans hd3.1
    · exact (bmstm_dotProduct_reindex_pull σ G b₁' b₂').trans hd3.2.1
    · exact (bmstm_dotProduct_reindex_pull σ G a₁' b₂').trans hd3.2.2.1
    · exact (bmstm_dotProduct_reindex_pull σ G a₂' b₁').trans hd3.2.2.2
  · apply Subgroup.map_injective (f := (φ : GL N (GaloisField 2 f) →* GL N' (GaloisField 2 f)))
      φ.injective
    have hhom : ((φ : GL N (GaloisField 2 f) →* GL N' (GaloisField 2 f)).comp H.subtype).comp ι =
        H''.subtype.comp ι' := by
      apply MonoidHom.ext
      intro x
      simp only [MonoidHom.comp_apply]
      exact congrArg Subtype.val (φH.apply_symm_apply (ι' x))
    have hB : Subgroup.map (φ : GL N (GaloisField 2 f) →* GL N' (GaloisField 2 f))
        (Subgroup.map H.subtype (Subgroup.map ι ((ggU .PSU r (max f 1)).D.rootGroup β₀))) =
        Subgroup.map H''.subtype (Subgroup.map ι' ((ggU .PSU r (max f 1)).D.rootGroup β₀)) := by
      rw [Subgroup.map_map, Subgroup.map_map, hhom]
      exact (Subgroup.map_map ((ggU .PSU r (max f 1)).D.rootGroup β₀) H''.subtype ι').symm
    rw [hB]
    have hroot' : Subgroup.map H''.subtype
        (Subgroup.map ι' ((ggU .PSU r (max f 1)).D.rootGroup β₀)) =
        altSiegelGroup (Matrix.reindex σ σ G) a₁' a₂' := hroot1
    rw [hroot']
    rw [show altSiegelGroup (Matrix.reindex σ σ G) a₁' a₂' =
        Subgroup.map (φ : GL N (GaloisField 2 f) →* GL N' (GaloisField 2 f))
          (altSiegelGroup G (a₁' ∘ σ) (a₂' ∘ σ)) from by
      rw [show (φ : GL N (GaloisField 2 f) →* GL N' (GaloisField 2 f)) =
        (bmstm_reindexGL σ).toMonoidHom from rfl, bmstm_altSiegelGroup_map]
      congr 1 <;> ext x <;> simp]
  · apply Subgroup.map_injective (f := (φ : GL N (GaloisField 2 f) →* GL N' (GaloisField 2 f)))
      φ.injective
    have hhom : ((φ : GL N (GaloisField 2 f) →* GL N' (GaloisField 2 f)).comp H.subtype).comp ι =
        H''.subtype.comp ι' := by
      apply MonoidHom.ext
      intro x
      simp only [MonoidHom.comp_apply]
      exact congrArg Subtype.val (φH.apply_symm_apply (ι' x))
    have hB : Subgroup.map (φ : GL N (GaloisField 2 f) →* GL N' (GaloisField 2 f))
        (Subgroup.map H.subtype (Subgroup.map ι ((ggU .PSU r (max f 1)).D.rootGroup (-β₀)))) =
        Subgroup.map H''.subtype (Subgroup.map ι' ((ggU .PSU r (max f 1)).D.rootGroup (-β₀))) := by
      rw [Subgroup.map_map, Subgroup.map_map, hhom]
      exact (Subgroup.map_map ((ggU .PSU r (max f 1)).D.rootGroup (-β₀)) H''.subtype ι').symm
    rw [hB]
    have hroot' : Subgroup.map H''.subtype
        (Subgroup.map ι' ((ggU .PSU r (max f 1)).D.rootGroup (-β₀))) =
        altSiegelGroup (Matrix.reindex σ σ G) b₁' b₂' := hroot2
    rw [hroot']
    rw [show altSiegelGroup (Matrix.reindex σ σ G) b₁' b₂' =
        Subgroup.map (φ : GL N (GaloisField 2 f) →* GL N' (GaloisField 2 f))
          (altSiegelGroup G (b₁' ∘ σ) (b₂' ∘ σ)) from by
      rw [show (φ : GL N (GaloisField 2 f) →* GL N' (GaloisField 2 f)) =
        (bmstm_reindexGL σ).toMonoidHom from rfl, bmstm_altSiegelGroup_map]
      congr 1 <;> ext x <;> simp]

private theorem bmstmx_closure_reindex
    {f : ℕ} {N N' : Type} [Fintype N] [DecidableEq N] [Fintype N'] [DecidableEq N']
    (σ : N ≃ N') (G : Matrix N N (GaloisField 2 f)) (G' : Matrix N' N' (GaloisField 2 f))
    (hG : G' = Matrix.reindex σ σ G)
    (H : Subgroup (GL N (GaloisField 2 f))) (H' : Subgroup (GL N' (GaloisField 2 f)))
    (hH : H' = H.map (bmstm_reindexGL σ).toMonoidHom)
    (h' : BMSTPSpClosureExplicit f G' H') : BMSTPSpClosureExplicit f G H := by
  rw [hG, hH] at h'
  intro S hSU hS hodd e he hadj hdeg₁ hdeg₂ J' hJe
  let ψ : Matrix N N (GaloisField 2 f) ≃ₐ[GaloisField 2 f] Matrix N' N' (GaloisField 2 f) :=
    Matrix.reindexAlgEquiv (GaloisField 2 f) (GaloisField 2 f) σ
  let φ : GL N (GaloisField 2 f) ≃* GL N' (GaloisField 2 f) := bmstm_reindexGL σ
  let H'' : Subgroup (GL N' (GaloisField 2 f)) :=
    H.map (φ : GL N (GaloisField 2 f) →* GL N' (GaloisField 2 f))
  let φH : ↥H ≃* ↥H'' := MulEquiv.subgroupMap φ H
  let S' : Set (GL N' (GaloisField 2 f)) := φ '' S
  let e' : Matrix N' N' (GaloisField 2 f) := ψ e
  let J'' : Subgroup ↥H'' := J'.map φH.toMonoidHom
  have hSU' : ∀ s' ∈ S', s' ∈ H'' := by
    rintro s' ⟨s, hs, rfl⟩
    exact Subgroup.mem_map.mpr ⟨s, hSU s hs, rfl⟩
  have hS' : ∀ s' ∈ S', ∀ s'' ∈ S', Commute s' s'' := by
    rintro s' ⟨s, hs, rfl⟩ s'' ⟨s'', hs'', rfl⟩
    exact (hS s hs s'' hs'').map (φ : GL N (GaloisField 2 f) →* GL N' (GaloisField 2 f))
  have hodd' : ∀ s' ∈ S', Odd (orderOf s') := by
    rintro s' ⟨s, hs, rfl⟩
    rw [φ.orderOf_eq]
    exact hodd s hs
  have hAdjoin : Algebra.adjoin (GaloisField 2 f) (Units.val '' S') =
      (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)).map ψ := by
    apply le_antisymm
    · rw [Algebra.adjoin_le_iff]
      rintro x ⟨u, ⟨s, hs, rfl⟩, rfl⟩
      exact Subalgebra.mem_map.mpr ⟨(s : Matrix N N (GaloisField 2 f)),
        Algebra.subset_adjoin ⟨s, hs, rfl⟩, rfl⟩
    · rw [Subalgebra.map_le, Algebra.adjoin_le_iff]
      rintro x ⟨s, hs, rfl⟩
      exact Algebra.subset_adjoin ⟨φ s, ⟨s, hs, rfl⟩, rfl⟩
  have he' : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) e' := by
    rw [hAdjoin]
    exact (bmstm_isPrimIdemIn_map ψ (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e).mpr he
  have hadj' : formAdj (RingHom.id (GaloisField 2 f)) (Matrix.reindex σ σ G) e' = e' := by
    change formAdj (RingHom.id (GaloisField 2 f)) (Matrix.reindex σ σ G) (Matrix.reindex σ σ e) =
      Matrix.reindex σ σ e
    rw [bmstm_formAdj_reindex, hadj]
  have hdeg₁' : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) e' := by
    rw [hAdjoin, bmstm_blockDegree_map]
    exact hdeg₁
  have hdeg₂' : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) e' < 4 := by
    rw [hAdjoin, bmstm_blockDegree_map]
    exact hdeg₂
  have hgl : glBlockCentralizer H''.subtype S' e' =
      (glBlockCentralizer H.subtype S e).map φH.toMonoidHom :=
    bmstm_glBlockCentralizer_map ψ φ (fun _ => rfl) H S e
  have hJe' : IsComponentOf J'' ⁅glBlockCentralizer H''.subtype S' e',
      glBlockCentralizer H''.subtype S' e'⁆ := by
    rw [hgl]
    have h := bmstm_isComponentOf_map φH hJe
    rwa [Subgroup.map_commutator] at h
  obtain ⟨r, ι', hrk, hcent, hrange, hclos⟩ :=
    h' S' hSU' hS' hodd' he' hadj' hdeg₁' hdeg₂' hJe'
  let ι : (ggU .PSU r (max f 1)).K →* ↥H := φH.symm.toMonoidHom.comp ι'
  refine ⟨r, ι, ?_, ?_, ?_, ?_⟩
  · rw [hrk]
    exact bmstmx_rank_reindex σ e
  · intro y hy
    apply hcent y
    have hι : φH (ι y) = ι' y := φH.apply_symm_apply (ι' y)
    rw [← hι]
    exact (bmstm_mem_center_map φH).mpr hy
  · apply Subgroup.map_injective (f := φH.toMonoidHom) φH.injective
    dsimp only [ι]
    rw [MonoidHom.range_comp φH.symm.toMonoidHom ι', Subgroup.map_map,
      show φH.toMonoidHom.comp φH.symm.toMonoidHom = MonoidHom.id ↥H'' from by ext x; simp,
      Subgroup.map_id]
    exact hrange.trans (by rw [show J'' = J'.map φH.toMonoidHom from rfl])
  · intro a₁ a₂ ha₁ ha₂ hli horth hle
    have ha₁' : a₁ ∘ σ.symm ≠ 0 := by
      intro h0; apply ha₁; ext x
      have := congrFun h0 (σ x); simpa using this
    have ha₂' : a₂ ∘ σ.symm ≠ 0 := by
      intro h0; apply ha₂; ext x
      have := congrFun h0 (σ x); simpa using this
    have hli' : LinearIndependent (GaloisField 2 f) ![a₁ ∘ σ.symm, a₂ ∘ σ.symm] := by
      rw [Fintype.linearIndependent_iff] at hli ⊢
      intro c hc
      apply hli c
      ext x
      have h := congrFun hc (σ x)
      simpa using h
    have horth' : (a₁ ∘ σ.symm) ⬝ᵥ Matrix.mulVec (Matrix.reindex σ σ G) (a₂ ∘ σ.symm) = 0 :=
      (bmstm_dotProduct_reindex σ G a₁ a₂).trans horth
    have hle' : altSiegelGroup (Matrix.reindex σ σ G) (a₁ ∘ σ.symm) (a₂ ∘ σ.symm) ≤
        J''.map H''.subtype := by
      rw [← bmstm_altSiegelGroup_map σ G a₁ a₂]
      have h1 : (altSiegelGroup G a₁ a₂).map (bmstm_reindexGL σ).toMonoidHom ≤
          (J'.map H.subtype).map (bmstm_reindexGL σ).toMonoidHom := Subgroup.map_mono hle
      rwa [bmstm_map_subtype_subgroup σ H J'] at h1
    obtain ⟨β, u, hβ, hlong, hroot⟩ :=
      hclos (a₁ ∘ σ.symm) (a₂ ∘ σ.symm) ha₁' ha₂' hli' horth' hle'
    refine ⟨β, u, hβ, hlong, ?_⟩
    apply Subgroup.map_injective (f := (φ : GL N (GaloisField 2 f) →* GL N' (GaloisField 2 f)))
      φ.injective
    have hhom : ((φ : GL N (GaloisField 2 f) →* GL N' (GaloisField 2 f)).comp H.subtype).comp ι =
        H''.subtype.comp ι' := by
      apply MonoidHom.ext
      intro x
      simp only [MonoidHom.comp_apply]
      exact congrArg Subtype.val (φH.apply_symm_apply (ι' x))
    rw [Subgroup.map_map, Subgroup.map_map, hhom,
      ← Subgroup.map_map (Subgroup.map (MulAut.conj u).toMonoidHom
          ((ggU .PSU r (max f 1)).D.rootGroup β))
        H''.subtype ι']
    have hroot' : Subgroup.map H''.subtype
        (Subgroup.map ι' (Subgroup.map (MulAut.conj u).toMonoidHom
          ((ggU .PSU r (max f 1)).D.rootGroup β))) =
        altSiegelGroup (Matrix.reindex σ σ G) (a₁ ∘ σ.symm) (a₂ ∘ σ.symm) := hroot
    rw [hroot']
    rw [show altSiegelGroup (Matrix.reindex σ σ G) (a₁ ∘ σ.symm) (a₂ ∘ σ.symm) =
        Subgroup.map (φ : GL N (GaloisField 2 f) →* GL N' (GaloisField 2 f))
          (altSiegelGroup G a₁ a₂) from by
      rw [show (φ : GL N (GaloisField 2 f) →* GL N' (GaloisField 2 f)) =
        (bmstm_reindexGL σ).toMonoidHom from rfl, bmstm_altSiegelGroup_map]]

private theorem bmstmx_model_scale_back
    {f : ℕ} {N : Type} [Fintype N] [DecidableEq N]
    (D : GL N (GaloisField 2 f)) (G₁ : Matrix N N (GaloisField 2 f))
    (H₁ : Subgroup (GL N (GaloisField 2 f)))
    (h' : BMSTPSpModelExplicit f
      (Matrix.transpose (D : Matrix N N (GaloisField 2 f)) * G₁ *
        (D : Matrix N N (GaloisField 2 f)))
      (H₁.map (MulAut.conj D⁻¹).toMonoidHom)) :
    BMSTPSpModelExplicit f G₁ H₁ := by
  intro S hSU hS hodd e he hadj hdeg₁ hdeg₂ J' hJe
  let φ : GL N (GaloisField 2 f) ≃* GL N (GaloisField 2 f) := MulAut.conj D⁻¹
  let ψ : Matrix N N (GaloisField 2 f) ≃ₐ[GaloisField 2 f] Matrix N N (GaloisField 2 f) :=
    bmstm_conjAlg D⁻¹
  let H'' : Subgroup (GL N (GaloisField 2 f)) :=
    H₁.map (φ : GL N (GaloisField 2 f) →* GL N (GaloisField 2 f))
  let φH : ↥H₁ ≃* ↥H'' := MulEquiv.subgroupMap φ H₁
  let S' : Set (GL N (GaloisField 2 f)) := φ '' S
  let e' : Matrix N N (GaloisField 2 f) := ψ e
  let J'' : Subgroup ↥H'' := J'.map φH.toMonoidHom
  have hSU' : ∀ s' ∈ S', s' ∈ H'' := by
    rintro s' ⟨s, hs, rfl⟩
    exact Subgroup.mem_map.mpr ⟨s, hSU s hs, rfl⟩
  have hS' : ∀ s' ∈ S', ∀ s'' ∈ S', Commute s' s'' := by
    rintro s' ⟨s, hs, rfl⟩ s'' ⟨s'', hs'', rfl⟩
    exact (hS s hs s'' hs'').map (φ : GL N (GaloisField 2 f) →* GL N (GaloisField 2 f))
  have hodd' : ∀ s' ∈ S', Odd (orderOf s') := by
    rintro s' ⟨s, hs, rfl⟩
    rw [φ.orderOf_eq]
    exact hodd s hs
  have hAdjoin : Algebra.adjoin (GaloisField 2 f) (Units.val '' S') =
      (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)).map ψ := by
    rw [show ψ = bmstm_conjAlg D⁻¹ from rfl, show S' = MulAut.conj D⁻¹ '' S from rfl,
      bmstm_conjAlg_map_adjoin D S]
  have he' : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) e' := by
    rw [hAdjoin]
    exact (bmstm_isPrimIdemIn_map ψ (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e).mpr he
  have hadj' : formAdj (RingHom.id (GaloisField 2 f)) (Matrix.transpose (D : Matrix N N (GaloisField
      2 f)) * G₁ * (D : Matrix N N (GaloisField 2 f))) e' = e' := by
    change formAdj (RingHom.id (GaloisField 2 f)) (Matrix.transpose (D : Matrix N N (GaloisField 2
        f)) * G₁ * (D : Matrix N N (GaloisField 2 f))) (bmstm_conjAlg D⁻¹ e) =
      bmstm_conjAlg D⁻¹ e
    rw [show bmstm_conjAlg D⁻¹ e = (D : Matrix N N (GaloisField 2 f))⁻¹ * e * (D : Matrix N N
        (GaloisField 2 f)) from by
      simp [bmstm_conjAlg, Matrix.GeneralLinearGroup.coe_inv],
      bmstm_conjAlg_formAdj D G₁ e, hadj]
  have hdeg₁' : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) e' := by
    rw [hAdjoin, bmstm_conjAlg_blockDegree]
    exact hdeg₁
  have hdeg₂' : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) e' < 4 := by
    rw [hAdjoin, bmstm_conjAlg_blockDegree]
    exact hdeg₂
  have hgl : glBlockCentralizer H''.subtype S' e' =
      (glBlockCentralizer H₁.subtype S e).map φH.toMonoidHom :=
    bmstm_conjAlg_glBlockCentralizer D H₁ S e
  have hJe' : IsComponentOf J'' ⁅glBlockCentralizer H''.subtype S' e',
      glBlockCentralizer H''.subtype S' e'⁆ := by
    rw [hgl]
    have h := bmstm_isComponentOf_map φH hJe
    rwa [Subgroup.map_commutator] at h
  obtain ⟨r, ι', β₀, hrk, hlong, hcent, hrange, hinj', a₁', a₂', b₁', b₂',
    hd1, hd2, hd3, hroot1, hroot2⟩ := h' S' hSU' hS' hodd' he' hadj' hdeg₁' hdeg₂' hJe'
  let ι : (ggU .PSU r (max f 1)).K →* ↥H₁ := φH.symm.toMonoidHom.comp ι'
  refine ⟨r, ι, β₀, ?_, hlong, ?_, ?_, ⟨φH.symm.injective.comp hinj'.1, hinj'.2⟩,
    Matrix.mulVec (D : Matrix N N (GaloisField 2 f)) a₁', Matrix.mulVec (D : Matrix N N (GaloisField
        2 f)) a₂', Matrix.mulVec (D : Matrix N N (GaloisField 2 f)) b₁', Matrix.mulVec (D : Matrix N
            N (GaloisField 2 f)) b₂',
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrk]
    exact bmstmx_rank_conjAlg D e
  · intro y hy
    apply hcent y
    have hι : φH (ι y) = ι' y := φH.apply_symm_apply (ι' y)
    rw [← hι]
    exact (bmstm_mem_center_map φH).mpr hy
  · apply Subgroup.map_injective (f := φH.toMonoidHom) φH.injective
    dsimp only [ι]
    rw [MonoidHom.range_comp φH.symm.toMonoidHom ι', Subgroup.map_map,
      show φH.toMonoidHom.comp φH.symm.toMonoidHom = MonoidHom.id ↥H'' from by ext x; simp,
      Subgroup.map_id]
    exact hrange.trans (by rw [show J'' = J'.map φH.toMonoidHom from rfl])
  · exact (bmstm_conjAlg_dotProduct' D G₁ a₁' b₁').trans hd1
  · exact (bmstm_conjAlg_dotProduct' D G₁ a₂' b₂').trans hd2
  · refine ⟨?_, ?_, ?_, ?_⟩
    · exact (bmstm_conjAlg_dotProduct' D G₁ a₁' a₂').trans hd3.1
    · exact (bmstm_conjAlg_dotProduct' D G₁ b₁' b₂').trans hd3.2.1
    · exact (bmstm_conjAlg_dotProduct' D G₁ a₁' b₂').trans hd3.2.2.1
    · exact (bmstm_conjAlg_dotProduct' D G₁ a₂' b₁').trans hd3.2.2.2
  · apply Subgroup.map_injective (f := (φ : GL N (GaloisField 2 f) →* GL N (GaloisField 2 f)))
      φ.injective
    have hhom : ((φ : GL N (GaloisField 2 f) →* GL N (GaloisField 2 f)).comp H₁.subtype).comp ι =
        H''.subtype.comp ι' := by
      apply MonoidHom.ext
      intro x
      simp only [MonoidHom.comp_apply]
      exact congrArg Subtype.val (φH.apply_symm_apply (ι' x))
    have hB : Subgroup.map (φ : GL N (GaloisField 2 f) →* GL N (GaloisField 2 f))
        (Subgroup.map H₁.subtype (Subgroup.map ι ((ggU .PSU r (max f 1)).D.rootGroup β₀))) =
        Subgroup.map H''.subtype (Subgroup.map ι' ((ggU .PSU r (max f 1)).D.rootGroup β₀)) := by
      rw [Subgroup.map_map, Subgroup.map_map, hhom]
      exact (Subgroup.map_map ((ggU .PSU r (max f 1)).D.rootGroup β₀) H''.subtype ι').symm
    rw [hB]
    have hroot' : Subgroup.map H''.subtype
        (Subgroup.map ι' ((ggU .PSU r (max f 1)).D.rootGroup β₀)) =
        altSiegelGroup (Matrix.transpose (D : Matrix N N (GaloisField 2 f)) * G₁ * (D : Matrix N N
            (GaloisField 2 f))) a₁' a₂' := hroot1
    rw [hroot']
    exact (bmstm_conjAlg_altSiegelGroup' D G₁ a₁' a₂').symm
  · apply Subgroup.map_injective (f := (φ : GL N (GaloisField 2 f) →* GL N (GaloisField 2 f)))
      φ.injective
    have hhom : ((φ : GL N (GaloisField 2 f) →* GL N (GaloisField 2 f)).comp H₁.subtype).comp ι =
        H''.subtype.comp ι' := by
      apply MonoidHom.ext
      intro x
      simp only [MonoidHom.comp_apply]
      exact congrArg Subtype.val (φH.apply_symm_apply (ι' x))
    have hB : Subgroup.map (φ : GL N (GaloisField 2 f) →* GL N (GaloisField 2 f))
        (Subgroup.map H₁.subtype (Subgroup.map ι ((ggU .PSU r (max f 1)).D.rootGroup (-β₀)))) =
        Subgroup.map H''.subtype (Subgroup.map ι' ((ggU .PSU r (max f 1)).D.rootGroup (-β₀))) := by
      rw [Subgroup.map_map, Subgroup.map_map, hhom]
      exact (Subgroup.map_map ((ggU .PSU r (max f 1)).D.rootGroup (-β₀)) H''.subtype ι').symm
    rw [hB]
    have hroot' : Subgroup.map H''.subtype
        (Subgroup.map ι' ((ggU .PSU r (max f 1)).D.rootGroup (-β₀))) =
        altSiegelGroup (Matrix.transpose (D : Matrix N N (GaloisField 2 f)) * G₁ * (D : Matrix N N
            (GaloisField 2 f))) b₁' b₂' := hroot2
    rw [hroot']
    exact (bmstm_conjAlg_altSiegelGroup' D G₁ b₁' b₂').symm

private theorem bmstmx_closure_scale_back
    {f : ℕ} {N : Type} [Fintype N] [DecidableEq N]
    (D : GL N (GaloisField 2 f)) (G₁ : Matrix N N (GaloisField 2 f))
    (H₁ : Subgroup (GL N (GaloisField 2 f)))
    (h' : BMSTPSpClosureExplicit f
      (Matrix.transpose (D : Matrix N N (GaloisField 2 f)) * G₁ *
        (D : Matrix N N (GaloisField 2 f)))
      (H₁.map (MulAut.conj D⁻¹).toMonoidHom)) :
    BMSTPSpClosureExplicit f G₁ H₁ := by
  intro S hSU hS hodd e he hadj hdeg₁ hdeg₂ J' hJe
  let φ : GL N (GaloisField 2 f) ≃* GL N (GaloisField 2 f) := MulAut.conj D⁻¹
  let ψ : Matrix N N (GaloisField 2 f) ≃ₐ[GaloisField 2 f] Matrix N N (GaloisField 2 f) :=
    bmstm_conjAlg D⁻¹
  let H'' : Subgroup (GL N (GaloisField 2 f)) :=
    H₁.map (φ : GL N (GaloisField 2 f) →* GL N (GaloisField 2 f))
  let φH : ↥H₁ ≃* ↥H'' := MulEquiv.subgroupMap φ H₁
  let S' : Set (GL N (GaloisField 2 f)) := φ '' S
  let e' : Matrix N N (GaloisField 2 f) := ψ e
  let J'' : Subgroup ↥H'' := J'.map φH.toMonoidHom
  have hSU' : ∀ s' ∈ S', s' ∈ H'' := by
    rintro s' ⟨s, hs, rfl⟩
    exact Subgroup.mem_map.mpr ⟨s, hSU s hs, rfl⟩
  have hS' : ∀ s' ∈ S', ∀ s'' ∈ S', Commute s' s'' := by
    rintro s' ⟨s, hs, rfl⟩ s'' ⟨s'', hs'', rfl⟩
    exact (hS s hs s'' hs'').map (φ : GL N (GaloisField 2 f) →* GL N (GaloisField 2 f))
  have hodd' : ∀ s' ∈ S', Odd (orderOf s') := by
    rintro s' ⟨s, hs, rfl⟩
    rw [φ.orderOf_eq]
    exact hodd s hs
  have hAdjoin : Algebra.adjoin (GaloisField 2 f) (Units.val '' S') =
      (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)).map ψ := by
    rw [show ψ = bmstm_conjAlg D⁻¹ from rfl, show S' = MulAut.conj D⁻¹ '' S from rfl,
      bmstm_conjAlg_map_adjoin D S]
  have he' : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) e' := by
    rw [hAdjoin]
    exact (bmstm_isPrimIdemIn_map ψ (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e).mpr he
  have hadj' : formAdj (RingHom.id (GaloisField 2 f)) (Matrix.transpose (D : Matrix N N (GaloisField
      2 f)) * G₁ * (D : Matrix N N (GaloisField 2 f))) e' = e' := by
    change formAdj (RingHom.id (GaloisField 2 f)) (Matrix.transpose (D : Matrix N N (GaloisField 2
        f)) * G₁ * (D : Matrix N N (GaloisField 2 f))) (bmstm_conjAlg D⁻¹ e) =
      bmstm_conjAlg D⁻¹ e
    rw [show bmstm_conjAlg D⁻¹ e = (D : Matrix N N (GaloisField 2 f))⁻¹ * e * (D : Matrix N N
        (GaloisField 2 f)) from by
      simp [bmstm_conjAlg, Matrix.GeneralLinearGroup.coe_inv],
      bmstm_conjAlg_formAdj D G₁ e, hadj]
  have hdeg₁' : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) e' := by
    rw [hAdjoin, bmstm_conjAlg_blockDegree]
    exact hdeg₁
  have hdeg₂' : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) e' < 4 := by
    rw [hAdjoin, bmstm_conjAlg_blockDegree]
    exact hdeg₂
  have hgl : glBlockCentralizer H''.subtype S' e' =
      (glBlockCentralizer H₁.subtype S e).map φH.toMonoidHom :=
    bmstm_conjAlg_glBlockCentralizer D H₁ S e
  have hJe' : IsComponentOf J'' ⁅glBlockCentralizer H''.subtype S' e',
      glBlockCentralizer H''.subtype S' e'⁆ := by
    rw [hgl]
    have h := bmstm_isComponentOf_map φH hJe
    rwa [Subgroup.map_commutator] at h
  obtain ⟨r, ι', hrk, hcent, hrange, hclos'⟩ :=
    h' S' hSU' hS' hodd' he' hadj' hdeg₁' hdeg₂' hJe'
  let ι : (ggU .PSU r (max f 1)).K →* ↥H₁ := φH.symm.toMonoidHom.comp ι'
  refine ⟨r, ι, ?_, ?_, ?_, ?_⟩
  · rw [hrk]
    exact bmstmx_rank_conjAlg D e
  · intro y hy
    apply hcent y
    have hι : φH (ι y) = ι' y := φH.apply_symm_apply (ι' y)
    rw [← hι]
    exact (bmstm_mem_center_map φH).mpr hy
  · apply Subgroup.map_injective (f := φH.toMonoidHom) φH.injective
    dsimp only [ι]
    rw [MonoidHom.range_comp φH.symm.toMonoidHom ι', Subgroup.map_map,
      show φH.toMonoidHom.comp φH.symm.toMonoidHom = MonoidHom.id ↥H'' from by ext x; simp,
      Subgroup.map_id]
    exact hrange.trans (by rw [show J'' = J'.map φH.toMonoidHom from rfl])
  · intro a₁ a₂ ha₁ ha₂ hli horth hle
    have ha₁' : Matrix.mulVec (D : Matrix N N (GaloisField 2 f))⁻¹ a₁ ≠ 0 :=
        bmstm_conjAlg_mulVec_ne_zero D ha₁
    have ha₂' : Matrix.mulVec (D : Matrix N N (GaloisField 2 f))⁻¹ a₂ ≠ 0 :=
        bmstm_conjAlg_mulVec_ne_zero D ha₂
    have hli' : LinearIndependent (GaloisField 2 f)
        ![Matrix.mulVec (D : Matrix N N (GaloisField 2 f))⁻¹ a₁, Matrix.mulVec (D : Matrix N N
            (GaloisField 2 f))⁻¹ a₂] :=
      bmstm_conjAlg_linearIndependent D hli
    have horth' : Matrix.mulVec (D : Matrix N N (GaloisField 2 f))⁻¹ a₁ ⬝ᵥ Matrix.mulVec
        (Matrix.transpose (D : Matrix N N (GaloisField 2 f)) * G₁ * (D : Matrix N N (GaloisField 2
            f)))
        (Matrix.mulVec (D : Matrix N N (GaloisField 2 f))⁻¹ a₂) = 0 := (bmstm_conjAlg_dotProduct D
            G₁ a₁ a₂).trans horth
    have hle' : altSiegelGroup (Matrix.transpose (D : Matrix N N (GaloisField 2 f)) * G₁ * (D :
        Matrix N N (GaloisField 2 f))) (Matrix.mulVec (D : Matrix N N (GaloisField 2 f))⁻¹ a₁)
        (Matrix.mulVec (D : Matrix N N (GaloisField 2 f))⁻¹ a₂) ≤ J''.map H''.subtype := by
      rw [← bmstm_conjAlg_altSiegelGroup D G₁ a₁ a₂]
      have h1 : (altSiegelGroup G₁ a₁ a₂).map
          (φ : GL N (GaloisField 2 f) →* GL N (GaloisField 2 f)) ≤
          (J'.map H₁.subtype).map (φ : GL N (GaloisField 2 f) →* GL N (GaloisField 2 f)) :=
        Subgroup.map_mono hle
      rwa [bmstm_map_subtype_subgroup' φ H₁ J'] at h1
    obtain ⟨β, u, hβ, hlong, hroot⟩ :=
      hclos' (Matrix.mulVec (D : Matrix N N (GaloisField 2 f))⁻¹ a₁) (Matrix.mulVec (D : Matrix N N
          (GaloisField 2 f))⁻¹ a₂) ha₁' ha₂' hli' horth' hle'
    refine ⟨β, u, hβ, hlong, ?_⟩
    apply Subgroup.map_injective (f := (φ : GL N (GaloisField 2 f) →* GL N (GaloisField 2 f)))
      φ.injective
    have hhom : ((φ : GL N (GaloisField 2 f) →* GL N (GaloisField 2 f)).comp H₁.subtype).comp ι =
        H''.subtype.comp ι' := by
      apply MonoidHom.ext
      intro x
      simp only [MonoidHom.comp_apply]
      exact congrArg Subtype.val (φH.apply_symm_apply (ι' x))
    rw [Subgroup.map_map, Subgroup.map_map, hhom,
      ← Subgroup.map_map (Subgroup.map (MulAut.conj u).toMonoidHom
          ((ggU .PSU r (max f 1)).D.rootGroup β))
        H''.subtype ι']
    have hroot' : Subgroup.map H''.subtype
        (Subgroup.map ι' (Subgroup.map (MulAut.conj u).toMonoidHom
          ((ggU .PSU r (max f 1)).D.rootGroup β))) =
        altSiegelGroup (Matrix.transpose (D : Matrix N N (GaloisField 2 f)) * G₁ * (D : Matrix N N
            (GaloisField 2 f))) (Matrix.mulVec (D : Matrix N N (GaloisField 2 f))⁻¹ a₁)
                (Matrix.mulVec (D : Matrix N N (GaloisField 2 f))⁻¹ a₂) := hroot
    rw [hroot']
    rw [show altSiegelGroup (Matrix.transpose (D : Matrix N N (GaloisField 2 f)) * G₁ * (D : Matrix
        N N (GaloisField 2 f))) (Matrix.mulVec (D : Matrix N N (GaloisField 2 f))⁻¹ a₁)
            (Matrix.mulVec (D : Matrix N N (GaloisField 2 f))⁻¹ a₂) =
        Subgroup.map (φ : GL N (GaloisField 2 f) →* GL N (GaloisField 2 f))
          (altSiegelGroup G₁ a₁ a₂) from (bmstm_conjAlg_altSiegelGroup D G₁ a₁ a₂).symm]

private theorem bmstmx_model_scale
    {f : ℕ} {N : Type} [Fintype N] [DecidableEq N]
    (D : GL N (GaloisField 2 f)) (G₁ G₂ : Matrix N N (GaloisField 2 f))
    (hG : G₂ = Matrix.transpose (D : Matrix N N (GaloisField 2 f)) * G₁ *
      (D : Matrix N N (GaloisField 2 f)))
    (H₁ H₂ : Subgroup (GL N (GaloisField 2 f)))
    (hH : H₂ = H₁.map (MulAut.conj D⁻¹).toMonoidHom)
    (h' : BMSTPSpModelExplicit f G₁ H₁) : BMSTPSpModelExplicit f G₂ H₂ := by
  rw [hG, hH]
  refine bmstmx_model_scale_back D⁻¹ (Matrix.transpose (D : Matrix N N (GaloisField 2 f)) * G₁ *
    (D : Matrix N N (GaloisField 2 f))) (H₁.map (MulAut.conj D⁻¹).toMonoidHom) ?_
  convert h' using 2
  · simpa only [Matrix.GeneralLinearGroup.coe_inv] using bmstm_transpose_inv_conj_gram D G₁
  · simpa only [inv_inv] using bmstm_map_conj_conj_inv D H₁

private theorem bmstmx_closure_scale
    {f : ℕ} {N : Type} [Fintype N] [DecidableEq N]
    (D : GL N (GaloisField 2 f)) (G₁ G₂ : Matrix N N (GaloisField 2 f))
    (hG : G₂ = Matrix.transpose (D : Matrix N N (GaloisField 2 f)) * G₁ *
      (D : Matrix N N (GaloisField 2 f)))
    (H₁ H₂ : Subgroup (GL N (GaloisField 2 f)))
    (hH : H₂ = H₁.map (MulAut.conj D⁻¹).toMonoidHom)
    (h' : BMSTPSpClosureExplicit f G₁ H₁) : BMSTPSpClosureExplicit f G₂ H₂ := by
  rw [hG, hH]
  refine bmstmx_closure_scale_back D⁻¹ (Matrix.transpose (D : Matrix N N (GaloisField 2 f)) * G₁ *
    (D : Matrix N N (GaloisField 2 f))) (H₁.map (MulAut.conj D⁻¹).toMonoidHom) ?_
  convert h' using 2
  · simpa only [Matrix.GeneralLinearGroup.coe_inv] using bmstm_transpose_inv_conj_gram D G₁
  · simpa only [inv_inv] using bmstm_map_conj_conj_inv D H₁

private theorem bmstmx_psp_model_minus
    (n f : ℕ) (hn : 4 ≤ n) : BMSTPSpModelExplicit f (LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
            (minusCoeffs 2 f).2))) (bmstm_H n f hn) := by
  refine bmstmx_model_scale (bmstm_Dunit n f) _ _ (bmstm_gram n f hn) _ (bmstm_H n f hn)
    (bmstm_H_scale n f hn) ?_
  refine bmstmx_model_reindex (bmstm_sigma n (by omega)) _ _ ?_ _ _
    (bmstm_H_perm n f hn) (bmstmx_psp_model n f)
  rw [show Matrix.reindex (bmstm_sigma n (by
    omega)) (bmstm_sigma n (by
      omega)) (Matrix.reindex (bmstm_sigma n (by
        omega)).symm (bmstm_sigma n (by
          omega)).symm (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
              (GaloisField 2 f))) = (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕
                  Fin n) (GaloisField 2 f)) from bmstm_reindex_comp_symm _ _]

private theorem bmstmx_psp_closure_minus
    (n f : ℕ) (hn : 4 ≤ n) : BMSTPSpClosureExplicit f (LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
            (minusCoeffs 2 f).2))) (bmstm_H n f hn) := by
  refine bmstmx_closure_scale (bmstm_Dunit n f) _ _ (bmstm_gram n f hn) _ (bmstm_H n f hn)
    (bmstm_H_scale n f hn) ?_
  refine bmstmx_closure_reindex (bmstm_sigma n (by omega)) _ _ ?_ _ _
    (bmstm_H_perm n f hn) (bmstmx_psp_closure n f)
  rw [show Matrix.reindex (bmstm_sigma n (by
    omega)) (bmstm_sigma n (by
      omega)) (Matrix.reindex (bmstm_sigma n (by
        omega)).symm (bmstm_sigma n (by
          omega)).symm (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
              (GaloisField 2 f))) = (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕
                  Fin n) (GaloisField 2 f)) from bmstm_reindex_comp_symm _ _]

theorem exists_blockModel_selfDualTwo_POmegaMinus_explicit
    (n f : ℕ) (S : Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈
    (Spin.spinMatrix
    (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
      (GaloisField 2 f)} (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hn : 4 ≤ n)
    (hadj : formAdj (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
      (QuadraticMap.polarBilin
      (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2))) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup
      ↥(spinGroup (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer
      (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2))
      S (e),
      glBlockCentralizer
        (Spin.spinMatrix
        (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) S (e)⁆) :
    ∃ (r : ℕ)
      (ι : (ggU .PSU r (max f 1)).K →*
      ↥(spinGroup (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)))
      (β₀ : Fin (ggU .PSU r (max f 1)).D.rank → ℤ),
        2 * r = Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.mulVecLin e)) ∧
      GGLongRoot (ggU .PSU r (max f 1)).D β₀ ∧
      (∀ y, ι y ∈ Subgroup.center
        ↥(spinGroup (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) →
        y ∈ Subgroup.center (ggU .PSU r (max f 1)).K) ∧ ι.range = J' ∧
      ∃ a₁ a₂ b₁ b₂ : (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) → (GaloisField 2 f),
        ((Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) a₁ = 0 ∧
          (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) a₂ = 0 ∧
          (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) b₁ = 0 ∧
          (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) b₂ = 0) ∧
        QuadraticMap.polar
          (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) a₁ b₁ = 1 ∧
          QuadraticMap.polar
          (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) a₂ b₂ = 1 ∧
        (QuadraticMap.polar
          (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) a₁ a₂ = 0 ∧
          QuadraticMap.polar
          (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) b₁ b₂ = 0 ∧
          QuadraticMap.polar
            (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) a₁ b₂ = 0 ∧
            QuadraticMap.polar
            (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) a₂ b₁ = 0)
            ∧
        (((ggU .PSU r (max f 1)).D.rootGroup β₀).map ι).map
        (Spin.spinAction
        (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) = siegelGroup
        (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) a₁ a₂ ∧
        (((ggU .PSU r (max f 1)).D.rootGroup (-β₀)).map ι).map
        (Spin.spinAction
        (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) = siegelGroup
        (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) b₁ b₂ := by
  exact bmst_model_of_psp_explicit f (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
      (minusCoeffs 2 f).2) (bmstm_hnd n f) (bmstm_hinj n f) (range_spinAction_quadMinus_eq_omegaGroup n f hn)
    (bmstm_hcent n f hn) (bmstm_H n f hn) (bmstm_hH n f hn) (bmstmx_psp_model_minus n f hn) S hSU
        hS hodd he hadj
    hdeg₁ hdeg₂ hJe

theorem exists_blockModel_selfDualTwo_POmegaMinus_explicit_inj
    (n f : ℕ) (S : Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈
    (Spin.spinMatrix
    (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
      (GaloisField 2 f)} (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hn : 4 ≤ n)
    (hadj : formAdj (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
      (QuadraticMap.polarBilin
      (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2))) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup
      ↥(spinGroup (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer
      (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2))
      S (e),
      glBlockCentralizer
        (Spin.spinMatrix
        (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) S (e)⁆) :
    ∃ (r : ℕ)
      (ι : (ggU .PSU r (max f 1)).K →*
      ↥(spinGroup (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)))
      (β₀ : Fin (ggU .PSU r (max f 1)).D.rank → ℤ),
        2 * r = Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.mulVecLin e)) ∧
      GGLongRoot (ggU .PSU r (max f 1)).D β₀ ∧
      (∀ y, ι y ∈ Subgroup.center
        ↥(spinGroup (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) →
        y ∈ Subgroup.center (ggU .PSU r (max f 1)).K) ∧ ι.range = J' ∧
      (Function.Injective ι ∧ 2 ≤ r ∧ (2 ^ max f 1 ≠ 2 ∨ 4 ≤ r)) ∧
      ∃ a₁ a₂ b₁ b₂ : (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) → (GaloisField 2 f),
        ((Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) a₁ = 0 ∧
          (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) a₂ = 0 ∧
          (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) b₁ = 0 ∧
          (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) b₂ = 0) ∧
        QuadraticMap.polar
          (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) a₁ b₁ = 1 ∧
          QuadraticMap.polar
          (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) a₂ b₂ = 1 ∧
        (QuadraticMap.polar
          (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) a₁ a₂ = 0 ∧
          QuadraticMap.polar
          (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) b₁ b₂ = 0 ∧
          QuadraticMap.polar
            (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) a₁ b₂ = 0 ∧
            QuadraticMap.polar
            (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) a₂ b₁ = 0)
            ∧
        (((ggU .PSU r (max f 1)).D.rootGroup β₀).map ι).map
        (Spin.spinAction
        (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) = siegelGroup
        (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) a₁ a₂ ∧
        (((ggU .PSU r (max f 1)).D.rootGroup (-β₀)).map ι).map
        (Spin.spinAction
        (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) = siegelGroup
        (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) b₁ b₂ := by
  exact bmst_model_of_psp_explicit_inj f
    (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) (bmstm_hnd n f)
    (bmstm_hinj n f) (range_spinAction_quadMinus_eq_omegaGroup n f hn) (bmstm_hcent n f hn)
    (bmstm_H n f hn) (bmstm_hH n f hn) (bmstmx_psp_model_minus n f hn) S hSU hS hodd he hadj
    hdeg₁ hdeg₂ hJe

theorem exists_blockModelClosure_selfDualTwo_POmegaMinus_explicit
    (n f : ℕ) (S : Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈
    (Spin.spinMatrix
    (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
      (GaloisField 2 f)} (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hn : 4 ≤ n)
    (hadj : formAdj (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
      (QuadraticMap.polarBilin
      (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2))) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup
      ↥(spinGroup (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer
      (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2))
      S (e),
      glBlockCentralizer
        (Spin.spinMatrix
        (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) S (e)⁆) :
    ∃ (r : ℕ) (ι : (ggU .PSU r (max f 1)).K →* ↥(spinGroup (Spin.quadMinus n
        (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2))),
      2 * r = Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.mulVecLin e)) ∧
      (∀ y, ι y ∈ Subgroup.center ↥(spinGroup (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2
          f).1 (minusCoeffs 2 f).2)) → y ∈ Subgroup.center (ggU .PSU r (max f 1)).K) ∧
      ι.range = J' ∧
      (∀ a₁ a₂ : ((Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) → GaloisField 2 f), a₁ ≠ 0 → a₂ ≠ 0 →
          LinearIndependent (GaloisField 2 f) ![a₁, a₂] → (Spin.quadMinus n (GaloisField 2 f)
          (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) a₁ = 0 → (Spin.quadMinus n (GaloisField 2 f)
          (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) a₂ = 0 →
        QuadraticMap.polar (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2
            f).2) a₁ a₂ = 0 → siegelGroup (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
            (minusCoeffs 2 f).2) a₁ a₂ ≤ J'.map (Spin.spinAction (Spin.quadMinus n (GaloisField 2
            f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) →
        ∃ (β : Fin (ggU .PSU r (max f 1)).D.rank → ℤ) (u : (ggU .PSU r (max f 1)).K),
          β ∈ (ggU .PSU r (max f 1)).D.roots ∧
            GGLongRoot (ggU .PSU r (max f 1)).D β ∧
          ((((ggU .PSU r (max f 1)).D.rootGroup β).map (MulAut.conj u).toMonoidHom).map ι).map
              (Spin.spinAction (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs
              2 f).2)) = siegelGroup (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
              (minusCoeffs 2 f).2) a₁ a₂) := by
  exact bmst_closure_of_psp_explicit f (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
      (minusCoeffs 2 f).2) (bmstm_hnd n f) (bmstm_hinj n f) (range_spinAction_quadMinus_eq_omegaGroup n f hn)
    (bmstm_hcent n f hn) (bmstm_H n f hn) (bmstm_hH n f hn) (bmstmx_psp_closure_minus n f hn) S hSU
        hS hodd he hadj
    hdeg₁ hdeg₂ hJe

section LinearModelAtTwo

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix

local notation "F₂" => GaloisField 2 1
local notation "F₄" => GaloisField 2 2
local notation "SU₂" => SU (unitaryInvolution F₄ 2 1)

private theorem bmstm_minusCoeffs_fst_at_two : (minusCoeffs 2 1).1 = 1 := by
  classical
  let := Fintype.ofFinite F₂
  have hcard : Fintype.card F₂ = 2 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card (p := 2) (n := 1) (by decide)]
    norm_num
  have h := FiniteField.pow_card_sub_one_eq_one (minusCoeffs 2 1).1
    (bmstm_minusCoeffs_fst_ne_zero 1)
  simpa only [hcard, Nat.reduceSub, pow_one] using h

private theorem bmstm_D_at_two_eq_one (n : ℕ) : bmstm_D n 1 = 1 := by
  ext i j
  simp [bmstm_D, bmstm_minusCoeffs_fst_at_two, Matrix.one_apply]

private theorem bmstm_Dunit_at_two_eq_one (n : ℕ) : bmstm_Dunit n 1 = 1 :=
  Units.ext (bmstm_D_at_two_eq_one n)

private theorem bmstm_gram_at_two (n : ℕ) (hn : 4 ≤ n) :
    LinearMap.toMatrix₂' F₂ (Spin.quadMinus n F₂ (minusCoeffs 2 1).1
      (minusCoeffs 2 1).2).polarBilin =
      Matrix.reindex (bmstm_sigma n (by omega)).symm (bmstm_sigma n (by omega)).symm
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F₂) := by
  simpa only [bmstm_D_at_two_eq_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
    using bmstm_gram n 1 hn

private theorem bmstm_H_at_two (n : ℕ) (hn : 4 ≤ n) :
    bmstm_H n 1 hn = (CFSG.Open.StatedSp n F₂).map
      (bmstm_reindexGL (bmstm_sigma n (by omega))).symm.toMonoidHom := by
  have hconj : (MulAut.conj (bmstm_Dunit n 1)⁻¹).toMonoidHom = MonoidHom.id _ := by
    ext x
    simp [bmstm_Dunit_at_two_eq_one]
  simpa only [hconj, Subgroup.map_id] using bmstm_H_scale n 1 hn

private theorem bmstm_linear_model_reindex_at_two
    {N N' : Type} [Fintype N] [DecidableEq N] [Fintype N'] [DecidableEq N']
    (σ : N ≃ N') (G : Matrix N N F₂) (G' : Matrix N' N' F₂)
    (hG : G' = Matrix.reindex σ σ G)
    (H : Subgroup (GL N F₂)) (H' : Subgroup (GL N' F₂))
    (hH : H' = H.map (bmstm_reindexGL σ).toMonoidHom)
    (h' : BMSTPSpLinearModelAtTwo G' H') : BMSTPSpLinearModelAtTwo G H := by
  rw [hG, hH] at h'
  intro S hSU hS hodd e he hadj hdeg₁ hdeg₂ J hJ
  let ψ : Matrix N N F₂ ≃ₐ[F₂] Matrix N' N' F₂ := Matrix.reindexAlgEquiv F₂ F₂ σ
  let φ : GL N F₂ ≃* GL N' F₂ := bmstm_reindexGL σ
  let H'' := H.map φ.toMonoidHom
  let φH : H ≃* H'' := MulEquiv.subgroupMap φ H
  let S' := φ '' S
  let e' := ψ e
  let J' := J.map φH.toMonoidHom
  have hSU' : ∀ s ∈ S', s ∈ H'' := by
    rintro s ⟨s₀, hs₀, rfl⟩
    exact Subgroup.mem_map_of_mem φ.toMonoidHom (hSU s₀ hs₀)
  have hS' : ∀ s ∈ S', ∀ t ∈ S', Commute s t := by
    rintro s ⟨s₀, hs₀, rfl⟩ t ⟨t₀, ht₀, rfl⟩
    exact (hS s₀ hs₀ t₀ ht₀).map φ.toMonoidHom
  have hodd' : ∀ s ∈ S', Odd (orderOf s) := by
    rintro s ⟨s₀, hs₀, rfl⟩
    rw [φ.orderOf_eq]
    exact hodd s₀ hs₀
  have hAdjoin : Algebra.adjoin F₂ (Units.val '' S') =
      (Algebra.adjoin F₂ (Units.val '' S)).map ψ := by
    apply le_antisymm
    · rw [Algebra.adjoin_le_iff]
      rintro x ⟨s, ⟨s₀, hs₀, rfl⟩, rfl⟩
      exact Subalgebra.mem_map.mpr ⟨(s₀ : Matrix N N F₂),
        Algebra.subset_adjoin ⟨s₀, hs₀, rfl⟩, rfl⟩
    · rw [Subalgebra.map_le, Algebra.adjoin_le_iff]
      rintro x ⟨s, hs, rfl⟩
      exact Algebra.subset_adjoin ⟨φ s, ⟨s, hs, rfl⟩, rfl⟩
  have he' : IsPrimIdemIn (Algebra.adjoin F₂ (Units.val '' S')) e' := by
    rw [hAdjoin]
    exact (bmstm_isPrimIdemIn_map ψ (Algebra.adjoin F₂ (Units.val '' S)) e).mpr he
  have hadj' : formAdj (RingHom.id F₂) (Matrix.reindex σ σ G) e' = e' := by
    change formAdj (RingHom.id F₂) (Matrix.reindex σ σ G) (Matrix.reindex σ σ e) =
      Matrix.reindex σ σ e
    rw [bmstm_formAdj_reindex, hadj]
  have hdeg₁' : 2 ≤ blockDegree (Algebra.adjoin F₂ (Units.val '' S')) e' := by
    rw [hAdjoin, bmstm_blockDegree_map]
    exact hdeg₁
  have hdeg₂' : blockDegree (Algebra.adjoin F₂ (Units.val '' S')) e' < 4 := by
    rw [hAdjoin, bmstm_blockDegree_map]
    exact hdeg₂
  have hgl : glBlockCentralizer H''.subtype S' e' =
      (glBlockCentralizer H.subtype S e).map φH.toMonoidHom :=
    bmstm_glBlockCentralizer_map ψ φ (fun _ => rfl) H S e
  have hJ' : IsComponentOf J' ⁅glBlockCentralizer H''.subtype S' e',
      glBlockCentralizer H''.subtype S' e'⁆ := by
    rw [hgl]
    have h := bmstm_isComponentOf_map φH hJ
    rwa [Subgroup.map_commutator] at h
  obtain ⟨m, A, ι', E', C', hm, hι', hRange', hE', hAct', hFix', hSplit', hAlt'⟩ :=
    h' S' hSU' hS' hodd' he' hadj' hdeg₁' hdeg₂' hJ'
  let : Algebra F₂ F₄ := A
  let T := LinearEquiv.funCongrLeft F₂ F₂ σ
  let R := LinearEquiv.funCongrLeft F₂ F₂ σ.symm
  let ι : SU₂ m →* H := φH.symm.toMonoidHom.comp ι'
  let E := T.toLinearMap.comp E'
  let C := C'.comap R.toLinearMap
  have hT (x : N' → F₂) : T x = x ∘ σ := rfl
  have hR (x : N → F₂) : R x = x ∘ σ.symm := rfl
  have hRC (x : N → F₂) : (R x) ∘ σ = x := by
    rw [hR]
    ext i
    simp
  have hφ (g : SU₂ m) : φ (ι g : GL N F₂) = (ι' g : GL N' F₂) :=
    congrArg Subtype.val (φH.apply_symm_apply (ι' g))
  have hMat (g : SU₂ m) : ((ι' g : GL N' F₂) : Matrix N' N' F₂) =
      Matrix.reindex σ σ ((ι g : GL N F₂) : Matrix N N F₂) :=
    (congrArg Units.val (hφ g)).symm
  have hVec (g : SU₂ m) (x : N' → F₂) :
      ((((ι' g : GL N' F₂) : Matrix N' N' F₂) *ᵥ x) ∘ σ) =
        ((ι g : GL N F₂) : Matrix N N F₂) *ᵥ (x ∘ σ) := by
    rw [hMat, bmstm_reindex_mulVec]
    ext i
    simp
  refine ⟨m, A, ι, E, C, hm, φH.symm.injective.comp hι', ?_, T.injective.comp hE',
    ?_, ?_, ?_, ?_⟩
  · apply Subgroup.map_injective (f := φH.toMonoidHom) φH.injective
    dsimp only [ι]
    rw [MonoidHom.range_comp, Subgroup.map_map,
      show φH.toMonoidHom.comp φH.symm.toMonoidHom = MonoidHom.id H'' from by ext x; simp,
      Subgroup.map_id]
    exact hRange'
  · intro g x
    change ((ι g : GL N F₂) : Matrix N N F₂) *ᵥ T (E' x) = T (E' _)
    rw [hT, hT, ← hVec, hAct']
  · intro g w hw
    have hw' : R w ∈ C' := hw
    have h := congrArg (fun x : N' → F₂ => x ∘ σ) (hFix' g (R w) hw')
    rwa [hVec, hRC] at h
  · intro z
    obtain ⟨x, w, hw, hz⟩ := hSplit' (R z)
    refine ⟨x, T w, ?_, ?_⟩
    · change R (T w) ∈ C'
      have hRT : R (T w) = w := by
        rw [hR, hT]
        ext i
        simp
      rwa [hRT]
    · have h := congrArg T hz
      rw [LinearEquiv.map_add] at h
      have hTR : T (R z) = z := by rw [hT, hRC]
      change z = T (E' x) + T w
      exact hTR.symm.trans h
  · intro g hg z
    let d := (((ι' g : GL N' F₂) : Matrix N' N' F₂) *ᵥ R z) - R z
    have hd : d ∘ σ = (((ι g : GL N F₂) : Matrix N N F₂) *ᵥ z) - z := by
      dsimp only [d]
      change ((((ι' g : GL N' F₂) : Matrix N' N' F₂) *ᵥ R z) ∘ σ) -
        (R z) ∘ σ = _
      rw [hVec, hRC]
    have h := bmstm_dotProduct_reindex_pull σ G (R z) d
    rw [hRC, hd] at h
    exact h.trans (hAlt' g hg (R z))

private theorem bmstm_psp_linear_model_minus_at_two (n : ℕ) (hn : 4 ≤ n) :
    BMSTPSpLinearModelAtTwo (LinearMap.toMatrix₂' F₂
      (Spin.quadMinus n F₂ (minusCoeffs 2 1).1 (minusCoeffs 2 1).2).polarBilin)
      (bmstm_H n 1 hn) := by
  rw [bmstm_gram_at_two n hn, bmstm_H_at_two n hn]
  refine bmstm_linear_model_reindex_at_two (bmstm_sigma n (by omega)) _
    (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F₂) ?_ _ _
    (bmstm_H_perm n 1 hn) ?_
  · exact (bmstm_reindex_comp_symm _ _).symm
  · intro S hSU hS hodd e he hadj hdeg₁ hdeg₂ J hJ
    exact exists_linearBlockModel_selfDualTwo_PSp_at_two n S hSU hS hodd
      he hadj hdeg₁ hdeg₂ hJ

theorem exists_linearBlockModel_selfDualTwo_POmegaMinus_at_two
    (n : ℕ) (hn : 4 ≤ n) (S : Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F₂))
    (hSU : ∀ s ∈ S, s ∈ (Spin.spinMatrix
      (Spin.quadMinus n F₂ (minusCoeffs 2 1).1 (minusCoeffs 2 1).2)).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F₂}
    (he : IsPrimIdemIn (Algebra.adjoin F₂ (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id F₂) (LinearMap.toMatrix₂' F₂
      (Spin.quadMinus n F₂ (minusCoeffs 2 1).1 (minusCoeffs 2 1).2).polarBilin) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin F₂ (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin F₂ (Units.val '' S)) e < 4)
    {J : Subgroup (spinGroup (Spin.quadMinus n F₂ (minusCoeffs 2 1).1 (minusCoeffs 2 1).2))}
    (hJ : IsComponentOf J ⁅glBlockCentralizer (Spin.spinMatrix
      (Spin.quadMinus n F₂ (minusCoeffs 2 1).1 (minusCoeffs 2 1).2)) S e,
      glBlockCentralizer (Spin.spinMatrix
      (Spin.quadMinus n F₂ (minusCoeffs 2 1).1 (minusCoeffs 2 1).2)) S e⁆) :
    ∃ (m : ℕ) (_ : Algebra F₂ F₄)
      (ι : SU₂ m →* spinGroup (Spin.quadMinus n F₂ (minusCoeffs 2 1).1 (minusCoeffs 2 1).2))
      (E : (Fin m → F₄) →ₗ[F₂] ((Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) → F₂))
      (C : Submodule F₂ ((Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) → F₂)),
      4 ≤ m ∧ Function.Injective ι ∧ ι.range = J ∧ Function.Injective E ∧
      (∀ g x, Spin.spinAction (Spin.quadMinus n F₂ (minusCoeffs 2 1).1 (minusCoeffs 2 1).2)
        (ι g) (E x) = E (natRep (SU₂ m) g x)) ∧
      (∀ g w, w ∈ C → Spin.spinAction
        (Spin.quadMinus n F₂ (minusCoeffs 2 1).1 (minusCoeffs 2 1).2) (ι g) w = w) ∧
      (∀ z, ∃ x, ∃ w ∈ C, z = E x + w) ∧
      (∀ g, g ^ 2 = 1 → ∀ z,
        (Spin.quadMinus n F₂ (minusCoeffs 2 1).1 (minusCoeffs 2 1).2).polarBilin z
          (Spin.spinAction (Spin.quadMinus n F₂ (minusCoeffs 2 1).1 (minusCoeffs 2 1).2)
            (ι g) z - z) = 0) :=
  bmst_linear_model_of_psp_at_two (Spin.quadMinus n F₂ (minusCoeffs 2 1).1 (minusCoeffs 2 1).2)
    (bmstm_hnd n 1) (bmstm_hinj n 1) (range_spinAction_quadMinus_eq_omegaGroup n 1 hn)
    (bmstm_hcent n 1 hn) (bmstm_H n 1 hn) (bmstm_hH n 1 hn)
    (bmstm_psp_linear_model_minus_at_two n hn) S hSU hS hodd he hadj hdeg₁ hdeg₂ hJ

end LinearModelAtTwo

end CFSG.StandardType.ClassicalPosition
