module

public import CFSG.ClassicalGroups.Orthogonal.MinusSplitTorus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KGen

open CFSG.Open Matrix
open CFSG.ClassicalGroups.Orthogonal (minusFlip minusFlip_inv minusFlip_apply_inl
  minusFlip_apply_inr minusFlip_apply_inl_of_ne minusFlip_apply_inr_of_ne minusFlip_apply_inr_inr)
open CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.OmegaEven (permGL mulVec_permGL)

variable {K : Type} [Field K]

private abbrev Idx2 := Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2

private abbrev Idx3 := Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2

private def embFun : (Idx2 ⊕ Fin 2) → Idx3
  | Sum.inl (Sum.inl _) => Sum.inl 1
  | Sum.inl (Sum.inr (Sum.inl _)) => Sum.inr (Sum.inl 1)
  | Sum.inl (Sum.inr (Sum.inr k)) => Sum.inr (Sum.inr k)
  | Sum.inr t => Fin.cases (Sum.inl 0) (fun _ => Sum.inr (Sum.inl 0)) t

private def embInvFun : Idx3 → (Idx2 ⊕ Fin 2)
  | Sum.inl i => Fin.cases (Sum.inr 0) (fun _ => Sum.inl (Sum.inl 0)) i
  | Sum.inr (Sum.inl j) => Fin.cases (Sum.inr 1) (fun _ => Sum.inl (Sum.inr (Sum.inl 0))) j
  | Sum.inr (Sum.inr k) => Sum.inl (Sum.inr (Sum.inr k))

private def embEquiv : (Idx2 ⊕ Fin 2) ≃ Idx3 where
  toFun := embFun
  invFun := embInvFun
  left_inv := by decide
  right_inv := by decide

private def embJ (a : Idx2) : Idx3 := embFun (Sum.inl a)

private def embK (t : Fin 2) : Idx3 := embFun (Sum.inr t)

private theorem embEquiv_apply_inl (a : Idx2) : embEquiv (Sum.inl a) = embJ a := rfl

private theorem embEquiv_apply_inr (t : Fin 2) : embEquiv (Sum.inr t) = embK t := rfl

private theorem embEquiv_symm_j (a : Idx2) : embEquiv.symm (embJ a) = Sum.inl a := by
  have h := embEquiv.symm_apply_apply (Sum.inl a)
  rwa [embEquiv_apply_inl] at h

private theorem embEquiv_symm_k (t : Fin 2) : embEquiv.symm (embK t) = Sum.inr t := by
  have h := embEquiv.symm_apply_apply (Sum.inr t)
  rwa [embEquiv_apply_inr] at h

private def embMatHom (K : Type) [Field K] :
    Matrix Idx2 Idx2 K →* Matrix Idx3 Idx3 K where
  toFun A := (Matrix.fromBlocks A 0 0 1).submatrix (embEquiv.symm) (embEquiv.symm)
  map_one' := by
    rw [Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]
  map_mul' A B := by
    have h : Matrix.fromBlocks A 0 0 1 * Matrix.fromBlocks B 0 0 1 =
        Matrix.fromBlocks (A * B) (0 : Matrix Idx2 (Fin 2) K) (0 : Matrix (Fin 2) Idx2 K)
          (1 : Matrix (Fin 2) (Fin 2) K) := by
      rw [Matrix.fromBlocks_multiply]
      simp
    rw [← h]
    exact (Matrix.submatrix_mul_equiv (Matrix.fromBlocks A 0 0 1) (Matrix.fromBlocks B 0 0 1)
      (embEquiv.symm) embEquiv.symm embEquiv.symm).symm

private def embGL (K : Type) [Field K] : GL Idx2 K →* GL Idx3 K :=
  Units.map (embMatHom K)

private theorem embMatHom_mulVec_apply {K : Type} [Field K]
    (A : Matrix Idx2 Idx2 K) (v : Idx3 → K) :
    embMatHom K A *ᵥ v =
      ((Matrix.fromBlocks A 0 0 1) *ᵥ (v ∘ embEquiv)) ∘ embEquiv.symm :=
  Matrix.submatrix_mulVec_equiv (Matrix.fromBlocks A 0 0 1) v embEquiv.symm embEquiv.symm

private theorem embMatHom_mulVec_j {K : Type} [Field K]
    (A : Matrix Idx2 Idx2 K) (v : Idx3 → K) (a : Idx2) :
    (embMatHom K A *ᵥ v) (embJ a) = (A *ᵥ (v ∘ embJ)) a := by
  rw [embMatHom_mulVec_apply]
  simp only [Function.comp_apply, embEquiv_symm_j, Matrix.fromBlocks_mulVec, Matrix.zero_mulVec,
    zero_add, Matrix.one_mulVec, add_zero, Sum.elim_inl]
  rfl

private theorem embMatHom_mulVec_k {K : Type} [Field K]
    (A : Matrix Idx2 Idx2 K) (v : Idx3 → K) (t : Fin 2) :
    (embMatHom K A *ᵥ v) (embK t) = v (embK t) := by
  rw [embMatHom_mulVec_apply]
  simp only [Function.comp_apply, embEquiv_symm_k, Matrix.fromBlocks_mulVec, Matrix.zero_mulVec,
    zero_add, Matrix.one_mulVec, add_zero, Sum.elim_inr]
  rfl

private theorem embGL_mulVec_j {K : Type} [Field K]
    (A : GL Idx2 K) (v : Idx3 → K) (a : Idx2) :
    (((embGL K A : GL Idx3 K) : Matrix Idx3 Idx3 K) *ᵥ v) (embJ a) =
      ((A : Matrix Idx2 Idx2 K) *ᵥ (v ∘ embJ)) a :=
  embMatHom_mulVec_j (A : Matrix Idx2 Idx2 K) v a

private theorem embGL_mulVec_k {K : Type} [Field K]
    (A : GL Idx2 K) (v : Idx3 → K) (t : Fin 2) :
    (((embGL K A : GL Idx3 K) : Matrix Idx3 Idx3 K) *ᵥ v) (embK t) = v (embK t) :=
  embMatHom_mulVec_k (A : Matrix Idx2 Idx2 K) v t

private theorem quadMinus_split {K : Type} [Field K] (b c : K) (w : Idx3 → K) :
    StatedQuadMinus 3 K b c w =
      w (Sum.inl 0) * w (Sum.inr (Sum.inl 0)) + StatedQuadMinus 2 K b c (w ∘ embJ) := by
  simp only [StatedQuadMinus, CFSG.MatrixModel.minusQuadCore]
  have h3 : (∑ i : Fin (3 - 1), w (Sum.inl i) * w (Sum.inr (Sum.inl i))) =
      w (Sum.inl 0) * w (Sum.inr (Sum.inl 0)) +
        w (Sum.inl 1) * w (Sum.inr (Sum.inl 1)) := by
    change (∑ i : Fin 2, w (Sum.inl i) * w (Sum.inr (Sum.inl i))) = _
    rw [Fin.sum_univ_two]
  have h1 : (∑ i : Fin (2 - 1), (w ∘ embJ) (Sum.inl i) *
      (w ∘ embJ) (Sum.inr (Sum.inl i))) = w (Sum.inl 1) * w (Sum.inr (Sum.inl 1)) := by
    change (∑ i : Fin 1, (w ∘ embJ) (Sum.inl i) * (w ∘ embJ) (Sum.inr (Sum.inl i))) = _
    rw [Fin.sum_univ_one]
    rfl
  rw [h3, h1]
  simp only [Function.comp_apply, embJ, embFun]
  ring

private theorem emb_mem_isometry {K : Type} [Field K] (b c : K) {A : GL Idx2 K}
    (hA : ∀ v, StatedQuadMinus 2 K b c ((A : Matrix Idx2 Idx2 K) *ᵥ v) =
      StatedQuadMinus 2 K b c v) :
    ∀ w, StatedQuadMinus 3 K b c (((embGL K A : GL Idx3 K) : Matrix Idx3 Idx3 K) *ᵥ w) =
      StatedQuadMinus 3 K b c w := by
  intro w
  rw [quadMinus_split, quadMinus_split]
  have hx : (((embGL K A : GL Idx3 K) : Matrix Idx3 Idx3 K) *ᵥ w) (Sum.inl 0) = w (Sum.inl 0) :=
    embGL_mulVec_k A w 0
  have hy : (((embGL K A : GL Idx3 K) : Matrix Idx3 Idx3 K) *ᵥ w) (Sum.inr (Sum.inl 0)) =
      w (Sum.inr (Sum.inl 0)) :=
    embGL_mulVec_k A w 1
  have hq : (((embGL K A : GL Idx3 K) : Matrix Idx3 Idx3 K) *ᵥ w) ∘ embJ =
      (A : Matrix Idx2 Idx2 K) *ᵥ (w ∘ embJ) := by
    funext a
    exact embGL_mulVec_j A w a
  rw [hx, hy, hq, hA]

private theorem emb_map_isom_le {K : Type} [Field K] (b c : K) :
    (CFSG.MatrixModel.isometryCore (StatedQuadMinus 2 K b c)).map (embGL K) ≤
      CFSG.MatrixModel.isometryCore (StatedQuadMinus 3 K b c) := by
  rw [CFSG.MatrixModel.isometryCore, MonoidHom.map_closure]
  refine Subgroup.closure_mono ?_
  rintro _ ⟨A, hA, rfl⟩
  exact emb_mem_isometry b c hA

private theorem emb_mem_statedOmega {K : Type} [Field K] (b c : K) {g : GL Idx2 K}
    (hg : g ∈ StatedOmega (StatedQuadMinus 2 K b c)) :
    embGL K g ∈ StatedOmega (StatedQuadMinus 3 K b c) := by
  have hmap : (StatedOmega (StatedQuadMinus 2 K b c)).map (embGL K) ≤
      StatedOmega (StatedQuadMinus 3 K b c) := by
    rw [StatedOmega, StatedOmega, Subgroup.map_commutator]
    exact Subgroup.commutator_mono (emb_map_isom_le b c) (emb_map_isom_le b c)
  exact hmap (Subgroup.mem_map_of_mem (embGL K) hg)

private theorem embMatHom_injective {K : Type} [Field K] :
    Function.Injective (embMatHom K) := by
  intro A B h
  ext a b
  have h' := congrFun (congrFun h (embJ a)) (embJ b)
  simpa [embMatHom, embEquiv_symm_j, Matrix.fromBlocks_apply₁₁] using h'

private theorem embGL_injective {K : Type} [Field K] :
    Function.Injective (embGL K) := by
  intro A B h
  apply Units.ext
  apply embMatHom_injective
  exact congrArg (fun u : GL Idx3 K => (u : Matrix Idx3 Idx3 K)) h

private theorem embJ_ne_x0 (a : Idx2) :
    embJ a ≠ (Sum.inl 0 : Idx3) := by
  rcases a with i | (j | k)
  · fin_cases i
    decide
  · fin_cases j
    decide
  · fin_cases k <;> decide

private theorem embGL_mulVec_single_x0 {K : Type} [Field K] (A : GL Idx2 K) :
    (((embGL K A : GL Idx3 K) : Matrix Idx3 Idx3 K) *ᵥ
        Pi.single (Sum.inl (0 : Fin (3 - 1))) (1 : K)) =
      Pi.single (Sum.inl (0 : Fin (3 - 1))) (1 : K) := by
  funext i
  obtain ⟨x, rfl⟩ : ∃ x, embEquiv x = i := ⟨embEquiv.symm i, embEquiv.apply_symm_apply i⟩
  rcases x with a | t
  · rw [show embEquiv (Sum.inl a) = embJ a from rfl, embGL_mulVec_j]
    have hv : (Pi.single (Sum.inl (0 : Fin (3 - 1))) (1 : K) : Idx3 → K) ∘ embJ = 0 := by
      funext c
      exact Pi.single_eq_of_ne (M := fun _ : Idx3 => K) (h := embJ_ne_x0 c) (x := (1 : K))
    rw [hv, Matrix.mulVec_zero]
    simp only [Pi.zero_apply]
    exact (Pi.single_eq_of_ne (M := fun _ : Idx3 => K) (h := embJ_ne_x0 a)
      (x := (1 : K))).symm
  · rw [show embEquiv (Sum.inr t) = embK t from rfl, embGL_mulVec_k]

private def flip0 : Equiv.Perm Idx3 := minusFlip (3 - 1) ⟨0, by norm_num⟩

private def flip1 : Equiv.Perm Idx3 := minusFlip (3 - 1) ⟨1, by norm_num⟩

private def flipS : Equiv.Perm Idx2 := minusFlip (2 - 1) ⟨0, by norm_num⟩

private theorem flip0_inv : (flip0 : Equiv.Perm Idx3)⁻¹ = flip0 :=
  minusFlip_inv (3 - 1) ⟨0, by norm_num⟩

private theorem flip1_inv : (flip1 : Equiv.Perm Idx3)⁻¹ = flip1 :=
  minusFlip_inv (3 - 1) ⟨1, by norm_num⟩

private theorem flipS_inv : (flipS : Equiv.Perm Idx2)⁻¹ = flipS :=
  minusFlip_inv (2 - 1) ⟨0, by norm_num⟩

private theorem flip0_embJ (a : Idx2) : flip0 (embJ a) = embJ a := by
  rcases a with i | (j | k)
  · fin_cases i; decide
  · fin_cases j; decide
  · fin_cases k <;> decide

private theorem flip0_embK (t : Fin 2) : flip0 (embK t) = embK (Equiv.swap 0 1 t) := by
  fin_cases t <;> decide

private theorem flip1_embK (t : Fin 2) : flip1 (embK t) = embK t := by
  fin_cases t <;> decide

private theorem embJ_flipS (a : Idx2) : embJ (flipS a) = flip1 (embJ a) := by
  rcases a with i | (j | k)
  · fin_cases i; decide
  · fin_cases j; decide
  · fin_cases k <;> decide

private theorem embGL_commute_flip0 {K : Type} [Field K] (A : GL Idx2 K) :
    Commute (embGL K A) (permGL (K := K) flip0) := by
  change (embGL K A) * permGL (K := K) flip0 = permGL (K := K) flip0 * embGL K A
  apply Units.ext
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  funext i
  obtain ⟨x, rfl⟩ : ∃ x, embEquiv x = i := ⟨embEquiv.symm i, embEquiv.apply_symm_apply i⟩
  rcases x with a | t
  · rw [show embEquiv (Sum.inl a) = embJ a from rfl]
    simp only [Units.val_mul, ← Matrix.mulVec_mulVec, mulVec_permGL, Function.comp_apply]
    rw [flip0_inv, flip0_embJ a, embGL_mulVec_j, embGL_mulVec_j]
    rfl
  · rw [show embEquiv (Sum.inr t) = embK t from rfl]
    simp only [Units.val_mul, ← Matrix.mulVec_mulVec, mulVec_permGL, Function.comp_apply]
    rw [flip0_inv, flip0_embK t, embGL_mulVec_k, embGL_mulVec_k, Function.comp_apply,
      flip0_embK t]

private theorem embGL_permGL_flipS {K : Type} [Field K] :
    embGL K (permGL (K := K) flipS) = permGL (K := K) flip1 := by
  apply Units.ext
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  funext i
  obtain ⟨x, rfl⟩ : ∃ x, embEquiv x = i := ⟨embEquiv.symm i, embEquiv.apply_symm_apply i⟩
  rcases x with a | t
  · rw [show embEquiv (Sum.inl a) = embJ a from rfl]
    simp only [embGL_mulVec_j, mulVec_permGL, Function.comp_apply]
    rw [flipS_inv, flip1_inv, embJ_flipS a]
  · rw [show embEquiv (Sum.inr t) = embK t from rfl]
    simp only [embGL_mulVec_k, mulVec_permGL, Function.comp_apply]
    rw [flip1_inv, flip1_embK t]

theorem exists_omegaEmbed (b c : K) :
    ∃ E : GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K →* GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K,
      Function.Injective E ∧
      (∀ g ∈ StatedOmega (StatedQuadMinus 2 K b c),
        E g ∈ StatedOmega (StatedQuadMinus 3 K b c)) ∧
      (∀ g, ((E g : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K) :
          Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K) *ᵥ
            Pi.single (Sum.inl ⟨0, by norm_num⟩) 1 = Pi.single (Sum.inl ⟨0, by norm_num⟩) 1) ∧
      (∀ g, Commute (E g) (permGL (minusFlip (3 - 1) ⟨0, by norm_num⟩))) ∧
      E (permGL (minusFlip (2 - 1) ⟨0, by norm_num⟩)) =
        permGL (minusFlip (3 - 1) ⟨1, by norm_num⟩) := by
  refine ⟨embGL K, embGL_injective, ?_, ?_, ?_, ?_⟩
  · intro g hg
    exact emb_mem_statedOmega b c hg
  · intro g
    exact embGL_mulVec_single_x0 g
  · intro g
    exact embGL_commute_flip0 g
  · exact embGL_permGL_flipS

end CFSG.LocalAnalysis.UniquenessCase.UC22.KGen
