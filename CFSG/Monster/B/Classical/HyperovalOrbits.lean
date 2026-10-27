module

public import CFSG.Monster.B.Classical.Hyperoval
import all CFSG.Fischer.F4
public import CFSG.Monster.B.Classical.PlaneAut
public import Mathlib.LinearAlgebra.Projectivization.Action
public import Mathlib.Tactic.Monotonicity.Lemmas
public import Mathlib.Topology.Sheaves.Presheaf

public section

namespace CFSG.Monster.B.Classical.Plane

open CFSG.Fischer
open scoped LinearAlgebra.Projectivization MatrixGroups Matrix

@[expose] noncomputable def pslPerm : PSL(3, F4) →* Equiv.Perm (Fin 21) :=
  Ωproj.symm.permCongrHom.toMonoidHom.comp (MulAction.toPermHom PSL(3, F4) (ℙ F4 (Fin 3 → F4)))

theorem pslPerm_apply (g : PSL(3, F4)) (i : Fin 21) : pslPerm g i = Ωproj.symm (g • Ωproj i) :=
  rfl

theorem pslPerm_mk_apply (M : Matrix.SpecialLinearGroup (Fin 3) F4) (i : Fin 21) :
    pslPerm (M : PSL(3, F4)) i = normIdx ((M : Matrix (Fin 3) (Fin 3) F4) *ᵥ Ω i) := by
  rw [pslPerm_apply, Matrix.ProjectiveSpecialLinearGroup.smul_proj_mk, Ωproj_apply,
    Projectivization.smul_mk, Ωproj_symm_mk]
  rfl

@[expose] def maskImage (f : Fin 21 → Fin 21) (m : ℕ) : ℕ :=
  ∑ i : Fin 21, if m.testBit i then 2 ^ (f i : ℕ) else 0

theorem mask_map_ofMask (σ : Equiv.Perm (Fin 21)) (m : ℕ) :
    mask ((ofMask m : Finset (Fin 21)).map σ.toEmbedding) = maskImage σ m := by
  rw [mask, Finset.sum_map, ofMask, Finset.sum_filter]
  rfl

theorem map_ofMask_eq_ofMask {σ : Equiv.Perm (Fin 21)} {m n : ℕ} (h : maskImage σ m = n) :
    (ofMask m : Finset (Fin 21)).map σ.toEmbedding = ofMask n := by
  rw [← h, ← mask_map_ofMask, ofMask_mask]

@[expose] def PreservesOrbits (N : Matrix (Fin 3) (Fin 3) F4) : Prop :=
  ∀ k : Fin 3, ∀ m ∈ orbMasks k, maskImage (fun i => normIdx (N *ᵥ Ω i)) m ∈ orbMasks k

instance (N : Matrix (Fin 3) (Fin 3) F4) : Decidable (PreservesOrbits N) := by
  unfold PreservesOrbits; infer_instance

set_option maxHeartbeats 8000000 in
theorem preservesOrbits_transvection : ∀ i j : Fin 3, i ≠ j → ∀ a : F4,
    PreservesOrbits (1 + Matrix.single i j a) := by
  decide +kernel

set_option maxHeartbeats 8000000 in
theorem preservesOrbits_diag : ∀ i j : Fin 3, i ≠ j → ∀ c : F4, c ≠ 0 →
    PreservesOrbits (Matrix.diagonal fun k => if k = i then c else if k = j then c⁻¹ else 1) := by
  decide +kernel

theorem map_mem_O_of_preserves
    (M : Matrix.SpecialLinearGroup (Fin 3) F4)
    (hM : PreservesOrbits (M : Matrix (Fin 3) (Fin 3) F4)) {k : Fin 3} {A : Finset (Fin 21)}
    (hA : A ∈ O k) : A.map (pslPerm (M : PSL(3, F4))).toEmbedding ∈ O k := by
  rw [mem_O] at hA ⊢
  rw [← ofMask_mask A, mask_map_ofMask]
  have : (⇑(pslPerm (M : PSL(3, F4))) : Fin 21 → Fin 21) =
      fun i => normIdx ((M : Matrix (Fin 3) (Fin 3) F4) *ᵥ Ω i) :=
    funext (pslPerm_mk_apply M)
  rw [this]
  exact (show ∀ k : Fin 3, ∀ m ∈ orbMasks k, _ from hM) k _ hA

theorem preservesOrbits_coe_transvection {i j : Fin 3} (hij : i ≠ j) (a : F4) :
    PreservesOrbits (Matrix.SpecialLinearGroup.transvection hij a : Matrix (Fin 3) (Fin 3) F4) := by
  rw [Matrix.SpecialLinearGroup.transvection_coe]
  exact preservesOrbits_transvection i j hij a

theorem preservesOrbits_coe_diag2n {i j : Fin 3} (hij : i ≠ j) {c : F4} (hc : c ≠ 0) :
    PreservesOrbits (Matrix.SpecialLinearGroup.diag2n hij c hc : Matrix (Fin 3) (Fin 3) F4) := by
  rw [Matrix.SpecialLinearGroup.diag2n_coe]
  exact preservesOrbits_diag i j hij c hc

theorem map_pslPerm_mul (g h : PSL(3, F4)) (A : Finset (Fin 21)) :
    A.map (pslPerm (g * h)).toEmbedding =
      (A.map (pslPerm h).toEmbedding).map (pslPerm g).toEmbedding := by
  rw [Finset.map_map, map_mul]
  rfl

theorem map_mem_O_aux
    (k : Fin 3) (M : Matrix.SpecialLinearGroup (Fin 3) F4) :
    ∀ A ∈ O k, A.map (pslPerm (M : PSL(3, F4))).toEmbedding ∈ O k := by
  refine Matrix.SpecialLinearGroup.diagonal_transvection_induction'
    (fun M : Matrix.SpecialLinearGroup (Fin 3) F4 =>
      ∀ A ∈ O k, A.map (pslPerm (M : PSL(3, F4))).toEmbedding ∈ O k) M ?_ ?_ ?_
  · intro i j hij c hc A hA
    exact map_mem_O_of_preserves (Matrix.SpecialLinearGroup.diag2n hij c hc)
      (preservesOrbits_coe_diag2n hij hc) hA
  · intro i j hij a A hA
    exact map_mem_O_of_preserves (Matrix.SpecialLinearGroup.transvection hij a)
      (preservesOrbits_coe_transvection hij a) hA
  · intro M N hM hN A hA
    rw [show ((M * N : Matrix.SpecialLinearGroup (Fin 3) F4) : PSL(3, F4)) =
      (M : PSL(3, F4)) * (N : PSL(3, F4)) from rfl, map_pslPerm_mul]
    exact hM _ (hN A hA)

theorem map_mem_O
    (g : PSL(3, F4)) {k : Fin 3} {A : Finset (Fin 21)} (hA : A ∈ O k) :
    A.map (pslPerm g).toEmbedding ∈ O k := by
  obtain ⟨M, rfl⟩ := QuotientGroup.mk_surjective g
  exact map_mem_O_aux k M A hA

@[expose] def genI : Fin 12 → Fin 3 := ![0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2]

@[expose] def genJ : Fin 12 → Fin 3 := ![1, 1, 2, 2, 0, 0, 2, 2, 0, 0, 1, 1]

@[expose] def genA : Fin 12 → F4 := ![1, F4.ω, 1, F4.ω, 1, F4.ω, 1, F4.ω, 1, F4.ω, 1, F4.ω]

theorem genI_ne_genJ : ∀ t : Fin 12, genI t ≠ genJ t := by decide

@[expose] def genSL (t : Fin 12) : Matrix.SpecialLinearGroup (Fin 3) F4 :=
  Matrix.SpecialLinearGroup.transvection (genI_ne_genJ t) (genA t)

@[expose] def genPerm : Fin 12 → Fin 21 → Fin 21 :=
  ![![0, 9, 10, 11, 12, 5, 6, 7, 8, 1, 2, 3, 4, 17, 19, 20, 18, 13, 16, 14, 15],
    ![0, 17, 20, 18, 19, 5, 6, 7, 8, 13, 15, 16, 14, 9, 12, 10, 11, 1, 3, 4, 2],
    ![6, 1, 10, 18, 14, 5, 0, 8, 7, 9, 2, 16, 19, 13, 4, 20, 11, 17, 3, 12, 15],
    ![8, 1, 20, 16, 12, 5, 7, 6, 0, 9, 15, 18, 4, 13, 19, 10, 3, 17, 11, 14, 2],
    ![0, 1, 2, 3, 4, 9, 10, 11, 12, 5, 6, 7, 8, 17, 18, 19, 20, 13, 14, 15, 16],
    ![0, 1, 2, 3, 4, 13, 14, 15, 16, 17, 18, 19, 20, 5, 6, 7, 8, 9, 10, 11, 12],
    ![2, 1, 0, 4, 3, 5, 10, 15, 20, 9, 6, 19, 16, 13, 18, 7, 12, 17, 14, 11, 8],
    ![4, 1, 3, 2, 0, 5, 14, 19, 12, 9, 18, 15, 8, 13, 6, 11, 20, 17, 10, 7, 16],
    ![0, 1, 2, 3, 4, 6, 5, 8, 7, 10, 9, 12, 11, 14, 13, 16, 15, 18, 17, 20, 19],
    ![0, 1, 2, 3, 4, 7, 8, 5, 6, 11, 12, 9, 10, 15, 16, 13, 14, 19, 20, 17, 18],
    ![0, 2, 1, 4, 3, 5, 6, 7, 8, 10, 9, 12, 11, 15, 16, 13, 14, 20, 19, 18, 17],
    ![0, 3, 4, 1, 2, 5, 6, 7, 8, 11, 12, 9, 10, 16, 15, 14, 13, 18, 17, 20, 19]]

theorem genPerm_spec : ∀ (t : Fin 12) (p : Fin 21),
    normIdx ((1 + Matrix.single (genI t) (genJ t) (genA t)) *ᵥ Ω p) = genPerm t p := by
  decide +kernel

theorem pslPerm_genSL (t : Fin 12) : ⇑(pslPerm (genSL t : PSL(3, F4))) = genPerm t := by
  funext p
  rw [pslPerm_mk_apply, genSL, Matrix.SpecialLinearGroup.transvection_coe, genPerm_spec]

@[expose, irreducible] def orbCert' : Fin 3 → List (ℕ × Fin 12) :=
  ![[(0, 0), (0, 1), (0, 2), (0, 3), (0, 5), (0, 9), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 7),
    (2, 2), (2, 3), (2, 4), (2, 9), (3, 3), (3, 5), (3, 9), (3, 11), (4, 8), (5, 0), (5, 1), (5, 9),
    (5, 11), (6, 1), (6, 3), (6, 7), (7, 3), (7, 4), (7, 5), (7, 6), (8, 4), (8, 5), (8, 9), (9, 4),
    (9, 5), (9, 8), (11, 1), (11, 7), (12, 10), (13, 4), (13, 8), (13, 9), (14, 4), (15, 11), (17,
    8), (19, 3), (19, 11), (23, 5), (23, 10), (24, 3), (27, 4), (29, 4), (40, 10)],
    [(0, 0), (0, 1), (0, 2), (0, 3), (0, 5), (0, 6), (0, 8), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5),
      (2, 2), (2, 3), (2, 4), (2, 8), (3, 5), (3, 8), (3, 9), (4, 5), (4, 8), (4, 9), (5, 1), (5,
      6), (5, 8), (6, 0), (6, 1), (6, 8), (7, 2), (7, 3), (7, 7), (8, 2), (8, 4), (9, 4), (9, 5),
      (9, 8), (10, 5), (11, 2), (11, 5), (12, 1), (13, 4), (14, 9), (15, 8), (18, 2), (19, 0), (19,
      2), (21, 2), (22, 3), (23, 5), (23, 11), (25, 2), (26, 5), (27, 4), (31, 11), (32, 4)],
    [(0, 1), (0, 2), (0, 5), (0, 6), (0, 8), (0, 10), (1, 2), (1, 4), (1, 5), (1, 8), (1, 9), (1,
      10), (2, 4), (2, 7), (2, 8), (2, 10), (2, 11), (3, 6), (3, 8), (3, 10), (3, 11), (4, 8), (4,
      10), (5, 0), (5, 2), (6, 6), (7, 4), (7, 6), (7, 7), (8, 5), (8, 8), (8, 9), (9, 8), (9, 9),
      (10, 2), (10, 3), (11, 2), (11, 3), (12, 4), (12, 5), (13, 7), (13, 10), (14, 8), (14, 11),
      (15, 0), (15, 2), (16, 4), (16, 6), (20, 2), (21, 6), (23, 6), (24, 2), (24, 6), (28, 9), (41,
      11)]]

theorem orbCert'_valid : ∀ k : Fin 3, ∀ t < 55,
    ((orbCert' k).getD t (0, 0)).1 < t + 1 ∧
      maskImage (genPerm ((orbCert' k).getD t (0, 0)).2)
        ((orbMasks k).getD ((orbCert' k).getD t (0, 0)).1 0) = (orbMasks k).getD (t + 1) 0 := by
  decide +kernel

theorem length_orbMasks : ∀ k : Fin 3, (orbMasks k).length = 56 := by decide +kernel

theorem reach (k : Fin 3) : ∀ t < 56, ∃ g : PSL(3, F4),
    (ofMask ((orbMasks k).getD 0 0) : Finset (Fin 21)).map (pslPerm g).toEmbedding =
      ofMask ((orbMasks k).getD t 0) := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro ht
    rcases t with _ | t
    · exact ⟨1, by rw [map_one]; exact Finset.map_refl⟩
    · obtain ⟨hp, himg⟩ := orbCert'_valid k t (by omega)
      generalize (orbCert' k).getD t (0, 0) = q at hp himg
      obtain ⟨g, hg⟩ := ih q.1 hp (by omega)
      refine ⟨genSL q.2 * g, ?_⟩
      have h2 := map_ofMask_eq_ofMask (σ := pslPerm (genSL q.2))
        (m := (orbMasks k).getD q.1 0) (n := (orbMasks k).getD (t + 1) 0)
        (by rw [pslPerm_genSL]; exact himg)
      rw [← h2, ← hg, map_pslPerm_mul]

theorem exists_eq_ofMask_of_mem_O {k : Fin 3} {A : Finset (Fin 21)} (hA : A ∈ O k) :
    ∃ t < 56, A = ofMask ((orbMasks k).getD t 0) := by
  simp only [O, List.mem_toFinset, List.mem_map] at hA
  obtain ⟨m, hm, rfl⟩ := hA
  obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hm
  exact ⟨t, by rw [← length_orbMasks k]; exact ht, by rw [List.getD_eq_getElem]⟩

theorem orbit_O {k : Fin 3} {A : Finset (Fin 21)} (hA : A ∈ O k) :
    {B | ∃ g : PSL(3, F4), A.map (pslPerm g).toEmbedding = B} = (O k : Set (Finset (Fin 21))) := by
  ext B
  simp only [Set.mem_ofPred_eq, Finset.mem_coe]
  constructor
  · rintro ⟨g, rfl⟩
    exact map_mem_O g hA
  · intro hB
    obtain ⟨s, hs, rfl⟩ := exists_eq_ofMask_of_mem_O hA
    obtain ⟨u, hu, rfl⟩ := exists_eq_ofMask_of_mem_O hB
    obtain ⟨g, hg⟩ := reach k s hs
    obtain ⟨h, hh⟩ := reach k u hu
    refine ⟨h * g⁻¹, ?_⟩
    rw [← hg, ← hh, map_pslPerm_mul, ← map_pslPerm_mul g⁻¹ g, inv_mul_cancel, map_one]
    exact congrArg (Finset.map _) Finset.map_refl

theorem leastMask_le : ∀ k : Fin 3, ∀ m ∈ orbMasks k, leastMask k ≤ m := by decide +kernel

theorem orbMasks_head : ∀ k : Fin 3, (orbMasks k).getD 0 0 = leastMask k := by decide +kernel

theorem leastMask_spec (k : Fin 3) :
    (∀ A ∈ O k, leastMask k ≤ mask A) ∧ ∃ A ∈ O k, mask A = leastMask k := by
  refine ⟨fun A hA => leastMask_le k _ (mem_O.1 hA), ofMask (leastMask k), ?_, ?_⟩
  · rw [mem_O, ← orbMasks_head k, mask_ofMask_orbMasks k _ (by
      rw [orbMasks_head]; revert k; decide +kernel)]
    rw [orbMasks_head]; revert k; decide +kernel
  · rw [← orbMasks_head k, mask_ofMask_orbMasks k _ (by
      rw [orbMasks_head]; revert k; decide +kernel)]

@[expose] def dMat : Matrix (Fin 3) (Fin 3) F4 := Matrix.diagonal ![F4.ω, 1, 1]

theorem dMat_mulVec_injective : Function.Injective (Matrix.mulVecLin dMat) := by
  intro v w h
  revert v w
  decide +kernel

@[expose] noncomputable def dProj : ℙ F4 (Fin 3 → F4) → ℙ F4 (Fin 3 → F4) :=
  Projectivization.map (Matrix.mulVecLin dMat) dMat_mulVec_injective

@[expose] def dPermFn : Fin 21 → Fin 21 := ![0, 1, 2, 3, 4, 5, 8, 6, 7, 17, 20, 18, 19, 9, 12, 10,
  11, 13, 16, 14, 15]

theorem dPermFn_spec : ∀ p : Fin 21, normIdx (dMat *ᵥ Ω p) = dPermFn p := by decide +kernel

theorem dProj_Ωproj (p : Fin 21) : Ωproj.symm (dProj (Ωproj p)) = dPermFn p := by
  rw [dProj, Ωproj_apply, Projectivization.map_mk, Ωproj_symm_mk, Matrix.mulVecLin_apply,
    dPermFn_spec]

theorem dPermFn_injective : Function.Injective dPermFn := by decide

@[expose] noncomputable def dPerm : Equiv.Perm (Fin 21) :=
  Equiv.ofBijective dPermFn (Finite.injective_iff_bijective.1 dPermFn_injective)

theorem coe_dPerm : ⇑dPerm = dPermFn := rfl

@[expose] def setImage (σ : Equiv.Perm (Fin 21)) (𝒪 : Finset (Finset (Fin 21))) :
    Finset (Finset (Fin 21)) :=
  𝒪.image fun A => A.map σ.toEmbedding

theorem setImage_mul (σ τ : Equiv.Perm (Fin 21)) (𝒪 : Finset (Finset (Fin 21))) :
    setImage (σ * τ) 𝒪 = setImage σ (setImage τ 𝒪) := by
  rw [setImage, setImage, setImage, Finset.image_image]
  congr 1
  funext A
  simp only [Function.comp_apply, Finset.map_map]
  congr 1

theorem setImage_one (𝒪 : Finset (Finset (Fin 21))) : setImage 1 𝒪 = 𝒪 := by
  have : (fun A : Finset (Fin 21) => A.map (1 : Equiv.Perm (Fin 21)).toEmbedding) = id :=
    funext fun A => Finset.map_refl
  rw [setImage, this, Finset.image_id]

theorem card_setImage (σ : Equiv.Perm (Fin 21)) (𝒪 : Finset (Finset (Fin 21))) :
    (setImage σ 𝒪).card = 𝒪.card :=
  Finset.card_image_of_injective _ (Finset.map_injective _)

theorem dPerm_orbMasks : ∀ k : Fin 3, ∀ m ∈ orbMasks k, maskImage dPermFn m ∈ orbMasks (k + 1) := by
  decide +kernel

theorem setImage_dPerm_O
    (k : Fin 3) : setImage dPerm (O k) = O (k + 1) := by
  refine Finset.eq_of_subset_of_card_le ?_ (by rw [card_setImage, card_O, card_O])
  intro B hB
  obtain ⟨A, hA, rfl⟩ := Finset.mem_image.1 hB
  rw [mem_O] at hA ⊢
  rw [← ofMask_mask A, mask_map_ofMask, coe_dPerm]
  exact dPerm_orbMasks k _ hA

theorem dPerm_mem_lineAut : dPerm ∈ lineAut := by
  intro a
  have h : ∀ a : Fin 21, ∃ b : Fin 21, maskImage dPermFn (lineMask a) = lineMask b := by
    decide +kernel
  obtain ⟨b, hb⟩ := h a
  refine ⟨b, ?_⟩
  have h1 : projLine a = ofMask (lineMask a) := by rw [← mask_projLine, ofMask_mask]
  have h2 : projLine b = ofMask (lineMask b) := by rw [← mask_projLine, ofMask_mask]
  rw [h1, h2]
  exact map_ofMask_eq_ofMask (by rw [coe_dPerm]; exact hb)

theorem setImage_dPerm_pow_O (k j : Fin 3) :
    setImage (dPerm ^ (j : ℕ)) (O k) = O (k + j) := by
  match j with
  | 0 => simp [setImage_one]
  | 1 => simp [setImage_dPerm_O]
  | 2 =>
    rw [show ((2 : Fin 3) : ℕ) = 2 from rfl, pow_two, setImage_mul, setImage_dPerm_O,
      setImage_dPerm_O, add_assoc]
    rfl

theorem card_stab_O_le (k : Fin 3) :
    Nat.card {σ : lineAut // setImage σ (O k) = O k} ≤ 40320 := by
  let Φ : {σ : lineAut // setImage σ (O k) = O k} × Fin 3 → lineAut := fun p =>
    ⟨dPerm ^ (p.2 : ℕ) * p.1.1, mul_mem (pow_mem dPerm_mem_lineAut _) p.1.1.2⟩
  have hΦ : Function.Injective Φ := by
    rintro ⟨⟨σ, hσ⟩, j⟩ ⟨⟨τ, hτ⟩, l⟩ h
    have h' : dPerm ^ (j : ℕ) * (σ : Equiv.Perm (Fin 21)) =
        dPerm ^ (l : ℕ) * (τ : Equiv.Perm (Fin 21)) := congrArg Subtype.val h
    have hO := congrArg (fun π => setImage π (O k)) h'
    simp only [setImage_mul, hσ, hτ, setImage_dPerm_pow_O] at hO
    have hjl : j = l := by
      by_contra hne
      exact O_ne (fun he => hne (add_left_cancel he)) hO
    subst hjl
    have hστ : (σ : Equiv.Perm (Fin 21)) = τ := mul_left_cancel h'
    have : σ = τ := Subtype.ext hστ
    subst this
    rfl
  have h1 := Nat.card_le_card_of_injective Φ hΦ
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin] at h1
  have h2 := card_lineAut_le
  omega

@[expose] def pslOrbit (A : Finset (Fin 21)) : Set (Finset (Fin 21)) :=
  {B | ∃ g : PSL(3, F4), A.map (pslPerm g).toEmbedding = B}

theorem pslOrbits_hyperovals :
    {S | ∃ A ∈ hyperovals, S = pslOrbit A} =
      {(O 0 : Set (Finset (Fin 21))), (O 1 : Set (Finset (Fin 21))),
        (O 2 : Set (Finset (Fin 21)))} := by
  ext S
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨A, hA, rfl⟩
    rw [hyperovals_eq, Finset.mem_union, Finset.mem_union] at hA
    rcases hA with (hA | hA) | hA
    · exact Or.inl (orbit_O hA)
    · exact Or.inr (Or.inl (orbit_O hA))
    · exact Or.inr (Or.inr (orbit_O hA))
  · have hne : ∀ i, (O i).Nonempty := fun i => by
      rw [← Finset.card_pos, card_O]; norm_num
    have hmem : ∀ i, ∀ A ∈ O i, A ∈ O 0 ∪ O 1 ∪ O 2 := fun i A hA => by
      match i, hA with
      | 0, hA => exact Finset.mem_union_left _ (Finset.mem_union_left _ hA)
      | 1, hA => exact Finset.mem_union_left _ (Finset.mem_union_right _ hA)
      | 2, hA => exact Finset.mem_union_right _ hA
    have key : ∀ i, ∃ A ∈ hyperovals, (O i : Set (Finset (Fin 21))) = pslOrbit A := fun i => by
      obtain ⟨A, hA⟩ := hne i
      refine ⟨A, ?_, (orbit_O hA).symm⟩
      rw [hyperovals_eq]
      exact hmem i A hA
    rintro (rfl | rfl | rfl)
    · exact key 0
    · exact key 1
    · exact key 2

theorem four_field_projective_plane_hyperoval_census :
    ((∀ i, IsNormalized (Ω i)) ∧ (∀ v, IsNormalized v → ∃ i, Ω i = v) ∧
      StrictMono fun i => lexKey (Ω i)) ∧
    hyperovals.card = 168 ∧
    hyperovals = O 0 ∪ O 1 ∪ O 2 ∧ (∀ i j : Fin 3, i ≠ j → Disjoint (O i) (O j)) ∧
    (∀ i, (O i).card = 56) ∧
    (∀ i, ∀ A ∈ O i, pslOrbit A = (O i : Set (Finset (Fin 21)))) ∧
    {S | ∃ A ∈ hyperovals, S = pslOrbit A} =
      {(O 0 : Set (Finset (Fin 21))), (O 1 : Set (Finset (Fin 21))),
        (O 2 : Set (Finset (Fin 21)))} ∧
    (∀ i, (∀ A ∈ O i, leastMask i ≤ mask A) ∧ ∃ A ∈ O i, mask A = leastMask i) ∧
    leastMask 0 = 1656 ∧ leastMask 1 = 2740 ∧ leastMask 2 = 3276 ∧
    (∀ p, dPerm p = Ωproj.symm (dProj (Ωproj p))) ∧
    (∀ i, setImage dPerm (O i) = O (i + 1)) ∧
    Nat.card lineAut ≤ 120960 ∧
    ∀ i, Nat.card {σ : lineAut // setImage σ (O i) = O i} ≤ 40320 :=
  ⟨Ω_spec, card_hyperovals, hyperovals_eq, fun _ _ h => disjoint_O h, card_O,
    fun _ _ hA => orbit_O hA, pslOrbits_hyperovals, leastMask_spec, rfl, rfl, rfl,
    fun p => (dProj_Ωproj p).symm, setImage_dPerm_O, card_lineAut_le, card_stab_O_le⟩

end CFSG.Monster.B.Classical.Plane
