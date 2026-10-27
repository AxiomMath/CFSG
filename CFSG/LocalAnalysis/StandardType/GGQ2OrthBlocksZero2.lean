module

public import CFSG.LocalAnalysis.StandardType.GGQ2OrthBlocksZero5

public section

namespace CFSG.StandardType.GGQ2Frame.OrthBlocks

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.SpJoin
  CFSG.StandardType.ClassicalPosition CFSG.ClassicalInvolution.Models.SymplecticPairs Matrix
open CFSG.Open (StatedSp)
open scoped BigOperators

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

variable {K : Type} [Field K] [Finite K] [CharP K 2]
variable (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K)

section CharTwo

omit [Finite K] [CharP K 2] in
private theorem mulVec_comp_embSum (t : ℕ) (δ : Fin 2) (S : Finset (Fin t))
    (M : Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
      (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K)
    (w : Fin (t + δ.val) ⊕ Fin (t + δ.val) → K)
    {z : Fin (t + δ.val) ⊕ Fin (t + δ.val)}
    (h : ∀ q : Fin (t + δ.val) ⊕ Fin (t + δ.val),
      q ∉ Set.range (embSum t δ S) → M z q = 0) :
    (M *ᵥ w) z =
      ∑ x : Fin (S.card + δ.val) ⊕ Fin (S.card + δ.val), M z (embSum t δ S x) *
        w (embSum t δ S x) := by
  rw [Matrix.mulVec_apply]
  change (∑ q : Fin (t + δ.val) ⊕ Fin (t + δ.val), M z q * w q) = _
  exact sum_comp_embSum fun q hq => by rw [h q hq, zero_mul]

omit [Finite K] [CharP K 2] in
theorem orthExt_mem_orthGroup (t : ℕ) (δ : Fin 2) (S : Finset (Fin t))
    {A : GL (Fin (S.card + δ.val) ⊕ Fin (S.card + δ.val)) K}
    (hA : A ∈ LargeEvenOrthGroup (planeQ (K := K) S.card δ)) :
    orthExt t δ S A ∈ LargeEvenOrthGroup (planeQ (K := K) t δ) := by
  rw [CFSG.PGLModel.mem_orthogonalGroup_iff] at hA ⊢
  intro v
  let M : Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
      (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K :=
    (orthExt t δ S A : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K)
  let vS : Fin (S.card + δ.val) ⊕ Fin (S.card + δ.val) → K := fun x => v (embSum t δ S x)
  let w : Fin (t + δ.val) ⊕ Fin (t + δ.val) → K := liftVec t δ S vS
  let vO : Fin (t + δ.val) ⊕ Fin (t + δ.val) → K :=
    fun z => if (WitSpNs.plane z : Fin (t + δ.val)) ∈ liftSupport t δ S then 0 else v z
  have hM_img : ∀ x y, M (embSum t δ S x) (embSum t δ S y) = A x y :=
    fun x y => orthExt_apply_image t δ S A x y
  have hM_not : ∀ {a b : Fin (t + δ.val) ⊕ Fin (t + δ.val)},
      ¬ (a ∈ Set.range (embSum t δ S) ∧ b ∈ Set.range (embSum t δ S)) →
        M a b = (1 : Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
          (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) a b :=
    fun h => orthExt_apply_not_mem t δ S A h
  have hw0 : ∀ z, (WitSpNs.plane z : Fin (t + δ.val)) ∉ liftSupport t δ S → w z = 0 :=
    fun z hz => liftVec_apply_of_plane_not_mem t δ S vS hz
  have hvO0 : ∀ z, (WitSpNs.plane z : Fin (t + δ.val)) ∈ liftSupport t δ S → vO z = 0 :=
    fun z hz => by simp [vO, hz]
  have hwS : ∀ x, w (embSum t δ S x) = vS x := fun x => liftVec_apply_embSum t δ S vS x
  have hw_not : ∀ q, q ∉ Set.range (embSum t δ S) → w q = 0 :=
    fun q hq => liftVec_apply_of_not_mem t δ S vS hq
  have hv : v = w + vO := by
    funext z
    by_cases hz : (WitSpNs.plane z : Fin (t + δ.val)) ∈ liftSupport t δ S
    · obtain ⟨x, rfl⟩ := (mem_range_embSum_iff z).2 hz
      have hxL : (WitSpNs.plane (embSum t δ S x) : Fin (t + δ.val)) ∈
          liftSupport t δ S :=
        (mem_range_embSum_iff (embSum t δ S x)).1 (Set.mem_range_self x)
      rw [Pi.add_apply, hwS, hvO0 _ hxL, add_zero]
    · have hz' : z ∉ Set.range (embSum t δ S) := fun h =>
        hz ((mem_range_embSum_iff z).1 h)
      rw [Pi.add_apply, hw0 z hz, zero_add]
      simp [vO, hz]
  have hQv : planeQ (K := K) t δ v = planeQ (K := K) t δ w + planeQ (K := K) t δ vO := by
    rw [hv]
    exact planeQ_add_of_support t δ S hw0 hvO0
  have hrow : ∀ z, z ∉ Set.range (embSum t δ S) → (M *ᵥ v) z = v z := by
    intro z hz
    have h : (M *ᵥ v) z = ((1 : Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
        (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) *ᵥ v) z := by
      rw [Matrix.mulVec_apply, Matrix.mulVec_apply]
      change (∑ q : Fin (t + δ.val) ⊕ Fin (t + δ.val), M z q * v q) = _
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [hM_not (fun hh => hz hh.1)]
      simp
    rw [h, Matrix.one_mulVec]
  have hMv : M *ᵥ v = M *ᵥ w + vO := by
    funext z
    by_cases hz : (WitSpNs.plane z : Fin (t + δ.val)) ∈ liftSupport t δ S
    · have hz' : z ∈ Set.range (embSum t δ S) := (mem_range_embSum_iff z).2 hz
      have hzero : ∀ q, q ∉ Set.range (embSum t δ S) → M z q = 0 := by
        intro q hq
        have hne : z ≠ q := by rintro rfl; exact hq hz'
        rw [hM_not (fun hh => hq hh.2), Matrix.one_apply_ne hne]
      rw [Pi.add_apply, hvO0 z hz, add_zero]
      calc (M *ᵥ v) z
          = ∑ x : Fin (S.card + δ.val) ⊕ Fin (S.card + δ.val),
              M z (embSum t δ S x) * v (embSum t δ S x) :=
            mulVec_comp_embSum t δ S M v hzero
        _ = ∑ x : Fin (S.card + δ.val) ⊕ Fin (S.card + δ.val),
              M z (embSum t δ S x) * w (embSum t δ S x) := by
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [hwS]
        _ = (M *ᵥ w) z := (mulVec_comp_embSum t δ S M w hzero).symm
    · have hz' : z ∉ Set.range (embSum t δ S) := fun h =>
        hz ((mem_range_embSum_iff z).1 h)
      have hwz : (M *ᵥ w) z = 0 := by
        rw [Matrix.mulVec_apply]
        change (∑ q : Fin (t + δ.val) ⊕ Fin (t + δ.val), M z q * w q) = 0
        refine Finset.sum_eq_zero fun q _ => ?_
        by_cases hq : q ∈ Set.range (embSum t δ S)
        · rw [hM_not (fun hh => hz' hh.1),
            Matrix.one_apply_ne (by rintro rfl; exact hz' hq), zero_mul]
        · rw [hw_not q hq, mul_zero]
      rw [Pi.add_apply, hwz, zero_add]
      exact (hrow z hz').trans (by simp [vO, hz])
  have hQw : planeQ (K := K) t δ w = planeQ (K := K) S.card δ vS := by
    rw [planeQ_lift t δ S hw0]
    congr 1
    funext x
    exact hwS x
  have hMrow : ∀ x, (M *ᵥ w) (embSum t δ S x) =
      ((A : Matrix (Fin (S.card + δ.val) ⊕ Fin (S.card + δ.val))
        (Fin (S.card + δ.val) ⊕ Fin (S.card + δ.val)) K) *ᵥ vS) x := by
    intro x
    have hzero : ∀ q, q ∉ Set.range (embSum t δ S) → M (embSum t δ S x) q = 0 := by
      intro q hq
      have hne : embSum t δ S x ≠ q := fun h => hq (h ▸ Set.mem_range_self x)
      rw [hM_not (fun hh => hq hh.2), Matrix.one_apply_ne hne]
    rw [mulVec_comp_embSum t δ S M w hzero, Matrix.mulVec_apply]
    change (∑ y : Fin (S.card + δ.val) ⊕ Fin (S.card + δ.val),
      M (embSum t δ S x) (embSum t δ S y) * w (embSum t δ S y)) = _
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hM_img, hwS]
    simp
  have hMw0 : ∀ z, (WitSpNs.plane z : Fin (t + δ.val)) ∉ liftSupport t δ S →
      (M *ᵥ w) z = 0 := by
    intro z hz
    have hz' : z ∉ Set.range (embSum t δ S) := fun h => hz ((mem_range_embSum_iff z).1 h)
    rw [Matrix.mulVec_apply]
    change (∑ q : Fin (t + δ.val) ⊕ Fin (t + δ.val), M z q * w q) = 0
    refine Finset.sum_eq_zero fun q _ => ?_
    by_cases hq : q ∈ Set.range (embSum t δ S)
    · rw [hM_not (fun hh => hz' hh.1),
        Matrix.one_apply_ne (by rintro rfl; exact hz' hq), zero_mul]
    · rw [hw_not q hq, mul_zero]
  have hQMw : planeQ (K := K) t δ (M *ᵥ w) = planeQ (K := K) S.card δ
      (((A : Matrix (Fin (S.card + δ.val) ⊕ Fin (S.card + δ.val))
        (Fin (S.card + δ.val) ⊕ Fin (S.card + δ.val)) K) *ᵥ vS)) := by
    rw [planeQ_lift t δ S hMw0]
    congr 1
    funext x
    exact hMrow x
  have hQMv : planeQ (K := K) t δ (M *ᵥ v) =
      planeQ (K := K) t δ (M *ᵥ w) + planeQ (K := K) t δ vO := by
    rw [hMv]
    exact planeQ_add_of_support t δ S hMw0 hvO0
  calc planeQ (K := K) t δ (M *ᵥ v)
      = planeQ (K := K) t δ (M *ᵥ w) + planeQ (K := K) t δ vO := hQMv
    _ = planeQ (K := K) S.card δ (((A : Matrix (Fin (S.card + δ.val) ⊕ Fin (S.card + δ.val))
        (Fin (S.card + δ.val) ⊕ Fin (S.card + δ.val)) K) *ᵥ vS)) +
          planeQ (K := K) t δ vO := by rw [hQMw]
    _ = planeQ (K := K) S.card δ vS + planeQ (K := K) t δ vO := by rw [hA vS]
    _ = planeQ (K := K) t δ w + planeQ (K := K) t δ vO := by rw [hQw]
    _ = planeQ (K := K) t δ v := hQv.symm


omit [Finite K] [CharP K 2] in
theorem orthExt_map_orthGroup_le (t : ℕ) (δ : Fin 2) (S : Finset (Fin t)) :
    (LargeEvenOrthGroup (planeQ (K := K) S.card δ)).map (orthExt t δ S) ≤
      LargeEvenOrthGroup (planeQ (K := K) t δ) := by
  rintro _ ⟨A, hA, rfl⟩
  exact orthExt_mem_orthGroup t δ S hA

omit [Finite K] [CharP K 2] in
theorem orthExt_map_omegaQ_le (t : ℕ) (δ : Fin 2) (S : Finset (Fin t)) :
    (omegaQ (K := K) S.card δ).map (orthExt t δ S) ≤ omegaQ (K := K) t δ := by
  rw [show omegaQ (K := K) S.card δ =
      ⁅LargeEvenOrthGroup (planeQ (K := K) S.card δ),
        LargeEvenOrthGroup (planeQ (K := K) S.card δ)⁆ from rfl,
    show omegaQ (K := K) t δ =
      ⁅LargeEvenOrthGroup (planeQ (K := K) t δ),
        LargeEvenOrthGroup (planeQ (K := K) t δ)⁆ from rfl,
    Subgroup.map_commutator]
  exact Subgroup.commutator_mono (orthExt_map_orthGroup_le t δ S)
    (orthExt_map_orthGroup_le t δ S)

omit [Finite K] in
theorem orthExtLeBlockGroup (t : ℕ) (δ : Fin 2) (S : Finset (Fin t)) :
    (omegaQ (K := K) S.card δ).map (orthExt t δ S) ≤
      (oBlockGroup ζ t δ (.zero S)).map (omegaQ (K := K) t δ).subtype := by
  rintro _ ⟨A, hA, rfl⟩
  have hΩ : orthExt t δ S A ∈ omegaQ (K := K) t δ :=
    orthExt_map_omegaQ_le t δ S ⟨A, hA, rfl⟩
  refine ⟨⟨orthExt t δ S A, hΩ⟩, ?_, rfl⟩
  exact (mem_oBlockGroup_zero_iff ζ t δ S).2 (orthExt_mul_one_sub t δ S A)

@[expose] def blockRestrict (t : ℕ) (δ : Fin 2) (S : Finset (Fin t))
    (g : Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
      (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) :
    Matrix (Fin (S.card + δ.val) ⊕ Fin (S.card + δ.val))
      (Fin (S.card + δ.val) ⊕ Fin (S.card + δ.val)) K :=
  fun x y => g (embSum t δ S x) (embSum t δ S y)

omit [Finite K] in
theorem spEmbedMat_blockRestrict (t : ℕ) (δ : Fin 2) (S : Finset (Fin t))
    {g : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K}
    (hgΩ : g ∈ omegaQ (K := K) t δ)
    (hgB : (⟨g, hgΩ⟩ : ↥(omegaQ (K := K) t δ)) ∈ oBlockGroup ζ t δ (.zero S)) :
    spEmbedMat (emb t δ S) (blockRestrict t δ S (g : Matrix (Fin (t + δ.val) ⊕
      Fin (t + δ.val)) (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K)) =
      (g : Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
        (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) := by
  ext a b
  by_cases ha : a ∈ Set.range (embSum t δ S)
  · by_cases hb : b ∈ Set.range (embSum t δ S)
    · obtain ⟨x, rfl⟩ := ha
      obtain ⟨y, rfl⟩ := hb
      change spEmbedMat (emb t δ S) (blockRestrict t δ S (g : Matrix (Fin (t + δ.val) ⊕
        Fin (t + δ.val)) (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K))
        (Sum.map (emb t δ S) (emb t δ S) x) (Sum.map (emb t δ S) (emb t δ S) y) =
          (g : Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
            (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) (Sum.map (emb t δ S) (emb t δ S) x)
            (Sum.map (emb t δ S) (emb t δ S) y)
      rw [spEmbedMat_apply_image (emb_injective t δ S)]
      rfl
    · obtain ⟨x, rfl⟩ := ha
      rw [spEmbedMat_apply_of_not_mem _ (fun h => hb h.2),
        apply_of_not_mem_plane_right ζ t δ S hgB
          (fun h => hb ((mem_range_embSum_iff b).2 h))]
  · rw [spEmbedMat_apply_of_not_mem _ (fun h => ha h.1),
      apply_of_not_mem_plane_left ζ t δ S hgB
        (fun h => ha ((mem_range_embSum_iff a).2 h))]

omit [Finite K] in
theorem mulVec_liftVec_apply (t : ℕ) (δ : Fin 2) (S : Finset (Fin t))
    {g : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K}
    (hgΩ : g ∈ omegaQ (K := K) t δ)
    (hgB : (⟨g, hgΩ⟩ : ↥(omegaQ (K := K) t δ)) ∈ oBlockGroup ζ t δ (.zero S))
    (v : Fin (S.card + δ.val) ⊕ Fin (S.card + δ.val) → K)
    (x : Fin (S.card + δ.val) ⊕ Fin (S.card + δ.val)) :
    ((g : Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
        (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) *ᵥ liftVec t δ S v) (embSum t δ S x) =
      (blockRestrict t δ S (g : Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
        (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) *ᵥ v) x := by
  have hzero : ∀ q, q ∉ Set.range (embSum t δ S) →
      (g : Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
        (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) (embSum t δ S x) q = 0 := by
    intro q hq
    have hne : embSum t δ S x ≠ q := fun h => hq (h ▸ Set.mem_range_self x)
    rw [apply_of_not_mem_plane_right ζ t δ S hgB
      (fun h => hq ((mem_range_embSum_iff q).2 h)), Matrix.one_apply_ne hne]
  rw [mulVec_comp_embSum t δ S _ _ hzero, Matrix.mulVec_apply]
  change (∑ y : Fin (S.card + δ.val) ⊕ Fin (S.card + δ.val),
    (g : Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
      (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) (embSum t δ S x) (embSum t δ S y) *
      liftVec t δ S v (embSum t δ S y)) = _
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [liftVec_apply_embSum]
  rfl

omit [Finite K] in
theorem mulVec_liftVec_vanish (t : ℕ) (δ : Fin 2) (S : Finset (Fin t))
    {g : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K}
    (hgΩ : g ∈ omegaQ (K := K) t δ)
    (hgB : (⟨g, hgΩ⟩ : ↥(omegaQ (K := K) t δ)) ∈ oBlockGroup ζ t δ (.zero S))
    (v : Fin (S.card + δ.val) ⊕ Fin (S.card + δ.val) → K)
    {z : Fin (t + δ.val) ⊕ Fin (t + δ.val)}
    (hz : (WitSpNs.plane z : Fin (t + δ.val)) ∉ liftSupport t δ S) :
    ((g : Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
        (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) *ᵥ liftVec t δ S v) z = 0 := by
  have hz' : z ∉ Set.range (embSum t δ S) := fun h => hz ((mem_range_embSum_iff z).1 h)
  rw [Matrix.mulVec_apply]
  change (∑ q : Fin (t + δ.val) ⊕ Fin (t + δ.val),
    (g : Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
      (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) z q * liftVec t δ S v q) = 0
  refine Finset.sum_eq_zero fun q _ => ?_
  by_cases hq : q ∈ Set.range (embSum t δ S)
  · rw [apply_of_not_mem_plane_left ζ t δ S hgB hz,
      Matrix.one_apply_ne (by rintro rfl; exact hz' hq), zero_mul]
  · rw [liftVec_apply_of_not_mem t δ S v hq, mul_zero]

omit [Finite K] in
theorem orthBlockGroupLeExt (t : ℕ) (δ : Fin 2) (S : Finset (Fin t))
    {g : ↥(omegaQ (K := K) t δ)} (hg : g ∈ oBlockGroup ζ t δ (.zero S)) :
    (g : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) ∈
      (LargeEvenOrthGroup (planeQ (K := K) S.card δ)).map (orthExt t δ S) := by
  have hgΩ : (g : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) ∈ omegaQ (K := K) t δ := g.2
  have hgB : (⟨(g : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K), hgΩ⟩ :
      ↥(omegaQ (K := K) t δ)) ∈ oBlockGroup ζ t δ (.zero S) := hg
  let N : Matrix (Fin (S.card + δ.val) ⊕ Fin (S.card + δ.val))
      (Fin (S.card + δ.val) ⊕ Fin (S.card + δ.val)) K :=
    blockRestrict t δ S ((g : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) :
      Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
        (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K)
  let N' : Matrix (Fin (S.card + δ.val) ⊕ Fin (S.card + δ.val))
      (Fin (S.card + δ.val) ⊕ Fin (S.card + δ.val)) K :=
    blockRestrict t δ S ((((g⁻¹ : ↥(omegaQ (K := K) t δ)) :
      GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K)) :
      Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
        (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K)
  have hN : spEmbedMat (emb t δ S) N =
      ((g : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) :
        Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
          (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) :=
    spEmbedMat_blockRestrict ζ t δ S hgΩ hgB
  have hN' : spEmbedMat (emb t δ S) N' =
      (((g⁻¹ : ↥(omegaQ (K := K) t δ)) : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) :
        Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
          (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) :=
    spEmbedMat_blockRestrict ζ t δ S (Subgroup.inv_mem _ hgΩ) (Subgroup.inv_mem _ hgB)
  have hNmul : N * N' = 1 := by
    apply spEmbedMat_injective (emb_injective t δ S)
    rw [spEmbedMat_mul (emb_injective t δ S), hN, hN', spEmbedMat_one,
      ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Units.val_one]
  have hN'mul : N' * N = 1 := by
    apply spEmbedMat_injective (emb_injective t δ S)
    rw [spEmbedMat_mul (emb_injective t δ S), hN', hN, spEmbedMat_one,
      ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one]
  let A : GL (Fin (S.card + δ.val) ⊕ Fin (S.card + δ.val)) K :=
    ⟨N, N', hNmul, hN'mul⟩
  have hExtA : orthExt t δ S A = g := Units.ext hN
  have hAO : A ∈ LargeEvenOrthGroup (planeQ (K := K) S.card δ) := by
    rw [CFSG.PGLModel.mem_orthogonalGroup_iff]
    intro v
    have hle : ⁅LargeEvenOrthGroup (planeQ (K := K) t δ),
        LargeEvenOrthGroup (planeQ (K := K) t δ)⁆ ≤
        LargeEvenOrthGroup (planeQ (K := K) t δ) := by
      rw [Subgroup.commutator_le]
      intro g1 h1 g2 h2
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ h1 h2)
        (Subgroup.inv_mem _ h1)) (Subgroup.inv_mem _ h2)
    have hlt : (g : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) ∈
        LargeEvenOrthGroup (planeQ (K := K) t δ) := hle g.2
    have hgO : planeQ (K := K) t δ ((((g : ↥(omegaQ (K := K) t δ)) :
        GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) :
        Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
          (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) *ᵥ liftVec t δ S v) =
        planeQ (K := K) t δ (liftVec t δ S v) :=
      (CFSG.PGLModel.mem_orthogonalGroup_iff).1 hlt (liftVec t δ S v)
    have hw0 : ∀ z, (WitSpNs.plane z : Fin (t + δ.val)) ∉ liftSupport t δ S →
        liftVec t δ S v z = 0 := fun z hz => liftVec_apply_of_plane_not_mem t δ S v hz
    have hgw0 : ∀ z, (WitSpNs.plane z : Fin (t + δ.val)) ∉ liftSupport t δ S →
        ((((g : ↥(omegaQ (K := K) t δ)) : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) :
          Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
            (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) *ᵥ liftVec t δ S v) z = 0 :=
      fun z hz => mulVec_liftVec_vanish ζ t δ S hgΩ hgB v hz
    have hQw : planeQ (K := K) t δ (liftVec t δ S v) = planeQ (K := K) S.card δ v := by
      rw [planeQ_lift t δ S hw0]
      congr 1
      funext x
      exact liftVec_apply_embSum t δ S v x
    have hQgw : planeQ (K := K) t δ ((((g : ↥(omegaQ (K := K) t δ)) :
        GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) :
        Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
          (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) *ᵥ liftVec t δ S v) =
        planeQ (K := K) S.card δ ((N : Matrix (Fin (S.card + δ.val) ⊕ Fin (S.card + δ.val))
          (Fin (S.card + δ.val) ⊕ Fin (S.card + δ.val)) K) *ᵥ v) := by
      rw [planeQ_lift t δ S hgw0]
      congr 1
      funext x
      exact mulVec_liftVec_apply ζ t δ S hgΩ hgB v x
    calc planeQ (K := K) S.card δ ((A : Matrix (Fin (S.card + δ.val) ⊕ Fin (S.card + δ.val))
          (Fin (S.card + δ.val) ⊕ Fin (S.card + δ.val)) K) *ᵥ v)
        = planeQ (K := K) t δ ((((g : ↥(omegaQ (K := K) t δ)) :
            GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) :
            Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
              (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) *ᵥ liftVec t δ S v) := hQgw.symm
      _ = planeQ (K := K) t δ (liftVec t δ S v) := hgO
      _ = planeQ (K := K) S.card δ v := hQw
  exact ⟨A, hAO, hExtA⟩

omit [Finite K] in
theorem orthBlockGroup_map_le_ext (t : ℕ) (δ : Fin 2) (S : Finset (Fin t)) :
    (oBlockGroup ζ t δ (.zero S)).map (omegaQ (K := K) t δ).subtype ≤
      (LargeEvenOrthGroup (planeQ (K := K) S.card δ)).map (orthExt t δ S) := by
  rintro _ ⟨g, hg, rfl⟩
  exact orthBlockGroupLeExt ζ t δ S hg

theorem oYcode_map_eq_orthExt (hK : Nat.card K = 2) (t : ℕ) (δ : Fin 2)
    (S : Finset (Fin t))
    (hS : PlaneRaw.admissible (.orthogonal δ) (.zero S : PlaneRaw.Code t)) :
    (oYcode ζ t δ (.zero S)).map (omegaQ (K := K) t δ).subtype =
      (omegaQ (K := K) S.card δ).map (orthExt t δ S) := by
  have hperf : ⁅omegaQ (K := K) S.card δ, omegaQ (K := K) S.card δ⁆ =
      omegaQ (K := K) S.card δ :=
    Subgroup.isPerfect_iff.1 (isQuasisimple_omegaQ hK S.card δ hS).1
  apply le_antisymm
  · calc (oYcode ζ t δ (.zero S)).map (omegaQ (K := K) t δ).subtype
        = ⁅(oBlockGroup ζ t δ (.zero S)).map (omegaQ (K := K) t δ).subtype,
            (oBlockGroup ζ t δ (.zero S)).map (omegaQ (K := K) t δ).subtype⁆ := by
          rw [oYcode, Subgroup.map_commutator]
      _ ≤ ⁅(LargeEvenOrthGroup (planeQ (K := K) S.card δ)).map (orthExt t δ S),
            (LargeEvenOrthGroup (planeQ (K := K) S.card δ)).map (orthExt t δ S)⁆ :=
          Subgroup.commutator_mono (orthBlockGroup_map_le_ext ζ t δ S)
            (orthBlockGroup_map_le_ext ζ t δ S)
      _ = (omegaQ (K := K) S.card δ).map (orthExt t δ S) := by
          rw [← Subgroup.map_commutator]
          rfl
  · calc (omegaQ (K := K) S.card δ).map (orthExt t δ S)
        = (⁅omegaQ (K := K) S.card δ, omegaQ (K := K) S.card δ⁆).map (orthExt t δ S) :=
          congrArg (fun H => H.map (orthExt t δ S)) hperf.symm
      _ = ⁅(omegaQ (K := K) S.card δ).map (orthExt t δ S),
            (omegaQ (K := K) S.card δ).map (orthExt t δ S)⁆ :=
          Subgroup.map_commutator ..
      _ ≤ ⁅(oBlockGroup ζ t δ (.zero S)).map (omegaQ (K := K) t δ).subtype,
            (oBlockGroup ζ t δ (.zero S)).map (omegaQ (K := K) t δ).subtype⁆ :=
          Subgroup.commutator_mono (orthExtLeBlockGroup ζ t δ S)
            (orthExtLeBlockGroup ζ t δ S)
      _ = (oYcode ζ t δ (.zero S)).map (omegaQ (K := K) t δ).subtype := by
          rw [oYcode, Subgroup.map_commutator]

noncomputable def oYcodeMulEquivOmegaQ (hK : Nat.card K = 2) (t : ℕ) (δ : Fin 2)
    (S : Finset (Fin t))
    (hS : PlaneRaw.admissible (.orthogonal δ) (.zero S : PlaneRaw.Code t)) :
    ↥(oYcode ζ t δ (.zero S)) ≃* ↥(omegaQ (K := K) S.card δ) :=
  ((Subgroup.equivMapOfInjective (oYcode ζ t δ (.zero S)) (omegaQ (K := K) t δ).subtype
      (omegaQ (K := K) t δ).subtype_injective).trans
    (MulEquiv.subgroupCongr (oYcode_map_eq_orthExt ζ hK t δ S hS))).trans
    (Subgroup.equivMapOfInjective (omegaQ (K := K) S.card δ) (orthExt t δ S)
      (orthExt_injective t δ S)).symm

end CharTwo

end

end CFSG.StandardType.GGQ2Frame.OrthBlocks
