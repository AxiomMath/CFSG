module

public import CFSG.Timmesfeld.Transvection.ModelSULowSpan
public import CFSG.LieType.Universal.Unitary.Hermitian
import CFSG.Timmesfeld.Transvection.OddModelBC2

public section

namespace CFSG.Timmesfeld.Transvection

open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.Universal.Unitary.SUExtras CFSG.Timmesfeld.ARS CFSG.Timmesfeld.LieEmbed
  CFSG.LinearAlgebra

namespace ModelRank

variable {F : Type} [Field F] {σ : F ≃+* F} {m : ℕ}

variable (σ m) in
@[expose] def lowBlock (g : SU σ m) : Matrix (Fin (m / 2)) (Fin (m / 2)) F :=
  Matrix.of fun a b => suMat σ m g (lowIdx a) (Fin.rev (lowIdx b))

variable (σ m) in
@[expose] def lowPart (g : SU σ m) : Matrix (Fin (m / 2)) (Fin (m / 2)) F :=
  Matrix.of fun a b => suMat σ m g (lowIdx a) (lowIdx b)

private theorem mat_eq_suMat (g : SU σ m) : mat σ m g = suMat σ m g := rfl

private theorem lowIdx_injective : Function.Injective (lowIdx (n := m)) :=
  fun _ _ h => Fin.ext (by simpa [val_lowIdx] using congrArg Fin.val h)

private theorem mulVec_single_one_apply (M : Matrix (Fin m) (Fin m) F) (j i : Fin m) :
    (M *ᵥ Pi.single i 1) j = M j i := by
  rw [Matrix.mulVec_single_one]
  rfl

private theorem suMat_apply_eq_one_of_mem_lowRad {w : SU σ m} (hw : w ∈ lowRad σ m)
    {j i : Fin m} (h : ¬(j.val < m / 2 ∧ m / 2 ≤ i.val)) :
    suMat σ m w j i = (1 : Matrix (Fin m) (Fin m) F) j i := by
  have hmem := (mem_lowRad.mp hw).1
  have hfix := (mem_lowRad.mp hw).2
  by_cases hj : m / 2 ≤ j.val
  · have h1 := hmem (Pi.single i 1)
    rw [mem_lowSpan] at h1
    have h2 := h1 j hj
    rw [Pi.sub_apply, mulVec_single_one_apply, sub_eq_zero] at h2
    rw [h2, Pi.single_apply, Matrix.one_apply]
  · push Not at hj
    have hi : i.val < m / 2 := by
      by_contra hlt
      push Not at hlt
      exact h ⟨hj, hlt⟩
    have hsingle : Pi.single i 1 ∈ lowSpan F m := by
      have hi' : i = lowIdx ⟨i.val, hi⟩ := Fin.ext rfl
      rw [hi']
      exact single_lowIdx_mem_lowSpan ⟨i.val, hi⟩
    have h1 := congrFun (hfix (Pi.single i 1) hsingle) j
    rw [mulVec_single_one_apply] at h1
    rw [h1, Pi.single_apply, Matrix.one_apply]

private theorem suMat_apply_eq_zero_of_rev_eq_of_mem_lowRad {w : SU σ m} (hw : w ∈ lowRad σ m)
    {a : Fin (m / 2)} {i : Fin m} (hi : Fin.rev i = i) :
    suMat σ m w (lowIdx a) i = 0 := by
  have hival : i.val = m - 1 - i.val := by
    have h := congrArg Fin.val hi
    simp only [Fin.val_rev] at h
    omega
  have hia : i ≠ lowIdx a := by
    intro h
    rw [h] at hival
    simp only [val_lowIdx] at hival
    have := a.isLt
    omega
  have hne_i : i ≠ Fin.rev (lowIdx a) := by
    intro h
    rw [h] at hival
    simp only [Fin.val_rev, val_lowIdx] at hival
    have := a.isLt
    omega
  have hsum := sum_mat_mul_mat (σ := σ) w i (Fin.rev (lowIdx a))
  rw [mat_eq_suMat] at hsum
  rw [hi, if_neg (fun h => hne_i h.symm)] at hsum
  rw [Finset.sum_eq_single (lowIdx a)] at hsum
  · rw [suMat_apply_eq_one_of_mem_lowRad hw (j := Fin.rev (lowIdx a))
      (i := Fin.rev (lowIdx a)) (by simp only [Fin.val_rev, val_lowIdx]; omega),
      one_apply_eq, mul_one] at hsum
    exact (map_eq_zero σ).mp hsum
  · intro t _ ht
    by_cases htl : t.val < m / 2
    · have hne : Fin.rev t ≠ Fin.rev (lowIdx a) := fun h => ht (Fin.rev_injective h)
      rw [suMat_apply_eq_one_of_mem_lowRad hw (j := Fin.rev t) (i := Fin.rev (lowIdx a))
        (by simp only [Fin.val_rev]; omega), one_apply_ne hne, mul_zero]
    · push Not at htl
      by_cases hti : t = i
      · subst t
        rw [suMat_apply_eq_one_of_mem_lowRad hw (j := i) (i := i) (by omega),
          one_apply_eq, map_one, one_mul, hi,
          suMat_apply_eq_one_of_mem_lowRad hw (j := i) (i := Fin.rev (lowIdx a))
          (by simp only [Fin.val_rev, val_lowIdx]; omega), one_apply_ne hne_i]
      · rw [suMat_apply_eq_one_of_mem_lowRad hw (j := t) (i := i) (by omega),
          one_apply_ne hti, map_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem sub_one_eq_zero_of_mem_lowRad {w : SU σ m} (hw : w ∈ lowRad σ m) {j i : Fin m}
    (h : ¬(j.val < m / 2 ∧ m / 2 ≤ i.val)) : (suMat σ m w - 1) j i = 0 := by
  rw [Matrix.sub_apply, suMat_apply_eq_one_of_mem_lowRad hw h, sub_self]

private theorem sub_one_apply_eq_zero_of_rev_eq_of_mem_lowRad {w : SU σ m} (hw : w ∈ lowRad σ m)
    {a : Fin (m / 2)} {i : Fin m} (hi : Fin.rev i = i) : (suMat σ m w - 1) (lowIdx a) i = 0 := by
  have hne : lowIdx a ≠ i := by
    intro h
    rw [← h] at hi
    exact lowIdx_ne_rev a a hi.symm
  rw [Matrix.sub_apply, suMat_apply_eq_zero_of_rev_eq_of_mem_lowRad hw hi, Matrix.one_apply,
    if_neg hne, sub_zero]

private theorem sub_one_apply_lowIdx_rev_lowIdx (w : SU σ m) (a b : Fin (m / 2)) :
    (suMat σ m w - 1) (lowIdx a) (Fin.rev (lowIdx b)) = lowBlock σ m w a b := by
  rw [Matrix.sub_apply, Matrix.one_apply, if_neg (lowIdx_ne_rev a b), sub_zero, lowBlock,
    Matrix.of_apply]

private theorem sum_eq_sum_lowIdx {M : Type*} [AddCommMonoid M] {f : Fin m → M}
    (h : ∀ i, m / 2 ≤ i.val → f i = 0) :
    ∑ i, f i = ∑ a : Fin (m / 2), f (lowIdx a) := by
  rw [← Finset.sum_subset (Finset.subset_univ _) ?_]
  · rw [Finset.sum_image]
    intro x _ y _ hxy
    exact lowIdx_injective hxy
  · intro x _ hx
    apply h x
    by_contra hlt
    push Not at hlt
    exact hx (Finset.mem_image.mpr
      ⟨⟨x.val, hlt⟩, Finset.mem_univ _, Fin.ext (by simp [val_lowIdx])⟩)

private theorem sum_eq_sum_rev_lowIdx {M : Type*} [AddCommMonoid M] {f : Fin m → M}
    (hlow : ∀ i, i.val < m / 2 → f i = 0) (hmid : ∀ i, Fin.rev i = i → f i = 0) :
    ∑ i, f i = ∑ a : Fin (m / 2), f (Fin.rev (lowIdx a)) := by
  rw [← Finset.sum_subset (Finset.subset_univ _) ?_]
  · rw [Finset.sum_image]
    intro x _ y _ hxy
    exact Fin.ext (by
      have h := congrArg Fin.val hxy
      simp only [Fin.val_rev, val_lowIdx] at h ⊢
      omega)
  · intro x _ hx
    by_cases hxl : x.val < m / 2
    · exact hlow x hxl
    · push Not at hxl
      by_cases hxm : Fin.rev x = x
      · exact hmid x hxm
      · obtain ⟨b, hb | hb⟩ := exists_lowIdx (fun h => hxm h.symm)
        · rw [hb] at hxl
          simp only [val_lowIdx] at hxl
          omega
        · exact absurd (Finset.mem_image.mpr ⟨b, Finset.mem_univ _, hb.symm⟩) hx

theorem lowBlock_mul {g h : SU σ m} (hg : g ∈ lowRad σ m) (hh : h ∈ lowRad σ m) :
    lowBlock σ m (g * h) = lowBlock σ m g + lowBlock σ m h := by
  ext a b
  have hsum := Finset.sum_eq_add (s := Finset.univ)
    (f := fun i => suMat σ m g (lowIdx a) i * suMat σ m h i (Fin.rev (lowIdx b)))
    (lowIdx a) (Fin.rev (lowIdx b)) (lowIdx_ne_rev a b)
    (fun c _ hc => by
      obtain ⟨hc1, hc2⟩ := hc
      by_cases hcl : c.val < m / 2
      · rw [suMat_apply_eq_one_of_mem_lowRad hg (by simp only [val_lowIdx]; omega),
          one_apply_ne hc1.symm, zero_mul]
      · push Not at hcl
        rw [suMat_apply_eq_one_of_mem_lowRad hh
          (by simp only [Fin.val_rev, val_lowIdx]; omega), one_apply_ne hc2, mul_zero])
    (fun h => absurd (Finset.mem_univ _) h)
    (fun h => absurd (Finset.mem_univ _) h)
  simp only [lowBlock, Matrix.of_apply, Matrix.add_apply, map_mul, Matrix.mul_apply]
  rw [hsum, suMat_apply_eq_one_of_mem_lowRad hg (j := lowIdx a) (i := lowIdx a)
      (by simp only [val_lowIdx]; omega),
    suMat_apply_eq_one_of_mem_lowRad hh (j := Fin.rev (lowIdx b)) (i := Fin.rev (lowIdx b))
      (by simp only [Fin.val_rev, val_lowIdx]; omega), one_apply_eq, one_apply_eq, one_mul,
    mul_one, add_comm]

theorem lowBlock_one : lowBlock σ m (1 : SU σ m) = 0 := by
  ext a b
  simp only [lowBlock, Matrix.of_apply, map_one, Matrix.one_apply_ne (lowIdx_ne_rev a b),
    Matrix.zero_apply]

theorem lowBlock_inv {g : SU σ m} (hg : g ∈ lowRad σ m) : lowBlock σ m g⁻¹ = -lowBlock σ m g := by
  have h1 : lowBlock σ m (g * g⁻¹) = lowBlock σ m g + lowBlock σ m g⁻¹ :=
    lowBlock_mul hg (inv_mem hg)
  rw [mul_inv_cancel, lowBlock_one] at h1
  exact eq_neg_of_add_eq_zero_right h1.symm

private theorem eq_one_of_mem_lowRad_of_lowBlock_eq_zero {w : SU σ m} (hw : w ∈ lowRad σ m)
    (hB : lowBlock σ m w = 0) : w = 1 := by
  apply suMat_injective σ
  rw [map_one]
  ext j i
  by_cases hblk : j.val < m / 2 ∧ m / 2 ≤ i.val
  · obtain ⟨hj, hi⟩ := hblk
    have hj' : j = lowIdx ⟨j.val, hj⟩ := Fin.ext (by simp [val_lowIdx])
    rw [hj']
    by_cases hrev : Fin.rev i = i
    · have h1 : (suMat σ m w - 1) (lowIdx ⟨j.val, hj⟩) i = 0 :=
        sub_one_apply_eq_zero_of_rev_eq_of_mem_lowRad hw hrev
      rw [Matrix.sub_apply, sub_eq_zero] at h1
      rw [h1, Matrix.one_apply, if_neg (fun h => lowIdx_ne_rev ⟨j.val, hj⟩ ⟨j.val, hj⟩
        (by rw [h, hrev]))]
    · obtain ⟨b, hb | hb⟩ := exists_lowIdx (fun h => hrev h.symm)
      · rw [hb] at hi
        simp only [val_lowIdx] at hi
        omega
      · have h1 : (suMat σ m w - 1) (lowIdx ⟨j.val, hj⟩) (Fin.rev (lowIdx b)) = 0 := by
          rw [sub_one_apply_lowIdx_rev_lowIdx, hB, Matrix.zero_apply]
        rw [Matrix.sub_apply, sub_eq_zero] at h1
        rw [hb, h1]
  · rw [suMat_apply_eq_one_of_mem_lowRad hw hblk]

theorem eq_of_lowBlock_eq {g h : SU σ m} (hg : g ∈ lowRad σ m) (hh : h ∈ lowRad σ m)
    (heq : lowBlock σ m g = lowBlock σ m h) : g = h := by
  have hw : g * h⁻¹ ∈ lowRad σ m := (lowRad σ m).mul_mem hg (inv_mem hh)
  have hB : lowBlock σ m (g * h⁻¹) = 0 := by
    rw [lowBlock_mul hg (inv_mem hh), lowBlock_inv hh, heq, add_neg_cancel]
  rw [← mul_inv_eq_one]
  exact eq_one_of_mem_lowRad_of_lowBlock_eq_zero hw hB

theorem lowBlock_add_conjTr {g : SU σ m} (hg : g ∈ lowRad σ m) :
    lowBlock σ m g + conjTr σ (lowBlock σ m g) = 0 := by
  ext a b
  have hsum := sum_mat_mul_mat (σ := σ) g (Fin.rev (lowIdx a)) (Fin.rev (lowIdx b))
  rw [mat_eq_suMat] at hsum
  rw [Fin.rev_rev, if_neg (fun h => lowIdx_ne_rev a b h.symm)] at hsum
  have h2 := Finset.sum_eq_add (s := Finset.univ)
    (f := fun t => σ (suMat σ m g t (Fin.rev (lowIdx a)))
      * suMat σ m g (Fin.rev t) (Fin.rev (lowIdx b)))
    (Fin.rev (lowIdx a)) (lowIdx b) (fun h => lowIdx_ne_rev b a h.symm)
    (fun c _ hc => by
      obtain ⟨hc1, hc2⟩ := hc
      by_cases hcl : c.val < m / 2
      · have hne : Fin.rev c ≠ Fin.rev (lowIdx b) := fun h => hc2 (Fin.rev_injective h)
        rw [suMat_apply_eq_one_of_mem_lowRad hg (j := Fin.rev c) (i := Fin.rev (lowIdx b))
          (by simp only [Fin.val_rev]; omega), one_apply_ne hne, mul_zero]
      · push Not at hcl
        rw [suMat_apply_eq_one_of_mem_lowRad hg (j := c) (i := Fin.rev (lowIdx a))
          (by simp only [Fin.val_rev]; omega), one_apply_ne hc1, map_zero, zero_mul])
    (fun h => absurd (Finset.mem_univ _) h)
    (fun h => absurd (Finset.mem_univ _) h)
  rw [h2] at hsum
  rw [suMat_apply_eq_one_of_mem_lowRad hg (j := Fin.rev (lowIdx a)) (i := Fin.rev (lowIdx a))
    (by simp only [Fin.val_rev, val_lowIdx]; omega), one_apply_eq, map_one, one_mul,
    Fin.rev_rev,
    suMat_apply_eq_one_of_mem_lowRad hg (j := Fin.rev (lowIdx b)) (i := Fin.rev (lowIdx b))
    (by simp only [Fin.val_rev, val_lowIdx]; omega), one_apply_eq, mul_one] at hsum
  simp only [lowBlock, Matrix.of_apply, Matrix.add_apply, conjTr_apply, Matrix.zero_apply]
  exact hsum

theorem lowBlock_of_suMat_eq_uTrans {v : Fin m → F} {c : F} {t : SU σ m}
    (ht : suMat σ m t = uTrans σ v c) :
    lowBlock σ m t = c • vecMulVec (fun a => v (lowIdx a)) (fun a => σ (v (lowIdx a))) := by
  ext a b
  simp only [lowBlock, Matrix.of_apply, ht, uTrans, Matrix.add_apply, Matrix.one_apply_ne
    (lowIdx_ne_rev a b), zero_add, Matrix.smul_apply, uNil, vecMulVec_apply, uRow_apply,
    Fin.rev_rev]

private theorem suMat_conj_apply_lowRad (g : SU σ m) {w : SU σ m} (hw : w ∈ lowRad σ m)
    (a b : Fin (m / 2)) :
    suMat σ m (g * w * g⁻¹) (lowIdx a) (Fin.rev (lowIdx b))
      = ∑ f, ∑ e, suMat σ m g (lowIdx a) (lowIdx e) * lowBlock σ m w e f
          * σ (suMat σ m g (lowIdx b) (lowIdx f)) := by
  have hinv : ∀ e f : Fin (m / 2),
      suMat σ m g⁻¹ (Fin.rev (lowIdx e)) (Fin.rev (lowIdx f))
        = σ (suMat σ m g (lowIdx f) (lowIdx e)) := by
    intro e f
    have h := Pres.mat_inv_apply (σ := σ) g (Fin.rev (lowIdx e)) (Fin.rev (lowIdx f))
    rw [mat_eq_suMat, mat_eq_suMat] at h
    simpa using h
  have hexp : suMat σ m (g * w * g⁻¹) (lowIdx a) (Fin.rev (lowIdx b))
      = ∑ j, (∑ i, suMat σ m g (lowIdx a) i * (suMat σ m w - 1) i j)
          * suMat σ m g⁻¹ j (Fin.rev (lowIdx b)) := by
    have hgg : (suMat σ m g * suMat σ m g⁻¹) (lowIdx a) (Fin.rev (lowIdx b)) = 0 := by
      rw [← map_mul, mul_inv_cancel, map_one, Matrix.one_apply_ne (lowIdx_ne_rev a b)]
    have h1 : suMat σ m w = 1 + (suMat σ m w - 1) := by abel
    conv_lhs => rw [map_mul, map_mul, h1, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one]
    rw [Matrix.add_apply, hgg, zero_add, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun j _ => by rw [Matrix.mul_apply]
  have hin : ∀ e : Fin (m / 2), (∑ i, suMat σ m g (lowIdx a) i
      * (suMat σ m w - 1) i (Fin.rev (lowIdx e)))
      = ∑ f, suMat σ m g (lowIdx a) (lowIdx f) * lowBlock σ m w f e := by
    intro e
    rw [sum_eq_sum_lowIdx (f := fun i => suMat σ m g (lowIdx a) i
      * (suMat σ m w - 1) i (Fin.rev (lowIdx e))) ?_]
    · exact Finset.sum_congr rfl fun f _ => by rw [sub_one_apply_lowIdx_rev_lowIdx]
    · intro i hi
      rw [sub_one_eq_zero_of_mem_lowRad hw (j := i) (i := Fin.rev (lowIdx e))
        (by simp only [Fin.val_rev, val_lowIdx]; omega), mul_zero]
  rw [hexp, sum_eq_sum_rev_lowIdx (f := fun j => (∑ i, suMat σ m g (lowIdx a) i
    * (suMat σ m w - 1) i j) * suMat σ m g⁻¹ j (Fin.rev (lowIdx b))) ?_ ?_]
  · have hstep : ∀ e : Fin (m / 2), ((∑ i, suMat σ m g (lowIdx a) i
        * (suMat σ m w - 1) i (Fin.rev (lowIdx e)))
          * suMat σ m g⁻¹ (Fin.rev (lowIdx e)) (Fin.rev (lowIdx b)))
        = ∑ f, suMat σ m g (lowIdx a) (lowIdx f) * lowBlock σ m w f e
            * σ (suMat σ m g (lowIdx b) (lowIdx e)) := by
      intro e
      rw [hin e, Finset.sum_mul]
      exact Finset.sum_congr rfl fun f _ => by rw [hinv e b]
    rw [Finset.sum_congr rfl fun e _ => hstep e]
  · intro j hj
    have hzero : (∑ i, suMat σ m g (lowIdx a) i * (suMat σ m w - 1) i j) = 0 :=
      Finset.sum_eq_zero fun i _ => by
        rw [sub_one_eq_zero_of_mem_lowRad hw (j := i) (i := j) (by omega), mul_zero]
    rw [hzero, zero_mul]
  · intro j hj
    have hzero : (∑ i, suMat σ m g (lowIdx a) i * (suMat σ m w - 1) i j) = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      by_cases hil : i.val < m / 2
      · have hi' : i = lowIdx ⟨i.val, hil⟩ := Fin.ext rfl
        rw [hi', sub_one_apply_eq_zero_of_rev_eq_of_mem_lowRad hw hj, mul_zero]
      · push Not at hil
        rw [sub_one_eq_zero_of_mem_lowRad hw (j := i) (i := j) (by omega), mul_zero]
    rw [hzero, zero_mul]

theorem lowBlock_conj (g : SU σ m) {w : SU σ m} (hw : w ∈ lowRad σ m) :
    lowBlock σ m (g * w * g⁻¹) = lowPart σ m g * lowBlock σ m w * conjTr σ (lowPart σ m g) := by
  ext a b
  have hright : (lowPart σ m g * lowBlock σ m w * conjTr σ (lowPart σ m g)) a b
      = ∑ f, ∑ e, suMat σ m g (lowIdx a) (lowIdx e) * lowBlock σ m w e f
          * σ (suMat σ m g (lowIdx b) (lowIdx f)) := by
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [lowPart, Matrix.of_apply, conjTr_apply]
  exact (suMat_conj_apply_lowRad g hw a b).trans hright.symm

theorem lowPart_mul (g : SU σ m) {h : SU σ m}
    (hh : ∀ x ∈ lowSpan F m, suMat σ m h *ᵥ x ∈ lowSpan F m) :
    lowPart σ m (g * h) = lowPart σ m g * lowPart σ m h := by
  ext a b
  have hzero : ∀ i, m / 2 ≤ i.val → suMat σ m h i (lowIdx b) = 0 := by
    intro i hi
    have h1 := hh (Pi.single (lowIdx b) 1) (single_lowIdx_mem_lowSpan b)
    rw [mem_lowSpan] at h1
    have h2 := h1 i hi
    rwa [mulVec_single_one_apply] at h2
  have hsum : ∑ i, suMat σ m g (lowIdx a) i * suMat σ m h i (lowIdx b)
      = ∑ e, suMat σ m g (lowIdx a) (lowIdx e) * suMat σ m h (lowIdx e) (lowIdx b) :=
    sum_eq_sum_lowIdx fun i hi => by rw [hzero i hi, mul_zero]
  simp only [lowPart, Matrix.of_apply, map_mul, Matrix.mul_apply]
  rw [hsum]

theorem lowPart_one : lowPart σ m (1 : SU σ m) = 1 := by
  ext a b
  by_cases h : a = b
  · subst h
    simp only [lowPart, Matrix.of_apply, map_one, Matrix.one_apply_eq]
  · have h' : lowIdx a ≠ lowIdx b := fun hh => h (lowIdx_injective hh)
    simp only [lowPart, Matrix.of_apply, map_one, Matrix.one_apply_ne h', Matrix.one_apply_ne h]

theorem conj_eq_conj_of_lowPart_eq {g h : SU σ m}
    (hg : g ∈ Subgroup.normalizer (lowRad σ m : Set (SU σ m)))
    (hh : h ∈ Subgroup.normalizer (lowRad σ m : Set (SU σ m)))
    (heq : lowPart σ m g = lowPart σ m h) {w : SU σ m} (hw : w ∈ lowRad σ m) :
    g * w * g⁻¹ = h * w * h⁻¹ := by
  refine eq_of_lowBlock_eq ((Subgroup.mem_normalizer_iff.mp hg w).1 hw)
    ((Subgroup.mem_normalizer_iff.mp hh w).1 hw) ?_
  rw [lowBlock_conj g hw, lowBlock_conj h hw, heq]

end ModelRank

end CFSG.Timmesfeld.Transvection
