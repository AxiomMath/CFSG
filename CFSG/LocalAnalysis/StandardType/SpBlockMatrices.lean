module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import CFSG.LocalAnalysis.StandardType.AlternatingEightCoverSmallModules

public section

namespace CFSG.StandardType

namespace SpBlocks

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] def Splits {R : Type*} [Zero R] (I : Finset ι) (M : Matrix ι ι R) : Prop :=
  ∀ a b : ι, (a ∈ I ↔ b ∉ I) → M a b = 0

@[expose] def blk {R : Type*} (I : Finset ι) (M : Matrix ι ι R) : Matrix I I R :=
  M.submatrix (fun a : I => (a : ι)) (fun a : I => (a : ι))

section Algebra

variable {R : Type*} [CommRing R] {I : Finset ι}

lemma Splits.mem_iff_of_ne_zero {M : Matrix ι ι R} (hM : Splits I M) {a c : ι} (h : M a c ≠ 0) :
    a ∈ I ↔ c ∈ I := by
  constructor
  · intro ha
    by_contra hc
    exact h (hM a c ⟨fun _ => hc, fun _ => ha⟩)
  · intro hc
    by_contra ha
    exact h (hM a c ⟨fun h => absurd h ha, fun h => absurd hc h⟩)

lemma mulVec_apply_eq_blk_of_splits (M : Matrix ι ι R) (y : ι → R) (hM : Splits I M) {a : ι}
    (ha : a ∈ I) : (M *ᵥ y) a = (blk I M *ᵥ (fun b : I => y b)) ⟨a, ha⟩ := by
  rw [Matrix.mulVec_apply_eq_sum, Matrix.mulVec_apply_eq_sum]
  simp only [blk, Matrix.submatrix_apply]
  rw [← Finset.sum_subset (Finset.subset_univ I) (fun x _ hx => by
    rw [hM a x ⟨fun _ => hx, fun _ => ha⟩, zero_mul])]
  rw [Finset.sum_subtype I (fun _ => Iff.rfl) (fun b => M a b * y b)]

theorem Splits.mul {M N : Matrix ι ι R} (hM : Splits I M) (hN : Splits I N) : Splits I (M * N) := by
  intro a b hab
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro c _
  by_cases hMc : M a c = 0
  · rw [hMc, zero_mul]
  by_cases hNc : N c b = 0
  · rw [hNc, mul_zero]
  have h1 : a ∈ I ↔ c ∈ I := hM.mem_iff_of_ne_zero hMc
  have h2 : c ∈ I ↔ b ∈ I := hN.mem_iff_of_ne_zero hNc
  have h3 : a ∈ I ↔ b ∈ I := h1.trans h2
  rw [h3] at hab
  exfalso
  by_cases hb : b ∈ I
  · exact (hab.mp hb) hb
  · exact hb (hab.mpr hb)

theorem Splits.transpose {M : Matrix ι ι R} (hM : Splits I M) : Splits I Mᵀ := by
  intro a b hab
  rw [Matrix.transpose_apply]
  exact hM b a ⟨fun hb ha => (hab.mp ha) hb, fun ha => by_contra fun hb => ha (hab.mpr hb)⟩

theorem blk_one : blk I (1 : Matrix ι ι R) = 1 := by
  ext a b
  simp only [blk, Matrix.submatrix_apply, Matrix.one_apply]
  by_cases h : a = b
  · rw [if_pos h, if_pos (congrArg Subtype.val h)]
  · rw [if_neg h, if_neg (fun hh => h (Subtype.ext hh))]

theorem Splits.blk_mul {M : Matrix ι ι R} (hM : Splits I M) (N : Matrix ι ι R) :
    blk I (M * N) = blk I M * blk I N := by
  ext a b
  simp only [blk, Matrix.submatrix_apply, Matrix.mul_apply]
  rw [Finset.sum_coe_sort I (fun c : ι => M (a : ι) c * N c (b : ι))]
  rw [Finset.sum_subset (Finset.subset_univ I) (fun x _ hx => by
    rw [hM (a : ι) x ⟨fun _ => hx, fun _ => a.2⟩, zero_mul])]

theorem blk_transpose (M : Matrix ι ι R) : blk I Mᵀ = (blk I M)ᵀ := by
  ext a b
  simp only [blk, Matrix.submatrix_apply, Matrix.transpose_apply]

theorem blk_map {S : Type*} [CommRing S] (M : Matrix ι ι R) (f : R →+* S) :
    blk I (M.map f) = (blk I M).map f := by
  ext a b
  simp only [blk, Matrix.submatrix_apply, Matrix.map_apply]

end Algebra

section Field

variable {K : Type*} [Field K] {I : Finset ι}

theorem Splits.isUnit_blk {M : Matrix ι ι K} (hM : Splits I M) (hu : IsUnit M) :
    IsUnit (blk I M) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro hdet
  rw [← Matrix.exists_mulVec_eq_zero_iff] at hdet
  obtain ⟨y, hy, hy0⟩ := hdet
  let yhat : ι → K := fun b => if h : b ∈ I then y ⟨b, h⟩ else 0
  have hMvec : M *ᵥ yhat = 0 := by
    funext a
    by_cases ha : a ∈ I
    · rw [mulVec_apply_eq_blk_of_splits M yhat hM ha]
      have hfun : (fun b : I => yhat (b : ι)) = y := by
        funext b
        simp only [yhat, dif_pos b.2]
      rw [hfun]
      exact congr_fun hy0 ⟨a, ha⟩
    · rw [Matrix.mulVec_apply_eq_sum]
      apply Finset.sum_eq_zero
      intro c _
      by_cases hc : c ∈ I
      · rw [hM a c ⟨fun h => absurd h ha, fun h => absurd hc h⟩, zero_mul]
      · simp only [yhat, dif_neg hc, mul_zero]
  have hinj : Function.Injective M.mulVec := Matrix.mulVec_injective_iff_isUnit.2 hu
  have hzero : yhat = 0 := hinj (by rw [hMvec, Matrix.mulVec_zero])
  apply hy
  funext i
  have := congr_fun hzero (i : ι)
  simpa [yhat, dif_pos i.2] using this

end Field

section Representations

variable {J : Type*} [Group J] [Finite J] {Ω : Type*} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]

@[expose] noncomputable def blkHom (I : Finset ι) (Q : J →* Matrix ι ι Ω)
    (hQ : ∀ g, Splits I (Q g)) : J →* Matrix I I Ω where
  toFun g := blk I (Q g)
  map_one' := by
    rw [map_one]
    exact blk_one
  map_mul' g h := by
    rw [map_mul]
    exact (hQ g).blk_mul (Q h)

theorem blkHom_apply (I : Finset ι) (Q : J →* Matrix ι ι Ω) (hQ : ∀ g, Splits I (Q g)) (g : J) :
    blkHom I Q hQ g = blk I (Q g) :=
  rfl

theorem IsAlternatingEightCover.blk_eq_one_of_card_le_three (hJ : IsAlternatingEightCover J)
    (I : Finset ι) (Q : J →* Matrix ι ι Ω) (hQ : ∀ g, Splits I (Q g)) (hI : I.card ≤ 3) (g : J) :
    blk I (Q g) = 1 := by
  have hcard : Fintype.card ↥I ≤ 3 := by
    rw [Fintype.card_coe]
    exact hI
  have h := IsAlternatingEightCover.map_eq_one_of_card_le_three hJ hcard (blkHom I Q hQ) g
  rw [blkHom_apply] at h
  exact h

theorem IsAlternatingEightCover.blk_eq_one_of_card_le_five (hJ : IsAlternatingEightCover J)
    (I : Finset ι) (Q : J →* Matrix ι ι Ω) (hQ : ∀ g, Splits I (Q g)) (σ : Ω ≃+* Ω)
    (hσ : ∀ η : Ω, η ^ 7 = 1 → ∃ k : ℕ, σ η = η ^ 2 ^ k) {H : Matrix ι ι Ω} (hH : Splits I H)
    (hHu : IsUnit H) (hform : ∀ g, (Q g)ᵀ * H * (Q g).map σ = H) (hI : I.card ≤ 5) (g : J) :
    blk I (Q g) = 1 := by
  have hcard : Fintype.card ↥I ≤ 5 := by
    rw [Fintype.card_coe]
    exact hI
  have hρ : ∀ g, ((blkHom I Q hQ) g)ᵀ * blk I H * ((blkHom I Q hQ) g).map σ = blk I H := by
    intro g
    have h1 : blk I ((Q g)ᵀ * H * (Q g).map σ) = blk I H := congrArg (blk I) (hform g)
    have h2 : blk I ((Q g)ᵀ) * blk I H * blk I ((Q g).map σ) = blk I H := by
      rw [← (hQ g).transpose.blk_mul H, ← ((hQ g).transpose.mul hH).blk_mul ((Q g).map σ)]
      exact h1
    change (blk I (Q g))ᵀ * blk I H * (blk I (Q g)).map (σ : Ω →+* Ω) = blk I H
    rw [← blk_transpose (Q g), ← blk_map (Q g) (σ : Ω →+* Ω)]
    exact h2
  have h := IsAlternatingEightCover.map_eq_one_of_card_le_five_of_form hJ σ hσ
      (G := blk I H) (hH.isUnit_blk hHu) hcard (blkHom I Q hQ) hρ g
  rw [blkHom_apply] at h
  exact h

end Representations

section Classes

variable {K : Type*} [Field K]

theorem entries_eq_of_commute_diagonal {A : Type*} (w : A → ι → K) {M : Matrix ι ι K}
    (hM : ∀ a, M * diagonal (w a) = diagonal (w a) * M) {α β : ι} (h : M α β ≠ 0) :
    (fun a => w a α) = fun a => w a β := by
  funext a
  have ha := congr_fun (congr_fun (hM a) α) β
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at ha
  exact (mul_left_cancel₀ h (ha.trans (mul_comm _ _))).symm

theorem splits_fiber_of_forall {κ : Type*} [DecidableEq κ] (c : ι → κ) {M : Matrix ι ι K}
    (hM : ∀ a b, M a b ≠ 0 → c a = c b) (k : κ) :
    Splits (Finset.univ.filter fun a => c a = k) M := by
  intro a b hab
  by_contra h
  have hcab : c a = c b := hM a b h
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hab
  rw [hcab] at hab
  by_cases hb : c b = k
  · exact (hab.mp hb) hb
  · exact hb (hab.mpr hb)

theorem mulVec_eq_self_of_blk_eq_one {κ : Type*} [DecidableEq κ] (c : ι → κ) (k₀ : κ)
    (M : Matrix ι ι K) (hs : ∀ k, Splits (Finset.univ.filter fun a => c a = k) M)
    (h1 : ∀ k, k ≠ k₀ → blk (Finset.univ.filter fun a => c a = k) M = 1) (y : ι → K)
    (hy : ∀ a, c a = k₀ → y a = 0) : M *ᵥ y = y := by
  funext a
  rw [mulVec_apply_eq_blk_of_splits M y (hs (c a)) (by simp)]
  by_cases ha : c a = k₀
  · rw [hy a ha]
    rw [Matrix.mulVec_apply_eq_sum]
    apply Finset.sum_eq_zero
    intro b _
    have hb : c (b : ι) = c a := (Finset.mem_filter.mp b.2).2
    rw [hy (b : ι) (hb.trans ha), mul_zero]
  · rw [h1 (c a) ha, Matrix.one_mulVec]

end Classes

end SpBlocks

end CFSG.StandardType
