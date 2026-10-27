module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagData
import CFSG.LieType.SteinbergBRParabolicTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.SP207Lin

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type*} [Field K] {m : ℕ}

@[expose] def CutBetween (I : Set ℕ) (q p : Fin m) : Prop := ∃ i ∈ I, (q : ℕ) < i ∧ i ≤ (p : ℕ)

open Classical in
@[expose] noncomputable def blk (I : Set ℕ) (p : Fin m) : ℕ :=
  ((Finset.range m).filter fun i => i ∈ I ∧ i ≤ (p : ℕ)).card

theorem blk_lt_iff (I : Set ℕ) (p q : Fin m) : blk I q < blk I p ↔ CutBetween I q p := by
  classical
  unfold blk CutBetween
  constructor
  · intro h
    have hqp : (q : ℕ) < p := by
      by_contra hn
      refine h.not_ge (Finset.card_le_card fun i hi => ?_)
      simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
      exact ⟨hi.1, hi.2.1, hi.2.2.trans (not_lt.1 hn)⟩
    have hsub : ((Finset.range m).filter fun i => i ∈ I ∧ i ≤ (q : ℕ)) ⊂
        ((Finset.range m).filter fun i => i ∈ I ∧ i ≤ (p : ℕ)) := by
      refine Finset.ssubset_iff_subset_ne.2 ⟨fun i hi => ?_, fun he => h.ne (by rw [he])⟩
      simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
      exact ⟨hi.1, hi.2.1, hi.2.2.trans hqp.le⟩
    obtain ⟨i, hi, hni⟩ := Finset.exists_of_ssubset hsub
    simp only [Finset.mem_filter, Finset.mem_range, not_and] at hi hni
    exact ⟨i, hi.2.1, not_le.1 (hni hi.1 hi.2.1), hi.2.2⟩
  · rintro ⟨i, hiI, hqi, hip⟩
    refine Finset.card_lt_card (Finset.ssubset_iff_of_subset (fun j hj => ?_) |>.2 ⟨i, ?_, ?_⟩)
    · simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
      exact ⟨hj.1, hj.2.1, hj.2.2.trans (hqi.le.trans hip)⟩
    · simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨p.2.trans_le' hip, hiI, hip⟩
    · simp only [Finset.mem_filter, Finset.mem_range, not_and, not_le]
      exact fun _ _ => hqi

theorem mem_flagStabilizer_iff {I : Set ℕ} {x : SpecialLinearGroup (Fin m) K} :
    x ∈ flagStabilizer m K I ↔ ∀ p q : Fin m, CutBetween I q p → x.val p q = 0 := by
  rw [mem_flagStabilizer]
  constructor
  · rintro h p q ⟨i, hi, hqi, hip⟩
    exact CFSG.LieType.SteinbergBR.BlockPar.mem_stabilizer_flagSpace_iff.1 (h i hi) p q hip hqi
  · intro h i hi
    exact CFSG.LieType.SteinbergBR.BlockPar.mem_stabilizer_flagSpace_iff.2 fun p q hip hqi =>
      h p q ⟨i, hi, hqi, hip⟩

theorem exists_unipotent_blockDiag {I : Set ℕ} {x : SpecialLinearGroup (Fin m) K}
    (hx : x ∈ flagStabilizer m K I) :
    ∃ u : SpecialLinearGroup (Fin m) K, u ∈ flagStabilizer m K I ∧ u ∈ unitriangular m K ∧
      ∀ p q : Fin m, (CutBetween I q p ∨ CutBetween I p q) →
        ((u⁻¹ * x : SpecialLinearGroup (Fin m) K) : Matrix (Fin m) (Fin m) K) p q = 0 := by
  set b : Fin m → ℕ := blk I with hbdef
  have hxb : (x : Matrix (Fin m) (Fin m) K).BlockTriangular b := fun p q h =>
    (mem_flagStabilizer_iff.1 hx) p q ((blk_lt_iff I p q).1 h)
  set l : Matrix (Fin m) (Fin m) K :=
    Matrix.of fun p q => if b p = b q then (x : Matrix (Fin m) (Fin m) K) p q else 0 with hl
  have hlb : l.BlockTriangular b := fun p q h => by simp [hl, h.ne']
  have hld : l.BlockTriangular fun p => OrderDual.toDual (b p) := fun p q h => by
    have h' : b p < b q := by simpa using h
    simp [hl, h'.ne]
  have hdet : l.det = 1 := by
    rw [hlb.det, ← x.prop, hxb.det]
    refine Finset.prod_congr rfl fun k _ => congrArg Matrix.det ?_
    ext ⟨p, hp⟩ ⟨q, hq⟩
    simp [Matrix.toSquareBlock, Matrix.toSquareBlockProp, hl, hp, hq]
  let L : SpecialLinearGroup (Fin m) K := ⟨l, hdet⟩
  have hLinv : ((L⁻¹ : SpecialLinearGroup (Fin m) K) : Matrix (Fin m) (Fin m) K) = l⁻¹ := by
    have h : l * ((L⁻¹ : SpecialLinearGroup (Fin m) K) : Matrix (Fin m) (Fin m) K) = 1 :=
      congrArg Subtype.val (mul_inv_cancel L)
    exact (Matrix.inv_eq_right_inv h).symm
  have : Invertible l := Matrix.invertibleOfIsUnitDet l (by rw [hdet]; exact isUnit_one)
  have hw1 : (l⁻¹).BlockTriangular b := blockTriangular_inv_of_blockTriangular hlb
  have hw2 : (l⁻¹).BlockTriangular fun p => OrderDual.toDual (b p) :=
    blockTriangular_inv_of_blockTriangular hld
  have hwd : ∀ p q, b p ≠ b q → l⁻¹ p q = 0 := fun p q h => by
    rcases lt_or_gt_of_ne h with h | h
    · exact hw2 (by simpa using h)
    · exact hw1 h
  have hdiag : ∀ p q, b p = b q →
      ((x : Matrix (Fin m) (Fin m) K) * l⁻¹) p q = (1 : Matrix (Fin m) (Fin m) K) p q := by
    intro p q hpq
    have h1 : ((x : Matrix (Fin m) (Fin m) K) * l⁻¹) p q = (l * l⁻¹) p q := by
      simp only [Matrix.mul_apply]
      refine Finset.sum_congr rfl fun r _ => ?_
      by_cases hr : b p = b r
      · simp [hl, hr]
      · simp [hwd r q (fun h => hr (hpq.trans h.symm))]
    rw [h1, Matrix.mul_inv_of_invertible]
  have hu : ((x * L⁻¹ : SpecialLinearGroup (Fin m) K) : Matrix (Fin m) (Fin m) K) =
      (x : Matrix (Fin m) (Fin m) K) * l⁻¹ := by
    rw [← hLinv]
    exact Matrix.SpecialLinearGroup.coe_mul x L⁻¹
  have hub : ((x : Matrix (Fin m) (Fin m) K) * l⁻¹).BlockTriangular b := hxb.mul hw1
  refine ⟨x * L⁻¹, mem_flagStabilizer_iff.2 fun p q hs => ?_, ⟨fun i j hji => ?_, fun i => ?_⟩,
    fun p q hs => ?_⟩
  · rw [hu]
    exact hub ((blk_lt_iff I p q).2 hs)
  · rw [hu]
    rcases lt_trichotomy (b j) (b i) with h | h | h
    · exact hub h
    · rw [hdiag i j h.symm, Matrix.one_apply_ne hji.ne']
    · obtain ⟨c, -, hc1, hc2⟩ := (blk_lt_iff I j i).1 h
      omega
  · rw [hu, hdiag i i rfl, Matrix.one_apply_eq]
  · have h : (x * L⁻¹)⁻¹ * x = L := by group
    rw [h]
    have hb : b p ≠ b q := by
      rcases hs with hs | hs
      · exact ((blk_lt_iff I p q).2 hs).ne'
      · exact ((blk_lt_iff I q p).2 hs).ne
    simp [L, hl, hb]

theorem pow_eq_one_of_mem_unitriangular [CharP K 2] {k : ℕ} (hk : m ≤ 2 ^ k)
    {u : SpecialLinearGroup (Fin m) K} (hu : u ∈ unitriangular m K) : u ^ 2 ^ k = 1 := by
  set N : Matrix (Fin m) (Fin m) K := (u : Matrix (Fin m) (Fin m) K) - 1 with hN
  have hNe : ∀ p q : Fin m, q ≤ p → N p q = 0 := fun p q hqp => by
    rcases hqp.lt_or_eq with h | rfl
    · simp [hN, hu.1 p q h, Matrix.one_apply_ne h.ne']
    · simp [hN, hu.2 q]
  have hpow : ∀ j : ℕ, ∀ p q : Fin m, (q : ℕ) < p + j → (N ^ j) p q = 0 := by
    intro j
    induction j with
    | zero =>
      intro p q h
      rw [pow_zero, Matrix.one_apply_ne (by intro hpq; subst hpq; omega)]
    | succ j ih =>
      intro p q h
      rw [pow_succ, Matrix.mul_apply]
      refine Finset.sum_eq_zero fun r _ => ?_
      by_cases hr : (r : ℕ) < p + j
      · rw [ih p r hr, zero_mul]
      · rw [hNe r q (by omega), mul_zero]
  have hN0 : N ^ 2 ^ k = 0 := by
    ext p q
    exact hpow _ p q (by have := q.2; omega)
  have h2 : ∀ M : Matrix (Fin m) (Fin m) K, M + M = 0 := fun M => by
    rw [← two_smul K M, show (2 : K) = 0 by simpa using CharP.cast_eq_zero K 2, zero_smul]
  have hsq : ∀ M : Matrix (Fin m) (Fin m) K, (1 + M) ^ 2 = 1 + M ^ 2 := fun M => by
    calc (1 + M) ^ 2 = 1 + (M + M) + M ^ 2 := by noncomm_ring
      _ = 1 + M ^ 2 := by rw [h2 M, add_zero]
  have hform : ∀ j : ℕ, ((1 : Matrix (Fin m) (Fin m) K) + N) ^ 2 ^ j = 1 + N ^ 2 ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, pow_mul, ih, hsq, ← pow_mul]
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [Matrix.SpecialLinearGroup.coe_pow, show (u : Matrix (Fin m) (Fin m) K) = 1 + N by simp [hN],
    hform, hN0, add_zero, Matrix.SpecialLinearGroup.coe_one]

end CFSG.LocalAnalysis.UniquenessCase.UC22.SP207Lin
