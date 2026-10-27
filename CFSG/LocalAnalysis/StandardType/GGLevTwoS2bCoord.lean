module

public import CFSG.LieType.Universal.Spin.Roots.TypeB
public import CFSG.LocalAnalysis.StandardType.GGLevTwoRoots

public section

namespace CFSG.StandardType.LevTwo

open CFSG.LieType.RootSystem
open scoped Matrix

@[expose] def levTwoS2b_coord (n : ℕ) : (Fin n → ℤ) → (Fin n → ℤ) :=
  CFSG.LieType.Universal.Spin.toStdB n

@[expose] def levTwoS2b_ofCoord (n : ℕ) : (Fin n → ℤ) → (Fin n → ℤ) :=
  CFSG.LieType.Universal.Spin.ofStdB n

theorem levTwoS2b_coord_add (n : ℕ) (v w : Fin n → ℤ) :
    levTwoS2b_coord n (v + w) = levTwoS2b_coord n v + levTwoS2b_coord n w :=
  CFSG.LieType.Universal.Spin.toStdB_add n v w

theorem levTwoS2b_coord_sub (n : ℕ) (v w : Fin n → ℤ) :
    levTwoS2b_coord n (v - w) = levTwoS2b_coord n v - levTwoS2b_coord n w :=
  CFSG.LieType.Universal.Spin.toStdB_sub n v w

theorem levTwoS2b_coord_neg (n : ℕ) (v : Fin n → ℤ) :
    levTwoS2b_coord n (-v) = -levTwoS2b_coord n v :=
  CFSG.LieType.Universal.Spin.toStdB_neg n v

theorem levTwoS2b_coord_smul (n : ℕ) (c : ℤ) (v : Fin n → ℤ) :
    levTwoS2b_coord n (c • v) = c • levTwoS2b_coord n v :=
  CFSG.LieType.Universal.Spin.toStdB_smul n c v

theorem levTwoS2b_coord_injective (n : ℕ) : Function.Injective (levTwoS2b_coord n) :=
  CFSG.LieType.Universal.Spin.toStdB_injective n

theorem levTwoS2b_coord_ofCoord (n : ℕ) (e : Fin n → ℤ) :
    levTwoS2b_coord n (levTwoS2b_ofCoord n e) = e :=
  CFSG.LieType.Universal.Spin.toStdB_ofStdB n e

theorem levTwoS2b_isRt_iff_coord (n : ℕ) (v : Fin n → ℤ) :
    IsRt (CFSG.LieType.Universal.Spin.isFiniteType_cartanB n) v ↔
      (∃ (i j : Fin n) (s t : ℤ), i ≠ j ∧ (s = 1 ∨ s = -1) ∧ (t = 1 ∨ t = -1) ∧
          levTwoS2b_coord n v = Pi.single i s + Pi.single j t) ∨
        ∃ (i : Fin n) (s : ℤ), (s = 1 ∨ s = -1) ∧ levTwoS2b_coord n v = Pi.single i s := by
  have hmem : IsRt (CFSG.LieType.Universal.Spin.isFiniteType_cartanB n) v ↔
      v ∈ roots (CFSG.LieType.Universal.Spin.isFiniteType_cartanB n) ∅ := by
    constructor
    · rintro ⟨w, j, rfl⟩
      exact Or.inl ⟨w, j, rfl⟩
    · rintro (⟨w, j, rfl⟩ | ⟨w, j, hj, -⟩)
      · exact ⟨w, j, rfl⟩
      · exact absurd hj (Set.notMem_empty j)
  rw [hmem, CFSG.LieType.Universal.Spin.rootsB_eq]
  rfl

@[expose] def levTwoS2b_D {n : ℕ} {p : ℕ} (c : Fin n → ZMod p) (k : Fin n) : ZMod p :=
  ∑ j : Fin n, if k.val ≤ j.val then c j else 0

theorem levTwoS2b_lam_coord (n : ℕ) (p : ℕ) (c : Fin n → ZMod p) (v : Fin n → ℤ) :
    lam c v = ∑ k : Fin n, ((levTwoS2b_coord n v k : ℤ) : ZMod p) * levTwoS2b_D c k := by
  have hv : ∀ a : Fin n,
      ((v a : ℤ) : ZMod p) =
        ∑ k : Fin n, (if k.val ≤ a.val then (levTwoS2b_coord n v k : ZMod p) else 0) := by
    intro a
    have h := congrFun (CFSG.LieType.Universal.Spin.ofStdB_toStdB n v) a
    rw [CFSG.LieType.Universal.Spin.ofStdB] at h
    rw [← h]
    push_cast
    rfl
  simp only [lam, levTwoS2b_D]
  calc ∑ a : Fin n, ((v a : ℤ) : ZMod p) * c a
      = ∑ a : Fin n, (∑ k : Fin n,
          (if k.val ≤ a.val then (levTwoS2b_coord n v k : ZMod p) else 0)) * c a :=
        Finset.sum_congr rfl fun a _ => by rw [hv a]
    _ = ∑ a : Fin n, ∑ k : Fin n,
          (if k.val ≤ a.val then (levTwoS2b_coord n v k : ZMod p) else 0) * c a := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_mul]
    _ = ∑ k : Fin n, ∑ a : Fin n,
          (if k.val ≤ a.val then (levTwoS2b_coord n v k : ZMod p) else 0) * c a :=
        Finset.sum_comm
    _ = ∑ k : Fin n, (levTwoS2b_coord n v k : ZMod p) *
          ∑ a : Fin n, (if k.val ≤ a.val then c a else 0) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        by_cases h : k.val ≤ a.val <;> simp [h]

theorem levTwoS2b_lam_ofCoord (n p : ℕ) (c : Fin n → ZMod p) (e : Fin n → ℤ) :
    lam c (levTwoS2b_ofCoord n e) = ∑ k : Fin n, ((e k : ℤ) : ZMod p) * levTwoS2b_D c k := by
  rw [levTwoS2b_lam_coord]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [levTwoS2b_coord_ofCoord]

theorem levTwoS2b_lam_eps_sub (n p : ℕ) (c : Fin n → ZMod p) (a b : Fin n) :
    lam c (levTwoS2b_ofCoord n (Pi.single a 1 - Pi.single b 1)) =
      levTwoS2b_D c a - levTwoS2b_D c b := by
  rw [levTwoS2b_lam_ofCoord]
  simp only [Pi.sub_apply, Int.cast_sub, sub_mul, Finset.sum_sub_distrib]
  rw [Fintype.sum_eq_single a]
  · rw [Fintype.sum_eq_single b]
    · simp
    · intro d hd
      simp [hd]
  · intro d hd
    simp [hd]

theorem levTwoS2b_lam_eps_add (n p : ℕ) (c : Fin n → ZMod p) (a b : Fin n) :
    lam c (levTwoS2b_ofCoord n (Pi.single a 1 + Pi.single b 1)) =
      levTwoS2b_D c a + levTwoS2b_D c b := by
  rw [levTwoS2b_lam_ofCoord]
  simp only [Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib]
  rw [Fintype.sum_eq_single a]
  · rw [Fintype.sum_eq_single b]
    · simp
    · intro d hd
      simp [hd]
  · intro d hd
    simp [hd]

theorem levTwoS2b_rank_bounds (n : ℕ) (_hn : 2 ≤ n) (p : ℕ) (c : Fin n → ZMod p)
    (Φ : Set (Fin n → ℤ)) (h : LevTwoData (CFSG.LieType.Universal.Spin.isFiniteType_cartanB n)
      p c Φ) :
    ∃ s : Finset (Fin n → ℤ), (s : Set (Fin n → ℤ)) ⊆ Φ ∧ 3 ≤ s.card ∧ s.card ≤ n := by
  obtain ⟨s, hs, hli, h3, -, -⟩ := h.rank
  refine ⟨s, hs, h3, ?_⟩
  have hcard := LinearIndependent.fintype_card_le_finrank hli
  rw [Fintype.card_coe, Module.finrank_pi, Fintype.card_fin] at hcard
  exact hcard

theorem levTwoS2b_ofCoord_sub (n : ℕ) (e f : Fin n → ℤ) :
    levTwoS2b_ofCoord n (e - f) = levTwoS2b_ofCoord n e - levTwoS2b_ofCoord n f := by
  funext a
  simp only [levTwoS2b_ofCoord, CFSG.LieType.Universal.Spin.ofStdB, Pi.sub_apply]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases h : b.val ≤ a.val <;> simp [h]

theorem levTwoS2b_ofCoord_neg (n : ℕ) (e : Fin n → ℤ) :
    levTwoS2b_ofCoord n (-e) = -levTwoS2b_ofCoord n e := by
  funext a
  simp only [levTwoS2b_ofCoord, CFSG.LieType.Universal.Spin.ofStdB, Pi.neg_apply]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases h : b.val ≤ a.val <;> simp [h]

@[expose] def levTwoS2b_longCoord (n : ℕ) (e : Fin n → ℤ) : Prop :=
  ∃ (a b : Fin n) (s t : ℤ), a ≠ b ∧ (s = 1 ∨ s = -1) ∧ (t = 1 ∨ t = -1) ∧
    e = Pi.single a s + Pi.single b t

@[expose] def levTwoS2b_shortCoord (n : ℕ) (e : Fin n → ℤ) : Prop :=
  ∃ (a : Fin n) (s : ℤ), (s = 1 ∨ s = -1) ∧ e = Pi.single a s

@[expose] def levTwoS2b_isLong (n : ℕ) (v : Fin n → ℤ) : Prop :=
  levTwoS2b_longCoord n (levTwoS2b_coord n v)

@[expose] def levTwoS2b_isShort (n : ℕ) (v : Fin n → ℤ) : Prop :=
  levTwoS2b_shortCoord n (levTwoS2b_coord n v)

@[expose] def levTwoS2b_allLong (n : ℕ) : Set (Fin n → ℤ) :=
  {v | IsRt (CFSG.LieType.Universal.Spin.isFiniteType_cartanB n) v ∧ levTwoS2b_isLong n v}

@[expose] def levTwoS2b_PhiCase2 (n : ℕ) (k : Fin n) : Set (Fin n → ℤ) :=
  {v | IsRt (CFSG.LieType.Universal.Spin.isFiniteType_cartanB n) v ∧ levTwoS2b_isLong n v ∧
    levTwoS2b_coord n v k = 0}

@[expose] def levTwoS2b_PhiCase3 (n p : ℕ) (c : Fin n → ZMod p) : Set (Fin n → ℤ) :=
  {v | IsRt (CFSG.LieType.Universal.Spin.isFiniteType_cartanB n) v ∧ levTwoS2b_isLong n v ∧
    lam c v = 0}

end CFSG.StandardType.LevTwo
