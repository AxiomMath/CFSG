module

public import CFSG.Quasithin.H13.L32NS8Model
public import Certificates.Certificate7211
public import Mathlib.Tactic.Polynomial.Basic
public import Std.Tactic.BVDecide.Normalize.Bool

public section

namespace CFSG.Quasithin.H13.S8Cert

open Matrix Mat8Cert CFSG.Quasithin.H13.L1442M S7Cert

theorem planeCheck_eq : planeCheck = true :=
  Certificates.certificate7211

theorem planeCheck_parts :
    t8BasicB = true ∧ t8FixB = true ∧ t8PlaneB = true ∧ s8IIB = true ∧ tvB = true := by
  have h := planeCheck_eq
  simp only [planeCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem s8G_valid : ∀ g ∈ s8G, Valid8 g := by
  intro g hg
  simp only [s8G, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> exact ⟨rfl, by decide⟩

theorem exists_mem_s8_evalW (w : List ℕ) :
    ∃ u ∈ s8, (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 (evalW s8G w) := by
  rw [s8_eq]
  exact exists_evalW s8G s8G_valid s8G_unit w

theorem t8G_valid : ∀ g ∈ t8G, Valid8 g := fun g hg => by
  obtain ⟨w, -, rfl⟩ := List.mem_map.mp hg
  exact valid8_evalW s8G s8G_valid w

theorem t8G_unit : ∀ g ∈ t8G, ∃ u : GL (Fin 8) (ZMod 2),
    (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 g := fun g hg => by
  obtain ⟨w, -, rfl⟩ := List.mem_map.mp hg
  obtain ⟨u, -, hu⟩ := exists_mem_s8_evalW w
  exact ⟨u, hu⟩

@[expose] def T1 : Subgroup (GL (Fin 8) (ZMod 2)) := genSub t8G

theorem T1_le_s8 : T1 ≤ s8 := by
  refine (Subgroup.closure_le _).mpr fun u hu => ?_
  obtain ⟨w, -, hw⟩ := List.mem_map.mp (show colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ t8G
    from hu)
  obtain ⟨v, hv, hv'⟩ := exists_mem_s8_evalW w
  have : u = v := Units.ext (by rw [hv', hw, dec8_colsOf])
  exact this ▸ hv

theorem card_T1 : Nat.card T1 = 128 := by
  have h := planeCheck_parts.1
  simp only [t8BasicB, Bool.and_eq_true, beq_iff_eq] at h
  unfold T1
  rw [card_genSub_of h.1 t8G_unit]
  exact h.2

theorem mem_T1_of {g : List ℕ} (hg : g ∈ t8G) :
    ∃ u ∈ T1, (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 g := by
  obtain ⟨u, hu⟩ := t8G_unit g hg
  exact ⟨u, mem_genSub_of_mem t8G_valid hg hu, hu⟩

theorem eq_vR_of_fix {v : Fin 8 → ZMod 2}
    (hv : ∀ t ∈ T1, (t : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v = v) (h0 : v ≠ 0) :
    v = vec8 vR := by
  have h := planeCheck_parts.2.1
  have hvn : v = vec8 (code8 v) := (vec8_code8 v).symm
  have hfix : ∀ g ∈ t8G, mv8 g (code8 v) = code8 v := by
    intro g hg
    obtain ⟨u, hu, hu'⟩ := mem_T1_of hg
    have h1 := hv u hu
    rw [hu', hvn, dec8_mulVec] at h1
    exact vec8_inj (mv8_lt (t8G_valid g hg) _) (code8_lt v) h1
  have hmem : code8 v ∈ (List.range 256).filter (fun v => t8G.all fun t => mv8 t v == v) := by
    simp only [List.mem_filter, List.mem_range, List.all_eq_true, beq_iff_eq]
    exact ⟨code8_lt v, hfix⟩
  simp only [t8FixB, beq_iff_eq] at h
  rw [h] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h1 | h1
  · exact absurd (by rw [hvn, h1, vec8_zero]) h0
  · rw [hvn, h1]

theorem inII_of_plane {a : Fin 8 → ZMod 2} (h0 : a ≠ 0)
    (hR : a ≠ vec8 vR)
    (ha : ∀ t ∈ T1, (t : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec a = a ∨
      (t : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec a = a + vec8 vR) :
    inII (code8 a) = true := by
  have h := planeCheck_parts.2.2.1
  simp only [t8PlaneB, List.all_eq_true, List.mem_range] at h
  have hvn : a = vec8 (code8 a) := (vec8_code8 a).symm
  have hlt : code8 a ^^^ vR < 256 := Nat.xor_lt_two_pow (n := 8) (code8_lt a) (by decide)
  have hgen : (t8G.all fun t => mv8 t (code8 a) == code8 a ||
      mv8 t (code8 a) == (code8 a ^^^ vR)) = true := by
    simp only [List.all_eq_true, Bool.or_eq_true, beq_iff_eq]
    intro g hg
    obtain ⟨u, hu, hu'⟩ := mem_T1_of hg
    rcases ha u hu with h1 | h1
    · left
      rw [hu', hvn, dec8_mulVec] at h1
      exact vec8_inj (mv8_lt (t8G_valid g hg) _) (code8_lt a) h1
    · right
      rw [hu', hvn, dec8_mulVec, ← vec8_xor] at h1
      exact vec8_inj (mv8_lt (t8G_valid g hg) _) hlt h1
  have h2 := h (code8 a) (code8_lt a)
  rw [hgen] at h2
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_true, Bool.false_eq_true, or_false,
    Bool.and_eq_true] at h2
  rcases h2 with (h3 | h3) | h3
  · exact absurd (by rw [hvn, h3, vec8_zero]) h0
  · exact absurd (by rw [hvn, h3]) hR
  · exact h3.1

theorem inII_s8 {u : GL (Fin 8) (ZMod 2)} (hu : u ∈ s8)
    (v : Fin 8 → ZMod 2) :
    inII (code8 ((u : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v)) = inII (code8 v) := by
  have h := planeCheck_parts.2.2.2.1
  simp only [s8IIB, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  rw [s8_eq] at hu
  induction hu using Subgroup.closure_induction generalizing v with
  | mem g hg =>
    have hg' : colsOf (g : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ s8G := hg
    have hv : v = vec8 (code8 v) := (vec8_code8 v).symm
    rw [hv, ← dec8_colsOf (g : Matrix (Fin 8) (Fin 8) (ZMod 2)), dec8_mulVec,
      code8_vec8 (mv8_lt (s8G_valid _ hg') _), code8_vec8 (code8_lt v)]
    exact h _ hg' _ (code8_lt v)
  | one => simp
  | mul x y _ _ hx hy =>
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hx, hy]
  | inv x _ hx =>
    have h1 := hx (((x⁻¹ : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v)
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec] at h1
    exact h1.symm

@[expose] def blk (M N : Matrix (Fin 4) (Fin 4) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks M 0 0 N)

theorem blk_mul (M N M' N' : Matrix (Fin 4) (Fin 4) (ZMod 2)) :
    blk M N * blk M' N' = blk (M * M') (N * N') := by
  unfold blk
  rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_mul_equiv,
    Matrix.fromBlocks_multiply]
  simp

theorem blk_one : blk 1 1 = 1 := by
  unfold blk
  rw [Matrix.fromBlocks_one, Matrix.reindex_apply, Matrix.submatrix_one_equiv]

theorem transpose_transvection (i j : Fin 4) (c : ZMod 2) :
    (transvection i j c)ᵀ = transvection j i c := by
  rw [transvection, transvection, Matrix.transpose_add, Matrix.transpose_one,
    Matrix.transpose_single]

theorem transvection_inv (i j : Fin 4) (hij : i ≠ j) :
    (transvection i j (1 : ZMod 2))⁻¹ = transvection i j 1 := by
  refine Matrix.inv_eq_left_inv ?_
  rw [transvection_mul_transvection_same i j hij, show (1 : ZMod 2) + 1 = 0 by decide,
    transvection_zero]

theorem blk_transvection_eq (i j : Fin 4) (hij : i ≠ j) :
    blk (transvection i j 1) (transvection j i 1) = dec8 (tvCols i j) := by
  fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide +kernel

theorem blk_transvection_mem (i j : Fin 4) (hij : i ≠ j) :
    ∃ u ∈ s8, (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) =
      blk (transvection i j 1) (transvection j i 1) := by
  have h := planeCheck_parts.2.2.2.2
  simp only [tvB, List.all_eq_true, beq_iff_eq] at h
  have hw : ((i : ℕ), (j : ℕ)) ∈ tvW.map (fun p => (p.1, p.2.1)) := by
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide
  obtain ⟨⟨i', j', w⟩, hmem, heq⟩ := List.mem_map.mp hw
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl⟩ := heq
  obtain ⟨u, hu, hu'⟩ := exists_mem_s8_evalW w
  refine ⟨u, hu, ?_⟩
  rw [hu', blk_transvection_eq i j hij]
  exact congrArg dec8 (h _ hmem)

theorem blk_mem_s8 (M : Matrix (Fin 4) (Fin 4) (ZMod 2))
    (hM : M.det ≠ 0) : ∃ u ∈ s8, (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = blk M (M⁻¹)ᵀ := by
  refine Matrix.diagonal_transvection_induction_of_det_ne_zero
    (fun M => ∃ u ∈ s8, (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = blk M (M⁻¹)ᵀ) M hM ?_ ?_ ?_
  · intro D hD
    have hD1 : Matrix.diagonal D = 1 := by
      have : ∀ i, D i = 1 := by
        intro i
        rw [Matrix.det_diagonal] at hD
        have hi : D i ≠ 0 := fun h0 => hD (Finset.prod_eq_zero (Finset.mem_univ i) h0)
        revert hi
        generalize D i = c
        revert c
        decide
      rw [show D = fun _ => 1 from funext this, Matrix.diagonal_one]
    refine ⟨1, one_mem _, ?_⟩
    rw [hD1, inv_one, Matrix.transpose_one, blk_one, Units.val_one]
  · intro t
    obtain ⟨i, j, hij, c⟩ := t
    rw [TransvectionStruct.toMatrix_mk]
    have hc : c = 0 ∨ c = 1 := by revert c; decide
    rcases hc with rfl | rfl
    · refine ⟨1, one_mem _, ?_⟩
      rw [transvection_zero, inv_one, Matrix.transpose_one, blk_one, Units.val_one]
    · rw [transvection_inv i j hij, transpose_transvection]
      exact blk_transvection_mem i j hij
  · rintro A B hA hB ⟨u, hu, hu'⟩ ⟨v, hv, hv'⟩
    refine ⟨u * v, mul_mem hu hv, ?_⟩
    rw [Units.val_mul, hu', hv', blk_mul, Matrix.mul_inv_rev, Matrix.transpose_mul]

theorem s8g4_eq : (s8g4 : Matrix (Fin 8) (Fin 8) (ZMod 2)) =
    Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (0 : Matrix (Fin 4) (Fin 4) (ZMod 2)) (1 : Matrix (Fin 4) (Fin 4) (ZMod 2))
        (1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) 0) := by
  decide +kernel

theorem s8g4_mem : s8g4 ∈ s8 := Subgroup.subset_closure (by simp)

theorem blk_mul_tau (Q N : Matrix (Fin 4) (Fin 4) (ZMod 2)) :
    blk Q N * (s8g4 : Matrix (Fin 8) (Fin 8) (ZMod 2)) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 0 Q N 0) := by
  rw [s8g4_eq]
  unfold blk
  rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_mul_equiv,
    Matrix.fromBlocks_multiply]
  simp

end CFSG.Quasithin.H13.S8Cert
