module

public import CFSG.LocalAnalysis.StandardType.GGHalfCentFrame

public section

namespace CFSG.StandardType.GGHalf

open CFSG.StandardType CFSG.StandardType.CoordSL Matrix

theorem supp_conj {n : ℕ} (A t : SpecialLinearGroup (Fin (n + 1)) F2) :
    supp (A * t * A⁻¹) = supp t := by
  unfold supp
  have hAA : (A : Matrix (Fin (n + 1)) (Fin (n + 1)) F2) *
      ((A⁻¹ : SpecialLinearGroup (Fin (n + 1)) F2) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) F2) = 1 := by
    have h := congrArg (fun x : SpecialLinearGroup (Fin (n + 1)) F2 =>
      (x : Matrix (Fin (n + 1)) (Fin (n + 1)) F2)) (mul_inv_cancel A)
    rwa [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at h
  have hsub : (A : Matrix (Fin (n + 1)) (Fin (n + 1)) F2) *
        ((t : Matrix (Fin (n + 1)) (Fin (n + 1)) F2) - 1) *
        ((A⁻¹ : SpecialLinearGroup (Fin (n + 1)) F2) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) F2) =
      ((A * t * A⁻¹ : SpecialLinearGroup (Fin (n + 1)) F2) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) F2) - 1 := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hAA]
  rw [← hsub]
  have hAi : IsUnit (((A⁻¹ : SpecialLinearGroup (Fin (n + 1)) F2) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) F2).det) := by
    rw [(A⁻¹).2]; exact isUnit_one
  have hA : IsUnit ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) F2).det) := by
    rw [A.2]; exact isUnit_one
  rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hAi,
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ hA]

private theorem centSupp_fromBlocks_sub {l m o n : Type*} {α : Type*} [AddGroup α]
    (A A' : Matrix n l α) (B B' : Matrix n m α) (C C' : Matrix o l α) (D D' : Matrix o m α) :
    Matrix.fromBlocks A B C D - Matrix.fromBlocks A' B' C' D' =
      Matrix.fromBlocks (A - A') (B - B') (C - C') (D - D') := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp only [Matrix.sub_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]

private theorem centSupp_rank_fromBlocks_le {e s r : ℕ} (C : Matrix (Fin e) (Fin e) F2)
    (k : Fin s → ℕ) (hzero : ∀ i : Fin s, k i % 3 = 0 → C ^ k i - 1 = 0) :
    (Matrix.fromBlocks (Matrix.blockDiagonal fun i => C ^ k i - 1) 0 0
        (0 : Matrix (Fin r) (Fin r) F2)).rank ≤
      e * (Finset.univ.filter fun i : Fin s => k i % 3 ≠ 0).card := by
  classical
  let T : Finset (Fin s) := Finset.univ.filter fun i => k i % 3 ≠ 0
  let g : (Fin e × T) → ((Fin e × Fin s) ⊕ Fin r) := fun p => Sum.inl (p.1, p.2.1)
  have hg : Function.Injective g := by
    intro p q h
    simp only [g, Sum.inl.injEq, Prod.mk.injEq] at h
    exact Prod.ext h.1 (Subtype.ext h.2)
  let S : Finset ((Fin e × Fin s) ⊕ Fin r) := (Finset.univ : Finset (Fin e × T)).image g
  have hS : S.card = e * T.card := by
    simp only [S]
    rw [Finset.card_image_of_injective _ hg, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin, Fintype.card_coe]
  have hsupp : Function.support (Matrix.fromBlocks (Matrix.blockDiagonal fun i => C ^ k i - 1) 0 0
      (0 : Matrix (Fin r) (Fin r) F2)).row ⊆ (S : Set ((Fin e × Fin s) ⊕ Fin r)) := by
    intro x hx
    by_contra hxS
    refine hx ?_
    funext y
    rw [Matrix.row_apply]
    rcases x with ⟨a, i⟩ | b
    · have hiT : k i % 3 = 0 := by
        by_contra hne
        exact hxS (by
          change Sum.inl (a, i) ∈ (Finset.univ : Finset (Fin e × T)).image g
          rw [Finset.mem_image]
          exact ⟨(a, ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩⟩),
            Finset.mem_univ _, rfl⟩)
      rcases y with ⟨b, j⟩ | c
      · rw [Matrix.fromBlocks_apply₁₁, Matrix.blockDiagonal_apply]
        by_cases hij : i = j
        · subst hij
          rw [if_pos rfl, hzero i hiT, Matrix.zero_apply, Pi.zero_apply]
        · rw [if_neg hij, Pi.zero_apply]
      · simp [Matrix.fromBlocks_apply₁₂]
    · rcases y with ⟨b', j'⟩ | c <;>
        simp [Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
  calc (Matrix.fromBlocks (Matrix.blockDiagonal fun i => C ^ k i - 1) 0 0
        (0 : Matrix (Fin r) (Fin r) F2)).rank
      ≤ S.card := Matrix.rank_le_card_of_support_subset _ S hsupp
    _ = e * T.card := hS

private theorem centSupp_le_rank_fromBlocks {e s r : ℕ} (C : Matrix (Fin e) (Fin e) F2)
    (k : Fin s → ℕ) (hinv : ∀ i : Fin s, k i % 3 ≠ 0 → IsUnit (C ^ k i - 1)) :
    e * (Finset.univ.filter fun i : Fin s => k i % 3 ≠ 0).card ≤
      (Matrix.fromBlocks (Matrix.blockDiagonal fun i => C ^ k i - 1) 0 0
        (0 : Matrix (Fin r) (Fin r) F2)).rank := by
  classical
  let T : Finset (Fin s) := Finset.univ.filter fun i => k i % 3 ≠ 0
  let g : (Fin e × T) → ((Fin e × Fin s) ⊕ Fin r) := fun p => Sum.inl (p.1, p.2.1)
  have hY : (Matrix.fromBlocks (Matrix.blockDiagonal fun i => C ^ k i - 1) 0 0
        (0 : Matrix (Fin r) (Fin r) F2)).submatrix g g =
      Matrix.blockDiagonal (fun i : T => C ^ k i.1 - 1) := by
    ext p q
    rcases p with ⟨a, i⟩
    rcases q with ⟨b, j⟩
    by_cases h : i = j
    · subst h
      simp only [Matrix.submatrix_apply, g, Matrix.fromBlocks_apply₁₁, Matrix.blockDiagonal_apply,
        Matrix.sub_apply, Matrix.one_apply, Pi.sub_apply]
    · have h' : i.1 ≠ j.1 := fun hh => h (Subtype.ext hh)
      simp only [Matrix.submatrix_apply, g, Matrix.fromBlocks_apply₁₁, Matrix.blockDiagonal_apply,
        h, h']
  have hdet : IsUnit (Matrix.blockDiagonal (fun i : T => C ^ k i.1 - 1)) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_blockDiagonal, IsUnit.prod_iff]
    intro i _
    exact (Matrix.isUnit_iff_isUnit_det _).mp (hinv i.1 (Finset.mem_filter.mp i.2).2)
  have hrank : (Matrix.blockDiagonal (fun i : T => C ^ k i.1 - 1)).rank = e * T.card := by
    rw [Matrix.rank_of_isUnit _ hdet, Fintype.card_prod, Fintype.card_fin, Fintype.card_coe]
  calc e * T.card = (Matrix.blockDiagonal (fun i : T => C ^ k i.1 - 1)).rank := hrank.symm
    _ = ((Matrix.fromBlocks (Matrix.blockDiagonal fun i => C ^ k i - 1) 0 0
          (0 : Matrix (Fin r) (Fin r) F2)).submatrix g g).rank := by rw [hY]
    _ ≤ (Matrix.fromBlocks (Matrix.blockDiagonal fun i => C ^ k i - 1) 0 0
          (0 : Matrix (Fin r) (Fin r) F2)).rank := Matrix.rank_submatrix_le _ _ _

theorem supp_nsSL {n s r : ℕ} (ε : Fin (n + 1) ≃ (Fin (rootPB phi3).dim × Fin s) ⊕ Fin r)
    (k : Fin s → ℕ) :
    supp (SLNS.nsSL ε det_rootMat_phi3 k) =
      2 * (Finset.univ.filter fun i : Fin s => k i % 3 ≠ 0).card := by
  classical
  have hcard : Nat.card F2 = 2 := by
    simpa using GaloisField.card 2 1 (by omega : (1 : ℕ) ≠ 0)
  have hK : ¬ 3 ∣ Nat.card F2 - 1 := by
    rw [hcard]; norm_num
  have hzero : ∀ i : Fin s, k i % 3 = 0 → rootMat phi3 ^ k i - 1 = 0 := by
    intro i hi
    obtain ⟨t, ht⟩ := Nat.dvd_of_mod_eq_zero hi
    rw [ht, pow_mul, rootMat_phi3_pow_three, one_pow, sub_self]
  have hinv : ∀ i : Fin s, k i % 3 ≠ 0 → IsUnit (rootMat phi3 ^ k i - 1) := by
    intro i hi
    have h3 : ¬ 3 ∣ k i := fun h => hi (Nat.mod_eq_zero_of_dvd h)
    have h := CoordSL.isUnit_rootMat_pow_sub (K := F2) (g := phi3) (ℓ := 3)
      Nat.prime_three hK natCast_three_ne_zero phi3_dvd_cyclotomic (k i) h3 (1 : F2)
    simpa using h
  have hcore : SLNS.nsCore (r := r) (rootMat phi3) k - 1 =
      Matrix.fromBlocks (Matrix.blockDiagonal fun i => rootMat phi3 ^ k i - 1) 0 0
        (0 : Matrix (Fin r) (Fin r) F2) := by
    have h1 : (1 : Matrix ((Fin (rootPB phi3).dim × Fin s) ⊕ Fin r)
          ((Fin (rootPB phi3).dim × Fin s) ⊕ Fin r) F2) =
        Matrix.fromBlocks (1 : Matrix (Fin (rootPB phi3).dim × Fin s)
            (Fin (rootPB phi3).dim × Fin s) F2) 0 0 (1 : Matrix (Fin r) (Fin r) F2) :=
      Matrix.fromBlocks_one.symm
    rw [SLNS.nsCore, h1, centSupp_fromBlocks_sub, Matrix.fromBlocks_inj]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [show (1 : Matrix (Fin (rootPB phi3).dim × Fin s)
              (Fin (rootPB phi3).dim × Fin s) F2) =
            Matrix.blockDiagonal (1 : Fin s → Matrix (Fin (rootPB phi3).dim)
              (Fin (rootPB phi3).dim) F2) from Matrix.blockDiagonal_one.symm,
        ← Matrix.blockDiagonal_sub]
      rfl
    · rw [sub_self]
    · rw [sub_self]
    · rw [sub_self]
  have hmat : SLNS.nsMat ε (rootMat phi3) k - 1 =
      (Matrix.fromBlocks (Matrix.blockDiagonal fun i => rootMat phi3 ^ k i - 1) 0 0
        (0 : Matrix (Fin r) (Fin r) F2)).submatrix ε ε := by
    rw [SLNS.nsMat, ← hcore]
    simp only [Matrix.submatrix_sub, Pi.sub_apply, Matrix.submatrix_one_equiv]
  have hXle := centSupp_rank_fromBlocks_le (C := rootMat phi3) (r := r) k hzero
  have hXge := centSupp_le_rank_fromBlocks (C := rootMat phi3) (r := r) k hinv
  have hX : (Matrix.fromBlocks (Matrix.blockDiagonal fun i => rootMat phi3 ^ k i - 1) 0 0
        (0 : Matrix (Fin r) (Fin r) F2)).rank =
      (rootPB phi3).dim * (Finset.univ.filter fun i : Fin s => k i % 3 ≠ 0).card :=
    le_antisymm hXle hXge
  unfold supp
  change Matrix.rank (SLNS.nsMat ε (rootMat phi3) k - 1) =
    2 * (Finset.univ.filter fun i : Fin s => k i % 3 ≠ 0).card
  rw [hmat, Matrix.rank_submatrix, hX, rootPB_phi3_dim]

end CFSG.StandardType.GGHalf

end
