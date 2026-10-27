module

public import CFSG.RankThree.PartTwo.Sec21.Item223Rank2ProofCliff
public import CFSG.Adapters.TauCetiExceptional.EvenD4
import all TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.D.TripledWeight

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item223Rank2Proof

open Matrix CFSG.TauCetiBridge.Twisted CFSG.TauCetiBridge.Minuscule CFSG.Blueprint.Chevalley
  CFSG.LieType.Steinberg.Minuscule TauCeti

section Natural

variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)

theorem mapMatrix_castM {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) :
    f.mapMatrix (castM A : Matrix (Fin n) (Fin n) R) = castM A := by
  ext r c
  simp [castM_apply]

theorem mapMatrix_lcMu (A : Matrix (Fin 8) (Fin 8) R) (a : Fin 8) :
    f.mapMatrix (lcMu A a) = lcMu (f.mapMatrix A) a := by
  ext r c
  simp [lcMu, Matrix.sum_apply, map_sum, castM_apply]

theorem mapMatrix_lcNu (A : Matrix (Fin 8) (Fin 8) R) (a : Fin 8) :
    f.mapMatrix (lcNu A a) = lcNu (f.mapMatrix A) a := by
  ext r c
  simp [lcNu, Matrix.sum_apply, map_sum, castM_apply]

theorem blk_mapMatrix (k : Fin 3) (M : Matrix (Fin 24) (Fin 24) R) :
    blk k (f.mapMatrix M) = f.mapMatrix (blk k M) :=
  rfl

end Natural

section Rational

theorem cliffEq_of_mem_points (A : Type) [CommRing A] (g : Matrix.GeneralLinearGroup (Fin 24) A)
    (hg : g ∈ D4Tripled.points A) : CliffEq (g : Matrix (Fin 24) (Fin 24) A) := by
  set T : Set (Matrix (Fin 24) (Fin 24) ℚ) :=
    Set.range fun g' : cliffGL ℚ =>
      ((g' : Matrix.GeneralLinearGroup (Fin 24) ℚ) : Matrix (Fin 24) (Fin 24) ℚ) with hT
  have hTcl : ∀ N ∈ T, CliffEq N := by
    rintro _ ⟨g', rfl⟩
    exact g'.2.2.1
  have hroot : ∀ (j : Fin 4 ⊕ Fin 4) (c : ℚ),
      (D4Tripled.rootSubgroupPoints j ℚ (Multiplicative.ofAdd c) :
        Matrix.GeneralLinearGroup (Fin 24) ℚ) ∈ cliffGL ℚ := by
    intro j c
    rcases j with i | i
    · refine mem_cliffGL_of (raisingMatrix_isBlockDiag i)
        (cliffEq_one_add_smul_raising i) (c := c) ?_ ?_
      · exact D4Tripled.coe_rootSubgroupPoints_inl i ℚ (Multiplicative.ofAdd c)
      · rw [← Subgroup.coe_inv, ← map_inv]
        exact D4Tripled.coe_rootSubgroupPoints_inl i ℚ (Multiplicative.ofAdd (-c))
    · refine mem_cliffGL_of (loweringMatrix_isBlockDiag i)
        (cliffEq_one_add_smul_lowering i) (c := c) ?_ ?_
      · exact D4Tripled.coe_rootSubgroupPoints_inr i ℚ (Multiplicative.ofAdd c)
      · rw [← Subgroup.coe_inv, ← map_inv]
        exact D4Tripled.coe_rootSubgroupPoints_inr i ℚ (Multiplicative.ofAdd (-c))
  have hM : ∀ P : MvPolynomial (Fin 24 × Fin 24) ℤ,
      (∀ N ∈ T, CFSG.TauCetiBridge.BigCell.evalMat N P = 0) →
        CFSG.TauCetiBridge.BigCell.evalMat (g : Matrix (Fin 24) (Fin 24) A) P = 0 :=
    fun P hP => d4_evalMat_eq_zero_of_root_subgroups (cliffGL ℚ) hroot P
      (fun g' hg' => hP _ ⟨⟨g', hg'⟩, rfl⟩) A g hg
  intro a
  constructor
  · refine sub_eq_zero.1 ?_
    ext r c
    exact natural_eq_zero (fun (B : Type) (_ : CommRing B) (M : Matrix (Fin 24) (Fin 24) B) =>
      (blk 2 M * castM (muMat a) - lcMu (blk 0 M) a * blk 1 M : Matrix (Fin 8) (Fin 8) B) r c)
      (fun B B' _ _ f M => by
        rw [blk_mapMatrix, blk_mapMatrix, blk_mapMatrix, ← mapMatrix_castM f, ← map_mul,
          ← mapMatrix_lcMu, ← map_mul, ← map_sub]
        rfl)
      T (fun N hN => by
        change (blk 2 N * castM (muMat a) - lcMu (blk 0 N) a * blk 1 N :
          Matrix (Fin 8) (Fin 8) ℚ) r c = 0
        rw [((hTcl N hN) a).1, sub_self]
        rfl) _ hM
  · refine sub_eq_zero.1 ?_
    ext r c
    exact natural_eq_zero (fun (B : Type) (_ : CommRing B) (M : Matrix (Fin 24) (Fin 24) B) =>
      (blk 1 M * castM (nuMat a) - lcNu (blk 0 M) a * blk 2 M : Matrix (Fin 8) (Fin 8) B) r c)
      (fun B B' _ _ f M => by
        rw [blk_mapMatrix, blk_mapMatrix, blk_mapMatrix, ← mapMatrix_castM f, ← map_mul,
          ← mapMatrix_lcNu, ← map_mul, ← map_sub]
        rfl)
      T (fun N hN => by
        change (blk 1 N * castM (nuMat a) - lcNu (blk 0 N) a * blk 2 N :
          Matrix (Fin 8) (Fin 8) ℚ) r c = 0
        rw [((hTcl N hN) a).2, sub_self]
        rfl) _ hM

theorem points_le_blockGL (A : Type*) [CommRing A] : D4Tripled.points A ≤ blockGL d4Blk A :=
  fun g hg => mem_blockGL_of (d4_points_isBlockDiag A g hg)
    (d4_points_isBlockDiag A g⁻¹ (inv_mem hg))

theorem det_eq_one_of_mem_points
    (L : Type) [Field L] (g : Matrix.GeneralLinearGroup (Fin 24) L)
    (hg : g ∈ D4Tripled.points L) : (g : Matrix (Fin 24) (Fin 24) L).det = 1 := by
  have h := (d4_points_isZero L g hg).det_eq_one
  rwa [Matrix.det_submatrix_equiv_self] at h

end Rational

section BlockHom

variable {R : Type*} [CommRing R]

@[expose] def blkHom (k : Fin 3) : ↥(blockGL d4Blk R) →* Matrix.GeneralLinearGroup (Fin 8) R where
  toFun g := ⟨blk k ((g : Matrix.GeneralLinearGroup (Fin 24) R) : Matrix (Fin 24) (Fin 24) R),
    blk k (((g : Matrix.GeneralLinearGroup (Fin 24) R)⁻¹ : Matrix.GeneralLinearGroup (Fin 24) R) :
      Matrix (Fin 24) (Fin 24) R),
    by rw [← blk_mul g.2.1, ← Units.val_mul, mul_inv_cancel, Units.val_one, blk_one],
    by rw [← blk_mul g.2.2, ← Units.val_mul, inv_mul_cancel, Units.val_one, blk_one]⟩
  map_one' := Units.ext (blk_one k)
  map_mul' g h := Units.ext (blk_mul g.2.1 _ k)

theorem eq_one_of_blk {M : Matrix (Fin 24) (Fin 24) R} (hM : IsBlockDiag d4Blk R M)
    (h : ∀ k, blk k M = 1) : M = 1 := by
  ext a b
  obtain ⟨⟨k, r⟩, rfl⟩ := blkIdx_bijective.2 a
  obtain ⟨⟨k', c⟩, rfl⟩ := blkIdx_bijective.2 b
  by_cases hk : k = k'
  · subst hk
    have hrc := congrFun (congrFun (h k) r) c
    rw [blk_apply] at hrc
    rw [hrc]
    by_cases hr : r = c
    · subst hr
      rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
    · rw [Matrix.one_apply_ne hr, Matrix.one_apply_ne ((blkIdx_injective k).ne hr)]
  · rw [hM _ _ (by rw [d4Blk_blkIdx, d4Blk_blkIdx]; exact hk), Matrix.one_apply_ne]
    intro he
    exact hk (by simpa [d4Blk_blkIdx] using congrArg d4Blk he)

end BlockHom

section Kernel

theorem eq_one_of_sq_eq_one_of_charTwo {L : Type*} [Field L] [CharP L 2] {x : L}
    (h : x ^ 2 = 1) : x = 1 := by
  have h2' : (2 : L) = 0 := CharP.cast_eq_zero L 2
  have h2 : (x - 1) ^ 2 = 0 := by linear_combination h - (x - 1) * h2' 
  exact sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 h2)

theorem eq_one_of_pow_sixteen_eq_one_of_charTwo {L : Type*} [Field L] [CharP L 2] {x : L}
    (h : x ^ 16 = 1) : x = 1 := by
  have h4 : x ^ 16 = ((x ^ 2) ^ 2) ^ 2 ^ 2 := by ring
  rw [h4] at h
  exact eq_one_of_sq_eq_one_of_charTwo (eq_one_of_sq_eq_one_of_charTwo
    (eq_one_of_sq_eq_one_of_charTwo (eq_one_of_sq_eq_one_of_charTwo (by rw [← h]; ring))))

theorem pushDown_injective (L : Type) [Field L] [CharP L 2] :
    Function.Injective (d4PushDown L).π := by
  rw [injective_iff_map_eq_one]
  intro z hz
  set M := ((z : Matrix.GeneralLinearGroup (Fin 24) L) : Matrix (Fin 24) (Fin 24) L) with hMdef
  have hc := (d4PushDown L).ker_iff z |>.1 hz
  have hdiag : ∀ a b, a ≠ b → M a b = 0 := fun a b hab =>
    CFSG.TauCetiBridge.Even.d4_isDiag_of_commute_two (fun i => (hc i).1) (fun i => (hc i).2) hab
  have hconst : ∀ a b, d4Blk a = d4Blk b → M a a = M b b := fun a b hab =>
    d4_diag_eq_of_commute hdiag (fun i => (hc i).1) (fun i => (hc i).2) hab
  set c : Fin 3 → L := fun k => M (blkIdx k 0) (blkIdx k 0) with hcdef
  have hMa : ∀ a, M a a = c (d4Blk a) := by
    intro a
    obtain ⟨⟨k, r⟩, rfl⟩ := blkIdx_bijective.2 a
    rw [d4Blk_blkIdx]
    exact hconst _ _ (by rw [d4Blk_blkIdx, d4Blk_blkIdx])
  have hblk : ∀ k, blk k M = c k • (1 : Matrix (Fin 8) (Fin 8) L) := by
    intro k
    ext r s
    rw [blk_apply, Matrix.smul_apply, smul_eq_mul]
    by_cases hrs : r = s
    · subst hrs
      rw [hMa, d4Blk_blkIdx, Matrix.one_apply_eq, mul_one]
    · rw [hdiag _ _ ((blkIdx_injective k).ne hrs), Matrix.one_apply_ne hrs, mul_zero]
  have hcl : CliffEq M := cliffEq_of_mem_points L (z : Matrix.GeneralLinearGroup (Fin 24) L) z.2
  have hlc : ∀ (u : L) a, lcMu (u • (1 : Matrix (Fin 8) (Fin 8) L)) a = u • castM (muMat a) ∧
      lcNu (u • (1 : Matrix (Fin 8) (Fin 8) L)) a = u • castM (nuMat a) := by
    intro u a
    rw [lcMu_smul, lcMu_one, lcNu_smul, lcNu_one]
    exact ⟨rfl, rfl⟩
  have h2 : c 2 = c 0 * c 1 := by
    have h := congrArg (fun A : Matrix (Fin 8) (Fin 8) L => A 0 0) ((hcl 3).1)
    simp only [hblk, (hlc _ _).1, smul_mul_assoc, Matrix.one_mul, Matrix.mul_smul,
      Matrix.mul_one, Matrix.smul_apply, smul_eq_mul] at h
    have h1 : (castM (muMat 3) : Matrix (Fin 8) (Fin 8) L) 0 0 = 1 := by
      rw [castM_apply]
      norm_num [muMat]
    rw [h1, mul_one, mul_one] at h
    exact h
  have h1 : c 1 = c 0 * c 2 := by
    have h := congrArg (fun A : Matrix (Fin 8) (Fin 8) L => A 0 0) ((hcl 4).2)
    simp only [hblk, (hlc _ _).2, smul_mul_assoc, Matrix.one_mul, Matrix.mul_smul,
      Matrix.mul_one, Matrix.smul_apply, smul_eq_mul] at h
    have h1 : (castM (nuMat 4) : Matrix (Fin 8) (Fin 8) L) 0 0 = 1 := by
      rw [castM_apply]
      norm_num [nuMat]
    rw [h1, mul_one, mul_one] at h
    exact h
  have hdet := det_eq_one_of_mem_points L (z : Matrix.GeneralLinearGroup (Fin 24) L) z.2
  have hMdiag : M = Matrix.diagonal fun a => c (d4Blk a) := by
    ext a b
    by_cases hab : a = b
    · subst hab
      rw [Matrix.diagonal_apply_eq, hMa]
    · rw [hdiag a b hab, Matrix.diagonal_apply_ne _ hab]
  have hprod : (∏ a : Fin 24, c (d4Blk a)) = c 0 ^ 8 * c 1 ^ 8 * c 2 ^ 8 := by
    rw [show (∏ a : Fin 24, c (d4Blk a)) = ∏ p : Fin 3 × Fin 8, c (d4Blk (blkIdx p.1 p.2)) from
      (Fintype.prod_bijective _ blkIdx_bijective _ _ fun _ => rfl).symm]
    simp only [d4Blk_blkIdx, Fintype.prod_prod_type, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, Fin.prod_univ_three]
  rw [← hMdef, hMdiag, Matrix.det_diagonal, hprod] at hdet
  have hc1 : c 1 ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by norm_num), mul_zero, zero_mul] at hdet
    exact zero_ne_one hdet
  have hc0 : c 0 = 1 := by
    refine eq_one_of_sq_eq_one_of_charTwo ?_
    have : c 1 = c 0 ^ 2 * c 1 := by
      calc c 1 = c 0 * c 2 := h1
        _ = c 0 * (c 0 * c 1) := by rw [h2]
        _ = c 0 ^ 2 * c 1 := by ring
    have h' : (c 0 ^ 2 - 1) * c 1 = 0 := by linear_combination -this
    exact sub_eq_zero.1 ((mul_eq_zero.1 h').resolve_right hc1)
  have hc12 : c 2 = c 1 := by rw [h2, hc0, one_mul]
  have hc1' : c 1 = 1 := by
    refine eq_one_of_pow_sixteen_eq_one_of_charTwo ?_
    rw [hc0, hc12, one_pow, one_mul] at hdet
    rw [← hdet]
    ring
  have hall : ∀ k, c k = 1 := by
    intro k
    fin_cases k
    · exact hc0
    · exact hc1'
    · exact hc12.trans hc1'
  apply Subtype.ext
  apply Units.ext
  change M = 1
  rw [hMdiag]
  ext a b
  simp only [hall, Matrix.diagonal_apply, Matrix.one_apply]

end Kernel

section Steinberg

@[expose] def trialityBlkPerm : Fin 3 → Equiv.Perm (Fin 8) :=
  ![Equiv.swap 3 4, Equiv.swap 3 4, 1]

theorem trialityPerm_blkIdx : ∀ (k : Fin 3) (r : Fin 8),
    DynkinType.d4TripledTrialityPerm (blkIdx k r) = blkIdx (k + 1) (trialityBlkPerm k r) := by
  decide +kernel

theorem permMat_mul_apply {L : Type*} [CommRing L] (π : Equiv.Perm (Fin 24))
    (P M : Matrix (Fin 24) (Fin 24) L) (hP : ∀ i j, P i j = if i = π j then 1 else 0)
    (i j : Fin 24) : (P * M) i j = M (π.symm i) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (π.symm i)]
  · rw [hP, ite_eq_left (π.apply_symm_apply i).symm, one_mul]
  · intro k _ hk
    rw [hP, ite_eq_right (fun h => hk (by rw [h, Equiv.symm_apply_apply])), zero_mul]
  · simp

theorem mul_permMat_apply {L : Type*} [CommRing L] (π : Equiv.Perm (Fin 24))
    (P M : Matrix (Fin 24) (Fin 24) L) (hP : ∀ i j, P i j = if i = π j then 1 else 0)
    (i j : Fin 24) : (M * P) i j = M i (π j) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (π j)]
  · rw [hP, ite_eq_left rfl, mul_one]
  · intro k _ hk
    rw [hP, ite_eq_right hk, mul_zero]
  · simp

variable {q : PrimePower} {hv : (LieTypeIndex.trialityD4 q).Valid}

theorem steinberg_fixed_entry (g : D4Tripled.points (d4Closure q hv))
    (hg : (d4Index q hv).steinberg g = g) (r c : Fin 24) :
    ((g : Matrix.GeneralLinearGroup (Fin 24) (d4Closure q hv)) :
        Matrix (Fin 24) (Fin 24) (d4Closure q hv))
      (DynkinType.d4TripledTrialityPerm r) (DynkinType.d4TripledTrialityPerm c) =
      ((g : Matrix.GeneralLinearGroup (Fin 24) (d4Closure q hv)) :
        Matrix (Fin 24) (Fin 24) (d4Closure q hv)) r c ^ q.card := by
  set π := DynkinType.d4TripledTrialityPerm with hπ
  set P := D4Tripled.trialityMatrix (d4Closure q hv) with hPdef
  have hP : ∀ i j, (P : Matrix (Fin 24) (Fin 24) (d4Closure q hv)) i j =
      if i = π j then 1 else 0 := fun i j => D4Tripled.coe_trialityMatrix_apply _ i j
  have hPinv : ((P⁻¹ : Matrix.GeneralLinearGroup (Fin 24) (d4Closure q hv)) :
      Matrix (Fin 24) (Fin 24) (d4Closure q hv)) = (P : Matrix _ _ _) * (P : Matrix _ _ _) := by
    have h3 : P ^ 3 = 1 := D4Tripled.trialityMatrix_pow_three _
    have : P⁻¹ = P * P := by
      rw [inv_eq_iff_mul_eq_one, ← pow_three, h3]
    rw [this, Units.val_mul]
  have hst := congrArg (fun x : D4Tripled.points (d4Closure q hv) =>
    ((x : Matrix.GeneralLinearGroup (Fin 24) (d4Closure q hv)) :
      Matrix (Fin 24) (Fin 24) (d4Closure q hv)) (π r) (π c)) hg
  rw [← hst, TypeTrialityD4LieIndex.steinberg_def, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, TypeTrialityD4LieIndex.graphAut_def, D4Tripled.coe_trialityPoints,
    Units.val_mul, Units.val_mul, hPinv, ← Matrix.mul_assoc, mul_permMat_apply π _ _ hP,
    mul_permMat_apply π _ _ hP, permMat_mul_apply π _ _ hP,
    TypeTrialityD4LieIndex.coe_frobenius_apply, Equiv.symm_apply_apply,
    DynkinType.d4TripledTrialityPerm_apply_apply_apply]
  exact congrArg (_ ^ ·) (LieTypeIndex.fieldOrder_trialityD4 q)

theorem steinberg_fixed_blk (g : D4Tripled.points (d4Closure q hv))
    (hg : (d4Index q hv).steinberg g = g) (k : Fin 3) (r c : Fin 8) :
    blk (k + 1) ((g : Matrix.GeneralLinearGroup (Fin 24) (d4Closure q hv)) :
        Matrix (Fin 24) (Fin 24) (d4Closure q hv)) (trialityBlkPerm k r) (trialityBlkPerm k c) =
      blk k ((g : Matrix.GeneralLinearGroup (Fin 24) (d4Closure q hv)) :
        Matrix (Fin 24) (Fin 24) (d4Closure q hv)) r c ^ q.card := by
  rw [blk_apply, blk_apply, ← trialityPerm_blkIdx, ← trialityPerm_blkIdx]
  exact steinberg_fixed_entry g hg _ _

end Steinberg

end CFSG.RankThree.PartTwo.Sec21.Item223Rank2Proof
