module

public import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSL

public section

namespace CFSG.StandardType

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix

namespace AutPSL

section Vec

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K]

theorem transvection_mulVec {i j : ι} (hij : i ≠ j) (b : K) (v : ι → K) :
    ((SpecialLinearGroup.transvection hij b : SpecialLinearGroup ι K) : Matrix ι ι K) *ᵥ v =
      v + Pi.single i (b * v j) := by
  rw [SpecialLinearGroup.transvection_coe, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.single_mulVec]
  rfl

theorem transvection_comm {i j k l : ι} (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k) (hli : l ≠ i)
    (a b : K) :
    SpecialLinearGroup.transvection hij a * SpecialLinearGroup.transvection hkl b =
      SpecialLinearGroup.transvection hkl b * SpecialLinearGroup.transvection hij a := by
  refine Subtype.ext ?_
  change (1 + Matrix.single i j a) * (1 + Matrix.single k l b) =
    (1 + Matrix.single k l b) * (1 + Matrix.single i j a)
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one,
    Matrix.single_mul_single_of_ne _ _ _ _ hjk, Matrix.single_mul_single_of_ne _ _ _ _ hli,
    add_zero]
  abel

theorem transvection_congr {i j i' j' : ι} (hij : i ≠ j) (hij' : i' ≠ j') (hi : i = i')
    (hj : j = j') (b : K) :
    SpecialLinearGroup.transvection hij b = SpecialLinearGroup.transvection hij' b := by
  subst hi hj
  rfl

end Vec

section OrdThree

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K] [CharP K 2]

noncomputable abbrev ordThree {i k : ι} (hik : i ≠ k) : SpecialLinearGroup ι K :=
  SpecialLinearGroup.transvection hik 1 * SpecialLinearGroup.transvection hik.symm 1

omit [CharP K 2] in
theorem ordThree_mulVec {i k : ι} (hik : i ≠ k) (v : ι → K) :
    ((ordThree hik : SpecialLinearGroup ι K) : Matrix ι ι K) *ᵥ v =
      v + Pi.single k (v i) + Pi.single i (v k + v i) := by
  change (((SpecialLinearGroup.transvection hik 1 : SpecialLinearGroup ι K) : Matrix ι ι K) *
    ((SpecialLinearGroup.transvection hik.symm 1 : SpecialLinearGroup ι K) : Matrix ι ι K)) *ᵥ v =
      _
  rw [← Matrix.mulVec_mulVec, transvection_mulVec, transvection_mulVec]
  simp only [one_mul, Pi.add_apply, Pi.single_eq_same]

theorem ordThree_pow_three {i k : ι} (hik : i ≠ k) :
    (ordThree hik : SpecialLinearGroup ι K) ^ 3 = 1 := by
  rw [pow_succ, pow_succ, pow_one]
  refine Subtype.ext ?_
  change ((ordThree hik : SpecialLinearGroup ι K) : Matrix ι ι K) *
    (ordThree hik : SpecialLinearGroup ι K) * (ordThree hik : SpecialLinearGroup ι K) = 1
  rw [Matrix.ext_iff_mulVec]
  intro v
  rw [Matrix.one_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ordThree_mulVec,
    ordThree_mulVec, ordThree_mulVec]
  funext l
  have hki := hik.symm
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  by_cases hli : l = i
  · subst hli
    simp [hki]
    linear_combination (6 * v l + 4 * v k) * h2
  · by_cases hlk : l = k
    · subst hlk
      simp [hik, hki]
      linear_combination (2 * v l + 4 * v i) * h2
    · simp [Pi.single_apply, hli, hlk]

omit [CharP K 2] in
theorem ordThree_not_mem_scalars {n : ℕ} {i k : Fin n} (hik : i ≠ k) :
    (ordThree hik : SpecialLinearGroup (Fin n) K) ∉ scalars n K := by
  rintro ⟨c, -, hc⟩
  have h := congrFun (ordThree_mulVec (K := K) hik (Pi.single i 1)) k
  rw [hc, Matrix.scalar_apply, Matrix.mulVec_diagonal] at h
  simp [hik.symm] at h

end OrdThree

section Fixed

variable {n : ℕ} {K : Type*} [Field K] [CharP K 2]

theorem graphAut_fixes {i j : Fin n} (hij : i ≠ j) (h1 : Fin.rev j = i) (h2 : Fin.rev i = j)
    (t : K) : graphAut (proj n K (SpecialLinearGroup.transvection hij t)) =
      proj n K (SpecialLinearGroup.transvection hij t) := by
  rw [graphAut_proj_transvection, transvection_congr _ hij h1 h2]

theorem compl_fixes {c : MulAut (projectiveSL n K)} (hc : c ∈ compl) {i j : Fin n}
    (hij : i ≠ j) (h1 : Fin.rev j = i) (h2 : Fin.rev i = j) :
    c (proj n K (SpecialLinearGroup.transvection hij 1)) =
      proj n K (SpecialLinearGroup.transvection hij 1) := by
  obtain ⟨σ, rfl | rfl⟩ := hc
  · rw [fieldAut_proj_transvection, map_one]
  · rw [MulAut.mul_apply, graphAut_fixes hij h1 h2, fieldAut_proj_transvection, map_one]

end Fixed

section Elements

variable {m : ℕ} {K : Type*} [Field K] [CharP K 2]

theorem last_ne_zero (hm : 1 ≤ m) : (Fin.last m : Fin (m + 1)) ≠ 0 := by
  simp only [ne_eq, Fin.ext_iff, Fin.val_last, Fin.val_zero]
  omega

noncomputable abbrev rootInv (hm : 1 ≤ m) : SpecialLinearGroup (Fin (m + 1)) K :=
  SpecialLinearGroup.transvection (last_ne_zero hm) 1

omit [CharP K 2] in
theorem ggInvSL_eq_rootInv (hm : 1 ≤ m) :
    ggInvSL (m + 1) 1 K = (rootInv hm : SpecialLinearGroup (Fin (m + 1)) K) := by
  refine Subtype.ext ?_
  change ggInvMatrix (m + 1) 1 K = 1 + Matrix.single (Fin.last m) 0 1
  exact ggInvMatrix_one m hm

theorem compl_fixes_rootInv (hm : 1 ≤ m) {c : MulAut (projectiveSL (m + 1) K)} (hc : c ∈ compl) :
    c (proj (m + 1) K (rootInv hm)) = proj (m + 1) K (rootInv hm) :=
  compl_fixes hc _ (Fin.rev_zero m) (Fin.rev_last m)

@[expose] def idxOne (hm : 1 ≤ m) : Fin (m + 1) :=
  ⟨1, by omega⟩

theorem idxOne_ne_rev (hm : 3 ≤ m) : idxOne (by omega) ≠ Fin.rev (idxOne (m := m) (by omega)) := by
  simp only [idxOne, ne_eq, Fin.ext_iff, Fin.val_rev]
  omega

noncomputable abbrev ordThreeElt (hm : 3 ≤ m) : SpecialLinearGroup (Fin (m + 1)) K :=
  ordThree (idxOne_ne_rev hm)

theorem compl_fixes_ordThree (hm : 3 ≤ m) {c : MulAut (projectiveSL (m + 1) K)}
    (hc : c ∈ compl) : c (proj (m + 1) K (ordThreeElt hm)) = proj (m + 1) K (ordThreeElt hm) := by
  rw [ordThreeElt, ordThree, map_mul, map_mul, compl_fixes hc _ (Fin.rev_rev _) rfl,
    compl_fixes hc _ rfl (Fin.rev_rev _)]

omit [CharP K 2] in
theorem ordThree_comm_rootInv (hm : 3 ≤ m) :
    (ordThreeElt hm : SpecialLinearGroup (Fin (m + 1)) K) * rootInv (by omega) =
      rootInv (by omega) * ordThreeElt hm := by
  have h0 : (0 : Fin (m + 1)) ≠ idxOne (by omega) := by
    simp [idxOne, Fin.ext_iff]
  have hl : idxOne (m := m) (by omega) ≠ Fin.last m := by
    simp only [idxOne, ne_eq, Fin.ext_iff, Fin.val_last]
    omega
  have hr0 : Fin.rev (idxOne (m := m) (by omega)) ≠ 0 := by
    simp only [idxOne, ne_eq, Fin.ext_iff, Fin.val_rev, Fin.val_zero]
    omega
  have hrl : Fin.rev (idxOne (m := m) (by omega)) ≠ Fin.last m := by
    simp only [idxOne, ne_eq, Fin.ext_iff, Fin.val_rev, Fin.val_last]
    omega
  rw [ordThreeElt, ordThree, mul_assoc,
    transvection_comm _ (last_ne_zero (by omega)) hl hr0.symm, ← mul_assoc,
    transvection_comm _ (last_ne_zero (by omega)) hrl h0, mul_assoc]

theorem orderOf_proj_ordThree (hm : 3 ≤ m) :
    orderOf (proj (m + 1) K (ordThreeElt hm)) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow, ordThree_pow_three, map_one]
  · rw [Ne, proj_eq_one_iff]
    exact ordThree_not_mem_scalars _

omit [CharP K 2] in
theorem exists_conj_of_mem_inndiag (hm : 2 ≤ m) {e : MulAut (projectiveSL (m + 1) K)}
    (he : e ∈ (inndiag : Subgroup (MulAut (projectiveSL (m + 1) K)))) :
    ∃ k : projectiveSL (m + 1) K, e (proj (m + 1) K (rootInv (by omega))) =
      k * proj (m + 1) K (rootInv (by omega)) * k⁻¹ := by
  obtain ⟨A, rfl⟩ := he
  set i₁ : Fin (m + 1) := ⟨1, by omega⟩ with hi₁
  set d : K := (A : Matrix (Fin (m + 1)) (Fin (m + 1)) K).det with hd
  have hd0 : d ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero A
  set e' : Fin (m + 1) → K := fun l => if l = i₁ then d else 1 with he'
  have hdetD : (Matrix.diagonal e').det = d := by
    rw [Matrix.det_diagonal]
    simp [e']
  set D : GL (Fin (m + 1)) K := Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal e')
    (by rw [hdetD]; exact hd0)
  have hDval : (D : Matrix (Fin (m + 1)) (Fin (m + 1)) K) = Matrix.diagonal e' := rfl
  have hdet1 : Matrix.GeneralLinearGroup.det (A * D⁻¹) = 1 := by
    rw [map_mul, map_inv, mul_inv_eq_one]
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, hDval,
      hdetD]
  obtain ⟨s, hs⟩ : A * D⁻¹ ∈ (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin (m + 1)) K →*
      GL (Fin (m + 1)) K).range := by
    rw [SpecialLinearGroup.range_toGL_eq_ker_det]
    exact hdet1
  have h0 : e' 0 = 1 := by
    simp only [e', hi₁, ite_eq_right_iff]
    intro h
    exact absurd (congrArg Fin.val h) (by simp)
  have hlast : e' (Fin.last m) = 1 := by
    simp only [e', hi₁, ite_eq_right_iff]
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_last] at this
    omega
  have hmat : (1 + Matrix.single (Fin.last m) 0 (1 : K)) * Matrix.diagonal e' =
      Matrix.diagonal e' * (1 + Matrix.single (Fin.last m) 0 (1 : K)) := by
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one]
    congr 1
    ext a b
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.single_apply]
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h
      rw [h0, hlast]
    · simp
  have hcomm : SpecialLinearGroup.toGL (rootInv (K := K) (m := m) (by omega)) * D =
      D * SpecialLinearGroup.toGL (rootInv (K := K) (m := m) (by omega)) :=
    Units.ext hmat
  refine ⟨proj (m + 1) K s, ?_⟩
  have key : CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation (m + 1) K A
      (rootInv (by omega)) = s * rootInv (by omega) * s⁻¹ := by
    apply SpecialLinearGroup.toGL_injective
    rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation, map_mul,
      map_mul, map_inv, hs]
    calc A * SpecialLinearGroup.toGL (rootInv (K := K) (m := m) (by omega)) * A⁻¹ =
        A * D⁻¹ * (D * SpecialLinearGroup.toGL (rootInv (K := K) (m := m) (by omega))) * A⁻¹ := by
          group
      _ = A * D⁻¹ * (SpecialLinearGroup.toGL (rootInv (K := K) (m := m) (by omega)) * D) * A⁻¹ := by
          rw [hcomm]
      _ = _ := by group
  rw [conjAut_proj, key, map_mul, map_mul, map_inv]

theorem goodAut_of_core (hm : 3 ≤ m) {c : MulAut (projectiveSL (m + 1) K)} (hc : c ∈ compl)
    (hO : ∀ Q : Subgroup (projectiveSL (m + 1) K), (∀ q ∈ Q, c q = q) → IsPGroup 2 Q →
      (∀ y : projectiveSL (m + 1) K, c y = y → ∀ q ∈ Q, y * q * y⁻¹ ∈ Q) → Q = ⊥)
    {e : MulAut (projectiveSL (m + 1) K)}
    (he : e ∈ (inndiag : Subgroup (MulAut (projectiveSL (m + 1) K)))) :
    GGGoodAut (proj (m + 1) K (rootInv (by omega))) (e * c * e⁻¹) := by
  refine GGGoodAut.conj ?_ e (exists_conj_of_mem_inndiag (by omega) he)
  refine ⟨hO, 1, ?_, proj (m + 1) K (ordThreeElt hm), compl_fixes_ordThree hm hc, ?_, ?_, ?_⟩
  · simp only [one_mul, inv_one, mul_one]
    exact compl_fixes_rootInv _ hc
  · simp only [one_mul, inv_one, mul_one]
    rw [← map_mul, ordThree_comm_rootInv, map_mul]
  · intro h
    have := orderOf_proj_ordThree (K := K) hm
    rw [h, orderOf_one] at this
    omega
  · rw [orderOf_proj_ordThree]
    decide

end Elements

end AutPSL

end CFSG.StandardType
