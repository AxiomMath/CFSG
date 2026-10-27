module

public import CFSG.LocalAnalysis.StandardType.GGQTwoVACLinCell
public import CFSG.LocalAnalysis.StandardType.GGHalfFiveBlockRank
public import CFSG.LocalAnalysis.StandardType.GGHalfWeylTorusCoord
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymmetricThreeBasic
public import CFSG.GroupTheory.ElementaryAbelianBasis
public import CFSG.LieType.BorelTits.LeviOrder
public import CFSG.LocalAnalysis.StandardType.GGHalfWeylLeviPerf

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly GGHalf Matrix
open CFSG.LieType.Universal.SpecialLinear

namespace GGHalf

namespace TorusRank

noncomputable section

abbrev blockCount (n : ℕ) : ℕ := (n + 1) / 2

abbrev blockExtra (n : ℕ) : ℕ := n + 1 - 2 * blockCount n

@[expose] def blockIdx (n : ℕ) (j : Fin (blockCount n)) : Fin n :=
  ⟨2 * j.val, by have := two_mul_lt_of_lt_half j.isLt; omega⟩

theorem blockIdx_val (n : ℕ) (j : Fin (blockCount n)) : (blockIdx n j).val = 2 * j.val :=
  rfl

theorem two_mul_blockCount_le (n : ℕ) : 2 * blockCount n ≤ n + 1 := by
  simpa [Nat.mul_comm] using Nat.div_mul_le_self (n + 1) 2

@[expose] noncomputable def torusFrameFun (n : ℕ) :
    ((Fin 2 × Fin (blockCount n)) ⊕ Fin (blockExtra n)) → Fin (n + 1) :=
  Sum.elim
    (fun p : Fin 2 × Fin (blockCount n) =>
      (⟨2 * p.2.val + p.1.val, by
        have h := two_mul_lt_of_lt_half p.2.isLt
        have := p.1.isLt
        omega⟩ : Fin (n + 1)))
    (fun i : Fin (blockExtra n) =>
      (⟨2 * blockCount n + i.val, by
        have h2k := two_mul_blockCount_le n
        have hi : i.val < n + 1 - 2 * blockCount n := i.isLt
        omega⟩ : Fin (n + 1)))

theorem torusFrameFun_inl (n : ℕ) (a : Fin 2) (j : Fin (blockCount n)) :
    (torusFrameFun n (Sum.inl (a, j)) : Fin (n + 1)).val = 2 * j.val + a.val := rfl

theorem torusFrameFun_bijective (n : ℕ) : Function.Bijective (torusFrameFun n) := by
  constructor
  · rintro (⟨a₁, j₁⟩ | i₁) (⟨a₂, j₂⟩ | i₂) h
    · simp only [torusFrameFun, Sum.elim_inl, Fin.mk.injEq] at h
      have ha : a₁ = a₂ := by have := a₁.isLt; have := a₂.isLt; omega
      have hj : j₁ = j₂ := by have := j₁.isLt; have := j₂.isLt; omega
      subst ha; subst hj; rfl
    · simp only [torusFrameFun, Sum.elim_inl, Sum.elim_inr, Fin.mk.injEq] at h
      have := j₁.isLt; have := a₁.isLt; have := i₂.isLt; omega
    · simp only [torusFrameFun, Sum.elim_inl, Sum.elim_inr, Fin.mk.injEq] at h
      have := j₂.isLt; have := a₂.isLt; have := i₁.isLt; omega
    · simp only [torusFrameFun, Sum.elim_inr, Fin.mk.injEq] at h
      have hi : i₁ = i₂ := by have := i₁.isLt; have := i₂.isLt; omega
      subst hi; rfl
  · intro x
    have hx := x.isLt
    have h2k := two_mul_blockCount_le n
    by_cases hlt : x.val < 2 * blockCount n
    · refine ⟨Sum.inl ((⟨x.val % 2, by omega⟩ : Fin 2),
        (⟨x.val / 2, by omega⟩ : Fin (blockCount n))), ?_⟩
      apply Fin.ext
      simp only [torusFrameFun, Sum.elim_inl]
      omega
    · refine ⟨Sum.inr ((⟨x.val - 2 * blockCount n, by rw [blockExtra]; omega⟩ :
        Fin (blockExtra n))), ?_⟩
      apply Fin.ext
      simp only [torusFrameFun, Sum.elim_inr]
      omega

@[expose] noncomputable def torusFrame (n : ℕ) :
    Fin (n + 1) ≃ (Fin 2 × Fin (blockCount n)) ⊕ Fin (blockExtra n) :=
  (Equiv.ofBijective (torusFrameFun n) (torusFrameFun_bijective n)).symm

theorem torusFrame_symm_inl (n : ℕ) (a : Fin 2) (j : Fin (blockCount n)) :
    ((torusFrame n).symm (Sum.inl (a, j)) : Fin (n + 1)).val = 2 * j.val + a.val := by
  have h : (torusFrame n).symm (Sum.inl (a, j)) = torusFrameFun n (Sum.inl (a, j)) := by
    simp only [torusFrame, Equiv.symm_symm, Equiv.ofBijective_apply]
  rw [h, torusFrameFun_inl]

theorem blockIdx_castSucc (n : ℕ) (j : Fin (blockCount n)) :
    (blockIdx n j).castSucc = (torusFrame n).symm (Sum.inl ((0 : Fin 2), j)) := by
  apply Fin.ext
  rw [Fin.val_castSucc, blockIdx_val, torusFrame_symm_inl]
  simp

theorem blockIdx_succ (n : ℕ) (j : Fin (blockCount n)) :
    (blockIdx n j).succ = (torusFrame n).symm (Sum.inl ((1 : Fin 2), j)) := by
  apply Fin.ext
  rw [Fin.val_succ, blockIdx_val, torusFrame_symm_inl]
  norm_num

theorem weylRep_eq_transvections (n : ℕ) (k : Fin n) :
    weylRep n F2 k =
      SpecialLinearGroup.transvection
          (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne 1 *
        SpecialLinearGroup.transvection
          ((show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne).symm 1 *
        SpecialLinearGroup.transvection
          (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne 1 := by
  rw [← slPerm_swap_castSucc_succ gf2_two k]
  exact slPerm_swap_eq_transvections gf2_two
    (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne

theorem omegaBlock_eq_transvections (n : ℕ) (k : Fin n) :
    omegaBlock n k =
      SpecialLinearGroup.transvection
          (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne 1 *
        SpecialLinearGroup.transvection
          ((show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne).symm 1 := by
  have hneg : (-1 : F2) = 1 := by
    rw [neg_eq_iff_add_eq_zero, one_add_one_eq_two, gf2_two]
  set x : SpecialLinearGroup (Fin (n + 1)) F2 :=
    SpecialLinearGroup.transvection
      (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne 1
  set y : SpecialLinearGroup (Fin (n + 1)) F2 :=
    SpecialLinearGroup.transvection
      ((show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne).symm 1
  have hxx : x * x = 1 := by
    rw [show x = SpecialLinearGroup.transvection
      (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne 1 from rfl]
    rw [← SpecialLinearGroup.transvection_add, one_add_one_eq_two, gf2_two]
    exact SpecialLinearGroup.transvection_coeff_zero _
  rw [omegaBlock, weylRep_eq_transvections]
  calc (x * y * x) * x = x * y * (x * x) := by group
    _ = x * y := by rw [hxx, mul_one]

theorem weylRep_commute_omegaBlock_of_even (n : ℕ) {p : Fin n} (hp : p.val % 2 = 0)
    {j : Fin (blockCount n)} (h : p ≠ blockIdx n j) :
    Commute (weylRep n F2 (blockIdx n j)) (omegaBlock n p) := by
  have hcc : p.castSucc ≠ (blockIdx n j).castSucc := by
    intro hv
    exact h (Fin.castSucc_injective n hv)
  have hcs : p.castSucc ≠ (blockIdx n j).succ := by
    intro hv
    have := congrArg Fin.val hv
    rw [Fin.val_castSucc, Fin.val_succ, blockIdx_val] at this
    omega
  have hsc : p.succ ≠ (blockIdx n j).castSucc := by
    intro hv
    have := congrArg Fin.val hv
    rw [Fin.val_succ, Fin.val_castSucc, blockIdx_val] at this
    omega
  have hss : p.succ ≠ (blockIdx n j).succ := by
    intro hv
    exact h (Fin.succ_injective n hv)
  have hne : p.castSucc ≠ p.succ := (Fin.castSucc_lt_succ (i := p)).ne
  rw [omegaBlock_eq_transvections]
  exact (weylRep_commute_transvection_of_two gf2_two (blockIdx n j) hne hcc hcs hsc hss 1).mul_right
    (weylRep_commute_transvection_of_two gf2_two (blockIdx n j)
      hne.symm hsc hss hcc hcs 1)

theorem weylRep_commute_weylRep_blocks (n : ℕ) {j j' : Fin (blockCount n)} (h : j ≠ j') :
    Commute (weylRep n F2 (blockIdx n j)) (weylRep n F2 (blockIdx n j')) := by
  have hj : j.val ≠ j'.val := fun hv => h (Fin.ext hv)
  have hdisj : Equiv.Perm.Disjoint
      (Equiv.swap (blockIdx n j).castSucc (blockIdx n j).succ)
      (Equiv.swap (blockIdx n j').castSucc (blockIdx n j').succ) := by
    apply Equiv.Perm.disjoint_swap_swap
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      not_false_eq_true, and_true, not_or]
    repeat' constructor
    all_goals
      intro hv
      have := congrArg Fin.val hv
      simp only [Fin.val_castSucc, Fin.val_succ, blockIdx_val] at this
      omega
  rw [weylRep_eq_slPerm, weylRep_eq_slPerm]
  exact hdisj.commute.map (slPerm gf2_two)

theorem weylRep_conj_omegaBlock_of_ne (n : ℕ) {j j' : Fin (blockCount n)} (h : j' ≠ j) :
    weylRep n F2 (blockIdx n j) * omegaBlock n (blockIdx n j') *
        (weylRep n F2 (blockIdx n j))⁻¹ = omegaBlock n (blockIdx n j') := by
  have hP : (blockIdx n j').val % 2 = 0 := by rw [blockIdx_val]; omega
  have hne : blockIdx n j' ≠ blockIdx n j := by
    intro hv
    apply h
    have hv' := congrArg Fin.val hv
    rw [blockIdx_val, blockIdx_val] at hv'
    exact Fin.ext (by omega)
  have hc := weylRep_commute_omegaBlock_of_even n hP hne
  have hww : weylRep n F2 (blockIdx n j) * weylRep n F2 (blockIdx n j) = 1 :=
    weylRep_mul_self n gf2_two (blockIdx n j)
  have hwinv : (weylRep n F2 (blockIdx n j))⁻¹ = weylRep n F2 (blockIdx n j) :=
    inv_eq_of_mul_eq_one_right hww
  rw [hwinv, hc.eq, mul_assoc, hww, mul_one]

theorem ne_inv_self_of_pow_three {K : Type*} [Group K] {g : K} (h3 : g ^ 3 = 1) (h1 : g ≠ 1) :
    g⁻¹ ≠ g := by
  intro h
  have hsq : g * g = 1 := by
    nth_rewrite 1 [← h]
    exact inv_mul_cancel g
  apply h1
  have h := h3
  rw [show g ^ 3 = g ^ 2 * g by rw [pow_succ], pow_two, hsq, one_mul] at h
  exact h

theorem weylRep_mem_slOn_compl (n : ℕ) {P : Fin n} (hP : P.val % 2 = 0)
    (j : Fin (blockCount n)) (h : blockIdx n j ≠ P) :
    weylRep n F2 (blockIdx n j) ∈
      slOn (n + 1) {i : Fin (n + 1) | i ≠ P.castSucc ∧ i ≠ P.succ} := by
  have hcc : (blockIdx n j).castSucc ≠ P.castSucc := by
    intro hv
    exact h (Fin.castSucc_injective n hv)
  have hcs : (blockIdx n j).castSucc ≠ P.succ := by
    intro hv
    have := congrArg Fin.val hv
    rw [Fin.val_castSucc, Fin.val_succ, blockIdx_val] at this
    omega
  have hsc : (blockIdx n j).succ ≠ P.castSucc := by
    intro hv
    have := congrArg Fin.val hv
    rw [Fin.val_succ, Fin.val_castSucc, blockIdx_val] at this
    omega
  have hss : (blockIdx n j).succ ≠ P.succ := by
    intro hv
    exact h (Fin.succ_injective n hv)
  let S : Set (Fin (n + 1)) := {i | i ≠ P.castSucc ∧ i ≠ P.succ}
  have hx : SpecialLinearGroup.transvection
      (show (blockIdx n j).castSucc < (blockIdx n j).succ from Fin.castSucc_lt_succ).ne 1 ∈
      slOn (n + 1) S :=
    transvection_mem_slOn (S := S)
      (show (blockIdx n j).castSucc < (blockIdx n j).succ from Fin.castSucc_lt_succ).ne 1
      ⟨hcc, hcs⟩ ⟨hsc, hss⟩
  have hy : SpecialLinearGroup.transvection
      ((show (blockIdx n j).castSucc < (blockIdx n j).succ from Fin.castSucc_lt_succ).ne).symm 1 ∈
      slOn (n + 1) S :=
    transvection_mem_slOn (S := S)
      ((show (blockIdx n j).castSucc < (blockIdx n j).succ from Fin.castSucc_lt_succ).ne).symm 1
      ⟨hsc, hss⟩ ⟨hcc, hcs⟩
  rw [weylRep_eq_transvections]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hy) hx

theorem weylRep_mem_normalizer_halfTorus (n : ℕ) (j : Fin (blockCount n)) :
    weylRep n F2 (blockIdx n j) ∈
      Subgroup.normalizer (halfTorus n : Set (SpecialLinearGroup (Fin (n + 1)) F2)) := by
  classical
  set w : SpecialLinearGroup (Fin (n + 1)) F2 := weylRep n F2 (blockIdx n j) with hw
  have hww : w * w = 1 := weylRep_mul_self n gf2_two (blockIdx n j)
  have hw_inv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
  have hgen : ∀ p : Fin n, p.val % 2 = 0 → w * omegaBlock n p * w⁻¹ ∈ halfTorus n := by
    intro p hp
    by_cases h : p = blockIdx n j
    · subst h
      rw [hw_inv, weylRep_mul_omegaBlock_mul_weylRep]
      exact Subgroup.inv_mem _ (Subgroup.subset_closure
        ⟨blockIdx n j, by rw [blockIdx_val]; omega, rfl⟩)
    · have hc := weylRep_commute_omegaBlock_of_even n hp h
      rw [hc.eq]
      rw [mul_assoc, mul_inv_cancel, mul_one]
      exact Subgroup.subset_closure ⟨p, hp, rfl⟩
  have hconj : ∀ t ∈ halfTorus n, w * t * w⁻¹ ∈ halfTorus n := by
    intro t ht
    refine Subgroup.closure_induction (p := fun x _ => w * x * w⁻¹ ∈ halfTorus n)
      ?_ ?_ ?_ ?_ ht
    · rintro x ⟨p, hp, rfl⟩
      exact hgen p hp
    · simp
    · rintro a b _ _ ha hb
      have heq : w * (a * b) * w⁻¹ = (w * a * w⁻¹) * (w * b * w⁻¹) := by group
      rw [heq]
      exact Subgroup.mul_mem _ ha hb
    · rintro a _ ha
      have h : w * a⁻¹ * w⁻¹ = (w * a * w⁻¹)⁻¹ := by group
      rw [h]
      exact Subgroup.inv_mem _ ha
  rw [Subgroup.mem_normalizer_iff]
  intro t
  constructor
  · exact hconj t
  · intro ht
    have h := hconj (w * t * w⁻¹) ht
    have h' : w * (w * t * w⁻¹) * w⁻¹ = t := by
      rw [hw_inv]
      calc w * (w * t * w) * w = (w * w) * t * (w * w) := by group
        _ = t := by rw [hww]; group
    rwa [h'] at h

theorem omegaBlock_coe (n : ℕ) (k : Fin n) :
    ((omegaBlock n k : SpecialLinearGroup (Fin (n + 1)) F2) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) F2) =
      1 + Matrix.single k.castSucc k.succ (1 : F2) +
        Matrix.single k.succ k.castSucc 1 + Matrix.single k.castSucc k.castSucc 1 := by
  have hneg : (-1 : F2) = 1 := by
    rw [neg_eq_iff_add_eq_zero, one_add_one_eq_two, gf2_two]
  set x : SpecialLinearGroup (Fin (n + 1)) F2 :=
    SpecialLinearGroup.transvection
      (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne 1
  set y : SpecialLinearGroup (Fin (n + 1)) F2 :=
    SpecialLinearGroup.transvection
      ((show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne).symm 1
  have hxx : x * x = 1 := by
    rw [show x = SpecialLinearGroup.transvection
      (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne 1 from rfl]
    rw [← SpecialLinearGroup.transvection_add, one_add_one_eq_two, gf2_two]
    exact SpecialLinearGroup.transvection_coeff_zero _
  have hxy : omegaBlock n k = x * y := by
    rw [omegaBlock, weylRep_eq_transvections]
    calc (x * y * x) * x = x * y * (x * x) := by group
      _ = x * y := by rw [hxx, mul_one]
  rw [hxy, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.SpecialLinearGroup.transvection_coe]
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul]
  rw [Matrix.single_mul_single_same, one_mul]
  abel

theorem omegaBlock_frame_inl_inl (n : ℕ) (j : Fin (blockCount n))
    (a b : Fin 2) (j' j'' : Fin (blockCount n)) :
    (((omegaBlock n (blockIdx n j) : SpecialLinearGroup (Fin (n + 1)) F2) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) F2).submatrix (torusFrame n).symm
          (torusFrame n).symm) (Sum.inl (a, j')) (Sum.inl (b, j'')) =
      (Matrix.blockDiagonal (Pi.mulSingle j TorusSupp.omega2)) (a, j') (b, j'') := by
  rw [Matrix.submatrix_apply, omegaBlock_coe]
  fin_cases a <;> fin_cases b
  ·
    simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, Matrix.blockDiagonal_apply,
      Pi.mulSingle_apply]
    split_ifs <;> simp_all [Fin.ext_iff, blockIdx_val, torusFrame_symm_inl,
      TorusSupp.omega2, TorusSupp.f2_one_add_one] <;> omega
  ·
    simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, Matrix.blockDiagonal_apply,
      Pi.mulSingle_apply]
    split_ifs <;> simp_all [Fin.ext_iff, blockIdx_val, torusFrame_symm_inl,
      TorusSupp.omega2] <;> omega
  ·
    simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, Matrix.blockDiagonal_apply,
      Pi.mulSingle_apply]
    split_ifs <;> simp_all [Fin.ext_iff, blockIdx_val, torusFrame_symm_inl,
      TorusSupp.omega2, TorusSupp.f2_one_add_one] <;> omega
  ·
    simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, Matrix.blockDiagonal_apply,
      Pi.mulSingle_apply]
    split_ifs <;> simp_all [Fin.ext_iff, blockIdx_val, torusFrame_symm_inl,
      TorusSupp.omega2, TorusSupp.f2_one_add_one] <;> omega

theorem omegaBlock_frame_inl_inr (n : ℕ) (j : Fin (blockCount n))
    (a : Fin 2) (j' : Fin (blockCount n)) (i : Fin (blockExtra n)) :
    (((omegaBlock n (blockIdx n j) : SpecialLinearGroup (Fin (n + 1)) F2) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) F2).submatrix (torusFrame n).symm
          (torusFrame n).symm) (Sum.inl (a, j')) (Sum.inr i) = 0 := by
  rw [Matrix.submatrix_apply, omegaBlock_coe]
  fin_cases a
  ·
    simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    simp_all [blockIdx_castSucc, blockIdx_succ]
  ·
    simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    simp_all [blockIdx_castSucc, blockIdx_succ]

theorem omegaBlock_frame_inr_inl (n : ℕ) (j : Fin (blockCount n))
    (i : Fin (blockExtra n)) (b : Fin 2) (j'' : Fin (blockCount n)) :
    (((omegaBlock n (blockIdx n j) : SpecialLinearGroup (Fin (n + 1)) F2) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) F2).submatrix (torusFrame n).symm
          (torusFrame n).symm) (Sum.inr i) (Sum.inl (b, j'')) = 0 := by
  rw [Matrix.submatrix_apply, omegaBlock_coe]
  fin_cases b
  ·
    simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    simp_all [blockIdx_castSucc, blockIdx_succ]
  ·
    simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    simp_all [blockIdx_castSucc, blockIdx_succ]

theorem omegaBlock_frame_inr_inr (n : ℕ) (j : Fin (blockCount n))
    (i i' : Fin (blockExtra n)) :
    (((omegaBlock n (blockIdx n j) : SpecialLinearGroup (Fin (n + 1)) F2) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) F2).submatrix (torusFrame n).symm
          (torusFrame n).symm) (Sum.inr i) (Sum.inr i') =
      (1 : Matrix (Fin (blockExtra n)) (Fin (blockExtra n)) F2) i i' := by
  rw [Matrix.submatrix_apply, omegaBlock_coe]
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  by_cases h : i = i'
  · subst h
    simp_all [blockIdx_castSucc, blockIdx_succ]
  · rw [if_neg h]
    simp_all [blockIdx_castSucc, blockIdx_succ]

@[expose] noncomputable def torusBlk (n : ℕ)
    (v : Fin (blockCount n) → Multiplicative (ZMod 3)) :
    Matrix ((Fin 2 × Fin (blockCount n)) ⊕ Fin (blockExtra n))
      ((Fin 2 × Fin (blockCount n)) ⊕ Fin (blockExtra n)) F2 :=
  Matrix.fromBlocks
    (Matrix.blockDiagonal fun j => TorusSupp.omega2 ^ (Multiplicative.toAdd (v j)).val)
    0 0 1

@[simp] theorem torusBlk_inl_inl (n : ℕ)
    (v : Fin (blockCount n) → Multiplicative (ZMod 3)) (a b : Fin 2)
    (j j' : Fin (blockCount n)) :
    torusBlk n v (Sum.inl (a, j)) (Sum.inl (b, j')) =
      if j = j' then (TorusSupp.omega2 ^ (Multiplicative.toAdd (v j)).val) a b else 0 := by
  rw [torusBlk, Matrix.fromBlocks_apply₁₁, Matrix.blockDiagonal_apply]

@[simp] theorem torusBlk_inl_inr (n : ℕ)
    (v : Fin (blockCount n) → Multiplicative (ZMod 3)) (a : Fin 2)
    (j : Fin (blockCount n)) (i : Fin (blockExtra n)) :
    torusBlk n v (Sum.inl (a, j)) (Sum.inr i) = 0 := by
  rw [torusBlk, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]

@[simp] theorem torusBlk_inr_inl (n : ℕ)
    (v : Fin (blockCount n) → Multiplicative (ZMod 3)) (i : Fin (blockExtra n))
    (a : Fin 2) (j : Fin (blockCount n)) :
    torusBlk n v (Sum.inr i) (Sum.inl (a, j)) = 0 := by
  rw [torusBlk, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]

@[simp] theorem torusBlk_inr_inr (n : ℕ)
    (v : Fin (blockCount n) → Multiplicative (ZMod 3)) (i i' : Fin (blockExtra n)) :
    torusBlk n v (Sum.inr i) (Sum.inr i') = if i = i' then 1 else 0 := by
  rw [torusBlk, Matrix.fromBlocks_apply₂₂, Matrix.one_apply]

abbrev FrameIdx (n : ℕ) := (Fin 2 × Fin (blockCount n)) ⊕ Fin (blockExtra n)

@[expose] noncomputable def frameEquiv (n : ℕ) :
    (Fin (n + 1) → F2) ≃ₗ[F2] (FrameIdx n → F2) :=
  LinearEquiv.funCongrLeft (M := F2) F2 (torusFrame n).symm

@[simp] theorem frameEquiv_apply (n : ℕ) (x : Fin (n + 1) → F2) (y : FrameIdx n) :
    frameEquiv n x y = x ((torusFrame n).symm y) := rfl

theorem frameEquiv_eq_comp (n : ℕ) (x : Fin (n + 1) → F2) :
    frameEquiv n x = x ∘ (torusFrame n).symm := by
  funext y
  rw [frameEquiv_apply]
  rfl

theorem frameEquiv_smul (n : ℕ) {t : SpecialLinearGroup (Fin (n + 1)) F2}
    {v : Fin (blockCount n) → Multiplicative (ZMod 3)}
    (hmat : (t : Matrix (Fin (n + 1)) (Fin (n + 1)) F2) =
      (torusBlk n v).submatrix (torusFrame n) (torusFrame n))
    (x : Fin (n + 1) → F2) :
    frameEquiv n (t • x) = torusBlk n v *ᵥ frameEquiv n x := by
  ext y
  have h := congrFun (Matrix.submatrix_mulVec_equiv (torusBlk n v) x
    (torusFrame n) (torusFrame n)) ((torusFrame n).symm y)
  rw [frameEquiv_apply]
  change (((t : Matrix (Fin (n + 1)) (Fin (n + 1)) F2) *ᵥ x)
    ((torusFrame n).symm y)) = _
  rw [hmat]
  simpa [frameEquiv_eq_comp] using h

noncomputable def fixSub (n : ℕ) (t : SpecialLinearGroup (Fin (n + 1)) F2) :
    Submodule F2 (Fin (n + 1) → F2) :=
  LinearMap.ker (Matrix.toLin' ((t : Matrix (Fin (n + 1)) (Fin (n + 1)) F2) - 1))

noncomputable def moveSub (n : ℕ) (t : SpecialLinearGroup (Fin (n + 1)) F2) :
    Submodule F2 (Fin (n + 1) → F2) :=
  LinearMap.range (Matrix.toLin' ((t : Matrix (Fin (n + 1)) (Fin (n + 1)) F2) - 1))

theorem mem_fixSub_iff {n : ℕ} {t : SpecialLinearGroup (Fin (n + 1)) F2}
    {v : Fin (n + 1) → F2} :
    v ∈ fixSub n t ↔ ((t : Matrix (Fin (n + 1)) (Fin (n + 1)) F2) - 1) *ᵥ v = 0 := by
  rw [fixSub, LinearMap.mem_ker, Matrix.toLin'_apply]

theorem mem_moveSub_iff {n : ℕ} {t : SpecialLinearGroup (Fin (n + 1)) F2}
    {v : Fin (n + 1) → F2} :
    v ∈ moveSub n t ↔ ∃ w, ((t : Matrix (Fin (n + 1)) (Fin (n + 1)) F2) - 1) *ᵥ w = v := by
  rw [moveSub, LinearMap.mem_range]
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w, by rwa [Matrix.toLin'_apply] at hw⟩
  · rintro ⟨w, hw⟩
    exact ⟨w, by rwa [Matrix.toLin'_apply]⟩

theorem frameEquiv_sub_one_smul (n : ℕ) {t : SpecialLinearGroup (Fin (n + 1)) F2}
    {v : Fin (blockCount n) → Multiplicative (ZMod 3)}
    (hmat : (t : Matrix (Fin (n + 1)) (Fin (n + 1)) F2) =
      (torusBlk n v).submatrix (torusFrame n) (torusFrame n))
    (x : Fin (n + 1) → F2) :
    frameEquiv n (((t : Matrix (Fin (n + 1)) (Fin (n + 1)) F2) - 1) *ᵥ x) =
      (torusBlk n v - 1) *ᵥ frameEquiv n x := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, map_sub]
  change frameEquiv n (t • x) - frameEquiv n x =
    torusBlk n v *ᵥ frameEquiv n x - frameEquiv n x
  rw [frameEquiv_smul n hmat]

theorem neg_one_f2 : (-1 : F2) = 1 := by
  rw [neg_eq_iff_add_eq_zero, one_add_one_eq_two, gf2_two]

theorem isUnit_omega2 : IsUnit TorusSupp.omega2 := by
  rw [Matrix.isUnit_iff_isUnit_det]
  have hdet : TorusSupp.omega2.det = -1 := by
    rw [Matrix.det_fin_two]
    simp [TorusSupp.omega2]
  rw [hdet, neg_one_f2]
  exact isUnit_one

theorem isUnit_omega2_sub_one : IsUnit (TorusSupp.omega2 - 1) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  have hdet : (TorusSupp.omega2 - 1).det = -1 := by
    rw [Matrix.det_fin_two]
    simp [TorusSupp.omega2, Matrix.sub_apply]
  rw [hdet, neg_one_f2]
  exact isUnit_one

theorem omega2_sq_sub_one_eq : TorusSupp.omega2 ^ 2 - 1 = TorusSupp.omega2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [TorusSupp.omega2, pow_two, Matrix.mul_apply, Matrix.sub_apply,
      Fin.sum_univ_two, gf2_two, neg_one_f2]

theorem isUnit_omega2_sq_sub_one : IsUnit (TorusSupp.omega2 ^ 2 - 1) := by
  rw [omega2_sq_sub_one_eq]
  exact isUnit_omega2

theorem isUnit_omega2_pow_sub_one_of_ne_zero {e : ℕ} (he : e ≠ 0) (hlt : e < 3) :
    IsUnit (TorusSupp.omega2 ^ e - 1) := by
  have hcases : e = 1 ∨ e = 2 := by omega
  rcases hcases with rfl | rfl
  · simpa using isUnit_omega2_sub_one
  · exact isUnit_omega2_sq_sub_one

theorem blockDiagonal_mulVec_apply {o m : Type*} [Fintype o] [Fintype m]
    [DecidableEq o] (f : o → Matrix m m F2) (x : m × o → F2) (a : m) (i : o) :
    (Matrix.blockDiagonal f *ᵥ x) (a, i) = (f i *ᵥ (fun b => x (b, i))) a := by
  change (∑ j : m × o, blockDiagonal f (a, i) j * x j) =
    (f i *ᵥ (fun b => x (b, i))) a
  have hsum : (∑ j : m × o, blockDiagonal f (a, i) j * x j) =
      ∑ j : o, ∑ b : m, blockDiagonal f (a, i) (b, j) * x (b, j) :=
    Fintype.sum_prod_type_right (γ := F2)
      (f := fun p : m × o => blockDiagonal f (a, i) p * x p)
  rw [hsum]
  change (∑ j : o, ∑ b : m, blockDiagonal f (a, i) (b, j) * x (b, j)) =
    ∑ b : m, f i a b * x (b, i)
  rw [Finset.sum_eq_single i]
  · simp [Matrix.blockDiagonal_apply]
  · intro j _ hji
    have hji' : i ≠ j := fun h => hji h.symm
    simp [Matrix.blockDiagonal_apply, hji']
  · intro hi
    simp at hi

theorem torusBlk_mulVec_inl (n : ℕ)
    (v : Fin (blockCount n) → Multiplicative (ZMod 3))
    (y : FrameIdx n → F2) (a : Fin 2) (i : Fin (blockCount n)) :
    (torusBlk n v *ᵥ y) (Sum.inl (a, i)) =
      ((TorusSupp.omega2 ^ (Multiplicative.toAdd (v i)).val) *ᵥ
        (fun b : Fin 2 => y (Sum.inl (b, i)))) a := by
  rw [torusBlk, Matrix.fromBlocks_mulVec]
  simp only [Matrix.zero_mulVec, add_zero]
  change (Matrix.blockDiagonal (fun j => TorusSupp.omega2 ^
    (Multiplicative.toAdd (v j)).val) *ᵥ (fun p : Fin 2 × Fin (blockCount n) =>
      y (Sum.inl p))) (a, i) = _
  rw [blockDiagonal_mulVec_apply]

theorem torusBlk_sub_one_mulVec_inl (n : ℕ)
    (v : Fin (blockCount n) → Multiplicative (ZMod 3))
    (y : FrameIdx n → F2) (a : Fin 2) (i : Fin (blockCount n)) :
    ((torusBlk n v - 1) *ᵥ y) (Sum.inl (a, i)) =
      ((TorusSupp.omega2 ^ (Multiplicative.toAdd (v i)).val - 1) *ᵥ
        (fun b : Fin 2 => y (Sum.inl (b, i)))) a := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, torusBlk_mulVec_inl,
    Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply]

theorem torusBlk_sub_one_mulVec_inr (n : ℕ)
    (v : Fin (blockCount n) → Multiplicative (ZMod 3))
    (y : FrameIdx n → F2) (r : Fin (blockExtra n)) :
    ((torusBlk n v - 1) *ᵥ y) (Sum.inr r) = 0 := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, torusBlk, Matrix.fromBlocks_mulVec]
  simp

noncomputable def blockSuppFrame (n : ℕ) (j : Fin (blockCount n)) :
    Submodule F2 (FrameIdx n → F2) where
  carrier := {x | (∀ i : Fin (blockCount n), i ≠ j → ∀ a : Fin 2,
      x (Sum.inl (a, i)) = 0) ∧ ∀ r : Fin (blockExtra n), x (Sum.inr r) = 0}
  zero_mem' := by
    refine ⟨?_, ?_⟩ <;> intros <;> rfl
  add_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    refine ⟨?_, ?_⟩
    · intro i hi a
      simp [hx1 i hi a, hy1 i hi a]
    · intro r
      simp [hx2 r, hy2 r]
  smul_mem' := by
    rintro c x ⟨hx1, hx2⟩
    refine ⟨?_, ?_⟩
    · intro i hi a
      simp [hx1 i hi a]
    · intro r
      simp [hx2 r]

noncomputable def offBlockFrame (n : ℕ) (j : Fin (blockCount n)) :
    Submodule F2 (FrameIdx n → F2) where
  carrier := {x | ∀ a : Fin 2, x (Sum.inl (a, j)) = 0}
  zero_mem' := by intro a; rfl
  add_mem' := by
    rintro x y hx hy a
    simp [hx a, hy a]
  smul_mem' := by
    rintro c x hx a
    simp [hx a]

theorem disjoint_blockSuppFrame_offBlockFrame (n : ℕ) (j : Fin (blockCount n)) :
    Disjoint (blockSuppFrame n j) (offBlockFrame n j) := by
  rw [Submodule.disjoint_def]
  rintro x ⟨hx1, hx2⟩ hx3
  funext y
  rcases y with ⟨a, i⟩ | r
  · by_cases hi : i = j
    · subst hi; exact hx3 a
    · exact hx1 i hi a
  · exact hx2 r

theorem mem_fixSub_forward_blockSupp (n : ℕ)
    {t : SpecialLinearGroup (Fin (n + 1)) F2}
    {v : Fin (blockCount n) → Multiplicative (ZMod 3)}
    (hmat : (t : Matrix (Fin (n + 1)) (Fin (n + 1)) F2) =
      (torusBlk n v).submatrix (torusFrame n) (torusFrame n))
    {j : Fin (blockCount n)}
    (hother : ∀ i : Fin (blockCount n), i ≠ j → v i ≠ 1)
    (hr : blockExtra n = 0) {x : Fin (n + 1) → F2} (hfix : x ∈ fixSub n t) :
    frameEquiv n x ∈ blockSuppFrame n j := by
  rw [mem_fixSub_iff] at hfix
  have hzero : (torusBlk n v - 1) *ᵥ frameEquiv n x = 0 := by
    rw [← frameEquiv_sub_one_smul n hmat, hfix, map_zero]
  constructor
  · intro i hi a
    have he : (Multiplicative.toAdd (v i)).val ≠ 0 := by
      intro h0
      apply hother i hi
      have hz : Multiplicative.toAdd (v i) = 0 := by
        rw [← ZMod.natCast_zmod_val (Multiplicative.toAdd (v i)), h0]
        norm_num
      exact Multiplicative.ofAdd.injective (by simpa using hz)
    have hunit : IsUnit (TorusSupp.omega2 ^
        (Multiplicative.toAdd (v i)).val - 1) :=
      isUnit_omega2_pow_sub_one_of_ne_zero he (ZMod.val_lt _)
    have hvec : (TorusSupp.omega2 ^ (Multiplicative.toAdd (v i)).val - 1) *ᵥ
        (fun b : Fin 2 => frameEquiv n x (Sum.inl (b, i))) = 0 := by
      funext b
      have := congrFun hzero (Sum.inl (b, i))
      rwa [torusBlk_sub_one_mulVec_inl] at this
    have hz : (fun b : Fin 2 => frameEquiv n x (Sum.inl (b, i))) = 0 :=
      (Matrix.mulVec_injective_of_isUnit hunit) (by simpa using hvec)
    exact congrFun hz a
  · intro r
    exact Fin.elim0 (hr ▸ r)

theorem blockSupp_forward_fixSub (n : ℕ)
    {t : SpecialLinearGroup (Fin (n + 1)) F2}
    {v : Fin (blockCount n) → Multiplicative (ZMod 3)}
    (hmat : (t : Matrix (Fin (n + 1)) (Fin (n + 1)) F2) =
      (torusBlk n v).submatrix (torusFrame n) (torusFrame n))
    {j : Fin (blockCount n)} (hvj : v j = 1)
    (hr : blockExtra n = 0) {x : Fin (n + 1) → F2}
    (hy : frameEquiv n x ∈ blockSuppFrame n j) :
    x ∈ fixSub n t := by
  rw [mem_fixSub_iff]
  have hzero : (torusBlk n v - 1) *ᵥ frameEquiv n x = 0 := by
    funext y
    rcases y with ⟨a, i⟩ | r
    · rw [torusBlk_sub_one_mulVec_inl]
      by_cases hi : i = j
      · rw [hi]
        have hej : (Multiplicative.toAdd (v j)).val = 0 := by rw [hvj]; rfl
        rw [hej, pow_zero, sub_self, Matrix.zero_mulVec]
        rfl
      · have hvec : (fun b : Fin 2 => frameEquiv n x (Sum.inl (b, i))) = 0 := by
          funext b
          exact hy.1 i hi b
        rw [hvec, Matrix.mulVec_zero]
        rfl
    · exact Fin.elim0 (hr ▸ r)
  rw [← frameEquiv_sub_one_smul n hmat] at hzero
  exact (frameEquiv n).injective hzero

theorem mem_fixSub_iff_mem_blockSupp (n : ℕ)
    {t : SpecialLinearGroup (Fin (n + 1)) F2}
    {v : Fin (blockCount n) → Multiplicative (ZMod 3)}
    (hmat : (t : Matrix (Fin (n + 1)) (Fin (n + 1)) F2) =
      (torusBlk n v).submatrix (torusFrame n) (torusFrame n))
    {j : Fin (blockCount n)} (hvj : v j = 1)
    (hother : ∀ i : Fin (blockCount n), i ≠ j → v i ≠ 1)
    (hr : blockExtra n = 0) (x : Fin (n + 1) → F2) :
    x ∈ fixSub n t ↔ frameEquiv n x ∈ blockSuppFrame n j :=
  ⟨mem_fixSub_forward_blockSupp n hmat hother hr,
    blockSupp_forward_fixSub n hmat hvj hr⟩

theorem moveSub_mem_offBlockFrame (n : ℕ)
    {t : SpecialLinearGroup (Fin (n + 1)) F2}
    {v : Fin (blockCount n) → Multiplicative (ZMod 3)}
    (hmat : (t : Matrix (Fin (n + 1)) (Fin (n + 1)) F2) =
      (torusBlk n v).submatrix (torusFrame n) (torusFrame n))
    {j : Fin (blockCount n)} (hvj : v j = 1)
    {x : Fin (n + 1) → F2} (hx : x ∈ moveSub n t) :
    frameEquiv n x ∈ offBlockFrame n j := by
  obtain ⟨w, hw⟩ := mem_moveSub_iff.mp hx
  rw [← hw, frameEquiv_sub_one_smul n hmat]
  intro a
  rw [torusBlk_sub_one_mulVec_inl]
  have hej : (Multiplicative.toAdd (v j)).val = 0 := by rw [hvj]; rfl
  rw [hej, pow_zero, sub_self, Matrix.zero_mulVec, Pi.zero_apply]

theorem isCompl_fixSub_moveSub (n : ℕ)
    {t : SpecialLinearGroup (Fin (n + 1)) F2}
    {v : Fin (blockCount n) → Multiplicative (ZMod 3)}
    (hmat : (t : Matrix (Fin (n + 1)) (Fin (n + 1)) F2) =
      (torusBlk n v).submatrix (torusFrame n) (torusFrame n))
    {j : Fin (blockCount n)} (hvj : v j = 1)
    (hother : ∀ i : Fin (blockCount n), i ≠ j → v i ≠ 1)
    (hr : blockExtra n = 0) :
    IsCompl (fixSub n t) (moveSub n t) := by
  have hfin : Module.finrank F2 (Fin (n + 1) → F2) = n + 1 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have hrank := LinearMap.finrank_range_add_finrank_ker
    (Matrix.toLin' ((t : Matrix (Fin (n + 1)) (Fin (n + 1)) F2) - 1))
  rw [hfin] at hrank
  have hdim : Module.finrank F2 (Fin (n + 1) → F2) ≤
      Module.finrank F2 (fixSub n t) + Module.finrank F2 (moveSub n t) := by
    rw [hfin]
    rw [fixSub, moveSub]
    omega
  rw [Submodule.isCompl_iff_disjoint _ _ hdim, Submodule.disjoint_def]
  intro x hxF hxW
  have hxs : frameEquiv n x ∈ blockSuppFrame n j :=
    (mem_fixSub_iff_mem_blockSupp n hmat hvj hother hr x).mp hxF
  have hxo : frameEquiv n x ∈ offBlockFrame n j :=
    moveSub_mem_offBlockFrame n hmat hvj hxW
  have hdisj := disjoint_blockSuppFrame_offBlockFrame n j
  rw [disjoint_iff_inf_le] at hdisj
  have hzero : frameEquiv n x = 0 := by
    simpa using hdisj ⟨hxs, hxo⟩
  exact (frameEquiv n).injective (by simpa using hzero)

theorem smul_mem_fixSub_of_comm {n : ℕ}
    {t g : SpecialLinearGroup (Fin (n + 1)) F2} (h : Commute g t)
    {v : Fin (n + 1) → F2} (hv : v ∈ fixSub n t) :
    g • v ∈ fixSub n t := by
  rw [mem_fixSub_iff] at hv ⊢
  rw [Matrix.sub_mulVec, Matrix.one_mulVec] at hv ⊢
  rw [sub_eq_zero] at hv ⊢
  change Matrix.mulVec (t : Matrix (Fin (n + 1)) (Fin (n + 1)) F2)
    (Matrix.mulVec (g : Matrix (Fin (n + 1)) (Fin (n + 1)) F2) v) =
      Matrix.mulVec (g : Matrix (Fin (n + 1)) (Fin (n + 1)) F2) v
  have hcomm_mat : (t : Matrix (Fin (n + 1)) (Fin (n + 1)) F2) *
      (g : Matrix (Fin (n + 1)) (Fin (n + 1)) F2) =
      (g : Matrix (Fin (n + 1)) (Fin (n + 1)) F2) *
        (t : Matrix (Fin (n + 1)) (Fin (n + 1)) F2) :=
    congrArg (fun x : SpecialLinearGroup (Fin (n + 1)) F2 =>
      (x : Matrix (Fin (n + 1)) (Fin (n + 1)) F2)) h.eq.symm
  rw [Matrix.mulVec_mulVec, hcomm_mat, ← Matrix.mulVec_mulVec, hv]

noncomputable def fixPermHom (n : ℕ) (t : SpecialLinearGroup (Fin (n + 1)) F2)
    (K : Subgroup (SpecialLinearGroup (Fin (n + 1)) F2))
    (hK : K ≤ Subgroup.centralizer ({t} : Set (SpecialLinearGroup (Fin (n + 1)) F2))) :
    ↥K →* Equiv.Perm ↥(fixSub n t) where
  toFun k :=
    { toFun := fun f => ⟨k.1 • f.1,
        smul_mem_fixSub_of_comm
          (show Commute k.1 t from
            Subgroup.mem_centralizer_singleton_iff.mp (hK k.2)) f.2⟩
      invFun := fun f => ⟨k.1⁻¹ • f.1,
        smul_mem_fixSub_of_comm
          ((show Commute k.1 t from
            Subgroup.mem_centralizer_singleton_iff.mp (hK k.2)).inv_left) f.2⟩
      left_inv := by
        intro f
        ext
        simp
      right_inv := by
        intro f
        ext
        simp }
  map_one' := by
    ext f
    simp
  map_mul' := by
    intro a b
    ext f
    simp [mul_smul]

theorem monoidHom_eq_one_of_perfect_of_solvable {G H : Type*} [Group G] [Group H]
    [Group.IsPerfect G] [Group.IsSolvable H] (f : G →* H) : f = 1 := by
  have : Group.IsPerfect ↥f.range := Group.IsPerfect.ofSurjective
    (MonoidHom.rangeRestrict_surjective f)
  have : Group.IsSolvable ↥f.range := inferInstance
  have hsub : Subsingleton ↥f.range := by
    by_contra h
    have : Nontrivial ↥f.range := not_subsingleton_iff_nontrivial.mp h
    exact (Group.IsPerfect.not_isSolvable ↥f.range) inferInstance
  exact MonoidHom.range_eq_bot_iff.mp (Subgroup.eq_bot_of_subsingleton (H := f.range))

theorem finrank_fixSub_add_supp (n : ℕ) (t : SpecialLinearGroup (Fin (n + 1)) F2) :
    Module.finrank F2 (fixSub n t) + supp t = n + 1 := by
  have hfin : Module.finrank F2 (Fin (n + 1) → F2) = n + 1 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have hrank := LinearMap.finrank_range_add_finrank_ker
    (Matrix.toLin' ((t : Matrix (Fin (n + 1)) (Fin (n + 1)) F2) - 1))
  rw [hfin] at hrank
  have hrange : Module.finrank F2
      (LinearMap.range (Matrix.toLin' ((t : Matrix (Fin (n + 1)) (Fin (n + 1)) F2) - 1))) =
      supp t := by
    rw [supp, Matrix.rank_eq_finrank_range_toLin
      ((t : Matrix (Fin (n + 1)) (Fin (n + 1)) F2) - 1)
      (Pi.basisFun F2 (Fin (n + 1))) (Pi.basisFun F2 (Fin (n + 1)))]
    congr 1
  have hker : Module.finrank F2 (fixSub n t) =
      Module.finrank F2 (LinearMap.ker (Matrix.toLin'
        ((t : Matrix (Fin (n + 1)) (Fin (n + 1)) F2) - 1))) := rfl
  rw [hker]
  omega

theorem natCard_fixSub_of_supp (n : ℕ) {t : SpecialLinearGroup (Fin (n + 1)) F2}
    (h : n + 1 - supp t = 2) : Nat.card (fixSub n t) = 4 := by
  have hcardF2 : Nat.card F2 = 2 := by
    change Nat.card (GaloisField 2 1) = 2
    rw [GaloisField.card 2 1 (by omega)]
    norm_num
  have hfr : Module.finrank F2 (fixSub n t) = 2 := by
    have := finrank_fixSub_add_supp n t
    omega
  have : FiniteDimensional F2 ↥(fixSub n t) :=
    FiniteDimensional.finiteDimensional_submodule (fixSub n t)
  rw [Module.natCard_eq_pow_finrank (K := F2), hfr, hcardF2]
  norm_num

theorem fixPermHom_eq_one (n : ℕ) (t : SpecialLinearGroup (Fin (n + 1)) F2)
    (K : Subgroup (SpecialLinearGroup (Fin (n + 1)) F2))
    (hK : K ≤ Subgroup.centralizer ({t} : Set (SpecialLinearGroup (Fin (n + 1)) F2)))
    [Group.IsPerfect ↥K] (hcard : Nat.card (fixSub n t) ≤ 4) :
    fixPermHom n t K hK = 1 := by
  have : Group.IsSolvable (Equiv.Perm ↥(fixSub n t)) := Equiv.Perm.isSolvable hcard
  exact monoidHom_eq_one_of_perfect_of_solvable _

theorem fixPermHom_apply_eq_self (n : ℕ) (t : SpecialLinearGroup (Fin (n + 1)) F2)
    (K : Subgroup (SpecialLinearGroup (Fin (n + 1)) F2))
    (hK : K ≤ Subgroup.centralizer ({t} : Set (SpecialLinearGroup (Fin (n + 1)) F2)))
    [Group.IsPerfect ↥K] (hcard : Nat.card (fixSub n t) ≤ 4)
    (k : ↥K) (f : ↥(fixSub n t)) :
    (fixPermHom n t K hK k) f = f := by
  have h1 : fixPermHom n t K hK = 1 := fixPermHom_eq_one n t K hK hcard
  have hk := congrArg (fun f : ↥K →* Equiv.Perm ↥(fixSub n t) => f k) h1
  simp only [MonoidHom.one_apply] at hk
  have h := congrArg (fun e : Equiv.Perm ↥(fixSub n t) => e f) hk
  simpa using h

theorem smul_mem_moveSub_of_comm {n : ℕ}
    {t g : SpecialLinearGroup (Fin (n + 1)) F2} (h : Commute g t)
    {w : Fin (n + 1) → F2} (hw : w ∈ moveSub n t) :
    g • w ∈ moveSub n t := by
  obtain ⟨y, hy⟩ := mem_moveSub_iff.mp hw
  rw [mem_moveSub_iff]
  refine ⟨g • y, ?_⟩
  have hcomm_mat : (t : Matrix (Fin (n + 1)) (Fin (n + 1)) F2) *
      (g : Matrix (Fin (n + 1)) (Fin (n + 1)) F2) =
      (g : Matrix (Fin (n + 1)) (Fin (n + 1)) F2) *
        (t : Matrix (Fin (n + 1)) (Fin (n + 1)) F2) :=
    congrArg (fun x : SpecialLinearGroup (Fin (n + 1)) F2 =>
      (x : Matrix (Fin (n + 1)) (Fin (n + 1)) F2)) h.eq.symm
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← hy, Matrix.sub_mulVec, Matrix.one_mulVec]
  change (t : Matrix (Fin (n + 1)) (Fin (n + 1)) F2) *ᵥ
      ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) F2) *ᵥ y) -
      (g : Matrix (Fin (n + 1)) (Fin (n + 1)) F2) *ᵥ y =
    (g : Matrix (Fin (n + 1)) (Fin (n + 1)) F2) *ᵥ
      ((t : Matrix (Fin (n + 1)) (Fin (n + 1)) F2) *ᵥ y - y)
  rw [Matrix.mulVec_sub]
  have hmat' : (t : Matrix (Fin (n + 1)) (Fin (n + 1)) F2) *ᵥ
      ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) F2) *ᵥ y) =
      (g : Matrix (Fin (n + 1)) (Fin (n + 1)) F2) *ᵥ
        ((t : Matrix (Fin (n + 1)) (Fin (n + 1)) F2) *ᵥ y) := by
    rw [Matrix.mulVec_mulVec, hcomm_mat, ← Matrix.mulVec_mulVec]
  rw [hmat']

theorem omegaBlock_submatrix_frame (n : ℕ) (j : Fin (blockCount n)) :
    (((omegaBlock n (blockIdx n j) : SpecialLinearGroup (Fin (n + 1)) F2) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) F2).submatrix (torusFrame n).symm (torusFrame n).symm) =
      Matrix.fromBlocks
        (Matrix.blockDiagonal (Pi.mulSingle j TorusSupp.omega2)) 0 0 1 := by
  ext p q
  rcases p with ⟨a, j'⟩ | i <;> rcases q with ⟨b, j''⟩ | i'
  · rw [omegaBlock_frame_inl_inl]
    rfl
  · rw [omegaBlock_frame_inl_inr, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
  · rw [omegaBlock_frame_inr_inl, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
  · rw [omegaBlock_frame_inr_inr, Matrix.fromBlocks_apply₂₂]

theorem fromBlocks_sub {l m o n : Type*} {α : Type*} [Sub α]
    (A A' : Matrix n l α) (B B' : Matrix n m α) (C C' : Matrix o l α)
    (D D' : Matrix o m α) :
    Matrix.fromBlocks A B C D - Matrix.fromBlocks A' B' C' D' =
      Matrix.fromBlocks (A - A') (B - B') (C - C') (D - D') := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp only [Matrix.sub_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]

theorem blockExtra_le_one (n : ℕ) : blockExtra n ≤ 1 := by
  have hmod : blockExtra n = (n + 1) % 2 := by
    rw [blockExtra, blockCount]
    omega
  rw [hmod]
  have := Nat.mod_lt (n + 1) (by norm_num : 0 < 2)
  omega

theorem card_eq_two_mul_blockCount_add (n : ℕ) :
    n + 1 = 2 * blockCount n + blockExtra n := by
  have h2k := two_mul_blockCount_le n
  rw [blockExtra]
  exact (Nat.add_sub_of_le h2k).symm

theorem exists_trivial_coord_of_fix_two (n : ℕ)
    (v : Fin (blockCount n) → Multiplicative (ZMod 3))
    (hfix : n + 1 - 2 * (Finset.univ.filter fun j => v j ≠ 1).card = 2) :
    ∃ j : Fin (blockCount n), v j = 1 ∧ ∀ i : Fin (blockCount n), i ≠ j → v i ≠ 1 := by
  classical
  let N := (Finset.univ.filter fun j : Fin (blockCount n) => v j ≠ 1).card
  let T := (Finset.univ.filter fun j : Fin (blockCount n) => v j = 1).card
  have htot : N + T = blockCount n := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin (blockCount n)))) (p := fun j => v j = 1)
    have h' : T + N = blockCount n := by
      simpa [N, T, Finset.card_univ, Fintype.card_fin, eq_comm, add_comm] using h
    omega
  have hNle : N ≤ blockCount n := by
    rw [← htot]; omega
  have hfix' : 2 * N + 2 = n + 1 := by omega
  have hcard := card_eq_two_mul_blockCount_add n
  have hr := blockExtra_le_one n
  have hN : N = blockCount n - 1 := by omega
  have hT : T = 1 := by omega
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp (by simpa [T] using hT)
  have hmemj : j ∈ Finset.univ.filter (fun i : Fin (blockCount n) => v i = 1) := by
    rw [hj]
    exact Finset.mem_singleton_self j
  have hvj : v j = 1 := (Finset.mem_filter.mp hmemj).2
  refine ⟨j, hvj, fun i hi => ?_⟩
  intro hvi
  have hmem : i ∈ Finset.univ.filter (fun j : Fin (blockCount n) => v j = 1) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvi⟩
  rw [hj] at hmem
  exact hi (Finset.mem_singleton.mp hmem)

theorem rank_fromBlocks_zero_left {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m m F2) :
    (Matrix.fromBlocks A 0 0 (0 : Matrix n n F2)).rank = A.rank := by
  classical
  let : Fintype F2 := Fintype.ofFinite F2
  let : DecidableEq F2 := Classical.decEq F2
  have h2 : Fintype.card F2 = 2 := by
    simpa using GaloisField.card 2 1 (by omega : (1 : ℕ) ≠ 0)
  have hinj : Function.Injective
      (fun u : m → F2 => (Sum.elim u 0 : m ⊕ n → F2)) :=
    fun u u' h => funext fun i => congrFun h (Sum.inl i)
  have h : Finset.univ.image (Matrix.fromBlocks A 0 0 (0 : Matrix n n F2)).mulVec =
      (Finset.univ.image A.mulVec).map ⟨_, hinj⟩ := by
    ext w
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_map,
      Function.Embedding.coeFn_mk, exists_exists_eq_and, Matrix.fromBlocks_mulVec,
      zero_mulVec, add_zero]
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨v ∘ Sum.inl, by funext x; cases x <;> rfl⟩
    · rintro ⟨v, rfl⟩
      exact ⟨Sum.elim v 0, by funext x; cases x <;> simp⟩
  apply Nat.pow_right_injective (le_refl 2)
  calc 2 ^ (Matrix.fromBlocks A 0 0 (0 : Matrix n n F2)).rank
      = (Finset.univ.image (Matrix.fromBlocks A 0 0 (0 : Matrix n n F2)).mulVec).card := by
        rw [CFSG.LocalAnalysis.ComponentInitial.card_image_mulVec_eq_pow_rank, h2]
    _ = (Finset.univ.image A.mulVec).card := by rw [h, Finset.card_map]
    _ = 2 ^ A.rank := by rw [CFSG.LocalAnalysis.ComponentInitial.card_image_mulVec_eq_pow_rank, h2]

theorem torusBlk_mul (n : ℕ) (v w : Fin (blockCount n) → Multiplicative (ZMod 3)) :
    torusBlk n (v * w) = torusBlk n v * torusBlk n w := by
  rw [torusBlk, torusBlk, torusBlk, Matrix.fromBlocks_multiply]
  rw [Matrix.fromBlocks_inj]
  refine ⟨?_, by simp, by simp, by simp⟩
  simp only [Matrix.mul_zero, add_zero]
  have hfun : (fun j : Fin (blockCount n) => TorusSupp.omega2 ^
        (Multiplicative.toAdd ((v * w) j)).val) =
      (fun j => TorusSupp.omega2 ^ (Multiplicative.toAdd (v j)).val *
        TorusSupp.omega2 ^ (Multiplicative.toAdd (w j)).val) := by
    funext j
    rw [Pi.mul_apply, toAdd_mul, ZMod.val_add, ← pow_add]
    conv_rhs => rw [TorusSupp.omega2_pow_mod
      ((Multiplicative.toAdd (v j)).val + (Multiplicative.toAdd (w j)).val)]
  rw [hfun, Matrix.blockDiagonal_mul]

theorem torusBlk_one (n : ℕ) : torusBlk (n := n) 1 = 1 := by
  have h0 : Multiplicative.toAdd (1 : Multiplicative (ZMod 3)) = 0 := rfl
  rw [torusBlk]
  simp only [Pi.one_apply, h0, ZMod.val_zero, pow_zero]
  change Matrix.fromBlocks (Matrix.blockDiagonal
    (1 : Fin (blockCount n) → Matrix (Fin 2) (Fin 2) F2)) 0 0 1 = 1
  rw [Matrix.blockDiagonal_one, Matrix.fromBlocks_one]

@[expose] noncomputable def torusGen (n : ℕ) (j : Fin (blockCount n)) :
    Fin (blockCount n) → Multiplicative (ZMod 3) :=
  Pi.mulSingle j (Multiplicative.ofAdd (1 : ZMod 3))

theorem torusBlk_gen (n : ℕ) (j : Fin (blockCount n)) :
    torusBlk n (torusGen n j) =
      Matrix.fromBlocks (Matrix.blockDiagonal (Pi.mulSingle j TorusSupp.omega2)) 0 0 1 := by
  rw [torusBlk]
  congr 2
  funext i
  rw [torusGen, Pi.mulSingle_apply, Pi.mulSingle_apply]
  by_cases hi : i = j
  · subst hi
    rw [if_pos rfl, if_pos rfl]
    rw [show (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 3))).val = 1 by
      show (1 : ZMod 3).val = 1
      decide, pow_one]
  · rw [if_neg hi, if_neg hi]
    simp

@[simp] theorem torusGen_self (n : ℕ) (j : Fin (blockCount n)) :
    torusGen n j j = Multiplicative.ofAdd (1 : ZMod 3) := by
  simp [torusGen]

theorem torusGen_of_ne (n : ℕ) {i j : Fin (blockCount n)} (h : i ≠ j) :
    torusGen n j i = 1 := by
  simp [torusGen, h]

theorem torusGen_sub_one_mulVec_eq_zero_of_offBlock (n : ℕ) (j : Fin (blockCount n))
    {y : FrameIdx n → F2} (hy : y ∈ offBlockFrame n j) :
    (torusBlk n (torusGen n j) - 1) *ᵥ y = 0 := by
  funext yidx
  rcases yidx with ⟨a, i⟩ | r
  · rw [torusBlk_sub_one_mulVec_inl]
    by_cases hi : i = j
    · rw [hi]
      have hzero : (fun b : Fin 2 => y (Sum.inl (b, j))) = 0 := by
        funext b
        exact hy b
      rw [hzero, Matrix.mulVec_zero]
      rfl
    · have hgen : torusGen n j i = 1 := torusGen_of_ne n hi
      rw [hgen]
      simp
  · rw [torusBlk_sub_one_mulVec_inr]
    rfl

theorem torusGen_smul_eq_self_of_mem_moveSub (n : ℕ)
    {t u : SpecialLinearGroup (Fin (n + 1)) F2}
    {v : Fin (blockCount n) → Multiplicative (ZMod 3)}
    {j : Fin (blockCount n)}
    (hmatT : (t : Matrix (Fin (n + 1)) (Fin (n + 1)) F2) =
      (torusBlk n v).submatrix (torusFrame n) (torusFrame n))
    (hmatU : (u : Matrix (Fin (n + 1)) (Fin (n + 1)) F2) =
      (torusBlk n (torusGen n j)).submatrix (torusFrame n) (torusFrame n))
    (hvj : v j = 1)
    {x : Fin (n + 1) → F2} (hx : x ∈ moveSub n t) :
    u • x = x := by
  have hxoff : frameEquiv n x ∈ offBlockFrame n j :=
    moveSub_mem_offBlockFrame n hmatT hvj hx
  have hz : (torusBlk n (torusGen n j) - 1) *ᵥ frameEquiv n x = 0 :=
    torusGen_sub_one_mulVec_eq_zero_of_offBlock n j hxoff
  have hz' : frameEquiv n (((u : Matrix (Fin (n + 1)) (Fin (n + 1)) F2) - 1) *ᵥ x) = 0 := by
    rw [frameEquiv_sub_one_smul n hmatU]
    exact hz
  have hvec : ((u : Matrix (Fin (n + 1)) (Fin (n + 1)) F2) - 1) *ᵥ x = 0 :=
    (frameEquiv n).injective (by simpa using hz')
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at hvec
  simpa [Matrix.SpecialLinearGroup.smul_def] using hvec

theorem torusGen_commute_of_fixPerm_vec (n : ℕ)
    {t u : SpecialLinearGroup (Fin (n + 1)) F2}
    {v : Fin (blockCount n) → Multiplicative (ZMod 3)}
    {j : Fin (blockCount n)}
    (hmatT : (t : Matrix (Fin (n + 1)) (Fin (n + 1)) F2) =
      (torusBlk n v).submatrix (torusFrame n) (torusFrame n))
    (hmatU : (u : Matrix (Fin (n + 1)) (Fin (n + 1)) F2) =
      (torusBlk n (torusGen n j)).submatrix (torusFrame n) (torusFrame n))
    (hvj : v j = 1)
    (hother : ∀ i : Fin (blockCount n), i ≠ j → v i ≠ 1)
    (hr : blockExtra n = 0) (huT : Commute u t)
    (K : Subgroup (SpecialLinearGroup (Fin (n + 1)) F2))
    (hK : K ≤ Subgroup.centralizer ({t} : Set (SpecialLinearGroup (Fin (n + 1)) F2)))
    [Group.IsPerfect ↥K] (hcard : Nat.card (fixSub n t) ≤ 4) (k : ↥K) :
    ∀ x : Fin (n + 1) → F2, k.1 • (u • x) = u • (k.1 • x) := by
  have hcompl := isCompl_fixSub_moveSub n hmatT hvj hother hr
  intro x
  obtain ⟨f, w, hfw, -⟩ := Submodule.existsUnique_add_of_isCompl hcompl x
  have hfF : (f : Fin (n + 1) → F2) ∈ fixSub n t := f.2
  have hwW : (w : Fin (n + 1) → F2) ∈ moveSub n t := w.2
  have hkf : k.1 • (f : Fin (n + 1) → F2) = (f : Fin (n + 1) → F2) := by
    exact congrArg Subtype.val (fixPermHom_apply_eq_self n t K hK hcard k f)
  have hkwW : k.1 • (w : Fin (n + 1) → F2) ∈ moveSub n t :=
    smul_mem_moveSub_of_comm (show Commute k.1 t from
      Subgroup.mem_centralizer_singleton_iff.mp (hK k.2)) hwW
  have huw : u • (w : Fin (n + 1) → F2) = (w : Fin (n + 1) → F2) :=
    torusGen_smul_eq_self_of_mem_moveSub n hmatT hmatU hvj hwW
  have hufF : u • (f : Fin (n + 1) → F2) ∈ fixSub n t :=
    smul_mem_fixSub_of_comm huT hfF
  have huw' : u • (k.1 • (w : Fin (n + 1) → F2)) = k.1 • (w : Fin (n + 1) → F2) :=
    torusGen_smul_eq_self_of_mem_moveSub n hmatT hmatU hvj hkwW
  have hkuf : k.1 • (u • (f : Fin (n + 1) → F2)) = u • (f : Fin (n + 1) → F2) := by
    exact congrArg Subtype.val
      (fixPermHom_apply_eq_self n t K hK hcard k ⟨u • (f : Fin (n + 1) → F2), hufF⟩)
  calc
    k.1 • (u • x) = k.1 • (u • ((f : Fin (n + 1) → F2) + (w : Fin (n + 1) → F2))) := by
      rw [hfw]
    _ = k.1 • (u • (f : Fin (n + 1) → F2) + u • (w : Fin (n + 1) → F2)) := by
      rw [smul_add]
    _ = k.1 • (u • (f : Fin (n + 1) → F2) + (w : Fin (n + 1) → F2)) := by
      rw [huw]
    _ = k.1 • (u • (f : Fin (n + 1) → F2)) + k.1 • (w : Fin (n + 1) → F2) := by
      rw [smul_add]
    _ = u • (f : Fin (n + 1) → F2) + k.1 • (w : Fin (n + 1) → F2) := by
      rw [hkuf]
    _ = u • (f : Fin (n + 1) → F2) + u • (k.1 • (w : Fin (n + 1) → F2)) := by
      congr 1
      exact huw'.symm
    _ = u • ((f : Fin (n + 1) → F2) + k.1 • (w : Fin (n + 1) → F2)) := by
      rw [← smul_add]
    _ = u • (k.1 • (f : Fin (n + 1) → F2) + k.1 • (w : Fin (n + 1) → F2)) := by
      congr 1
      rw [hkf]
    _ = u • (k.1 • ((f : Fin (n + 1) → F2) + (w : Fin (n + 1) → F2))) := by
      rw [← smul_add]
    _ = u • (k.1 • x) := by rw [hfw]

theorem torusGen_commute_of_fixPerm (n : ℕ)
    {t u : SpecialLinearGroup (Fin (n + 1)) F2}
    {v : Fin (blockCount n) → Multiplicative (ZMod 3)}
    {j : Fin (blockCount n)}
    (hmatT : (t : Matrix (Fin (n + 1)) (Fin (n + 1)) F2) =
      (torusBlk n v).submatrix (torusFrame n) (torusFrame n))
    (hmatU : (u : Matrix (Fin (n + 1)) (Fin (n + 1)) F2) =
      (torusBlk n (torusGen n j)).submatrix (torusFrame n) (torusFrame n))
    (hvj : v j = 1)
    (hother : ∀ i : Fin (blockCount n), i ≠ j → v i ≠ 1)
    (hr : blockExtra n = 0) (huT : Commute u t)
    (K : Subgroup (SpecialLinearGroup (Fin (n + 1)) F2))
    (hK : K ≤ Subgroup.centralizer ({t} : Set (SpecialLinearGroup (Fin (n + 1)) F2)))
    [Group.IsPerfect ↥K] (hcard : Nat.card (fixSub n t) ≤ 4) (k : ↥K) :
    Commute k.1 u := by
  have hcomm_vec := torusGen_commute_of_fixPerm_vec n hmatT hmatU hvj hother hr huT
    K hK hcard k
  apply Subtype.ext
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  simpa [Matrix.toLin'_apply, Matrix.mulVec_mulVec, Matrix.SpecialLinearGroup.smul_def]
    using hcomm_vec x

theorem closure_range_torusGen (n : ℕ) :
    Subgroup.closure (Set.range (torusGen n)) = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro v
  rw [Subgroup.mem_closure]
  intro K hK
  have hv : v = ∏ j : Fin (blockCount n), (torusGen n j) ^ (Multiplicative.toAdd (v j)).val := by
    funext k
    rw [Finset.prod_apply, Finset.prod_eq_single k]
    · simp only [Pi.pow_apply, torusGen, Pi.mulSingle_apply]
      have hpow : (Multiplicative.ofAdd (1 : ZMod 3)) ^
          (Multiplicative.toAdd (v k)).val = v k := by
        rw [show (Multiplicative.ofAdd (1 : ZMod 3)) ^
            (Multiplicative.toAdd (v k)).val =
            Multiplicative.ofAdd (((Multiplicative.toAdd (v k)).val : ZMod 3)) from by
          induction (Multiplicative.toAdd (v k)).val with
          | zero => simp
          | succ n ih => rw [pow_succ, ih]; simp]
        rw [ZMod.natCast_zmod_val]
        rfl
      exact hpow.symm
    · intro b _ hb
      rw [Pi.pow_apply, torusGen, Pi.mulSingle_apply, if_neg (fun h => hb h.symm)]
      simp
    · intro hk
      exact absurd (Finset.mem_univ k) hk
  rw [hv]
  exact Subgroup.prod_mem K fun j _ => K.pow_mem (hK ⟨j, rfl⟩) _

noncomputable def torusMatHom (n : ℕ) :
    ↥(halfTorus n) →*
      Matrix ((Fin 2 × Fin (blockCount n)) ⊕ Fin (blockExtra n))
        ((Fin 2 × Fin (blockCount n)) ⊕ Fin (blockExtra n)) F2 where
  toFun t := ((t : SpecialLinearGroup (Fin (n + 1)) F2) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) F2).submatrix (torusFrame n).symm (torusFrame n).symm
  map_one' := by
    change ((1 : SpecialLinearGroup (Fin (n + 1)) F2) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) F2).submatrix (torusFrame n).symm
        (torusFrame n).symm = 1
    rw [Matrix.SpecialLinearGroup.coe_one, Matrix.submatrix_one_equiv]
  map_mul' := by
    intro a b
    change (((a * b : ↥(halfTorus n)) : SpecialLinearGroup (Fin (n + 1)) F2) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) F2).submatrix (torusFrame n).symm
        (torusFrame n).symm =
      ((a : SpecialLinearGroup (Fin (n + 1)) F2) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) F2).submatrix (torusFrame n).symm
          (torusFrame n).symm *
      ((b : SpecialLinearGroup (Fin (n + 1)) F2) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) F2).submatrix (torusFrame n).symm
          (torusFrame n).symm
    rw [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.submatrix_mul_equiv]

noncomputable def torusBlkHom (n : ℕ) :
    (Fin (blockCount n) → Multiplicative (ZMod 3)) →*
      Matrix ((Fin 2 × Fin (blockCount n)) ⊕ Fin (blockExtra n))
        ((Fin 2 × Fin (blockCount n)) ⊕ Fin (blockExtra n)) F2 where
  toFun := torusBlk n
  map_one' := torusBlk_one n
  map_mul' := torusBlk_mul n

theorem torusMatHom_comp_torusBlkHom (n : ℕ)
    {Φ : (Fin (blockCount n) → Multiplicative (ZMod 3)) ≃* ↥(halfTorus n)}
    (hΦ : ∀ j : Fin (blockCount n),
      ((Φ (torusGen n j) : ↥(halfTorus n)) : SpecialLinearGroup (Fin (n + 1)) F2) =
        omegaBlock n (blockIdx n j)) :
    (torusMatHom n).comp Φ.toMonoidHom = torusBlkHom n := by
  refine MonoidHom.eq_of_eqOn_dense (s := Set.range (torusGen n))
    (closure_range_torusGen n) ?_
  rintro _ ⟨j, rfl⟩
  change (((Φ (torusGen n j) : ↥(halfTorus n)) :
    SpecialLinearGroup (Fin (n + 1)) F2) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) F2).submatrix (torusFrame n).symm
      (torusFrame n).symm = torusBlk n (torusGen n j)
  rw [hΦ j, omegaBlock_submatrix_frame, torusBlk_gen]

theorem torusMat_eq_blk (n : ℕ)
    {Φ : (Fin (blockCount n) → Multiplicative (ZMod 3)) ≃* ↥(halfTorus n)}
    (hΦ : ∀ j : Fin (blockCount n),
      ((Φ (torusGen n j) : ↥(halfTorus n)) : SpecialLinearGroup (Fin (n + 1)) F2) =
        omegaBlock n (blockIdx n j))
    (v : Fin (blockCount n) → Multiplicative (ZMod 3)) :
    (((Φ v : ↥(halfTorus n)) : SpecialLinearGroup (Fin (n + 1)) F2) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) F2) =
      (torusBlk n v).submatrix (torusFrame n) (torusFrame n) := by
  have h := DFunLike.congr_fun (torusMatHom_comp_torusBlkHom n hΦ) v
  change (((Φ v : ↥(halfTorus n)) : SpecialLinearGroup (Fin (n + 1)) F2) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) F2).submatrix (torusFrame n).symm
      (torusFrame n).symm = torusBlk n v at h
  rw [← h, Matrix.submatrix_submatrix]
  simp

theorem supp_torusCoord (n : ℕ)
    {Φ : (Fin (blockCount n) → Multiplicative (ZMod 3)) ≃* ↥(halfTorus n)}
    (hΦ : ∀ j : Fin (blockCount n),
      ((Φ (torusGen n j) : ↥(halfTorus n)) : SpecialLinearGroup (Fin (n + 1)) F2) =
        omegaBlock n (blockIdx n j))
    (v : Fin (blockCount n) → Multiplicative (ZMod 3)) :
    supp ((Φ v : ↥(halfTorus n)) : SpecialLinearGroup (Fin (n + 1)) F2) =
      2 * (Finset.univ.filter fun j : Fin (blockCount n) => v j ≠ 1).card := by
  classical
  have hmat := torusMat_eq_blk n hΦ v
  unfold supp
  rw [hmat]
  rw [← Matrix.rank_submatrix (A := (torusBlk n v).submatrix (torusFrame n)
    (torusFrame n) - 1) (torusFrame n).symm (torusFrame n).symm]
  have hsub : ((torusBlk n v).submatrix (torusFrame n) (torusFrame n) - 1).submatrix
      (torusFrame n).symm (torusFrame n).symm = torusBlk n v - 1 := by
    ext p q
    simp only [Matrix.submatrix_apply, Matrix.sub_apply]
    simp [Matrix.one_apply, Equiv.apply_symm_apply, (torusFrame n).symm.injective.eq_iff]
  rw [hsub]
  have hblk : torusBlk n v - 1 = Matrix.fromBlocks
      (Matrix.blockDiagonal (fun j => TorusSupp.omega2 ^
        (Multiplicative.toAdd (v j)).val - 1)) 0 0 0 := by
    rw [torusBlk, ← Matrix.fromBlocks_one, fromBlocks_sub]
    simp only [sub_self]
    congr 1
    rw [← Matrix.blockDiagonal_one, ← Matrix.blockDiagonal_sub]
    rfl
  rw [hblk, rank_fromBlocks_zero_left, TorusSupp.rank_blockDiagonal_fin2]
  · have hfilter : (Finset.univ.filter fun j : Fin (blockCount n) =>
        TorusSupp.omega2 ^ (Multiplicative.toAdd (v j)).val - 1 ≠ 0) =
        (Finset.univ.filter fun j : Fin (blockCount n) => v j ≠ 1) := by
      apply Finset.filter_congr
      intro j _
      exact TorusSupp.omega2_pow_sub_one_ne_zero_iff (v j)
    rw [hfilter]
  · intro j
    exact TorusSupp.omega2_pow_sub_one_zero_or_isUnit _

theorem zmod3_sq_eq_one (x : Multiplicative (ZMod 3)) : x * x = 1 ↔ x = 1 := by
  revert x
  decide

theorem omegaBlock_ne_of_zpow_eq_one (n : ℕ)
    {Φ : (Fin (blockCount n) → Multiplicative (ZMod 3)) ≃* ↥(halfTorus n)}
    (hΦ : ∀ j : Fin (blockCount n),
      ((Φ (torusGen n j) : ↥(halfTorus n)) : SpecialLinearGroup (Fin (n + 1)) F2) =
        omegaBlock n (blockIdx n j))
    {v : Fin (blockCount n) → Multiplicative (ZMod 3)} {j i : Fin (blockCount n)}
    (hij : i ≠ j) (hother : ∀ k : Fin (blockCount n), k ≠ j → v k ≠ 1)
    (hs : ((Φ v : ↥(halfTorus n)) : SpecialLinearGroup (Fin (n + 1)) F2) =
      omegaBlock n (blockIdx n j)) : False := by
  have htgen : ∀ k : Fin (blockCount n), (torusGen n j) k = if k = j then
      Multiplicative.ofAdd (1 : ZMod 3) else 1 := fun k => by
    simp [torusGen, Pi.mulSingle_apply]
  have hv : v = torusGen n j := by
    apply Φ.injective
    apply Subtype.ext
    rw [hs]
    exact (hΦ j).symm
  have hi := congrFun hv i
  rw [htgen i, if_neg hij] at hi
  exact hother i hij hi

theorem omegaBlock_ne_of_zpow_sq (n : ℕ)
    {Φ : (Fin (blockCount n) → Multiplicative (ZMod 3)) ≃* ↥(halfTorus n)}
    (hΦ : ∀ j : Fin (blockCount n),
      ((Φ (torusGen n j) : ↥(halfTorus n)) : SpecialLinearGroup (Fin (n + 1)) F2) =
        omegaBlock n (blockIdx n j))
    {v : Fin (blockCount n) → Multiplicative (ZMod 3)} {j i : Fin (blockCount n)}
    (hij : i ≠ j) (hother : ∀ k : Fin (blockCount n), k ≠ j → v k ≠ 1)
    (hs2 : ((Φ v : ↥(halfTorus n)) : SpecialLinearGroup (Fin (n + 1)) F2) ^ 2 =
      omegaBlock n (blockIdx n j)) : False := by
  have hEq : v ^ (2 : ℤ) = torusGen n j := by
    apply Φ.injective
    apply Subtype.ext
    rw [map_zpow]
    simpa [hΦ j] using hs2
  have hi := congrFun hEq i
  have hsq : v i * v i = 1 := by
    simpa [pow_two, torusGen, Pi.mulSingle_apply, Pi.pow_apply, hij] using hi
  exact hother i hij ((zmod3_sq_eq_one (v i)).mp hsq)

theorem omegaBlock_not_mem_zpowers_of_trivial_coord (n : ℕ)
    {Φ : (Fin (blockCount n) → Multiplicative (ZMod 3)) ≃* ↥(halfTorus n)}
    (hΦ : ∀ j : Fin (blockCount n),
      ((Φ (torusGen n j) : ↥(halfTorus n)) : SpecialLinearGroup (Fin (n + 1)) F2) =
        omegaBlock n (blockIdx n j))
    {v : Fin (blockCount n) → Multiplicative (ZMod 3)} {j i : Fin (blockCount n)}
    (hij : i ≠ j) (hother : ∀ k : Fin (blockCount n), k ≠ j → v k ≠ 1) :
    omegaBlock n (blockIdx n j) ∉ Subgroup.zpowers
      ((Φ v : ↥(halfTorus n)) : SpecialLinearGroup (Fin (n + 1)) F2) := by
  intro hmem
  obtain ⟨s, hs⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have ht3 : ((Φ v : ↥(halfTorus n)) : SpecialLinearGroup (Fin (n + 1)) F2) ^ 3 = 1 :=
    halfTorus_pow_three (Φ v).2
  have hs' := hs
  rw [zpow_eq_zpow_emod' s (n := 3) ht3] at hs'
  change ((Φ v : ↥(halfTorus n)) : SpecialLinearGroup (Fin (n + 1)) F2) ^
    (s % (3 : ℤ)) = omegaBlock n (blockIdx n j) at hs'
  have hlt := Int.emod_lt_of_pos s (by norm_num : (0 : ℤ) < 3)
  have hnonneg := Int.emod_nonneg s (by norm_num : (3 : ℤ) ≠ 0)
  have hcases : s % (3 : ℤ) = 0 ∨ s % (3 : ℤ) = 1 ∨ s % (3 : ℤ) = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · rw [h0, zpow_zero] at hs'
    exact omegaBlock_ne_one n (blockIdx n j) hs'.symm
  · have hs1 : ((Φ v : ↥(halfTorus n)) : SpecialLinearGroup (Fin (n + 1)) F2) =
        omegaBlock n (blockIdx n j) := by
      rw [h1, zpow_one] at hs'
      exact hs'
    exact omegaBlock_ne_of_zpow_eq_one n hΦ hij hother hs1
  · have hs2 : ((Φ v : ↥(halfTorus n)) : SpecialLinearGroup (Fin (n + 1)) F2) ^ 2 =
        omegaBlock n (blockIdx n j) := by
      rw [h2] at hs'
      simpa using hs'
    exact omegaBlock_ne_of_zpow_sq n hΦ hij hother hs2

theorem supp_omegaBlock_block (n : ℕ) (j : Fin (blockCount n)) :
    supp (omegaBlock n (blockIdx n j)) = 2 := by
  classical
  obtain ⟨Φ, hΦ⟩ := exists_torusCoord n
  have hΦ' : ∀ i : Fin (blockCount n),
      ((Φ (torusGen n i) : ↥(halfTorus n)) : SpecialLinearGroup (Fin (n + 1)) F2) =
        omegaBlock n (blockIdx n i) := by
    intro i
    simpa [torusGen, blockIdx] using hΦ i
  have h := supp_torusCoord n hΦ' (torusGen n j)
  have hfilter : (Finset.univ.filter fun i : Fin (blockCount n) => torusGen n j i ≠ 1) = {j} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hi
      by_contra hij
      apply hi
      rw [torusGen, Pi.mulSingle_eq_of_ne hij]
    · intro hij
      subst hij
      simp [torusGen]
  rw [← hΦ' j, h, hfilter]
  simp

theorem exists_single_nontrivial_coord (n : ℕ)
    (v : Fin (blockCount n) → Multiplicative (ZMod 3))
    (hcard : (Finset.univ.filter fun j : Fin (blockCount n) => v j ≠ 1).card = 1) :
    ∃ j : Fin (blockCount n), v j ≠ 1 ∧ ∀ i : Fin (blockCount n), i ≠ j → v i = 1 := by
  classical
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hcard
  have hvj : v j ≠ 1 := by
    have := Finset.mem_filter.mp (hj ▸ Finset.mem_singleton_self j)
    exact this.2
  have hv_other : ∀ i : Fin (blockCount n), i ≠ j → v i = 1 := by
    intro i hi
    by_contra hne
    have hmem : i ∈ Finset.univ.filter (fun j : Fin (blockCount n) => v j ≠ 1) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
    rw [hj] at hmem
    exact hi (Finset.mem_singleton.mp hmem)
  exact ⟨j, hvj, hv_other⟩

theorem omegaBlock_eq_or_inv_of_mulSingle (n : ℕ)
    {Φ : (Fin (blockCount n) → Multiplicative (ZMod 3)) ≃* ↥(halfTorus n)}
    (hΦ : ∀ j : Fin (blockCount n),
      ((Φ (torusGen n j) : ↥(halfTorus n)) : SpecialLinearGroup (Fin (n + 1)) F2) =
        omegaBlock n (blockIdx n j))
    {j : Fin (blockCount n)} {c : Multiplicative (ZMod 3)} (hc : c ≠ 1)
    {t : SpecialLinearGroup (Fin (n + 1)) F2}
    (ht : t = ((Φ (Pi.mulSingle j c) : ↥(halfTorus n)) :
      SpecialLinearGroup (Fin (n + 1)) F2)) :
    t = omegaBlock n (blockIdx n j) ∨ t = (omegaBlock n (blockIdx n j))⁻¹ := by
  set z := Multiplicative.toAdd c with hzdef
  have hz : z = 0 ∨ z = 1 ∨ z = 2 := by
    have hlt : z.val < 3 := ZMod.val_lt z
    have hcases : z.val = 0 ∨ z.val = 1 ∨ z.val = 2 := by omega
    rcases hcases with h | h | h
    · left; rw [← ZMod.natCast_zmod_val z, h]; norm_num
    · right; left; rw [← ZMod.natCast_zmod_val z, h]; norm_num
    · right; right; rw [← ZMod.natCast_zmod_val z, h]; norm_num
  have hvz : Multiplicative.ofAdd z = c := rfl
  rcases hz with hz | hz | hz
  · exfalso
    apply hc
    rw [← hvz, hz]
    rfl
  · refine Or.inl ?_
    rw [ht]
    have hv : Pi.mulSingle j c = torusGen n j := by
      rw [torusGen]
      congr 2
    rw [hv]
    exact hΦ j
  · refine Or.inr ?_
    rw [ht]
    have hv : Pi.mulSingle j c = torusGen n j ^ 2 := by
      rw [torusGen, ← Pi.mulSingle_pow]
      congr 2
    rw [hv, map_pow, Subgroup.coe_pow, hΦ j]
    have h3 : omegaBlock n (blockIdx n j) ^ 3 = 1 := omegaBlock_pow_three n (blockIdx n j)
    exact eq_inv_of_mul_eq_one_left (by
      rw [← pow_succ, show 2 + 1 = 3 by norm_num, h3])

theorem exists_omegaBlock_of_supp_two (n : ℕ)
    {Φ : (Fin (blockCount n) → Multiplicative (ZMod 3)) ≃* ↥(halfTorus n)}
    (hΦ : ∀ j : Fin (blockCount n),
      ((Φ (torusGen n j) : ↥(halfTorus n)) : SpecialLinearGroup (Fin (n + 1)) F2) =
        omegaBlock n (blockIdx n j))
    {t : SpecialLinearGroup (Fin (n + 1)) F2} (ht : t ∈ halfTorus n) (h2 : supp t = 2) :
    ∃ j : Fin (blockCount n),
      t = omegaBlock n (blockIdx n j) ∨ t = (omegaBlock n (blockIdx n j))⁻¹ := by
  classical
  let v := Φ.symm ⟨t, ht⟩
  have htv : ((Φ v : ↥(halfTorus n)) : SpecialLinearGroup (Fin (n + 1)) F2) = t := by
    change ((Φ (Φ.symm ⟨t, ht⟩) : ↥(halfTorus n)) : SpecialLinearGroup (Fin (n + 1)) F2) = t
    rw [MulEquiv.apply_symm_apply]
  have hsupp := supp_torusCoord n hΦ v
  rw [htv, h2] at hsupp
  have hcard : (Finset.univ.filter fun j : Fin (blockCount n) => v j ≠ 1).card = 1 :=
    Nat.mul_left_cancel (by norm_num : 0 < 2) hsupp.symm
  obtain ⟨j, hvj, hv_other⟩ := exists_single_nontrivial_coord n v hcard
  have hv_eq : v = Pi.mulSingle j (v j) := by
    funext i
    by_cases hi : i = j
    · subst hi; rw [Pi.mulSingle_eq_same]
    · rw [Pi.mulSingle_eq_of_ne hi, hv_other i hi]
  have htv' : t = ((Φ (Pi.mulSingle j (v j)) : ↥(halfTorus n)) :
      SpecialLinearGroup (Fin (n + 1)) F2) := by
    rw [← htv, hv_eq]
    simp
  exact ⟨j, omegaBlock_eq_or_inv_of_mulSingle n hΦ hvj htv'⟩

end
end TorusRank
end GGHalf
variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J : Subgroup G}

open GGHalf.TorusRank

omit [Finite G] in
theorem weylAut_fix_of_ne (n : ℕ)
    {ψ : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2 →* G}
    (j : Fin (blockCount n)) {j' : Fin (blockCount n)} (hj' : j' ≠ j)
    {Bs : Subgroup G} {φ : MulAut ↥Bs}
    (hgen : ∀ b : ↥Bs, ((φ b : ↥Bs) : G) =
      ψ (weylRep n GGHalf.F2 (blockIdx n j)) * (b : G) *
        (ψ (weylRep n GGHalf.F2 (blockIdx n j)))⁻¹)
    {b : ↥Bs} (hb : (b : G) = ψ (omegaBlock n (blockIdx n j'))) :
    ((φ b : ↥Bs) : G) = ψ (omegaBlock n (blockIdx n j')) := by
  rw [hgen b, hb, ← map_mul, ← map_inv, ← map_mul]
  congr 1
  exact weylRep_conj_omegaBlock_of_ne n hj'

theorem ggQ2Lin_weylAut_data_aut {n : ℕ}
    {ψ : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2 →* G}
    (hF : GGHalfTorusFrame Bs L (GGHalf.halfTorus n) ψ)
    {P : Fin n} {j : Fin (blockCount n)}
    (hS : weylRep n GGHalf.F2 (blockIdx n j) ∈
      slOn (n + 1) {i : Fin (n + 1) | i ≠ P.castSucc ∧ i ≠ P.succ})
    (hJeq : J = (slOn (n + 1) {i : Fin (n + 1) | i ≠ P.castSucc ∧ i ≠ P.succ}).map ψ)
    (hN : weylRep n GGHalf.F2 (blockIdx n j) ∈
      Subgroup.normalizer
        (GGHalf.halfTorus n : Set (Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2))) :
    ∃ φ : MulAut ↥Bs, φ ∈ ggAutomizer J Bs ∧ φ ≠ 1 ∧ φ * φ = 1 ∧
      (∀ b : ↥Bs, ((φ b : ↥Bs) : G) =
        ψ (weylRep n GGHalf.F2 (blockIdx n j)) * (b : G) *
          (ψ (weylRep n GGHalf.F2 (blockIdx n j)))⁻¹) := by
  let w : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2 :=
    weylRep n GGHalf.F2 (blockIdx n j)
  have hwJ : ψ w ∈ J := by
    rw [hJeq]
    exact Subgroup.mem_map.mpr ⟨w, hS, rfl⟩
  have hwN : ψ w ∈ Subgroup.normalizer (Bs : Set G) := hF.mem_normalizer hN
  let φ : MulAut ↥Bs := ggConjAut Bs hwN
  have hww : w * w = 1 := weylRep_mul_self n gf2_two (blockIdx n j)
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
  have hbω_mem : ψ (omegaBlock n (blockIdx n j)) ∈ Bs :=
    hF.torus_le (Subgroup.mem_map.mpr
      ⟨omegaBlock n (blockIdx n j), Subgroup.subset_closure
        ⟨blockIdx n j, by rw [blockIdx_val]; omega, rfl⟩, rfl⟩)
  let bω : ↥Bs := ⟨ψ (omegaBlock n (blockIdx n j)), hbω_mem⟩
  have hact : ((φ bω : ↥Bs) : G) = ψ ((omegaBlock n (blockIdx n j))⁻¹) := by
    change (((ggConjAut Bs hwN) bω : ↥Bs) : G) = _
    rw [ggConjAut_apply]
    rw [← map_mul, ← map_inv, ← map_mul]
    congr 1
    rw [hwinv, weylRep_mul_omegaBlock_mul_weylRep]
  have hφne : φ ≠ 1 := by
    intro hφ
    have hb : ((φ bω : ↥Bs) : G) = (bω : G) := by rw [hφ]; rfl
    have heq : ψ ((omegaBlock n (blockIdx n j))⁻¹) = ψ (omegaBlock n (blockIdx n j)) := by
      rw [← hact, hb]
    exact ne_inv_self_of_pow_three (omegaBlock_pow_three n (blockIdx n j))
      (omegaBlock_ne_one n (blockIdx n j)) (hF.inj heq)
  have hφsq : φ * φ = 1 := by
    rw [← pow_two]
    ext b
    change (((ggConjAut Bs hwN ^ 2) b : ↥Bs) : G) =
      (((1 : MulAut ↥Bs) b : ↥Bs) : G)
    rw [ggConjAut_pow_apply]
    have hwwG : ψ w * ψ w = 1 := by rw [← map_mul, hww, map_one]
    rw [pow_two, hwwG]
    simp
  have hgen : ∀ b : ↥Bs, ((φ b : ↥Bs) : G) =
      ψ w * (b : G) * (ψ w)⁻¹ := by
    intro b
    change (((ggConjAut Bs hwN) b : ↥Bs) : G) = _
    rw [ggConjAut_apply]
  exact ⟨φ, ggConjAut_mem_ggAutomizer hwJ hwN, hφne, hφsq, by simpa [w] using hgen⟩
omit [Finite G] in
theorem ggQ2Lin_weylAut_data_inv {n : ℕ}
    {ψ : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2 →* G}
    {Bs : Subgroup G} {φ : MulAut ↥Bs} {j : Fin (blockCount n)}
    (hgen : ∀ b : ↥Bs, ((φ b : ↥Bs) : G) =
      ψ (weylRep n GGHalf.F2 (blockIdx n j)) * (b : G) *
        (ψ (weylRep n GGHalf.F2 (blockIdx n j)))⁻¹)
    (bω : ↥Bs) (hbω : (bω : G) = ψ (omegaBlock n (blockIdx n j))) :
    ((φ bω : ↥Bs) : G) = ψ ((omegaBlock n (blockIdx n j))⁻¹) := by
  rw [hgen bω, hbω, ← map_mul, ← map_inv, ← map_mul]
  congr 1
  rw [inv_eq_of_mul_eq_one_right (weylRep_mul_self n gf2_two (blockIdx n j)),
    weylRep_mul_omegaBlock_mul_weylRep]

theorem ggQ2Lin_weylAut_data {n : ℕ}
    {ψ : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2 →* G}
    (hF : GGHalfTorusFrame Bs L (GGHalf.halfTorus n) ψ)
    {P : Fin n} {j : Fin (blockCount n)}
    (hS : weylRep n GGHalf.F2 (blockIdx n j) ∈
      slOn (n + 1) {i : Fin (n + 1) | i ≠ P.castSucc ∧ i ≠ P.succ})
    (hJeq : J = (slOn (n + 1) {i : Fin (n + 1) | i ≠ P.castSucc ∧ i ≠ P.succ}).map ψ)
    (hN : weylRep n GGHalf.F2 (blockIdx n j) ∈
      Subgroup.normalizer
        (GGHalf.halfTorus n : Set (Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2))) :
    ∃ φ : MulAut ↥Bs, φ ∈ ggAutomizer J Bs ∧ φ ≠ 1 ∧ φ * φ = 1 ∧
      (∀ b : ↥Bs, ((φ b : ↥Bs) : G) =
        ψ (weylRep n GGHalf.F2 (blockIdx n j)) * (b : G) *
          (ψ (weylRep n GGHalf.F2 (blockIdx n j)))⁻¹) ∧
      (∀ b : ↥Bs, (b : G) = ψ (omegaBlock n (blockIdx n j)) →
        ((φ b : ↥Bs) : G) = ψ ((omegaBlock n (blockIdx n j))⁻¹)) ∧
      (∀ (j' : Fin (blockCount n)), j' ≠ j → ∀ b : ↥Bs,
        (b : G) = ψ (omegaBlock n (blockIdx n j')) →
          ((φ b : ↥Bs) : G) = ψ (omegaBlock n (blockIdx n j'))) := by
  obtain ⟨φ, hmem, hne, hsq, hgen⟩ := ggQ2Lin_weylAut_data_aut hF hS hJeq hN
  have hbω_mem : ψ (omegaBlock n (blockIdx n j)) ∈ Bs :=
    hF.torus_le (Subgroup.mem_map.mpr
      ⟨omegaBlock n (blockIdx n j), Subgroup.subset_closure
        ⟨blockIdx n j, by rw [blockIdx_val]; omega, rfl⟩, rfl⟩)
  let bω : ↥Bs := ⟨ψ (omegaBlock n (blockIdx n j)), hbω_mem⟩
  have hinv : ∀ b : ↥Bs, (b : G) = ψ (omegaBlock n (blockIdx n j)) →
      ((φ b : ↥Bs) : G) = ψ ((omegaBlock n (blockIdx n j))⁻¹) := by
    intro b hb
    have hb' : b = bω := Subtype.ext (by rw [hb])
    rw [hb']
    exact ggQ2Lin_weylAut_data_inv hgen bω rfl
  have hfix : ∀ (j' : Fin (blockCount n)), j' ≠ j → ∀ b : ↥Bs,
      (b : G) = ψ (omegaBlock n (blockIdx n j')) →
        ((φ b : ↥Bs) : G) = ψ (omegaBlock n (blockIdx n j')) := by
    intro j' hj' b hb
    exact weylAut_fix_of_ne n j hj' hgen hb
  exact ⟨φ, hmem, hne, hsq, hgen, hinv, hfix⟩

theorem ggQ2Lin_fix_ge_three_impossible {n : ℕ}
    {ψ : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2 →* G}
    (hS : GGQTwoSetting p B Bs x L D J)
    (hF : GGHalfTorusFrame Bs L (GGHalf.halfTorus n) ψ)
    {z : G} {t : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2} {a : ℤ}
    (hz : z = x ^ a * ψ t) (ht : t ∈ GGHalf.halfTorus n)
    (hDclos : D = Subgroup.closure ({x, z} : Set G))
    (h4 : 4 ≤ GGHalf.supp t) (hfix : 3 ≤ n + 1 - GGHalf.supp t) : False := by
  obtain ⟨-, hcomp⟩ := ggQ2Lin_layer_eq hS hF hz hDclos
  exact GGHalf.layer_centralizer_not_component ht h4 hfix
    ⟨LargeEvenLayer (Subgroup.centralizer ({t} : Set
      (Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2))), rfl, hcomp⟩

theorem ggQ2Lin_actsAs_of_eq {n : ℕ}
    {ψ : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2 →* G}
    (hS : GGQTwoSetting p B Bs x L D J)
    (hF : GGHalfTorusFrame Bs L (GGHalf.halfTorus n) ψ)
    {z : G} {t : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2} {a : ℤ}
    (hz : z = x ^ a * ψ t) :
    GGHalfActsAs ψ.range ψ z t := by
  have hcfg : GGConfig p B Bs x L D J := hS.1.1
  obtain ⟨-, -, -, hLx, -⟩ := hcfg.tableB_facts
  intro l hl
  obtain ⟨s, rfl⟩ := hl
  have hψtL : ψ t ∈ L := by rw [← hF.range]; exact ⟨t, rfl⟩
  have hψsL : ψ s ∈ L := by rw [← hF.range]; exact ⟨s, rfl⟩
  have hxt : Commute x (ψ t) := by
    rw [Commute]
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hLx hψtL)).symm
  have hxs : Commute x (ψ s) := by
    rw [Commute]
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hLx hψsL)).symm
  have huL : ψ t * ψ s * (ψ t)⁻¹ ∈ L :=
    L.mul_mem (L.mul_mem hψtL hψsL) (L.inv_mem hψtL)
  have hxu : Commute x (ψ t * ψ s * (ψ t)⁻¹) :=
    ((hxt.mul_right hxs).mul_right hxt.inv_right)
  have hxua : Commute (x ^ a) (ψ t * ψ s * (ψ t)⁻¹) := hxu.zpow_left a
  rw [hz]
  have hconj : (x ^ a * ψ t) * ψ s * (x ^ a * ψ t)⁻¹ =
      x ^ a * (ψ t * ψ s * (ψ t)⁻¹) * (x ^ a)⁻¹ := by group
  rw [hconj, hxua.eq, mul_assoc, mul_inv_cancel, mul_one]

theorem ggQ2Lin_x_not_mem_L {n : ℕ}
    {ψ : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2 →* G}
    (hS : GGQTwoSetting p B Bs x L D J) (hp : p = 3)
    (hF : GGHalfTorusFrame Bs L (GGHalf.halfTorus n) ψ) : x ∉ L := by
  intro hxL
  have hcfg : GGConfig p B Bs x L D J := hS.1.1
  obtain ⟨-, -, -, hLx, -⟩ := hcfg.tableB_facts
  have hxcenter : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro z
    apply Subtype.ext
    simpa using Subgroup.mem_centralizer_singleton_iff.mp (hLx z.2)
  have hx1 : x = 1 := by
    have hbot : (⟨x, hxL⟩ : ↥L) ∈ (⊥ : Subgroup ↥L) := by
      rw [← ggQ2Lin_center_eq_bot hF]
      exact hxcenter
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hbot)
  have hxord : orderOf x = 3 := by
    rw [hcfg.orderOf_x, hp]
  rw [hx1, orderOf_one] at hxord
  omega

theorem zpow_eq_one_of_mem_of_not_mem {G : Type*} [Group G]
    {H : Subgroup G} {x : G} (hx3 : x ^ 3 = 1) (hxH : x ∉ H) {c : ℤ}
    (hc : x ^ c ∈ H) : x ^ c = 1 := by
  have hred : x ^ c = x ^ (c % (3 : ℤ)) := zpow_eq_zpow_emod' c (n := 3) hx3
  rw [hred] at hc ⊢
  have hlt := Int.emod_lt_of_pos c (by norm_num : (0 : ℤ) < 3)
  have hnon := Int.emod_nonneg c (by norm_num : (3 : ℤ) ≠ 0)
  have hcases : c % (3 : ℤ) = 0 ∨ c % (3 : ℤ) = 1 ∨ c % (3 : ℤ) = 2 := by omega
  rcases hcases with h | h | h
  · rw [h, zpow_zero]
  · rw [h, zpow_one] at hc ⊢
    exact absurd hc hxH
  · rw [h] at hc ⊢
    exfalso
    apply hxH
    have hx4 : x = (x ^ (2 : ℤ)) ^ (2 : ℤ) := by
      rw [← _root_.zpow_mul]
      norm_num
      exact show x = x ^ (4 : ℕ) from by
        rw [show (4 : ℕ) = 1 + 3 by norm_num, pow_add, hx3, mul_one, pow_one]
    rw [hx4]
    exact H.zpow_mem hc 2

theorem mem_closure_pair_of_commute {G : Type*} [Group G] {x z y : G}
    (h : Commute x z) (hy : y ∈ Subgroup.closure ({x, z} : Set G)) :
    ∃ r s : ℤ, x ^ r * z ^ s = y := by
  let S : Subgroup G :=
    { carrier := {y | ∃ r s : ℤ, x ^ r * z ^ s = y}
      one_mem' := ⟨0, 0, by simp⟩
      mul_mem' := by
        rintro y₁ y₂ ⟨r₁, s₁, rfl⟩ ⟨r₂, s₂, rfl⟩
        refine ⟨r₁ + r₂, s₁ + s₂, ?_⟩
        calc
          x ^ (r₁ + r₂) * z ^ (s₁ + s₂) =
              (x ^ r₁ * x ^ r₂) * (z ^ s₁ * z ^ s₂) := by
            rw [_root_.zpow_add, _root_.zpow_add]
          _ = x ^ r₁ * (x ^ r₂ * z ^ s₁) * z ^ s₂ := by group
          _ = x ^ r₁ * (z ^ s₁ * x ^ r₂) * z ^ s₂ := by
            rw [(h.zpow_zpow r₂ s₁).eq]
          _ = (x ^ r₁ * z ^ s₁) * (x ^ r₂ * z ^ s₂) := by group
      inv_mem' := by
        rintro y ⟨r, s, rfl⟩
        refine ⟨-r, -s, ?_⟩
        rw [_root_.mul_inv_rev, ← _root_.zpow_neg, ← _root_.zpow_neg]
        exact (h.zpow_zpow (-r) (-s)).eq }
  have hxS : x ∈ S := ⟨1, 0, by simp⟩
  have hzS : z ∈ S := ⟨0, 1, by simp⟩
  rw [Subgroup.mem_closure] at hy
  exact hy S (by rintro _ (rfl | rfl); exacts [hxS, hzS])

theorem ggQ2Lin_psi_not_mem_D {n : ℕ}
    {ψ : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2 →* G}
    (hS : GGQTwoSetting p B Bs x L D J) (hp : p = 3)
    (hF : GGHalfTorusFrame Bs L (GGHalf.halfTorus n) ψ)
    (hxL : x ∉ L)
    {z : G} {t : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2} {a : ℤ}
    (hz : z = x ^ a * ψ t)
    (hDclos : D = Subgroup.closure ({x, z} : Set G))
    {u : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2}
    (hu : u ∉ Subgroup.zpowers t) : ψ u ∉ D := by
  intro hmem
  have hcfg : GGConfig p B Bs x L D J := hS.1.1
  obtain ⟨-, -, -, hLx, -⟩ := hcfg.tableB_facts
  have hψtL : ψ t ∈ L := by
    rw [← hF.range]
    exact ⟨t, rfl⟩
  have hxcomm : Commute x (ψ t) :=
    (Subgroup.mem_centralizer_singleton_iff.mp (hLx hψtL)).symm
  have hxz : Commute x z := by
    rw [hz]
    exact ((Commute.refl x).zpow_right a).mul_right hxcomm
  rw [hDclos] at hmem
  obtain ⟨r, s, hd12⟩ := mem_closure_pair_of_commute hxz hmem
  have hzpow : z ^ s = x ^ (a * s) * ψ (t ^ s) := by
    rw [hz, Commute.mul_zpow (hxcomm.zpow_left a), ← _root_.zpow_mul, map_zpow]
  have hEq : ψ u = x ^ (r + a * s) * ψ (t ^ s) := by
    rw [← hd12, hzpow, ← mul_assoc, ← _root_.zpow_add]
  have hψuL : ψ u ∈ L := by
    rw [← hF.range]
    exact ⟨u, rfl⟩
  have hψtpowL : ψ (t ^ s) ∈ L := by
    rw [← hF.range]
    exact ⟨t ^ s, rfl⟩
  have hxInL : x ^ (r + a * s) ∈ L := by
    have hxeq : x ^ (r + a * s) = ψ u * (ψ (t ^ s))⁻¹ := by
      rw [hEq]
      group
    rw [hxeq]
    exact L.mul_mem hψuL (L.inv_mem hψtpowL)
  have hx3 : x ^ 3 = 1 := by
    have h := pow_orderOf_eq_one x
    rwa [hcfg.orderOf_x, hp] at h
  have hxpow1 : x ^ (r + a * s) = 1 :=
    zpow_eq_one_of_mem_of_not_mem hx3 hxL hxInL
  have hψeq : ψ u = ψ (t ^ s) := by rw [hEq, hxpow1, one_mul]
  exact hu (Subgroup.mem_zpowers_iff.mpr ⟨s, (hF.inj hψeq).symm⟩)

theorem ggQ2Lin_fix_two_coord (n : ℕ)
    {t : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2}
    (ht : t ∈ GGHalf.halfTorus n) (hfix : n + 1 - GGHalf.supp t = 2) :
    ∃ Φ : (Fin (GGHalf.TorusRank.blockCount n) → Multiplicative (ZMod 3)) ≃*
        ↥(GGHalf.halfTorus n),
      (∀ j : Fin (GGHalf.TorusRank.blockCount n),
        ((Φ (GGHalf.TorusRank.torusGen n j) : ↥(GGHalf.halfTorus n)) :
          Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2) =
          GGHalf.omegaBlock n (GGHalf.TorusRank.blockIdx n j)) ∧
      ∃ v : Fin (GGHalf.TorusRank.blockCount n) → Multiplicative (ZMod 3),
        ((Φ v : ↥(GGHalf.halfTorus n)) :
          Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2) = t ∧
        n + 1 - 2 * (Finset.univ.filter fun j :
          Fin (GGHalf.TorusRank.blockCount n) => v j ≠ 1).card = 2 := by
  classical
  obtain ⟨Φ, hΦ0⟩ := GGHalf.exists_torusCoord n
  have hΦ : ∀ j : Fin (GGHalf.TorusRank.blockCount n),
      ((Φ (GGHalf.TorusRank.torusGen n j) : ↥(GGHalf.halfTorus n)) :
        Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2) =
        GGHalf.omegaBlock n (GGHalf.TorusRank.blockIdx n j) := by
    intro j
    simpa [GGHalf.TorusRank.torusGen, GGHalf.TorusRank.blockIdx] using hΦ0 j
  let v := Φ.symm ⟨t, ht⟩
  have htv : ((Φ v : ↥(GGHalf.halfTorus n)) :
      Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2) = t := by
    change ((Φ (Φ.symm ⟨t, ht⟩) : ↥(GGHalf.halfTorus n)) :
      Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2) = t
    rw [MulEquiv.apply_symm_apply]
  have hsuppN := GGHalf.TorusRank.supp_torusCoord n hΦ v
  rw [htv] at hsuppN
  refine ⟨Φ, hΦ, v, htv, ?_⟩
  rw [← hsuppN]
  exact hfix

theorem ggQ2Lin_fix_two_find_omega (n : ℕ) (hn : 5 ≤ n)
    {Φ : (Fin (GGHalf.TorusRank.blockCount n) → Multiplicative (ZMod 3)) ≃*
        ↥(GGHalf.halfTorus n)}
    (hΦ : ∀ j : Fin (GGHalf.TorusRank.blockCount n),
      ((Φ (GGHalf.TorusRank.torusGen n j) : ↥(GGHalf.halfTorus n)) :
        Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2) =
        GGHalf.omegaBlock n (GGHalf.TorusRank.blockIdx n j))
    {t : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2}
    {v : Fin (GGHalf.TorusRank.blockCount n) → Multiplicative (ZMod 3)}
    (htv : ((Φ v : ↥(GGHalf.halfTorus n)) :
      Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2) = t)
    (hfixN : n + 1 - 2 * (Finset.univ.filter fun j :
      Fin (GGHalf.TorusRank.blockCount n) => v j ≠ 1).card = 2) :
    ∃ (j : Fin (GGHalf.TorusRank.blockCount n))
      (u : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2),
      v j = 1 ∧ (∀ i : Fin (GGHalf.TorusRank.blockCount n), i ≠ j → v i ≠ 1) ∧
      GGHalf.TorusRank.blockExtra n = 0 ∧ u ∈ GGHalf.halfTorus n ∧
      (t : Matrix (Fin (n + 1)) (Fin (n + 1)) GGHalf.F2) =
        (GGHalf.TorusRank.torusBlk n v).submatrix (GGHalf.TorusRank.torusFrame n)
          (GGHalf.TorusRank.torusFrame n) ∧
      (u : Matrix (Fin (n + 1)) (Fin (n + 1)) GGHalf.F2) =
        (GGHalf.TorusRank.torusBlk n (GGHalf.TorusRank.torusGen n j)).submatrix
          (GGHalf.TorusRank.torusFrame n) (GGHalf.TorusRank.torusFrame n) ∧
      u ∉ Subgroup.zpowers t := by
  have hNle : (Finset.univ.filter fun j : Fin (GGHalf.TorusRank.blockCount n) =>
      v j ≠ 1).card ≤ GGHalf.TorusRank.blockCount n := by
    simpa using (Finset.card_filter_le (s := (Finset.univ : Finset
      (Fin (GGHalf.TorusRank.blockCount n)))) (p := fun j => v j ≠ 1))
  have hcard := GGHalf.TorusRank.card_eq_two_mul_blockCount_add n
  have hrle := GGHalf.TorusRank.blockExtra_le_one n
  have hr : GGHalf.TorusRank.blockExtra n = 0 := by omega
  obtain ⟨j, hvj, hother⟩ :=
    GGHalf.TorusRank.exists_trivial_coord_of_fix_two n v hfixN
  have hk2 : 1 < GGHalf.TorusRank.blockCount n := by
    rw [GGHalf.TorusRank.blockCount]
    omega
  obtain ⟨i, hi⟩ := Finset.exists_mem_ne (s := (Finset.univ : Finset
    (Fin (GGHalf.TorusRank.blockCount n)))) (by simpa using hk2) j
  have hine : i ≠ j := hi.2
  let u : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2 :=
    ((Φ (GGHalf.TorusRank.torusGen n j) : ↥(GGHalf.halfTorus n)) :
      Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2)
  have hu_mem : u ∈ GGHalf.halfTorus n := (Φ (GGHalf.TorusRank.torusGen n j)).2
  have hmatT : (t : Matrix (Fin (n + 1)) (Fin (n + 1)) GGHalf.F2) =
      (GGHalf.TorusRank.torusBlk n v).submatrix (GGHalf.TorusRank.torusFrame n)
        (GGHalf.TorusRank.torusFrame n) := by
    rw [← htv]
    exact GGHalf.TorusRank.torusMat_eq_blk n hΦ v
  have hmatU : (u : Matrix (Fin (n + 1)) (Fin (n + 1)) GGHalf.F2) =
      (GGHalf.TorusRank.torusBlk n (GGHalf.TorusRank.torusGen n j)).submatrix
        (GGHalf.TorusRank.torusFrame n) (GGHalf.TorusRank.torusFrame n) :=
    GGHalf.TorusRank.torusMat_eq_blk n hΦ (GGHalf.TorusRank.torusGen n j)
  have hu_not : u ∉ Subgroup.zpowers t := by
    have h := GGHalf.TorusRank.omegaBlock_not_mem_zpowers_of_trivial_coord
      n hΦ hine hother
    rw [htv] at h
    simpa [u, ← hΦ j] using h
  exact ⟨j, u, hvj, hother, hr, hu_mem, hmatT, hmatU, hu_not⟩

theorem ggQ2Lin_fix_two_D_eq {n : ℕ}
    {ψ : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2 →* G}
    (hS : GGQTwoSetting p B Bs x L D J) (hp : p = 3) (hn : 5 ≤ n)
    (hF : GGHalfTorusFrame Bs L (GGHalf.halfTorus n) ψ)
    (hBs : Bs = Subgroup.zpowers x ⊔ (GGHalf.halfTorus n).map ψ)
    {z : G} {t : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2} {a : ℤ}
    (hz : z = x ^ a * ψ t)
    (hDclos : D = Subgroup.closure ({x, z} : Set G)) :
    D = Bs ⊓ Subgroup.centralizer (J : Set G) := by
  have hcfg : GGConfig p B Bs x L D J := hS.1.1
  obtain ⟨-, -, -, hxD, hKlayer, hKcomp, hDcent⟩ := hcfg.2.2.1
  obtain ⟨-, -, -, hLx, -⟩ := hcfg.tableB_facts
  obtain ⟨hJmap, hcomp0⟩ := ggQ2Lin_layer_eq hS hF hz hDclos
  have hCD : Subgroup.centralizer (D : Set G) =
      Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({z} : Set G) := by
    rw [hDclos, centralizer_closure_pair_eq_inf]
  have hCDL : L ⊓ Subgroup.centralizer (D : Set G) =
      L ⊓ Subgroup.centralizer ({z} : Set G) := by
    rw [hCD, ← inf_assoc, inf_eq_left.mpr hLx]
  have hmapC := ggQ2Lin_inf_centralizer_eq_map hS hF hz
  have hJlayer : J = LargeEvenLayer (L ⊓ Subgroup.centralizer ({z} : Set G)) := by
    rw [hJmap, hmapC, largeEvenLayer_map_of_injective ψ hF.inj]
  have hKJ : (LargeEvenLayer (L ⊓ Subgroup.centralizer (D : Set G))) = J := by
    rw [hCDL, ← hJlayer]
  have hB : B = Bs := ggQ2Lin_B_eq hS hp hn hF hBs
  have hDcent' : D = B ⊓ Subgroup.centralizer
      (LargeEvenLayer (L ⊓ Subgroup.centralizer (D : Set G)) : Set G) := by
    simpa only [hKlayer] using hDcent
  rw [hDcent', hKJ, hB]

theorem ggQ2Lin_fix_two_contradiction {n : ℕ}
    {ψ : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2 →* G}
    (hS : GGQTwoSetting p B Bs x L D J) (hp : p = 3) (hn : 5 ≤ n)
    (hF : GGHalfTorusFrame Bs L (GGHalf.halfTorus n) ψ)
    (hBs : Bs = Subgroup.zpowers x ⊔ (GGHalf.halfTorus n).map ψ)
    {z : G} {t : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2} {a : ℤ}
    (hz : z = x ^ a * ψ t) (ht : t ∈ GGHalf.halfTorus n)
    (hDclos : D = Subgroup.closure ({x, z} : Set G))
    (hfix : n + 1 - GGHalf.supp t = 2)
    (v : Fin (GGHalf.TorusRank.blockCount n) → Multiplicative (ZMod 3))
    (j : Fin (GGHalf.TorusRank.blockCount n))
    (u : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2)
    (hvj : v j = 1)
    (hother : ∀ i : Fin (GGHalf.TorusRank.blockCount n), i ≠ j → v i ≠ 1)
    (hr : GGHalf.TorusRank.blockExtra n = 0)
    (hu_mem : u ∈ GGHalf.halfTorus n)
    (hmatT : (t : Matrix (Fin (n + 1)) (Fin (n + 1)) GGHalf.F2) =
      (GGHalf.TorusRank.torusBlk n v).submatrix (GGHalf.TorusRank.torusFrame n)
        (GGHalf.TorusRank.torusFrame n))
    (hmatU : (u : Matrix (Fin (n + 1)) (Fin (n + 1)) GGHalf.F2) =
      (GGHalf.TorusRank.torusBlk n (GGHalf.TorusRank.torusGen n j)).submatrix
        (GGHalf.TorusRank.torusFrame n) (GGHalf.TorusRank.torusFrame n))
    (hu_not : u ∉ Subgroup.zpowers t) : False := by
  have hxL : x ∉ L := ggQ2Lin_x_not_mem_L hS hp hF
  have hDnot : ψ u ∉ D :=
    ggQ2Lin_psi_not_mem_D hS hp hF hxL hz hDclos hu_not
  have hD_eq : D = Bs ⊓ Subgroup.centralizer (J : Set G) :=
    ggQ2Lin_fix_two_D_eq hS hp hn hF hBs hz hDclos
  obtain ⟨hJmap, hcomp0⟩ := ggQ2Lin_layer_eq hS hF hz hDclos
  let K0 := LargeEvenLayer (Subgroup.centralizer ({t} :
    Set (Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2)))
  have hK0le : K0 ≤ Subgroup.centralizer ({t} :
      Set (Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2)) := hcomp0.1
  have : Group.IsPerfect ↥K0 := Group.isPerfect_def.mpr hcomp0.2.2.1
  have hcard4 : Nat.card (fixSub n t) ≤ 4 := by
    rw [natCard_fixSub_of_supp n hfix]
  have huT : Commute u t := by
    exact show Commute u t from GGHalf.halfTorus_comm hu_mem ht
  have hψuCJ : ψ u ∈ Subgroup.centralizer (J : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [hJmap] at hy
    obtain ⟨k, hkK, rfl⟩ := Subgroup.mem_map.mp hy
    have hcomm := GGHalf.TorusRank.torusGen_commute_of_fixPerm n hmatT hmatU hvj
      hother hr huT K0 hK0le hcard4 ⟨k, hkK⟩
    exact (hcomm.map ψ).eq
  have hψuBs : ψ u ∈ Bs := hF.torus_le (Subgroup.mem_map.mpr ⟨u, hu_mem, rfl⟩)
  have hmem : ψ u ∈ Bs ⊓ Subgroup.centralizer (J : Set G) := ⟨hψuBs, hψuCJ⟩
  exact hDnot (by rwa [← hD_eq] at hmem)

theorem ggQ2Lin_fix_two_impossible {n : ℕ}
    {ψ : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2 →* G}
    (hS : GGQTwoSetting p B Bs x L D J) (hp : p = 3) (hn : 5 ≤ n)
    (hF : GGHalfTorusFrame Bs L (GGHalf.halfTorus n) ψ)
    (hBs : Bs = Subgroup.zpowers x ⊔ (GGHalf.halfTorus n).map ψ)
    {z : G} {t : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2} {a : ℤ}
    (hz : z = x ^ a * ψ t) (ht : t ∈ GGHalf.halfTorus n)
    (hDclos : D = Subgroup.closure ({x, z} : Set G))
    (hfix : n + 1 - GGHalf.supp t = 2) : False := by
  obtain ⟨Φ, hΦ, v, htv, hfixN⟩ := ggQ2Lin_fix_two_coord n ht hfix
  obtain ⟨j, u, hvj, hother, hr, hu_mem, hmatT, hmatU, hu_not⟩ :=
    ggQ2Lin_fix_two_find_omega n hn hΦ htv hfixN
  exact ggQ2Lin_fix_two_contradiction hS hp hn hF hBs hz ht hDclos hfix
    v j u hvj hother hr hu_mem hmatT hmatU hu_not

structure WeylAutData (n : ℕ)
    (ψ : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2 →* G)
    (Bs J : Subgroup G) (P : Fin n) (j : Fin (GGHalf.TorusRank.blockCount n)) where
  φ : MulAut ↥Bs
  mem : φ ∈ ggAutomizer J Bs
  ne : φ ≠ 1
  sq : φ * φ = 1
  act : ∀ b : ↥Bs, ((φ b : ↥Bs) : G) =
    ψ (weylRep n GGHalf.F2 (GGHalf.TorusRank.blockIdx n j)) * (b : G) *
      (ψ (weylRep n GGHalf.F2 (GGHalf.TorusRank.blockIdx n j)))⁻¹
  inv : ∀ b : ↥Bs, (b : G) = ψ (GGHalf.omegaBlock n
      (GGHalf.TorusRank.blockIdx n j)) →
    ((φ b : ↥Bs) : G) = ψ ((GGHalf.omegaBlock n
      (GGHalf.TorusRank.blockIdx n j))⁻¹)
  fix : ∀ (j' : Fin (GGHalf.TorusRank.blockCount n)), j' ≠ j → ∀ b : ↥Bs,
    (b : G) = ψ (GGHalf.omegaBlock n (GGHalf.TorusRank.blockIdx n j')) →
      ((φ b : ↥Bs) : G) = ψ (GGHalf.omegaBlock n
        (GGHalf.TorusRank.blockIdx n j'))

noncomputable def ggQ2Lin_supp_two_getAut (m : ℕ)
    {ψ : Matrix.SpecialLinearGroup (Fin (m + 2 + 1)) GGHalf.F2 →* G}
    {Bs J : Subgroup G}
    {j0 : Fin (GGHalf.TorusRank.blockCount (m + 2))}
    (hF : GGHalfTorusFrame Bs L (GGHalf.halfTorus (m + 2)) ψ)
    (hJeq : J = (GGHalf.slOn (m + 2 + 1) {i : Fin (m + 2 + 1) |
      i ≠ (GGHalf.TorusRank.blockIdx (m + 2) j0).castSucc ∧
        i ≠ (GGHalf.TorusRank.blockIdx (m + 2) j0).succ}).map ψ) :
    ∀ j : Fin (GGHalf.TorusRank.blockCount (m + 2)), j ≠ j0 →
      WeylAutData (m + 2) ψ Bs J (GGHalf.TorusRank.blockIdx (m + 2) j0) j := by
  let P : Fin (m + 2) := GGHalf.TorusRank.blockIdx (m + 2) j0
  have hPval : P.val % 2 = 0 := by
    simp only [P, GGHalf.TorusRank.blockIdx_val]
    omega
  have getAut : ∀ j : Fin (GGHalf.TorusRank.blockCount (m + 2)), j ≠ j0 →
      WeylAutData (m + 2) ψ Bs J P j := by
    intro j hj
    have hS' : weylRep (m + 2) GGHalf.F2 (GGHalf.TorusRank.blockIdx (m + 2) j) ∈
        GGHalf.slOn (m + 2 + 1) {i : Fin (m + 2 + 1) |
          i ≠ P.castSucc ∧ i ≠ P.succ} := by
      apply GGHalf.TorusRank.weylRep_mem_slOn_compl (m + 2) hPval j
      intro h'
      apply hj
      have hv := congrArg Fin.val h'
      have hP : P = GGHalf.TorusRank.blockIdx (m + 2) j0 := rfl
      rw [GGHalf.TorusRank.blockIdx_val, hP, GGHalf.TorusRank.blockIdx_val] at hv
      have hjval : j.val ≠ j0.val := fun hv' => hj (Fin.ext hv')
      exact Fin.ext (by omega)
    have hN' : weylRep (m + 2) GGHalf.F2 (GGHalf.TorusRank.blockIdx (m + 2) j) ∈
        Subgroup.normalizer (GGHalf.halfTorus (m + 2) :
          Set (Matrix.SpecialLinearGroup (Fin (m + 2 + 1)) GGHalf.F2)) :=
      GGHalf.TorusRank.weylRep_mem_normalizer_halfTorus (m + 2) j
    have h := ggQ2Lin_weylAut_data (P := P) (j := j) hF hS' hJeq hN'
    let φ := Classical.choose h
    have hspec := Classical.choose_spec h
    exact ⟨φ, hspec.1, hspec.2.1, hspec.2.2.1, hspec.2.2.2.1,
      hspec.2.2.2.2.1, hspec.2.2.2.2.2⟩
  exact getAut

theorem ggQ2Lin_supp_two_weyl_data (m : ℕ) (hm : 3 ≤ m)
    {ψ : Matrix.SpecialLinearGroup (Fin (m + 2 + 1)) GGHalf.F2 →* G}
    {Bs J : Subgroup G}
    {j0 : Fin (GGHalf.TorusRank.blockCount (m + 2))}
    (hF : GGHalfTorusFrame Bs L (GGHalf.halfTorus (m + 2)) ψ)
    (hJeq : J = (GGHalf.slOn (m + 2 + 1) {i : Fin (m + 2 + 1) |
      i ≠ (GGHalf.TorusRank.blockIdx (m + 2) j0).castSucc ∧
        i ≠ (GGHalf.TorusRank.blockIdx (m + 2) j0).succ}).map ψ) :
    ∃ (j1 j2 : Fin (GGHalf.TorusRank.blockCount (m + 2))),
      j1 ≠ j0 ∧ j2 ≠ j0 ∧ j2 ≠ j1 ∧
      ∃ (d1 : WeylAutData (m + 2) ψ Bs J (GGHalf.TorusRank.blockIdx (m + 2) j0) j1),
        ∃ (d2 : WeylAutData (m + 2) ψ Bs J (GGHalf.TorusRank.blockIdx (m + 2) j0) j2),
          d1 = d1 ∧ d2 = d2 := by
  classical
  have getAut := ggQ2Lin_supp_two_getAut m hF hJeq
  have hk3 : 3 ≤ GGHalf.TorusRank.blockCount (m + 2) := by
    rw [GGHalf.TorusRank.blockCount]
    omega
  have hcard_erase : 2 ≤ (Finset.univ.erase j0).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ j0), Finset.card_univ, Fintype.card_fin]
    omega
  have hone : 1 < (Finset.univ.erase j0).card := by omega
  obtain ⟨j1, hj1⟩ := Finset.exists_mem_ne hone j0
  have hj1_erase : j1 ∈ Finset.univ.erase j0 := hj1.1
  have hj1ne : j1 ≠ j0 := hj1.2
  obtain ⟨j2, hj2⟩ := Finset.card_pos.mp (by
    rw [Finset.card_erase_of_mem hj1_erase, Finset.card_erase_of_mem (Finset.mem_univ j0),
      Finset.card_univ, Fintype.card_fin]
    omega)
  have hj2_erase : j2 ∈ Finset.univ.erase j0 := Finset.mem_of_mem_erase hj2
  have hj2ne1 : j2 ≠ j1 := (Finset.mem_erase.mp hj2).1
  have hj2ne0 : j2 ≠ j0 := (Finset.mem_erase.mp hj2_erase).1
  exact ⟨j1, j2, hj1ne, hj2ne0, hj2ne1, getAut j1 hj1ne, getAut j2 hj2ne0,
    rfl, rfl⟩

omit [Finite G] in
theorem ggQ2Lin_supp_two_weyl_comm (m : ℕ)
    {ψ : Matrix.SpecialLinearGroup (Fin (m + 2 + 1)) GGHalf.F2 →* G}
    {Bs J : Subgroup G} {P : Fin (m + 2)}
    {j1 j2 : Fin (GGHalf.TorusRank.blockCount (m + 2))}
    (d1 : WeylAutData (m + 2) ψ Bs J P j1)
    (d2 : WeylAutData (m + 2) ψ Bs J P j2)
    (hψcomm : Commute (ψ (weylRep (m + 2) GGHalf.F2
      (GGHalf.TorusRank.blockIdx (m + 2) j1)))
      (ψ (weylRep (m + 2) GGHalf.F2 (GGHalf.TorusRank.blockIdx (m + 2) j2)))) :
    d1.φ * d2.φ = d2.φ * d1.φ := by
  ext b
  rw [MulAut.mul_apply, MulAut.mul_apply, d1.act (d2.φ b), d2.act b, d2.act (d1.φ b),
    d1.act b]
  calc ψ (weylRep (m + 2) GGHalf.F2 (GGHalf.TorusRank.blockIdx (m + 2) j1)) *
        (ψ (weylRep (m + 2) GGHalf.F2 (GGHalf.TorusRank.blockIdx (m + 2) j2)) *
          (b : G) *
            (ψ (weylRep (m + 2) GGHalf.F2
              (GGHalf.TorusRank.blockIdx (m + 2) j2)))⁻¹) *
        (ψ (weylRep (m + 2) GGHalf.F2 (GGHalf.TorusRank.blockIdx (m + 2) j1)))⁻¹
      = (ψ (weylRep (m + 2) GGHalf.F2 (GGHalf.TorusRank.blockIdx (m + 2) j1)) *
          ψ (weylRep (m + 2) GGHalf.F2 (GGHalf.TorusRank.blockIdx (m + 2) j2))) *
          (b : G) *
            (ψ (weylRep (m + 2) GGHalf.F2 (GGHalf.TorusRank.blockIdx (m + 2) j1)) *
              ψ (weylRep (m + 2) GGHalf.F2
                (GGHalf.TorusRank.blockIdx (m + 2) j2)))⁻¹ := by group
    _ = (ψ (weylRep (m + 2) GGHalf.F2 (GGHalf.TorusRank.blockIdx (m + 2) j2)) *
          ψ (weylRep (m + 2) GGHalf.F2 (GGHalf.TorusRank.blockIdx (m + 2) j1))) *
          (b : G) *
            (ψ (weylRep (m + 2) GGHalf.F2 (GGHalf.TorusRank.blockIdx (m + 2) j2)) *
              ψ (weylRep (m + 2) GGHalf.F2
                (GGHalf.TorusRank.blockIdx (m + 2) j1)))⁻¹ := by rw [hψcomm.eq]
    _ = ψ (weylRep (m + 2) GGHalf.F2 (GGHalf.TorusRank.blockIdx (m + 2) j2)) *
        (ψ (weylRep (m + 2) GGHalf.F2 (GGHalf.TorusRank.blockIdx (m + 2) j1)) *
          (b : G) *
            (ψ (weylRep (m + 2) GGHalf.F2
              (GGHalf.TorusRank.blockIdx (m + 2) j1)))⁻¹) *
        (ψ (weylRep (m + 2) GGHalf.F2 (GGHalf.TorusRank.blockIdx (m + 2) j2)))⁻¹ := by
          group

omit [Finite G] in
theorem ggQ2Lin_supp_two_weyl_ne (m : ℕ)
    {ψ : Matrix.SpecialLinearGroup (Fin (m + 2 + 1)) GGHalf.F2 →* G}
    {Bs J : Subgroup G} {P : Fin (m + 2)}
    {j1 j2 : Fin (GGHalf.TorusRank.blockCount (m + 2))}
    (hF : GGHalfTorusFrame Bs L (GGHalf.halfTorus (m + 2)) ψ)
    (hj : j2 ≠ j1)
    (d1 : WeylAutData (m + 2) ψ Bs J P j1)
    (d2 : WeylAutData (m + 2) ψ Bs J P j2) :
    d2.φ ≠ d1.φ := by
  intro heq
  have hb1_mem : ψ (GGHalf.omegaBlock (m + 2) (GGHalf.TorusRank.blockIdx (m + 2) j1)) ∈ Bs :=
    hF.torus_le (Subgroup.mem_map.mpr
      ⟨GGHalf.omegaBlock (m + 2) (GGHalf.TorusRank.blockIdx (m + 2) j1),
        Subgroup.subset_closure ⟨GGHalf.TorusRank.blockIdx (m + 2) j1,
          by rw [GGHalf.TorusRank.blockIdx_val]; omega, rfl⟩, rfl⟩)
  let b1 : ↥Bs := ⟨ψ (GGHalf.omegaBlock (m + 2) (GGHalf.TorusRank.blockIdx (m + 2) j1)), hb1_mem⟩
  have h1 : ((d1.φ b1 : ↥Bs) : G) = ψ ((GGHalf.omegaBlock (m + 2)
      (GGHalf.TorusRank.blockIdx (m + 2) j1))⁻¹) := d1.inv b1 rfl
  have h2 : ((d2.φ b1 : ↥Bs) : G) = ψ (GGHalf.omegaBlock (m + 2)
      (GGHalf.TorusRank.blockIdx (m + 2) j1)) := d2.fix j1 hj.symm b1 rfl
  rw [heq] at h2
  have heqψ : ψ ((GGHalf.omegaBlock (m + 2) (GGHalf.TorusRank.blockIdx (m + 2) j1))⁻¹) =
      ψ (GGHalf.omegaBlock (m + 2) (GGHalf.TorusRank.blockIdx (m + 2) j1)) := by
    rw [← h1, h2]
  exact GGHalf.TorusRank.ne_inv_self_of_pow_three (GGHalf.omegaBlock_pow_three (m + 2)
    (GGHalf.TorusRank.blockIdx (m + 2) j1)) (GGHalf.omegaBlock_ne_one (m + 2)
    (GGHalf.TorusRank.blockIdx (m + 2) j1)) (hF.inj heqψ)

theorem ggQ2Lin_supp_two_J_eq (m : ℕ) (hm : 3 ≤ m)
    {ψ : Matrix.SpecialLinearGroup (Fin (m + 2 + 1)) GGHalf.F2 →* G}
    (hS : GGQTwoSetting p B Bs x L D J)
    (hF : GGHalfTorusFrame Bs L (GGHalf.halfTorus (m + 2)) ψ)
    {z : G} {t : Matrix.SpecialLinearGroup (Fin (m + 2 + 1)) GGHalf.F2} {a : ℤ}
    (hz : z = x ^ a * ψ t) (ht : t ∈ GGHalf.halfTorus (m + 2)) (ht1 : t ≠ 1)
    (hDclos : D = Subgroup.closure ({x, z} : Set G))
    (hsupp : GGHalf.supp t = 2)
    {P : Fin (m + 2)}
    (htzp : t ∈ Subgroup.zpowers (GGHalf.omegaBlock (m + 1 + 1) P))
    (hActs : GGHalfActsAs ψ.range ψ z t) :
    J = (GGHalf.slOn (m + 2 + 1) {i : Fin (m + 2 + 1) |
      i ≠ P.castSucc ∧ i ≠ P.succ}).map ψ := by
  have hcfg : GGConfig p B Bs x L D J := hS.1.1
  have hDJ : LargeEvenStdSub p B x L D J := hcfg.2.2
  obtain ⟨-, -, -, -, hKlayer, hKcomp, -⟩ := hDJ.1
  have hJleL : J ≤ L := by
    rw [hKlayer]
    exact sSup_le fun K hK => hK.1.trans inf_le_left
  have hJψ : J ≤ ψ.range := by rw [hF.range]; exact hJleL
  have hzD : z ∈ D := by
    rw [hDclos]; exact Subgroup.subset_closure (by simp)
  have hJz : J ≤ Subgroup.centralizer ({z} : Set G) := by
    have hCDz : Subgroup.centralizer (D : Set G) ≤ Subgroup.centralizer ({z} : Set G) :=
      Subgroup.centralizer_le (by
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact hzD)
    have hJCD : J ≤ L ⊓ Subgroup.centralizer (D : Set G) := by
      rw [hKlayer]
      exact sSup_le fun K hK => hK.1
    exact hJCD.trans (inf_le_right.trans hCDz)
  have hJp : commutator J = ⊤ := hKcomp.2.2.1
  have hcardJ : Nat.card J = Nat.card (Matrix.SpecialLinearGroup (Fin (m + 1)) GGHalf.F2) := by
    rcases ggQ2Lin_J_card_or hS hF hz ht ht1 hDclos with h | h
    · have h1 : Nat.card J = 1 := by
        rw [h, hsupp]
        exact CFSG.LieType.BorelTits.card_specialLinearGroup_fin_one
          (K := GaloisField 2 2)
      exact absurd (Subgroup.card_eq_one.mp h1) (GGHalf.ne_bot_of_isComponentOf hKcomp)
    · rw [h, hsupp]
      have hidx : m + 2 + 1 - 2 = m + 1 := by omega
      rw [hidx]
  exact GGHalf.eq_map_slOn_of_perfect (m := m) hm hF.inj (x := z)
    (P := P) (t := t) htzp ht1 hActs hJψ hJz hJp hcardJ

theorem ggQ2Lin_supp_two_dvd_four {n : ℕ}
    {ψ : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2 →* G}
    (hS : GGQTwoSetting p B Bs x L D J) (_hp : p = 3) (hn : 5 ≤ n)
    (hF : GGHalfTorusFrame Bs L (GGHalf.halfTorus n) ψ)
    {z : G} {t : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2} {a : ℤ}
    (hz : z = x ^ a * ψ t) (ht : t ∈ GGHalf.halfTorus n) (ht1 : t ≠ 1)
    (hDclos : D = Subgroup.closure ({x, z} : Set G))
    (hsupp : GGHalf.supp t = 2) :
    4 ∣ Nat.card (ggAutomizer J Bs) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hm : 3 ≤ m := by omega
  classical
  obtain ⟨Φ, hΦ0⟩ := GGHalf.exists_torusCoord (m + 2)
  have hΦ : ∀ j : Fin (GGHalf.TorusRank.blockCount (m + 2)),
      ((Φ (GGHalf.TorusRank.torusGen (m + 2) j) : ↥(GGHalf.halfTorus (m + 2))) :
        Matrix.SpecialLinearGroup (Fin (m + 2 + 1)) GGHalf.F2) =
        GGHalf.omegaBlock (m + 2) (GGHalf.TorusRank.blockIdx (m + 2) j) := by
    intro j
    simpa [GGHalf.TorusRank.torusGen, GGHalf.TorusRank.blockIdx] using hΦ0 j
  obtain ⟨j0, hz0⟩ :=
    GGHalf.TorusRank.exists_omegaBlock_of_supp_two (m + 2) hΦ ht hsupp
  let P : Fin (m + 2) := GGHalf.TorusRank.blockIdx (m + 2) j0
  have hPval : P.val % 2 = 0 := by
    simp only [P, GGHalf.TorusRank.blockIdx_val]
    omega
  have htzp : t ∈ Subgroup.zpowers (GGHalf.omegaBlock (m + 1 + 1) P) := by
    rcases hz0 with h | h
    · rw [h]; exact Subgroup.mem_zpowers _
    · rw [h]
      exact Subgroup.mem_zpowers_iff.mpr ⟨-1, by rw [_root_.zpow_neg, zpow_one]⟩
  have hActs : GGHalfActsAs ψ.range ψ z t := ggQ2Lin_actsAs_of_eq hS hF hz
  have hJeq := ggQ2Lin_supp_two_J_eq m hm hS hF hz ht ht1 hDclos hsupp htzp hActs
  obtain ⟨j1, j2, hj1ne, hj2ne0, hj2ne1, d1, d2, -⟩ :=
    ggQ2Lin_supp_two_weyl_data m hm hF hJeq
  have hψcomm : Commute (ψ (weylRep (m + 2) GGHalf.F2
      (GGHalf.TorusRank.blockIdx (m + 2) j1)))
      (ψ (weylRep (m + 2) GGHalf.F2 (GGHalf.TorusRank.blockIdx (m + 2) j2))) :=
    (GGHalf.TorusRank.weylRep_commute_weylRep_blocks (m + 2) hj2ne1.symm).map ψ
  have hφcomm := ggQ2Lin_supp_two_weyl_comm m d1 d2 hψcomm
  have hφne21 := ggQ2Lin_supp_two_weyl_ne m hF hj2ne1 d1 d2
  have hcard4 : Nat.card ↥(Subgroup.closure ({d1.φ, d2.φ} : Set (MulAut ↥Bs))) = 4 :=
    CFSG.GroupTheory.card_closure_pair_of_involutions d1.sq d2.sq hφcomm d1.ne d2.ne hφne21
  have hHle : Subgroup.closure ({d1.φ, d2.φ} : Set (MulAut ↥Bs)) ≤ ggAutomizer J Bs := by
    rw [Subgroup.closure_le]
    rintro φ (rfl | rfl)
    · exact d1.mem
    · exact d2.mem
  have hdvd := Subgroup.card_dvd_of_le hHle
  rwa [hcard4] at hdvd

theorem ggQ2Lin_fix_le_one {n : ℕ}
    {ψ : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2 →* G}
    (hS : GGQTwoSetting p B Bs x L D J) (hp : p = 3) (hn : 5 ≤ n)
    (hF : GGHalfTorusFrame Bs L (GGHalf.halfTorus n) ψ)
    (hBs : Bs = Subgroup.zpowers x ⊔ (GGHalf.halfTorus n).map ψ)
    {z : G} {t : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2} {a : ℤ}
    (hz : z = x ^ a * ψ t) (ht : t ∈ GGHalf.halfTorus n) (ht1 : t ≠ 1)
    (hDclos : D = Subgroup.closure ({x, z} : Set G))
    (hguard : ¬ 4 ∣ Nat.card (ggAutomizer J Bs)) :
    n + 1 - GGHalf.supp t ≤ 1 := by
  classical
  obtain ⟨Φ, hΦ0⟩ := GGHalf.exists_torusCoord n
  have hΦ : ∀ j : Fin (GGHalf.TorusRank.blockCount n),
      ((Φ (GGHalf.TorusRank.torusGen n j) : ↥(GGHalf.halfTorus n)) :
        Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2) =
        GGHalf.omegaBlock n (GGHalf.TorusRank.blockIdx n j) := by
    intro j
    simpa [GGHalf.TorusRank.torusGen, GGHalf.TorusRank.blockIdx] using hΦ0 j
  let v := Φ.symm ⟨t, ht⟩
  have htv : ((Φ v : ↥(GGHalf.halfTorus n)) :
      Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2) = t := by
    change ((Φ (Φ.symm ⟨t, ht⟩) : ↥(GGHalf.halfTorus n)) :
      Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2) = t
    rw [MulEquiv.apply_symm_apply]
  have hsuppN := GGHalf.TorusRank.supp_torusCoord n hΦ v
  rw [htv] at hsuppN
  let N := (Finset.univ.filter fun j : Fin (GGHalf.TorusRank.blockCount n) => v j ≠ 1).card
  have hvne : v ≠ 1 := by
    intro hv1
    apply ht1
    rw [← htv, hv1]
    simp
  have hNpos : 0 < N := by
    obtain ⟨j, hj⟩ : ∃ j : Fin (GGHalf.TorusRank.blockCount n), v j ≠ 1 := by
      by_contra h
      push Not at h
      exact hvne (funext h)
    change 0 < (Finset.univ.filter fun j : Fin (GGHalf.TorusRank.blockCount n) => v j ≠ 1).card
    exact Finset.card_pos.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
  by_contra hle
  have hs2 : 2 ≤ n + 1 - GGHalf.supp t := by omega
  have hsupp_even : GGHalf.supp t = 2 * N := by simpa [N] using hsuppN
  by_cases hsupp2 : GGHalf.supp t = 2
  · exact hguard (ggQ2Lin_supp_two_dvd_four hS hp hn hF hz ht ht1 hDclos hsupp2)
  · have hsupp4 : 4 ≤ GGHalf.supp t := by omega
    by_cases hs3 : 3 ≤ n + 1 - GGHalf.supp t
    · exact ggQ2Lin_fix_ge_three_impossible hS hF hz ht hDclos hsupp4 hs3
    · have hs_eq2 : n + 1 - GGHalf.supp t = 2 := by omega
      exact ggQ2Lin_fix_two_impossible hS hp hn hF hBs hz ht hDclos hs_eq2

end CFSG.StandardType
end
