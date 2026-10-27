module

public import CFSG.LocalAnalysis.StandardType.GGQTwoVACLinCell
public import CFSG.LocalAnalysis.StandardType.GGQTwoVACLinFix
public import CFSG.LocalAnalysis.StandardType.GGQTwoOriginalNormalizerLift
public import CFSG.LocalAnalysis.StandardType.GGQTwoLemma895
public import CFSG.LocalAnalysis.StandardType.GGHalfFrameGF2
public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenA3SL8Model
public import CFSG.LocalAnalysis.StandardType.GGHalfWeylTorusCoord
public import CFSG.LocalAnalysis.StandardType.GGHalfBlockPerm
public import CFSG.Mathlib.GroupTheory.ConjCentralizer
public import CFSG.LocalAnalysis.StandardType.GGE0ShapeConjAux
public import CFSG.GroupTheory.InvolutionPair

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal.SpecialLinear Matrix
open CFSG.StandardType.CoordSL
open CFSG.StandardType.GGHalf

namespace GGQ2Lin

@[expose] def R (n : ℕ) : ℕ := (n + 1) / 2

@[expose] def Q (n : ℕ) : ℕ := n + 1 - 2 * R n

theorem two_mul_R_le (n : ℕ) : 2 * R n ≤ n + 1 := by
  unfold R
  exact Nat.mul_div_le (n + 1) 2

theorem two_mul_R_add_Q (n : ℕ) : 2 * R n + Q n = n + 1 := by
  unfold Q
  exact Nat.add_sub_cancel' (two_mul_R_le n)

theorem Q_le_one (n : ℕ) : Q n ≤ 1 := by
  have h := Nat.div_add_mod (n + 1) 2
  have hlt := Nat.mod_lt (n + 1) (by norm_num : 0 < 2)
  unfold Q R
  omega

@[expose] def pairIdx (n : ℕ) (i : Fin (R n)) : Fin n :=
  ⟨2 * i.val, by have := i.isLt; unfold R at this; omega⟩

theorem pairIdx_castSucc (n : ℕ) (i : Fin (R n)) :
    (pairIdx n i).castSucc = ⟨2 * i.val, by have := i.isLt; unfold R at this; omega⟩ :=
  Fin.ext rfl

theorem pairIdx_succ (n : ℕ) (i : Fin (R n)) :
    (pairIdx n i).succ = ⟨2 * i.val + 1, by have := i.isLt; unfold R at this; omega⟩ :=
  Fin.ext rfl

@[expose] def pairCoord (n : ℕ) (i : Fin (R n)) (a : Fin 2) : Fin (n + 1) :=
  ⟨2 * i.val + a.val, by have := i.isLt; have := a.isLt; unfold R at *; omega⟩

@[expose] def restCoord (n : ℕ) (j : Fin (Q n)) : Fin (n + 1) :=
  ⟨2 * R n + j.val, by have := j.isLt; have := two_mul_R_add_Q n; omega⟩

@[expose] def aDim (a : Fin 2) : Fin (rootPB phi3).dim :=
  ⟨a.val, by rw [rootPB_phi3_dim]; exact a.isLt⟩

noncomputable def pairEquiv (n : ℕ) : Fin 2 × Fin (R n) ≃ Fin (2 * R n) :=
  ((Equiv.prodComm (α := Fin 2) (β := Fin (R n))).trans
    (finProdFinEquiv (m := R n) (n := 2))).trans
    (finCongr (Nat.mul_comm (R n) 2))

theorem pairEquiv_val (n : ℕ) (a : Fin 2) (i : Fin (R n)) :
    (pairEquiv n (a, i)).val = 2 * i.val + a.val := by
  unfold pairEquiv
  simp only [Equiv.trans_apply, finCongr_apply, Fin.val_cast]
  rw [show (Equiv.prodComm (α := Fin 2) (β := Fin (R n))) (a, i) = (i, a) from rfl]
  simp [finProdFinEquiv]
  omega

theorem pairEquiv_add_lt (n : ℕ) (i : Fin (R n)) (a : Fin 2) :
    2 * i.val + a.val < 2 * R n := by
  have := i.isLt; have := a.isLt; omega

noncomputable def epsTwo (n : ℕ) :
    Fin (n + 1) ≃ (Fin 2 × Fin (R n)) ⊕ Fin (Q n) :=
  (finCongr (two_mul_R_add_Q n).symm).trans
    ((finSumFinEquiv (m := 2 * R n) (n := Q n)).symm.trans
      (Equiv.sumCongr (pairEquiv n).symm (Equiv.refl _)))

theorem epsTwo_inl (n : ℕ) (i : Fin (R n)) (a : Fin 2) :
    epsTwo n (pairCoord n i a) = Sum.inl (a, i) := by
  unfold epsTwo pairCoord
  change ((finSumFinEquiv (m := 2 * R n) (n := Q n)).symm.trans
      (Equiv.sumCongr (pairEquiv n).symm (Equiv.refl _)))
      ((finCongr (two_mul_R_add_Q n).symm) ⟨2 * i.val + a.val, _⟩) = _
  rw [Equiv.trans_apply, show (finCongr (two_mul_R_add_Q n).symm :
      Fin (n + 1) ≃ Fin (2 * R n + Q n)) ⟨2 * i.val + a.val, _⟩ =
      Fin.castAdd (Q n) ⟨2 * i.val + a.val, pairEquiv_add_lt n i a⟩ from by
    apply Fin.ext; simp [Fin.castAdd, Fin.cast]]
  have hsum : (finSumFinEquiv (m := 2 * R n) (n := Q n)).symm
      (Fin.castAdd (Q n) ⟨2 * i.val + a.val, pairEquiv_add_lt n i a⟩) =
      Sum.inl ⟨2 * i.val + a.val, pairEquiv_add_lt n i a⟩ :=
    (Equiv.symm_apply_eq (finSumFinEquiv (m := 2 * R n) (n := Q n))).mpr
      (by rw [finSumFinEquiv_apply_left])
  rw [hsum, Equiv.sumCongr_apply, Sum.map_inl]
  congr 1
  exact (Equiv.symm_apply_eq (pairEquiv n)).mpr (Fin.ext (by rw [pairEquiv_val]))

theorem epsTwo_inr (n : ℕ) (j : Fin (Q n)) :
    epsTwo n (restCoord n j) = Sum.inr j := by
  unfold epsTwo restCoord
  change ((finSumFinEquiv (m := 2 * R n) (n := Q n)).symm.trans
      (Equiv.sumCongr (pairEquiv n).symm (Equiv.refl _)))
      ((finCongr (two_mul_R_add_Q n).symm) ⟨2 * R n + j.val, _⟩) = _
  rw [Equiv.trans_apply, show (finCongr (two_mul_R_add_Q n).symm :
      Fin (n + 1) ≃ Fin (2 * R n + Q n)) ⟨2 * R n + j.val, _⟩ =
      Fin.natAdd (2 * R n) j from by
    apply Fin.ext; simp [Fin.natAdd]]
  have hsum : (finSumFinEquiv (m := 2 * R n) (n := Q n)).symm
      (Fin.natAdd (2 * R n) j) = Sum.inr j :=
    (Equiv.symm_apply_eq (finSumFinEquiv (m := 2 * R n) (n := Q n))).mpr
      (by rw [finSumFinEquiv_apply_right])
  rw [hsum, Equiv.sumCongr_apply, Sum.map_inr, Equiv.refl_apply]

noncomputable def eps (n : ℕ) :
    Fin (n + 1) ≃ (Fin (rootPB phi3).dim × Fin (R n)) ⊕ Fin (Q n) :=
  (epsTwo n).trans (Equiv.sumCongr
    (Equiv.prodCongr (finCongr rootPB_phi3_dim).symm (Equiv.refl (Fin (R n))))
    (Equiv.refl (Fin (Q n))))

theorem eps_inl (n : ℕ) (i : Fin (R n)) (a : Fin 2) :
    eps n (pairCoord n i a) = Sum.inl (aDim a, i) := by
  unfold eps
  rw [Equiv.trans_apply, epsTwo_inl, Equiv.sumCongr_apply, Sum.map_inl]
  congr 1

theorem eps_inr (n : ℕ) (j : Fin (Q n)) : eps n (restCoord n j) = Sum.inr j := by
  unfold eps
  rw [Equiv.trans_apply, epsTwo_inr, Equiv.sumCongr_apply, Sum.map_inr, Equiv.refl_apply]

theorem eps_symm_inl (n : ℕ) (i : Fin (R n)) (a : Fin 2) :
    (eps n).symm (Sum.inl (aDim a, i)) = pairCoord n i a :=
  (Equiv.symm_apply_eq (eps n)).mpr (eps_inl n i a).symm

theorem eps_symm_inr (n : ℕ) (j : Fin (Q n)) :
    (eps n).symm (Sum.inr j) = restCoord n j :=
  (Equiv.symm_apply_eq (eps n)).mpr (eps_inr n j).symm


theorem natCard_F2 : Nat.card F2 = 2 := by
  rw [GaloisField.card 2 1 (by omega)]
  norm_num

theorem rootMat_apply (a b : Fin (rootPB phi3).dim) :
    rootMat phi3 a b = if a.val = 0 ∧ b.val = 0 then 0 else 1 :=
  rootMat_apply_of_card_two (K := F2) natCard_F2 (g := phi3) rootPB_phi3_dim a b

theorem fin_two_cases (b : Fin (rootPB phi3).dim) : b = aDim 0 ∨ b = aDim 1 := by
  have hb : b.val < 2 := by simpa [rootPB_phi3_dim] using b.isLt
  rcases Nat.lt_succ_iff_lt_or_eq.mp hb with h | h
  · left
    apply Fin.ext
    rw [show b.val = 0 from by omega]
    simp [aDim]
  · right
    apply Fin.ext
    rw [h]
    simp [aDim]

theorem basis_aDim_zero : (rootPB phi3).basis (aDim 0) = 1 := by
  rw [PowerBasis.basis_eq_pow]
  simp [aDim]

theorem basis_aDim_one : (rootPB phi3).basis (aDim 1) = AdjoinRoot.root phi3 := by
  rw [PowerBasis.basis_eq_pow]
  rw [show (aDim 1 : Fin (rootPB phi3).dim).val = 1 from rfl, pow_one]
  unfold rootPB
  exact AdjoinRoot.powerBasis_gen _

theorem root_mul_basis_zero :
    AdjoinRoot.root phi3 * (rootPB phi3).basis (aDim 0) = (rootPB phi3).basis (aDim 1) := by
  apply (rootPB phi3).basis.repr.injective
  ext b
  have hroot : (rootPB phi3).basis.repr (AdjoinRoot.root phi3 *
      (rootPB phi3).basis (aDim 0)) b = rootMat phi3 b (aDim 0) := by
    rw [← Algebra.leftMulMatrix_eq_repr_mul (rootPB phi3).basis (AdjoinRoot.root phi3) b (aDim 0)]
    rfl
  rw [hroot, rootMat_apply, Module.Basis.repr_self, Finsupp.single_apply]
  rcases fin_two_cases b with rfl | rfl <;> simp [aDim]

theorem root_mul_basis_one :
    AdjoinRoot.root phi3 * (rootPB phi3).basis (aDim 1) =
      (rootPB phi3).basis (aDim 0) + (rootPB phi3).basis (aDim 1) := by
  apply (rootPB phi3).basis.repr.injective
  ext b
  have hroot : (rootPB phi3).basis.repr (AdjoinRoot.root phi3 *
      (rootPB phi3).basis (aDim 1)) b = rootMat phi3 b (aDim 1) := by
    rw [← Algebra.leftMulMatrix_eq_repr_mul (rootPB phi3).basis (AdjoinRoot.root phi3) b (aDim 1)]
    rfl
  rw [hroot, rootMat_apply]
  simp only [map_add, Module.Basis.repr_self, Finsupp.add_apply, Finsupp.single_apply]
  rcases fin_two_cases b with rfl | rfl <;> simp [aDim]

theorem frameCoords_pair_zero (n : ℕ) (i : Fin (R n)) :
    frameCoords phi3 (eps n) (Pi.single i (1 : AdjoinRoot phi3),
      (0 : Fin (Q n) → F2)) = Pi.single (pairCoord n i 0) 1 := by
  rw [← basis_aDim_zero]
  rw [frameCoords_single_basis]
  rw [eps_symm_inl]

theorem frameCoords_pair_one (n : ℕ) (i : Fin (R n)) :
    frameCoords phi3 (eps n) (Pi.single i ((rootPB phi3).basis (aDim 1)),
      (0 : Fin (Q n) → F2)) = Pi.single (pairCoord n i 1) 1 := by
  rw [frameCoords_single_basis]
  rw [eps_symm_inl]

theorem frameCoords_rest (n : ℕ) (j : Fin (Q n)) :
    frameCoords phi3 (eps n) ((0 : Fin (R n) → AdjoinRoot phi3), Pi.single j 1) =
      Pi.single (restCoord n j) 1 := by
  funext y
  by_cases hy : y = restCoord n j
  · subst hy
    rw [frameCoords_apply, eps_inr]
    simp
  · have hε : eps n y ≠ Sum.inr j := fun h =>
      hy ((eps n).injective (h.trans (eps_inr n j).symm))
    rcases h : eps n y with ⟨a, i⟩ | j'
    · simp [frameCoords_apply, h, Pi.single_apply, hy]
    · have hjj : j' ≠ j := fun hh => hε (by rw [h, hh])
      simp [frameCoords_apply, h, Pi.single_apply, hjj, hy]

theorem transvection_self_mul {N : ℕ} {i j : Fin N} (hij : i ≠ j) :
    SpecialLinearGroup.transvection hij (1 : F2) *
      SpecialLinearGroup.transvection hij 1 = 1 := by
  rw [← SpecialLinearGroup.transvection_add, show (1 : F2) + 1 = 0 from by
    rw [one_add_one_eq_two, gf2_two]]
  exact SpecialLinearGroup.transvection_coeff_zero hij

theorem omegaBlock_eq_mul (n : ℕ) (k : Fin n) :
    omegaBlock n k =
      SpecialLinearGroup.transvection
          (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne (1 : F2) *
        SpecialLinearGroup.transvection
          (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne.symm 1 := by
  have hneg : (-1 : F2) = 1 := by
    rw [neg_eq_iff_add_eq_zero, one_add_one_eq_two, gf2_two]
  rw [omegaBlock, CFSG.LieType.Universal.SpecialLinear.weylRep, hneg]
  rw [mul_assoc (SpecialLinearGroup.transvection _ (1 : F2) *
      SpecialLinearGroup.transvection _ 1) _ _,
    transvection_self_mul (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne, mul_one]

theorem omegaBlock_coe_sum (n : ℕ) (k : Fin n) :
    ((omegaBlock n k : SpecialLinearGroup (Fin (n + 1)) F2) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) F2) =
      1 + Matrix.single k.castSucc k.succ (1 : F2) +
        Matrix.single k.succ k.castSucc 1 + Matrix.single k.castSucc k.castSucc 1 := by
  have hne : k.castSucc ≠ k.succ := (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne
  rw [omegaBlock_eq_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe]
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul]
  rw [Matrix.single_mul_single_same]
  simp only [one_mul]
  abel

theorem omegaBlock_mulVec (n : ℕ) (k : Fin n) (v : Fin (n + 1) → F2) (i : Fin (n + 1)) :
    (((omegaBlock n k : SpecialLinearGroup (Fin (n + 1)) F2) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) F2) *ᵥ v) i =
      if i = k.castSucc then v k.succ
      else if i = k.succ then v k.castSucc + v k.succ
      else v i := by
  rw [omegaBlock_coe_sum]
  simp only [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec, Pi.add_apply,
    Function.update_apply]
  simp
  have hne : k.castSucc ≠ k.succ := (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne
  by_cases h0 : i = k.castSucc
  · subst h0
    simp only [if_neg hne]
    split_ifs <;> ring_nf <;> rw [show (2 : F2) = 0 from gf2_two, mul_zero, zero_add]
  · by_cases h1 : i = k.succ
    · subst h1
      simp only [if_neg hne.symm]
      split_ifs <;> ring_nf
    · simp [h0, h1]

@[expose] noncomputable def blockGen (n : ℕ) (i : Fin (R n)) :
    SpecialLinearGroup (Fin (n + 1)) F2 := omegaBlock n (pairIdx n i)

theorem pairCoord_inj {n : ℕ} {i i' : Fin (R n)} {a a' : Fin 2}
    (h : pairCoord n i a = pairCoord n i' a') : i = i' ∧ a = a' := by
  have hv := congrArg Fin.val h
  simp [pairCoord] at hv
  constructor <;> apply Fin.ext <;> omega

theorem blockGen_castSucc (n : ℕ) (i : Fin (R n)) :
    (pairIdx n i).castSucc = pairCoord n i 0 := by
  rw [pairIdx_castSucc]
  apply Fin.ext
  simp [pairCoord]

theorem blockGen_succ (n : ℕ) (i : Fin (R n)) :
    (pairIdx n i).succ = pairCoord n i 1 := by
  rw [pairIdx_succ]
  apply Fin.ext
  simp [pairCoord]

theorem blockGen_comm (n : ℕ) {i j : Fin (R n)} (hij : i ≠ j) :
    Commute (blockGen n i) (blockGen n j) := by
  rcases lt_or_gt_of_ne hij with h | h
  · have hle : (pairIdx n i).val + 2 ≤ (pairIdx n j).val := by
      simp [pairIdx]; omega
    exact omegaBlock_comm (n := n) hle
  · have hle : (pairIdx n j).val + 2 ≤ (pairIdx n i).val := by
      simp [pairIdx]; omega
    exact (omegaBlock_comm (n := n) hle).symm

theorem blockGen_mulVec_zero (n : ℕ) (i : Fin (R n)) :
    ((blockGen n i : SpecialLinearGroup (Fin (n + 1)) F2) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) F2) *ᵥ
      Pi.single (pairCoord n i 0) (1 : F2) = Pi.single (pairCoord n i 1) 1 := by
  funext x
  rw [blockGen, omegaBlock_mulVec, blockGen_castSucc, blockGen_succ]
  by_cases h0 : x = pairCoord n i 0
  · subst h0
    rw [if_pos rfl]
    have hne : pairCoord n i 0 ≠ pairCoord n i 1 := by
      intro h
      have := congrArg Fin.val h
      simp [pairCoord] at this
    simp [hne]
  · rw [if_neg h0]
    by_cases h1 : x = pairCoord n i 1
    · subst h1
      rw [if_pos rfl]
      have h01 : pairCoord n i 1 ≠ pairCoord n i 0 := by
        intro h
        have := congrArg Fin.val h
        simp [pairCoord] at this
      simp [h01]
    · rw [if_neg h1]
      simp [h0, h1]

theorem blockGen_mulVec_one (n : ℕ) (i : Fin (R n)) :
    ((blockGen n i : SpecialLinearGroup (Fin (n + 1)) F2) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) F2) *ᵥ
      Pi.single (pairCoord n i 1) (1 : F2) =
      Pi.single (pairCoord n i 0) 1 + Pi.single (pairCoord n i 1) 1 := by
  funext x
  rw [blockGen, omegaBlock_mulVec, blockGen_castSucc, blockGen_succ]
  by_cases h0 : x = pairCoord n i 0
  · subst h0
    rw [if_pos rfl]
    have hne : pairCoord n i 0 ≠ pairCoord n i 1 := by
      intro h
      have := congrArg Fin.val h
      simp [pairCoord] at this
    simp [hne]
  · rw [if_neg h0]
    by_cases h1 : x = pairCoord n i 1
    · subst h1
      rw [if_pos rfl]
      have h01 : pairCoord n i 1 ≠ pairCoord n i 0 := by
        intro h
        have := congrArg Fin.val h
        simp [pairCoord] at this
      simp [h01]
    · rw [if_neg h1]
      simp [h0, h1]

theorem blockGen_mulVec_eq_self_of_support (n : ℕ) (j : Fin (R n))
    {v : Fin (n + 1) → F2}
    (hv : ∀ x, x = pairCoord n j 0 ∨ x = pairCoord n j 1 → v x = 0) :
    ((blockGen n j : SpecialLinearGroup (Fin (n + 1)) F2) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) F2) *ᵥ v = v := by
  funext x
  rw [blockGen, omegaBlock_mulVec, blockGen_castSucc, blockGen_succ]
  by_cases h0 : x = pairCoord n j 0
  · rw [if_pos h0]
    rw [hv (pairCoord n j 1) (Or.inr rfl), hv x (Or.inl h0)]
  · rw [if_neg h0]
    by_cases h1 : x = pairCoord n j 1
    · rw [if_pos h1]
      rw [hv (pairCoord n j 0) (Or.inl rfl), hv (pairCoord n j 1) (Or.inr rfl), zero_add,
        hv x (Or.inr h1)]
    · rw [if_neg h1]

theorem blockGen_mulVec_pairCoord_of_ne (n : ℕ) {i i0 : Fin (R n)} (hne : i ≠ i0)
    (a : Fin 2) :
    ((blockGen n i : SpecialLinearGroup (Fin (n + 1)) F2) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) F2) *ᵥ
      Pi.single (pairCoord n i0 a) (1 : F2) = Pi.single (pairCoord n i0 a) 1 := by
  apply blockGen_mulVec_eq_self_of_support
  intro x hx
  have hx' : x ≠ pairCoord n i0 a := by
    rcases hx with h | h <;> rw [h] <;> intro hh <;> exact hne (pairCoord_inj hh).1
  simp [hx']

theorem blockGen_mulVec_restCoord (n : ℕ) (i : Fin (R n)) (j : Fin (Q n)) :
    ((blockGen n i : SpecialLinearGroup (Fin (n + 1)) F2) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) F2) *ᵥ
      Pi.single (restCoord n j) (1 : F2) = Pi.single (restCoord n j) 1 := by
  apply blockGen_mulVec_eq_self_of_support
  intro x hx
  have hx' : x ≠ restCoord n j := by
    rcases hx with h | h <;> rw [h]
    · intro hh
      have := congrArg Fin.val hh
      simp [pairCoord, restCoord] at this
      omega
    · intro hh
      have := congrArg Fin.val hh
      simp [pairCoord, restCoord] at this
      omega
  simp [hx']

theorem mat_eq_of_mulVec_single {d : ℕ} {M N : Matrix (Fin d) (Fin d) F2}
    (h : ∀ x, M *ᵥ Pi.single x (1 : F2) = N *ᵥ Pi.single x 1) : M = N := by
  ext x y
  have hh := congrFun (h y) x
  simpa [Matrix.mulVec_single, Matrix.col_apply] using hh

theorem nsMat_single_mulVec_single (n : ℕ) (i i0 : Fin (R n)) (u : AdjoinRoot phi3) :
    SLNS.nsMat (eps n) (rootMat phi3) (Pi.single i 1) *ᵥ
      frameCoords phi3 (eps n) (Pi.single i0 u, (0 : Fin (Q n) → F2)) =
      frameCoords phi3 (eps n)
        (Pi.single i0 ((if i0 = i then AdjoinRoot.root phi3 else 1) * u),
          (0 : Fin (Q n) → F2)) := by
  rw [nsMat_mulVec_frameCoords]
  congr 1
  apply Prod.ext
  · funext i'
    by_cases h0 : i' = i0
    · rw [h0]
      by_cases hi : i0 = i
      · rw [hi]; simp
      · simp [hi]
    · by_cases hi : i' = i
      · rw [hi]
        have hne : i ≠ i0 := fun h => h0 (hi.trans h)
        simp [hne]
      · simp [h0, hi]
  · rfl

theorem nsMat_single_mulVec_rest (n : ℕ) (i : Fin (R n)) (j : Fin (Q n)) :
    SLNS.nsMat (eps n) (rootMat phi3) (Pi.single i 1) *ᵥ
      frameCoords phi3 (eps n) ((0 : Fin (R n) → AdjoinRoot phi3), Pi.single j 1) =
      frameCoords phi3 (eps n) ((0 : Fin (R n) → AdjoinRoot phi3), Pi.single j 1) := by
  rw [nsMat_mulVec_frameCoords]
  congr 1
  apply Prod.ext
  · funext i'; simp
  · rfl

theorem ggQ2Lin_single_add_basis (n : ℕ) (i₀ : Fin (R n)) :
    ((Pi.single i₀ ((rootPB phi3).basis (aDim 0) + (rootPB phi3).basis (aDim 1)) :
        Fin (R n) → AdjoinRoot phi3), (0 : Fin (Q n) → F2)) =
      ((Pi.single i₀ ((rootPB phi3).basis (aDim 0)) : Fin (R n) → AdjoinRoot phi3),
        (0 : Fin (Q n) → F2)) +
      ((Pi.single i₀ ((rootPB phi3).basis (aDim 1)) : Fin (R n) → AdjoinRoot phi3),
        (0 : Fin (Q n) → F2)) := by
  ext <;> simp [Pi.single_add]

theorem nsSL_single_eq_blockGen (n : ℕ) (i : Fin (R n)) :
    SLNS.nsSL (eps n) det_rootMat_phi3 (Pi.single i 1) = blockGen n i := by
  apply Subtype.ext
  change SLNS.nsMat (eps n) (rootMat phi3) (Pi.single i 1) =
    ((blockGen n i : SpecialLinearGroup (Fin (n + 1)) F2) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) F2)
  apply mat_eq_of_mulVec_single
  intro y
  rcases hε : eps n y with ⟨a, i0⟩ | j
  · rcases fin_two_cases a with ha | ha
    · rw [ha] at hε
      have hy : y = pairCoord n i0 0 := by
        rw [← eps_symm_inl n i0 0, ← hε, Equiv.symm_apply_apply]
      rw [hy, ← frameCoords_pair_zero, nsMat_single_mulVec_single]
      by_cases hi : i = i0
      · rw [hi]
        rw [if_pos rfl, mul_one]
        rw [frameCoords_pair_zero, blockGen_mulVec_zero, ← basis_aDim_one, frameCoords_pair_one]
      · have hne : i0 ≠ i := fun h => hi h.symm
        rw [if_neg hne, one_mul]
        rw [frameCoords_pair_zero, blockGen_mulVec_pairCoord_of_ne n hi 0]
    · rw [ha] at hε
      have hy : y = pairCoord n i0 1 := by
        rw [← eps_symm_inl n i0 1, ← hε, Equiv.symm_apply_apply]
      rw [hy, ← frameCoords_pair_one, nsMat_single_mulVec_single]
      by_cases hi : i = i0
      · rw [hi]
        rw [if_pos rfl]
        rw [root_mul_basis_one, frameCoords_pair_one, blockGen_mulVec_one]
        have hpair := ggQ2Lin_single_add_basis n i0
        rw [hpair, map_add, basis_aDim_zero, frameCoords_pair_zero, frameCoords_pair_one]
      · have hne : i0 ≠ i := fun h => hi h.symm
        rw [if_neg hne, one_mul]
        rw [frameCoords_pair_one, blockGen_mulVec_pairCoord_of_ne n hi 1]
  · have hy : y = restCoord n j := by
      rw [← eps_symm_inr n j, ← hε, Equiv.symm_apply_apply]
    rw [hy, ← frameCoords_rest, nsMat_single_mulVec_rest, frameCoords_rest]
    exact (blockGen_mulVec_restCoord n i j).symm


noncomputable local instance halfTorusCommMonoid (n : ℕ) : CommMonoid ↥(halfTorus n) :=
  { (inferInstance : Monoid ↥(halfTorus n)) with
    mul_comm := fun a b => Subtype.ext (halfTorus_comm a.2 b.2) }

theorem blockGen_mem (n : ℕ) (i : Fin (R n)) : blockGen n i ∈ halfTorus n :=
  Subgroup.subset_closure ⟨pairIdx n i, by simp [pairIdx], rfl⟩

@[expose] noncomputable def bg (n : ℕ) (j : Fin (R n)) : ↥(halfTorus n) :=
  ⟨blockGen n j, blockGen_mem n j⟩

theorem nsSL_eq_prod (n : ℕ) (k : Fin (R n) → ℕ) :
    SLNS.nsSL (eps n) det_rootMat_phi3 k =
      ↑(Finset.univ.prod (fun j => (bg n j : ↥(halfTorus n)) ^ (k j))) := by
  have hdecomp : k = ∑ j : Fin (R n), k j • Pi.single j (1 : ℕ) := by
    funext i
    rw [Finset.sum_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [Pi.smul_apply, Pi.single_eq_of_ne' hj, smul_zero]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  have hsingle : ∀ j : Fin (R n),
      SLNS.nsSL (eps n) det_rootMat_phi3 (Pi.single j 1) =
        (↑(bg n j : ↥(halfTorus n)) :
          SpecialLinearGroup (Fin (n + 1)) F2) := by
    intro j
    exact nsSL_single_eq_blockGen n j
  have hgen : ∀ t : Finset (Fin (R n)),
      SLNS.nsSL (eps n) det_rootMat_phi3 (t.sum fun j => k j • Pi.single j (1 : ℕ)) =
        ↑(t.prod fun j => (bg n j : ↥(halfTorus n)) ^ (k j)) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp [SLNS.nsSL_zero]
    | insert j t hj ih =>
        rw [Finset.sum_insert hj, Finset.prod_insert hj, ← SLNS.nsSL_mul, ih,
          ← SLNS.nsSL_pow, hsingle j, ← Subgroup.coe_pow, ← Subgroup.coe_mul]
  conv_lhs => rw [hdecomp]
  exact hgen Finset.univ

theorem tZero_eq_prod (n : ℕ) :
    SLNS.nsSL (eps n) det_rootMat_phi3 (fun _ => 1) =
      ↑(Finset.univ.prod (fun j => (bg n j : ↥(halfTorus n)))) := by
  simpa using nsSL_eq_prod n (fun _ => 1)

theorem tZero_mem (n : ℕ) :
    SLNS.nsSL (eps n) det_rootMat_phi3 (fun _ => 1) ∈ halfTorus n := by
  rw [tZero_eq_prod]
  exact (Finset.univ.prod (fun j => (bg n j : ↥(halfTorus n)))).2

theorem supp_tZero (n : ℕ) : supp (SLNS.nsSL (eps n) det_rootMat_phi3 (fun _ => 1)) = 2 * R n := by
  rw [supp_nsSL]
  congr 1
  rw [show (Finset.univ.filter fun i : Fin (R n) => (fun _ => 1) i % 3 ≠ 0) = Finset.univ from by
    apply Finset.filter_true_of_mem
    intro i _
    norm_num]
  simp


noncomputable def torusCoord (n : ℕ) :
    (Fin (R n) → Multiplicative (ZMod 3)) ≃* ↥(halfTorus n) :=
  (exists_torusCoord n).choose

theorem torusCoord_gen (n : ℕ) (j : Fin (R n)) :
    ((torusCoord n (Pi.mulSingle j (Multiplicative.ofAdd (1 : ZMod 3))) : ↥(halfTorus n)) :
      SpecialLinearGroup (Fin (n + 1)) F2) = blockGen n j :=
  (exists_torusCoord n).choose_spec j

theorem ofAdd_one_pow_mul (x : Multiplicative (ZMod 3)) :
    (Multiplicative.ofAdd (1 : ZMod 3)) ^ (Multiplicative.toAdd x).val = x := by
  rw [show (Multiplicative.ofAdd (1 : ZMod 3)) ^ (Multiplicative.toAdd x).val =
      Multiplicative.ofAdd (((Multiplicative.toAdd x).val : ZMod 3)) from by
    induction (Multiplicative.toAdd x).val with
    | zero => simp
    | succ n ih => rw [pow_succ, ih]; simp]
  rw [ZMod.natCast_zmod_val]
  rfl

theorem prod_gen_eq (n : ℕ) (v : Fin (R n) → Multiplicative (ZMod 3)) :
    v = ∏ j : Fin (R n),
      (Pi.mulSingle j (Multiplicative.ofAdd (1 : ZMod 3))) ^
        (Multiplicative.toAdd (v j)).val := by
  funext k
  rw [Finset.prod_apply]
  rw [Finset.prod_eq_single k]
  · simp only [Pi.pow_apply, Pi.mulSingle_apply]
    exact (ofAdd_one_pow_mul (v k)).symm
  · intro b _ hb
    rw [Pi.pow_apply, Pi.mulSingle_apply, if_neg (fun h => hb h.symm)]
    simp
  · intro hk; exact absurd (Finset.mem_univ k) hk

theorem torusCoord_apply_prod (n : ℕ) (v : Fin (R n) → Multiplicative (ZMod 3)) :
    (torusCoord n v : SpecialLinearGroup (Fin (n + 1)) F2) =
      ↑(Finset.univ.prod (fun j =>
        (bg n j : ↥(halfTorus n)) ^
          (Multiplicative.toAdd (v j)).val)) := by
  conv_lhs => rw [prod_gen_eq n v]
  rw [map_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  rw [map_pow]
  congr 1
  apply Subtype.ext
  exact torusCoord_gen n j

@[expose] def flip2 (a : Fin 2) : Fin 2 := if a = 0 then 1 else 0

theorem flip2_zero : flip2 0 = 1 := by simp [flip2]

theorem flip2_one : flip2 1 = 0 := by simp [flip2]

theorem flip2_invol (a : Fin 2) : flip2 (flip2 a) = a := by
  fin_cases a <;> simp [flip2]

@[expose] def swapPair (n : ℕ) (S : Finset (Fin (R n))) (p : Fin 2 × Fin (R n)) :
    Fin 2 × Fin (R n) :=
  (if p.2 ∈ S then flip2 p.1 else p.1, p.2)

theorem swapPair_invol (n : ℕ) (S : Finset (Fin (R n))) :
    Function.Involutive (swapPair n S) := by
  intro p
  obtain ⟨a, i⟩ := p
  by_cases h : i ∈ S <;> simp [swapPair, h, flip2_invol]

@[expose] noncomputable def swapPairEquiv (n : ℕ) (S : Finset (Fin (R n))) :
    (Fin 2 × Fin (R n)) ≃ (Fin 2 × Fin (R n)) :=
  Function.Involutive.toPerm (swapPair n S) (swapPair_invol n S)

theorem swapPairEquiv_apply (n : ℕ) (S : Finset (Fin (R n))) (p : Fin 2 × Fin (R n)) :
    swapPairEquiv n S p = swapPair n S p := rfl

@[expose] noncomputable def swapSumEquiv (n : ℕ) (S : Finset (Fin (R n))) :
    ((Fin 2 × Fin (R n)) ⊕ Fin (Q n)) ≃ ((Fin 2 × Fin (R n)) ⊕ Fin (Q n)) :=
  Equiv.sumCongr (swapPairEquiv n S) (Equiv.refl _)

theorem epsTwo_symm_inl (n : ℕ) (i : Fin (R n)) (a : Fin 2) :
    (epsTwo n).symm (Sum.inl (a, i)) = pairCoord n i a :=
  (Equiv.symm_apply_eq (epsTwo n)).mpr (epsTwo_inl n i a).symm

theorem epsTwo_symm_inr (n : ℕ) (j : Fin (Q n)) :
    (epsTwo n).symm (Sum.inr j) = restCoord n j :=
  (Equiv.symm_apply_eq (epsTwo n)).mpr (epsTwo_inr n j).symm

@[expose] noncomputable def swapPerm (n : ℕ) (S : Finset (Fin (R n))) : Equiv.Perm (Fin (n + 1)) :=
  (epsTwo n).trans ((swapSumEquiv n S).trans (epsTwo n).symm)

theorem swapPerm_apply_pair (n : ℕ) (S : Finset (Fin (R n))) (i : Fin (R n)) (a : Fin 2) :
    swapPerm n S (pairCoord n i a) = pairCoord n i (if i ∈ S then flip2 a else a) := by
  unfold swapPerm
  simp only [Equiv.trans_apply, swapSumEquiv, Equiv.sumCongr_apply]
  rw [epsTwo_inl]
  simp only [Sum.map_inl, swapPairEquiv_apply, swapPair]
  rw [epsTwo_symm_inl]

theorem swapPerm_apply_rest (n : ℕ) (S : Finset (Fin (R n))) (j : Fin (Q n)) :
    swapPerm n S (restCoord n j) = restCoord n j := by
  unfold swapPerm
  simp only [Equiv.trans_apply, swapSumEquiv, Equiv.sumCongr_apply]
  rw [epsTwo_inr]
  simp only [Sum.map_inr, Equiv.refl_apply]
  rw [epsTwo_symm_inr]

@[expose] noncomputable def delta (n : ℕ) (S : Finset (Fin (R n))) :
    SpecialLinearGroup (Fin (n + 1)) F2 :=
  slPerm gf2_two (swapPerm n S)

theorem delta_conj_blockGen_of_mem (n : ℕ) (S : Finset (Fin (R n))) {i : Fin (R n)}
    (hi : i ∈ S) :
    delta n S * blockGen n i * (delta n S)⁻¹ = (blockGen n i)⁻¹ := by
  unfold delta blockGen
  refine slPerm_conj_omegaBlock_inv (swapPerm n S) (k := pairIdx n i) (k' := pairIdx n i) ?_ ?_
  · rw [blockGen_castSucc, blockGen_succ, swapPerm_apply_pair, if_pos hi, flip2_zero]
  · rw [blockGen_succ, blockGen_castSucc, swapPerm_apply_pair, if_pos hi, flip2_one]

theorem delta_conj_blockGen_of_not_mem (n : ℕ) (S : Finset (Fin (R n))) {i : Fin (R n)}
    (hi : i ∉ S) :
    delta n S * blockGen n i * (delta n S)⁻¹ = blockGen n i := by
  unfold delta blockGen
  refine slPerm_conj_omegaBlock (swapPerm n S) (k := pairIdx n i) (k' := pairIdx n i) ?_ ?_
  · rw [blockGen_castSucc, swapPerm_apply_pair, if_neg hi]
  · rw [blockGen_succ, swapPerm_apply_pair, if_neg hi]

theorem blockGen_inv_eq_sq (n : ℕ) (j : Fin (R n)) :
    (blockGen n j)⁻¹ = blockGen n j ^ 2 := by
  have h3 : blockGen n j ^ 3 = 1 := by
    unfold blockGen
    exact omegaBlock_pow_three n (pairIdx n j)
  have h : blockGen n j * blockGen n j ^ 2 = 1 := by
    rw [show blockGen n j * blockGen n j ^ 2 = blockGen n j ^ 3 from by group]
    exact h3
  exact inv_eq_of_mul_eq_one_right h

theorem delta_conj_bg (n : ℕ) (S : Finset (Fin (R n))) (j : Fin (R n)) :
    delta n S * (bg n j : SpecialLinearGroup (Fin (n + 1)) F2) * (delta n S)⁻¹ =
      ((bg n j) ^ (if j ∈ S then 2 else 1) : ↥(halfTorus n)) := by
  by_cases hj : j ∈ S
  · rw [if_pos hj]
    change delta n S * blockGen n j * (delta n S)⁻¹ =
      (↑((bg n j) ^ 2) : SpecialLinearGroup (Fin (n + 1)) F2)
    rw [delta_conj_blockGen_of_mem n S hj, Subgroup.coe_pow, blockGen_inv_eq_sq]
    simp [bg]
  · rw [if_neg hj, pow_one]
    change delta n S * blockGen n j * (delta n S)⁻¹ =
      (↑(bg n j) : SpecialLinearGroup (Fin (n + 1)) F2)
    rw [delta_conj_blockGen_of_not_mem n S hj]
    simp [bg]

@[expose] def swapSet (n : ℕ) (v : Fin (R n) → Multiplicative (ZMod 3)) :
    Finset (Fin (R n)) :=
  Finset.univ.filter fun j => (Multiplicative.toAdd (v j)).val = 2

theorem mem_swapSet {n : ℕ} {v : Fin (R n) → Multiplicative (ZMod 3)} {j : Fin (R n)} :
    j ∈ swapSet n v ↔ (Multiplicative.toAdd (v j)).val = 2 := by
  simp [swapSet]

theorem delta_conj_prod (n : ℕ) (S : Finset (Fin (R n)))
    (s : Finset (Fin (R n))) :
    delta n S * ((s.prod (fun j => bg n j) : ↥(halfTorus n)) :
        SpecialLinearGroup (Fin (n + 1)) F2) * (delta n S)⁻¹ =
      ((s.prod (fun j => (bg n j) ^ (if j ∈ S then 2 else 1)) : ↥(halfTorus n)) :
        SpecialLinearGroup (Fin (n + 1)) F2) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, Subgroup.coe_mul, Subgroup.coe_mul]
      rw [show delta n S * ((bg n a : SpecialLinearGroup (Fin (n + 1)) F2) *
            ↑(s.prod (fun j => bg n j) : ↥(halfTorus n))) * (delta n S)⁻¹ =
          (delta n S * (bg n a : SpecialLinearGroup (Fin (n + 1)) F2) * (delta n S)⁻¹) *
            (delta n S * ↑(s.prod (fun j => bg n j) : ↥(halfTorus n)) *
              (delta n S)⁻¹) by group]
      rw [delta_conj_bg, ih]

theorem delta_conj_tZero_eq (n : ℕ) (v : Fin (R n) → Multiplicative (ZMod 3))
    (hv : ∀ j, v j ≠ 1) :
    delta n (swapSet n v) * SLNS.nsSL (eps n) det_rootMat_phi3 (fun _ => 1) *
        (delta n (swapSet n v))⁻¹ =
      (torusCoord n v : SpecialLinearGroup (Fin (n + 1)) F2) := by
  set S := swapSet n v
  have he : ∀ j : Fin (R n), (if j ∈ S then 2 else 1) =
      (Multiplicative.toAdd (v j)).val := by
    intro j
    by_cases hj : j ∈ S
    · rw [if_pos hj, (mem_swapSet.mp hj)]
    · rw [if_neg hj]
      have hne : (Multiplicative.toAdd (v j)).val ≠ 0 := by
        intro h0
        apply hv j
        have hz : Multiplicative.toAdd (v j) = 0 := by
          rw [← ZMod.natCast_zmod_val (Multiplicative.toAdd (v j)), h0, Nat.cast_zero]
        have := congrArg Multiplicative.ofAdd hz
        rwa [show Multiplicative.ofAdd (Multiplicative.toAdd (v j)) = v j from rfl,
          show Multiplicative.ofAdd (0 : ZMod 3) = 1 from rfl] at this
      have hlt : (Multiplicative.toAdd (v j)).val < 3 := ZMod.val_lt _
      have hne2 : (Multiplicative.toAdd (v j)).val ≠ 2 := fun h2 =>
        hj (mem_swapSet.mpr h2)
      omega
  rw [tZero_eq_prod]
  rw [delta_conj_prod]
  rw [torusCoord_apply_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  rw [he j]

theorem ones_one (n : ℕ) : ones (fun _ : Fin (R n) => 1) = R n := by
  unfold ones
  simp

theorem card_SL_le_one {m : ℕ} (hm : m ≤ 1) :
    Nat.card (SpecialLinearGroup (Fin m) F2) = 1 := by
  interval_cases m
  · have : Subsingleton (Matrix (Fin 0) (Fin 0) F2) := by
      constructor
      intro A B
      ext i
      exact i.elim0
    exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩
  · have : Fintype F2 := Fintype.ofFinite F2
    rw [Matrix.card_SL_field (𝔽 := F2) (n := 1)]
    have hcard : Fintype.card F2 = 2 := by
      rw [← Nat.card_eq_fintype_card, natCard_F2]
    rw [hcard]
    norm_num

theorem ggQ2Lin_card_zeroBlk (n : ℕ) :
    Nat.card (zeroBlk (n := n) (s := R n) (r := Q n) (eps n) (fun _ => 1)) = 1 := by
  rw [natCard_zeroBlk (eps n) (fun _ => 1) (fun _ => Or.inr rfl), ones_one]
  have hq : n + 1 - 2 * R n = Q n := by unfold Q; rfl
  rw [hq]
  exact card_SL_le_one (Q_le_one n)

theorem layer_tZero_eq_classBlk (n : ℕ) (hn : 5 ≤ n) :
    LargeEvenLayer (Subgroup.centralizer
      ({SLNS.nsSL (eps n) det_rootMat_phi3 (fun _ => 1)} :
        Set (SpecialLinearGroup (Fin (n + 1)) F2))) =
      classBlk (n := n) (s := R n) (r := Q n) (eps n) (fun _ => 1) := by
  classical
  set Y := SLNS.nsSL (eps n) det_rootMat_phi3 (fun _ => 1) with hY
  set C := Subgroup.centralizer ({Y} : Set (SpecialLinearGroup (Fin (n + 1)) F2)) with hC
  have ht : Y ∈ halfTorus n := tZero_mem n
  have hsupp : supp Y = 2 * R n := supp_tZero n
  obtain ⟨Z, Λ, hZcard, hΛcard, hdisj, hZcomp, hΛcomp, hcomp⟩ :=
    centralizer_blocks (halfTorus_pow_three ht)
  have hR : 2 ≤ R n := by unfold R; omega
  have hΛc : IsComponentOf Λ C := hΛcomp (by rw [hsupp]; omega)
  have hzero_card : Nat.card (zeroBlk (n := n) (s := R n) (r := Q n) (eps n) (fun _ => 1)) = 1 :=
    ggQ2Lin_card_zeroBlk n
  have hzero_bot : zeroBlk (n := n) (s := R n) (r := Q n) (eps n) (fun _ => 1) = ⊥ :=
    Subgroup.eq_bot_of_card_eq _ hzero_card
  have hZcard1 : Nat.card Z = 1 := by
    rw [hZcard]
    have hq : n + 1 - supp Y = Q n := by
      rw [hsupp]
      unfold Q
      rfl
    rw [hq]
    exact card_SL_le_one (Q_le_one n)
  have hZbot : Z = ⊥ := Subgroup.eq_bot_of_card_eq Z hZcard1
  have hΛne : Λ ≠ ⊥ := ne_bot_of_isComponentOf hΛc
  have hΛeq : Λ = classBlk (n := n) (s := R n) (r := Q n) (eps n) (fun _ => 1) := by
    rcases comp_eq_zeroBlk_or_classBlk (n := n) (s := R n) (r := Q n) (eps n)
      (fun _ => 1) (fun _ => Or.inr rfl) hΛc with h | h
    · rw [h, hzero_bot] at hΛne
      exact absurd rfl hΛne
    · exact h
  have hlayer_le : LargeEvenLayer C ≤ classBlk (n := n) (s := R n) (r := Q n) (eps n)
      (fun _ => 1) := by
    unfold LargeEvenLayer
    refine sSup_le ?_
    intro K hK
    rcases hcomp K hK with rfl | rfl
    · exact absurd hZbot (ne_bot_of_isComponentOf hK)
    · exact hΛeq.le
  have hclass_le : classBlk (n := n) (s := R n) (r := Q n) (eps n) (fun _ => 1) ≤
      LargeEvenLayer C := by
    rw [← hΛeq]
    exact le_sSup (s := {K : Subgroup (SpecialLinearGroup (Fin (n + 1)) F2) |
      IsComponentOf K C}) hΛc
  exact le_antisymm hlayer_le hclass_le

theorem layer_classBlk_conj (n : ℕ) (hn : 5 ≤ n)
    (t : SpecialLinearGroup (Fin (n + 1)) F2) (ht : t ∈ halfTorus n)
    (hv : ∀ j, (torusCoord n).symm ⟨t, ht⟩ j ≠ 1) :
    LargeEvenLayer (Subgroup.centralizer ({t} :
        Set (SpecialLinearGroup (Fin (n + 1)) F2))) =
      (classBlk (n := n) (s := R n) (r := Q n) (eps n) (fun _ => 1)).map
        (MulAut.conj (delta n (swapSet n ((torusCoord n).symm ⟨t, ht⟩)))).toMonoidHom := by
  set v := (torusCoord n).symm ⟨t, ht⟩ with hvdef
  set D := delta n (swapSet n v) with hD
  have htv : t = D * SLNS.nsSL (eps n) det_rootMat_phi3 (fun _ => 1) * D⁻¹ := by
    rw [delta_conj_tZero_eq n v hv]
    exact (congrArg Subtype.val ((torusCoord n).apply_symm_apply ⟨t, ht⟩)).symm
  have hcent : Subgroup.centralizer ({t} :
      Set (SpecialLinearGroup (Fin (n + 1)) F2)) =
      (Subgroup.centralizer ({SLNS.nsSL (eps n) det_rootMat_phi3 (fun _ => 1)} :
        Set (SpecialLinearGroup (Fin (n + 1)) F2))).map (MulAut.conj D).toMonoidHom := by
    rw [htv]
    exact (Subgroup.map_conj_centralizer_singleton D _).symm
  rw [hcent, ← shapeConj_largeEvenLayer_map_conj, layer_tZero_eq_classBlk n hn]


theorem supp_torusCoord (n : ℕ) (v : Fin (R n) → Multiplicative (ZMod 3)) :
    supp (torusCoord n v : SpecialLinearGroup (Fin (n + 1)) F2) =
      2 * (Finset.univ.filter fun j => v j ≠ 1).card := by
  rw [torusCoord_apply_prod, ← nsSL_eq_prod]
  rw [supp_nsSL]
  have hf : (Finset.univ.filter fun i => (Multiplicative.toAdd (v i)).val % 3 ≠ 0) =
      (Finset.univ.filter fun j => v j ≠ 1) := by
    apply Finset.filter_congr
    intro j _
    have h1 : v j = 1 ↔ Multiplicative.toAdd (v j) = 0 := by
      constructor
      · intro h
        rw [h]
        rfl
      · intro h
        apply Multiplicative.toAdd.injective
        rw [h]
        rfl
    rw [Nat.mod_eq_of_lt (ZMod.val_lt _), Ne, Ne, ZMod.val_eq_zero]
    exact not_congr h1.symm
  rw [hf]

theorem torusCoord_ne_one_of_supp (n : ℕ) (v : Fin (R n) → Multiplicative (ZMod 3))
    (hv : n + 1 - supp (torusCoord n v : SpecialLinearGroup (Fin (n + 1)) F2) ≤ 1) :
    ∀ j, v j ≠ 1 := by
  have hsupp := supp_torusCoord n v
  have hc_le : (Finset.univ.filter fun j => v j ≠ 1).card ≤ R n := by
    calc (Finset.univ.filter fun j => v j ≠ 1).card
        ≤ (Finset.univ : Finset (Fin (R n))).card := Finset.card_filter_le _ _
      _ = R n := by simp
  have hn1 := two_mul_R_add_Q n
  have hQ := Q_le_one n
  rw [hsupp] at hv
  have hc : (Finset.univ.filter fun j => v j ≠ 1).card = R n := by omega
  intro j hj
  have hsub : (Finset.univ.filter fun i => v i ≠ 1) ⊆ Finset.univ.erase j := by
    intro i hi
    rw [Finset.mem_filter] at hi
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ i⟩
    intro hij
    exact hi.2 (hij ▸ hj)
  have hle : (Finset.univ.filter fun i => v i ≠ 1).card ≤ R n - 1 := by
    calc (Finset.univ.filter fun i => v i ≠ 1).card
        ≤ (Finset.univ.erase j).card := Finset.card_le_card hsub
      _ = R n - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]
  rw [hc] at hle
  have hRpos : 0 < R n := by
    have := j.isLt
    omega
  omega


variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J : Subgroup G}

theorem ggQ2Lin_J_eq_classBlk_conj {n : ℕ}
    {ψ : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2 →* G}
    (hS : GGQTwoSetting p B Bs x L D J)
    (hF : GGHalfTorusFrame Bs L (GGHalf.halfTorus n) ψ)
    {z : G} {t : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2} {a : ℤ}
    (hz : z = x ^ a * ψ t) (ht : t ∈ GGHalf.halfTorus n)
    (hDclos : D = Subgroup.closure ({x, z} : Set G))
    (hs : n + 1 - GGHalf.supp t ≤ 1) (hn : 5 ≤ n) :
    J = Subgroup.map ψ ((classBlk (n := n) (s := R n) (r := Q n) (eps n) (fun _ => 1)).map
      (MulAut.conj (delta n (swapSet n ((torusCoord n).symm ⟨t, ht⟩)))).toMonoidHom) := by
  set v := (torusCoord n).symm ⟨t, ht⟩ with hvdef
  have htv : (torusCoord n v : SpecialLinearGroup (Fin (n + 1)) GGHalf.F2) = t :=
    congrArg Subtype.val ((torusCoord n).apply_symm_apply ⟨t, ht⟩)
  have hv : ∀ j, v j ≠ 1 := torusCoord_ne_one_of_supp n v (by rw [htv]; exact hs)
  obtain ⟨hJ, -⟩ := ggQ2Lin_layer_eq hS hF hz hDclos
  rw [hJ, layer_classBlk_conj n hn t ht hv]


noncomputable local instance charPAdjoinRootPhi3 : CharP (AdjoinRoot phi3) 2 :=
  charP_of_injective_algebraMap (algebraMap F2 (AdjoinRoot phi3)).injective 2

@[expose] noncomputable def permMatSL (n : ℕ) (σ : Equiv.Perm (Fin (R n))) :
    SpecialLinearGroup (Fin (R n)) (AdjoinRoot phi3) :=
  ⟨σ.permMatrix (AdjoinRoot phi3), by
    rw [Matrix.det_permutation]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
    · rw [h]; simp
    · rw [h]
      have h2 : (2 : AdjoinRoot phi3) = 0 := CharP.cast_eq_zero _ 2
      have hneg : (-1 : AdjoinRoot phi3) = 1 := by
        rw [neg_eq_iff_add_eq_zero, one_add_one_eq_two, h2]
      simpa using hneg⟩

theorem permMatSL_inv (n : ℕ) (σ : Equiv.Perm (Fin (R n))) :
    (permMatSL n σ)⁻¹ = permMatSL n σ.symm := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  change σ.permMatrix (AdjoinRoot phi3) *
    Equiv.Perm.permMatrix (AdjoinRoot phi3) σ.symm = 1
  rw [← Matrix.permMatrix_mul (σ := σ.symm) (τ := σ),
    show σ.symm * σ = 1 from by ext x; simp, Matrix.permMatrix_one]

theorem blockAct_perm (n : ℕ) (σ : Equiv.Perm (Fin (R n)))
    (x : (Fin (R n) → AdjoinRoot phi3) × (Fin (Q n) → F2)) :
    CoordSL.blockAct phi3 (permMatSL n σ) x =
      (fun i => x.1 (σ i), x.2) := by
  rw [CoordSL.blockAct_apply]
  congr 1
  change σ.permMatrix (AdjoinRoot phi3) *ᵥ x.1 = fun i => x.1 (σ i)
  rw [Matrix.permMatrix_mulVec]
  rfl

theorem frameForm_theta_conj (n : ℕ) (σ : Equiv.Perm (Fin (R n)))
    (k : Fin (R n) → ℕ) :
    CoordSL.frameForm phi3 (eps n)
      ((((CoordSL.theta phi3 (eps n) (permMatSL n σ) :
          SpecialLinearGroup (Fin (n + 1)) F2) : Matrix (Fin (n + 1)) (Fin (n + 1)) F2) *
        ((SLNS.nsSL (eps n) det_rootMat_phi3 k :
          SpecialLinearGroup (Fin (n + 1)) F2) : Matrix (Fin (n + 1)) (Fin (n + 1)) F2) *
        (((CoordSL.theta phi3 (eps n) (permMatSL n σ))⁻¹ :
          SpecialLinearGroup (Fin (n + 1)) F2) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) F2))) =
      CoordSL.frameForm phi3 (eps n)
        ((SLNS.nsSL (eps n) det_rootMat_phi3 (fun i => k (σ i)) :
          SpecialLinearGroup (Fin (n + 1)) F2) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) F2) := by
  rw [CoordSL.frameForm_mul, CoordSL.frameForm_mul]
  have hθ : ∀ M : SpecialLinearGroup (Fin (R n)) (AdjoinRoot phi3),
      CoordSL.frameForm phi3 (eps n)
        ((CoordSL.theta phi3 (eps n) M : SpecialLinearGroup (Fin (n + 1)) F2) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) F2) = CoordSL.blockAct phi3 M := by
    intro M
    rw [show ((CoordSL.theta phi3 (eps n) M : SpecialLinearGroup (Fin (n + 1)) F2) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) F2) =
        CoordSL.thetaMat phi3 (eps n) M from rfl, CoordSL.frameForm_thetaMat]
  have hns : ∀ k' : Fin (R n) → ℕ,
      CoordSL.frameForm phi3 (eps n)
        ((SLNS.nsSL (eps n) det_rootMat_phi3 k' : SpecialLinearGroup (Fin (n + 1)) F2) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) F2) =
        CoordSL.torusAct' phi3 k' := by
    intro k'
    rw [show ((SLNS.nsSL (eps n) det_rootMat_phi3 k' :
        SpecialLinearGroup (Fin (n + 1)) F2) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) F2) =
        SLNS.nsMat (eps n) (rootMat phi3) k' from rfl,
      CoordSL.frameForm_nsMat' (g := phi3) (ε := eps n) k']
  rw [hθ, hns]
  rw [show ((CoordSL.theta phi3 (eps n) (permMatSL n σ))⁻¹ :
      SpecialLinearGroup (Fin (n + 1)) F2) =
      CoordSL.theta phi3 (eps n) ((permMatSL n σ)⁻¹) from (map_inv _ _).symm,
    permMatSL_inv]
  rw [hθ, hns]
  refine LinearMap.ext fun x => ?_
  obtain ⟨u, w⟩ := x
  apply Prod.ext
  · funext i
    rw [LinearMap.comp_apply, LinearMap.comp_apply, blockAct_perm, blockAct_perm]
    simp [CoordSL.torusAct'_apply, CoordSL.torusAct, Equiv.symm_apply_apply]
  · rfl

theorem theta_perm_conj_nsSL (n : ℕ) (σ : Equiv.Perm (Fin (R n)))
    (k : Fin (R n) → ℕ) :
    (CoordSL.theta phi3 (eps n) (permMatSL n σ) : SpecialLinearGroup (Fin (n + 1)) F2) *
        SLNS.nsSL (eps n) det_rootMat_phi3 k *
        (CoordSL.theta phi3 (eps n) (permMatSL n σ))⁻¹ =
      SLNS.nsSL (eps n) det_rootMat_phi3 (fun i => k (σ i)) := by
  apply Subtype.ext
  apply CoordSL.frameForm_injective phi3 (eps n)
  exact frameForm_theta_conj n σ k

theorem theta_perm_conj_blockGen (n : ℕ) (σ : Equiv.Perm (Fin (R n))) (i : Fin (R n)) :
    (CoordSL.theta phi3 (eps n) (permMatSL n σ) : SpecialLinearGroup (Fin (n + 1)) F2) *
        blockGen n i * (CoordSL.theta phi3 (eps n) (permMatSL n σ))⁻¹ =
      blockGen n (σ.symm i) := by
  rw [← nsSL_single_eq_blockGen n i, ← nsSL_single_eq_blockGen n (σ.symm i)]
  rw [theta_perm_conj_nsSL]
  congr 2
  funext j
  simp only [Pi.single_apply]
  by_cases h : σ j = i
  · have hj : j = σ.symm i := (Equiv.eq_symm_apply σ).mpr h
    rw [if_pos h, if_pos hj]
  · have hj : j ≠ σ.symm i := fun hh => h ((Equiv.eq_symm_apply σ).mp hh)
    rw [if_neg h, if_neg hj]

theorem coordBlockSL_univ (n : ℕ) :
    CFSG.RankThree.CALinearPlane.coordBlockSL (AdjoinRoot phi3)
      (Finset.univ : Finset (Fin (R n))) = ⊤ := by
  rw [eq_top_iff]
  intro g _
  rw [CFSG.RankThree.CALinearPlane.mem_coordBlockSL_iff]
  intro i j hij
  simp at hij

theorem theta_perm_mem_classBlk (n : ℕ) (σ : Equiv.Perm (Fin (R n))) :
    (CoordSL.theta phi3 (eps n) (permMatSL n σ) : SpecialLinearGroup (Fin (n + 1)) F2) ∈
      classBlk (n := n) (s := R n) (r := Q n) (eps n) (fun _ => 1) := by
  unfold classBlk
  refine Subgroup.mem_map.mpr ⟨permMatSL n σ, ?_, rfl⟩
  change permMatSL n σ ∈ RankThree.CALinearPlane.coordBlockSL (AdjoinRoot phi3)
    (classSet (fun _ : Fin (R n) => ((1 : ℕ) : ZMod 3)) 1)
  rw [show (classSet (fun _ : Fin (R n) => ((1 : ℕ) : ZMod 3)) 1) = Finset.univ from by
    ext i; simp [classSet]]
  rw [coordBlockSL_univ n]
  exact Subgroup.mem_top _

theorem swapPerm_mul_self (n : ℕ) (S : Finset (Fin (R n))) :
    swapPerm n S * swapPerm n S = 1 := by
  ext x
  simp only [Equiv.Perm.mul_apply, Equiv.Perm.coe_one, id_eq]
  rcases h : epsTwo n x with ⟨a, i⟩ | j
  · have hx : x = pairCoord n i a := by
      rw [← epsTwo_symm_inl n i a, ← h, Equiv.symm_apply_apply]
    rw [hx, swapPerm_apply_pair, swapPerm_apply_pair]
    by_cases hi : i ∈ S <;> simp [hi, flip2_invol]
  · have hx : x = restCoord n j := by
      rw [← epsTwo_symm_inr n j, ← h, Equiv.symm_apply_apply]
    rw [hx, swapPerm_apply_rest, swapPerm_apply_rest]

theorem delta_sq (n : ℕ) (S : Finset (Fin (R n))) :
    delta n S * delta n S = 1 := by
  unfold delta
  rw [← map_mul, swapPerm_mul_self, map_one]

theorem delta_inv_eq_self (n : ℕ) (S : Finset (Fin (R n))) :
    (delta n S)⁻¹ = delta n S := by
  rw [eq_comm, inv_eq_of_mul_eq_one_right]
  exact delta_sq n S

theorem permMatSL_mul_self (n : ℕ) (σ : Equiv.Perm (Fin (R n))) :
    permMatSL n σ * permMatSL n σ = permMatSL n (σ * σ) := by
  apply Subtype.ext
  change σ.permMatrix (AdjoinRoot phi3) * σ.permMatrix (AdjoinRoot phi3) =
    (σ * σ).permMatrix (AdjoinRoot phi3)
  rw [Matrix.permMatrix_mul]

theorem theta_perm_inv_eq (n : ℕ) (σ : Equiv.Perm (Fin (R n))) :
    ((CoordSL.theta phi3 (eps n) (permMatSL n σ) :
      SpecialLinearGroup (Fin (n + 1)) F2))⁻¹ =
      (CoordSL.theta phi3 (eps n) (permMatSL n σ.symm) :
        SpecialLinearGroup (Fin (n + 1)) F2) := by
  rw [show ((CoordSL.theta phi3 (eps n) (permMatSL n σ) :
      SpecialLinearGroup (Fin (n + 1)) F2))⁻¹ =
      (CoordSL.theta phi3 (eps n) ((permMatSL n σ)⁻¹) :
        SpecialLinearGroup (Fin (n + 1)) F2) from (map_inv _ _).symm,
    permMatSL_inv]

theorem theta_perm_sq (n : ℕ) (σ : Equiv.Perm (Fin (R n))) (hσ : σ * σ = 1) :
    (CoordSL.theta phi3 (eps n) (permMatSL n σ) :
      SpecialLinearGroup (Fin (n + 1)) F2) *
      (CoordSL.theta phi3 (eps n) (permMatSL n σ) :
        SpecialLinearGroup (Fin (n + 1)) F2) = 1 := by
  have h1 : permMatSL n 1 = 1 := by
    apply Subtype.ext
    change (1 : Equiv.Perm (Fin (R n))).permMatrix (AdjoinRoot phi3) = 1
    rw [Matrix.permMatrix_one]
  rw [← map_mul, permMatSL_mul_self, hσ, h1, map_one]


theorem conj_pow_eq_nat {G : Type} [Group G] (D B : G) (s : ℕ) :
    D * B ^ s * D⁻¹ = (D * B * D⁻¹) ^ s := by
  induction s with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ]
      calc D * (B ^ n * B) * D⁻¹ = (D * B ^ n * D⁻¹) * (D * B * D⁻¹) := by group
        _ = (D * B * D⁻¹) ^ n * (D * B * D⁻¹) := by rw [ih]

theorem delta_theta_blockGen_pow (n : ℕ) (S : Finset (Fin (R n)))
    (σ : Equiv.Perm (Fin (R n))) (i : Fin (R n)) :
    (delta n S * (CoordSL.theta phi3 (eps n) (permMatSL n σ) :
        SpecialLinearGroup (Fin (n + 1)) F2) * (delta n S)⁻¹) *
        blockGen n i *
        (delta n S * (CoordSL.theta phi3 (eps n) (permMatSL n σ) :
          SpecialLinearGroup (Fin (n + 1)) F2) * (delta n S)⁻¹)⁻¹ =
      (blockGen n (σ.symm i)) ^
        ((if i ∈ S then 2 else 1) * (if σ.symm i ∈ S then 2 else 1)) := by
  set U := (CoordSL.theta phi3 (eps n) (permMatSL n σ) :
    SpecialLinearGroup (Fin (n + 1)) F2) with hU
  set B := blockGen n (σ.symm i) with hB
  have hDinv : (delta n S)⁻¹ = delta n S := delta_inv_eq_self n S
  set s := if i ∈ S then 2 else 1 with hs
  set s' := if σ.symm i ∈ S then 2 else 1 with hs'
  have hDAi : delta n S * blockGen n i * (delta n S)⁻¹ = (blockGen n i) ^ s := by
    by_cases hi : i ∈ S
    · rw [if_pos hi] at hs
      rw [hs, delta_conj_blockGen_of_mem n S hi, blockGen_inv_eq_sq]
    · rw [if_neg hi] at hs
      rw [hs, pow_one, delta_conj_blockGen_of_not_mem n S hi]
  have hDAj : delta n S * B * (delta n S)⁻¹ = B ^ s' := by
    rw [hB]
    by_cases hj : σ.symm i ∈ S
    · rw [if_pos hj] at hs'
      rw [hs', delta_conj_blockGen_of_mem n S hj, blockGen_inv_eq_sq]
    · rw [if_neg hj] at hs'
      rw [hs', pow_one, delta_conj_blockGen_of_not_mem n S hj]
  have h1 : (delta n S * U * (delta n S)⁻¹) * blockGen n i *
      (delta n S * U * (delta n S)⁻¹)⁻¹ =
      delta n S * U * (delta n S * blockGen n i * (delta n S)⁻¹) * U⁻¹ * (delta n S)⁻¹ := by
    rw [hDinv]
    rw [_root_.mul_inv_rev, _root_.mul_inv_rev, hDinv]
    group
  have h2 : U * (blockGen n i) ^ s * U⁻¹ = B ^ s := by
    rw [conj_pow_eq_nat U (blockGen n i) s, theta_perm_conj_blockGen, hB]
  have h3 : delta n S * B ^ s * (delta n S)⁻¹ = B ^ (s * s') := by
    rw [conj_pow_eq_nat (delta n S) B s, hDAj, ← pow_mul]
    congr 1
    exact mul_comm s' s
  calc
    (delta n S * U * (delta n S)⁻¹) * blockGen n i *
        (delta n S * U * (delta n S)⁻¹)⁻¹
        = delta n S * U * (delta n S * blockGen n i * (delta n S)⁻¹) * U⁻¹ * (delta n S)⁻¹ := h1
    _ = delta n S * U * (blockGen n i) ^ s * U⁻¹ * (delta n S)⁻¹ := by rw [hDAi]
    _ = delta n S * (U * (blockGen n i) ^ s * U⁻¹) * (delta n S)⁻¹ := by group
    _ = delta n S * B ^ s * (delta n S)⁻¹ := by rw [h2]
    _ = B ^ (s * s') := h3


@[expose] noncomputable def u (n : ℕ) (S : Finset (Fin (R n)))
    (σ : Equiv.Perm (Fin (R n))) : SpecialLinearGroup (Fin (n + 1)) F2 :=
  delta n S * (CoordSL.theta phi3 (eps n) (permMatSL n σ) :
    SpecialLinearGroup (Fin (n + 1)) F2) * (delta n S)⁻¹

theorem u_mem_classBlk (n : ℕ) (S : Finset (Fin (R n)))
    (σ : Equiv.Perm (Fin (R n))) :
    u n S σ ∈ (classBlk (n := n) (s := R n) (r := Q n) (eps n) (fun _ => 1)).map
      (MulAut.conj (delta n S)).toMonoidHom := by
  unfold u
  refine Subgroup.mem_map.mpr ⟨(CoordSL.theta phi3 (eps n) (permMatSL n σ) :
    SpecialLinearGroup (Fin (n + 1)) F2), theta_perm_mem_classBlk n σ, rfl⟩

theorem exists_pairIdx_of_even {n : ℕ} {k : Fin n} (hk : k.val % 2 = 0) :
    ∃ i : Fin (R n), pairIdx n i = k := by
  refine ⟨⟨k.val / 2, ?_⟩, ?_⟩
  · unfold R
    have hklt := k.isLt
    omega
  · apply Fin.ext
    unfold pairIdx
    simp only
    have hdvd : 2 ∣ k.val := Nat.dvd_of_mod_eq_zero hk
    rw [Nat.mul_comm]
    exact Nat.div_mul_cancel hdvd

theorem conj_mem_closure_of_gens {G : Type*} [Group G] (s : Set G)
    (H : Subgroup G) (c : G) (hH : H = Subgroup.closure s)
    (hgen : ∀ x ∈ s, c * x * c⁻¹ ∈ H) : ∀ t ∈ H, c * t * c⁻¹ ∈ H := by
  intro t ht
  rw [hH] at ht
  induction ht using Subgroup.closure_induction with
  | mem y hy => exact hgen y hy
  | one => simp
  | mul y z _ _ ihy ihz =>
      rw [show c * (y * z) * c⁻¹ = (c * y * c⁻¹) * (c * z * c⁻¹) by group]
      exact mul_mem ihy ihz
  | inv y _ ihy =>
      rw [show c * y⁻¹ * c⁻¹ = (c * y * c⁻¹)⁻¹ by group]
      exact inv_mem ihy

theorem u_blockGen (n : ℕ) (S : Finset (Fin (R n)))
    (σ : Equiv.Perm (Fin (R n))) (i : Fin (R n)) :
    u n S σ * blockGen n i * (u n S σ)⁻¹ =
      (blockGen n (σ.symm i)) ^
        ((if i ∈ S then 2 else 1) * (if σ.symm i ∈ S then 2 else 1)) := by
  simpa [u] using delta_theta_blockGen_pow n S σ i

theorem u_conj_omegaBlock (n : ℕ) (S : Finset (Fin (R n)))
    (σ : Equiv.Perm (Fin (R n))) {k : Fin n} (hk : k.val % 2 = 0) :
    u n S σ * omegaBlock n k * (u n S σ)⁻¹ ∈ halfTorus n := by
  obtain ⟨i, rfl⟩ := exists_pairIdx_of_even hk
  rw [show omegaBlock n (pairIdx n i) = blockGen n i from rfl, u_blockGen]
  exact pow_mem (blockGen_mem n (σ.symm i)) _

theorem u_conj_mem_halfTorus (n : ℕ) (S : Finset (Fin (R n)))
    (σ : Equiv.Perm (Fin (R n))) {t : SpecialLinearGroup (Fin (n + 1)) F2}
    (ht : t ∈ halfTorus n) :
    u n S σ * t * (u n S σ)⁻¹ ∈ halfTorus n := by
  refine conj_mem_closure_of_gens {x | ∃ k : Fin n, k.val % 2 = 0 ∧ x = omegaBlock n k}
    (halfTorus n) (u n S σ) rfl ?_ t ht
  rintro x ⟨k, hk, rfl⟩
  exact u_conj_omegaBlock n S σ hk

theorem u_mul_self (n : ℕ) (S : Finset (Fin (R n)))
    (σ : Equiv.Perm (Fin (R n))) (hσ : σ * σ = 1) :
    u n S σ * u n S σ = 1 := by
  unfold u
  rw [show (delta n S * (CoordSL.theta phi3 (eps n) (permMatSL n σ) :
        SpecialLinearGroup (Fin (n + 1)) F2) * (delta n S)⁻¹) *
      (delta n S * (CoordSL.theta phi3 (eps n) (permMatSL n σ) :
        SpecialLinearGroup (Fin (n + 1)) F2) * (delta n S)⁻¹) =
      delta n S * ((CoordSL.theta phi3 (eps n) (permMatSL n σ) :
        SpecialLinearGroup (Fin (n + 1)) F2) *
        (CoordSL.theta phi3 (eps n) (permMatSL n σ) :
          SpecialLinearGroup (Fin (n + 1)) F2)) * (delta n S)⁻¹ by group]
  rw [theta_perm_sq n σ hσ]
  rw [mul_one, delta_inv_eq_self]
  exact delta_sq n S

theorem u_mul_eq (n : ℕ) (S : Finset (Fin (R n)))
    (σ τ : Equiv.Perm (Fin (R n))) :
    u n S σ * u n S τ =
      delta n S * ((CoordSL.theta phi3 (eps n) (permMatSL n σ) :
        SpecialLinearGroup (Fin (n + 1)) F2) *
        (CoordSL.theta phi3 (eps n) (permMatSL n τ) :
          SpecialLinearGroup (Fin (n + 1)) F2)) * (delta n S)⁻¹ := by
  have hDinv : (delta n S)⁻¹ = delta n S := delta_inv_eq_self n S
  unfold u
  rw [hDinv]
  calc
    (delta n S * (CoordSL.theta phi3 (eps n) (permMatSL n σ) :
        SpecialLinearGroup (Fin (n + 1)) F2) * delta n S) *
        (delta n S * (CoordSL.theta phi3 (eps n) (permMatSL n τ) :
          SpecialLinearGroup (Fin (n + 1)) F2) * delta n S)
        = delta n S * (CoordSL.theta phi3 (eps n) (permMatSL n σ) :
            SpecialLinearGroup (Fin (n + 1)) F2) * (delta n S * delta n S) *
            (CoordSL.theta phi3 (eps n) (permMatSL n τ) :
              SpecialLinearGroup (Fin (n + 1)) F2) * delta n S := by group
    _ = delta n S * ((CoordSL.theta phi3 (eps n) (permMatSL n σ) :
          SpecialLinearGroup (Fin (n + 1)) F2) *
          (CoordSL.theta phi3 (eps n) (permMatSL n τ) :
            SpecialLinearGroup (Fin (n + 1)) F2)) * delta n S := by
        rw [delta_sq, mul_one]; group

theorem permMatSL_mul_comm (n : ℕ) (σ τ : Equiv.Perm (Fin (R n)))
    (h : σ * τ = τ * σ) :
    permMatSL n σ * permMatSL n τ = permMatSL n τ * permMatSL n σ := by
  apply Subtype.ext
  change σ.permMatrix (AdjoinRoot phi3) * τ.permMatrix (AdjoinRoot phi3) =
    τ.permMatrix (AdjoinRoot phi3) * σ.permMatrix (AdjoinRoot phi3)
  rw [← Matrix.permMatrix_mul, ← Matrix.permMatrix_mul, h]

theorem u_mul_comm (n : ℕ) (S : Finset (Fin (R n)))
    (σ τ : Equiv.Perm (Fin (R n))) (h : σ * τ = τ * σ) :
    u n S σ * u n S τ = u n S τ * u n S σ := by
  have hU : (CoordSL.theta phi3 (eps n) (permMatSL n σ) :
      SpecialLinearGroup (Fin (n + 1)) F2) *
      (CoordSL.theta phi3 (eps n) (permMatSL n τ) :
        SpecialLinearGroup (Fin (n + 1)) F2) =
      (CoordSL.theta phi3 (eps n) (permMatSL n τ) :
        SpecialLinearGroup (Fin (n + 1)) F2) *
      (CoordSL.theta phi3 (eps n) (permMatSL n σ) :
        SpecialLinearGroup (Fin (n + 1)) F2) := by
    rw [← map_mul, ← map_mul, permMatSL_mul_comm n σ τ h]
  have hDinv : (delta n S)⁻¹ = delta n S := delta_inv_eq_self n S
  rw [u_mul_eq n S σ τ, u_mul_eq n S τ σ, hU]

theorem torusCoord_symm_blockGen (n : ℕ) (j : Fin (R n)) :
    (torusCoord n).symm (⟨blockGen n j, blockGen_mem n j⟩ : ↥(halfTorus n)) =
      Pi.mulSingle j (Multiplicative.ofAdd (1 : ZMod 3)) := by
  apply (torusCoord n).injective
  rw [MulEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [torusCoord_gen]

theorem blockGen_pow_ne_of_ne {n : ℕ} {i j : Fin (R n)} (hij : i ≠ j)
    {e : ℕ} (he : e = 1 ∨ e = 2 ∨ e = 4) :
    (blockGen n j) ^ e ≠ blockGen n i := by
  intro h
  have hsub : (⟨blockGen n j, blockGen_mem n j⟩ : ↥(halfTorus n)) ^ e =
      ⟨blockGen n i, blockGen_mem n i⟩ := by
    apply Subtype.ext
    rw [Subgroup.coe_pow]
    exact h
  have hconj := congrArg (fun x : ↥(halfTorus n) => (torusCoord n).symm x) hsub
  rw [map_pow, torusCoord_symm_blockGen, torusCoord_symm_blockGen] at hconj
  have heval := congrFun hconj j
  simp only [Pi.pow_apply, Pi.mulSingle_apply, hij.symm, if_false] at heval
  rcases he with rfl | rfl | rfl
  · exact (by decide : (Multiplicative.ofAdd (1 : ZMod 3)) ^ 1 ≠ 1) heval
  · exact (by decide : (Multiplicative.ofAdd (1 : ZMod 3)) ^ 2 ≠ 1) heval
  · exact (by decide : (Multiplicative.ofAdd (1 : ZMod 3)) ^ 4 ≠ 1) heval

noncomputable def fourEmb (n : ℕ) (hR : 4 ≤ R n) : Fin 4 ↪ Fin (R n) :=
  Fin.castLEEmb hR

noncomputable def sigmaOf (n : ℕ) (hR : 4 ≤ R n) (τ : Equiv.Perm (Fin 4)) :
    Equiv.Perm (Fin (R n)) :=
  Equiv.Perm.viaEmbeddingHom (fourEmb n hR) τ

def tau1 : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 2 3

def tau2 : Equiv.Perm (Fin 4) := Equiv.swap 0 2 * Equiv.swap 1 3

theorem tau1_sq : tau1 * tau1 = 1 := by decide

theorem tau2_sq : tau2 * tau2 = 1 := by decide

theorem tau1_comm_tau2 : tau1 * tau2 = tau2 * tau1 := by decide

theorem tau1_symm_zero : tau1.symm 0 = 1 := by decide

theorem tau2_symm_zero : tau2.symm 0 = 2 := by decide

theorem tau1_one : tau1 1 = 0 := by decide

theorem tau2_two : tau2 2 = 0 := by decide

theorem tau1_two : tau1 2 = 3 := by decide

theorem tau1_three : tau1 3 = 2 := by decide

theorem sigmaOf_apply (n : ℕ) (hR : 4 ≤ R n) (τ : Equiv.Perm (Fin 4)) (i : Fin 4) :
    sigmaOf n hR τ (fourEmb n hR i) = fourEmb n hR (τ i) := by
  change Equiv.Perm.viaEmbeddingHom (fourEmb n hR) τ (fourEmb n hR i) = _
  exact Equiv.Perm.viaEmbedding_apply τ (fourEmb n hR) i

theorem sigma1_sq (n : ℕ) (hR : 4 ≤ R n) :
    sigmaOf n hR tau1 * sigmaOf n hR tau1 = 1 := by
  change Equiv.Perm.viaEmbeddingHom (fourEmb n hR) tau1 *
    Equiv.Perm.viaEmbeddingHom (fourEmb n hR) tau1 = 1
  rw [← map_mul, tau1_sq, map_one]

theorem sigma2_sq (n : ℕ) (hR : 4 ≤ R n) :
    sigmaOf n hR tau2 * sigmaOf n hR tau2 = 1 := by
  change Equiv.Perm.viaEmbeddingHom (fourEmb n hR) tau2 *
    Equiv.Perm.viaEmbeddingHom (fourEmb n hR) tau2 = 1
  rw [← map_mul, tau2_sq, map_one]

theorem sigma1_comm_sigma2 (n : ℕ) (hR : 4 ≤ R n) :
    sigmaOf n hR tau1 * sigmaOf n hR tau2 = sigmaOf n hR tau2 * sigmaOf n hR tau1 := by
  change Equiv.Perm.viaEmbeddingHom (fourEmb n hR) tau1 *
    Equiv.Perm.viaEmbeddingHom (fourEmb n hR) tau2 =
    Equiv.Perm.viaEmbeddingHom (fourEmb n hR) tau2 *
    Equiv.Perm.viaEmbeddingHom (fourEmb n hR) tau1
  rw [← map_mul, ← map_mul, tau1_comm_tau2]

theorem sigma1_symm_zero (n : ℕ) (hR : 4 ≤ R n) :
    (sigmaOf n hR tau1).symm (fourEmb n hR 0) = fourEmb n hR 1 := by
  rw [Equiv.symm_apply_eq]
  rw [sigmaOf_apply, tau1_one]

theorem sigma2_symm_zero (n : ℕ) (hR : 4 ≤ R n) :
    (sigmaOf n hR tau2).symm (fourEmb n hR 0) = fourEmb n hR 2 := by
  rw [Equiv.symm_apply_eq]
  rw [sigmaOf_apply, tau2_two]

theorem sigma1_symm_two (n : ℕ) (hR : 4 ≤ R n) :
    (sigmaOf n hR tau1).symm (fourEmb n hR 2) = fourEmb n hR 3 := by
  rw [Equiv.symm_apply_eq]
  rw [sigmaOf_apply, tau1_three]

theorem blockGen_pow_ne_pow_of_ne {n : ℕ} {i j : Fin (R n)} (hij : i ≠ j)
    {e f : ℕ} (he : e = 1 ∨ e = 2 ∨ e = 4) :
    (blockGen n j) ^ e ≠ (blockGen n i) ^ f := by
  intro h
  have hsub : (⟨blockGen n j, blockGen_mem n j⟩ : ↥(halfTorus n)) ^ e =
      (⟨blockGen n i, blockGen_mem n i⟩ : ↥(halfTorus n)) ^ f := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_pow]
    exact h
  have hconj := congrArg (fun x : ↥(halfTorus n) => (torusCoord n).symm x) hsub
  rw [map_pow, map_pow, torusCoord_symm_blockGen, torusCoord_symm_blockGen] at hconj
  have heval := congrFun hconj j
  simp only [Pi.pow_apply, Pi.mulSingle_apply, hij.symm, if_false, one_pow] at heval
  rcases he with rfl | rfl | rfl <;>
    exact (by decide : (Multiplicative.ofAdd (1 : ZMod 3)) ^ _ ≠ 1) heval

theorem prod_two_cond {a b : Prop} [Decidable a] [Decidable b] :
    (if a then 2 else 1) * (if b then 2 else 1) = 1 ∨
    (if a then 2 else 1) * (if b then 2 else 1) = 2 ∨
    (if a then 2 else 1) * (if b then 2 else 1) = 4 := by
  by_cases ha : a <;> by_cases hb : b <;> simp [ha, hb]

omit [Finite G] in
theorem psi_u_blockGen {n : ℕ} {ψ : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2 →* G}
    (S : Finset (Fin (R n))) (σ : Equiv.Perm (Fin (R n))) (i : Fin (R n)) :
    ψ (u n S σ) * ψ (blockGen n i) * (ψ (u n S σ))⁻¹ =
      ψ ((blockGen n (σ.symm i)) ^
        ((if i ∈ S then 2 else 1) * (if σ.symm i ∈ S then 2 else 1))) := by
  rw [← map_mul, ← map_inv, ← map_mul, u_blockGen]

theorem ofAdd_one_pow_nat (e : ℕ) :
    (Multiplicative.ofAdd (1 : ZMod 3)) ^ e = Multiplicative.ofAdd ((e : ZMod 3)) := by
  induction e with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, ← ofAdd_add, Nat.cast_succ]

theorem blockGen_pow_ne_pow_of_ne_of_not_dvd {n : ℕ} {i j : Fin (R n)} (hij : i ≠ j)
    {e f : ℕ} (he : ¬ 3 ∣ e) :
    (blockGen n j) ^ e ≠ (blockGen n i) ^ f := by
  intro h
  have hsub : (⟨blockGen n j, blockGen_mem n j⟩ : ↥(halfTorus n)) ^ e =
      (⟨blockGen n i, blockGen_mem n i⟩ : ↥(halfTorus n)) ^ f := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_pow]
    exact h
  have hconj := congrArg (fun x : ↥(halfTorus n) => (torusCoord n).symm x) hsub
  rw [map_pow, map_pow, torusCoord_symm_blockGen, torusCoord_symm_blockGen] at hconj
  have heval := congrFun hconj j
  simp only [Pi.pow_apply, Pi.mulSingle_apply, hij.symm, if_false, one_pow, if_true] at heval
  have hfval := congrFun hconj i
  simp only [Pi.pow_apply, Pi.mulSingle_apply, hij, if_false, one_pow, if_true] at hfval
  have h3 : 3 ∣ e ∧ 3 ∣ f := by
    refine ⟨?_, ?_⟩
    · rw [ofAdd_one_pow_nat] at heval
      exact (ZMod.natCast_eq_zero_iff e 3).mp
        (Multiplicative.ofAdd.injective (by simpa using heval))
    · rw [ofAdd_one_pow_nat] at hfval
      exact (ZMod.natCast_eq_zero_iff f 3).mp
        (Multiplicative.ofAdd.injective (by simpa using hfval.symm))
  exact he h3.1

theorem not_three_dvd_prod_two_cond {a b : Prop} [Decidable a] [Decidable b] :
    ¬ 3 ∣ (if a then 2 else 1) * (if b then 2 else 1) := by
  by_cases ha : a <;> by_cases hb : b <;> simp [ha, hb]

theorem permMatSL_mul (n : ℕ) (σ τ : Equiv.Perm (Fin (R n))) :
    permMatSL n σ * permMatSL n τ = permMatSL n (τ * σ) := by
  apply Subtype.ext
  change σ.permMatrix (AdjoinRoot phi3) * τ.permMatrix (AdjoinRoot phi3) =
    (τ * σ).permMatrix (AdjoinRoot phi3)
  exact (Matrix.permMatrix_mul (R := AdjoinRoot phi3) (σ := τ) (τ := σ)).symm

theorem u_mul (n : ℕ) (S : Finset (Fin (R n)))
    (σ τ : Equiv.Perm (Fin (R n))) :
    u n S σ * u n S τ = u n S (τ * σ) := by
  rw [u_mul_eq]
  rw [show (CoordSL.theta phi3 (eps n) (permMatSL n σ) :
        SpecialLinearGroup (Fin (n + 1)) F2) *
        (CoordSL.theta phi3 (eps n) (permMatSL n τ) :
          SpecialLinearGroup (Fin (n + 1)) F2) =
        (CoordSL.theta phi3 (eps n) (permMatSL n (τ * σ)) :
          SpecialLinearGroup (Fin (n + 1)) F2) from by
    rw [← map_mul, permMatSL_mul]]
  rfl

theorem sigmaOf_mul (n : ℕ) (hR : 4 ≤ R n) (τ υ : Equiv.Perm (Fin 4)) :
    sigmaOf n hR τ * sigmaOf n hR υ = sigmaOf n hR (τ * υ) := by
  change Equiv.Perm.viaEmbeddingHom (fourEmb n hR) τ *
    Equiv.Perm.viaEmbeddingHom (fourEmb n hR) υ =
    Equiv.Perm.viaEmbeddingHom (fourEmb n hR) (τ * υ)
  rw [← map_mul]

theorem sigma1_mul_sigma2 (n : ℕ) (hR : 4 ≤ R n) :
    sigmaOf n hR tau1 * sigmaOf n hR tau2 = sigmaOf n hR (tau1 * tau2) :=
  sigmaOf_mul n hR tau1 tau2

theorem sigmaOf_symm_apply (n : ℕ) (hR : 4 ≤ R n) (τ : Equiv.Perm (Fin 4)) (i : Fin 4) :
    (sigmaOf n hR τ).symm (fourEmb n hR i) = fourEmb n hR (τ.symm i) := by
  change (Equiv.Perm.viaEmbeddingHom (fourEmb n hR) τ)⁻¹ (fourEmb n hR i) = _
  rw [← map_inv, Equiv.Perm.viaEmbeddingHom_apply, Equiv.Perm.viaEmbedding_apply]
  rfl
theorem tau12_symm_zero_ne : (tau1 * tau2).symm (0 : Fin 4) ≠ 0 := by decide

theorem sigma12_symm_zero_ne (n : ℕ) (hR : 4 ≤ R n) :
    (sigmaOf n hR tau1 * sigmaOf n hR tau2).symm (fourEmb n hR 0) ≠
      fourEmb n hR 0 := by
  rw [sigma1_mul_sigma2, sigmaOf_symm_apply]
  intro h
  exact tau12_symm_zero_ne ((fourEmb n hR).injective h)

theorem fourEmb_zero_ne_one (n : ℕ) (hR : 4 ≤ R n) :
    fourEmb n hR 1 ≠ fourEmb n hR 0 := by
  intro h
  exact (by decide : (1 : Fin 4) ≠ 0) ((fourEmb n hR).injective h)

theorem fourEmb_zero_ne_two (n : ℕ) (hR : 4 ≤ R n) :
    fourEmb n hR 2 ≠ fourEmb n hR 0 := by
  intro h
  exact (by decide : (2 : Fin 4) ≠ 0) ((fourEmb n hR).injective h)

theorem fourEmb_one_ne_two (n : ℕ) (hR : 4 ≤ R n) :
    fourEmb n hR 1 ≠ fourEmb n hR 2 := by
  intro h
  exact (by decide : (1 : Fin 4) ≠ 2) ((fourEmb n hR).injective h)

theorem mem_normalizer_of_conj_mem {G : Type} [Group G] {H : Subgroup G} {g : G}
    (hg2 : g * g = 1) (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) :
    g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact h y
  · intro hy
    have hg : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg2
    have hz : g * y * g ∈ H := by rwa [hg] at hy
    have hh := h (g * y * g) hz
    have hyy : g * (g * y * g) * g⁻¹ = y := by
      rw [hg]
      calc g * (g * y * g) * g = (g * g) * y * (g * g) := by group
        _ = y := by simp [hg2]
    rwa [hyy] at hh

theorem mem_normalizer_zpowers_of_commute {G : Type} [Group G] {g x : G}
    (h : Commute g x) : g ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
  have hx : (MulAut.conj g) x = x := by
    change g * x * g⁻¹ = x
    rw [h.eq, mul_assoc, mul_inv_cancel, mul_one]
  change Subgroup.zpowers ((MulAut.conj g) x) = Subgroup.zpowers x
  rw [hx]

omit [Finite G] in
theorem psi_u_mem_normalizer_halfTorus {n : ℕ}
    {ψ : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2 →* G}
    (S : Finset (Fin (R n))) (σ : Equiv.Perm (Fin (R n))) (hσ : σ * σ = 1) :
    ψ (u n S σ) ∈
      Subgroup.normalizer (((GGHalf.halfTorus n).map ψ : Subgroup G) : Set G) := by
  have hg2 : ψ (u n S σ) * ψ (u n S σ) = 1 := by
    rw [← map_mul, u_mul_self n S σ hσ, map_one]
  refine mem_normalizer_of_conj_mem hg2 ?_
  intro y hy
  obtain ⟨s, hsT, rfl⟩ := Subgroup.mem_map.mp hy
  have huc := u_conj_mem_halfTorus n S σ hsT
  have hconj : ψ (u n S σ) * ψ s * (ψ (u n S σ))⁻¹ =
      ψ (u n S σ * s * (u n S σ)⁻¹) := by
    rw [← map_mul, ← map_inv, ← map_mul]
  rw [hconj]
  exact Subgroup.mem_map.mpr ⟨_, huc, rfl⟩

theorem psi_u_mem_normalizer_zpowers {n : ℕ} {G : Type} [Group G] [Finite G]
    {ψ : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2 →* G}
    {L : Subgroup G} {x : G} {S : Finset (Fin (R n))} {σ : Equiv.Perm (Fin (R n))}
    (hL : ψ (u n S σ) ∈ L) (hLx : L ≤ Subgroup.centralizer ({x} : Set G)) :
    ψ (u n S σ) ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G) :=
  mem_normalizer_zpowers_of_commute
    (Subgroup.mem_centralizer_singleton_iff.mp (hLx hL))

theorem psi_u_mem_normalizer_sup {n : ℕ} {G : Type} [Group G] [Finite G]
    {ψ : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2 →* G}
    {Bs L : Subgroup G} {x : G}
    (hF : GGHalfTorusFrame Bs L (GGHalf.halfTorus n) ψ)
    (hBs : Bs = Subgroup.zpowers x ⊔ (GGHalf.halfTorus n).map ψ)
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G))
    (S : Finset (Fin (R n))) (σ : Equiv.Perm (Fin (R n))) (hσ : σ * σ = 1) :
    ψ (u n S σ) ∈ Subgroup.normalizer (Bs : Set G) := by
  have hL : ψ (u n S σ) ∈ L := by
    rw [← hF.range]
    exact ⟨u n S σ, rfl⟩
  rw [hBs]
  exact Subgroup.inf_normalizer_le_normalizer_sup _ _
    ⟨psi_u_mem_normalizer_zpowers hL hLx, psi_u_mem_normalizer_halfTorus S σ hσ⟩

theorem psi_u_involution {n : ℕ} {G : Type} [Group G] [Finite G]
    {ψ : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2 →* G}
    {S : Finset (Fin (R n))} {σ : Equiv.Perm (Fin (R n))} (hσ : σ * σ = 1) :
    ψ (u n S σ) * ψ (u n S σ) = 1 := by
  rw [← map_mul, u_mul_self n S σ hσ, map_one]

theorem psi_u_comm {n : ℕ} {G : Type} [Group G] [Finite G]
    {ψ : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2 →* G}
    {S : Finset (Fin (R n))} {σ τ : Equiv.Perm (Fin (R n))}
    (h : σ * τ = τ * σ) :
    ψ (u n S σ) * ψ (u n S τ) = ψ (u n S τ) * ψ (u n S σ) := by
  rw [← map_mul, ← map_mul, u_mul_comm n S σ τ h]

theorem psi_u_conj_blockGen_ne {n : ℕ} {G : Type} [Group G] [Finite G]
    {ψ : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2 →* G}
    {Bs L : Subgroup G} (hF : GGHalfTorusFrame Bs L (GGHalf.halfTorus n) ψ)
    (hR : 4 ≤ R n) (S : Finset (Fin (R n))) (σ : Equiv.Perm (Fin (R n))) {j : Fin (R n)}
    (hj : σ.symm (fourEmb n hR 0) = j) (hji : j ≠ fourEmb n hR 0) :
    ψ (u n S σ) * ψ (blockGen n (fourEmb n hR 0)) * (ψ (u n S σ))⁻¹ ≠
      ψ (blockGen n (fourEmb n hR 0)) := by
  intro hconj
  rw [psi_u_blockGen (n := n) S σ (fourEmb n hR 0), hj] at hconj
  have h2 : (blockGen n j) ^ ((if fourEmb n hR 0 ∈ S then 2 else 1) *
      (if j ∈ S then 2 else 1)) = blockGen n (fourEmb n hR 0) := hF.inj hconj
  refine (blockGen_pow_ne_pow_of_ne_of_not_dvd
    (e := (if fourEmb n hR 0 ∈ S then 2 else 1) * (if j ∈ S then 2 else 1))
    (f := 1) hji.symm (not_three_dvd_prod_two_cond)) ?_
  · simpa only [pow_one] using h2

theorem psi_u_ne_one {n : ℕ} {G : Type} [Group G] [Finite G]
    {ψ : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2 →* G}
    {Bs L : Subgroup G} (hF : GGHalfTorusFrame Bs L (GGHalf.halfTorus n) ψ)
    (hR : 4 ≤ R n) (S : Finset (Fin (R n))) (σ : Equiv.Perm (Fin (R n))) {j : Fin (R n)}
    (hj : σ.symm (fourEmb n hR 0) = j) (hji : j ≠ fourEmb n hR 0) :
    ψ (u n S σ) ≠ 1 := by
  intro h1
  have hmove : ψ (u n S σ) * ψ (blockGen n (fourEmb n hR 0)) * (ψ (u n S σ))⁻¹ =
      ψ (blockGen n (fourEmb n hR 0)) := by rw [h1]; group
  exact (psi_u_conj_blockGen_ne hF hR S σ hj hji) hmove

theorem psi_u_ne_of_symm_ne {n : ℕ} {G : Type} [Group G] [Finite G]
    {ψ : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2 →* G}
    {Bs L : Subgroup G} (hF : GGHalfTorusFrame Bs L (GGHalf.halfTorus n) ψ)
    (hR : 4 ≤ R n) (S : Finset (Fin (R n))) {σ τ : Equiv.Perm (Fin (R n))} {i j : Fin (R n)}
    (hi : σ.symm (fourEmb n hR 0) = i) (hj : τ.symm (fourEmb n hR 0) = j)
    (hij : i ≠ j) : ψ (u n S σ) ≠ ψ (u n S τ) := by
  intro h
  have hconj : ψ (u n S σ) * ψ (blockGen n (fourEmb n hR 0)) * (ψ (u n S σ))⁻¹ =
      ψ (u n S τ) * ψ (blockGen n (fourEmb n hR 0)) * (ψ (u n S τ))⁻¹ := by rw [h]
  rw [psi_u_blockGen (n := n) S σ (fourEmb n hR 0),
    psi_u_blockGen (n := n) S τ (fourEmb n hR 0), hi, hj] at hconj
  have h2 := hF.inj hconj
  exact (blockGen_pow_ne_pow_of_ne_of_not_dvd
    (e := (if fourEmb n hR 0 ∈ S then 2 else 1) * (if i ∈ S then 2 else 1))
    (f := (if fourEmb n hR 0 ∈ S then 2 else 1) * (if j ∈ S then 2 else 1))
    hij.symm (not_three_dvd_prod_two_cond)) h2

theorem ggConjAut_mul_self {G : Type} [Group G] {A : Subgroup G} {g : G}
    (hgN : g ∈ Subgroup.normalizer (A : Set G)) (hg2 : g * g = 1) :
    ggConjAut A hgN * ggConjAut A hgN = 1 := by
  ext a
  simp only [MulAut.mul_apply, ggConjAut_apply, MulAut.one_apply]
  calc g * (g * ↑a * g⁻¹) * g⁻¹ = (g * g) * ↑a * (g * g)⁻¹ := by group
    _ = ↑a := by rw [hg2]; group

theorem ggConjAut_mul_comm {G : Type} [Group G] {A : Subgroup G} {g h : G}
    (hgN : g ∈ Subgroup.normalizer (A : Set G))
    (hhN : h ∈ Subgroup.normalizer (A : Set G)) (hcomm : g * h = h * g) :
    ggConjAut A hgN * ggConjAut A hhN = ggConjAut A hhN * ggConjAut A hgN := by
  ext a
  simp only [MulAut.mul_apply, ggConjAut_apply]
  calc g * (h * a * h⁻¹) * g⁻¹ = (g * h) * a * (h⁻¹ * g⁻¹) := by group
    _ = (h * g) * a * (h⁻¹ * g⁻¹) := by rw [hcomm]
    _ = (h * g) * a * (g⁻¹ * h⁻¹) := by
        rw [show h⁻¹ * g⁻¹ = g⁻¹ * h⁻¹ by
          rw [← mul_inv_rev g h, hcomm, mul_inv_rev h g]]
    _ = h * (g * a * g⁻¹) * h⁻¹ := by group

theorem ggConjAut_ne_one_of_hker {G : Type} [Group G] {A K : Subgroup G} {g : G}
    (hgN : g ∈ Subgroup.normalizer (A : Set G)) (hgK : g ∈ K) (hg1 : g ≠ 1)
    (hker : ∀ x ∈ K, (∀ a ∈ A, x * a * x⁻¹ = a) → x = 1) :
    ggConjAut A hgN ≠ 1 := by
  intro h1
  apply hg1
  refine hker g hgK fun a ha => ?_
  have := congrArg (fun φ : MulAut ↥A => ((φ ⟨a, ha⟩ : ↥A) : G)) h1
  simpa [ggConjAut_apply] using this

theorem ggConjAut_ne_of_hker {G : Type} [Group G] {A K : Subgroup G} {g h : G}
    (hgN : g ∈ Subgroup.normalizer (A : Set G))
    (hhN : h ∈ Subgroup.normalizer (A : Set G)) (hgK : g ∈ K) (hhK : h ∈ K)
    (hne : g ≠ h)
    (hker : ∀ x ∈ K, (∀ a ∈ A, x * a * x⁻¹ = a) → x = 1) :
    ggConjAut A hgN ≠ ggConjAut A hhN := by
  intro h1
  apply hne
  have h2 : h⁻¹ * g ∈ K := K.mul_mem (K.inv_mem hhK) hgK
  have h3 : h⁻¹ * g = 1 := by
    refine hker (h⁻¹ * g) h2 fun a ha => ?_
    have h4 := congrArg (fun φ : MulAut ↥A => ((φ ⟨a, ha⟩ : ↥A) : G)) h1
    simp only [ggConjAut_apply] at h4
    calc (h⁻¹ * g) * a * (h⁻¹ * g)⁻¹
        = h⁻¹ * (g * a * g⁻¹) * h := by group
      _ = h⁻¹ * (h * a * h⁻¹) * h := by rw [h4]
      _ = a := by group
  have h5 : g = h := by
    have := congrArg (fun x => h * x) h3
    simpa [mul_assoc] using this
  exact h5

theorem ggQ2Lin_four_dvd_aut {G : Type} [Group G] [Finite G] {A J : Subgroup G} {g h : G}
    (hgJ : g ∈ J) (hhJ : h ∈ J)
    (hgN : g ∈ Subgroup.normalizer (A : Set G))
    (hhN : h ∈ Subgroup.normalizer (A : Set G))
    (hg2 : g * g = 1) (hh2 : h * h = 1) (hcomm : g * h = h * g)
    (hg1 : g ≠ 1) (hh1 : h ≠ 1) (hne : g ≠ h)
    (hker : ∀ x ∈ Subgroup.closure ({g, h} : Set G),
      (∀ a ∈ A, x * a * x⁻¹ = a) → x = 1) :
    4 ∣ Nat.card (ggAutomizer J A) := by
  classical
  have hgK : g ∈ Subgroup.closure ({g, h} : Set G) := Subgroup.subset_closure (by simp)
  have hhK : h ∈ Subgroup.closure ({g, h} : Set G) := Subgroup.subset_closure (by simp)
  have hφg2 : ggConjAut A hgN * ggConjAut A hgN = 1 := ggConjAut_mul_self hgN hg2
  have hφh2 : ggConjAut A hhN * ggConjAut A hhN = 1 := ggConjAut_mul_self hhN hh2
  have hφcomm : ggConjAut A hgN * ggConjAut A hhN =
      ggConjAut A hhN * ggConjAut A hgN := ggConjAut_mul_comm hgN hhN hcomm
  have hφg1 : ggConjAut A hgN ≠ 1 := ggConjAut_ne_one_of_hker hgN hgK hg1 hker
  have hφh1 : ggConjAut A hhN ≠ 1 := ggConjAut_ne_one_of_hker hhN hhK hh1 hker
  have hφne : ggConjAut A hgN ≠ ggConjAut A hhN :=
    ggConjAut_ne_of_hker hgN hhN hgK hhK hne hker
  have hmemg : ggConjAut A hgN ∈ ggAutomizer J A := ggConjAut_mem_ggAutomizer hgJ hgN
  have hmemh : ggConjAut A hhN ∈ ggAutomizer J A := ggConjAut_mem_ggAutomizer hhJ hhN
  have hle : Subgroup.closure ({ggConjAut A hgN, ggConjAut A hhN} : Set (MulAut ↥A)) ≤
      ggAutomizer J A :=
    (Subgroup.closure_le _).mpr (by
      rintro φ (rfl | rfl)
      · exact hmemg
      · exact hmemh)
  have hcard : Nat.card (Subgroup.closure
      ({ggConjAut A hgN, ggConjAut A hhN} : Set (MulAut ↥A))) = 4 :=
    CFSG.GroupTheory.card_closure_pair_eq_four hφg2 hφh2 hφcomm hφg1 hφh1 hφne
  have hdvd := Subgroup.card_dvd_of_le hle
  rwa [hcard] at hdvd

theorem ggQ2Lin_u_frame_mem {n : ℕ}
    {ψ : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2 →* G}
    (hS : GGQTwoSetting p B Bs x L D J)
    (hF : GGHalfTorusFrame Bs L (GGHalf.halfTorus n) ψ)
    (hBs : Bs = Subgroup.zpowers x ⊔ (GGHalf.halfTorus n).map ψ)
    (S : Finset (Fin (R n)))
    (hJ : J = Subgroup.map ψ
      ((classBlk (n := n) (s := R n) (r := Q n) (eps n) (fun _ => 1)).map
        (MulAut.conj (delta n S)).toMonoidHom))
    {σ : Equiv.Perm (Fin (R n))} (hσ : σ * σ = 1) :
    ψ (u n S σ) ∈ J ∧ ψ (u n S σ) ∈ Subgroup.normalizer (Bs : Set G) ∧
      ψ (u n S σ) * ψ (u n S σ) = 1 := by
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hS.1.1.tableB_facts.2.2.2.1
  refine ⟨?_, psi_u_mem_normalizer_sup hF hBs hLx S σ hσ, psi_u_involution hσ⟩
  rw [hJ]
  exact Subgroup.mem_map.mpr ⟨u n S σ, u_mem_classBlk n S σ, rfl⟩

theorem ggQ2Lin_four_dvd_of_moves {G : Type} [Group G] [Finite G] {A J : Subgroup G}
    {g h b0 : G} (hgJ : g ∈ J) (hhJ : h ∈ J)
    (hgN : g ∈ Subgroup.normalizer (A : Set G))
    (hhN : h ∈ Subgroup.normalizer (A : Set G))
    (hg2 : g * g = 1) (hh2 : h * h = 1) (hcomm : g * h = h * g)
    (hg1 : g ≠ 1) (hh1 : h ≠ 1) (hne : g ≠ h) (hb0 : b0 ∈ A)
    (hg_move : g * b0 * g⁻¹ ≠ b0) (hh_move : h * b0 * h⁻¹ ≠ b0)
    (hgh_move : (g * h) * b0 * (g * h)⁻¹ ≠ b0) :
    4 ∣ Nat.card (ggAutomizer J A) := by
  refine ggQ2Lin_four_dvd_aut hgJ hhJ hgN hhN hg2 hh2 hcomm hg1 hh1 hne ?_
  intro x hx hcent
  have hxset : x ∈ ({1, g, h, g * h} : Set G) := by
    rw [← CFSG.GroupTheory.coe_closure_pair_eq hg2 hh2 hcomm hg1 hh1 hne]
    exact hx
  rcases hxset with rfl | rfl | rfl | rfl
  · rfl
  · exact absurd (hcent b0 hb0) hg_move
  · exact absurd (hcent b0 hb0) hh_move
  · exact absurd (hcent b0 hb0) hgh_move

omit [Finite G] in
theorem ggQ2Lin_blockGen_mem_bstar {n : ℕ}
    {ψ : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2 →* G}
    (hBs : Bs = Subgroup.zpowers x ⊔ (GGHalf.halfTorus n).map ψ) (i : Fin (R n)) :
    ψ (blockGen n i) ∈ Bs := by
  rw [hBs]
  exact Subgroup.mem_sup_right (Subgroup.mem_map.mpr ⟨blockGen n i, blockGen_mem n i, rfl⟩)

theorem ggQ2Lin_four_dvd {n : ℕ}
    {ψ : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2 →* G}
    (hS : GGQTwoSetting p B Bs x L D J) (hn : 5 ≤ n)
    (hF : GGHalfTorusFrame Bs L (GGHalf.halfTorus n) ψ)
    (hBs : Bs = Subgroup.zpowers x ⊔ (GGHalf.halfTorus n).map ψ)
    {z : G} {t : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2} {a : ℤ}
    (hz : z = x ^ a * ψ t) (ht : t ∈ GGHalf.halfTorus n)
    (hDclos : D = Subgroup.closure ({x, z} : Set G))
    (hs : n + 1 - GGHalf.supp t ≤ 1) (hR : 4 ≤ R n) :
    4 ∣ Nat.card (ggAutomizer J Bs) := by
  classical
  set v : Fin (R n) → Multiplicative (ZMod 3) := (torusCoord n).symm ⟨t, ht⟩ with hvdef
  set S : Finset (Fin (R n)) := swapSet n v with hSdef
  have hJ := ggQ2Lin_J_eq_classBlk_conj hS hF hz ht hDclos hs hn
  rw [← hvdef, ← hSdef] at hJ
  set σ₁ : Equiv.Perm (Fin (R n)) := sigmaOf n hR tau1 with hσ₁def
  set σ₂ : Equiv.Perm (Fin (R n)) := sigmaOf n hR tau2 with hσ₂def
  set g : G := ψ (u n S σ₁) with hgdef; set h : G := ψ (u n S σ₂) with hhdef
  set b0 : G := ψ (blockGen n (fourEmb n hR 0)) with hb0def
  have hσ1 : σ₁ * σ₁ = 1 := by rw [hσ₁def]; exact sigma1_sq n hR
  have hσ2 : σ₂ * σ₂ = 1 := by rw [hσ₂def]; exact sigma2_sq n hR
  obtain ⟨hgJ, hgN, hg2⟩ := ggQ2Lin_u_frame_mem hS hF hBs S hJ hσ1
  obtain ⟨hhJ, hhN, hh2⟩ := ggQ2Lin_u_frame_mem hS hF hBs S hJ hσ2
  have hb0Bs : b0 ∈ Bs := by
    rw [hb0def]; exact ggQ2Lin_blockGen_mem_bstar hBs (fourEmb n hR 0)
  have hcomm : g * h = h * g := by
    rw [hgdef, hhdef]; exact psi_u_comm (sigma1_comm_sigma2 n hR)
  have hσ1s : σ₁.symm (fourEmb n hR 0) = fourEmb n hR 1 := by
    rw [hσ₁def]; exact sigma1_symm_zero n hR
  have hσ2s : σ₂.symm (fourEmb n hR 0) = fourEmb n hR 2 := by
    rw [hσ₂def]; exact sigma2_symm_zero n hR
  have hg_move : g * b0 * g⁻¹ ≠ b0 := by
    rw [hgdef, hb0def]
    exact psi_u_conj_blockGen_ne hF hR S σ₁ hσ1s (fourEmb_zero_ne_one n hR)
  have hh_move : h * b0 * h⁻¹ ≠ b0 := by
    rw [hhdef, hb0def]
    exact psi_u_conj_blockGen_ne hF hR S σ₂ hσ2s (fourEmb_zero_ne_two n hR)
  have hgh_move : (g * h) * b0 * (g * h)⁻¹ ≠ b0 := by
    rw [hgdef, hhdef, hb0def, ← map_mul, u_mul, ← sigma1_comm_sigma2 n hR]
    exact psi_u_conj_blockGen_ne hF hR S (σ₁ * σ₂) rfl (sigma12_symm_zero_ne n hR)
  have hg1 : g ≠ 1 := by
    rw [hgdef]; exact psi_u_ne_one hF hR S σ₁ hσ1s (fourEmb_zero_ne_one n hR)
  have hh1 : h ≠ 1 := by
    rw [hhdef]; exact psi_u_ne_one hF hR S σ₂ hσ2s (fourEmb_zero_ne_two n hR)
  have hne : g ≠ h := by
    rw [hgdef, hhdef]
    exact psi_u_ne_of_symm_ne hF hR S hσ1s hσ2s (fourEmb_one_ne_two n hR)
  exact ggQ2Lin_four_dvd_of_moves hgJ hhJ hgN hhN hg2 hh2 hcomm hg1 hh1 hne hb0Bs
    hg_move hh_move hgh_move

theorem ggQ2Lin_supp_eq_six {n : ℕ}
    {ψ : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2 →* G}
    (hS : GGQTwoSetting p B Bs x L D J) (hn : 5 ≤ n)
    (hF : GGHalfTorusFrame Bs L (GGHalf.halfTorus n) ψ)
    (hBs : Bs = Subgroup.zpowers x ⊔ (GGHalf.halfTorus n).map ψ)
    {z : G} {t : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2} {a : ℤ}
    (hz : z = x ^ a * ψ t) (ht : t ∈ GGHalf.halfTorus n)
    (hDclos : D = Subgroup.closure ({x, z} : Set G))
    (hs : n + 1 - GGHalf.supp t ≤ 1)
    (hguard : ¬ 4 ∣ Nat.card (ggAutomizer J Bs)) :
    GGHalf.supp t = 6 ∧ (n = 5 ∨ n = 6) := by
  classical
  set v : Fin (R n) → Multiplicative (ZMod 3) := (torusCoord n).symm ⟨t, ht⟩ with hvdef
  have htv : (torusCoord n v : SpecialLinearGroup (Fin (n + 1)) F2) = t :=
    congrArg Subtype.val ((torusCoord n).apply_symm_apply ⟨t, ht⟩)
  have hv : ∀ j, v j ≠ 1 := torusCoord_ne_one_of_supp n v (by rw [htv]; exact hs)
  have hsupp : GGHalf.supp t = 2 * R n := by
    rw [← htv, supp_torusCoord]
    have hfilter : (Finset.univ.filter fun j : Fin (R n) => v j ≠ 1) = Finset.univ :=
      Finset.filter_true_of_mem (fun j _ => hv j)
    rw [hfilter]
    simp
  have hR3 : R n = 3 := by
    have hRge : 3 ≤ R n := by unfold R; omega
    by_contra hne
    exact hguard (ggQ2Lin_four_dvd hS hn hF hBs hz ht hDclos hs (by omega))
  have hsupp6 : GGHalf.supp t = 6 := by rw [hsupp, hR3]
  have hn56 : n = 5 ∨ n = 6 := by
    have h := two_mul_R_add_Q n
    rw [hR3] at h
    have hQ := Q_le_one n
    omega
  exact ⟨hsupp6, hn56⟩


theorem supp_eq_two_mul_R {n : ℕ}
    {t : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2}
    (ht : t ∈ GGHalf.halfTorus n) (hs : n + 1 - GGHalf.supp t ≤ 1) :
    GGHalf.supp t = 2 * R n := by
  classical
  set v : Fin (R n) → Multiplicative (ZMod 3) := (torusCoord n).symm ⟨t, ht⟩ with hvdef
  have htv : (torusCoord n v : SpecialLinearGroup (Fin (n + 1)) F2) = t :=
    congrArg Subtype.val ((torusCoord n).apply_symm_apply ⟨t, ht⟩)
  have hv : ∀ j, v j ≠ 1 := torusCoord_ne_one_of_supp n v (by rw [htv]; exact hs)
  rw [← htv, supp_torusCoord]
  have hfilter : (Finset.univ.filter fun j : Fin (R n) => v j ≠ 1) = Finset.univ :=
    Finset.filter_true_of_mem (fun j _ => hv j)
  rw [hfilter]
  simp

theorem mem_ggAutDispl {G : Type} [Group G] {Bs J : Subgroup G} {g : G}
    (hgJ : g ∈ J) (hgN : g ∈ Subgroup.normalizer (Bs : Set G)) (b : ↥Bs) :
    ((b⁻¹ * ggConjAut Bs hgN b : ↥Bs) : G) ∈ ggAutDispl Bs (ggAutomizer J Bs) :=
  Subgroup.subset_closure ⟨ggConjAut Bs hgN, ggConjAut_mem_ggAutomizer hgJ hgN, b, rfl⟩

theorem ggQ2Lin_displ_coord_one {n : ℕ} (i j : Fin (R n)) (e : ℕ) :
    (torusCoord n).symm ((bg n i)⁻¹ * (bg n j) ^ e) =
      (Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod 3)))⁻¹ *
        (Pi.mulSingle j (Multiplicative.ofAdd (1 : ZMod 3))) ^ e := by
  rw [map_mul, map_inv, map_pow]
  simp only [bg]
  rw [torusCoord_symm_blockGen, torusCoord_symm_blockGen]

theorem ggQ2Lin_single_displ {n : ℕ}
    {ψ : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2 →* G}
    (hS : GGQTwoSetting p B Bs x L D J)
    (hF : GGHalfTorusFrame Bs L (GGHalf.halfTorus n) ψ)
    (hBs : Bs = Subgroup.zpowers x ⊔ (GGHalf.halfTorus n).map ψ)
    (S : Finset (Fin (R n)))
    (hJ : J = Subgroup.map ψ
      ((classBlk (n := n) (s := R n) (r := Q n) (eps n) (fun _ => 1)).map
        (MulAut.conj (delta n S)).toMonoidHom))
    {τ : Equiv.Perm (Fin (R n))} (hτ : τ * τ = 1)
    (i j : Fin (R n)) (hτi : τ.symm i = j) :
    ∃ (d : G) (t : ↥(GGHalf.halfTorus n)) (e : ℕ),
      d ∈ ggAutDispl Bs (ggAutomizer J Bs) ∧ ψ t = d ∧
        t = (bg n i)⁻¹ * (bg n j) ^ e ∧
        e = (if i ∈ S then 2 else 1) * (if j ∈ S then 2 else 1) := by
  obtain ⟨hgJ, hgN, -⟩ := ggQ2Lin_u_frame_mem hS hF hBs S hJ hτ
  let e : ℕ := (if i ∈ S then 2 else 1) * (if j ∈ S then 2 else 1)
  let b : ↥Bs := ⟨ψ (blockGen n i), by
    rw [hBs]
    exact Subgroup.mem_sup_right (Subgroup.mem_map.mpr ⟨blockGen n i, blockGen_mem n i, rfl⟩)⟩
  let d : G := ((b⁻¹ * ggConjAut Bs hgN b : ↥Bs) : G)
  let t : ↥(GGHalf.halfTorus n) := (bg n i)⁻¹ * (bg n j) ^ e
  refine ⟨d, t, e, mem_ggAutDispl hgJ hgN b, ?_, rfl, rfl⟩
  have h1 : ψ (u n S τ) * (b : G) * (ψ (u n S τ))⁻¹ = ψ ((blockGen n j) ^ e) := by
    change ψ (u n S τ) * ψ (blockGen n i) * (ψ (u n S τ))⁻¹ = _
    rw [← map_mul, ← map_inv, ← map_mul]
    rw [u_blockGen n S τ i, hτi]
  have hb : (b : G) = ψ (blockGen n i) := rfl
  have hφ : ((ggConjAut Bs hgN b : ↥Bs) : G) = ψ (u n S τ) * (b : G) * (ψ (u n S τ))⁻¹ :=
    rfl
  calc
    ψ t = (ψ (blockGen n i))⁻¹ * ψ ((blockGen n j) ^ e) := by
      simp only [t, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, bg, map_mul,
        map_inv, map_pow]
    _ = (ψ (blockGen n i))⁻¹ * (ψ (u n S τ) * (ψ (blockGen n i)) * (ψ (u n S τ))⁻¹) := by
      rw [h1]
    _ = ((b : ↥Bs) : G)⁻¹ * ((ggConjAut Bs hgN b : ↥Bs) : G) := by rw [hb, hφ]
    _ = d := rfl

theorem ggQ2Lin_ofAdd_inv_pow (a : ZMod 3) :
    ((Multiplicative.ofAdd (1 : ZMod 3))⁻¹) ^ a.val = Multiplicative.ofAdd (-a) := by
  calc ((Multiplicative.ofAdd (1 : ZMod 3))⁻¹) ^ a.val
      = ((Multiplicative.ofAdd (1 : ZMod 3)) ^ a.val)⁻¹ := inv_pow _ _
    _ = (Multiplicative.ofAdd ((a.val : ZMod 3)))⁻¹ := by rw [ofAdd_one_pow_nat]
    _ = (Multiplicative.ofAdd a)⁻¹ := by rw [ZMod.natCast_zmod_val]
    _ = Multiplicative.ofAdd (-a) := (ofAdd_neg a).symm

theorem ggQ2Lin_displ_coord_eval {n : ℕ} {i0 i1 i2 : Fin (R n)}
    (hi01 : i0 ≠ i1) (hi02 : i0 ≠ i2) (hi12 : i1 ≠ i2)
    {e1 e2 : ℕ} (w1 w2 : Fin (R n) → Multiplicative (ZMod 3))
    (hw1def : w1 = (Pi.mulSingle i0 (Multiplicative.ofAdd (1 : ZMod 3)))⁻¹ *
      (Pi.mulSingle i1 (Multiplicative.ofAdd (1 : ZMod 3))) ^ e1)
    (hw2def : w2 = (Pi.mulSingle i2 (Multiplicative.ofAdd (1 : ZMod 3)))⁻¹ *
      (Pi.mulSingle i1 (Multiplicative.ofAdd (1 : ZMod 3))) ^ e2)
    {t1 t2 : ↥(GGHalf.halfTorus n)}
    (ht1 : t1 = (bg n i0)⁻¹ * (bg n i1) ^ e1)
    (ht2 : t2 = (bg n i2)⁻¹ * (bg n i1) ^ e2) :
    (torusCoord n).symm t1 = w1 ∧ (torusCoord n).symm t2 = w2 ∧
      w1 i0 = (Multiplicative.ofAdd (1 : ZMod 3))⁻¹ ∧ w2 i0 = 1 ∧
      w1 i2 = 1 ∧ w2 i2 = (Multiplicative.ofAdd (1 : ZMod 3))⁻¹ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ht1, hw1def]; exact ggQ2Lin_displ_coord_one i0 i1 e1
  · rw [ht2, hw2def]; exact ggQ2Lin_displ_coord_one i2 i1 e2
  · rw [hw1def]
    rw [Pi.mul_apply, Pi.inv_apply, Pi.pow_apply, Pi.mulSingle_eq_same,
      Pi.mulSingle_eq_of_ne' hi01.symm, one_pow, mul_one]
  · rw [hw2def]
    rw [Pi.mul_apply, Pi.inv_apply, Pi.pow_apply, Pi.mulSingle_eq_of_ne' hi02.symm,
      Pi.mulSingle_eq_of_ne' hi01.symm,
      show (1 : Multiplicative (ZMod 3))⁻¹ = 1 from inv_one, one_pow, one_mul]
  · rw [hw1def]
    rw [Pi.mul_apply, Pi.inv_apply, Pi.pow_apply, Pi.mulSingle_eq_of_ne' hi02,
      Pi.mulSingle_eq_of_ne' hi12,
      show (1 : Multiplicative (ZMod 3))⁻¹ = 1 from inv_one, one_pow, one_mul]
  · rw [hw2def]
    rw [Pi.mul_apply, Pi.inv_apply, Pi.pow_apply, Pi.mulSingle_eq_same,
      Pi.mulSingle_eq_of_ne' hi12, one_pow, mul_one]

omit [Finite G] in
theorem ggQ2Lin_displ_indep {n : ℕ}
    {ψ : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2 →* G}
    {Bs L : Subgroup G} (hF : GGHalfTorusFrame Bs L (GGHalf.halfTorus n) ψ)
    {i0 i1 i2 : Fin (R n)} (hi01 : i0 ≠ i1) (hi02 : i0 ≠ i2) (hi12 : i1 ≠ i2)
    {e1 e2 : ℕ} {t1 t2 : ↥(GGHalf.halfTorus n)} {d1 d2 : G}
    (ht1 : t1 = (bg n i0)⁻¹ * (bg n i1) ^ e1)
    (ht2 : t2 = (bg n i2)⁻¹ * (bg n i1) ^ e2)
    (hd1 : ψ t1 = d1) (hd2 : ψ t2 = d2)
    (hd1mem : d1 ∈ ggAutDispl Bs (ggAutomizer J Bs))
    (hd2mem : d2 ∈ ggAutDispl Bs (ggAutomizer J Bs)) :
    Function.Injective (fun q : ZMod 3 × ZMod 3 =>
      (⟨d1 ^ q.1.val * d2 ^ q.2.val,
        Subgroup.mul_mem _ (Subgroup.pow_mem _ hd1mem _)
          (Subgroup.pow_mem _ hd2mem _)⟩ :
        ggAutDispl Bs (ggAutomizer J Bs))) := by
  let w1 : Fin (R n) → Multiplicative (ZMod 3) :=
    (Pi.mulSingle i0 (Multiplicative.ofAdd (1 : ZMod 3)))⁻¹ *
      (Pi.mulSingle i1 (Multiplicative.ofAdd (1 : ZMod 3))) ^ e1
  let w2 : Fin (R n) → Multiplicative (ZMod 3) :=
    (Pi.mulSingle i2 (Multiplicative.ofAdd (1 : ZMod 3)))⁻¹ *
      (Pi.mulSingle i1 (Multiplicative.ofAdd (1 : ZMod 3))) ^ e2
  obtain ⟨hw1, hw2, hw1_i0, hw2_i0, hw1_i2, hw2_i2⟩ :=
    ggQ2Lin_displ_coord_eval hi01 hi02 hi12 w1 w2 rfl rfl ht1 ht2
  intro p q hpq
  have hG : d1 ^ p.1.val * d2 ^ p.2.val = d1 ^ q.1.val * d2 ^ q.2.val :=
    congrArg Subtype.val hpq
  rw [← hd1, ← hd2, ← map_pow, ← map_pow, ← map_mul, ← map_pow, ← map_pow, ← map_mul] at hG
  have hT : t1 ^ p.1.val * t2 ^ p.2.val = t1 ^ q.1.val * t2 ^ q.2.val := by
    apply Subtype.ext
    simpa only [Subgroup.coe_mul, Subgroup.coe_pow] using hF.inj hG
  have hcoord := congrArg (fun z : ↥(GGHalf.halfTorus n) => (torusCoord n).symm z) hT
  simp only [map_mul, map_pow, hw1, hw2] at hcoord
  have h0 := congrFun hcoord i0
  have h2 := congrFun hcoord i2
  simp only [Pi.mul_apply, Pi.pow_apply, hw1_i0, hw2_i0, one_pow, mul_one] at h0
  simp only [Pi.mul_apply, Pi.pow_apply, hw1_i2, hw2_i2, one_pow, one_mul] at h2
  have hp1 : p.1 = q.1 := by
    have h := h0
    rw [ggQ2Lin_ofAdd_inv_pow p.1, ggQ2Lin_ofAdd_inv_pow q.1] at h
    exact neg_injective (Multiplicative.ofAdd.injective h)
  have hp2 : p.2 = q.2 := by
    have h := h2
    rw [ggQ2Lin_ofAdd_inv_pow p.2, ggQ2Lin_ofAdd_inv_pow q.2] at h
    exact neg_injective (Multiplicative.ofAdd.injective h)
  exact Prod.ext hp1 hp2

theorem ggQ2Lin_displ_card {n : ℕ}
    {ψ : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2 →* G}
    {Bs L : Subgroup G} (hF : GGHalfTorusFrame Bs L (GGHalf.halfTorus n) ψ)
    {i0 i1 i2 : Fin (R n)} (hi01 : i0 ≠ i1) (hi02 : i0 ≠ i2) (hi12 : i1 ≠ i2)
    {e1 e2 : ℕ} {t1 t2 : ↥(GGHalf.halfTorus n)} {d1 d2 : G}
    (ht1 : t1 = (bg n i0)⁻¹ * (bg n i1) ^ e1)
    (ht2 : t2 = (bg n i2)⁻¹ * (bg n i1) ^ e2)
    (hd1 : ψ t1 = d1) (hd2 : ψ t2 = d2)
    (hd1mem : d1 ∈ ggAutDispl Bs (ggAutomizer J Bs))
    (hd2mem : d2 ∈ ggAutDispl Bs (ggAutomizer J Bs)) :
    9 ≤ Nat.card (ggAutDispl Bs (ggAutomizer J Bs)) := by
  have h9 := Nat.card_le_card_of_injective _ (ggQ2Lin_displ_indep hF hi01 hi02 hi12
    ht1 ht2 hd1 hd2 hd1mem hd2mem)
  simpa [Nat.card_prod, Nat.card_zmod] using h9

theorem ggQ2Lin_nine_le_displ {n : ℕ}
    {ψ : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2 →* G}
    (hS : GGQTwoSetting p B Bs x L D J) (hn : 5 ≤ n)
    (hF : GGHalfTorusFrame Bs L (GGHalf.halfTorus n) ψ)
    (hBs : Bs = Subgroup.zpowers x ⊔ (GGHalf.halfTorus n).map ψ)
    {z : G} {t : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2} {a : ℤ}
    (hz : z = x ^ a * ψ t) (ht : t ∈ GGHalf.halfTorus n)
    (hDclos : D = Subgroup.closure ({x, z} : Set G))
    (hs : n + 1 - GGHalf.supp t ≤ 1) (hsix : GGHalf.supp t = 6) :
    9 ≤ Nat.card (ggAutDispl Bs (ggAutomizer J Bs)) := by
  classical
  have hsupp : GGHalf.supp t = 2 * R n := supp_eq_two_mul_R ht hs
  have hR3 : R n = 3 := by omega
  set v : Fin (R n) → Multiplicative (ZMod 3) := (torusCoord n).symm ⟨t, ht⟩ with hvdef
  set S : Finset (Fin (R n)) := swapSet n v with hSdef
  have hJ := ggQ2Lin_J_eq_classBlk_conj hS hF hz ht hDclos hs hn
  rw [← hvdef, ← hSdef] at hJ
  let i0 : Fin (R n) := ⟨0, by omega⟩
  let i1 : Fin (R n) := ⟨1, by omega⟩
  let i2 : Fin (R n) := ⟨2, by omega⟩
  let τ1 : Equiv.Perm (Fin (R n)) := Equiv.swap i0 i1
  let τ2 : Equiv.Perm (Fin (R n)) := Equiv.swap i1 i2
  have hτ1sq : τ1 * τ1 = 1 := by
    change (Equiv.swap i0 i1).trans (Equiv.swap i0 i1) = Equiv.refl _
    rw [Equiv.swap_swap]
  have hτ2sq : τ2 * τ2 = 1 := by
    change (Equiv.swap i1 i2).trans (Equiv.swap i1 i2) = Equiv.refl _
    rw [Equiv.swap_swap]
  have hτ1i0 : τ1.symm i0 = i1 := by
    change (Equiv.swap i0 i1).symm i0 = i1
    rw [Equiv.symm_swap, Equiv.swap_apply_left]
  have hτ2i2 : τ2.symm i2 = i1 := by
    change (Equiv.swap i1 i2).symm i2 = i1
    rw [Equiv.symm_swap, Equiv.swap_apply_right]
  have hi01 : i0 ≠ i1 := by
    intro h
    have := congrArg Fin.val h
    simp [i0, i1] at this
  have hi02 : i0 ≠ i2 := by
    intro h
    have := congrArg Fin.val h
    simp [i0, i2] at this
  have hi12 : i1 ≠ i2 := by
    intro h
    have := congrArg Fin.val h
    simp [i1, i2] at this
  obtain ⟨d1, t1, e1, hd1mem, hd1, ht1, -⟩ :=
    ggQ2Lin_single_displ hS hF hBs S hJ hτ1sq i0 i1 hτ1i0
  obtain ⟨d2, t2, e2, hd2mem, hd2, ht2, -⟩ :=
    ggQ2Lin_single_displ hS hF hBs S hJ hτ2sq i2 i1 hτ2i2
  exact ggQ2Lin_displ_card hF hi01 hi02 hi12 ht1 ht2 hd1 hd2 hd1mem hd2mem



theorem ggQ2Lin_thetaMat_injective {n s r : ℕ}
    (ε : Fin (n + 1) ≃ (Fin (rootPB phi3).dim × Fin s) ⊕ Fin r) :
    Function.Injective (CoordSL.thetaMat phi3 ε) := by
  intro A B h
  have h2 := congrArg (CoordSL.frameForm phi3 ε) h
  rw [CoordSL.frameForm_thetaMat, CoordSL.frameForm_thetaMat] at h2
  ext i j
  have h3 := LinearMap.congr_fun h2
    (Pi.single j (1 : AdjoinRoot phi3), fun _ => (0 : F2))
  rw [CoordSL.blockAct_apply, CoordSL.blockAct_apply] at h3
  have := congrFun (congrArg Prod.fst h3) i
  simpa [Matrix.mulVec_single] using this

theorem ggQ2Lin_torusCoord_eq_nsSL {n : ℕ}
    {u : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2}
    (hu : u ∈ GGHalf.halfTorus n) :
    u = SLNS.nsSL (eps n) det_rootMat_phi3
      (fun i => (Multiplicative.toAdd ((torusCoord n).symm ⟨u, hu⟩ i)).val) := by
  set v := (torusCoord n).symm ⟨u, hu⟩ with hv
  have h1 : ((torusCoord n) v : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2) = u :=
    congrArg Subtype.val ((torusCoord n).apply_symm_apply ⟨u, hu⟩)
  rw [← h1, torusCoord_apply_prod, ← nsSL_eq_prod]

theorem ggQ2Lin_classBlk_torus_diagonal {n : ℕ}
    {u : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2}
    {k : Fin (R n) → ℕ}
    (hu_nsSL : u = SLNS.nsSL (eps n) det_rootMat_phi3 k)
    (huC : u ∈ classBlk (n := n) (s := R n) (r := Q n) (eps n) (fun _ => 1)) :
    ∃ N : Matrix.SpecialLinearGroup (Fin (R n)) (AdjoinRoot phi3),
      (N : Matrix (Fin (R n)) (Fin (R n)) (AdjoinRoot phi3)) =
        Matrix.diagonal (fun i => AdjoinRoot.root phi3 ^ k i) := by
  obtain ⟨N, -, hNθ⟩ := Subgroup.mem_map.mp huC
  refine ⟨N, ?_⟩
  apply ggQ2Lin_thetaMat_injective (s := R n) (r := Q n) (eps n)
  calc
    CoordSL.thetaMat phi3 (eps n) (N : Matrix (Fin (R n)) (Fin (R n)) (AdjoinRoot phi3))
        = (CoordSL.theta phi3 (eps n) N : Matrix (Fin (n + 1)) (Fin (n + 1)) GGHalf.F2) :=
      rfl
    _ = (u : Matrix (Fin (n + 1)) (Fin (n + 1)) GGHalf.F2) := congrArg Subtype.val hNθ
    _ = (SLNS.nsSL (eps n) det_rootMat_phi3 k :
          Matrix (Fin (n + 1)) (Fin (n + 1)) GGHalf.F2) := congrArg Subtype.val hu_nsSL
    _ = SLNS.nsMat (eps n) (rootMat phi3) k := rfl
    _ = CoordSL.thetaMat phi3 (eps n)
          (Matrix.diagonal (fun i => AdjoinRoot.root phi3 ^ k i)) :=
      (CoordSL.thetaMat_diagonal (g := phi3) (ε := eps n) (k := k)).symm

theorem ggQ2Lin_classBlk_torus_det {n : ℕ}
    {u : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2}
    {k : Fin (R n) → ℕ}
    (hu_nsSL : u = SLNS.nsSL (eps n) det_rootMat_phi3 k)
    (huC : u ∈ classBlk (n := n) (s := R n) (r := Q n) (eps n) (fun _ => 1)) :
    (∏ i : Fin (R n), AdjoinRoot.root phi3 ^ k i) = 1 := by
  obtain ⟨N, hNval⟩ := ggQ2Lin_classBlk_torus_diagonal hu_nsSL huC
  have h := N.2
  rw [hNval, Matrix.det_diagonal] at h
  exact h

theorem ggQ2Lin_classBlk_torus_coord_one {n : ℕ}
    {u : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2}
    {v : Fin (R n) → Multiplicative (ZMod 3)}
    (hsuppv : GGHalf.supp u = 2 * (Finset.univ.filter fun j : Fin (R n) => v j ≠ 1).card)
    (hNdet : (∏ i : Fin (R n), AdjoinRoot.root phi3 ^
      (Multiplicative.toAdd (v i)).val) = 1)
    (hsupp : GGHalf.supp u = 2) : False := by
  rw [hsuppv] at hsupp
  have hcard : (Finset.univ.filter fun j : Fin (R n) => v j ≠ 1).card = 1 := by omega
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hcard
  have hvj : v j ≠ 1 := by
    have hmem : j ∈ Finset.univ.filter (fun j : Fin (R n) => v j ≠ 1) := by
      rw [hj]; exact Finset.mem_singleton_self j
    exact (Finset.mem_filter.mp hmem).2
  have hvi : ∀ i, i ≠ j → v i = 1 := by
    intro i hi
    by_contra hne
    have hmem : i ∈ Finset.univ.filter (fun j : Fin (R n) => v j ≠ 1) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ i, hne⟩
    rw [hj] at hmem
    exact hi (Finset.mem_singleton.mp hmem)
  have hzero : ∀ i, i ≠ j → (Multiplicative.toAdd (v i)).val = 0 := by
    intro i hi
    rw [hvi i hi]
    rfl
  have hprod : (∏ i : Fin (R n), AdjoinRoot.root phi3 ^
      (Multiplicative.toAdd (v i)).val) =
      AdjoinRoot.root phi3 ^ (Multiplicative.toAdd (v j)).val := by
    rw [Finset.prod_eq_single j]
    · intro i _ hi; rw [hzero i hi, pow_zero]
    · intro hjm; exact absurd (Finset.mem_univ j) hjm
  have hroot : AdjoinRoot.root phi3 ^ (Multiplicative.toAdd (v j)).val = 1 := by
    rw [hprod] at hNdet
    exact hNdet
  have hbne : Multiplicative.toAdd (v j) ≠ 0 := by
    intro h0
    apply hvj
    have h1 : v j = Multiplicative.ofAdd (Multiplicative.toAdd (v j)) := rfl
    rw [h1, h0]
    rfl
  exact (CoordSL.root_pow_val_ne_one
    (CoordSL.root_isPrimitiveRoot Nat.prime_three natCast_three_ne_zero
      phi3_dvd_cyclotomic) hbne) hroot

theorem ggQ2Lin_classBlk_torus_supp_ne_two {n : ℕ}
    {u : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2}
    (huT : u ∈ GGHalf.halfTorus n)
    (huC : u ∈ classBlk (n := n) (s := R n) (r := Q n) (eps n) (fun _ => 1)) :
    GGHalf.supp u ≠ 2 := by
  classical
  set v := (torusCoord n).symm ⟨u, huT⟩ with hv
  have hu_nsSL : u = SLNS.nsSL (eps n) det_rootMat_phi3
      (fun i => (Multiplicative.toAdd (v i)).val) := by
    simpa [hv] using ggQ2Lin_torusCoord_eq_nsSL huT
  have hNdet : (∏ i : Fin (R n), AdjoinRoot.root phi3 ^
      (Multiplicative.toAdd (v i)).val) = 1 := ggQ2Lin_classBlk_torus_det hu_nsSL huC
  have hsuppv : GGHalf.supp u = 2 * (Finset.univ.filter fun j : Fin (R n) => v j ≠ 1).card := by
    have h := supp_torusCoord n v
    have hu_eq : ((torusCoord n) v : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2) = u :=
      congrArg Subtype.val ((torusCoord n).apply_symm_apply ⟨u, huT⟩)
    rw [← hu_eq]
    exact h
  intro hsupp
  exact ggQ2Lin_classBlk_torus_coord_one hsuppv hNdet hsupp

theorem ggQ2Lin_delta_conj_mem_halfTorus (n : ℕ) (S : Finset (Fin (R n)))
    {t : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2}
    (ht : t ∈ GGHalf.halfTorus n) :
    delta n S * t * (delta n S)⁻¹ ∈ GGHalf.halfTorus n := by
  refine conj_mem_closure_of_gens {x | ∃ k : Fin n, k.val % 2 = 0 ∧ x = omegaBlock n k}
    (GGHalf.halfTorus n) (delta n S) rfl ?_ t ht
  rintro x ⟨k, hk, rfl⟩
  obtain ⟨i, rfl⟩ := exists_pairIdx_of_even hk
  show delta n S * blockGen n i * (delta n S)⁻¹ ∈ GGHalf.halfTorus n
  by_cases hi : i ∈ S
  · rw [delta_conj_blockGen_of_mem n S hi]
    exact Subgroup.inv_mem _ (blockGen_mem n i)
  · rw [delta_conj_blockGen_of_not_mem n S hi]
    exact blockGen_mem n i

theorem ggQ2Lin_supp_ne_two_of_mem_classBlkConj {n : ℕ}
    (S : Finset (Fin (R n)))
    {u : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2}
    (huT : u ∈ GGHalf.halfTorus n)
    (huK : u ∈ (classBlk (n := n) (s := R n) (r := Q n) (eps n) (fun _ => 1)).map
      (MulAut.conj (delta n S)).toMonoidHom) :
    GGHalf.supp u ≠ 2 := by
  obtain ⟨w, hwC, hwu⟩ := Subgroup.mem_map.mp huK
  have hwT : w ∈ GGHalf.halfTorus n := by
    have hwu' : delta n S * w * (delta n S)⁻¹ = u := hwu
    have hw_eq : w = (delta n S)⁻¹ * u * delta n S := by
      rw [← hwu']; group
    rw [hw_eq, delta_inv_eq_self n S]
    have h := ggQ2Lin_delta_conj_mem_halfTorus n S huT
    rwa [delta_inv_eq_self n S] at h
  have hsuppw := ggQ2Lin_classBlk_torus_supp_ne_two hwT hwC
  have hsupp_eq : GGHalf.supp u = GGHalf.supp w := by
    rw [← hwu]
    exact GGHalf.supp_conj (delta n S) w
  rwa [hsupp_eq]


theorem ggQ2Lin_mem_bstar_decomp {n : ℕ}
    {ψ : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2 →* G}
    (hS : GGQTwoSetting p B Bs x L D J)
    (hF : GGHalfTorusFrame Bs L (GGHalf.halfTorus n) ψ)
    (hBs : Bs = Subgroup.zpowers x ⊔ (GGHalf.halfTorus n).map ψ)
    {d : G} (hd : d ∈ Bs) :
    ∃ (a : ℤ) (t : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2),
      t ∈ GGHalf.halfTorus n ∧ d = x ^ a * ψ t := by
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hS.1.1.tableB_facts.2.2.2.1
  have hcent : Subgroup.zpowers x ≤
      Subgroup.centralizer (((GGHalf.halfTorus n).map ψ : Subgroup G) : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hb
    have hbtL : ψ t ∈ L := by rw [← hF.range]; exact ⟨t, rfl⟩
    have hcomm : Commute x (ψ t) := by
      rw [Commute]
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hLx hbtL)).symm
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ha
    rw [← hk]
    exact (hcomm.zpow_left k).symm
  have hnormal : Subgroup.zpowers x ≤
      Subgroup.normalizer (((GGHalf.halfTorus n).map ψ : Subgroup G) : Set G) :=
    hcent.trans (Subgroup.centralizer_le_normalizer _)
  have hdmem : d ∈ (((Subgroup.zpowers x ⊔ (GGHalf.halfTorus n).map ψ : Subgroup G)) : Set G) := by
    rw [← hBs]; exact hd
  rw [Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.zpowers x)
    ((GGHalf.halfTorus n).map ψ) hnormal, Set.mem_mul] at hdmem
  obtain ⟨a, ha, b, hb, hdab⟩ := hdmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hb
  exact ⟨k, t, ht, by rw [← hdab, ← hk]⟩

theorem ggQ2Lin_inf_le_map_halfTorus_inf {n : ℕ}
    {ψ : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2 →* G}
    (hS : GGQTwoSetting p B Bs x L D J)
    (hF : GGHalfTorusFrame Bs L (GGHalf.halfTorus n) ψ)
    (hBs : Bs = Subgroup.zpowers x ⊔ (GGHalf.halfTorus n).map ψ)
    {K' : Subgroup (Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2)}
    (hJ : J = Subgroup.map ψ K') :
    ggAutDispl Bs (ggAutomizer J Bs) ≤
      Subgroup.map ψ (GGHalf.halfTorus n ⊓ K') := by
  have hN : Bs ≤ Subgroup.normalizer (L : Set G) :=
    GGDichotomy.le_normalizer_of_innerDiagOn hS.1.2.2.1.1
  have hBsJ : Bs ≤ Subgroup.normalizer (J : Set G) :=
    QTwoCav.bstar_le_normalizer_j hS hN
  intro d hd
  have hdinf := ggAutDispl_le_inf hBsJ hd
  obtain ⟨hdBs, hdJ⟩ := hdinf
  obtain ⟨k, hkK', hkd⟩ := Subgroup.mem_map.mp (by rw [← hJ]; exact hdJ)
  obtain ⟨a, t, ht, hdt⟩ := ggQ2Lin_mem_bstar_decomp hS hF hBs hdBs
  have hkL : ψ k ∈ L := by rw [← hF.range]; exact ⟨k, rfl⟩
  have htL : ψ t ∈ L := by rw [← hF.range]; exact ⟨t, rfl⟩
  have hxaL : x ^ a ∈ L := by
    have hx : x ^ a = ψ k * (ψ t)⁻¹ := by rw [hkd, hdt]; group
    rw [hx]
    exact L.mul_mem hkL (L.inv_mem htL)
  have hxcent : x ^ a ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hxl : Commute x l :=
      (Subgroup.mem_centralizer_singleton_iff.mp (hS.1.1.tableB_facts.2.2.2.1 hl)).symm
    exact (hxl.zpow_left a).eq.symm
  have hxbot : x ^ a = 1 := by
    have hZ : (⟨x ^ a, hxaL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro z
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxcent z z.2)
    rw [ggQ2Lin_center_eq_bot hF] at hZ
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hZ)
  have hψeq : ψ k = ψ t := by
    rw [hkd, hdt, hxbot, one_mul]
  have hkt : k = t := hF.inj hψeq
  exact Subgroup.mem_map.mpr ⟨t, ⟨ht, hkt ▸ hkK'⟩, by rw [hdt, hxbot, one_mul]⟩


theorem ggQ2Lin_oneBlock_of_supp {n : ℕ} {H : Type} [Group H]
    {ψ : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2 →* G}
    (hS : GGQTwoSetting p B Bs x L D J)
    (hF : GGHalfTorusFrame Bs L (GGHalf.halfTorus n) ψ)
    (hBs : Bs = Subgroup.zpowers x ⊔ (GGHalf.halfTorus n).map ψ)
    (S : Finset (Fin (R n)))
    (hJ : J = Subgroup.map ψ
      ((classBlk (n := n) (s := R n) (r := Q n) (eps n) (fun _ => 1)).map
        (MulAut.conj (delta n S)).toMonoidHom))
    {t0 : H} {ι : H ≃* Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2}
    {e : H ≃* ↥L} (he : ∀ x, ((e x : ↥L) : G) = ψ (ι x))
    (hιsupp : GGHalf.supp (ι t0) = 2) :
    GGQTwoVACOneBlock L (ggAutDispl Bs (ggAutomizer J Bs)) t0 := by
  refine ⟨e, ?_⟩
  intro d hdE hconj
  have hdle : (d : G) ∈ Subgroup.map ψ
      (GGHalf.halfTorus n ⊓ (classBlk (n := n) (s := R n) (r := Q n) (eps n)
        (fun _ => 1)).map (MulAut.conj (delta n S)).toMonoidHom) :=
    ggQ2Lin_inf_le_map_halfTorus_inf hS hF hBs hJ hdE
  obtain ⟨k, hk, hψk⟩ := Subgroup.mem_map.mp hdle
  let u : H := e.symm d
  have hue : e u = d := e.apply_symm_apply d
  have huk : ι u = k := by
    apply hF.inj
    rw [← he u, hψk]
    exact congrArg Subtype.val hue
  have hsuppk : GGHalf.supp (ι u) ≠ 2 := by
    rw [huk]
    exact ggQ2Lin_supp_ne_two_of_mem_classBlkConj S hk.1 hk.2
  obtain ⟨c, hc⟩ := hconj
  have hc_eq : (↑c : ↥L) * d * (↑c)⁻¹ = e t0 := by
    rw [hc]; group
  have hc' : e.symm (↑c) * u * (e.symm (↑c))⁻¹ = t0 := by
    apply e.injective
    rw [map_mul, map_mul, map_inv, e.apply_symm_apply, hue]
    exact hc_eq
  have hc'' := congrArg ι hc'
  simp only [map_mul, map_inv] at hc''
  have hsupp_eq : GGHalf.supp (ι u) = GGHalf.supp (ι t0) := by
    rw [← hc'', GGHalf.supp_conj]
  rw [hιsupp] at hsupp_eq
  exact hsuppk hsupp_eq


theorem ggQ2Lin_D_eq_closure_of_mem_not_zpowers (hS : GGQTwoSetting p B Bs x L D J)
    (hp : p = 3) {z : G} (hzD : z ∈ D) (hzx : z ∉ Subgroup.zpowers x) :
    D = Subgroup.closure ({x, z} : Set G) := by
  have hcfg : GGConfig p B Bs x L D J := hS.1.1
  have hDJ : LargeEvenStdSub p B x L D J := hcfg.2.2
  obtain ⟨hDleB, hElemD, hcardD, hxD, -, -, -⟩ := hDJ.1
  have hcardD9 : Nat.card D = 9 := by rw [hcardD, hp]; norm_num
  have hxcard : Nat.card (Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers, hcfg.orderOf_x, hp]
  have hxD' : x ∈ Subgroup.closure ({x, z} : Set G) :=
    Subgroup.subset_closure (by simp)
  have hzD' : z ∈ Subgroup.closure ({x, z} : Set G) :=
    Subgroup.subset_closure (by simp)
  have hle : Subgroup.closure ({x, z} : Set G) ≤ D := by
    rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact hxD
    · exact hzD
  have hlt : Subgroup.zpowers x < Subgroup.closure ({x, z} : Set G) := by
    refine lt_of_le_of_ne (Subgroup.zpowers_le.mpr hxD') ?_
    intro heq
    exact hzx (heq ▸ hzD')
  have hdvd : Nat.card (Subgroup.closure ({x, z} : Set G)) ∣ 9 := by
    simpa [hcardD9] using Subgroup.card_dvd_of_le hle
  have h3dvd : 3 ∣ Nat.card (Subgroup.closure ({x, z} : Set G)) := by
    have h := Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hxD')
    rwa [hxcard] at h
  have hgt : 3 < Nat.card (Subgroup.closure ({x, z} : Set G)) := by
    have := Subgroup.card_lt_of_lt hlt
    rwa [hxcard] at this
  have hcard : Nat.card (Subgroup.closure ({x, z} : Set G)) = 9 := by
    have hle9 : Nat.card (Subgroup.closure ({x, z} : Set G)) ≤ 9 :=
      Nat.le_of_dvd (by norm_num) hdvd
    interval_cases Nat.card (Subgroup.closure ({x, z} : Set G)) <;> omega
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hcardD9])).symm

noncomputable local instance ggQ2LinFintypeF2 : Fintype GGHalf.F2 := Fintype.ofFinite _

theorem ggQ2Lin_card_f2 : Fintype.card GGHalf.F2 = 2 := by
  rw [← Nat.card_eq_fintype_card]
  exact GaloisField.card 2 1 (by omega)

@[expose] noncomputable def ggQ2LinIota (d : ℕ) :
    Matrix.SpecialLinearGroup (Fin d) (ZMod 2) ≃*
      Matrix.SpecialLinearGroup (Fin d) GGHalf.F2 where
  toFun := Matrix.SpecialLinearGroup.map
    (ZMod.ringEquiv GGHalf.F2 ggQ2Lin_card_f2).toRingHom
  invFun := Matrix.SpecialLinearGroup.map
    (ZMod.ringEquiv GGHalf.F2 ggQ2Lin_card_f2).symm.toRingHom
  left_inv x := by
    apply Subtype.ext
    ext i j
    exact (ZMod.ringEquiv GGHalf.F2 ggQ2Lin_card_f2).symm_apply_apply (x i j)
  right_inv x := by
    apply Subtype.ext
    ext i j
    exact (ZMod.ringEquiv GGHalf.F2 ggQ2Lin_card_f2).apply_symm_apply (x i j)
  map_mul' x y := (Matrix.SpecialLinearGroup.map
    (ZMod.ringEquiv GGHalf.F2 ggQ2Lin_card_f2).toRingHom).map_mul x y

theorem ggQ2LinIota_apply (d : ℕ)
    (x : Matrix.SpecialLinearGroup (Fin d) (ZMod 2)) :
    (ggQ2LinIota d x : Matrix (Fin d) (Fin d) GGHalf.F2) =
      Matrix.SpecialLinearGroup.map
        (ZMod.ringEquiv GGHalf.F2 ggQ2Lin_card_f2).toRingHom x := rfl

theorem ggQ2LinIota_apply_entry (d : ℕ)
    (x : Matrix.SpecialLinearGroup (Fin d) (ZMod 2)) (i j : Fin d) :
    (ggQ2LinIota d x : Matrix (Fin d) (Fin d) GGHalf.F2) i j =
      (ZMod.ringEquiv GGHalf.F2 ggQ2Lin_card_f2) (x i j) := by
  rw [ggQ2LinIota_apply, Matrix.SpecialLinearGroup.map_apply_coe,
    RingHom.mapMatrix_apply, Matrix.map_apply]
  rfl

theorem ggQ2LinIota_W6T_zero :
    ggQ2LinIota 6 (CFSG.RankThree.PartTwo.Sec4.RonanK429F.W6.T 0) = omegaBlock 5 0 := by
  apply Subtype.ext
  ext i j
  rw [ggQ2LinIota_apply_entry]
  fin_cases i <;> fin_cases j <;>
    simp [CFSG.RankThree.PartTwo.Sec4.RonanK429F.W6.coe_T,
      CFSG.RankThree.PartTwo.Sec4.RonanK429F.W6.t1M,
      omegaBlock_coe_sum, Matrix.single, one_add_one_eq_two, gf2_two]

theorem ggQ2LinIota_W7T_zero :
    ggQ2LinIota 7 (CFSG.RankThree.PartTwo.Sec4.RonanK429F.W7.T 0) = omegaBlock 6 0 := by
  apply Subtype.ext
  ext i j
  rw [ggQ2LinIota_apply_entry]
  fin_cases i <;> fin_cases j <;>
    simp [CFSG.RankThree.PartTwo.Sec4.RonanK429F.W7.coe_T,
      CFSG.RankThree.PartTwo.Sec4.RonanK429F.W7.t1M,
      omegaBlock_coe_sum, Matrix.single, one_add_one_eq_two, gf2_two]

theorem ggQ2LinIota_W6T_supp :
    GGHalf.supp (ggQ2LinIota 6 (CFSG.RankThree.PartTwo.Sec4.RonanK429F.W6.T 0)) = 2 := by
  rw [ggQ2LinIota_W6T_zero]
  have h := CFSG.StandardType.GGHalf.TorusRank.supp_omegaBlock_block 5 ⟨0, by decide⟩
  simpa [CFSG.StandardType.GGHalf.TorusRank.blockIdx] using h

theorem ggQ2LinIota_W7T_supp :
    GGHalf.supp (ggQ2LinIota 7 (CFSG.RankThree.PartTwo.Sec4.RonanK429F.W7.T 0)) = 2 := by
  rw [ggQ2LinIota_W7T_zero]
  have h := CFSG.StandardType.GGHalf.TorusRank.supp_omegaBlock_block 6 ⟨0, by decide⟩
  simpa [CFSG.StandardType.GGHalf.TorusRank.blockIdx] using h

theorem ggQ2Lin_oneBlock_of_iota {n : ℕ} {H : Type} [Group H]
    {ψ : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2 →* G}
    (hS : GGQTwoSetting p B Bs x L D J)
    (hF : GGHalfTorusFrame Bs L (GGHalf.halfTorus n) ψ)
    (hBs : Bs = Subgroup.zpowers x ⊔ (GGHalf.halfTorus n).map ψ)
    (S : Finset (Fin (R n)))
    (hJ : J = Subgroup.map ψ
      ((classBlk (n := n) (s := R n) (r := Q n) (eps n) (fun _ => 1)).map
        (MulAut.conj (delta n S)).toMonoidHom))
    (t0 : H) (ι : H ≃* Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2)
    (hιsupp : GGHalf.supp (ι t0) = 2) :
    GGQTwoVACOneBlock L (ggAutDispl Bs (ggAutomizer J Bs)) t0 := by
  let φ : H →* G := ψ.comp ι.toMonoidHom
  have hφinj : Function.Injective φ := fun a b h => ι.injective (hF.inj h)
  have hφrange : φ.range = L := by
    rw [← hF.range]
    ext g
    constructor
    · rintro ⟨a, rfl⟩; exact ⟨ι a, rfl⟩
    · rintro ⟨b, rfl⟩; exact ⟨ι.symm b, by simp [φ]⟩
  let e : H ≃* ↥L := (MonoidHom.ofInjective hφinj).trans (MulEquiv.subgroupCongr hφrange)
  have he : ∀ a, ((e a : ↥L) : G) = ψ (ι a) := by
    intro a
    rfl
  exact ggQ2Lin_oneBlock_of_supp hS hF hBs S hJ he hιsupp

theorem ggQ2Lin_oneBlock_W6 {n : ℕ}
    {ψ : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2 →* G}
    (hS : GGQTwoSetting p B Bs x L D J) (hn : 5 ≤ n)
    (hF : GGHalfTorusFrame Bs L (GGHalf.halfTorus n) ψ)
    (hBs : Bs = Subgroup.zpowers x ⊔ (GGHalf.halfTorus n).map ψ)
    {z : G} {t : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2} {a : ℤ}
    (hz : z = x ^ a * ψ t) (ht : t ∈ GGHalf.halfTorus n)
    (hDclos : D = Subgroup.closure ({x, z} : Set G))
    (hs : n + 1 - GGHalf.supp t ≤ 1) (hn5 : n = 5) :
    GGQTwoVACOneBlock L (ggAutDispl Bs (ggAutomizer J Bs))
      (CFSG.RankThree.PartTwo.Sec4.RonanK429F.W6.T 0) := by
  subst hn5
  set v : Fin (R 5) → Multiplicative (ZMod 3) := (torusCoord 5).symm ⟨t, ht⟩ with hvdef
  set S : Finset (Fin (R 5)) := swapSet 5 v with hSdef
  have hJ := ggQ2Lin_J_eq_classBlk_conj hS hF hz ht hDclos hs (by omega)
  rw [← hvdef, ← hSdef] at hJ
  exact ggQ2Lin_oneBlock_of_iota hS hF hBs S hJ _ (ggQ2LinIota 6) ggQ2LinIota_W6T_supp

theorem ggQ2Lin_oneBlock_W7 {n : ℕ}
    {ψ : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2 →* G}
    (hS : GGQTwoSetting p B Bs x L D J) (hn : 5 ≤ n)
    (hF : GGHalfTorusFrame Bs L (GGHalf.halfTorus n) ψ)
    (hBs : Bs = Subgroup.zpowers x ⊔ (GGHalf.halfTorus n).map ψ)
    {z : G} {t : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2} {a : ℤ}
    (hz : z = x ^ a * ψ t) (ht : t ∈ GGHalf.halfTorus n)
    (hDclos : D = Subgroup.closure ({x, z} : Set G))
    (hs : n + 1 - GGHalf.supp t ≤ 1) (hn6 : n = 6) :
    GGQTwoVACOneBlock L (ggAutDispl Bs (ggAutomizer J Bs))
      (CFSG.RankThree.PartTwo.Sec4.RonanK429F.W7.T 0) := by
  subst hn6
  set v : Fin (R 6) → Multiplicative (ZMod 3) := (torusCoord 6).symm ⟨t, ht⟩ with hvdef
  set S : Finset (Fin (R 6)) := swapSet 6 v with hSdef
  have hJ := ggQ2Lin_J_eq_classBlk_conj hS hF hz ht hDclos hs (by omega)
  rw [← hvdef, ← hSdef] at hJ
  exact ggQ2Lin_oneBlock_of_iota hS hF hBs S hJ _ (ggQ2LinIota 7) ggQ2LinIota_W7T_supp


end GGQ2Lin

open GGQ2Lin

theorem ggQTwoVACCellOn_lin : GGQTwoVACCellOn GGQ2VACLabLin := by
  intro G _ _ p B Bs x L D J hS hp hL hguard
  subst hp
  obtain ⟨n, ψ, hn, hF, hBs⟩ := ggQ2Lin_frame hS hL rfl
  have hB : B = Bs := ggQ2Lin_B_eq hS rfl hn hF hBs
  obtain ⟨z, t, a, ht, ht1, hzD, hzx, hzt⟩ := ggQ2Lin_exists_t hS rfl hF hBs
  have hDclos : D = Subgroup.closure ({x, z} : Set G) :=
    ggQ2Lin_D_eq_closure_of_mem_not_zpowers hS rfl hzD hzx
  have hs : n + 1 - GGHalf.supp t ≤ 1 :=
    ggQ2Lin_fix_le_one hS rfl hn hF hBs hzt ht ht1 hDclos hguard
  obtain ⟨hsix, hn56⟩ := ggQ2Lin_supp_eq_six hS hn hF hBs hzt ht hDclos hs hguard
  have h9 : 9 ≤ Nat.card (ggAutDispl Bs (ggAutomizer J Bs)) :=
    ggQ2Lin_nine_le_displ hS hn hF hBs hzt ht hDclos hs hsix
  have hone : GGQTwoVACOneBlock L (ggAutDispl Bs (ggAutomizer J Bs))
        (CFSG.RankThree.PartTwo.Sec4.RonanK429F.W6.T 0) ∨
      GGQTwoVACOneBlock L (ggAutDispl Bs (ggAutomizer J Bs))
        (CFSG.RankThree.PartTwo.Sec4.RonanK429F.W7.T 0) := by
    rcases hn56 with hn5 | hn6
    · exact Or.inl (ggQ2Lin_oneBlock_W6 hS hn hF hBs hzt ht hDclos hs hn5)
    · exact Or.inr (ggQ2Lin_oneBlock_W7 hS hn hF hBs hzt ht hDclos hs hn6)
  exact ⟨ggQTwoI1_of_eq hS hB, ggQTwoK1_of_eq hS hB, h9, hone⟩




end CFSG.StandardType

end
