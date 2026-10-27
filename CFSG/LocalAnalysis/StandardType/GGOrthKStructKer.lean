module

public import CFSG.LocalAnalysis.StandardType.GGOrthKStructDefs
import CFSG.LocalAnalysis.StandardType.GGHalfFiveBlockRank
import CFSG.LocalAnalysis.StandardType.GGHalfFiveRes

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.StandardType.GGHalf
  CFSG.StandardType.GGHalf.TorusSupp CFSG.LieType.Universal.SpecialLinear Matrix

private theorem okKer_mul_inv_mul_mul_self {G : Type*} [Group G] {x y : G} (hx : x * x = 1) :
    (x * y * x) * x = x * y := by
  rw [mul_assoc (x * y) x x, hx, mul_one]

private theorem okKer_omegaBlock_eq_mul' (n : ℕ) (k : Fin n) :
    omegaBlock n k =
      SpecialLinearGroup.transvection (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne
          (1 : F2) *
        SpecialLinearGroup.transvection
          (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne.symm 1 := by
  have hx2 : SpecialLinearGroup.transvection
        (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne (1 : F2) *
      SpecialLinearGroup.transvection
        (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne 1 = 1 := by
    have hneg : (-1 : F2) = 1 := by
      rw [neg_eq_iff_add_eq_zero, one_add_one_eq_two, gf2_two]
    have ht := Matrix.SpecialLinearGroup.transvection_mul_neg
      (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne (1 : F2)
    rwa [hneg] at ht
  have hneg : (-1 : F2) = 1 := by
    rw [neg_eq_iff_add_eq_zero, one_add_one_eq_two, gf2_two]
  rw [omegaBlock, weylRep, hneg]
  exact okKer_mul_inv_mul_mul_self hx2

private theorem okKer_omegaBlock_coe (n : ℕ) (k : Fin n) :
    ((omegaBlock n k : SpecialLinearGroup (Fin (n + 1)) F2) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) F2) =
      1 + Matrix.single k.castSucc k.succ (1 : F2) +
        Matrix.single k.succ k.castSucc 1 + Matrix.single k.castSucc k.castSucc 1 := by
  rw [okKer_omegaBlock_eq_mul', Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe]
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul]
  rw [Matrix.single_mul_single_same, one_mul]
  abel

private theorem okKer_ofAdd_one_pow (x : Multiplicative (ZMod 3)) :
    (Multiplicative.ofAdd (1 : ZMod 3)) ^ (Multiplicative.toAdd x).val = x := by
  rw [show (Multiplicative.ofAdd (1 : ZMod 3)) ^ (Multiplicative.toAdd x).val =
      Multiplicative.ofAdd (((Multiplicative.toAdd x).val : ZMod 3)) from by
    induction (Multiplicative.toAdd x).val with
    | zero => simp
    | succ n ih => rw [pow_succ, ih]; simp]
  rw [ZMod.natCast_zmod_val]
  rfl

private noncomputable def okKer_E (n : ℕ) :
    Fin (((n + 1) / 2) * 2) ⊕ Fin ((n + 1) - ((n + 1) / 2) * 2) ≃ Fin (n + 1) :=
  finSumFinEquiv.trans (finCongr (by omega))

private theorem okKer_E_inl (n : ℕ) (p : Fin (((n + 1) / 2) * 2)) :
    okKer_E n (Sum.inl p) = ⟨p.val, by omega⟩ := rfl

private theorem okKer_E_inr (n : ℕ) (k : Fin ((n + 1) - ((n + 1) / 2) * 2)) :
    okKer_E n (Sum.inr k) = ⟨((n + 1) / 2) * 2 + k.val, by omega⟩ := rfl

private noncomputable def okKer_gen (n : ℕ) (j : Fin ((n + 1) / 2)) :
    Fin ((n + 1) / 2) → Multiplicative (ZMod 3) :=
  Pi.mulSingle j (Multiplicative.ofAdd (1 : ZMod 3))

private theorem okKer_closure_gen_eq_top (n : ℕ) :
    Subgroup.closure (Set.range (okKer_gen n)) = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro v
  rw [Subgroup.mem_closure]
  intro K hK
  have hv : v = ∏ j : Fin ((n + 1) / 2), (okKer_gen n j) ^
      (Multiplicative.toAdd (v j)).val := by
    funext k
    rw [Finset.prod_apply]
    rw [Finset.prod_eq_single k]
    · simp only [Pi.pow_apply, okKer_gen, Pi.mulSingle_apply, if_pos rfl]
      exact (okKer_ofAdd_one_pow (v k)).symm
    · intro b _ hb
      rw [Pi.pow_apply, okKer_gen, Pi.mulSingle_apply, if_neg (fun h => hb h.symm)]
      simp
    · intro hk; exact absurd (Finset.mem_univ k) hk
  rw [hv]
  exact Subgroup.prod_mem K fun j _ => K.pow_mem (hK ⟨j, rfl⟩) _

private noncomputable def okKer_blk (n : ℕ) (v : Fin ((n + 1) / 2) → Multiplicative (ZMod 3)) :
    Matrix (Fin (((n + 1) / 2) * 2)) (Fin (((n + 1) / 2) * 2)) F2 :=
  resBlocks ((n + 1) / 2)
    (Matrix.diagonal (fun j => omega2 ^ (Multiplicative.toAdd (v j)).val))

private theorem okKer_blk_one (n : ℕ) : okKer_blk n 1 = 1 := by
  rw [okKer_blk]
  have h : (fun j : Fin ((n + 1) / 2) => omega2 ^
      (Multiplicative.toAdd ((1 : Fin ((n + 1) / 2) → Multiplicative (ZMod 3)) j)).val) = 1 := by
    funext j
    simp
  rw [h]
  change resBlocks ((n + 1) / 2) (Matrix.diagonal (fun _ => (1 : Matrix (Fin 2) (Fin 2) F2))) = 1
  rw [Matrix.diagonal_one, map_one]

private theorem okKer_blk_mul (n : ℕ) (v w : Fin ((n + 1) / 2) → Multiplicative (ZMod 3)) :
    okKer_blk n (v * w) = okKer_blk n v * okKer_blk n w := by
  rw [okKer_blk, okKer_blk, okKer_blk]
  have h : (fun j : Fin ((n + 1) / 2) => omega2 ^
      (Multiplicative.toAdd ((v * w) j)).val) =
      (fun j => omega2 ^ (Multiplicative.toAdd (v j)).val *
        omega2 ^ (Multiplicative.toAdd (w j)).val) := by
    funext j
    rw [Pi.mul_apply, toAdd_mul, ZMod.val_add, ← pow_add]
    exact (omega2_pow_mod _).symm
  rw [h]
  simp only [← Matrix.diagonal_mul_diagonal, map_mul]

private noncomputable def okKer_blkHom (n : ℕ) :
    (Fin ((n + 1) / 2) → Multiplicative (ZMod 3)) →*
      Matrix (Fin (((n + 1) / 2) * 2) ⊕ Fin ((n + 1) - ((n + 1) / 2) * 2))
        (Fin (((n + 1) / 2) * 2) ⊕ Fin ((n + 1) - ((n + 1) / 2) * 2)) F2 where
  toFun v := Matrix.fromBlocks (okKer_blk n v) 0 0 1
  map_one' := by rw [okKer_blk_one, Matrix.fromBlocks_one]
  map_mul' := by
    intro v w
    rw [okKer_blk_mul, Matrix.fromBlocks_multiply]
    simp

private noncomputable def okKer_psiHom (n : ℕ)
    (Φ : (Fin ((n + 1) / 2) → Multiplicative (ZMod 3)) ≃* ↥(halfTorus n)) :
    (Fin ((n + 1) / 2) → Multiplicative (ZMod 3)) →*
      Matrix (Fin (((n + 1) / 2) * 2) ⊕ Fin ((n + 1) - ((n + 1) / 2) * 2))
        (Fin (((n + 1) / 2) * 2) ⊕ Fin ((n + 1) - ((n + 1) / 2) * 2)) F2 where
  toFun v := (((Φ v : ↥(halfTorus n)) : SpecialLinearGroup (Fin (n + 1)) F2) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) F2).submatrix (okKer_E n) (okKer_E n)
  map_one' := by
    simp only [map_one, Subgroup.coe_one, Matrix.SpecialLinearGroup.coe_one]
    exact Matrix.submatrix_one_equiv (okKer_E n)
  map_mul' := by
    intro v w
    simp only [map_mul, Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    rw [Matrix.submatrix_mul_equiv]

private theorem okKer_E_inl_val (n : ℕ) (p : Fin (((n + 1) / 2) * 2)) :
    (okKer_E n (Sum.inl p)).val = p.val := by
  rw [okKer_E_inl]

private theorem okKer_E_inr_val (n : ℕ) (p : Fin ((n + 1) - ((n + 1) / 2) * 2)) :
    (okKer_E n (Sum.inr p)).val = ((n + 1) / 2) * 2 + p.val := by
  rw [okKer_E_inr]

private theorem okKer_omegaBlock_apply_val (n : ℕ) (k : Fin n) (x y : Fin (n + 1)) :
    (((omegaBlock n k : SpecialLinearGroup (Fin (n + 1)) F2) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) F2) x y) =
      (if x.val = y.val then 1 else 0) +
        (if k.val = x.val ∧ k.val + 1 = y.val then 1 else 0) +
        (if k.val + 1 = x.val ∧ k.val = y.val then 1 else 0) +
        (if k.val = x.val ∧ k.val = y.val then 1 else 0) := by
  rw [okKer_omegaBlock_coe]
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, Fin.ext_iff,
    Fin.val_castSucc, Fin.val_succ]

private theorem okKer_omegaBlock_submatrix (n : ℕ) (j : Fin ((n + 1) / 2)) :
    (((omegaBlock n ⟨2 * j.val, two_mul_lt_of_lt_half j.isLt⟩ :
        SpecialLinearGroup (Fin (n + 1)) F2) : Matrix (Fin (n + 1)) (Fin (n + 1)) F2).submatrix
        (okKer_E n) (okKer_E n)) =
      Matrix.fromBlocks (resBlocks ((n + 1) / 2) (Matrix.diagonal (Pi.mulSingle j omega2)))
        0 0 1 := by
  ext r c
  rcases r with r | r <;> rcases c with c | c
  · obtain ⟨⟨i, e⟩, rfl⟩ := finProdFinEquiv.surjective r
    obtain ⟨⟨i', e'⟩, rfl⟩ := finProdFinEquiv.surjective c
    rw [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁, resBlocks_apply,
      Matrix.diagonal_apply, okKer_omegaBlock_apply_val, okKer_E_inl_val, okKer_E_inl_val,
      finProdFinEquiv_apply_val, finProdFinEquiv_apply_val, Pi.mulSingle_apply]
    fin_cases e <;> fin_cases e' <;>
      simp only [Fin.ext_iff, Fin.val_mk] <;>
      split_ifs <;>
      first
        | (exfalso; omega)
        | simp [omega2, f2_one_add_one, Matrix.one_apply]
  · rw [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply,
      okKer_omegaBlock_apply_val, okKer_E_inl_val, okKer_E_inr_val]
    simp only [Fin.ext_iff, Fin.val_mk]
    split_ifs <;> first | (exfalso; omega) | simp [omega2, f2_one_add_one]
  · rw [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply,
      okKer_omegaBlock_apply_val, okKer_E_inr_val, okKer_E_inl_val]
    simp only [Fin.ext_iff, Fin.val_mk]
    split_ifs <;> first | (exfalso; omega) | simp [omega2, f2_one_add_one]
  · rw [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₂, Matrix.one_apply,
      okKer_omegaBlock_apply_val, okKer_E_inr_val, okKer_E_inr_val]
    simp only [Fin.ext_iff, Fin.val_mk]
    split_ifs <;> first | (exfalso; omega) | simp [omega2, f2_one_add_one]

private theorem okKer_ker_eq_range {V : Type*} [AddCommGroup V] [Module F2 V] (T : V →ₗ[F2] V)
    (hT : T.comp (T.comp T) = LinearMap.id) :
    LinearMap.ker (T.comp T + T + LinearMap.id) = LinearMap.range (T - LinearMap.id) := by
  apply le_antisymm
  · intro x hx
    rw [LinearMap.mem_ker] at hx
    rw [LinearMap.mem_range]
    refine ⟨T x, ?_⟩
    have h2 : T (T x) + T x + x = 0 := by
      simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply] using hx
    have hneg : -x = x := by rw [neg_eq_iff_add_eq_zero, ← two_smul F2 x, gf2_two, zero_smul]
    have hnegT : -T x = T x := by
      rw [neg_eq_iff_add_eq_zero, ← two_smul F2 (T x), gf2_two, zero_smul]
    rw [LinearMap.sub_apply, LinearMap.id_apply, sub_eq_add_neg, hnegT]
    have h3 : T (T x) + T x = x := by
      have h4 : T (T x) + T x = -x := by
        apply eq_neg_of_add_eq_zero_left
        exact h2
      rwa [hneg] at h4
    exact h3
  · rintro x ⟨y, rfl⟩
    rw [LinearMap.mem_ker]
    have hy : T (T (T y)) = y := by
      have h := congrArg (fun f : V →ₗ[F2] V => f y) hT
      simpa only [LinearMap.comp_apply, LinearMap.id_apply] using h
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
      LinearMap.id_apply]
    simp only [map_sub]
    rw [hy]
    abel

private theorem okKer_finrank_ker_eq_rank (N : ℕ) (M : Matrix (Fin N) (Fin N) F2)
    (hM : M ^ 3 = 1) :
    Module.finrank F2 (LinearMap.ker (Matrix.toLin' (M ^ 2 + M + 1))) = Matrix.rank (M - 1) := by
  have hpoly : Matrix.toLin' (M ^ 2 + M + 1) =
      (Matrix.toLin' M).comp (Matrix.toLin' M) + Matrix.toLin' M + LinearMap.id := by
    rw [map_add, map_add]
    have h2 : Matrix.toLin' (M ^ 2) = (Matrix.toLin' M).comp (Matrix.toLin' M) := by
      rw [pow_two, Matrix.toLin'_mul]
    rw [h2, Matrix.toLin'_one]
  have hsub : Matrix.toLin' (M - 1) = Matrix.toLin' M - LinearMap.id := by
    rw [map_sub, Matrix.toLin'_one]
  have hT : (Matrix.toLin' M).comp ((Matrix.toLin' M).comp (Matrix.toLin' M)) = LinearMap.id := by
    have h1 : Matrix.toLin' (M ^ 3) =
        ((Matrix.toLin' M).comp (Matrix.toLin' M)).comp (Matrix.toLin' M) := by
      rw [show M ^ 3 = (M * M) * M by rw [pow_succ, pow_two], Matrix.toLin'_mul,
        Matrix.toLin'_mul]
    rw [hM, Matrix.toLin'_one] at h1
    rw [h1]
    exact (LinearMap.comp_assoc (Matrix.toLin' M) (Matrix.toLin' M) (Matrix.toLin' M)).symm
  have hker : LinearMap.ker (Matrix.toLin' (M ^ 2 + M + 1)) =
      LinearMap.ker ((Matrix.toLin' M).comp (Matrix.toLin' M) + Matrix.toLin' M +
        LinearMap.id) := by rw [hpoly]
  have hran : LinearMap.range (Matrix.toLin' (M - 1)) =
      LinearMap.range (Matrix.toLin' M - LinearMap.id) := by rw [hsub]
  have e1 := congrArg (fun p : Submodule F2 (Fin N → F2) => Module.finrank F2 (↥p)) hker
  have e2 := congrArg (fun p : Submodule F2 (Fin N → F2) => Module.finrank F2 (↥p)) hran
  have e3 := congrArg (fun p : Submodule F2 (Fin N → F2) => Module.finrank F2 (↥p))
    (okKer_ker_eq_range (Matrix.toLin' M) hT)
  change Module.finrank F2 (↥(LinearMap.ker (Matrix.toLin' (M ^ 2 + M + 1)))) =
    Module.finrank F2 (↥(LinearMap.range (Matrix.toLin' (M - 1))))
  rw [e1, e3, ← e2]
  rfl

private theorem okKer_rank_fromBlocks_zero (m o : ℕ) (C : Matrix (Fin m) (Fin m) F2) :
    Matrix.rank (Matrix.fromBlocks C 0 0 0 :
      Matrix (Fin m ⊕ Fin o) (Fin m ⊕ Fin o) F2) = Matrix.rank C := by
  apply le_antisymm
  · rw [Matrix.rank_eq_finrank_span_row, Matrix.rank_eq_finrank_span_row]
    let φ : (Fin m → F2) →ₗ[F2] (Fin m ⊕ Fin o → F2) :=
      { toFun := fun f => Sum.elim f 0
        map_add' := by intro f g; funext r; rcases r with i | i <;> simp
        map_smul' := by intro c f; funext r; rcases r with i | i <;> simp }
    have hspan : Submodule.span F2 (Set.range (Matrix.fromBlocks C 0 0 0 :
        Matrix (Fin m ⊕ Fin o) (Fin m ⊕ Fin o) F2).row) =
        Submodule.map φ (Submodule.span F2 (Set.range C.row)) := by
      rw [← Submodule.span_image]
      apply le_antisymm
      · rw [Submodule.span_le]
        rintro g ⟨r, rfl⟩
        rcases r with i | j
        · refine Submodule.subset_span ⟨C.row i, ⟨i, rfl⟩, ?_⟩
          funext r
          rcases r with l | l
          · change (Sum.elim (C.row i) (0 : Fin o → F2)) (Sum.inl l) =
              (Matrix.fromBlocks C 0 0 0).row (Sum.inl i) (Sum.inl l)
            rw [Sum.elim_inl, Matrix.row_apply, Matrix.row_apply, Matrix.fromBlocks_apply₁₁]
          · change (Sum.elim (C.row i) (0 : Fin o → F2)) (Sum.inr l) =
              (Matrix.fromBlocks C 0 0 0).row (Sum.inl i) (Sum.inr l)
            rw [Sum.elim_inr, Matrix.row_apply, Matrix.fromBlocks_apply₁₂]
            simp
        · have hzero : (Matrix.fromBlocks C 0 0 0 :
              Matrix (Fin m ⊕ Fin o) (Fin m ⊕ Fin o) F2).row (Sum.inr j) = 0 := by
            funext l
            rcases l with l | l
            · rw [Matrix.row_apply, Matrix.fromBlocks_apply₂₁]; simp
            · rw [Matrix.row_apply, Matrix.fromBlocks_apply₂₂]; simp
          rw [hzero]
          exact Submodule.zero_mem _
      · rw [Submodule.span_le]
        rintro g ⟨f, ⟨i, rfl⟩, rfl⟩
        refine Submodule.subset_span ⟨Sum.inl i, ?_⟩
        funext r
        rcases r with l | l
        · change (Matrix.fromBlocks C 0 0 0).row (Sum.inl i) (Sum.inl l) =
            (Sum.elim (C.row i) (0 : Fin o → F2)) (Sum.inl l)
          rw [Sum.elim_inl, Matrix.row_apply, Matrix.row_apply, Matrix.fromBlocks_apply₁₁]
        · change (Matrix.fromBlocks C 0 0 0).row (Sum.inl i) (Sum.inr l) =
            (Sum.elim (C.row i) (0 : Fin o → F2)) (Sum.inr l)
          rw [Sum.elim_inr, Matrix.row_apply, Matrix.fromBlocks_apply₁₂]
          simp
    rw [hspan]
    exact Submodule.finrank_map_le _ _
  · rw [show C = (Matrix.fromBlocks C 0 0 0 :
        Matrix (Fin m ⊕ Fin o) (Fin m ⊕ Fin o) F2).submatrix Sum.inl Sum.inl from by
      ext i j; rw [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁]]
    exact Matrix.rank_submatrix_le _ _ _

private theorem okKer_fromBlocks_sub_one (k lo : ℕ)
    (A : Matrix (Fin (k * 2)) (Fin (k * 2)) F2) :
    (Matrix.fromBlocks A 0 0 1 :
      Matrix (Fin (k * 2) ⊕ Fin lo) (Fin (k * 2) ⊕ Fin lo) F2) - 1 =
      Matrix.fromBlocks (A - 1) 0 0 0 := by
  rw [show (1 : Matrix (Fin (k * 2) ⊕ Fin lo) (Fin (k * 2) ⊕ Fin lo) F2) =
      Matrix.fromBlocks 1 0 0 1 from (Matrix.fromBlocks_one).symm]
  rw [sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add]
  simp [sub_eq_add_neg]

private theorem okKer_resBlocks_diagonal_sub_one (k : ℕ)
    (f : Fin k → Matrix (Fin 2) (Fin 2) F2) :
    resBlocks k (Matrix.diagonal f) - 1 =
      resBlocks k (Matrix.diagonal (fun j => f j - 1)) := by
  rw [show (1 : Matrix (Fin (k * 2)) (Fin (k * 2)) F2) =
      resBlocks k (1 : Matrix (Fin k) (Fin k) (Matrix (Fin 2) (Fin 2) F2)) from
    (map_one (resBlocks k)).symm]
  rw [show (1 : Matrix (Fin k) (Fin k) (Matrix (Fin 2) (Fin 2) F2)) =
      Matrix.diagonal (fun _ => 1) from Matrix.diagonal_one.symm]
  rw [← map_sub, ← Matrix.diagonal_sub]

private theorem okKer_rank_resBlocks_diagonal (k : ℕ)
    (g : Fin k → Matrix (Fin 2) (Fin 2) F2) :
    Matrix.rank (resBlocks k (Matrix.diagonal g)) = Matrix.rank (Matrix.blockDiagonal g) := by
  let e : Fin (k * 2) ≃ Fin 2 × Fin k :=
    finProdFinEquiv.symm.trans (Equiv.prodComm (Fin k) (Fin 2))
  have hreindex : resBlocks k (Matrix.diagonal g) =
      (Matrix.blockDiagonal g).submatrix e e := by
    ext r s
    obtain ⟨⟨i, j⟩, rfl⟩ := (finProdFinEquiv (m := k) (n := 2)).surjective r
    obtain ⟨⟨i', j'⟩, rfl⟩ := (finProdFinEquiv (m := k) (n := 2)).surjective s
    have he : e (finProdFinEquiv (i, j)) = (j, i) := by
      simp [e, Equiv.prodComm_apply]
    have he' : e (finProdFinEquiv (i', j')) = (j', i') := by
      simp [e, Equiv.prodComm_apply]
    rw [resBlocks_apply, Matrix.submatrix_apply, he, he']
    by_cases h : i = i'
    · subst h; simp [Matrix.diagonal_apply, Matrix.blockDiagonal_apply]
    · simp [Matrix.diagonal_apply, Matrix.blockDiagonal_apply, h]
  rw [hreindex]
  exact Matrix.rank_submatrix (Matrix.blockDiagonal g) e e

private theorem okKer_rank_eq (n : ℕ)
    (Φ : (Fin ((n + 1) / 2) → Multiplicative (ZMod 3)) ≃* ↥(halfTorus n))
    (hΦ : IsTorusCoord n Φ) (a : Fin ((n + 1) / 2) → Multiplicative (ZMod 3)) :
    Matrix.rank ((((Φ a : ↥(halfTorus n)) : SpecialLinearGroup (Fin (n + 1)) F2) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) F2) - 1) =
      2 * (Finset.univ.filter fun j => a j ≠ 1).card := by
  classical
  have hgen : Set.EqOn (⇑(okKer_psiHom n Φ)) (⇑(okKer_blkHom n)) (Set.range (okKer_gen n)) := by
    rintro _ ⟨j, rfl⟩
    have hPhi_j : ((Φ (okKer_gen n j) : ↥(halfTorus n)) :
        SpecialLinearGroup (Fin (n + 1)) F2) =
        omegaBlock n ⟨2 * j.val, two_mul_lt_of_lt_half j.isLt⟩ := by
      simpa only [okKer_gen] using hΦ j
    have hblk : okKer_blk n (okKer_gen n j) =
        resBlocks ((n + 1) / 2) (Matrix.diagonal (Pi.mulSingle j omega2)) := by
      rw [okKer_blk]
      congr 1
      rw [Matrix.diagonal_injective.eq_iff]
      funext j'
      rw [okKer_gen]
      simp only [Pi.mulSingle_apply]
      by_cases h : j' = j
      · subst h; simp [ZMod.val_one]
      · rw [if_neg h, if_neg h]; simp [ZMod.val_zero]
    show (((Φ (okKer_gen n j) : ↥(halfTorus n)) : SpecialLinearGroup (Fin (n + 1)) F2) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) F2).submatrix (okKer_E n) (okKer_E n) =
      Matrix.fromBlocks (okKer_blk n (okKer_gen n j)) 0 0 1
    rw [hPhi_j, okKer_omegaBlock_submatrix, hblk]
  have hEq : okKer_psiHom n Φ = okKer_blkHom n := by
    apply MonoidHom.ext
    intro v
    exact MonoidHom.eqOn_closure (s := Set.range (okKer_gen n)) hgen (by
      rw [okKer_closure_gen_eq_top]; exact Subgroup.mem_top v)
  have hsub : (((Φ a : ↥(halfTorus n)) : SpecialLinearGroup (Fin (n + 1)) F2) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) F2).submatrix (okKer_E n) (okKer_E n) =
      Matrix.fromBlocks (okKer_blk n a) 0 0 1 := by
    have h := DFunLike.congr_fun hEq a
    exact h
  let g : Fin ((n + 1) / 2) → Matrix (Fin 2) (Fin 2) F2 :=
    fun j => omega2 ^ (Multiplicative.toAdd (a j)).val - 1
  have hblk_sub : okKer_blk n a - 1 =
      resBlocks ((n + 1) / 2) (Matrix.diagonal g) := by
    rw [okKer_blk]
    exact okKer_resBlocks_diagonal_sub_one _ _
  calc Matrix.rank ((((Φ a : ↥(halfTorus n)) : SpecialLinearGroup (Fin (n + 1)) F2) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) F2) - 1)
      = Matrix.rank (((((Φ a : ↥(halfTorus n)) : SpecialLinearGroup (Fin (n + 1)) F2) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) F2) - 1).submatrix
            (okKer_E n) (okKer_E n)) :=
        (Matrix.rank_submatrix _ (okKer_E n) (okKer_E n)).symm
    _ = Matrix.rank (Matrix.fromBlocks
          (resBlocks ((n + 1) / 2) (Matrix.diagonal g)) 0 0 0) := by
        rw [show ((((Φ a : ↥(halfTorus n)) : SpecialLinearGroup (Fin (n + 1)) F2) :
            Matrix (Fin (n + 1)) (Fin (n + 1)) F2) - 1).submatrix
              (okKer_E n) (okKer_E n) =
            ((((Φ a : ↥(halfTorus n)) : SpecialLinearGroup (Fin (n + 1)) F2) :
              Matrix (Fin (n + 1)) (Fin (n + 1)) F2).submatrix (okKer_E n) (okKer_E n)) - 1
          from by simp [Matrix.submatrix_sub, Matrix.submatrix_one_equiv]]
        rw [hsub, okKer_fromBlocks_sub_one, hblk_sub]
    _ = Matrix.rank (resBlocks ((n + 1) / 2) (Matrix.diagonal g)) :=
        okKer_rank_fromBlocks_zero _ _ _
    _ = Matrix.rank (Matrix.blockDiagonal g) := okKer_rank_resBlocks_diagonal _ g
    _ = 2 * (Finset.univ.filter fun j => g j ≠ 0).card :=
        rank_blockDiagonal_fin2 g (fun j => omega2_pow_sub_one_zero_or_isUnit _)
    _ = 2 * (Finset.univ.filter fun j => a j ≠ 1).card := by
        have hf : (Finset.univ.filter fun j => g j ≠ 0) =
            (Finset.univ.filter fun j => a j ≠ 1) :=
          Finset.filter_congr (fun j _ => omega2_pow_sub_one_ne_zero_iff (a j))
        rw [hf]

theorem ggOrthKStruct_ker {n : ℕ}
    (Φ : (Fin ((n + 1) / 2) → Multiplicative (ZMod 3)) ≃* ↥(halfTorus n)) (hΦ : IsTorusCoord n Φ)
    (a : Fin ((n + 1) / 2) → Multiplicative (ZMod 3)) :
    Module.finrank F2 (LinearMap.ker (Matrix.toLin'
        (((Φ a : SpecialLinearGroup (Fin (n + 1)) F2) : Matrix (Fin (n + 1)) (Fin (n + 1)) F2) ^ 2 +
          ((Φ a : SpecialLinearGroup (Fin (n + 1)) F2) : Matrix (Fin (n + 1)) (Fin (n + 1)) F2) +
          1))) = 2 * (Finset.univ.filter fun j => a j ≠ 1).card := by
  have hcoe : ∀ (x : SpecialLinearGroup (Fin (n + 1)) F2) (k : ℕ),
      ((x ^ k : SpecialLinearGroup (Fin (n + 1)) F2) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) F2) =
      ((x : Matrix (Fin (n + 1)) (Fin (n + 1)) F2)) ^ k := by
    intro x k
    induction k with
    | zero => rw [pow_zero, pow_zero, Matrix.SpecialLinearGroup.coe_one]
    | succ k ih => rw [pow_succ, pow_succ, Matrix.SpecialLinearGroup.coe_mul, ih]
  have hM : (((Φ a : ↥(halfTorus n)) : SpecialLinearGroup (Fin (n + 1)) F2) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) F2) ^ 3 = 1 := by
    have h := congrArg (fun x : SpecialLinearGroup (Fin (n + 1)) F2 =>
      (x : Matrix (Fin (n + 1)) (Fin (n + 1)) F2)) (halfTorus_pow_three (n := n) (Φ a).2)
    rwa [hcoe, Matrix.SpecialLinearGroup.coe_one] at h
  exact (okKer_finrank_ker_eq_rank (n + 1)
    (((Φ a : ↥(halfTorus n)) : SpecialLinearGroup (Fin (n + 1)) F2) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) F2) hM).trans (okKer_rank_eq n Φ hΦ a)

end CFSG.StandardType

end
