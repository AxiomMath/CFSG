module

public import CFSG.LocalAnalysis.StandardType.GGHalfFiveBlockRank
public import CFSG.LocalAnalysis.StandardType.GGHalfFiveRes
public import CFSG.LocalAnalysis.StandardType.GGHalfCentSupp
public import CFSG.LocalAnalysis.StandardType.GGHalfWeylTorusCoord

public section

namespace CFSG.StandardType.GGHalf

open CFSG.LieType.Universal.SpecialLinear Matrix

namespace TorusSupp

@[expose] noncomputable def kOf (j : Fin 3) : Fin 5 := ⟨2 * j.val, by omega⟩

@[expose] noncomputable def gen (j : Fin 3) : Fin 3 → Multiplicative (ZMod 3) :=
  Pi.mulSingle j (Multiplicative.ofAdd (1 : ZMod 3))

private theorem mul_inv_mul_mul_self {G : Type*} [Group G] {x y : G} (hx : x * x = 1) :
    (x * y * x) * x = x * y := by
  rw [mul_assoc (x * y) x x, hx, mul_one]

private theorem omegaBlock_eq_mul' (n : ℕ) (k : Fin n) :
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
  exact mul_inv_mul_mul_self hx2

private theorem coe_omegaBlock_sum' (n : ℕ) (k : Fin n) :
    ((omegaBlock n k : SpecialLinearGroup (Fin (n + 1)) F2) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) F2) =
      1 + Matrix.single k.castSucc k.succ (1 : F2) +
        Matrix.single k.succ k.castSucc 1 + Matrix.single k.castSucc k.castSucc 1 := by
  rw [omegaBlock_eq_mul', Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe]
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul]
  rw [Matrix.single_mul_single_same, one_mul]
  abel

private theorem omegaBlock_block (j : Fin 3) :
    (((omegaBlock 5 (kOf j) : SpecialLinearGroup (Fin 6) F2)) :
        Matrix (Fin 6) (Fin 6) F2).submatrix blockEquiv blockEquiv =
      Matrix.blockDiagonal (Pi.mulSingle j omega2) := by
  rw [coe_omegaBlock_sum']
  ext p q
  obtain ⟨a, b⟩ := p
  obtain ⟨a', b'⟩ := q
  fin_cases a <;> fin_cases b <;> fin_cases a' <;> fin_cases b' <;> fin_cases j <;>
    simp [blockEquiv, kOf, omega2, f2_one_add_one, gf2_two, Matrix.submatrix_apply,
      Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, Matrix.blockDiagonal_apply,
      Pi.mulSingle_apply]

private noncomputable def blk (v : Fin 3 → Multiplicative (ZMod 3)) :
    Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) F2 :=
  Matrix.blockDiagonal fun j => omega2 ^ (Multiplicative.toAdd (v j)).val

private theorem blk_one : blk 1 = 1 := by
  rw [blk, show (fun j : Fin 3 => omega2 ^
        (Multiplicative.toAdd ((1 : Fin 3 → Multiplicative (ZMod 3)) j)).val) =
      (1 : Fin 3 → Matrix (Fin 2) (Fin 2) F2) from by
    funext j
    rw [Pi.one_apply]
    exact pow_zero omega2, Matrix.blockDiagonal_one]

private theorem blk_mul (v w : Fin 3 → Multiplicative (ZMod 3)) :
    blk (v * w) = blk v * blk w := by
  simp only [blk]
  rw [← Matrix.blockDiagonal_mul]
  congr 1
  funext j
  rw [Pi.mul_apply, toAdd_mul, ZMod.val_add, ← pow_add]
  exact (omega2_pow_mod _).symm

theorem ofAdd_one_pow (x : Multiplicative (ZMod 3)) :
    (Multiplicative.ofAdd (1 : ZMod 3)) ^ (Multiplicative.toAdd x).val = x := by
  rw [show (Multiplicative.ofAdd (1 : ZMod 3)) ^ (Multiplicative.toAdd x).val =
      Multiplicative.ofAdd (((Multiplicative.toAdd x).val : ZMod 3)) from by
    induction (Multiplicative.toAdd x).val with
    | zero => simp
    | succ n ih => rw [pow_succ, ih]; simp]
  rw [ZMod.natCast_zmod_val]
  rfl

private theorem closure_gen_eq_top : Subgroup.closure (Set.range gen) = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro v
  rw [Subgroup.mem_closure]
  intro K hK
  have hv : v = ∏ j : Fin 3, (gen j) ^ (Multiplicative.toAdd (v j)).val := by
    funext k
    rw [Finset.prod_apply]
    rw [Finset.prod_eq_single k]
    · simp only [Pi.pow_apply, gen, Pi.mulSingle_apply, if_pos rfl]
      exact (ofAdd_one_pow (v k)).symm
    · intro b _ hb
      rw [Pi.pow_apply, gen, Pi.mulSingle_apply, if_neg (fun h => hb h.symm)]
      simp
    · intro hk; exact absurd (Finset.mem_univ k) hk
  rw [hv]
  exact Subgroup.prod_mem K fun j _ => K.pow_mem (hK ⟨j, rfl⟩) _

private noncomputable def phiMatHom (Φ : (Fin 3 → Multiplicative (ZMod 3)) ≃* ↥(halfTorus 5)) :
    (Fin 3 → Multiplicative (ZMod 3)) →* Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) F2 where
  toFun v := (((Φ v : ↥(halfTorus 5)) : SpecialLinearGroup (Fin 6) F2) :
      Matrix (Fin 6) (Fin 6) F2).submatrix blockEquiv blockEquiv
  map_one' := by
    simp only [map_one, Subgroup.coe_one, Matrix.SpecialLinearGroup.coe_one]
    exact Matrix.submatrix_one_equiv blockEquiv
  map_mul' := by
    intro v w
    simp only [map_mul, Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    rw [Matrix.submatrix_mul_equiv]

private noncomputable def blkHom :
    (Fin 3 → Multiplicative (ZMod 3)) →* Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) F2 where
  toFun := blk
  map_one' := blk_one
  map_mul' := blk_mul

private theorem phiMatHom_gen (Φ : (Fin 3 → Multiplicative (ZMod 3)) ≃* ↥(halfTorus 5))
    (hΦ : ∀ j : Fin 3, ((Φ (gen j) : ↥(halfTorus 5)) :
      SpecialLinearGroup (Fin 6) F2) = omegaBlock 5 (kOf j)) (j : Fin 3) :
    phiMatHom Φ (gen j) = blkHom (gen j) := by
  change (((Φ (gen j) : ↥(halfTorus 5)) : SpecialLinearGroup (Fin 6) F2) :
      Matrix (Fin 6) (Fin 6) F2).submatrix blockEquiv blockEquiv = blk (gen j)
  rw [hΦ j, omegaBlock_block j]
  simp only [blk, gen]
  congr 1
  funext i
  rw [Pi.mulSingle_apply, Pi.mulSingle_apply]
  by_cases hi : i = j
  · rw [if_pos hi, if_pos hi]
    rw [show (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 3))).val = 1 by
      show (1 : ZMod 3).val = 1
      decide, pow_one]
  · rw [if_neg hi, if_neg hi]
    simp

private theorem phiMat_eq_blk (Φ : (Fin 3 → Multiplicative (ZMod 3)) ≃* ↥(halfTorus 5))
    (hΦ : ∀ j : Fin 3, ((Φ (gen j) : ↥(halfTorus 5)) :
      SpecialLinearGroup (Fin 6) F2) = omegaBlock 5 (kOf j))
    (v : Fin 3 → Multiplicative (ZMod 3)) :
    (((Φ v : ↥(halfTorus 5)) : SpecialLinearGroup (Fin 6) F2) :
      Matrix (Fin 6) (Fin 6) F2).submatrix blockEquiv blockEquiv = blk v := by
  have h := MonoidHom.eq_of_eqOn_dense (s := Set.range gen) closure_gen_eq_top
    (fun x hx => by
      obtain ⟨j, rfl⟩ := hx
      exact phiMatHom_gen Φ hΦ j)
  exact DFunLike.congr_fun h v

theorem supp_torusCoord (Φ : (Fin 3 → Multiplicative (ZMod 3)) ≃* ↥(halfTorus 5))
    (hΦ : ∀ j : Fin 3, ((Φ (gen j) : ↥(halfTorus 5)) :
      SpecialLinearGroup (Fin 6) F2) = omegaBlock 5 (kOf j))
    (v : Fin 3 → Multiplicative (ZMod 3)) :
    supp ((Φ v : ↥(halfTorus 5)) : SpecialLinearGroup (Fin 6) F2) =
      2 * (Finset.univ.filter fun j : Fin 3 => v j ≠ 1).card := by
  classical
  unfold supp
  let M : Matrix (Fin 6) (Fin 6) F2 := ((Φ v : ↥(halfTorus 5)) : SpecialLinearGroup (Fin 6) F2)
  change (M - 1).rank = 2 * (Finset.univ.filter fun j : Fin 3 => v j ≠ 1).card
  have hmat : M.submatrix blockEquiv blockEquiv = blk v := phiMat_eq_blk Φ hΦ v
  rw [← Matrix.rank_submatrix (A := M - 1) blockEquiv blockEquiv]
  have hsub : (M - 1).submatrix blockEquiv blockEquiv = blk v - 1 := by
    ext p q
    rw [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.sub_apply]
    have hpq : M (blockEquiv p) (blockEquiv q) = blk v p q := by
      have h1 := congrFun (congrFun hmat p) q
      rwa [Matrix.submatrix_apply] at h1
    rw [hpq]
    simp only [Matrix.one_apply, blockEquiv.injective.eq_iff]
  rw [hsub]
  have hblk : blk v - 1 = Matrix.blockDiagonal
      (fun j : Fin 3 => omega2 ^ (Multiplicative.toAdd (v j)).val - 1) := by
    rw [blk, show (1 : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) F2) =
        Matrix.blockDiagonal (1 : Fin 3 → Matrix (Fin 2) (Fin 2) F2) from
      Matrix.blockDiagonal_one.symm, ← Matrix.blockDiagonal_sub]
    rfl
  rw [hblk]
  rw [rank_blockDiagonal_fin2
    (f := fun j : Fin 3 => omega2 ^ (Multiplicative.toAdd (v j)).val - 1)
    (fun j => omega2_pow_sub_one_zero_or_isUnit _)]
  rw [show (Finset.univ.filter fun j : Fin 3 =>
        omega2 ^ (Multiplicative.toAdd (v j)).val - 1 ≠ 0) =
      (Finset.univ.filter fun j : Fin 3 => v j ≠ 1) from by
    apply Finset.filter_congr
    intro j _
    exact omega2_pow_sub_one_ne_zero_iff (v j)]

theorem torusCoord_gen_eq (Φ : (Fin 3 → Multiplicative (ZMod 3)) ≃* ↥(halfTorus 5))
    (hΦ : ∀ j : Fin 3, ((Φ (Pi.mulSingle j (Multiplicative.ofAdd (1 : ZMod 3))) :
        ↥(halfTorus 5)) : SpecialLinearGroup (Fin 6) F2) =
      omegaBlock 5 ⟨2 * j.val, two_mul_lt_of_lt_half j.isLt⟩) :
    ∀ j : Fin 3, ((Φ (gen j) : ↥(halfTorus 5)) :
      SpecialLinearGroup (Fin 6) F2) = omegaBlock 5 (kOf j) := by
  intro j
  have h := hΦ j
  have hk : (⟨2 * j.val, two_mul_lt_of_lt_half j.isLt⟩ : Fin 5) = kOf j := Fin.ext rfl
  rw [hk] at h
  exact h

theorem supp_omegaBlock_kOf (j : Fin 3) : supp (omegaBlock 5 (kOf j)) = 2 := by
  obtain ⟨Φ, hΦ⟩ := exists_torusCoord 5
  have hΦ' := torusCoord_gen_eq Φ hΦ
  have h := supp_torusCoord Φ hΦ' (gen j)
  rw [hΦ' j] at h
  rw [h]
  have hf : (Finset.univ.filter fun i : Fin 3 => gen j i ≠ 1) = {j} := by
    apply Finset.ext
    intro i
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨-, hne⟩
      by_contra hij
      exact hne (by rw [gen, Pi.mulSingle_eq_of_ne (fun h => hij h)])
    · intro hij
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [hij, gen, Pi.mulSingle_eq_same]
      decide
  rw [hf]
  simp


end TorusSupp

end CFSG.StandardType.GGHalf

end
