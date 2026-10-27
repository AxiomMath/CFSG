module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Wreath
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Rows
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Transport
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherLinTwo
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherL62

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.RankThree.PartTwo.Sec4.Item434Kit

section Generic

variable {H : Type} [Group H]

theorem l62_vecElt_ones {z : Fin 3 → H} : vecElt z ![1, 1, 1] = z 0 * z 1 * z 2 := by
  show z 0 ^ (1 : ZMod 3).val * z 1 ^ (1 : ZMod 3).val * z 2 ^ (1 : ZMod 3).val =
    z 0 * z 1 * z 2
  rw [show (1 : ZMod 3).val = 1 from rfl]
  simp only [pow_one]

theorem l62_conj_ones {z : Fin 3 → H} {m : H} (h0 : m * z 0 * m⁻¹ = z 0 ^ 2)
    (h1 : m * z 1 * m⁻¹ = z 1) (h2 : m * z 2 * m⁻¹ = z 2) :
    m * vecElt z ![1, 1, 1] * m⁻¹ = vecElt z ![2, 1, 1] := by
  have e2 : vecElt z ![2, 1, 1] = z 0 ^ 2 * z 1 * z 2 := by
    show z 0 ^ (2 : ZMod 3).val * z 1 ^ (1 : ZMod 3).val * z 2 ^ (1 : ZMod 3).val =
      z 0 ^ 2 * z 1 * z 2
    rw [show (2 : ZMod 3).val = 2 from rfl, show (1 : ZMod 3).val = 1 from rfl]
    simp only [pow_one]
  rw [l62_vecElt_ones, e2]
  calc m * (z 0 * z 1 * z 2) * m⁻¹ = (m * z 0 * m⁻¹) * (m * z 1 * m⁻¹) * (m * z 2 * m⁻¹) := by
        group
    _ = z 0 ^ 2 * z 1 * z 2 := by rw [h0, h1, h2]

theorem l62_vecElt_const {z : Fin 3 → H} {t : H} (hf : WreathFacts z t) (r : ZMod 3) :
    vecElt z (fun _ => r) = vecElt z ![1, 1, 1] ^ r.val := by
  have hu : Multiplicative.ofAdd (fun _ : Fin 3 => r) =
      (Multiplicative.ofAdd (![1, 1, 1] : Fin 3 → ZMod 3)) ^ r.val := by
    apply Multiplicative.toAdd.injective
    ext i
    fin_cases i <;> simp
  have h := congrArg (vecHom hf) hu
  rw [map_pow] at h
  exact h

theorem l62_not_mem {z : Fin 3 → H} {t : H} (hf : WreathFacts z t) :
    vecElt z ![2, 1, 1] ∉ Subgroup.zpowers (vecElt z ![1, 1, 1]) := by
  intro hmem
  have hc3 : vecElt z ![1, 1, 1] ^ 3 = 1 :=
    (isElemAbelian_baseA hf).2 _ (vecElt_mem_baseA hf _)
  have hc1 : vecElt z ![1, 1, 1] ≠ 1 := fun h => absurd (congrFun (hf.inj _ h) 0) (by decide)
  have hord : orderOf (vecElt z ![1, 1, 1]) = 3 := orderOf_eq_prime hc3 hc1
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hk' : vecElt z ![1, 1, 1] ^ (k : ZMod 3).val = vecElt z ![2, 1, 1] := by
    rw [← zpow_natCast, ZMod.val_intCast, ← hk]
    have h3 := zpow_mod_orderOf (vecElt z ![1, 1, 1]) k
    rwa [hord] at h3
  have hc : vecElt z (fun _ => (k : ZMod 3)) = vecElt z ![2, 1, 1] := by
    rw [l62_vecElt_const hf]
    exact hk'
  have h := vecElt_injective hf hc
  have h0 : (k : ZMod 3) = 2 := congrFun h 0
  have h1 : (k : ZMod 3) = 1 := congrFun h 1
  exact absurd (h0.symm.trans h1) (by decide)

end Generic

section Blk

open Item434SmallTwoOther

theorem l62_blk_symm_eq_sq {n : ℕ} {a b : Fin n} (hab : a ≠ b) :
    blk hab.symm = blk hab ^ 2 := by
  apply SL_ext_smul
  intro k
  rw [pow_two, mul_smul]
  by_cases hka : k = a
  · rw [hka, blk_smul_fst hab, blk_smul_snd hab, blk_smul_snd hab.symm, add_comm]
  · by_cases hkb : k = b
    · rw [hkb, blk_smul_fst hab.symm, blk_smul_snd hab, smul_add, blk_smul_fst hab,
        blk_smul_snd hab]
      rw [add_comm (Pi.single b 1 : Fin n → GaloisField 2 1), add_assoc,
        gf2_vec_add_self, add_zero]
    · simp only [blk_smul_of_ne hab hka hkb, blk_smul_of_ne hab.symm hkb hka]

theorem l62_blk_pow_smul {n : ℕ} {a b k : Fin n} (hab : a ≠ b) (hka : k ≠ a) (hkb : k ≠ b)
    (m : ℕ) : blk hab ^ m • (Pi.single k 1 : Fin n → GaloisField 2 1) = Pi.single k 1 :=
  pow_smul_eq_of_smul_eq (blk_smul_of_ne hab hka hkb) m

end Blk

section Wreath

open Item434SmallTwoOther

theorem l62_ne01 : (0 : Fin 6) ≠ 1 := by decide

theorem l62_ne23 : (2 : Fin 6) ≠ 3 := by decide

theorem l62_ne45 : (4 : Fin 6) ≠ 5 := by decide

theorem l62_c01 : Commute (blk l62_ne01) (blk l62_ne23) :=
  commute_blk_blk _ _ (by decide) (by decide) (by decide) (by decide)

theorem l62_c02 : Commute (blk l62_ne01) (blk l62_ne45) :=
  commute_blk_blk _ _ (by decide) (by decide) (by decide) (by decide)

theorem l62_c12 : Commute (blk l62_ne23) (blk l62_ne45) :=
  commute_blk_blk _ _ (by decide) (by decide) (by decide) (by decide)

@[expose] noncomputable def l62Z : Fin 3 → Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 1) :=
  ![blk l62_ne01, blk l62_ne23, blk l62_ne45]

@[expose] def l62Perm : Equiv.Perm (Fin 6) where
  toFun := ![2, 3, 4, 5, 0, 1]
  invFun := ![4, 5, 0, 1, 2, 3]
  left_inv := by
    intro x
    fin_cases x <;> rfl
  right_inv := by
    intro x
    fin_cases x <;> rfl

theorem l62Perm_cube : l62Perm ^ 3 = 1 := by
  ext x
  fin_cases x <;> rfl

@[expose] noncomputable def l62T : Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 1) :=
  permSL l62Perm

theorem l62_wreathFacts : WreathFacts l62Z l62T where
  pow_z i := by
    fin_cases i
    · exact blk_pow_three _
    · exact blk_pow_three _
    · exact blk_pow_three _
  comm_z i j := by
    fin_cases i <;> fin_cases j
    · rfl
    · exact l62_c01.eq
    · exact l62_c02.eq
    · exact l62_c01.symm.eq
    · rfl
    · exact l62_c12.eq
    · exact l62_c02.symm.eq
    · exact l62_c12.symm.eq
    · rfl
  inj v hv := by
    have hv' : blk l62_ne01 ^ (v 0).val * blk l62_ne23 ^ (v 1).val *
        blk l62_ne45 ^ (v 2).val = 1 := hv
    have hfix : ∀ k : Fin 6, (blk l62_ne01 ^ (v 0).val * blk l62_ne23 ^ (v 1).val *
        blk l62_ne45 ^ (v 2).val) • (Pi.single k 1 : Fin 6 → GaloisField 2 1) =
        Pi.single k 1 := fun k => by
      rw [hv', one_smul]
    have h0 : (v 0).val = 0 := by
      have h := hfix 0
      rw [mul_smul, mul_smul, l62_blk_pow_smul (k := 0) l62_ne45 (by decide) (by decide),
        l62_blk_pow_smul (k := 0) l62_ne23 (by decide) (by decide)] at h
      exact eq_zero_of_blk_pow_smul l62_ne01 (ZMod.val_lt _) h
    have h1 : (v 1).val = 0 := by
      have h := hfix 2
      rw [(Commute.pow_pow l62_c01 (v 0).val (v 1).val).eq, mul_assoc, mul_smul, mul_smul,
        l62_blk_pow_smul (k := 2) l62_ne45 (by decide) (by decide),
        l62_blk_pow_smul (k := 2) l62_ne01 (by decide) (by decide)] at h
      exact eq_zero_of_blk_pow_smul l62_ne23 (ZMod.val_lt _) h
    have h2 : (v 2).val = 0 := by
      have h := hfix 4
      have hc : Commute (blk l62_ne01 ^ (v 0).val * blk l62_ne23 ^ (v 1).val)
          (blk l62_ne45 ^ (v 2).val) :=
        Commute.mul_left (Commute.pow_pow l62_c02 _ _) (Commute.pow_pow l62_c12 _ _)
      rw [hc.eq, mul_smul, mul_smul, l62_blk_pow_smul (k := 4) l62_ne23 (by decide) (by decide),
        l62_blk_pow_smul (k := 4) l62_ne01 (by decide) (by decide)] at h
      exact eq_zero_of_blk_pow_smul l62_ne45 (ZMod.val_lt _) h
    funext i
    fin_cases i
    · exact (ZMod.val_eq_zero _).mp h0
    · exact (ZMod.val_eq_zero _).mp h1
    · exact (ZMod.val_eq_zero _).mp h2
  pow_t := by
    rw [l62T, ← permSL_pow, l62Perm_cube, permSL_one]
  conj0 := permSL_conj_blk l62Perm l62_ne01 l62_ne23 rfl rfl
  conj1 := permSL_conj_blk l62Perm l62_ne23 l62_ne45 rfl rfl
  conj2 := permSL_conj_blk l62Perm l62_ne45 l62_ne01 rfl rfl
  t_ne v hv := by
    have hc : Commute (vecElt l62Z v) (blk l62_ne01) :=
      Commute.mul_left (Commute.mul_left (Commute.pow_left (Commute.refl _) _)
        (Commute.pow_left l62_c01.symm _)) (Commute.pow_left l62_c02.symm _)
    rw [hv] at hc
    have h1 : l62T * blk l62_ne01 * l62T⁻¹ = blk l62_ne01 := by
      rw [hc.eq, mul_inv_cancel_right]
    have h2 : blk l62_ne23 = blk l62_ne01 :=
      (permSL_conj_blk l62Perm l62_ne01 l62_ne23 rfl rfl).symm.trans h1
    have h3 : blk l62_ne01 • (Pi.single 0 1 : Fin 6 → GaloisField 2 1) =
        Pi.single 0 1 := by
      rw [← h2]
      exact blk_smul_of_ne l62_ne23 (by decide) (by decide)
    exact blk_smul_fst_ne l62_ne01 h3

theorem l62_card_wreathW : Nat.card (wreathW l62Z l62T) = 81 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 1)) :=
    Finite.of_injective _ Subtype.val_injective
  have hle := Item434AltPerm.card_le_of_isPGroup (isPGroup_wreathW l62_wreathFacts)
  rw [Item434SmallTwoOther.L62.factorization_card_SL6] at hle
  have hge := le_card_wreathW l62_wreathFacts
  norm_num at hle
  omega

@[expose] noncomputable def l62M : Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 1) :=
  permSL (Equiv.swap 0 1)

theorem l62_flip :
    ∃ m : Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 1),
      m * vecElt l62Z ![1, 1, 1] * m⁻¹ ∈ baseA l62Z ∧
      m * vecElt l62Z ![1, 1, 1] * m⁻¹ ∉ Subgroup.zpowers (vecElt l62Z ![1, 1, 1]) := by
  have hs0 : (Equiv.swap (0 : Fin 6) 1) 0 = 1 := Equiv.swap_apply_left _ _
  have hs1 : (Equiv.swap (0 : Fin 6) 1) 1 = 0 := Equiv.swap_apply_right _ _
  have hs2 : (Equiv.swap (0 : Fin 6) 1) 2 = 2 :=
    Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
  have hs3 : (Equiv.swap (0 : Fin 6) 1) 3 = 3 :=
    Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
  have hs4 : (Equiv.swap (0 : Fin 6) 1) 4 = 4 :=
    Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
  have hs5 : (Equiv.swap (0 : Fin 6) 1) 5 = 5 :=
    Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
  have e0 : l62M * l62Z 0 * l62M⁻¹ = l62Z 0 ^ 2 :=
    (permSL_conj_blk (Equiv.swap 0 1) l62_ne01 l62_ne01.symm hs0 hs1).trans
      (l62_blk_symm_eq_sq l62_ne01)
  have e1 : l62M * l62Z 1 * l62M⁻¹ = l62Z 1 :=
    permSL_conj_blk (Equiv.swap 0 1) l62_ne23 l62_ne23 hs2 hs3
  have e2 : l62M * l62Z 2 * l62M⁻¹ = l62Z 2 :=
    permSL_conj_blk (Equiv.swap 0 1) l62_ne45 l62_ne45 hs4 hs5
  refine ⟨l62M, ?_⟩
  rw [l62_conj_ones (z := l62Z) e0 e1 e2]
  exact ⟨vecElt_mem_baseA l62_wreathFacts _, l62_not_mem l62_wreathFacts⟩

end Wreath

theorem listRow_sl6 [Finite (Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 1))] :
    ListRow (Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 1)) :=
  listRow_of_wreath3 l62_wreathFacts l62_card_wreathW
    (by rw [Item434SmallTwoOther.L62.card_SL6]; norm_num) l62_flip

theorem listRow_l62 [Finite (projSL 6 (GaloisField 2 1))] :
    ListRow (projSL 6 (GaloisField 2 1)) := by
  haveI : Finite (Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 1)) :=
    Finite.of_injective _ Subtype.val_injective
  exact ListRow.of_mulEquiv (Item434SmallTwoOther.slEquivProjSL (by norm_num)) listRow_sl6

theorem outerRow_l62 [Finite (projSL 6 (GaloisField 2 1))] :
    OuterRow (projSL 6 (GaloisField 2 1)) :=
  outerRow_of_not_three_dvd_outer
    (Item434SmallTwoOther.not_three_dvd_card_outer_projSL_gf2 (by norm_num))

theorem row_l62 : RowOf (projSL 6 (GaloisField 2 1)) := by
  intro S _ _ _ _ ⟨e⟩
  haveI : Finite (projSL 6 (GaloisField 2 1)) := Finite.of_equiv S e.toEquiv
  exact GoodRow.of_mulEquiv e.symm ⟨listRow_l62, outerRow_l62⟩

end CFSG.RankThree.PartTwo.Sec4.RonanK432
