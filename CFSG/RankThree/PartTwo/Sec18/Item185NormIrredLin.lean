module

public import CFSG.RankThree.PartTwo.Sec18.Item185InnerBase
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherL62
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherL72
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherU42Tools
import CFSG.RankThree.PartTwo.Sec18.Item185NormIrredOmega
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LinearPlane
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFormFixed
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearInnerFixed
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item185Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projOmegaMinus)
open CFSG.RankThree.PartTwo.Sec4.Item434Kit (WreathFacts vecElt baseA wreathW isPGroup_wreathW
  le_card_wreathW)
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther (blk permSL slEquivProjSL blk_pow_three
  permSL_conj_blk blk_smul_of_ne blk_smul_fst blk_smul_snd blk_smul_fst_ne commute_blk_blk
  eq_zero_of_blk_pow_smul pow_smul_eq_of_smul_eq permSL_pow permSL_one SL_ext_smul gf2_vec_add_self)
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther.L62 (factorization_card_SL6)
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther.L72 (factorization_card_SL7)
open scoped MatrixGroups

private theorem vecElt_map {G H : Type} [Group G] [Group H] (e : G ≃* H) (z : Fin 3 → G)
    (v : Fin 3 → ZMod 3) : vecElt (fun i => e (z i)) v = e (vecElt z v) := by
  simp [vecElt, map_mul, map_pow]

private theorem wreathW_map {G H : Type} [Group G] [Group H] (e : G ≃* H) (z : Fin 3 → G)
    (t : G) : wreathW (fun i => e (z i)) (e t) = (wreathW z t).map e.toMonoidHom := by
  simp only [wreathW, baseA, Subgroup.map_sup, MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom]

private theorem sylowSignModel_of_mulEquiv {G H : Type} [Group G] [Group H] [Finite G] [Finite H]
    (e : G ≃* H) (h : SylowSignModel G) : SylowSignModel H := by
  obtain ⟨z, t, s, hf, hW, h81, hs⟩ := h
  have hcard : Nat.card H = Nat.card G := (Nat.card_congr e.toEquiv).symm
  refine ⟨fun i => e (z i), e t, e s, ?_, ?_, ?_, ?_⟩
  · refine ⟨fun i => ?_, fun i j => ?_, fun v hv => ?_, ?_, ?_, ?_, ?_, fun v hv => ?_⟩
    · show e (z i) ^ 3 = 1
      rw [← map_pow, hf.pow_z i, map_one]
    · show e (z i) * e (z j) = e (z j) * e (z i)
      rw [← map_mul, ← map_mul, hf.comm_z i j]
    · rw [vecElt_map] at hv
      exact hf.inj v (e.injective (by rw [hv, map_one]))
    · show e t ^ 3 = 1
      rw [← map_pow, hf.pow_t, map_one]
    · show e t * e (z 0) * (e t)⁻¹ = e (z 1)
      rw [← map_inv, ← map_mul, ← map_mul, hf.conj0]
    · show e t * e (z 1) * (e t)⁻¹ = e (z 2)
      rw [← map_inv, ← map_mul, ← map_mul, hf.conj1]
    · show e t * e (z 2) * (e t)⁻¹ = e (z 0)
      rw [← map_inv, ← map_mul, ← map_mul, hf.conj2]
    · rw [vecElt_map] at hv
      exact hf.t_ne v (e.injective hv)
  · rw [wreathW_map, Subgroup.card_map_of_injective e.injective, hcard]
    exact hW
  · rw [wreathW_map, Subgroup.card_map_of_injective e.injective]
    exact h81
  · intro w
    rw [vecElt_map, vecElt_map, ← map_inv, ← map_mul, ← map_mul, hs w]

private theorem blk_symm_eq_sq' {n : ℕ} {a b : Fin n} (hab : a ≠ b) :
    blk hab.symm = blk hab ^ 2 := by
  apply SL_ext_smul
  intro k
  rw [pow_two, mul_smul]
  by_cases hka : k = a
  · rw [hka, blk_smul_snd hab.symm, blk_smul_fst hab, blk_smul_snd hab, add_comm]
  by_cases hkb : k = b
  · rw [hkb, blk_smul_fst hab.symm, blk_smul_snd hab, smul_add, blk_smul_fst hab,
      blk_smul_snd hab, add_comm (Pi.single b 1), add_assoc, gf2_vec_add_self, add_zero]
  · rw [blk_smul_of_ne hab.symm hkb hka, blk_smul_of_ne hab hka hkb, blk_smul_of_ne hab hka hkb]

private theorem wreathFacts_blocks {n : ℕ} {a₀ b₀ a₁ b₁ a₂ b₂ : Fin n}
    (hinj : Function.Injective ![a₀, b₀, a₁, b₁, a₂, b₂])
    (h01 : a₀ ≠ b₀) (h23 : a₁ ≠ b₁) (h45 : a₂ ≠ b₂)
    {σ : Equiv.Perm (Fin n)} (hσ3 : σ ^ 3 = 1)
    (hσ0 : σ a₀ = a₁) (hσ1 : σ b₀ = b₁) (hσ2 : σ a₁ = a₂) (hσ3' : σ b₁ = b₂)
    (hσ4 : σ a₂ = a₀) (hσ5 : σ b₂ = b₀) :
    WreathFacts ![blk h01, blk h23, blk h45] (permSL σ) := by
  have d02 : a₀ ≠ a₁ := hinj.ne (show (0 : Fin 6) ≠ 2 by decide)
  have d03 : a₀ ≠ b₁ := hinj.ne (show (0 : Fin 6) ≠ 3 by decide)
  have d04 : a₀ ≠ a₂ := hinj.ne (show (0 : Fin 6) ≠ 4 by decide)
  have d05 : a₀ ≠ b₂ := hinj.ne (show (0 : Fin 6) ≠ 5 by decide)
  have d12 : b₀ ≠ a₁ := hinj.ne (show (1 : Fin 6) ≠ 2 by decide)
  have d13 : b₀ ≠ b₁ := hinj.ne (show (1 : Fin 6) ≠ 3 by decide)
  have d14 : b₀ ≠ a₂ := hinj.ne (show (1 : Fin 6) ≠ 4 by decide)
  have d15 : b₀ ≠ b₂ := hinj.ne (show (1 : Fin 6) ≠ 5 by decide)
  have d24 : a₁ ≠ a₂ := hinj.ne (show (2 : Fin 6) ≠ 4 by decide)
  have d25 : a₁ ≠ b₂ := hinj.ne (show (2 : Fin 6) ≠ 5 by decide)
  have d34 : b₁ ≠ a₂ := hinj.ne (show (3 : Fin 6) ≠ 4 by decide)
  have d35 : b₁ ≠ b₂ := hinj.ne (show (3 : Fin 6) ≠ 5 by decide)
  have c01 : Commute (blk h01) (blk h23) := commute_blk_blk h01 h23 d02 d03 d12 d13
  have c02 : Commute (blk h01) (blk h45) := commute_blk_blk h01 h45 d04 d05 d14 d15
  have c12 : Commute (blk h23) (blk h45) := commute_blk_blk h23 h45 d24 d25 d34 d35
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    exacts [blk_pow_three h01, blk_pow_three h23, blk_pow_three h45]
  · intro i j
    fin_cases i <;> fin_cases j <;>
      first
        | rfl
        | exact c01.eq
        | exact c01.symm.eq
        | exact c02.eq
        | exact c02.symm.eq
        | exact c12.eq
        | exact c12.symm.eq
  · intro v hv
    have hv' : blk h01 ^ (v 0).val * blk h23 ^ (v 1).val * blk h45 ^ (v 2).val = 1 := hv
    have hfix : ∀ k : Fin n, (blk h01 ^ (v 0).val * blk h23 ^ (v 1).val * blk h45 ^ (v 2).val) •
        (Pi.single k 1 : Fin n → GaloisField 2 1) = Pi.single k 1 := fun k => by
      rw [hv', one_smul]
    have hz0 : (v 0).val = 0 := by
      have h := hfix a₀
      rw [mul_smul, mul_smul, pow_smul_eq_of_smul_eq (blk_smul_of_ne h45 d04 d05) _,
        pow_smul_eq_of_smul_eq (blk_smul_of_ne h23 d02 d03) _] at h
      exact eq_zero_of_blk_pow_smul h01 (ZMod.val_lt _) h
    have hz1 : (v 1).val = 0 := by
      have h := hfix a₁
      rw [(Commute.pow_pow c01 (v 0).val (v 1).val).eq, mul_smul, mul_smul,
        pow_smul_eq_of_smul_eq (blk_smul_of_ne h45 d24 d25) _,
        pow_smul_eq_of_smul_eq (blk_smul_of_ne h01 d02.symm d12.symm) _] at h
      exact eq_zero_of_blk_pow_smul h23 (ZMod.val_lt _) h
    have hz2 : (v 2).val = 0 := by
      have h := hfix a₂
      have hc : Commute (blk h01 ^ (v 0).val * blk h23 ^ (v 1).val) (blk h45 ^ (v 2).val) :=
        Commute.mul_left (Commute.pow_pow c02 _ _) (Commute.pow_pow c12 _ _)
      rw [hc.eq, mul_smul, mul_smul,
        pow_smul_eq_of_smul_eq (blk_smul_of_ne h23 d24.symm d34.symm) _,
        pow_smul_eq_of_smul_eq (blk_smul_of_ne h01 d04.symm d14.symm) _] at h
      exact eq_zero_of_blk_pow_smul h45 (ZMod.val_lt _) h
    funext i
    fin_cases i
    · exact (ZMod.val_eq_zero _).mp hz0
    · exact (ZMod.val_eq_zero _).mp hz1
    · exact (ZMod.val_eq_zero _).mp hz2
  · show permSL σ ^ 3 = 1
    rw [← permSL_pow, hσ3, permSL_one]
  · exact permSL_conj_blk σ h01 h23 hσ0 hσ1
  · exact permSL_conj_blk σ h23 h45 hσ2 hσ3'
  · exact permSL_conj_blk σ h45 h01 hσ4 hσ5
  · intro v hv
    have hc : Commute (vecElt ![blk h01, blk h23, blk h45] v) (blk h01) := by
      show Commute (blk h01 ^ (v 0).val * blk h23 ^ (v 1).val * blk h45 ^ (v 2).val) (blk h01)
      exact Commute.mul_left (Commute.mul_left (Commute.pow_left (Commute.refl _) _)
        (Commute.pow_left c01.symm _)) (Commute.pow_left c02.symm _)
    rw [hv] at hc
    have hconj : permSL σ * blk h01 * (permSL σ)⁻¹ = blk h01 := by
      rw [hc.eq, mul_inv_cancel_right]
    have hblk : blk h01 = blk h23 := hconj.symm.trans (permSL_conj_blk σ h01 h23 hσ0 hσ1)
    have hne := blk_smul_fst_ne h01
    rw [hblk] at hne
    exact hne (blk_smul_of_ne h23 d02 d03)

private theorem sign_blocks {n : ℕ} {a₀ b₀ a₁ b₁ a₂ b₂ : Fin n} (h01 : a₀ ≠ b₀)
    (h23 : a₁ ≠ b₁) (h45 : a₂ ≠ b₂) {τ : Equiv.Perm (Fin n)}
    (hτ0 : τ a₀ = b₀) (hτ1 : τ b₀ = a₀) (hτ2 : τ a₁ = b₁) (hτ3 : τ b₁ = a₁)
    (hτ4 : τ a₂ = a₂) (hτ5 : τ b₂ = b₂) :
    permSL τ * blk h01 * (permSL τ)⁻¹ = blk h01 ^ 2 ∧
      permSL τ * blk h23 * (permSL τ)⁻¹ = blk h23 ^ 2 ∧
      permSL τ * blk h45 * (permSL τ)⁻¹ = blk h45 :=
  ⟨(permSL_conj_blk τ h01 h01.symm hτ0 hτ1).trans (blk_symm_eq_sq' h01),
    (permSL_conj_blk τ h23 h23.symm hτ2 hτ3).trans (blk_symm_eq_sq' h23),
    permSL_conj_blk τ h45 h45 hτ4 hτ5⟩

private theorem card_wreathW_of_factorization {H : Type} [Group H] [Finite H] {z : Fin 3 → H}
    {t : H} (hf : WreathFacts z t) (h4 : (Nat.card H).factorization 3 = 4) :
    Nat.card (wreathW z t) = 81 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle := CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.card_le_of_isPGroup (isPGroup_wreathW hf)
  rw [h4] at hle
  have := le_card_wreathW hf
  norm_num at hle
  omega

private def sigma6 : Equiv.Perm (Fin 6) :=
  ⟨![2, 3, 4, 5, 0, 1], ![4, 5, 0, 1, 2, 3], by decide, by decide⟩

private def tau6 : Equiv.Perm (Fin 6) :=
  ⟨![1, 0, 3, 2, 4, 5], ![1, 0, 3, 2, 4, 5], by decide, by decide⟩

private def sigma7 : Equiv.Perm (Fin 7) :=
  ⟨![2, 3, 4, 5, 0, 1, 6], ![4, 5, 0, 1, 2, 3, 6], by decide, by decide⟩

private def tau7 : Equiv.Perm (Fin 7) :=
  ⟨![1, 0, 3, 2, 4, 5, 6], ![1, 0, 3, 2, 4, 5, 6], by decide, by decide⟩

private theorem sigma6_pow_three : sigma6 ^ 3 = 1 := by
  ext x
  fin_cases x <;> rfl

private theorem sigma7_pow_three : sigma7 ^ 3 = 1 := by
  ext x
  fin_cases x <;> rfl

private theorem sylowSignModel_SL_six : SylowSignModel SL(6, GaloisField 2 1) := by
  have hinj : Function.Injective ![(0 : Fin 6), 1, 2, 3, 4, 5] := by decide
  have h01 : (0 : Fin 6) ≠ 1 := by decide
  have h23 : (2 : Fin 6) ≠ 3 := by decide
  have h45 : (4 : Fin 6) ≠ 5 := by decide
  have hf := wreathFacts_blocks hinj h01 h23 h45 sigma6_pow_three (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  obtain ⟨s0, s1, s2⟩ := sign_blocks h01 h23 h45 (τ := tau6) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have hW := card_wreathW_of_factorization hf factorization_card_SL6
  unfold SylowSignModel
  refine ⟨![blk h01, blk h23, blk h45], permSL sigma6, permSL tau6, hf, ?_, ?_, ?_⟩
  · rw [factorization_card_SL6]
    exact hW.trans (by norm_num)
  · exact hW
  · intro w
    exact CFSG.RankThree.PartTwo.Sec8.Item812Res12.conj_vecElt_of_sgn hf s0 s1 s2 w

private theorem sylowSignModel_SL_seven : SylowSignModel SL(7, GaloisField 2 1) := by
  have hinj : Function.Injective ![(0 : Fin 7), 1, 2, 3, 4, 5] := by decide
  have h01 : (0 : Fin 7) ≠ 1 := by decide
  have h23 : (2 : Fin 7) ≠ 3 := by decide
  have h45 : (4 : Fin 7) ≠ 5 := by decide
  have hf := wreathFacts_blocks hinj h01 h23 h45 sigma7_pow_three (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  obtain ⟨s0, s1, s2⟩ := sign_blocks h01 h23 h45 (τ := tau7) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have hW := card_wreathW_of_factorization hf factorization_card_SL7
  unfold SylowSignModel
  refine ⟨![blk h01, blk h23, blk h45], permSL sigma7, permSL tau7, hf, ?_, ?_, ?_⟩
  · rw [factorization_card_SL7]
    exact hW.trans (by norm_num)
  · exact hW
  · intro w
    exact CFSG.RankThree.PartTwo.Sec8.Item812Res12.conj_vecElt_of_sgn hf s0 s1 s2 w

theorem sylowSignModel_projSL_six_two : SylowSignModel (projSL 6 (GaloisField 2 1)) :=
  sylowSignModel_of_mulEquiv (slEquivProjSL (by norm_num)) sylowSignModel_SL_six

theorem sylowSignModel_projSL_seven_two : SylowSignModel (projSL 7 (GaloisField 2 1)) :=
  sylowSignModel_of_mulEquiv (slEquivProjSL (by norm_num)) sylowSignModel_SL_seven

section U4

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther.U42 (SU42 mat mat_mul mat_pow mat_one
  mat_injective mat_t t F4 ζ ζ_cube ζ_ne_one ζ_sq_cube ρ diagS mem_SU42 uData
  nonempty_mulEquiv factorization_card_SU42)

private theorem orderOf_ζ : orderOf ζ = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime ζ_cube ζ_ne_one

private theorem three_dvd_of_zeta_pow {n : ℕ} (h : ζ ^ n = 1) : 3 ∣ n := by
  have := orderOf_dvd_of_pow_eq_one h
  rwa [orderOf_ζ] at this

private theorem ζ_two_mul_self : ζ ^ 2 * ζ = 1 := by
  linear_combination ζ_cube

private theorem ζ_sq_sq : (ζ ^ 2) ^ 2 = ζ := by
  linear_combination ζ * ζ_cube

private noncomputable def dzS : Fin 3 → Fin 4 → F4 :=
  ![![ζ ^ 2, ζ, ζ ^ 2, ζ], ![ζ ^ 2, ζ ^ 2, ζ, ζ], ![ζ, ζ ^ 2, ζ ^ 2, ζ]]

private theorem dzS_cube (i : Fin 3) (k : Fin 4) : dzS i k ^ 3 = 1 := by
  fin_cases i <;> fin_cases k <;> simp [dzS, ζ_cube, ζ_sq_cube]

private theorem prod_dzS (i : Fin 3) : ∏ k, dzS i k = 1 := by
  fin_cases i <;> simp [dzS, Fin.prod_univ_four] <;>
    linear_combination (ζ ^ 2 * ζ + 1) * ζ_two_mul_self

private noncomputable def zS (i : Fin 3) : SU42 := diagS (dzS i) (dzS_cube i) (prod_dzS i)

private theorem mat_zS (i : Fin 3) : mat (zS i) = diagonal (dzS i) := rfl

private theorem mat_vecEltS (v : Fin 3 → ZMod 3) :
    mat (vecElt zS v) = diagonal fun k =>
      dzS 0 k ^ (v 0).val * dzS 1 k ^ (v 1).val * dzS 2 k ^ (v 2).val := by
  rw [vecElt, mat_mul, mat_mul, mat_pow, mat_pow, mat_pow, mat_zS, mat_zS, mat_zS,
    Matrix.diagonal_pow, Matrix.diagonal_pow, Matrix.diagonal_pow,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  rfl

private def σ4 : Equiv.Perm (Fin 4) := ⟨![3, 2, 1, 0], ![3, 2, 1, 0], by decide, by decide⟩

private noncomputable def sGL : GL (Fin 4) F4 :=
  ⟨σ4.permMatrix F4, σ4⁻¹.permMatrix F4,
    by rw [← permMatrix_mul, inv_mul_cancel, permMatrix_one],
    by rw [← permMatrix_mul, mul_inv_cancel, permMatrix_one]⟩

private theorem σ4_map_bar : (σ4.permMatrix F4).map uData.bar = σ4.permMatrix F4 := by
  ext i j
  simp only [map_apply, PEquiv.toMatrix_apply]
  split_ifs <;> simp

private theorem sGL_pieces :
    ((σ4.permMatrix F4).map uData.bar)ᵀ * σ4.permMatrix F4 = 1 ∧
      (σ4.permMatrix F4).det = 1 := by
  constructor
  · rw [σ4_map_bar, transpose_permMatrix, ← permMatrix_mul, mul_inv_cancel, permMatrix_one]
  · rw [det_permutation]
    have hs : Equiv.Perm.sign σ4 = 1 := by decide
    rw [hs]
    simp

private noncomputable def sU : SU42 := ⟨sGL, mem_SU42.mpr sGL_pieces⟩

private theorem mat_sU : mat sU = σ4.permMatrix F4 := rfl

private theorem t_mul_zS0 : t * zS 0 = zS 1 * t := by
  apply mat_injective
  rw [mat_mul, mat_mul, mat_t, mat_zS, mat_zS]
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases a <;> fin_cases b <;> simp [dzS, ρ]

private theorem t_mul_zS1 : t * zS 1 = zS 2 * t := by
  apply mat_injective
  rw [mat_mul, mat_mul, mat_t, mat_zS, mat_zS]
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases a <;> fin_cases b <;> simp [dzS, ρ]

private theorem t_mul_zS2 : t * zS 2 = zS 0 * t := by
  apply mat_injective
  rw [mat_mul, mat_mul, mat_t, mat_zS, mat_zS]
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases a <;> fin_cases b <;> simp [dzS, ρ]

private theorem sU_mul_zS0 : sU * zS 0 = zS 0 ^ 2 * sU := by
  apply mat_injective
  rw [mat_mul, mat_mul, mat_pow, mat_zS, mat_sU, Matrix.diagonal_pow]
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases a <;> fin_cases b <;> simp [dzS, σ4, ζ_sq_sq]

private theorem sU_mul_zS1 : sU * zS 1 = zS 1 ^ 2 * sU := by
  apply mat_injective
  rw [mat_mul, mat_mul, mat_pow, mat_zS, mat_sU, Matrix.diagonal_pow]
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases a <;> fin_cases b <;> simp [dzS, σ4, ζ_sq_sq]

private theorem sU_mul_zS2 : sU * zS 2 = zS 2 * sU := by
  apply mat_injective
  rw [mat_mul, mat_mul, mat_zS, mat_sU]
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases a <;> fin_cases b <;> simp [dzS, σ4]

private theorem sU_conj0 : sU * zS 0 * sU⁻¹ = zS 0 ^ 2 := by
  rw [sU_mul_zS0, mul_inv_cancel_right]

private theorem sU_conj1 : sU * zS 1 * sU⁻¹ = zS 1 ^ 2 := by
  rw [sU_mul_zS1, mul_inv_cancel_right]

private theorem sU_conj2 : sU * zS 2 * sU⁻¹ = zS 2 := by
  rw [sU_mul_zS2, mul_inv_cancel_right]

private theorem wreathFacts_S : WreathFacts zS t where
  pow_z i := by
    apply mat_injective
    rw [mat_pow, mat_zS, Matrix.diagonal_pow, mat_one, ← Matrix.diagonal_one]
    congr 1
    funext k
    exact dzS_cube i k
  comm_z i j := by
    apply mat_injective
    rw [mat_mul, mat_mul, mat_zS, mat_zS, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext k
    exact mul_comm _ _
  inj v hv := by
    have hmat : mat (vecElt zS v) = 1 := by rw [hv]; rfl
    rw [mat_vecEltS] at hmat
    have h0 : dzS 0 0 ^ (v 0).val * dzS 1 0 ^ (v 1).val * dzS 2 0 ^ (v 2).val = 1 := by
      have := congrFun (congrFun hmat 0) 0
      rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at this
      exact this
    have h1 : dzS 0 1 ^ (v 0).val * dzS 1 1 ^ (v 1).val * dzS 2 1 ^ (v 2).val = 1 := by
      have := congrFun (congrFun hmat 1) 1
      rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at this
      exact this
    have h2 : dzS 0 2 ^ (v 0).val * dzS 1 2 ^ (v 1).val * dzS 2 2 ^ (v 2).val = 1 := by
      have := congrFun (congrFun hmat 2) 2
      rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at this
      exact this
    have h0' : (ζ ^ 2) ^ (v 0).val * (ζ ^ 2) ^ (v 1).val * ζ ^ (v 2).val = 1 := h0
    have h1' : ζ ^ (v 0).val * (ζ ^ 2) ^ (v 1).val * (ζ ^ 2) ^ (v 2).val = 1 := h1
    have h2' : (ζ ^ 2) ^ (v 0).val * ζ ^ (v 1).val * (ζ ^ 2) ^ (v 2).val = 1 := h2
    have d0 : 3 ∣ 2 * (v 0).val + 2 * (v 1).val + (v 2).val :=
      three_dvd_of_zeta_pow (by rw [pow_add, pow_add, pow_mul, pow_mul]; exact h0')
    have d1 : 3 ∣ (v 0).val + 2 * (v 1).val + 2 * (v 2).val :=
      three_dvd_of_zeta_pow (by rw [pow_add, pow_add, pow_mul, pow_mul]; exact h1')
    have d2 : 3 ∣ 2 * (v 0).val + (v 1).val + 2 * (v 2).val :=
      three_dvd_of_zeta_pow (by rw [pow_add, pow_add, pow_mul, pow_mul]; exact h2')
    have key : ∀ x y z : ZMod 3,
        3 ∣ 2 * x.val + 2 * y.val + z.val → 3 ∣ x.val + 2 * y.val + 2 * z.val →
          3 ∣ 2 * x.val + y.val + 2 * z.val → x = 0 ∧ y = 0 ∧ z = 0 := by
      decide
    obtain ⟨hx, hy, hz⟩ := key (v 0) (v 1) (v 2) d0 d1 d2
    funext i
    fin_cases i
    · exact hx
    · exact hy
    · exact hz
  pow_t := CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther.U42.wreathFacts.pow_t
  conj0 := by rw [t_mul_zS0, mul_inv_cancel_right]
  conj1 := by rw [t_mul_zS1, mul_inv_cancel_right]
  conj2 := by rw [t_mul_zS2, mul_inv_cancel_right]
  t_ne v hv := by
    have h := congrFun (congrFun (congrArg mat hv) 1) 0
    rw [mat_vecEltS, Matrix.diagonal_apply_ne _ (by decide), mat_t] at h
    simp [ρ] at h

private theorem sylowSignModel_SU42 : SylowSignModel SU42 := by
  have hW := card_wreathW_of_factorization wreathFacts_S factorization_card_SU42
  unfold SylowSignModel
  refine ⟨zS, t, sU, wreathFacts_S, ?_, ?_, ?_⟩
  · rw [factorization_card_SU42]
    exact hW.trans (by norm_num)
  · exact hW
  · intro w
    exact CFSG.RankThree.PartTwo.Sec8.Item812Res12.conj_vecElt_of_sgn wreathFacts_S
      sU_conj0 sU_conj1 sU_conj2 w

theorem sylowSignModel_projSU_four_two : SylowSignModel (projSU 4 2 1) := by
  obtain ⟨e⟩ := nonempty_mulEquiv
  exact sylowSignModel_of_mulEquiv e.symm sylowSignModel_SU42

end U4

theorem sylowSignModel_projOmegaMinus_three_two {b c : GaloisField 2 1}
    (hbc : ∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0) :
    SylowSignModel (projOmegaMinus 3 (GaloisField 2 1) b c) := by
  obtain ⟨e⟩ := CFSG.RankThree.PartTwo.Sec4.RonanK429F.nonempty_projOmegaMinus_equiv_om8 hbc
  exact sylowSignModel_of_mulEquiv e.symm (omega_sylowSignModel hbc)

theorem normIrred_projSL_six_two : NormIrred (projSL 6 (GaloisField 2 1)) :=
  NormIrred.of_sylowSignModel sylowSignModel_projSL_six_two

theorem normIrred_projSL_seven_two : NormIrred (projSL 7 (GaloisField 2 1)) :=
  NormIrred.of_sylowSignModel sylowSignModel_projSL_seven_two

theorem normIrred_projSU_four_two : NormIrred (projSU 4 2 1) :=
  NormIrred.of_sylowSignModel sylowSignModel_projSU_four_two

theorem normIrred_projOmegaMinus_three_two {b c : GaloisField 2 1}
    (hbc : ∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0) :
    NormIrred (projOmegaMinus 3 (GaloisField 2 1) b c) :=
  NormIrred.of_sylowSignModel (sylowSignModel_projOmegaMinus_three_two hbc)

end CFSG.RankThree.PartTwo.Sec18.Item185Proof
