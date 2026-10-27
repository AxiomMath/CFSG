module

public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LieType.Universal.Unitary.Basic
public import CFSG.LieType.BorelTits.UnitaryForm
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
import Mathlib.LinearAlgebra.Matrix.Notation
import CFSG.LocalAnalysis.UniquenessCase.UC22S217U38
import CFSG.LocalAnalysis.UniquenessCase.Lie.SU3Cover
import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridgeSUTorus
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846d
public import CFSG.LocalAnalysis.UniquenessCase.UCFront07
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
public import CFSG.LocalAnalysis.UniquenessCase.UCR638
public import CFSG.Milestones.ASVolI.I2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

local notation "Y₂" => (!![0, 0, 1; 0, 1, 0; 1, 0, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2))

local notation "ι₂" K => ZMod.castHom (dvd_refl 2) K

theorem uc22s217u38_exists_root {K : Type} [Field K] [Finite K] (hK : Nat.card K = 64) :
    ∃ t : K, t ^ 9 = 1 ∧ t ^ 3 ≠ 1 := by
  have hcard : Nat.card Kˣ = 63 := by simp only [Nat.card_units, hK]
  by_contra hne
  have hall : ∀ x : Kˣ, x ^ 21 = 1 := fun x => by
    have h63 : (x : K) ^ 63 = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← hcard, pow_card_eq_one', Units.val_one]
    have h9 : ((x : K) ^ 7) ^ 9 = 1 := by rw [← pow_mul]; exact h63
    have h3 : ((x : K) ^ 7) ^ 3 = 1 := by
      by_contra h3
      exact hne ⟨(x : K) ^ 7, h9, h3⟩
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, show (21 : ℕ) = 7 * 3 from rfl, pow_mul]
    exact h3
  have hexp : Monoid.exponent Kˣ ∣ 21 := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 hall
  rw [IsCyclic.exponent_eq_card, hcard] at hexp
  norm_num at hexp

private theorem uc22s217u38_y₂_cube : Y₂ * Y₂ * Y₂ = 1 := by decide

private theorem uc22s217u38_y₂_det : Matrix.det Y₂ = 1 := by
  rw [Matrix.det_fin_three]
  decide

private theorem uc22s217u38_y₂_unitary : Y₂ᵀ * antidiag 3 * Y₂ = antidiag 3 := by decide

private theorem uc22s217u38_y₂_entry : (Y₂ ^ 1) 0 2 = 1 ∧ (Y₂ ^ 2) 0 2 = 1 := by decide

private theorem uc22s217u38_y₂_supp (a b : Fin 3) : Y₂ a b = 0 ∨ (a = 1 ↔ b = 1) := by
  fin_cases a <;> fin_cases b <;> decide

private theorem uc22s217u38_rev_one : ∀ s : Fin 3, (Fin.rev s = 1 ↔ s = 1) := by decide

section Elements

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private def uc22s217u38_d (t : K) : Fin 3 → K := fun s => if s = 1 then t ^ 7 else t

private theorem uc22s217u38_d_pow {t : K} (ht : t ^ 9 = 1) (s : Fin 3) :
    uc22s217u38_d t s ^ 9 = 1 := by
  by_cases hs : s = 1
  · rw [show uc22s217u38_d t s = t ^ 7 from if_pos hs, ← pow_mul, show 7 * 9 = 9 * 7 from rfl,
      pow_mul, ht, one_pow]
  · rw [show uc22s217u38_d t s = t from if_neg hs, ht]

private theorem uc22s217u38_d_eq {t : K} {a b : Fin 3} (hab : a = 1 ↔ b = 1) :
    uc22s217u38_d t a = uc22s217u38_d t b := by
  by_cases ha : a = 1
  · rw [show uc22s217u38_d t a = t ^ 7 from if_pos ha,
      show uc22s217u38_d t b = t ^ 7 from if_pos (hab.1 ha)]
  · rw [show uc22s217u38_d t a = t from if_neg ha,
      show uc22s217u38_d t b = t from if_neg (fun hb => ha (hab.2 hb))]

private theorem uc22s217u38_d_unitary {t : K} (ht : t ^ 9 = 1) (s : Fin 3) :
    unitaryInvolution K 2 3 (uc22s217u38_d t s) * uc22s217u38_d t (Fin.rev s) = 1 := by
  rw [uc22s217u38_d_eq (uc22s217u38_rev_one s), unitaryInvolution_apply,
    show 2 ^ 3 = 8 from rfl, ← pow_succ]
  exact uc22s217u38_d_pow ht s

private theorem uc22s217u38_d_det {t : K} (ht : t ^ 9 = 1) :
    (diagonal (uc22s217u38_d t)).det = 1 := by
  rw [Matrix.det_diagonal, Fin.prod_univ_three]
  have h0 : uc22s217u38_d t 0 = t := if_neg (by decide)
  have h1 : uc22s217u38_d t 1 = t ^ 7 := if_pos rfl
  have h2 : uc22s217u38_d t 2 = t := if_neg (by decide)
  rw [h0, h1, h2, show t * t ^ 7 * t = t ^ 9 by ring, ht]

private noncomputable def uc22s217u38_h {t : K} (ht : t ^ 9 = 1) :
    SU (unitaryInvolution K 2 3) 3 :=
  ⟨CFSG.StandardType.InnerDiagSU.diagJ (uc22s217u38_d t) (uc22s217u38_d_unitary ht),
    mem_SU.2 ⟨uc22s217u38_d_det ht,
      CFSG.StandardType.InnerDiagSU.isJUnitary_diagJ _ (uc22s217u38_d_unitary ht)⟩⟩

private theorem uc22s217u38_h_mat {t : K} (ht : t ^ 9 = 1) :
    SUExtras.mat (unitaryInvolution K 2 3) 3 (uc22s217u38_h ht) = diagonal (uc22s217u38_d t) :=
  rfl

private theorem uc22s217u38_σ_ι (a : ZMod 2) :
    unitaryInvolution K 2 3 ((ι₂ K) a) = (ι₂ K) a :=
  RingHom.congr_fun (Subsingleton.elim ((unitaryInvolution K 2 3).toRingHom.comp (ι₂ K)) (ι₂ K)) a

private theorem uc22s217u38_yK_cube :
    (ι₂ K).mapMatrix Y₂ * (ι₂ K).mapMatrix Y₂ * (ι₂ K).mapMatrix Y₂ = 1 := by
  rw [← map_mul, ← map_mul, uc22s217u38_y₂_cube, map_one]

private theorem uc22s217u38_yK_det : ((ι₂ K).mapMatrix Y₂).det = 1 := by
  rw [← RingHom.map_det, uc22s217u38_y₂_det, map_one]

private theorem uc22s217u38_yK_unitary :
    conjTr (unitaryInvolution K 2 3) ((ι₂ K).mapMatrix Y₂) * antidiag 3 * (ι₂ K).mapMatrix Y₂ =
      antidiag 3 := by
  have hconj : conjTr (unitaryInvolution K 2 3) ((ι₂ K).mapMatrix Y₂) = (ι₂ K).mapMatrix Y₂ᵀ := by
    ext i j
    simp only [conjTr, Matrix.transpose_apply, Matrix.map_apply, RingHom.mapMatrix_apply]
    exact uc22s217u38_σ_ι _
  have hanti : (ι₂ K).mapMatrix (antidiag 3 : Matrix (Fin 3) (Fin 3) (ZMod 2)) = antidiag 3 := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, antidiag, Matrix.of_apply]
    split_ifs <;> simp
  rw [hconj, ← hanti, ← map_mul, ← map_mul, uc22s217u38_y₂_unitary]

private noncomputable def uc22s217u38_y : SU (unitaryInvolution K 2 3) 3 :=
  ⟨⟨(ι₂ K).mapMatrix Y₂, (ι₂ K).mapMatrix Y₂ * (ι₂ K).mapMatrix Y₂,
      by rw [← Matrix.mul_assoc]; exact uc22s217u38_yK_cube, uc22s217u38_yK_cube⟩,
    mem_SU.2 ⟨uc22s217u38_yK_det, uc22s217u38_yK_unitary⟩⟩

private theorem uc22s217u38_y_mat :
    SUExtras.mat (unitaryInvolution K 2 3) 3 (uc22s217u38_y : SU (unitaryInvolution K 2 3) 3) =
      (ι₂ K).mapMatrix Y₂ :=
  rfl

theorem uc22s217u38_exists_hy (hK : Nat.card K = (2 ^ 3) ^ 2) :
    ∃ h y : SU (unitaryInvolution K 2 3) 3, h * y = y * h ∧ h ^ 9 = 1 ∧ y ^ 9 = 1 ∧
      ∀ i j : ℕ, h ^ i * y ^ j ∈ center (SU (unitaryInvolution K 2 3) 3) → 3 ∣ i ∧ 3 ∣ j := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨t, ht9, ht3⟩ := uc22s217u38_exists_root (hK.trans (by norm_num))
  have ht0 : t ≠ 0 := fun h0 => by
    rw [h0, zero_pow (by norm_num)] at ht9
    exact zero_ne_one ht9
  have hY₂3 : Y₂ ^ 3 = 1 := by
    rw [pow_three']
    exact uc22s217u38_y₂_cube
  have hy3 : (uc22s217u38_y : SU (unitaryInvolution K 2 3) 3) ^ 3 = 1 := by
    apply SUExtras.mat_injective
    rw [map_pow, map_one, uc22s217u38_y_mat, pow_three']
    exact uc22s217u38_yK_cube
  refine ⟨uc22s217u38_h ht9, uc22s217u38_y, ?_, ?_, ?_, ?_⟩
  ·
    apply SUExtras.mat_injective
    rw [map_mul, map_mul, uc22s217u38_h_mat, uc22s217u38_y_mat]
    ext a b
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal, RingHom.mapMatrix_apply, Matrix.map_apply]
    by_cases hab : Y₂ a b = 0
    · rw [hab, map_zero, mul_zero, zero_mul]
    · rw [uc22s217u38_d_eq ((uc22s217u38_y₂_supp a b).resolve_left hab), mul_comm]
  ·
    apply SUExtras.mat_injective
    rw [map_pow, map_one, uc22s217u38_h_mat, Matrix.diagonal_pow, ← Matrix.diagonal_one]
    congr 1
    funext s
    rw [Pi.pow_apply]
    exact uc22s217u38_d_pow ht9 s
  ·
    rw [show 9 = 3 * 3 from rfl, pow_mul, hy3, one_pow]
  ·
    intro i j hz
    obtain ⟨c, hc⟩ := CFSG.StandardType.InnerDiagSU.exists_scalar_of_mem_center hK (n := 3)
      (by norm_num) (by decide) hz
    have e1 : SUExtras.mat (unitaryInvolution K 2 3) 3 (uc22s217u38_h ht9 ^ i * uc22s217u38_y ^ j) =
        diagonal (uc22s217u38_d t ^ i) * (ι₂ K).mapMatrix (Y₂ ^ (j % 3)) := by
      rw [map_mul, map_pow, map_pow, uc22s217u38_h_mat, uc22s217u38_y_mat, Matrix.diagonal_pow,
        ← map_pow, pow_eq_pow_mod j hY₂3]
    have hm := e1.symm.trans hc
    have hentry : ∀ a b : Fin 3, uc22s217u38_d t a ^ i * (ι₂ K) ((Y₂ ^ (j % 3)) a b) =
        Matrix.scalar (Fin 3) c a b := fun a b => by
      rw [← hm, Matrix.diagonal_mul, Pi.pow_apply, RingHom.mapMatrix_apply, Matrix.map_apply]
    have hd0 : uc22s217u38_d t 0 = t := if_neg (by decide)
    have hd1 : uc22s217u38_d t 1 = t ^ 7 := if_pos rfl
    have hj : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
    rcases hj with hj | hj | hj
    ·
      have e00 := hentry 0 0
      have e11 := hentry 1 1
      rw [hj, pow_zero, Matrix.one_apply_eq, map_one, mul_one, hd0, Matrix.scalar_apply,
        Matrix.diagonal_apply_eq] at e00
      rw [hj, pow_zero, Matrix.one_apply_eq, map_one, mul_one, hd1, Matrix.scalar_apply,
        Matrix.diagonal_apply_eq] at e11
      have heq : t ^ i = (t ^ 7) ^ i := e00.trans e11.symm
      have h6 : t ^ (6 * i) = 1 := by
        have h1 : t ^ (6 * i) * t ^ i = 1 * t ^ i := by
          rw [← pow_add, one_mul, show 6 * i + i = 7 * i by ring, pow_mul, ← heq]
        exact mul_right_cancel₀ (pow_ne_zero _ ht0) h1
      have hord : orderOf t = 3 ^ (1 + 1) :=
        orderOf_eq_prime_pow (by rwa [pow_one]) (by norm_num [ht9])
      have hdvd := orderOf_dvd_of_pow_eq_one h6
      rw [hord] at hdvd
      norm_num at hdvd
      exact ⟨by omega, Nat.dvd_of_mod_eq_zero hj⟩
    ·
      have e02 := hentry 0 2
      rw [hj, uc22s217u38_y₂_entry.1, map_one, mul_one, hd0, Matrix.scalar_apply,
        Matrix.diagonal_apply_ne _ (show (0 : Fin 3) ≠ 2 by decide)] at e02
      exact absurd e02 (pow_ne_zero i ht0)
    ·
      have e02 := hentry 0 2
      rw [hj, uc22s217u38_y₂_entry.2, map_one, mul_one, hd0, Matrix.scalar_apply,
        Matrix.diagonal_apply_ne _ (show (0 : Fin 3) ≠ 2 by decide)] at e02
      exact absurd e02 (pow_ne_zero i ht0)

end Elements

variable {G : Type} [Group G] [Finite G]

theorem uc22s217u38_pRank_of_su38
    {M L : Subgroup G} (hL : L ∈ calC M)
    (hnN : ¬ M ≤ normalizer (L : Set G)) (hX : IsSU3 (Bar2 L) 3) : 4 ≤ Open.pRank 3 M := by
  obtain ⟨hq, hU3⟩ := hX
  obtain ⟨-, K, hKf, hKfin, hK, ⟨e₁⟩⟩ := CFSG.Blueprint.LieModel.statedClassicalModel hU3 (by decide)
  haveI : CharP K 2 := uc22pwlie_charP_two (n := 6) (hK.trans (by norm_num))
  obtain ⟨α, hα, hαc, -⟩ := uc22pwsu3_exists_cover (by norm_num) hK hq e₁
  obtain ⟨h, y, hhy, hh9, hy9, hZ⟩ := uc22s217u38_exists_hy hK
  exact uc22s217u38_pRank_of_cover hL hnN (uc22pwsu3_commutator_eq_top (by norm_num) hK) hα hαc
    hhy hh9 hy9 hZ

theorem uc22s217u38_three_mem_sig
    {D : Data G} (hSg : UC6S846.SigmaStd D) {L : Subgroup G}
    (hL : L ∈ calC D.M) (hnN : ¬ (L.subgroupOf D.M).Normal) (hX : IsSU3 (Bar2 L) 3) :
    3 ∈ D.sig ∧ CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M := by
  have hnN' : ¬ D.M ≤ normalizer (L : Set G) := fun h =>
    hnN ((Subgroup.normal_subgroupOf_iff_le_normalizer hL.1.le).2 h)
  have h3 : 3 ∈ D.sig :=
    hSg.four_mem 3 Nat.prime_three (by norm_num) (uc22s217u38_pRank_of_su38 hL hnN' hX)
  exact ⟨h3, UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hL) h3⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
