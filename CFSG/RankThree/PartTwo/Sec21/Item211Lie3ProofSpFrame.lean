module

public import CFSG.RankThree.PartTwo.Sec21.Item211Lie3ProofSpBlocks
import Mathlib.Tactic.NoncommRing

public section

namespace CFSG.RankThree.PartTwo.Sec21

namespace Item211Lie3Proof

open Matrix CFSG.Assembly.LowTwoRank
open CFSG.RankThree.SubgroupLists (plusBlock minusBlock tStdMat tStd IsNCInv exists_conj_eq_tStd
  plusBlock_mul plusBlock_one coe_tStd spGram transpose_mul_spGram_mul)

local notation "V₄" => Fin 2 ⊕ Fin 2

variable {K : Type} [Field K]

theorem eq_of_add_self_eq_add_self {M : Type*} [AddCommGroup M] [Module K M] (h2 : (2 : K) ≠ 0)
    {x y : M} (h : x + x = y + y) : x = y := by
  have h' : (2 : K) • x = (2 : K) • y := by rw [two_smul, two_smul, h]
  exact smul_right_injective M h2 h'

theorem transpose_poly_mul_spGram {G : Matrix V₄ V₄ K}
    (hJ : Gᵀ * spGram 2 K * G = spGram 2 K) (hG3 : G * G * G = 1) :
    (G * G + G + 1)ᵀ * spGram 2 K = spGram 2 K * (G * G + G + 1) := by
  set J := spGram 2 K
  have h1 : Gᵀ * J = J * (G * G) := by
    calc Gᵀ * J = Gᵀ * J * (G * G * G) := by rw [hG3, Matrix.mul_one]
      _ = (Gᵀ * J * G) * (G * G) := by simp only [Matrix.mul_assoc]
      _ = J * (G * G) := by rw [hJ]
  have h2 : (G * G)ᵀ * J = J * G := by
    calc (G * G)ᵀ * J = Gᵀ * (Gᵀ * J) := by rw [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = Gᵀ * (J * (G * G)) := by rw [h1]
      _ = Gᵀ * J * (G * G) := by rw [Matrix.mul_assoc]
      _ = J * (G * G) * (G * G) := by rw [h1]
      _ = J * (G * G * G) * G := by simp only [Matrix.mul_assoc]
      _ = J * G := by rw [hG3, Matrix.mul_one]
  rw [Matrix.transpose_add, Matrix.transpose_add, Matrix.transpose_one, Matrix.add_mul,
    Matrix.add_mul, h2, h1, Matrix.one_mul, Matrix.mul_add, Matrix.mul_add, Matrix.mul_one]
  abel

@[expose] noncomputable def frameMat (G : Matrix V₄ V₄ K) : Matrix V₄ V₄ K :=
  (2 * 3⁻¹ : K) • (G * G + G + 1) - 1

theorem frameMat_mul_self (h3 : (3 : K) ≠ 0) {G : Matrix V₄ V₄ K} (hG3 : G * G * G = 1) :
    frameMat G * frameMat G = 1 := by
  set P : Matrix V₄ V₄ K := G * G + G + 1 with hPdef
  set c : K := 2 * 3⁻¹ with hc
  have hPP : P * P = P + P + P := by
    have e : P * P - (P + P + P) = (G * G * G - 1) * (G + 1 + 1) := by
      rw [hPdef]
      noncomm_ring
    rw [hG3, sub_self, Matrix.zero_mul, sub_eq_zero] at e
    exact e
  have hc3 : c * 3 = 2 := by rw [hc, mul_assoc, inv_mul_cancel₀ h3, mul_one]
  have e1 : frameMat G * frameMat G = (c * c) • (P * P) - (c + c) • P + 1 := by
    rw [frameMat, ← hc, ← hPdef]
    simp only [sub_mul, mul_sub, smul_mul_smul_comm, Matrix.one_mul, Matrix.mul_one, add_smul]
    abel
  have e2 : (c * c) • (P + P + P) - (c + c) • P = (c * (c * 3 - 2)) • P := by
    rw [show c * (c * 3 - 2) = c * c + c * c + c * c - (c + c) by ring]
    simp only [sub_smul, add_smul, smul_add]
  rw [e1, hPP, e2, hc3, sub_self, mul_zero, zero_smul, zero_add]

theorem frameMat_mem (h3 : (3 : K) ≠ 0) {G : Matrix V₄ V₄ K}
    (hJ : Gᵀ * spGram 2 K * G = spGram 2 K) (hG3 : G * G * G = 1) :
    (frameMat G)ᵀ * spGram 2 K * frameMat G = spGram 2 K := by
  have hPJ := transpose_poly_mul_spGram hJ hG3
  have hSJ : (frameMat G)ᵀ * spGram 2 K = spGram 2 K * frameMat G := by
    rw [frameMat, Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one, Matrix.sub_mul,
      Matrix.smul_mul, hPJ, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one]
  rw [hSJ, Matrix.mul_assoc, frameMat_mul_self h3 hG3, Matrix.mul_one]

theorem commute_frameMat {G N : Matrix V₄ V₄ K} (hN : N * G = G * N) :
    N * frameMat G = frameMat G * N := by
  have hGG : N * (G * G) = G * G * N := by
    rw [← Matrix.mul_assoc, hN, Matrix.mul_assoc, hN, Matrix.mul_assoc]
  rw [frameMat, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add,
    Matrix.mul_add, Matrix.add_mul, Matrix.add_mul, hGG, hN, Matrix.mul_one, Matrix.one_mul]

theorem isNCInv_frameInv (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) {g : GL V₄ K}
    (hg : g ∈ StatedSp 2 K) (hg3 : (g : Matrix V₄ V₄ K) * g * g = 1) (hg1 : g ≠ 1)
    (hP : (g : Matrix V₄ V₄ K) * g + g + 1 ≠ 0) :
    ∃ s : GL V₄ K, (s : Matrix V₄ V₄ K) = frameMat (g : Matrix V₄ V₄ K) ∧ IsNCInv s := by
  set G : Matrix V₄ V₄ K := (g : Matrix V₄ V₄ K) with hGdef
  have hSS := frameMat_mul_self h3 hg3
  let s : GL V₄ K := ⟨frameMat G, frameMat G, hSS, hSS⟩
  have hc0 : (2 * 3⁻¹ : K) ≠ 0 := mul_ne_zero h2 (inv_ne_zero h3)
  have hGP : G * (G * G + G + 1) = G * G + G + 1 := by
    have e : G * (G * G + G + 1) - (G * G + G + 1) = G * G * G - 1 := by noncomm_ring
    rw [hg3, sub_self, sub_eq_zero] at e
    exact e
  refine ⟨s, rfl, ?_, Units.ext hSS, fun h => ?_, fun h => ?_⟩
  · rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff]
    exact frameMat_mem h3 (transpose_mul_spGram_mul hg) hg3
  ·
    have hS : frameMat G = 1 := congrArg Units.val h
    rw [frameMat, sub_eq_iff_eq_add] at hS
    have e : G * ((2 * 3⁻¹ : K) • (G * G + G + 1)) = (2 * 3⁻¹ : K) • (G * G + G + 1) := by
      rw [Matrix.mul_smul, hGP]
    rw [hS, Matrix.mul_add, Matrix.mul_one] at e
    apply hg1
    exact Units.ext (eq_of_add_self_eq_add_self h2 e)
  ·
    have hS : frameMat G = -1 := by
      have e := congrArg Units.val h
      rw [Units.val_neg, Units.val_one] at e
      exact e
    rw [frameMat, sub_eq_iff_eq_add, neg_add_cancel] at hS
    exact hP ((smul_eq_zero.mp hS).resolve_left hc0)

@[expose] def frConj (h : GL V₄ K) (N : Matrix V₄ V₄ K) : Matrix V₄ V₄ K :=
  ((h⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) * N * (h : Matrix V₄ V₄ K)

theorem frConj_mul (h : GL V₄ K) (M N : Matrix V₄ V₄ K) :
    frConj h (M * N) = frConj h M * frConj h N := by
  have e : (h : Matrix V₄ V₄ K) * ((h⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  calc frConj h (M * N) = ((h⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) * M *
        ((h : Matrix V₄ V₄ K) * ((h⁻¹ : GL V₄ K) : Matrix V₄ V₄ K)) * N * (h : Matrix V₄ V₄ K) := by
        rw [e, Matrix.mul_one, frConj, Matrix.mul_assoc _ M N]
    _ = frConj h M * frConj h N := by simp only [frConj, Matrix.mul_assoc]

theorem frConj_one (h : GL V₄ K) : frConj h 1 = 1 := by
  rw [frConj, Matrix.mul_one, ← Units.val_mul, inv_mul_cancel, Units.val_one]

theorem frConj_neg (h : GL V₄ K) (N : Matrix V₄ V₄ K) : frConj h (-N) = -frConj h N := by
  rw [frConj, frConj, Matrix.mul_neg, Matrix.neg_mul]

theorem frConj_injective (h : GL V₄ K) : Function.Injective (frConj h) := by
  intro M N hMN
  have e : ∀ X : Matrix V₄ V₄ K, (h : Matrix V₄ V₄ K) * frConj h X *
      ((h⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) = X := by
    intro X
    have e1 : (h : Matrix V₄ V₄ K) * ((h⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc (h : Matrix V₄ V₄ K) * frConj h X * ((h⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) =
        ((h : Matrix V₄ V₄ K) * ((h⁻¹ : GL V₄ K) : Matrix V₄ V₄ K)) * X *
          ((h : Matrix V₄ V₄ K) * ((h⁻¹ : GL V₄ K) : Matrix V₄ V₄ K)) := by
          simp only [frConj, Matrix.mul_assoc]
      _ = X := by rw [e1, Matrix.one_mul, Matrix.mul_one]
  rw [← e M, hMN, e N]

theorem exists_frame (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) {g : GL V₄ K}
    (hg : g ∈ StatedSp 2 K) (hg3 : (g : Matrix V₄ V₄ K) * g * g = 1) (hg1 : g ≠ 1)
    (hP : (g : Matrix V₄ V₄ K) * g + g + 1 ≠ 0) :
    ∃ h ∈ StatedSp 2 K,
      (∀ N : Matrix V₄ V₄ K, N * (g : Matrix V₄ V₄ K) = (g : Matrix V₄ V₄ K) * N →
        frConj h N * tStdMat = tStdMat * frConj h N) ∧
      plusBlock (frConj h g) = 1 ∧
      minusBlock (frConj h g) * minusBlock (frConj h g) + minusBlock (frConj h g) + 1 = 0 := by
  set G : Matrix V₄ V₄ K := (g : Matrix V₄ V₄ K) with hGdef
  obtain ⟨s, hs, hsNC⟩ := isNCInv_frameInv h2 h3 hg hg3 hg1 hP
  obtain ⟨h, hh, hconj⟩ := exists_conj_eq_tStd h2 hsNC
  set H : Matrix V₄ V₄ K := (h : Matrix V₄ V₄ K) with hHdef
  set Hi : Matrix V₄ V₄ K := ((h⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) with hHidef
  have hHHi : H * Hi = 1 := by rw [hHdef, hHidef, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hHiH : Hi * H = 1 := by rw [hHdef, hHidef, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hc : ∀ X : Matrix V₄ V₄ K, H * (Hi * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hHHi, Matrix.one_mul]
  have hT : tStdMat = Hi * frameMat G * H := by
    have e := congrArg Units.val hconj
    rw [Units.val_mul, Units.val_mul, coe_tStd, hs] at e
    rw [← e]
    calc tStdMat = (Hi * H) * tStdMat * (Hi * H) := by
          rw [hHiH, Matrix.one_mul, Matrix.mul_one]
      _ = Hi * (H * tStdMat * Hi) * H := by simp only [Matrix.mul_assoc]
  have hfr : ∀ N : Matrix V₄ V₄ K, N * G = G * N →
      Hi * N * H * tStdMat = tStdMat * (Hi * N * H) := by
    intro N hN
    have hNS := commute_frameMat hN
    rw [hT]
    simp only [Matrix.mul_assoc, hc]
    rw [← Matrix.mul_assoc N, hNS, Matrix.mul_assoc]
  refine ⟨h, hh, hfr, ?_⟩
  rw [show frConj h (g : Matrix V₄ V₄ K) = Hi * G * H from rfl]
  set g' := Hi * G * H with hg'
  have hg't : g' * tStdMat = tStdMat * g' := hfr G rfl
  have hg'2 : (g' * g') * tStdMat = tStdMat * (g' * g') := by
    rw [Matrix.mul_assoc, hg't, ← Matrix.mul_assoc, hg't, Matrix.mul_assoc]
  have hTg : tStdMat = (2 * 3⁻¹ : K) • (g' * g' + g' + 1) - 1 := by
    have e : g' * g' + g' + 1 = Hi * (G * G + G + 1) * H := by
      rw [hg']
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, hc, Matrix.mul_one, hHiH]
    rw [hT, e, frameMat, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, hHiH]
  have hg'3 : g' * g' * g' = 1 := by
    calc g' * g' * g' = Hi * G * (H * Hi) * G * (H * Hi) * G * H := by
          simp only [hg', Matrix.mul_assoc]
      _ = Hi * (G * G * G) * H := by
          rw [hHHi, Matrix.mul_one, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg3, Matrix.mul_one, hHiH]
  have hc0 : (2 * 3⁻¹ : K) ≠ 0 := mul_ne_zero h2 (inv_ne_zero h3)
  constructor
  ·
    set B := plusBlock g' with hB
    have hBt : (2 * 3⁻¹ : K) • (B * B + B + 1) - 1 = 1 := by
      have e := congrArg plusBlock hTg
      rw [CFSG.RankThree.PartTwo.Sec21.Item211Lie3Proof.plusBlock_tStdMat, plusBlock_sub,
        plusBlock_smul, plusBlock_add, plusBlock_add, plusBlock_mul h2 hg't hg't, plusBlock_one]
        at e
      exact e.symm
    have hB3 : B * B * B = 1 := by
      have e := congrArg plusBlock hg'3
      rwa [plusBlock_mul h2 hg'2 hg't, plusBlock_mul h2 hg't hg't, plusBlock_one] at e
    rw [sub_eq_iff_eq_add] at hBt
    have hBX : B * (B * B + B + 1) = B * B + B + 1 := by
      have e : B * (B * B + B + 1) - (B * B + B + 1) = B * B * B - 1 := by noncomm_ring
      rw [hB3, sub_self, sub_eq_zero] at e
      exact e
    have e : B * ((2 * 3⁻¹ : K) • (B * B + B + 1)) = (2 * 3⁻¹ : K) • (B * B + B + 1) := by
      rw [Matrix.mul_smul, hBX]
    rw [hBt, Matrix.mul_add, Matrix.mul_one] at e
    exact eq_of_add_self_eq_add_self h2 e
  ·
    have e := congrArg minusBlock hTg
    rw [minusBlock_tStdMat, minusBlock_sub, minusBlock_smul, minusBlock_add, minusBlock_add,
      minusBlock_mul h2 hg't, minusBlock_one, eq_sub_iff_add_eq, neg_add_cancel] at e
    exact (smul_eq_zero.mp e.symm).resolve_left hc0

end Item211Lie3Proof

end CFSG.RankThree.PartTwo.Sec21
