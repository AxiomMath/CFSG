module

public import CFSG.RankThree.PartTwo.Sec21.Item211Lie3ProofSpFrame
public import CFSG.RankThree.PartTwo.Sec21.Item211Lie3ProofSpMinus
public import CFSG.RankThree.PartTwo.Sec21.Item211Lie3ProofSL2
public import CFSG.RankThree.PartTwo.Sec21.Item211Lie3ProofCore

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.LowTwoRank
open Matrix
open scoped MatrixGroups

namespace Item211Lie3Proof

open Item211Lie2Proof
open CFSG.RankThree.SubgroupLists (plusBlock minusBlock tStdMat det_plusBlock plusBlock_mul
  plusBlock_one)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (pairMat lam coe_lam commute_lam_lam
  pairMat_one)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (gsp conjAut conjSp coe_conjSp
  conjAut_proj)

local notation "V₄" => Fin 2 ⊕ Fin 2

variable {K : Type} [Field K]

@[expose] noncomputable def pairSp : SL(2, K) × SL(2, K) →* StatedSp 2 K :=
  (lam (0 : Fin 2)).noncommCoprod (lam (1 : Fin 2)) fun a b => commute_lam_lam (by decide) a b

theorem coe_pairSp (a b : SL(2, K)) :
    (((pairSp (a, b) : StatedSp 2 K) : GL V₄ K) : Matrix V₄ V₄ K) =
      pairMat (Sum.inl 0 : V₄) (Sum.inr 0) (a : Matrix (Fin 2) (Fin 2) K) *
        pairMat (Sum.inl 1 : V₄) (Sum.inr 1) (b : Matrix (Fin 2) (Fin 2) K) := by
  rw [pairSp, MonoidHom.noncommCoprod_apply, Subgroup.coe_mul, Units.val_mul, coe_lam, coe_lam]

@[expose] noncomputable def framePhi (hS : StatedSp 2 K) :
    SL(2, K) × SL(2, K) →* MulAut (StatedProj (StatedSp 2 K)) :=
  (MulAut.conj : StatedProj (StatedSp 2 K) →* MulAut (StatedProj (StatedSp 2 K))).comp
    ((QuotientGroup.mk' _).comp ((MulAut.conj hS).toMonoidHom.comp pairSp))

theorem framePhi_apply (hS : StatedSp 2 K) (ab : SL(2, K) × SL(2, K)) :
    framePhi hS ab = MulAut.conj
      ((hS * pairSp ab * hS⁻¹ : StatedSp 2 K) : StatedProj (StatedSp 2 K)) :=
  rfl

theorem frConj_conj (h : GL V₄ K) (X : Matrix V₄ V₄ K) :
    frConj h ((h : Matrix V₄ V₄ K) * X * ((h⁻¹ : GL V₄ K) : Matrix V₄ V₄ K)) = X := by
  have e1 : ((h⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) * (h : Matrix V₄ V₄ K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  calc frConj h ((h : Matrix V₄ V₄ K) * X * ((h⁻¹ : GL V₄ K) : Matrix V₄ V₄ K)) =
      (((h⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) * (h : Matrix V₄ V₄ K)) * X *
        (((h⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) * (h : Matrix V₄ V₄ K)) := by
        simp only [frConj, Matrix.mul_assoc]
    _ = X := by rw [e1, Matrix.one_mul, Matrix.mul_one]

theorem coe_conj_eq_frConj (hS y : StatedSp 2 K) :
    (((hS⁻¹ * y * hS : StatedSp 2 K) : GL V₄ K) : Matrix V₄ V₄ K) =
      frConj (hS : GL V₄ K) ((y : GL V₄ K) : Matrix V₄ V₄ K) := by
  rw [frConj, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_mul]

theorem exists_framePhi_eq (h2 : (2 : K) ≠ 0) (hS y : StatedSp 2 K)
    (hy : frConj (hS : GL V₄ K) ((y : GL V₄ K) : Matrix V₄ V₄ K) * tStdMat =
      tStdMat * frConj (hS : GL V₄ K) ((y : GL V₄ K) : Matrix V₄ V₄ K)) :
    ∃ a b : SL(2, K),
      (a : Matrix (Fin 2) (Fin 2) K) = plusBlock (frConj (hS : GL V₄ K) (y : GL V₄ K)) ∧
      (b : Matrix (Fin 2) (Fin 2) K) = minusBlock (frConj (hS : GL V₄ K) (y : GL V₄ K)) ∧
      MulAut.conj (y : StatedProj (StatedSp 2 K)) = framePhi hS (a, b) := by
  set y' : StatedSp 2 K := hS⁻¹ * y * hS with hy'
  have hcoe := coe_conj_eq_frConj hS y
  rw [← hy'] at hcoe
  rw [← hcoe] at hy ⊢
  let a : SL(2, K) := ⟨plusBlock ((y' : GL V₄ K) : Matrix V₄ V₄ K), det_plusBlock h2 y'.2 hy⟩
  let b : SL(2, K) := ⟨minusBlock ((y' : GL V₄ K) : Matrix V₄ V₄ K), det_minusBlock h2 y'.2 hy⟩
  refine ⟨a, b, rfl, rfl, ?_⟩
  rw [framePhi_apply]
  have e : pairSp (a, b) = y' :=
    Subtype.ext (Units.ext (by rw [coe_pairSp]; exact (eq_pairMat_mul_pairMat h2 hy).symm))
  rw [e, hy']
  congr 2
  group

theorem framePhi_eq_one
    (hinj : Function.Injective
      (MulAut.conj : StatedProj (StatedSp 2 K) →* MulAut (StatedProj (StatedSp 2 K))))
    (hS : StatedSp 2 K) {a b : SL(2, K)} (h : framePhi hS (a, b) = 1) : a = 1 ∨ a = -1 := by
  rw [framePhi_apply, ← map_one MulAut.conj] at h
  have h1 := hinj h
  have e : ((pairSp (a, b) : StatedSp 2 K) : GL V₄ K) =
      (hS : GL V₄ K)⁻¹ * ((hS * pairSp (a, b) * hS⁻¹ : StatedSp 2 K) : GL V₄ K) * hS := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hp : ∀ c : GL V₄ K, ((pairSp (a, b) : StatedSp 2 K) : GL V₄ K) = c →
      (a : Matrix (Fin 2) (Fin 2) K) = plusBlock (c : Matrix V₄ V₄ K) := by
    intro c hc
    have e2 := congrArg (fun g : GL V₄ K => plusBlock (g : Matrix V₄ V₄ K)) hc
    simp only [coe_pairSp, plusBlock_pairMat_mul_pairMat] at e2
    exact e2
  rcases mk_eq_one_iff_sp.mp h1 with h3 | h3
  · left
    have h4 := hp 1 (by rw [e, h3, mul_one, inv_mul_cancel])
    rw [Units.val_one, plusBlock_one] at h4
    exact Subtype.ext h4
  · right
    have h4 := hp (-1) (by rw [e, h3, mul_neg_one, neg_mul, inv_mul_cancel])
    rw [Units.val_neg, Units.val_one, plusBlock_neg, plusBlock_one] at h4
    exact Subtype.ext (by rw [h4, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one])

theorem mul_conj_mul_inv {X : Type*} [Group X] (α : MulAut X) (y : X) :
    α * MulAut.conj y * α⁻¹ = MulAut.conj (α y) := by
  ext x
  simp [MulAut.conj_apply]

theorem conjAut_commute_framePhi (h2 : (2 : K) ≠ 0) (hS : StatedSp 2 K) (A : gsp 2 K)
    (hA : frConj (hS : GL V₄ K) ((A : GL V₄ K) : Matrix V₄ V₄ K) * tStdMat =
      tStdMat * frConj (hS : GL V₄ K) ((A : GL V₄ K) : Matrix V₄ V₄ K)) {c : K}
    (hA1 : plusBlock (frConj (hS : GL V₄ K) ((A : GL V₄ K) : Matrix V₄ V₄ K)) = c • 1)
    (a : SL(2, K)) :
    conjAut 2 K A * framePhi hS (a, 1) = framePhi hS (a, 1) * conjAut 2 K A := by
  set z : StatedSp 2 K := hS * pairSp (a, 1) * hS⁻¹ with hz
  set P : Matrix V₄ V₄ K := pairMat (Sum.inl 0 : V₄) (Sum.inr 0) (a : Matrix (Fin 2) (Fin 2) K) *
    pairMat (Sum.inl 1 : V₄) (Sum.inr 1) ((1 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) with hP
  have hzP : frConj (hS : GL V₄ K) ((z : GL V₄ K) : Matrix V₄ V₄ K) = P := by
    rw [hz, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_mul,
      coe_pairSp, frConj_conj]
  have hPt : P * tStdMat = tStdMat * P := pairMat_mul_pairMat_commute _ _
  have hAz : (A : GL V₄ K) * z = z * A := by
    apply Units.ext
    apply frConj_injective (hS : GL V₄ K)
    rw [Units.val_mul, Units.val_mul, frConj_mul, frConj_mul, hzP]
    have hAP : frConj (hS : GL V₄ K) ((A : GL V₄ K) : Matrix V₄ V₄ K) * P * tStdMat =
        tStdMat * (frConj (hS : GL V₄ K) ((A : GL V₄ K) : Matrix V₄ V₄ K) * P) := by
      rw [Matrix.mul_assoc, hPt, ← Matrix.mul_assoc, hA, Matrix.mul_assoc]
    have hPA : P * frConj (hS : GL V₄ K) ((A : GL V₄ K) : Matrix V₄ V₄ K) * tStdMat =
        tStdMat * (P * frConj (hS : GL V₄ K) ((A : GL V₄ K) : Matrix V₄ V₄ K)) := by
      rw [Matrix.mul_assoc, hA, ← Matrix.mul_assoc, hPt, Matrix.mul_assoc]
    refine eq_of_plusBlock_minusBlock h2 hAP hPA ?_ ?_
    · rw [plusBlock_mul h2 hA hPt, plusBlock_mul h2 hPt hA, hA1, hP,
        plusBlock_pairMat_mul_pairMat, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
        Matrix.mul_one]
    · rw [minusBlock_mul h2 hA, minusBlock_mul h2 hPt, hP, minusBlock_pairMat_mul_pairMat,
        Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one, Matrix.one_mul]
  have hfix : conjAut 2 K A (z : StatedProj (StatedSp 2 K)) = z := by
    have e : conjSp 2 K A z = z := by
      apply Subtype.ext
      rw [coe_conjSp, hAz, mul_inv_cancel_right]
    change conjAut 2 K A (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj 2 K z) =
      CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj 2 K z
    rw [conjAut_proj, e]
  calc conjAut 2 K A * framePhi hS (a, 1) =
      conjAut 2 K A * framePhi hS (a, 1) * (conjAut 2 K A)⁻¹ * conjAut 2 K A := by group
    _ = framePhi hS (a, 1) * conjAut 2 K A := by
      rw [framePhi_apply, ← hz, mul_conj_mul_inv, hfix]

theorem exists_lift_commute (h2 : (2 : K) ≠ 0)
    (hinj : Function.Injective
      (MulAut.conj : StatedProj (StatedSp 2 K) →* MulAut (StatedProj (StatedSp 2 K))))
    {d₀ : StatedSp 2 K} (hd3 : (d₀ : GL V₄ K) ^ 3 = 1) {w : MulAut (StatedProj (StatedSp 2 K))}
    (hw : w ∈ (MulAut.conj : StatedProj (StatedSp 2 K) →* MulAut _).range ⊓
      Subgroup.centralizer {MulAut.conj (d₀ : StatedProj (StatedSp 2 K))}) :
    ∃ w₀ : StatedSp 2 K, MulAut.conj (w₀ : StatedProj (StatedSp 2 K)) = w ∧
      (d₀ : GL V₄ K) * w₀ = w₀ * d₀ := by
  obtain ⟨⟨y, rfl⟩, hy⟩ := Subgroup.mem_inf.mp hw
  obtain ⟨w₀, rfl⟩ := QuotientGroup.mk_surjective y
  refine ⟨w₀, rfl, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff] at hy
  have hc : (d₀ : StatedProj (StatedSp 2 K)) * w₀ = w₀ * d₀ := hinj (by
    rw [map_mul, map_mul]
    exact hy.symm)
  exact commute_of_pow_three_of_signs (ne_neg_gl h2 _) hd3 (comm_or_anticomm_of_mk hc)

theorem conjAut_sign (A : gsp 2 K) (y : StatedSp 2 K)
    (h : conjAut 2 K A (y : StatedProj (StatedSp 2 K)) = y) :
    (A : GL V₄ K) * y = y * A ∨ (A : GL V₄ K) * y = -(y * A) := by
  have h' : ((conjSp 2 K A y : StatedSp 2 K) : StatedProj (StatedSp 2 K)) = y := h
  rcases mk_eq_mk_iff_sp.mp h' with h1 | h1
  · left
    rw [coe_conjSp] at h1
    calc (A : GL V₄ K) * y = (A : GL V₄ K) * y * (A : GL V₄ K)⁻¹ * A := by group
      _ = y * A := by rw [← h1]
  · right
    rw [coe_conjSp] at h1
    have h2 := congrArg Neg.neg h1
    rw [neg_neg] at h2
    calc (A : GL V₄ K) * y = (A : GL V₄ K) * y * (A : GL V₄ K)⁻¹ * A := by group
      _ = -(y : GL V₄ K) * A := by rw [← h2]
      _ = -(y * A) := neg_mul _ _

theorem fix_of_commute_conj {X : Type*} [Group X]
    (hinj : Function.Injective (MulAut.conj : X →* MulAut X)) {α : MulAut X} {y : X}
    (h : α * MulAut.conj y = MulAut.conj y * α) : α y = y := by
  apply hinj
  rw [← mul_conj_mul_inv, h, mul_inv_cancel_right]

theorem commute_of_sign (h2 : (2 : K) ≠ 0) (h : GL V₄ K) {m : Matrix (Fin 2) (Fin 2) K}
    (hm : ¬ IsScalar2 m) {N₁ N₂ : GL V₄ K}
    (h₁ : frConj h (N₁ : Matrix V₄ V₄ K) * tStdMat = tStdMat * frConj h (N₁ : Matrix V₄ V₄ K))
    (h₁m : minusBlock (frConj h (N₁ : Matrix V₄ V₄ K)) * m =
      m * minusBlock (frConj h (N₁ : Matrix V₄ V₄ K)))
    (h₂ : frConj h (N₂ : Matrix V₄ V₄ K) * tStdMat = tStdMat * frConj h (N₂ : Matrix V₄ V₄ K))
    (h₂m : minusBlock (frConj h (N₂ : Matrix V₄ V₄ K)) * m =
      m * minusBlock (frConj h (N₂ : Matrix V₄ V₄ K)))
    (h₂d : (minusBlock (frConj h (N₂ : Matrix V₄ V₄ K))).det = 1)
    (hs : N₁ * N₂ = N₂ * N₁ ∨ N₁ * N₂ = -(N₂ * N₁)) : N₁ * N₂ = N₂ * N₁ := by
  rcases hs with hs | hs
  · exact hs
  exfalso
  have hinv : minusBlock (frConj h (N₁ : Matrix V₄ V₄ K)) *
      minusBlock (frConj h ((N₁⁻¹ : GL V₄ K) : Matrix V₄ V₄ K)) = 1 := by
    rw [← minusBlock_mul h2 h₁, ← frConj_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      frConj_one, minusBlock_one]
  have hdet1 : (minusBlock (frConj h (N₁ : Matrix V₄ V₄ K))).det ≠ 0 := by
    intro h0
    have e := congrArg Matrix.det hinv
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at e
    exact zero_ne_one e
  have hc := commute_of_commute_nonscalar hm h₁m.symm h₂m.symm
  have e := congrArg (fun g : GL V₄ K => minusBlock (frConj h (g : Matrix V₄ V₄ K))) hs
  simp only [Units.val_mul, Units.val_neg, frConj_mul, frConj_neg, minusBlock_neg] at e
  rw [minusBlock_mul h2 h₁, minusBlock_mul h2 h₂, hc] at e
  have e0 : minusBlock (frConj h (N₂ : Matrix V₄ V₄ K)) *
      minusBlock (frConj h (N₁ : Matrix V₄ V₄ K)) = 0 := by
    have e1 : (2 : K) • (minusBlock (frConj h (N₂ : Matrix V₄ V₄ K)) *
        minusBlock (frConj h (N₁ : Matrix V₄ V₄ K))) = 0 := by
      rw [two_smul]
      nth_rewrite 1 [e]
      rw [neg_add_cancel]
    exact (smul_eq_zero.mp e1).resolve_left h2
  have e2 := congrArg Matrix.det e0
  rw [Matrix.det_mul, h₂d, one_mul, Matrix.det_zero] at e2
  exact hdet1 e2

end Item211Lie3Proof

end CFSG.RankThree.PartTwo.Sec21
