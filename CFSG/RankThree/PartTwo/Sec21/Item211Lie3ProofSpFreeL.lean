module

public import CFSG.RankThree.PartTwo.Sec21.Item211Lie3ProofSpFrameB
public import CFSG.RankThree.PartTwo.Sec21.Item211Lie3ProofSpPhi

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.LowTwoRank
open Matrix
open scoped MatrixGroups

namespace Item211Lie3Proof

open Item211Lie2Proof
open CFSG.RankThree.SubgroupLists (spForm spGram spForm_mulVec transpose_mul_spGram_mul)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (gsp conjAut conjSp coe_conjSp
  conjAut_proj)

local notation "V₄" => Fin 2 ⊕ Fin 2

variable {K : Type} [Field K]

theorem cube_eq_one_of_root {G : Matrix V₄ V₄ K} (hG : G * G + G + 1 = 0) : G * G * G = 1 := by
  have e : G * G * G - 1 = (G - 1) * (G * G + G + 1) := by noncomm_ring
  rw [hG, Matrix.mul_zero, sub_eq_zero] at e
  exact e

theorem spForm_skew_of_root {d₀ : GL V₄ K} (hd : d₀ ∈ StatedSp 2 K)
    (hG : (d₀ : Matrix V₄ V₄ K) * d₀ + d₀ + 1 = 0) (x y : V₄ → K) :
    spForm 2 K (((2 : K) • (d₀ : Matrix V₄ V₄ K) + 1) *ᵥ x) y =
      -spForm 2 K x (((2 : K) • (d₀ : Matrix V₄ V₄ K) + 1) *ᵥ y) := by
  set G : Matrix V₄ V₄ K := (d₀ : Matrix V₄ V₄ K) with hGdef
  have hG3 := cube_eq_one_of_root hG
  have hGG : G * G = -G - 1 := by
    rw [← sub_eq_zero, ← hG]
    abel
  have hGx : spForm 2 K (G *ᵥ x) y = -spForm 2 K x (G *ᵥ y) - spForm 2 K x y := by
    have e := spForm_mulVec hd x ((G * G) *ᵥ y)
    rw [← hGdef, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hG3, Matrix.one_mulVec, hGG,
      Matrix.sub_mulVec, Matrix.neg_mulVec, Matrix.one_mulVec, map_sub, map_neg] at e
    exact e
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, map_add, map_smul,
    LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hGx]
  ring

theorem mulVec_sq_of_root {G : Matrix V₄ V₄ K} (hG : G * G + G + 1 = 0) (x : V₄ → K) :
    ((2 : K) • G + 1) *ᵥ (((2 : K) • G + 1) *ᵥ x) = -(3 : K) • x := by
  rw [Matrix.mulVec_mulVec]
  have e : ((2 : K) • G + 1) * ((2 : K) • G + 1) = (4 : K) • (G * G + G + 1) - (3 : K) • 1 := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, smul_smul, smul_add]
    module
  rw [e, hG, smul_zero, zero_sub, Matrix.neg_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    neg_smul]

theorem frConj_commute_jStd {G : Matrix V₄ V₄ K} {h : GL V₄ K}
    (hj : ((2 : K) • G + 1) * (h : Matrix V₄ V₄ K) = (h : Matrix V₄ V₄ K) * jStd)
    {N : Matrix V₄ V₄ K} (hN : N * G = G * N) :
    frConj h N * jStd = jStd * frConj h N := by
  have hjf : frConj h ((2 : K) • G + 1) = jStd := by
    rw [frConj, Matrix.mul_assoc, hj, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.one_mul]
  have hNj : N * ((2 : K) • G + 1) = ((2 : K) • G + 1) * N := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, hN, Matrix.mul_one,
      Matrix.one_mul]
  rw [← hjf, ← frConj_mul, ← frConj_mul, hNj]

theorem xiMat_mem (h3 : (3 : K) ≠ 0) (g : SL(2, K)) :
    (xiMat (g : Matrix (Fin 2) (Fin 2) K) 0)ᵀ * spGram 2 K *
      xiMat (g : Matrix (Fin 2) (Fin 2) K) 0 = spGram 2 K := by
  have hstar := star_xiMat (g : Matrix (Fin 2) (Fin 2) K) 0
  rw [adjugate_zero, neg_zero] at hstar
  have e1 : -(spGram 2 K * (xiMat (g : Matrix (Fin 2) (Fin 2) K) 0)ᵀ * spGram 2 K) *
      xiMat (g : Matrix (Fin 2) (Fin 2) K) 0 = 1 := by
    rw [hstar, xiMat_mul_xiMat_zero h3, adjugate_mul, g.2, one_smul, xiMat_one]
  have e2 := congrArg (fun M => spGram 2 K * M) e1
  simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_one, ← Matrix.mul_assoc,
    spGram_mul_self, Matrix.neg_mul, Matrix.one_mul, neg_neg] at e2
  exact e2

@[expose] noncomputable def xiGL (h3 : (3 : K) ≠ 0) : SL(2, K) →* GL V₄ K where
  toFun g := ⟨xiMat (g : Matrix (Fin 2) (Fin 2) K) 0, xiMat ((g⁻¹ : SL(2, K)) :
      Matrix (Fin 2) (Fin 2) K) 0, by
    rw [xiMat_mul_xiMat_zero h3, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, xiMat_one], by
    rw [xiMat_mul_xiMat_zero h3, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, xiMat_one]⟩
  map_one' := by
    apply Units.ext
    change xiMat ((1 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 = 1
    rw [Matrix.SpecialLinearGroup.coe_one, xiMat_one]
  map_mul' g g' := by
    apply Units.ext
    change xiMat ((g * g' : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 =
      xiMat (g : Matrix (Fin 2) (Fin 2) K) 0 * xiMat (g' : Matrix (Fin 2) (Fin 2) K) 0
    rw [xiMat_mul_xiMat_zero h3, Matrix.SpecialLinearGroup.coe_mul]

theorem coe_xiGL (h3 : (3 : K) ≠ 0) (g : SL(2, K)) :
    ((xiGL h3 g : GL V₄ K) : Matrix V₄ V₄ K) = xiMat (g : Matrix (Fin 2) (Fin 2) K) 0 := rfl

@[expose] noncomputable def xiSL (h3 : (3 : K) ≠ 0) : SL(2, K) →* StatedSp 2 K :=
  (xiGL h3).codRestrict (StatedSp 2 K) fun g => by
    rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff, coe_xiGL]
    exact xiMat_mem h3 g

theorem coe_xiSL (h3 : (3 : K) ≠ 0) (g : SL(2, K)) :
    (((xiSL h3 g : StatedSp 2 K) : GL V₄ K) : Matrix V₄ V₄ K) =
      xiMat (g : Matrix (Fin 2) (Fin 2) K) 0 := rfl

@[expose] noncomputable def framePsi (h3 : (3 : K) ≠ 0) (hS : StatedSp 2 K) :
    SL(2, K) →* MulAut (StatedProj (StatedSp 2 K)) :=
  (MulAut.conj : StatedProj (StatedSp 2 K) →* MulAut (StatedProj (StatedSp 2 K))).comp
    ((QuotientGroup.mk' _).comp ((MulAut.conj hS).toMonoidHom.comp (xiSL h3)))

theorem framePsi_apply (h3 : (3 : K) ≠ 0) (hS : StatedSp 2 K) (g : SL(2, K)) :
    framePsi h3 hS g = MulAut.conj
      ((hS * xiSL h3 g * hS⁻¹ : StatedSp 2 K) : StatedProj (StatedSp 2 K)) :=
  rfl

theorem frConj_xiSL (h3 : (3 : K) ≠ 0) (hS : StatedSp 2 K) (g : SL(2, K)) :
    frConj (hS : GL V₄ K) ((((hS * xiSL h3 g * hS⁻¹ : StatedSp 2 K) : GL V₄ K)) :
      Matrix V₄ V₄ K) = xiMat (g : Matrix (Fin 2) (Fin 2) K) 0 := by
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_mul,
    coe_xiSL, frConj_conj]

theorem framePsi_eq_one (h3 : (3 : K) ≠ 0)
    (hinj : Function.Injective
      (MulAut.conj : StatedProj (StatedSp 2 K) →* MulAut (StatedProj (StatedSp 2 K))))
    (hS : StatedSp 2 K) {g : SL(2, K)} (h : framePsi h3 hS g = 1) : g = 1 ∨ g = -1 := by
  rw [framePsi_apply, ← map_one MulAut.conj] at h
  have h1 := hinj h
  have e := frConj_xiSL h3 hS g
  rcases mk_eq_one_iff_sp.mp h1 with h4 | h4
  · left
    rw [h4, Units.val_one, frConj_one, ← xiMat_one] at e
    exact Subtype.ext (xiMat_injective h3 e).1.symm
  · right
    rw [h4, Units.val_neg, Units.val_one, frConj_neg, frConj_one, ← xiMat_one, ← xiMat_neg,
      neg_zero] at e
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]
    exact (xiMat_injective h3 e).1.symm

theorem conjAut_commute_framePsi (h3 : (3 : K) ≠ 0) (hS : StatedSp 2 K) (A : gsp 2 K)
    {α β : K} (hA : frConj (hS : GL V₄ K) ((A : GL V₄ K) : Matrix V₄ V₄ K) = rSc α β)
    (g : SL(2, K)) :
    conjAut 2 K A * framePsi h3 hS g = framePsi h3 hS g * conjAut 2 K A := by
  set z : StatedSp 2 K := hS * xiSL h3 g * hS⁻¹ with hz
  have hAz : (A : GL V₄ K) * z = z * A := by
    apply Units.ext
    apply frConj_injective (hS : GL V₄ K)
    rw [Units.val_mul, Units.val_mul, frConj_mul, frConj_mul, hz, frConj_xiSL, hA]
    exact rSc_comm h3 α β _ 0
  have hfix : conjAut 2 K A (z : StatedProj (StatedSp 2 K)) = z := by
    have e : conjSp 2 K A z = z := by
      apply Subtype.ext
      rw [coe_conjSp, hAz, mul_inv_cancel_right]
    change conjAut 2 K A (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj 2 K z) =
      CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj 2 K z
    rw [conjAut_proj, e]
  calc conjAut 2 K A * framePsi h3 hS g =
      conjAut 2 K A * framePsi h3 hS g * (conjAut 2 K A)⁻¹ * conjAut 2 K A := by group
    _ = framePsi h3 hS g * conjAut 2 K A := by
      rw [framePsi_apply, ← hz, mul_conj_mul_inv, hfix]

end Item211Lie3Proof

end CFSG.RankThree.PartTwo.Sec21
