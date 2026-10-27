module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGDefs
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SpinPlusModel
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofKleinSix
public import CFSG.LieType.Universal.Spin.Generation.Eichler
public import CFSG.LieType.Universal.Spin.Chevalley.Plus
public import CFSG.LieType.Universal.SpecialLinearRoots
public import CFSG.ClassicalInvolution.ModelFacts.Families
public import CFSG.ClassicalGroups.Orthogonal.OmegaSiegelRoot
public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionExceptional
public import CFSG.LieType.Universal.Spin

public section

namespace CFSG.StandardType.RCKRP

open Matrix QuadraticMap
open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.RootSystem CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos
  CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag StatedLieAdmissible)
open CFSG.ComponentClassification.CatLeafProof.KleinSix
open CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalGroups.Orthogonal.OmegaSiegel

variable {F : Type} [Field F] [Finite F] [CharP F 2]

private def irgK1_gammaOf (a b : Fin 4) : Fin 3 → ℤ :=
  fun k => (if (a : ℕ) ≤ (k : ℕ) then 1 else 0) - (if (b : ℕ) ≤ (k : ℕ) then 1 else 0)

private theorem irgK1_gammaOf_toStd (a b : Fin 4) :
    SpecialLinear.toStd 3 (irgK1_gammaOf a b) = Pi.single a 1 - Pi.single b 1 := by
  funext c
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [irgK1_gammaOf, SpecialLinear.toStd]

private theorem irgK1_rhoGL_spinPlusThreeEquiv (x : spinGroup (quadPlus 3 F)) :
    rhoGL (CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.spinPlusThreeEquiv x) =
      spinAction (quadPlus 3 F) x := by
  rw [CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.spinPlusThreeEquiv]
  simp only [MulEquiv.trans_apply]
  rw [MonoidHom.apply_ofInjective_symm]
  simp [MulEquiv.subgroupCongr_apply, MonoidHom.ofInjective_apply]

private theorem irgK1_eichler_swap {a b : Fin 3 ⊕ Fin 3 → F} (ha : quadPlus 3 F a = 0)
    (hb : quadPlus 3 F b = 0) (hab : polar (quadPlus 3 F) a b = 0) (c : F) :
    eichler (quadPlus 3 F) a (c • b) = eichler (quadPlus 3 F) b (c • a) := by
  rw [eichler_comm_of_singular (a := a) (b := c • b) ha
      (by simp [hb, QuadraticMap.map_smul]) (by rw [polar_smul_right, hab, smul_zero]),
    eichler_smul_left]

private theorem irgK1_transv_congr {a b : Fin 4} (hab hab' : a ≠ b) (c : F) :
    transv a b hab c = transv a b hab' c := by
  apply Subtype.ext
  rfl

private def irgK1_ab : Fin 3 → Fin 3 → Bool → Bool → Fin 4 × Fin 4
  | 0, 1, true,  true  => (0, 3)
  | 0, 1, true,  false => (1, 2)
  | 0, 1, false, true  => (2, 1)
  | 0, 1, false, false => (3, 0)
  | 0, 2, true,  true  => (0, 2)
  | 0, 2, true,  false => (1, 3)
  | 0, 2, false, true  => (3, 1)
  | 0, 2, false, false => (2, 0)
  | 1, 2, true,  true  => (0, 1)
  | 1, 2, true,  false => (2, 3)
  | 1, 2, false, true  => (3, 2)
  | 1, 2, false, false => (1, 0)
  | 1, 0, true,  true  => (0, 3)
  | 1, 0, true,  false => (2, 1)
  | 1, 0, false, true  => (1, 2)
  | 1, 0, false, false => (3, 0)
  | 2, 0, true,  true  => (0, 2)
  | 2, 0, true,  false => (3, 1)
  | 2, 0, false, true  => (1, 3)
  | 2, 0, false, false => (2, 0)
  | 2, 1, true,  true  => (0, 1)
  | 2, 1, true,  false => (3, 2)
  | 2, 1, false, true  => (2, 3)
  | 2, 1, false, false => (1, 0)
  | _, _, _, _ => (0, 0)

private theorem irgK1_ab_ne (i j : Fin 3) (s t : Bool) (hij : i ≠ j) :
    (irgK1_ab i j s t).1 ≠ (irgK1_ab i j s t).2 := by
  revert hij
  fin_cases i <;> fin_cases j <;> cases s <;> cases t <;>
    simp [irgK1_ab]

private theorem irgK1_ab_swap (i j : Fin 3) (s t : Bool) :
    irgK1_ab i j s t = irgK1_ab j i t s := by
  fin_cases i <;> fin_cases j <;> cases s <;> cases t <;>
    simp [irgK1_ab]

private theorem irgK1_ab_neg (i j : Fin 3) (s t : Bool) :
    irgK1_ab i j (!s) (!t) = ((irgK1_ab i j s t).2, (irgK1_ab i j s t).1) := by
  fin_cases i <;> fin_cases j <;> cases s <;> cases t <;>
    simp [irgK1_ab]

private theorem irgK1_gen_01tt {hn : 3 ≤ 3} (hij : (0 : Fin 3) ≠ 1)
    (hab : (0 : Fin 4) ≠ 3) (c : F) :
    CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.spinPlusThreeEquiv
        ((plusFrame 3 F hn).longRoot hij true true (.ofAdd c)) =
      transv (0 : Fin 4) (3 : Fin 4) hab c := by
  rw [irgK1_transv_congr hab (by decide)]
  apply CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.rhoGL_injective'
  rw [irgK1_rhoGL_spinPlusThreeEquiv, HypFrame.spinAction_longRoot_eq_eichler, plusFrame_vec]
  rw [rho_transv_03]

private theorem irgK1_gen_01tf {hn : 3 ≤ 3} (hij : (0 : Fin 3) ≠ 1)
    (hab : (1 : Fin 4) ≠ 2) (c : F) :
    CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.spinPlusThreeEquiv
        ((plusFrame 3 F hn).longRoot hij true false (.ofAdd c)) =
      transv (1 : Fin 4) (2 : Fin 4) hab c := by
  rw [irgK1_transv_congr hab (by decide)]
  apply CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.rhoGL_injective'
  rw [irgK1_rhoGL_spinPlusThreeEquiv, HypFrame.spinAction_longRoot_eq_eichler, plusFrame_vec]
  rw [rho_transv_12]

private theorem irgK1_gen_01ft {hn : 3 ≤ 3} (hij : (0 : Fin 3) ≠ 1)
    (hab : (2 : Fin 4) ≠ 1) (c : F) :
    CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.spinPlusThreeEquiv
        ((plusFrame 3 F hn).longRoot hij false true (.ofAdd c)) =
      transv (2 : Fin 4) (1 : Fin 4) hab c := by
  rw [irgK1_transv_congr hab (by decide)]
  apply CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.rhoGL_injective'
  rw [irgK1_rhoGL_spinPlusThreeEquiv, HypFrame.spinAction_longRoot_eq_eichler, plusFrame_vec]
  rw [irgK1_eichler_swap (by simp [quadPlus_single_inl, quadPlus_single_inr])
    (by simp [quadPlus_single_inl, quadPlus_single_inr])
    (by simp [polar_quadPlus_single_inl, polar_quadPlus_single_inr, polar_smul_right])]
  rw [rho_transv_21]

private theorem irgK1_gen_01ff {hn : 3 ≤ 3} (hij : (0 : Fin 3) ≠ 1)
    (hab : (3 : Fin 4) ≠ 0) (c : F) :
    CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.spinPlusThreeEquiv
        ((plusFrame 3 F hn).longRoot hij false false (.ofAdd c)) =
      transv (3 : Fin 4) (0 : Fin 4) hab c := by
  rw [irgK1_transv_congr hab (by decide)]
  apply CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.rhoGL_injective'
  rw [irgK1_rhoGL_spinPlusThreeEquiv, HypFrame.spinAction_longRoot_eq_eichler, plusFrame_vec]
  rw [irgK1_eichler_swap (by simp [quadPlus_single_inl, quadPlus_single_inr])
    (by simp [quadPlus_single_inl, quadPlus_single_inr])
    (by simp [polar_quadPlus_single_inl, polar_quadPlus_single_inr, polar_smul_right])]
  rw [rho_transv_30]

private theorem irgK1_gen_02tt {hn : 3 ≤ 3} (hij : (0 : Fin 3) ≠ 2)
    (hab : (0 : Fin 4) ≠ 2) (c : F) :
    CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.spinPlusThreeEquiv
        ((plusFrame 3 F hn).longRoot hij true true (.ofAdd c)) =
      transv (0 : Fin 4) (2 : Fin 4) hab c := by
  rw [irgK1_transv_congr hab (by decide)]
  apply CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.rhoGL_injective'
  rw [irgK1_rhoGL_spinPlusThreeEquiv, HypFrame.spinAction_longRoot_eq_eichler, plusFrame_vec]
  rw [irgK1_eichler_swap (by simp [quadPlus_single_inl, quadPlus_single_inr])
    (by simp [quadPlus_single_inl, quadPlus_single_inr])
    (by simp [polar_quadPlus_single_inl, polar_quadPlus_single_inr, polar_smul_right])]
  rw [rho_transv_02]

private theorem irgK1_gen_02tf {hn : 3 ≤ 3} (hij : (0 : Fin 3) ≠ 2)
    (hab : (1 : Fin 4) ≠ 3) (c : F) :
    CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.spinPlusThreeEquiv
        ((plusFrame 3 F hn).longRoot hij true false (.ofAdd c)) =
      transv (1 : Fin 4) (3 : Fin 4) hab c := by
  rw [irgK1_transv_congr hab (by decide)]
  apply CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.rhoGL_injective'
  rw [irgK1_rhoGL_spinPlusThreeEquiv, HypFrame.spinAction_longRoot_eq_eichler, plusFrame_vec]
  rw [rho_transv_13]

private theorem irgK1_gen_02ft {hn : 3 ≤ 3} (hij : (0 : Fin 3) ≠ 2)
    (hab : (3 : Fin 4) ≠ 1) (c : F) :
    CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.spinPlusThreeEquiv
        ((plusFrame 3 F hn).longRoot hij false true (.ofAdd c)) =
      transv (3 : Fin 4) (1 : Fin 4) hab c := by
  rw [irgK1_transv_congr hab (by decide)]
  apply CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.rhoGL_injective'
  rw [irgK1_rhoGL_spinPlusThreeEquiv, HypFrame.spinAction_longRoot_eq_eichler, plusFrame_vec]
  rw [irgK1_eichler_swap (by simp [quadPlus_single_inl, quadPlus_single_inr])
    (by simp [quadPlus_single_inl, quadPlus_single_inr])
    (by simp [polar_quadPlus_single_inl, polar_quadPlus_single_inr, polar_smul_right])]
  rw [rho_transv_31]

private theorem irgK1_gen_02ff {hn : 3 ≤ 3} (hij : (0 : Fin 3) ≠ 2)
    (hab : (2 : Fin 4) ≠ 0) (c : F) :
    CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.spinPlusThreeEquiv
        ((plusFrame 3 F hn).longRoot hij false false (.ofAdd c)) =
      transv (2 : Fin 4) (0 : Fin 4) hab c := by
  rw [irgK1_transv_congr hab (by decide)]
  apply CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.rhoGL_injective'
  rw [irgK1_rhoGL_spinPlusThreeEquiv, HypFrame.spinAction_longRoot_eq_eichler, plusFrame_vec]
  rw [rho_transv_20]

private theorem irgK1_gen_12tt {hn : 3 ≤ 3} (hij : (1 : Fin 3) ≠ 2)
    (hab : (0 : Fin 4) ≠ 1) (c : F) :
    CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.spinPlusThreeEquiv
        ((plusFrame 3 F hn).longRoot hij true true (.ofAdd c)) =
      transv (0 : Fin 4) (1 : Fin 4) hab c := by
  rw [irgK1_transv_congr hab (by decide)]
  apply CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.rhoGL_injective'
  rw [irgK1_rhoGL_spinPlusThreeEquiv, HypFrame.spinAction_longRoot_eq_eichler, plusFrame_vec]
  rw [rho_transv_01]

private theorem irgK1_gen_12tf {hn : 3 ≤ 3} (hij : (1 : Fin 3) ≠ 2)
    (hab : (2 : Fin 4) ≠ 3) (c : F) :
    CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.spinPlusThreeEquiv
        ((plusFrame 3 F hn).longRoot hij true false (.ofAdd c)) =
      transv (2 : Fin 4) (3 : Fin 4) hab c := by
  rw [irgK1_transv_congr hab (by decide)]
  apply CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.rhoGL_injective'
  rw [irgK1_rhoGL_spinPlusThreeEquiv, HypFrame.spinAction_longRoot_eq_eichler, plusFrame_vec]
  rw [rho_transv_23]

private theorem irgK1_gen_12ft {hn : 3 ≤ 3} (hij : (1 : Fin 3) ≠ 2)
    (hab : (3 : Fin 4) ≠ 2) (c : F) :
    CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.spinPlusThreeEquiv
        ((plusFrame 3 F hn).longRoot hij false true (.ofAdd c)) =
      transv (3 : Fin 4) (2 : Fin 4) hab c := by
  rw [irgK1_transv_congr hab (by decide)]
  apply CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.rhoGL_injective'
  rw [irgK1_rhoGL_spinPlusThreeEquiv, HypFrame.spinAction_longRoot_eq_eichler, plusFrame_vec]
  rw [irgK1_eichler_swap (by simp [quadPlus_single_inl, quadPlus_single_inr])
    (by simp [quadPlus_single_inl, quadPlus_single_inr])
    (by simp [polar_quadPlus_single_inl, polar_quadPlus_single_inr, polar_smul_right])]
  rw [rho_transv_32]

private theorem irgK1_gen_12ff {hn : 3 ≤ 3} (hij : (1 : Fin 3) ≠ 2)
    (hab : (1 : Fin 4) ≠ 0) (c : F) :
    CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.spinPlusThreeEquiv
        ((plusFrame 3 F hn).longRoot hij false false (.ofAdd c)) =
      transv (1 : Fin 4) (0 : Fin 4) hab c := by
  rw [irgK1_transv_congr hab (by decide)]
  apply CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.rhoGL_injective'
  rw [irgK1_rhoGL_spinPlusThreeEquiv, HypFrame.spinAction_longRoot_eq_eichler, plusFrame_vec]
  rw [irgK1_eichler_swap (by simp [quadPlus_single_inl, quadPlus_single_inr])
    (by simp [quadPlus_single_inl, quadPlus_single_inr])
    (by simp [polar_quadPlus_single_inl, polar_quadPlus_single_inr, polar_smul_right])]
  rw [rho_transv_10]

private theorem irgK1_gen_10tt {hn : 3 ≤ 3} (hij : (1 : Fin 3) ≠ 0)
    (hab : (0 : Fin 4) ≠ 3) (c : F) :
    CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.spinPlusThreeEquiv
        ((plusFrame 3 F hn).longRoot hij true true (.ofAdd c)) =
      transv (0 : Fin 4) (3 : Fin 4) hab c := by
  rw [irgK1_transv_congr hab (by decide)]
  rw [HypFrame.longRoot_swap]
  simpa [CharTwo.neg_eq] using
    irgK1_gen_01tt (hij := hij.symm) (hab := by decide) c

private theorem irgK1_gen_10tf {hn : 3 ≤ 3} (hij : (1 : Fin 3) ≠ 0)
    (hab : (2 : Fin 4) ≠ 1) (c : F) :
    CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.spinPlusThreeEquiv
        ((plusFrame 3 F hn).longRoot hij true false (.ofAdd c)) =
      transv (2 : Fin 4) (1 : Fin 4) hab c := by
  rw [irgK1_transv_congr hab (by decide)]
  rw [HypFrame.longRoot_swap]
  simpa [CharTwo.neg_eq] using
    irgK1_gen_01ft (hij := hij.symm) (hab := by decide) c

private theorem irgK1_gen_10ft {hn : 3 ≤ 3} (hij : (1 : Fin 3) ≠ 0)
    (hab : (1 : Fin 4) ≠ 2) (c : F) :
    CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.spinPlusThreeEquiv
        ((plusFrame 3 F hn).longRoot hij false true (.ofAdd c)) =
      transv (1 : Fin 4) (2 : Fin 4) hab c := by
  rw [irgK1_transv_congr hab (by decide)]
  rw [HypFrame.longRoot_swap]
  simpa [CharTwo.neg_eq] using
    irgK1_gen_01tf (hij := hij.symm) (hab := by decide) c

private theorem irgK1_gen_10ff {hn : 3 ≤ 3} (hij : (1 : Fin 3) ≠ 0)
    (hab : (3 : Fin 4) ≠ 0) (c : F) :
    CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.spinPlusThreeEquiv
        ((plusFrame 3 F hn).longRoot hij false false (.ofAdd c)) =
      transv (3 : Fin 4) (0 : Fin 4) hab c := by
  rw [irgK1_transv_congr hab (by decide)]
  rw [HypFrame.longRoot_swap]
  simpa [CharTwo.neg_eq] using
    irgK1_gen_01ff (hij := hij.symm) (hab := by decide) c

private theorem irgK1_gen_20tt {hn : 3 ≤ 3} (hij : (2 : Fin 3) ≠ 0)
    (hab : (0 : Fin 4) ≠ 2) (c : F) :
    CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.spinPlusThreeEquiv
        ((plusFrame 3 F hn).longRoot hij true true (.ofAdd c)) =
      transv (0 : Fin 4) (2 : Fin 4) hab c := by
  rw [irgK1_transv_congr hab (by decide)]
  rw [HypFrame.longRoot_swap]
  simpa [CharTwo.neg_eq] using
    irgK1_gen_02tt (hij := hij.symm) (hab := by decide) c

private theorem irgK1_gen_20tf {hn : 3 ≤ 3} (hij : (2 : Fin 3) ≠ 0)
    (hab : (3 : Fin 4) ≠ 1) (c : F) :
    CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.spinPlusThreeEquiv
        ((plusFrame 3 F hn).longRoot hij true false (.ofAdd c)) =
      transv (3 : Fin 4) (1 : Fin 4) hab c := by
  rw [irgK1_transv_congr hab (by decide)]
  rw [HypFrame.longRoot_swap]
  simpa [CharTwo.neg_eq] using
    irgK1_gen_02ft (hij := hij.symm) (hab := by decide) c

private theorem irgK1_gen_20ft {hn : 3 ≤ 3} (hij : (2 : Fin 3) ≠ 0)
    (hab : (1 : Fin 4) ≠ 3) (c : F) :
    CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.spinPlusThreeEquiv
        ((plusFrame 3 F hn).longRoot hij false true (.ofAdd c)) =
      transv (1 : Fin 4) (3 : Fin 4) hab c := by
  rw [irgK1_transv_congr hab (by decide)]
  rw [HypFrame.longRoot_swap]
  simpa [CharTwo.neg_eq] using
    irgK1_gen_02tf (hij := hij.symm) (hab := by decide) c

private theorem irgK1_gen_20ff {hn : 3 ≤ 3} (hij : (2 : Fin 3) ≠ 0)
    (hab : (2 : Fin 4) ≠ 0) (c : F) :
    CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.spinPlusThreeEquiv
        ((plusFrame 3 F hn).longRoot hij false false (.ofAdd c)) =
      transv (2 : Fin 4) (0 : Fin 4) hab c := by
  rw [irgK1_transv_congr hab (by decide)]
  rw [HypFrame.longRoot_swap]
  simpa [CharTwo.neg_eq] using
    irgK1_gen_02ff (hij := hij.symm) (hab := by decide) c

private theorem irgK1_gen_21tt {hn : 3 ≤ 3} (hij : (2 : Fin 3) ≠ 1)
    (hab : (0 : Fin 4) ≠ 1) (c : F) :
    CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.spinPlusThreeEquiv
        ((plusFrame 3 F hn).longRoot hij true true (.ofAdd c)) =
      transv (0 : Fin 4) (1 : Fin 4) hab c := by
  rw [irgK1_transv_congr hab (by decide)]
  rw [HypFrame.longRoot_swap]
  simpa [CharTwo.neg_eq] using
    irgK1_gen_12tt (hij := hij.symm) (hab := by decide) c

private theorem irgK1_gen_21tf {hn : 3 ≤ 3} (hij : (2 : Fin 3) ≠ 1)
    (hab : (3 : Fin 4) ≠ 2) (c : F) :
    CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.spinPlusThreeEquiv
        ((plusFrame 3 F hn).longRoot hij true false (.ofAdd c)) =
      transv (3 : Fin 4) (2 : Fin 4) hab c := by
  rw [irgK1_transv_congr hab (by decide)]
  rw [HypFrame.longRoot_swap]
  simpa [CharTwo.neg_eq] using
    irgK1_gen_12ft (hij := hij.symm) (hab := by decide) c

private theorem irgK1_gen_21ft {hn : 3 ≤ 3} (hij : (2 : Fin 3) ≠ 1)
    (hab : (2 : Fin 4) ≠ 3) (c : F) :
    CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.spinPlusThreeEquiv
        ((plusFrame 3 F hn).longRoot hij false true (.ofAdd c)) =
      transv (2 : Fin 4) (3 : Fin 4) hab c := by
  rw [irgK1_transv_congr hab (by decide)]
  rw [HypFrame.longRoot_swap]
  simpa [CharTwo.neg_eq] using
    irgK1_gen_12tf (hij := hij.symm) (hab := by decide) c

private theorem irgK1_gen_21ff {hn : 3 ≤ 3} (hij : (2 : Fin 3) ≠ 1)
    (hab : (1 : Fin 4) ≠ 0) (c : F) :
    CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.spinPlusThreeEquiv
        ((plusFrame 3 F hn).longRoot hij false false (.ofAdd c)) =
      transv (1 : Fin 4) (0 : Fin 4) hab c := by
  rw [irgK1_transv_congr hab (by decide)]
  rw [HypFrame.longRoot_swap]
  simpa [CharTwo.neg_eq] using
    irgK1_gen_12ff (hij := hij.symm) (hab := by decide) c


private theorem irgK1_compat {hn : 3 ≤ 3} (β' : Fin 3 → ℤ)
    (hβ' : β' ∈ (Spin.plusDatum 3 F hn).roots)
    (hlong : GGLongRoot (Spin.plusDatum 3 F hn) β') :
    ∃ γ : Fin 3 → ℤ, γ ∈ (SpecialLinear.rootDatum 3 F).roots ∧
      GGLongRoot (SpecialLinear.rootDatum 3 F) γ ∧
      ∃ w : SpecialLinearGroup (Fin 4) F,
        ((plusRootGroup 3 F hn β').map
            (CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.spinPlusThreeEquiv
              (F := F)).toMonoidHom) =
            ((SpecialLinear.rootGroup 3 F γ).map (MulAut.conj w).toMonoidHom) ∧
        ((plusRootGroup 3 F hn (-β')).map
            (CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.spinPlusThreeEquiv
              (F := F)).toMonoidHom) =
            ((SpecialLinear.rootGroup 3 F (-γ)).map (MulAut.conj w).toMonoidHom) := by
  have hgood : ∀ (a b : Fin 4) (hab : a ≠ b),
      irgK1_gammaOf a b ∈ (SpecialLinear.rootDatum 3 F).roots ∧
      GGLongRoot (SpecialLinear.rootDatum 3 F) (irgK1_gammaOf a b) := by
    intro a b hab
    have hγ : irgK1_gammaOf a b ∈ (SpecialLinear.rootDatum 3 F).roots := by
      change irgK1_gammaOf a b ∈ roots (SpecialLinear.isFiniteType_A 3) ∅
      rw [SpecialLinear.roots_eq]
      exact ⟨a, b, hab, irgK1_gammaOf_toStd a b⟩
    refine ⟨hγ, ?_⟩
    exact CFSG.StandardType.ggLongRoot_of_symmetric
      (CFSG.ClassicalInvolution.ModelFacts.isIrreducible_A (by norm_num : 0 < 3))
      (fun i j => CFSG.ClassicalInvolution.ModelFacts.cartanA_symm 3 i j) rfl hγ
  obtain ⟨i, j, hij, s, t, hβ, hgrp⟩ := Spin.exists_plusRootGroup_eq (n := 3) (K := F) hn hβ'
  let a := (irgK1_ab i j s t).1
  let b := (irgK1_ab i j s t).2
  have hab : a ≠ b := irgK1_ab_ne i j s t hij
  obtain ⟨hγroot, hγlong⟩ := hgood a b hab
  refine ⟨irgK1_gammaOf a b, hγroot, hγlong, 1, ?_, ?_⟩
  · have hsrc : plusRootGroup 3 F hn β' =
        ((plusFrame 3 F hn).longRoot hij s t).range :=
      plusRootGroup_eq hn hij s t hβ
    have htgt : SpecialLinear.rootGroup 3 F (irgK1_gammaOf a b) =
        (SpecialLinearGroup.transvectionHom (A := F) hab).range :=
      SpecialLinear.rootGroup_eq 3 F hab (irgK1_gammaOf_toStd a b)
    have hconj : MulAut.conj (1 : SpecialLinearGroup (Fin 4) F) = 1 := by
      ext y; simp [MulAut.conj_apply]
    have hone : (MulEquiv.toMonoidHom (1 : MulAut (SpecialLinearGroup (Fin 4) F))) =
        MonoidHom.id _ := by ext x; rfl
    rw [hsrc, htgt, hconj, hone, Subgroup.map_id]
    rw [MonoidHom.map_range]
    congr 1
    apply MonoidHom.ext
    intro x
    rw [MonoidHom.comp_apply, SpecialLinearGroup.transvectionHom_apply]
    fin_cases i <;> fin_cases j <;> cases s <;> cases t <;>
      first
        | exact (hij rfl).elim
        | exact irgK1_gen_01tt hij hab (Multiplicative.toAdd x)
        | exact irgK1_gen_01tf hij hab (Multiplicative.toAdd x)
        | exact irgK1_gen_01ft hij hab (Multiplicative.toAdd x)
        | exact irgK1_gen_01ff hij hab (Multiplicative.toAdd x)
        | exact irgK1_gen_02tt hij hab (Multiplicative.toAdd x)
        | exact irgK1_gen_02tf hij hab (Multiplicative.toAdd x)
        | exact irgK1_gen_02ft hij hab (Multiplicative.toAdd x)
        | exact irgK1_gen_02ff hij hab (Multiplicative.toAdd x)
        | exact irgK1_gen_12tt hij hab (Multiplicative.toAdd x)
        | exact irgK1_gen_12tf hij hab (Multiplicative.toAdd x)
        | exact irgK1_gen_12ft hij hab (Multiplicative.toAdd x)
        | exact irgK1_gen_12ff hij hab (Multiplicative.toAdd x)
        | exact irgK1_gen_10tt hij hab (Multiplicative.toAdd x)
        | exact irgK1_gen_10tf hij hab (Multiplicative.toAdd x)
        | exact irgK1_gen_10ft hij hab (Multiplicative.toAdd x)
        | exact irgK1_gen_10ff hij hab (Multiplicative.toAdd x)
        | exact irgK1_gen_20tt hij hab (Multiplicative.toAdd x)
        | exact irgK1_gen_20tf hij hab (Multiplicative.toAdd x)
        | exact irgK1_gen_20ft hij hab (Multiplicative.toAdd x)
        | exact irgK1_gen_20ff hij hab (Multiplicative.toAdd x)
        | exact irgK1_gen_21tt hij hab (Multiplicative.toAdd x)
        | exact irgK1_gen_21tf hij hab (Multiplicative.toAdd x)
        | exact irgK1_gen_21ft hij hab (Multiplicative.toAdd x)
        | exact irgK1_gen_21ff hij hab (Multiplicative.toAdd x)
  · have hsrc : plusRootGroup 3 F hn (-β') =
        ((plusFrame 3 F hn).longRoot hij (!s) (!t)).range :=
      plusRootGroup_eq hn hij (!s) (!t) (by
        rw [Spin.toStdD_neg, hβ, neg_add, ← Pi.single_neg, ← Pi.single_neg]
        simp only [Spin.boolSign_not])
    have htgt : SpecialLinear.rootGroup 3 F (-(irgK1_gammaOf a b)) =
        (SpecialLinearGroup.transvectionHom (A := F) hab.symm).range :=
      SpecialLinear.rootGroup_eq 3 F hab.symm (by
        rw [SpecialLinear.toStd_neg, irgK1_gammaOf_toStd, neg_sub])
    have hconj : MulAut.conj (1 : SpecialLinearGroup (Fin 4) F) = 1 := by
      ext y; simp [MulAut.conj_apply]
    have hone : (MulEquiv.toMonoidHom (1 : MulAut (SpecialLinearGroup (Fin 4) F))) =
        MonoidHom.id _ := by ext x; rfl
    rw [hsrc, htgt, hconj, hone, Subgroup.map_id]
    rw [MonoidHom.map_range]
    congr 1
    apply MonoidHom.ext
    intro x
    rw [MonoidHom.comp_apply, SpecialLinearGroup.transvectionHom_apply]
    fin_cases i <;> fin_cases j <;> cases s <;> cases t <;>
      first
        | exact (hij rfl).elim
        | exact irgK1_gen_01ft hij hab.symm (Multiplicative.toAdd x)
        | exact irgK1_gen_01ff hij hab.symm (Multiplicative.toAdd x)
        | exact irgK1_gen_01tt hij hab.symm (Multiplicative.toAdd x)
        | exact irgK1_gen_01tf hij hab.symm (Multiplicative.toAdd x)
        | exact irgK1_gen_02ft hij hab.symm (Multiplicative.toAdd x)
        | exact irgK1_gen_02ff hij hab.symm (Multiplicative.toAdd x)
        | exact irgK1_gen_02tt hij hab.symm (Multiplicative.toAdd x)
        | exact irgK1_gen_02tf hij hab.symm (Multiplicative.toAdd x)
        | exact irgK1_gen_12ft hij hab.symm (Multiplicative.toAdd x)
        | exact irgK1_gen_12ff hij hab.symm (Multiplicative.toAdd x)
        | exact irgK1_gen_12tt hij hab.symm (Multiplicative.toAdd x)
        | exact irgK1_gen_12tf hij hab.symm (Multiplicative.toAdd x)
        | exact irgK1_gen_10ft hij hab.symm (Multiplicative.toAdd x)
        | exact irgK1_gen_10ff hij hab.symm (Multiplicative.toAdd x)
        | exact irgK1_gen_10tt hij hab.symm (Multiplicative.toAdd x)
        | exact irgK1_gen_10tf hij hab.symm (Multiplicative.toAdd x)
        | exact irgK1_gen_20ft hij hab.symm (Multiplicative.toAdd x)
        | exact irgK1_gen_20ff hij hab.symm (Multiplicative.toAdd x)
        | exact irgK1_gen_20tt hij hab.symm (Multiplicative.toAdd x)
        | exact irgK1_gen_20tf hij hab.symm (Multiplicative.toAdd x)
        | exact irgK1_gen_21ft hij hab.symm (Multiplicative.toAdd x)
        | exact irgK1_gen_21ff hij hab.symm (Multiplicative.toAdd x)
        | exact irgK1_gen_21tt hij hab.symm (Multiplicative.toAdd x)
        | exact irgK1_gen_21tf hij hab.symm (Multiplicative.toAdd x)

theorem irgIsoCompat_omegaPlus_three
    {g : ℕ} (hg : 1 ≤ g) :
    ∃ e : (ggU .POmegaPlus 3 g).K ≃* (ggU .PSL 4 g).K, IRGIsoCompat e := by
  have hsrc : ggU .POmegaPlus 3 g =
      (⟨spinGroup (quadPlus 3 (GaloisField 2 g)),
        Spin.plusDatum 3 (GaloisField 2 g) (le_refl 3)⟩ : LieUniversal) := by
    simp only [ggU, CFSG.LieType.Universal.lieUniversal, show 3 ≤ 3 from le_refl 3,
      ↓reduceDIte]
  unfold IRGIsoCompat
  simp only [IRGGoodRoot]
  rw [hsrc]
  refine ⟨CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.spinPlusThreeEquiv, ?_⟩
  intro β' hβ' hlong
  obtain ⟨γ, hγroot, hγlong, w, h1, h2⟩ := irgK1_compat (hn := le_refl 3) β' hβ' hlong
  exact ⟨γ, ⟨hγroot, Or.inl hγlong⟩, w, h1, h2⟩

end CFSG.StandardType.RCKRP
