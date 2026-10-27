module

public import CFSG.RankThree.E6.RootLatticeTools
public import CFSG.LocalAnalysis.StandardType.GGKG3K3dCheck

public section

namespace CFSG.StandardType.GGKG3.K3dWeyl

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.StandardType.GGKG3.K3dCheck

@[expose] noncomputable def weylMat6 (c : WeylGroup .E6) : Matrix (Fin 6) (Fin 6) ℤ :=
  Matrix.of fun i j => weylMatrix c i j

theorem weylMat6_apply (c : WeylGroup .E6) (i j : Fin 6) : weylMat6 c i j = weylMatrix c i j :=
  rfl

theorem weylMat6_mul (c c' : WeylGroup .E6) : weylMat6 (c * c') = weylMat6 c * weylMat6 c' := by
  have h := weylMatrix_mul c c'
  ext i j
  exact congrFun (congrFun h i) j

theorem weylMat6_one : weylMat6 (1 : WeylGroup .E6) = 1 := by
  have h := weylMatrix_one (τ := .E6)
  ext i j
  exact congrFun (congrFun h i) j

theorem weylMat6_trace (c : WeylGroup .E6) : (weylMat6 c).trace = (weylMatrix c).trace :=
  rfl

theorem weylMat6_mulVec (c : WeylGroup .E6) (x : Fin Tag.E6.rank → ℤ) :
    (weylMat6 c).mulVec x = c • x :=
  weylMatrix_mulVec c x

private lemma kg3_weylMat6_simple' (i a b : Fin Tag.E6.rank) :
    weylMat6 (simple .E6 i) a b =
      (if a = b then 1 else 0) - (if a = i then kC i b else 0) := by
  change weylMatrix (simple .E6 i) a b =
      (if a = b then 1 else 0) - (if a = i then kC i b else 0)
  rw [weylMatrix_apply, simple_smul, reflect]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  have hsum : (∑ j : Fin Tag.E6.rank,
      Tag.E6.cartan i j * (if j = b then (1 : ℤ) else 0)) = kC i b := by
    rw [Finset.sum_eq_single b]
    · simp [kC]
    · intro j _ hj
      simp [hj]
    · intro hb
      exact absurd (Finset.mem_univ b) hb
  rw [hsum]
  by_cases hai : a = i
  · rw [if_pos hai, if_pos hai]
    ring
  · rw [if_neg hai, if_neg hai]
    ring

private def kg3_S (i : Fin 6) : Matrix (Fin 6) (Fin 6) ℤ :=
  Matrix.of fun a b => (if a = b then 1 else 0) - (if a = i then kC i b else 0)

private lemma kg3_weylMat6_simple (i a b : Fin 6) :
    weylMat6 (simple .E6 i) a b =
      (if a = b then 1 else 0) - (if a = i then kC i b else 0) :=
  kg3_weylMat6_simple' i a b

private lemma kg3_weylMat6_simple_eq (i : Fin 6) :
    weylMat6 (simple .E6 i) = kg3_S i := by
  ext a b
  exact kg3_weylMat6_simple i a b

private lemma kg3_S_orth (i : Fin 6) :
    (kg3_S i).transpose * Matrix.of kC * kg3_S i = Matrix.of kC := by
  fin_cases i <;> decide +kernel

private lemma kg3_S_dvd (i a b : Fin 6) :
    3 ∣ ((kg3_S i - 1) * Matrix.of kAdjC) a b := by
  fin_cases i <;> fin_cases a <;> fin_cases b <;> decide +kernel

theorem k3_weylMat6_orth (c : WeylGroup .E6) :
    (weylMat6 c).transpose * Matrix.of kC * weylMat6 c = Matrix.of kC := by
  refine (coxeterSystem .E6).simple_induction_left
    (p := fun c => (weylMat6 c).transpose * Matrix.of kC * weylMat6 c = Matrix.of kC)
    c ?_ ?_
  · rw [weylMat6_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
  · intro w i hw
    let j : Fin 6 := i
    have hsimple : weylMat6 ((coxeterSystem .E6).simple i) = kg3_S j :=
      kg3_weylMat6_simple_eq j
    rw [weylMat6_mul, hsimple, Matrix.transpose_mul]
    calc
      (weylMat6 w).transpose * (kg3_S j).transpose * Matrix.of kC * (kg3_S j * weylMat6 w)
          = (weylMat6 w).transpose *
              ((kg3_S j).transpose * Matrix.of kC * kg3_S j) * weylMat6 w := by
            simp only [Matrix.mul_assoc]
      _ = (weylMat6 w).transpose * Matrix.of kC * weylMat6 w := by rw [kg3_S_orth]
      _ = Matrix.of kC := hw

theorem k3_weylMat6_sub_one_adj (c : WeylGroup .E6) (i j : Fin 6) :
    3 ∣ ((weylMat6 c - 1) * Matrix.of kAdjC) i j := by
  refine (coxeterSystem .E6).simple_induction_left
    (p := fun c => ∀ i j : Fin 6, 3 ∣ ((weylMat6 c - 1) * Matrix.of kAdjC) i j)
    c ?_ ?_ i j
  · intro i j
    rw [weylMat6_one]
    simp
  · intro w k hw a b
    let j : Fin 6 := k
    have hsimple : weylMat6 ((coxeterSystem .E6).simple k) = kg3_S j :=
      kg3_weylMat6_simple_eq j
    rw [weylMat6_mul, hsimple]
    have hS : 3 ∣ ((kg3_S j - 1) * Matrix.of kAdjC) a b := kg3_S_dvd j a b
    have hsplit : ((kg3_S j * weylMat6 w - 1) * Matrix.of kAdjC) a b =
        (kg3_S j * ((weylMat6 w - 1) * Matrix.of kAdjC)) a b +
          ((kg3_S j - 1) * Matrix.of kAdjC) a b := by
      have hmat : (kg3_S j * weylMat6 w - 1) * Matrix.of kAdjC =
          kg3_S j * ((weylMat6 w - 1) * Matrix.of kAdjC) +
            (kg3_S j - 1) * Matrix.of kAdjC := by
        noncomm_ring
      rw [hmat, Matrix.add_apply]
    rw [hsplit]
    apply dvd_add
    · rw [Matrix.mul_apply]
      apply Finset.dvd_sum
      intro x _
      exact dvd_mul_of_dvd_right (hw x b) (kg3_S j a x)
    · exact hS

end CFSG.StandardType.GGKG3.K3dWeyl
