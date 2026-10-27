module

public import CFSG.LieType.Chevalley.OrthogonalFixedOrbitMaps
public import CFSG.LieType.Ree.SmallReeCollectionCheck
public import CFSG.RankThree.PartOne.SEITZ11.G2SevenRep

public section

namespace CFSG.RankThree.PartOne.SEITZ11.G2Seven

open Matrix CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley.RootOps CFSG.LieType.Ree CFSG.RankThree.PartOne
  CFSG.LieType.Steinberg.RankTwo CFSG.LocalAnalysis.ComponentInitial

section Theta

variable {R : Type*} [CommRing R]

@[expose] def theta0 (M : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 7) (Fin 7) R :=
  !![1, 0, 0, 0, 0, 0, 0;
     0, M 1 1, M 1 0, 0, 0, 0, 0;
     0, M 0 1, M 0 0, 0, 0, 0, 0;
     0, 0, 0, M 0 0, 0, M 0 1, 0;
     0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, M 1 0, 0, M 1 1, 0;
     0, 0, 0, 0, 0, 0, 1]

theorem theta0_mul (M N : Matrix (Fin 2) (Fin 2) R) :
    theta0 (M * N) = theta0 M * theta0 N := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [theta0, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem theta0_one : theta0 (1 : Matrix (Fin 2) (Fin 2) R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [theta0]

@[expose] def theta1 (M : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 7) (Fin 7) R :=
  !![M 0 0 * M 1 1 + M 0 1 * M 1 0, M 0 0 * M 1 0, 0, M 0 1 * M 1 1, 0, 0, 0;
     2 * (M 0 0 * M 0 1), M 0 0 * M 0 0, 0, M 0 1 * M 0 1, 0, 0, 0;
     0, 0, M 1 1, 0, M 1 0, 0, 0;
     2 * (M 1 0 * M 1 1), M 1 0 * M 1 0, 0, M 1 1 * M 1 1, 0, 0, 0;
     0, 0, M 0 1, 0, M 0 0, 0, 0;
     0, 0, 0, 0, 0, M 0 0, M 0 1;
     0, 0, 0, 0, 0, M 1 0, M 1 1]

theorem theta1_mul (M N : Matrix (Fin 2) (Fin 2) R) :
    theta1 (M * N) = theta1 M * theta1 N := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [theta1, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem theta1_one : theta1 (1 : Matrix (Fin 2) (Fin 2) R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [theta1]

theorem theta0_upper (c : R) : theta0 !![1, c; 0, 1] = rootMat 0 c := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [theta0, rootMat, opMat, opMatSq, entMat, ent7, ent7sq]

theorem theta0_lower (c : R) : theta0 !![1, 0; c, 1] = rootMat 2 c := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [theta0, rootMat, opMat, opMatSq, entMat, ent7, ent7sq]

theorem theta1_upper (c : R) : theta1 !![1, c; 0, 1] = rootMat 1 c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [theta1, rootMat, opMat, opMatSq, entMat, ent7, ent7sq, mul_comm]

theorem theta1_lower (c : R) : theta1 !![1, 0; c, 1] = rootMat 5 c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [theta1, rootMat, opMat, opMatSq, entMat, ent7, ent7sq, mul_comm]

@[expose] def theta0Hom : Matrix (Fin 2) (Fin 2) R →* Matrix (Fin 7) (Fin 7) R where
  toFun := theta0
  map_one' := theta0_one
  map_mul' := theta0_mul

@[expose] def theta1Hom : Matrix (Fin 2) (Fin 2) R →* Matrix (Fin 7) (Fin 7) R where
  toFun := theta1
  map_one' := theta1_one
  map_mul' := theta1_mul

@[expose] def thetaGL (θ : Matrix (Fin 2) (Fin 2) R →* Matrix (Fin 7) (Fin 7) R) :
    Matrix.SpecialLinearGroup (Fin 2) R →* GL (Fin 7) R :=
  (θ.comp ((Units.coeHom _).comp Matrix.SpecialLinearGroup.toGL)).toHomUnits

end Theta

abbrev ia : Fin Tag.G2.rank := ⟨0, by decide⟩

abbrev ib : Fin Tag.G2.rank := ⟨1, by decide⟩

theorem root_pos0 : g2CommRoot 0 = Pi.single ia 1 := by decide
theorem root_pos1 : g2CommRoot 1 = Pi.single ib 1 := by decide
theorem root_pos2 : g2CommRoot 2 = -Pi.single ia 1 := by decide
theorem root_pos5 : g2CommRoot 5 = -Pi.single ib 1 := by decide

section Rho

variable (k : Type) [Field k]

theorem pinnedWeyl_single (i : Fin Tag.G2.rank) :
    pinnedWeyl Tag.G2 k (Pi.single i 1) = 1 := by
  simp [pinnedWeyl, pinnedData_single]

theorem rootSL2_single_eq (i : Fin Tag.G2.rank) :
    rootSL2 Tag.G2 k (Pi.single i 1) = simpleRootSL2 Tag.G2 k i := by
  ext A : 1
  rw [rootSL2_apply, pinnedData_single, pinnedWeyl_single]
  simp

theorem rootSL2_single_uSL (i : Fin Tag.G2.rank) (c : k) :
    rootSL2 Tag.G2 k (Pi.single i 1) (uSL c) =
      ((xPar (rootOperatorFamily Tag.G2) (Pi.single i 1) c : adjointGroup Tag.G2 k) :
        ModGL Tag.G2 k) := by
  rw [rootSL2_single_eq, simpleRootSL2_uSL, ← pinnedX_single,
    (rootOperatorFamily Tag.G2).pinnedX_eq_eltUnit k (isRoot_single _ i)]
  have hs : (rootOperatorFamily Tag.G2).pinnedFamilySign (Pi.single i 1) = 1 := by
    rw [RootOperatorFamily.pinnedFamilySign, pinnedData_single]; rfl
  rw [hs, xPar_of_isRoot (isRoot_single _ i)]
  simp

theorem rootSL2_single_vSL (i : Fin Tag.G2.rank) (c : k)
    (hs : (rootOperatorFamily Tag.G2).pinnedFamilySign (-Pi.single i 1) = 1) :
    rootSL2 Tag.G2 k (Pi.single i 1) (vSL c) =
      ((xPar (rootOperatorFamily Tag.G2) (-Pi.single i 1) c : adjointGroup Tag.G2 k) :
        ModGL Tag.G2 k) := by
  rw [rootSL2_single_eq, simpleRootSL2_vSL, ← pinnedX_neg_single,
    (rootOperatorFamily Tag.G2).pinnedX_eq_eltUnit k (isRoot_neg_single _ i)]
  rw [hs, xPar_of_isRoot (isRoot_neg_single _ i)]
  simp

theorem sign_pos2 : (rootOperatorFamily Tag.G2).pinnedFamilySign (-Pi.single ia 1) = 1 := by
  rw [← root_pos2]
  exact (pinnedFamilySign_of_signOneB (τ := Tag.G2) (g := 2) (by decide +kernel)).2

theorem sign_pos5 : (rootOperatorFamily Tag.G2).pinnedFamilySign (-Pi.single ib 1) = 1 := by
  rw [← root_pos5]
  exact (pinnedFamilySign_of_signOneB (τ := Tag.G2) (g := 5) (by decide +kernel)).2

@[expose] noncomputable def rhoG (β : Fin Tag.G2.rank → ℤ) : SL2 k →* adjointGroup Tag.G2 k :=
  (rootSL2 Tag.G2 k β).codRestrict _ (rootSL2_mem_adjointGroup β)

variable [Finite k]

@[expose] noncomputable def phi7 (β : Fin Tag.G2.rank → ℤ) : SL2 k →* GL (Fin 7) k :=
  (rep7 k).comp (rhoG k β)

theorem phi7_a_u (c : k) :
    ((phi7 k (Pi.single ia 1) (uSL c) : GL (Fin 7) k) : Matrix (Fin 7) (Fin 7) k) =
      rootMat 0 c := by
  have h : rhoG k (Pi.single ia 1) (uSL c) =
      xPar (rootOperatorFamily Tag.G2) (g2CommRoot 0) c :=
    Subtype.ext (by rw [root_pos0]; exact rootSL2_single_uSL k ia c)
  simp only [phi7, MonoidHom.comp_apply, h]
  exact rep7_xPar_pos k (by norm_num) c

theorem phi7_a_v (c : k) :
    ((phi7 k (Pi.single ia 1) (vSL c) : GL (Fin 7) k) : Matrix (Fin 7) (Fin 7) k) =
      rootMat 2 c := by
  have h : rhoG k (Pi.single ia 1) (vSL c) =
      xPar (rootOperatorFamily Tag.G2) (g2CommRoot 2) c :=
    Subtype.ext (by rw [root_pos2]; exact rootSL2_single_vSL k ia c sign_pos2)
  simp only [phi7, MonoidHom.comp_apply, h]
  exact rep7_xPar_pos k (by norm_num) c

theorem phi7_b_u (c : k) :
    ((phi7 k (Pi.single ib 1) (uSL c) : GL (Fin 7) k) : Matrix (Fin 7) (Fin 7) k) =
      rootMat 1 c := by
  have h : rhoG k (Pi.single ib 1) (uSL c) =
      xPar (rootOperatorFamily Tag.G2) (g2CommRoot 1) c :=
    Subtype.ext (by rw [root_pos1]; exact rootSL2_single_uSL k ib c)
  simp only [phi7, MonoidHom.comp_apply, h]
  exact rep7_xPar_pos k (by norm_num) c

theorem phi7_b_v (c : k) :
    ((phi7 k (Pi.single ib 1) (vSL c) : GL (Fin 7) k) : Matrix (Fin 7) (Fin 7) k) =
      rootMat 5 c := by
  have h : rhoG k (Pi.single ib 1) (vSL c) =
      xPar (rootOperatorFamily Tag.G2) (g2CommRoot 5) c :=
    Subtype.ext (by rw [root_pos5]; exact rootSL2_single_vSL k ib c sign_pos5)
  simp only [phi7, MonoidHom.comp_apply, h]
  exact rep7_xPar_pos k (by norm_num) c

theorem phi7_a_eq (M : SL2 k) :
    ((phi7 k (Pi.single ia 1) M : GL (Fin 7) k) : Matrix (Fin 7) (Fin 7) k) =
      theta0 (M : Matrix (Fin 2) (Fin 2) k) := by
  have h : phi7 k (Pi.single ia 1) = thetaGL theta0Hom :=
    MonoidHom.eq_of_eqOn_dense (sl2_closure_upper_lower (K := k)) fun g hg => by
      rcases hg with ⟨c, rfl⟩ | ⟨c, rfl⟩
      · exact Units.ext ((phi7_a_u k c).trans (theta0_upper c).symm)
      · exact Units.ext ((phi7_a_v k c).trans (theta0_lower c).symm)
  rw [h]
  rfl

theorem phi7_b_eq (M : SL2 k) :
    ((phi7 k (Pi.single ib 1) M : GL (Fin 7) k) : Matrix (Fin 7) (Fin 7) k) =
      theta1 (M : Matrix (Fin 2) (Fin 2) k) := by
  have h : phi7 k (Pi.single ib 1) = thetaGL theta1Hom :=
    MonoidHom.eq_of_eqOn_dense (sl2_closure_upper_lower (K := k)) fun g hg => by
      rcases hg with ⟨c, rfl⟩ | ⟨c, rfl⟩
      · exact Units.ext ((phi7_b_u k c).trans (theta1_upper c).symm)
      · exact Units.ext ((phi7_b_v k c).trans (theta1_lower c).symm)
  rw [h]
  rfl

end Rho

end CFSG.RankThree.PartOne.SEITZ11.G2Seven
