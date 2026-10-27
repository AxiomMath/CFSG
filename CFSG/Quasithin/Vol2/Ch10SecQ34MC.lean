module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10P34

open CFSG.Blueprint Matrix

variable (a : ℕ) {K : Type} [Field K]

theorem det_S (u v : K) : (suzukiS a u v).det = 1 := by
  rw [← Matrix.det_transpose, Matrix.det_of_isUpperTriangular]
  · simp [suzukiS, Fin.prod_univ_four]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [suzukiS]

theorem det_D (l : Kˣ) : (suzukiD a l).det = 1 := by
  have h : l ^ (1 + (2 ^ a : ℤ)) * l ^ (2 ^ a : ℤ) * l ^ (-(2 ^ a : ℤ)) *
      l ^ (-1 - (2 ^ a : ℤ)) = 1 := by
    rw [← _root_.zpow_add, ← _root_.zpow_add, ← _root_.zpow_add]
    ring_nf
    exact zpow_zero l
  rw [suzukiD, Matrix.det_diagonal, Fin.prod_univ_four]
  change ((l ^ (1 + (2 ^ a : ℤ)) : Kˣ) : K) * ((l ^ (2 ^ a : ℤ) : Kˣ) : K) *
    ((l ^ (-(2 ^ a : ℤ)) : Kˣ) : K) * ((l ^ (-1 - (2 ^ a : ℤ)) : Kˣ) : K) = 1
  rw [← Units.val_mul, ← Units.val_mul, ← Units.val_mul, h, Units.val_one]

variable (K) in
theorem W_mul_self : suzukiW K * suzukiW K = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [suzukiW, Matrix.mul_apply, Fin.sum_univ_four]

@[expose] noncomputable def sElt (u v : K) : ↥(suzukiGroup a K) :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (suzukiS a u v) (by rw [det_S]; exact one_ne_zero),
    Subgroup.subset_closure (Or.inl ⟨u, v, rfl⟩)⟩

@[expose] noncomputable def dElt (l : Kˣ) : ↥(suzukiGroup a K) :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (suzukiD a l) (by rw [det_D]; exact one_ne_zero),
    Subgroup.subset_closure (Or.inr (Or.inl ⟨l, rfl⟩))⟩

variable (K) in
@[expose] noncomputable def wElt : ↥(suzukiGroup a K) :=
  ⟨⟨suzukiW K, suzukiW K, W_mul_self K, W_mul_self K⟩,
    Subgroup.subset_closure (Or.inr (Or.inr rfl))⟩

theorem mulVec_S_one_zero (x : Fin 4 → K) :
    suzukiS a 1 0 *ᵥ x = ![x 0, x 0 + x 1, x 1 + x 2, x 0 + x 1 + x 2 + x 3] := by
  ext i
  fin_cases i <;> simp [suzukiS, suzukiN, mulVec, dotProduct, Fin.sum_univ_four]

theorem mulVec_S_zero (v c : K) :
    suzukiS a 0 v *ᵥ Pi.single 0 c = ![c, 0, v * c, v ^ 2 ^ (a + 1) * c] := by
  ext i
  fin_cases i <;> simp [suzukiS, suzukiN, mulVec, dotProduct, Pi.single_apply]

theorem mulVec_W (x : Fin 4 → K) : suzukiW K *ᵥ x = ![x 3, x 2, x 1, x 0] := by
  ext i
  fin_cases i <;> simp [suzukiW, mulVec, dotProduct, Fin.sum_univ_four]

theorem mulVec_D_one (l : Kˣ) (c : K) :
    suzukiD a l *ᵥ Pi.single 1 c = Pi.single 1 (((l ^ (2 ^ a : ℤ) : Kˣ) : K) * c) := by
  ext i
  fin_cases i <;> simp [suzukiD, mulVec_diagonal]

end CFSG.Quasithin.Vol2.Ch10.SecB.C10P34
