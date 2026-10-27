module

public import CFSG.Quasithin.EmptyFaithful.E22SUGen
public import CFSG.Quasithin.EmptyFaithful.E22SULift

public section

namespace CFSG.Quasithin.E22S

open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.Assembly.LowTwoRank CFSG.Open
open scoped Matrix

variable {K : Type} [Field K] {p f : ℕ}

abbrev PSU3 (p f : ℕ) (K : Type) [Field K] : Type := StatedProj (unitarySU p f K 3)

@[expose] noncomputable def suMk (hU : UnitaryFieldData p f K) (M : Matrix (Fin 3) (Fin 3) K)
    (hdet : M.det = 1) (hu : (M.map hU.bar)ᵀ * M = 1) : ↥(unitarySU p f K 3) :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M (by rw [hdet]; exact one_ne_zero),
    (mem_unitarySU_iff hU).mpr ⟨by simpa using hdet, by simpa using hu⟩⟩

theorem suMk_val (hU : UnitaryFieldData p f K) (M : Matrix (Fin 3) (Fin 3) K) (hdet : M.det = 1)
    (hu : (M.map hU.bar)ᵀ * M = 1) :
    (((suMk hU M hdet hu : ↥(unitarySU p f K 3)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      M := rfl

@[expose] def matZ (K : Type) [Field K] : Matrix (Fin 3) (Fin 3) K :=
  !![-1, 0, 0; 0, -1, 0; 0, 0, 1]

@[expose] def matSw (K : Type) [Field K] : Matrix (Fin 3) (Fin 3) K :=
  !![0, 1, 0; 1, 0, 0; 0, 0, -1]

theorem det_matZ : (matZ K).det = 1 := by simp [matZ, Matrix.det_fin_three]

theorem det_matSw : (matSw K).det = 1 := by simp [matSw, Matrix.det_fin_three]

theorem bar_matZ (hU : UnitaryFieldData p f K) : (matZ K).map hU.bar = matZ K := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [matZ]

theorem bar_matSw (hU : UnitaryFieldData p f K) : (matSw K).map hU.bar = matSw K := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [matSw]

theorem matZ_mul_self : matZ K * matZ K = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [matZ, Matrix.mul_apply, Fin.sum_univ_three]

theorem matSw_mul_self : matSw K * matSw K = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [matSw, Matrix.mul_apply, Fin.sum_univ_three]

theorem matZ_transpose : (matZ K)ᵀ = matZ K := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [matZ]

theorem matSw_transpose : (matSw K)ᵀ = matSw K := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [matSw]

@[expose] noncomputable def zS (hU : UnitaryFieldData p f K) : ↥(unitarySU p f K 3) :=
  suMk hU (matZ K) det_matZ (by rw [bar_matZ, matZ_transpose, matZ_mul_self])

@[expose] noncomputable def swS (hU : UnitaryFieldData p f K) : ↥(unitarySU p f K 3) :=
  suMk hU (matSw K) det_matSw (by rw [bar_matSw, matSw_transpose, matSw_mul_self])

theorem zS_mul_self (hU : UnitaryFieldData p f K) : zS hU * zS hU = 1 :=
  Subtype.ext (Units.ext (by
    show matZ K * matZ K = 1
    exact matZ_mul_self))

theorem swS_mul_self (hU : UnitaryFieldData p f K) : swS hU * swS hU = 1 :=
  Subtype.ext (Units.ext (by
    show matSw K * matSw K = 1
    exact matSw_mul_self))

theorem zS_mul_swS (hU : UnitaryFieldData p f K) : zS hU * swS hU = swS hU * zS hU :=
  Subtype.ext (Units.ext (by
    show matZ K * matSw K = matSw K * matZ K
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [matZ, matSw, Matrix.mul_apply, Fin.sum_univ_three]))

@[expose] def kleinSub {G : Type*} [Group G] (a b : G) (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) : Subgroup G where
  carrier := {x | x = 1 ∨ x = a ∨ x = b ∨ x = a * b}
  one_mem' := Or.inl rfl
  mul_mem' := by
    have h1 : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
    have h2 : b * (a * b) = a := by rw [← mul_assoc, ← hab, mul_assoc, hb, mul_one]
    have h3 : a * b * a = b := by rw [mul_assoc, ← hab, ← mul_assoc, ha, one_mul]
    have h4 : a * b * b = a := by rw [mul_assoc, hb, mul_one]
    have h5 : a * b * (a * b) = 1 := by rw [← mul_assoc, h3, hb]
    have h6 : b * a = a * b := hab.symm
    rintro x y (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl) <;>
      simp [ha, hb, h1, h2, h3, h4, h5, h6]
  inv_mem' := by
    have h5 : a * b * (a * b) = 1 := by
      rw [← mul_assoc, show a * b * a = b by rw [mul_assoc, ← hab, ← mul_assoc, ha, one_mul], hb]
    rintro x (rfl | rfl | rfl | rfl)
    · simp
    · exact Or.inr (Or.inl (inv_eq_of_mul_eq_one_right ha))
    · exact Or.inr (Or.inr (Or.inl (inv_eq_of_mul_eq_one_right hb)))
    · exact Or.inr (Or.inr (Or.inr (inv_eq_of_mul_eq_one_right h5)))

theorem mem_kleinSub {G : Type*} [Group G] {a b : G} {ha : a * a = 1} {hb : b * b = 1}
    {hab : a * b = b * a} {x : G} :
    x ∈ kleinSub a b ha hb hab ↔ x = 1 ∨ x = a ∨ x = b ∨ x = a * b := Iff.rfl

@[expose] noncomputable def zP (hU : UnitaryFieldData p f K) : PSU3 p f K :=
  QuotientGroup.mk (zS hU)

@[expose] noncomputable def swP (hU : UnitaryFieldData p f K) : PSU3 p f K :=
  QuotientGroup.mk (swS hU)

theorem zP_mul_self (hU : UnitaryFieldData p f K) : zP hU * zP hU = 1 := by
  rw [zP, ← QuotientGroup.mk_mul, zS_mul_self, QuotientGroup.mk_one]

theorem swP_mul_self (hU : UnitaryFieldData p f K) : swP hU * swP hU = 1 := by
  rw [swP, ← QuotientGroup.mk_mul, swS_mul_self, QuotientGroup.mk_one]

theorem zP_mul_swP (hU : UnitaryFieldData p f K) : zP hU * swP hU = swP hU * zP hU := by
  rw [zP, swP, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, zS_mul_swS]

@[expose] noncomputable def V0P (hU : UnitaryFieldData p f K) : Subgroup (PSU3 p f K) :=
  kleinSub (zP hU) (swP hU) (zP_mul_self hU) (swP_mul_self hU) (zP_mul_swP hU)

@[expose] noncomputable def J12P (p f : ℕ) (K : Type) [Field K] : Subgroup (PSU3 p f K) :=
  (suStab K (p ^ f) 2).map (QuotientGroup.mk' (suScalars p f K))

end CFSG.Quasithin.E22S
