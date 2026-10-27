module

public import CFSG.RankThree.PartTwo.KFacts.HeringKS12Config
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434RemU43

public section

namespace CFSG.RankThree.PartTwo.KFacts

namespace HeringU4

open CFSG.LieType.Multipliers.U43 Matrix
open CFSG.Open (StatedSU)
open CFSG.RankThree.PartTwo.Sec4.Item434RemU43 (piU piU_eq_one_iff UX)

def xM : Matrix (Fin 4) (Fin 4) F9 :=
  !![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩;
    ⟨2, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩;
    ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 2⟩, ⟨2, 2⟩;
    ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 2⟩, ⟨1, 1⟩]

def xiM : Matrix (Fin 4) (Fin 4) F9 :=
  !![⟨1, 2⟩, ⟨2, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩;
    ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩;
    ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩;
    ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨1, 2⟩]

def yM : Matrix (Fin 4) (Fin 4) F9 :=
  !![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩;
    ⟨2, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩;
    ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩;
    ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨1, 2⟩]

def yiM : Matrix (Fin 4) (Fin 4) F9 :=
  !![⟨1, 2⟩, ⟨2, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩;
    ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩;
    ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 2⟩, ⟨2, 2⟩;
    ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 2⟩, ⟨1, 1⟩]

def tM : Matrix (Fin 4) (Fin 4) F9 :=
  !![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
    ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
    ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩;
    ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩]

def gM : Matrix (Fin 4) (Fin 4) F9 :=
  !![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩;
    ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩;
    ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
    ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]

def hM : Matrix (Fin 4) (Fin 4) F9 :=
  !![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩;
    ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 2⟩, ⟨0, 0⟩;
    ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩;
    ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]

noncomputable def mkSU (M : Matrix (Fin 4) (Fin 4) F9) (hd : M.det = 1)
    (hu : (M.map (· ^ 3))ᵀ * M = 1) : StatedSU 4 3 F9 :=
  ⟨GeneralLinearGroup.mk'' M (by rw [hd]; exact isUnit_one), Subgroup.subset_closure ⟨hd, hu⟩⟩

theorem SU_ext {a b : StatedSU 4 3 F9}
    (h : ((a : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9) =
      ((b : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9)) : a = b :=
  Subtype.ext (Units.ext h)

noncomputable def xS : StatedSU 4 3 F9 := mkSU xM (by decide +kernel) (by decide +kernel)

noncomputable def xiS : StatedSU 4 3 F9 := mkSU xiM (by decide +kernel) (by decide +kernel)

noncomputable def yS : StatedSU 4 3 F9 := mkSU yM (by decide +kernel) (by decide +kernel)

noncomputable def yiS : StatedSU 4 3 F9 := mkSU yiM (by decide +kernel) (by decide +kernel)

noncomputable def tS : StatedSU 4 3 F9 := mkSU tM (by decide +kernel) (by decide +kernel)

noncomputable def gS : StatedSU 4 3 F9 := mkSU gM (by decide +kernel) (by decide +kernel)

noncomputable def hS : StatedSU 4 3 F9 := mkSU hM (by decide +kernel) (by decide +kernel)

theorem xS_inv : xS⁻¹ = xiS :=
  inv_eq_of_mul_eq_one_right (by apply SU_ext; decide +kernel)

theorem yS_inv : yS⁻¹ = yiS :=
  inv_eq_of_mul_eq_one_right (by apply SU_ext; decide +kernel)

theorem gS_inv : gS⁻¹ = gS :=
  inv_eq_of_mul_eq_one_right (by apply SU_ext; decide +kernel)

theorem hS_inv : hS⁻¹ = hS :=
  inv_eq_of_mul_eq_one_right (by apply SU_ext; decide +kernel)

theorem xS_pow3 : xS ^ 3 = 1 := by
  rw [pow_three]; apply SU_ext; decide +kernel

theorem yS_pow3 : yS ^ 3 = 1 := by
  rw [pow_three]; apply SU_ext; decide +kernel

theorem tS_pow2 : tS ^ 2 = 1 := by
  rw [sq]; apply SU_ext; decide +kernel

theorem xS_yS_comm : xS * yS = yS * xS := by
  apply SU_ext; decide +kernel

theorem tS_xS_comm : tS * xS = xS * tS := by
  apply SU_ext; decide +kernel

theorem tS_yS_comm : tS * yS = yS * tS := by
  apply SU_ext; decide +kernel

theorem gS_xS_conj : gS * xS * gS⁻¹ = xS⁻¹ := by
  rw [gS_inv, xS_inv]; apply SU_ext; decide +kernel

theorem gS_yS_conj : gS * yS * gS⁻¹ = yS := by
  rw [gS_inv]; apply SU_ext; decide +kernel

theorem hS_yS_conj : hS * yS * hS⁻¹ = yS⁻¹ := by
  rw [hS_inv, yS_inv]; apply SU_ext; decide +kernel

theorem piU_ne_one_of_entry {a : StatedSU 4 3 F9} {i j : Fin 4} (hij : i ≠ j)
    (hne : ((a : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9) i j ≠ 0) : piU a ≠ 1 := by
  intro h
  obtain ⟨c, hc⟩ := piU_eq_one_iff.mp h
  apply hne
  have h2 := congrArg (fun G : GL (Fin 4) F9 =>
    ((G : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9) i j) hc
  simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_apply_ne _ hij] at h2
  exact h2.symm

theorem piU_ne_one_of_diag {a : StatedSU 4 3 F9} {i j : Fin 4}
    (hne : ((a : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9) i i ≠
      ((a : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9) j j) : piU a ≠ 1 := by
  intro h
  obtain ⟨c, hc⟩ := piU_eq_one_iff.mp h
  apply hne
  have hi := congrArg (fun G : GL (Fin 4) F9 =>
    ((G : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9) i i) hc
  have hj := congrArg (fun G : GL (Fin 4) F9 =>
    ((G : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9) j j) hc
  simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq]
    at hi hj
  rw [← hi, ← hj]

theorem piU_ne_of_entry {a b : StatedSU 4 3 F9} {i j : Fin 4} (hij : i ≠ j)
    (hne : (((a * b⁻¹ : StatedSU 4 3 F9) : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9) i j ≠ 0) :
    piU a ≠ piU b := by
  intro h
  apply piU_ne_one_of_entry hij hne
  rw [map_mul, map_inv, h, mul_inv_cancel]

theorem piU_x_ne_one : piU xS ≠ 1 :=
  piU_ne_one_of_entry (i := 0) (j := 1) (by decide) (by decide +kernel)

theorem piU_y_ne_one : piU yS ≠ 1 :=
  piU_ne_one_of_entry (i := 0) (j := 1) (by decide) (by decide +kernel)

theorem piU_t_ne_one : piU tS ≠ 1 :=
  piU_ne_one_of_diag (i := 0) (j := 2) (by decide +kernel)

theorem piU_y_ne_x : piU yS ≠ piU xS := by
  apply piU_ne_of_entry (i := 2) (j := 3) (by decide)
  rw [xS_inv]
  decide +kernel

theorem piU_y_ne_x_sq : piU yS ≠ piU xS ^ 2 := by
  rw [← map_pow]
  apply piU_ne_of_entry (i := 0) (j := 1) (by decide)
  rw [sq, _root_.mul_inv_rev, xS_inv]
  decide +kernel

theorem piU_x_pow3 : piU xS ^ 3 = 1 := by
  rw [← map_pow, xS_pow3, map_one]

theorem piU_y_pow3 : piU yS ^ 3 = 1 := by
  rw [← map_pow, yS_pow3, map_one]

theorem piU_xy_comm : piU xS * piU yS = piU yS * piU xS := by
  rw [← map_mul, ← map_mul, xS_yS_comm]

theorem piU_gx : piU gS * piU xS * (piU gS)⁻¹ = (piU xS)⁻¹ := by
  simpa only [map_mul, map_inv] using congrArg piU gS_xS_conj

theorem piU_gy : piU gS * piU yS * (piU gS)⁻¹ = piU yS := by
  simpa only [map_mul, map_inv] using congrArg piU gS_yS_conj

theorem piU_hy : piU hS * piU yS * (piU hS)⁻¹ = (piU yS)⁻¹ := by
  simpa only [map_mul, map_inv] using congrArg piU hS_yS_conj

theorem piU_t2 : piU tS ^ 2 = 1 := by
  rw [← map_pow, tS_pow2, map_one]

theorem piU_tx : piU tS * piU xS = piU xS * piU tS := by
  rw [← map_mul, ← map_mul, tS_xS_comm]

theorem piU_ty : piU tS * piU yS = piU yS * piU tS := by
  rw [← map_mul, ← map_mul, tS_yS_comm]

theorem ks12ConfigN_UX : KS12ConfigN UX :=
  KS12ConfigN.of_involution piU_x_pow3 piU_y_pow3 piU_xy_comm piU_x_ne_one piU_y_ne_one
    piU_y_ne_x piU_y_ne_x_sq piU_gx piU_gy piU_hy piU_t_ne_one piU_t2 piU_tx piU_ty

end HeringU4

open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.RankThree.PartTwo.Sec4.Item434RemU43 (projSUEquivUX)

theorem ks12ConfigN_projSU : KS12ConfigN (projSU 4 3 1) :=
  KS12ConfigN.of_mulEquiv projSUEquivUX.symm HeringU4.ks12ConfigN_UX

theorem ks12CoverU4 : KS12CoverU4 := by
  intro X _ _ _ hZ he
  obtain ⟨e⟩ := he
  exact ks12Concl_of_configN hZ e ks12ConfigN_projSU

end CFSG.RankThree.PartTwo.KFacts
