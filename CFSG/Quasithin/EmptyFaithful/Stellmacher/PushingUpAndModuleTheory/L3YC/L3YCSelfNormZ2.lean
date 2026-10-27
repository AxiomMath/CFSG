module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.GL3TwoOrder
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.MkOfDetNeZero

public section

namespace CFSG.Quasithin

namespace Stellmacher.PU.L3YC

open Matrix
open scoped Pointwise

abbrev G3 : Type := Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)

def LowerZ (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) : Prop :=
  M 1 0 = 0 ∧ M 2 0 = 0 ∧ M 2 1 = 0

instance (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) : Decidable (LowerZ M) :=
  inferInstanceAs (Decidable (M 1 0 = 0 ∧ M 2 0 = 0 ∧ M 2 1 = 0))

def xM : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 1, 0; 0, 1, 0; 0, 0, 1]

def yM : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 0; 0, 1, 1; 0, 0, 1]

theorem selfnorm_decide : ∀ M : Matrix (Fin 3) (Fin 3) (ZMod 2), M.det = 1 →
    LowerZ (M * xM * M.adjugate) → LowerZ (M * yM * M.adjugate) → LowerZ M := by
  decide +kernel

theorem adjugate_lowerZ : ∀ M : Matrix (Fin 3) (Fin 3) (ZMod 2), M.det = 1 →
    LowerZ M → LowerZ M.adjugate := by
  decide +kernel

theorem card_lowerZ : (Finset.univ.filter
    (fun M : Matrix (Fin 3) (Fin 3) (ZMod 2) => M.det = 1 ∧ LowerZ M)).card = 8 := by
  decide +kernel

theorem det_eq_one_of_unit (g : G3) : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).det = 1 := by
  have h := ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero
  generalize (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).det = a at h ⊢
  fin_cases a
  · exact absurd rfl h
  · rfl

theorem coe_inv_eq_adjugate (g : G3) :
    ((g⁻¹ : G3) : Matrix (Fin 3) (Fin 3) (ZMod 2)) = (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).adjugate := by
  rw [Matrix.GeneralLinearGroup.coe_inv, Matrix.inv_def, det_eq_one_of_unit, Ring.inverse_one,
    one_smul]

def Uthree : Subgroup G3 where
  carrier := {g | LowerZ (g : Matrix (Fin 3) (Fin 3) (ZMod 2))}
  mul_mem' := by
    rintro a b ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩
    refine ⟨?_, ?_, ?_⟩ <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, a1, a2, a3, b1, b2, b3]
  one_mem' := by
    refine ⟨?_, ?_, ?_⟩ <;> simp
  inv_mem' := by
    intro g hg
    show LowerZ ((g⁻¹ : G3) : Matrix (Fin 3) (Fin 3) (ZMod 2))
    rw [coe_inv_eq_adjugate]
    exact adjugate_lowerZ _ (det_eq_one_of_unit g) hg

theorem mem_Uthree {g : G3} : g ∈ Uthree ↔ LowerZ (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
  Iff.rfl

theorem card_Uthree : Nat.card Uthree = 8 := by
  have e : Uthree ≃ {M : Matrix (Fin 3) (Fin 3) (ZMod 2) // M.det = 1 ∧ LowerZ M} :=
    { toFun := fun g => ⟨(g.1 : Matrix (Fin 3) (Fin 3) (ZMod 2)), det_eq_one_of_unit g.1, g.2⟩
      invFun := fun M => ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M.1 (by rw [M.2.1]; decide),
        by
          show LowerZ ((Matrix.GeneralLinearGroup.mkOfDetNeZero M.1 _ : G3) :
            Matrix (Fin 3) (Fin 3) (ZMod 2))
          simpa using M.2.2⟩
      left_inv := fun g => Subtype.ext (Units.ext (by simp))
      right_inv := fun M => Subtype.ext (by simp) }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact card_lowerZ

def gx : G3 := Matrix.GeneralLinearGroup.mkOfDetNeZero xM (by decide)

def gy : G3 := Matrix.GeneralLinearGroup.mkOfDetNeZero yM (by decide)

theorem gx_mem : gx ∈ Uthree := by
  show LowerZ xM
  decide

theorem gy_mem : gy ∈ Uthree := by
  show LowerZ yM
  decide

theorem mem_Uthree_of_normalizes {g : G3} (h : ∀ x ∈ Uthree, g * x * g⁻¹ ∈ Uthree) :
    g ∈ Uthree := by
  have h1 := h gx gx_mem
  have h2 := h gy gy_mem
  rw [mem_Uthree, Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
    coe_inv_eq_adjugate] at h1 h2
  have ex : ((gx : G3) : Matrix (Fin 3) (Fin 3) (ZMod 2)) = xM := rfl
  have ey : ((gy : G3) : Matrix (Fin 3) (Fin 3) (ZMod 2)) = yM := rfl
  rw [ex] at h1
  rw [ey] at h2
  exact selfnorm_decide _ (det_eq_one_of_unit g) h1 h2

theorem selfNormalizing_of_card_eight (P : Subgroup G3) (hP : Nat.card P = 8) {g : G3}
    (h : ∀ x ∈ P, g * x * g⁻¹ ∈ P) : g ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hG : Nat.card G3 = 168 :=
    CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.card_GL_three_two
  have hf : (Nat.card G3).factorization 2 = 3 := by
    rw [hG]; decide +kernel
  let SP : Sylow 2 G3 := Sylow.ofCard P (by rw [hf, hP]; norm_num)
  let SU : Sylow 2 G3 := Sylow.ofCard Uthree (by rw [hf, card_Uthree]; norm_num)
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq G3 SU SP
  have hmem : ∀ x : G3, x ∈ P ↔ a⁻¹ * x * a ∈ Uthree := by
    intro x
    have hP' : (P : Subgroup G3) = MulAut.conj a • (Uthree : Subgroup G3) :=
      (congrArg (fun Q : Sylow 2 G3 => (Q : Subgroup G3)) ha).symm
    rw [hP', Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp [MulAut.smul_def, mul_assoc]
  rw [hmem]
  apply mem_Uthree_of_normalizes
  intro x hx
  have hx' : a * x * a⁻¹ ∈ P := by rw [hmem]; simpa [mul_assoc] using hx
  have := (hmem _).mp (h _ hx')
  simpa [mul_assoc] using this

end Stellmacher.PU.L3YC

end CFSG.Quasithin
