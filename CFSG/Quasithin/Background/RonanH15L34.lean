module

public import CFSG.Quasithin.Background.HMathieuM21
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourExactModel
import all CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData

public section

namespace CFSG.Quasithin.RonanH15

open CFSG.ComponentClassification.PSL3Four Matrix CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin.H.Mathieu
open scoped MatrixGroups

theorem getD_V_ne_zero (i : Fin 21) : V.getD i 0 ≠ 0 := by
  have h := vecOf_ne_zero (⟨i, by omega⟩ : Fin 42)
  rwa [vecOf, Nat.mod_eq_of_lt i.2] at h

@[expose] def rho21Fun (A : GL (Fin 3) F4) (i : Fin 21) : Fin 21 :=
  ⟨vIdx ((A : Matrix (Fin 3) (Fin 3) F4) *ᵥ V.getD i 0), vIdx_lt _⟩

theorem rho21Fun_mul (A B : GL (Fin 3) F4) (i : Fin 21) :
    rho21Fun A (rho21Fun B i) = rho21Fun (A * B) i :=
  Fin.ext (vIdx_mulVec_mulVec A B (getD_V_ne_zero i))

theorem rho21Fun_one (i : Fin 21) : rho21Fun 1 i = i := by
  apply Fin.ext
  have h := vIdx_vecOf (⟨i, by omega⟩ : Fin 42)
  rw [vecOf, Nat.mod_eq_of_lt i.2] at h
  simp only [rho21Fun, Units.val_one, Matrix.one_mulVec]
  exact h

@[expose] noncomputable def rho21 : GL (Fin 3) F4 →* Equiv.Perm (Fin 21) where
  toFun A :=
    { toFun := rho21Fun A
      invFun := rho21Fun A⁻¹
      left_inv := fun i => by rw [rho21Fun_mul, inv_mul_cancel, rho21Fun_one]
      right_inv := fun i => by rw [rho21Fun_mul, mul_inv_cancel, rho21Fun_one] }
  map_one' := Equiv.ext rho21Fun_one
  map_mul' A B := Equiv.ext fun i => (rho21Fun_mul A B i).symm

@[expose] noncomputable def rho21SL : SpecialLinearGroup (Fin 3) F4 →* Equiv.Perm (Fin 21) :=
  rho21.comp SpecialLinearGroup.toGL

theorem rho21Fun_scalar {B : GL (Fin 3) F4} {c : F4} (hc : c ≠ 0)
    (hB : (B : Matrix (Fin 3) (Fin 3) F4) = scalar (Fin 3) c) (i : Fin 21) : rho21Fun B i = i := by
  apply Fin.ext
  have h := vIdx_vecOf (⟨i, by omega⟩ : Fin 42)
  rw [vecOf, Nat.mod_eq_of_lt i.2] at h
  have e : (scalar (Fin 3) c) *ᵥ V.getD i 0 = c • V.getD i 0 := by
    funext k
    rw [scalar_apply, mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  simp only [rho21Fun]
  rw [hB, e, vIdx_smul hc]
  exact h

theorem scalars_le_ker_rho21 : LinearFlag.scalars 3 F4 ≤ rho21SL.ker := by
  intro A hA
  obtain ⟨c, -, hAc⟩ := LinearFlag.mem_scalars.1 hA
  rw [MonoidHom.mem_ker]
  exact Equiv.ext fun i => rho21Fun_scalar c.ne_zero hAc i

theorem card_range_rho21_le : Nat.card rho21SL.range ≤ 20160 := by
  have h := Subgroup.card_ker_mul_card_range rho21SL
  rw [card_SL] at h
  have h2 : 3 ≤ Nat.card rho21SL.ker :=
    card_scalars.symm.le.trans (Subgroup.card_le_of_le scalars_le_ker_rho21)
  nlinarith

abbrev sigma21 : Equiv.Perm (Fin 21) :=
  List.formPerm [9, 12] * List.formPerm [10, 11] * List.formPerm [13, 15] *
    List.formPerm [14, 16] * List.formPerm [17, 18] * List.formPerm [19, 20]

@[expose] def matA : SpecialLinearGroup (Fin 3) F4 :=
  ⟨!![⟨1⟩, ⟨0⟩, ⟨0⟩; ⟨3⟩, ⟨3⟩, ⟨1⟩; ⟨1⟩, ⟨3⟩, ⟨3⟩], by
    rw [Matrix.det_fin_three]
    decide⟩

@[expose] def matB : SpecialLinearGroup (Fin 3) F4 :=
  ⟨!![⟨1⟩, ⟨3⟩, ⟨2⟩; ⟨0⟩, ⟨2⟩, ⟨3⟩; ⟨0⟩, ⟨1⟩, ⟨1⟩], by
    rw [Matrix.det_fin_three]
    decide⟩

theorem sigma21_conj_a : sigma21 * m21gA * sigma21⁻¹ = rho21SL matA := by
  refine Equiv.ext fun i => ?_
  revert i
  decide +kernel

theorem sigma21_conj_b : sigma21 * m21gB * sigma21⁻¹ = rho21SL matB := by
  refine Equiv.ext fun i => ?_
  revert i
  decide +kernel

theorem map_conj_M21nat_le :
    M21nat.map (MulAut.conj sigma21).toMonoidHom ≤ rho21SL.range := by
  rw [M21nat, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨g, hg, rfl⟩
  rcases hg with rfl | rfl
  · exact ⟨matA, sigma21_conj_a.symm⟩
  · exact ⟨matB, sigma21_conj_b.symm⟩

theorem map_conj_M21nat_eq :
    M21nat.map (MulAut.conj sigma21).toMonoidHom = rho21SL.range := by
  refine Subgroup.eq_of_le_of_card_ge map_conj_M21nat_le ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj sigma21).injective, card_M21nat]
  exact card_range_rho21_le

theorem ker_rho21_eq_center :
    rho21SL.ker = Subgroup.center (SpecialLinearGroup (Fin 3) F4) := by
  rw [← LinearFlag.scalars_eq_center 3 F4]
  refine (Subgroup.eq_of_le_of_card_ge scalars_le_ker_rho21 ?_).symm
  have h := Subgroup.card_ker_mul_card_range rho21SL
  have h1 : Nat.card rho21SL.range = 20160 := by
    rw [← map_conj_M21nat_eq, Subgroup.card_map_of_injective (MulAut.conj sigma21).injective,
      card_M21nat]
  rw [card_SL, h1] at h
  have hk : Nat.card rho21SL.ker ≤ 3 := by omega
  rw [card_scalars]
  exact hk

@[expose] noncomputable def M21natEquivPSL :
    ↥M21nat ≃* PSL(3, F4) :=
  ((M21nat.equivMapOfInjective _ (MulAut.conj sigma21).injective).trans
    ((MulEquiv.subgroupCongr map_conj_M21nat_eq).trans
      (QuotientGroup.quotientKerEquivRange rho21SL).symm)).trans
    (QuotientGroup.quotientMulEquivOfEq ker_rho21_eq_center)

theorem nonempty_mog21_equiv_PSL :
    Nonempty (↥mog21 ≃* PSL(3, F4)) :=
  ⟨mog21EquivM21nat.trans M21natEquivPSL⟩

end CFSG.Quasithin.RonanH15
