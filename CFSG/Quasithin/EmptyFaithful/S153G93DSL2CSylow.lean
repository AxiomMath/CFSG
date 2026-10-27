module

public import CFSG.Quasithin.EmptyFaithful.SBc17SL2Defs
public import Mathlib.GroupTheory.PGroup
import CFSG.Quasithin.EmptyFaithful.SBc17SL2Syl
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.Sylow
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public section

namespace CFSG.Quasithin

namespace S153G93D

namespace SL2C

open SBc17

open scoped Pointwise

variable {F : Type} [Field F]

theorem card_SL2 [Fintype F] : Nat.card (SL2 F) = Fintype.card F * (Fintype.card F ^ 2 - 1) := by
  have h := Matrix.card_SL_mul_card_units (n := Fin 2) (R := F)
  rw [Matrix.card_GL_field, Nat.card_units, Nat.card_eq_fintype_card (α := F)] at h
  simp only [Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one] at h
  have hq : 2 ≤ Fintype.card F := Fintype.one_lt_card
  have hq1 : 0 < Fintype.card F - 1 := by omega
  apply Nat.eq_of_mul_eq_mul_right hq1
  rw [h, show Fintype.card F ^ 2 - Fintype.card F = Fintype.card F * (Fintype.card F - 1) by
    rw [Nat.mul_sub_one, sq]]
  ring

theorem isSylow_upperSub [Finite F] [CharP F 2] :
    IsPGroup 2 (upperSub F) ∧ ¬ 2 ∣ (upperSub F).index := by
  have := Fintype.ofFinite F
  obtain ⟨⟨n, hn0⟩, -, hn⟩ := FiniteField.card F 2
  simp only [PNat.mk_coe] at hn
  have hcard : Nat.card (upperSub F) = 2 ^ n := by rw [card_upperSub, hn]
  refine ⟨IsPGroup.of_card hcard, ?_⟩
  have h := (upperSub F).index_mul_card
  rw [hcard, card_SL2, hn] at h
  have hpos : 0 < 2 ^ n := Nat.two_pow_pos n
  have hidx : (upperSub F).index = (2 ^ n) ^ 2 - 1 :=
    Nat.eq_of_mul_eq_mul_right hpos (by rw [h, mul_comm])
  rw [hidx, ← pow_mul]
  have h2 : 2 ∣ 2 ^ (n * 2) := dvd_pow_self 2 (by omega)
  have h1 : 1 ≤ 2 ^ (n * 2) := Nat.one_le_two_pow
  generalize 2 ^ (n * 2) = x at h1 h2
  omega

theorem exists_conj_upperSub [Finite F] [CharP F 2] {P : Subgroup (SL2 F)}
    (hP : IsPGroup 2 P) (hidx : ¬ 2 ∣ P.index) :
    ∃ g : SL2 F, ∀ x : SL2 F, x ∈ P ↔ g⁻¹ * x * g ∈ upperSub F := by
  obtain ⟨hU, hUidx⟩ := isSylow_upperSub (F := F)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SL2 F) (hU.toSylow hUidx) (hP.toSylow hidx)
  refine ⟨g, fun x => ?_⟩
  have hP' : (MulAut.conj g • upperSub F : Subgroup (SL2 F)) = P :=
    congrArg (fun S : Sylow 2 (SL2 F) => (S : Subgroup (SL2 F))) hg
  rw [← hP', Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  show (MulAut.conj g)⁻¹ x ∈ upperSub F ↔ _
  rw [MulAut.conj_inv_apply]

end SL2C

end S153G93D

end CFSG.Quasithin
