module

public import CFSG.LocalAnalysis.WeakClosure81.W16LKU3
public import CFSG.LocalAnalysis.WeakClosure81.SevenSixteenKFacts
import CFSG.ClassicalGroups.Unitary.ThreeEven

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open
open Subgroup

private theorem w16l_map_centralizer {X : Type} [Group X] (H : Subgroup X) (e : X ≃* X) :
    (Subgroup.centralizer (H : Set X)).map e.toMonoidHom =
      Subgroup.centralizer ((H.map e.toMonoidHom : Subgroup X) : Set X) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩ z hz
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
    rw [← map_mul, ← map_mul, hy w hw]
  · intro hx
    refine ⟨e.symm x, ?_, by simp⟩
    intro w hw
    apply e.injective
    have h := hx (e w) (Subgroup.mem_map_of_mem e.toMonoidHom hw)
    simpa [map_mul, e.apply_symm_apply] using h

private theorem w16l_sylowCenter_smul {X : Type} [Group X] (Q : Sylow 2 X) (g : X) :
    sylowCenter (g • Q) = conjSubgroup (sylowCenter Q) g⁻¹ := by
  have hcoe : ((g • Q : Sylow 2 X) : Subgroup X) =
      (Q : Subgroup X).map (MulAut.conj g).toMonoidHom := by
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  have hRHS : conjSubgroup (sylowCenter Q) g⁻¹ =
      (sylowCenter Q).map (MulAut.conj g).toMonoidHom := by
    rw [conjSubgroup, inv_inv]
  rw [hRHS, sylowCenter, hcoe, sylowCenter]
  rw [← w16l_map_centralizer (H := (Q : Subgroup X)) (e := MulAut.conj g)]
  exact (Subgroup.map_inf (Q : Subgroup X)
    (Subgroup.centralizer ((Q : Subgroup X) : Set X))
    (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm

theorem sylowCenter_conj_exists {X : Type} [Group X] (Q : Sylow 2 X) (g : X) :
    ∃ Q' : Sylow 2 X, (Q' : Subgroup X) = conjSubgroup (Q : Subgroup X) g ∧
      sylowCenter Q' = conjSubgroup (sylowCenter Q) g := by
  refine ⟨g⁻¹ • Q, ?_, ?_⟩
  · rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  · rw [w16l_sylowCenter_smul, inv_inv]

theorem exists_conj_eq_sylowCenter {X : Type} [Group X] [Finite X] (Q Q' : Sylow 2 X) :
    ∃ h : X, conjSubgroup (sylowCenter Q) h = sylowCenter Q' := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (Sylow 2 X) := Sylow.finite_of_finiteIndex Q
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X Q Q'
  refine ⟨g⁻¹, ?_⟩
  rw [← w16l_sylowCenter_smul Q g, hg]

section Certified


variable {P : Type} [Group P] [Finite P] {n : ℕ}

theorem IsPSUGp.isU3Shape (hP : IsPSUGp P 3 n) : IsU3Shape P n := by
  have hperf : Group.IsPerfect P := CFSG.ClassicalGroups.Unitary.isPerfect_of_lieModel_psu3 hP
  have hsimple : IsSimpleGroup P :=
    (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity P 3 2 n
      (CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hP)).2
  have hcenter : Subgroup.center P = ⊥ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center P) with h | h
    · exact h
    · exfalso
      have hbot : commutator P = ⊥ := (commutator_eq_bot_iff_center_eq_top P).mpr h
      have htop : commutator P = ⊤ := hperf.commutator_eq_top
      rw [hbot] at htop
      exact (bot_ne_top : (⊥ : Subgroup P) ≠ ⊤) htop
  have e : P ⧸ Subgroup.center P ≃* P :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot
  refine ⟨hperf.commutator_eq_top, ?_, ?_⟩
  · exact CFSG.Blueprint.LieModel.of_mulEquiv e.symm hP
  · rw [hcenter, Subgroup.card_bot]
    exact one_dvd 3

theorem IsPSUGp.exists_sylow_sylowCenter_eq (hP : IsPSUGp P 3 n) {R : Subgroup P}
    (hR : IsElemAbelian 2 R) (hcard : Nat.card R = 2 ^ n) :
    ∃ Q : Sylow 2 P, sylowCenter Q = R := by
  have hX : IsU3Shape P n := hP.isU3Shape
  obtain ⟨Q, hRQ⟩ := (IsPGroup.of_card hcard).exists_le_sylow
  refine ⟨Q, ?_⟩
  have hle : R ≤ sylowCenter Q := by
    intro x hx
    have hxx : x * x = 1 := by
      rw [← pow_two]
      exact hR.2 x hx
    exact (hX.mul_self_eq_one_iff Q (hRQ hx)).mp hxx
  have hcardle : Nat.card (sylowCenter Q) ≤ Nat.card R := by
    rw [hX.card_sylowCenter Q, hcard]
  exact (Subgroup.eq_of_le_of_card_ge hle hcardle).symm

theorem IsPSUGp.sylowCenter_injective (hP : IsPSUGp P 3 n) {Q Q' : Sylow 2 P}
    (h : sylowCenter Q = sylowCenter Q') : Q = Q' := by
  have hX : IsU3Shape P n := hP.isU3Shape
  by_contra hne
  have hTI : (Q : Subgroup P) ⊓ (Q' : Subgroup P) = ⊥ := hX.sylow_inf_eq_bot hne
  have hle : sylowCenter Q ≤ (Q : Subgroup P) ⊓ (Q' : Subgroup P) :=
    le_inf (by unfold sylowCenter; exact inf_le_left)
      (by rw [h]; unfold sylowCenter; exact inf_le_left)
  have hbot : sylowCenter Q = ⊥ := le_bot_iff.mp (hTI ▸ hle)
  have hcard := hX.card_sylowCenter Q
  rw [hbot, Subgroup.card_bot] at hcard
  have hge : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (two_le_of_isPSUGp hP)
  omega

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end
