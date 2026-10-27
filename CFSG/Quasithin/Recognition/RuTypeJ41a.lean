module

public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Recognition.RuTypeJ27d

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped MatrixGroups

namespace SL3

@[expose] def Pl : Subgroup SL(3, ZMod 2) where
  carrier := {g | mat g 2 0 = 0 ∧ mat g 2 1 = 0}
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    simp only [Set.mem_ofPred_eq, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_three]
    simp [ha1, ha2, hb1, hb2]
  one_mem' := by simp
  inv_mem' := by
    rintro a ⟨ha1, ha2⟩
    simp only [Set.mem_ofPred_eq, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_three]
    simp [ha1, ha2]

instance : DecidablePred (· ∈ Pl) := fun g =>
  inferInstanceAs (Decidable (mat g 2 0 = 0 ∧ mat g 2 1 = 0))

theorem card_Pl : Nat.card Pl = 24 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem P0_le_Pl : P0 ≤ Pl := by
  intro g hg
  revert g
  decide +kernel

@[expose] def R2m : Subgroup SL(3, ZMod 2) where
  carrier := {g | mat g 0 0 = 1 ∧ mat g 0 1 = 0 ∧ mat g 1 0 = 0 ∧ mat g 1 1 = 1 ∧
    mat g 2 0 = 0 ∧ mat g 2 1 = 0 ∧ mat g 2 2 = 1}
  mul_mem' := by
    rintro a b ⟨ha1, ha2, ha3, ha4, ha5, ha6, ha7⟩ ⟨hb1, hb2, hb3, hb4, hb5, hb6, hb7⟩
    simp only [Set.mem_ofPred_eq, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_three]
    simp [ha1, ha2, ha3, ha4, ha5, ha6, ha7, hb1, hb2, hb3, hb4, hb5, hb6, hb7]
  one_mem' := by simp
  inv_mem' := by
    rintro a ⟨ha1, ha2, ha3, ha4, ha5, ha6, ha7⟩
    simp only [Set.mem_ofPred_eq, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_three]
    simp [ha1, ha2, ha3, ha4, ha5, ha6, ha7]

instance : DecidablePred (· ∈ R2m) := fun g =>
  inferInstanceAs (Decidable (mat g 0 0 = 1 ∧ mat g 0 1 = 0 ∧ mat g 1 0 = 0 ∧ mat g 1 1 = 1 ∧
    mat g 2 0 = 0 ∧ mat g 2 1 = 0 ∧ mat g 2 2 = 1))

theorem card_R2m : Nat.card R2m = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem R2m_le_Pl : R2m ≤ Pl := by
  intro g hg
  revert g
  decide +kernel

theorem R2m_le_P0 : R2m ≤ P0 := by
  intro g hg
  revert g
  decide +kernel

theorem conj_mem_R2m : ∀ g ∈ Pl, ∀ x ∈ R2m, g * x * g⁻¹ ∈ R2m := by
  decide +kernel

theorem Pl_plane : ∀ g ∈ Pl, ∀ y : Fin 3 → ZMod 2, y 2 = 0 → (natAct3 g y) 2 = 0 := by
  decide +kernel

@[expose] def gpl : SL(3, ZMod 2) := ⟨!![0, 1, 0; 1, 0, 0; 0, 0, 1], by decide⟩

theorem gpl_mem_Pl : gpl ∈ Pl := by decide

theorem gpl_not_mem_Stab0 : gpl ∉ Stab0 := by decide

theorem natAct3_gpl_e0 : natAct3 gpl e0 = ![0, 1, 0] := by decide

end SL3

namespace RuDataM

variable {G : Type} [Group G] (M : RuDataM G)

noncomputable abbrev G2 : Subgroup G := pullL M.L M.θ SL3.Pl

noncomputable abbrev R2 : Subgroup G := pullL M.L M.θ SL3.R2m

theorem card_G2 : Nat.card M.G2 = 2 ^ 11 * 24 := by
  rw [M.card_pullL, SL3.card_Pl]

theorem card_R2 : Nat.card M.R2 = 2 ^ 13 := by
  rw [M.card_pullL, SL3.card_R2m]
  norm_num

theorem R2_le_G2 : M.R2 ≤ M.G2 := fun x hx => by
  obtain ⟨h, hx⟩ := mem_pullL.mp hx
  exact mem_pullL.mpr ⟨h, SL3.R2m_le_Pl hx⟩

theorem S_le_R2 : ruS M.L ≤ M.R2 := M.S_le_pullL _

@[expose] noncomputable def gel : M.L := (M.θ_surj SL3.gpl).choose

theorem θ_gel : M.θ M.gel = SL3.gpl := (M.θ_surj SL3.gpl).choose_spec

theorem gel_mem_G2 : (M.gel : G) ∈ M.G2 :=
  mem_pullL.mpr ⟨M.gel.2, by rw [M.θ_gel]; exact SL3.gpl_mem_Pl⟩

theorem gel_not_mem_LT1 : (M.gel : G) ∉ M.LT1 := by
  intro h
  obtain ⟨h1, h2⟩ := mem_pullL.mp h
  apply SL3.gpl_not_mem_Stab0
  rw [← M.θ_gel]
  exact h2

noncomputable abbrev Ual : Subgroup G := M.conjU (M.gel : G)

variable [Finite G]

theorem T_le_G2 : (M.T : Subgroup G) ≤ M.G2 := fun _ ht =>
  mem_pullL.mpr ⟨M.toRuData.T_le_L ht, SL3.P0_le_Pl (M.toRuDataN.θ_mem_P0 ht _)⟩

theorem Ual_ne_U : M.Ual ≠ ruU M.L M.T := fun h =>
  M.gel_not_mem_LT1 ((M.conjU_eq_U_iff M.gel.2).mp h)

theorem Ual_le_S : M.Ual ≤ ruS M.L := M.conjU_le_S M.gel.2

theorem card_Ual : Nat.card M.Ual = 32 := by
  rw [M.card_conjU, M.toRuData.card_U]

theorem card_Ual_inf_Q : Nat.card ↥(M.Ual ⊓ ruQ M.T) = 16 :=
  M.card_conjU_inf_Q M.gel.2 M.Ual_ne_U

theorem exists_Ual_not_Q : ∃ v ∈ M.Ual, v ∉ ruQ M.T := by
  by_contra h
  push Not at h
  have hle : M.Ual ≤ M.Ual ⊓ ruQ M.T := fun x hx => ⟨hx, h x hx⟩
  have := Subgroup.card_le_of_le hle
  rw [M.card_Ual, M.card_Ual_inf_Q] at this
  norm_num at this

@[expose] noncomputable def vel : G := M.exists_Ual_not_Q.choose

theorem vel_mem_Ual : M.vel ∈ M.Ual := M.exists_Ual_not_Q.choose_spec.1

theorem vel_not_mem_Q : M.vel ∉ ruQ M.T := M.exists_Ual_not_Q.choose_spec.2

theorem vel_mem_S : M.vel ∈ ruS M.L := M.Ual_le_S M.vel_mem_Ual

theorem vel_mem_T : M.vel ∈ (M.T : Subgroup G) := M.toRuData.S_le_T M.vel_mem_S

theorem vel_mem_H : M.vel ∈ ruH M.T := M.toRuData.T_le_H M.vel_mem_T

theorem vel_mem_K : M.vel ∈ M.K := M.S_le_K M.vel_mem_S

theorem vel_mul_self : M.vel * M.vel = 1 := by
  have h0 : (M.gel : G)⁻¹ * M.vel * M.gel ∈ ruU M.L M.T := M.mem_conjU.mp M.vel_mem_Ual
  have h := M.U_sq h0
  have e : M.vel * M.vel = (M.gel : G) * (((M.gel : G)⁻¹ * M.vel * M.gel) ^ 2) * (M.gel : G)⁻¹ := by
    rw [pow_two]; group
  rw [e, h]
  group

theorem exists_inv_five_of_K {w : G} (hwH : w ∈ ruH M.T) (hwK : w ∈ M.K) (hwQ : w ∉ ruQ M.T)
    (hw2 : w * w = 1) : ∃ x ∈ ruH M.T, orderOf x = 5 ∧ w * x * w⁻¹ = x⁻¹ := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
  have hφw : M.φ ⟨w, hwH⟩ ^ 2 = 1 ∧ M.φ ⟨w, hwH⟩ ≠ 1 ∧ (M.φ ⟨w, hwH⟩).right = 1 := by
    refine ⟨?_, fun h1 => hwQ ?_, ?_⟩
    · rw [← map_pow]
      have : (⟨w, hwH⟩ : ruH M.T) ^ 2 = 1 := Subtype.ext (by rw [pow_two]; exact hw2)
      rw [this, map_one]
    · have hk : (⟨w, hwH⟩ : ruH M.T) ∈ M.φ.ker := h1
      rw [M.φ_ker, Subgroup.mem_subgroupOf] at hk
      exact hk
    · obtain ⟨hk, hk1⟩ := M.mem_K_iff.mp hwK
      exact hk1
  obtain ⟨g, hg5, hg1⟩ := Sigma.exists_conj_mul_order_five _ hφw
  obtain ⟨h, hh⟩ := M.φ_surj g
  set y : G := w * ((h : G) * w * (h : G)⁻¹)
  have hyH : y ∈ ruH M.T := mul_mem hwH (mul_mem (mul_mem h.2 hwH) (inv_mem h.2))
  have hφy : M.φ ⟨y, hyH⟩ = M.φ ⟨w, hwH⟩ * (g * M.φ ⟨w, hwH⟩ * g⁻¹) := by
    have e : (⟨y, hyH⟩ : ruH M.T) = ⟨w, hwH⟩ * (h * ⟨w, hwH⟩ * h⁻¹) := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, hh]
  have hy5Q : y ^ 5 ∈ ruQ M.T := by
    have hk : (⟨y, hyH⟩ : ruH M.T) ^ 5 ∈ M.φ.ker := by
      rw [MonoidHom.mem_ker, map_pow, hφy, hg5]
    rw [M.φ_ker, Subgroup.mem_subgroupOf] at hk
    simpa using hk
  set x : G := y ^ (2 ^ 11)
  have hxH : x ∈ ruH M.T := pow_mem hyH _
  have hx5 : orderOf x = 5 := by
    refine orderOf_eq_prime ?_ ?_
    · have h1 : (y ^ 5) ^ (2 ^ 11) = 1 := by
        have := pow_card_eq_one' (G := ruQ M.T) (x := ⟨_, hy5Q⟩)
        rw [M.toRuData.card_Q] at this
        exact congrArg Subtype.val this
      rw [← pow_mul, mul_comm, pow_mul] at h1
      exact h1
    · intro h1
      apply hg1
      have hφx : M.φ ⟨x, hxH⟩ = (M.φ ⟨y, hyH⟩) ^ (2 ^ 11) := by
        rw [← map_pow]
        rfl
      have h2 : (M.φ ⟨y, hyH⟩) ^ (2 ^ 11) = 1 := by
        rw [← hφx, show (⟨x, hxH⟩ : ruH M.T) = 1 from Subtype.ext h1, map_one]
      have h3 : (M.φ ⟨y, hyH⟩) ^ 5 = 1 := by rw [hφy, hg5]
      have hgcd := (pow_gcd_eq_one (a := M.φ ⟨y, hyH⟩)).mpr ⟨h3, h2⟩
      rw [show Nat.gcd 5 (2 ^ 11) = 1 by norm_num, pow_one] at hgcd
      rw [← hφy]
      exact hgcd
  have hinvy : w * y * w⁻¹ = y⁻¹ := by
    simp only [y]
    rw [hwi]
    calc w * (w * ((h : G) * w * (h : G)⁻¹)) * w = (w * w) * ((h : G) * w * (h : G)⁻¹) * w := by
          group
      _ = (h : G) * w * (h : G)⁻¹ * w := by rw [hw2, one_mul]
      _ = (w * ((h : G) * w * (h : G)⁻¹))⁻¹ := by
          simp only [mul_inv_rev, inv_inv, hwi]
          group
  refine ⟨x, hxH, hx5, ?_⟩
  simp only [x]
  rw [← conj_pow, hinvy, inv_pow]

theorem exists_b5el : ∃ x ∈ ruH M.T, orderOf x = 5 ∧ M.vel * x * M.vel⁻¹ = x⁻¹ :=
  M.exists_inv_five_of_K M.vel_mem_H M.vel_mem_K M.vel_not_mem_Q M.vel_mul_self

@[expose] noncomputable def b5el : G := M.exists_b5el.choose

theorem b5el_mem_H : M.b5el ∈ ruH M.T := M.exists_b5el.choose_spec.1

theorem orderOf_b5el : orderOf M.b5el = 5 := M.exists_b5el.choose_spec.2.1

theorem vel_inv_b5el : M.vel * M.b5el * M.vel⁻¹ = M.b5el⁻¹ := M.exists_b5el.choose_spec.2.2

end RuDataM

end CFSG.Quasithin.RuType
