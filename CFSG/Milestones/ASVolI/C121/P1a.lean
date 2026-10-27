module

public import CFSG.Milestones.ASVolI.C121.J
public import CFSG.Milestones.ASVolI.C121.MP

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC CFSG.LieType.BorelTits
open scoped MatrixGroups

theorem burnsideC121_exists_autIEquiv {Ω : Type} [Group Ω] {Y V : Subgroup Ω}
    (hV : IsElemAbelian 2 V) (hYN : Y ≤ Subgroup.normalizer (V : Set Ω)) {F : Type} [Field F]
    (α : ↥Y →* SL(2, F)) (hαs : Function.Surjective α)
    (hker : α.ker = (Y ⊓ Subgroup.centralizer (V : Set Ω)).subgroupOf Y) :
    ∃ e : ↥(autI hV Y) ≃* SL(2, F), ∀ y : ↥Y,
      e ⟨convHom hV Y hYN y, (range_convHom hV Y hYN) ▸ ⟨y, rfl⟩⟩ = α y := by
  set φ := convHom hV Y hYN with hφ
  have hkφ : φ.ker = α.ker := by rw [ker_convHom, hker]
  let e1 : ↥(autI hV Y) ≃* ↥φ.range := MulEquiv.subgroupCongr (range_convHom hV Y hYN).symm
  let e2 : ↥φ.range ≃* ↥Y ⧸ φ.ker := (QuotientGroup.quotientKerEquivRange φ).symm
  let e3 : (↥Y ⧸ φ.ker) ≃* ↥Y ⧸ α.ker := QuotientGroup.quotientMulEquivOfEq hkφ
  let e4 : (↥Y ⧸ α.ker) ≃* SL(2, F) := QuotientGroup.quotientKerEquivOfSurjective α hαs
  refine ⟨e1.trans (e2.trans (e3.trans e4)), fun y => ?_⟩
  have h2 : e2 ⟨φ y, ⟨y, rfl⟩⟩ = (y : ↥Y ⧸ φ.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  show e4 (e3 (e2 (e1 _))) = α y
  have h1 : e1 ⟨φ y, (range_convHom hV Y hYN) ▸ ⟨y, rfl⟩⟩ = ⟨φ y, ⟨y, rfl⟩⟩ := rfl
  rw [h1, h2]
  rfl

namespace burnsideC121_YCtx

variable {Ω : Type} [Group Ω] [Finite Ω] {X R T Y W : Subgroup Ω}
  (c : burnsideC121_YCtx X R T Y W) {n : ℕ} {F : Type} [Field F] [Fintype F]
  (D : burnsideC121_NatD Y W n F)

include c D

theorem alpha_surjective (hn : 2 ≤ n) : Function.Surjective D.α := by
  have h4 : 4 ≤ Nat.card F := by
    rw [Nat.card_eq_fintype_card, D.card]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  rw [← MonoidHom.range_eq_top, D.αr, CFSG.Quasithin.C126.Nat.commutator_sl2_eq_top h4]

theorem alpha_ker_eq : D.α.ker = (Y ⊓ Subgroup.centralizer (W : Set Ω)).subgroupOf Y := by
  rw [c.inf_centralizer_W D, D.αk]

theorem exists_autIEquiv_W (hn : 2 ≤ n) : Nonempty (↥(autI c.W_elem Y) ≃* SL(2, F)) := by
  obtain ⟨e, -⟩ := burnsideC121_exists_autIEquiv c.W_elem c.Y_le_normalizer_W D.α
    (c.alpha_surjective D hn) (c.alpha_ker_eq D)
  exact ⟨e⟩

theorem relIndex_pCore_three (hn : n = 1) : (pCoreOf 2 Y).relIndex Y = 3 := by
  have h1 : (pCoreOf 2 Y).relIndex Y = Nat.card D.α.range := by
    rw [Subgroup.relIndex, ← D.αk, Subgroup.index_ker]
  rw [h1, D.αr]
  exact burnsideC121_card_commutator_sl2_two (by rw [D.card, hn]; rfl)

theorem RY_eq_pCore (hn : n = 1) : R ⊓ Y = pCoreOf 2 Y :=
  CFSG.Quasithin.C124.Z3.eq_of_relIndex_three_of_isPGroup c.pCore_Y_le_RY inf_le_right
    (c.relIndex_pCore_three D hn) (c.R_pGroup.to_le inf_le_left)

omit D in
theorem not_le_normalizer_P (hYS : ¬ Y ≤ Subgroup.normalizer (baum T : Set Ω)) :
    ¬ Y ≤ Subgroup.normalizer (burnsideC121_P X R T Y : Set Ω) := fun h =>
  hYS (c.baum_P ▸ h.trans (normalizer_le_normalizer_baum _))

theorem minParabolic_H (hYS : ¬ Y ≤ Subgroup.normalizer (baum T : Set Ω)) :
    ∃ M : Subgroup Ω, MinParabolic (burnsideC121_H X T Y) (burnsideC121_P X R T Y) M := by
  rw [c.H_eq]
  have hsyl : IsSylowTwoOf (burnsideC121_P X R T Y ⊓ Y) Y := by
    rw [c.P_inf_Y]; exact c.hY.sylow
  by_cases hn : 2 ≤ n
  · obtain ⟨e⟩ := c.exists_autIEquiv_W D hn
    have hF : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, D.card]
    exact burnsideC121_minParabolic_of_sl2 c.W_elem c.Y_le_normalizer_W c.P_le_normalizer_W
      c.P_pGroup c.P_le_normalizer hsyl (by rw [c.inf_centralizer_W D]; exact c.pCore_Y_le_P)
      hn hF e (c.not_le_normalizer_P hYS)
  · have hn1 : n = 1 := by have := D.one_le; omega
    refine ⟨_, burnsideC121_minParabolic_of_three c.P_pGroup c.P_le_normalizer hsyl ?_
      (c.not_le_normalizer_P hYS)⟩
    rw [c.P_inf_Y, c.RY_eq_pCore D hn1]
    exact c.relIndex_pCore_three D hn1

theorem minParabolic_YS (hYS : ¬ Y ≤ Subgroup.normalizer (baum T : Set Ω))
    (hSyl : IsSylowTwoOf (baum T) (Y ⊔ baum T)) :
    ∃ M : Subgroup Ω, MinParabolic (Y ⊔ baum T) (baum T) M := by
  have hsyl : IsSylowTwoOf (baum T ⊓ Y) Y :=
    A4.isSylowTwoOf_inf_normal hSyl le_sup_left (sup_le Subgroup.le_normalizer c.S_le_normalizer)
  have hO : pCoreOf 2 Y ≤ baum T := (B6.pCoreOf_two_le_of_isSylowTwoOf hsyl).trans inf_le_left
  by_cases hn : 2 ≤ n
  · obtain ⟨e⟩ := c.exists_autIEquiv_W D hn
    have hF : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, D.card]
    exact burnsideC121_minParabolic_of_sl2 c.W_elem c.Y_le_normalizer_W
      (c.S_le_P.trans c.P_le_normalizer_W) c.S_pGroup c.S_le_normalizer hsyl
      (by rw [c.inf_centralizer_W D]; exact hO) hn hF e hYS
  · have hn1 : n = 1 := by have := D.one_le; omega
    refine ⟨_, burnsideC121_minParabolic_of_three c.S_pGroup c.S_le_normalizer hsyl ?_ hYS⟩
    have hSY : baum T ⊓ Y = pCoreOf 2 Y :=
      CFSG.Quasithin.C124.Z3.eq_of_relIndex_three_of_isPGroup (le_inf hO (pCoreOf_le 2 Y))
        inf_le_right (c.relIndex_pCore_three D hn1) (c.S_pGroup.to_le inf_le_left)
    rw [hSY]
    exact c.relIndex_pCore_three D hn1

end burnsideC121_YCtx

end CFSG.ASVolI
