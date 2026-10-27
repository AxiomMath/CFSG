module

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ThreeCaseB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.Context
import CFSG.Quasithin.Background.E4Solv

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {Ch : Choice2011 G}

namespace S231

theorem inf_Z_ne_bot (c : Ctx23L D Ch) {V : Subgroup G}
    (hVeq : V = conjClosure c.N (V ⊓ D.Z)) (hVne : V ≠ ⊥) : V ⊓ D.Z ≠ ⊥ := by
  intro hVZ
  refine hVne ?_
  have hN : c.N ≤ normalizer ((⊥ : Subgroup G) : Set G) := by
    rw [Subgroup.normalizer_eq_top]; exact le_top
  have hle : conjClosure c.N (V ⊓ D.Z) ≤ (⊥ : Subgroup G) := by
    rw [hVZ]
    exact uc22p22v_conjClosure_le hN le_rfl
  rw [hVeq]
  exact le_bot_iff.mp hle

theorem N_le_normalizer_V (c : Ctx23L D Ch) {V : Subgroup G}
    (hVeq : V = conjClosure c.N (V ⊓ D.Z)) : c.N ≤ normalizer (V : Set G) := by
  have h := uc22p22v_le_normalizer_conjClosure c.N (V ⊓ D.Z)
  rwa [← hVeq] at h

theorem W_le (c : Ctx23L D Ch) {V : Subgroup G} (hVeq : V = conjClosure c.N (V ⊓ D.Z)) :
    conjClosure c.L0 (V ⊓ D.Z) ≤ V :=
  uc22p22v_conjClosure_le ((Ctx23L.L0_le_N c).trans (N_le_normalizer_V c hVeq)) inf_le_left

theorem isElemAbelian_W (c : Ctx23L D Ch) {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hVeq : V = conjClosure c.N (V ⊓ D.Z)) :
    IsElemAbelian 2 (conjClosure c.L0 (V ⊓ D.Z)) :=
  CFSG.Open.IsElemAbelian.mono hV (W_le c hVeq)

theorem sup_le_normalizer_W (c : Ctx23L D Ch) (V : Subgroup G) :
    c.L0 ⊔ D.T ≤ normalizer (conjClosure c.L0 (V ⊓ D.Z) : Set G) := by
  have hTZ : D.T ≤ centralizer ((V ⊓ D.Z : Subgroup G) : Set G) :=
    (uc22main1_T_le_centralizer D).trans (Subgroup.centralizer_le inf_le_right)
  have hEq : conjClosure (c.L0 ⊔ D.T) (V ⊓ D.Z) = conjClosure c.L0 (V ⊓ D.Z) := by
    rw [← quasithin_conjClosure_eq (V ⊓ D.Z) (c.L0 ⊔ D.T),
      CFSG.Quasithin.H13.NQS134.conjClosure_sup_eq c.hL0.1.1 hTZ,
      quasithin_conjClosure_eq (V ⊓ D.Z) c.L0]
  rw [← hEq]
  exact uc22p22v_le_normalizer_conjClosure (c.L0 ⊔ D.T) (V ⊓ D.Z)

theorem V_le_T (c : Ctx23L D Ch) {V : Subgroup G} (hVle : V ≤ c.V) : V ≤ D.T :=
  hVle.trans (Ctx23L.V_le_T_basic c)

theorem V_le_N (c : Ctx23L D Ch) {V : Subgroup G} (hVle : V ≤ c.V) : V ≤ c.N :=
  (V_le_T c hVle).trans (Ctx23L.T_le_N c)

theorem normalizer_V_eq (c : Ctx23L D Ch) {V : Subgroup G} (hVle : V ≤ c.V)
    (hVeq : V = conjClosure c.N (V ⊓ D.Z)) (hVne : V ≠ ⊥) :
    normalizer (V : Set G) = c.N :=
  normalizer_eq_of_isMaxTwoLocal (Ctx23L.N_mem_calMOf_T c).1 hVne
    (D.sylowM.isPGroup.to_le (V_le_T c hVle)) (N_le_normalizer_V c hVeq)

theorem centralizer_le_M (c : Ctx23L D Ch) {V X : Subgroup G}
    (hVeq : V = conjClosure c.N (V ⊓ D.Z)) (hVne : V ≠ ⊥) (hX : V ⊓ D.Z ≤ X) :
    centralizer (X : Set G) ≤ D.M := by
  obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (inf_Z_ne_bot c hVeq hVne)
  have hu1' : (u : G) ≠ 1 := fun h => hu1 (Subtype.ext h)
  refine (Subgroup.centralizer_le ?_).trans
    (Ctx23.centralizer_le_M c.toCtx23 (Data.Z_le_U D u.2.2) hu1')
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  rw [hy]
  exact hX u.2

theorem aParam_autI_eq_aBar {W : Subgroup G} (hW : IsElemAbelian 2 W) (X : Subgroup G) :
    E3.aParam (autI hW X) = aBar X ⊥ W hW := by
  show E3.aParam (autI hW X) = E3.aParam (barSub (⊥ : Subgroup G) W hW X)
  rw [TwelveTwentyThree.barSub_bot_eq_map_autI W hW X,
    CFSG.Quasithin.H.aParam_map_congrHom]

theorem T_not_le_centralizer_W (c : Ctx23L D Ch) {V : Subgroup G} (hVle : V ≤ c.V)
    (hVeq : V = conjClosure c.N (V ⊓ D.Z)) (hVne : V ≠ ⊥)
    (hW : IsElemAbelian 2 (conjClosure c.L0 (V ⊓ D.Z))) :
    ¬ D.T ≤ centralizer (conjClosure c.L0 (V ⊓ D.Z) : Set G) := by
  intro hT
  have hWleV : conjClosure c.L0 (V ⊓ D.Z) ≤ V := W_le c hVeq
  have hWleT : conjClosure c.L0 (V ⊓ D.Z) ≤ D.T := hWleV.trans (V_le_T c hVle)
  have hWleZ : conjClosure c.L0 (V ⊓ D.Z) ≤ D.Z := by
    intro w hw
    exact CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff.mpr
      ⟨hWleT hw, fun k hk => (Subgroup.mem_centralizer_iff.mp (hT hk) w hw).symm, hW.2 w hw⟩
  have hWleU : conjClosure c.L0 (V ⊓ D.Z) ≤ D.U := hWleZ.trans (Data.Z_le_U D)
  have hWne : conjClosure c.L0 (V ⊓ D.Z) ≠ ⊥ := by
    intro hbot
    have h := uc22p22v_le_conjClosure c.L0 (V ⊓ D.Z)
    rw [hbot] at h
    exact (inf_Z_ne_bot c hVeq hVne) (le_bot_iff.mp h)
  apply Ctx23L.L0_not_le_M c
  intro l hl
  refine Ctx23.mem_M_of_ne_bot c.toCtx23 ?_
  have hWnorm : l ∈ normalizer (conjClosure c.L0 (V ⊓ D.Z) : Set G) :=
    uc22p22v_le_normalizer_conjClosure c.L0 (V ⊓ D.Z) hl
  have hconj : conjClosure c.L0 (V ⊓ D.Z) ≤
      CFSG.CGT.Timmesfeld75.conjSubgroup l D.U := by
    intro w hw
    rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup]
    have hlinv : l⁻¹ ∈ normalizer (conjClosure c.L0 (V ⊓ D.Z) : Set G) :=
      (normalizer (conjClosure c.L0 (V ⊓ D.Z) : Set G)).inv_mem hWnorm
    have hmem : l⁻¹ * w * l⁻¹⁻¹ ∈ conjClosure c.L0 (V ⊓ D.Z) :=
      (Subgroup.mem_normalizer_iff.mp hlinv w).1 hw
    exact hWleU (by simpa using hmem)
  have hbot : D.U ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup l D.U ≠ ⊥ := by
    intro h
    have hle := le_inf hWleU hconj
    rw [h] at hle
    exact hWne (le_bot_iff.mp hle)
  exact hbot

theorem one_le_aBar (c : Ctx23L D Ch) {V : Subgroup G} (hVle : V ≤ c.V)
    (hVeq : V = conjClosure c.N (V ⊓ D.Z)) (hVne : V ≠ ⊥)
    (hW : IsElemAbelian 2 (conjClosure c.L0 (V ⊓ D.Z))) :
    1 ≤ aBar (c.L0 ⊔ D.T) ⊥ (conjClosure c.L0 (V ⊓ D.Z)) hW := by
  have hTNW : D.T ≤ normalizer (conjClosure c.L0 (V ⊓ D.Z) : Set G) :=
    (le_sup_right : D.T ≤ c.L0 ⊔ D.T).trans (sup_le_normalizer_W c V)
  have hpg : IsPGroup 2 (autI hW D.T) :=
    E3.isPGroup_autI hW hTNW D.sylowM.isPGroup
  have hautne : autI hW D.T ≠ ⊥ := fun h =>
    T_not_le_centralizer_W c hVle hVeq hVne hW ((autI_eq_bot_iff hW hTNW).1 h)
  obtain ⟨τ, hτmem, hτo⟩ := E3.exists_orderOf_two_of_isPGroup hpg hautne
  have hτ2 : τ ^ 2 = 1 := by
    have h := pow_orderOf_eq_one τ
    rwa [hτo] at h
  have hA_ne : Subgroup.zpowers τ ≠ ⊥ := by
    intro hbot
    have h1 : τ = 1 := (Subgroup.zpowers_eq_bot).1 hbot
    rw [h1, orderOf_one] at hτo
    exact absurd hτo (by decide)
  have hA_le : Subgroup.zpowers τ ≤ autI hW (c.L0 ⊔ D.T) :=
    (Subgroup.zpowers_le.mpr hτmem).trans (autI_mono hW le_sup_right)
  have hA_mem : Subgroup.zpowers τ ∈ E3.aSet 1 (autI hW (c.L0 ⊔ D.T)) := by
    rw [E3.aSet_one]
    exact ⟨hA_le, hA_ne, E3.isElemAbelian2_zpowers hτ2⟩
  have h1 : 1 ≤ E3.aParam (autI hW (c.L0 ⊔ D.T)) :=
    E3.le_aParam_of_mem_aSet one_pos hA_mem
  rwa [aParam_autI_eq_aBar hW (c.L0 ⊔ D.T)] at h1

end S231

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
