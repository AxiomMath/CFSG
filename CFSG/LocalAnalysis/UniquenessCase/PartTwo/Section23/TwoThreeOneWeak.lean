module

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeOneBasic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeOneUnique
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ThreeWeakClosure
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.Context

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {Ch : Choice2011 G}

namespace S231

theorem commutator_wClos_eq_bot (c : Ctx23L D Ch) {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hW : IsElemAbelian 2 (conjClosure c.L0 (V ⊓ D.Z))) {i : ℕ}
    (hi : aBar (c.L0 ⊔ D.T) ⊥ (conjClosure c.L0 (V ⊓ D.Z)) hW + i < E3.sParam hV) :
    ⁅E3.wClos V i D.T, conjClosure c.L0 (V ⊓ D.Z)⁆ = ⊥ := by
  have hS : IsSylowIn 2 D.T (c.L0 ⊔ D.T) := TwelveShort.isSylowIn_of_le D le_sup_right
  have hUn : c.L0 ⊔ D.T ≤
      Subgroup.normalizer (conjClosure c.L0 (V ⊓ D.Z) : Set G) :=
    S231.sup_le_normalizer_W c V
  have ha : E3.aParam (autI hW (c.L0 ⊔ D.T)) =
      aBar (c.L0 ⊔ D.T) ⊥ (conjClosure c.L0 (V ⊓ D.Z)) hW :=
    S231.aParam_autI_eq_aBar hW (c.L0 ⊔ D.T)
  have hi' : i < E3.sParam hV - E3.aParam (autI hW (c.L0 ⊔ D.T)) := by
    rw [ha]
    omega
  exact (CFSG.LocalAnalysis.WeakClosure81.six_eleven_one_generic
    (V := V) (H := c.L0 ⊔ D.T) (S := D.T)
    (U := conjClosure c.L0 (V ⊓ D.Z)) (Z := ⊥) hV hS hUn hW bot_le hi').1

theorem wClos_le_pCoreOf (c : Ctx23L D Ch) {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hVeq : V = conjClosure c.N (V ⊓ D.Z)) (hVne : V ≠ ⊥)
    (hW : IsElemAbelian 2 (conjClosure c.L0 (V ⊓ D.Z))) {i : ℕ}
    (hi : aBar (c.L0 ⊔ D.T) ⊥ (conjClosure c.L0 (V ⊓ D.Z)) hW + i < E3.sParam hV) :
    E3.wClos V i D.T ≤ CFSG.Open.pCoreOf 2 (c.L0 ⊔ D.T) := by
  have hcomm : E3.wClos V i D.T ≤
      Subgroup.centralizer (conjClosure c.L0 (V ⊓ D.Z) : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).1
      (S231.commutator_wClos_eq_bot c hV hW hi)
  have hinf : D.T ⊓ Subgroup.centralizer (conjClosure c.L0 (V ⊓ D.Z) : Set G) ≤
      CFSG.Open.pCoreOf 2 (c.L0 ⊔ D.T) :=
    S231.inf_centralizer_le_pCoreOf (L := c.L0)
      (X := conjClosure c.L0 (V ⊓ D.Z)) c.hL0.1 (S231.sup_le_normalizer_W c V)
      (S231.centralizer_le_M c hVeq hVne (uc22p22v_le_conjClosure c.L0 (V ⊓ D.Z)))
  exact (le_inf (E3.wClos_le i D.T) hcomm).trans hinf

theorem sup_le_normalizer_wClos (c : Ctx23L D Ch) {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hVeq : V = conjClosure c.N (V ⊓ D.Z)) (hVne : V ≠ ⊥)
    (hW : IsElemAbelian 2 (conjClosure c.L0 (V ⊓ D.Z))) {i : ℕ}
    (hi : aBar (c.L0 ⊔ D.T) ⊥ (conjClosure c.L0 (V ⊓ D.Z)) hW + i < E3.sParam hV) :
    c.L0 ⊔ D.T ≤ normalizer (E3.wClos V i D.T : Set G) := by
  have hQT : CFSG.Open.pCoreOf 2 (c.L0 ⊔ D.T) ≤ D.T :=
    CFSG.Quasithin.E1.pCoreOf_two_le_of_isSylowIn
      (TwelveShort.isSylowIn_of_le D le_sup_right)
  have hEq : E3.wClos V i D.T = E3.wClos V i (CFSG.Open.pCoreOf 2 (c.L0 ⊔ D.T)) :=
    wClos_eq_of_gammaSet_le
      (fun A hA => (E3.le_wClos hA).trans
        (S231.wClos_le_pCoreOf c hV hVeq hVne hW hi)) hQT
  rw [hEq]
  exact (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (c.L0 ⊔ D.T)).trans
    (E3.normalizer_le_normalizer_wClos (V := V) (i := i)
      (CFSG.Open.pCoreOf 2 (c.L0 ⊔ D.T)))

theorem sup_le_normalizer_center_wClos (c : Ctx23L D Ch) {V : Subgroup G}
    (hV : IsElemAbelian 2 V) (hVeq : V = conjClosure c.N (V ⊓ D.Z)) (hVne : V ≠ ⊥)
    (hW : IsElemAbelian 2 (conjClosure c.L0 (V ⊓ D.Z))) {i : ℕ}
    (hi : aBar (c.L0 ⊔ D.T) ⊥ (conjClosure c.L0 (V ⊓ D.Z)) hW + i < E3.sParam hV) :
    c.L0 ⊔ D.T ≤ normalizer ((E3.wClos V i D.T ⊓ centralizer (E3.wClos V i D.T : Set G) :
      Subgroup G) : Set G) := by
  intro x hx
  exact uc22p22ta_mem_normalizer_center
    (S231.sup_le_normalizer_wClos c hV hVeq hVne hW hi hx)

theorem normalizer_wClos_zero_mem_hSet (c : Ctx23L D Ch) {V : Subgroup G}
    (hV : IsElemAbelian 2 V) (hVle : V ≤ c.V) (hVeq : V = conjClosure c.N (V ⊓ D.Z))
    (hVne : V ≠ ⊥) (hW : IsElemAbelian 2 (conjClosure c.L0 (V ⊓ D.Z)))
    (hi : aBar (c.L0 ⊔ D.T) ⊥ (conjClosure c.L0 (V ⊓ D.Z)) hW < E3.sParam hV) :
    normalizer (E3.wClos V 0 D.T : Set G) ∈ hSet D.T D.M := by
  have hrk0 : 0 < rk ↥V := by
    rw [Nat.pos_iff_ne_zero]
    intro h0
    exact hVne ((rk_eq_zero_iff_of_isPGroup (B2F.isPGroup_of_isElemAbelian hV)).mp h0)
  have hVW : V ≤ E3.wClos V 0 D.T :=
    E3.le_wClos_of_mQuot_le_self hV (S231.V_le_T c hVle) le_rfl
      (E3.mQuot_self V).le hrk0
  have hWne : E3.wClos V 0 D.T ≠ ⊥ := fun h => hVne (le_bot_iff.mp (h ▸ hVW))
  have hW2 : IsPGroup 2 (E3.wClos V 0 D.T) :=
    D.sylowM.isPGroup.to_le (E3.wClos_le 0 D.T)
  have hTW : D.T ≤ Subgroup.normalizer (E3.wClos V 0 D.T : Set G) :=
    (Subgroup.le_normalizer : D.T ≤ Subgroup.normalizer (D.T : Set G)).trans
      (E3.normalizer_le_normalizer_wClos (V := V) (i := 0) D.T)
  have hL0W : c.L0 ≤ Subgroup.normalizer (E3.wClos V 0 D.T : Set G) :=
    le_sup_left.trans
      (S231.sup_le_normalizer_wClos c hV hVeq hVne hW (i := 0) (by simpa using hi))
  refine ⟨hTW, fun h => Ctx23L.L0_not_le_M c (hL0W.trans h), ?_⟩
  exact D.standing.charTwo _ ⟨E3.wClos V 0 D.T, hWne, hW2, rfl⟩

private theorem center_wClos_one_ne_bot_S04 {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hVT : V ≤ D.T) (hVne : V ≠ ⊥) (hrk : 1 < rk ↥V) :
    E3.wClos V 1 D.T ⊓ Subgroup.centralizer (E3.wClos V 1 D.T : Set G) ≠ ⊥ := by
  have hVW : V ≤ E3.wClos V 1 D.T :=
    E3.le_wClos_of_mQuot_le_self hV hVT le_rfl
      ((E3.mQuot_self V).le.trans zero_le_one) hrk
  have hWne : E3.wClos V 1 D.T ≠ ⊥ := fun h => hVne (le_bot_iff.mp (h ▸ hVW))
  have hW2 : IsPGroup 2 (E3.wClos V 1 D.T) :=
    D.sylowM.isPGroup.to_le (E3.wClos_le 1 D.T)
  have : Nontrivial ↥(E3.wClos V 1 D.T) :=
    (Subgroup.nontrivial_iff_ne_bot _).2 hWne
  have := hW2.center_nontrivial
  obtain ⟨z, hz⟩ := exists_ne (1 : ↥(center ↥(E3.wClos V 1 D.T)))
  intro hbot
  have hzmem : ((z : ↥(E3.wClos V 1 D.T)) : G) ∈
      E3.wClos V 1 D.T ⊓ Subgroup.centralizer (E3.wClos V 1 D.T : Set G) := by
    refine ⟨(z : ↥(E3.wClos V 1 D.T)).2,
      Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.1 z.2) ⟨h, hh⟩)
  rw [hbot, Subgroup.mem_bot] at hzmem
  exact hz (Subtype.ext (Subtype.ext hzmem))

theorem normalizer_center_wClos_one_mem_hSet (c : Ctx23L D Ch) {V : Subgroup G}
    (hV : IsElemAbelian 2 V) (hVle : V ≤ c.V) (hVeq : V = conjClosure c.N (V ⊓ D.Z))
    (hVne : V ≠ ⊥) (hW : IsElemAbelian 2 (conjClosure c.L0 (V ⊓ D.Z)))
    (hi : aBar (c.L0 ⊔ D.T) ⊥ (conjClosure c.L0 (V ⊓ D.Z)) hW + 1 < E3.sParam hV)
    (hrk : 1 < rk ↥V) :
    normalizer ((E3.wClos V 1 D.T ⊓ centralizer (E3.wClos V 1 D.T : Set G) : Subgroup G) :
      Set G) ∈ hSet D.T D.M := by
  set W : Subgroup G := E3.wClos V 1 D.T with hWdef
  set ZW : Subgroup G := W ⊓ Subgroup.centralizer (W : Set G) with hZWdef
  have hZWne : ZW ≠ ⊥ := by
    simpa [W, ZW] using center_wClos_one_ne_bot_S04 hV (S231.V_le_T c hVle) hVne hrk
  have hW2 : IsPGroup 2 W := D.sylowM.isPGroup.to_le (E3.wClos_le 1 D.T)
  have hL0ZW : c.L0 ≤ Subgroup.normalizer (ZW : Set G) := by
    simpa [W, ZW] using le_sup_left.trans
      (S231.sup_le_normalizer_center_wClos c hV hVeq hVne hW (i := 1) hi)
  refine ⟨?_, fun h => Ctx23L.L0_not_le_M c (hL0ZW.trans h), ?_⟩
  · intro t ht
    exact uc22p22ta_mem_normalizer_center
      (E3.normalizer_le_normalizer_wClos (V := V) (i := 1) D.T (Subgroup.le_normalizer ht))
  · exact D.standing.charTwo _ ⟨ZW, hZWne, hW2.to_le inf_le_left, rfl⟩

end S231

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
