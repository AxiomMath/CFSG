module

import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.ComponentClassification.Quasisimple
public import CFSG.Quasithin.Background.E3Defs

public section

namespace CFSG.Quasithin.RonanE42

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3
open scoped commutatorElement

variable {Q : Type} [Group Q] [Finite Q]

theorem generalizedFitting_le_of_normal (hO2 : CFSG.pCore 2 Q = ⊥)
    (hF : CFSG.IsQuasisimple ↥(CFSG.generalizedFitting Q) ∨
      ∃ p : ℕ, p.Prime ∧ Nat.card ↥(CFSG.generalizedFitting Q) = p)
    {Y : Subgroup Q} [Y.Normal] {y : Q} (hyY : y ∈ Y) (hy1 : y ≠ 1) {n : ℕ}
    (hyn : y ^ (2 ^ n) = 1) :
    CFSG.generalizedFitting Q ≤ Y := by
  haveI hFchar : (CFSG.generalizedFitting Q).Characteristic := by
    rw [CFSG.generalizedFitting_eq_componentClassification]
    exact CFSG.ComponentClassification.GeneralizedFitting.characteristic Q
  haveI hFn : (CFSG.generalizedFitting Q).Normal := inferInstance
  rcases hF with hQ | ⟨p, hp, hcard⟩
  ·
    haveI : Group.IsPerfect ↥(CFSG.generalizedFitting Q) := hQ.1
    have hQ' : CFSG.Open.IsQuasisimple ↥(CFSG.generalizedFitting Q) :=
      ⟨Group.IsPerfect.commutator_eq_top, hQ.2.1⟩
    rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hQ'
      ((Y ⊓ CFSG.generalizedFitting Q).subgroupOf (CFSG.generalizedFitting Q)) with hc | ht
    · exfalso
      set Zq : Subgroup Q := (Subgroup.center ↥(CFSG.generalizedFitting Q)).map
        (CFSG.generalizedFitting Q).subtype
      have hYF : Y ⊓ CFSG.generalizedFitting Q ≤ Zq := by
        intro x hx
        have hmem : (⟨x, hx.2⟩ : ↥(CFSG.generalizedFitting Q)) ∈
            (Y ⊓ CFSG.generalizedFitting Q).subgroupOf (CFSG.generalizedFitting Q) :=
          Subgroup.mem_subgroupOf.mpr hx
        exact Subgroup.mem_map_of_mem _ (hc hmem)
      have hZcent :
          Zq ≤ Subgroup.centralizer ((CFSG.generalizedFitting Q : Subgroup Q) : Set Q) := by
        intro z hz
        obtain ⟨f, hf, rfl⟩ := Subgroup.mem_map.mp hz
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hf ⟨h, hh⟩)
      have hZF : ⁅Zq, CFSG.generalizedFitting Q⁆ = ⊥ :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hZcent
      have hFYZ : ⁅CFSG.generalizedFitting Q, Y⁆ ≤ Zq :=
        (Subgroup.commutator_le_inf (CFSG.generalizedFitting Q) Y).trans
          ((inf_comm _ _).le.trans hYF)
      have h3 : ⁅⁅CFSG.generalizedFitting Q, Y⁆, CFSG.generalizedFitting Q⁆ = ⊥ :=
        le_antisymm ((Subgroup.commutator_mono_left hFYZ).trans hZF.le) bot_le
      have hFY : ⁅CFSG.generalizedFitting Q, Y⁆ = ⊥ :=
        CFSG.ComponentClassification.Quasisimple.perfect_double_commutator _ _ h3
      have hYc : Y ≤ Subgroup.centralizer ((CFSG.generalizedFitting Q : Subgroup Q) : Set Q) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp
          (by rw [Subgroup.commutator_comm]; exact hFY)
      have hYle : Y ≤ CFSG.generalizedFitting Q :=
        hYc.trans (CFSG.centralizer_generalizedFitting_le Q)
      have hcomm : ∀ a ∈ Y, ∀ b ∈ Y, Commute a b := by
        intro a ha b hb
        have hza : a ∈ Zq := hYF ⟨ha, hYle ha⟩
        exact ((Subgroup.mem_centralizer_iff.mp (hZcent hza)) b (hYle hb)).symm
      let P : Subgroup Q :=
        { carrier := {z | z ∈ Y ∧ z ^ (2 ^ n) = 1}
          mul_mem' := fun {a b} ha hb =>
            ⟨Y.mul_mem ha.1 hb.1, by rw [(hcomm a ha.1 b hb.1).mul_pow, ha.2, hb.2, one_mul]⟩
          one_mem' := ⟨Y.one_mem, by rw [one_pow]⟩
          inv_mem' := fun {a} ha => ⟨Y.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
      have hPn : P.Normal := by
        refine ⟨fun z hz g => ⟨Subgroup.Normal.conj_mem inferInstance z hz.1 g, ?_⟩⟩
        rw [conj_pow, hz.2, mul_one, mul_inv_cancel]
      have hPp : IsPGroup 2 P := by
        intro g
        refine ⟨n, Subtype.ext ?_⟩
        simpa using g.2.2
      have hPle : P ≤ CFSG.pCore 2 Q := by
        unfold CFSG.pCore
        exact le_sSup ⟨hPn, hPp⟩
      have hyP : y ∈ P := ⟨hyY, hyn⟩
      exact hy1 (Subgroup.mem_bot.mp (hPle.trans hO2.le hyP))
    · exact (Subgroup.subgroupOf_eq_top.mp ht).trans inf_le_left
  ·
    haveI : Fact (Nat.card ↥(CFSG.generalizedFitting Q)).Prime := ⟨by rw [hcard]; exact hp⟩
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card
      ((Y ⊓ CFSG.generalizedFitting Q).subgroupOf (CFSG.generalizedFitting Q)) with hb | ht
    · exfalso
      have hYF0 : Y ⊓ CFSG.generalizedFitting Q = ⊥ := by
        have hsub : Y ⊓ CFSG.generalizedFitting Q ≤ CFSG.generalizedFitting Q := inf_le_right
        have h := disjoint_iff.mp (Subgroup.subgroupOf_eq_bot.mp hb)
        rwa [inf_eq_left.mpr hsub] at h
      have hcomm0 : ⁅Y, CFSG.generalizedFitting Q⁆ ≤ ⊥ :=
        (Subgroup.commutator_le_inf Y (CFSG.generalizedFitting Q)).trans hYF0.le
      have hYc : Y ≤ Subgroup.centralizer ((CFSG.generalizedFitting Q : Subgroup Q) : Set Q) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp (le_bot_iff.mp hcomm0)
      have hYle : Y ≤ CFSG.generalizedFitting Q :=
        hYc.trans (CFSG.centralizer_generalizedFitting_le Q)
      have hy_bot : y ∈ (⊥ : Subgroup Q) := by
        rw [← hYF0]
        exact ⟨hyY, hYle hyY⟩
      exact hy1 (Subgroup.mem_bot.mp hy_bot)
    · exact (Subgroup.subgroupOf_eq_top.mp ht).trans inf_le_left

end CFSG.Quasithin.RonanE42
