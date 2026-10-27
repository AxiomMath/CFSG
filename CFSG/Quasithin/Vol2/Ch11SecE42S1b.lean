module

public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
public import CFSG.Quasithin.Vol2.Ch11SecE42A36
public import CFSG.Quasithin.Vol2.Ch1ModO2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

variable {G : Type} [Group G] [Finite G]

theorem not_isSolvable_of_isQuasisimple {X : Type} [Group X] (hQ : CFSG.IsQuasisimple X) :
    ¬ Group.IsSolvable X := by
  intro hs
  have hsol : Group.IsSolvable ↥(⊤ : Subgroup X) := inferInstance
  have hperf : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊤ := by
    rw [← commutator_def]
    exact hQ.1.commutator_eq_top
  have hbot := eq_bot_of_perfect_of_solvable hperf hsol
  obtain ⟨-, -, a, b, hab⟩ := hQ
  apply hab
  induction a using QuotientGroup.induction_on with
  | H x =>
    induction b using QuotientGroup.induction_on with
    | H y =>
      have hx : x ∈ (⊥ : Subgroup X) := hbot ▸ Subgroup.mem_top x
      have hy : y ∈ (⊥ : Subgroup X) := hbot ▸ Subgroup.mem_top y
      rw [Subgroup.mem_bot.mp hx, Subgroup.mem_bot.mp hy]

theorem not_isQuasisimple_of_case21 {H Kp : Subgroup G} (hKp : Kp ∈ cComp H)
    (h21 : ⁅(CFSG.oddCore ↥(modO2Image H Kp)).map (modO2Image H Kp).subtype,
      modO2Image H Kp⁆ ≠ ⊥) :
    ¬ CFSG.IsQuasisimple (↥Kp ⧸ CFSG.pCore 2 ↥Kp) := by
  intro hQ
  obtain ⟨e⟩ := modO2_mulEquiv hKp
  have hQ' := (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr e).1 hQ
  have hne : CFSG.oddCore ↥(modO2Image H Kp) ≠ ⊤ := by
    intro htop
    have hodd : Odd (Nat.card ↥(modO2Image H Kp)) := by
      rw [← Subgroup.card_top, ← htop]
      exact SecD.odd_card_oddCore _
    exact not_isSolvable_of_isQuasisimple hQ' (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd)
  have hZ := SecA.le_center_of_normal_ne_top hQ' hne
  apply h21
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  rintro _ ⟨x, hx, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have := Subgroup.mem_center_iff.mp (hZ hx) ⟨y, hy⟩
  simpa using congrArg Subtype.val this

end CFSG.Quasithin.Vol2.Ch11.SecE
