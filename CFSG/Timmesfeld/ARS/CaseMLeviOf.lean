module

public import CFSG.Timmesfeld.ARS.Sec12Transvection
public import CFSG.Timmesfeld.ARS.CaseMFinal
public import CFSG.Timmesfeld.Transvection.FrameSubgroup
public import CFSG.Timmesfeld.Transvection.Small
public import CFSG.Timmesfeld.ARS.Sec12MeetsLines
public import CFSG.Timmesfeld.ARS.Sec12Three

public section

namespace CFSG.Timmesfeld.ARS

open Transvection CFSG.LieType CFSG.LieType.Universal

variable {G : Type} [Group G] {R : Set (Subgroup G)}

namespace Sec12

variable {A A₀ : Subgroup G} (hS : Sec12 R A A₀)
include hS

theorem transvectionHyp_restrict' (hconn : LeviConnected R A A₀) :
    TransvectionHyp (levi R A A₀) (restrict (leviSet R A A₀) (levi R A A₀)) :=
  have := hS.hyp.finite
  hS.transvectionHyp_restrict hconn fun h2 => small_of_meetsLines
    (hS.isTransvectionClass_restrict hconn) hS.pointsDetermined_restrict hS.center_levi_eq_bot
    hS.exists_ne_commuting_restrict hS.meetsLines_restrict
    (fun N hN h3 => hS.eq_bot_of_normal_isPGroup_three hconn
      (hS.card_eq_two_of_exists_restrict h2) N hN h3) h2

theorem isSmallFrame {E C : Subgroup G} {P Q : Fin 3 → Subgroup G}
    (hfr : IsSubframe R A A₀ E C P Q) : IsSmallFrame (leviSet R A A₀) P Q 2 where
  memP i := (hfr.memP i).1
  memQ i := (hfr.memQ i).1
  opposite := hfr.opposite
  commuting := hfr.commuting
  residue _ hX h := hS.le_sup_of_isSubframe hfr hX (h 0 (by decide)).1 (h 0 (by decide)).2
    (h 1 (by decide)).1 (h 1 (by decide)).2

end Sec12

namespace CaseM

theorem unitaryLongRoot_six (h : 2 ≤ 2 * 3) :
    (unitaryLongRoot (2 * 3) h : Fin (2 * 3 / 2) → ℤ) = Pi.single (2 : Fin 3) 1 := by
  funext i
  fin_cases i <;> rfl

theorem caseMLeviInput_of_frame (hT : SubgroupTransvectionStatementFrame) : CaseMLeviInput := by
  intro G _ R A A₀ hS hconn f hf hcard
  have hR := hS.hyp.root
  obtain ⟨E, C, P, Q, hfr⟩ := hS.exists_isSubframe
  obtain ⟨f', hf', hcard', h⟩ := hT G (levi R A A₀) (leviSet R A A₀) (fun X hX => le_gen hX)
    (hS.transvectionHyp_restrict' hconn) hS.meetsLines 3 (by norm_num) P Q 2
    (hS.isSmallFrame hfr)
  obtain rfl : f' = f := by
    have h1 := hcard' _ (hfr.memP 0).1
    rw [hR.card_eq (hfr.memP 0).1.1.1 hS.mem, hcard] at h1
    exact (Nat.pow_right_injective le_rfl h1).symm
  rcases h with h | ⟨Φ, hker, hrange, hΔ⟩
  · exact Or.inl h
  · refine Or.inr ⟨Φ, hker.le, hrange, ?_⟩
    rwa [unitaryLongRoot_six] at hΔ

end CaseM

theorem caseMStep_of_frame (hT : SubgroupTransvectionStatementFrame) : CaseMStep :=
  caseMStep_of_frameInput (caseMFrameInput_of_leviInput (CaseM.caseMLeviInput_of_frame hT))

end CFSG.Timmesfeld.ARS
