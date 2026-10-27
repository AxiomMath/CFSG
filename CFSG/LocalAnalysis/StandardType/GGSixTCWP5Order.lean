module

public import CFSG.LocalAnalysis.StandardType.TableC.HypDefs
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5Inputs
import CFSG.Blueprint.LieModelAPI
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatAlt
import CFSG.Timmesfeld.Orders.ExceptionalTwisted

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.Open

private theorem w6O_nineteen_dvd_of_psu_three_two_three {Y : Type} [Group Y]
    (h : LieModel Y .PSU 3 2 3) : 19 ∣ Nat.card Y := by
  rw [CFSG.SeitzReduction.UnitaryPilot.card_of_lieModel_PSU_two_pow h]
  decide

private theorem w6O_thirteen_dvd_of_trialityD4
    {Y : Type} [Group Y] (h : LieModel Y .trialityD4 0 2 1) : 13 ∣ Nat.card Y := by
  have hce : ChevalleyExceptionalModel Y .trialityD4 2 1 :=
    ((LieModel.chevalleyExceptional_iff (t := .trialityD4)
      (by decide : .trialityD4 ∈ chevalleyExceptionalTags)).1 h).2
  have htw : TwistedChevalleyModel Y .D4 (2 ^ 1) := by
    simpa only [ChevalleyExceptionalModel] using hce.2
  rw [CFSG.Timmesfeld.ExceptionalOrders.card_of_twistedChevalleyModel_D4_two (by norm_num) htw]
  decide

private theorem w6O_card_subgroupOf_eq {G : Type} [Group G] {H K : Subgroup G} (h : H ≤ K) :
    Nat.card ↥(H.subgroupOf K) = Nat.card ↥H :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

private theorem w6O_card_quotient_center_dvd (G : Type) [Group G] :
    Nat.card (G ⧸ Subgroup.center G) ∣ Nat.card G :=
  ⟨Nat.card ↥(Subgroup.center G), Subgroup.card_eq_card_quotient_mul_card_subgroup _⟩

private theorem w6O_subgroupOf_le_centralizer {G : Type} [Group G] {L G₀ : Subgroup G} {g : G}
    (hg : g ∈ G₀) (hLg : L ≤ Subgroup.centralizer ({g} : Set G)) :
    L.subgroupOf G₀ ≤ Subgroup.centralizer ({⟨g, hg⟩} : Set ↥G₀) := by
  intro l hl
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  subst hh
  exact Subtype.ext
    ((Subgroup.mem_centralizer_iff.mp (hLg (Subgroup.mem_subgroupOf.mp hl))) g
      (Set.mem_singleton g))

section Order

variable {X : Type} [Group X] [Finite X] {n f p : ℕ} {G₀ B D J L : Subgroup X} {x : X}

theorem GGTCHyp.psu_six_of_order_three_twE6
    (hA : TwE6q2OrderThreeCentralizers)
    {ψ : (ggU .twistedE6 n f).K →* X} (h : GGTCHyp .twistedE6 n f ψ p G₀ B D J L x)
    (hf : f = 1) (hZ : Subgroup.center ↥G₀ = ⊥) {g : X} (hg : g ∈ G₀) (hg3 : orderOf g = 3)
    (hLg : L ≤ Subgroup.centralizer ({g} : Set X))
    (hlab : LieModel (↥L ⧸ Subgroup.center ↥L) .PSU 3 2 3 ∨
      LieModel (↥L ⧸ Subgroup.center ↥L) .trialityD4 0 2 1 ∨
      LieModel (↥L ⧸ Subgroup.center ↥L) .PSU 6 2 1) :
    LieModel (↥L ⧸ Subgroup.center ↥L) .PSU 6 2 1 := by
  have hmodel : LieModel ↥G₀ .twistedE6 n 2 1 := by
    have h0 : LieModel (↥G₀ ⧸ Subgroup.center ↥G₀) .twistedE6 n 2 f := h.model
    rw [hf] at h0
    exact LieModel.of_quotient_center hZ h0
  have hg'3 : orderOf (⟨g, hg⟩ : ↥G₀) = 3 := by
    rw [Subgroup.orderOf_mk, hg3]
  have hcent := hA ↥G₀ n hmodel ⟨g, hg⟩ hg'3
  have hle : L.subgroupOf G₀ ≤ Subgroup.centralizer ({⟨g, hg⟩} : Set ↥G₀) :=
    w6O_subgroupOf_le_centralizer hg hLg
  have hcard_le : Nat.card ↥L ∣ Nat.card (Subgroup.centralizer ({⟨g, hg⟩} : Set ↥G₀)) := by
    rw [← w6O_card_subgroupOf_eq h.l_le]
    exact Subgroup.card_dvd_of_le hle
  have hquot : Nat.card (↥L ⧸ Subgroup.center ↥L) ∣ Nat.card ↥L :=
    w6O_card_quotient_center_dvd ↥L
  have hdvd : Nat.card (↥L ⧸ Subgroup.center ↥L) ∣
      Nat.card (Subgroup.centralizer ({⟨g, hg⟩} : Set ↥G₀)) :=
    dvd_trans hquot hcard_le
  rcases hlab with h1 | h2 | h3
  · exact absurd (dvd_trans (w6O_nineteen_dvd_of_psu_three_two_three h1) hdvd) hcent.2
  · exact absurd (dvd_trans (w6O_thirteen_dvd_of_trialityD4 h2) hdvd) hcent.1
  · exact h3

end Order

end CFSG.StandardType.TableCRes

end
