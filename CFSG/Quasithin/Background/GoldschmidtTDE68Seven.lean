module

public import CFSG.Quasithin.Background.GoldschmidtTDE68Wrap
public import CFSG.Quasithin.Background.GoldschmidtTDE68A7Model

public section

namespace CFSG.Quasithin.E6.Alt

open Subgroup CFSG.Quasithin.E6.Bar CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1

variable {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y}

theorem card_G7 : Nat.card A7.G7 = 8 * 315 := by
  rw [A7.card_alt7]

theorem altRank_caseD {A R : Subgroup Y} {z : Y} (hD : Lemma115CaseD L z)
    (h : E68BaseHyp L A R) :
    (A ⊓ Subgroup.centralizer (L : Set Y)).relIndex A ≤ 4 ∧
      ((A ⊓ Subgroup.centralizer (L : Set Y)).relIndex A = 4 →
        L ≤ ⨆ (a : Y) (_ : a ∈ A ∧ a ∉ Subgroup.centralizer (L : Set Y)),
          L ⊓ Subgroup.centralizer ({a} : Set Y)) := by
  obtain ⟨φ, -, hZ, -, -⟩ := hD
  exact altRank_of_iso A7.altModel_seven A7.card_D7q (by decide) card_G7 φ hZ h

theorem card_comp_caseD {R K : Subgroup Y} {u z : Y} (hD : Lemma115CaseD L z)
    (h : E68CentHyp L R u)
    (hK : IsComponentIn K (L ⊓ Subgroup.centralizer ({u} : Set Y))) : Nat.card ↥K = 60 := by
  obtain ⟨φ, -, hZ, -, -⟩ := hD
  exact card_comp_of_iso A7.altModel_seven A7.card_D7q (by decide) card_G7 φ hZ h hK

end CFSG.Quasithin.E6.Alt
