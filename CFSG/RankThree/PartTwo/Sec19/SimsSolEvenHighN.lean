module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenCentral

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo

namespace Cfg.PiData

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {C : Cfg G M X 10} (D : C.PiData)

theorem centInM_ten_of (hR : Nat.card ↥(Rc X) ≤ 2)
    (h2 : ∀ x : ↥(CFSG.Open.pCoreOf 2 M), barLen (Multiplicative.toAdd (D.piQ x)) = 2 →
      Subgroup.centralizer ({(x : G)} : Set G) ≤ M)
    (h4 : ∀ x : ↥(CFSG.Open.pCoreOf 2 M), barLen (Multiplicative.toAdd (D.piQ x)) = 4 →
      Subgroup.centralizer ({(x : G)} : Set G) ≤ M) :
    ∀ x ∈ CFSG.Open.pCoreOf 2 M, x ≠ 1 → Subgroup.centralizer ({x} : Set G) ≤ M := by
  intro x hx hx1
  by_cases hl2 : barLen (Multiplicative.toAdd (D.piQ ⟨x, hx⟩)) = 2
  · exact h2 ⟨x, hx⟩ hl2
  by_cases hl4 : barLen (Multiplicative.toAdd (D.piQ ⟨x, hx⟩)) = 4
  · exact h4 ⟨x, hx⟩ hl4
  exact (D.centralizer_le_of_len hR ⟨x, hx⟩ hx1 ⟨hl2, hl4⟩).1

end Cfg.PiData

end CFSG.RankThree.PartTwo.Sec19.SolEven
