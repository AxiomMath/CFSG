module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBRkDefs
import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Subgroup

variable {G : Type} [Group G] [Finite G]

theorem ggL48TB0Rk_pow_le_card_of_le_four {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J X B₂ : Subgroup G} {d y : G} {K U U₁ : Subgroup G}
    (hS : GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁) {r : ℕ} (hr : r ≤ 4) :
    p ^ r ≤ Nat.card Bs := by
  have hp : p.Prime := hS.1.1.1.2.2.2.2.2.1.1
  have hβ := hS.1.1.1.2.2.2.2.2.1
  have hsS := hS.1.1.1.2.2.2.2.2.2.1
  have hBst := hS.1.1.2.1
  have hBBs : Nat.card B ≤ Nat.card Bs := Subgroup.card_le_of_le hBst.1
  exact (Nat.pow_le_pow_right hp.pos hr).trans
    ((pow_four_le_card_of_bmax hp hsS.1 hβ.2.2.2).trans hBBs)

theorem ggL48TB0Rk_pow_le_card_of_inn (h : GGL48TB0TwConfigInputInn) {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J X B₂ : Subgroup G} {d y : G} {K U U₁ : Subgroup G}
    (hS : GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁)
    (hJD : Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D) {r : ℕ}
    (hmark : GGInnerDiagOnLab (fun p lab => GGL48TB0TwRow p lab ∧ GGL48TB0Rank lab = r) p Bs L) :
    p ^ r ≤ Nat.card Bs := by
  by_cases hr : 4 < r
  · exact h G p B Bs x L D J X B₂ d y K U U₁ hS hJD r hr hmark
  · exact ggL48TB0Rk_pow_le_card_of_le_four hS (not_lt.mp hr)

end CFSG.StandardType

end
