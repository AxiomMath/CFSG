module

public import CFSG.Quasithin.H13.VolIG248Q8
public import CFSG.Quasithin.H13.A5Inputs2

public section

namespace CFSG.Quasithin.H13.VolI

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

theorem stmtG248Core {G : Type} [Group G] [Finite G] {V V₁ L T H : Subgroup G}
    (hyp : AlmostSpecialA5Core V V₁ L T H)
    (hcomm : ⁅conjClosure V H, lOne L V₁⁆ ⊔ V₁ = conjClosure V H)
    (hO2 : pCoreOf 2 (lOne L V₁) ≤ pCoreOf 2 H) {g : G} (hg : g ∈ L)
    (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) :
    conjClosure V H ⊔ rconj (conjClosure V H) g = L ∧ IsShort2 L ∧ IsAltType L 5 ∧
      pCoreOf 2 L = conjClosure V₁ L ∧ conjClosure V H = pCoreOf 2 (lOne L V₁) ∧
      IsQ8Sq ↥(conjClosure V H) := by
  obtain ⟨St⟩ := hyp.nonempty_setting
  let X : G248.Setting V V₁ L T H g := ⟨St, hcomm, hO2, hg, hgN⟩
  exact ⟨X.I_eq, X.isShort2, X.isAltType, X.pCoreOf_L_eq, X.U_eq, X.isQ8Sq⟩

theorem stmtG248 : A5.StmtG248 := by
  intro G _ _ V V₁ L T H hyp hcomm hO2 g hg hgN
  exact stmtG248Core hyp.toCore hcomm hO2 hg hgN

end CFSG.Quasithin.H13.VolI
