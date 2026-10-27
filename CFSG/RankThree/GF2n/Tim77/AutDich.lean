module

public import CFSG.RankThree.GF2n.Tim77.AutDichL2
public import CFSG.RankThree.GF2n.Tim77.AutDichSz
public import CFSG.RankThree.GF2n.Tim77.AutDichU3

public section

namespace CFSG.RankThree.GF2n.Tim77

theorem autDich {L : Type} [Group L] [Finite L]
    (hL : CFSG.BenderSuzuki.IsBenderGroup L) (σ : MulAut L) (hσ : σ * σ = 1) {ā : L}
    (hā : orderOf ā = 2) (hfix : σ ā = ā) :
    (∃ τ : L, τ * τ = 1 ∧ τ * ā = ā * τ ∧ ∀ z : L, σ z = τ * z * τ⁻¹) ∨
      (∃ t : L, orderOf t = 2 ∧ σ t = t ∧ ¬ Commute ā t) := by
  rcases hL with ⟨n, hn, e⟩ | ⟨n, hn, e⟩ | ⟨n, hn, e⟩
  · exact autDich_l2 hn e σ hσ hā hfix
  · exact autDich_sz hn e σ hσ hā hfix
  · exact autDich_u3 hn e σ hσ hā hfix

end CFSG.RankThree.GF2n.Tim77
