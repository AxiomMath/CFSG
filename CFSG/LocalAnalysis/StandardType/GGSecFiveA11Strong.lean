module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveA11Block
public import CFSG.LocalAnalysis.StandardType.GGSecFiveCompatRestDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePresTagClassical

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

section Strong

@[expose] def GGSecFiveA11StrongInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGSecFiveRestHyp p B Bs x L D J → GGSecFiveA11Config p B Bs x L D J →
      ∃ (ψ₀ : (ggU .PSL 12 1).K →* G) (y : G) (K : Subgroup G) (u : (ggU .PSL 12 1).K),
        GGPresentsG0 (ggG0 p B x L D J) (ggU .PSL 12 1).D .PSL 12 1 ψ₀ ∧ GGNbr p B x D J y K ∧
          K = (ψ₀.comp ((MulAut.conj u).toMonoidHom.comp
            (slBlockHom₃ 8 (GaloisField 2 1)))).range

theorem ggSecFiveA11Input_of_strong (h : GGSecFiveA11StrongInput) : GGSecFiveA11Input := by
  intro G _ _ p B Bs x L D J hR hA
  obtain ⟨ψ₀, _y, _K, _u, hpres, -, -⟩ := h G p B Bs x L D J hR hA
  obtain ⟨⟨hadm, -⟩, ⟨hrange, hker⟩, -⟩ := hpres
  refine Or.inr (Or.inr ⟨.PSL, 12, 1, ?_⟩)
  exact ggSecFivePres_of_psi_PSL hadm (by decide) ψ₀ hker hrange

theorem ggSecFiveCompatRestA11Input_of_strong (h : GGSecFiveA11StrongInput) :
    GGSecFiveCompatRestA11Input := by
  intro G _ _ p B Bs x L D J hcfg hOp hInn hNT hA hd t n f ψ hpres hL
  have hR : GGSecFiveRestHyp p B Bs x L D J :=
    ⟨hcfg, hOp, hInn, hNT, hd, fun ⟨m, f', hs⟩ => hL hs.leviCase⟩
  obtain ⟨ψ₀, y, K, u, hpres₀, hK, hKeq⟩ := h G p B Bs x L D J hR hA
  refine ⟨.PSL, 12, 1, ψ₀, hpres₀, K, Or.inr ⟨y, hK⟩, ?_⟩
  rw [hKeq]
  exact ggCompatPresented_slBlock₃_conj (n := 8) (f := 1) (by norm_num) le_rfl hpres₀.2.1.2 u

end Strong

end CFSG.StandardType

end
