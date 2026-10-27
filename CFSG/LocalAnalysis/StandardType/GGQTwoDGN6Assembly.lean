module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDGNAssembly
public import CFSG.LocalAnalysis.StandardType.GGQTwoDNbr6Defs

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly CFSG.ClassicalInvolution.Phan

@[expose] def QTwoOrthJAnchor4Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → ∀ (Bs X J : Subgroup G) (x : G)
    (Φ : OrthTorus.OrthFrameCore p Bs X), Nat.card Φ.F = 2 → 4 ≤ Φ.r →
      Subgroup.center ↥X = ⊥ → x ∈ Bs → J ≤ X →
        IsComponentOf J (X ⊓ Subgroup.centralizer ({x} : Set G)) →
          ∃ x' y' : OmPlusIdx Φ.r,
            omPlusRefl p x' * omPlusRefl p y' ≠ omPlusRefl p y' * omPlusRefl p x' ∧
              Φ.img (Φ.rank2 x' y') ≤ J

theorem qTwoD_gn_of_chart4 {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs L D J : Subgroup G}
    {x y : G} {K' : Subgroup G} (hC : GGConfig p B Bs x L D J) (hLB : GGLBalanceInput)
    (hPJ : GGStdSubPrimeInput) (hJA4 : QTwoOrthJAnchor4Input) (hnbr : GGNbr p B x D J y K')
    (hchart : QTwoDL1Chart4 p B Bs K') :
    K' ≤ ⨆ (g : G) (_ : g ∈ K') (_ : ∃ φ : MulAut ↥Bs,
        g ∈ Subgroup.normalizer (Bs : Set G) ∧ ∀ b : ↥Bs, ((φ b : ↥Bs) : G) = g * b * g⁻¹),
      J.map (MulAut.conj g).toMonoidHom := by
  have hp : p.Prime := hC.1.2.2.2.2.2.1.1
  rcases hchart with ⟨F, _, _, _, n, ψ, hF, hloc, hrange, hdiag, -⟩ | ⟨Φ, hF, h4, -, hZ⟩
  · have hn4 : 4 ≤ n := hloc.four_le
    have hn : 5 ≤ n := by
      by_contra hlt
      have hn : n = 4 := by omega
      subst n
      exact qTwoD_not_unitaryChart_four hC hLB hPJ hnbr hF hloc hrange hdiag
    exact qTwoD_gn_of_unitaryChart hC hLB hPJ hnbr hF hloc hrange hdiag hn
  · haveI : Fact p.Prime := ⟨hp⟩
    have hJX : J ≤ K' := le_of_ggNbr hLB hC.1 hC.2.2 (hPJ G p B x L D J hC.1 hC.2.2) hnbr
    have hcomp := ggIsComponentOf_inf_centralizer_nbr hC hnbr hJX
    have hxBs : x ∈ Bs := hC.2.1.1 hC.1.2.2.2.2.2.2.1.2.1
    obtain ⟨x', y', hnc, hle⟩ := hJA4 G p hp Bs K' J x Φ hF h4 hZ hxBs hJX hcomp
    exact qTwoD_gn_of_orthChart Φ hF hnc hle

section Inputs

theorem ggQTwoGNInputOn_of_inputs4 {R : ℕ → Prop}
    (hLB : GGLBalanceInput) (hPJ : GGStdSubPrimeInput) (hChN : GGQTwoDL1Chart4NbrInputOn R)
    (hJA4 : QTwoOrthJAnchor4Input) :
    GGQTwoGNInputOn R := by
  intro G _ _ p B Bs x L D J 𝒦 ι M e hcfg m e' hRm hM y K' hnbr _
  exact qTwoD_gn_of_chart4 hcfg.1.1.1 hLB hPJ hJA4 hnbr
    (hChN G p B Bs x L D J 𝒦 ι M e hcfg m e' hRm hM y K' hnbr)

end Inputs

end CFSG.StandardType.QTwo

end
