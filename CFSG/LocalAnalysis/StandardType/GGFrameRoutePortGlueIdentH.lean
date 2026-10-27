module

public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortGlueIdentAut
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP10E6Real
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP10E6Norm
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9Wa
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9U8

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Assembly CFSG.Open CFSG.StandardType

theorem card_automizer_centralizer_le_of_end
    {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G}
    (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ 7) (hxBs : x ∈ Bs) (hx1 : x ≠ 1)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hNL : Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({x} : Set G) ≤
      Subgroup.normalizer (L : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hBstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hNT : GGNoTransvection 3 Bs)
    (hL : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twA, 6, 1⟩ ∨ lab = ⟨.twE6, 0, 1⟩) 3 Bs L) :
    Nat.card (ggAutomizer (Subgroup.centralizer ({x} : Set G)) Bs) ≤ 103680 := by
  refine (card_automizer_centralizer_le hBs hxBs hNT hN hNL hker).trans ?_
  rcases hL.elim_or with hL | hL
  · obtain ⟨k, F, hfield, hfin, θ, hlab, hF, hk3, hTB, hrk⟩ :=
      P9_Wa_tbGroup_twA (S := fun _ lab => lab = ⟨.twA, 6, 1⟩) hBs hcard (Or.inl rfl)
        hxBs hx1 hN hker hBstar (fun lab hlab => by rw [hlab]; exact ⟨rfl, rfl⟩) hL
    have hk6 : k = 6 := congrArg LargeEvenLabel.rank hlab
    obtain ⟨-, hdvd⟩ := P9_U_dim_and_card_dvd hF (by omega) (by omega) (by omega) hTB hrk
    have hk7 : k + 1 = 7 := by omega
    rw [hk7] at hdvd
    exact (Nat.le_of_dvd (Nat.mul_pos (by norm_num) (Nat.factorial_pos _)) hdvd).trans
      (by norm_num [Nat.factorial])
  · obtain ⟨e, hreal⟩ :=
      p10_twE6_realization (n := 7) hBs hcard (by norm_num) hxBs hx1 hN hker hBstar hL
    exact Nat.le_of_dvd (by norm_num)
      (p10i_twE6_normalizer_bound (ggGamma L hN).range e hreal)

end CFSG.StandardType.FrameRoute

end
