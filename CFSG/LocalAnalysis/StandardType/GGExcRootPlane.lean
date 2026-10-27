module

public import CFSG.LocalAnalysis.StandardType.GGExcStdFormLemmas
public import CFSG.LocalAnalysis.StandardType.GGAssemblyElevenDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank

section Plane

theorem rootPlaneAt_exc_of_stdForm (hreg : GGExcRegimeInput) (hstd : GGSixExcStandardFormInput)
    (hplane : GGLatAdmPlaneExc) (t : StatedLieTag) (ht : GGExcFive t) : GGRootPlaneAt t := by
  intro G _ _ p B Bs x L D J t' n f ψ ht' hctx s1
  subst t'
  have hp := hctx.prime
  have hp2 := hctx.ne_two
  obtain ⟨S, π, F, hS, hπ, -, -, -, hF3, -⟩ :=
    hstd G p B Bs x L D J t n f ψ ht hctx s1
      (hreg G p B Bs x L D J t n f ψ ht hctx s1)
  obtain ⟨f₁, f₂, h1π, h2π, h1, h2, hind, ⟨α, hα, hαπ, hα1, hα2⟩, hO⟩ :=
    hplane t f ht S π hS hπ p hp hp2 (f = 1)
  obtain ⟨E, hEB, hEab, hEcard, hEmem⟩ :=
    F.exists_plane_subgroup hp hctx.bstar.2.1 f₁ f₂ h1π h2π h1 h2 hind
  obtain ⟨γ, u, hγ, hcent, r, hr, hr2⟩ := hF3 α hα hαπ
  refine ⟨E, γ, u, r, hEB, hEab, hEcard, hγ, ?_, hr, hr2, ?_⟩
  ·
    intro e he
    obtain ⟨heB, a, c, hcoord, -⟩ := hEmem e he
    exact hcent ⟨e, heB⟩ (by rw [hcoord, latChar_smul_add, hα1, hα2]; simp)
  ·
    intro e he hne
    obtain ⟨heB, a, c, hcoord, hac⟩ := hEmem e he
    have hacne : a ≠ 0 ∨ c ≠ 0 := hac hne
    obtain ⟨O, hOrb, hnsolv, hcardO⟩ := hO a c hacne
    rw [← hcoord] at hOrb
    have hb1 : (⟨e, heB⟩ : Bs) ≠ 1 := fun h => hne (congrArg Subtype.val h)
    obtain ⟨L₁, hL₁, hL⟩ := F.comp_ex ⟨e, heB⟩ hb1 O hOrb hnsolv
    exact Or.inr ⟨L₁, hL₁, F.card_inf_centralizer_le hp L₁ O hL hcardO⟩

theorem rootPlaneExc_of_stdForm (hreg : GGExcRegimeInput) (hstd : GGSixExcStandardFormInput)
    (hplane : GGLatAdmPlaneExc) : GGRootPlaneExcRound11 :=
  ⟨rootPlaneAt_exc_of_stdForm hreg hstd hplane .F4 (Or.inl rfl),
    rootPlaneAt_exc_of_stdForm hreg hstd hplane .E6 (Or.inr (Or.inl rfl)),
    rootPlaneAt_exc_of_stdForm hreg hstd hplane .E7 (Or.inr (Or.inr (Or.inl rfl))),
    rootPlaneAt_exc_of_stdForm hreg hstd hplane .E8 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),
    rootPlaneAt_exc_of_stdForm hreg hstd hplane .twistedE6
      (Or.inr (Or.inr (Or.inr (Or.inr rfl))))⟩

end Plane

end CFSG.StandardType
