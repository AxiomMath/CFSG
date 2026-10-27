module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45FinalTorus
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45RestAssembly
public import CFSG.LocalAnalysis.StandardType.GGFieldNbrTableB

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGProp41I1Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D →
      GGFieldNbrCanonical p B Bs x D J → GGOpAutTrivial p Bs

theorem ggProp41Input_of_iOne
    (hex : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
      (L : Subgroup G), GGThmIHyp p B x L → GGBstar p B Bs →
        ∃ D J : Subgroup G, LargeEvenStdSub p B x L D J ∧
          Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D)
    (hc₀ : GGFieldNbrCanonicalInput) (h : GGProp41I1Input) : GGProp41Input := by
  intro G _ _ p B Bs x L D J hcfg _
  obtain ⟨D', J', hDJ', hI1⟩ := hex G p B Bs x L hcfg.1 hcfg.2.1
  have hcfg' : GGConfig p B Bs x L D' J' := ⟨hcfg.1, hcfg.2.1, hDJ'⟩
  exact h G p B Bs x L D' J' hcfg' hI1 (hc₀ G p B Bs x L D' J' hcfg')

end CFSG.StandardType

end
