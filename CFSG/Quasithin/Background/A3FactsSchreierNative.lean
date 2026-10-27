module

public import CFSG.Quasithin.Background.A3FactsSchreier
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAssembly
public import CFSG.LocalAnalysis.ComponentClassification.SporadicSchreierDispatch
public import CFSG.Sporadic.Schreier.PairJ2Pairs
public import CFSG.Sporadic.Schreier.PairHSPairs
public import CFSG.Sporadic.Schreier.RuModel
public import CFSG.Sporadic.Schreier.TitsOuter

public section

namespace CFSG.Quasithin

namespace A3Facts

open CFSG.Blueprint CFSG.ComponentClassification
open CFSG.ComponentClassification.SporadicSchreierDispatch (SporadicSchreierCase)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem sporadicSchreierCase_of_J4_He
    (hJ4 : SporadicSchreierCase .J4)
    (hHe : SporadicSchreierCase .He) (s : TauCeti.SporadicName)
    (hs : s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨ s = .J1 ∨ s = .J2 ∨ s = .J4 ∨
      s = .HS ∨ s = .He ∨ s = .Ru) :
    SporadicSchreierCase s := by
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact SporadicSchreierDispatch.sporadicSchreierCase_M11
  · exact SporadicSchreierDispatch.sporadicSchreierCase_M12
  · exact SporadicSchreierDispatch.sporadicSchreierCase_M22
  · exact SporadicSchreierDispatch.sporadicSchreierCase_M23
  · exact SporadicSchreierDispatch.sporadicSchreierCase_M24
  · exact SporadicSchreierDispatch.sporadicSchreierCase_J1
  · exact SporadicSchreierDispatch.sporadicSchreierCase_of_outer
      CFSG.Sporadic.Schreier.AT_J2_Schreier.2.2
  · exact hJ4
  · exact SporadicSchreierDispatch.sporadicSchreierCase_of_outer
      CFSG.Sporadic.Schreier.AT_HS_Schreier.2
  · exact hHe
  · exact SporadicSchreierDispatch.sporadicSchreierCase_of_outer
      CFSG.Sporadic.RuSchreier.AT_Ru_model_Schreier.{0}.1

theorem simpleOutList_of_J4_He
    (hJ4 : SporadicSchreierCase .J4)
    (hHe : SporadicSchreierCase .He) : SimpleOutList := by
  intro S _ _ hS hnonab hlist
  have hTits : ∀ p f : ℕ, ReeTitsModel S .Tits p f → Group.IsSolvable (Outer S) :=
    fun p f h => (CFSG.Sporadic.Schreier.Tits.AT_Tits_model_Schreier S p f h).2
  rcases hlist with ⟨n, hn5, -, ⟨e⟩⟩ | ⟨p, -, -, hodd⟩ | (⟨f, hf⟩ | htits) | ⟨n, -, hmodel⟩ |
    ⟨s, hs, ⟨e⟩⟩
  · exact CatalogueSchreierAlternating.alternating_schreier_of_equiv n hn5 e
  · rcases hodd with ⟨f, -, hm⟩ | hm | hm <;>
      exact CatalogueSchreierAssembly.classical_model_outer_solvable hm
  · rcases hf with ⟨-, hm⟩ | ⟨-, hm⟩ | ⟨-, hm⟩ | ⟨-, hm⟩ | ⟨-, hm⟩ | ⟨-, hm⟩ | ⟨-, -, hm⟩ |
      ⟨-, -, hm⟩
    · exact CatalogueSchreierAssembly.classical_model_outer_solvable hm
    · exact CatalogueSchreierAssembly.classical_model_outer_solvable hm
    · exact CatalogueSchreierAssembly.classical_model_outer_solvable hm
    · exact CatalogueSchreierAssembly.classical_model_outer_solvable hm
    · exact CatalogueSchreierAssembly.exceptional_rep_outer_solvable hTits
        (Or.inl ⟨.G2, 2, f, by decide, hm⟩)
    · exact CatalogueSchreierAssembly.exceptional_rep_outer_solvable hTits
        (Or.inl ⟨.trialityD4, 2, f, by decide, hm⟩)
    · exact CatalogueSchreierAssembly.exceptional_rep_outer_solvable hTits
        (Or.inr (Or.inl ⟨.twistedF4, 2, f, by decide, hm⟩))
    · exact CatalogueSchreierAssembly.exceptional_rep_outer_solvable hTits
        (Or.inr (Or.inr ⟨2, f, hm⟩))
  · exact hTits 2 1 htits
  · exact CatalogueSchreierAssembly.classical_model_outer_solvable hmodel
  · have := hS
    exact sporadicSchreierCase_of_J4_He hJ4 hHe s hs S hnonab ⟨e⟩

theorem schreierList_of_J4_He
    (hJ4 : SporadicSchreierCase .J4)
    (hHe : SporadicSchreierCase .He) : SchreierList :=
  schreierList_of_simpleOutList (simpleOutList_of_J4_He hJ4 hHe)

theorem schreierSQTK_of_J4_He
    (hJ4 : SporadicSchreierCase .J4)
    (hHe : SporadicSchreierCase .He) : SchreierSQTK :=
  (schreierList_of_J4_He hJ4 hHe).toSQTK

end A3Facts

end CFSG.Quasithin
