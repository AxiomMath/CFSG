module

public import CFSG.RankThree.PartOne.KE.EvenE7E8QPlusLang
public import CFSG.RankThree.PartOne.KE.EndpointStatements
public import CFSG.RankThree.Classical.SteinbergBJOrthogonalDefiningComponent

public section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.RankThree.Chevalley (cartanFunctional cartanFunctional_single
  exists_central_surjection_adjointGroup)

theorem evenE7E8QPlusExclusion : EvenE7E8QPlusExclusion := by
  intro X _ _ p hp hp3 N _ hN hX L _ τ hτ f hf hmod hpq
  have hL := CFSG.RankThree.Classical.localRank_le_of_le_quotient hp (by omega) N hN L
  have key : ∀ τ' : Tag, (τ' = .E7 ∨ τ' = .E8) →
      UntwistedChevalleyModel (L ⧸ Subgroup.center L) τ' (2 ^ f) → False := by
    rintro τ' hτ' ⟨K, _, _, hK, ⟨e⟩⟩
    obtain ⟨φ, hφ, hker⟩ := exists_central_surjection_adjointGroup e
    obtain ⟨θ, n, hθ, hn2, hn⟩ :=
      even_E7_E8_qplus_rational_reflection_torus τ' hτ' hf K hK hp hp3 hpq
    have hrank : 7 ≤ τ'.rank := by rcases hτ' with rfl | rfl <;> decide
    obtain ⟨-, -, -, -, -, -, -, -, hrk⟩ :=
      CFSG.RankThree.CentralCover.reflection_normalizers_actual_central_cover_fixed_hyperplane_rank
        (⊤ : Subgroup L) φ hφ hker hp (by omega) (by omega) θ hθ (cartanFunctional τ' p)
        (cartanFunctional_single τ' p) n hn (hn2 ⟨0, by omega⟩)
    omega
  rcases hτ with rfl | rfl
  · exact key .E7 (Or.inl rfl) hmod.2
  · exact key .E8 (Or.inr rfl) hmod.2

end CFSG.RankThree.PartOne.KE
