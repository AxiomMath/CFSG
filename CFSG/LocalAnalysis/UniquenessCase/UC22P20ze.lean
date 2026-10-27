module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P20yc
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20za
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20zda

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22pw_ch (hR1 : uc22pwCartanRankOne) (hR2 : uc22pwCartanGraph) (hE : UC22P20gExcFacts)
    (hu38 : uc22p20oU38Witness) (hB : ListBNonabelian) (D : Data G) (h1930 : H1930 D)
    (h20_7 : S20_7 D) :
    ∀ L0 ∈ calLLow D.T D.M, ∀ n : ℕ, NParam L0 n →
      ∃ B0 : Subgroup G, B0 ∈ calB1 D.T D.M L0 ∧ piSet B0 = etaSet n ∧ AlphaCond D.T B0 n ∧
        B0 ≤ D.M := by
  intro L hL n hn
  have hLc : L ∈ calL D.T D.M := hL.prop
  obtain ⟨hn2, h1 | h2 | ⟨K, K₂, t, htT, hK, hK₂, hne, hLK, ht, hsh⟩⟩ :=
    uc22pw_cases hE D h1930 h20_7 hL hn
  · obtain ⟨hq, hsh⟩ := h1
    obtain ⟨E, hE'⟩ := uc22pw_good_rankOne hR1 D hLc hq hn2 hsh
    exact uc22pw_lift D hB h1930 hLc hE'
  · obtain ⟨hq, hsh⟩ := h2
    obtain ⟨E, hE'⟩ := uc22pw_good_graph hR2 D hLc hq hn2 hsh
    exact uc22pw_lift D hB h1930 hLc hE'
  · obtain ⟨E, hE'⟩ := uc22pw_good_two hR1 hu38 D hLc hK hK₂ hne hLK htT ht hn2 hsh
    exact uc22pw_lift D hB h1930 hLc hE'

theorem uc22pw_ch_of_trivial (Ch : Choice2011 G) (hCh : ∀ L₀ B₀ : Subgroup G, Ch L₀ B₀)
    (hR1 : uc22pwCartanRankOne) (hR2 : uc22pwCartanGraph) (hE : UC22P20gExcFacts)
    (hu38 : uc22p20oU38Witness) (hB : ListBNonabelian) (D : Data G) (h1930 : H1930 D)
    (h20_7 : S20_7 D) :
    ∀ L0 ∈ calLLow D.T D.M, ∀ n : ℕ, NParam L0 n →
      ∃ B0 : Subgroup G, Ch L0 B0 ∧ B0 ∈ calB1 D.T D.M L0 ∧ piSet B0 = etaSet n ∧
        AlphaCond D.T B0 n ∧ B0 ≤ D.M := by
  intro L0 hL n hn
  obtain ⟨B0, h1, h2, h3, h4⟩ := uc22pw_ch hR1 hR2 hE hu38 hB D h1930 h20_7 L0 hL n hn
  exact ⟨B0, hCh L0 B0, h1, h2, h3, h4⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
