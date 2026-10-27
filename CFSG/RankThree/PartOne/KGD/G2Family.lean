module

public import CFSG.RankThree.PartOne.KGD.G2Even
public import CFSG.RankThree.PartOne.KGD.G2Three
public import CFSG.RankThree.PartOne.KE.Statements

public section

namespace CFSG.RankThree.PartOne.KGD

open CFSG.RankThree.Chevalley

theorem g2_family : G2CrossPrimeActualComponentOddAction := by
  intro G _ _ p hp hp3 E hE hEcard t ht ht1 L hL ℓ f hℓ hℓp hf hT hEL hSL
  by_cases h2 : ℓ = 2
  · subst h2
    exact g2_even_component hp hp3 hE hEcard ht ht1 hL hT hEL hSL
  by_cases h3 : ℓ = 3
  · subst h3
    exact g2_three_component hp hp3 hE hEcard ht ht1 hL hT hEL hSL
  obtain ⟨h1, h2', h3', h4⟩ := odd_nonthree_G2_cross_prime_actual_component_odd_action hp hp3 hE
    hEcard ht ht1 hL hℓ h2 h3 hℓp hf hT hEL hSL
  exact ⟨⟨h1, h2', h3'⟩, h4⟩

end CFSG.RankThree.PartOne.KGD
