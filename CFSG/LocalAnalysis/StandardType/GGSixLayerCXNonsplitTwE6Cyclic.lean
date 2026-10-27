module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitF4Dvd
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitTwE6Arith
public import CFSG.RankThree.PartOne.KE.CTTwistedEight
public import CFSG.RankThree.PartOne.KE.CTTwistedTwelve
public import CFSG.RankThree.PartOne.KE.CTTwistedEighteen

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KE CFSG.LieType.Chevalley

namespace TwE6Nonsplit

section Regular


theorem not_isComponentOf_centralizer_twE6_of_dvd_phi_regular {K : Type} [Field K] [Finite K]
    [CharP K 2] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (2 ^ f)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {m : ℕ}
    (hm : m = 8 ∨ m = 12 ∨ m = 18)
    (hpf : (p : ℤ) ∣ (CFSG.RankThree.Chevalley.exhaustionPhi m).eval ((2 ^ f : ℕ) : ℤ))
    {a : twistedE6RootGroup K σ} (ha : orderOf a = p)
    {X : Subgroup (twistedE6RootGroup K σ)} :
    ¬ IsComponentOf X (Subgroup.centralizer ({a} : Set (twistedE6RootGroup K σ))) := by
  rcases hm with rfl | rfl | rfl
  · obtain ⟨-, -, k, hc⟩ :=
      twisted_E6_eight_cyclic_sylow Nat.prime_two hf K hK σ hσ hp hp3 hpf
    obtain ⟨T, hT, -, -, -, -, -, hcent⟩ := hc
    obtain ⟨g, -, hg⟩ := hcent a ha
    exact F4Nonsplit.not_isComponentOf_of_conj_centralizer_cyclic hT hg
  · obtain ⟨-, -, k, hc⟩ :=
      twisted_E6_twelve_cyclic_sylow Nat.prime_two hf K hK σ hσ hp hp3 hpf
    obtain ⟨T, hT, -, -, -, -, -, hcent⟩ := hc
    obtain ⟨g, -, hg⟩ := hcent a ha
    exact F4Nonsplit.not_isComponentOf_of_conj_centralizer_cyclic hT hg
  · obtain ⟨-, -, k, hc⟩ :=
      twisted_E6_eighteen_cyclic_sylow Nat.prime_two hf K hK σ hσ hp hp3 hpf
    obtain ⟨T, hT, -, -, -, -, -, hcent⟩ := hc
    obtain ⟨g, -, hg⟩ := hcent a ha
    exact F4Nonsplit.not_isComponentOf_of_conj_centralizer_cyclic hT hg

end Regular

end TwE6Nonsplit

end CFSG.StandardType
