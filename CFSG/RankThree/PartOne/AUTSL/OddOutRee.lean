module

public import CFSG.RankThree.PartOne.S11d.OutAbstract
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LocalAnalysis.ComponentClassification.LiteratureLocalSmallReeOuter
import CFSG.LocalAnalysis.ComponentInitial.BasicFacts

public section

namespace CFSG.RankThree.PartOne.AUTSL

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.OutStructure
open CFSG.ComponentClassification.LiteratureLocal.SmallRee (outer_reeGamma_cyclic)


theorem outPNice_twistedG2 {p : ℕ} (hp : p.Prime) {X : Type} [Group X] {f : ℕ}
    (h : ReeTitsModel X .twistedG2 3 f) : OutPNice p X := by
  obtain ⟨hfin, -, -, ⟨a, ha, hfa⟩, hiso⟩ := small_Ree_model_Schreier X 3 f h
  obtain ⟨-, a', hfa', K, _, _, hK, hw⟩ := h
  have ha' : a' = a := by omega
  subst ha'
  have : CharP K ReeTag.G2.prime :=
    finite_field_prime_power_characteristic Nat.prime_three (by omega) hK
  obtain ⟨E⟩ := hiso a' K hfa hK hw
  have hK' : Nat.card K = 3 ^ (2 * a' + 1) := by rw [hK, hfa]
  have : Finite (ReeTag.G2.reeGamma K a') := Finite.of_equiv X E.toEquiv
  exact OutPNice.of_mulEquiv E (outPNice_of_isCyclic_outer hp (outer_reeGamma_cyclic ha hK').1)

end CFSG.RankThree.PartOne.AUTSL
