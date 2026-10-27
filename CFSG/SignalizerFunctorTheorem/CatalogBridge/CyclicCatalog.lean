module

public import CFSG.SignalizerFunctorTheorem.CatalogBridge.Cyclic
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.Alternating
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.Sporadic

public section

open CFSG CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

theorem catalog_pSubgroupsCyclic
    (hHS : Nat.card (Outer (NativeSporadic.Carrier .HS)) ≤ 2)
    (hopen : CFSG.RankThree.PartOne.SporadicOuterOrderLeTwoSimple)
    {p : ℕ} (hp : p.Prime) {X : Type} [Group X] [Finite X] (hsimple : IsSimpleGroup X)
    (hnonab : ∃ a b : X, a * b ≠ b * a) (hcat : Catalog X) (hcop : Nat.Coprime p (Nat.card X)) :
    PSubgroupsCyclic p X := by
  have hpX : ¬ p ∣ Nat.card X := (Nat.Prime.coprime_iff_not_dvd hp).mp hcop
  have hp2 : p ≠ 2 := ne_two_of_coprime_card_of_simple_nonabelian hsimple hnonab hcop
  rcases hcat with ⟨q, hq, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨t, n, ℓ, f, hm⟩ | hexc | hspor
  · exfalso
    obtain ⟨a, b, hab⟩ := hnonab
    apply hab
    have h1 : e (a * b) = e (b * a) := by
      rw [map_mul, map_mul]
      exact mul_comm _ _
    exact e.injective h1
  · exact (hypothesisA_alternating hp hsimple hnonab hn e hcop).2.2.2.2.1
  · exact pSubgroupsCyclic_classical hm hp hp2 hpX
  · exact pSubgroupsCyclic_exceptional hexc hp hp2 hpX
  · exact (hypothesisA_sporadic hHS hopen hsimple hnonab hspor hp hcop).2.2.2.2.1

end CFSG.SignalizerFunctorTheorem.CatalogBridge
