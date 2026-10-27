module

public import CFSG.Assembly.DichotomyDefs
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PrimeOrderCentralizerTest

public section

universe u v w

namespace CFSG.Assembly.Dichotomy

private theorem pCore_eq_open (p : ℕ) (X : Type*) [Group X] :
    pCore p X = CFSG.Open.pCore p X := rfl

theorem _root_.CFSG.Milestones.cls_involution_centralizers_characteristic_two_transfer (G : Type) [Group G] [Finite G]
    (hC : ∀ t : G, orderOf t = 2 → dichotomyCharP 2 (Subgroup.centralizer ({t} : Set G))) :
    IsCharTwoType G := by
  intro H hH
  obtain ⟨P, hP, htwo, rfl⟩ := hH
  let H := Subgroup.normalizer (P : Set G)
  have hcentralizers : ∀ t : G, orderOf t = 2 →
      Subgroup.centralizer
          (CFSG.Open.pCore 2 (Subgroup.centralizer ({t} : Set G)) :
            Set (Subgroup.centralizer ({t} : Set G))) ≤
        CFSG.Open.pCore 2 (Subgroup.centralizer ({t} : Set G)) := by
    intro t ht
    simpa only [dichotomyCharP] using hC t ht
  have hlocal := CFSG.RankThreeCoreUniqueness.Helpers.prime_order_centralizer_local_characteristic
    2 Nat.prime_two hcentralizers P hP htwo
  intro x hx
  have hinternal : (⟨x, hx.1⟩ : H) ∈
      Subgroup.centralizer (CFSG.Open.pCore 2 H : Set H) := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro y hy
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hx.2 y.val
      (Subgroup.mem_map_of_mem H.subtype (pCore_eq_open 2 H ▸ hy))
  exact Subgroup.mem_map_of_mem H.subtype (pCore_eq_open 2 H ▸ hlocal hinternal)

end CFSG.Assembly.Dichotomy
