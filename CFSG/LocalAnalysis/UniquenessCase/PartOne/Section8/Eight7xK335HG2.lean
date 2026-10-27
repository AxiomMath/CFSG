module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK335Inputs
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK335HSylRange
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanK12

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

theorem k335G2Local_holds
    : K335G2Local := by
  intro X _ _ p f hLie hp3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hp, hf1, -, h3⟩ := hLie.admissible
  have h4 : 4 ≤ p ^ f := by
    by_contra hlt
    have h33 : p ^ f = 3 := by omega
    have hdvd : p ∣ 3 := h33 ▸ dvd_pow_self p (by omega)
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hdvd)
  have hp2 : p = 2 → 2 ≤ f := by
    rintro rfl
    by_contra hf
    have : f = 1 := by omega
    subst this
    omega
  obtain ⟨S⟩ : Nonempty (Sylow 3 X) := inferInstance
  have hcen : Nat.card (Subgroup.center (S : Subgroup X)) = 3 :=
    g2SylowCenterCardThree_holds X p f hp hp3 hp2 hLie S
  have h3dvd : 3 ∣ Nat.card (Subgroup.center (S : Subgroup X)) := by rw [hcen]
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 3 h3dvd
  have hordw : orderOf ((w : (S : Subgroup X)) : X) = 3 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hw
  have hSL := CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan.k12SL_holds X p f hp
    hp3 h4 (hLie.chevalleyExceptionalModel (by decide)) S (w : (S : Subgroup X)) w.2 hordw
  obtain ⟨K, hKf, hKfin, hcase⟩ := hSL
  have hSw : (S : Subgroup X) ≤
      Subgroup.centralizer ({((w : (S : Subgroup X)) : X)} : Set X) := by
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp w.2 ⟨s, hs⟩).symm
  have : Fintype K := Fintype.ofFinite K
  rcases hcase with ⟨hcard, hmod, ⟨e⟩⟩ | ⟨hcard, hmod, ⟨e⟩⟩
  · obtain ⟨φ, hφ, S', hS', hS'φ⟩ := k335_exists_sylow_le_range (k335_isSylowOf_top S) hSw e
    exact ⟨K, hKf, inferInstance, CFSG.Open.StatedSL 3 K, Or.inl ⟨hmod, hcard, rfl⟩, φ, hφ,
      S', hS', hS'φ⟩
  · obtain ⟨φ, hφ, S', hS', hS'φ⟩ := k335_exists_sylow_le_range (k335_isSylowOf_top S) hSw e
    exact ⟨K, hKf, inferInstance, CFSG.Open.StatedSU 3 (p ^ f) K, Or.inr ⟨hmod, hcard, rfl⟩, φ,
      hφ, S', hS', hS'φ⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
