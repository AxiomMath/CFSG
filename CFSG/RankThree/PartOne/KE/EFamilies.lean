module

public import CFSG.RankThree.PartOne.KE.FamilyArith
import CFSG.RankThree.Chevalley.SteinbergCFHigherExceptionalDefiningComponent
import CFSG.RankThree.Chevalley.SteinbergBNSplitTorusComponentExclusion
import CFSG.RankThree.Chevalley.SteinbergBTTwistedE6DefiningExclusion
import CFSG.RankThree.Chevalley.SteinbergBNTwistedE6QuadraticExclusion
import CFSG.RankThree.OddKernel.ThreeComplementQuotient
import CFSG.RankThree.PartOne.KE8F.E8Phi4Five
public import CFSG.RankThree.PartOne.KE.Statements

public section

namespace CFSG.RankThree.PartOne.KE

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.RankThree.LocalRank
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.Blueprint (ChevalleyExceptionalModel)
open CFSG.RankThree.Chevalley

theorem ordinary_E_prefix {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (N : Subgroup X) [N.Normal] (hN : ¬ p ∣ Nat.card N) (hX : localRank p X ≤ 3)
    (L : Subgroup (X ⧸ N)) {τ : StatedLieTag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {ℓ f : ℕ}
    (hℓ : ℓ.Prime) (hmod : ChevalleyExceptionalModel (L ⧸ Subgroup.center L) τ ℓ f) :
    ℓ ≠ p ∧ ¬ (p : ℤ) ∣ cycloVal 1 ℓ f ∧ (ℓ ≠ 2 → ¬ (p : ℤ) ∣ cycloVal 2 ℓ f) := by
  have hτ' : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
    rcases hτ with h | h | h <;> simp [h]
  have hℓp : ℓ ≠ p := by
    rintro rfl
    exact higher_ordinary_exceptional_defining_prime_actual_component_exclusion hp hp3 N hN hX L
      hτ' f hmod
  have hq1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ hℓ.pos
  have hodd : ℓ ≠ 2 → ¬ (p : ℤ) ∣ cycloVal 1 ℓ f ∧ ¬ (p : ℤ) ∣ cycloVal 2 ℓ f := fun hℓ2 =>
    not_dvd_cycloVal_one_two_of_not_dvd_sq hq1 fun hd =>
      odd_higher_ordinary_exceptional_cross_prime_quadratic_factor_exclusion hp hp3 N hN hX L hℓ
        hℓ2 hd hτ' hmod
  refine ⟨hℓp, ?_, fun hℓ2 => (hodd hℓ2).2⟩
  by_cases hℓ2 : ℓ = 2
  · subst hℓ2
    exact not_dvd_cycloVal_one_of hq1
      (even_ordinary_E_split_prime_actual_component_exclusion hp hp3 N hN hX L hτ hmod)
  · exact (hodd hℓ2).1

theorem originalE7_of_endpoints (hq : EvenE7E8QPlusExclusion) (hE : E7Endpoints) :
    OriginalE7ComponentLocalCoreOddAction := by
  intro X _ _ hX p hp hp3 N _ hN E hE' hEc t ht ht1 L hL ℓ f hℓ hf hmod hpT hEL hSL
  have hrank : localRank p X ≤ 3 :=
    (CFSG.RankThree.OddKernel.localRank_le_evenRank hp (by omega)).trans hX
  obtain ⟨hℓp, h1, h2'⟩ := ordinary_E_prefix hp hp3 N hN hrank L (τ := .E7)
    (Or.inr (Or.inl rfl)) hℓ hmod
  have hq1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ hℓ.pos
  have h2 : ¬ (p : ℤ) ∣ cycloVal 2 ℓ f := by
    by_cases hℓ2 : ℓ = 2
    · subst hℓ2
      exact not_dvd_cycloVal_two_of (hq X p hp hp3 N hN hrank L hL .E7 (Or.inl rfl) f hf hmod)
    · exact h2' hℓ2
  obtain ⟨hrow, hguard, -⟩ :=
    exact_E_type_and_triality_cross_prime_factor_exhaustion hp hp3 hℓp hmod
  have hguard' : SmallPrimeGuard p ℓ f := hguard
  obtain ⟨m, hm, hdvd⟩ := (hrow hpT).2.1 rfl
  have hd : (p : ℤ) ∣ cycloVal m ℓ f := hdvd
  have app : ∀ {Cond : ℕ → ℕ → ℕ → Prop}, OddEndpoint .E7 Cond → Cond p ℓ f →
      ComponentLocalCoreOddConclusion p E t L := fun H hc =>
    H (X ⧸ N) p ℓ f hp hp3 hℓ hℓp hf hc E hE' hEc t ht ht1 L hL hmod hEL hSL
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hd h1
  · exact absurd hd h2
  · exact app hE.phi3Phi6 (Or.inl hd)
  · exact app hE.phi4Phi12 (Or.inl hd)
  · exact app hE.phi5Phi10 ⟨five_lt_of_dvd_five hguard' h1 hd, Or.inl hd⟩
  · exact app hE.phi3Phi6 (Or.inr hd)
  · exact app hE.phi7Phi14 ⟨seven_lt_of_dvd_seven hguard' h1 hd, Or.inl hd⟩
  · exact app hE.phi8 hd
  · exact app hE.coxeter (Or.inl hd)
  · exact app hE.phi5Phi10 ⟨five_lt_of_dvd_ten hguard' h2 hd, Or.inr hd⟩
  · exact app hE.phi4Phi12 (Or.inr hd)
  · exact app hE.phi7Phi14 ⟨seven_lt_of_dvd_fourteen hguard' h2 hd, Or.inr hd⟩
  · exact app hE.coxeter (Or.inr hd)

theorem originalE8_of_endpoints (hq : EvenE7E8QPlusExclusion) (hE : E8Endpoints) :
    OriginalE8ComponentLocalCoreOddAction := by
  intro X _ _ hX p hp hp3 N _ hN E hE' hEc t ht ht1 L hL ℓ f hℓ hf hmod hpT hEL hSL
  have hrank : localRank p X ≤ 3 :=
    (CFSG.RankThree.OddKernel.localRank_le_evenRank hp (by omega)).trans hX
  obtain ⟨hℓp, h1, h2'⟩ := ordinary_E_prefix hp hp3 N hN hrank L (τ := .E8)
    (Or.inr (Or.inr rfl)) hℓ hmod
  have hq1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ hℓ.pos
  have h2 : ¬ (p : ℤ) ∣ cycloVal 2 ℓ f := by
    by_cases hℓ2 : ℓ = 2
    · subst hℓ2
      exact not_dvd_cycloVal_two_of (hq X p hp hp3 N hN hrank L hL .E8 (Or.inr rfl) f hf hmod)
    · exact h2' hℓ2
  obtain ⟨hrow, hguard, hΦ20⟩ :=
    exact_E_type_and_triality_cross_prime_factor_exhaustion hp hp3 hℓp hmod
  have hguard' : SmallPrimeGuard p ℓ f := hguard
  obtain ⟨m, hm, hdvd⟩ := (hrow hpT).2.2.1 rfl
  have hd : (p : ℤ) ∣ cycloVal m ℓ f := hdvd
  have app : ∀ {Cond : ℕ → ℕ → ℕ → Prop}, OddEndpoint .E8 Cond → Cond p ℓ f →
      ComponentLocalCoreOddConclusion p E t L := fun H hc =>
    H (X ⧸ N) p ℓ f hp hp3 hℓ hℓp hf hc E hE' hEc t ht ht1 L hL hmod hEL hSL
  have phi4_case : (p : ℤ) ∣ cycloVal 4 ℓ f → ComponentLocalCoreOddConclusion p E t L := fun h4 => by
    by_cases h5 : p = 5
    · by_cases hℓ2 : ℓ = 2
      · exact app hE.phi4 ⟨h4, fun _ => hℓ2⟩
      · subst h5
        exact absurd hmod (KE8F.E8Phi4FiveOddExclusion N hN hrank L hℓ hℓ2 (by exact_mod_cast h4))
    · exact app hE.phi4 ⟨h4, fun h => absurd h h5⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  · exact absurd hd h1
  · exact absurd hd h2
  · exact app hE.phi3Phi6 (Or.inl hd)
  · exact phi4_case hd
  · exact app hE.phi5Phi10 ⟨five_lt_of_dvd_five hguard' h1 hd, Or.inl hd⟩
  · exact app hE.phi3Phi6 (Or.inr hd)
  · exact app hE.phi7Phi14 ⟨seven_lt_of_dvd_seven hguard' h1 hd, Or.inl hd⟩
  · exact app hE.phi8Phi12 (Or.inl hd)
  · exact app hE.phi9Phi18 (Or.inl hd)
  · exact app hE.phi5Phi10 ⟨five_lt_of_dvd_ten hguard' h2 hd, Or.inr hd⟩
  · exact app hE.phi8Phi12 (Or.inr hd)
  · exact app hE.phi7Phi14 ⟨seven_lt_of_dvd_fourteen hguard' h2 hd, Or.inr hd⟩
  · exact app hE.phi15Phi30 (Or.inl hd)
  · exact app hE.phi9Phi18 (Or.inr hd)
  ·
    by_cases h5 : 5 < p
    · exact app hE.phi20Phi24 (Or.inr ⟨h5, hd⟩)
    · have hp5 : p = 5 := by
        rcases (show p = 4 ∨ p = 5 by omega) with h | h
        · subst h
          norm_num at hp
        · exact h
      subst hp5
      have h20 : ((5 : ℕ) : ℤ) ∣ cycloVal 20 ℓ f := hd
      have h4 : ((5 : ℕ) : ℤ) ∣ cycloVal 4 ℓ f := by
        have := (hΦ20.2 ((ℓ ^ f : ℕ) : ℤ)).1 (by exact_mod_cast h20)
        exact_mod_cast this
      exact phi4_case h4
  · exact app hE.phi20Phi24 (Or.inl hd)
  · exact app hE.phi15Phi30 (Or.inr hd)

theorem originalE6_of_endpoints (hE : E6Endpoints) :
    OriginalE6AndTwistedE6ComponentLocalCoreOddAction := by
  intro X _ _ hX p hp hp3 N _ hN E hE' hEc t ht ht1 L hL τ hτ ℓ f hℓ hf hmod hpT hEL hSL
  have hrank : localRank p X ≤ 3 :=
    (CFSG.RankThree.OddKernel.localRank_le_evenRank hp (by omega)).trans hX
  have hq1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ hℓ.pos
  rcases hτ with rfl | rfl
  ·
    obtain ⟨hℓp, h1, h2'⟩ := ordinary_E_prefix hp hp3 N hN hrank L (τ := .E6) (Or.inl rfl) hℓ hmod
    obtain ⟨hrow, hguard, -⟩ :=
      exact_E_type_and_triality_cross_prime_factor_exhaustion hp hp3 hℓp hmod
    have hguard' : SmallPrimeGuard p ℓ f := hguard
    obtain ⟨m, hm, hdvd⟩ := (hrow hpT).1 rfl
    have hd : (p : ℤ) ∣ cycloVal m ℓ f := hdvd
    have app : ∀ {Cond : ℕ → ℕ → ℕ → Prop}, OddEndpoint .E6 Cond → Cond p ℓ f →
        ComponentLocalCoreOddConclusion p E t L := fun H hc =>
      H (X ⧸ N) p ℓ f hp hp3 hℓ hℓp hf hc E hE' hEc t ht ht1 L hL hmod hEL hSL
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd hd h1
    · by_cases hℓ2 : ℓ = 2
      · exact app hE.evenQPlus ⟨hℓ2, hd⟩
      · exact absurd hd (h2' hℓ2)
    · exact app hE.phi3 hd
    · exact app hE.phi4 hd
    · exact app hE.phi5 ⟨five_lt_of_dvd_five hguard' h1 hd, hd⟩
    · exact app hE.phi6 hd
    · exact app hE.phi8 hd
    · exact app hE.phi9 hd
    · exact app hE.phi12 hd
  ·
    have hℓp : ℓ ≠ p := by
      rintro rfl
      exact twisted_E6_defining_prime_actual_component_exclusion hp hp3 N hN hrank L f hmod
    obtain ⟨h1, h2⟩ := not_dvd_cycloVal_one_two_of_not_dvd_sq hq1
      (twisted_E6_cross_prime_actual_component_quadratic_factor_exclusion hp hp3 N hN hrank L
        hmod).1
    obtain ⟨hrow, hguard, -⟩ :=
      exact_E_type_and_triality_cross_prime_factor_exhaustion hp hp3 hℓp hmod
    have hguard' : SmallPrimeGuard p ℓ f := hguard
    obtain ⟨m, hm, hdvd⟩ := (hrow hpT).2.2.2.1 rfl
    have hd : (p : ℤ) ∣ cycloVal m ℓ f := hdvd
    have app : ∀ {Cond : ℕ → ℕ → ℕ → Prop}, OddEndpoint .twistedE6 Cond → Cond p ℓ f →
        ComponentLocalCoreOddConclusion p E t L := fun H hc =>
      H (X ⧸ N) p ℓ f hp hp3 hℓ hℓp hf hc E hE' hEc t ht ht1 L hL hmod hEL hSL
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd hd h1
    · exact absurd hd h2
    · exact app hE.twPhi3 hd
    · exact app hE.twPhi4 hd
    · exact app hE.twPhi6 hd
    · exact app hE.twPhi8 hd
    · exact app hE.twPhi10 ⟨five_lt_of_dvd_ten hguard' h2 hd, hd⟩
    · exact app hE.twPhi12 hd
    · exact app hE.twPhi18 hd

end CFSG.RankThree.PartOne.KE
