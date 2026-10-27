module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K42i
public import CFSG.LocalAnalysis.UniquenessCase.UC6K42g
public import CFSG.LocalAnalysis.UniquenessCase.UC6K42h

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UCK (fixV)
open scoped commutatorElement

theorem fermat_strong_uc6 {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    ∀ n : ℕ, ∀ (G : Type) [Group G] [Finite G] (V : Type) [AddCommGroup V] [Module (ZMod p) V]
      [Finite V] (ρ : Representation (ZMod p) G V), Function.Injective ρ →
      ∀ r : ℕ, r.Prime → r ≠ p → r ≠ 2 → ∀ D : Subgroup G, Nat.card D = r → fixV ρ D = ⊥ →
      ∀ Q : Subgroup G, Nat.card Q = n → IsPGroup 2 Q → Q ≠ ⊥ → D ≤ normalizer (Q : Set G) →
        ⁅D, Q⁆ = Q → ∃ k : ℕ, orderOf (2 : ZMod r) = 2 ^ k := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro G _ _ V _ _ _ ρ hρ r hr hrp hr2 D hD hfix Q hQn hQ2 hQne hDQ hcomm
    obtain ⟨W, hWinv, hWnt, hWirr⟩ :=
      exists_irreducible_uc6 hp2 hr hr2 hrp ρ hρ hD hQ2 hQne hDQ
    obtain ⟨G₂, _, _, ρ₂, D₂, Q₂, hρ₂, hirr₂, hD₂, hfix₂, hQ₂2, hQ₂ne, hDQ₂, hcomm₂, htop₂, hcard₂⟩ :=
      restrict_data_uc6 hr ρ hD hfix hQ2 hDQ hcomm W hWinv hWnt hWirr
    by_cases hex : ∃ Q₁ : Subgroup G₂, Q₁ ≤ Q₂ ∧ D₂ ≤ normalizer (Q₁ : Set G₂) ∧ ⁅D₂, Q₁⁆ = Q₁ ∧
        Q₁ ≠ ⊥ ∧ Q₁ ≠ Q₂
    · obtain ⟨Q₁, hQ₁le, hDQ₁, hcomm₁, hQ₁ne, hQ₁ne2⟩ := hex
      have hlt : Nat.card Q₁ < n := by
        have : Nat.card Q₁ < Nat.card Q₂ := by
          by_contra hge
          exact hQ₁ne2 (Subgroup.eq_of_le_of_card_ge hQ₁le (not_lt.1 hge))
        omega
      exact ih (Nat.card Q₁) hlt G₂ ↥W ρ₂ hρ₂ r hr hrp hr2 D₂ hD₂ hfix₂ Q₁ rfl
        (hQ₂2.to_le hQ₁le) hQ₁ne hDQ₁ hcomm₁
    · push Not at hex
      exact fermat_main_uc6 hp2 ρ₂ hρ₂ hirr₂ hr hr2 hrp hD₂ hfix₂ hQ₂2 hQ₂ne hDQ₂ hcomm₂ htop₂
        (fun Q₁ h1 h2 h3 => by
          by_cases h4 : Q₁ = ⊥
          · exact Or.inl h4
          · exact Or.inr (hex Q₁ h1 h2 h3 h4))

theorem k42_fermat_uc6 : UCK.K42Fermat := by
  intro p hp hp2 G _ _ _ V _ _ _ ρ hρ r hr hrp hr2 D hD hfix Q hQ2 hQne hDQ hcomm
  haveI : Fact p.Prime := ⟨hp⟩
  exact fermat_strong_uc6 hp2 (Nat.card Q) G V ρ hρ r hr hrp hr2 D hD hfix Q rfl hQ2 hQne hDQ hcomm

theorem k42_uc6 : UCK.K42 := k42_of_fermat k42_fermat_uc6

end CFSG.LocalAnalysis.UniquenessCase.UC6
