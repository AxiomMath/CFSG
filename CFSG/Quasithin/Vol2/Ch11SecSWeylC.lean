module

public import CFSG.Quasithin.Vol2.Ch11SecSWeylA

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.SWeyl

open CFSG.Open CFSG.Blueprint C11P9A CFSG.QuasithinUnique.Setup.X6

variable {Q : Type} [Group Q] [Finite Q]

theorem normalizer_dInf_eq {S : Subgroup Q} {P : Fin 2 → Subgroup Q}
    (hres : ResidualOvergroupsAt Q S P) (hB : ∀ j, dInf (P j) ≠ ⊥)
    (hN : ∀ X : Subgroup Q, X.Normal → ⁅X, X⁆ = X → X ≠ ⊥ → X = ⊤) (j : Fin 2) :
    Subgroup.normalizer (dInf (P j) : Set Q) = P j := by
  have hcov : P j ⋖ ⊤ := (hres.2.2.1 (P j) (hres.2.1 j)).mpr ⟨j, rfl⟩
  have hle : P j ≤ Subgroup.normalizer (dInf (P j) : Set Q) := by
    rw [CFSG.QuasithinUnique.Vol2Native.A312L.dInf_eq_perfectCore]
    exact Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore _)
  rcases hcov.eq_or_eq hle le_top with e | e
  · exact e
  · refine absurd (hN _ (Subgroup.normalizer_eq_top_iff.mp e)
      (Subgroup.isPerfect_iff.mp (dInf_isPerfect (P j))) (hB j)) fun h => hcov.lt.ne ?_
    rw [eq_top_iff, ← h]
    exact dInf_le (P j)

theorem not_dvd_of_borel {S M : Subgroup Q} (hS : IsPGroup 2 ↥S)
    (hMS : M ≤ Subgroup.normalizer (S : Set Q))
    (hcard : Nat.card ↥(Subgroup.normalizer (S : Set Q)) = Nat.card ↥S * 9) :
    ¬ 27 ∣ Nat.card ↥M := by
  intro h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := hS.exists_card_eq
  have h1 : 27 ∣ 2 ^ a * 9 := by
    rw [← ha, ← hcard]
    exact h.trans (Subgroup.card_dvd_of_le hMS)
  have h2 : 3 ∣ 2 ^ a := by
    obtain ⟨c, hc⟩ := h1
    exact ⟨c, by omega⟩
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2
  omega

theorem part2_of_residual {S : Subgroup Q} (hS : QuasithinUnique.IsSylowTwoOf S ⊤)
    {P : Fin 2 → Subgroup Q} (hres : ResidualOvergroupsAt Q S P) (hB : ∀ j, dInf (P j) ≠ ⊥)
    (hN : ∀ X : Subgroup Q, X.Normal → ⁅X, X⁆ = X → X ≠ ⊥ → X = ⊤)
    (htop : ∀ X : Subgroup Q, IsL24Sub S X → X ≠ ⊤ → ¬ IsL24Sub S ⊤)
    (hkey : ∀ j : Fin 2, IsL24Sub S (dInf (P j)) → ∀ E : Subgroup Q, E ≤ P 0 ⊓ P 1 →
      Nat.card ↥E = 9 →
      ∀ E₂ : Subgroup Q, E₂ ≤ E ⊓ sectionCentralizer (dInf (P j)) (pCoreOf 2 (dInf (P j))) →
        E₂ ≠ ⊥ → ¬ Subgroup.normalizer (E₂ : Set Q) ≤ P j)
    {B₁ B₂ : Subgroup Q} (hne : B₁ ≠ B₂) (h₁ : IsL24Sub S B₁) (h₂ : IsL24Sub S B₂)
    {E : Subgroup Q} (hE : Nat.card ↥E = 9) (hE₁ : E ≤ Subgroup.normalizer (B₁ : Set Q))
    (hE₂ : E ≤ Subgroup.normalizer (B₂ : Set Q)) (E₂ : Subgroup Q)
    (hle : E₂ ≤ E ⊓ sectionCentralizer B₂ (pCoreOf 2 B₂)) (hne₂ : E₂ ≠ ⊥) :
    ¬ Subgroup.normalizer (E₂ : Set Q) ≤ Subgroup.normalizer (B₂ : Set Q) := by
  have hpp := parabPair_of_residual_of hS hres hB hN htop
  have hNP := normalizer_dInf_eq hres hB hN
  obtain ⟨k, rfl⟩ := eq_or_eq_of_ne hpp hne h₁ h₂
  obtain ⟨k', rfl⟩ := eq_or_eq_of_ne hpp hne.symm h₂ h₁
  have hkk : k' ≠ k := fun h => hne (by rw [h])
  have hEM : E ≤ P 0 ⊓ P 1 := by
    have h := le_inf hE₁ hE₂
    rw [hNP k', hNP k] at h
    fin_cases k <;> fin_cases k'
    · exact absurd rfl hkk
    · exact h.trans (inf_comm _ _).le
    · exact h
    · exact absurd rfl hkk
  rw [hNP k]
  exact hkey k h₂ E hEM hE E₂ hle hne₂

end CFSG.Quasithin.Vol2.Ch11.SecS.SWeyl
