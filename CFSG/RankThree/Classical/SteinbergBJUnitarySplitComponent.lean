module

public import CFSG.RankThree.Classical.SteinbergBJOrthogonalDefiningComponent

public section

namespace CFSG.RankThree.Classical

open CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.Assembly.RankThreeEven (localRank)

theorem unitary_split_prime_actual_component_parameter_restriction {X : Type} [Group X]
    [Finite X] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (N : Subgroup X) [N.Normal]
    (hN : ¬p ∣ Nat.card N) (hX : localRank p X ≤ 3) (L : Subgroup (X ⧸ N)) {ℓ n f : ℕ}
    (hmod : StatedClassicalModel (L ⧸ Subgroup.center L) .PSU n ℓ f) (hpq : p ∣ ℓ ^ f + 1) :
    (ℓ = 2 → n ≤ 5) ∧ (ℓ ≠ 2 → n ≤ 4 ∨ (n = 5 ∧ p = 5)) ∧ (p ≤ n → n = 5 ∧ p = 5) := by
  have hL := localRank_le_of_le_quotient hp (by omega) N hN L
  obtain ⟨⟨hℓ, hf, hn, -⟩, K, _, _, hK, ⟨e⟩⟩ := hmod
  have h : UnitaryFieldData ℓ f K := ⟨hℓ, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨φ, hφ, hker⟩ :=
    CFSG.RankThree.CentralLift.exists_top_cover (e.trans (unitaryPSUEquiv h (by omega)).symm)
  obtain ⟨u, -, hu, V, hV, hVab, hVcard⟩ :=
    CFSG.RankThree.Classical2.unitary_split_prime_central_cover_two_local_rank ⊤ h hp hp3 hpq hn
      φ hφ hker
  have hr := CFSG.RankThree.Classical2.le_localRank_of_involution_elemAbelian hp hu
    (le_inf_iff.mp hV).2 hVab hVcard
  have h6 : ¬p ∣ 6 := fun h6 => by
    rcases (Nat.Prime.dvd_mul hp).mp (show p ∣ 2 * 3 from h6) with h2 | h3
    · exact absurd (Nat.le_of_dvd (by norm_num) h2) (by omega)
    · exact absurd (Nat.le_of_dvd (by norm_num) h3) (by omega)
  have h5 : p ∣ 5 → p = 5 := fun h5 => (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h5
  have hodd : ℓ ≠ 2 → n ≤ 4 ∨ (n = 5 ∧ p = 5) := by
    intro hℓ2
    by_cases hpn : p ∣ n
    · simp only [hℓ2, hpn, ↓reduceIte] at hr
      rcases (show n ≤ 4 ∨ n = 5 by omega) with h4 | rfl
      · exact Or.inl h4
      · exact Or.inr ⟨rfl, h5 hpn⟩
    · simp only [hℓ2, hpn, ↓reduceIte] at hr
      exact Or.inl (by omega)
  have hle5 : n ≤ 5 := by
    by_cases hℓ2 : ℓ = 2
    · by_cases hpn : p ∣ n
      · simp only [hℓ2, hpn, ↓reduceIte] at hr
        rcases (show n ≤ 5 ∨ n = 6 by omega) with h5' | rfl
        · exact h5'
        · exact absurd hpn h6
      · simp only [hℓ2, hpn, ↓reduceIte] at hr
        omega
    · rcases hodd hℓ2 with h4 | ⟨rfl, -⟩
      · omega
      · exact le_rfl
  have hp5 : 5 ≤ p := by
    rcases (show p = 4 ∨ 5 ≤ p by omega) with rfl | h
    · exact absurd hp (by norm_num)
    · exact h
  exact ⟨fun _ => hle5, hodd, fun hpn => ⟨by omega, by omega⟩⟩

end CFSG.RankThree.Classical
