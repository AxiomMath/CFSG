module

public import CFSG.RankThree.CentralCover.SteinbergBNLinearSplitPrime
public import CFSG.RankThree.Classical2.TwoLocalRankCoprimeQuotient

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBY

open CFSG CFSG.Assembly.RankThreeEven CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

theorem linear_split_prime_actual_component_parameter_restriction {X : Type} [Group X]
    [Finite X] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (N : Subgroup X) [N.Normal]
    (hN : ¬ p ∣ Nat.card N) (hX : localRank p X ≤ 3) {L : Subgroup (X ⧸ N)}
    (_hL : IsComponent L) {ℓ n f : ℕ} (hℓ : ℓ.Prime)
    (hT : StatedClassicalModel (L ⧸ Subgroup.center L) .PSL n ℓ f) (hpq : p ∣ ℓ ^ f - 1) :
    (ℓ = 2 → n ≤ 5) ∧ (ℓ ≠ 2 → n ≤ 4 ∨ (n = 5 ∧ p = 5)) := by
  classical
  have hp2 : p ≠ 2 := by omega
  have hQ : localRank p (X ⧸ N) ≤ 3 :=
    (RankThree.Classical2.localRank_quotient_le hp hp2 N hN).trans hX
  obtain ⟨⟨-, -, hn2, -⟩, K, _, _, hK, ⟨e⟩⟩ := hT
  have := Fintype.ofFinite K
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ := charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hK])
  have hpK : p ∣ Fintype.card K - 1 := by rwa [← Nat.card_eq_fintype_card, hK]
  set φ : L →* Matrix.ProjectiveSpecialLinearGroup (Fin n) K :=
    ((e.trans (projectiveSpecialLinearGroupEquivStatedProj n K).symm).toMonoidHom).comp
      (QuotientGroup.mk' (Subgroup.center L)) with hφ
  have hφs : Function.Surjective φ :=
    (e.trans (projectiveSpecialLinearGroupEquivStatedProj n K).symm).surjective.comp
      (QuotientGroup.mk'_surjective _)
  have hφk : φ.ker ≤ Subgroup.center L := by
    intro x hx
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
    exact hx
  have hrank : 3 ≤ n → (if ℓ = 2 then n - 2 - (if p ∣ n then 1 else 0) else
      n - 1 - (if p ∣ n then 1 else 0)) ≤ 3 := fun hn3 => by
    obtain ⟨-, -, -, -, -, -, -, hle⟩ :=
      RankThree.CentralCover.linear_split_prime_central_cover_two_local_rank L hℓ hp hp3 hpK hn3
        φ hφs hφk
    exact hle.trans hQ
  have hp6 : ¬ p ∣ 6 := by
    intro h
    have h6 : p ∣ 2 * 3 := by simpa using h
    rcases (Nat.Prime.dvd_mul hp).mp h6 with h | h
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h
      omega
  refine ⟨fun hℓ2 => ?_, fun hℓ2 => ?_⟩
  · by_contra hn
    push Not at hn
    have h := hrank (by omega)
    simp only [hℓ2, ↓reduceIte] at h
    by_cases hpn : p ∣ n
    · simp only [hpn, ↓reduceIte] at h
      have hn7 : 7 ≤ n := by
        by_contra h7
        have : n = 6 := by omega
        exact hp6 (this ▸ hpn)
      omega
    · simp only [hpn, ↓reduceIte] at h
      omega
  · by_cases hn3 : 3 ≤ n
    · have h := hrank hn3
      simp only [hℓ2, ↓reduceIte] at h
      by_cases hpn : p ∣ n
      · simp only [hpn, ↓reduceIte] at h
        by_cases hn5 : n = 5
        · subst hn5
          exact Or.inr ⟨rfl, (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp hpn⟩
        · left
          omega
      · simp only [hpn, ↓reduceIte] at h
        left
        omega
    · left
      omega

end CFSG.RankThree.GroupTheory.SteinbergBY
