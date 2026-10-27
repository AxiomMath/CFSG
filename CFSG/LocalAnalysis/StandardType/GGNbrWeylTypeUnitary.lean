module

public import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitFamilies
import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeUnitaryAux

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

private theorem ggWTU1_nbrC_not_dvd_four {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ∣ 4 := by
  intro h
  have h2 : p ∣ 2 ^ 2 := by simpa using h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2))

theorem ggNbrTableBWeylTypeNonSplitOn_unitary :
    GGNbrTableBWeylTypeNonSplitOn GGNbrNonSplitUnitaryLabel := by
  rintro p hp hp2 ⟨tag, rank, n⟩ hlab ⟨hcase, hpq⟩ - Q hQ
  have hn : 1 ≤ n := hlab.1
  simp only at hcase hpq
  rcases hcase with ⟨ht, hr, h53⟩ | ⟨ht, hr⟩
  · subst ht
    have hr' : 3 ≤ rank := hr
    by_cases hpd : p ∣ rank + 1
    · have h4 : rank + 1 ≠ 4 := fun h => ggWTU1_nbrC_not_dvd_four hp hp2 (h ▸ hpd)
      have hnd : ¬ (rank + 1 = 6 ∧ p = 3) := fun ⟨h6, h3⟩ => h53 ⟨by omega, h3⟩
      obtain ⟨K, _, _, hK, hQ', hl, hw⟩ :=
        ggWTU1_recipeUnitary_dvd_weylTypeW hp hpq hn (by omega) hpd hnd hQ
      exact ⟨K, inferInstance, inferInstance, hK, hQ', fun _ _ => ⟨_, hl, hw⟩⟩
    · have hdq : (rank + 1, 2 ^ n) ≠ (3, 2) := fun h => by
        have := congrArg Prod.fst h
        simp only at this
        omega
      obtain ⟨K, _, _, hK, hQ', hP⟩ :=
        ggWTU1_recipeUnitary_weylTypeW hp hpq hn (by omega) hdq hpd hQ
      exact ⟨K, inferInstance, inferInstance, hK, hQ', fun _ _ => hP⟩
  · subst ht
    have hr' : rank = 3 := hr
    subst hr'
    have hdq : ((4 : ℕ), 2 ^ n) ≠ (3, 2) := fun h => by
      have := congrArg Prod.fst h
      simp only at this
      omega
    obtain ⟨K, _, _, hK, hQ', hP⟩ :=
      ggWTU1_recipeUnitary_weylTypeW (d := 4) hp hpq hn (by omega) hdq
        (ggWTU1_nbrC_not_dvd_four hp hp2) hQ
    exact ⟨K, inferInstance, inferInstance, hK, hQ', fun _ _ => hP⟩

end CFSG.StandardType

end
