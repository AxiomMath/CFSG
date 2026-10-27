module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114E3Defs
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R3URank
public import CFSG.LocalAnalysis.UniquenessCase.UC22S218X

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]


theorem s21_8X_of_s21_8XT (hGA : GriessAllModelsStatement) {D : Data G} {Ch : Choice2011 G}
    (hM3 : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q D.M ≤ 3) (h8XT : S21_8XT D Ch) :
    S21_8X D Ch := by
  intro hH c L hL n hX hn
  rcases hX with hX | hX | hX | hX | hX | hX
  · exact h8XT hH c L hL n (Or.inl hX) hn
  · exact h8XT hH c L hL n (Or.inr (Or.inl hX)) hn
  · exact h8XT hH c L hL n (Or.inr (Or.inr (Or.inl hX))) hn
  · exact h8XT hH c L hL n (Or.inr (Or.inr (Or.inr (Or.inl hX)))) hn
  · exact h8XT hH c L hL n (Or.inr (Or.inr (Or.inr (Or.inr hX)))) hn
  have hX' : LieModel (BarInf L) .PSU 5 2 n := hX
  have hn1 := (LieModel.admissible hX').2.1
  have hn1' : n ≠ 1 := fun h => hn ⟨0, h⟩
  have hn2 : n ≠ 2 := fun h => hn ⟨1, h⟩
  obtain ⟨p, hp, hpn, hp5⟩ : ∃ p : ℕ, p.Prime ∧ p ∣ 2 ^ n + 1 ∧ p ≠ 5 := by
    obtain rfl | h4 : n = 3 ∨ 4 ≤ n := by omega
    · exact ⟨3, Nat.prime_three, by norm_num, by norm_num⟩
    · obtain ⟨p, hp, hpn, -, hp5⟩ := uc22p20o_prime_add_one_ne_three_five h4
      exact ⟨p, hp, hpn, hp5⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    have : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
    omega
  have h4 := uc22s2114r3u_four_le_pRank hGA hL le_rfl hX' hp hp2 (fun _ => hp5) hpn
  have hLM := CFSG.SectionRank.pRank_mono hp.one_lt hL.1.le
  have := hM3 p hp hp2
  omega

end CFSG.LocalAnalysis.UniquenessCase.UC22
