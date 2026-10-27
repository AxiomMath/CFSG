module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114Defs
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R3URank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]


theorem s21_14R3U_of_pRank_le_three (hGA : GriessAllModelsStatement) {D : Data G}
    {Ch : Choice2011 G} (hM3 : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q D.M ≤ 3) :
    S21_14R3U D Ch := by
  rintro - - L hL - - ⟨f, hX⟩
  exfalso
  obtain ⟨m, hm, hm5, hX⟩ : ∃ m : ℕ, 5 ≤ m ∧ m ≠ 5 ∧ LieModel (BarInf L) .PSU m 2 f := by
    rcases hX with hX | hX
    · exact ⟨6, by norm_num, by norm_num, hX⟩
    · exact ⟨7, by norm_num, by norm_num, hX⟩
  have hf := (LieModel.admissible hX).2.1
  have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  obtain ⟨p, hp, hpf⟩ := Nat.exists_prime_and_dvd (n := 2 ^ f + 1) (by omega)
  have hp2 : p ≠ 2 := by
    rintro rfl
    have : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
    omega
  have h4 := uc22s2114r3u_four_le_pRank hGA hL hm hX hp hp2 (fun h => absurd h hm5) hpf
  have hLM := CFSG.SectionRank.pRank_mono hp.one_lt hL.1.le
  have := hM3 p hp hp2
  omega

end CFSG.LocalAnalysis.UniquenessCase.UC22
