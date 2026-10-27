module

public import CFSG.RankThree.CentralLift.ClassicalCenterTrivial
public import CFSG.RankThree.Classical2.TwoLocalRankCoprimeQuotient
public import CFSG.RankThree.PartTwo.Setup

public section

namespace CFSG.RankThree.Classical

open CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (localRank)

theorem localRank_le_of_le_quotient {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (N : Subgroup X) [N.Normal] (hN : ¬p ∣ Nat.card N) (L : Subgroup (X ⧸ N)) :
    localRank p L ≤ localRank p X :=
  (CFSG.RankThree.PartTwo.localRank_subgroup_le hp L).trans
    (CFSG.RankThree.Classical2.localRank_quotient_le hp hp2 N hN)

theorem orthogonal_defining_prime_actual_component_exclusion {X : Type} [Group X] [Finite X]
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (N : Subgroup X) [N.Normal] (hN : ¬p ∣ Nat.card N)
    (hX : localRank p X ≤ 3) (L : Subgroup (X ⧸ N)) {c : StatedLieTag}
    (hc : c = .POmegaOdd ∨ c = .POmegaPlus ∨ c = .POmegaMinus) (n f : ℕ) :
    ¬StatedClassicalModel (L ⧸ Subgroup.center L) c n p f := by
  intro hmod
  have hL := localRank_le_of_le_quotient hp (by omega) N hN L
  rcases hc with rfl | rfl | rfl
  · obtain ⟨⟨-, hf, hn, -⟩, K, _, _, hK, ⟨e⟩⟩ := hmod
    have := CFSG.RankThree.CentralLift.four_mul_le_localRank_of_omegaOdd hp hp3 hf hK hn e
    omega
  · obtain ⟨⟨-, hf, hn⟩, K, _, _, hK, ⟨e⟩⟩ := hmod
    have := CFSG.RankThree.CentralLift.four_mul_le_localRank_of_omegaPlus hp hp3 hf hK hn e
    omega
  · obtain ⟨⟨-, hf, hn⟩, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := hmod
    have := CFSG.RankThree.CentralLift.four_mul_le_localRank_of_omegaMinus hp hp3 hf hK hn hirr e
    omega

end CFSG.RankThree.Classical
