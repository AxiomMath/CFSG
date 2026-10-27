module

public import CFSG.RankThree.PartTwo.Sec21.Item226Gaps
public import CFSG.RankThree.PartTwo.Census.Classical.EvenWitness
public import CFSG.RankThree.PartTwo.Census.Classical.EvenPrimes
public import CFSG.RankThree.PartTwo.Census.Classical.EvenMain
public import CFSG.RankThree.PartOne.S12.ModelTransport
public import CFSG.Adapters.RankTwoModelTransports

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS21LocalRank

open CFSG CFSG.Assembly.LowTwoRank Matrix
open CFSG.Assembly.RankThreeEven (projImage projSU localRank)
open CFSG.Adapters.RankTwoModelTransports (statedProjEquivMapMk)

noncomputable def statedProjSUEquivProjSU (n p f : ℕ) [Fact p.Prime] :
    StatedProj (StatedSU n (p ^ f) (GaloisField p (2 * f))) ≃* projSU n p f :=
  (statedProjEquivMapMk (StatedSU n (p ^ f) (GaloisField p (2 * f)))).trans
    (MulEquiv.subgroupCongr (CFSG.RankThree.PartOne.projImage_statedSU_eq_projSU n p f))

theorem localRankLowerBound226 : Sec21.LocalRankLowerBound226 := by
  intro X _ _ n hn hodd hn3 he
  obtain ⟨e⟩ := he
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn5 : 4 ≤ n := by
    obtain ⟨k, rfl⟩ := hodd
    omega
  obtain ⟨s, hs, hs7, hsd⟩ := Census.exists_prime_seven_le_dvd_two_pow_add_one hn5
  refine ⟨s, hs, by omega, ?_⟩
  have h := Census.unitaryFieldData_galoisField_two (f := n) (by omega)
  have hw := Census.le_localRank_statedSU_torus (k := 2) (n := 5) h hs hsd (by norm_num)
    (Or.inr fun h5 => by
      have := Nat.le_of_dvd (by norm_num) h5
      omega)
  rw [Census.localRank_eq_of_mulEquiv (e.trans (statedProjSUEquivProjSU 5 2 n).symm) hs]
  exact hw

end CFSG.RankThree.PartTwo.KFacts.KS21LocalRank
