module

public import CFSG.RankThree.PartOne.N143.CaseB2
public import CFSG.RankThree.PartOne.N143.CaseSup
public import CFSG.RankThree.PartOne.S12.Sec141Struct

public section

namespace CFSG.RankThree.PartOne.N143

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem two_pow_mod_three (f : ℕ) : 2 ^ f % 3 = 1 ∨ 2 ^ f % 3 = 2 := by
  have h3 : ¬ 3 ∣ 2 ^ f := fun h =>
    absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h) (by norm_num)
  omega

theorem node143Comm_of_jfacts {Q : (X : Type) → [Group X] → Prop} (hSchreier : SchreierFor InCatalog)
    (hRow1 : KF123Row 1) (h107 : InSec10Seven) (h109 : InSec10Nine) (h122 : Node122)
    (hpair : KF134Pair) (hJ : JFacts) (hB2 : Node143CommB2Sup) (h64W : KF64WWith Q)
    (h613 : Item613With Q) : Node143Comm := by
  intro G _ _ p A c L E hyp h12 h13 hnotFive hEA hallL3 hthree
  subst hEA
  by_contra hno
  push Not at hno
  have hess : HessianCase p E := fun s hs t ht hst => hno s hs t ht hst
  have hctx : HessCtx p E c L := ⟨hyp, h12, h13, hnotFive, hallL3, hthree, hess⟩
  have hgood : ∀ J ∈ thetaCompZeroStarE p E, ∃ c' : G, JGood p E c' J := fun J hJm =>
    jGood_of_mem hRow1 h107 h109 h122 hctx hJm
  have hp : p.Prime := hyp.prime
  have : Fact p.Prime := ⟨hp⟩
  have : IsElementaryAbelian p E := hyp.E_elem
  obtain ⟨cL, hLg⟩ := hgood L h13.inZeroStar
  obtain ⟨s, hs, -⟩ := hLg.exists_reflection
  obtain ⟨hcard, P, z, hspec⟩ := hessianGeometry hyp.A_card (Sec12Three.five_le hyp) hthree
    h13.irreducible ⟨s, hs⟩ hess
  obtain ⟨f, -, hf, hm⟩ := hLg.model
  rcases two_pow_mod_three f with h1 | h2
  · exact caseA_contra hJ hpair hctx hgood hspec hcard hf hm h1
  · by_cases h3C : 3 ∣ Nat.card (Subgroup.centralizer (E : Set G))
    · exact caseB1_false hSchreier h613 h64W hJ hpair hctx hgood hspec hcard hf hm h2 h3C
    · exact caseB2_false hJ (node143CommB2_of_sup hSchreier hRow1 h107 h109 h122 hpair hJ h613 h64W hB2)
        hctx hgood hspec hcard hf hm h2 h3C

end CFSG.RankThree.PartOne.N143
