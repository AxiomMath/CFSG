module

public import CFSG.RankThree.PartTwo.Sec15.Gagen1515FpfCtx
public import CFSG.RankThree.PartTwo.Sec14.Item148Steps
import CFSG.RankThree.PartTwo.Sec14.Concl142HJPoint
import CFSG.RankThree.PartTwo.Sec15.Wales154Stage
import CFSG.RankThree.PartTwo.Sec17.PropULemmaThree
import CFSG.RankThree.PartTwo.Sec15.Gagen1515FpfOmega
public import CFSG.RankThree.PartTwo.Sec14.Concl142HJ

public section

namespace CFSG.RankThree.PartTwo.Sec15.Gagen1515Fpf

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {A L : Subgroup G} {c d : G}

theorem not_case467
    (h134 : Item134) (h48 : Sec4.Item4_8) (h : Ctx A c L d)
    {Y : Subgroup G} (hY : Y ∈ scriptY A) :
    letI := ker148_normal hY.2
    ¬ Case148Four A (lB A) Y ∧ ¬ Case148Six A (lB A) Y ∧ ¬ Case148Seven A (lB A) Y := by
  have hHJ : AllPointsHJ A :=
    allPointsHJ_of_j2 h134 h48 h.conf.sec15R.toSec14Std h.conf.j2
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨-, ⟨c', L', hc', hL', ⟨φ7⟩⟩, -⟩
    obtain ⟨φJ⟩ := Wales154.quot_j2_of_allPointsHJ h.conf.sec15R.toSec14Std hHJ hc' hL'
    exact (Sec17.PropU.isEmpty_equiv_small_of_equiv_J2 ⟨φJ⟩).1.false φ7
  · rintro ⟨-, -, h6⟩
    have h3 : (omegaA A).ncard = 3 := (omega_case2 h134 h48 h).2.1
    omega
  · rintro ⟨a₁, a₂, L₁, L₂, J₁, J₂, p₁, f₁, e₁, p₂, f₂, e₂, hp₁, hp₂,
      ha₁Ω, ha₂Ω, hL₁, hL₂, -, -, -, -, -, -, -, -, -, -, -, hIso₁, hIso₂⟩
    haveI : Fact p₁.Prime := hp₁
    obtain ⟨φJ⟩ := Wales154.quot_j2_of_allPointsHJ h.conf.sec15R.toSec14Std hHJ ha₁Ω hL₁
    exact Sec17.PropU.not_isoLThreePi_of_equiv_J2 ⟨φJ⟩ p₁ (f₁ * e₁) hIso₁

section Cert148


theorem not_case5
    (h134 : Item134)
    (h48 : Sec4.Item4_8) (h : Ctx A c L d) {Y : Subgroup G} (hY : Y ∈ scriptY A) :
    letI := ker148_normal hY.2
    ¬ Case148Five A (lB A) Y := by
  have hHJ : AllPointsHJ A :=
    allPointsHJ_of_j2 h134 h48 h.conf.sec15R.toSec14Std h.conf.j2
  rintro ⟨c', hc'A, L', n, m, hc', hL', -, -, -, -, -, -, hε, -, -⟩
  obtain ⟨φJ⟩ := Wales154.quot_j2_of_allPointsHJ h.conf.sec15R.toSec14Std hHJ hc' hL'
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact Sec17.PropU.not_isLThreeEpsAt_of_equiv_J2 ⟨φJ⟩ 2 (n * m) hε

end Cert148

end Ctx

end CFSG.RankThree.PartTwo.Sec15.Gagen1515Fpf
