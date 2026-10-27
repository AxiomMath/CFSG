module

public import CFSG.RankThree.PartOne.KC.SymplecticNoninnerPlaneDescent
public import CFSG.Assembly.GL83LieDefs
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartOne.S11d.OutAbstract
public import CFSG.RankThree.PartTwo.KFacts.KP14McLaughlin
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.LowTwoRank
open CFSG.RankThree.PartOne.KCSpComm CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)

theorem kJ217OutSp62 {X : Type} [Group X] [Finite X] (h : StatedClassicalModel X .PSp 3 2 1)
    (σ : MulAut X) (hσ : σ ^ 3 = 1) : ∃ k : X, σ = MulAut.conj k := by
  obtain ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩ := h
  have O : SpOuter 2 1 3 K := spOuter Nat.prime_two le_rfl (by norm_num) (by simpa using hK)
  set T := StatedProj (StatedSp 3 K) with hT
  have hσ' : (MulAut.congr e σ) ^ 3 = 1 := by rw [← map_pow, hσ, map_one]
  set σ' : MulAut T := MulAut.congr e σ with hσ'def
  have hodd : Odd (orderOf σ') :=
    Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one hσ')
  have hE : σ' ∈ spSemilinearAutGroup 3 K :=
    mem_of_odd_orderOf_of_index_dvd_two _ O.index_dvd hodd
  have hD : σ' ∈ spLinearAutGroup 3 K := by
    by_contra hnD
    have hne1 : σ' ≠ 1 := by
      rintro h1
      exact hnD (h1 ▸ Subgroup.one_mem _)
    have hord : orderOf σ' = 3 := orderOf_eq_prime hσ' hne1
    obtain ⟨hpf, -⟩ := O.descent 3 Nat.prime_three σ' hE hnD hord
    omega
  have := inner_normal T
  have hin : σ' ∈ inner T :=
    mem_of_pow_eq_one_of_relIndex_dvd_two (O.relIndex_dvd.trans (Nat.gcd_dvd_left 2 _))
      Nat.prime_three (by norm_num) hD hσ'
  obtain ⟨y, hy⟩ := hin
  refine ⟨e.symm y, ?_⟩
  ext x
  apply e.injective
  have h1 : (MulAut.conj y) (e x) = (MulAut.congr e σ) (e x) := by rw [hy]
  have h2 : (MulAut.congr e σ) (e x) = e (σ x) := by simp [MulAut.congr_apply]
  rw [h2, MulAut.conj_apply] at h1
  rw [MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, ← h1]

end CFSG.RankThree.PartTwo.Sec21
