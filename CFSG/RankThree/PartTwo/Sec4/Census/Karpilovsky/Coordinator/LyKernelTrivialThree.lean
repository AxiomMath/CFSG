module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.LyThreeMcLSubgroup
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.McLCoverNoThreeCover
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving.CarrierPerfect
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.KernelTrivialBridge
public import CFSG.Quasithin.Vol2.Ch11SecJ4MultA2

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator

open CFSG.Blueprint CFSG.Quasithin.Vol2.Ch11.SecS.J4Mult CFSG.Sporadic.Recognition

theorem noPerfectCentralCover_three_Ly :
    NoPerfectCentralCover 3 NativeSporadic.Ly := by
  obtain ⟨H, hH, ⟨φ⟩⟩ := exists_subgroup_ly_mclCover
  have : Group.IsPerfect McLMultiplier.MclCover := LyonsSims.isPerfect_mclCover
  have : Finite NativeSporadic.Ly :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Ly.card_Ly']; norm_num)
  refine noPerfectCentralCover_of_subgroup Nat.prime_three noPerfectCentralCover_three_mclCover H
    hH (MonoidHom.ofClass φ) φ.surjective ?_
  have hker : ((MonoidHom.ofClass φ)).ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).2 φ.injective
  rw [hker, Subgroup.card_bot]
  exact Nat.coprime_one_left 3

theorem kernelTrivialAt_three_Ly :
    CFSG.AGLEmbedding.KernelTrivialAt (NativeSporadic.Carrier .Ly) 3 := by
  show CFSG.AGLEmbedding.KernelTrivialAt NativeSporadic.Ly 3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite NativeSporadic.Ly :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Ly.card_Ly']; norm_num)
  have : IsSimpleGroup NativeSporadic.Ly := CFSG.Sporadic.Ly.isSimpleGroup_Ly
  have : Group.IsPerfect NativeSporadic.Ly :=
    Proving.isPerfect_of_simple_not_prime_card NativeSporadic.Ly (by
      rw [CFSG.Sporadic.Ly.card_Ly']
      intro hp
      have := hp.eq_one_or_self_of_dvd 2 (by norm_num)
      omega)
  exact UniversalCoverMonster.kernelTrivialAt_of_not_dvd_card_hopfMultiplier
    (not_dvd_card_hopfMultiplier noPerfectCentralCover_three_Ly)

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
