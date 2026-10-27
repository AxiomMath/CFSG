module

public import CFSG.LocalAnalysis.UniquenessCase.FundamentalLieFunLowerBound
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenSix.FunGeneral
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGroupProofsA
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieCover

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup CFSG.Blueprint
open CFSG.ClassicalInvolution.Generic
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
open CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped MatrixGroups


theorem exists_noncommuting_of_isFundamentalOver
    {X : Type} [Group X] {q : ℕ} {K : Subgroup X} (hK : IsFundamentalOver q K) :
    ∃ a b : X, a * b ≠ b * a := by
  obtain ⟨t, n, p, e, hp, hp2, _, hfund, hadm, ψ, _, hker, R, hR, _⟩ := hK
  let : Fact p.Prime := ⟨hp⟩
  rcases CFSG.ClassicalInvolution.ModelFacts.nonempty_equiv_sl2_galoisField_of_mem_fundamentalSubgroups
      hp2 hfund hadm hR with ⟨⟨eR⟩⟩ | ⟨_, ⟨eR⟩⟩
  · obtain ⟨a, _, b, _, hab⟩ := F14.exists_noncommuting_map_of_equiv_sl2 ψ hker eR
    exact ⟨ψ a, ψ b, hab⟩
  · obtain ⟨a, _, b, _, hab⟩ := F14.exists_noncommuting_map_of_equiv_sl2 ψ hker eR
    exact ⟨ψ a, ψ b, hab⟩

theorem fundamental_ambient_of_lieModel
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {t : StatedLieTag} {n p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible t n p e) (hX : LieModel X t n p e)
    (hA1 : ¬ (t = .PSL ∧ n = 2))
    {K : Subgroup X} (hK : IsFundamentalOver (p ^ e) K) :
    center X = ⊥ ∧ CFSG.Open.IsQuasisimple X ∧
      (¬ IsL2Over17 (X ⧸ center X) (p ^ e)) ∧
      HypOmegaGen {J : Subgroup X | IsFundamentalOver (p ^ e) J} := by
  have hnc := exists_noncommuting_of_isFundamentalOver hK
  have hZ : center X = ⊥ := CFSG.ComponentClassification.RankTwoOddLie.center_eq_bot_of_simple hnc
  have hperfect : Group.IsPerfect X :=
    TauCeti.IsSimpleGroup.isPerfect_of_not_isMulCommutative (by
      intro h
      obtain ⟨a, b, hab⟩ := hnc
      exact hab (h.is_comm.comm a b))
  have hqs : CFSG.Open.IsQuasisimple X := ⟨hperfect.commutator_eq_top,
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).isSimpleGroup⟩
  have hXq := hX.quotient_center hZ
  have hL2 : ¬ IsL2Over17 (X ⧸ center X) (p ^ e) := by
    intro h2
    exact k_LieModelNotL2_holds (X ⧸ center X) t n p e (p ^ e) hp2
      (by
        by_cases ht : t = .PSL
        · exact Or.inr (fun hn => hA1 ⟨ht, hn⟩)
        · exact Or.inl ht) hadm hXq h2
  exact ⟨hZ, hqs, hL2,
    hypOmegaGen_fundamental_of_lieModel hp hp2 ⟨t, n, e, hadm, rfl, hXq⟩ hL2⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
