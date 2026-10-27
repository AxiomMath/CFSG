module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiDefs
public import CFSG.Foundations.QuasisimpleMulEquiv
public import CFSG.Adapters.SpecialLinearPerfect
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_13
public import CFSG.LieType.Steinberg.CentralExt.SUTwo

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item462AltProof.KSLThree

open CFSG CFSG.RankThree.PartTwo.Sec4 CFSG.Assembly.LowTwoRank

theorem isQuasisimple_specialLinear_two {F : Type} [Field F] [Finite F] (h4 : 4 ≤ Nat.card F) :
    CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) F) := by
  have hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card F h4
  have hsimple : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    CFSG.BenderSuzuki.External.huppert_II_6_13 2 le_rfl (Or.inr (by omega)) (Or.inr (by omega))
  refine ⟨hperf, hsimple, ?_⟩
  by_contra hcomm
  simp only [not_exists, not_not] at hcomm
  have : IsMulCommutative (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := ⟨⟨hcomm⟩⟩
  exact Group.IsPerfect.not_isMulCommutative _ this

open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg in
theorem isQuasisimple_statedSU_two {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]
    [CharP K p] (hK : Nat.card K = (p ^ f) ^ 2) (hq : 4 ≤ p ^ f) :
    CFSG.IsQuasisimple (StatedSU 2 (p ^ f) K) := by
  obtain ⟨ζ, hζ0, hζ⟩ := exists_unitaryInvolution_eq_neg hK
  have e : Matrix.SpecialLinearGroup (Fin 2) (fixedSubfield K p f) ≃* StatedSU 2 (p ^ f) K :=
    (hypEquiv hζ0 hζ).trans (equivStatedSU hK 2)
  have h4 : 4 ≤ Nat.card (fixedSubfield K p f) := by
    rw [card_fixedSubfield hK]
    exact hq
  exact CFSG.IsQuasisimple.of_mulEquiv e.symm (isQuasisimple_specialLinear_two h4)

theorem isQuasisimple_slPi_two {π : Bool} {p f : ℕ} {K : Type} [Field K] (hK : PiField π p f K)
    (hq3 : 3 < p ^ f) : IsQuasisimple (slPi π 2 (p ^ f) K) := by
  haveI := hK.finite
  haveI : Fact p.Prime := ⟨hK.prime⟩
  cases π
  · haveI : CharP K p := hK.unitary.charP
    exact isQuasisimple_statedSU_two hK.card (by omega)
  · have h4 : 4 ≤ Nat.card K := by
      rw [hK.card]
      exact hq3
    exact CFSG.IsQuasisimple.of_mulEquiv (specialLinearGroupEquivStatedSL 2 K).symm
      (isQuasisimple_specialLinear_two h4)

end CFSG.RankThree.PartTwo.Sec4.Item462AltProof.KSLThree

end
