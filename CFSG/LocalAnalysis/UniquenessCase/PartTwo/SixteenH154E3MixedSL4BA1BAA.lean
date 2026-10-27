module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Background.HSL
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Open Subgroup

theorem s16h_sl4_natNorm_involution {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4)
    {s : MulAut (StdMod (Fin 2) K)}
    (hsN : s ∈ natNorm (CFSG.Assembly.LowTwoRank.StatedSL 2 K))
    (hs2 : s ^ 2 = 1) (hs1 : s ≠ 1) :
    2 ≤ rkIdx (fixV (Subgroup.zpowers s)) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hK2 : Nat.card K = 2 ^ 2 := by rw [hK]; norm_num
  have hΓ : HasScalarCommutant (CFSG.Assembly.LowTwoRank.StatedSL 2 K) :=
    hasScalarCommutant_statedSL (K := K) (by norm_num)
  let g : ↥(natNorm (CFSG.Assembly.LowTwoRank.StatedSL 2 K)) := ⟨s, hsN⟩
  by_cases hσ : fieldHom hΓ g = 1
  · have hlin : (g : MulAut (StdMod (Fin 2) K)) ∈ linSub :=
      (fieldHom_eq_one_iff hΓ g).mp hσ
    have hglin : IsSemilinear s (RingEquiv.refl K) := mem_linSub.mp hlin
    exact le_rkIdx_fixV_of_linear (ι := Fin 2) (K := K) (n := 2) hK2 hglin hs1
  · have hsemi : IsSemilinear s (fieldAut hΓ g) := isSemilinear_fieldAut hΓ g
    have hσne : fieldAut hΓ g ≠ RingEquiv.refl K := hσ
    obtain ⟨-, heq⟩ :=
      rkIdx_fixV_of_semilinear_two (ι := Fin 2) (n := 2) (K := K) (by norm_num) hK2 hsemi hσne hs2
    have hcard : Fintype.card (Fin 2) = 2 := by simp
    rw [hcard] at heq
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
