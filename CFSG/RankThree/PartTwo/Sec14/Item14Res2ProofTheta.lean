module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec14.Item148ResProofTheta
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

namespace Res2

variable {G : Type} [Group G]

theorem theta_le_center_img148 {A Y K : Subgroup G} [(ker148 A Y).Normal] (hKM : K ≤ Y ⊔ A)
    (ψ : ↥K →* ↥(img148 A Y K)) (hψs : Function.Surjective ψ)
    (hψker : ψ.ker = (Main148.phi148 (A := A) (Y := Y) hKM).ker)
    (hθeq : aschbacherSolvableCore 3 ↥(img148 A Y K) = (aschbacherSolvableCore 3 ↥K).map ψ)
    (hcomm : ⁅inSubgroup (aschbacherSolvableCore 3) K, K⁆ ≤ pPrimeCoreOf 3 Y) :
    aschbacherSolvableCore 3 ↥(img148 A Y K) ≤ Subgroup.center ↥(img148 A Y K) := by
  rw [hθeq]
  rintro _ ⟨t, ht, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro w
  obtain ⟨k, rfl⟩ := hψs w
  have hmem : ((t * k * t⁻¹ * k⁻¹ : ↥K) : G) ∈ pPrimeCoreOf 3 Y := by
    have htK : (t : G) ∈ inSubgroup (aschbacherSolvableCore 3) K := ⟨t, ht, rfl⟩
    have h1 := Subgroup.commutator_mem_commutator htK k.2
    simpa [commutatorElement_def] using hcomm h1
  have h2 : t * k * t⁻¹ * k⁻¹ ∈ ψ.ker := by
    rw [hψker, MonoidHom.mem_ker]
    exact (Main148.phi148_eq_one_iff hKM _).mpr hmem
  rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one,
    mul_inv_eq_iff_eq_mul] at h2
  exact h2.symm

end Res2

open Res148 Main148 Res2

end CFSG.RankThree.PartTwo.Sec14
