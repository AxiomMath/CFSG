module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRanksTwF4
public import CFSG.RankThree.PartTwo.Sec4.Item413Eigen
public import CFSG.RankThree.PartTwo.Sec21.ReeF4Cent2ProofFix
public import CFSG.RankThree.PartOne.SEITZQ1.Plane
public import CFSG.LieType.Steinberg.CentralExt.SUThreeOrder
public import CFSG.LieType.Universal.Unitary.Comparison
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.RankThree.PartOne.KE.A1SL2
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KLR.CoreGroup
public import CFSG.RankThree.PartOne.KLR.FrobTrick
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec4.Item413AutGen
public import CFSG.RankThree.PartTwo.Sec4.Item47
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import CFSG.StronglyEmbedded.ParityCriterion

public section

namespace CFSG.StandardType

namespace TwF4SUThree

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

section Embed

theorem exists_injective_unitarySU_hom (a : ℕ) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∃ Ψ : unitarySU 2 (2 * a + 1) (GaloisField 2 (2 * (2 * a + 1))) 3 →*
      ReeTag.F4.reeGamma K a, Function.Injective Ψ := by
  classical
  let L := AlgebraicClosure K
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  obtain ⟨D⟩ := CFSG.RankThree.PartOne.KLR.reeFrameData_nonempty (K := K) (L := L) hK
  let K' := GaloisField 2 (2 * (2 * a + 1))
  have hK' : Nat.card K' = 2 ^ (2 * (2 * a + 1)) := GaloisField.card 2 _ (by omega)
  have h : UnitaryFieldData 2 (2 * a + 1) K' := ⟨Nat.prime_two, by omega, hK'⟩
  let _ : Algebra (ZMod 2) L := ZMod.algebra L 2
  have : Algebra.IsAlgebraic (ZMod 2) K' := Algebra.IsAlgebraic.of_finite (ZMod 2) K'
  let ι : K' →+* L := (IsAlgClosed.lift (R := ZMod 2) (S := K') (M := L)).toRingHom
  obtain ⟨ω', hω', -⟩ := CFSG.RankThree.PartOne.SEITZQ1.q1_exists_omega h (odd_two_mul_add_one a)
  have hω : ι ω' ^ 2 + ι ω' + 1 = 0 := by
    rw [← map_pow, ← map_add, ← map_one ι, ← map_add, hω', map_zero]
  have hFr : ∀ c, D.Frq (ι c) = ι (h.bar c) := fun c => by
    rw [CFSG.RankThree.PartOne.SEITZQ1.frq_eq_pow D hK, UnitaryFieldData.bar_apply, map_pow]
  obtain ⟨Ψ, hΨ⟩ := CFSG.RankThree.PartOne.SEITZQ1.q1_exists_hom D hK hω
    (CFSG.RankThree.PartOne.SEITZQ1.q1SUToSL h ι)
    (CFSG.RankThree.PartOne.SEITZQ1.q1SUToSL_fixed h ι D.Frq hFr)
  have hj : Function.Injective (CFSG.RankThree.PartOne.SEITZQ1.q1SUToSL h ι) := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have hm : ((u : GL (Fin 3) K') : Matrix (Fin 3) (Fin 3) K').map ι = 1 := by
      rw [← CFSG.RankThree.PartOne.SEITZQ1.coe_q1SUToSL h ι, hu]
      rfl
    have hm' : ((u : GL (Fin 3) K') : Matrix (Fin 3) (Fin 3) K') = 1 :=
      Matrix.map_injective ι.injective (hm.trans (Matrix.map_one ι ι.map_zero ι.map_one).symm)
    exact Subtype.ext (Units.ext hm')
  refine ⟨Ψ, ?_⟩
  rw [injective_iff_map_eq_one]
  intro u hu
  have h1 := (hΨ u).symm
  rw [hu, map_one, mul_inv_eq_one, mul_eq_left] at h1
  have h2 : CFSG.RankThree.PartOne.SEITZQ1.q1SUToSL h ι u = 1 :=
    CFSG.RankThree.PartTwo.Sec8.ReeF4Cent2Proof.q1Psi0_injective D.isFrob (by rw [h1, map_one])
  exact hj (by rw [h2, map_one])

end Embed

end TwF4SUThree

end CFSG.StandardType
