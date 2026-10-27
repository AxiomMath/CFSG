module

public import CFSG.RankThree.PartTwo.Sec8.Hering88Swap
import CFSG.RankThree.PartTwo.Sec8.Item812Res9ProofRee
import CFSG.RankThree.PartTwo.Sec8.Item812Res11ProofU38
import CFSG.RankThree.PartTwo.Sec11.KS11Lie7ProofConj
public import CFSG.RankThree.PartTwo.Sec8.Item812Res10ProofUnitary
public import CFSG.RankThree.PartTwo.Sec8.Item812Res8ProofG2Two
public import CFSG.RankThree.PartTwo.Sec8.Item812Res9ProofG2Two

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo


theorem kF88SwapCent_of_JCentA (hA : KF89JCentA) : KF88SwapCent := by
  intro G _ _ A c L a b X n h Y hY hIJ x hx hxY
  obtain ⟨Y₀, hY₀, hYeq⟩ := hY
  have hYeq' : Y = Y₀.map (Subgroup.centralizer ({a} : Set G)).subtype := hYeq.symm
  subst hYeq'
  have hYat : Y₀.map (Subgroup.centralizer ({a} : Set G)).subtype ∈ thetaComponentsAt 3 a :=
    ⟨Y₀, hY₀, rfl⟩
  have hAel := h.mem_partTwoF.1
  have haA : a ∈ A := h.a_mem
  have hAc : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hAel.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hθ : inSubgroup (aschbacherSolvableCore 3)
      (Y₀.map (Subgroup.centralizer ({a} : Set G)).subtype) ≤
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G)) := by
    rw [PartOne.theta_eq_inf_of_mem_thetaComponentsAt Nat.prime_three hYat]
    exact inf_le_right
  ext g
  constructor
  · rintro ⟨hgA, hg⟩
    have hgC : g ∈ Subgroup.centralizer ({a} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hAc g hgA a haA)
    refine hA G A c L a b X n h Y₀ hY₀ hIJ ⟨g, hgC⟩ hgA ?_
    intro y hy
    have h1 := hθ (hg (y : G) ⟨y, hy, rfl⟩)
    obtain ⟨z, hz, hzy⟩ := h1
    have : z = (⟨g, hgC⟩ : Subgroup.centralizer ({a} : Set G)) * y *
        (⟨g, hgC⟩ : Subgroup.centralizer ({a} : Set G))⁻¹ * y⁻¹ :=
      Subtype.ext (by simpa using hzy)
    rwa [← this]
  · rintro ⟨k, rfl⟩
    refine ⟨Subgroup.zpow_mem A haA k, fun y hy => ?_⟩
    obtain ⟨y₀, -, rfl⟩ := hy
    have hc : Commute a (y₀ : G) :=
      (Subgroup.mem_centralizer_singleton_iff.mp y₀.2).symm
    have h1 : a ^ k * (y₀ : G) = (y₀ : G) * a ^ k := (hc.zpow_left k).eq
    have : a ^ k * (y₀ : G) * (a ^ k)⁻¹ * (y₀ : G)⁻¹ = 1 := by
      rw [h1, mul_inv_cancel_right, mul_inv_cancel]
    change a ^ k * (y₀ : G) * (a ^ k)⁻¹ * (y₀ : G)⁻¹ ∈ _
    rw [this]
    exact Subgroup.one_mem _

theorem kF89JCentA_holds
    (h45 : Sec4.Item4_5) (h84 : Pair84A) : KF89JCentA :=
  have hG2o : KFG2Ord3Inv :=
    kFG2Ord3Inv_of Sec11.KS11Lie7Proof.g2ThreeConjSL2Minus_holds kFG2Ord3InvTwo_holds
  have hJ2 : KF89JTwoLocal :=
    kF89JTwoLocal_of h84 (kF89G2TwoLocal_of hG2o kF89G2TwoTwoLocal_holds) kF89Sp4TwoLocal_holds
      kF89ReeTwoLocal_holds
  have hBI : KF89BNotCentI :=
    kF89BNotCentI_of h45 (kF89BNotCentIUnitary_of h45 (kF89BNotCentIU38_of h45))
      kF89ReeTwoLocal_holds
  kF89JCentA_of h45 h84 hJ2 hBI

theorem kF88SwapCent_holds
    (h45 : Sec4.Item4_5) (h84 : Pair84A) : KF88SwapCent :=
  kF88SwapCent_of_JCentA (kF89JCentA_holds h45 h84)

end CFSG.RankThree.PartTwo.Sec8
