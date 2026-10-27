module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.Residual
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.NormalComplement
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Suzuki.V.theorem_2_10

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki.External

universe u

/-- Huppert XI.2.5(b), cyclic Sylow-2 branch.  A cyclic Sylow subgroup for
the least prime divisor gives a normal 2-complement, contradicting a top
2-residual. -/
public theorem huppert_XI_2_5_pResidual_ne_top_of_cyclic_sylow_two
    {G : Type u} [Group G] [Finite G]
    (hEven : 2 ∣ Nat.card G) (P : Sylow 2 G) (hP : IsCyclic P) :
    hktPResidual 2 G ≠ (⊤ : Subgroup G) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmin : (Nat.card G).minFac = 2 :=
    (Nat.minFac_eq_two_iff (Nat.card G)).2 hEven
  have hcomp : HasNormalPComplement 2 G :=
    Suzuki.V.suzuki_ch5_theorem_2_10_corollary_1 P hmin hP
  exact hktPResidual_ne_top_of_hasNormalPComplement_of_dvd_card hcomp hEven

/-- Huppert XI.2.5(b), generalized-quaternion Sylow-2 branch.  Under a top
2-residual, IV.5.11 forces the group order to be divisible by three. -/
public theorem huppert_XI_2_5_three_dvd_card_of_quaternion_sylow
    {G : Type u} [Group G] [Finite G]
    (hEven : 2 ∣ Nat.card G)
    (hres : hktPResidual 2 G = (⊤ : Subgroup G))
    (P : Sylow 2 G)
    (hPquaternion :
      ∃ k : ℕ, 2 ≤ k ∧ IsPGroup 2 (QuaternionGroup k) ∧
        Nonempty (P ≃* QuaternionGroup k)) :
    3 ∣ Nat.card G := by
  by_contra hthree
  have hcomp : HasNormalPComplement 2 G :=
    huppert_IV_5_11_hasNormalPComplement_of_quaternion_sylow_two
      P hPquaternion hthree
  exact
    (hktPResidual_ne_top_of_hasNormalPComplement_of_dvd_card hcomp hEven) hres
end CFSG.BenderSuzuki.External
