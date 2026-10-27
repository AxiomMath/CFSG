module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section1
public import Mathlib.GroupTheory.Exponent

namespace CFSG
end CFSG
open CFSG

/-! # Data for the A7 equation-(8) omega argument -/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- The synchronized equation-(6) factors together with the characteristic
omega subgroup used in equation (8). -/
public structure SecondCaseA7OmegaData
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w) where
  K : Subgroup G
  B : Subgroup G
  F : Subgroup G
  s : d.E
  s_involution : IsInvolution (s : G)
  s_mem_H : (s : G) ∈ c.H
  K_inverted : (K : Set G) =
    invertedElements (c.U ⊓ w.M) (s : G)
  B_fixed : B = centralizerIn c.U (s : G)
  U_inter_M_eq : K ⊔ B = c.U ⊓ w.M
  K_card : Nat.card K = 3
  K_le_E : K ≤ d.E
  F_fixed : F = centralizerIn c.FU (s : G)
  FU_inter_M_eq : K ⊔ F = c.FU ⊓ w.M
  FU_inter_M_card : Nat.card ↥(c.FU ⊓ w.M) = 9
  F_normal_M : IsNormalIn F w.M
  F_centralizes_E : F ≤ Subgroup.centralizer (d.E : Set G)
  F_card : Nat.card F = 3
  F_normalizer : Subgroup.normalizer (F : Set G) = w.M
  FU_isPGroup : IsPGroup 3 c.FU
  Q : Subgroup c.FU
  Q_le_upperCentralSeries_two :
    Q ≤ Subgroup.upperCentralSeries c.FU 2
  Q_not_cyclic : ¬ IsCyclic Q
  Q_exponent : Monoid.exponent Q = 3
  Q_characteristic : Q.Characteristic

end CFSG.GorensteinWalter
