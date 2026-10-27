module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinJ3A0Impossible
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinJ3FixedSubgroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinB3Subgroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinCosetInvolution
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-! The `J₃` fibre is empty in the Klein-four first case. -/
public theorem firstCase_klein_b3_zero
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat)) :
    cosetInvolution_b c.Hhat 3 = 0 := by
  classical
  by_contra hb3
  have hJ3pos : 0 < Nat.card {x : G // x ∈ firstCaseJ c 3} := by
    rw [firstCase_J_n_card c 3]
    omega
  obtain ⟨y, hyJ⟩ := (Nat.card_pos_iff.mp hJ3pos).1
  obtain ⟨X, hXne, hXle, hXcard, hXinv, hXinf, _hXnotcent⟩ :=
    firstCase_klein_J3_inverted_subgroup hmin c hfirst hklein hyJ
  have hA0ne : Subgroup.centralizer (X : Set G) ⊓
      Subgroup.centralizer ({y} : Set G) ≠ ⊥ :=
    firstCase_klein_J3_centralizer_fixed_nontrivial
      hmin c hfirst hklein hyJ hXne hXle hXcard hXinv hXinf
  exact firstCase_klein_J3_A0_impossible hmin c hfirst hklein hyJ
    hXne hXle hXcard hXinv hXinf hA0ne

end CFSG.GorensteinWalter
