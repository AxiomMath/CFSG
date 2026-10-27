module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieG2Trans
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieG2Borel
public import CFSG.Quasithin.Vol2.F134LieG2Power
import CFSG.RankThree.Chevalley.EvenRealThreeCentralizingInvolution

set_option linter.unusedSectionVars false

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.F134.LieG2
open CFSG.Quasithin.H13.NQCore

namespace CFSG.Quasithin.H13.NQCore

theorem g2Even_simple :
    ∀ n : ℕ, NoOddCfg fun (X : Type) [Group X] => ChevalleyExceptionalModel X .G2 2 n := by
  intro n A _ _ p _ L P T hp5 hL hcfg
  obtain ⟨⟨-, hn1, -, hq3⟩, hmod⟩ := hL
  have hn : 2 ≤ n := by
    by_contra hlt
    obtain rfl : n = 1 := by omega
    norm_num at hq3
  obtain ⟨K, _, _, hK, ⟨e₀⟩⟩ :=
    CFSG.RankThree.Chevalley.exists_mulEquiv_adjointGroup_of_untwisted hmod
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hK
  have : Finite (ModGL .G2 K) := finite_modGL
  have hBC : borelGroup .G2 K ≤ adjointGroup .G2 K :=
    ((triangular_borel_structure.{0, 0} .G2 K).2.2.2.2.2.2.2.2.2.2.2 K).1
  have hUC : posUnipotent .G2 K ≤ adjointGroup .G2 K := le_sup_right.trans hBC
  obtain ⟨hUp, hUi⟩ := isPGroup_and_not_dvd_index 2 hUC card_posUnipotent
  refine G2.false_of_borel_data hp5 hcfg e₀
    (B := (borelGroup .G2 K).subgroupOf (adjointGroup .G2 K)) hUp hUi ?_ ?_ ?_
  · intro a H ha hUH hH
    exact G2.le_borelGroup_of_card_eq_prime hK hn (Fact.out : p.Prime) hp5 ha hUH hH
  · intro x hx y hy
    exact commutator_mem_posUnipotent hx hy
  · intro α hα
    exact exists_pow_of_map_posUnipotent hK hn α hα

end CFSG.Quasithin.H13.NQCore
