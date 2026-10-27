module

public import CFSG.RankThree.PartOne.TAIL.KSideLin
public import CFSG.RankThree.PartOne.TAIL.KSideOutTwo

public section

namespace CFSG.RankThree.PartOne.TAIL

open Subgroup CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory

theorem kData_of_model_two {G : Type} [Group G] [Finite G] {K : Subgroup G} {c : G}
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ 21)
    (e : ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F) (hc7 : c ^ 7 = 1)
    (hc : InducesFieldAut 7 c K) : KData G K c := by
  have hg : Nat.gcd 2 (Nat.card F - 1) = 1 := by
    rw [hF]
    norm_num
  have hZ : K ⊓ Subgroup.centralizer (K : Set G) = ⊥ :=
    inf_centralizer_eq_bot_of_mulEquiv e (center_sl_eq_bot (by norm_num) hg)
  have hS : ∀ R : Subgroup G, R ≤ K → IsPGroup 7 R → IsCyclic ↥R ∧ Nat.card ↥R ≤ 49 :=
    sylow_transport e fun R hR => sylow_sl_two hF R hR
  exact kData_of_parts hZ hS (OutData.of_mulEquiv e (outData_sl_two hF)) hc7 hc

theorem kData_of_model {G : Type} [Group G] [Finite G] {K : Subgroup G} {c : G} {m : ℕ}
    {F : Type} [Field F] [Finite F]
    (hm : (m = 2 ∧ Nat.card F = 2 ^ 21) ∨ ((m = 3 ∨ m = 4) ∧ Nat.card F = 2 ^ 7))
    (e : ↥K ≃* Matrix.SpecialLinearGroup (Fin m) F) (hc7 : c ^ 7 = 1)
    (hc : InducesFieldAut 7 c K) : KData G K c := by
  rcases hm with ⟨rfl, hF⟩ | ⟨hm, hF⟩
  · exact kData_of_model_two hF e hc7 hc
  · exact kData_of_model_lin hm hF e hc7 hc

end CFSG.RankThree.PartOne.TAIL
