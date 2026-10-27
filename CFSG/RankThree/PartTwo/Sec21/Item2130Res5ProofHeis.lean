module

public import CFSG.RankThree.PartTwo.Sec21.Item2130Res5ProofHeisCtx
public import CFSG.RankThree.PartTwo.Sec21.Item2130Res3ProofTypes

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)

namespace Item2130Res5Proof

variable {G : Type} [Group G] [Finite G]

theorem heisCtx_of {A E U L : Subgroup G} {c b : G} {U₀ Y : Subgroup G}
    (hcfg : Config2130 G A E U c L) (h9 : Nat.card (A ⊓ L : Subgroup G) = 9)
    (hC : Choice2130 A E c L b U₀ Y) : HeisCtx G A b Y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpair := hcfg.pair
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hA27 : Nat.card A = 27 := by rw [hcfg.card_eq, h9]
  have hEA : E ≤ A := hpair.mem_E.2
  have hE27 : Nat.card E = 27 := hpair.mem_E.1.2.1
  have hEeq : E = A := Subgroup.eq_of_le_of_card_ge hEA (by rw [hA27, hE27])
  have hAE : A ∈ partTwoE G := hEeq ▸ hpair.mem_E.1
  have hbA : b ∈ A := hC.b_mem.1
  have hb3 : b ^ 3 = 1 := hAe.2 b hbA
  have hA3 : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hAe.2 g g.2)⟩
  have hAb : A ≤ Subgroup.centralizer ({b} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨b, hbA⟩))
  exact
    { toPartTwoStanding := hpair.standing
      partTwoF_eq := (hpair.side hAE).symm
      mem_partTwoE := hAE
      eq_of_le := fun hB hAB => hpair.mem_S.1.2.1 _ hB hAB
      mem_A := hbA
      orderOf_eq := orderOf_eq_prime hb3 hC.b_ne_one
      mem_thetaComponentsAt := lZeroStarAt_subset A b hC.y_mem
      le_normalizer := hC.three_norm A hA3 hAb
      sectionCentralizer_eq := hC.sec_cent }

end Item2130Res5Proof

open Item2130Res5Proof

theorem item2130Heis125_of
    (h45 : Sec4.Item4_5) : Item2130Heis125 := by
  intro G _ _ A E U c L b U₀ Y hcfg h9 hC _ htype hH
  have hty : Sec13.Item131bProof.HeisType (Y ⧸ aschbacherSolvableCore 3 Y) := by
    rcases htype with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact Or.inl h
  exact normalizer_le_of_heis_threeH (Sec12.item125BarThree_of_item45' h45)
    (heisCtx_of hcfg h9 hC) hH hty

end CFSG.RankThree.PartTwo.Sec21
