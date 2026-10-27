module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SporadicThreePermutingLe
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SporadicPermutesInvariant
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatJ3E9
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.SporRank
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.SporData
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2HoldsSpor
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.OddCoversLift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SporadicModelGlue

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

theorem sporadicThreePermuting_J3
    {Y : Type} [Group Y] [Finite Y] {K S : Subgroup Y} [K.Normal]
    (hS : CFSG.Quasithin.IsSylowIn 2 S ⊤) (e : ↥K ≃* CFSG.Blueprint.NativeSporadic.J3) :
    ∃ E : Subgroup Y, E ≤ K ∧ E ≠ ⊥ ∧ IsPGroup 3 ↥E ∧ (∀ x ∈ E, x ^ 3 = 1) ∧
      ¬ IsCyclic ↥E ∧ CFSG.LocalAnalysis.UniquenessCase.UC22.Permutes E S := by
  open CFSG.QuasithinUnique.Ch1.SporLat.J3K in
  have hx := e9x_pow_three
  open CFSG.QuasithinUnique.Ch1.SporLat.J3K in
  have hy := e9y_pow_three
  open CFSG.QuasithinUnique.Ch1.SporLat.J3K in
  have hxy := e9x_mul_e9y
  open CFSG.QuasithinUnique.Ch1.SporLat.J3K in
  have hQ9 := CFSG.RankThree.Asc83Table.card_closure_pair_eq_nine hx hy hxy e9x_ne_one
    e9y_not_mem_zpowers
  open CFSG.QuasithinUnique.Ch1.SporLat.J3K in
  have hc : ⁅e9x, e9y⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hxy
  open CFSG.QuasithinUnique.Ch1.SporLat.J3K in
  have hzx : Commute ⁅e9x, e9y⁆ e9x := by rw [hc]; exact Commute.one_left _
  open CFSG.QuasithinUnique.Ch1.SporLat.J3K in
  have hzy : Commute ⁅e9x, e9y⁆ e9y := by rw [hc]; exact Commute.one_left _
  open CFSG.QuasithinUnique.Ch1.SporLat.J3K in
  have hQP : Subgroup.closure ({e9x, e9y} : Set ↥CFSG.Sporadic.Schreier.j3P) ≤
      CFSG.QuasithinUnique.Ch1.SporLat.J3K.Y 3 :=
    (Subgroup.closure_le _).2
      (Set.insert_subset_iff.2 ⟨e9x_mem, Set.singleton_subset_iff.2 e9y_mem⟩)
  exact exists_permutes_of_invariant_member CFSG.QuasithinUnique.Ch1.SporLat.J3K.S_sylow
    (CFSG.QuasithinUnique.Ch1.SporLat.J3K.S_le_Y 3) CFSG.QuasithinUnique.Ch1.SporLat.J3K.card_Y3
    CFSG.QuasithinUnique.Ch1.SporLat.J3K.map_Y3 hQP hQ9
    (fun q hq => pow_three_eq_one_of_mem_closure_cubic hx hy hzx hzy hq)
    (e.trans CFSG.Sporadic.Schreier.j3PermEquiv) hS

section RankThreeHolds

open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator


theorem k_SporadicThreePermutingLe_three_holds : K_SporadicThreePermutingLe 3 := by
  intro Y _ _ K S s hKN hQ hOdd hs hC hIdx hSyl hm3 hle hON
  obtain ⟨e⟩ := hs
  have hperf : Group.IsPerfect ↥K := (Group.isPerfect_def).2 hQ.1
  have hdvd := CFSG.Quasithin.B69K.OddCovers.card_center_dvd_hopfMultiplier hperf e
  rw [CFSG.OddStandard.HigherRank.YamadaG23.l2Sporadic_holds s] at hdvd
  have h12 : Nat.card (Subgroup.center ↥K) ∣ 12 :=
    hdvd.trans (sporadicMultiplierOrder_dvd_twelve s)
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group s
  by_cases hZ : Subgroup.center ↥K = ⊥
  ·
    let eK : ↥K ≃* CFSG.Blueprint.NativeSporadic.Carrier s :=
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans e
    by_cases hJ : s = .J3
    · subst hJ
      exact sporadicThreePermuting_J3 hSyl eK
    · exact absurd (by omega : CFSG.Open.pRank 3 (⊤ : Subgroup ↥K) = 3)
        (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.sporadic_three_rank_ne_three s hJ
          (eK.trans b))
  ·
    have hcop : Nat.Coprime (Nat.card (Subgroup.center ↥K)) 2 :=
      (Nat.coprime_two_right).mpr hOdd
    have hdvd3 : Nat.card (Subgroup.center ↥K) ∣ 3 := by
      have hd12 : Nat.card (Subgroup.center ↥K) ∣ 2 * (2 * 3) := by simpa using h12
      exact hcop.dvd_of_dvd_mul_left (hcop.dvd_of_dvd_mul_left hd12)
    have hZcard : Nat.card (Subgroup.center ↥K) = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd3 with h1 | h3
      · exact absurd h1 fun h => hZ (Subgroup.card_eq_one.mp h)
      · exact h3
    have hs7 : s = .M22 ∨ s = .J3 ∨ s = .McL ∨ s = .Suz ∨ s = .ONan ∨ s = .Fi22 ∨
        s = .Fi24Prime := by
      apply CFSG.HardMathSupport.Timmesfeld.Coordinator.eq_of_three_dvd_sporadicMultiplierOrder
      have hfun : CFSG.RankThree.PartTwo.Sec4.Census.sporadicMultiplierOrder s =
          CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.sporadicMultiplierOrder s := by
        cases s <;> rfl
      rw [hfun, hZcard] at hdvd
      exact hdvd
    have heb : Nonempty (↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.sporadic s).Group) :=
      ⟨e.trans b⟩
    rcases hs7 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    ·
      obtain ⟨E, -, hE, hc⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num)
        (⊤ : Subgroup ↥K)
      have h9 :=
        CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.abelian_three_card_le_nine_hatM22
          hQ.1 hZcard (e.trans b) E (IsPGroup.of_card hc)
          (fun x hx y hy => congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
      have h27 : 3 ^ 3 ≤ 3 ^ CFSG.Open.pRank 3 (⊤ : Subgroup ↥K) :=
        Nat.pow_le_pow_right (by norm_num) hm3
      rw [hc] at h9
      have := h27.trans h9
      norm_num at this
    · have := CFSG.HardMathSupport.Solomon.Coordinator.sporCover_J3_pRank_ge_four ↥K hperf
        hZcard heb
      omega
    · have := CFSG.HardMathSupport.Solomon.Coordinator.sporCover_McL_pRank_ge_four ↥K hperf
        hZcard heb
      omega
    · have := CFSG.HardMathSupport.Solomon.Coordinator.sporCover_Suz_pRank_ge_four ↥K hperf
        hZcard heb
      omega
    · exact absurd rfl hON
    · have := CFSG.HardMathSupport.Solomon.Coordinator.sporCover_Fi22_pRank_ge_four ↥K hperf
        hZcard heb
      omega
    · have := CFSG.HardMathSupport.Solomon.Coordinator.sporCover_Fi24Prime_pRank_ge_four ↥K
        hperf hZcard heb
      omega

end RankThreeHolds

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
