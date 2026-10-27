module

public import CFSG.LocalAnalysis.StandardType.GGOTwoPrimeOddProduct
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP13E7
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP13E7Cent
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommLinTransferS3

public noncomputable section

namespace CFSG.StandardType.FrameRoute

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.OddStandard.SmallF3.Omega.E7RootSet TableBExcTwo TableBExcTwoTB
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Lin


theorem p13e7_card_ggOTwoPrime_hyp_frame {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) :
    Nat.card (ggOTwoPrime (Subgroup.centralizer
      (p13e7Hyp K (redV (frameE7.root 0)) : Set (adjointGroup .E7 K)))) = 6 := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let T : Subgroup (adjointGroup .E7 K) := (tE K frameE7).range
  let F : Subgroup (adjointGroup .E7 K) := p13e7Hyp K (redV (frameE7.root 0))
  let R : Subgroup (adjointGroup .E7 K) := (rho K frameE7 0).range
  have hTcard : Nat.card T = 3 ^ 7 :=
    (p13a6_E7 (E := T) hK (MulEquiv.refl _) (by simp [T])).1
  have hFT : F ≤ T := by
    rintro x hx
    change x ∈ ((p13e7HypVec (redV (frameE7.root 0))).toSubgroup.map (tE K frameE7)) at hx
    obtain ⟨v, -, rfl⟩ := hx
    exact ⟨v, rfl⟩
  have hT3 : IsPGroup 3 T := IsPGroup.of_card hTcard
  have hF3 : IsPGroup 3 F := hT3.to_le hFT
  obtain ⟨e⟩ := nonempty_mulEquiv_perm_three_of_card_two hK
  let eR : R ≃* Equiv.Perm (Fin 3) :=
    (MonoidHom.ofInjective (rho_injective frameE7 0)).symm.trans e
  have hRcard : Nat.card R = 6 := by
    rw [Nat.card_congr eR.toEquiv]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
  have hRC : R ≤ Subgroup.centralizer (F : Set (adjointGroup .E7 K)) := by
    rintro _ ⟨A, rfl⟩
    exact Subgroup.mem_centralizer_iff.mpr fun f hf =>
      (p13e7_commute_rho_of_mem_hyp_frame hf A).eq
  have hne : Subgroup.centralizer (F : Set (adjointGroup .E7 K)) ≠ T := by
    intro h
    have hdiv := Subgroup.card_dvd_of_le (h ▸ hRC)
    rw [hRcard, hTcard] at hdiv
    norm_num at hdiv
  rcases p13e7_case_frame hK with h | ⟨R', ⟨e'⟩, hFR, hdis, hC, -, -⟩
  · exact False.elim (hne h)
  · rw [hC, ggOTwoPrime_sup_of_isPGroup_odd (p := 3) (by decide) hF3 hFR hdis,
      ggOTwoPrime_eq_self_of_equiv_perm e', Nat.card_congr e'.toEquiv]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]

end CFSG.StandardType.FrameRoute
