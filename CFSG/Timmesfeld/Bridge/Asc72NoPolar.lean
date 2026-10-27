module

public import CFSG.Timmesfeld.Bridge.Asc72Width
public import CFSG.Timmesfeld.Bridge.SchurNarrow
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.NoLeastLocalFailure

public section

namespace CFSG.Timmesfeld.Bridge.Asc72

open CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge

theorem isBenderGroup_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : CFSG.BenderSuzuki.IsBenderGroup Y) : CFSG.BenderSuzuki.IsBenderGroup X := by
  rcases h with ⟨n, hn, f⟩ | ⟨n, hn, f⟩ | ⟨n, hn, f⟩
  · exact .isPSL2 n hn (e.trans f)
  · exact .isSuzuki n hn (e.trans f)
  · exact .isPSU3 n hn (e.trans f)

variable {G : Type} [Group G] {D : Set G}

theorem Setup.not_isSolvable (hS : Setup G D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) :
    ¬ Group.IsSolvable G := by
  intro hsol
  obtain ⟨d, hd⟩ := hS.nonempty
  have htop : (⊤ : Subgroup G) = ⊥ :=
    hrad ⊤ inferInstance (Group.isSolvable_of_isSolvable_injective
      (f := (⊤ : Subgroup G).subtype) Subtype.val_injective)
  exact hS.oddT.ne_one hd ((Subgroup.mem_bot).mp (htop ▸ Subgroup.mem_top d))

theorem isBenderGroup_of_noPolar [Finite G] (hS : Setup G D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) (hdisc : Disconnected D)
    (hnp : Moufang.NoPolar D) : CFSG.BenderSuzuki.IsBenderGroup G := by
  obtain ⟨x, hx, -⟩ := id hdisc
  have hSE := (fusionStronglyEmbedded_iff _).2
    (asc73For_of CFSG.ShultStronglyClosedTI.theoremTwo schurNarrowInput G D hS.normal
      hS.oddT.isInvolutionSet hS.gen hnp hdisc x hx)
  have hns := hS.not_isSolvable hrad
  obtain ⟨u, hu, v, hv, huv, hc⟩ := hS.exists_commute_of_not_isSolvable hns
  rcases bender_strongly_embedded_normal_series G _ hSE with
    hSyl | ⟨M, N, hM, hNn, hMN, -, hMo, hNo, hB⟩
  · exfalso
    have hNC := noCommutingDistinctInvolutions_of_sylow hSyl
    have heq := hNC ⟨u, hS.oddT.orderOf_eq_two hu⟩ ⟨v, hS.oddT.orderOf_eq_two hv⟩ hc.eq
    exact huv (congrArg Subtype.val heq)
  · have hM1 : M = ⊥ := hrad M hM (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hMo)
    have hDN : D ⊆ N := fun d hd => mem_of_odd_index hNo (hS.oddT.mul_self_eq_one hd)
    have hNtop : N = ⊤ := hS.eq_top_of_subset N hDN
    have hsub : M.subgroupOf N = ⊥ := by
      rw [hM1, Subgroup.bot_subgroupOf]
    let e₁ : G ≃* N := (Subgroup.topEquiv.symm).trans (MulEquiv.subgroupCongr hNtop.symm)
    let e₂ : N ≃* N ⧸ M.subgroupOf N :=
      (QuotientGroup.quotientBot.symm).trans (QuotientGroup.quotientMulEquivOfEq hsub.symm)
    exact isBenderGroup_of_mulEquiv (e₁.trans e₂) (isBenderGroup_of_fusionIsBenderGroup hB)

end CFSG.Timmesfeld.Bridge.Asc72
