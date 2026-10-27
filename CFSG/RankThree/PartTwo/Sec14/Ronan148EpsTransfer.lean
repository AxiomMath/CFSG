module

public import CFSG.RankThree.PartTwo.Sec14.Item148ResProofEps
public import CFSG.RankThree.PartTwo.Sec4.RonanEpsCfgForward
public import CFSG.RankThree.PartTwo.Sec4.RonanK429CfgTransfer
public import CFSG.RankThree.PartTwo.Sec4.Item45Closed
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Census

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.RonanEps

theorem inf_centralizer_eq_bot {G : Type} [Group G] {A L K' : Subgroup G} {c : G} (hK'L : K' ≤ L)
    (hcent : Subgroup.zpowers c = A ⊓ Subgroup.centralizer (K' : Set G)) (hc1 : c ≠ 1)
    (hc3 : c ^ 3 = 1) (hLc : ¬ L ≤ Subgroup.centralizer {c}) :
    A ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set H := A ⊓ Subgroup.centralizer (L : Set G) with hH
  have hle : H ≤ Subgroup.zpowers c := by
    rw [hcent]
    exact inf_le_inf_left A (Subgroup.centralizer_le hK'L)
  have hco : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have hcard : Nat.card (Subgroup.zpowers c) = 3 := by rw [Nat.card_zpowers, hco]
  haveI : Fact (Nat.card (Subgroup.zpowers c)).Prime := ⟨hcard ▸ Nat.prime_three⟩
  rcases (H.subgroupOf (Subgroup.zpowers c)).eq_bot_or_eq_top_of_prime_card with h | h
  · rw [Subgroup.subgroupOf_eq_bot] at h
    exact h.eq_bot_of_le hle
  · rw [Subgroup.subgroupOf_eq_top] at h
    exfalso
    apply hLc
    intro l hl
    have hcL : c ∈ Subgroup.centralizer (L : Set G) := (h (Subgroup.mem_zpowers c)).2
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hcL l hl

section Census

theorem item4_29EpsOuter_of_rowsS
    (R : KEpsRowsS) : Item4_29EpsOuter := by
  intro G _ _ hG hθ hE A hA c hc hc1 L hL hLn hLc K hK K' hK' htype hcent
  have hAN : A ≤ Subgroup.normalizer (L : Set G) := by
    intro a _
    rw [Subgroup.normalizer_eq_top_iff.mpr hLn]
    exact Subgroup.mem_top a
  have hK'M : K' ≤ L ⊓ Subgroup.centralizer {c} := hK' ▸ Subgroup.map_subtype_le K
  have hK'L : K' ≤ L := hK'M.trans inf_le_left
  have eK : K ≃* K' := (K.equivMapOfInjective _ (Subgroup.subtype_injective _)).trans
    (MulEquiv.subgroupCongr hK'.symm)
  have hK'q : IsQuasisimple K' := CFSG.LocalCores.isQuasisimple_of_mulEquiv eK hK.1
  have hK'sn : (K'.subgroupOf (L ⊓ Subgroup.centralizer {c})).IsSubnormal := by
    rw [hK', Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective
      (Subgroup.subtype_injective _)]
    exact hK.2
  have hK'type : IsTypeEps (K' ⧸ CFSG.pCore 2 K') :=
    isTypeEps_of_mulEquiv (quotPCoreTwoCongr eK).symm htype
  have hAC : A ⊓ Subgroup.centralizer (L : Set G) = ⊥ :=
    inf_centralizer_eq_bot hK'L hcent hc1 (hA.1.2 c hc) hLc
  have hAK' := normalizer_le_of_item4_5 rank3II_4_5 hG hA hc hL hK'M hK'q hK'sn
  obtain ⟨-, hcfg⟩ := cfgSEps_of hθ hA hc hL hAN hAC hLc hK'M hK'q hK'sn hK'type hAK' hcent
  have hq : IsQuasisimple L := hL.1
  have hlist := RonanK432.list42_quotient_center hq (sectionFourHyp_subgroup hG L)
  exact R.noCfg_of_list42 hq.2.1 hq.2.2 hlist _ _ _ hcfg

end Census

end CFSG.RankThree.PartTwo.Sec14
