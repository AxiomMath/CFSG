module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ThreeWeakClosure
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeAEqVRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KRankOneBorel.Holds
public import CFSG.GroupTheory.DedekindNormalizer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.CGT.Timmesfeld75 (IsTI conjSubgroup)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {Ch : Choice2011 G}

omit [Finite G] in
theorem inf_sup_eq_sup_inf_of_le_normalizer {L T X : Subgroup G}
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hTX : T ≤ X) :
    (L ⊔ T) ⊓ X = (L ⊓ X) ⊔ T := by
  have h := CFSG.GroupTheory.inf_sup_eq_sup_inf_of_le_normalizer
    (S := T) (T := L) (U := X) hTX hTL
  calc (L ⊔ T) ⊓ X = X ⊓ (L ⊔ T) := inf_comm _ _
    _ = X ⊓ (T ⊔ L) := by rw [sup_comm L T]
    _ = T ⊔ (X ⊓ L) := h
    _ = (L ⊓ X) ⊔ T := by rw [inf_comm X L, sup_comm T (L ⊓ X)]

theorem eq_bot_of_isPerfect_of_isSylowIn_normal {L S : Subgroup G}
    (hperf : Group.IsPerfect ↥L) (hSL : S ≤ L)
    (hSn : L ≤ Subgroup.normalizer (S : Set G)) (hSyl : IsSylowIn 2 S L) : L = ⊥ := by
  by_contra hL
  haveI : Nontrivial ↥L := (Subgroup.nontrivial_iff_ne_bot L).2 hL
  haveI : Group.IsPerfect ↥L := hperf
  haveI hN : (S.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSL).mpr hSn
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : IsPGroup 2 (S.subgroupOf L) := hSyl.isPGroup.comap_subtype
  have hnil : Group.IsNilpotent ↥(S.subgroupOf L) := hS2.isNilpotent
  haveI : Group.IsSolvable ↥(S.subgroupOf L) := @IsNilpotent.to_isSolvable _ _ hnil
  have hrel : (S.subgroupOf L).index = S.relIndex L := by
    rw [← Subgroup.relIndex_top_right (H := S.subgroupOf L), ← Subgroup.subgroupOf_self L,
      Subgroup.relIndex_subgroupOf (le_rfl : L ≤ L)]
  have hodd : Odd (Nat.card (↥L ⧸ (S.subgroupOf L))) := by
    rw [← Subgroup.index_eq_card, hrel]
    exact Nat.not_even_iff_odd.mp fun h => hSyl.not_dvd_relIndex h.two_dvd
  haveI : Group.IsSolvable (↥L ⧸ (S.subgroupOf L)) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have hsolv : Group.IsSolvable ↥L := Group.isSolvable_of_subgroup_quotient (S.subgroupOf L)
  exact Group.IsPerfect.not_isSolvable ↥L hsolv

namespace Ctx23L

theorem L0_le_normalizer_of_sup_eq (c : Ctx23L D Ch) (h2010 : S20_10 D) (h1930 : H1930 D)
    (heq : c.L0 ⊔ D.T =
      ((c.L0 ⊔ D.T) ⊓ Subgroup.normalizer (D.U : Set G)) ⊔
        ((c.L0 ⊔ D.T) ⊓ Subgroup.normalizer (E3.wClos D.U 0 D.T : Set G))) :
    c.L0 ≤ Subgroup.normalizer (E3.wClos D.U 0 D.T : Set G) := by
  let W0 : Subgroup G := E3.wClos D.U 0 D.T
  let J : Subgroup G := c.L0 ⊓ Subgroup.normalizer (W0 : Set G)
  let S : Subgroup G := D.T ⊓ c.L0
  have hTN : D.T ≤ Subgroup.normalizer (W0 : Set G) :=
    Subgroup.le_normalizer.trans (E3.normalizer_le_normalizer_wClos (V := D.U) (i := 0) D.T)
  have hSI : D.T ≤ Subgroup.normalizer (S : Set G) :=
    (le_inf Subgroup.le_normalizer c.hL0.1.1).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hJ1 : D.T ⊓ c.L0 ≤ J := le_inf inf_le_right (inf_le_left.trans hTN)
  have hTJ : D.T ≤ Subgroup.normalizer (J : Set G) :=
    (le_inf c.hL0.1.1 (hTN.trans Subgroup.le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  rcases kRankOneBorel_holds (T := D.T) (L := c.L0) (J := J) D.sylowM.isPGroup c.hL0.1.1
      (isSylowIn_T_inf c) c.hL0.1.2.1 (s20_10Shape_of h2010 h1930 c.hL0)
      hJ1 inf_le_left hTJ with hJN | hJL
  · have hM : c.L0 ⊓ D.M ≤ Subgroup.normalizer (S : Set G) :=
      inf_M_le_normalizer_sylow c h2010 h1930 kRankOneBorel_holds
    have hHle : c.L0 ⊔ D.T ≤ Subgroup.normalizer (S : Set G) := by
      rw [heq, normalizer_eq_of_inCalV D (uc22p22e_inCalV_U D)]
      refine sup_le ?_ ?_
      · rw [inf_sup_eq_sup_inf_of_le_normalizer c.hL0.1.1 D.sylowM.le]
        exact sup_le hM hSI
      · rw [inf_sup_eq_sup_inf_of_le_normalizer c.hL0.1.1 hTN]
        exact sup_le hJN hSI
    have hL0N : c.L0 ≤ Subgroup.normalizer (S : Set G) :=
      (le_sup_left : c.L0 ≤ c.L0 ⊔ D.T).trans hHle
    have hperf : Group.IsPerfect ↥c.L0 := Subgroup.isPerfect_iff.mpr c.hL0.1.2.1
    have hbot : c.L0 = ⊥ :=
      eq_bot_of_isPerfect_of_isSylowIn_normal hperf (inf_le_right : S ≤ c.L0) hL0N
        (isSylowIn_T_inf c)
    exact absurd (hbot ▸ bot_le) (L0_not_le_M c)
  · rw [← hJL]
    exact inf_le_right

theorem isCalH0_U (c : Ctx23L D Ch) (h861 : W3Lem86_1 G)
    (hTim : CFSG.CGT.Timmesfeld75.NodeStatement) (hcat : ¬ CFSG.Blueprint.Catalog G)
    (h2010 : S20_10 D) (h1930 : H1930 D)
    (hU0 : c.U0 = conjClosure (c.L0 ⊓ D.M) D.Z) (hlt : c.U0 < D.U) :
    CFSG.LocalAnalysis.WeakClosure81.IsCalH0 D.U (c.L0 ⊔ D.T) := by
  refine ⟨isCalH_U c, ?_⟩
  by_contra hnot
  have h4 : 4 ≤ Nat.card D.U := four_le_card_U c hU0 hlt
  have hV7 : CFSG.LocalAnalysis.WeakClosure81.Hyp7 D.U :=
    ⟨(uCore_le_and_isElemAbelian D.standing.charTwo D.maxLocal.1 D.sylowM).2, by omega,
      c.hTI⟩
  have hWgt : D.U < E3.wClos D.U 0 D.T := wClos_zero_gt c hTim hcat h4
  have hSyl : IsSylowIn 2 D.T ((c.L0 ⊔ D.T) ⊓ normalizer (D.U : Set G)) := by
    have hSylH : IsSylowIn 2 D.T (c.L0 ⊔ D.T) := TwelveShort.isSylowIn_of_le D le_sup_right
    have hle : D.T ≤ (c.L0 ⊓ D.M) ⊔ D.T := le_sup_right
    have hleH : (c.L0 ⊓ D.M) ⊔ D.T ≤ c.L0 ⊔ D.T :=
      sup_le (inf_le_left.trans le_sup_left) le_sup_right
    have hmul := Subgroup.relIndex_mul_relIndex D.T ((c.L0 ⊓ D.M) ⊔ D.T) (c.L0 ⊔ D.T) hle hleH
    have hSylD : IsSylowIn 2 D.T ((c.L0 ⊓ D.M) ⊔ D.T) :=
      ⟨hle, hSylH.isPGroup, fun hdvd => hSylH.not_dvd_relIndex (hmul ▸ hdvd.mul_right _)⟩
    have hded : (c.L0 ⊔ D.T) ⊓ D.M = (c.L0 ⊓ D.M) ⊔ D.T :=
      inf_sup_eq_sup_inf_of_le_normalizer c.hL0.1.1 D.sylowM.le
    rw [normalizer_eq_of_inCalV D (uc22p22e_inCalV_U D), hded]
    exact hSylD
  obtain ⟨heq, -⟩ := h861 D.U (c.L0 ⊔ D.T) D.T hV7 (isCalH_U c)
    (fun h0 => hnot h0.2) hSyl hWgt.ne' (Or.inl (centralizersInM_U c))
  have hL0W : c.L0 ≤ Subgroup.normalizer (E3.wClos D.U 0 D.T : Set G) :=
    L0_le_normalizer_of_sup_eq c h2010 h1930 heq
  have hTN : D.T ≤ Subgroup.normalizer (E3.wClos D.U 0 D.T : Set G) :=
    Subgroup.le_normalizer.trans (E3.normalizer_le_normalizer_wClos (V := D.U) (i := 0) D.T)
  have hWle : E3.wClos D.U 0 D.T ≤ pCoreOf 2 (c.L0 ⊔ D.T) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((E3.wClos_le 0 D.T).trans le_sup_right) (sup_le hL0W hTN)
      (D.sylowM.isPGroup.to_le (E3.wClos_le 0 D.T))
  exact hnot ((E3.le_wClos ⟨Data.u_le_T D, 1, by rw [conjSubgroup_one],
    by rw [conjSubgroup_one, E3.mQuot_self]⟩).trans hWle)

end Ctx23L

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
