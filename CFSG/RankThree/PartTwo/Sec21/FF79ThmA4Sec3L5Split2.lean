module

public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L5Split
public import CFSG.RankThree.PartTwo.Sec21.FF79ThmA4Sec3L4Ap2

import CFSG.RankThree.PartTwo.Sec21.FF79ThmA4Sec3L4Rank2
import CFSG.GH74.Uniqueness.Bender.Core

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.H4

open CFSG CFSG.RankThree.PartTwo.Sec21
open CFSG.Assembly (KProper InCatalog)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {b : G} {J B A P D : Subgroup G} {a : G}

theorem s35_cqImg_inf_layer {U As : Subgroup G} :
    cqImg U (As ⊓ OppE 3 (CenS U)) = cqImg U As ⊓ layer (CQ U) := by
  ext y
  constructor
  · intro hy
    obtain ⟨c, hc, rfl⟩ := mem_cqImg.mp hy
    obtain ⟨_, hl⟩ := mem_OppE.mp hc.2
    exact ⟨mk_mem_cqImg c hc.1, hl⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨c, hc, rfl⟩ := mem_cqImg.mp h1
    exact mk_mem_cqImg c ⟨hc, mem_OppE.mpr ⟨c.2, h2⟩⟩

theorem s35_cqImg_sylow {U As : Subgroup G} (hAs : IsSylowOf 3 As (CenS U)) :
    IsSylowOf 3 (cqImg U As) ⊤ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : (pPrimeCore 3 ↥(CenS U)).Normal := pPrimeCore_normal
  have hSyl : IsSylowOf 3 (As.subgroupOf (CenS U)) ⊤ := by
    refine L41.isSylowOf_of_card_p le_top ?_
    rw [Subgroup.card_top, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAs.1).toEquiv,
      L41.isSylowOf_card_p hAs]
  exact pp_isSylowOf_map _ (coprime_pPrimeCore _) hSyl

theorem s35_card_Shat {U As : Subgroup G} (hAs : IsSylowOf 3 As (CenS U))
    (hL : IsLnq 3 2 2 (⊤ : Subgroup (layer (CQ U)))) :
    Nat.card ↥(As ⊓ OppE 3 (CenS U)) = 9 := by
  haveI : (layer (CQ U)).Normal := s35_layer_normal
  have h1 := s35_card_sylow_inf (s35_cqImg_sylow hAs) (s35_layer_card hL)
  rw [← s35_cqImg_inf_layer, cqImg_card (hAs.2.1.to_inf_left) (inf_le_left.trans hAs.1)] at h1
  exact h1

theorem s35_Shat_le_A (h : FF79Sec34In4 b J B A P D) (hU : FF79Sec34UFacts b a J A)
    {As : Subgroup G} (hAs : FF79AStar b D A As)
    (h9 : Nat.card ↥(As ⊓ OppE 3 (CenS (U34 b a J A))) = 9) :
    As ⊓ OppE 3 (CenS (U34 b a J A)) ≤ A := by
  obtain ⟨-, -, -, hbAs, -, -, -, hAdef⟩ := hAs
  have hb3 : orderOf b = 3 := h.hyp.ord
  have hbN : b ∈ Nor (As ⊓ OppE 3 (CenS (U34 b a J A))) :=
    nor_inf hbAs (nor_OppE_of_nor (nor_cenS_of_nor hU.b_nor))
  have hbS : b ∉ As ⊓ OppE 3 (CenS (U34 b a J A)) :=
    fun hb => sec34S_b_not_mem hU (OppE_le _ hb.2)
  have hinf := sec34S_inf_zpowers hb3 hbS
  have hZ : Subgroup.zpowers b ≤ Subgroup.normalizer
      ((As ⊓ OppE 3 (CenS (U34 b a J A)) : Subgroup G) : Set G) :=
    (Subgroup.zpowers_le).mpr hbN
  have hcard : Nat.card ↥(As ⊓ OppE 3 (CenS (U34 b a J A)) ⊔ Subgroup.zpowers b) = 27 := by
    rw [CFSG.GH74.Uniqueness.Bender.card_sup_eq_mul_of_le_normalizer hZ hinf, h9,
      Nat.card_zpowers, hb3]
  intro x hx
  exact (hAdef x hx.1).mp (s35_comm_card27 hcard (Subgroup.mem_sup_left hx)
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers b)))

theorem sec35_split (hG : IsSimpleGroup G) (hna : ∃ x y : G, x * y ≠ y * x)
    (hKp : KProper InCatalog G) (hs : FF79Sec3 b J) (h : FF79Sec34In4 b J B A P D)
    (hU : FF79Sec34UFacts b a J A) (hoa : orderOf a = 3)
    (hK : IsLnq 2 2 2 (Lay (J ⊓ Cen a))) (haC : a ∈ CenS (U34 b a J A))
    (hL : IsLnq 3 2 2 (⊤ : Subgroup (layer (CenS (U34 b a J A) ⧸
      pPrimeCore 3 (CenS (U34 b a J A)))))) :
    IsElemAb 3 2 (A ⊓ OppE 3 (CenS (U34 b a J A))) ∧
    U34 b a J A ⊓ (A ⊓ OppE 3 (CenS (U34 b a J A))) = ⊥ ∧
    U34 b a J A ⊔ (A ⊓ OppE 3 (CenS (U34 b a J A))) = A ∧
    b ∈ Nor (A ⊓ OppE 3 (CenS (U34 b a J A))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨As, hAs⟩ := h.star
  have hSyl := sec34_As_syl hs h hU hAs
  have h9 := s35_card_Shat hSyl hL
  have hle := s35_Shat_le_A h hU hAs h9
  have hU2 : A ⊓ OppE 3 (CenS (U34 b a J A)) = As ⊓ OppE 3 (CenS (U34 b a J A)) :=
    le_antisymm (inf_le_inf_right _ hAs.1) (le_inf hle inf_le_right)
  obtain ⟨hAc, hAp⟩ := (isElementaryAbelian_iff 3 A).mp h.elemA.1
  have hel : IsElemAb 3 2 (A ⊓ OppE 3 (CenS (U34 b a J A))) := by
    refine ⟨(isElementaryAbelian_iff 3 _).mpr ⟨fun x hx y hy => hAc x hx.1 y hy.1,
      fun x hx => hAp x hx.1⟩, ?_⟩
    rw [hU2, h9]; norm_num
  have hinf : U34 b a J A ⊓ (A ⊓ OppE 3 (CenS (U34 b a J A))) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    obtain ⟨hxU, -, hxO⟩ := hx
    have hxC : x ∈ CenS (U34 b a J A) := sec34_UleC hU hxU
    obtain ⟨hxC', hlay⟩ := mem_OppE.mp hxO
    have hz := cqImg_le_center (U := U34 b a J A) (T := U34 b a J A) le_rfl
      (mk_mem_cqImg ⟨x, hxC⟩ hxU)
    have h1 := s35_layer_center hL _ hlay hz
    have h2 : (⟨x, hxC⟩ : ↥(CenS (U34 b a J A))) ∈ pPrimeCore 3 ↥(CenS (U34 b a J A)) :=
      (QuotientGroup.eq_one_iff _).mp h1
    have hxo : x ∈ Opp 3 (CenS (U34 b a J A)) := Subgroup.mem_map.mpr ⟨_, h2, rfl⟩
    exact eq_one_of_mem_opp (haveI := hU.elemU.1; IsElementaryAbelian.isPGroup 3 _) hxU hxo
  refine ⟨hel, hinf, ?_, nor_inf h.bA (nor_OppE_of_nor (nor_cenS_of_nor hU.b_nor))⟩
  have hel' := rank2_elemAb_sup hU.elemU hel
    (fun x hx y hy => hAc x (hU.U_le_A hx) y hy.1) hinf
  exact Subgroup.eq_of_le_of_card_ge (sup_le hU.U_le_A inf_le_left)
    (by rw [hel'.2, h.elemA.2])

end CFSG.RankThree.PartTwo.Sec21.FF79.H4
