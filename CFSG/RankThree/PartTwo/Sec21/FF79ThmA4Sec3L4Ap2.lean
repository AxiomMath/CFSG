module

public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L4Ap1
public import CFSG.RankThree.PartTwo.Sec21.FF79ThmA4Sec3L4Syl

import CFSG.GroupTheory.PCore.PrimeSetCore

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.H4

open CFSG CFSG.RankThree.PartTwo.Sec21
open CFSG.Assembly (KProper InCatalog)

section Generic

variable {G : Type} [Group G] [Finite G]

theorem mem_cqImg {U T : Subgroup G} {y : CQ U} :
    y ∈ cqImg U T ↔ ∃ c : ↥(CenS U), (c : G) ∈ T ∧ (QuotientGroup.mk c : CQ U) = y := by
  unfold cqImg
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, QuotientGroup.mk'_apply]

theorem mk_mem_cqImg {U T : Subgroup G} (c : ↥(CenS U)) (hc : (c : G) ∈ T) :
    (QuotientGroup.mk c : CQ U) ∈ cqImg U T := mem_cqImg.mpr ⟨c, hc, rfl⟩

theorem isPGroup_subgroupOf {T C : Subgroup G} (hT3 : IsPGroup 3 T) (hTC : T ≤ C) :
    IsPGroup 3 (T.subgroupOf C) :=
  hT3.of_surjective (Subgroup.subgroupOfEquivOfLe hTC).symm.toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hTC).symm.surjective

theorem coprime_pPrimeCore (U : Subgroup G) :
    Nat.Coprime 3 (Nat.card (pPrimeCore 3 ↥(CenS U))) := pPrimeCore_coprime_card

theorem cqImg_card {U T : Subgroup G} (hT3 : IsPGroup 3 T) (hTC : T ≤ CenS U) :
    Nat.card (cqImg U T) = Nat.card T := by
  haveI : (pPrimeCore 3 ↥(CenS U)).Normal := pPrimeCore_normal
  have h1 := pp_card_map (pPrimeCore 3 ↥(CenS U)) (coprime_pPrimeCore U)
    (isPGroup_subgroupOf hT3 hTC)
  unfold cqImg
  rw [h1]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTC).toEquiv

theorem cq_eq_of_mk_eq {U T : Subgroup G} (hT3 : IsPGroup 3 T) (hTC : T ≤ CenS U)
    {x y : ↥(CenS U)} (hx : (x : G) ∈ T) (hy : (y : G) ∈ T)
    (h : (QuotientGroup.mk x : CQ U) = QuotientGroup.mk y) : x = y := by
  haveI : (pPrimeCore 3 ↥(CenS U)).Normal := pPrimeCore_normal
  exact pp_eq_of_mk_eq (pPrimeCore 3 ↥(CenS U)) (coprime_pPrimeCore U)
    (isPGroup_subgroupOf hT3 hTC) (Subgroup.mem_subgroupOf.mpr hx) (Subgroup.mem_subgroupOf.mpr hy)
    h

theorem cqImg_elemAb {U T : Subgroup G} (hT : IsElementaryAbelian 3 T) (hTC : T ≤ CenS U) :
    IsElementaryAbelian 3 (cqImg U T) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsElementaryAbelian 3 (T.subgroupOf (CenS U)) := IsElementaryAbelian.subgroupOf hTC
  unfold cqImg
  exact IsElementaryAbelian.map _

theorem elemAb_of_cqImg {U T : Subgroup G} (hT3 : IsPGroup 3 T) (hTC : T ≤ CenS U)
    (hT : IsElementaryAbelian 3 (cqImg U T)) : IsElementaryAbelian 3 T := by
  rw [isElementaryAbelian_iff] at hT ⊢
  obtain ⟨hc, hp⟩ := hT
  refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
  · have := hc _ (mk_mem_cqImg ⟨x, hTC hx⟩ hx) _ (mk_mem_cqImg ⟨y, hTC hy⟩ hy)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul] at this
    exact congrArg Subtype.val
      (cq_eq_of_mk_eq hT3 hTC (T.mul_mem hx hy) (T.mul_mem hy hx) this)
  · have := hp _ (mk_mem_cqImg ⟨x, hTC hx⟩ hx)
    rw [← QuotientGroup.mk_pow] at this
    have h2 := cq_eq_of_mk_eq hT3 hTC (x := ⟨x, hTC hx⟩ ^ 3) (y := 1) (T.pow_mem hx 3)
      T.one_mem (this.trans rfl)
    simpa using congrArg Subtype.val h2

theorem cqβ_mk_of_cen {U : Subgroup G} {b : G} (hb : b ∈ Nor U) (x : ↥(CenS U))
    (hx : (x : G) ∈ Cen b) : cqβ U b hb (QuotientGroup.mk x : CQ U) = QuotientGroup.mk x := by
  rw [mk_conjAut_eq]
  congr 1
  apply Subtype.ext
  show b * (x : G) * b⁻¹ = x
  exact mul_inv_eq_iff_eq_mul.mpr (Subgroup.mem_centralizer_iff.mp hx b (Set.mem_singleton b))

theorem cqβ_pow_three {U : Subgroup G} {b : G} (hb : b ∈ Nor U) (hb3 : b ^ 3 = 1) :
    cqβ U b hb ^ 3 = 1 := by
  ext y
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective y
  have : (cqβ U b hb ^ 3) (QuotientGroup.mk c : CQ U) =
      cqβ U b hb (cqβ U b hb (cqβ U b hb (QuotientGroup.mk c : CQ U))) := by
    simp [pow_succ, MulAut.mul_apply]
  rw [this]
  simp only [mk_conjAut_eq]
  rw [conjAut_pow3 (nor_cenS_of_nor hb) hb3]
  rfl

theorem le_cenS_of_le {T V : Subgroup G} (hT : IsMulCommutative T) (hVT : V ≤ T) : T ≤ CenS V :=
  fun x hx => Subgroup.mem_centralizer_iff.mpr fun h hh => setLike_mul_comm (hVT hh) hx

theorem cqImg_le_center {U T : Subgroup G} (hTU : T ≤ U) :
    cqImg U T ≤ Subgroup.center (CQ U) := by
  intro y hy
  obtain ⟨c, hcT, rfl⟩ := mem_cqImg.mp hy
  rw [Subgroup.mem_center_iff]
  intro z
  obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective z
  have := Subgroup.mem_centralizer_iff.mp d.2 c (hTU hcT)
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  exact congrArg QuotientGroup.mk (Subtype.ext this.symm)

end Generic

section Basic

variable {G : Type} [Group G] [Finite G]
variable {b : G} {J B A P D : Subgroup G} {a : G}

theorem sec34_UleC (hU : FF79Sec34UFacts b a J A) : U34 b a J A ≤ CenS (U34 b a J A) :=
  le_cenS_of_le (hU.elemU.1.toIsMulCommutative) le_rfl

theorem sec34_a_cen_b (hU : FF79Sec34UFacts b a J A) : a ∈ Cen b := by
  have : a ∈ U34 b a J A ⊓ Cen b := by rw [hU.cenU_b]; exact Subgroup.mem_zpowers a
  exact this.2

theorem sec34_AleC (h : FF79Sec34In4 b J B A P D) (hU : FF79Sec34UFacts b a J A) :
    A ≤ CenS (U34 b a J A) :=
  le_cenS_of_le h.elemA.1.toIsMulCommutative hU.U_le_A

theorem sec34_ap_basic (hs : FF79Sec3 b J) (h : FF79Sec34In4 b J B A P D)
    (hU : FF79Sec34UFacts b a J A) (hoa : orderOf a = 3)
    (hK : IsLnq 2 2 2 (Lay (J ⊓ Cen a))) (haC : a ∈ CenS (U34 b a J A)) :
    cqβ (U34 b a J A) b hU.b_nor ^ 3 = 1 ∧ pPrimeCore 3 (CQ (U34 b a J A)) = ⊥ ∧
    (∃ S : Subgroup (CQ (U34 b a J A)), IsSylowOf 3 S ⊤ ∧ IsMulCommutative S) ∧
    cqImg (U34 b a J A) (U34 b a J A) ≤ Subgroup.center (CQ (U34 b a J A)) ∧
    Nat.card (cqImg (U34 b a J A) (U34 b a J A)) = 9 ∧
    (QuotientGroup.mk (⟨a, haC⟩ : ↥(CenS (U34 b a J A))) : CQ (U34 b a J A)) ∈
      cqImg (U34 b a J A) (U34 b a J A) ∧
    orderOf (QuotientGroup.mk (⟨a, haC⟩ : ↥(CenS (U34 b a J A))) : CQ (U34 b a J A)) = 3 ∧
    cqβ (U34 b a J A) b hU.b_nor (QuotientGroup.mk (⟨a, haC⟩ : ↥(CenS (U34 b a J A)))) =
      QuotientGroup.mk (⟨a, haC⟩ : ↥(CenS (U34 b a J A))) ∧
    (∃ A' : Subgroup (CQ (U34 b a J A)), IsElemAb 3 4 A' ∧
      cqImg (U34 b a J A) (U34 b a J A) ≤ A') := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : (pPrimeCore 3 ↥(CenS (U34 b a J A))).Normal := pPrimeCore_normal
  have hb3 : orderOf b = 3 := h.hyp.ord
  have hb3' : b ^ 3 = 1 := by rw [← hb3]; exact pow_orderOf_eq_one b
  have hU3 : IsPGroup 3 (U34 b a J A) :=
    haveI := hU.elemU.1; IsElementaryAbelian.isPGroup 3 _
  have hUcard : Nat.card (U34 b a J A) = 9 := by simpa using hU.elemU.2
  refine ⟨cqβ_pow_three hU.b_nor hb3', pPrimeCore_quotient_eq_bot Nat.prime_three, ?_,
    cqImg_le_center le_rfl, ?_, mk_mem_cqImg _ hU.a_mem, ?_, ?_, ?_⟩
  · obtain ⟨As, hAs⟩ := h.star
    have hS := sec34_As_syl hs h hU hAs
    have hAsC : As ≤ CenS (U34 b a J A) := hS.1
    have hSyl : IsSylowOf 3 (As.subgroupOf (CenS (U34 b a J A))) ⊤ := by
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      refine L41.isSylowOf_of_card_p le_top ?_
      rw [Subgroup.card_top, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAsC).toEquiv,
        L41.isSylowOf_card_p hS]
    refine ⟨(As.subgroupOf (CenS (U34 b a J A))).map
      (QuotientGroup.mk' (pPrimeCore 3 ↥(CenS (U34 b a J A)))),
      pp_isSylowOf_map _ (coprime_pPrimeCore _) hSyl, ?_⟩
    haveI : IsMulCommutative As := hAs.2.2.1
    infer_instance
  · rw [cqImg_card hU3 (sec34_UleC hU), hUcard]
  · have h1 : orderOf (⟨a, haC⟩ : ↥(CenS (U34 b a J A))) = 3 := by
      rw [← hoa, ← Subgroup.orderOf_mk a haC]
    have h2 : IsPGroup 3 (Subgroup.zpowers (⟨a, haC⟩ : ↥(CenS (U34 b a J A)))) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h1]; simp)
    rw [pp_orderOf_mk _ (coprime_pPrimeCore _) h2, h1]
  · exact cqβ_mk_of_cen hU.b_nor ⟨a, haC⟩ (sec34_a_cen_b hU)
  · refine ⟨cqImg (U34 b a J A) A, ⟨cqImg_elemAb h.elemA.1 (sec34_AleC h hU), ?_⟩,
      ?_⟩
    · rw [cqImg_card (haveI := h.elemA.1; IsElementaryAbelian.isPGroup 3 _) (sec34_AleC h hU)]
      simpa using h.elemA.2
    · rintro y hy
      obtain ⟨c, hc, rfl⟩ := mem_cqImg.mp hy
      exact mk_mem_cqImg c (hU.U_le_A hc)

end Basic

end CFSG.RankThree.PartTwo.Sec21.FF79.H4
