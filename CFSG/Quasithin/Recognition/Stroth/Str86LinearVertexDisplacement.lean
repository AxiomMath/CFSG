module

public import CFSG.Quasithin.Recognition.Stroth.Str86LinearVertex
public import CFSG.Quasithin.Recognition.Stroth.BenderChief
public import CFSG.Quasithin.Vol2.Ch3zTrans

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]
variable {H U L N : Subgroup G} {m : ℕ}

noncomputable def l2SectionAction (hstep : IsChiefStep H U L N) (hUH : U ≤ H)
    [(L.subgroupOf N).Normal] : ↥H →* MulAut (SectionW N L) := by
  have hHL : H ≤ Subgroup.normalizer (L : Set G) := D14.le_normalizer_of_isNormalIn hstep.2.1
  have hHN : H ≤ Subgroup.normalizer (N : Set G) := D14.le_normalizer_of_isNormalIn hstep.1
  have hNL : N ≤ Subgroup.normalizer (L : Set G) := (hstep.1.1.trans hUH).trans hHL
  haveI : (L.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hstep.2.2.1.le).mpr hNL
  exact CFSG.Quasithin.Vol2.Ch11.SecD.quotAct hHN hHL

theorem l2SectionAction_mk (hstep : IsChiefStep H U L N) (hUH : U ≤ H)
    [(L.subgroupOf N).Normal] (h : ↥H) (u : ↥N) :
    l2SectionAction hstep hUH h (QuotientGroup.mk u) =
      QuotientGroup.mk (conjAct N ⟨(h : G), D14.le_normalizer_of_isNormalIn hstep.1 h.2⟩ u) := by
  have hHL : H ≤ Subgroup.normalizer (L : Set G) := D14.le_normalizer_of_isNormalIn hstep.2.1
  have hHN : H ≤ Subgroup.normalizer (N : Set G) := D14.le_normalizer_of_isNormalIn hstep.1
  have hNL : N ≤ Subgroup.normalizer (L : Set G) := (hstep.1.1.trans hUH).trans hHL
  haveI : (L.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hstep.2.2.1.le).mpr hNL
  exact CFSG.Quasithin.Vol2.Ch11.SecD.quotAct_mk hHN hHL h u

theorem chiefQuotEquiv_l2SectionAction (hstep : IsChiefStep H U L N) (hUH : U ≤ H)
    [(L.subgroupOf N).Normal]
    (hE : IsElemAbelian 2 (Ch3z.chiefMod L N)) (h : ↥H) (w : SectionW N L) :
    letI : CommGroup (Ch3z.chiefMod L N) := l2ChiefSectionCommGroup hE
    Ch3z.chiefQuotEquiv (hNL := (hstep.1.1.trans hUH).trans
        (D14.le_normalizer_of_isNormalIn hstep.2.1)) (l2SectionAction hstep hUH h w) =
      l2ChiefSectionAction hstep hE h (Ch3z.chiefQuotEquiv (hNL := (hstep.1.1.trans hUH).trans
        (D14.le_normalizer_of_isNormalIn hstep.2.1)) w) := by
  letI : CommGroup (Ch3z.chiefMod L N) := l2ChiefSectionCommGroup hE
  have hHL : H ≤ Subgroup.normalizer (L : Set G) := D14.le_normalizer_of_isNormalIn hstep.2.1
  have hHN : H ≤ Subgroup.normalizer (N : Set G) := D14.le_normalizer_of_isNormalIn hstep.1
  have hNL : N ≤ Subgroup.normalizer (L : Set G) := (hstep.1.1.trans hUH).trans hHL
  haveI : (L.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hstep.2.2.1.le).mpr hNL
  induction w using QuotientGroup.induction_on with
  | H u =>
    rw [l2SectionAction_mk, Ch3z.chiefQuotEquiv_mk, Ch3z.chiefQuotEquiv_mk,
      l2ChiefSectionAction_eq_chiefPsi]
    refine (Ch3z.chiefPsi_iota hHL hHN hNL h u ?_).symm

theorem l2ChiefSectionRep_pow_le_relIndex_centralizerMod (hm2 : 2 ≤ m)
    (hL2 : IsL2Quot m (oTwoQuot ↥H))
    (hU : IsPGroup 2 U) (hUH : U ≤ H)
    (hstep : IsChiefStep H U L N) (hnc : ¬ IsCentralStep H L N)
    {t : G} (htH : t ∈ H) (ht : t * t ∈ pCoreOf 2 H) (htO : t ∉ pCoreOf 2 H) :
    letI : CommGroup (Ch3z.chiefMod L N) :=
      l2ChiefSectionCommGroup (isElemAbelian_chiefMod hstep hUH hU)
    letI : (L.subgroupOf N).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hstep.2.2.1.le).mpr
        ((hstep.1.1.trans hUH).trans (D14.le_normalizer_of_isNormalIn hstep.2.1))
    2 ^ m ≤ (centralizerMod L N (Subgroup.zpowers t)).relIndex N := by
  classical
  haveI : Fintype (GaloisField 2 m) := Fintype.ofFinite _
  let hE := isElemAbelian_chiefMod hstep hUH hU
  letI : CommGroup (Ch3z.chiefMod L N) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod L N)) := l2ChiefSectionModule hE
  have hHL : H ≤ Subgroup.normalizer (L : Set G) := D14.le_normalizer_of_isNormalIn hstep.2.1
  have hHN : H ≤ Subgroup.normalizer (N : Set G) := D14.le_normalizer_of_isNormalIn hstep.1
  have hNL : N ≤ Subgroup.normalizer (L : Set G) := (hstep.1.1.trans hUH).trans hHL
  haveI : (L.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hstep.2.2.1.le).mpr hNL
  obtain ⟨e₀⟩ := hL2
  let e : oTwoQuot ↥H ≃* SL(2, GaloisField 2 m) :=
    e₀.trans (CFSG.CGT.Timmesfeld75.pslMulEquivSL (F := GaloisField 2 m))
  let a : SL(2, GaloisField 2 m) := e (QuotientGroup.mk ⟨t, htH⟩)
  let ρ := l2ChiefSectionRep hstep hUH hE e
  haveI : Fact ρ.IsIrreducible := ⟨l2ChiefSectionRep_irreducible hstep hUH hE e⟩
  have hnt : ∃ g, ρ g ≠ 1 := l2ChiefSectionRep_nontrivial hstep hUH hE e hnc
  have hm : 1 ≤ m := by omega
  have hF : Fintype.card (GaloisField 2 m) = 2 ^ m := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 2 m (by omega)]
  have hsqfix : Nat.card (CFSG.RankThree.FFModules.fixSub ρ
      (Subgroup.zpowers a)) ^ 2 = Nat.card (Additive (Ch3z.chiefMod L N)) := by
    exact l2ChiefSectionRep_sq_card_fixSub hm2 hstep hUH hE e hnc htH ht htO
  have hWle : (2 ^ m) ^ 2 ≤ Nat.card (Additive (Ch3z.chiefMod L N)) :=
    CFSG.Timmesfeld.Bridge.RootMany.sq_le_card_of_irreducible hm hF ρ hnt
  have hfixle : 2 ^ m ≤ Nat.card (CFSG.RankThree.FFModules.fixSub ρ
      (Subgroup.zpowers a)) := by
    rw [← hsqfix] at hWle
    exact (Nat.pow_le_pow_iff_left (by norm_num : 2 ≠ 0)).mp hWle
  have hfixcard : Nat.card (fixV (Subgroup.zpowers (l2ChiefSectionAction hstep hE ⟨t, htH⟩))) =
      Nat.card (CFSG.RankThree.FFModules.fixSub ρ (Subgroup.zpowers a)) := by
    rw [show ρ = (CFSG.RankThree.FFModules.autRep (Ch3z.chiefMod L N)).comp
      (l2ChiefSectionSL2Action hstep hUH hE e) from rfl]
    rw [CFSG.RankThree.FFModules.card_fixSub_autRep_comp
      (E := Ch3z.chiefMod L N) (ι := l2ChiefSectionSL2Action hstep hUH hE e)
      (B := Subgroup.zpowers a)]
    congr 1
    rw [MonoidHom.map_zpowers]
    congr 1
    rw [l2ChiefSectionSL2Action_apply, MulEquiv.symm_apply_apply, l2ChiefSectionQuotAction_mk]
  let K : Subgroup (SectionW N L) :=
    (fixV (Subgroup.zpowers (l2ChiefSectionAction hstep hE ⟨t, htH⟩))).comap
      (Ch3z.chiefQuotEquiv hNL).toMonoidHom
  have hKmem : ∀ u : ↥N, QuotientGroup.mk u ∈ K ↔
      l2SectionAction hstep hUH ⟨t, htH⟩ (QuotientGroup.mk u) = QuotientGroup.mk u := by
    intro u
    constructor
    · intro hu
      have hu' : l2ChiefSectionAction hstep hE ⟨t, htH⟩
          (Ch3z.chiefQuotEquiv hNL (QuotientGroup.mk u)) =
          Ch3z.chiefQuotEquiv hNL (QuotientGroup.mk u) :=
        mem_fixV_zpowers_iff_apply.mp hu
      apply (Ch3z.chiefQuotEquiv hNL).injective
      rw [chiefQuotEquiv_l2SectionAction (hE := hE), hu']
    · intro hu
      have h2 := congrArg (Ch3z.chiefQuotEquiv hNL) hu
      rw [chiefQuotEquiv_l2SectionAction (hE := hE)] at h2
      exact mem_fixV_zpowers_iff_apply.mpr h2
  have hact : ∀ u : ↥N, l2SectionAction hstep hUH ⟨t, htH⟩ (QuotientGroup.mk u) =
      QuotientGroup.mk (conjAct N ⟨t, hHN htH⟩ u) :=
    fun u => l2SectionAction_mk hstep hUH ⟨t, htH⟩ u
  have hidx := relIndex_centralizerMod_eq_index_of_fixedSection hHN hHL htH hNL
    (l2SectionAction hstep hUH ⟨t, htH⟩) K hKmem hact
  have hKindex : K.index =
      (fixV (Subgroup.zpowers (l2ChiefSectionAction hstep hE ⟨t, htH⟩))).index :=
    Subgroup.index_comap_of_surjective _ (Ch3z.chiefQuotEquiv hNL).surjective
  have hcardfix : Nat.card (fixV (Subgroup.zpowers (l2ChiefSectionAction hstep hE ⟨t, htH⟩))) *
      (fixV (Subgroup.zpowers (l2ChiefSectionAction hstep hE ⟨t, htH⟩))).index =
      Nat.card (Ch3z.chiefMod L N) :=
    Subgroup.card_mul_index _
  have hW : Nat.card (fixV (Subgroup.zpowers (l2ChiefSectionAction hstep hE ⟨t, htH⟩))) ^ 2 =
      Nat.card (Ch3z.chiefMod L N) := by
    rw [hfixcard]
    exact hsqfix.trans (Nat.card_congr Additive.ofMul).symm
  have hfixpos : 0 <
      Nat.card (fixV (Subgroup.zpowers (l2ChiefSectionAction hstep hE ⟨t, htH⟩))) := by
    by_contra h0
    have h0' : Nat.card (fixV (Subgroup.zpowers (l2ChiefSectionAction hstep hE ⟨t, htH⟩))) = 0 :=
      Nat.eq_zero_of_not_pos h0
    rw [h0', zero_pow (by norm_num)] at hW
    exact (Nat.card_pos (α := Ch3z.chiefMod L N)).ne' hW.symm
  have hidxfix : (fixV (Subgroup.zpowers (l2ChiefSectionAction hstep hE ⟨t, htH⟩))).index =
      Nat.card (fixV (Subgroup.zpowers (l2ChiefSectionAction hstep hE ⟨t, htH⟩))) := by
    have h2 : Nat.card (fixV (Subgroup.zpowers (l2ChiefSectionAction hstep hE ⟨t, htH⟩))) *
        (fixV (Subgroup.zpowers (l2ChiefSectionAction hstep hE ⟨t, htH⟩))).index =
        Nat.card (fixV (Subgroup.zpowers (l2ChiefSectionAction hstep hE ⟨t, htH⟩))) *
        Nat.card (fixV (Subgroup.zpowers (l2ChiefSectionAction hstep hE ⟨t, htH⟩))) := by
      rw [hcardfix, ← hW, pow_two]
    exact Nat.eq_of_mul_eq_mul_left hfixpos h2
  rw [hidx, hKindex, hidxfix, hfixcard]
  exact hfixle

end CFSG.Quasithin.Stroth
