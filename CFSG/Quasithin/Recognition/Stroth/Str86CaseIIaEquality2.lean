module

public import CFSG.Quasithin.Recognition.GoldschmidtF112RLeaves
public import CFSG.Quasithin.Recognition.Stroth.Str86LinearVertexDisplacement

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G]

private theorem str86_card_chiefMod {L N : Subgroup G}
    (hNL : N ≤ Subgroup.normalizer (L : Set G)) :
    Nat.card ↥(Ch3z.chiefMod L N) = L.relIndex N := by
  have hker : (Ch3z.chiefIota hNL).ker = L.subgroupOf N := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact Ch3z.chiefIota_eq_one_iff hNL x
  have hmain := Subgroup.card_ker_mul_card_range (Ch3z.chiefIota hNL)
  rw [hker, MonoidHom.range_eq_top.mpr (Ch3z.chiefIota_surjective hNL), Subgroup.card_top]
    at hmain
  have hcard : Nat.card ↥(L.subgroupOf N) = Nat.card ↥(L ⊓ N) :=
    Nat.card_congr
      { toFun := fun x => ⟨(x.1 : G), x.2, x.1.2⟩
        invFun := fun y => ⟨⟨y.1, y.2.2⟩, y.2.1⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
  rw [hcard, mul_comm] at hmain
  rw [← Subgroup.relIndex_mul_card L N] at hmain
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hmain

theorem str86_chiefSection_sq_relIndex {H U L N : Subgroup G} {m : ℕ}
    (hm2 : 2 ≤ m) (hL2 : IsL2Quot m (oTwoQuot ↥H))
    (hU : IsPGroup 2 U) (hUH : U ≤ H)
    (hstep : IsChiefStep H U L N) (hnc : ¬ IsCentralStep H L N)
    {t : G} (htH : t ∈ H) (ht : t * t ∈ pCoreOf 2 H) (htO : t ∉ pCoreOf 2 H) :
    (centralizerMod L N (Subgroup.zpowers t)).relIndex N ^ 2 = L.relIndex N := by
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
  have hsqfix : Nat.card (CFSG.RankThree.FFModules.fixSub ρ
      (Subgroup.zpowers a)) ^ 2 = Nat.card (Additive (Ch3z.chiefMod L N)) :=
    l2ChiefSectionRep_sq_card_fixSub hm2 hstep hUH hE e hnc htH ht htO
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
  have hD : (centralizerMod L N (Subgroup.zpowers t)).relIndex N =
      Nat.card (fixV (Subgroup.zpowers (l2ChiefSectionAction hstep hE ⟨t, htH⟩))) := by
    rw [hidx, hKindex, hidxfix]
  rw [hD, hW, str86_card_chiefMod hNL]

end CFSG.Quasithin.Stroth

end
