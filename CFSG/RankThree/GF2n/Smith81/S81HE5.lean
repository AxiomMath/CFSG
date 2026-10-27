module

public import CFSG.RankThree.GF2n.Smith81.S81HE7Bound
public import CFSG.RankThree.GF2n.Smith81.SubConfigHolds
public import CFSG.RankThree.GF2n.Smith81.S81WTacitFree45
public import CFSG.RankThree.GF2n.Smith81.ETables
public import CFSG.RankThree.GF2n.Smith81.S81G2E7
public import CFSG.RankThree.GF2n.Smith81.InspE45
public import CFSG.RankThree.GF2n.Stroth80.Sec12Certified
public import CFSG.RankThree.GF2n.Stroth80.Sec34ClassicalProof
public import CFSG.GroupTheory.Fitting.SimpleNormal

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.Blueprint CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n
  CFSG.RankThree.GF2n.Stroth80

section Reduction

theorem lgenBar_eq_fstar_E5_of (h34 : Stroth34Statement) (hGen : StrothGenByBStatement)
    (hSt : Stroth1980Rel) {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
    (hb : Smith1981Below (Nat.card G)) (hc : SmithECfg M Q Z B) (h5 : InCaseE5 M Q Z B)
    [(Q.subgroupOf (H0 M Z)).Normal] :
    bar (H0 M Z) Q (Lgen M (LB M Q B)) = generalizedFitting (SubCfgGroup M Q Z) := by
  have hT := eTacitE5_of_genByB hGen G M Q Z B hb hc h5
  obtain ⟨t, hD, hE5⟩ := h5
  obtain ⟨hN, f, hf, hLF⟩ :=
    lieModel_of_caseE5_recursion hb (hSt _ hb.1) SubCfg.subConfigE5Statement_holds hc hD hE5
  have hS : IsSimpleGroup (FStar (SubCfgGroup M Q Z)) := Timmesfeld.isSimpleGroup_of_lieModel hLF
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · have := hc.ctx.hyp.q4
      rw [hf] at this
      norm_num at this
    · exact h
  have hFv := Insp.factorization_two_card_of_lieModel hf1
    (by simp [Insp.TimmesfeldTag] : Insp.TimmesfeldTag .E7 0 f) hLF
  have hsyl : Smith219Arith.sylowExp .E7 0 = 63 := rfl
  rw [hsyl] at hFv
  have h4F : 4 ∣ Nat.card (FStar (SubCfgGroup M Q Z)) := by
    have h := Nat.ordProj_dvd (Nat.card (FStar (SubCfgGroup M Q Z))) 2
    rw [hFv] at h
    exact (pow_dvd_pow 2 (by nlinarith : 2 ≤ f * 63)).trans h
  have hC := Insp.centralizer_fstar_eq_bot hS h4F
  haveI : (generalizedFitting (SubCfgGroup M Q Z)).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := SubCfgGroup M Q Z)).2
  obtain ⟨K, _, _, _, hK, ⟨g⟩⟩ := E7Model.exists_equiv_EGrp_of_lieModel hLF
  set e := g.trans (HardMathSupport.Cooperstein.Coordinator.Survivors.e7Equiv (K := K))
  have hLH := Br37.Lgen_LB_le_H0 hc.ctx
  have hw : Width Q Z 28 := by simpa [Width] using hE5.1
  have hLBm : ∀ m ∈ M, bar (H0 M Z) Q (conjSubgroup m (LB M Q B)) ≤
      generalizedFitting (SubCfgGroup M Q Z) := by
    intro m hm
    have hB' := hc.ctx.conj_of_mem hm
    have hLe : LB M Q (conjSubgroup m B) ≤ H0 M Z := by
      rw [hc.ctx.LB_conj hm]
      exact (Br37.conj_le_Lgen hm).trans hLH
    rw [← hc.ctx.LB_conj hm]
    obtain ⟨hno, hgen⟩ := hT _ hB'
    have hcard := (card_LB_of_ctx h34 hB' hw (by norm_num) hno hgen).1
    have hbar : Nat.card (bar (H0 M Z) Q (LB M Q (conjSubgroup m B))) * Nat.card Q =
        Nat.card (LB M Q (conjSubgroup m B)) := bar_card_mul_card_of_le le_sup_left hLe
    refine le_of_card_ge_E7 hC hK e ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
        Subgroup.coe_pow]
      exact hB'.sq_mem_Q_of_mem_LB (Subgroup.mem_subgroupOf.1 hx)
    · have h1 : Nat.card (bar (H0 M Z) Q (LB M Q (conjSubgroup m B))) = Nat.card Z ^ 27 := by
        rw [hcard] at hbar
        exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (by rw [hbar, mul_comm])
      rw [h1, hf, ← pow_mul, mul_comm]
  have hP : Lgen M (LB M Q B) ≤ ((generalizedFitting (SubCfgGroup M Q Z)).comap
      (QuotientGroup.mk' (Q.subgroupOf (H0 M Z)))).map (H0 M Z).subtype := by
    refine Br37.Lgen_le_of fun m hm x hx => ?_
    have hxH : x ∈ H0 M Z := hLH (Br37.conj_le_Lgen hm hx)
    exact ⟨⟨x, hxH⟩, hLBm m hm ⟨⟨x, hxH⟩, hx, rfl⟩, rfl⟩
  have hle : bar (H0 M Z) Q (Lgen M (LB M Q B)) ≤ generalizedFitting (SubCfgGroup M Q Z) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hP (Subgroup.mem_subgroupOf.1 hx)
    rw [show x = y from Subtype.ext hyx.symm]
    exact hy
  have hNorm : (bar (H0 M Z) Q (Lgen M (LB M Q B))).Normal := by
    have hn : ((Lgen M (LB M Q B)).subgroupOf (H0 M Z)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hLH).2
        ((inf_le_left : H0 M Z ≤ M).trans (Lgen_normalizes M _))
    exact hn.map _ (QuotientGroup.mk'_surjective _)
  have hne : bar (H0 M Z) Q (Lgen M (LB M Q B)) ≠ ⊥ := by
    intro h
    have htL : t ∈ Lgen M (LB M Q B) := le_Lgen_self M _ hD.2.1
    have hmem : QuotientGroup.mk' (Q.subgroupOf (H0 M Z)) ⟨t, hLH htL⟩ ∈
        bar (H0 M Z) Q (Lgen M (LB M Q B)) := ⟨⟨t, hLH htL⟩, htL, rfl⟩
    rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at hmem
    exact hD.2.2.1 hmem
  exact le_antisymm hle (GroupTheory.generalizedFitting_le_of_normal hS hNorm hne)

theorem exists_lgen_hom_EAut_E5_of (h34 : Stroth34Statement) (hGen : StrothGenByBStatement)
    (hSt : Stroth1980Rel) {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
    (hb : Smith1981Below (Nat.card G)) (hc : SmithECfg M Q Z B) (h5 : InCaseE5 M Q Z B) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = Nat.card Z ∧
      ∃ θ : Lgen M (LB M Q B) →* E7Model.EAut K,
        Function.Surjective θ ∧ ∀ s, θ s = 1 ↔ (s : G) ∈ Q := by
  obtain ⟨t, hD, hE5⟩ := h5
  obtain ⟨hN, f, hf, hLF⟩ :=
    lieModel_of_caseE5_recursion hb (hSt _ hb.1) SubCfg.subConfigE5Statement_holds hc hD hE5
  haveI := hN
  have hEq := lgenBar_eq_fstar_E5_of h34 hGen hSt hb hc ⟨t, hD, hE5⟩
  obtain ⟨K, _, _, _, hK, ⟨g⟩⟩ := E7Model.exists_equiv_EGrp_of_lieModel hLF
  have hLH := Br37.Lgen_LB_le_H0 hc.ctx
  set ρ : ↥(Lgen M (LB M Q B)) →* SubCfgGroup M Q Z :=
    (QuotientGroup.mk' (Q.subgroupOf (H0 M Z))).comp (Subgroup.inclusion hLH) with hρ
  have hρF : ∀ s, ρ s ∈ generalizedFitting (SubCfgGroup M Q Z) := fun s => by
    rw [← hEq]
    exact ⟨Subgroup.inclusion hLH s, s.2, rfl⟩
  set ρ' := ρ.codRestrict _ hρF
  refine ⟨K, inferInstance, inferInstance, inferInstance, hK.trans hf.symm,
    (E7Model.eGrpEquivEAut K).toMonoidHom.comp (g.toMonoidHom.comp ρ'), ?_, ?_⟩
  · intro y
    obtain ⟨x, hx⟩ := (E7Model.eGrpEquivEAut K).surjective y
    obtain ⟨u, rfl⟩ := g.surjective x
    have hu : (u : SubCfgGroup M Q Z) ∈ bar (H0 M Z) Q (Lgen M (LB M Q B)) := by
      rw [hEq]
      exact u.2
    obtain ⟨v, hv, hvu⟩ := hu
    refine ⟨⟨v, hv⟩, ?_⟩
    rw [← hx]
    change (E7Model.eGrpEquivEAut K) (g (ρ' ⟨v, hv⟩)) = _
    congr 2
    exact Subtype.ext hvu
  · intro s
    change (E7Model.eGrpEquivEAut K) (g (ρ' s)) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff, ← Subtype.coe_inj]
    change ρ s = 1 ↔ _
    rw [hρ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf]
    rfl

end Reduction

section Certified

theorem exists_lgen_hom_EAut_E5 (hSt : Stroth1980Rel)
    {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G} (hb : Smith1981Below (Nat.card G))
    (hc : SmithECfg M Q Z B) (h5 : InCaseE5 M Q Z B) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = Nat.card Z ∧
      ∃ θ : Lgen M (LB M Q B) →* E7Model.EAut K,
        Function.Surjective θ ∧ ∀ s, θ s = 1 ↔ (s : G) ∈ Q :=
  exists_lgen_hom_EAut_E5_of stroth34Statement_unconditional strothGenByBStatement_certified hSt
    hb hc h5

end Certified

end CFSG.RankThree.GF2n.Smith81
