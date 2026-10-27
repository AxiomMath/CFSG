module

public import CFSG.RankThree.GF2n.Stroth80.Sec4Model
public import CFSG.RankThree.GF2n.Stroth80.Sec12Cases
public import CFSG.RankThree.GF2n.Stroth80.Stroth1980Below
public import CFSG.RankThree.GF2n.Smith81.ESetup
public import CFSG.RankThree.GF2n.Smith81.Lanes
public import CFSG.RankThree.GF2n.Smith81.Sec2Defs
public import CFSG.RankThree.GF2n.Smith81.TiFusion
public import CFSG.RankThree.GF2n.Stroth80.Sec12CaseVIEquiv

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

variable {G : Type} [Group G]

section SubData

abbrev SubCfgGroup (M Q Z : Subgroup G) [(Q.subgroupOf (H0 M Z)).Normal] : Type :=
  ↥(H0 M Z) ⧸ Q.subgroupOf (H0 M Z)

variable (M Q Z N : Subgroup G) [(Q.subgroupOf (H0 M Z)).Normal]

abbrev SubCfgQ : Subgroup (SubCfgGroup M Q Z) := bar (H0 M Z) Q N

abbrev SubCfgZ : Subgroup (SubCfgGroup M Q Z) := cen (SubCfgQ M Q Z N)

abbrev SubCfgM : Subgroup (SubCfgGroup M Q Z) :=
  Subgroup.normalizer ((SubCfgZ M Q Z N : Subgroup _) : Set _)

end SubData

section Nt

variable [Finite G] {M Q Z B : Subgroup G}

theorem Q_le_Nt (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) : Q ≤ Nt M (LB M Q B) t := by
  have hRM : Rt M (LB M Q B) t ≤ M := Rt_le_M hc.LB_le_M t
  have hQR : Q ≤ Rt M (LB M Q B) t := hc.Q_le_Rt ht
  haveI : (Q.subgroupOf (Rt M (LB M Q B) t)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer fun x hx => hc.hyp.Q_normal.2 (hRM hx)
  have hp : IsPGroup 2 (Q.subgroupOf (Rt M (LB M Q B) t)) :=
    (isPGroup_Q' hc.hyp).comap_of_injective _ (Subgroup.subtype_injective _)
  have hle : Q.subgroupOf (Rt M (LB M Q B) t) ≤ CFSG.pCore 2 ↥(Rt M (LB M Q B) t) :=
    le_sSup ⟨inferInstance, hp⟩
  calc Q = (Q.subgroupOf (Rt M (LB M Q B) t)).map (Rt M (LB M Q B) t).subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hQR).symm
    _ ≤ Nt M (LB M Q B) t := Subgroup.map_mono hle

theorem Nt_le_H0 (hc : Ctx M Q Z B) (t : G) : Nt M (LB M Q B) t ≤ H0 M Z :=
  (Subgroup.map_subtype_le _).trans ((Rt_le_Lgen M (LB M Q B) t).trans (Lgen_le_H0 hc))

theorem card_bar_Nt (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B)
    [(Q.subgroupOf (H0 M Z)).Normal] :
    Nat.card (bar (H0 M Z) Q (Nt M (LB M Q B) t)) * Nat.card Q = Nat.card (Nt M (LB M Q B) t) :=
  bar_card_mul_card_of_le (M := H0 M Z) (Q_le_Nt hc ht) (Nt_le_H0 hc t)

end Nt

section Recursion

variable [Finite G]

theorem card_H0_quot_lt [Finite G] {M Q Z : Subgroup G}
    (H : StrothHyp M Q Z) [(Q.subgroupOf (H0 M Z)).Normal] :
    Nat.card (↥(H0 M Z) ⧸ Q.subgroupOf (H0 M Z)) < Nat.card G := by
  have hQM : Q ≤ M := by
    rw [H.hQ]
    exact Subgroup.map_subtype_le _
  have hZQ : Z ≤ Q := by
    rw [H.hZ]
    exact Subgroup.map_subtype_le _
  have hZC : Z ≤ Subgroup.centralizer (Q : Set G) := by
    rw [H.hZ, CFSG.RankThree.GF2n.Stroth80.cen_eq]
    exact inf_le_right
  have hQH : Q ≤ H0 M Z := fun x hx =>
    ⟨hQM hx, Subgroup.mem_centralizer_iff.mpr fun z hz =>
      (Subgroup.mem_centralizer_iff.mp (hZC hz) x hx).symm⟩
  have hdecomp := Subgroup.card_eq_card_quotient_mul_card_subgroup (Q.subgroupOf (H0 M Z))
  have hsub : Nat.card (Q.subgroupOf (H0 M Z)) = Nat.card Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQH).toEquiv
  rw [hsub] at hdecomp
  have hZcard : Nat.card Z ≤ Nat.card Q := Subgroup.card_le_of_le hZQ
  have hH0 : Nat.card (H0 M Z) ≤ Nat.card G := Subgroup.card_le_card_group (H0 M Z)
  have hN : 0 < Nat.card G := Nat.card_pos
  have h4 : 4 ≤ Nat.card Q := le_trans H.q4 hZcard
  have hmul := Nat.mul_le_mul (le_refl (Nat.card (↥(H0 M Z) ⧸ Q.subgroupOf (H0 M Z)))) h4
  omega

theorem exists_smithConclusion_of_subConfig {M Q Z N : Subgroup G} (H : StrothHyp M Q Z)
    (hb : Smith1981Below (Nat.card G)) (hS : Stroth1980Below (Nat.card G))
    (h : SubConfig M Q Z N) :
    ∃ hN : (Q.subgroupOf (H0 M Z)).Normal,
      haveI := hN
      ∃ B' : Subgroup (SubCfgGroup M Q Z),
        (∃ g, B' = conjSubgroup g (SubCfgZ M Q Z N)) ∧ B' ≤ SubCfgQ M Q Z N ∧
        B' ≠ SubCfgZ M Q Z N ∧
        StrothConclusion (SubCfgM M Q Z N) (SubCfgQ M Q Z N) (SubCfgZ M Q Z N) B' ∧
        SmithConclusion (SubCfgM M Q Z N) (SubCfgQ M Q Z N) (SubCfgZ M Q Z N) B' := by
  obtain ⟨hN, hsub⟩ := h
  refine ⟨hN, ?_⟩
  haveI := hN
  obtain ⟨B', hB'⟩ := exists_ctx_of_strothHyp hsub
  have hc := hS _ (card_H0_quot_lt H) _ _ _ hsub B' hB'.conj hB'.le hB'.ne
  exact ⟨B', hB'.conj, hB'.le, hB'.ne, hc,
    hb.1 _ (card_H0_quot_lt H) _ _ _ hsub B' hB'.conj hB'.le hB'.ne hc⟩

end Recursion

@[expose] def SubConfigE4Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (t : G) (N : Subgroup G),
    N = Nt M (LB M Q B) t → Smith1981Below (Nat.card G) → SmithECfg M Q Z B →
    CaseE4 M Q Z B t → ∀ [(Q.subgroupOf (H0 M Z)).Normal],
      StrothHyp (SubCfgM M Q Z N) (SubCfgQ M Q Z N) (SubCfgZ M Q Z N) →
      ∀ B' : Subgroup (SubCfgGroup M Q Z), (∃ g, B' = conjSubgroup g (SubCfgZ M Q Z N)) →
        B' ≤ SubCfgQ M Q Z N → B' ≠ SubCfgZ M Q Z N →
        StrothConclusion (SubCfgM M Q Z N) (SubCfgQ M Q Z N) (SubCfgZ M Q Z N) B' →
        ∃ t' : SubCfgGroup M Q Z,
          CtxD4 (SubCfgM M Q Z N) (SubCfgQ M Q Z N) (SubCfgZ M Q Z N) B' t' ∧
            CaseE2Plus (SubCfgM M Q Z N) (SubCfgQ M Q Z N) (SubCfgZ M Q Z N) B' t' 4

@[expose] def SubConfigE5Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (t : G) (N : Subgroup G),
    N = Nt M (LB M Q B) t → Smith1981Below (Nat.card G) → SmithECfg M Q Z B →
    CaseE5 M Q Z B t → ∀ [(Q.subgroupOf (H0 M Z)).Normal],
      StrothHyp (SubCfgM M Q Z N) (SubCfgQ M Q Z N) (SubCfgZ M Q Z N) →
      ∀ B' : Subgroup (SubCfgGroup M Q Z), (∃ g, B' = conjSubgroup g (SubCfgZ M Q Z N)) →
        B' ≤ SubCfgQ M Q Z N → B' ≠ SubCfgZ M Q Z N →
        StrothConclusion (SubCfgM M Q Z N) (SubCfgQ M Q Z N) (SubCfgZ M Q Z N) B' →
        ∃ t' : SubCfgGroup M Q Z,
          CtxD4 (SubCfgM M Q Z N) (SubCfgQ M Q Z N) (SubCfgZ M Q Z N) B' t' ∧
            CaseE4 (SubCfgM M Q Z N) (SubCfgQ M Q Z N) (SubCfgZ M Q Z N) B' t'

section Reduction

variable [Finite G]

theorem lieModel_of_caseE4_recursion {M Q Z B : Subgroup G} {t : G}
    (hb : Smith1981Below (Nat.card G)) (hS : Stroth1980Below (Nat.card G))
    (hX : SubConfigE4Statement)
    (hc : SmithECfg M Q Z B) (hD : CtxD4 M Q Z B t) (h4 : CaseE4 M Q Z B t) :
    ∃ hN : (Q.subgroupOf (H0 M Z)).Normal,
      haveI := hN
      ∃ f : ℕ, Nat.card Z = 2 ^ f ∧
        CFSG.Blueprint.LieModel (FStar (SubCfgGroup M Q Z)) .POmegaPlus 6 2 f := by
  obtain ⟨hN, B', hg, hle, hne, hStr, hSm⟩ :=
    exists_smithConclusion_of_subConfig hc.ctx.hyp hb hS h4.2.2.2
  refine ⟨hN, ?_⟩
  haveI := hN
  obtain ⟨hN', hsub⟩ := h4.2.2.2
  obtain ⟨t', ht', hE2⟩ := hX G M Q Z B t _ rfl hb hc h4 hsub B' hg hle hne hStr
  obtain ⟨f, hf, hL⟩ := ((smithConclusion_iff_lanes _ _ _ _).mp hSm).2.1.2.2.1 t' 4 ht' hE2
  refine ⟨f, ?_, hL⟩
  have hbar := card_bar_Nt hc.ctx hD.2.1
  have hq : Nat.card (bar (H0 M Z) Q (Nt M (LB M Q B) t)) = Nat.card Z ^ 17 := by
    rw [h4.2.1] at hbar
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (by rw [hbar, mul_comm])
  have hZ' : Nat.card (SubCfgZ M Q Z (Nt M (LB M Q B) t)) = Nat.card Z :=
    Nat.pow_left_injective (n := 17) (by norm_num) (hE2.2.1.symm.trans hq)
  rw [← hZ']
  exact hf

theorem lieModel_of_caseE5_recursion {M Q Z B : Subgroup G} {t : G}
    (hb : Smith1981Below (Nat.card G)) (hS : Stroth1980Below (Nat.card G))
    (hX : SubConfigE5Statement)
    (hc : SmithECfg M Q Z B) (hD : CtxD4 M Q Z B t) (h5 : CaseE5 M Q Z B t) :
    ∃ hN : (Q.subgroupOf (H0 M Z)).Normal,
      haveI := hN
      ∃ f : ℕ, Nat.card Z = 2 ^ f ∧
        CFSG.Blueprint.LieModel (FStar (SubCfgGroup M Q Z)) .E7 0 2 f := by
  obtain ⟨hN, B', hg, hle, hne, hStr, hSm⟩ :=
    exists_smithConclusion_of_subConfig hc.ctx.hyp hb hS h5.2.2.2
  refine ⟨hN, ?_⟩
  haveI := hN
  obtain ⟨hN', hsub⟩ := h5.2.2.2
  obtain ⟨t', ht', hE4⟩ := hX G M Q Z B t _ rfl hb hc h5 hsub B' hg hle hne hStr
  obtain ⟨f, hf, hL⟩ := ((smithConclusion_iff_lanes _ _ _ _).mp hSm).2.2.1.2.2.1 t' ht' hE4
  refine ⟨f, ?_, hL⟩
  have hbar := card_bar_Nt hc.ctx hD.2.1
  have hq : Nat.card (bar (H0 M Z) Q (Nt M (LB M Q B) t)) = Nat.card Z ^ 33 := by
    rw [h5.2.1] at hbar
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (by rw [hbar, mul_comm])
  have hZ' : Nat.card (SubCfgZ M Q Z (Nt M (LB M Q B) t)) = Nat.card Z :=
    Nat.pow_left_injective (n := 33) (by norm_num) (hE4.1.symm.trans hq)
  rw [← hZ']
  exact hf

end Reduction

end CFSG.RankThree.GF2n.Smith81
