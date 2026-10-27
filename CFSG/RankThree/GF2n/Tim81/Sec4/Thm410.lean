module

public import CFSG.RankThree.GF2n.Tim81.Sec4.Subpairs
public import CFSG.RankThree.GF2n.Tim81.Sec4.KIInspRankThree
public import CFSG.RankThree.GF2n.Tim81.Sec4.KIInspPSL
public import CFSG.RankThree.GF2n.Tim81.Sec4.Gaps.Cert
public import CFSG.RankThree.GF2n.Tim81.Sec4.ListBridges

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Tim78
open RootHyp
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {M V H : Subgroup G}

private theorem isL2OrSzGroup_or_subpairWitness (hG : GapsStatement)
    {L : Type} [Group L] {T : Subgroup L} {g : L}
    (hList : ListGroup L) (hT : Assembly.IsElemAbelian 2 T)
    (hwc : WeaklyClosedIn T (Subgroup.normalizer (T : Set L)))
    (hwti : CentralTI.WeakTI T) (hgen : T ⊔ conjSubgroup g T = ⊤) :
    IsL2OrSzGroup L ∨ SubpairWitness L := by
  classical
  rcases hList with ⟨m, s, hm2, hs1, hPSL⟩ | ⟨s, hs2, hPSU⟩ |
    ⟨s, hsodd, hs3, hSz⟩ | ⟨k, hk6, hk9, hAk⟩ | hM22 | hM23 | hM24
  · by_cases hm : m = 2
    · subst m
      exact Or.inl (IsL2OrSzGroup.of_psl2_model hPSL)
    by_cases hm3 : m = 3
    · subst m
      exact absurd hgen (kiInsp_PSL3 hPSL T hT g)
    have hm4 : 4 ≤ m := by omega
    by_cases h41 : (m, s) = (4, 1)
    · obtain ⟨rfl, rfl⟩ := h41
      exact Or.inr (hG L (Or.inl ⟨8, by norm_num, by norm_num,
        nonempty_mulEquiv_alternating_eight_of_psl4_model hPSL⟩))
    · exact absurd hgen (kiInsp_PSL hPSL hm4 h41 T hT hwc hwti g)
  · exact absurd hgen (kiInsp_PSU3 hPSU T hT g)
  · exact Or.inl (IsL2OrSzGroup.of_sz_lieModel hSz)
  · exact Or.inr (hG L (Or.inl ⟨k, hk6, hk9, hAk⟩))
  · exact Or.inr (hG L (Or.inr (Or.inl hM22)))
  · exact Or.inr (hG L (Or.inr (Or.inr (Or.inl hM23))))
  · exact Or.inr (hG L (Or.inr (Or.inr (Or.inr hM24))))

private theorem false_of_subpairImage_witness (h79 : Tim79aStatementWCQ) (hA5 : HA5Statement)
    (hCT : CentralTIStatement) (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H)
    {Z : Subgroup (HBar V H)} [Z.Normal] (hZ : Z ≤ Subgroup.center (HBar V H))
    {g : G} (hg : g ∈ H)
    (hwit : (Group.IsSolvable (subpairImage M V H Z g) ∧
        ¬ IsPGroup 2 (subpairImage M V H Z g)) ∨
      ∃ R : Subgroup (subpairImage M V H Z g), ∃ _ : R.Normal,
        Group.IsSolvable ↥R ∧
          Nonempty (↥(subpairImage M V H Z g) ⧸ R ≃* alternatingGroup (Fin 5))) :
    False := by
  rcases hwit with ⟨hsolv, hn2⟩ | ⟨R, hRnorm, hRsolv, ⟨e5⟩⟩
  · exact RootHyp.false_of_solvable_subpair h79 h hPH hVH hZ hg hsolv hn2
  · letI : R.Normal := hRnorm
    exact RootHyp.false_of_alt5_subpair h79 hA5 hCT h hPH hVH hZ hg R hRsolv e5

private theorem false_of_gaps_witness (h79 : Tim79aStatementWCQ) (hA5 : HA5Statement)
    (hCT : CentralTIStatement) (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H)
    {Z : Subgroup (HBar V H)} [Z.Normal] (hZ : Z ≤ Subgroup.center (HBar V H))
    (hW : SubpairWitness (HBar V H ⧸ Z))
    (hWC : IsWC ((imgK V H (Pc M V)).map (QuotientGroup.mk' Z)))
    (h4 : 4 ≤ Nat.card ((imgK V H (Pc M V)).map (QuotientGroup.mk' Z))) : False := by
  classical
  obtain ⟨gq', hwit⟩ := hW _ hWC h4
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective Z gq'
  obtain ⟨gH, hgpi⟩ := piK_surjective V H x
  let g : G := (gH : G)
  have hgH : g ∈ H := gH.2
  have hgq : QuotientGroup.mk' Z (piK V H ⟨g, hgH⟩) = gq' := by
    have hgH' : (⟨g, hgH⟩ : ↥H) = gH := Subtype.ext rfl
    rw [hgH', hgpi, hx]
  have hsub := map_imgK_subpair (hPH := hPH) (g := g) hgH (Z := Z)
  have hsub' : subpairImage M V H Z g =
      (imgK V H (Pc M V)).map (QuotientGroup.mk' Z) ⊔
        conjSubgroup gq' ((imgK V H (Pc M V)).map (QuotientGroup.mk' Z)) := by
    simpa [g, hgq] using hsub
  have hwit' : (Group.IsSolvable (subpairImage M V H Z g) ∧
        ¬ IsPGroup 2 (subpairImage M V H Z g)) ∨
      ∃ R : Subgroup (subpairImage M V H Z g), ∃ _ : R.Normal,
        Group.IsSolvable ↥R ∧
          Nonempty (↥(subpairImage M V H Z g) ⧸ R ≃* alternatingGroup (Fin 5)) := by
    rw [hsub']
    exact hwit
  exact false_of_subpairImage_witness h79 hA5 hCT h hPH hVH hZ hgH hwit'

private theorem isL2OrSz_T_facts (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M) :
    Assembly.IsElemAbelian 2 (imgK V H (Pc M V)) ∧
      IsTI (imgK V H (Pc M V)) ∧
      ¬ (imgK V H (Pc M V)).Normal ∧
      4 ≤ Nat.card (imgK V H (Pc M V)) := by
  classical
  exact ⟨isElemAbelian_imgK h hPH hVH, isTI_imgK h hPH hVH,
    not_normal_imgK h hPH hH hnM, four_le_card_imgK h hPH hVH hH hnM⟩

private theorem isL2OrSz_T_gen_facts (h : RootHyp M V) (hPH : Pc M V ≤ H)
    {y : G} (hy : y ∈ H)
    (hHy : H = Pc M V ⊔ conjSubgroup y (Pc M V)) :
    imgK V H (Pc M V) ⊔ conjSubgroup (piK V H ⟨y, hy⟩) (imgK V H (Pc M V)) = ⊤ ∧
      Subgroup.normalClosure (imgK V H (Pc M V) : Set (HBar V H)) = ⊤ ∧
      WeaklyClosedIn (imgK V H (Pc M V))
        (Subgroup.normalizer ((imgK V H (Pc M V)) : Set (HBar V H))) := by
  have hTgen : imgK V H (Pc M V) ⊔
      conjSubgroup (piK V H ⟨y, hy⟩) (imgK V H (Pc M V)) = ⊤ := by
    have hPyH : conjSubgroup y (Pc M V) ≤ H := conjSubgroup_le_of_le_of_mem hPH hy
    calc imgK V H (Pc M V) ⊔
          conjSubgroup (piK V H ⟨y, hy⟩) (imgK V H (Pc M V))
        = imgK V H (Pc M V) ⊔ imgK V H (conjSubgroup y (Pc M V)) := by
          rw [imgK_conjSubgroup hy hPH]
      _ = imgK V H (Pc M V ⊔ conjSubgroup y (Pc M V)) := imgK_sup hPH hPyH
      _ = imgK V H H := by rw [hHy]
      _ = ⊤ := imgK_self V H
  have hgen : Subgroup.normalClosure (imgK V H (Pc M V) : Set (HBar V H)) = ⊤ := by
    simpa using normalClosure_imgK_eq_top h hPH hy hHy
  have hwcT : WeaklyClosedIn (imgK V H (Pc M V))
      (Subgroup.normalizer ((imgK V H (Pc M V)) : Set (HBar V H))) := by
    refine ⟨Subgroup.le_normalizer, ?_⟩
    intro gbar hgbar
    obtain ⟨x, rfl⟩ := piK_surjective V H gbar
    have hconj : conjSubgroup (piK V H x) (imgK V H (Pc M V)) =
        imgK V H (conjSubgroup (x : G) (Pc M V)) :=
      (imgK_conjSubgroup (V := V) (H := H) (S := Pc M V) x.2 hPH).symm
    rw [hconj] at hgbar ⊢
    exact weaklyClosed_imgK h hPH x.2 hgbar
  exact ⟨hTgen, hgen, hwcT⟩

private theorem isL2OrSz_quotient_step (hG : GapsStatement) (hA : TheoremAStmt)
    (h79 : Tim79aStatementWCQ)
    (hA5 : HA5Statement) (hCT : CentralTIStatement)
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    {y : G} (hy : y ∈ H)
    (hT_el : Assembly.IsElemAbelian 2 (imgK V H (Pc M V)))
    (hTI : IsTI (imgK V H (Pc M V)))
    (hnotNormal : ¬ (imgK V H (Pc M V)).Normal)
    (h4T : 4 ≤ Nat.card (imgK V H (Pc M V)))
    (hTgen : imgK V H (Pc M V) ⊔
      conjSubgroup (piK V H ⟨y, hy⟩) (imgK V H (Pc M V)) = ⊤)
    (hgen : Subgroup.normalClosure (imgK V H (Pc M V) : Set (HBar V H)) = ⊤)
    (hwcT : WeaklyClosedIn (imgK V H (Pc M V))
      (Subgroup.normalizer ((imgK V H (Pc M V)) : Set (HBar V H)))) :
    IsL2OrSz V H := by
  classical
  let Y := HBar V H
  let T : Subgroup Y := imgK V H (Pc M V)
  obtain ⟨Z, hZcenter, hZnormal, hList⟩ :=
    exists_listGroup_quot hA h hPH hVH hH hnM
  letI : Z.Normal := hZnormal
  have hZcenterY : Z ≤ Subgroup.center Y := by simpa [Y] using hZcenter
  let L := Y ⧸ Z
  let Tq : Subgroup L := T.map (QuotientGroup.mk' Z)
  let gq : L := QuotientGroup.mk' Z (piK V H ⟨y, hy⟩)
  have hList' : ListGroup L := by simpa [L, Y] using hList
  have hTZ : T ⊓ Z = ⊥ :=
    CentralTI.inf_eq_bot_of_not_normal hTI hZcenterY hnotNormal
  have hTqgen : Tq ⊔ conjSubgroup gq Tq = ⊤ := by
    have h := CentralTI.map_sup_conj_eq_top (T := T) (Z := Z) hTgen
    simpa [Tq, gq] using h
  have hTq_el : Assembly.IsElemAbelian 2 Tq := by
    simpa [Tq] using CFSG.Open.IsElemAbelian.map hT_el (QuotientGroup.mk' Z)
  have hwcTq : WeaklyClosedIn Tq (Subgroup.normalizer (Tq : Set L)) := by
    change WeaklyClosedIn (T.map (QuotientGroup.mk' Z))
      (Subgroup.normalizer ((T.map (QuotientGroup.mk' Z)) : Set (Y ⧸ Z)))
    exact ⟨Subgroup.le_normalizer,
      CentralTI.weaklyClosed_map_mk' (T := T) (Z := Z) hZcenterY hwcT⟩
  have hwTIq : CentralTI.WeakTI Tq := by
    simpa [Tq] using CentralTI.weakTI_map (T := T) (Z := Z) hT_el hTI hZcenterY
  have h4Tq : 4 ≤ Nat.card Tq := by
    have hcard : Nat.card Tq = Nat.card T := by
      let f : ↥T →* Y ⧸ Z := (QuotientGroup.mk' Z).domRestrict T
      have hker : f.ker = ⊥ := by
        change ((QuotientGroup.mk' Z).domRestrict T).ker = ⊥
        rw [MonoidHom.ker_domRestrict, QuotientGroup.ker_mk', Subgroup.subgroupOf_eq_bot,
          disjoint_iff, inf_comm]
        exact hTZ
      have hf : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp hker
      have hcard' := Nat.card_congr (MonoidHom.ofInjective hf).toEquiv
      have hrange : f.range = T.map (QuotientGroup.mk' Z) :=
        MonoidHom.domRestrict_range (K := T) (QuotientGroup.mk' Z)
      rw [hrange] at hcard'
      exact hcard'.symm
    have h4T' : 4 ≤ Nat.card T := h4T
    omega
  have hWCq : IsWC Tq := by
    simpa [Tq] using CentralTI.isWC_map_mk' (T := T) (Z := Z) hT_el hTI hwcT hZcenterY
  rcases isL2OrSzGroup_or_subpairWitness hG hList' hTq_el hwcTq hwTIq hTqgen with
    hL2 | hW
  · have hZbot : Z = ⊥ := hCT Y T Z hT_el hgen hTI hwcT hZcenterY hL2
    have e : L ≃* Y := by
      dsimp [L]
      exact (QuotientGroup.quotientMulEquivOfEq (G := Y) hZbot).trans
        (QuotientGroup.quotientBot (G := Y))
    exact IsL2OrSzGroup.of_mulEquiv e hL2
  · exfalso
    exact false_of_gaps_witness h79 hA5 hCT h hPH hVH hZcenter hW hWCq h4Tq

theorem RootHyp.isL2OrSz_of_inputs
    (hA : TheoremAStmt) (h79 : Tim79aStatementWCQ)
    (hA5 : HA5Statement) (hCT : CentralTIStatement)
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M) : IsL2OrSz V H := by
  classical
  obtain ⟨y, hy, -, -, hHy⟩ := h.exists_mem_conj_eq_of_eq_sup hPH hH
  obtain ⟨hT_el, hTI, hnotNormal, h4T⟩ := isL2OrSz_T_facts h hPH hVH hH hnM
  obtain ⟨hTgen, hgen, hwcT⟩ := isL2OrSz_T_gen_facts h hPH hy hHy
  exact isL2OrSz_quotient_step Gaps.gapsStatement hA h79 hA5 hCT h hPH hVH hH hnM hy
    hT_el hTI hnotNormal h4T hTgen hgen hwcT

theorem sec41Statement_of_inputs
    (hA : TheoremAStmt) (h79 : Tim79aStatementWCQ)
    (hA5 : HA5Statement) (hCT : CentralTIStatement) : Sec41Statement := by
  intro G _ _ M V h h₀ hmem
  have hVH : V ≤ inSubgroup (pCore 2) (Pc M V ⊔ conjSubgroup h₀ (Pc M V)) :=
    h.le_pCore_of_isHMember h79 hmem
  exact h.isL2OrSz_of_inputs hA h79 hA5 hCT hmem.2.1 hVH rfl hmem.2.2

end CFSG.RankThree.GF2n.Tim81
