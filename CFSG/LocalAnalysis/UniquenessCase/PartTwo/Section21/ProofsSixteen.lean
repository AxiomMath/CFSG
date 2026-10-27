module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.StatementsSixInf
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20p
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
public import CFSG.Open.QTFaithfulEmptyTauCeti
public import CFSG.RankThree.PartOne.S11d.PlaneCases
public import CFSG.Quasithin.H13.A5S1327j
public import CFSG.CGT.Timmesfeld75.NodeAux

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Blueprint Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem isL2_of_isAlt_five {X : Type} [Group X] {n : ℕ} (h : IsAlt X n) (hn : n = 5) :
    IsL2 X 2 := by
  subst hn
  obtain ⟨e⟩ := h
  exact CFSG.Quasithin.H13.A5.lieModel_of_alternating_five e

private theorem calC_ne_top {D : Data G} {L : Subgroup G} (hL : L ∈ calC D.M) : L ≠ ⊤ := by
  intro htop
  have hLM : L ≤ D.M := CFSG.Open.IsSubnormal.le hL.1
  exact uc22p20a_M_ne_top D (top_le_iff.mp (htop ▸ hLM))

private theorem barInf_isCatalogGroup {D : Data G} {L : Subgroup G}
    (hL : L ∈ calC D.M) : CFSG.Open.IsCatalogGroup (BarInf L) := by
  have hK : CFSG.Open.IsKGroup ↥L := D.standing.kProper.isKGroup L (calC_ne_top hL)
  obtain ⟨hsimple, hnonab⟩ :=
    uc22p20c_barInf_simple (uc22p20e_cComp_of_calC hL)
  haveI : IsSimpleGroup (BarInf L) := hsimple
  refine hK.isCatalogGroup_of_surjective (⊤ : Subgroup ↥L) hnonab ?_ ?_
  · exact (QuotientGroup.mk' (CFSG.solvableRadical ↥L)).comp Subgroup.topEquiv.toMonoidHom
  · exact (QuotientGroup.mk'_surjective _).comp Subgroup.topEquiv.surjective

private theorem barInf_catalog {D : Data G} {L : Subgroup G} (hL : L ∈ calC D.M)
    (hCA : CFSG.Open.QTFaithfulEmptyTauCeti.CatalogAgree) :
    CFSG.Blueprint.Catalog (BarInf L) := by
  obtain ⟨hsimple, hnonab⟩ := uc22p20c_barInf_simple (uc22p20e_cComp_of_calC hL)
  haveI : IsSimpleGroup (BarInf L) := hsimple
  exact (CFSG.Assembly.CatalogAgreeOn.imp hCA) (BarInf L) hnonab
    (barInf_isCatalogGroup hL)

private theorem center_bar2_eq_bot_of_isL2_barInf {D : Data G} {L : Subgroup G}
    (hL : L ∈ calC D.M) {n : ℕ} (h : IsL2 (BarInf L) n) :
    Subgroup.center (Bar2 L) = ⊥ := by
  change CFSG.Blueprint.LieModel (BarInf L) .PSL 2 2 n at h
  have hq : CFSG.Open.IsQuasisimple (Bar2 L) := hL.2.2
  haveI : Group.IsPerfect (Bar2 L) := Group.isPerfect_def.mpr hq.1
  have hodd : Odd (Nat.card (Subgroup.center (Bar2 L))) := by
    simpa [Bar2] using uc22p20p_odd_center_bar2 ↥L
  have hadm := h.admissible
  have hnne : n ≠ 1 := by
    intro hn
    subst hn
    exact hadm.2.2.2.1 (by norm_num)
  have hn2 : 2 ≤ n := by
    rcases Nat.eq_or_lt_of_le hadm.2.1 with heq | hlt
    · exact absurd heq.symm hnne
    · exact hlt
  obtain ⟨-, K, hKfield, hKfin, hKcard, ⟨eBar⟩⟩ := h.statedClassicalModel (by decide)
  letI : Field K := hKfield
  letI : Finite K := hKfin
  obtain ⟨e0⟩ := uc22p21k_barInf_equiv_of_calC hL
  have e : (Bar2 L) ⧸ Subgroup.center (Bar2 L) ≃* StatedProj (StatedSL 2 K) :=
    e0.symm.trans eBar
  have h2 : IsPGroup 2 (Subgroup.center (Bar2 L)) :=
    CFSG.Quasithin.isPGroup_two_of_mulEquiv_stated_psl_two_even
      (Subgroup.center (Bar2 L)) le_rfl hn2 hKcard e
  haveI : Subsingleton (Subgroup.center (Bar2 L)) :=
    CFSG.GH74.Generic.eq_bot_of_isPGroup_two_of_odd h2 hodd
  exact Subgroup.eq_bot_of_subsingleton _

private theorem center_bar2_eq_bot_of_isSz_barInf {D : Data G} {L : Subgroup G}
    (hL : L ∈ calC D.M) {n : ℕ} (h : IsSz (BarInf L) n) :
    Subgroup.center (Bar2 L) = ⊥ := by
  change CFSG.Blueprint.LieModel (BarInf L) .twistedB2 0 2 n at h
  have hq : CFSG.Open.IsQuasisimple (Bar2 L) := hL.2.2
  haveI : Group.IsPerfect (Bar2 L) := Group.isPerfect_def.mpr hq.1
  have hodd : Odd (Nat.card (Subgroup.center (Bar2 L))) := by
    simpa [Bar2] using uc22p20p_odd_center_bar2 ↥L
  obtain ⟨e0⟩ := uc22p21k_barInf_equiv_of_calC hL
  have hblue : CFSG.Blueprint.LieModel ((Bar2 L) ⧸ Subgroup.center (Bar2 L)) .twistedB2 0 2 n :=
    LieModel.of_mulEquiv e0 h
  have hSz : CFSG.Quasithin.IsSz n ((Bar2 L) ⧸ Subgroup.center (Bar2 L)) :=
    CFSG.CGT.Timmesfeld75.lieModel_twistedB2_iff.mp hblue
  have h2 : IsPGroup 2 (Subgroup.center (Bar2 L)) :=
    CFSG.Quasithin.isPGroup_two_of_isSz (Subgroup.center (Bar2 L)) le_rfl hSz
  haveI : Subsingleton (Subgroup.center (Bar2 L)) :=
    CFSG.GH74.Generic.eq_bot_of_isPGroup_two_of_odd h2 hodd
  exact Subgroup.eq_bot_of_subsingleton _

private theorem isL2_bar2_of_barInf {D : Data G} {L : Subgroup G}
    (hL : L ∈ calC D.M) {n : ℕ} (h : IsL2 (BarInf L) n) : IsL2 (Bar2 L) n := by
  obtain ⟨e⟩ :=
    uc22p21k_barInf_equiv_of_center_bot hL.2.2 (center_bar2_eq_bot_of_isL2_barInf hL h)
  exact LieModel.of_mulEquiv e h

private theorem isSz_bar2_of_barInf {D : Data G} {L : Subgroup G}
    (hL : L ∈ calC D.M) {n : ℕ} (h : IsSz (BarInf L) n) : IsSz (Bar2 L) n := by
  obtain ⟨e⟩ :=
    uc22p21k_barInf_equiv_of_center_bot hL.2.2 (center_bar2_eq_bot_of_isSz_barInf hL h)
  exact LieModel.of_mulEquiv e h

private theorem isSU3_bar2_of_isU3 {D : Data G} {L : Subgroup G}
    (hL : L ∈ calC D.M) {n : ℕ} (h : IsU3 (BarInf L) n) : IsSU3 (Bar2 L) n := by
  refine ⟨hL.2.2, ?_⟩
  obtain ⟨e⟩ := uc22p21k_barInf_equiv_of_calC hL
  exact LieModel.of_mulEquiv e h

private theorem isL2Odd_seven_of_isL3_one {X : Type} [Group X] (h : IsL3 X 1) : IsL2Odd X 7 :=
  CFSG.LocalAnalysis.ComponentInitial.PSL3_two_PSL2_seven_paired_isomorphism X h

theorem s21_16_of_s21_6Inf {D : Data G} {Ch : Choice2011 G}
    (h6 : S21_6Inf D Ch) (h12 : S21_12 D Ch) (h13 : S21_13 D Ch) (h14 : S21_14 D Ch)
    (hCA : CFSG.Open.QTFaithfulEmptyTauCeti.CatalogAgree) : S21_16 D Ch := by
  intro h1930 c L hL
  obtain ⟨hsimple, hnonab⟩ := uc22p20c_barInf_simple (uc22p20e_cComp_of_calC hL)
  haveI : IsSimpleGroup (BarInf L) := hsimple
  rcases CFSG.RankThree.PartOne.PlaneCases.catalog_cases (barInf_catalog hL hCA) with
    hcyc | halt | hlie | hsporRep
  ·
    obtain ⟨q, -, ⟨e⟩⟩ := hcyc
    obtain ⟨a, b, hab⟩ := hnonab
    exact (hab (e.injective (by rw [map_mul, map_mul, mul_comm]))).elim
  ·
    obtain ⟨n, -, halt⟩ := halt
    have hn5 : n = 5 := h13 h1930 c L hL n halt
    exact Or.inr (Or.inr (Or.inl ⟨2, isL2_bar2_of_barInf hL (isL2_of_isAlt_five halt hn5)⟩))
  ·
    obtain ⟨t, n, p, f, hadm, hmodel⟩ := hlie
    have hp : p.Prime := hadm.1
    have hchev : IsChev (BarInf L) p := ⟨t, n, f, hadm, hmodel⟩
    by_cases hp2 : p = 2
    · subst hp2
      rcases h14 h1930 c L hL hchev with hrank | hsp4 | hL3
      · obtain ⟨n, hL2 | hSz | hU3⟩ := hrank
        · exact Or.inr (Or.inr (Or.inl ⟨n, isL2_bar2_of_barInf hL hL2⟩))
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n, isSz_bar2_of_barInf hL hSz⟩)))
        · exact Or.inr (Or.inl ⟨n, isSU3_bar2_of_isU3 hL hU3⟩)
      · exact Or.inl hsp4
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨7, Nat.prime_seven, by norm_num, isL2Odd_seven_of_isL3_one hL3⟩))))
    ·
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨p, hp, hp2, (h12 h1930 c L hL p hp hp2 hchev).1⟩))))
  ·
    obtain ⟨s, hsporShape⟩ := hsporRep
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h6 h1930 c L hL ⟨s, hsporShape⟩).1))))

end CFSG.LocalAnalysis.UniquenessCase.UC22