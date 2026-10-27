module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Std
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Case2LnLift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165Bar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154CritS2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Good

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_e3_uniqueMax_of_fixed (D : Data G) (S : s16h_Std D) {V₀ V L : Subgroup G}
    (h : Setting16 D V₀ V L) {q : ℕ} (hq : q ∈ D.sig)
    (hv1 : v1Sub D.M V₀ V h.hyp151.isElemAbelian L ≤ wSub V₀ V h.hyp151.isElemAbelian L)
    (hfix : ∀ w : Vtil V₀ V h.hyp151.isElemAbelian,
      w ∈ wTil V₀ V h.hyp151.isElemAbelian L → w ≠ 1 →
      ∃ E : Subgroup (MulAut (Vtil V₀ V h.hyp151.isElemAbelian)),
        E ≤ Mbar D.M V₀ V h.hyp151.isElemAbelian ∧ IsElemAbelian q E ∧ q ^ 2 ≤ Nat.card ↥E ∧
          ∀ e ∈ E, e w = w) :
    ∀ w ∈ wSub V₀ V h.hyp151.isElemAbelian L ⊔ v1Sub D.M V₀ V h.hyp151.isElemAbelian L,
      w ≠ 1 → UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
  have hV := h.hyp151.isElemAbelian
  haveI : Finite (MulAut (Vtil V₀ V hV)) := MulEquiv.finite_left
  have hpp := D.sig_prime q hq
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp151.hyp125.pairFacts.le_normalizer
      h.hyp151.hyp125.pairFacts.le_normalizer₀
  intro w hw hw1
  have hwW : w ∈ wSub V₀ V hV L := by
    rw [sup_eq_left.2 hv1] at hw
    exact hw
  by_cases hw0 : w ∈ V₀
  · exact s16h_v0_good D S.h61 h.hyp16 ⟨q, hq, S.hx.three_le q hq⟩ w hw0 hw1
  · have hwV : w ∈ V := preTil_le V₀ V hV (wTil V₀ V hV L) hwW
    let wtil : Vtil V₀ V hV := mkTil V₀ V hV (IntMod.mk hV ⟨w, hwV⟩)
    have hwtil : wtil ∈ wTil V₀ V hV L :=
      (mem_preTil_iff_of_mem V₀ V hV (wTil V₀ V hV L) hwV).1 hwW
    have hwtil1 : wtil ≠ 1 := by
      intro h1
      apply hw0
      have h2 : (IntMod.mk hV ⟨w, hwV⟩ : IntMod V hV) ∈ modNull V₀ V hV :=
        (QuotientGroup.eq_one_iff (N := modNull V₀ V hV) _).1 h1
      exact (mem_modNull V₀ V hV _).1 h2
    obtain ⟨E, hEMbar, hEab, hEcard, hEfix⟩ := hfix wtil hwtil hwtil1
    have hEp : IsPGroup q E := hEab.isPGroup
    have hEnc : ¬ IsCyclic ↥E := s16c7_not_isCyclic_of_elemAbelian hpp.1 hEab hEcard
    let φ : ↥D.M →* MulAut (Vtil V₀ V hV) := barHom V₀ V hV hMs
    have hErange : E ≤ φ.range := by
      rw [range_barHom V₀ V hV hMs]
      exact hEMbar
    obtain ⟨B, hBp, hBc, hB⟩ := exists_noncyclic_pGroup_map_le φ hpp.1 hErange hEp hEnc
    let P : Subgroup G := B.map D.M.subtype
    have hPp : IsPGroup q P := hBp.map D.M.subtype
    have hPc : ¬ IsCyclic ↥P := fun hc =>
      hBc ((Subgroup.equivMapOfInjective B D.M.subtype D.M.subtype_injective).isCyclic.2 hc)
    have hPle : P ≤ F11.CElt D.M V₀ w := by
      rw [Subgroup.map_le_iff_le_comap]
      intro b hb
      rw [Subgroup.mem_comap]
      have hbfix : φ b wtil = wtil := hEfix (φ b) (hB b hb)
      have hcomm : (b : G) * w * (b : G)⁻¹ * w⁻¹ ∈ V₀ :=
        (barHom_fix_iff V₀ V hV hMs b (IntMod.mk hV ⟨w, hwV⟩)).1 hbfix
      exact ⟨b.2, (stabTil_le_normalizer₀ V₀ V) (hMs b.2), hcomm⟩
    exact s16c34_uniqueMax_cent_of_cElt D S.h61 S.h127 h.hyp16 hq hPp hPc hwV hw0 hPle

theorem s16h_e3_bar_rank_ge (D : Data G) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V) {q k : ℕ}
    (hqC : ¬ q ∣ Nat.card ↥(F11.CTilde D.M V₀ V))
    (hE : ∃ E : Subgroup G, E ≤ D.M ∧ IsElemAbelian q E ∧ Nat.card ↥E = q ^ k)
    [Fact q.Prime] :
    ∃ Eb : Subgroup (MulAut (Vtil V₀ V h.isElemAbelian)),
      Eb ≤ Mbar D.M V₀ V h.isElemAbelian ∧ IsElemAbelian q Eb ∧ Nat.card ↥Eb = q ^ k := by
  obtain ⟨E, hEM, hEab, hEcard⟩ := hE
  have hV := h.isElemAbelian
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.pairFacts.le_normalizer h.pairFacts.le_normalizer₀
  have hEs : E ≤ stabTil V₀ V := hEM.trans hMs
  have hdisj : E ⊓ F11.CTilde D.M V₀ V = ⊥ := by
    refine (Subgroup.disjoint_of_coprime_natCard (H := E)
      (K := F11.CTilde D.M V₀ V) ?_).eq_bot
    rw [hEcard]
    exact Nat.Coprime.pow_left _
      ((Nat.Prime.coprime_iff_not_dvd (Fact.out : q.Prime)).2 hqC)
  have hpre : preBarSub E V₀ V hV ⊥ = ⊥ := by
    apply le_antisymm _ bot_le
    intro g hg
    rw [Subgroup.mem_bot]
    obtain ⟨hgE, hgs, hbot⟩ := (mem_preBarSub E V₀ V hV ⊥).1 hg
    rw [Subgroup.mem_bot] at hbot
    have hgC : g ∈ F11.CTilde D.M V₀ V := by
      rw [mem_cTilde_iff hV h.pairFacts.le_normalizer]
      refine ⟨hEM hgE, hEs hgE, ?_⟩
      change actTil V₀ V hV ⟨g, hEs hgE⟩ = 1
      rw [show (⟨g, hEs hgE⟩ : ↥(stabTil V₀ V)) = ⟨g, hgs⟩ from Subtype.ext rfl, hbot]
    have h3 : g ∈ E ⊓ F11.CTilde D.M V₀ V := ⟨hgE, hgC⟩
    rw [hdisj, Subgroup.mem_bot] at h3
    exact h3
  refine ⟨barSub V₀ V hV E, barSub_mono V₀ V hV hEM, s16h_barSub_isElemAbelian hV hEab, ?_⟩
  have hcard : Nat.card ↥(barSub V₀ V hV E) = Nat.card ↥E := by
    have h := s16c7_card_mul_card_preBarSub hV hEs
      (Q := (⊥ : Subgroup (MulAut (Vtil V₀ V hV)))) bot_le
    simpa [hpre] using h.symm
  rw [hcard, hEcard]

theorem s16h_e3_bar_card_le (D : Data G) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V) {q m : ℕ}
    (hq : q.Prime) (hqC : ¬ q ∣ Nat.card ↥(F11.CTilde D.M V₀ V))
    (hm : CFSG.Open.pRank q D.M ≤ m) :
    ∀ Eb : Subgroup (MulAut (Vtil V₀ V h.isElemAbelian)),
      Eb ≤ Mbar D.M V₀ V h.isElemAbelian → IsElemAbelian q Eb → Nat.card ↥Eb ≤ q ^ m := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Finite (MulAut (Vtil V₀ V h.isElemAbelian)) := MulEquiv.finite_left
  have hV := h.isElemAbelian
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.pairFacts.le_normalizer h.pairFacts.le_normalizer₀
  intro Eb hEbMbar hEbab
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := q)).1 hEbab.isPGroup
  have hk_le : k ≤ CFSG.Open.pRank q D.M := by
    let φ : ↥D.M →* MulAut (Vtil V₀ V hV) := barHom V₀ V hV hMs
    haveI : φ.ker.Normal := MonoidHom.normal_ker φ
    have hCtildeM : F11.CTilde D.M V₀ V ≤ D.M := by
      rw [cTilde_eq_preBarSub_bot hV h.pairFacts.le_normalizer]
      exact inf_le_left
    have hNcard : Nat.card ↥φ.ker = Nat.card ↥(F11.CTilde D.M V₀ V) := by
      rw [ker_barHom V₀ V hV h.pairFacts.le_normalizer hMs]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCtildeM).toEquiv
    have hN : ¬ q ∣ Nat.card ↥φ.ker := by
      rw [hNcard]
      exact hqC
    have hquot := CFSG.SectionRank.pRank_quotient_eq (G := ↥D.M) (N := φ.ker) hN
    have hequiv2 := CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := q) hq.one_lt
      (QuotientGroup.quotientKerEquivRange φ)
    have hrange : φ.range = Mbar D.M V₀ V hV := range_barHom V₀ V hV hMs
    have hequiv1 := CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := q) hq.one_lt
      (MulEquiv.subgroupCongr hrange).symm
    have hMbar : CFSG.Open.pRank q (Mbar D.M V₀ V hV) = CFSG.Open.pRank q D.M := by
      calc CFSG.Open.pRank q (Mbar D.M V₀ V hV)
          = CFSG.Open.pRank q (⊤ : Subgroup (Mbar D.M V₀ V hV)) :=
            CFSG.SectionRank.pRank_eq_pRank_top_subgroup _
        _ = CFSG.Open.pRank q (⊤ : Subgroup φ.range) := hequiv1
        _ = CFSG.Open.pRank q (⊤ : Subgroup (↥D.M ⧸ φ.ker)) := hequiv2.symm
        _ = CFSG.Open.pRank q (⊤ : Subgroup ↥D.M) := hquot
        _ = CFSG.Open.pRank q D.M :=
            (CFSG.SectionRank.pRank_eq_pRank_top_subgroup D.M).symm
    exact (CFSG.SectionRank.le_pRank hq.one_lt le_rfl hEbab hk).trans
      ((CFSG.SectionRank.pRank_mono hq.one_lt hEbMbar).trans (le_of_eq hMbar))
  rw [hk]
  exact Nat.pow_le_pow_right hq.pos (hk_le.trans hm)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
