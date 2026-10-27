module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Table
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Kernel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC34UniqueP
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenGapFourConj

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_barSub_isElemAbelian {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) {E : Subgroup G}
    {q : ℕ} (hE : IsElemAbelian q E) : IsElemAbelian q (barSub V₀ V hV E) :=
  (hE.subgroupOf (stabTil V₀ V)).map (actTil V₀ V hV)

theorem s16h_barSub_le_normalizer_of_s15_le_two (D : Data G) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hs : s15 D.M V₀ V h.isElemAbelian L ≤ 2) {q : ℕ} (hq : Odd q)
    {E : Subgroup G} (hEM : E ≤ D.M) (hE : IsElemAbelian q E) :
    barSub V₀ V h.isElemAbelian E ≤
      normalizer (barSub V₀ V h.isElemAbelian L : Set (MulAut (Vtil V₀ V h.isElemAbelian))) := by
  intro y hy
  haveI : Finite (MulAut (Vtil V₀ V h.isElemAbelian)) := MulEquiv.finite_left
  exact s15GapFour_mem_normalizer_of_odd (Mbar D.M V₀ V h.isElemAbelian)
    (barSub V₀ V h.isElemAbelian L) hs (barSub_mono V₀ V h.isElemAbelian hEM hy) hq
    ((s16h_barSub_isElemAbelian h.isElemAbelian hE).2 y hy)

theorem s16h_card_le_pow_mul_card_inf_preBarSub (D : Data G) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) {q c : ℕ}
    (hBB : s16h_BlockBound (Mbar D.M V₀ V h.isElemAbelian) (barSub V₀ V h.isElemAbelian L) q c)
    {E : Subgroup G} (hEM : E ≤ D.M) (hE : IsElemAbelian q E)
    (hEn : barSub V₀ V h.isElemAbelian E ≤
      normalizer (barSub V₀ V h.isElemAbelian L : Set (MulAut (Vtil V₀ V h.isElemAbelian)))) :
    Nat.card ↥E ≤ q ^ c * Nat.card ↥(E ⊓ preBarSub D.M V₀ V h.isElemAbelian
      (centSub (wTil V₀ V h.isElemAbelian L))) := by
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  exact s16h_card_le_mul_card_preBarSub h.isElemAbelian hEM (hEM.trans hMs) _
    (hBB _ (le_inf (barSub_mono V₀ V h.isElemAbelian hEM) hEn)
      (s16h_barSub_isElemAbelian h.isElemAbelian hE))

theorem s16h_uniqueMax_of_card_le (D : Data G) (h61 : UC6.R6_1 D) (h127 : R127 D)
    {V₀ V L : Subgroup G} (h : Setting16 D V₀ V L) {q : ℕ} (hq : q ∈ D.sig)
    (h3 : 3 ≤ CFSG.Open.pRank q D.M) {E : Subgroup G} (hE : IsElemAbelian q E)
    (hPcard : q ^ 2 ≤ Nat.card ↥(E ⊓ preBarSub D.M V₀ V h.hyp151.isElemAbelian
      (centSub (wTil V₀ V h.hyp151.isElemAbelian L)))) :
    ∀ w ∈ wSub V₀ V h.hyp151.isElemAbelian L, w ≠ 1 →
      UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
  have hV := h.hyp151.isElemAbelian
  have hpp := D.sig_prime q hq
  intro w hw hw1
  by_cases hw0 : w ∈ V₀
  · exact s16c34_uniqueMax_cent_of_mem_v0 D h61 h.hyp16 hq h3 hw0 hw1
  · have hwV : w ∈ V := preTil_le V₀ V hV _ hw
    have hPab : IsElemAbelian q (E ⊓ preBarSub D.M V₀ V hV (centSub (wTil V₀ V hV L))) :=
      hE.mono inf_le_left
    exact s16c34_uniqueMax_cent_of_cElt D h61 h127 h.hyp16 hq hPab.isPGroup
      (s16c7_not_isCyclic_of_elemAbelian hpp.1 hPab hPcard) hwV hw0
      (inf_le_right.trans (s16h_preBarSub_le_cElt_of_le_centSub hV le_rfl hw))

theorem s16h_uniqueMax_of_blockBound_two (D : Data G) (h61 : UC6.R6_1 D) (h127 : R127 D)
    {V₀ V L : Subgroup G} (h : Setting16 D V₀ V L)
    (hs : s15 D.M V₀ V h.hyp151.isElemAbelian L ≤ 2) {q : ℕ} (hq : q ∈ D.sig)
    (h4 : 4 ≤ CFSG.Open.pRank q D.M)
    (hBB : s16h_BlockBound (Mbar D.M V₀ V h.hyp151.isElemAbelian)
      (barSub V₀ V h.hyp151.isElemAbelian L) q 2) :
    ∀ w ∈ wSub V₀ V h.hyp151.isElemAbelian L, w ≠ 1 →
      UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
  have hV := h.hyp151.isElemAbelian
  have hpp := D.sig_prime q hq
  obtain ⟨E, hEM, hE, hEcard⟩ :=
    c23_exists_elemAbelian_card_pow (p := q) (M := D.M) (k := 4) hpp.1
      (by rw [UC6.groupPRank_eq_pRank]; exact h4)
  have hEn := s16h_barSub_le_normalizer_of_s15_le_two D h.hyp151 hs
    (hpp.1.odd_of_ne_two hpp.2) hEM hE
  have hcard := s16h_card_le_pow_mul_card_inf_preBarSub D h.hyp151 hBB hEM hE hEn
  refine s16h_uniqueMax_of_card_le D h61 h127 h hq (by omega) hE ?_
  rw [hEcard] at hcard
  refine Nat.le_of_mul_le_mul_left (a := q ^ 2) ?_ (pow_pos hpp.1.pos 2)
  calc q ^ 2 * q ^ 2 = q ^ 4 := by ring
    _ ≤ _ := hcard

theorem s16h_v1Sub_le_preTil (D : Data G) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    (hv1 : v1Sub D.M V₀ V h.isElemAbelian L ≤ V₀) (S : Subgroup (Vtil V₀ V h.isElemAbelian)) :
    v1Sub D.M V₀ V h.isElemAbelian L ≤ preTil V₀ V h.isElemAbelian S := by
  have hV := h.isElemAbelian
  intro v hv
  have hvV : v ∈ V := s15_Infra_v1Sub_le h.hyp125 hV hv
  refine (mem_preTil_iff_of_mem V₀ V hV _ hvV).2 ?_
  have h0 : mkTil V₀ V hV (IntMod.mk hV ⟨v, hvV⟩) = 1 :=
    (QuotientGroup.eq_one_iff (N := modNull V₀ V hV) _).2 (hv1 hv)
  rw [h0]
  exact Subgroup.one_mem _

theorem s16h_v1Sub_le_wSub (D : Data G) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    (hv1 : v1Sub D.M V₀ V h.isElemAbelian L ≤ V₀) :
    v1Sub D.M V₀ V h.isElemAbelian L ≤ wSub V₀ V h.isElemAbelian L :=
  s16h_v1Sub_le_preTil D h hv1 _

theorem s16h_unique₁_of_wSub (D : Data G) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    (hv1 : v1Sub D.M V₀ V h.isElemAbelian L ≤ V₀)
    (h1 : ∀ w ∈ wSub V₀ V h.isElemAbelian L, w ≠ 1 →
      UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G))) :
    ∀ w ∈ wSub V₀ V h.isElemAbelian L ⊔ v1Sub D.M V₀ V h.isElemAbelian L, w ≠ 1 →
      UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := fun w hw hw1 =>
  h1 w ((sup_le le_rfl (s16h_v1Sub_le_wSub D h hv1)) hw) hw1

theorem s16h_hyp154_of_unique₁_two (D : Data G) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    (hs : s15 D.M V₀ V h.isElemAbelian L = 2)
    (h1 : ∀ w ∈ wSub V₀ V h.isElemAbelian L ⊔ v1Sub D.M V₀ V h.isElemAbelian L, w ≠ 1 →
      UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)))
    (hδ : delta15 D.M V₀ V h.isElemAbelian L < gamma15 D.M V₀ V h.isElemAbelian L - 1) :
    Hyp154 D V₀ V L := by
  have hV := h.isElemAbelian
  refine ⟨h, h1, ?_, fun g _ X _ Y _ _ _ => ⟨hs, hδ⟩⟩
  intro x hx y hy hxy w hw hw1
  have hbot : (⨆ X ∈ {X | X ∈ wConj D.M V₀ V hV L ∧ X ≠ conjSubgroup (wSub V₀ V hV L) x ∧
      X ≠ conjSubgroup (wSub V₀ V hV L) y}, X) = ⊥ := by
    refine le_bot_iff.1 (iSup₂_le fun X hX => ?_)
    exfalso
    obtain ⟨hXw, hXx, hXy⟩ := hX
    haveI : Finite (Subgroup G) := Finite.of_injective _ SetLike.coe_injective
    have hsub : ({X, conjSubgroup (wSub V₀ V hV L) x, conjSubgroup (wSub V₀ V hV L) y} :
        Set (Subgroup G)) ⊆ wConj D.M V₀ V hV L := by
      intro Z hZ
      rcases hZ with rfl | rfl | rfl
      · exact hXw
      · exact ⟨x, hx, rfl⟩
      · exact ⟨y, hy, rfl⟩
    have h3 : ({X, conjSubgroup (wSub V₀ V hV L) x, conjSubgroup (wSub V₀ V hV L) y} :
        Set (Subgroup G)).ncard = 3 :=
      Set.ncard_eq_three.2 ⟨X, _, _, hXx, hXy, hxy, rfl⟩
    have h2 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [ncard_wConj D h hV, hs, h3] at h2
    omega
  rw [hbot, sup_bot_eq] at hw
  exact h1 w (Subgroup.mem_sup_right hw) hw1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
