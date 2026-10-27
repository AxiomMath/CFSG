module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154CritO2Hyp

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s16h_card_eq_of_le_three_mul_card_of_card_eq_pow {p n : ℕ} (hp : p.Prime)
    (h5 : 5 ≤ p) {E E₁ : Subgroup G} (hE₁ : E₁ ≤ E) (hEn : Nat.card ↥E = p ^ n)
    (hcard : Nat.card ↥E ≤ 3 * Nat.card ↥E₁) : Nat.card ↥E₁ = p ^ n := by
  have hmul := Subgroup.relIndex_mul_card (H := E₁) (K := E)
  rw [inf_eq_left.2 hE₁, hEn] at hmul
  have hpos : 0 < Nat.card ↥E₁ := by
    haveI : Nonempty ↥E₁ := ⟨1⟩
    exact Nat.card_pos
  have hrel : E₁.relIndex E ≤ 3 := by
    have hle : E₁.relIndex E * Nat.card ↥E₁ ≤ 3 * Nat.card ↥E₁ := by
      calc E₁.relIndex E * Nat.card ↥E₁ = p ^ n := hmul
        _ = Nat.card ↥E := hEn.symm
        _ ≤ 3 * Nat.card ↥E₁ := hcard
    exact Nat.le_of_mul_le_mul_right hle hpos
  have hdvd : E₁.relIndex E ∣ p ^ n := ⟨Nat.card ↥E₁, hmul.symm⟩
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  have hk0 : k = 0 := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exact h
    · exfalso
      have hp_le : p ≤ E₁.relIndex E := by
        rw [hk]
        exact Nat.le_self_pow (n := k) h.ne' p
      omega
  rw [hk, hk0, pow_zero, one_mul] at hmul
  exact hmul

theorem s16h_uniqueMax_of_blockBound_one_five (D : Data G) (h61 : UC6.R6_1 D) (h127 : R127 D)
    {V₀ V L : Subgroup G} (h : Setting16 D V₀ V L)
    (hs : s15 D.M V₀ V h.hyp151.isElemAbelian L ≤ 3) {q : ℕ} (hq : q ∈ D.sig)
    (h3 : 3 ≤ CFSG.Open.pRank q D.M) (h5 : 5 ≤ q)
    (hBB : s16h_BlockBound (Mbar D.M V₀ V h.hyp151.isElemAbelian)
      (barSub V₀ V h.hyp151.isElemAbelian L) q 1) :
    ∀ w ∈ wSub V₀ V h.hyp151.isElemAbelian L, w ≠ 1 →
      UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
  have hV := h.hyp151.isElemAbelian
  have hpp := D.sig_prime q hq
  obtain ⟨E, hEM, hE, hEcard⟩ :=
    c23_exists_elemAbelian_card_pow (p := q) (M := D.M) (k := 3) hpp.1
      (by rw [UC6.groupPRank_eq_pRank]; exact h3)
  set E₁ := E ⊓ nBar D.M V₀ V hV L with hE₁
  have hthree := s16h_card_le_three_mul_card_inf_nBar D h.hyp151 hs hEM
  have hE₁card : Nat.card ↥E₁ = q ^ 3 :=
    s16h_card_eq_of_le_three_mul_card_of_card_eq_pow (E := E) (E₁ := E₁) hpp.1 h5
      inf_le_left hEcard hthree
  have hcard := s16h_card_le_pow_mul_card_inf_preBarSub D h.hyp151 hBB (E := E₁)
    (inf_le_left.trans hEM) (hE.mono inf_le_left)
    (s16h_barSub_le_normalizer_of_le_nBar D.M V₀ V hV inf_le_right)
  refine s16h_uniqueMax_of_card_le D h61 h127 h hq h3 (E := E₁)
    (hE.mono inf_le_left) ?_
  rw [hE₁card] at hcard
  refine Nat.le_of_mul_le_mul_left ?_ hpp.1.pos
  calc q * q ^ 2 = q ^ 3 := by ring
    _ ≤ q ^ 1 * Nat.card ↥(E₁ ⊓ preBarSub D.M V₀ V hV (centSub (wTil V₀ V hV L))) := hcard
    _ = q * Nat.card ↥(E₁ ⊓ preBarSub D.M V₀ V hV (centSub (wTil V₀ V hV L))) := by ring

theorem s16h_uniqueMax_or_dvd_of_blockBound_one_five (D : Data G) (h61 : UC6.R6_1 D)
    (h127 : R127 D) {V₀ V L : Subgroup G} (h : Setting16 D V₀ V L)
    (hs : s15 D.M V₀ V h.hyp151.isElemAbelian L = 3) {q : ℕ} (hq : q ∈ D.sig)
    (h3 : 3 ≤ CFSG.Open.pRank q D.M) (h5 : 5 ≤ q)
    (hv1 : v1Sub D.M V₀ V h.hyp151.isElemAbelian L ≤ V₀)
    (hBB : s16h_BlockBound (Mbar D.M V₀ V h.hyp151.isElemAbelian)
      (barSub V₀ V h.hyp151.isElemAbelian L) q 1)
    {X Y : Subgroup G} (hX : X ∈ wConj D.M V₀ V h.hyp151.isElemAbelian L)
    (hY : Y ∈ wConj D.M V₀ V h.hyp151.isElemAbelian L) :
    ∀ u ∈ X ⊔ Y ⊔ v1Sub D.M V₀ V h.hyp151.isElemAbelian L, u ≠ 1 →
      UniqueMax D.M (D.M ⊓ centralizer ({u} : Set G)) ∨
        q ∣ Nat.card ↥(D.M ⊓ centralizer ({u} : Set G)) := by
  have hV := h.hyp151.isElemAbelian
  have hpp := D.sig_prime q hq
  obtain ⟨x, hx, rfl⟩ := hX
  obtain ⟨y, hy, rfl⟩ := hY
  intro u hu hu1
  by_cases hu0 : u ∈ V₀
  · exact Or.inl (s16c34_uniqueMax_cent_of_mem_v0 D h61 h.hyp16 hq h3 hu0 hu1)
  · right
    have hu' := s16h_sup_le_preTil D h.hyp151 hv1 hx hy hu
    have huV : u ∈ V := preTil_le V₀ V hV _ hu'
    obtain ⟨E, hEM, hE, hEcard⟩ :=
      c23_exists_elemAbelian_card_pow (p := q) (M := D.M) (k := 3) hpp.1
        (by rw [UC6.groupPRank_eq_pRank]; exact h3)
    have hcard := s16h_card_le_sq_mul_card_inf_preBarSub_sup D h.hyp151 hs hpp.1 hpp.2 hBB hEM hE
      hx hy
    set P := (E ⊓ nBar D.M V₀ V hV L) ⊓ preBarSub D.M V₀ V hV (centSub (wTil V₀ V hV
      (conjSubgroup L x) ⊔ wTil V₀ V hV (conjSubgroup L y))) with hP
    have hPab : IsElemAbelian q P := hE.mono (inf_le_left.trans inf_le_left)
    haveI : Fact q.Prime := ⟨hpp.1⟩
    have hPne : Nat.card ↥P ≠ 1 := by
      intro h1
      rw [hEcard, h1, mul_one] at hcard
      have hq2pos : 0 < q ^ 2 := pow_pos (by omega) 2
      have hlt : 3 * q ^ 2 < q ^ 3 := by
        calc 3 * q ^ 2 < q * q ^ 2 := mul_lt_mul_of_pos_right (by omega) hq2pos
          _ = q ^ 3 := by ring
      exact absurd hcard (not_le.mpr hlt)
    exact s16h_dvd_card_cent_of_cElt D h127 h.hyp16 hpp.1 hpp.2 huV hu0
      (inf_le_right.trans (s16h_preBarSub_le_cElt_of_le_centSub hV le_rfl hu'))
      (hPab.isPGroup.card_eq_or_dvd.resolve_left hPne)

theorem s16h_inf_eq_bot_of_blockBound_one_five (D : Data G) (h61 : UC6.R6_1 D) (h127 : R127 D)
    {V₀ V L : Subgroup G} (h : Setting16 D V₀ V L)
    (hs : s15 D.M V₀ V h.hyp151.isElemAbelian L = 3) {q : ℕ} (hq : q ∈ D.sig)
    (hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded q D.M)
    (h3 : 3 ≤ CFSG.Open.pRank q D.M) (h5 : 5 ≤ q)
    (hv1 : v1Sub D.M V₀ V h.hyp151.isElemAbelian L ≤ V₀)
    (hBB : s16h_BlockBound (Mbar D.M V₀ V h.hyp151.isElemAbelian)
      (barSub V₀ V h.hyp151.isElemAbelian L) q 1)
    {g : G} (hg : g ∉ D.M) {X Y : Subgroup G} (hX : X ∈ wConj D.M V₀ V h.hyp151.isElemAbelian L)
    (hY : Y ∈ wConj D.M V₀ V h.hyp151.isElemAbelian L) :
    (X ⊔ Y ⊔ v1Sub D.M V₀ V h.hyp151.isElemAbelian L) ⊓
      conjSubgroup (wSub V₀ V h.hyp151.isElemAbelian L ⊔
        v1Sub D.M V₀ V h.hyp151.isElemAbelian L) g = ⊥ := by
  have hV := h.hyp151.isElemAbelian
  have hV1 := s15_Infra_v1Sub_le (L := L) h.hyp151.hyp125 hV
  have h1 := s16h_uniqueMax_of_blockBound_one_five D h61 h127 h hs.le hq h3 h5 hBB
  exact s16h_inf_conjSubgroup_eq_bot_of_strong D.maxLocal
    (fun _ hg' => s16h_not_dvd_inf_conjSubgroup hsp hg')
    (s16h_isPGroup_two_of_le hV (sup_le (sup_le (s16h_wConj_le_v D h.hyp151 hX)
      (s16h_wConj_le_v D h.hyp151 hY)) hV1))
    (s16h_isPGroup_two_of_le hV (sup_le (preTil_le V₀ V hV _) hV1))
    (s16h_uniqueMax_or_dvd_of_blockBound_one_five D h61 h127 h hs hq h3 h5 hv1 hBB hX hY)
    (s16h_unique₁_of_wSub D h.hyp151 hv1 h1) hg

theorem s16h_hyp154_of_blockBound_one_five (D : Data G) (h61 : UC6.R6_1 D) (h127 : R127 D)
    {V₀ V L : Subgroup G} (h : Setting16 D V₀ V L)
    (hs : s15 D.M V₀ V h.hyp151.isElemAbelian L = 3) {q : ℕ} (hq : q ∈ D.sig)
    (hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded q D.M)
    (h3 : 3 ≤ CFSG.Open.pRank q D.M) (h5 : 5 ≤ q)
    (hv1 : v1Sub D.M V₀ V h.hyp151.isElemAbelian L ≤ V₀)
    (hBB : s16h_BlockBound (Mbar D.M V₀ V h.hyp151.isElemAbelian)
      (barSub V₀ V h.hyp151.isElemAbelian L) q 1) :
    Hyp154 D V₀ V L := by
  have h1 := s16h_uniqueMax_of_blockBound_one_five D h61 h127 h hs.le hq h3 h5 hBB
  have hU₁ := s16h_unique₁_of_wSub D h.hyp151 hv1 h1
  refine ⟨h.hyp151, hU₁, s16h_unique₂_of_unique₁_three D h.hyp151 hs hU₁, ?_⟩
  intro g hg X hX Y hY _ hne
  exact absurd (s16h_inf_eq_bot_of_blockBound_one_five D h61 h127 h hs hq hsp h3 h5 hv1 hBB hg hX
    hY) hne

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
