module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154CritO2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_preTil_mono (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V)
    {S T : Subgroup (Vtil V₀ V hV)} (h : S ≤ T) : preTil V₀ V hV S ≤ preTil V₀ V hV T := by
  intro g hg
  obtain ⟨x, hx, hxS⟩ := (mem_preTil V₀ V hV S).1 hg
  exact (mem_preTil V₀ V hV T).2 ⟨x, hx, h hxS⟩

theorem s16h_isPGroup_two_of_le {V U : Subgroup G} (hV : IsElemAbelian 2 V) (hUV : U ≤ V) :
    IsPGroup 2 U := by
  intro g
  refine ⟨1, Subtype.ext ?_⟩
  simpa using hV.2 g.1 (hUV g.2)

theorem s16h_wConj_le_v (D : Data G) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    {X : Subgroup G} (hX : X ∈ wConj D.M V₀ V h.isElemAbelian L) : X ≤ V := by
  obtain ⟨m, hm, rfl⟩ := hX
  rw [← s15_Infra_wSub_conjSubgroup V₀ V L h.isElemAbelian (s16h_le_stabTil h hm)]
  exact preTil_le V₀ V h.isElemAbelian _

theorem s16h_sup_le_preTil (D : Data G) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    (hv1 : v1Sub D.M V₀ V h.isElemAbelian L ≤ V₀) {x y : G} (hx : x ∈ D.M) (hy : y ∈ D.M) :
    conjSubgroup (wSub V₀ V h.isElemAbelian L) x ⊔ conjSubgroup (wSub V₀ V h.isElemAbelian L) y ⊔
        v1Sub D.M V₀ V h.isElemAbelian L ≤
      preTil V₀ V h.isElemAbelian (wTil V₀ V h.isElemAbelian (conjSubgroup L x) ⊔
        wTil V₀ V h.isElemAbelian (conjSubgroup L y)) := by
  have hV := h.isElemAbelian
  have hMs := s16h_le_stabTil h
  rw [← s15_Infra_wSub_conjSubgroup V₀ V L hV (hMs hx),
    ← s15_Infra_wSub_conjSubgroup V₀ V L hV (hMs hy)]
  exact sup_le (sup_le (s16h_preTil_mono V₀ V hV le_sup_left)
    (s16h_preTil_mono V₀ V hV le_sup_right)) (s16h_v1Sub_le_preTil D h hv1 _)

theorem s16h_uniqueMax_of_blockBound_one (D : Data G) (h61 : UC6.R6_1 D) (h127 : R127 D)
    {V₀ V L : Subgroup G} (h : Setting16 D V₀ V L)
    (hs : s15 D.M V₀ V h.hyp151.isElemAbelian L ≤ 3) {q : ℕ} (hq : q ∈ D.sig)
    (h4 : 4 ≤ CFSG.Open.pRank q D.M)
    (hBB : s16h_BlockBound (Mbar D.M V₀ V h.hyp151.isElemAbelian)
      (barSub V₀ V h.hyp151.isElemAbelian L) q 1) :
    ∀ w ∈ wSub V₀ V h.hyp151.isElemAbelian L, w ≠ 1 →
      UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
  have hV := h.hyp151.isElemAbelian
  have hpp := D.sig_prime q hq
  have hq3 : 3 ≤ q := by
    have := hpp.1.two_le
    have := hpp.2
    omega
  obtain ⟨E, hEM, hE, hEcard⟩ :=
    c23_exists_elemAbelian_card_pow (p := q) (M := D.M) (k := 4) hpp.1
      (by rw [UC6.groupPRank_eq_pRank]; exact h4)
  set E₁ := E ⊓ nBar D.M V₀ V hV L with hE₁
  have h3 := s16h_card_le_three_mul_card_inf_nBar D h.hyp151 hs hEM
  have hcard := s16h_card_le_pow_mul_card_inf_preBarSub D h.hyp151 hBB (E := E₁)
    (inf_le_left.trans hEM) (hE.mono inf_le_left)
    (s16h_barSub_le_normalizer_of_le_nBar D.M V₀ V hV inf_le_right)
  refine s16h_uniqueMax_of_card_le D h61 h127 h hq (by omega) (E := E₁)
    (hE.mono inf_le_left) ?_
  rw [hEcard] at h3
  set P := Nat.card ↥(E₁ ⊓ preBarSub D.M V₀ V hV (centSub (wTil V₀ V hV L))) with hP
  have key : q * q ^ 3 ≤ q * (3 * P) := by
    calc q * q ^ 3 = q ^ 4 := by ring
      _ ≤ 3 * Nat.card ↥E₁ := h3
      _ ≤ 3 * (q ^ 1 * P) := Nat.mul_le_mul_left _ hcard
      _ = q * (3 * P) := by ring
  have key2 : q ^ 3 ≤ 3 * P := Nat.le_of_mul_le_mul_left key hpp.1.pos
  nlinarith [key2, sq_nonneg q, Nat.pos_of_ne_zero hpp.1.ne_zero]

theorem s16h_uniqueMax_or_dvd_of_blockBound_one (D : Data G) (h61 : UC6.R6_1 D)
    (h127 : R127 D) {V₀ V L : Subgroup G} (h : Setting16 D V₀ V L)
    (hs : s15 D.M V₀ V h.hyp151.isElemAbelian L = 3) {q : ℕ} (hq : q ∈ D.sig)
    (h4 : 4 ≤ CFSG.Open.pRank q D.M)
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
  · exact Or.inl (s16c34_uniqueMax_cent_of_mem_v0 D h61 h.hyp16 hq (by omega) hu0 hu1)
  · right
    have hu' := s16h_sup_le_preTil D h.hyp151 hv1 hx hy hu
    have huV : u ∈ V := preTil_le V₀ V hV _ hu'
    obtain ⟨E, hEM, hE, hEcard⟩ :=
      c23_exists_elemAbelian_card_pow (p := q) (M := D.M) (k := 4) hpp.1
        (by rw [UC6.groupPRank_eq_pRank]; exact h4)
    have hcard := s16h_card_le_sq_mul_card_inf_preBarSub_sup D h.hyp151 hs hpp.1 hpp.2 hBB hEM hE
      hx hy
    set P := (E ⊓ nBar D.M V₀ V hV L) ⊓ preBarSub D.M V₀ V hV (centSub (wTil V₀ V hV
      (conjSubgroup L x) ⊔ wTil V₀ V hV (conjSubgroup L y))) with hP
    have hPab : IsElemAbelian q P := hE.mono (inf_le_left.trans inf_le_left)
    haveI : Fact q.Prime := ⟨hpp.1⟩
    have hq3 : 3 ≤ q := by
      have := hpp.1.two_le
      have := hpp.2
      omega
    have hPne : Nat.card ↥P ≠ 1 := by
      intro h1
      rw [hEcard, h1] at hcard
      have h9 : 9 ≤ q ^ 2 := by nlinarith
      have hsq : q ^ 4 = q ^ 2 * q ^ 2 := by ring
      nlinarith [Nat.mul_le_mul_right (q ^ 2) h9]
    exact s16h_dvd_card_cent_of_cElt D h127 h.hyp16 hpp.1 hpp.2 huV hu0
      (inf_le_right.trans (s16h_preBarSub_le_cElt_of_le_centSub hV le_rfl hu'))
      (hPab.isPGroup.card_eq_or_dvd.resolve_left hPne)

theorem s16h_unique₂_of_unique₁_three (D : Data G) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    (hs : s15 D.M V₀ V h.isElemAbelian L = 3)
    (h1 : ∀ w ∈ wSub V₀ V h.isElemAbelian L ⊔ v1Sub D.M V₀ V h.isElemAbelian L, w ≠ 1 →
      UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G))) :
    ∀ x ∈ D.M, ∀ y ∈ D.M,
      conjSubgroup (wSub V₀ V h.isElemAbelian L) x ≠
        conjSubgroup (wSub V₀ V h.isElemAbelian L) y →
      ∀ w ∈ v1Sub D.M V₀ V h.isElemAbelian L ⊔
        ⨆ X ∈ {X | X ∈ wConj D.M V₀ V h.isElemAbelian L ∧
          X ≠ conjSubgroup (wSub V₀ V h.isElemAbelian L) x ∧
          X ≠ conjSubgroup (wSub V₀ V h.isElemAbelian L) y}, X,
      w ≠ 1 → UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
  have hV := h.isElemAbelian
  haveI : Finite (Subgroup G) := Finite.of_injective _ SetLike.coe_injective
  intro x hx y hy hxy w hw hw1
  have hcard : ({conjSubgroup (wSub V₀ V hV L) x, conjSubgroup (wSub V₀ V hV L) y} :
      Set (Subgroup G)).ncard < (wConj D.M V₀ V hV L).ncard := by
    rw [Set.ncard_pair hxy, ncard_wConj D h hV, hs]
    omega
  obtain ⟨Z, ⟨z, hz, rfl⟩, hZ⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hcard
  have hle : (⨆ X ∈ {X | X ∈ wConj D.M V₀ V hV L ∧
      X ≠ conjSubgroup (wSub V₀ V hV L) x ∧ X ≠ conjSubgroup (wSub V₀ V hV L) y}, X) ≤
      conjSubgroup (wSub V₀ V hV L) z := by
    refine iSup₂_le fun X hX => ?_
    obtain ⟨hXw, hXx, hXy⟩ := hX
    have hsub : ({X, conjSubgroup (wSub V₀ V hV L) x, conjSubgroup (wSub V₀ V hV L) y} :
        Set (Subgroup G)) ⊆ wConj D.M V₀ V hV L := by
      rintro T (rfl | rfl | rfl)
      · exact hXw
      · exact ⟨x, hx, rfl⟩
      · exact ⟨y, hy, rfl⟩
    have h3 : ({X, conjSubgroup (wSub V₀ V hV L) x, conjSubgroup (wSub V₀ V hV L) y} :
        Set (Subgroup G)).ncard = 3 :=
      Set.ncard_eq_three.2 ⟨X, _, _, hXx, hXy, hxy, rfl⟩
    have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [h3, ncard_wConj D h hV, hs])
      (Set.toFinite _)
    have hmem : conjSubgroup (wSub V₀ V hV L) z ∈
        ({X, conjSubgroup (wSub V₀ V hV L) x, conjSubgroup (wSub V₀ V hV L) y} :
          Set (Subgroup G)) := by
      rw [heq]
      exact ⟨z, hz, rfl⟩
    rcases hmem with h' | h' | h'
    · exact h'.ge
    · exact absurd h' (fun e => hZ (Or.inl e))
    · exact absurd h' (fun e => hZ (Or.inr e))
  have hv1z : conjSubgroup (v1Sub D.M V₀ V hV L) z = v1Sub D.M V₀ V hV L :=
    conjSubgroup_eq_iff_mem_normalizer.2 (s15_Infra_le_normalizer_v1Sub h.hyp125 hV hz)
  have hV1z : v1Sub D.M V₀ V hV L ≤ conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) z :=
    calc v1Sub D.M V₀ V hV L = conjSubgroup (v1Sub D.M V₀ V hV L) z := hv1z.symm
      _ ≤ conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) z :=
        Subgroup.map_mono le_sup_right
  have hmem : w ∈ conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) z :=
    (sup_le hV1z (Subgroup.map_mono le_sup_left)) (sup_le_sup_left hle _ hw)
  have hMz : conjSubgroup D.M z = D.M :=
    conjSubgroup_eq_iff_mem_normalizer.2 (Subgroup.le_normalizer hz)
  have hu := uniqueMax_conjSubgroup_of_mem (g := z) (M := D.M) h1 hmem hw1
  rwa [hMz] at hu

theorem s16h_inf_eq_bot_of_blockBound_one (D : Data G) (h61 : UC6.R6_1 D) (h127 : R127 D)
    {V₀ V L : Subgroup G} (h : Setting16 D V₀ V L)
    (hs : s15 D.M V₀ V h.hyp151.isElemAbelian L = 3) {q : ℕ} (hq : q ∈ D.sig)
    (hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded q D.M)
    (h4 : 4 ≤ CFSG.Open.pRank q D.M)
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
  have h1 := s16h_uniqueMax_of_blockBound_one D h61 h127 h hs.le hq h4 hBB
  exact s16h_inf_conjSubgroup_eq_bot_of_strong D.maxLocal
    (fun _ hg' => s16h_not_dvd_inf_conjSubgroup hsp hg')
    (s16h_isPGroup_two_of_le hV (sup_le (sup_le (s16h_wConj_le_v D h.hyp151 hX)
      (s16h_wConj_le_v D h.hyp151 hY)) hV1))
    (s16h_isPGroup_two_of_le hV (sup_le (preTil_le V₀ V hV _) hV1))
    (s16h_uniqueMax_or_dvd_of_blockBound_one D h61 h127 h hs hq h4 hv1 hBB hX hY)
    (s16h_unique₁_of_wSub D h.hyp151 hv1 h1) hg

theorem s16h_hyp154_of_blockBound_one (D : Data G) (h61 : UC6.R6_1 D) (h127 : R127 D)
    {V₀ V L : Subgroup G} (h : Setting16 D V₀ V L)
    (hs : s15 D.M V₀ V h.hyp151.isElemAbelian L = 3) {q : ℕ} (hq : q ∈ D.sig)
    (hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded q D.M)
    (h4 : 4 ≤ CFSG.Open.pRank q D.M)
    (hv1 : v1Sub D.M V₀ V h.hyp151.isElemAbelian L ≤ V₀)
    (hBB : s16h_BlockBound (Mbar D.M V₀ V h.hyp151.isElemAbelian)
      (barSub V₀ V h.hyp151.isElemAbelian L) q 1) :
    Hyp154 D V₀ V L := by
  have h1 := s16h_uniqueMax_of_blockBound_one D h61 h127 h hs.le hq h4 hBB
  have hU₁ := s16h_unique₁_of_wSub D h.hyp151 hv1 h1
  refine ⟨h.hyp151, hU₁, s16h_unique₂_of_unique₁_three D h.hyp151 hs hU₁, ?_⟩
  intro g hg X hX Y hY _ hne
  exact absurd (s16h_inf_eq_bot_of_blockBound_one D h61 h127 h hs hq hsp h4 hv1 hBB hg hX hY) hne

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
