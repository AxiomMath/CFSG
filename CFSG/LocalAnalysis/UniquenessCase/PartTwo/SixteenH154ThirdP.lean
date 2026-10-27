module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154CritO2Hyp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154UNt
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Bar

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_exists_conj_not_mem_pair (D : Data G) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    (hs : 2 < s15 D.M V₀ V h.isElemAbelian L) {X Y : Subgroup G}
    (hX : X ∈ wConj D.M V₀ V h.isElemAbelian L) (hY : Y ∈ wConj D.M V₀ V h.isElemAbelian L) :
    ∃ z ∈ D.M, conjSubgroup (wSub V₀ V h.isElemAbelian L) z ≠ X ∧
      conjSubgroup (wSub V₀ V h.isElemAbelian L) z ≠ Y := by
  have hV := h.isElemAbelian
  haveI : Finite (Subgroup G) := Finite.of_injective _ SetLike.coe_injective
  have h2 : ({X, Y} : Set (Subgroup G)).ncard ≤ 2 := by
    have hle := Set.ncard_insert_le X ({Y} : Set (Subgroup G))
    rw [Set.ncard_singleton] at hle
    simpa using hle
  have hcard : ({X, Y} : Set (Subgroup G)).ncard < (wConj D.M V₀ V hV L).ncard := by
    rw [ncard_wConj D h hV]
    omega
  obtain ⟨Z, ⟨z, hz, rfl⟩, hZnot⟩ :=
    Set.exists_mem_notMem_of_ncard_lt_ncard hcard (Set.toFinite _)
  exact ⟨z, hz, (fun heq => hZnot (by rw [heq]; simp)), fun heq => hZnot (by rw [heq]; simp)⟩

theorem s16h_dvd_card_cent_of_mem_sup (D : Data G) (h127 : R127 D) {V₀ V L : Subgroup G}
    (h : Setting16 D V₀ V L) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hqL : q ∣ Nat.card ↥(barSub V₀ V h.hyp151.isElemAbelian L)) {X Y : Subgroup G}
    (hX : X ∈ wConj D.M V₀ V h.hyp151.isElemAbelian L)
    (hY : Y ∈ wConj D.M V₀ V h.hyp151.isElemAbelian L) {z : G} (hz : z ∈ D.M)
    (hzX : conjSubgroup (wSub V₀ V h.hyp151.isElemAbelian L) z ≠ X)
    (hzY : conjSubgroup (wSub V₀ V h.hyp151.isElemAbelian L) z ≠ Y) {u : G}
    (hu : u ∈ X ⊔ Y ⊔ v1Sub D.M V₀ V h.hyp151.isElemAbelian L) (hu0 : u ∉ V₀) :
    q ∣ Nat.card ↥(D.M ⊓ centralizer ({u} : Set G)) := by
  have hV := h.hyp151.isElemAbelian
  have hV1 : v1Sub D.M V₀ V hV L ≤ V := s15_Infra_v1Sub_le (L := L) h.hyp151.hyp125 hV
  have huV : u ∈ V :=
    (sup_le (sup_le (s16h_wConj_le_v D h.hyp151 hX) (s16h_wConj_le_v D h.hyp151 hY)) hV1) hu
  have hS : ∀ Z ∈ ({X, Y} : Set (Subgroup G)),
      Z ∈ wConj D.M V₀ V hV L ∧ Z ≠ conjSubgroup (wSub V₀ V hV L) z := by
    intro Z hZ
    rcases hZ with hZX | hZY
    · rw [hZX]; exact ⟨hX, hzX.symm⟩
    · rw [hZY]; exact ⟨hY, hzY.symm⟩
  have hle0 := s16h_le_preTil_fixV_of_ne D h.hyp151 hz (S := ({X, Y} : Set (Subgroup G))) hS
  have hleXY : X ⊔ Y ≤ ⨆ Z ∈ ({X, Y} : Set (Subgroup G)), Z :=
    sup_le (le_iSup₂_of_le X (by simp) le_rfl) (le_iSup₂_of_le Y (by simp) le_rfl)
  have hsup : X ⊔ Y ⊔ v1Sub D.M V₀ V hV L ≤
      v1Sub D.M V₀ V hV L ⊔ ⨆ Z ∈ ({X, Y} : Set (Subgroup G)), Z :=
    sup_le (hleXY.trans le_sup_right) le_sup_left
  have huPre : u ∈ preTil V₀ V hV (fixV (barSub V₀ V hV (conjSubgroup L z))) := hle0 (hsup hu)
  have hP : conjSubgroup L z ≤ F11.CElt D.M V₀ u :=
    s16h_conjSubgroup_le_celt_of_barSub_le (K := L) h.hyp151.hyp125 h.hyp151.le le_rfl hz huPre
  have hqP : q ∣ Nat.card ↥(conjSubgroup L z) := by
    refine hqL.trans ?_
    rw [E3.card_conjSubgroup]
    exact c8_card_barSub_dvd V₀ V hV L
  exact s16h_dvd_card_cent_of_cElt D h127 h.hyp16 hq hq2 huV hu0 hP hqP

theorem s16h_hyp154_of_condU2_dvd (D : Data G) (h61 : UC6.R6_1 D) (h127 : R127 D)
    {V₀ V L : Subgroup G} (h : Setting16 D V₀ V L)
    (hσ : ∃ p ∈ D.sig, 3 ≤ CFSG.Open.pRank p D.M)
    (hU : s16h_CondU2 D V₀ V L h.hyp151.isElemAbelian)
    (hs : 2 < s15 D.M V₀ V h.hyp151.isElemAbelian L) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded q D.M)
    (hqL : q ∣ Nat.card ↥(barSub V₀ V h.hyp151.isElemAbelian L)) : Hyp154 D V₀ V L := by
  have hV := h.hyp151.isElemAbelian
  have hV1 : v1Sub D.M V₀ V hV L ≤ V := s15_Infra_v1Sub_le (L := L) h.hyp151.hyp125 hV
  have h1 := s16h_unique₁_of_condU2 D h61 h hσ hU hs
  have h2 := s16h_unique₂_of_condU2 D h61 h hσ hU
  refine ⟨h.hyp151, h1, h2, ?_⟩
  intro g hg X hX Y hY _ hne
  obtain ⟨z, hz, hzX, hzY⟩ := s16h_exists_conj_not_mem_pair D h.hyp151 hs hX hY
  have h₁ : IsPGroup 2 ↥(X ⊔ Y ⊔ v1Sub D.M V₀ V hV L) :=
    s16h_isPGroup_two_of_le hV (sup_le (sup_le (s16h_wConj_le_v D h.hyp151 hX)
      (s16h_wConj_le_v D h.hyp151 hY)) hV1)
  have h₂ : IsPGroup 2 ↥(wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) :=
    s16h_isPGroup_two_of_le hV (sup_le (preTil_le V₀ V hV _) hV1)
  have hU₂ := s16h_unique₁_of_condU2 D h61 h hσ hU hs
  have hU₁ : ∀ u ∈ X ⊔ Y ⊔ v1Sub D.M V₀ V hV L, u ≠ 1 →
      UniqueMax D.M (D.M ⊓ centralizer ({u} : Set G)) ∨
        q ∣ Nat.card ↥(D.M ⊓ centralizer ({u} : Set G)) := by
    intro u hu hu1
    by_cases hu0 : u ∈ V₀
    · exact Or.inl (s16h_v0_good D h61 h.hyp16 hσ u hu0 hu1)
    · exact Or.inr (s16h_dvd_card_cent_of_mem_sup D h127 h hq hq2 hqL hX hY hz hzX hzY hu hu0)
  exact absurd (s16h_inf_conjSubgroup_eq_bot_of_strong D.maxLocal
    (fun _ hg' => s16h_not_dvd_inf_conjSubgroup hsp hg') h₁ h₂ hU₁ hU₂ hg) hne

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
