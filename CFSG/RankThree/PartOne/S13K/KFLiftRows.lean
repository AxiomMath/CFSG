module

public import CFSG.RankThree.PartOne.S13K.KFLift
public import CFSG.RankThree.PartOne.S13K.KF136At
public import CFSG.RankThree.PartOne.S13K.Reinst
public import CFSG.RankThree.PartOne.KF.U4Multiplier

public section

namespace CFSG.RankThree.PartOne.S13K

open CFSG CFSG.Assembly CFSG.RankThree.PartOne CFSG.RankThree.GroupTheory
  CFSG.Assembly.LowTwoRank

theorem isQuasisimple_and_center_of_model_psl_two {X : Type} [Group X] {f : ℕ}
    (h : StatedClassicalModel X .PSL 2 2 f) :
    CFSG.IsQuasisimple X ∧ Subgroup.center X = ⊥ := by
  obtain ⟨hadm, K, hK, hKfin, hcard, ⟨e⟩⟩ := h
  obtain ⟨-, hf1, -, h22, -⟩ := hadm
  have hf2 : 2 ≤ f := by
    by_contra hlt
    have hf1' : f = 1 := by omega
    subst hf1'
    exact h22 rfl
  have hch : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hcard
  obtain ⟨e'⟩ := CFSG.RankThree.PartOne.KFU.nonempty_SL2_mulEquiv_statedProj (F := K)
  have hq : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  have h4 : ∃ s : Finset K, s.card = 4 := by
    have := Fintype.ofFinite K
    have hle : 4 ≤ (Finset.univ : Finset K).card := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hcard]
      exact hq
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq hle
    exact ⟨s, hs⟩
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (e'.trans e.symm)
    (CFSG.RankThree.Classical.isQuasisimple_SL2 h4), ?_⟩
  rw [← Subgroup.map_center_eq (e'.trans e.symm), CFSG.RankThree.PartOne.KFU.center_SL2_eq_bot,
    Subgroup.map_bot]

theorem isQuasisimple_of_model_psl_two {X : Type} [Group X] {f : ℕ}
    (h : StatedClassicalModel X .PSL 2 2 f) : CFSG.IsQuasisimple X :=
  (isQuasisimple_and_center_of_model_psl_two h).1

theorem KFAt.toLiftAt {G : Type} [Group G] {p : ℕ} {E : Subgroup G} {f : ℕ} {t : MulAut E}
    (h : KFAt p E f t) : KFLiftAt p E t := by
  obtain ⟨hne, hmod, -, hmoved, k, hk, hkK, hkt⟩ := h
  exact ⟨(isQuasisimple_and_center_of_model_psl_two hmod).1,
    (isQuasisimple_and_center_of_model_psl_two hmod).2, hne, hmoved, k, hk, hkK, hkt⟩

theorem card_E_of_ne {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G}
    {L E : Subgroup G} (hF : Sec12Facts G p A c L E) (hEA : E ≠ A) : Nat.card E = p ^ 4 := by
  obtain ⟨-, r, -, -, -, -, hr8, hr9⟩ := hF.three
  refine hr9 ?_
  by_contra hlt
  exact hEA (hr8 (by omega))

theorem kfLiftRow9_holds (hGA : CFSG.Open.GriessAllModelsStatement) :
    KFLiftRow 9 := by
  intro G _ _ p A c L E h hF hEA hrow t ht htL
  obtain ⟨f, hf, hpq, hmodel⟩ := hrow
  have h1 : KFAt p E f t := (kf126U4_of_multipliers hGA G p A c L E f h hF hf hpq hmodel
    (card_E_of_ne hF hEA)).1 t ht htL
  exact KFAt.toLiftAt (p := p) (E := E) (f := f) (t := t) h1

theorem kfLiftRow10_holds (hGA : CFSG.Open.GriessAllModelsStatement) :
    KFLiftRow 10 := by
  intro G _ _ p A c L E h hF hEA hrow t ht htL
  obtain ⟨f, hf, hpq, hmodel⟩ := hrow
  exact KFAt.toLiftAt (p := p) (E := E) (f := f) (t := t)
    (kfAt_row10 hGA h hF hEA hf hpq hmodel t ht htL)

theorem kfLiftAll_of_rows (h1 : KFLiftRowOne) (h9 : KFLiftRow 9) (h10 : KFLiftRow 10)
    (h11 : KFLiftRow 11) (h12 : KFLiftRow 12) : KFLiftAll := by
  intro G _ _ p A c L E h hF hF13 hT hcase t ht
  obtain ⟨hrefl, X, hX, htX⟩ := ht
  have ht' : t ∈ reflectionSet p E := ⟨hrefl, X, hX, htX⟩
  obtain ⟨B, c', hB, hc'B, hc'1, h', hF'⟩ := hF13.reinstantiate X hX
  obtain ⟨-, r, hr1, hr12, hrow, -, hr8, -⟩ := hF'.three
  have hBE : B ≤ E := hB.1
  have hBcard : Nat.card B = p ^ 3 := hB.2.2.1
  rcases hcase with hEA | ⟨hEA, hall⟩
  · have hEB : E ≠ B := by
      intro hEB
      apply hEA
      refine (Subgroup.eq_of_le_of_card_ge h.A_le_E (le_of_eq ?_)).symm
      rw [h.A_card, ← hBcard, hEB]
    have hr9 : 9 ≤ r := by
      by_contra hlt
      exact hEB (hr8 (by omega))
    interval_cases r
    · exact h9 G p B c' X E h' hF' hEB hrow t ht' htX
    · exact h10 G p B c' X E h' hF' hEB hrow t ht' htX
    · exact h11 G p B c' X E h' hF' hEB hrow t ht' htX
    · exact h12 G p B c' X E h' hF' hEB hrow t ht' htX
  · have hBA : B = A := by
      refine Subgroup.eq_of_le_of_card_ge (hEA ▸ hBE) (le_of_eq ?_)
      rw [h.A_card, hBcard]
    have hXz : X ∈ sectionTenZeroStar p A := hBA ▸ CFSG.RankThree.PartOne.Sec12Three.L_mem_zeroStar h'
    exact h1 G p B c' X E h' hF' (hEA.trans hBA.symm) (hall X hXz) t ht' htX

theorem kf132Types_row9 (hGA : CFSG.Open.GriessAllModelsStatement) :
    KF132Types 9 := by
  intro G _ _ p A c L E h hF _ _ hrow _ hE4 t ht htL K hK
  obtain ⟨f, hf, hpq, hmodel⟩ := hrow
  have h1 : KFAt p E f t := (kf126U4_of_multipliers hGA G p A c L E f h hF hf hpq hmodel
    (hE4 (by norm_num))).1 t ht htL
  have hKeq : K = kZero p E t := hK.2 h1.1
  refine ⟨f, ⟨hf, hpq, hmodel⟩, ?_, fun h8 => absurd h8 (by norm_num)⟩
  rw [hKeq]
  exact h1.2.1

theorem kf132Types_row10 (hGA : CFSG.Open.GriessAllModelsStatement) :
    KF132Types 10 := by
  intro G _ _ p A c L E h hF _ _ hrow _ hE4 t ht htL K hK
  obtain ⟨f, hf, hpq, hmodel⟩ := hrow
  have h1 : KFAt p E f t := kfAt_row10 hGA h hF (ne_of_card_E h (hE4 (by norm_num))) hf hpq hmodel
    t ht htL
  have hKeq : K = kZero p E t := hK.2 h1.1
  refine ⟨f, ⟨hf, hpq, hmodel⟩, ?_, fun h8 => absurd h8 (by norm_num)⟩
  rw [hKeq]
  exact h1.2.1

end CFSG.RankThree.PartOne.S13K
