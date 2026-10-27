module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.ConjRank857
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22wb
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Mult
public import CFSG.Timmesfeld.Final.Simple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08
open CFSG.Blueprint (LieModel)


theorem not_threeCover_PSL5 {X : Type} [Group X] [Finite X]
    (hq : CFSG.Open.IsQuasisimple X) {p f : ℕ}
    (hS : LieModel (X ⧸ Subgroup.center X) .PSL 5 p f) :
    Nat.card (Subgroup.center X) ≠ 3 := by
  intro hZ
  haveI : Group.IsPerfect X := ⟨hq.1⟩
  have hmod : CFSG.Open.StatedClassicalModel (X ⧸ Subgroup.center X) .PSL 5 p f :=
    LieModel.statedClassicalModel hS (by decide)
  obtain ⟨-, ⟨e⟩⟩ := CFSG.LieType.Steinberg.CentralExt.GriessClassical.psl_row hmod
  have hdvd :=
    CFSG.ComponentClassification.CatFactsL4U4.Cover82.Mult.card_center_dvd_hopfMultiplier
      (S := X ⧸ Subgroup.center X) (Q := X) (MulEquiv.refl _)
  rw [Nat.card_congr e.toEquiv] at hdvd
  have hgen : CFSG.Blueprint.Multiplier.genericOrders .PSL 5 p f =
      (Nat.gcd 5 (p ^ f - 1), 1) := rfl
  have hex : CFSG.Blueprint.Multiplier.exceptionalOrders .PSL 5 p f = (1, 1) := by
    unfold CFSG.Blueprint.Multiplier.exceptionalOrders
    split <;> simp_all
  have hz (n : ℕ) : Nat.card (Multiplicative (ZMod n)) = n := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have hcard : Nat.card (CFSG.Blueprint.Multiplier.generic .PSL 5 p f ×
      CFSG.Blueprint.Multiplier.exceptional .PSL 5 p f) = Nat.gcd 5 (p ^ f - 1) := by
    simp [CFSG.Blueprint.Multiplier.generic, CFSG.Blueprint.Multiplier.exceptional, hgen, hex, hz]
  rw [hcard] at hdvd
  have h3 : 3 ∣ Nat.gcd 5 (p ^ f - 1) := hZ ▸ hdvd
  have h5 : Nat.gcd 5 (p ^ f - 1) ∣ 5 := Nat.gcd_dvd_left _ _
  have := h3.trans h5
  norm_num at this

theorem not_threeCover_PSU5 {X : Type} [Group X] [Finite X]
    (hq : CFSG.Open.IsQuasisimple X) {p f : ℕ}
    (hS : LieModel (X ⧸ Subgroup.center X) .PSU 5 p f) :
    Nat.card (Subgroup.center X) ≠ 3 := by
  intro hZ
  haveI : Group.IsPerfect X := ⟨hq.1⟩
  have hmod : CFSG.Open.StatedClassicalModel (X ⧸ Subgroup.center X) .PSU 5 p f :=
    LieModel.statedClassicalModel hS (by decide)
  obtain ⟨-, ⟨e⟩⟩ :=
    CFSG.LieType.Steinberg.CentralExt.GriessClassical.psu_odd_row hmod (by norm_num)
  have hdvd :=
    CFSG.ComponentClassification.CatFactsL4U4.Cover82.Mult.card_center_dvd_hopfMultiplier
      (S := X ⧸ Subgroup.center X) (Q := X) (MulEquiv.refl _)
  rw [Nat.card_congr e.toEquiv] at hdvd
  have hgen : CFSG.Blueprint.Multiplier.genericOrders .PSU 5 p f =
      (Nat.gcd 5 (p ^ f + 1), 1) := rfl
  have hex : CFSG.Blueprint.Multiplier.exceptionalOrders .PSU 5 p f = (1, 1) := by
    unfold CFSG.Blueprint.Multiplier.exceptionalOrders
    split <;> simp_all
  have hz (n : ℕ) : Nat.card (Multiplicative (ZMod n)) = n := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have hcard : Nat.card (CFSG.Blueprint.Multiplier.generic .PSU 5 p f ×
      CFSG.Blueprint.Multiplier.exceptional .PSU 5 p f) = Nat.gcd 5 (p ^ f + 1) := by
    simp [CFSG.Blueprint.Multiplier.generic, CFSG.Blueprint.Multiplier.exceptional, hgen, hex, hz]
  rw [hcard] at hdvd
  have h3 : 3 ∣ Nat.gcd 5 (p ^ f + 1) := hZ ▸ hdvd
  have h5 : Nat.gcd 5 (p ^ f + 1) ∣ 5 := Nat.gcd_dvd_left _ _
  have := h3.trans h5
  norm_num at this

theorem center_card_le_three_and_center_three_imp_of_list857 {G : Type} [Group G] [Finite G]
    {M L : Subgroup G} (hL : L ∈ calC M) (hlist : List857 (Bar2 L)) :
    Nat.card (Subgroup.center (Bar2 L)) ≤ 3 ∧
      (3 ∣ Nat.card (Subgroup.center (Bar2 L)) →
        IsA6Z3 (Bar2 L) ∨ IsA7Z3 (Bar2 L) ∨ IsM22Z3 (Bar2 L)) := by
  have hq : CFSG.Open.IsQuasisimple (Bar2 L) := hL.2.2
  unfold List857 at hlist
  rcases hlist with h1 | h2 | h3
  · rcases h1 with h | h | h | h | h | h | h | h | h | h | h
    ·
      obtain ⟨p, f, -, h⟩ := h
      haveI : IsSimpleGroup (Bar2 L) := CFSG.Timmesfeld.isSimpleGroup_of_lieModel h
      have hZ : Subgroup.center (Bar2 L) = ⊥ :=
        CFSG.LocalAnalysis.UniquenessCase.UC22.P22w.center_eq_bot_of_isSimpleGroup hq
      refine ⟨?_, fun h3 => ?_⟩
      · rw [hZ, Subgroup.card_bot]
        norm_num
      · rw [hZ, Subgroup.card_bot] at h3
        norm_num at h3
    ·
      obtain ⟨p, f, -, h⟩ := h
      haveI : IsSimpleGroup (Bar2 L) := CFSG.Timmesfeld.isSimpleGroup_of_lieModel h
      have hZ : Subgroup.center (Bar2 L) = ⊥ :=
        CFSG.LocalAnalysis.UniquenessCase.UC22.P22w.center_eq_bot_of_isSimpleGroup hq
      refine ⟨?_, fun h3 => ?_⟩
      · rw [hZ, Subgroup.card_bot]
        norm_num
      · rw [hZ, Subgroup.card_bot] at h3
        norm_num at h3
    ·
      obtain ⟨p, f, -, h | h⟩ := h
      · haveI : IsSimpleGroup (Bar2 L) := CFSG.Timmesfeld.isSimpleGroup_of_lieModel h
        have hZ : Subgroup.center (Bar2 L) = ⊥ :=
          CFSG.LocalAnalysis.UniquenessCase.UC22.P22w.center_eq_bot_of_isSimpleGroup hq
        refine ⟨?_, fun h3 => ?_⟩
        · rw [hZ, Subgroup.card_bot]
          norm_num
        · rw [hZ, Subgroup.card_bot] at h3
          norm_num at h3
      · refine ⟨center_card_le_three_of_threeCover h, fun _ => ?_⟩
        exact False.elim (not_threeCover_PSL5 hq h.2.2 h.2.1)
    ·
      obtain ⟨p, f, -, h | h⟩ := h
      · haveI : IsSimpleGroup (Bar2 L) := CFSG.Timmesfeld.isSimpleGroup_of_lieModel h
        have hZ : Subgroup.center (Bar2 L) = ⊥ :=
          CFSG.LocalAnalysis.UniquenessCase.UC22.P22w.center_eq_bot_of_isSimpleGroup hq
        refine ⟨?_, fun h3 => ?_⟩
        · rw [hZ, Subgroup.card_bot]
          norm_num
        · rw [hZ, Subgroup.card_bot] at h3
          norm_num at h3
      · refine ⟨center_card_le_three_of_threeCover h, fun _ => ?_⟩
        exact False.elim (not_threeCover_PSU5 hq h.2.2 h.2.1)
    ·
      obtain ⟨p, f, h⟩ := h
      haveI : IsSimpleGroup (Bar2 L) := CFSG.Timmesfeld.isSimpleGroup_of_lieModel h
      have hZ : Subgroup.center (Bar2 L) = ⊥ :=
        CFSG.LocalAnalysis.UniquenessCase.UC22.P22w.center_eq_bot_of_isSimpleGroup hq
      refine ⟨?_, fun h3 => ?_⟩
      · rw [hZ, Subgroup.card_bot]
        norm_num
      · rw [hZ, Subgroup.card_bot] at h3
        norm_num at h3
    ·
      obtain ⟨e⟩ := h
      haveI : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .M11) :=
        CFSG.Sporadic.Mathieu.fam_m11_simplicity.2.2
      haveI : IsSimpleGroup (Bar2 L) := e.isSimpleGroup
      have hZ : Subgroup.center (Bar2 L) = ⊥ :=
        CFSG.LocalAnalysis.UniquenessCase.UC22.P22w.center_eq_bot_of_isSimpleGroup hq
      refine ⟨?_, fun h3 => ?_⟩
      · rw [hZ, Subgroup.card_bot]
        norm_num
      · rw [hZ, Subgroup.card_bot] at h3
        norm_num at h3
    ·
      obtain ⟨e⟩ := h
      haveI : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .M22) :=
        CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
      haveI : IsSimpleGroup (Bar2 L) := e.isSimpleGroup
      have hZ : Subgroup.center (Bar2 L) = ⊥ :=
        CFSG.LocalAnalysis.UniquenessCase.UC22.P22w.center_eq_bot_of_isSimpleGroup hq
      refine ⟨?_, fun h3 => ?_⟩
      · rw [hZ, Subgroup.card_bot]
        norm_num
      · rw [hZ, Subgroup.card_bot] at h3
        norm_num at h3
    ·
      obtain ⟨e⟩ := h
      haveI : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .M23) :=
        CFSG.Sporadic.Mathieu.fam_m23_simplicity.2.2
      haveI : IsSimpleGroup (Bar2 L) := e.isSimpleGroup
      have hZ : Subgroup.center (Bar2 L) = ⊥ :=
        CFSG.LocalAnalysis.UniquenessCase.UC22.P22w.center_eq_bot_of_isSimpleGroup hq
      refine ⟨?_, fun h3 => ?_⟩
      · rw [hZ, Subgroup.card_bot]
        norm_num
      · rw [hZ, Subgroup.card_bot] at h3
        norm_num at h3
    ·
      obtain ⟨e⟩ := h
      haveI : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .HS) :=
        CFSG.Sporadic.HS.isSimpleGroup_HS
      haveI : IsSimpleGroup (Bar2 L) := e.isSimpleGroup
      have hZ : Subgroup.center (Bar2 L) = ⊥ :=
        CFSG.LocalAnalysis.UniquenessCase.UC22.P22w.center_eq_bot_of_isSimpleGroup hq
      refine ⟨?_, fun h3 => ?_⟩
      · rw [hZ, Subgroup.card_bot]
        norm_num
      · rw [hZ, Subgroup.card_bot] at h3
        norm_num at h3
    ·
      obtain ⟨e⟩ := h
      haveI : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
      haveI : IsSimpleGroup (Bar2 L) := e.isSimpleGroup
      have hZ : Subgroup.center (Bar2 L) = ⊥ :=
        CFSG.LocalAnalysis.UniquenessCase.UC22.P22w.center_eq_bot_of_isSimpleGroup hq
      refine ⟨?_, fun h3 => ?_⟩
      · rw [hZ, Subgroup.card_bot]
        norm_num
      · rw [hZ, Subgroup.card_bot] at h3
        norm_num at h3
    ·
      obtain ⟨e⟩ := h
      haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
      haveI : IsSimpleGroup (Bar2 L) := e.isSimpleGroup
      have hZ : Subgroup.center (Bar2 L) = ⊥ :=
        CFSG.LocalAnalysis.UniquenessCase.UC22.P22w.center_eq_bot_of_isSimpleGroup hq
      refine ⟨?_, fun h3 => ?_⟩
      · rw [hZ, Subgroup.card_bot]
        norm_num
      · rw [hZ, Subgroup.card_bot] at h3
        norm_num at h3
  · rcases h2 with h | h | h
    ·
      refine ⟨le_of_eq h.2.1, fun _ => ?_⟩
      exact Or.inl h
    ·
      refine ⟨le_of_eq h.2.1, fun _ => ?_⟩
      exact Or.inr (Or.inl h)
    ·
      refine ⟨le_of_eq h.2.1, fun _ => ?_⟩
      exact Or.inr (Or.inr h)
  · rcases h3 with h | h | h | h | h | h | h | h | h | h | h | h
    ·
      haveI : IsSimpleGroup (Bar2 L) := CFSG.Timmesfeld.isSimpleGroup_of_lieModel h
      have hZ : Subgroup.center (Bar2 L) = ⊥ :=
        CFSG.LocalAnalysis.UniquenessCase.UC22.P22w.center_eq_bot_of_isSimpleGroup hq
      refine ⟨?_, fun h3 => ?_⟩
      · rw [hZ, Subgroup.card_bot]
        norm_num
      · rw [hZ, Subgroup.card_bot] at h3
        norm_num at h3
    ·
      obtain ⟨p, f, h⟩ := h
      haveI : IsSimpleGroup (Bar2 L) := CFSG.Timmesfeld.isSimpleGroup_of_lieModel h
      have hZ : Subgroup.center (Bar2 L) = ⊥ :=
        CFSG.LocalAnalysis.UniquenessCase.UC22.P22w.center_eq_bot_of_isSimpleGroup hq
      refine ⟨?_, fun h3 => ?_⟩
      · rw [hZ, Subgroup.card_bot]
        norm_num
      · rw [hZ, Subgroup.card_bot] at h3
        norm_num at h3
    ·
      haveI : IsSimpleGroup (Bar2 L) := CFSG.Timmesfeld.isSimpleGroup_of_lieModel h
      have hZ : Subgroup.center (Bar2 L) = ⊥ :=
        CFSG.LocalAnalysis.UniquenessCase.UC22.P22w.center_eq_bot_of_isSimpleGroup hq
      refine ⟨?_, fun h3 => ?_⟩
      · rw [hZ, Subgroup.card_bot]
        norm_num
      · rw [hZ, Subgroup.card_bot] at h3
        norm_num at h3
    ·
      obtain ⟨p, f, h⟩ := h
      haveI : IsSimpleGroup (Bar2 L) := CFSG.Timmesfeld.isSimpleGroup_of_lieModel h
      have hZ : Subgroup.center (Bar2 L) = ⊥ :=
        CFSG.LocalAnalysis.UniquenessCase.UC22.P22w.center_eq_bot_of_isSimpleGroup hq
      refine ⟨?_, fun h3 => ?_⟩
      · rw [hZ, Subgroup.card_bot]
        norm_num
      · rw [hZ, Subgroup.card_bot] at h3
        norm_num at h3
    ·
      obtain ⟨f, h⟩ := h
      haveI : IsSimpleGroup (Bar2 L) := CFSG.Timmesfeld.isSimpleGroup_of_lieModel h
      have hZ : Subgroup.center (Bar2 L) = ⊥ :=
        CFSG.LocalAnalysis.UniquenessCase.UC22.P22w.center_eq_bot_of_isSimpleGroup hq
      refine ⟨?_, fun h3 => ?_⟩
      · rw [hZ, Subgroup.card_bot]
        norm_num
      · rw [hZ, Subgroup.card_bot] at h3
        norm_num at h3
    ·
      haveI : IsSimpleGroup (Bar2 L) := CFSG.Timmesfeld.isSimpleGroup_of_lieModel h
      have hZ : Subgroup.center (Bar2 L) = ⊥ :=
        CFSG.LocalAnalysis.UniquenessCase.UC22.P22w.center_eq_bot_of_isSimpleGroup hq
      refine ⟨?_, fun h3 => ?_⟩
      · rw [hZ, Subgroup.card_bot]
        norm_num
      · rw [hZ, Subgroup.card_bot] at h3
        norm_num at h3
    ·
      obtain ⟨e⟩ := h
      haveI : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .J2) :=
        CFSG.Sporadic.J2.isSimpleGroup_J2
      haveI : IsSimpleGroup (Bar2 L) := e.isSimpleGroup
      have hZ : Subgroup.center (Bar2 L) = ⊥ :=
        CFSG.LocalAnalysis.UniquenessCase.UC22.P22w.center_eq_bot_of_isSimpleGroup hq
      refine ⟨?_, fun h3 => ?_⟩
      · rw [hZ, Subgroup.card_bot]
        norm_num
      · rw [hZ, Subgroup.card_bot] at h3
        norm_num at h3
    ·
      obtain ⟨e⟩ := h
      haveI : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .He) :=
        CFSG.Sporadic.He.isSimpleGroup_He
      haveI : IsSimpleGroup (Bar2 L) := e.isSimpleGroup
      have hZ : Subgroup.center (Bar2 L) = ⊥ :=
        CFSG.LocalAnalysis.UniquenessCase.UC22.P22w.center_eq_bot_of_isSimpleGroup hq
      refine ⟨?_, fun h3 => ?_⟩
      · rw [hZ, Subgroup.card_bot]
        norm_num
      · rw [hZ, Subgroup.card_bot] at h3
        norm_num at h3
    ·
      obtain ⟨e⟩ := h
      haveI : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .Ru) :=
        CFSG.Sporadic.Ru.isSimpleGroup_Ru
      haveI : IsSimpleGroup (Bar2 L) := e.isSimpleGroup
      have hZ : Subgroup.center (Bar2 L) = ⊥ :=
        CFSG.LocalAnalysis.UniquenessCase.UC22.P22w.center_eq_bot_of_isSimpleGroup hq
      refine ⟨?_, fun h3 => ?_⟩
      · rw [hZ, Subgroup.card_bot]
        norm_num
      · rw [hZ, Subgroup.card_bot] at h3
        norm_num at h3
    ·
      obtain ⟨e⟩ := h
      haveI : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .J4) :=
        CFSG.Sporadic.J4.isSimpleGroup_J4
      haveI : IsSimpleGroup (Bar2 L) := e.isSimpleGroup
      have hZ : Subgroup.center (Bar2 L) = ⊥ :=
        CFSG.LocalAnalysis.UniquenessCase.UC22.P22w.center_eq_bot_of_isSimpleGroup hq
      refine ⟨?_, fun h3 => ?_⟩
      · rw [hZ, Subgroup.card_bot]
        norm_num
      · rw [hZ, Subgroup.card_bot] at h3
        norm_num at h3
    ·
      obtain ⟨e⟩ := h
      haveI : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .M12) :=
        CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
      haveI : IsSimpleGroup (Bar2 L) := e.isSimpleGroup
      have hZ : Subgroup.center (Bar2 L) = ⊥ :=
        CFSG.LocalAnalysis.UniquenessCase.UC22.P22w.center_eq_bot_of_isSimpleGroup hq
      refine ⟨?_, fun h3 => ?_⟩
      · rw [hZ, Subgroup.card_bot]
        norm_num
      · rw [hZ, Subgroup.card_bot] at h3
        norm_num at h3
    ·
      obtain ⟨e⟩ := h
      haveI : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .M24) :=
        CFSG.Sporadic.Mathieu.fam_m24_simplicity.2.2
      haveI : IsSimpleGroup (Bar2 L) := e.isSimpleGroup
      have hZ : Subgroup.center (Bar2 L) = ⊥ :=
        CFSG.LocalAnalysis.UniquenessCase.UC22.P22w.center_eq_bot_of_isSimpleGroup hq
      refine ⟨?_, fun h3 => ?_⟩
      · rw [hZ, Subgroup.card_bot]
        norm_num
      · rw [hZ, Subgroup.card_bot] at h3
        norm_num at h3
theorem center_card_le_three_of_list857 {G : Type} [Group G] [Finite G]
    {M L : Subgroup G} (hL : L ∈ calC M) (hlist : List857 (Bar2 L)) :
    Nat.card (Subgroup.center (Bar2 L)) ≤ 3 :=
  (center_card_le_three_and_center_three_imp_of_list857 hL hlist).1

theorem center_three_imp_of_list857 {G : Type} [Group G] [Finite G]
    {M L : Subgroup G} (hL : L ∈ calC M) (hlist : List857 (Bar2 L))
    (h3 : 3 ∣ Nat.card (Subgroup.center (Bar2 L))) :
    IsA6Z3 (Bar2 L) ∨ IsA7Z3 (Bar2 L) ∨ IsM22Z3 (Bar2 L) :=
  (center_card_le_three_and_center_three_imp_of_list857 hL hlist).2 h3

theorem four_le_pRank_three_of_three_conj_list857 {G : Type} [Group G] [Finite G]
    {M L L1 L2 L3 : Subgroup G}
    (hL : L ∈ calC M)
    (h1 : L1 ∈ conjSetOf M L) (h2 : L2 ∈ conjSetOf M L) (h3 : L3 ∈ conjSetOf M L)
    (h12 : L1 ≠ L2) (h13 : L1 ≠ L3) (h23 : L2 ≠ L3)
    (hr : CFSG.Open.pRank 3 L = 2)
    (hlist : List857 (Bar2 L)) :
    4 ≤ CFSG.Open.pRank 3 M :=
  four_le_pRank_three_of_three_conj_list857_of_center hL h1 h2 h3 h12 h13 h23 hr hlist
    (center_card_le_three_of_list857 hL hlist)

theorem ncard_conjSetOf_le_two_of_list857 {G : Type} [Group G] [Finite G]
    {M L : Subgroup G} (hL : L ∈ calC M)
    (hr : CFSG.Open.pRank 3 L = 2) (hlist : List857 (Bar2 L))
    (hm3 : CFSG.Open.pRank 3 M ≤ 3) :
    (conjSetOf M L).ncard ≤ 2 :=
  ncard_conjSetOf_le_two_of_list857_of_center hL hr hlist
    (center_card_le_three_of_list857 hL hlist) hm3


theorem normal_or_ncard_two_of_list857 {G : Type} [Group G] [Finite G]
    {M L : Subgroup G} (hL : L ∈ calC M)
    (hr : CFSG.Open.pRank 3 L = 2) (hlist : List857 (Bar2 L))
    (hm3 : CFSG.Open.pRank 3 M ≤ 3) :
    M ≤ Subgroup.normalizer (L : Set G) ∨
      ((conjSetOf M L).ncard = 2 ∧
        (IsA6Z3 (Bar2 L) ∨ IsA7Z3 (Bar2 L) ∨ IsM22Z3 (Bar2 L))) := by
  by_cases hN : M ≤ Subgroup.normalizer (L : Set G)
  · exact Or.inl hN
  · right
    have h2 : 2 ≤ (conjSetOf M L).ncard := two_le_ncard_conjSetOf_of_not_le_normalizer hN
    have hle : (conjSetOf M L).ncard ≤ 2 := ncard_conjSetOf_le_two_of_list857 hL hr hlist hm3
    have heq : (conjSetOf M L).ncard = 2 := by omega
    have h3 : 3 ∣ Nat.card (Subgroup.center (Bar2 L)) := by
      by_contra hnc
      obtain ⟨L', hne, hset⟩ :=
        exists_pair_eq_conjSetOf_of_ncard_eq_two (mem_conjSetOf_self M L) heq
      have hL' : L' ∈ conjSetOf M L := by rw [hset]; simp
      have h4 := four_le_pRank_three_of_two_conj_of_not_three_dvd_center hL
        (mem_conjSetOf_self M L) hL' hne.symm hr hnc
      omega
    exact ⟨heq, center_three_imp_of_list857 hL hlist h3⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
