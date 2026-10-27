module

public import CFSG.LocalAnalysis.WeakClosure81.EightEightDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)

variable {G : Type} [Group G] [Finite G]

theorem MinCex88.le_normalizer_one {V H T : Subgroup G} {i : ℕ} (h : MinCex88 V H T i)
    (h1 : ¬ Concl881 V H) {X : Subgroup G} (hTX : T ≤ X) (hXH : X < H)
    (hX : ¬ HasCompFactor X IsCalL1) : X ≤ normalizer (V : Set G) := by
  by_contra hXM
  have hX88 := h.hyp.of_le hTX hXH.le hXM
  have hc := (h.concl_of_lt hX88 hXH).1
  obtain ⟨hpr, hsp, -⟩ := not_concl881_iff.mp h1
  exact hX (hc ((CFSG.SectionRank.pRank_mono (by norm_num) hXH.le).trans hpr) hsp)

theorem MinCex88.le_normalizer_zero {V H T : Subgroup G} {i : ℕ} (h : MinCex88 V H T i)
    (h2 : ¬ Concl882 V H) {X : Subgroup G} (hTX : T ≤ X) (hXH : X < H)
    (hX : ¬ HasCompFactor X IsCalL0) : X ≤ normalizer (V : Set G) := by
  by_contra hXM
  have hX88 := h.hyp.of_le hTX hXH.le hXM
  have hc := (h.concl_of_lt hX88 hXH).2
  obtain ⟨h3, hp, -⟩ := not_concl882_iff.mp h2
  refine hX (hc ((CFSG.SectionRank.pRank_mono (by norm_num) hXH.le).trans h3) ?_)
  intro p hpp hp2 hpX
  have hpH : 3 < CFSG.Open.pRank p H :=
    lt_of_lt_of_le hpX (CFSG.SectionRank.pRank_mono hpp.one_lt hXH.le)
  exact (CFSG.SectionRank.pRank_mono hpp.one_lt (inf_le_inf_right _ hXH.le)).trans
    (hp p hpp hp2 hpH)

private theorem lGen_le_inf {V H T : Subgroup G} (P : ∀ (X : Type) [Group X], Prop)
    (hP : ∀ X : Subgroup G, T ≤ X → X < H → ¬ HasCompFactor X P →
      X ≤ normalizer (V : Set G)) :
    lGen P H T ≤ H ⊓ normalizer (V : Set G) :=
  iSup₂_le fun X hX => le_inf hX.2.1.le (hP X hX.1 hX.2.1 hX.2.2)

private theorem inf_lt {V H T : Subgroup G} {i : ℕ} (h : MinCex88 V H T i) :
    T ≤ H ⊓ normalizer (V : Set G) ∧ H ⊓ normalizer (V : Set G) < H :=
  ⟨h.hyp.sylow.le, lt_of_le_of_ne inf_le_left fun heq => h.hyp.notLe (heq ▸ inf_le_right)⟩

theorem MinCex88.hyps_5_13 {V H T : Subgroup G} {i : ℕ} (h : MinCex88 V H T i)
    (h1 : ¬ Concl881 V H) :
    CFSG.Open.IsKGroup ↥H ∧ IsSylowIn 2 T H ∧ T < H ∧ CFSG.Open.pRank 3 H ≤ 1 ∧
      ¬ HasCompFactor H IsCalL1 ∧ H ≠ lGen IsCalL1 H T := by
  obtain ⟨hpr, -, hno⟩ := not_concl881_iff.mp h1
  obtain ⟨hTM, hlt⟩ := inf_lt h
  refine ⟨h.hyp.kgroup, isSylowIn_of_isCalH h.hyp.calH h.hyp.sylow, lt_of_le_of_lt hTM hlt,
    hpr, hno, ?_⟩
  intro heq
  have hle := lGen_le_inf (V := V) (H := H) (T := T) IsCalL1
    (fun X hTX hXH hX => h.le_normalizer_one h1 hTX hXH hX)
  rw [← heq] at hle
  exact absurd (lt_of_le_of_lt hle hlt) (lt_irrefl _)

theorem MinCex88.hyps_5_11 {V H T : Subgroup G} {i : ℕ} (h : MinCex88 V H T i)
    (h2 : ¬ Concl882 V H) :
    CFSG.Open.IsKGroup ↥H ∧ IsSylowIn 2 T H ∧ T < H ∧ ¬ HasCompFactor H IsCalL0 ∧
      H ≠ lGen IsCalL0 H T ∧
      ∀ p : ℕ, p.Prime → p ≠ 2 →
        CFSG.Open.pRank p H ≤ 3 ∨ CFSG.Open.pRank p (lGen IsCalL0 H T) ≤ 1 := by
  obtain ⟨-, hp, hno⟩ := not_concl882_iff.mp h2
  obtain ⟨hTM, hlt⟩ := inf_lt h
  have hle := lGen_le_inf (V := V) (H := H) (T := T) IsCalL0
    (fun X hTX hXH hX => h.le_normalizer_zero h2 hTX hXH hX)
  refine ⟨h.hyp.kgroup, isSylowIn_of_isCalH h.hyp.calH h.hyp.sylow, lt_of_le_of_lt hTM hlt,
    hno, ?_, ?_⟩
  · intro heq
    rw [← heq] at hle
    exact absurd (lt_of_le_of_lt hle hlt) (lt_irrefl _)
  · intro p hpp hp2
    by_cases hp3 : CFSG.Open.pRank p H ≤ 3
    · exact Or.inl hp3
    · exact Or.inr ((CFSG.SectionRank.pRank_mono hpp.one_lt hle).trans
        (hp p hpp hp2 (not_le.mp hp3)))

private theorem calNIn_eq_of {H T : Subgroup G} {P : ∀ (X : Type) [Group X], Prop}
    {M : Subgroup G} (hN : calNIn H T = {lGen P H T}) (hle : lGen P H T ≤ H ⊓ M)
    (hTM : T ≤ H ⊓ M) (hlt : H ⊓ M < H) : calNIn H T = {H ⊓ M} := by
  obtain ⟨X, hX, hMX⟩ := exists_mem_calNIn_of_lt hTM hlt
  rw [hN, Set.mem_singleton_iff] at hX
  subst hX
  rw [hN, le_antisymm hle hMX]

theorem MinCex88.calNIn_eq {V H T : Subgroup G} {i : ℕ} (h5_11 : Asch5_11) (h5_13 : Asch5_13)
    (h : MinCex88 V H T i) : calNIn H T = {H ⊓ normalizer (V : Set G)} := by
  obtain ⟨hTM, hlt⟩ := inf_lt h
  rcases not_and_or.mp h.fail with h1 | h2
  · obtain ⟨hK, hT, hTlt, h3, hno, hne⟩ := h.hyps_5_13 h1
    exact calNIn_eq_of (h5_13 G H T hK hT hTlt h3 hno hne).1
      (lGen_le_inf (V := V) (H := H) (T := T) IsCalL1
        (fun X hTX hXH hX => h.le_normalizer_one h1 hTX hXH hX)) hTM hlt
  · obtain ⟨hK, hT, hTlt, hno, hne, hp⟩ := h.hyps_5_11 h2
    exact calNIn_eq_of (h5_11 G H T hK hT hTlt hno hne hp).1.1
      (lGen_le_inf (V := V) (H := H) (T := T) IsCalL0
        (fun X hTX hXH hX => h.le_normalizer_zero h2 hTX hXH hX)) hTM hlt

end CFSG.LocalAnalysis.WeakClosure81

end
