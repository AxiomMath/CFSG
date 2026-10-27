module

public import CFSG.LocalAnalysis.WeakClosure81.EightNine
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5ASDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)

variable {G : Type} [Group G] [Finite G]

private theorem lGen_le_inf {V H T : Subgroup G} (P : ∀ (X : Type) [Group X], Prop)
    (hP : ∀ X : Subgroup G, T ≤ X → X < H → ¬ HasCompFactor X P →
      X ≤ normalizer (V : Set G)) :
    lGen P H T ≤ H ⊓ normalizer (V : Set G) :=
  iSup₂_le fun X hX => le_inf hX.2.1.le (hP X hX.1 hX.2.1 hX.2.2)

private theorem inf_lt {V H T : Subgroup G} {i : ℕ} (h : MinCex88 V H T i) :
    T ≤ H ⊓ normalizer (V : Set G) ∧ H ⊓ normalizer (V : Set G) < H :=
  ⟨h.hyp.sylow.le, lt_of_le_of_ne inf_le_left fun heq => h.hyp.notLe (heq ▸ inf_le_right)⟩

private theorem calNIn_eq_of {H T : Subgroup G} {P : ∀ (X : Type) [Group X], Prop}
    {M : Subgroup G} (hN : calNIn H T = {lGen P H T}) (hle : lGen P H T ≤ H ⊓ M)
    (hTM : T ≤ H ⊓ M) (hlt : H ⊓ M < H) : calNIn H T = {H ⊓ M} := by
  obtain ⟨X, hX, hMX⟩ := exists_mem_calNIn_of_lt hTM hlt
  rw [hN, Set.mem_singleton_iff] at hX
  subst hX
  rw [hN, le_antisymm hle hMX]

theorem MinCex88.calNIn_eq_AS {V H T : Subgroup G} {i : ℕ} (h5_11 : Asch5_11AS)
    (h5_13 : Asch5_13AS) (h : MinCex88 V H T i) :
    calNIn H T = {H ⊓ normalizer (V : Set G)} := by
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
