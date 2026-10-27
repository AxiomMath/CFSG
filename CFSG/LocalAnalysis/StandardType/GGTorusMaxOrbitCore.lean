module

public import Mathlib.Data.Set.Card

public section

namespace CFSG.StandardType.FrameRoute

variable {V ι : Type*} [Zero V]

private theorem tmOrb_rep_mem (f : ι → V → V) (hff : ∀ i v, f i (f i v) = v)
    (hf0 : ∀ i, f i 0 = 0) (lab dep : V → ℕ) (rep : ℕ → V)
    (hlab : ∀ v, v ≠ 0 → ∀ i, lab (f i v) = lab v)
    (hdep0 : ∀ v, v ≠ 0 → dep v = 0 → v = rep (lab v))
    (hdesc : ∀ v, v ≠ 0 → dep v ≠ 0 → ∃ i, dep (f i v) < dep v)
    {T : Set V} (hT : ∀ i, ∀ v ∈ T, f i v ∈ T) :
    ∀ (n : ℕ) (v : V), dep v = n → v ∈ T → v ≠ 0 → rep (lab v) ∈ T := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro v hn hv hv0
    by_cases hd : dep v = 0
    · rwa [← hdep0 v hv0 hd]
    · obtain ⟨i, hi⟩ := hdesc v hv0 hd
      have hne : f i v ≠ 0 := fun h => hv0 (by rw [← hff i v, h, hf0])
      rw [← hlab v hv0 i]
      exact ih _ (hn ▸ hi) _ rfl (hT i v hv) hne

theorem tmOrb_mem_of_tables (f : ι → V → V) (hff : ∀ i v, f i (f i v) = v)
    (hf0 : ∀ i, f i 0 = 0) (lab dep : V → ℕ) (rep : ℕ → V)
    (hlab : ∀ v, v ≠ 0 → ∀ i, lab (f i v) = lab v)
    (hdep0 : ∀ v, v ≠ 0 → dep v = 0 → v = rep (lab v))
    (hdesc : ∀ v, v ≠ 0 → dep v ≠ 0 → ∃ i, dep (f i v) < dep v)
    {T : Set V} (hT : ∀ i, ∀ v ∈ T, f i v ∈ T) {v : V} (hv : v ∈ T) (hv0 : v ≠ 0)
    {u : V} (hu0 : u ≠ 0) (hu : lab u = lab v) : u ∈ T := by
  have hrep := tmOrb_rep_mem f hff hf0 lab dep rep hlab hdep0 hdesc hT _ v rfl hv hv0
  suffices h : ∀ (n : ℕ) (u : V), dep u = n → u ≠ 0 → lab u = lab v → u ∈ T from
    h _ u rfl hu0 hu
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro u hn hu0 hu
    by_cases hd : dep u = 0
    · rw [hdep0 u hu0 hd, hu]
      exact hrep
    · obtain ⟨i, hi⟩ := hdesc u hu0 hd
      have hne : f i u ≠ 0 := fun h => hu0 (by rw [← hff i u, h, hf0])
      rw [← hff i u]
      exact hT i _ (ih _ (hn ▸ hi) _ rfl hne ((hlab u hu0 i).trans hu))

theorem tmOrb_length_le_ncard_of_tables [Finite V] (f : ι → V → V)
    (hff : ∀ i v, f i (f i v) = v) (hf0 : ∀ i, f i 0 = 0) (lab dep : V → ℕ) (rep : ℕ → V)
    (hlab : ∀ v, v ≠ 0 → ∀ i, lab (f i v) = lab v)
    (hdep0 : ∀ v, v ≠ 0 → dep v = 0 → v = rep (lab v))
    (hdesc : ∀ v, v ≠ 0 → dep v ≠ 0 → ∃ i, dep (f i v) < dep v)
    {T : Set V} (hT : ∀ i, ∀ v ∈ T, f i v ∈ T) {v : V} (hv : v ∈ T) (hv0 : v ≠ 0)
    (L : List V) (hL : L.Nodup) (hLlab : ∀ u ∈ L, u ≠ 0 ∧ lab u = lab v) :
    L.length ≤ T.ncard := by
  classical
  have hsub : (L.toFinset : Set V) ⊆ T := fun u hu => by
    rw [Finset.mem_coe, List.mem_toFinset] at hu
    exact tmOrb_mem_of_tables f hff hf0 lab dep rep hlab hdep0 hdesc hT hv hv0
      (hLlab u hu).1 (hLlab u hu).2
  calc L.length = L.toFinset.card := (List.toFinset_card_of_nodup hL).symm
    _ = (L.toFinset : Set V).ncard := (Set.ncard_coe_finset _).symm
    _ ≤ T.ncard := Set.ncard_le_ncard hsub (Set.toFinite T)

end CFSG.StandardType.FrameRoute

end
