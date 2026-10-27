module

public import CFSG.Sporadic.SmallOddCore.LocalSpec


public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open Equiv Equiv.Perm Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

structure ExactEnum (n : ℕ) (H : Subgroup (Perm (Fin n))) (E : Array Table) : Prop where
  rep : ∀ k < E.size, Rep n E[k]! (tablePerm n E[k]!)
  mem : ∀ k < E.size, tablePerm n E[k]! ∈ H
  cover : ∀ x ∈ H, ∃ k < E.size, Rep n E[k]! x
  nodup : (E.toList.map (tablePerm n)).Nodup

namespace ExactEnum

variable {n : ℕ} {H : Subgroup (Perm (Fin n))} {E : Array Table}

theorem forall_mem (hE : ExactEnum n H E) {P : Perm (Fin n) → Prop} {f : Table → Bool}
    (hf : ∀ T x, Rep n T x → f T = true → P x) (h : E.all f = true) : ∀ x ∈ H, P x := by
  intro x hx
  obtain ⟨k, hk, hrep⟩ := hE.cover x hx
  exact hf _ _ hrep (by rw [getElem!_pos E k hk]; exact Array.all_eq_true.1 h k hk)

theorem forall_entry (hE : ExactEnum n H E) {P : Perm (Fin n) → Prop} {f : Table → Bool}
    (hf : ∀ T x, Rep n T x → x ∈ H → f T = true → P x) (h : E.all f = true) :
    ∀ k < E.size, P (tablePerm n E[k]!) := by
  intro k hk
  exact hf _ _ (hE.rep k hk) (hE.mem k hk)
    (by rw [getElem!_pos E k hk]; exact Array.all_eq_true.1 h k hk)

theorem entry_mem (hE : ExactEnum n H E) (k : ℕ) (hk : k < E.size) : tablePerm n E[k]! ∈ H :=
  hE.mem k hk

theorem of_enumOK (hn : n < 2 ^ 32) {cap m : ℕ} {gs : List Table}
    (hg : ∀ g ∈ gs, permOK n g = true) (h : enumOK n cap m gs = true) :
    Nat.card (genOf n gs) = m ∧
      ExactEnum n (genOf n gs) (mulClosureH n gs.toArray cap).1 := by
  obtain ⟨hcard, hrep, hcov, hdist⟩ := enumOK_spec hn hg h
  refine ⟨hcard, ⟨fun k hk => (hrep k hk).1, fun k hk => (hrep k hk).2, hcov, ?_⟩⟩
  exact nodup_of_hkeysDistinct (forall₂_tablePerm fun k hk => (hrep k hk).1) hdist

theorem of_lb (hn : n < 2 ^ 32) {gs : List Table} (hg : ∀ g ∈ gs, permOK n g = true)
    {E : Array Table} {par lab : Array ℕ} {m : ℕ}
    (htree : mulTreeOK n gs.toArray E par lab = true) (hdist : hkeysDistinct n E.toList = true)
    (hsize : E.size = m) (hcard : Nat.card (genOf n gs) ≤ m) : ExactEnum n (genOf n gs) E := by
  classical
  have hGg : ∀ l < gs.toArray.size,
      Rep n gs.toArray[l]! (tp n gs.toArray[l]!) ∧ tp n gs.toArray[l]! ∈ genOf n gs := by
    intro l hl
    have hmem : gs.toArray[l]! ∈ gs := by simpa using getElem!_mem_array hl
    exact ⟨rep_tp (hg _ hmem), tp_mem_genOf hmem⟩
  have hspec := mulTreeOK_spec hn (genOf n gs) hGg htree
  have hrep : ∀ k < E.size, Rep n E[k]! (tablePerm n E[k]!) := by
    intro k hk
    obtain ⟨c, -, hc⟩ := hspec k hk
    rw [tablePerm_eq hc]
    exact hc
  have hmem : ∀ k < E.size, tablePerm n E[k]! ∈ genOf n gs := by
    intro k hk
    obtain ⟨c, hc, hcrep⟩ := hspec k hk
    rw [tablePerm_eq hcrep]
    exact hc
  have hnodup := nodup_of_hkeysDistinct (forall₂_tablePerm hrep) hdist
  refine ⟨hrep, hmem, ?_, hnodup⟩
  set L := E.toList.map (tablePerm n) with hL
  have hlen : L.length = m := by rw [hL, List.length_map, Array.length_toList, hsize]
  have hsub : (L.toFinset : Set (Perm (Fin n))) ⊆ (genOf n gs : Set (Perm (Fin n))) := by
    intro x hx
    simp only [Finset.mem_coe, List.mem_toFinset, hL, List.mem_map] at hx
    obtain ⟨T, hT, rfl⟩ := hx
    obtain ⟨k, hk, rfl⟩ := Array.getElem_of_mem (Array.mem_toList_iff.mp hT)
    have := hmem k hk
    rwa [getElem!_pos E k hk] at this
  have hcardL : (L.toFinset : Set (Perm (Fin n))).ncard = m := by
    rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hnodup, hlen]
  have heq : (L.toFinset : Set (Perm (Fin n))) = (genOf n gs : Set (Perm (Fin n))) := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
    rw [hcardL, ← Nat.card_coe_set_eq]
    exact hcard
  intro x hx
  have : x ∈ (L.toFinset : Set (Perm (Fin n))) := by rw [heq]; exact hx
  simp only [Finset.mem_coe, List.mem_toFinset, hL, List.mem_map] at this
  obtain ⟨T, hT, rfl⟩ := this
  obtain ⟨k, hk, rfl⟩ := Array.getElem_of_mem (Array.mem_toList_iff.mp hT)
  exact ⟨k, hk, by rw [getElem!_pos E k hk]; exact (by
    have := hrep k hk; rwa [getElem!_pos E k hk] at this)⟩

end ExactEnum

end CFSG.Sporadic.Recognition.LyonsSims
