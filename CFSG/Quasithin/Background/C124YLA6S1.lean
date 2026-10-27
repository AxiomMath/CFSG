module

public import CFSG.Quasithin.Background.C124YLA6Vec

set_option maxRecDepth 100000

public section

namespace CFSG.Quasithin.C124.YL.A6

open Equiv

@[expose] def okSub (l : List P6) : Bool :=
  memP 1 l && l.all fun a => l.all fun b => memP (a * b) l

@[expose] def okElem (l : List P6) : Bool :=
  l.all fun a => eqP (a * a) 1 && l.all fun b => eqP (a * b) (b * a)

@[expose] def nontriv (l : List P6) : Bool := l.any fun a => !eqP a 1

theorem s1_dec : ∀ l ∈ plist.sublists, okSub l = true → okElem l = true → nontriv l = true →
    32 ≤ l.length * cntL l →
      (∀ g ∈ l, memP g klist = true) ∧ (∀ g ∈ klist, memP g l = true) := by
  decide +kernel

theorem plist_nodup : plist.Nodup := by decide +kernel

theorem card_of_list {l : List P6} (hn : l.Nodup) {H : Subgroup P6} (h : ∀ g, g ∈ l ↔ g ∈ H) :
    Nat.card H = l.length := by
  classical
  have e : ↥H ≃ ↥l.toFinset :=
    Equiv.subtypeEquivRight fun g => by rw [List.mem_toFinset, h]
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe,
    List.toFinset_card_of_nodup hn]

theorem s1 (H : Subgroup P6) (hHP : H ≤ Pg) (hne : H ≠ ⊥)
    (hel : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) (hsq : ∀ a ∈ H, a * a = 1)
    (hcnt : ∀ l : List P6, (∀ g, g ∈ l ↔ g ∈ H) → 32 ≤ Nat.card H * cntL l) : H = Kg := by
  classical
  set l : List P6 := plist.filter (fun g => decide (g ∈ H)) with hl
  have hmem : ∀ g, g ∈ l ↔ g ∈ H := by
    intro g
    rw [hl, List.mem_filter]
    simp only [decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨hHP h, h⟩⟩
  have hsub : l ∈ plist.sublists := List.mem_sublists.2 List.filter_sublist
  have hcard : Nat.card H = l.length := card_of_list (plist_nodup.filter _) hmem
  have hok1 : okSub l = true := by
    simp only [okSub, Bool.and_eq_true, memP_iff, List.all_eq_true]
    exact ⟨(hmem 1).2 H.one_mem, fun a ha b hb => (hmem _).2 (H.mul_mem ((hmem a).1 ha)
      ((hmem b).1 hb))⟩
  have hok2 : okElem l = true := by
    simp only [okElem, Bool.and_eq_true, eqP_iff, List.all_eq_true]
    exact fun a ha => ⟨hsq a ((hmem a).1 ha), fun b hb => hel a ((hmem a).1 ha) b ((hmem b).1 hb)⟩
  have hok3 : nontriv l = true := by
    obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
    simp only [nontriv, List.any_eq_true, Bool.not_eq_true']
    refine ⟨a, (hmem a).2 a.2, ?_⟩
    rw [Bool.eq_false_iff]
    exact fun h => ha1 (Subtype.ext (eqP_iff.1 h))
  have key := s1_dec l hsub hok1 hok2 hok3 (by rw [← hcard]; exact hcnt l hmem)
  apply le_antisymm
  · intro g hg
    exact memP_iff.1 (key.1 g ((hmem g).2 hg))
  · intro g hg
    exact (hmem g).1 (memP_iff.1 (key.2 g hg))

end CFSG.Quasithin.C124.YL.A6
