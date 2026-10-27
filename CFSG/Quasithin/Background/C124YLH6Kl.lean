module

public import CFSG.Quasithin.Background.C124YLA6S1

set_option maxRecDepth 100000

public section

namespace CFSG.Quasithin.C124.YL.A6

open Equiv

@[expose] def kAlist : List P6 :=
  [1, swap 4 5 * swap 2 3, swap 3 5 * swap 2 4, swap 3 4 * swap 2 5]

theorem kAlist_mul : ∀ a ∈ kAlist, ∀ b ∈ kAlist, memP (a * b) kAlist = true := by decide +kernel

theorem kAlist_inv : ∀ a ∈ kAlist, memP a⁻¹ kAlist = true := by decide +kernel

@[expose] def KAg : Subgroup P6 :=
  sgOfList kAlist (by decide +kernel) kAlist_mul kAlist_inv

theorem klein_dec : ∀ l ∈ plist.sublists, okSub l = true → okElem l = true → l.length = 4 →
    ((∀ g ∈ l, memP g klist = true) ∧ (∀ g ∈ klist, memP g l = true)) ∨
      ((∀ g ∈ l, memP g kAlist = true) ∧ (∀ g ∈ kAlist, memP g l = true)) := by
  decide +kernel

theorem klein_of_le_Pg {H : Subgroup P6} (hHP : H ≤ Pg) (h4 : Nat.card H = 4)
    (hel : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) (hsq : ∀ a ∈ H, a * a = 1) :
    H = Kg ∨ H = KAg := by
  classical
  set l : List P6 := plist.filter (fun g => decide (g ∈ H)) with hldef
  have hmem : ∀ g, g ∈ l ↔ g ∈ H := by
    intro g
    rw [hldef, List.mem_filter]
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
  rcases klein_dec l hsub hok1 hok2 (by rw [← hcard]; exact h4) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    apply le_antisymm
    · intro g hg
      exact memP_iff.1 (h1 g ((hmem g).2 hg))
    · intro g hg
      exact (hmem g).1 (memP_iff.1 (h2 g hg))
  · right
    apply le_antisymm
    · intro g hg
      exact memP_iff.1 (h1 g ((hmem g).2 hg))
    · intro g hg
      exact (hmem g).1 (memP_iff.1 (h2 g hg))

end CFSG.Quasithin.C124.YL.A6
