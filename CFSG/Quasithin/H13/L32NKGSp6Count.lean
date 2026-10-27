module

public import CFSG.Quasithin.H13.L32NKGSp6Search

public section

namespace CFSG.Quasithin.H13.KGSp6

open CFSG.KGroups.Sp6

theorem countP_flatMap_eq {α β : Type} (P : β → Bool) (L : List α) (F : α → List β) :
    (L.flatMap F).countP P = (L.map fun a => (F a).countP P).sum := by
  induction L with
  | nil => rfl
  | cons a L ih => simp [List.countP_append, ih]

theorem sum_map_ite {α : Type} (P : List ℕ → Bool) (g : α → List ℕ) (l : List α) :
    (l.map fun a => if P (g a) then 1 else 0).sum = (l.map g).countP P := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, ih, List.countP_cons]
    split <;> simp_all
    omega

theorem spCount_eq (r : ℕ) (P : List ℕ → Bool) : spCount r P = (spLeaves r).countP P := by
  simp only [spCount, spLeaves, countP_flatMap_eq, sum_map_ite]

theorem nodup_flatMap_pos (n : ℕ) {L : List ℕ} {F : ℕ → List (List ℕ)} (hL : L.Nodup)
    (hF : ∀ a ∈ L, (F a).Nodup) (hpos : ∀ a ∈ L, ∀ x ∈ F a, x.getD n 0 = a) :
    (L.flatMap F).Nodup := by
  rw [List.nodup_flatMap]
  refine ⟨hF, ?_⟩
  refine List.Pairwise.imp_of_mem ?_ hL
  intro a b ha hb hab x hxa hxb
  exact hab ((hpos a ha x hxa).symm.trans (hpos b hb x hxb))

theorem spLeaves_nodup (r : ℕ) : (spLeaves r).Nodup := by
  have hc : ∀ p : ℕ → Bool, ((List.range r).filter p).Nodup := fun p =>
    List.nodup_range.filter p
  unfold spLeaves
  refine nodup_flatMap_pos 0 (hc _) (fun c0 _ => ?_) (fun c0 _ x hx => ?_)
  · refine nodup_flatMap_pos 1 (hc _) (fun c1 _ => ?_) (fun c1 _ x hx => ?_)
    · refine nodup_flatMap_pos 2 (hc _) (fun c2 _ => ?_) (fun c2 _ x hx => ?_)
      · refine nodup_flatMap_pos 3 (hc _) (fun c3 _ => ?_) (fun c3 _ x hx => ?_)
        · refine nodup_flatMap_pos 4 (hc _) (fun c4 _ => ?_) (fun c4 _ x hx => ?_)
          · exact (hc _).map fun a b h => by simpa using h
          · simp only [List.mem_map] at hx
            obtain ⟨c5, -, rfl⟩ := hx
            rfl
        · simp only [List.mem_flatMap, List.mem_map] at hx
          obtain ⟨c4, -, c5, -, rfl⟩ := hx
          rfl
      · simp only [List.mem_flatMap, List.mem_map] at hx
        obtain ⟨c3, -, c4, -, c5, -, rfl⟩ := hx
        rfl
    · simp only [List.mem_flatMap, List.mem_map] at hx
      obtain ⟨c2, -, c3, -, c4, -, c5, -, rfl⟩ := hx
      rfl
  · simp only [List.mem_flatMap, List.mem_map] at hx
    obtain ⟨c1, -, c2, -, c3, -, c4, -, c5, -, rfl⟩ := hx
    rfl


theorem length_of_countCheck {r n : ℕ} (h : countCheck r n = true) : (spLeaves r).length = n := by
  have h' : spCount r (fun _ => true) = n := by
    unfold countCheck at h
    exact (beq_iff_eq).1 h
  rw [spCount_eq, List.countP_true] at h'
  exact h'

theorem mem_of_normCheck {r : ℕ} {s : List ℕ} {N : List (List ℕ)} (h : normCheck r s N = true)
    {x : List ℕ} (hx : x ∈ spLeaves r)
    (hn : ((List.range 6).map fun k => powC s (k + 1)).any (fun p => mulC x s == mulC p x) =
      true) : x ∈ N := by
  have h' : spCount r (fun x => ((List.range 6).map fun k => powC s (k + 1)).any
      (fun p => mulC x s == mulC p x) && !N.contains x) = 0 := by
    unfold normCheck at h
    exact (beq_iff_eq).1 h
  rw [spCount_eq, List.countP_eq_zero] at h'
  by_contra hxN
  have := h' x hx
  simp [hn, hxN] at this

theorem countP_le_of_witCheck {r : ℕ} {G N : List (List ℕ)} {bound : ℕ}
    (h : witCheck r G N bound = true) :
    (spLeaves r).countP (fun x => !G.contains x && !N.any fun n => five (mulC x n)) ≤ bound := by
  unfold witCheck at h
  have h' := of_decide_eq_true h
  rw [spCount_eq] at h'
  simpa [Std.HashSet.contains_ofList] using h'

end CFSG.Quasithin.H13.KGSp6
