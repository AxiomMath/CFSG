module

public import Certificates.Certificate4174

public section

namespace CFSG.Quasithin.J4Loc

open CFSG.Sporadic.J4.QT

theorem mem_srt {x : Nat} {l : List Nat} : x ∈ srt l ↔ x ∈ l := List.mem_mergeSort

def spanF (b : List Nat) : List Nat := b.foldl (fun acc v => acc ++ acc.map (· ^^^ v)) [0]

theorem mem_spanS {x : Nat} {b : List Nat} : x ∈ spanS b ↔ x ∈ spanF b := mem_srt

private theorem foldl_span_zero (b : List Nat) : ∀ acc : List Nat, 0 ∈ acc →
    0 ∈ b.foldl (fun acc v => acc ++ acc.map (· ^^^ v)) acc := by
  induction b with
  | nil => intro acc h; simpa using h
  | cons v b ih =>
    intro acc h
    simp only [List.foldl_cons]
    exact ih _ (List.mem_append_left _ h)

private theorem foldl_span_closed (b : List Nat) : ∀ acc : List Nat,
    (∀ x ∈ acc, ∀ y ∈ acc, x ^^^ y ∈ acc) →
    ∀ x ∈ b.foldl (fun acc v => acc ++ acc.map (· ^^^ v)) acc,
      ∀ y ∈ b.foldl (fun acc v => acc ++ acc.map (· ^^^ v)) acc,
        x ^^^ y ∈ b.foldl (fun acc v => acc ++ acc.map (· ^^^ v)) acc := by
  induction b with
  | nil => intro acc h; simpa using h
  | cons v b ih =>
    intro acc h
    simp only [List.foldl_cons]
    refine ih _ ?_
    intro x hx y hy
    simp only [List.mem_append, List.mem_map] at hx hy ⊢
    rcases hx with hx | ⟨a, ha, rfl⟩ <;> rcases hy with hy | ⟨b', hb, rfl⟩
    · exact Or.inl (h x hx y hy)
    · refine Or.inr ⟨x ^^^ b', h x hx b' hb, ?_⟩
      rw [Nat.xor_assoc]
    · refine Or.inr ⟨a ^^^ y, h a ha y hy, ?_⟩
      rw [Nat.xor_assoc, Nat.xor_assoc, Nat.xor_comm y v]
    · refine Or.inl ?_
      have : a ^^^ v ^^^ (b' ^^^ v) = a ^^^ b' := by
        rw [Nat.xor_assoc, ← Nat.xor_assoc v, Nat.xor_comm v b', Nat.xor_assoc b' v v,
          Nat.xor_self, Nat.xor_zero]
      rw [this]
      exact h a ha b' hb

theorem spanF_zero (b : List Nat) : 0 ∈ spanF b := foldl_span_zero b [0] (by simp)

theorem spanF_xor (b : List Nat) {x y : Nat} (hx : x ∈ spanF b) (hy : y ∈ spanF b) :
    x ^^^ y ∈ spanF b :=
  foldl_span_closed b [0] (by
    intro x hx y hy
    simp only [List.mem_singleton] at hx hy ⊢
    subst hx; subst hy; rfl) x hx y hy

theorem mem_subs {B : List Nat} (hB : B ∈ subs) : ∃ b, B = spanS b := by
  simp only [subs, List.mem_map] at hB
  obtain ⟨b, -, hb⟩ := hB
  exact ⟨b, hb.symm⟩

theorem subs_prop {B : List Nat} (hB : B ∈ subs) :
    (∀ c ∈ B, c < 2048) ∧ B.Pairwise (· < ·) ∧ 0 ∈ B ∧ (∀ x ∈ B, ∀ y ∈ B, x ^^^ y ∈ B) ∧
    (∀ i < 4, ∀ c ∈ B, actT (kTab i) c ∈ B ∧ actT (kInvTab i) c ∈ B) :=
  Certificates.certificate4174.1 B hB

theorem subs_zero_mem : [0] ∈ subs :=
  Certificates.certificate4174.2.1

theorem subs_chain {B : List Nat} (hB : B ∈ subs) {v : Nat}
    (hv : v < 2048) (hvB : v ∉ B) (hfix : ∀ i < 4, (actT (kTab i) v ^^^ v) ∈ B) :
    ∃ B' ∈ subs, (∀ x ∈ B, x ∈ B') ∧ v ∈ B' ∧ ∀ y ∈ B', y ∈ B ∨ ∃ x ∈ B, y = x ^^^ v :=
  Certificates.certificate4174.2.2.1 B hB v hv hvB hfix

theorem atLeastF_sound (f : Nat → Nat) (n : Nat) : ∀ (fuel c : Nat) (acc : List Nat), acc.Nodup →
    (∀ y ∈ acc, ∃ c' < c, f c' = y) → atLeastF f n fuel c acc = true →
    n ≤ ((Finset.range (c + fuel)).image f).card := by
  intro fuel
  induction fuel with
  | zero =>
    intro c acc hnd hacc h
    simp only [atLeastF, decide_eq_true_eq] at h
    have hsub : acc.toFinset ⊆ (Finset.range (c + 0)).image f := by
      intro y hy
      obtain ⟨c', hc', rfl⟩ := hacc y (List.mem_toFinset.1 hy)
      exact Finset.mem_image.2 ⟨c', Finset.mem_range.2 (by omega), rfl⟩
    calc n ≤ acc.length := h
      _ = acc.toFinset.card := (List.toFinset_card_of_nodup hnd).symm
      _ ≤ _ := Finset.card_le_card hsub
  | succ fuel ih =>
    intro c acc hnd hacc h
    simp only [atLeastF] at h
    by_cases h1 : n ≤ acc.length
    · have hsub : acc.toFinset ⊆ (Finset.range (c + (fuel + 1))).image f := by
        intro y hy
        obtain ⟨c', hc', rfl⟩ := hacc y (List.mem_toFinset.1 hy)
        exact Finset.mem_image.2 ⟨c', Finset.mem_range.2 (by omega), rfl⟩
      calc n ≤ acc.length := h1
        _ = acc.toFinset.card := (List.toFinset_card_of_nodup hnd).symm
        _ ≤ _ := Finset.card_le_card hsub
    · rw [ite_eq_right h1] at h
      by_cases h2 : acc.contains (f c) = true
      · rw [ite_eq_left h2] at h
        have := ih (c + 1) acc hnd (fun y hy => by
          obtain ⟨c', hc', rfl⟩ := hacc y hy
          exact ⟨c', by omega, rfl⟩) h
        rwa [show c + 1 + fuel = c + (fuel + 1) by omega] at this
      · rw [ite_eq_right h2] at h
        have hnd' : (f c :: acc).Nodup := by
          refine List.nodup_cons.2 ⟨fun hm => h2 (List.contains_iff_mem.2 hm), hnd⟩
        have := ih (c + 1) (f c :: acc) hnd' (fun y hy => by
          rcases List.mem_cons.1 hy with rfl | hy
          · exact ⟨c, by omega, rfl⟩
          · obtain ⟨c', hc', rfl⟩ := hacc y hy
            exact ⟨c', by omega, rfl⟩) h
        rwa [show c + 1 + fuel = c + (fuel + 1) by omega] at this

theorem rank_ge {t : List Nat} (ht : t ∈ tabL) (hne : t ≠ idT) :
    16 ≤ ((Finset.range 2048).image (fun c => actT t c ^^^ c)).card :=
  Certificates.certificate4174.2.2.2.1 t ht hne

end CFSG.Quasithin.J4Loc
