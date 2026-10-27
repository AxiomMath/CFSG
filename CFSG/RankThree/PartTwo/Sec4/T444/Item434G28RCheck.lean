module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434G28Bin
public import Std.Data.HashSet.Lemmas

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434G28

@[expose] def rClosed (S : Array ℕ) (gens : List ℕ) : Bool :=
  let H : Std.HashSet ℕ := Std.HashSet.ofArray S
  H.contains id2 && S.all fun s => gens.all fun g => H.contains (mul2 s g)

theorem rClosed_spec {S : Array ℕ} {gens : List ℕ} (h : rClosed S gens = true) :
    id2 ∈ S ∧ ∀ s ∈ S, ∀ g ∈ gens, mul2 s g ∈ S := by
  have hmem : ∀ x, (Std.HashSet.ofArray S).contains x = true ↔ x ∈ S := by
    intro x
    rw [Std.HashSet.ofArray_eq_ofList, Std.HashSet.contains_ofList]
    simp
  simp only [rClosed, Bool.and_eq_true, hmem, Array.all_eq_true', List.all_eq_true] at h
  exact ⟨h.1, fun s hs g hg => h.2 s hs g hg⟩

@[expose] def rF3 (S : Array ℕ) : Bool :=
  S.all fun s => pw2 s 21 != id2 || pw2 s 3 == id2 || pw2 s 7 == id2

theorem rF3_spec {S : Array ℕ} (h : rF3 S = true) :
    ∀ s ∈ S, pw2 s 21 = id2 → pw2 s 3 = id2 ∨ pw2 s 7 = id2 := by
  intro s hs h21
  simp only [rF3, Array.all_eq_true'] at h
  simpa [h21] using h s hs

@[expose] def comm2 (a b : ℕ) : Bool := mul2 a b == mul2 b a

@[expose] def invols (S : Array ℕ) : Array ℕ := S.filter fun s => s != id2 && mul2 s s == id2

@[expose] def ord3s (S : Array ℕ) : Array ℕ := S.filter fun s => s != id2 && pw2 s 3 == id2

theorem mem_invols {S : Array ℕ} {t : ℕ} : t ∈ invols S ↔ t ∈ S ∧ t ≠ id2 ∧ mul2 t t = id2 := by
  simp [invols, Array.mem_filter]

theorem mem_ord3s {S : Array ℕ} {t : ℕ} : t ∈ ord3s S ↔ t ∈ S ∧ t ≠ id2 ∧ pw2 t 3 = id2 := by
  simp [ord3s, Array.mem_filter]

@[expose] def rLocal (S : Array ℕ) : Bool :=
  let I := invols S
  let T := ord3s S
  I.all fun t =>
    let Ct := T.filter fun e => comm2 t e
    (Ct.all fun e => Ct.all fun u => u == e || u == mul2 e e || !comm2 u e) &&
    (I.all fun t' => t == t' || !comm2 t t' || Ct.all fun e => !comm2 t' e)

theorem rLocal_spec {S : Array ℕ} (h : rLocal S = true) :
    ∀ t ∈ S, t ≠ id2 → mul2 t t = id2 →
      (∀ e ∈ S, e ≠ id2 → pw2 e 3 = id2 → mul2 t e = mul2 e t →
        ∀ u ∈ S, u ≠ id2 → pw2 u 3 = id2 → mul2 t u = mul2 u t →
          u = e ∨ u = mul2 e e ∨ mul2 u e ≠ mul2 e u) ∧
      (∀ t' ∈ S, t' ≠ id2 → mul2 t' t' = id2 → t = t' ∨ mul2 t t' ≠ mul2 t' t ∨
        ∀ e ∈ S, e ≠ id2 → pw2 e 3 = id2 → mul2 t e = mul2 e t → mul2 t' e ≠ mul2 e t') := by
  intro t ht ht1 ht2
  have htI : t ∈ invols S := mem_invols.mpr ⟨ht, ht1, ht2⟩
  simp only [rLocal, Array.all_eq_true'] at h
  have h1 := h t htI
  simp only [Bool.and_eq_true, Array.all_eq_true', Bool.or_eq_true, beq_iff_eq,
    Bool.not_eq_true', Array.mem_filter, mem_invols, mem_ord3s, comm2] at h1
  obtain ⟨hA, hB⟩ := h1
  refine ⟨fun e he he1 he3 hte u hu hu1 hu3 htu => ?_, fun t' ht' ht'1 ht'2 => ?_⟩
  · have := hA e ⟨⟨he, he1, he3⟩, hte⟩ u ⟨⟨hu, hu1, hu3⟩, htu⟩
    simpa [or_assoc] using this
  · have := hB t' ⟨ht', ht'1, ht'2⟩
    rcases this with (h | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (by simpa using h))
    · refine Or.inr (Or.inr fun e he he1 he3 hte => ?_)
      simpa using h e ⟨⟨he, he1, he3⟩, hte⟩

@[expose] def rCheck (S : Array ℕ) (gens : List ℕ) : Bool :=
  S.all (fun s => decide (s < 2 ^ 36)) && rClosed S gens && rF3 S && rLocal S

theorem rCheck_spec {S : Array ℕ} {gens : List ℕ} (h : rCheck S gens = true) :
    (∀ s ∈ S, s < 2 ^ 36) ∧ (id2 ∈ S ∧ ∀ s ∈ S, ∀ g ∈ gens, mul2 s g ∈ S) ∧
      (∀ s ∈ S, pw2 s 21 = id2 → pw2 s 3 = id2 ∨ pw2 s 7 = id2) ∧ rLocal S = true := by
  simp only [rCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨fun s hs => ?_, rClosed_spec h2, rF3_spec h3, h4⟩
  simpa using Array.all_eq_true'.mp h1 s hs

end CFSG.RankThree.PartTwo.Sec4.Item434G28
