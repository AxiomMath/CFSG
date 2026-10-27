module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import Certificates.Data.CFSGNative.AS91.M24Geom

public section

namespace CFSG.Quasithin.H13.AS91.M24G

@[expose] def labelClasses (n k : ℕ) (f : ℕ → List Bool) : List (List ℕ) :=
  (List.range k).map fun i =>
    (((List.range n).map fun p => (p, f p)).filter fun e => e.2.getD i false).map (·.1)

theorem labelClass_eq (l : List ℕ) (f : ℕ → List Bool) (i : ℕ) :
    ((l.map fun p => (p, f p)).filter fun e => e.2.getD i false).map (·.1) =
      l.filter fun p => (f p).getD i false := by
  rw [List.filter_map, List.map_map]
  exact List.map_id _

theorem length_filter_range (k : ℕ) (q : ℕ → Bool) :
    ((List.range k).filter q).length = ((Finset.range k).filter fun i => q i = true).card := by
  show _ = Multiset.card (Multiset.filter (fun i => q i = true) (Multiset.range k))
  rw [Multiset.range, Multiset.filter_coe, Multiset.coe_card]
  simp

theorem length_filter_range_eq_one {k : ℕ} {q : ℕ → Bool} :
    ((List.range k).filter q).length = 1 ↔ ∃! i, i < k ∧ q i = true := by
  rw [length_filter_range, Finset.card_eq_one]
  constructor
  · rintro ⟨a, ha⟩
    have hmem : ∀ i, (i < k ∧ q i = true) ↔ i = a := by
      intro i
      have h := Finset.ext_iff.1 ha i
      rwa [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton] at h
    exact ⟨a, (hmem a).2 rfl, fun i hi => (hmem i).1 hi⟩
  · rintro ⟨a, ha, huniq⟩
    refine ⟨a, Finset.ext fun i => ?_⟩
    rw [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    exact ⟨fun hi => huniq i hi, fun hi => hi ▸ ha⟩

theorem classOrbitCheck_spec {n k : ℕ} {f : ℕ → List Bool} {sizes : List ℕ}
    {steps : List (ℕ → ℕ)} (h : Native.classOrbitCheck n (labelClasses n k f) sizes steps = true) :
    sizes.length = k ∧ (∀ p < n, ∃! i, i < k ∧ (f p).getD i false = true) ∧
      ∀ i < k, ∃ p₀ < n, (f p₀).getD i false = true ∧
        ((List.range n).filter fun p => (f p).getD i false).length = sizes.getD i 0 ∧
        Native.reachOK n steps p₀ ((List.range n).filter fun p => (f p).getD i false) = true := by
  have hcls : labelClasses n k f = (List.range k).map fun i =>
      (List.range n).filter fun p => (f p).getD i false := by
    unfold labelClasses
    exact List.map_congr_left fun i _ => labelClass_eq (List.range n) f i
  rw [hcls] at h
  unfold Native.classOrbitCheck at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨hlen, hpart⟩, hzip⟩ := h
  rw [List.length_map, List.length_range] at hlen
  refine ⟨hlen.symm, ?_, ?_⟩
  · intro p hp
    have h1 := hpart p (List.mem_range.2 hp)
    rw [List.filter_map, List.length_map] at h1
    obtain ⟨i, hi, hu⟩ := length_filter_range_eq_one.1 h1
    have key : ∀ j, ((fun c : List ℕ => c.contains p) ∘ fun i =>
        (List.range n).filter fun p => (f p).getD i false) j = true ↔
          (f p).getD j false = true := by
      intro j
      simp [List.contains_eq_mem, List.mem_filter, List.mem_range, hp]
    exact ⟨i, ⟨hi.1, (key i).1 hi.2⟩, fun j hj => hu j ⟨hj.1, (key j).2 hj.2⟩⟩
  · intro i hi
    have hik : i < ((List.range k).map fun i =>
        (List.range n).filter fun p => (f p).getD i false).length := by simp [hi]
    have his : i < sizes.length := hlen ▸ (by simpa using hik)
    have hzi : i < (((List.range k).map fun i =>
        (List.range n).filter fun p => (f p).getD i false).zip sizes).length := by
      simp [List.length_zip, hi, his]
    have hmem := List.getElem_mem hzi
    have hpair := hzip _ hmem
    rw [List.getElem_zip, List.getElem_map, List.getElem_range] at hpair
    rw [List.getD_eq_getElem _ _ his]
    generalize hc : (List.range n).filter (fun p => (f p).getD i false) = c at hpair ⊢
    cases c with
    | nil => simp at hpair
    | cons p₀ t =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hpair
      obtain ⟨hl, hr⟩ := hpair
      have hp₀ : p₀ ∈ (List.range n).filter (fun p => (f p).getD i false) := by
        rw [hc]
        exact List.mem_cons_self
      rw [List.mem_filter, List.mem_range] at hp₀
      exact ⟨p₀, hp₀.1, hp₀.2, hl, hr⟩

theorem ncard_eq_length_filter {β : Type*} {n : ℕ} {F : ℕ → β}
    (hinj : ∀ p < n, ∀ p' < n, F p = F p' → p = p') {P : β → Prop}
    (hP : ∀ x, P x ↔ ∃ p < n, F p = x) (b : ℕ → Bool) {Q : β → Prop}
    (hQ : ∀ p < n, Q (F p) ↔ b p = true) :
    {x | P x ∧ Q x}.ncard = ((List.range n).filter b).length := by
  classical
  have hset : {x | P x ∧ Q x} =
      (((Finset.range n).filter fun p => b p = true).image F : Set β) := by
    ext x
    simp only [Set.mem_setOf_eq, Finset.coe_image, Finset.coe_filter, Finset.mem_range,
      Set.mem_image]
    constructor
    · rintro ⟨hx, hq⟩
      obtain ⟨p, hp, rfl⟩ := (hP x).1 hx
      exact ⟨p, ⟨hp, (hQ p hp).1 hq⟩, rfl⟩
    · rintro ⟨p, ⟨hp, hb⟩, rfl⟩
      exact ⟨(hP _).2 ⟨p, hp, rfl⟩, (hQ p hp).2 hb⟩
  rw [hset, Set.ncard_coe_finset, Finset.card_image_of_injOn, length_filter_range]
  intro p hp p' hp' he
  simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hp hp'
  exact hinj p hp.1 p' hp'.1 he

theorem mem_combs {k : ℕ} {l c : List ℕ} : c ∈ Native.combs k l ↔ c.Sublist l ∧ c.length = k := by
  induction l generalizing k c with
  | nil =>
    cases k with
    | zero => simp [Native.combs, List.sublist_nil]
    | succ k =>
      simp only [Native.combs, List.not_mem_nil, false_iff, not_and, List.sublist_nil]
      rintro rfl
      simp
  | cons a l ih =>
    cases k with
    | zero =>
      simp only [Native.combs, List.mem_singleton, List.length_eq_zero_iff]
      constructor
      · rintro rfl
        exact ⟨List.nil_sublist _, rfl⟩
      · exact fun h => h.2
    | succ k =>
      simp only [Native.combs, List.mem_append, List.mem_map, ih, List.sublist_cons_iff]
      constructor
      · rintro (⟨c', ⟨hs, hl⟩, rfl⟩ | ⟨hs, hl⟩)
        · exact ⟨Or.inr ⟨c', rfl, hs⟩, by simp [hl]⟩
        · exact ⟨Or.inl hs, hl⟩
      · rintro ⟨hs | ⟨r, rfl, hr⟩, hl⟩
        · exact Or.inr ⟨hs, hl⟩
        · exact Or.inl ⟨r, ⟨hr, by simpa using hl⟩, rfl⟩

theorem sort_mem_combs {l : List ℕ} (hl : l.Pairwise (· < ·)) {S : Finset ℕ}
    (hS : ∀ x ∈ S, x ∈ l) : S.sort ∈ Native.combs S.card l := by
  rw [mem_combs, Finset.length_sort]
  refine ⟨List.sublist_of_subperm_of_sortedLE ?_
    ((Finset.sortedLT_sort S).pairwise.imp le_of_lt).sortedLE (hl.imp le_of_lt).sortedLE, rfl⟩
  exact List.Nodup.subperm (Finset.sort_nodup _ _) fun x hx => hS x ((Finset.mem_sort _).1 hx)

theorem pairwise_lt_filter_range (n : ℕ) (q : ℕ → Bool) :
    ((List.range n).filter q).Pairwise (· < ·) :=
  (List.pairwise_lt_range).filter _

end CFSG.Quasithin.H13.AS91.M24G
