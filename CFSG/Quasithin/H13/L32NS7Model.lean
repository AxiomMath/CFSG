module

public import CFSG.Quasithin.H13.L32NMat8
public import CFSG.Quasithin.H13.L32NItems1442Models
public import Certificates.Certificate7176
public import Mathlib.Tactic.Basify
public import Std.Data.HashSet.Lemmas
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Quasithin.H13.S7Cert

open Mat8Cert CFSG.Quasithin.H13.L1442M

theorem s7Check_eq : s7Check = true :=
  Certificates.certificate7176

theorem s7Check_parts :
    s7BasicB = true ∧ pB = true ∧ cvB = true ∧ eWB = true ∧ ovB = true ∧ oB = true ∧
      m12B = true := by
  have h := s7Check_eq
  simp only [s7Check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem validB_iff {x : List ℕ} : validB x = true ↔ Valid8 x := by
  simp only [validB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq]
  rfl

theorem nodup_of_nodupB {L : List (List ℕ)} (h : nodupB L = true) : L.Nodup := by
  simp only [nodupB, decide_eq_true_eq] at h
  have h2 : ((L.map code64).mergeSort).Nodup :=
    (List.isChain_iff_pairwise.mp h).imp (fun hab => ne_of_lt hab)
  exact List.Nodup.of_map _ ((List.mergeSort_perm _ _).nodup_iff.mp h2)

theorem subB_spec {gens L : List (List ℕ)} (h : subB gens L = true) :
    (∀ x ∈ L, Valid8 x) ∧ (∀ x ∈ L, ∀ g ∈ gens, mul8 g x ∈ L) ∧ L.Nodup ∧ one8 ∈ L ∧
      ∀ g ∈ gens, Valid8 g := by
  simp only [subB, closedB, Bool.and_eq_true, List.all_eq_true, Std.HashSet.contains_ofList,
    List.contains_iff_mem] at h
  obtain ⟨⟨⟨⟨hv, hc⟩, hn⟩, ho⟩, hg⟩ := h
  exact ⟨fun x hx => validB_iff.mp (hv x hx), hc, nodup_of_nodupB hn, ho,
    fun g hg' => validB_iff.mp (hg g hg')⟩

theorem mem_elemsOf {gens : List (List ℕ)} {cap : ℕ} {x : List ℕ} (hx : x ∈ elemsOf gens cap) :
    ∃ w, x = evalW gens w := by
  obtain ⟨w, -, rfl⟩ := List.mem_map.mp hx
  exact ⟨w, rfl⟩

theorem mem_genSub_iff_of {gens : List (List ℕ)} (h : subB gens (elemsOf gens) = true)
    (hunit : ∀ g ∈ gens, ∃ u : GL (Fin 8) (ZMod 2), (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 g)
    (u : GL (Fin 8) (ZMod 2)) :
    u ∈ genSub gens ↔ colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ elemsOf gens := by
  obtain ⟨-, hc, -, ho, hg⟩ := subB_spec h
  exact mem_genSub_iff gens _ hg hunit (fun _ hx => mem_elemsOf hx) ho hc u

theorem card_genSub_of {gens : List (List ℕ)} (h : subB gens (elemsOf gens) = true)
    (hunit : ∀ g ∈ gens, ∃ u : GL (Fin 8) (ZMod 2),
      (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 g) :
    Nat.card (genSub gens) = (elemsOf gens).length := by
  obtain ⟨hv, hc, hn, ho, hg⟩ := subB_spec h
  exact card_genSub gens _ hg hunit (fun _ hx => mem_elemsOf hx) hv ho hc hn

theorem mem_genSub_of_mem {gens : List (List ℕ)} (hgens : ∀ g ∈ gens, Valid8 g)
    {u : GL (Fin 8) (ZMod 2)} {g : List ℕ} (hg : g ∈ gens)
    (hu : (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 g) : u ∈ genSub gens :=
  Subgroup.subset_closure (show colsOf _ ∈ gens by rw [hu, colsOf_dec8 (hgens g hg)]; exact hg)

theorem s7G_cols : s7G = [colsOf (s7g0 : Matrix (Fin 8) (Fin 8) (ZMod 2)),
    colsOf (s7g1 : Matrix (Fin 8) (Fin 8) (ZMod 2)),
    colsOf (s7g2 : Matrix (Fin 8) (Fin 8) (ZMod 2))] := by
  decide +kernel

theorem s7G_unit : ∀ g ∈ s7G, ∃ u : GL (Fin 8) (ZMod 2),
    (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 g := by
  rw [s7G_cols]
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact ⟨s7g0, (dec8_colsOf _).symm⟩
  · exact ⟨s7g1, (dec8_colsOf _).symm⟩
  · exact ⟨s7g2, (dec8_colsOf _).symm⟩

theorem eq_of_colsOf_eq {u v : GL (Fin 8) (ZMod 2)}
    (h : colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) =
      colsOf (v : Matrix (Fin 8) (Fin 8) (ZMod 2))) :
    u = v := by
  apply Units.ext
  rw [← dec8_colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)), h, dec8_colsOf]

theorem s7_eq : s7 = genSub s7G := by
  unfold s7 genSub
  congr 1
  ext g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq, s7G_cols,
    List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro (rfl | rfl | rfl) <;> simp
  · rintro (h | h | h)
    · exact Or.inl (eq_of_colsOf_eq h)
    · exact Or.inr (Or.inl (eq_of_colsOf_eq h))
    · exact Or.inr (Or.inr (eq_of_colsOf_eq h))

theorem s7Basic_spec :
    subB s7G s7E = true ∧ s7E.length = 5040 := by
  have h := s7Check_parts.1
  simp only [s7BasicB, Bool.and_eq_true, beq_iff_eq] at h
  exact h

theorem mem_s7_iff (u : GL (Fin 8) (ZMod 2)) :
    u ∈ s7 ↔ colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ s7E := by
  rw [s7_eq]
  exact mem_genSub_iff_of s7Basic_spec.1 s7G_unit u

theorem card_s7 : Nat.card s7 = 5040 := by
  rw [s7_eq, card_genSub_of s7Basic_spec.1 s7G_unit]
  exact s7Basic_spec.2

theorem exists_mem_s7 {c : List ℕ} (hc : c ∈ s7E) :
    ∃ u ∈ s7, (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 c := by
  obtain ⟨w, rfl⟩ := mem_elemsOf hc
  rw [s7_eq]
  exact exists_evalW s7G (subB_spec s7Basic_spec.1).2.2.2.2 s7G_unit w

theorem genSub_le_s7 {gens : List (List ℕ)}
    (hgens : ∀ g ∈ gens, g ∈ s7E) : genSub gens ≤ s7 :=
  (Subgroup.closure_le _).mpr fun u hu => (mem_s7_iff u).mpr (hgens _ hu)

theorem unit_of_s7E {gens : List (List ℕ)}
    (hgens : ∀ g ∈ gens, g ∈ s7E) :
    ∀ g ∈ gens, ∃ u : GL (Fin 8) (ZMod 2), (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 g :=
  fun g hg => let ⟨u, _, hu⟩ := exists_mem_s7 (hgens g hg); ⟨u, hu⟩

theorem colsOf_mem_s7E {u : GL (Fin 8) (ZMod 2)} (hu : u ∈ s7) :
    colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ s7E := (mem_s7_iff u).mp hu

@[expose] def P7 : Subgroup (GL (Fin 8) (ZMod 2)) := genSub pG

theorem pB_spec :
    (elemsOf pG).length = 16 ∧ subB pG (elemsOf pG) = true ∧ (∀ g ∈ pG, g ∈ s7E) ∧
      ∀ v, v < 256 → (∀ p ∈ pG, mv8 p v = v) → v = 0 ∨ v = vStar := by
  have h := s7Check_parts.2.1
  simp only [pB] at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Std.HashSet.contains_ofList,
    List.contains_iff_mem] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, h3, fun v hv hfix => ?_⟩
  have := h4 v (List.mem_range.mpr hv)
  simp only [Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at this
  rcases this with (h5 | h5) | h5
  · exfalso
    have h6 : (pG.all fun p => mv8 p v == v) = true := by
      simp only [List.all_eq_true, beq_iff_eq]; exact hfix
    rw [h6] at h5
    exact Bool.noConfusion h5
  · exact Or.inl h5
  · exact Or.inr h5

theorem P7_le_s7 : P7 ≤ s7 := genSub_le_s7 pB_spec.2.2.1

theorem mem_P7_iff (u : GL (Fin 8) (ZMod 2)) :
    u ∈ P7 ↔ colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ elemsOf pG :=
  mem_genSub_iff_of pB_spec.2.1 (unit_of_s7E pB_spec.2.2.1) u

theorem card_P7 : Nat.card P7 = 16 := by
  rw [P7, card_genSub_of pB_spec.2.1 (unit_of_s7E pB_spec.2.2.1), pB_spec.1]

theorem eq_of_fixed_P7 (v : Fin 8 → ZMod 2)
    (hv : ∀ g ∈ P7, (g : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v = v) :
    v = 0 ∨ v = vec8 vStar := by
  have hval := (subB_spec pB_spec.2.1).2.2.2.2
  have hfix : ∀ p ∈ pG, mv8 p (code8 v) = code8 v := by
    intro p hp
    obtain ⟨u, hu⟩ := unit_of_s7E pB_spec.2.2.1 p hp
    have := hv u (mem_genSub_of_mem hval hp hu)
    rw [← vec8_code8 v, hu, dec8_mulVec] at this
    exact vec8_inj (mv8_lt (hval p hp) _) (code8_lt v) (by rw [this, vec8_code8])
  rcases pB_spec.2.2.2 (code8 v) (code8_lt v) hfix with h | h
  · left
    rw [← vec8_code8 v, h, vec8_zero]
  · right
    rw [← vec8_code8 v, h]

end CFSG.Quasithin.H13.S7Cert
