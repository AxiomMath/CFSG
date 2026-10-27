module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcRaw

public section

namespace CFSG.StandardType.GGQ2Frame.ExcRaw
private theorem coroot_zero_coord :
    ∀ (k l : Fin 24), k ≠ l → ∀ a b : ZMod 3,
      (∀ t : Fin 4, a * (H 0 k t : ZMod 3) + b * (H 0 l t : ZMod 3) = 0) →
      a = 0 ∧ b = 0 := by
  decide +kernel

private theorem vanish_bot (j : Root 0) : Vanish 0 ⊥ j := by
  intro u hu
  rw [Submodule.mem_bot] at hu
  subst u
  exact map_zero (root 0 j)

private theorem vanish_span_singleton {u : V 0} {j : Root 0} :
    Vanish 0 (Submodule.span (ZMod 3) {u}) j ↔ root 0 j u = 0 := by
  constructor
  · intro h
    exact h u (Submodule.mem_span_singleton_self u)
  · intro h v hv
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [map_smul, h, smul_zero]

private theorem closed_of_bool_check {c : Finset (Fin 24)} {u : V 0} {f : Fin 24 → Fin 24 → Bool}
    (hf : ∀ i j, f i j = true ↔ root 0 j u = 0 → Adj 0 i j → j ∈ c)
    (hcheck : (List.finRange 24).all (fun i =>
      if i ∈ c then (List.finRange 24).all (fun j => f i j) else true) = true) :
    ∀ i ∈ c, ∀ j : Fin 24, root 0 j u = 0 → Adj 0 i j → j ∈ c := by
  intro i hi j hj hadj
  have h1 := List.all_eq_true.mp hcheck i (List.mem_finRange i)
  rw [if_pos hi] at h1
  have h2 := List.all_eq_true.mp h1 j (List.mem_finRange j)
  exact (hf i j).mp h2 hj hadj

private theorem conn_of_bool_check {c : Finset (Fin 24)} {f : Fin 24 → Fin 24 → Fin 24 → Bool}
    (hf : ∀ i j k, f i j k = true ↔ k ∈ c ∧ Adj 0 i k ∧ Adj 0 k j)
    (hcheck : (List.finRange 24).all (fun i =>
      if i ∈ c then (List.finRange 24).all (fun j =>
        if j ∈ c then (List.finRange 24).any (f i j) else true) else true) = true) :
    ∀ i ∈ c, ∀ j ∈ c, ∃ k ∈ c, Adj 0 i k ∧ Adj 0 k j := by
  intro i hi j hj
  have h1 := List.all_eq_true.mp hcheck i (List.mem_finRange i)
  rw [if_pos hi] at h1
  have h2 := List.all_eq_true.mp h1 j (List.mem_finRange j)
  rw [if_pos hj] at h2
  obtain ⟨k, -, hk⟩ := List.any_eq_true.mp h2
  exact ⟨k, (hf i j k).mp hk⟩

private theorem isComp_of_vanishing {u : V 0} {c : Finset (Fin 24)} (hne : c.Nonempty)
    (hvan : ∀ i ∈ c, root 0 i u = 0)
    (hclosed : ∀ i ∈ c, ∀ j : Fin 24, root 0 j u = 0 → Adj 0 i j → j ∈ c)
    (hconn : ∀ i ∈ c, ∀ j ∈ c, ∃ k ∈ c, Adj 0 i k ∧ Adj 0 k j) :
    IsComp 0 (Vanish 0 (Submodule.span (ZMod 3) {u})) c := by
  refine ⟨hne, ?_, ?_, ?_⟩
  · intro i hi
    exact vanish_span_singleton.2 (hvan i hi)
  · intro i hi j hj hadj
    exact hclosed i hi j ((vanish_span_singleton).mp hj) hadj
  · intro T hT hTne hTclosed
    refine Finset.Subset.antisymm hT ?_
    intro j hj
    obtain ⟨i, hi⟩ := hTne
    obtain ⟨k, hk, hik, hkj⟩ := hconn i (hT hi) j hj
    exact hTclosed k (hTclosed i hi k hk hik) j hj hkj

theorem coroot_zero_linIndep {k l : Root 0} (hkl : k ≠ l) {a b : ZMod 3}
    (h : a • coroot 0 k + b • coroot 0 l = 0) : a = 0 ∧ b = 0 := by
  have hcoord : ∀ t : Fin 4,
      a * (H 0 k t : ZMod 3) + b * (H 0 l t : ZMod 3) = 0 := by
    intro t
    have h' := congrArg (fun v : V 0 => v t) h
    change a * (H 0 k t : ZMod 3) + b * (H 0 l t : ZMod 3) = 0 at h'
    exact h'
  exact coroot_zero_coord k l hkl a b hcoord

theorem exists_adj_adj_zero (i j : Root 0) : ∃ k, Adj 0 i k ∧ Adj 0 k j := by
  revert i j
  unfold Adj
  decide +kernel

theorem eq_univ_of_occurs_bot {c : Finset (Root 0)} (hc : occurs 0 ⊥ c) : c = Finset.univ := by
  obtain ⟨hne, -, hclosed, -⟩ := hc
  obtain ⟨i₀, hi₀⟩ := hne
  apply Finset.eq_univ_of_forall
  intro j
  obtain ⟨k, hik, hkj⟩ := exists_adj_adj_zero i₀ j
  exact hclosed k (hclosed i₀ hi₀ k (vanish_bot k) hik) j (vanish_bot j) hkj

theorem ne_bot_of_occurs_zero {U : Submodule (ZMod 3) (V 0)} {c : Finset (Root 0)}
    (hU : occurs 0 U c) (hc : c.card ≠ 24) : U ≠ ⊥ := by
  rintro rfl
  exact hc (by rw [eq_univ_of_occurs_bot hU, Finset.card_univ, Fintype.card_fin]; rfl)

private theorem occurs_code1 :
    occurs 0 (Submodule.span (ZMod 3) {(![0, 0, 0, 1] : V 0)})
      ({0, 1, 7, 10, 11, 14, 20, 22, 23} : Finset (Fin 24)) := by
  change IsComp 0 (Vanish 0 (Submodule.span (ZMod 3) {(![0, 0, 0, 1] : V 0)}))
    ({0, 1, 7, 10, 11, 14, 20, 22, 23} : Finset (Fin 24))
  refine isComp_of_vanishing (u := (![0, 0, 0, 1] : V 0))
    (c := ({0, 1, 7, 10, 11, 14, 20, 22, 23} : Finset (Fin 24))) ?_ ?_ ?_ ?_
  · decide +kernel
  · decide +kernel
  · let f : Fin 24 → Fin 24 → Bool := fun i j =>
      !decide (root 0 j (![0, 0, 0, 1] : V 0) = 0) ||
        !decide (pairing 0 i j ≠ 0 ∨ pairing 0 j i ≠ 0) ||
          decide (j ∈ ({0, 1, 7, 10, 11, 14, 20, 22, 23} : Finset (Fin 24)))
    have hf : ∀ i j, f i j = true ↔ root 0 j (![0, 0, 0, 1] : V 0) = 0 →
        Adj 0 i j → j ∈ ({0, 1, 7, 10, 11, 14, 20, 22, 23} : Finset (Fin 24)) := by
      intro i j
      unfold Adj
      simp [f, Bool.or_eq_true, decide_eq_true_eq]
      tauto
    have hcheck : (List.finRange 24).all (fun i =>
        if i ∈ ({0, 1, 7, 10, 11, 14, 20, 22, 23} : Finset (Fin 24)) then
          (List.finRange 24).all (fun j => f i j)
        else true) = true := by
      decide +kernel
    exact closed_of_bool_check hf hcheck
  · let f : Fin 24 → Fin 24 → Fin 24 → Bool := fun i j k =>
      decide (k ∈ ({0, 1, 7, 10, 11, 14, 20, 22, 23} : Finset (Fin 24))) &&
        decide (pairing 0 i k ≠ 0 ∨ pairing 0 k i ≠ 0) &&
          decide (pairing 0 k j ≠ 0 ∨ pairing 0 j k ≠ 0)
    have hf : ∀ i j k, f i j k = true ↔
        k ∈ ({0, 1, 7, 10, 11, 14, 20, 22, 23} : Finset (Fin 24)) ∧
          Adj 0 i k ∧ Adj 0 k j := by
      intro i j k
      unfold Adj
      simp [f, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
    have hcheck : (List.finRange 24).all (fun i =>
        if i ∈ ({0, 1, 7, 10, 11, 14, 20, 22, 23} : Finset (Fin 24)) then
          (List.finRange 24).all (fun j =>
            if j ∈ ({0, 1, 7, 10, 11, 14, 20, 22, 23} : Finset (Fin 24)) then
              (List.finRange 24).any (f i j)
            else true)
        else true) = true := by
      decide +kernel
    exact conn_of_bool_check hf hcheck


private theorem occurs_code2 :
    occurs 0 (Submodule.span (ZMod 3) {(![0, 1, 1, 1] : V 0)})
      ({1, 2, 6, 8, 10, 11, 12, 15, 23} : Finset (Fin 24)) := by
  change IsComp 0 (Vanish 0 (Submodule.span (ZMod 3) {(![0, 1, 1, 1] : V 0)}))
    ({1, 2, 6, 8, 10, 11, 12, 15, 23} : Finset (Fin 24))
  refine isComp_of_vanishing (u := (![0, 1, 1, 1] : V 0))
    (c := ({1, 2, 6, 8, 10, 11, 12, 15, 23} : Finset (Fin 24))) ?_ ?_ ?_ ?_
  · decide +kernel
  · decide +kernel
  · let f : Fin 24 → Fin 24 → Bool := fun i j =>
      !decide (root 0 j (![0, 1, 1, 1] : V 0) = 0) ||
        !decide (pairing 0 i j ≠ 0 ∨ pairing 0 j i ≠ 0) ||
          decide (j ∈ ({1, 2, 6, 8, 10, 11, 12, 15, 23} : Finset (Fin 24)))
    have hf : ∀ i j, f i j = true ↔ root 0 j (![0, 1, 1, 1] : V 0) = 0 →
        Adj 0 i j → j ∈ ({1, 2, 6, 8, 10, 11, 12, 15, 23} : Finset (Fin 24)) := by
      intro i j
      unfold Adj
      simp [f, Bool.or_eq_true, decide_eq_true_eq]
      tauto
    have hcheck : (List.finRange 24).all (fun i =>
        if i ∈ ({1, 2, 6, 8, 10, 11, 12, 15, 23} : Finset (Fin 24)) then
          (List.finRange 24).all (fun j => f i j)
        else true) = true := by
      decide +kernel
    exact closed_of_bool_check hf hcheck
  · let f : Fin 24 → Fin 24 → Fin 24 → Bool := fun i j k =>
      decide (k ∈ ({1, 2, 6, 8, 10, 11, 12, 15, 23} : Finset (Fin 24))) &&
        decide (pairing 0 i k ≠ 0 ∨ pairing 0 k i ≠ 0) &&
          decide (pairing 0 k j ≠ 0 ∨ pairing 0 j k ≠ 0)
    have hf : ∀ i j k, f i j k = true ↔
        k ∈ ({1, 2, 6, 8, 10, 11, 12, 15, 23} : Finset (Fin 24)) ∧
          Adj 0 i k ∧ Adj 0 k j := by
      intro i j k
      unfold Adj
      simp [f, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
    have hcheck : (List.finRange 24).all (fun i =>
        if i ∈ ({1, 2, 6, 8, 10, 11, 12, 15, 23} : Finset (Fin 24)) then
          (List.finRange 24).all (fun j =>
            if j ∈ ({1, 2, 6, 8, 10, 11, 12, 15, 23} : Finset (Fin 24)) then
              (List.finRange 24).any (f i j)
            else true)
        else true) = true := by
      decide +kernel
    exact conn_of_bool_check hf hcheck


private theorem occurs_code3 :
    occurs 0 (Submodule.span (ZMod 3) {(![0, 1, 0, 0] : V 0)})
      ({3, 6, 7, 9, 12, 13, 15, 17, 23} : Finset (Fin 24)) := by
  change IsComp 0 (Vanish 0 (Submodule.span (ZMod 3) {(![0, 1, 0, 0] : V 0)}))
    ({3, 6, 7, 9, 12, 13, 15, 17, 23} : Finset (Fin 24))
  refine isComp_of_vanishing (u := (![0, 1, 0, 0] : V 0))
    (c := ({3, 6, 7, 9, 12, 13, 15, 17, 23} : Finset (Fin 24))) ?_ ?_ ?_ ?_
  · decide +kernel
  · decide +kernel
  · let f : Fin 24 → Fin 24 → Bool := fun i j =>
      !decide (root 0 j (![0, 1, 0, 0] : V 0) = 0) ||
        !decide (pairing 0 i j ≠ 0 ∨ pairing 0 j i ≠ 0) ||
          decide (j ∈ ({3, 6, 7, 9, 12, 13, 15, 17, 23} : Finset (Fin 24)))
    have hf : ∀ i j, f i j = true ↔ root 0 j (![0, 1, 0, 0] : V 0) = 0 →
        Adj 0 i j → j ∈ ({3, 6, 7, 9, 12, 13, 15, 17, 23} : Finset (Fin 24)) := by
      intro i j
      unfold Adj
      simp [f, Bool.or_eq_true, decide_eq_true_eq]
      tauto
    have hcheck : (List.finRange 24).all (fun i =>
        if i ∈ ({3, 6, 7, 9, 12, 13, 15, 17, 23} : Finset (Fin 24)) then
          (List.finRange 24).all (fun j => f i j)
        else true) = true := by
      decide +kernel
    exact closed_of_bool_check hf hcheck
  · let f : Fin 24 → Fin 24 → Fin 24 → Bool := fun i j k =>
      decide (k ∈ ({3, 6, 7, 9, 12, 13, 15, 17, 23} : Finset (Fin 24))) &&
        decide (pairing 0 i k ≠ 0 ∨ pairing 0 k i ≠ 0) &&
          decide (pairing 0 k j ≠ 0 ∨ pairing 0 j k ≠ 0)
    have hf : ∀ i j k, f i j k = true ↔
        k ∈ ({3, 6, 7, 9, 12, 13, 15, 17, 23} : Finset (Fin 24)) ∧
          Adj 0 i k ∧ Adj 0 k j := by
      intro i j k
      unfold Adj
      simp [f, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
    have hcheck : (List.finRange 24).all (fun i =>
        if i ∈ ({3, 6, 7, 9, 12, 13, 15, 17, 23} : Finset (Fin 24)) then
          (List.finRange 24).all (fun j =>
            if j ∈ ({3, 6, 7, 9, 12, 13, 15, 17, 23} : Finset (Fin 24)) then
              (List.finRange 24).any (f i j)
            else true)
        else true) = true := by
      decide +kernel
    exact conn_of_bool_check hf hcheck


private theorem occurs_code4 :
    occurs 0 (Submodule.span (ZMod 3) {(![0, 1, 1, 0] : V 0)})
      ({1, 4, 5, 9, 10, 11, 13, 17, 23} : Finset (Fin 24)) := by
  change IsComp 0 (Vanish 0 (Submodule.span (ZMod 3) {(![0, 1, 1, 0] : V 0)}))
    ({1, 4, 5, 9, 10, 11, 13, 17, 23} : Finset (Fin 24))
  refine isComp_of_vanishing (u := (![0, 1, 1, 0] : V 0))
    (c := ({1, 4, 5, 9, 10, 11, 13, 17, 23} : Finset (Fin 24))) ?_ ?_ ?_ ?_
  · decide +kernel
  · decide +kernel
  · let f : Fin 24 → Fin 24 → Bool := fun i j =>
      !decide (root 0 j (![0, 1, 1, 0] : V 0) = 0) ||
        !decide (pairing 0 i j ≠ 0 ∨ pairing 0 j i ≠ 0) ||
          decide (j ∈ ({1, 4, 5, 9, 10, 11, 13, 17, 23} : Finset (Fin 24)))
    have hf : ∀ i j, f i j = true ↔ root 0 j (![0, 1, 1, 0] : V 0) = 0 →
        Adj 0 i j → j ∈ ({1, 4, 5, 9, 10, 11, 13, 17, 23} : Finset (Fin 24)) := by
      intro i j
      unfold Adj
      simp [f, Bool.or_eq_true, decide_eq_true_eq]
      tauto
    have hcheck : (List.finRange 24).all (fun i =>
        if i ∈ ({1, 4, 5, 9, 10, 11, 13, 17, 23} : Finset (Fin 24)) then
          (List.finRange 24).all (fun j => f i j)
        else true) = true := by
      decide +kernel
    exact closed_of_bool_check hf hcheck
  · let f : Fin 24 → Fin 24 → Fin 24 → Bool := fun i j k =>
      decide (k ∈ ({1, 4, 5, 9, 10, 11, 13, 17, 23} : Finset (Fin 24))) &&
        decide (pairing 0 i k ≠ 0 ∨ pairing 0 k i ≠ 0) &&
          decide (pairing 0 k j ≠ 0 ∨ pairing 0 j k ≠ 0)
    have hf : ∀ i j k, f i j k = true ↔
        k ∈ ({1, 4, 5, 9, 10, 11, 13, 17, 23} : Finset (Fin 24)) ∧
          Adj 0 i k ∧ Adj 0 k j := by
      intro i j k
      unfold Adj
      simp [f, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
    have hcheck : (List.finRange 24).all (fun i =>
        if i ∈ ({1, 4, 5, 9, 10, 11, 13, 17, 23} : Finset (Fin 24)) then
          (List.finRange 24).all (fun j =>
            if j ∈ ({1, 4, 5, 9, 10, 11, 13, 17, 23} : Finset (Fin 24)) then
              (List.finRange 24).any (f i j)
            else true)
        else true) = true := by
      decide +kernel
    exact conn_of_bool_check hf hcheck


private theorem occurs_code5 :
    occurs 0 (Submodule.span (ZMod 3) {(![0, 0, 1, 1] : V 0)})
      ({0, 5, 6, 12, 15, 16, 19, 22, 23} : Finset (Fin 24)) := by
  change IsComp 0 (Vanish 0 (Submodule.span (ZMod 3) {(![0, 0, 1, 1] : V 0)}))
    ({0, 5, 6, 12, 15, 16, 19, 22, 23} : Finset (Fin 24))
  refine isComp_of_vanishing (u := (![0, 0, 1, 1] : V 0))
    (c := ({0, 5, 6, 12, 15, 16, 19, 22, 23} : Finset (Fin 24))) ?_ ?_ ?_ ?_
  · decide +kernel
  · decide +kernel
  · let f : Fin 24 → Fin 24 → Bool := fun i j =>
      !decide (root 0 j (![0, 0, 1, 1] : V 0) = 0) ||
        !decide (pairing 0 i j ≠ 0 ∨ pairing 0 j i ≠ 0) ||
          decide (j ∈ ({0, 5, 6, 12, 15, 16, 19, 22, 23} : Finset (Fin 24)))
    have hf : ∀ i j, f i j = true ↔ root 0 j (![0, 0, 1, 1] : V 0) = 0 →
        Adj 0 i j → j ∈ ({0, 5, 6, 12, 15, 16, 19, 22, 23} : Finset (Fin 24)) := by
      intro i j
      unfold Adj
      simp [f, Bool.or_eq_true, decide_eq_true_eq]
      tauto
    have hcheck : (List.finRange 24).all (fun i =>
        if i ∈ ({0, 5, 6, 12, 15, 16, 19, 22, 23} : Finset (Fin 24)) then
          (List.finRange 24).all (fun j => f i j)
        else true) = true := by
      decide +kernel
    exact closed_of_bool_check hf hcheck
  · let f : Fin 24 → Fin 24 → Fin 24 → Bool := fun i j k =>
      decide (k ∈ ({0, 5, 6, 12, 15, 16, 19, 22, 23} : Finset (Fin 24))) &&
        decide (pairing 0 i k ≠ 0 ∨ pairing 0 k i ≠ 0) &&
          decide (pairing 0 k j ≠ 0 ∨ pairing 0 j k ≠ 0)
    have hf : ∀ i j k, f i j k = true ↔
        k ∈ ({0, 5, 6, 12, 15, 16, 19, 22, 23} : Finset (Fin 24)) ∧
          Adj 0 i k ∧ Adj 0 k j := by
      intro i j k
      unfold Adj
      simp [f, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
    have hcheck : (List.finRange 24).all (fun i =>
        if i ∈ ({0, 5, 6, 12, 15, 16, 19, 22, 23} : Finset (Fin 24)) then
          (List.finRange 24).all (fun j =>
            if j ∈ ({0, 5, 6, 12, 15, 16, 19, 22, 23} : Finset (Fin 24)) then
              (List.finRange 24).any (f i j)
            else true)
        else true) = true := by
      decide +kernel
    exact conn_of_bool_check hf hcheck


private theorem occurs_code6 :
    occurs 0 (Submodule.span (ZMod 3) {(![0, 0, 1, 0] : V 0)})
      ({0, 8, 9, 13, 17, 18, 21, 22, 23} : Finset (Fin 24)) := by
  change IsComp 0 (Vanish 0 (Submodule.span (ZMod 3) {(![0, 0, 1, 0] : V 0)}))
    ({0, 8, 9, 13, 17, 18, 21, 22, 23} : Finset (Fin 24))
  refine isComp_of_vanishing (u := (![0, 0, 1, 0] : V 0))
    (c := ({0, 8, 9, 13, 17, 18, 21, 22, 23} : Finset (Fin 24))) ?_ ?_ ?_ ?_
  · decide +kernel
  · decide +kernel
  · let f : Fin 24 → Fin 24 → Bool := fun i j =>
      !decide (root 0 j (![0, 0, 1, 0] : V 0) = 0) ||
        !decide (pairing 0 i j ≠ 0 ∨ pairing 0 j i ≠ 0) ||
          decide (j ∈ ({0, 8, 9, 13, 17, 18, 21, 22, 23} : Finset (Fin 24)))
    have hf : ∀ i j, f i j = true ↔ root 0 j (![0, 0, 1, 0] : V 0) = 0 →
        Adj 0 i j → j ∈ ({0, 8, 9, 13, 17, 18, 21, 22, 23} : Finset (Fin 24)) := by
      intro i j
      unfold Adj
      simp [f, Bool.or_eq_true, decide_eq_true_eq]
      tauto
    have hcheck : (List.finRange 24).all (fun i =>
        if i ∈ ({0, 8, 9, 13, 17, 18, 21, 22, 23} : Finset (Fin 24)) then
          (List.finRange 24).all (fun j => f i j)
        else true) = true := by
      decide +kernel
    exact closed_of_bool_check hf hcheck
  · let f : Fin 24 → Fin 24 → Fin 24 → Bool := fun i j k =>
      decide (k ∈ ({0, 8, 9, 13, 17, 18, 21, 22, 23} : Finset (Fin 24))) &&
        decide (pairing 0 i k ≠ 0 ∨ pairing 0 k i ≠ 0) &&
          decide (pairing 0 k j ≠ 0 ∨ pairing 0 j k ≠ 0)
    have hf : ∀ i j k, f i j k = true ↔
        k ∈ ({0, 8, 9, 13, 17, 18, 21, 22, 23} : Finset (Fin 24)) ∧
          Adj 0 i k ∧ Adj 0 k j := by
      intro i j k
      unfold Adj
      simp [f, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
    have hcheck : (List.finRange 24).all (fun i =>
        if i ∈ ({0, 8, 9, 13, 17, 18, 21, 22, 23} : Finset (Fin 24)) then
          (List.finRange 24).all (fun j =>
            if j ∈ ({0, 8, 9, 13, 17, 18, 21, 22, 23} : Finset (Fin 24)) then
              (List.finRange 24).any (f i j)
            else true)
        else true) = true := by
      decide +kernel
    exact conn_of_bool_check hf hcheck

theorem exists_occurs_nine (i : Root 0) :
    ∃ (U : Submodule (ZMod 3) (V 0)) (c : Finset (Root 0)), i ∈ c ∧ c.card = 9 ∧
      occurs 0 U c := by
  change ∃ (U : Submodule (ZMod 3) (V 0)) (c : Finset (Fin 24)),
    Fin.cast (by rfl : nroots 0 = 24) i ∈ c ∧ c.card = 9 ∧ occurs 0 U c
  fin_cases i
  · refine ⟨_, ({0, 1, 7, 10, 11, 14, 20, 22, 23} : Finset (Fin 24)), ?_, ?_, occurs_code1⟩ <;> decide
  · refine ⟨_, ({0, 1, 7, 10, 11, 14, 20, 22, 23} : Finset (Fin 24)), ?_, ?_, occurs_code1⟩ <;> decide
  · refine ⟨_, ({1, 2, 6, 8, 10, 11, 12, 15, 23} : Finset (Fin 24)), ?_, ?_, occurs_code2⟩ <;> decide
  · refine ⟨_, ({3, 6, 7, 9, 12, 13, 15, 17, 23} : Finset (Fin 24)), ?_, ?_, occurs_code3⟩ <;> decide
  · refine ⟨_, ({1, 4, 5, 9, 10, 11, 13, 17, 23} : Finset (Fin 24)), ?_, ?_, occurs_code4⟩ <;> decide
  · refine ⟨_, ({1, 4, 5, 9, 10, 11, 13, 17, 23} : Finset (Fin 24)), ?_, ?_, occurs_code4⟩ <;> decide
  · refine ⟨_, ({1, 2, 6, 8, 10, 11, 12, 15, 23} : Finset (Fin 24)), ?_, ?_, occurs_code2⟩ <;> decide
  · refine ⟨_, ({0, 1, 7, 10, 11, 14, 20, 22, 23} : Finset (Fin 24)), ?_, ?_, occurs_code1⟩ <;> decide
  · refine ⟨_, ({1, 2, 6, 8, 10, 11, 12, 15, 23} : Finset (Fin 24)), ?_, ?_, occurs_code2⟩ <;> decide
  · refine ⟨_, ({3, 6, 7, 9, 12, 13, 15, 17, 23} : Finset (Fin 24)), ?_, ?_, occurs_code3⟩ <;> decide
  · refine ⟨_, ({0, 1, 7, 10, 11, 14, 20, 22, 23} : Finset (Fin 24)), ?_, ?_, occurs_code1⟩ <;> decide
  · refine ⟨_, ({0, 1, 7, 10, 11, 14, 20, 22, 23} : Finset (Fin 24)), ?_, ?_, occurs_code1⟩ <;> decide
  · refine ⟨_, ({1, 2, 6, 8, 10, 11, 12, 15, 23} : Finset (Fin 24)), ?_, ?_, occurs_code2⟩ <;> decide
  · refine ⟨_, ({3, 6, 7, 9, 12, 13, 15, 17, 23} : Finset (Fin 24)), ?_, ?_, occurs_code3⟩ <;> decide
  · refine ⟨_, ({0, 1, 7, 10, 11, 14, 20, 22, 23} : Finset (Fin 24)), ?_, ?_, occurs_code1⟩ <;> decide
  · refine ⟨_, ({1, 2, 6, 8, 10, 11, 12, 15, 23} : Finset (Fin 24)), ?_, ?_, occurs_code2⟩ <;> decide
  · refine ⟨_, ({0, 5, 6, 12, 15, 16, 19, 22, 23} : Finset (Fin 24)), ?_, ?_, occurs_code5⟩ <;> decide
  · refine ⟨_, ({3, 6, 7, 9, 12, 13, 15, 17, 23} : Finset (Fin 24)), ?_, ?_, occurs_code3⟩ <;> decide
  · refine ⟨_, ({0, 8, 9, 13, 17, 18, 21, 22, 23} : Finset (Fin 24)), ?_, ?_, occurs_code6⟩ <;> decide
  · refine ⟨_, ({0, 5, 6, 12, 15, 16, 19, 22, 23} : Finset (Fin 24)), ?_, ?_, occurs_code5⟩ <;> decide
  · refine ⟨_, ({0, 1, 7, 10, 11, 14, 20, 22, 23} : Finset (Fin 24)), ?_, ?_, occurs_code1⟩ <;> decide
  · refine ⟨_, ({0, 8, 9, 13, 17, 18, 21, 22, 23} : Finset (Fin 24)), ?_, ?_, occurs_code6⟩ <;> decide
  · refine ⟨_, ({0, 1, 7, 10, 11, 14, 20, 22, 23} : Finset (Fin 24)), ?_, ?_, occurs_code1⟩ <;> decide
  · refine ⟨_, ({0, 1, 7, 10, 11, 14, 20, 22, 23} : Finset (Fin 24)), ?_, ?_, occurs_code1⟩ <;> decide

theorem card_ne_of_admissible_zero {c : Finset (Root 0)} (hc : admissible 0 c) :
    c.card ≠ 1 ∧ c.card ≠ 3 := by
  have hlab : CFSG.Assembly.LargeEvenInLambda2 (labelF4 c.card) := hc.2
  constructor
  · intro h
    rw [h] at hlab
    simp [labelF4, CFSG.Assembly.LargeEvenInLambda2] at hlab
  · intro h
    rw [h] at hlab
    simp [labelF4, CFSG.Assembly.LargeEvenInLambda2] at hlab

end CFSG.StandardType.GGQ2Frame.ExcRaw

end
