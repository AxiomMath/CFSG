module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporE81Table

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434SporE81

open CFSG.Assembly (IsElemAbelian)

@[expose] def elemsOf (mul : ℕ → ℕ → ℕ) : List ℕ → List ℕ
  | [] => [0]
  | a :: gs =>
    let r := elemsOf mul gs
    r ++ r.map (mul a) ++ r.map (mul (mul a a))

theorem length_elemsOf (mul : ℕ → ℕ → ℕ) (gs : List ℕ) :
    (elemsOf mul gs).length = 3 ^ gs.length := by
  induction gs with
  | nil => rfl
  | cons a gs ih =>
    simp only [elemsOf, List.length_append, List.length_map, ih, List.length_cons]
    ring

@[expose] def isStrictAsc : List ℕ → Bool
  | [] => true
  | [_] => true
  | a :: b :: l => decide (a < b) && isStrictAsc (b :: l)

theorem pairwise_of_isStrictAsc : ∀ l : List ℕ, isStrictAsc l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: l, h => by
    simp only [isStrictAsc, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := pairwise_of_isStrictAsc (b :: l) h.2
    refine List.Pairwise.cons ?_ ih
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.1
    · exact h.1.trans ((List.pairwise_cons.1 ih).1 x hx)

theorem nodup_of_sorted_isStrictAsc {l : List ℕ}
    (h : isStrictAsc (l.mergeSort (fun a b => decide (a ≤ b))) = true) : l.Nodup := by
  have hp := List.mergeSort_perm l (fun a b => decide (a ≤ b))
  exact hp.nodup_iff.1 (List.Pairwise.imp (fun h' => ne_of_lt h') (pairwise_of_isStrictAsc _ h))

theorem contains_foldl_insert (xs : List ℕ) :
    ∀ (s : Std.HashSet ℕ) (i : ℕ), (xs.foldl (fun s j => s.insert j) s).contains i = true →
      s.contains i = true ∨ i ∈ xs := by
  induction xs with
  | nil => intro s i h; exact Or.inl h
  | cons x xs ih =>
    intro s i h
    rcases ih _ _ h with h1 | h1
    · rw [Std.HashSet.contains_insert] at h1
      simp only [Bool.or_eq_true, beq_iff_eq] at h1
      rcases h1 with rfl | h1
      · exact Or.inr (List.mem_cons_self ..)
      · exact Or.inl h1
    · exact Or.inr (List.mem_cons_of_mem _ h1)

variable {W : Type*} [Group W] {p : ℕ → W} {m N : ℕ} {g : ℕ → W} {edges : Array (Array ℕ)}
  {par lab : Array ℕ}

theorem elemsOf_mem (hT : IsTable p m N g edges par lab) :
    ∀ gs : List ℕ, (∀ a ∈ gs, a < N) → ∀ x ∈ elemsOf (mulIdx edges par lab N) gs,
      x < N ∧ g x ∈ Subgroup.closure (g '' {a | a ∈ gs}) := by
  intro gs
  induction gs with
  | nil =>
    intro _ x hx
    simp only [elemsOf, List.mem_singleton] at hx
    subst hx
    exact ⟨hT.pos, by rw [hT.g0]; exact Subgroup.one_mem _⟩
  | cons a gs ih =>
    intro hgs x hx
    have haN : a < N := hgs a (List.mem_cons_self ..)
    have ih' := ih (fun b hb => hgs b (List.mem_cons_of_mem _ hb))
    have hmono : Subgroup.closure (g '' {b | b ∈ gs}) ≤
        Subgroup.closure (g '' {b | b ∈ a :: gs}) :=
      Subgroup.closure_mono (Set.image_mono fun b hb => List.mem_cons_of_mem _ hb)
    have hga : g a ∈ Subgroup.closure (g '' {b | b ∈ a :: gs}) :=
      Subgroup.subset_closure ⟨a, List.mem_cons_self .., rfl⟩
    have hmul : ∀ i < N, ∀ j < N, mulIdx edges par lab N i j < N ∧
        g (mulIdx edges par lab N i j) = g i * g j := fun i hi j hj =>
      mulIdx_spec hT N i hi.le hi j hj
    simp only [elemsOf, List.mem_append, List.mem_map] at hx
    rcases hx with (hx | ⟨y, hy, rfl⟩) | ⟨y, hy, rfl⟩
    · exact ⟨(ih' x hx).1, hmono (ih' x hx).2⟩
    · obtain ⟨h1, h2⟩ := hmul a haN y (ih' y hy).1
      exact ⟨h1, by rw [h2]; exact Subgroup.mul_mem _ hga (hmono (ih' y hy).2)⟩
    · obtain ⟨h1, h2⟩ := hmul a haN a haN
      obtain ⟨h3, h4⟩ := hmul _ h1 y (ih' y hy).1
      refine ⟨h3, ?_⟩
      rw [h4, h2]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hga hga) (hmono (ih' y hy).2)

@[expose] def tabCheck2 (m N : ℕ) (edges : Array (Array ℕ)) (par lab : Array ℕ) (idZ : ℕ)
    (sets : List (List ℕ)) : Bool :=
  let mul := mulIdx edges par lab N
  let covered : Std.HashSet ℕ :=
    (sets.flatMap (elemsOf mul)).foldl (fun s j => s.insert j) ∅
  decide (0 < idZ ∧ idZ < N) && (mul idZ (mul idZ idZ) == 0) &&
  (List.range m).all (fun k => (edges[idZ]!)[k]! == mul idZ (edges[0]!)[k]!) &&
  sets.all (fun gs => decide (4 ≤ gs.length) && gs.all (fun a => decide (a < N)) &&
    gs.all (fun a => (mul a (mul a a) == 0) && gs.all fun b => mul a b == mul b a) &&
    (elemsOf mul gs).contains idZ &&
    isStrictAsc ((elemsOf mul gs).mergeSort (fun a b => decide (a ≤ b)))) &&
  (List.range N).all (fun i =>
    (mul i (mul i i) != 0) || i == 0 || i == idZ || i == mul idZ idZ || covered.contains i)

theorem tab_sound2 {J : Subgroup W} [Finite J] {idZ : ℕ} {sets : List (List ℕ)}
    (hT : IsTable p m N g edges par lab) (hpJ : ∀ k < m, p k ∈ J)
    (h : tabCheck2 m N edges par lab idZ sets = true) :
    ∃ z : W, z ∈ Subgroup.closure (p '' {k | k < m}) ∧ z ^ 3 = 1 ∧ z ≠ 1 ∧
      (∀ q ∈ Subgroup.closure (p '' {k | k < m}), q * z = z * q) ∧
      ∀ s ∈ Subgroup.closure (p '' {k | k < m}), s ^ 3 = 1 → s ∉ Subgroup.zpowers z →
        ∃ E : Subgroup W, E ≤ J ∧ IsElemAbelian 3 E ∧ 81 ≤ Nat.card E ∧ s ∈ E ∧ z ∈ E := by
  unfold tabCheck2 at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hz, hz3⟩, hzc⟩, hsets⟩, hcover⟩ := h
  have hz3 := beq_iff_eq.1 hz3
  have hzc' : ∀ k < m, (edges[idZ]!)[k]! = mulIdx edges par lab N idZ (edges[0]!)[k]! :=
    fun k hk => beq_iff_eq.1 (List.all_eq_true.1 hzc k (List.mem_range.2 hk))
  set Q := Subgroup.closure (p '' {k | k < m}) with hQ
  have hQJ : Q ≤ J := by
    rw [hQ, Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    exact hpJ k hk
  have hmul : ∀ i < N, ∀ j < N, mulIdx edges par lab N i j < N ∧
      g (mulIdx edges par lab N i j) = g i * g j := fun i hi j hj =>
    mulIdx_spec hT N i hi.le hi j hj
  obtain ⟨hz0, hzN⟩ := of_decide_eq_true hz
  have hzmem : g idZ ∈ Q := g_mem hT idZ hzN
  have hzcube : g idZ ^ 3 = 1 := by
    obtain ⟨h1, h2⟩ := hmul idZ hzN idZ hzN
    obtain ⟨h3, h4⟩ := hmul idZ hzN _ h1
    have : g (mulIdx edges par lab N idZ (mulIdx edges par lab N idZ idZ)) = g 0 := by rw [hz3]
    rw [h4, h2, hT.g0] at this
    rw [pow_three]
    exact this
  have hzne : g idZ ≠ 1 := by
    intro h1
    rw [← hT.g0] at h1
    exact hz0.ne' (hT.inj _ hzN _ hT.pos h1)
  have hcentral : ∀ q ∈ Q, q * g idZ = g idZ * q := by
    have hle : Q ≤ Subgroup.centralizer {g idZ} := by
      rw [hQ, Subgroup.closure_le]
      rintro _ ⟨k, hk, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      obtain ⟨h1, h2⟩ := hT.edge idZ hzN k hk
      obtain ⟨h3, h4⟩ := hT.edge 0 hT.pos k hk
      obtain ⟨h5, h6⟩ := hmul idZ hzN _ h3
      have e1 : g ((edges[idZ]!)[k]!) = g (mulIdx edges par lab N idZ (edges[0]!)[k]!) := by
        rw [hzc' k hk]
      rw [h2, h6, h4, hT.g0, mul_one] at e1
      exact e1
    exact fun q hq => Subgroup.mem_centralizer_singleton_iff.1 (hle hq)
  refine ⟨g idZ, hzmem, hzcube, hzne, hcentral, ?_⟩
  intro s hsQ hs3 hsz
  obtain ⟨i, hiN, rfl⟩ := hT.surj s hsQ
  have hcube0 : mulIdx edges par lab N i (mulIdx edges par lab N i i) = 0 := by
    obtain ⟨h1, h2⟩ := hmul i hiN i hiN
    obtain ⟨h3, h4⟩ := hmul i hiN _ h1
    have : g (mulIdx edges par lab N i (mulIdx edges par lab N i i)) = g 0 := by
      rw [h4, h2, hT.g0, ← pow_three]
      exact hs3
    exact hT.inj _ h3 _ hT.pos this
  have hc := List.all_eq_true.1 hcover i (List.mem_range.2 hiN)
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hc
  rcases hc with ((((hc | hc) | hc) | hc) | hc)
  · exact absurd hcube0 hc
  · exact absurd (by rw [hc, hT.g0]; exact Subgroup.one_mem _) hsz
  · exact absurd (by rw [hc]; exact Subgroup.mem_zpowers _) hsz
  · obtain ⟨h1, h2⟩ := hmul idZ hzN idZ hzN
    refine absurd ?_ hsz
    rw [hc, h2]
    exact Subgroup.mul_mem _ (Subgroup.mem_zpowers _) (Subgroup.mem_zpowers _)
  ·
    obtain ⟨gs, hgs, hig⟩ : ∃ gs ∈ sets, i ∈ elemsOf (mulIdx edges par lab N) gs := by
      rcases contains_foldl_insert _ _ _ hc with h0 | h0
      · simp at h0
      · obtain ⟨gs, hgs, hig⟩ := List.mem_flatMap.1 h0
        exact ⟨gs, hgs, hig⟩
    have hts := List.all_eq_true.1 hsets gs hgs
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
      List.contains_iff_mem] at hts
    obtain ⟨⟨⟨⟨h4, hgN⟩, hcomm⟩, hzt⟩, hsort⟩ := hts
    set S : Set W := g '' {a | a ∈ gs} with hS
    have hSQ : S ⊆ Q := by
      rintro _ ⟨a, ha, rfl⟩
      exact g_mem hT a (hgN a ha)
    set E := Subgroup.closure S with hE
    have hEJ : E ≤ J := by
      rw [hE, Subgroup.closure_le]
      exact fun x hx => hQJ (hSQ hx)
    refine ⟨E, hEJ, ?_, ?_, (elemsOf_mem hT gs hgN i hig).2,
      (elemsOf_mem hT gs hgN idZ hzt).2⟩
    · refine isElemAbelian_closure_of_comm ?_ ?_
      · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
        have hab := (hcomm a ha).2 b hb
        obtain ⟨h1, h2⟩ := hmul a (hgN a ha) b (hgN b hb)
        obtain ⟨h3, h5⟩ := hmul b (hgN b hb) a (hgN a ha)
        show g a * g b = g b * g a
        rw [← h2, ← h5, hab]
      · rintro _ ⟨a, ha, rfl⟩
        have haN := hgN a ha
        obtain ⟨h1, h2⟩ := hmul a haN a haN
        obtain ⟨h3, h5⟩ := hmul a haN _ h1
        have := (hcomm a ha).1
        rw [this, hT.g0] at h5
        rw [pow_three, ← h2, ← h5]
    · have : Finite E := Finite.of_injective (Subgroup.inclusion hEJ)
        (Subgroup.inclusion_injective hEJ)
      have hnd : (elemsOf (mulIdx edges par lab N) gs).Nodup := nodup_of_sorted_isStrictAsc hsort
      set L := elemsOf (mulIdx edges par lab N) gs with hL
      have hLN : ∀ x ∈ L, x < N := fun x hx => (elemsOf_mem hT gs hgN x hx).1
      have hinj : Set.InjOn g {a | a ∈ L} := fun a ha b hb hab =>
        hT.inj a (hLN a ha) b (hLN b hb) hab
      have hcard : (g '' {a | a ∈ L}).ncard = L.length := by
        rw [hinj.ncard_image]
        have : {a | a ∈ L} = (L.toFinset : Set ℕ) := by ext a; simp
        rw [this, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd]
      have hsub : g '' {a | a ∈ L} ⊆ (E : Set W) := by
        rintro _ ⟨a, ha, rfl⟩
        exact (elemsOf_mem hT gs hgN a ha).2
      have : Finite (E : Set W) := inferInstanceAs (Finite E)
      have hle : (g '' {a | a ∈ L}).ncard ≤ (E : Set W).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
      have hlen : L.length = 3 ^ gs.length := length_elemsOf _ gs
      calc 81 = 3 ^ 4 := by norm_num
        _ ≤ 3 ^ gs.length := Nat.pow_le_pow_right (by norm_num) h4
        _ = L.length := hlen.symm
        _ = (g '' {a | a ∈ L}).ncard := hcard.symm
        _ ≤ (E : Set W).ncard := hle
        _ = Nat.card E := (Nat.card_coe_set_eq (E : Set W)).symm

end CFSG.RankThree.PartTwo.Sec4.Item434SporE81
