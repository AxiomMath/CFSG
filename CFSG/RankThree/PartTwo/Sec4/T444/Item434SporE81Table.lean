module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporE81Gen

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434SporE81

open CFSG.Assembly (IsElemAbelian)

@[expose] def mulIdx (edges : Array (Array ℕ)) (par lab : Array ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, j => j
  | f + 1, i, j => if i = 0 then j else (edges[mulIdx edges par lab f par[i]! j]!)[lab[i]!]!

structure IsTable {W : Type*} [Group W] (p : ℕ → W) (m N : ℕ) (g : ℕ → W)
    (edges : Array (Array ℕ)) (par lab : Array ℕ) : Prop where
  pos : 0 < N
  g0 : g 0 = 1
  edge : ∀ i < N, ∀ k < m, (edges[i]!)[k]! < N ∧ g (edges[i]!)[k]! = p k * g i
  tree : ∀ i < N, 0 < i → par[i]! < i ∧ lab[i]! < m ∧ g i = p lab[i]! * g par[i]!
  inj : ∀ i < N, ∀ j < N, g i = g j → i = j
  surj : ∀ x ∈ Subgroup.closure (p '' {k | k < m}), ∃ i < N, g i = x

variable {W : Type*} [Group W] {p : ℕ → W} {m N : ℕ} {g : ℕ → W} {edges : Array (Array ℕ)}
  {par lab : Array ℕ}

theorem mulIdx_spec (hT : IsTable p m N g edges par lab) :
    ∀ f i, i ≤ f → i < N → ∀ j < N, mulIdx edges par lab f i j < N ∧
      g (mulIdx edges par lab f i j) = g i * g j := by
  intro f
  induction f with
  | zero =>
    intro i hi hiN j hj
    have h0 : i = 0 := by omega
    subst h0
    simp [mulIdx, hT.g0, hj]
  | succ f ih =>
    intro i hi hiN j hj
    by_cases h0 : i = 0
    · subst h0
      simp [mulIdx, hT.g0, hj]
    · obtain ⟨hp, hl, hg⟩ := hT.tree i hiN (Nat.pos_of_ne_zero h0)
      obtain ⟨h1, h2⟩ := ih (par[i]!) (by omega) (by omega) j hj
      obtain ⟨h3, h4⟩ := hT.edge _ h1 lab[i]! hl
      simp only [mulIdx, h0, ite_false]
      refine ⟨h3, ?_⟩
      rw [h4, h2, hg, mul_assoc]

theorem g_mem (hT : IsTable p m N g edges par lab) :
    ∀ i < N, g i ∈ Subgroup.closure (p '' {k | k < m}) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    by_cases h0 : i = 0
    · subst h0
      rw [hT.g0]
      exact Subgroup.one_mem _
    · obtain ⟨hp, hl, hg⟩ := hT.tree i hi (Nat.pos_of_ne_zero h0)
      rw [hg]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨_, hl, rfl⟩)
        (ih _ hp (hp.trans hi))

@[expose] def tabCheck (m N : ℕ) (edges : Array (Array ℕ)) (par lab : Array ℕ) (idZ : ℕ)
    (sets : List (List ℕ)) : Bool :=
  let mul := mulIdx edges par lab N
  decide (0 < idZ ∧ idZ < N) && (mul idZ (mul idZ idZ) == 0) &&
  (List.range m).all (fun k => (edges[idZ]!)[k]! == mul idZ (edges[0]!)[k]!) &&
  sets.all (fun s => decide (81 ≤ s.length) && decide (s.Pairwise (· < ·)) &&
    s.all (fun a => decide (a < N)) && s.contains idZ &&
    s.all (fun a => (mul a (mul a a) == 0) && s.all fun b => mul a b == mul b a)) &&
  (List.range N).all (fun i =>
    (mul i (mul i i) != 0) || i == 0 || i == idZ || i == mul idZ idZ ||
      sets.any (fun s => s.contains i))

theorem tab_sound {J : Subgroup W} [Finite J] {idZ : ℕ} {sets : List (List ℕ)}
    (hT : IsTable p m N g edges par lab) (hpJ : ∀ k < m, p k ∈ J)
    (h : tabCheck m N edges par lab idZ sets = true) :
    ∃ z : W, z ∈ Subgroup.closure (p '' {k | k < m}) ∧ z ^ 3 = 1 ∧ z ≠ 1 ∧
      (∀ q ∈ Subgroup.closure (p '' {k | k < m}), q * z = z * q) ∧
      ∀ s ∈ Subgroup.closure (p '' {k | k < m}), s ^ 3 = 1 → s ∉ Subgroup.zpowers z →
        ∃ E : Subgroup W, E ≤ J ∧ IsElemAbelian 3 E ∧ 81 ≤ Nat.card E ∧ s ∈ E ∧ z ∈ E := by
  unfold tabCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hz, hz3⟩, hzc⟩, hsets⟩, hcover⟩ := h
  have hz3 := beq_iff_eq.1 hz3
  have hzc' : ∀ k < m, (edges[idZ]!)[k]! = mulIdx edges par lab N idZ (edges[0]!)[k]! := fun k hk =>
    beq_iff_eq.1 (List.all_eq_true.1 hzc k (List.mem_range.2 hk))
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
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, List.any_eq_true,
    List.contains_iff_mem] at hc
  rcases hc with ((((hc | hc) | hc) | hc) | ⟨t, ht, hit⟩)
  · exact absurd hcube0 hc
  · exact absurd (by rw [hc, hT.g0]; exact Subgroup.one_mem _) hsz
  · exact absurd (by rw [hc]; exact Subgroup.mem_zpowers _) hsz
  · obtain ⟨h1, h2⟩ := hmul idZ hzN idZ hzN
    refine absurd ?_ hsz
    rw [hc, h2]
    exact Subgroup.mul_mem _ (Subgroup.mem_zpowers _) (Subgroup.mem_zpowers _)
  ·
    have hts := List.all_eq_true.1 hsets t ht
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
      List.contains_iff_mem] at hts
    obtain ⟨⟨⟨⟨h81, hsort⟩, htN⟩, hzt⟩, hcomm⟩ := hts
    set S : Set W := g '' {a | a ∈ t} with hS
    have hSQ : S ⊆ Q := by
      rintro _ ⟨a, ha, rfl⟩
      exact g_mem hT a (htN a ha)
    set E := Subgroup.closure S with hE
    have hEJ : E ≤ J := by
      rw [hE, Subgroup.closure_le]
      exact fun x hx => hQJ (hSQ hx)
    refine ⟨E, hEJ, ?_, ?_, Subgroup.subset_closure ⟨i, hit, rfl⟩,
      Subgroup.subset_closure ⟨idZ, hzt, rfl⟩⟩
    · refine isElemAbelian_closure_of_comm ?_ ?_
      · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
        have hab := (hcomm a ha).2 b hb
        obtain ⟨h1, h2⟩ := hmul a (htN a ha) b (htN b hb)
        obtain ⟨h3, h4⟩ := hmul b (htN b hb) a (htN a ha)
        show g a * g b = g b * g a
        rw [← h2, ← h4, hab]
      · rintro _ ⟨a, ha, rfl⟩
        have haN := htN a ha
        obtain ⟨h1, h2⟩ := hmul a haN a haN
        obtain ⟨h3, h4⟩ := hmul a haN _ h1
        have := (hcomm a ha).1
        rw [this, hT.g0] at h4
        rw [pow_three, ← h2, ← h4]
    · have : Finite E := Finite.of_injective (Subgroup.inclusion hEJ)
        (Subgroup.inclusion_injective hEJ)
      have hnd : t.Nodup := hsort.imp (fun h => ne_of_lt h)
      have hinj : Set.InjOn g {a | a ∈ t} := fun a ha b hb hab =>
        hT.inj a (htN a ha) b (htN b hb) hab
      have hcard : S.ncard = t.length := by
        rw [hS, hinj.ncard_image]
        have : {a | a ∈ t} = (t.toFinset : Set ℕ) := by ext a; simp
        rw [this, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd]
      have : Finite (E : Set W) := inferInstanceAs (Finite E)
      have hle : S.ncard ≤ (E : Set W).ncard :=
        Set.ncard_le_ncard (Subgroup.subset_closure) (Set.toFinite _)
      calc 81 ≤ t.length := h81
        _ = S.ncard := hcard.symm
        _ ≤ (E : Set W).ncard := hle
        _ = Nat.card E := (Nat.card_coe_set_eq (E : Set W)).symm

end CFSG.RankThree.PartTwo.Sec4.Item434SporE81
