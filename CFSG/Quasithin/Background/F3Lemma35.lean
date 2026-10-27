module

public import CFSG.Quasithin.Background.F3Cover

public section

namespace CFSG.Quasithin

universe u

variable {V : Type u} {Γ : SimpleGraph V}

namespace GPath

variable {n : ℕ}

theorem take_take (p : GPath Γ n) (k j : ℕ) (hk : k ≤ n) (hj : j ≤ k) :
    (p.take k hk).take j hj = p.take j (hj.trans hk) :=
  ext' fun i hi => by
    simp [take_apply_of_le _ _ _ hi, take_apply_of_le _ _ _ (hi.trans hj)]

theorem snoc_take_self (p : GPath Γ n) (w : V) (h : Γ.Adj (p n) w) :
    (p.snoc w h).take n (Nat.le_succ n) = p :=
  ext' fun i hi => by
    simp [take_apply_of_le _ _ _ hi, snoc_of_le _ _ _ hi]

theorem smul_take {H : Type*} [Group H] [MulAction H V] [GraphAction H Γ] (g : H) (p : GPath Γ n)
    (k : ℕ) (hk : k ≤ n) : (g • p).take k hk = g • p.take k hk :=
  ext' fun i hi => by simp [take_apply_of_le _ _ _ hi]

theorem noBack_snoc {p : GPath Γ n} (hp : p.NoBack) {w : V} (h : Γ.Adj (p n) w)
    (hw : 1 ≤ n → w ≠ p (n - 1)) : (p.snoc w h).NoBack := by
  intro i hi heq
  by_cases h2 : i + 2 ≤ n
  · rw [snoc_of_le _ _ _ (by omega), snoc_of_le _ _ _ h2] at heq
    exact hp i h2 heq
  · have hi' : i + 2 = n + 1 := by omega
    have hin : i = n - 1 := by omega
    rw [snoc_of_le _ _ _ (by omega), hi', snoc_last] at heq
    exact hw (by omega) (by rw [← heq, hin])

theorem noBack_snoc_last_ne {p : GPath Γ n} {w : V} {h : Γ.Adj (p n) w} (hp : (p.snoc w h).NoBack)
    (hn : 1 ≤ n) : w ≠ p (n - 1) := by
  intro heq
  apply hp (n - 1) (by omega)
  rw [snoc_of_le _ _ _ (by omega), show n - 1 + 2 = n + 1 by omega, snoc_last, heq]

@[expose] def F35Conclusion (Γ : SimpleGraph V) (H : Type*) [Group H] [MulAction H V]
    [GraphAction H Γ] (u : V) (m : ℕ) (p : GPath Γ (m + 1)) : Prop :=
    (∀ i ≤ m, Γ.dist u (p i) = i) ∧
    (∀ i ≤ m, ∀ q : GPath Γ i, q ∈ nbPaths Γ u i → Γ.dist u (q i) = i) ∧
    (∀ i ≤ m, ∀ v w : V, Γ.dist u v = i → Γ.dist u w = i → ∃ g : H, g • u = u ∧ g • v = w) ∧
    (∀ (i : ℕ) (hi : i < m), ∀ q : GPath Γ i, q 0 = u → q i = p i → q.IsGeodesic →
      q = p.take i (by omega)) ∧
    (∀ i < m, Set.BijOn (fun q : GPath Γ i => q i) (nbPaths Γ u i) {v | Γ.dist u v = i}) ∧
    ((∀ p' ∈ nbPaths Γ u (m + 1), Γ.dist u (p' (m + 1)) = m + 1 ∧
        ∀ q : GPath Γ m, q 0 = u → q.IsGeodesic → q m = p' m → q = p'.take m (by omega)) ∨
      ((∀ v : V, Γ.dist u v ≤ m) ∧
        (∀ y, Γ.Adj (p m) y → Γ.dist u y = m - 1) ∧
        (∀ y, Γ.Adj (p m) y →
          ∃! t : GPath Γ m, t 0 = u ∧ t m = p m ∧ t.IsGeodesic ∧ t (m - 1) = y) ∧
        (∀ y₁ y₂ z₁ z₂ : V, Γ.Adj (p m) y₁ → Γ.Adj (p m) y₂ → Γ.Adj (p m) z₁ → Γ.Adj (p m) z₂ →
          y₁ ≠ y₂ → z₁ ≠ z₂ → ∃ g : H, g • u = u ∧ g • p m = p m ∧ g • y₁ = z₁ ∧ g • y₂ = z₂) ∧
        (∀ t₁ t₂ t₃ t₄ : GPath Γ m, (t₁ 0 = u ∧ t₁ m = p m ∧ t₁.IsGeodesic) →
          (t₂ 0 = u ∧ t₂ m = p m ∧ t₂.IsGeodesic) → (t₃ 0 = u ∧ t₃ m = p m ∧ t₃.IsGeodesic) →
          (t₄ 0 = u ∧ t₄ m = p m ∧ t₄.IsGeodesic) → t₁ ≠ t₂ → t₃ ≠ t₄ →
          ∃ g : H, g • u = u ∧ g • p m = p m ∧ g • t₁ = t₃ ∧ g • t₂ = t₄))) ∧
    ((∀ y, Γ.Adj (p (m + 1)) y → y ≠ p m → ¬ ∀ g ∈ (p.stabPath : Subgroup H), g • y = y) →
      Γ.dist u (p (m + 1)) = m + 1)

section Trans

variable {H : Type*} [Group H] [MulAction H V] [GraphAction H Γ] {u : V} {m : ℕ}

theorem exists_extension (hval : ∀ v a b : V, ∃ w, Γ.Adj v w ∧ w ≠ a ∧ w ≠ b) {n : ℕ}
    {q : GPath Γ n} (hq : q ∈ nbPaths Γ u n) :
    ∃ (w : V) (h : Γ.Adj (q n) w), q.snoc w h ∈ nbPaths Γ u (n + 1) := by
  obtain ⟨w, hw, hwa, -⟩ := hval (q n) (q (n - 1)) (q (n - 1))
  refine ⟨w, hw, ?_, noBack_snoc hq.2 hw (fun _ => hwa)⟩
  rw [snoc_of_le _ _ _ (Nat.zero_le n)]
  exact hq.1

variable (hval : ∀ v a b : V, ∃ w, Γ.Adj v w ∧ w ≠ a ∧ w ≠ b)
  (htrans : ∀ q q' : GPath Γ (m + 1), q ∈ nbPaths Γ u (m + 1) → q' ∈ nbPaths Γ u (m + 1) →
    ∃ g : H, g • u = u ∧ g • q = q')

include hval htrans in
theorem trans_le : ∀ (k n : ℕ), n + k = m + 1 → ∀ q q' : GPath Γ n, q ∈ nbPaths Γ u n →
    q' ∈ nbPaths Γ u n → ∃ g : H, g • u = u ∧ g • q = q' := by
  intro k
  induction k with
  | zero =>
    intro n hn q q' hq hq'
    have : n = m + 1 := by omega
    subst this
    exact htrans q q' hq hq'
  | succ k ih =>
    intro n hn q q' hq hq'
    obtain ⟨w, hw, hqw⟩ := exists_extension hval hq
    obtain ⟨w', hw', hqw'⟩ := exists_extension hval hq'
    obtain ⟨g, hgu, hg⟩ := ih (n + 1) (by omega) _ _ hqw hqw'
    refine ⟨g, hgu, ?_⟩
    have := congrArg (fun r : GPath Γ (n + 1) => r.take n (Nat.le_succ n)) hg
    simpa [smul_take, snoc_take_self] using this

include hval htrans in
theorem exists_fix_path_smul_eq {i : ℕ} (hi : i ≤ m) {q : GPath Γ i} (hq : q ∈ nbPaths Γ u i)
    {y y' : V} (hy : Γ.Adj (q i) y) (hy' : Γ.Adj (q i) y') (hy1 : 1 ≤ i → y ≠ q (i - 1))
    (hy1' : 1 ≤ i → y' ≠ q (i - 1)) :
    ∃ g : H, g • u = u ∧ g • q = q ∧ g • y = y' := by
  have hr : q.snoc y hy ∈ nbPaths Γ u (i + 1) :=
    ⟨by rw [snoc_of_le _ _ _ (Nat.zero_le i)]; exact hq.1, noBack_snoc hq.2 hy hy1⟩
  have hr' : q.snoc y' hy' ∈ nbPaths Γ u (i + 1) :=
    ⟨by rw [snoc_of_le _ _ _ (Nat.zero_le i)]; exact hq.1, noBack_snoc hq.2 hy' hy1'⟩
  obtain ⟨g, hgu, hg⟩ := trans_le hval htrans (m + 1 - (i + 1)) (i + 1) (by omega) _ _ hr hr'
  refine ⟨g, hgu, ?_, ?_⟩
  · have := congrArg (fun r : GPath Γ (i + 1) => r.take i (Nat.le_succ i)) hg
    simpa [smul_take, snoc_take_self] using this
  · have := congrArg (fun r : GPath Γ (i + 1) => r (i + 1)) hg
    simpa using this

variable (hΓ : Γ.Connected)

include hval htrans hΓ in
theorem exists_fix_smul_eq_of_dist {k : ℕ} (hk : k ≤ m + 1) {v w : V} (hv : Γ.dist u v = k)
    (hw : Γ.dist u w = k) : ∃ g : H, g • u = u ∧ g • v = w := by
  obtain ⟨a, ha0, hak, hanb⟩ := exists_geodesic' hΓ u v hv
  obtain ⟨b, hb0, hbk, hbnb⟩ := exists_geodesic' hΓ u w hw
  obtain ⟨g, hgu, hg⟩ := trans_le hval htrans (m + 1 - k) k (by omega) a b ⟨ha0, hanb⟩ ⟨hb0, hbnb⟩
  refine ⟨g, hgu, ?_⟩
  have := congrArg (fun r : GPath Γ k => r k) hg
  simp only [smul_apply] at this
  rw [hak, hbk] at this
  exact this

theorem IsGeodesic.smul (hΓ : Γ.Connected) {n : ℕ} {q : GPath Γ n} (h : q.IsGeodesic) (g : H) :
    (g • q).IsGeodesic := by
  show Γ.dist (g • q 0) (g • q n) = n
  rw [dist_smul hΓ]
  exact h

theorem dist_smul_fix (hΓ : Γ.Connected) {g : H} (hg : g • u = u) (v : V) :
    Γ.dist u (g • v) = Γ.dist u v := by
  have := dist_smul hΓ g u v
  rwa [hg] at this

theorem IsGeodesic.dist_eq (hΓ : Γ.Connected) {n : ℕ} {q : GPath Γ n} (h : q.IsGeodesic) {j : ℕ}
    (hj : j ≤ n) : Γ.dist (q 0) (q j) = j :=
  dist_prefix hΓ q h hj

variable {c : V → Bool} (hc : ∀ a b, Γ.Adj a b → c a ≠ c b)

include hc in
theorem dist_two (hΓ : Γ.Connected) {m : ℕ} (hm : 1 ≤ m) {p : GPath Γ (m + 1)}
    (hp : p ∈ nbPaths Γ u (m + 1)) : Γ.dist u (p 1) = 1 ∧ Γ.dist u (p 2) = 2 := by
  have h1 : Γ.dist u (p 1) = 1 := by
    rw [← hp.1]
    exact SimpleGraph.dist_eq_one_iff_adj.mpr (p.adj 0 (by omega))
  refine ⟨h1, ?_⟩
  have hadj : Γ.Adj (p 1) (p 2) := p.adj 1 (by omega)
  rcases dist_adj_succ_or hΓ hc u hadj with h | h
  · omega
  · exfalso
    have h0 : Γ.dist u (p 2) = 0 := by omega
    have : u = p 2 := (hΓ.dist_eq_zero_iff).mp h0
    exact hp.2 0 (by omega) (by rw [hp.1]; exact this)

theorem IsGeodesic.take (hΓ : Γ.Connected) {n : ℕ} {q : GPath Γ n} (h : q.IsGeodesic) (k : ℕ)
    (hk : k ≤ n) : (q.take k hk).IsGeodesic := by
  show Γ.dist ((q.take k hk) 0) ((q.take k hk) k) = k
  rw [take_apply_of_le _ _ _ (Nat.zero_le k), take_apply_of_le _ _ _ le_rfl]
  exact h.dist_eq hΓ hk

include hΓ hval htrans in
theorem unique_geod_lt {p : GPath Γ (m + 1)} (hp : p ∈ nbPaths Γ u (m + 1)) {n : ℕ}
    (hnm : n ≤ m + 1) (hn : ∀ j ≤ n, Γ.dist u (p j) = j) :
    ∀ (i : ℕ) (hi : i < n), ∀ q : GPath Γ i, q 0 = u → q i = p i → q.IsGeodesic →
      q = p.take i (by omega) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi q hq0 hqi hqg
    by_cases hi0 : i = 0
    · subst hi0
      refine ext' fun j hj => ?_
      have : j = 0 := by omega
      subst this
      rw [hq0, take_apply_of_le _ _ _ le_rfl, hp.1]
    · have hi1 : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr hi0
      by_cases hprev : q (i - 1) = p (i - 1)
      · have hg' : (q.take (i - 1) (by omega)).IsGeodesic := hqg.take hΓ _ _
        have heq := ih (i - 1) (by omega) (by omega) (q.take (i - 1) (by omega))
          (by rw [take_apply_of_le _ _ _ (Nat.zero_le _)]; exact hq0)
          (by rw [take_apply_of_le _ _ _ le_rfl]; exact hprev) hg'
        refine ext' fun j hj => ?_
        by_cases hji : j ≤ i - 1
        · have e1 : (q.take (i - 1) (by omega)) j = (p.take (i - 1) (by omega)) j :=
            congrArg (fun r => r j) heq
          rw [take_apply_of_le _ _ _ hji, take_apply_of_le _ _ _ hji] at e1
          rw [take_apply_of_le _ _ _ hj]
          exact e1
        · have : j = i := by omega
          subst this
          rw [hqi, take_apply_of_le _ _ _ le_rfl]
      · exfalso
        have hadj : Γ.Adj ((p.take i (by omega)) i) (q (i - 1)) := by
          rw [take_apply_of_le _ _ _ le_rfl, ← hqi]
          have := q.adj (i - 1) (by omega)
          rw [Nat.sub_add_cancel hi1] at this
          exact this.symm
        have hr : (p.take i (by omega)).snoc (q (i - 1)) hadj ∈ nbPaths Γ u (i + 1) := by
          refine ⟨?_, noBack_snoc (hp.2.take i _) hadj (fun _ => ?_)⟩
          · rw [snoc_of_le _ _ _ (Nat.zero_le i), take_apply_of_le _ _ _ (Nat.zero_le i)]
            exact hp.1
          · rw [take_apply_of_le _ _ _ (by omega : i - 1 ≤ i)]
            exact hprev
        have hs : p.take (i + 1) (by omega) ∈ nbPaths Γ u (i + 1) :=
          ⟨by rw [take_apply_of_le _ _ _ (Nat.zero_le _)]; exact hp.1, hp.2.take _ _⟩
        obtain ⟨g, hgu, hg⟩ := trans_le hval htrans (m + 1 - (i + 1)) (i + 1) (by omega) _ _ hs hr
        have h1 : g • p (i + 1) = q (i - 1) := by
          have := congrArg (fun r : GPath Γ (i + 1) => r (i + 1)) hg
          simpa [take_apply_of_le _ _ _ (le_refl (i + 1))] using this
        have hd1 : Γ.dist u (g • p (i + 1)) = i + 1 := by
          rw [dist_smul_fix hΓ hgu]
          exact hn (i + 1) (by omega)
        have hd2 : Γ.dist u (q (i - 1)) = i - 1 := by
          have := hqg.dist_eq hΓ (j := i - 1) (by omega)
          rwa [hq0] at this
        rw [h1] at hd1
        omega

theorem _root_.CFSG.Quasithin.GPath.NoBack.ne' {n : ℕ} {p : GPath Γ n} (h : p.NoBack) {i k : ℕ}
    (hk : k = i + 2) (hn : k ≤ n) : p i ≠ p k := by
  subst hk
  exact h i hn

include hΓ hval htrans in
theorem dist_nbr_top {p : GPath Γ (m + 1)} (hp : p ∈ nbPaths Γ u (m + 1)) {j : ℕ} (hj : j + 2 ≤ m)
    (hd : ∀ k ≤ j + 2, Γ.dist u (p k) = k) (hd' : Γ.dist u (p (j + 3)) = j + 1) {y : V}
    (hy : Γ.Adj (p (j + 2)) y) : Γ.dist u y = j + 1 := by
  by_cases hyj : y = p (j + 1)
  · rw [hyj]
    exact hd (j + 1) (by omega)
  · have hq : p.take (j + 2) (by omega) ∈ nbPaths Γ u (j + 2) :=
      ⟨by rw [take_apply_of_le _ _ _ (Nat.zero_le _)]; exact hp.1, hp.2.take _ _⟩
    have e : (p.take (j + 2) (by omega)) (j + 2) = p (j + 2) := take_apply_of_le _ _ _ le_rfl
    have e' : (p.take (j + 2) (by omega)) (j + 1) = p (j + 1) :=
      take_apply_of_le _ _ _ (by omega)
    obtain ⟨g, hgu, -, hg⟩ := exists_fix_path_smul_eq hval htrans (i := j + 2) hj hq
      (y := y) (y' := p (j + 3)) (by rw [e]; exact hy) (by rw [e]; exact p.adj (j + 2) (by omega))
      (fun _ => by rw [show j + 2 - 1 = j + 1 from rfl, e']; exact hyj)
      (fun _ => by
        rw [show j + 2 - 1 = j + 1 from rfl, e']
        exact (hp.2.ne' (i := j + 1) (k := j + 3) (by omega) (by omega)).symm)
    have := dist_smul_fix hΓ hgu y
    rw [hg, hd'] at this
    exact this.symm

include hΓ hval htrans in
theorem dist_nbr_pre {p : GPath Γ (m + 1)} (hp : p ∈ nbPaths Γ u (m + 1)) {j : ℕ} (hj : j + 1 ≤ m)
    (hd : Γ.dist u (p (j + 2)) = j + 2) {y : V} (hy : Γ.Adj (p (j + 1)) y) (hyj : y ≠ p j) :
    Γ.dist u y = j + 2 := by
  have hq : p.take (j + 1) (by omega) ∈ nbPaths Γ u (j + 1) :=
    ⟨by rw [take_apply_of_le _ _ _ (Nat.zero_le _)]; exact hp.1, hp.2.take _ _⟩
  have e : (p.take (j + 1) (by omega)) (j + 1) = p (j + 1) := take_apply_of_le _ _ _ le_rfl
  have e' : (p.take (j + 1) (by omega)) j = p j := take_apply_of_le _ _ _ (by omega)
  obtain ⟨g, hgu, -, hg⟩ := exists_fix_path_smul_eq hval htrans (i := j + 1) hj hq
    (y := p (j + 2)) (y' := y) (by rw [e]; exact p.adj (j + 1) (by omega)) (by rw [e]; exact hy)
    (fun _ => by
      rw [show j + 1 - 1 = j from rfl, e']
      exact (hp.2.ne' (i := j) (k := j + 2) (by omega) (by omega)).symm)
    (fun _ => by rw [show j + 1 - 1 = j from rfl, e']; exact hyj)
  have := dist_smul_fix hΓ hgu (p (j + 2))
  rw [hg, hd] at this
  exact this

include hΓ hc hval htrans in
theorem le_of_maximal {p : GPath Γ (m + 1)} (hp : p ∈ nbPaths Γ u (m + 1)) {j : ℕ}
    (hd : ∀ k ≤ j + 2, Γ.dist u (p k) = k) (hmax : j + 2 < m + 1 → Γ.dist u (p (j + 3)) ≠ j + 3) :
    m ≤ j + 2 := by
  by_contra hlt0
  have hlt : j + 2 < m := not_le.mp hlt0
  have hj3 : Γ.dist u (p (j + 3)) = j + 1 := by
    have hadj : Γ.Adj (p (j + 2)) (p (j + 3)) := p.adj (j + 2) (by omega)
    have hd2 := hd (j + 2) le_rfl
    have hm3 := hmax (by omega)
    rcases dist_adj_succ_or hΓ hc u hadj with h | h
    · exact absurd (by omega) hm3
    · omega
  have hL1 : ∀ y, Γ.Adj (p (j + 2)) y → Γ.dist u y = j + 1 := fun y hy =>
    dist_nbr_top hval htrans hΓ hp (by omega) hd hj3 hy
  have hL2 : ∀ y, Γ.Adj (p (j + 1)) y → y ≠ p j → Γ.dist u y = j + 2 := fun y hy hne =>
    dist_nbr_pre hval htrans hΓ hp (by omega) (hd (j + 2) le_rfl) hy hne
  obtain ⟨g, hgu, hg⟩ := exists_fix_smul_eq_of_dist hval htrans hΓ (k := j + 1) (by omega)
    (v := p (j + 1)) (w := p (j + 3)) (hd (j + 1) (by omega)) hj3
  have hv0adj : Γ.Adj (p (j + 3)) (g • p j) := by
    have := (GraphAction.adj_smul g (p j) (p (j + 1))).mpr (p.adj j (by omega))
    rw [hg] at this
    exact this.symm
  have hv0dist : Γ.dist u (g • p j) = j := by
    rw [dist_smul_fix hΓ hgu]
    exact hd j (by omega)
  have he : ∀ y', Γ.Adj (p (j + 3)) y' → y' ≠ g • p j → Γ.dist u y' = j + 2 := by
    intro y' hy' hne
    have h1 : Γ.Adj (p (j + 1)) (g⁻¹ • y') := by
      have := (GraphAction.adj_smul g⁻¹ (p (j + 3)) y').mpr hy'
      rwa [← hg, inv_smul_smul] at this
    have h2 : g⁻¹ • y' ≠ p j := by
      intro h
      apply hne
      rw [← h, smul_inv_smul]
    have h3 := hL2 _ h1 h2
    have h4 := dist_smul_fix hΓ hgu (g⁻¹ • y')
    rw [smul_inv_smul] at h4
    rw [h4]
    exact h3
  obtain ⟨w, hw, hwa, hwb⟩ := hval (p (j + 3)) (p (j + 2)) (g • p j)
  have hwd : Γ.dist u w = j + 2 := he w hw hwb
  have eT : (p.take (j + 3) (by omega)) (j + 3) = p (j + 3) := take_apply_of_le _ _ _ le_rfl
  have eT' : (p.take (j + 3) (by omega)) (j + 2) = p (j + 2) := take_apply_of_le _ _ _ (by omega)
  have hadr : Γ.Adj ((p.take (j + 3) (by omega)) (j + 3)) (g • p j) := by rw [eT]; exact hv0adj
  have hads : Γ.Adj ((p.take (j + 3) (by omega)) (j + 3)) w := by rw [eT]; exact hw
  have h0 : (p.take (j + 3) (by omega)) 0 = u := by
    rw [take_apply_of_le _ _ _ (Nat.zero_le _)]
    exact hp.1
  have hr : (p.take (j + 3) (by omega)).snoc (g • p j) hadr ∈ nbPaths Γ u (j + 4) := by
    refine ⟨by rw [snoc_of_le _ _ _ (Nat.zero_le _)]; exact h0,
      noBack_snoc (hp.2.take _ _) hadr (fun _ => ?_)⟩
    rw [show j + 3 - 1 = j + 2 from rfl, eT']
    intro h
    have h5 := hd (j + 2) le_rfl
    rw [← h, hv0dist] at h5
    omega
  have hs : (p.take (j + 3) (by omega)).snoc w hads ∈ nbPaths Γ u (j + 4) := by
    refine ⟨by rw [snoc_of_le _ _ _ (Nat.zero_le _)]; exact h0,
      noBack_snoc (hp.2.take _ _) hads (fun _ => ?_)⟩
    rw [show j + 3 - 1 = j + 2 from rfl, eT']
    exact hwa
  obtain ⟨g', hg'u, hg'⟩ := trans_le hval htrans (m + 1 - (j + 4)) (j + 4) (by omega) _ _ hr hs
  have h6 : g' • (g • p j) = w := by
    have := congrArg (fun r : GPath Γ (j + 4) => r (j + 4)) hg'
    simpa using this
  have h7 := dist_smul_fix hΓ hg'u (g • p j)
  rw [h6, hwd, hv0dist] at h7
  omega

theorem smul_inv_smul' {n : ℕ} (g : H) (q : GPath Γ n) : g • g⁻¹ • q = q :=
  ext' fun i _ => by simp

theorem inv_smul_smul' {n : ℕ} (g : H) (q : GPath Γ n) : g⁻¹ • g • q = q :=
  ext' fun i _ => by simp

include hΓ hval htrans in
theorem unique_geod_sphere {p : GPath Γ (m + 1)} (hp : p ∈ nbPaths Γ u (m + 1)) {n : ℕ}
    (hnm : n ≤ m + 1) (hn : ∀ j ≤ n, Γ.dist u (p j) = j) {i : ℕ} (hi : i < n) {v : V}
    (hv : Γ.dist u v = i) (q q' : GPath Γ i) (hq0 : q 0 = u) (hq0' : q' 0 = u) (hqv : q i = v)
    (hqv' : q' i = v) (hg : q.IsGeodesic) (hg' : q'.IsGeodesic) : q = q' := by
  obtain ⟨g, hgu, hgv⟩ := exists_fix_smul_eq_of_dist hval htrans hΓ (k := i) (by omega)
    (v := p i) (w := v) (hn i hi.le) hv
  have hginv : g⁻¹ • u = u := by
    rw [inv_smul_eq_iff]
    exact hgu.symm
  have key : ∀ r : GPath Γ i, r 0 = u → r i = v → r.IsGeodesic → g⁻¹ • r = p.take i (by omega) := by
    intro r hr0 hri hrg
    refine unique_geod_lt hval htrans hΓ hp hnm hn i hi (g⁻¹ • r) ?_ ?_ (hrg.smul hΓ g⁻¹)
    · rw [smul_apply, hr0, hginv]
    · rw [smul_apply, hri, ← hgv, inv_smul_smul]
  have h1 := key q hq0 hqv hg
  have h2 := key q' hq0' hqv' hg'
  rw [← smul_inv_smul' g q, h1, ← smul_inv_smul' g q', h2]

include hΓ hc in
theorem exists_maximal {p : GPath Γ (m + 1)} (hm : 1 ≤ m) (hp : p ∈ nbPaths Γ u (m + 1)) :
    ∃ n : ℕ, 2 ≤ n ∧ n ≤ m + 1 ∧ (∀ k ≤ n, Γ.dist u (p k) = k) ∧
      (n < m + 1 → Γ.dist u (p (n + 1)) ≠ n + 1) := by
  classical
  let P : ℕ → Prop := fun k => Γ.dist u (p k) = k
  have hP0 : P 0 := by
    show Γ.dist u (p 0) = 0
    rw [hp.1]
    exact SimpleGraph.dist_self
  have hP2 : P 2 := (dist_two hc hΓ hm hp).2
  refine ⟨Nat.findGreatest P (m + 1), Nat.le_findGreatest (by omega) hP2,
    Nat.findGreatest_le _, ?_, fun h => ?_⟩
  · have hn : P (Nat.findGreatest P (m + 1)) := Nat.findGreatest_spec (by omega) hP0
    have hgeo : (p.take (Nat.findGreatest P (m + 1)) (Nat.findGreatest_le _)).IsGeodesic := by
      show Γ.dist _ _ = _
      rw [take_apply_of_le _ _ _ (Nat.zero_le _), take_apply_of_le _ _ _ le_rfl, hp.1]
      exact hn
    intro k hk
    have := hgeo.dist_eq hΓ hk
    rwa [take_apply_of_le _ _ _ (Nat.zero_le _), take_apply_of_le _ _ _ hk, hp.1] at this
  · exact Nat.findGreatest_is_greatest (P := P) (Nat.lt_succ_self _) h

include hΓ hval htrans in
theorem case_top {p : GPath Γ (m + 1)} (hp : p ∈ nbPaths Γ u (m + 1))
    (hd : Γ.dist u (p (m + 1)) = m + 1) :
    ∀ p' ∈ nbPaths Γ u (m + 1), Γ.dist u (p' (m + 1)) = m + 1 ∧
      ∀ q : GPath Γ m, q 0 = u → q.IsGeodesic → q m = p' m → q = p'.take m (by omega) := by
  intro p' hp'
  obtain ⟨g, hgu, hg⟩ := htrans p p' hp hp'
  have hd' : Γ.dist u (p' (m + 1)) = m + 1 := by
    have := congrArg (fun r : GPath Γ (m + 1) => r (m + 1)) hg
    simp only [smul_apply] at this
    rw [← this, dist_smul_fix hΓ hgu]
    exact hd
  refine ⟨hd', fun q hq0 hqg hqm => ?_⟩
  have hgeo : p'.IsGeodesic := by
    show Γ.dist (p' 0) (p' (m + 1)) = m + 1
    rw [hp'.1]
    exact hd'
  have hn : ∀ j ≤ m + 1, Γ.dist u (p' j) = j := fun j hj => by
    have := hgeo.dist_eq hΓ hj
    rwa [hp'.1] at this
  exact unique_geod_lt hval htrans hΓ hp' (le_refl _) hn m (Nat.lt_succ_self m) q hq0 hqm hqg

include hΓ hc hval htrans in
theorem mid_nbr {p : GPath Γ (m + 1)} (hp : p ∈ nbPaths Γ u (m + 1)) (hm2 : 2 ≤ m)
    (hd : ∀ k ≤ m, Γ.dist u (p k) = k) (hlast : Γ.dist u (p (m + 1)) ≠ m + 1) {y : V}
    (hy : Γ.Adj (p m) y) : Γ.dist u y = m - 1 := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
  have hlast' : Γ.dist u (p (j + 3)) ≠ j + 3 := hlast
  have hj3 : Γ.dist u (p (j + 3)) = j + 1 := by
    have hadj : Γ.Adj (p (j + 2)) (p (j + 3)) := p.adj (j + 2) (by omega)
    have hd2 := hd (j + 2) le_rfl
    rcases dist_adj_succ_or hΓ hc u hadj with h | h
    · exact absurd (by omega) hlast'
    · omega
  have := dist_nbr_top hval htrans hΓ hp (j := j) le_rfl hd hj3 hy
  omega

include hΓ htrans in
theorem mid_dist_le {p : GPath Γ (m + 1)} (hp : p ∈ nbPaths Γ u (m + 1))
    (hlast : Γ.dist u (p (m + 1)) ≠ m + 1) (v : V) : Γ.dist u v ≤ m := by
  by_contra hlt0
  have hlt : m < Γ.dist u v := not_le.mp hlt0
  obtain ⟨q, hq0, hqe, hqnb⟩ := exists_geodesic' hΓ u v (n := Γ.dist u v) rfl
  have hqg : q.IsGeodesic := by
    show Γ.dist (q 0) (q (Γ.dist u v)) = Γ.dist u v
    rw [hq0, hqe]
  have hqt : q.take (m + 1) (by omega) ∈ nbPaths Γ u (m + 1) :=
    ⟨by rw [take_apply_of_le _ _ _ (Nat.zero_le _)]; exact hq0, hqnb.take _ _⟩
  obtain ⟨g, hgu, hg⟩ := htrans p _ hp hqt
  have h1 := congrArg (fun r : GPath Γ (m + 1) => r (m + 1)) hg
  simp only [smul_apply, take_apply_of_le _ _ _ (le_refl (m + 1))] at h1
  have h2 := dist_smul_fix hΓ hgu (p (m + 1))
  rw [h1] at h2
  have h3 := hqg.dist_eq hΓ (j := m + 1) (by omega)
  rw [hq0] at h3
  have h4 : Γ.dist u (p (m + 1)) = m + 1 := by rw [← h2]; exact h3
  exact hlast h4

include hΓ hc hval htrans in
theorem mid_unique_through {p : GPath Γ (m + 1)} (hp : p ∈ nbPaths Γ u (m + 1)) (hm2 : 2 ≤ m)
    (hd : ∀ k ≤ m, Γ.dist u (p k) = k) (hlast : Γ.dist u (p (m + 1)) ≠ m + 1) {y : V}
    (hy : Γ.Adj (p m) y) :
    ∃! t : GPath Γ m, t 0 = u ∧ t m = p m ∧ t.IsGeodesic ∧ t (m - 1) = y := by
  have hdy := mid_nbr hval htrans hΓ hc hp hm2 hd hlast hy
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
  have hdy' : Γ.dist u y = j + 1 := by omega
  obtain ⟨a, ha0, hae, -⟩ := exists_geodesic' hΓ u y hdy'
  have hadj : Γ.Adj (a (j + 1)) (p (j + 2)) := by rw [hae]; exact hy.symm
  have hmj : j + 2 - 1 = j + 1 := rfl
  refine ⟨a.snoc (p (j + 2)) hadj, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [snoc_of_le _ _ _ (Nat.zero_le _)]
    exact ha0
  · rw [snoc_last]
  · show Γ.dist ((a.snoc (p (j + 2)) hadj) 0) ((a.snoc (p (j + 2)) hadj) (j + 2)) = j + 2
    rw [snoc_of_le _ _ _ (Nat.zero_le _), snoc_last, ha0, hd (j + 2) le_rfl]
  · rw [hmj, snoc_of_le _ _ _ le_rfl]
    exact hae
  · rintro t ⟨ht0, htm, htg, hty⟩
    have hgt : (t.take (j + 1) (by omega)).IsGeodesic := htg.take hΓ _ _
    have hgt' : (a.take (j + 1) le_rfl).IsGeodesic := by
      show Γ.dist ((a.take (j + 1) le_rfl) 0) ((a.take (j + 1) le_rfl) (j + 1)) = j + 1
      rw [take_apply_of_le _ _ _ (Nat.zero_le _), take_apply_of_le _ _ _ le_rfl, ha0, hae]
      exact hdy'
    have hag : a.IsGeodesic := by
      show Γ.dist (a 0) (a (j + 1)) = j + 1
      rw [ha0, hae]
      exact hdy'
    have heq : t.take (j + 1) (by omega) = a := by
      refine unique_geod_sphere hval htrans hΓ hp (n := j + 2) (by omega) hd (by omega)
        hdy' _ _ ?_ ha0 ?_ hae hgt hag
      · rw [take_apply_of_le _ _ _ (Nat.zero_le _)]
        exact ht0
      · rw [take_apply_of_le _ _ _ le_rfl, ← hmj]
        exact hty
    refine ext' fun i hi => ?_
    by_cases hi' : i ≤ j + 1
    · have := congrArg (fun r : GPath Γ (j + 1) => r i) heq
      simp only [take_apply_of_le _ _ _ hi'] at this
      rw [this, snoc_of_le _ _ _ hi']
    · have : i = j + 2 := by omega
      subst this
      rw [htm, snoc_last]

include hΓ hc hval htrans in
theorem mid_trans_pts {p : GPath Γ (m + 1)} (hp : p ∈ nbPaths Γ u (m + 1)) (hm2 : 2 ≤ m)
    (hd : ∀ k ≤ m, Γ.dist u (p k) = k) (hlast : Γ.dist u (p (m + 1)) ≠ m + 1) {y z : V}
    (hy : Γ.Adj (p m) y) (hz : Γ.Adj (p m) z) :
    ∃ g : H, g • u = u ∧ g • p m = p m ∧ g • y = z := by
  obtain ⟨ty, ⟨ty0, tym, tyg, tyy⟩, -⟩ := mid_unique_through hval htrans hΓ hc hp hm2 hd hlast hy
  obtain ⟨tz, ⟨tz0, tzm, tzg, tzz⟩, -⟩ := mid_unique_through hval htrans hΓ hc hp hm2 hd hlast hz
  obtain ⟨g, hgu, hg⟩ := trans_le hval htrans 1 m (by omega) ty tz
    ⟨ty0, noBack_of_dist_eq hΓ ty tyg⟩ ⟨tz0, noBack_of_dist_eq hΓ tz tzg⟩
  refine ⟨g, hgu, ?_, ?_⟩
  · have := congrArg (fun r : GPath Γ m => r m) hg
    simp only [smul_apply] at this
    rwa [tym, tzm] at this
  · have := congrArg (fun r : GPath Γ m => r (m - 1)) hg
    simp only [smul_apply] at this
    rwa [tyy, tzz] at this

include hΓ hc hval htrans in
theorem mid_two_trans {p : GPath Γ (m + 1)} (hp : p ∈ nbPaths Γ u (m + 1)) (hm2 : 2 ≤ m)
    (hd : ∀ k ≤ m, Γ.dist u (p k) = k) (hlast : Γ.dist u (p (m + 1)) ≠ m + 1) {y₁ y₂ z₁ z₂ : V}
    (hy₁ : Γ.Adj (p m) y₁) (hy₂ : Γ.Adj (p m) y₂) (hz₁ : Γ.Adj (p m) z₁) (hz₂ : Γ.Adj (p m) z₂)
    (hyne : y₁ ≠ y₂) (hzne : z₁ ≠ z₂) :
    ∃ g : H, g • u = u ∧ g • p m = p m ∧ g • y₁ = z₁ ∧ g • y₂ = z₂ := by
  obtain ⟨g₁, hg₁u, hg₁m, hg₁⟩ := mid_trans_pts hval htrans hΓ hc hp hm2 hd hlast hy₁ hz₁
  have hy₂' : Γ.Adj (p m) (g₁ • y₂) := by
    have := (GraphAction.adj_smul g₁ (p m) y₂).mpr hy₂
    rwa [hg₁m] at this
  have hne : g₁ • y₂ ≠ z₁ := by
    intro h
    apply hyne
    rw [← hg₁] at h
    exact (smul_left_cancel g₁ h).symm
  obtain ⟨t, ⟨t0, tm, tg, tz⟩, -⟩ := mid_unique_through hval htrans hΓ hc hp hm2 hd hlast hz₁
  have htn : t ∈ nbPaths Γ u m := ⟨t0, noBack_of_dist_eq hΓ t tg⟩
  obtain ⟨g₂, hg₂u, hg₂t, hg₂⟩ := exists_fix_path_smul_eq hval htrans (i := m) le_rfl htn
    (y := g₁ • y₂) (y' := z₂) (by rw [tm]; exact hy₂') (by rw [tm]; exact hz₂)
    (fun _ => by rw [tz]; exact hne) (fun _ => by rw [tz]; exact hzne.symm)
  have hg₂m : g₂ • p m = p m := by
    have := congrArg (fun r : GPath Γ m => r m) hg₂t
    simp only [smul_apply] at this
    rwa [tm] at this
  have hg₂z : g₂ • z₁ = z₁ := by
    have := congrArg (fun r : GPath Γ m => r (m - 1)) hg₂t
    simp only [smul_apply] at this
    rwa [tz] at this
  refine ⟨g₂ * g₁, ?_, ?_, ?_, ?_⟩
  · rw [mul_smul, hg₁u, hg₂u]
  · rw [mul_smul, hg₁m, hg₂m]
  · rw [mul_smul, hg₁, hg₂z]
  · rw [mul_smul, hg₂]

include hΓ hc hval htrans in
theorem mid_two_trans_geod {p : GPath Γ (m + 1)} (hp : p ∈ nbPaths Γ u (m + 1)) (hm2 : 2 ≤ m)
    (hd : ∀ k ≤ m, Γ.dist u (p k) = k) (hlast : Γ.dist u (p (m + 1)) ≠ m + 1)
    {t₁ t₂ t₃ t₄ : GPath Γ m} (h₁ : t₁ 0 = u ∧ t₁ m = p m ∧ t₁.IsGeodesic)
    (h₂ : t₂ 0 = u ∧ t₂ m = p m ∧ t₂.IsGeodesic) (h₃ : t₃ 0 = u ∧ t₃ m = p m ∧ t₃.IsGeodesic)
    (h₄ : t₄ 0 = u ∧ t₄ m = p m ∧ t₄.IsGeodesic) (hne : t₁ ≠ t₂) (hne' : t₃ ≠ t₄) :
    ∃ g : H, g • u = u ∧ g • p m = p m ∧ g • t₁ = t₃ ∧ g • t₂ = t₄ := by
  have adj : ∀ t : GPath Γ m, t m = p m → Γ.Adj (p m) (t (m - 1)) := fun t htm => by
    have := t.adj (m - 1) (by omega)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ m), htm] at this
    exact this.symm
  have uniq : ∀ t t' : GPath Γ m, (t 0 = u ∧ t m = p m ∧ t.IsGeodesic) →
      (t' 0 = u ∧ t' m = p m ∧ t'.IsGeodesic) → t (m - 1) = t' (m - 1) → t = t' :=
    fun t t' h h' hy => by
      obtain ⟨t'', _, huniq⟩ := mid_unique_through hval htrans hΓ hc hp hm2 hd hlast (adj t h.2.1)
      have e1 := huniq t ⟨h.1, h.2.1, h.2.2, rfl⟩
      have e2 := huniq t' ⟨h'.1, h'.2.1, h'.2.2, hy.symm⟩
      exact e1.trans e2.symm
  have hy : t₁ (m - 1) ≠ t₂ (m - 1) := fun h => hne (uniq t₁ t₂ h₁ h₂ h)
  have hz : t₃ (m - 1) ≠ t₄ (m - 1) := fun h => hne' (uniq t₃ t₄ h₃ h₄ h)
  obtain ⟨g, hgu, hgm, hg1, hg2⟩ := mid_two_trans hval htrans hΓ hc hp hm2 hd hlast
    (adj t₁ h₁.2.1) (adj t₂ h₂.2.1) (adj t₃ h₃.2.1) (adj t₄ h₄.2.1) hy hz
  have back : ∀ t t' : GPath Γ m, (t 0 = u ∧ t m = p m ∧ t.IsGeodesic) →
      (t' 0 = u ∧ t' m = p m ∧ t'.IsGeodesic) → g • t (m - 1) = t' (m - 1) → g • t = t' :=
    fun t t' h h' hgt => by
      refine uniq (g • t) t' ⟨?_, ?_, h.2.2.smul hΓ g⟩ h' ?_
      · rw [smul_apply, h.1, hgu]
      · rw [smul_apply, h.2.1, hgm]
      · rw [smul_apply]
        exact hgt
  exact ⟨g, hgu, hgm, back t₁ t₃ h₁ h₃ hg1, back t₂ t₄ h₂ h₄ hg2⟩

include hΓ hc hval htrans in
theorem mid_fixed {p : GPath Γ (m + 1)} (hp : p ∈ nbPaths Γ u (m + 1)) (hm2 : 2 ≤ m)
    (hd : ∀ k ≤ m, Γ.dist u (p k) = k) (hlast : Γ.dist u (p (m + 1)) ≠ m + 1) :
    ∃ y, Γ.Adj (p (m + 1)) y ∧ y ≠ p m ∧ ∀ g ∈ (p.stabPath : Subgroup H), g • y = y := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
  have hlast' : Γ.dist u (p (j + 3)) ≠ j + 3 := hlast
  have hj3 : Γ.dist u (p (j + 3)) = j + 1 := by
    have hadj : Γ.Adj (p (j + 2)) (p (j + 3)) := p.adj (j + 2) (by omega)
    have hd2 := hd (j + 2) le_rfl
    rcases dist_adj_succ_or hΓ hc u hadj with h | h
    · exact absurd (by omega) hlast'
    · omega
  obtain ⟨a, ha0, hae, -⟩ := exists_geodesic' hΓ u (p (j + 3)) hj3
  have hag : a.IsGeodesic := by
    show Γ.dist (a 0) (a (j + 1)) = j + 1
    rw [ha0, hae]
    exact hj3
  refine ⟨a j, ?_, ?_, ?_⟩
  · have := a.adj j (by omega)
    rw [hae] at this
    exact this.symm
  · intro h
    have h1 := hag.dist_eq hΓ (j := j) (by omega)
    rw [ha0, h] at h1
    have := hd (j + 2) le_rfl
    omega
  · intro g hg
    have hg' : ∀ i, i ≤ j + 2 + 1 → g • p i = p i := hg
    have hgu : g • u = u := by
      have := hg' 0 (Nat.zero_le _)
      rwa [hp.1] at this
    have hgp : g • p (j + 3) = p (j + 3) := hg' (j + 3) le_rfl
    have heq : g • a = a := by
      refine unique_geod_sphere hval htrans hΓ hp (n := j + 2) (by omega) hd (i := j + 1)
        (by omega) hj3 _ _ ?_ ha0 ?_ hae (hag.smul hΓ g) hag
      · rw [smul_apply, ha0, hgu]
      · rw [smul_apply, hae, hgp]
    have := congrArg (fun r : GPath Γ (j + 1) => r j) heq
    simpa using this

include hΓ hc hval htrans in
theorem lemma_F35 (hm : 1 ≤ m) {p : GPath Γ (m + 1)} (hp : p ∈ nbPaths Γ u (m + 1)) :
    F35Conclusion Γ H u m p := by
  unfold F35Conclusion
  obtain ⟨n, hn2, hnm, hd, hmax⟩ := exists_maximal hΓ hc hm hp
  have hmn : m ≤ n := by
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 2 := ⟨n - 2, by omega⟩
    exact le_of_maximal hval htrans hΓ hc hp hd (fun h => hmax h)
  have hd1 : ∀ i ≤ m, Γ.dist u (p i) = i := fun i hi => hd i (by omega)
  have hnbij : ∀ i ≤ m, ∀ q : GPath Γ i, q ∈ nbPaths Γ u i → Γ.dist u (q i) = i := by
    intro i hi q hq
    have hs : p.take i (by omega) ∈ nbPaths Γ u i :=
      ⟨by rw [take_apply_of_le _ _ _ (Nat.zero_le _)]; exact hp.1, hp.2.take _ _⟩
    obtain ⟨g, hgu, hg⟩ := trans_le hval htrans (m + 1 - i) i (by omega) _ _ hs hq
    have h1 := congrArg (fun r : GPath Γ i => r i) hg
    simp only [smul_apply, take_apply_of_le _ _ _ (le_refl i)] at h1
    rw [← h1, dist_smul_fix hΓ hgu]
    exact hd1 i hi
  have h2 : ∀ (i : ℕ) (hi : i < m), ∀ q : GPath Γ i, q 0 = u → q i = p i → q.IsGeodesic →
      q = p.take i (by omega) := fun i hi =>
    unique_geod_lt hval htrans hΓ hp hnm hd i (by omega)
  refine ⟨hd1, hnbij, fun i hi v w hv hw =>
    exists_fix_smul_eq_of_dist hval htrans hΓ (by omega) hv hw, h2, ?_, ?_, ?_⟩
  · intro i hi
    refine ⟨fun q hq => hnbij i hi.le q hq, fun q hq q' hq' hqq => ?_, fun v hv => ?_⟩
    · have hg : q.IsGeodesic := by
        show Γ.dist (q 0) (q i) = i
        rw [hq.1]
        exact hnbij i hi.le q hq
      have hg' : q'.IsGeodesic := by
        show Γ.dist (q' 0) (q' i) = i
        rw [hq'.1]
        exact hnbij i hi.le q' hq'
      exact unique_geod_sphere hval htrans hΓ hp hnm hd (by omega) (hnbij i hi.le q hq) q q'
        hq.1 hq'.1 rfl hqq.symm hg hg'
    · obtain ⟨q, hq0, hqe, hqnb⟩ := exists_geodesic' hΓ u v (n := i) hv
      exact ⟨q, ⟨hq0, hqnb⟩, hqe⟩
  · by_cases hlast : Γ.dist u (p (m + 1)) = m + 1
    · exact Or.inl (case_top hval htrans hΓ hp hlast)
    · right
      have hnm' : n = m := by
        by_contra hne
        have : n = m + 1 := by omega
        subst this
        exact hlast (hd _ le_rfl)
      subst hnm'
      have hm2 : 2 ≤ n := hn2
      refine ⟨mid_dist_le htrans hΓ hp hlast, fun y hy => mid_nbr hval htrans hΓ hc hp hm2 hd hlast hy,
        fun y hy => mid_unique_through hval htrans hΓ hc hp hm2 hd hlast hy,
        fun y₁ y₂ z₁ z₂ h1 h2 h3 h4 hyne hzne =>
          mid_two_trans hval htrans hΓ hc hp hm2 hd hlast h1 h2 h3 h4 hyne hzne,
        fun t₁ t₂ t₃ t₄ h1 h2 h3 h4 hne hne' =>
          mid_two_trans_geod hval htrans hΓ hc hp hm2 hd hlast h1 h2 h3 h4 hne hne'⟩
  · intro H4
    by_contra hlast
    have hnm' : n = m := by
      by_contra hne
      have : n = m + 1 := by omega
      subst this
      exact hlast (hd _ le_rfl)
    subst hnm'
    obtain ⟨y, hy, hne, hfix⟩ := mid_fixed hval htrans hΓ hc hp hn2 hd hlast
    exact H4 y hy hne hfix

end Trans

end GPath

end CFSG.Quasithin
