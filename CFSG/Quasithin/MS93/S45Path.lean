module

public import CFSG.Quasithin.MS93.S4Stmt
import CFSG.Quasithin.MS93.S4ABasic

public section

namespace CFSG.Quasithin.MS93.S45

open CFSG.Quasithin CFSG.Quasithin.Fan86.Univ SimpleGraph

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] (X : GoldAmalgam A C B)

structure IsNBPath (p : ℕ → Vtx X) (N : ℕ) : Prop where
  adj : ∀ i, i < N → X.treeGraph.Adj (p i) (p (i + 1))
  nb : ∀ i, i + 2 ≤ N → p (i + 2) ≠ p i

namespace IsNBPath

variable {X} {p : ℕ → Vtx X} {N : ℕ}

theorem dist_eq (hp : IsNBPath X p N) {i : ℕ} :
    ∀ k, i + k ≤ N → X.treeGraph.dist (p i) (p (i + k)) = k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases k with _ | _ | k
    · simp
    · simpa using dist_eq_one_of_adj X (hp.adj i (by omega))
    · have h1 := ih (k + 1) (by omega) (by omega)
      have h0 := ih k (by omega) (by omega)
      have hadj : X.treeGraph.Adj (p (i + (k + 1))) (p (i + (k + 2))) := by
        simpa [Nat.add_assoc] using hp.adj (i + (k + 1)) (by omega)
      have hadj0 : X.treeGraph.Adj (p (i + k)) (p (i + (k + 1))) := by
        simpa [Nat.add_assoc] using hp.adj (i + k) (by omega)
      rcases dist_adj_cases X hadj (p i) with h2 | h2
      · rw [h2, h1]
      · exfalso
        have h2' : X.treeGraph.dist (p i) (p (i + (k + 2))) = k := by omega
        have e1 : p (i + (k + 2)) = geo X (p i) (p (i + (k + 1))) k := by
          have := eq_geo X (u := p i) (w := p (i + (k + 1))) (x := p (i + (k + 2))) (by
            rw [h2', tdist_comm, dist_eq_one_of_adj X hadj, h1])
          rwa [h2'] at this
        have e2 : p (i + k) = geo X (p i) (p (i + (k + 1))) k := by
          have := eq_geo X (u := p i) (w := p (i + (k + 1))) (x := p (i + k)) (by
            rw [h0, dist_eq_one_of_adj X hadj0, h1])
          rwa [h0] at this
        exact hp.nb (i + k) (by omega) (by
          rw [show i + k + 2 = i + (k + 2) by omega, e1, e2])

theorem dist_eq' (hp : IsNBPath X p N) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ N) :
    X.treeGraph.dist (p i) (p j) = j - i := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  rw [hp.dist_eq k hj]
  omega

theorem eq_geo (hp : IsNBPath X p N) {i j k : ℕ} (hik : i ≤ k) (hkj : k ≤ j) (hj : j ≤ N) :
    p k = geo X (p i) (p j) (k - i) := by
  apply eq_geo_of_dist X (hp.dist_eq' hik (hkj.trans hj))
  rw [hp.dist_eq' hik (hkj.trans hj), hp.dist_eq' hkj hj, hp.dist_eq' (hik.trans hkj) hj]
  omega

theorem eq_geo_rev (hp : IsNBPath X p N) {i j k : ℕ} (hik : i ≤ k) (hkj : k ≤ j) (hj : j ≤ N) :
    p k = geo X (p j) (p i) (j - k) := by
  apply eq_geo_of_dist X (by rw [tdist_comm]; exact hp.dist_eq' hkj hj)
  rw [tdist_comm X (p j), hp.dist_eq' hkj hj, tdist_comm, hp.dist_eq' hik (hkj.trans hj),
    tdist_comm, hp.dist_eq' (hik.trans hkj) hj]
  omega

theorem isMVtx_iff (hp : IsNBPath X p N) {i : ℕ} (hi : i ≤ N) :
    IsMVtx X (p i) ↔ (IsMVtx X (p 0) ↔ Even i) := by
  have h := even_dist_iff X (p 0) (p i)
  rw [hp.dist_eq' (Nat.zero_le i) hi, Nat.sub_zero] at h
  tauto

theorem mono (hp : IsNBPath X p N) {M : ℕ} (hM : M ≤ N) : IsNBPath X p M :=
  ⟨fun i hi => hp.adj i (by omega), fun i hi => hp.nb i (by omega)⟩

end IsNBPath

structure IsGoodPath (p : ℕ → Vtx X) (N : ℕ) : Prop extends IsNBPath X p N where
  mvtx : IsMVtx X (p 0)
  crit : ∀ i, Even i → i + 8 ≤ N → IsCritical X (p (i + 8)) (p i)
  straight : ∀ i, Even i → 2 ≤ i → i + 2 ≤ N → ∃ g ∈ stab X (p i), g • p (i + 2) = p (i - 2)
  pe : ∀ i, Even i → 8 ≤ i → i < N →
    ¬ ZM X (p (i - 8)) ≤ Subgroup.normalizer (Usup X (p i) (p (i + 1)) : Set X.Universal)

theorem isGoodPath_geo (h : Hyp20 X) (hb : critDist X = 8) {α α' : Vtx X}
    (hc : IsCritical X α α') (hs : IsStraight X α α') :
    IsGoodPath X (fun i => geo X α' α i) 8 := by
  have hd : X.treeGraph.dist α α' = 8 := hc.2.1.trans hb
  have hd' : X.treeGraph.dist α' α = 8 := by rw [tdist_comm]; exact hd
  have hsym : ∀ m, m ≤ 8 → geo X α α' m = geo X α' α (8 - m) := fun m hm => by
    rw [← geo_symm X (show m ≤ X.treeGraph.dist α α' by omega), hd]
  refine ⟨⟨fun i hi => adj_geo X (by omega), fun i hi heq => ?_⟩, ?_, ?_, ?_, ?_⟩
  · have := dist_geo_geo X (u := α') (w := α) (show i ≤ i + 2 by omega) (by omega)
    rw [heq, SimpleGraph.dist_self] at this
    omega
  · simpa using IsCritical.isMVtx_right X h hc
  · intro i _ hi
    obtain rfl : i = 0 := by omega
    simpa [geo_of_le X (show X.treeGraph.dist α' α ≤ 0 + 8 by omega)] using hc
  · intro i hie hi2 hi
    obtain ⟨j, rfl⟩ := hie
    obtain ⟨g, hg, hgeq⟩ := hs (4 - j) (by omega) (by omega)
    refine ⟨g⁻¹, ?_, ?_⟩
    · rw [hsym _ (by omega), show 8 - 2 * (4 - j) = j + j by omega] at hg
      exact inv_mem hg
    · rw [hsym _ (by omega), hsym _ (by omega), show 8 - (2 * (4 - j) + 2) = j + j - 2 by omega,
        show 8 - (2 * (4 - j) - 2) = j + j + 2 by omega] at hgeq
      rw [inv_smul_eq_iff, ← hgeq]
  · intro i _ hi hi'
    omega

theorem IsGoodPath.extend {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
    (h : PUHyp M T L) (hb : critDist (puAmalgam h.le) = 8)
    (h444 : ∀ α α' : Vtx (puAmalgam h.le), IsCritical _ α α' → IsStraight _ α α' →
      Concl444 h.le α α')
    (hγ : ∀ δ δ' : Vtx (puAmalgam h.le), IsCritical _ δ δ' →
      ∃ γ, (puAmalgam h.le).treeGraph.Adj δ γ ∧
        ¬ ZM _ δ' ≤ Subgroup.normalizer (Usup _ δ γ : Set (puAmalgam h.le).Universal))
    {p : ℕ → Vtx (puAmalgam h.le)} {N : ℕ} (hp : IsGoodPath _ p N) (hN : 8 ≤ N) (hNe : Even N) :
    ∃ p' : ℕ → Vtx (puAmalgam h.le), (∀ i, i ≤ N → p' i = p i) ∧ IsGoodPath _ p' (N + 2) := by
  have hp' := hp.toIsNBPath
  have hc : IsCritical (puAmalgam h.le) (p N) (p (N - 8)) := by
    have := hp.crit (N - 8) (by rcases hNe with ⟨k, hk⟩; exact ⟨k - 4, by omega⟩) (by omega)
    rwa [show N - 8 + 8 = N by omega] at this
  have hgeo : ∀ m, m ≤ 8 → geo (puAmalgam h.le) (p N) (p (N - 8)) m = p (N - m) := fun m hm => by
    rw [hp'.eq_geo_rev (i := N - 8) (j := N) (k := N - m) (by omega) (by omega) le_rfl,
      show N - (N - m) = m by omega]
  have hgeo' : geo (puAmalgam h.le) (p (N - 8)) (p N) 2 = p (N - 6) := by
    rw [hp'.eq_geo (i := N - 8) (j := N) (k := N - 6) (by omega) (by omega) le_rfl,
      show N - 6 - (N - 8) = 2 by omega]
  have hs : IsStraight (puAmalgam h.le) (p N) (p (N - 8)) := by
    intro j hj hj'
    rw [tdist_comm, hp'.dist_eq' (by omega) le_rfl] at hj'
    have hev : Even (N - 2 * j) := by rcases hNe with ⟨k, hk⟩; exact ⟨k - j, by omega⟩
    obtain ⟨g, hg, hgeq⟩ := hp.straight (N - 2 * j) hev (by omega) (by omega)
    refine ⟨g⁻¹, ?_, ?_⟩
    · rw [hgeo _ (by omega)]
      exact inv_mem hg
    · rw [hgeo _ (by omega), hgeo _ (by omega), inv_smul_eq_iff,
        show N - (2 * j - 2) = N - 2 * j + 2 by omega, hgeq,
        show N - (2 * j + 2) = N - 2 * j - 2 by omega]
  obtain ⟨γ, hγa, hγZ⟩ := hγ _ _ hc
  obtain ⟨t, ht, htU, htZ⟩ := h444 _ _ hc hs γ hγa hγZ
  rw [hgeo 1 (by omega)] at htU
  rw [hgeo 2 (by omega), hgeo'] at htZ
  have ht' : t • p N = p N := mem_stab (puAmalgam h.le) |>.mp ht
  have hZ' : ¬ ZM (puAmalgam h.le) (t • p (N - 2)) ≤ Qv (puAmalgam h.le) (p (N - 6)) := by
    rw [zm_smul]; exact htZ
  have hMN2 : IsMVtx (puAmalgam h.le) (t • p (N - 2)) := by
    rw [isMVtx_smul, hp'.isMVtx_iff (by omega)]
    have : Even (N - 2) := by rcases hNe with ⟨k, hk⟩; exact ⟨k - 1, by omega⟩
    exact ⟨fun _ => this, fun _ => hp.mvtx⟩
  have hadj1 : (puAmalgam h.le).treeGraph.Adj (p (N - 2)) (p (N - 1)) := by
    simpa [show N - 2 + 1 = N - 1 by omega] using hp.adj (N - 2) (by omega)
  have hadj0 : (puAmalgam h.le).treeGraph.Adj (p (N - 1)) (p N) := by
    simpa [show N - 1 + 1 = N by omega] using hp.adj (N - 1) (by omega)
  have hne1 : t • p (N - 1) ≠ p (N - 1) := by
    intro heq
    apply hZ'
    apply zm_le_qv_of_dist_lt (puAmalgam h.le) hMN2
    have h1 : (puAmalgam h.le).treeGraph.Adj (t • p (N - 2)) (p (N - 1)) := by
      rw [← heq]; exact (adj_smul (puAmalgam h.le) t _ _).mpr hadj1
    have h2 := dist_triangle (puAmalgam h.le) (t • p (N - 2)) (p (N - 1)) (p (N - 6))
    rw [dist_eq_one_of_adj (puAmalgam h.le) h1, tdist_comm (puAmalgam h.le) (p (N - 1)),
      hp'.dist_eq' (show N - 6 ≤ N - 1 by omega) (by omega)] at h2
    omega
  let p' : ℕ → Vtx (puAmalgam h.le) := fun i =>
    if i = N + 1 then t • p (N - 1) else if i = N + 2 then t • p (N - 2) else p i
  have hp'le : ∀ i, i ≤ N → p' i = p i := fun i hi => by
    simp [p', show i ≠ N + 1 by omega, show i ≠ N + 2 by omega]
  have hp'1 : p' (N + 1) = t • p (N - 1) := by simp [p']
  have hp'2 : p' (N + 2) = t • p (N - 2) := by simp [p']
  have hnb : IsNBPath (puAmalgam h.le) p' (N + 2) := by
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · rcases (show i < N ∨ i = N ∨ i = N + 1 by omega) with hi' | hi' | hi'
      · rw [hp'le i (by omega), hp'le (i + 1) (by omega)]; exact hp.adj i hi'
      · subst i
        rw [hp'le _ le_rfl, hp'1, ← ht']
        exact (adj_smul (puAmalgam h.le) t _ _).mpr hadj0.symm
      · subst i
        rw [hp'1, hp'2]
        exact (adj_smul (puAmalgam h.le) t _ _).mpr hadj1.symm
    · rcases (show i + 2 ≤ N ∨ i = N - 1 ∨ i = N by omega) with hi' | hi' | hi'
      · rw [hp'le _ hi', hp'le i (by omega)]; exact hp.nb i hi'
      · subst i
        rw [show N - 1 + 2 = N + 1 by omega, hp'1, hp'le _ (by omega)]; exact hne1
      · subst i
        rw [hp'2, hp'le _ le_rfl]
        intro heq
        rw [← ht'] at heq
        have := smul_left_cancel t heq
        exact hp.nb (N - 2) (by omega) (by rw [show N - 2 + 2 = N by omega]; exact this.symm)
  refine ⟨p', hp'le, ⟨hnb, by rw [hp'le 0 (by omega)]; exact hp.mvtx, ?_, ?_, ?_⟩⟩
  · intro i hie hi
    rcases (show i + 8 ≤ N ∨ i = N - 6 by
      rcases hie with ⟨k, hk⟩; rcases hNe with ⟨m, hm⟩; omega) with hi' | hi'
    · rw [hp'le _ hi', hp'le i (by omega)]; exact hp.crit i hie hi'
    · subst i
      rw [show N - 6 + 8 = N + 2 by omega, hp'2, hp'le _ (by omega)]
      refine ⟨hMN2, ?_, hZ'⟩
      have := hnb.dist_eq' (show N - 6 ≤ N + 2 by omega) le_rfl
      rw [hp'2, hp'le _ (by omega), show N + 2 - (N - 6) = 8 by omega] at this
      rw [tdist_comm, this, hb]
  · intro i hie hi2 hi
    rcases (show i + 2 ≤ N ∨ i = N by
      rcases hie with ⟨k, hk⟩; rcases hNe with ⟨m, hm⟩; omega) with hi' | hi'
    · rw [hp'le _ hi', hp'le i (by omega), hp'le (i - 2) (by omega)]
      exact hp.straight i hie hi2 hi'
    · subst i
      refine ⟨t⁻¹, ?_, ?_⟩
      · rw [hp'le _ le_rfl]; exact inv_mem ht
      · rw [hp'2, hp'le _ (by omega), inv_smul_smul]
  · intro i hie hi8 hi
    rcases (show i < N ∨ i = N by
      rcases hie with ⟨k, hk⟩; rcases hNe with ⟨m, hm⟩; omega) with hi' | hi'
    · rw [hp'le _ (by omega), hp'le _ (by omega), hp'le _ (by omega)]
      exact hp.pe i hie hi8 hi'
    · subst i
      rw [hp'le _ (by omega), hp'le _ le_rfl, hp'1]
      have : Usup (puAmalgam h.le) (p N) (t • p (N - 1)) = Usup (puAmalgam h.le) (p N) γ := by
        conv_lhs => rw [← ht']
        rw [usup_smul, htU]
      rw [this]
      exact hγZ

theorem exists_isGoodPath {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
    (h : PUHyp M T L) (hb : critDist (puAmalgam h.le) = 8)
    (hex : ∃ α α' : Vtx (puAmalgam h.le), IsCritical _ α α' ∧ IsStraight _ α α')
    (h444 : ∀ α α' : Vtx (puAmalgam h.le), IsCritical _ α α' → IsStraight _ α α' →
      Concl444 h.le α α')
    (hγ : ∀ δ δ' : Vtx (puAmalgam h.le), IsCritical _ δ δ' →
      ∃ γ, (puAmalgam h.le).treeGraph.Adj δ γ ∧
        ¬ ZM _ δ' ≤ Subgroup.normalizer (Usup _ δ γ : Set (puAmalgam h.le).Universal)) :
    ∀ n : ℕ, ∃ p : ℕ → Vtx (puAmalgam h.le), IsGoodPath _ p (8 + 2 * n) := by
  intro n
  induction n with
  | zero =>
    obtain ⟨α, α', hc, hs⟩ := hex
    exact ⟨_, isGoodPath_geo _ h.hyp20 hb hc hs⟩
  | succ n ih =>
    obtain ⟨p, hp⟩ := ih
    obtain ⟨p', -, hp'⟩ := hp.extend h hb h444 hγ (by omega) ⟨4 + n, by omega⟩
    exact ⟨p', by rwa [show 8 + 2 * (n + 1) = 8 + 2 * n + 2 by omega]⟩

end CFSG.Quasithin.MS93.S45
