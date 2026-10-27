module

public import CFSG.Quasithin.MS93.S45Path
import CFSG.Quasithin.MS93.S4ABasic

public section

namespace CFSG.Quasithin.MS93.S45

open CFSG.Quasithin CFSG.Quasithin.Fan86.Univ SimpleGraph

theorem IsGoodPath.extend_of {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
    (h : PUHyp M T L) (hb : critDist (puAmalgam h.le) = 8)
    (h444 : ∀ α α' : Vtx (puAmalgam h.le), IsCritical _ α α' → IsStraight _ α α' →
      Concl444 h.le α α')
    {p : ℕ → Vtx (puAmalgam h.le)} {N : ℕ} (hp : IsGoodPath _ p N) (hN : 8 ≤ N) (hNe : Even N)
    {γ : Vtx (puAmalgam h.le)} (hγa : (puAmalgam h.le).treeGraph.Adj (p N) γ)
    (hγZ : ¬ ZM _ (p (N - 8)) ≤
      Subgroup.normalizer (Usup _ (p N) γ : Set (puAmalgam h.le).Universal)) :
    ∃ p' : ℕ → Vtx (puAmalgam h.le), (∀ i, i ≤ N → p' i = p i) ∧ IsGoodPath _ p' (N + 2) ∧
      Usup (puAmalgam h.le) (p N) (p' (N + 1)) = Usup _ (p N) γ := by
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
  have hU1 : Usup (puAmalgam h.le) (p N) (p' (N + 1)) = Usup (puAmalgam h.le) (p N) γ := by
    rw [hp'1]
    conv_lhs => rw [← ht']
    rw [usup_smul, htU]
  refine ⟨p', hp'le, ⟨hnb, by rw [hp'le 0 (by omega)]; exact hp.mvtx, ?_, ?_, ?_⟩, hU1⟩
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


end CFSG.Quasithin.MS93.S45
