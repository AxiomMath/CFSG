module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86TreeBasic

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V : Type*} {Γ : SimpleGraph V}

@[expose] def Arc.take {n : ℕ} (P : Arc Γ n) (k : ℕ) (hk : k ≤ n) : Arc Γ k where
  vert := P.vert
  adj i hi := P.adj i (by omega)
  nb i hi := P.nb i (by omega)

@[expose] def Arc.step (a b : V) (h : Γ.Adj a b) : Arc Γ 1 where
  vert i := if i = 0 then a else b
  adj i hi := by
    have h0 : i = 0 := by omega
    subst h0
    simpa using h
  nb i hi := by omega

@[expose] def Arc.append {m n : ℕ} (P : Arc Γ m) (Q : Arc Γ n) (h : P.vert m = Q.vert 0)
    (hnb : 1 ≤ m → 1 ≤ n → P.vert (m - 1) ≠ Q.vert 1) : Arc Γ (m + n) where
  vert i := if i ≤ m then P.vert i else Q.vert (i - m)
  adj i hi := by
    show Γ.Adj (if i ≤ m then P.vert i else Q.vert (i - m))
      (if i + 1 ≤ m then P.vert (i + 1) else Q.vert (i + 1 - m))
    split_ifs with h1 h2 h2
    · exact P.adj i (by omega)
    · have h3 : i = m := by omega
      subst h3
      rw [h, show i + 1 - i = 0 + 1 by omega]
      exact Q.adj 0 (by omega)
    · omega
    · rw [show i + 1 - m = (i - m) + 1 by omega]
      exact Q.adj (i - m) (by omega)
  nb i hi := by
    show (if i ≤ m then P.vert i else Q.vert (i - m)) ≠
      (if i + 2 ≤ m then P.vert (i + 2) else Q.vert (i + 2 - m))
    split_ifs with h1 h2 h2
    · exact P.nb i h2
    · by_cases h3 : i = m
      · subst h3
        rw [h, show i + 2 - i = 0 + 2 by omega]
        exact Q.nb 0 (by omega)
      · have h4 : i = m - 1 := by omega
        rw [show i + 2 - m = 1 by omega, h4]
        exact hnb (by omega) (by omega)
    · omega
    · rw [show i + 2 - m = (i - m) + 2 by omega]
      exact Q.nb (i - m) (by omega)

theorem Arc.append_vert_le {m n : ℕ} (P : Arc Γ m) (Q : Arc Γ n) (h : P.vert m = Q.vert 0)
    (hnb : 1 ≤ m → 1 ≤ n → P.vert (m - 1) ≠ Q.vert 1) {i : ℕ} (hi : i ≤ m) :
    (Arc.append P Q h hnb).vert i = P.vert i := by
  simp [Arc.append, hi]

theorem Arc.append_vert_ge {m n : ℕ} (P : Arc Γ m) (Q : Arc Γ n) (h : P.vert m = Q.vert 0)
    (hnb : 1 ≤ m → 1 ≤ n → P.vert (m - 1) ≠ Q.vert 1) {i : ℕ} (hi : m ≤ i) :
    (Arc.append P Q h hnb).vert i = Q.vert (i - m) := by
  rcases Nat.eq_or_lt_of_le hi with rfl | hlt
  · simp [Arc.append, h]
  · simp [Arc.append, show ¬ i ≤ m by omega]

theorem IsTree.exists_adj_dist_succ (hT : Γ.IsTree) {u v : V} {n : ℕ}
    (h : Γ.dist u v = n + 1) : ∃ w, Γ.Adj w v ∧ Γ.dist u w = n := by
  obtain ⟨p, hp⟩ := hT.connected.exists_walk_length_eq_dist u v
  have hne : v ≠ u := fun h' => by
    rw [h', dist_self] at h
    omega
  obtain ⟨w, hw, q, hq⟩ := (p.reverse).exists_eq_cons_of_ne hne
  have hlen : q.length = n := by
    have := congrArg Walk.length hq
    rw [Walk.length_reverse, Walk.length_cons, hp, h] at this
    omega
  refine ⟨w, hw.symm, ?_⟩
  have h1 : Γ.dist u w ≤ n := by
    have := dist_le q.reverse
    rw [Walk.length_reverse] at this
    omega
  have h2 := hT.connected.dist_triangle (u := u) (v := w) (w := v)
  have h3 : Γ.dist w v = 1 := dist_eq_one_iff_adj.mpr hw.symm
  omega

theorem IsTree.exists_arc (hT : Γ.IsTree) :
    ∀ (n : ℕ) (u v : V), Γ.dist u v = n → ∃ P : Arc Γ n, P.vert 0 = u ∧ P.vert n = v
  | 0, u, v, h => by
    have : u = v := by
      by_contra hne
      exact absurd h (hT.connected.pos_dist_of_ne hne).ne'
    subst this
    exact ⟨⟨fun _ => u, fun i hi => by omega, fun i hi => by omega⟩, rfl, rfl⟩
  | n + 1, u, v, h => by
    obtain ⟨w, hwv, hw⟩ := IsTree.exists_adj_dist_succ hT h
    obtain ⟨P, hP0, hPn⟩ := IsTree.exists_arc hT n u w hw
    have hne : 1 ≤ n → v ≠ P.vert (n - 1) := fun hn h' => by
      have := Arc.dist_eq hT P (n - 1) (by omega)
      rw [hP0, ← h'] at this
      omega
    have hj : (Arc.step w v hwv).vert 0 = w := by simp [Arc.step]
    have hs1 : (Arc.step w v hwv).vert 1 = v := by simp [Arc.step]
    have hP : P.vert n = (Arc.step w v hwv).vert 0 := by rw [hj, hPn]
    have hnb : 1 ≤ n → 1 ≤ 1 → P.vert (n - 1) ≠ (Arc.step w v hwv).vert 1 := fun hn _ => by
      rw [hs1]
      exact (hne hn).symm
    refine ⟨Arc.append P (Arc.step w v hwv) hP hnb, ?_, ?_⟩
    · rw [Arc.append_vert_le _ _ _ _ (Nat.zero_le n), hP0]
    · rw [Arc.append_vert_ge _ _ _ _ (Nat.le_succ n), show n.succ - n = 1 by omega, hs1]

theorem IsTree.exists_arc_between (hT : Γ.IsTree) (u v : V) :
    ∃ P : Arc Γ (Γ.dist u v), P.vert 0 = u ∧ P.vert (Γ.dist u v) = v :=
  IsTree.exists_arc hT _ u v rfl

end CFSG.Quasithin.Fan86
