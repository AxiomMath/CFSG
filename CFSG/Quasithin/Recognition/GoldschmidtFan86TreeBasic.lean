module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3TArc

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

section Dist

variable {V : Type*} {Γ : SimpleGraph V}

theorem IsTree.eq_of_dist_succ (hT : Γ.IsTree) {r v w₁ w₂ : V} (h₁ : Γ.Adj w₁ v)
    (h₂ : Γ.Adj w₂ v) (d₁ : Γ.dist r w₁ + 1 = Γ.dist r v)
    (d₂ : Γ.dist r w₂ + 1 = Γ.dist r v) : w₁ = w₂ := by
  classical
  obtain ⟨p₁, hp₁, hl₁⟩ := (hT.connected r w₁).exists_path_of_dist
  obtain ⟨p₂, hp₂, hl₂⟩ := (hT.connected r w₂).exists_path_of_dist
  have hv₁ : v ∉ p₁.support := fun hv => by
    have h1 := Walk.length_takeUntil_le_length p₁ hv
    have h2 := dist_le (p₁.takeUntil v hv)
    omega
  have hv₂ : v ∉ p₂.support := fun hv => by
    have h1 := Walk.length_takeUntil_le_length p₂ hv
    have h2 := dist_le (p₂.takeUntil v hv)
    omega
  have hq := (hT.isAcyclic.subsingleton_path r v).elim ⟨_, hp₁.concat hv₁ h₁⟩
    ⟨_, hp₂.concat hv₂ h₂⟩
  obtain ⟨hw, -⟩ := Walk.concat_inj (congrArg Subtype.val hq)
  exact hw

theorem IsTree.dist_adj_ne (hT : Γ.IsTree) {r u v : V} (h : Γ.Adj u v) :
    Γ.dist r u ≠ Γ.dist r v := by
  classical
  intro heq
  obtain ⟨p, hp, hl⟩ := (hT.connected r u).exists_path_of_dist
  obtain ⟨q, hq, hql⟩ := (hT.connected r v).exists_path_of_dist
  by_cases hv : v ∈ p.support
  · have h1 := Walk.take_spec p hv
    have h2 := dist_le (p.takeUntil v hv)
    have h3 : 0 < (p.dropUntil v hv).length := by
      rcases Nat.eq_zero_or_pos (p.dropUntil v hv).length with h0 | h0
      · exact absurd (Walk.eq_of_length_eq_zero h0) h.ne.symm
      · exact h0
    have h4 := congrArg Walk.length h1
    rw [Walk.length_append] at h4
    omega
  · have := (hT.isAcyclic.subsingleton_path r v).elim ⟨_, hp.concat hv h⟩ ⟨q, hq⟩
    have h5 := congrArg (fun w : Γ.Path r v => w.1.length) this
    simp only [Walk.length_concat] at h5
    omega

theorem IsTree.dist_adj_cases (hT : Γ.IsTree) {r u v : V} (h : Γ.Adj u v) :
    Γ.dist r v = Γ.dist r u + 1 ∨ Γ.dist r u = Γ.dist r v + 1 := by
  have h1 := hT.connected.dist_triangle (u := r) (v := u) (w := v)
  have h2 := hT.connected.dist_triangle (u := r) (v := v) (w := u)
  have h3 : Γ.dist u v = 1 := dist_eq_one_iff_adj.mpr h
  have h4 : Γ.dist v u = 1 := dist_eq_one_iff_adj.mpr h.symm
  have h5 := IsTree.dist_adj_ne hT (r := r) h
  omega

end Dist

section ArcLemmas

variable {V : Type*} {Γ : SimpleGraph V} {n : ℕ}

def Arc.drop (P : Arc Γ n) (i : ℕ) : Arc Γ (n - i) where
  vert k := P.vert (i + k)
  adj k hk := P.adj (i + k) (by omega)
  nb k hk := P.nb (i + k) (by omega)

theorem Arc.dist_eq (hT : Γ.IsTree) (P : Arc Γ n) :
    ∀ k, k ≤ n → Γ.dist (P.vert 0) (P.vert k) = k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases k with _ | _ | k
    · simp
    · exact dist_eq_one_iff_adj.mpr (P.adj 0 (by omega))
    · have i0 := ih k (by omega) (by omega)
      have i1 := ih (k + 1) (by omega) (by omega)
      have hadj1 : Γ.Adj (P.vert k) (P.vert (k + 1)) := P.adj k (by omega)
      have hadj2 : Γ.Adj (P.vert (k + 1)) (P.vert (k + 1 + 1)) := P.adj (k + 1) (by omega)
      have hne : P.vert k ≠ P.vert (k + 1 + 1) := P.nb k (by omega)
      rcases IsTree.dist_adj_cases hT (r := P.vert 0) hadj2 with h | h
      · omega
      · exfalso
        exact hne (IsTree.eq_of_dist_succ hT (r := P.vert 0) hadj1 hadj2.symm (by omega) (by omega))

theorem Arc.dist_vert (hT : Γ.IsTree) (P : Arc Γ n) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ n) :
    Γ.dist (P.vert i) (P.vert j) = j - i := by
  have := Arc.dist_eq hT (Arc.drop P i) (j - i) (by omega)
  simpa [Arc.drop, Nat.add_sub_cancel' hij] using this

theorem Arc.vert_injOn (hT : Γ.IsTree) (P : Arc Γ n) {i j : ℕ} (hi : i ≤ n) (hj : j ≤ n)
    (h : P.vert i = P.vert j) : i = j := by
  wlog hij : i ≤ j generalizing i j
  · exact (this hj hi h.symm (by omega)).symm
  have := Arc.dist_vert hT P hij hj
  rw [h, dist_self] at this
  omega

theorem Arc.vert_eq_of_ends (hT : Γ.IsTree) (P Q : Arc Γ n) (h0 : P.vert 0 = Q.vert 0)
    (hn : P.vert n = Q.vert n) : ∀ k, k ≤ n → P.vert k = Q.vert k := by
  intro k
  induction k with
  | zero => exact fun _ => h0
  | succ k ih =>
    intro hk
    have hPQ := ih (by omega)
    have dP : Γ.dist (P.vert n) (P.vert (k + 1)) + 1 = Γ.dist (P.vert n) (P.vert k) := by
      rw [dist_comm (u := P.vert n) (v := P.vert (k + 1)),
        dist_comm (u := P.vert n) (v := P.vert k), Arc.dist_vert hT P (by omega) le_rfl,
        Arc.dist_vert hT P (by omega) le_rfl]
      omega
    have dQ : Γ.dist (P.vert n) (Q.vert (k + 1)) + 1 = Γ.dist (P.vert n) (P.vert k) := by
      rw [hn, hPQ, dist_comm (u := Q.vert n) (v := Q.vert (k + 1)),
        dist_comm (u := Q.vert n) (v := Q.vert k), Arc.dist_vert hT Q (by omega) le_rfl,
        Arc.dist_vert hT Q (by omega) le_rfl]
      omega
    refine IsTree.eq_of_dist_succ hT (r := P.vert n) (P.adj k (by omega)).symm ?_ dP dQ
    rw [hPQ]
    exact (Q.adj k (by omega)).symm

end ArcLemmas

section Action

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V} {n : ℕ}

def Arc.smul (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v) (g : G)
    (P : Arc Γ n) : Arc Γ n where
  vert i := g • P.vert i
  adj i hi := (hadj g _ _).2 (P.adj i hi)
  nb i hi h := P.nb i hi (MulAction.injective g h)

theorem Arc.fixes_of_ends (hT : Γ.IsTree) (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔
    Γ.Adj u v) {g : G} (P : Arc Γ n) (h0 : g • P.vert 0 = P.vert 0) (hn : g • P.vert n = P.vert n) :
    ∀ k, k ≤ n → g • P.vert k = P.vert k :=
  Arc.vert_eq_of_ends hT (Arc.smul hadj g P) P h0 hn

end Action

end CFSG.Quasithin.Fan86
