module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Loc

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace FanTree

variable (F : FanTree Γ G)
include F

theorem fix_vertex_of_fix_two {v a c : V} (ha : Γ.Adj v a) (hc : Γ.Adj v c) (hac : a ≠ c) {g : G}
    (hga : g • a = a) (hgc : g • c = c) : g • v = v := by
  have h1 : Γ.Adj a (g • v) := by
    have := (F.adj_smul g v a).2 ha
    rw [hga] at this
    exact this.symm
  have h2 : Γ.Adj (g • v) c := by
    have := (F.adj_smul g v c).2 hc
    rw [hgc] at this
    exact this
  exact (F.eq_of_adj_adj ha.symm hc h1 h2 hac).symm

theorem fix_two_nbrs {v a c : V} (ha : Γ.Adj v a) (hc : Γ.Adj v c) (hac : a ≠ c) {g : G}
    (hga : g • a = a) (hgc : g • c = c) : g ∈ nbrStab Γ G v :=
  mem_nbrStab.2 fun w hw => F.frobenius_two v a c ha hc hac g
    (MulAction.mem_stabilizer_iff.2 (F.fix_vertex_of_fix_two ha hc hac hga hgc)) hga hgc w hw

theorem mem_nbrStab_smul_iff (g : G) (v : V) {h : G} :
    h ∈ nbrStab Γ G (g • v) ↔ g⁻¹ * h * g ∈ nbrStab Γ G v := by
  rw [mem_nbrStab, mem_nbrStab]
  constructor
  · intro H w hw
    have hw' : Γ.Adj (g • v) (g • w) := (F.adj_smul g v w).2 hw
    have := H _ hw'
    simp [mul_smul, this]
  · intro H w hw
    have hw' : Γ.Adj v (g⁻¹ • w) := by
      have := (F.adj_smul g⁻¹ (g • v) w).2 hw
      simpa using this
    have := H _ hw'
    have h2 : g⁻¹ • h • w = g⁻¹ • w := by simpa [mul_smul] using this
    exact (MulAction.injective g⁻¹) h2

theorem conj_mem_nbrStab_of_stab {v : V} {g : G} (hg : g ∈ MulAction.stabilizer G v) {h : G}
    (hh : h ∈ nbrStab Γ G v) : g * h * g⁻¹ ∈ nbrStab Γ G v :=
  nbrStab_conj_mem F (MulAction.mem_stabilizer_iff.1 hg) hh

theorem mem_stabRange_iff_nbrStab {x : ℕ → V} {i k : ℕ} (hik : i + 2 ≤ k)
    (hadj : ∀ m, i ≤ m → m < k → Γ.Adj (x m) (x (m + 1)))
    (hnb : ∀ m, i ≤ m → m + 2 ≤ k → x m ≠ x (m + 2)) {g : G} :
    g ∈ stabRange G x i k ↔ ∀ m, i < m → m < k → g ∈ nbrStab Γ G (x m) := by
  constructor
  · intro hg m hm1 hm2
    have h1 := mem_stabRange.1 hg (m - 1) (by omega) (by omega)
    have h2 := mem_stabRange.1 hg (m + 1) (by omega) (by omega)
    have a1 : Γ.Adj (x m) (x (m - 1)) := by
      have := (hadj (m - 1) (by omega) (by omega)).symm
      rwa [show m - 1 + 1 = m by omega] at this
    exact F.fix_two_nbrs a1 (hadj m (by omega) hm2) (by
      intro h
      have := hnb (m - 1) (by omega) (by omega)
      rw [show m - 1 + 2 = m + 1 by omega] at this
      exact this h) h1 h2
  · intro hg
    rw [mem_stabRange]
    intro m hm1 hm2
    rcases Nat.lt_or_ge i m with h | h
    · rcases Nat.lt_or_ge m k with h' | h'
      · exact MulAction.mem_stabilizer_iff.1 (F.nbrStab_le_stabilizer _ (hg m h h'))
      · rw [show m = k by omega]
        exact mem_nbrStab.1 (hg (k - 1) (by omega) (by omega)) (x k) (by
          have := hadj (k - 1) (by omega) (by omega)
          rwa [show k - 1 + 1 = k by omega] at this)
    · rw [show m = i by omega]
      exact mem_nbrStab.1 (hg (i + 1) (by omega) (by omega)) (x i) (hadj i le_rfl (by omega)).symm

end FanTree

end CFSG.Quasithin.Fan86
