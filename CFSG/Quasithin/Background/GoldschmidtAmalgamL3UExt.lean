module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3UCent

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace CosetGeom

variable {G : Type*} [Group G] {G₀ G₁ G₂ : Subgroup G}

theorem isGeo_of_adj_of_dist {q : ℕ → CosetGeom G₀ G₁ G₂} {n : ℕ} (hG : G₀ = G₁ ⊔ G₂)
    (hadj : ∀ i, i < n → (graph G₀ G₁ G₂).Adj (q i) (q (i + 1)))
    (hd : n ≤ CosetGeom.dist (q 0) (q n)) : IsGeo q n := by
  have hle : ∀ i k, i + k ≤ n → CosetGeom.dist (q i) (q (i + k)) ≤ k := by
    intro i k
    induction k with
    | zero => intro _; simp [CosetGeom.dist_self]
    | succ k ih =>
      intro hik
      have h1 := ih (by omega)
      have h2 : CosetGeom.dist (q (i + k)) (q (i + (k + 1))) = 1 :=
        dist_eq_one_iff_adj.mpr (hadj (i + k) (by omega))
      have h3 := CosetGeom.dist_triangle hG (q i) (q (i + k)) (q (i + (k + 1)))
      omega
  intro i j hij hj
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  have h1 := hle i k hj
  have h2 := hle 0 i (by omega)
  have h3 := hle (i + k) (n - (i + k)) (by omega)
  rw [show i + k + (n - (i + k)) = n by omega] at h3
  rw [Nat.zero_add] at h2
  have h4 := CosetGeom.dist_triangle hG (q 0) (q i) (q n)
  have h5 := CosetGeom.dist_triangle hG (q i) (q (i + k)) (q n)
  omega

end CosetGeom

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

namespace GoldHyp3

variable (h : GoldHyp3 A B z V)

include h

theorem exists_crit_ext {m : ℕ} (hb : critDist (A ⊔ B) A B V = m + 1) (hm : 2 ≤ m)
    {p : ℕ → CosetGeom (A ⊔ B) A B} (hp : IsGeo p (m + 1)) (hv0 : vtype (p 0) = false)
    {v : CosetGeom (A ⊔ B) A B} (hv : (graph (A ⊔ B) A B).Adj (p 0) v)
    (hbad : ¬ Vv V v ≤ ballStab 1 (p (m - 1))) :
    ∃ q : ℕ → CosetGeom (A ⊔ B) A B, IsGeo q (m + 1) ∧ vtype (q 0) = false ∧
      ¬ Vv V (q 0) ≤ ballStab 1 (q (m + 1)) ∧ q 1 = v ∧ ∀ i, q (i + 2) = p i := by
  have hvt : vtype v = true := vtype_eq_true_of_adj hv hv0
  obtain ⟨w, hw, hwbad⟩ : ∃ w, (graph (A ⊔ B) A B).Adj v w ∧
      ¬ Vv V w ≤ ballStab 1 (p (m - 1)) := by
    by_contra hcon
    push Not at hcon
    exact hbad ((Vv_B_le_iff hvt).mpr hcon)
  have hwt : vtype w = false := vtype_eq_false_of_adj hw hvt
  obtain ⟨q, hq0, hq1, hq2⟩ : ∃ q : ℕ → CosetGeom (A ⊔ B) A B, q 0 = w ∧ q 1 = v ∧
      ∀ i, q (i + 2) = p i :=
    ⟨fun j => if j = 0 then w else if j = 1 then v else p (j - 2), by simp, by simp,
      fun i => by simp only [show i + 2 ≠ 0 by omega, show i + 2 ≠ 1 by omega, ite_false,
        Nat.add_sub_cancel]⟩
  have hqm : q (m + 1) = p (m - 1) := by
    have := hq2 (m - 1)
    rwa [show m - 1 + 2 = m + 1 by omega] at this
  have hadj : ∀ i, i < m + 1 → (graph (A ⊔ B) A B).Adj (q i) (q (i + 1)) := by
    intro i hi
    rcases Nat.lt_or_ge i 2 with hi2 | hi2
    · obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
      · rw [hq0]
        exact hq1 ▸ hw.symm
      · have e : q (1 + 1) = p 0 := hq2 0
        rw [hq1, e]
        exact hv.symm
    · obtain ⟨k, rfl⟩ : ∃ k, i = k + 2 := ⟨i - 2, by omega⟩
      rw [show k + 2 + 1 = (k + 1) + 2 by omega, hq2, hq2]
      exact hp.adj (by omega)
  have hdist : m + 1 ≤ CosetGeom.dist (q 0) (q (m + 1)) := by
    by_contra hlt
    exact hwbad (by
      rw [hq0, hqm] at hlt
      exact h.Vv_le_ballStab_one_of_dist hb hwt (by omega))
  refine ⟨q, isGeo_of_adj_of_dist rfl hadj hdist, by rw [hq0]; exact hwt, ?_, hq1, hq2⟩
  rw [hq0, hqm]
  exact hwbad

end GoldHyp3

end GoldAmL3

end F6

end CFSG.Quasithin
