module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab8Slide
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab8Ball

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmLab6
  CFSG.Quasithin.F6.GoldAmLab7

namespace F6

namespace GoldAmLab8

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {V V₂ : Subgroup D} {z c : D}

theorem reach_of_pushUp (h : TwoSys A B z V c V₂) (h3 : GoldAmL3.GoldHyp3 A B z V) {b : ℕ}
    (hb : critDist (A ⊔ B) A B V = b) (hb5 : 5 ≤ b)
    (hPU : ∀ x y : CosetGeom (A ⊔ B) A B, vtype x = true → (graph (A ⊔ B) A B).Adj x y →
      ¬ stab x ≤ Subgroup.normalizer ((ballStab 1 x ⊓ ballStab 1 y : Subgroup D) : Set D)) :
    ∀ x y : CosetGeom (A ⊔ B) A B, CosetGeom.dist x y < b → Nm A B V V₂ x ≤ ballStab 1 y := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨x₀, y₀, hlt, hn₀⟩ := hcon
  have hS : ∃ n, ∃ x y : CosetGeom (A ⊔ B) A B, CosetGeom.dist x y = n ∧
      ¬ Nm A B V V₂ x ≤ ballStab 1 y := ⟨_, x₀, y₀, rfl, hn₀⟩
  obtain ⟨α, α', hαd, hαn⟩ := Nat.find_spec hS
  have hmin : ∀ x' y' : CosetGeom (A ⊔ B) A B, CosetGeom.dist x' y' < Nat.find hS →
      Nm A B V V₂ x' ≤ ballStab 1 y' := by
    intro x' y' hlt'
    by_contra hcon'
    exact Nat.find_min hS (m := CosetGeom.dist x' y') hlt' ⟨x', y', rfl, hcon'⟩
  have hle : Nat.find hS ≤ CosetGeom.dist x₀ y₀ := Nat.find_min' hS ⟨x₀, y₀, rfl, hn₀⟩
  have hge : b ≤ Nat.find hS + 1 := by
    by_contra hlt'
    exact hαn (Nm_le_ballStab_of_dist h h3 hb α (Nat.find hS) α' hαd (by omega))
  obtain ⟨m, hm⟩ : ∃ m, Nat.find hS = m + 1 := ⟨Nat.find hS - 1, by omega⟩
  rw [hm] at hαd hmin hge hle
  have hVα := goodV_all h α
  have hVα' := goodV_all h α'
  obtain ⟨r, hr0, hrn, hr⟩ := exists_geodesic (rfl : A ⊔ B = A ⊔ B) (m + 1) α α' hαd
  have hdist : ∀ i j, i ≤ j → j ≤ m + 1 → CosetGeom.dist (r i) (r j) = j - i := hr
  have hadj : ∀ i, i < m + 1 → (graph (A ⊔ B) A B).Adj (r i) (r (i + 1)) := fun i hi => hr.adj hi
  have hαε : Nm A B V V₂ α ≤ ballStab 1 (r m) := hmin _ _ (by
    rw [← hr0]
    have := hdist 0 m (by omega) (by omega)
    omega)
  have hα'p : Nm A B V V₂ α' ≤ ballStab 1 (r 1) := hmin _ _ (by
    rw [← hrn, CosetGeom.dist_comm]
    have := hdist 1 (m + 1) (by omega) le_rfl
    omega)
  have hle1 : Nm A B V V₂ α ≤ stab α' := fun n hn =>
    ballStab_le_stab_of_dist_le (n := 1) (γ := r m) (δ := α')
      (by rw [← hrn]; exact (dist_eq_one_iff_adj.mpr (hadj m (by omega))).le) (hαε hn)
  have hnot' : ¬ Nm A B V V₂ α' ≤ ballStab 1 α := not_nm_le_symm hVα hVα' hle1 hαn
  have hα0 : vtype α = true := by
    by_contra hv
    exact hαn (Nm_le_ballStab_A (V₂ := V₂) h3 hb (Bool.eq_false_iff.mpr hv) (by omega))
  have hα'0 : vtype α' = true := by
    by_contra hv
    exact hnot' (by
      rw [CosetGeom.dist_comm] at hαd
      exact Nm_le_ballStab_A (V₂ := V₂) h3 hb (Bool.eq_false_iff.mpr hv) (by omega))
  have hp : (graph (A ⊔ B) A B).Adj (r m) α' := by rw [← hrn]; exact hadj m (by omega)
  obtain ⟨μ, hμ, -, hμn⟩ := exists_nbr_not_le_of_not_normal h h3 (α := α) (α' := α') (ε := r m)
    (p₁ := r 1) (by rw [← hr0]; exact hadj 0 (by omega)) hp.symm hαε hα'p hαn
    (hPU α' (r m) hα'0 hp.symm)
  have hμ0 : vtype μ = false := vtype_eq_false_of_adj hμ hα'0
  refine hμn (Nm_le_ballStab_A (V₂ := V₂) h3 hb hμ0 ?_)
  have h1 := CosetGeom.dist_triangle (G₁ := A) (G₂ := B) rfl μ α' (r 1)
  have h2 : CosetGeom.dist μ α' = 1 := by
    rw [CosetGeom.dist_comm]; exact dist_eq_one_iff_adj.mpr hμ
  have h3' : CosetGeom.dist α' (r 1) = m := by
    rw [← hrn, CosetGeom.dist_comm]
    have := hdist 1 (m + 1) (by omega) le_rfl
    omega
  omega

end GoldAmLab8

end F6

end CFSG.Quasithin
