module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab8Fin
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab8Slide
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab8Ball
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3RCoinc

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmLab6
  CFSG.Quasithin.F6.GoldAmLab7

namespace F6

namespace GoldAmLab8

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {V V₂ : Subgroup D} {z c : D}

theorem false_of_critical_geodesic (d : Doubled A B z V c V₂) (h3 : GoldAmL3.GoldHyp3 A B z V)
    (hPU : PushUp A B) {m : ℕ} (hm : 2 ≤ m)
    (hreach : ∀ x y : CosetGeom (A ⊔ B) A B, CosetGeom.dist x y < m + 2 →
      Nm A B V V₂ x ≤ ballStab 1 y)
    {r : ℕ → CosetGeom (A ⊔ B) A B} (hr : IsGeo r (m + 2))
    (hnot : ¬ Nm A B V V₂ (r 0) ≤ ballStab 1 (r (m + 2))) : False := by
  have h := d.sys
  have hdist : ∀ i j, i ≤ j → j ≤ m + 2 → CosetGeom.dist (r i) (r j) = j - i := hr
  have hadj : ∀ i, i < m + 2 → (graph (A ⊔ B) A B).Adj (r i) (r (i + 1)) := fun i hi => hr.adj hi
  have hαε : Nm A B V V₂ (r 0) ≤ ballStab 1 (r (m + 1)) :=
    hreach _ _ (by have := hdist 0 (m + 1) (by omega) (by omega); omega)
  have hα'p : Nm A B V V₂ (r (m + 2)) ≤ ballStab 1 (r 1) :=
    hreach _ _ (by
      have := hdist 1 (m + 2) (by omega) le_rfl
      rw [CosetGeom.dist_comm]
      omega)
  have hle : Nm A B V V₂ (r 0) ≤ stab (r (m + 2)) := fun n hn =>
    ballStab_le_stab_of_dist_le (n := 1) (γ := r (m + 1)) (δ := r (m + 2))
      (dist_eq_one_iff_adj.mpr (hadj (m + 1) (by omega))).le (hαε hn)
  have hnot' : ¬ Nm A B V V₂ (r (m + 2)) ≤ ballStab 1 (r 0) :=
    not_nm_le_symm (goodV_all h (r 0)) (goodV_all h (r (m + 2))) hle hnot
  obtain ⟨μ, hμ, -, hμn⟩ := exists_nbr_not_le_of_not_normal h h3 (hadj 0 (by omega))
    (hadj (m + 1) (by omega)).symm hαε hα'p hnot (hPU _ _ (hadj (m + 1) (by omega)).symm)
  obtain ⟨ν, hν, -, hνn⟩ := exists_nbr_not_le_of_not_normal h h3
    (hadj (m + 1) (by omega)).symm (hadj 0 (by omega)) hα'p hαε hnot' (hPU _ _ (hadj 0 (by omega)))
  exact false_of_two_slides d h3 hm hreach hr hμ hμn hν hνn

theorem false_of_doubled (d : Doubled A B z V c V₂) (h3 : GoldAmL3.GoldHyp3 A B z V)
    (hb : 5 ≤ critDist (A ⊔ B) A B V) (hPU : PushUp A B) : False := by
  classical
  have h := d.sys
  have hA : A ≤ Subgroup.normalizer (V : Set D) := h.nat.reduced.2.1
  obtain ⟨m₀, hm₀⟩ : ∃ m₀, critDist (A ⊔ B) A B V = m₀ + 1 :=
    ⟨critDist (A ⊔ B) A B V - 1, by omega⟩
  obtain ⟨p, hp0, hp, hcrit⟩ := h3.exists_crit_geodesic hm₀
  have hS : ∃ n, ∃ x y : CosetGeom (A ⊔ B) A B, CosetGeom.dist x y = n ∧
      ¬ Nm A B V V₂ x ≤ ballStab 1 y := by
    refine ⟨m₀ + 1, p 0, p (m₀ + 1), ?_, ?_⟩
    · have := hp 0 (m₀ + 1) (Nat.zero_le _) le_rfl
      omega
    · rw [hp0, Nm_γ₀ hA]
      exact hcrit
  obtain ⟨x, y, hxy, hxyn⟩ := Nat.find_spec hS
  have hmin : ∀ x' y' : CosetGeom (A ⊔ B) A B, CosetGeom.dist x' y' < Nat.find hS →
      Nm A B V V₂ x' ≤ ballStab 1 y' := by
    intro x' y' hlt
    by_contra hcon
    exact Nat.find_min hS (m := CosetGeom.dist x' y') hlt ⟨x', y', rfl, hcon⟩
  have h4 : 4 ≤ Nat.find hS := by
    by_contra hlt
    exact hxyn (Nm_le_ballStab_of_dist h h3 rfl x (Nat.find hS) y hxy (by omega))
  obtain ⟨m, hm⟩ : ∃ m, Nat.find hS = m + 2 := ⟨Nat.find hS - 2, by omega⟩
  rw [hm] at hmin hxy
  obtain ⟨r, hr0, hrn, hr⟩ := exists_geodesic (rfl : A ⊔ B = A ⊔ B) (m + 2) x y hxy
  refine false_of_critical_geodesic d h3 hPU (m := m) (by omega) hmin hr ?_
  rw [hr0, hrn]
  exact hxyn

end GoldAmLab8

end F6

end CFSG.Quasithin
