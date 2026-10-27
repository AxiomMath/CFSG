module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P52B
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5PCore

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P65

variable (F : FanTree Γ G)
include F

theorem ray_bound (ℓ : Line Γ) (c : ℤ) (hv : valence Γ (ℓ.vert c) = 5) :
    (MulAction.stabilizer G (ℓ.vert (c + 4))).relIndex (nbrStab Γ G (ℓ.vert c)) ≤
      4 * (nbrStab Γ G (ℓ.vert c)).relIndex
        (MulAction.stabilizer G (ℓ.vert c) ⊓ MulAction.stabilizer G (ℓ.vert (c + 1))) := by
  set h := (nbrStab Γ G (ℓ.vert c)).relIndex
    (MulAction.stabilizer G (ℓ.vert c) ⊓ MulAction.stabilizer G (ℓ.vert (c + 1))) with hh
  let v : ℕ → V := fun j => ℓ.vert (c + j)
  have hadj : ∀ j, Γ.Adj (v j) (v (j + 1)) := fun j => by
    have := ℓ.adj (c + j)
    simpa [v, add_assoc] using this
  have hnb : ∀ j, v j ≠ v (j + 2) := fun j => by
    have := ℓ.nb (c + j)
    simpa [v, add_assoc] using this
  have hv1 : valence Γ (ℓ.vert (c + 1)) = 3 := by
    have h1 : valence Γ (ℓ.vert c) ≠ valence Γ (ℓ.vert (c + 1)) := F.alternating _ _ (ℓ.adj c)
    have h2 : valence Γ (ℓ.vert (c + 1)) = 3 ∨ valence Γ (ℓ.vert (c + 1)) = 5 := F.valence _
    omega
  have hv2 : valence Γ (ℓ.vert (c + 2)) = 5 := by rw [ℓ.valence_add_two F c]; exact hv
  have hv3 : valence Γ (ℓ.vert (c + 3)) = 3 := by
    have := ℓ.valence_add_two F (c + 1)
    rw [show c + 1 + 2 = c + 3 by omega] at this
    rw [this]
    exact hv1
  let f : ℕ → ℕ := fun j => if valence Γ (v j) = 3 then 2 else h
  have hf : ∀ j, 1 ≤ j → j < 4 → (nbrStab Γ G (v j)).relIndex
      (MulAction.stabilizer G (v j) ⊓ MulAction.stabilizer G (v (j - 1))) ≤ f j := by
    intro j hj1 hj4
    have hadj1 : Γ.Adj (v j) (v (j - 1)) := by
      have := (hadj (j - 1)).symm
      rwa [show j - 1 + 1 = j by omega] at this
    by_cases h3 : valence Γ (v j) = 3
    · simp only [f, h3, ↓reduceIte]
      exact (F.relIndex_nbrStab_eq_two hadj1 h3).le
    · simp only [f, h3, ↓reduceIte]
      have hp1 : valence Γ (v j) = 3 ∨ valence Γ (v j) = 5 := F.valence _
      have := F.relIndex_edge_eq (ℓ.adj c) hadj1 (by omega : valence Γ (v j) = valence Γ (ℓ.vert c))
      rw [this]
  have key := F.relIndex_chain hadj hnb f hf 4 (by norm_num) le_rfl
  have hprod : ∏ j ∈ Finset.Ico 1 4, f j = 2 * h * 2 := by
    have hv1' : valence Γ (v 1) = 3 := by simpa [v] using hv1
    have hv2' : valence Γ (v 2) = 5 := by simpa [v] using hv2
    have hv3' : valence Γ (v 3) = 3 := by simpa [v] using hv3
    have f1 : f 1 = 2 := by simp [f, hv1']
    have f2 : f 2 = h := by simp [f, hv2']
    have f3 : f 3 = 2 := by simp [f, hv3']
    rw [show Finset.Ico 1 4 = {1, 2, 3} by decide]
    simp [Finset.prod_insert, f1, f2, f3]
    ring
  rw [hprod] at key
  have e0 : v 0 = ℓ.vert c := by simp [v]
  have e4 : v 4 = ℓ.vert (c + 4) := by simp [v]
  rw [e0, e4, inf_comm, Subgroup.inf_relIndex_right] at key
  calc _ ≤ 2 * h * 2 := key
    _ = 4 * h := by ring

end P65

end CFSG.Quasithin.Fan86
