module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseModA

public section

namespace CFSG.Quasithin.F53.Stellmacher.S43.Even.E20A

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F53Mod Equiv
open scoped commutatorElement

@[expose] def commOneF : Finset orth.W := spanF (commGensF orth S5SylF Finset.univ)

theorem mem_commW_S5Syl_iff (w : orth.W) : w ∈ commW orth S5Syl ⊤ ↔ w ∈ commOneF :=
  mem_commW_iff orth mem_S5Syl_iff (Uf := Finset.univ) (fun u => by simp) w

set_option maxRecDepth 100000 in
private theorem mem_S5SylF_of_trivF : ∀ σ : Perm (Fin 5), σ 4 = 4 →
    (∀ w ∈ commOneF, ∀ b ∈ S5SylF, orth.act b (orth.act σ w * w⁻¹) = orth.act σ w * w⁻¹) →
    σ ∈ S5SylF := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem fix_of_fourF : ∀ σ : Perm (Fin 5), σ 4 = 4 → ∀ w : orth.W,
    (∀ b ∈ S5SylF, orth.act b w = w) → orth.act σ w = w := by
  decide +kernel

private theorem swap_not_memF : swap (0 : Fin 5) 1 ∉ S5SylF := by
  decide +kernel

theorem mem_S5Syl_of_triv {σ : Perm (Fin 5)} (h4 : σ 4 = 4)
    (h : ∀ w ∈ commW orth S5Syl ⊤, orth.act σ w * w⁻¹ ∈ fixW orth S5Syl) : σ ∈ S5Syl := by
  rw [mem_S5Syl_iff]
  refine mem_S5SylF_of_trivF σ h4 fun w hw b hb => ?_
  exact h w ((mem_commW_S5Syl_iff w).mpr hw) b ((mem_S5Syl_iff b).mpr hb)

theorem act_eq_of_mem_fixW {σ : Perm (Fin 5)} (h4 : σ 4 = 4) {w : orth.W}
    (hw : w ∈ fixW orth S5Syl) : orth.act σ w = w :=
  fix_of_fourF σ h4 w fun b hb => hw b ((mem_S5Syl_iff b).mpr hb)

theorem swap_not_mem_S5Syl : swap (0 : Fin 5) 1 ∉ S5Syl := by
  rw [mem_S5Syl_iff]
  exact swap_not_memF

variable {G : Type} [Group G] {X S Z : Subgroup G}

namespace D5

variable (D : Dict5 X S Z)

theorem mem_S_of_triv {x : ↥X} (h4 : D.ψ x 4 = 4)
    (h : ∀ v ∈ ⁅Z, S⁆, ⁅(x : G), v⁆ ∈ Z ⊓ Subgroup.centralizer (S : Set G)) : (x : G) ∈ S := by
  refine (D.mem_S_iff x).mpr (mem_S5Syl_of_triv h4 fun w hw => ?_)
  have hv : D.φ w ∈ ⁅Z, S⁆ := by
    rw [D.comm_eq]
    exact ⟨w, hw, rfl⟩
  have h1 := h _ hv
  rw [D.fix_eq] at h1
  obtain ⟨w', hw', hw'e⟩ := h1
  have e : ⁅(x : G), D.φ w⁆ = D.φ (orth.act (D.ψ x) w * w⁻¹) := by
    rw [map_mul, map_inv, D.act_eq, commutatorElement_def]
  rw [e] at hw'e
  rw [← D.inj hw'e]
  exact hw'

theorem comm_fix {x : ↥X} (h4 : D.ψ x 4 = 4) {z : G}
    (hz : z ∈ Z ⊓ Subgroup.centralizer (S : Set G)) : (x : G) * z = z * x := by
  rw [D.fix_eq] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  have h1 : (x : G) * D.φ w * (x : G)⁻¹ = D.φ w := by
    rw [← D.act_eq, act_eq_of_mem_fixW h4 hw]
  calc (x : G) * D.φ w = ((x : G) * D.φ w * (x : G)⁻¹) * x := by group
    _ = D.φ w * x := by rw [h1]

theorem exists_not_mem_S : ∃ x : ↥X, D.ψ x 4 = 4 ∧ (x : G) ∉ S := by
  obtain ⟨x, hx⟩ := D.surj (swap 0 1)
  refine ⟨x, ?_, fun h => swap_not_mem_S5Syl ?_⟩
  · rw [hx]
    decide
  · rw [← hx]
    exact (D.mem_S_iff x).mp h

end D5

end CFSG.Quasithin.F53.Stellmacher.S43.Even.E20A
