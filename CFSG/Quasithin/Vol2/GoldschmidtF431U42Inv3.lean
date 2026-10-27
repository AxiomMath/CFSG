module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Inv

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Quasithin CFSG.Open U42F431
open scoped Pointwise

theorem centralizer_x :
    Subgroup.centralizer ({xY} : Set Y) = P1 := by
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff, mem_P1_iff]
  constructor
  · intro h
    exact (mem_centralizer_x_iff g.2).1 (congrArg Subtype.val h)
  · intro h
    exact Subtype.ext ((mem_centralizer_x_iff g.2).2 h)

theorem fix_t_iff (p : Fin 45) : t45 p = p ↔ p.val ∈ L0 := by
  have h := chkT_spec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hp : p.val ∈ fixPts t0L ↔ p.val ∈ L0 := by rw [h.2]
  rw [← hp, fixPts, List.mem_filter, List.mem_range, beq_iff_eq]
  have := repL_t45.2 p
  constructor
  · intro ht
    exact ⟨p.2, by rw [this, ht]⟩
  · rintro ⟨-, hh⟩
    apply Fin.ext
    rw [← this]
    exact hh

theorem centralizer_t_le :
    Subgroup.centralizer ({tY} : Set Y) ≤ P2 := by
  intro g hg
  rw [Subgroup.mem_centralizer_singleton_iff] at hg
  have hc : (g : P45) * t45 = t45 * (g : P45) := congrArg Subtype.val hg
  have hmap : ∀ h : P45, h * t45 = t45 * h → ∀ p : Fin 45, p.val ∈ L0 → (h p).val ∈ L0 := by
    intro h hh p hp
    rw [← fix_t_iff] at hp ⊢
    have := congrArg (fun f : P45 => f p) hh
    simp only [Equiv.Perm.mul_apply] at this
    rw [← this, hp]
  rw [mem_P2_iff]
  have hg' : ((g : Y) : P45)⁻¹ * t45 = t45 * ((g : Y) : P45)⁻¹ := by
    calc ((g : Y) : P45)⁻¹ * t45
        = ((g : Y) : P45)⁻¹ * (t45 * (g : P45)) * ((g : Y) : P45)⁻¹ := by group
      _ = ((g : Y) : P45)⁻¹ * ((g : P45) * t45) * ((g : Y) : P45)⁻¹ := by rw [hc]
      _ = t45 * ((g : Y) : P45)⁻¹ := by group
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact hmap _ hc p hp
  · intro hq
    refine ⟨((g : Y) : P45)⁻¹ q, hmap _ hg' q hq, ?_⟩
    exact Equiv.apply_symm_apply ((g : Y) : P45) q

theorem center_T_eq {w : Y} (hwT : w ∈ T)
    (hc : ∀ s ∈ T, s * w = w * s) (hw1 : w ≠ 1) : w = xY :=
  (center_T_spec hwT hc).resolve_left hw1

end CFSG.Quasithin.H13.F431.U42
