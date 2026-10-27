module

public import CFSG.Monster.AxisCount.DenseModFive
public import CFSG.YGroups.Y443.Native.Witness
import CFSG.Monster.Griess.ModFiveSeparation

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.YGroups.Y443

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.Monster.Griess.ModFive
  CFSG.Monster.Generated CFSG.Monster.Spin CFSG.YGroups.Y443Native

theorem interp_bV_eq_inX :
    interp (bV ()) = inX (fun _ => (1 : ℚ)) := by
  rw [interp_bV, sum_basisB_X]

theorem N₀_apply_zero : N₀ (spinOfRow 0) 0 = 1 := by
  change ((wV ()).D.getD (98580 + 24 * rowOf (spinOfRow 0) + ((0 : Fin 24) : ℕ)) 0 : ℚ) /
    2 ^ (wV ()).e = 1
  rw [rowOf_spinOfRow (by norm_num), wV_getD _ (by norm_num)]
  simp [wV_e]

theorem one_not_mem_D5 : (1 : ℚ) ∉ D5 := fun h => by
  have h1 := (intCast_mem_D5_iff 1).1 (by simpa using h)
  omega

theorem wordLin_eq_of_cong5D {w₁ w₂ : List Native.Gen}
    (h₁ : ∀ g ∈ w₁, g.validB = true) (h₂ : ∀ g ∈ w₂, g.validB = true)
    (hsep : ∀ c d : ShortIdx, (∀ k ∈ Finset.Icc 1 14,
      qf c ((interpA (aV ()) : Matrix (Fin 24) (Fin 24) ℚ) ^ k) -
        qf d ((interpA (aV ()) : Matrix (Fin 24) (Fin 24) ℚ) ^ k) ∈ D5) → c = d)
    (ha : Cong5D (Native.evalWord w₁ (aV ())) (Native.evalWord w₂ (aV ())))
    (hb : Cong5D (Native.evalWord w₁ (bV ())) (Native.evalWord w₂ (bV ())))
    (hw : Cong5D (Native.evalWord w₁ (wV ())) (Native.evalWord w₂ (wV ()))) :
    wordLin w₁ = wordLin w₂ := by
  set g := (wordLin w₂)⁻¹ * wordLin w₁ with hgdef
  have hg : g ∈ Gmat := mul_mem (inv_mem (wordLin_mem_Gmat w₂)) (wordLin_mem_Gmat w₁)
  have hgL : ∀ v, Int5 v → Int5 (g v) := fun v hv => wordLin_inv_int5 w₂ (wordLin_int5 w₁ hv)
  have key : ∀ x : Native.DVec, Cong5D (Native.evalWord w₁ x) (Native.evalWord w₂ x) →
      Cong5 (g (interp x)) (interp x) := by
    intro x hx
    have h := cong5_interp_of_cong5D hx
    rw [evalWord_sound w₁ h₁, evalWord_sound w₂ h₂] at h
    have h' := cong5_map (fun y hy => wordLin_inv_int5 w₂ hy) h
    have e : (wordLin w₂)⁻¹ (wordLin w₂ (interp x)) = interp x :=
      (wordLin w₂).symm_apply_apply _
    rw [e] at h'
    exact h'
  have h1 : g = 1 := eq_one_of_cong5_three_vectors (a₀ := interpA (aV ()))
    (β := fun _ => (1 : ℚ)) (N₀ := N₀) (K := 14) hsep (fun _ => one_not_mem_D5)
    ⟨spinOfRow 0, 0, by rw [N₀_apply_zero]; exact one_not_mem_D5⟩ hg hgL
    (by rw [← interp_aV]; exact key _ ha) (by rw [← interp_bV_eq_inX]; exact key _ hb)
    (by rw [← interp_wV]; exact key _ hw)
  exact (inv_mul_eq_one.1 h1).symm

end CFSG.YGroups.Y443
