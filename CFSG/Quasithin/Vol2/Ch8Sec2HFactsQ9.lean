module

public import CFSG.Quasithin.Vol2.Ch8Sec2HFactsL3
public import CFSG.Quasithin.Background.HFL3Quad

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu

theorem two_lt_qOf_l3nine {V : Type} [CommGroup V] [Finite V] {L X : Subgroup (MulAut V)}
    (hLX : Mathieu.IsOver L X) {n : ℕ} (hn : 1 ≤ n) (hL : BinaryNineTensor L ⊤ ⊥ n) :
    (2 : WithTop ℚ) < qOf X := by
  obtain ⟨K, _, _, _, hK, e, -, hXN⟩ := exists_model_l3nine hLX hL
  have key : ∀ A, IsA2 X A → commSeries A 2 = ⊥ → 2 * rk ↥A < rkIdx (fixV A) := by
    intro A hA hA2
    have hquad : IsQuadratic A := (isQuadratic_iff_commSeries_two A).2 hA2
    have hq : ∀ a ∈ A, ∀ b ∈ A, ∀ v : V, b (a v * v⁻¹) = a v * v⁻¹ := fun a ha b hb v =>
      hquad (Subgroup.subset_closure ⟨a, ha, v, rfl⟩) b hb
    have hne : A.map (congrHom e) ≠ ⊥ := fun h =>
      hA.ne_bot ((Subgroup.map_eq_bot_iff_of_injective _ (congrHom_injective e)).mp h)
    have h := L3Nine.two_mul_rk_lt_of_quadratic hn hK ((Subgroup.map_mono hA.le).trans hXN)
      ((isElemAbelian2_map_congrHom e).2 hA.isElemAbelian2) hne (L3Nine.quad_map_congrHom e hq)
    rwa [rk_map_congrHom, rkIdx_fixV_map_congrHom] at h
  have h2 : ((2 : ℚ) : WithTop ℚ) < qOf X := by
    unfold qOf
    rw [lt_kq_iff]
    intro A hA hq
    have hr : (0 : ℚ) < (rk ↥A : ℚ) := by exact_mod_cast hA.rk_pos
    have h3 : ((2 * rk ↥A : ℕ) : ℚ) < (rkIdx (fixV A) : ℚ) := by exact_mod_cast key A hA hq
    unfold rAV
    rw [lt_div_iff₀ hr]
    push_cast at h3
    linarith
  exact_mod_cast h2

end CFSG.Quasithin.H13
