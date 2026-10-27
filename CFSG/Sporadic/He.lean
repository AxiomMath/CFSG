module

public import CFSG.Sporadic.He.Simple

public section

namespace CFSG.Sporadic.He

open CFSG.Blueprint

theorem fam_he_simplicity :
    Finite NativeSporadic.He ∧ Nontrivial NativeSporadic.He ∧
    IsSimpleGroup NativeSporadic.He := by
  have h : IsSimpleGroup NativeSporadic.He := isSimpleGroup_He
  exact ⟨inferInstance, h.toNontrivial, h⟩

theorem fam_he_order : Nat.card NativeSporadic.He = 4030387200 ∧
    ∃ x y : NativeSporadic.He, x.val.val = NativeSporadic.decode 7 50 1 NativeSporadic.HeSeed1 ∧
      y.val.val = NativeSporadic.decode 7 50 1 NativeSporadic.HeSeed2 ∧
      orderOf x = 2 ∧ orderOf y = 7 ∧ orderOf (x * y) = 17 := by
  refine ⟨card_He, heEquivJ.symm a, heEquivJ.symm b, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← mat_heEquivJ, MulEquiv.apply_symm_apply]; rfl
  · rw [← mat_heEquivJ, MulEquiv.apply_symm_apply]; rfl
  · rw [MulEquiv.orderOf_eq, orderOf_a]
  · rw [MulEquiv.orderOf_eq, orderOf_b]
  · rw [← map_mul, MulEquiv.orderOf_eq, orderOf_ab]

theorem det_mat_eq_one (g : J) : (mat g).det = 1 := by
  have := isSimpleGroup_J
  let φ : J →* (ZMod 7)ˣ := Matrix.GeneralLinearGroup.det.comp J.subtype
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with hK | hK
  · exfalso
    have h := Nat.card_le_card_of_injective φ ((MonoidHom.ker_eq_bot_iff φ).1 hK)
    rw [card_J, Nat.card_eq_fintype_card, ZMod.card_units] at h
    norm_num at h
  · have hg : g ∈ φ.ker := by rw [hK]; trivial
    have h1 : Matrix.GeneralLinearGroup.det (g : GL (Fin 50) (ZMod 7)) = 1 :=
      MonoidHom.mem_ker.1 hg
    have h2 := congrArg Units.val h1
    rwa [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] at h2

theorem fam_he_generator_determinants :
    (NativeSporadic.decode 7 50 1 NativeSporadic.HeSeed1).det = 1 ∧
      (NativeSporadic.decode 7 50 1 NativeSporadic.HeSeed2).det = 1 :=
  ⟨det_mat_eq_one a, det_mat_eq_one b⟩

end CFSG.Sporadic.He
