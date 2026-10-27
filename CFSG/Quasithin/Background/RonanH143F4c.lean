module

public import CFSG.Quasithin.Background.RonanH143F4b

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH143

open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H16Pf

@[expose] def mat1 : Matrix (Fin 2) (Fin 2) F4 := !![0, 1; 1, F4.α]

@[expose] def mat2 : Matrix (Fin 2) (Fin 2) F4 := !![1, 1; 0, 1]

theorem det_mat1 : mat1.det = 1 := by
  rw [Matrix.det_fin_two]
  decide +kernel

theorem det_mat2 : mat2.det = 1 := by
  rw [Matrix.det_fin_two]
  decide +kernel

theorem det_eq_one_of_mem_StatedSL {A : GL (Fin 2) F4} (hA : A ∈ CFSG.Open.StatedSL 2 F4) :
    (A : Matrix (Fin 2) (Fin 2) F4).det = 1 := by
  have hle : CFSG.Open.StatedSL 2 F4 ≤
      ((Matrix.detMonoidHom : Matrix (Fin 2) (Fin 2) F4 →* F4).comp
        (Units.coeHom (Matrix (Fin 2) (Fin 2) F4))).ker := by
    unfold CFSG.Open.StatedSL
    rw [Subgroup.closure_le]
    intro B hB
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    exact hB
  exact MonoidHom.mem_ker.1 (hle hA)

theorem mulVec_mat1 : ∀ t : Fin 16, mat1.mulVec (vecOf t) = vecOf (tab F1 t) := by
  decide +kernel

theorem mulVec_mat2 : ∀ t : Fin 16, mat2.mulVec (vecOf t) = vecOf (tab FA2 t) := by
  decide +kernel

theorem exists_gl_mat :
    ∃ g₁ g₂ : GL (Fin 2) F4, g₁ ∈ CFSG.Open.StatedSL 2 F4 ∧ g₂ ∈ CFSG.Open.StatedSL 2 F4 ∧
      (∀ t : Fin 16, natHom 2 F4 g₁ (Multiplicative.ofAdd (vecOf t)) =
        Multiplicative.ofAdd (vecOf (tab F1 t))) ∧
      (∀ t : Fin 16, natHom 2 F4 g₂ (Multiplicative.ofAdd (vecOf t)) =
        Multiplicative.ofAdd (vecOf (tab FA2 t))) := by
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero mat1 (by rw [det_mat1]; exact one_ne_zero),
    Matrix.GeneralLinearGroup.mkOfDetNeZero mat2 (by rw [det_mat2]; exact one_ne_zero),
    ?_, ?_, ?_, ?_⟩
  · unfold CFSG.Open.StatedSL
    apply Subgroup.subset_closure
    show mat1.det = 1
    exact det_mat1
  · unfold CFSG.Open.StatedSL
    apply Subgroup.subset_closure
    show mat2.det = 1
    exact det_mat2
  · intro t
    change Multiplicative.ofAdd (mat1.mulVec (vecOf t)) = Multiplicative.ofAdd (vecOf (tab F1 t))
    rw [mulVec_mat1 t]
  · intro t
    change Multiplicative.ofAdd (mat2.mulVec (vecOf t)) = Multiplicative.ofAdd (vecOf (tab FA2 t))
    rw [mulVec_mat2 t]

theorem card_natSub_SL_le : Nat.card ↥(natSub 2 F4 (CFSG.Open.StatedSL 2 F4)) ≤ 60 := by
  have h1 : Nat.card ↥(natSub 2 F4 (CFSG.Open.StatedSL 2 F4)) ≤
      Nat.card ↥(CFSG.Open.StatedSL 2 F4) := by
    refine Nat.card_le_card_of_surjective
      (fun A : ↥(CFSG.Open.StatedSL 2 F4) =>
        (⟨natHom 2 F4 A.1, Subgroup.mem_map_of_mem (natHom 2 F4) A.2⟩ :
          ↥(natSub 2 F4 (CFSG.Open.StatedSL 2 F4)))) ?_
    rintro ⟨y, hy⟩
    have hy' : y ∈ (CFSG.Open.StatedSL 2 F4).map (natHom 2 F4) := hy
    obtain ⟨A, hA, rfl⟩ := Subgroup.mem_map.1 hy'
    exact ⟨⟨A, hA⟩, rfl⟩
  have h2 : Nat.card ↥(CFSG.Open.StatedSL 2 F4) ≤
      Nat.card {M : Matrix (Fin 2) (Fin 2) F4 // M.det = 1} := by
    refine Nat.card_le_card_of_injective
      (fun A : ↥(CFSG.Open.StatedSL 2 F4) =>
        (⟨(A.1 : Matrix (Fin 2) (Fin 2) F4), det_eq_one_of_mem_StatedSL A.2⟩ :
          {M : Matrix (Fin 2) (Fin 2) F4 // M.det = 1})) ?_
    intro A B h
    exact Subtype.ext (Units.ext (congrArg Subtype.val h))
  have h3 : Nat.card {M : Matrix (Fin 2) (Fin 2) F4 // M.det = 1} = 60 := by
    have e : {M : Matrix (Fin 2) (Fin 2) F4 // M.det = 1} ≃
        {M : Matrix (Fin 2) (Fin 2) F4 // M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1} :=
      Equiv.subtypeEquivRight (fun M => by rw [Matrix.det_fin_two])
    rw [Nat.card_congr e, Nat.card_eq_fintype_card]
    decide +kernel
  exact h1.trans (h2.trans h3.le)

end CFSG.Quasithin.RonanH143
