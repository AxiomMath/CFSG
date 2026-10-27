module

public import CFSG.RankThree.Classical.SteinbergBJUnitaryThreeInvolutions

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.OE5

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LinearGroups CFSG.RankThree.Classical

variable {K : Type} [Field K]

theorem card_gu2 (h : UnitaryFieldData 5 1 K) :
    Nat.card {A : GL (Fin 2) K // ((A : Matrix (Fin 2) (Fin 2) K).map h.bar)ᵀ * A = 1} =
      720 := by
  have hBs := gramForm_isSymm h (G := (1 : Matrix (Fin 2) (Fin 2) K)) (by
    rw [Matrix.map_one _ (map_zero h.bar) (map_one h.bar), transpose_one])
  have hBl := gramForm_separatingLeft h (G := (1 : Matrix (Fin 2) (Fin 2) K)) (by simp)
  have h1 := (unitary_full_group_order h hBs hBl (Module.finrank_fin_fun K) (by norm_num)).1
  have e : {A : GL (Fin 2) K // ((A : Matrix (Fin 2) (Fin 2) K).map h.bar)ᵀ * A = 1} ≃
      sesqUnitaryGroup (gramForm h (1 : Matrix (Fin 2) (Fin 2) K)) :=
    Matrix.GeneralLinearGroup.toLin.toEquiv.subtypeEquiv fun g => by
      rw [← Matrix.mul_one (((g : Matrix (Fin 2) (Fin 2) K).map h.bar)ᵀ),
        ← gramForm_isometry_iff h, mem_sesqUnitaryGroup]
      simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv,
        Matrix.GeneralLinearGroup.coe_toLin, Matrix.mulVecLin_apply]
  rw [Nat.card_congr e]
  have h2 : (Nat.card (sesqUnitaryGroup (gramForm h (1 : Matrix (Fin 2) (Fin 2) K))) : ℤ) =
      720 := by
    rw [h1]
    decide
  exact_mod_cast h2

theorem entries_of_commute (hc : (2 : K) ≠ 0) {g : Matrix (Fin 3) (Fin 3) K}
    (hg : g * negNegOneDiag K = negNegOneDiag K * g) :
    g 0 2 = 0 ∧ g 1 2 = 0 ∧ g 2 0 = 0 ∧ g 2 1 = 0 := by
  have e : ∀ i j, g i j * ![(-1 : K), -1, 1] j = ![(-1 : K), -1, 1] i * g i j := fun i j => by
    have := congrFun (congrFun hg i) j
    simpa [negNegOneDiag, mul_diagonal, diagonal_mul] using this
  have key : ∀ x : K, x * 1 = -1 * x → x = 0 := fun x hx => by
    have h2 : (2 : K) * x = 0 := by linear_combination hx
    exact (mul_eq_zero.mp h2).resolve_left hc
  have key' : ∀ x : K, x * -1 = 1 * x → x = 0 := fun x hx => by
    have h2 : (2 : K) * x = 0 := by linear_combination -hx
    exact (mul_eq_zero.mp h2).resolve_left hc
  exact ⟨key _ (by simpa using e 0 2), key _ (by simpa using e 1 2),
    key' _ (by simpa using e 2 0), key' _ (by simpa using e 2 1)⟩

@[expose] def block (g : Matrix (Fin 3) (Fin 3) K) : Matrix (Fin 2) (Fin 2) K :=
  Matrix.of fun i j => g i.castSucc j.castSucc

theorem block_unitary (h : UnitaryFieldData 5 1 K) {g : Matrix (Fin 3) (Fin 3) K}
    (hg : (g.map h.bar)ᵀ * g = 1) (h20 : g 2 0 = 0) (h21 : g 2 1 = 0) :
    ((block g).map h.bar)ᵀ * block g = 1 := by
  ext i j
  have e := congrFun (congrFun hg i.castSucc) j.castSucc
  simp only [mul_apply, transpose_apply, map_apply, Fin.sum_univ_three, Fin.sum_univ_two,
    block, of_apply] at e ⊢
  fin_cases i <;> fin_cases j <;> simp_all

theorem det_eq_block {g : Matrix (Fin 3) (Fin 3) K} (h02 : g 0 2 = 0) (h12 : g 1 2 = 0)
    (h20 : g 2 0 = 0) (h21 : g 2 1 = 0) : g.det = (block g).det * g 2 2 := by
  rw [det_fin_three, det_fin_two, h02, h12, h20, h21]
  simp only [block, of_apply, Fin.castSucc_zero, Fin.castSucc_one]
  ring

theorem orderOf_invT (h : UnitaryFieldData 5 1 K) : orderOf (unitaryInvT h) = 2 := by
  have h1 := orderOf_unitaryProj_unitaryInvT h (by norm_num)
  have h2 : orderOf (unitaryInvT h) ∣ 2 := orderOf_dvd_of_pow_eq_one (unitaryInvT_sq h)
  have h3 : orderOf (unitaryProj h 3 (unitaryInvT h)) ∣ orderOf (unitaryInvT h) :=
    orderOf_map_dvd _ _
  rw [h1] at h3
  exact Nat.dvd_antisymm h2 h3

abbrev mat (g : unitarySU 5 1 K 3) : Matrix (Fin 3) (Fin 3) K :=
  ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)

theorem entries_of_mem_centralizer (h : UnitaryFieldData 5 1 K)
    (g : Subgroup.centralizer {unitaryInvT h}) :
    mat (g : unitarySU 5 1 K 3) 0 2 = 0 ∧ mat (g : unitarySU 5 1 K 3) 1 2 = 0 ∧
      mat (g : unitarySU 5 1 K 3) 2 0 = 0 ∧ mat (g : unitarySU 5 1 K 3) 2 1 = 0 := by
  have : CharP K 5 := h.charP
  have hc : (2 : K) ≠ 0 := by
    intro h2
    have := (CharP.cast_eq_zero_iff K 5 2).mp (by exact_mod_cast h2)
    omega
  have hg := Subgroup.mem_centralizer_singleton_iff.mp g.2
  have hg' := congrArg (fun x : unitarySU 5 1 K 3 => mat x) hg
  simp only [mat, Subgroup.coe_mul, Units.val_mul, coe_unitaryInvT] at hg'
  exact entries_of_commute hc hg'

theorem card_centralizer_invT_le (h : UnitaryFieldData 5 1 K) :
    Nat.card (Subgroup.centralizer {unitaryInvT h}) ≤ 720 := by
  have := h.finite
  have hmem : ∀ g : Subgroup.centralizer {unitaryInvT h},
      (mat (g : unitarySU 5 1 K 3)).det = 1 ∧
        ((mat (g : unitarySU 5 1 K 3)).map h.bar)ᵀ * mat (g : unitarySU 5 1 K 3) = 1 :=
    fun g => (mem_unitarySU_iff h).mp (g : unitarySU 5 1 K 3).2
  have hU : ∀ g : Subgroup.centralizer {unitaryInvT h},
      ((block (mat (g : unitarySU 5 1 K 3))).map h.bar)ᵀ * block (mat (g : unitarySU 5 1 K 3)) =
        1 := fun g =>
    block_unitary h (hmem g).2 (entries_of_mem_centralizer h g).2.2.1
      (entries_of_mem_centralizer h g).2.2.2
  let φ : Subgroup.centralizer {unitaryInvT h} →
      {A : GL (Fin 2) K // ((A : Matrix (Fin 2) (Fin 2) K).map h.bar)ᵀ * A = 1} := fun g =>
    ⟨⟨block (mat (g : unitarySU 5 1 K 3)),
      ((block (mat (g : unitarySU 5 1 K 3))).map h.bar)ᵀ, mul_eq_one_comm.mp (hU g), hU g⟩,
      hU g⟩
  have hinj : Function.Injective φ := by
    intro g g' hgg'
    have hB : block (mat (g : unitarySU 5 1 K 3)) = block (mat (g' : unitarySU 5 1 K 3)) :=
      congrArg (fun A : {A : GL (Fin 2) K // ((A : Matrix (Fin 2) (Fin 2) K).map h.bar)ᵀ * A = 1} =>
        ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) hgg'
    obtain ⟨a02, a12, a20, a21⟩ := entries_of_mem_centralizer h g
    obtain ⟨b02, b12, b20, b21⟩ := entries_of_mem_centralizer h g'
    have hd := (hmem g).1
    have hd' := (hmem g').1
    rw [det_eq_block a02 a12 a20 a21] at hd
    rw [det_eq_block b02 b12 b20 b21, ← hB] at hd'
    have hne : (block (mat (g : unitarySU 5 1 K 3))).det ≠ 0 := left_ne_zero_of_mul_eq_one hd
    have h22 := mul_left_cancel₀ hne (hd.trans hd'.symm)
    have hBij : ∀ i j : Fin 2, mat (g : unitarySU 5 1 K 3) i.castSucc j.castSucc =
        mat (g' : unitarySU 5 1 K 3) i.castSucc j.castSucc := fun i j =>
      congrFun (congrFun hB i) j
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j
    · exact hBij 0 0
    · exact hBij 0 1
    · exact a02.trans b02.symm
    · exact hBij 1 0
    · exact hBij 1 1
    · exact a12.trans b12.symm
    · exact a20.trans b20.symm
    · exact a21.trans b21.symm
    · exact h22
  calc Nat.card (Subgroup.centralizer {unitaryInvT h})
      ≤ Nat.card {A : GL (Fin 2) K // ((A : Matrix (Fin 2) (Fin 2) K).map h.bar)ᵀ * A = 1} :=
        Nat.card_le_card_of_injective φ hinj
    _ = 720 := card_gu2 h

end CFSG.Quasithin.Vol2.Ch11.SecS.OE5
