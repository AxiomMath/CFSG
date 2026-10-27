module

public import CFSG.ClassicalInvolution.Phan.Center
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosBlockAux3

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.ClassicalInvolution.Phan CFSG.LieType.BorelTits

variable {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {m : ℕ}

@[expose] def qTwoLMDivKind_diag (F0 : Type) [Field F0] [Finite F0] [CharP F0 2] (m : ℕ) :
    Subgroup (Su F0 2 1 m) where
  carrier := {u | ggIsDiagMat (u : GL (Fin m) F0)}
  mul_mem' := by
    rintro u v ⟨d, hd⟩ ⟨e, he⟩
    refine ⟨fun i => d i * e i, ?_⟩
    rw [Subgroup.coe_mul, Units.val_mul, hd, he, Matrix.diagonal_mul_diagonal]
  one_mem' := ⟨fun _ => 1, by
    rw [Subgroup.coe_one, Units.val_one, Matrix.diagonal_one]⟩
  inv_mem' := by
    rintro u ⟨d, hd⟩
    refine ⟨Ring.inverse d, ?_⟩
    rw [Subgroup.coe_inv, Matrix.coe_units_inv, hd, Matrix.inv_diagonal]

omit [Field F0] [Finite F0] [CharP F0 2] in
private theorem qTwoLMDivKindDiag_card_eq_sq (hF : Nat.card F0 = 4) :
    Nat.card F0 = (2 ^ 1) ^ 2 := by
  rw [hF]; norm_num

omit [CharP F0 2] in
private theorem qTwoLMDivKindDiag_card_units (hF : Nat.card F0 = 4) : Nat.card F0ˣ = 3 := by
  rw [CFSG.ClassicalGroups.Unitary.card_units_of_card (qTwoLMDivKindDiag_card_eq_sq hF)]
  norm_num

omit [CharP F0 2] in
private theorem qTwoLMDivKindDiag_pow_three_of_ne_zero (hF : Nat.card F0 = 4) {c : F0}
    (hc : c ≠ 0) : c ^ 3 = 1 := by
  have h := @FiniteField.pow_card_sub_one_eq_one F0 _ (Fintype.ofFinite F0) c hc
  rw [← @Nat.card_eq_fintype_card F0 (Fintype.ofFinite F0), hF] at h
  simpa using h

private theorem qTwoLMDivKindDiag_unitary_mul_self (c : F0) :
    unitaryInvolution F0 2 1 c * c = c ^ 3 := by
  rw [unitaryInvolution_apply, show (2 : ℕ) ^ 1 = 2 by norm_num,
    show c ^ 2 * c = c ^ 3 by ring]

theorem qTwoLMDivKind_norm_eq_one (hF : Nat.card F0 = 4) {c : F0} (hc : c ≠ 0) :
    unitaryInvolution F0 2 1 c * c = 1 := by
  rw [qTwoLMDivKindDiag_unitary_mul_self, qTwoLMDivKindDiag_pow_three_of_ne_zero hF hc]

private theorem qTwoLMDivKindDiag_prod_eq_one {u : Su F0 2 1 m} {d : Fin m → F0}
    (hd : ((u : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) = Matrix.diagonal d) :
    ∏ k, d k = 1 := by
  have h1 := u.2.1
  rwa [hd, Matrix.det_diagonal] at h1

omit [Finite F0] [CharP F0 2] in
private theorem qTwoLMDivKindDiag_apply_ne_zero {d : Fin m → F0} (hdet : ∏ k, d k = 1)
    (i : Fin m) : d i ≠ 0 := by
  intro h0
  have hz : ∏ k, d k = 0 := Finset.prod_eq_zero (Finset.mem_univ i) h0
  rw [hdet] at hz
  exact one_ne_zero hz

private theorem qTwoLMDivKindDiag_entry_ne_zero {u : Su F0 2 1 m}
    (hu : u ∈ qTwoLMDivKind_diag F0 m) (i : Fin m) :
    (((u : GL (Fin m) F0)) : Matrix (Fin m) (Fin m) F0) i i ≠ 0 := by
  obtain ⟨d, hd⟩ := hu
  rw [hd, Matrix.diagonal_apply_eq]
  exact qTwoLMDivKindDiag_apply_ne_zero (qTwoLMDivKindDiag_prod_eq_one hd) i

private noncomputable def qTwoLMDivKindDiag_units (u : qTwoLMDivKind_diag F0 m) :
    Fin m → F0ˣ :=
  fun i => Units.mk0 ((((u : Su F0 2 1 m) : GL (Fin m) F0) :
    Matrix (Fin m) (Fin m) F0) i i) (qTwoLMDivKindDiag_entry_ne_zero u.2 i)

private theorem qTwoLMDivKindDiag_units_apply (u : qTwoLMDivKind_diag F0 m) (i : Fin m) :
    ((qTwoLMDivKindDiag_units u i : F0ˣ) : F0) =
      (((u : Su F0 2 1 m) : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) i i :=
  Units.val_mk0 _

private theorem qTwoLMDivKindDiag_prod_units (u : qTwoLMDivKind_diag F0 m) :
    ∏ i, qTwoLMDivKindDiag_units u i = 1 := by
  obtain ⟨d, hd⟩ := u.2
  have hdet : ∏ k, d k = 1 := qTwoLMDivKindDiag_prod_eq_one hd
  have hval : ((∏ i, qTwoLMDivKindDiag_units u i : F0ˣ) : F0) = 1 := by
    rw [Units.coe_prod]
    calc ∏ i, ((qTwoLMDivKindDiag_units u i : F0ˣ) : F0)
        = ∏ i, ((((u : Su F0 2 1 m) : GL (Fin m) F0) :
            Matrix (Fin m) (Fin m) F0) i i) :=
          Finset.prod_congr rfl fun i _ => qTwoLMDivKindDiag_units_apply u i
      _ = ∏ i, d i := by
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [hd, Matrix.diagonal_apply_eq]
      _ = 1 := hdet
  apply Units.ext
  simpa using hval

private noncomputable def qTwoLMDivKindDiag_toUnits (u : qTwoLMDivKind_diag F0 m) :
    {e : Fin m → F0ˣ // ∏ i, e i = 1} :=
  ⟨qTwoLMDivKindDiag_units u, qTwoLMDivKindDiag_prod_units u⟩

private theorem qTwoLMDivKindDiag_toUnits_apply (u : qTwoLMDivKind_diag F0 m) (i : Fin m) :
    ((qTwoLMDivKindDiag_toUnits u).1 i : F0) =
      (((u : Su F0 2 1 m) : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) i i :=
  qTwoLMDivKindDiag_units_apply u i

private noncomputable def qTwoLMDivKindDiag_ofUnits (hF : Nat.card F0 = 4)
    (e : {e : Fin m → F0ˣ // ∏ i, e i = 1}) : qTwoLMDivKind_diag F0 m :=
  ⟨ggNSPosPB2_diagSU (fun i => (e.1 i : F0))
      (by
        have h : ((∏ i, e.1 i : F0ˣ) : F0) = 1 := by rw [e.2, Units.val_one]
        simpa only [Units.coe_prod] using h)
      (fun i => qTwoLMDivKind_norm_eq_one hF (e.1 i).ne_zero),
    ⟨fun i => (e.1 i : F0), ggNSPosPB2_diagSU_coe _ _ _⟩⟩

private theorem qTwoLMDivKindDiag_ofUnits_coe (hF : Nat.card F0 = 4)
    (e : {e : Fin m → F0ˣ // ∏ i, e i = 1}) :
    ((((qTwoLMDivKindDiag_ofUnits hF e : qTwoLMDivKind_diag F0 m) : Su F0 2 1 m) :
      GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) = Matrix.diagonal (fun i => (e.1 i : F0)) :=
  ggNSPosPB2_diagSU_coe _ _ _

private noncomputable def qTwoLMDivKindDiag_unitsEquiv (hF : Nat.card F0 = 4) :
    qTwoLMDivKind_diag F0 m ≃ {e : Fin m → F0ˣ // ∏ i, e i = 1} where
  toFun := qTwoLMDivKindDiag_toUnits
  invFun := qTwoLMDivKindDiag_ofUnits hF
  left_inv u := by
    obtain ⟨d, hd⟩ := u.2
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    rw [qTwoLMDivKindDiag_ofUnits_coe hF, hd]
    congr 1
    funext i
    rw [qTwoLMDivKindDiag_toUnits_apply, hd, Matrix.diagonal_apply_eq]
  right_inv e := by
    apply Subtype.ext
    funext i
    apply Units.ext
    rw [qTwoLMDivKindDiag_toUnits_apply, qTwoLMDivKindDiag_ofUnits_coe hF,
      Matrix.diagonal_apply_eq]

private noncomputable def qTwoLMDivKindDiag_prodOneEquiv (n : ℕ) :
    {e : Fin (n + 1) → F0ˣ // ∏ i, e i = 1} ≃ (Fin n → F0ˣ) where
  toFun := fun e i => e.1 (Fin.castSucc i)
  invFun f := ⟨Fin.snoc f ((∏ i, f i)⁻¹), by
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    exact mul_inv_cancel _⟩
  left_inv e := by
    ext i
    refine Fin.lastCases ?_ ?_ i
    · simp only [Fin.snoc_last]
      have h : (∏ i : Fin n, e.1 (Fin.castSucc i)) * e.1 (Fin.last n) = 1 := by
        rw [← Fin.prod_univ_castSucc]
        exact e.2
      exact congrArg (fun u : F0ˣ => (u : F0)) (eq_inv_of_mul_eq_one_right h).symm
    · intro j
      simp only [Fin.snoc_castSucc]
  right_inv f := by
    ext i
    simp only [Fin.snoc_castSucc]

theorem qTwoLMDivKind_card_diag (hF : Nat.card F0 = 4) (hm : 1 ≤ m) :
    Nat.card (qTwoLMDivKind_diag F0 m) = 3 ^ (m - 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [Nat.add_sub_cancel,
    Nat.card_congr (qTwoLMDivKindDiag_unitsEquiv (m := n + 1) hF),
    Nat.card_congr (qTwoLMDivKindDiag_prodOneEquiv (F0 := F0) n), Nat.card_fun,
    Nat.card_fin, qTwoLMDivKindDiag_card_units hF]

theorem qTwoLMDivKind_pow_three_of_mem_diag (hF : Nat.card F0 = 4) {u : Su F0 2 1 m}
    (hu : u ∈ qTwoLMDivKind_diag F0 m) : u ^ 3 = 1 := by
  obtain ⟨d, hd⟩ := hu
  have hdet : ∏ k, d k = 1 := qTwoLMDivKindDiag_prod_eq_one hd
  have hdp : ∀ k, d k ^ 3 = 1 := by
    intro k
    rw [← qTwoLMDivKindDiag_unitary_mul_self (d k)]
    exact qTwoLMDivKind_norm_eq_one hF (qTwoLMDivKindDiag_apply_ne_zero hdet k)
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hd, Matrix.diagonal_pow,
    show d ^ 3 = fun _ => (1 : F0) from funext hdp, Matrix.diagonal_one]
  rfl

theorem qTwoLMDivKind_center_le_diag (hF : Nat.card F0 = 4) (hm : 3 ≤ m) :
    Subgroup.center (Su F0 2 1 m) ≤ qTwoLMDivKind_diag F0 m := by
  intro z hz
  obtain ⟨u, hu⟩ := exists_scalar_of_mem_center
    (CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution
      (qTwoLMDivKindDiag_card_eq_sq hF)) hm hz
  exact ⟨fun _ => (u : F0), by rw [hu, Matrix.scalar_apply]⟩

theorem qTwoLMDivKind_card_center_le (hF : Nat.card F0 = 4) (hm : 3 ≤ m) :
    Nat.card (Subgroup.center (Su F0 2 1 m)) ≤ 3 := by
  have hσ := CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution
    (qTwoLMDivKindDiag_card_eq_sq hF)
  let f : Subgroup.center (Su F0 2 1 m) → F0ˣ := fun z =>
    Classical.choose (exists_scalar_of_mem_center hσ hm z.2)
  have hf : ∀ z : Subgroup.center (Su F0 2 1 m),
      (((z.1 : Su F0 2 1 m) : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) =
        Matrix.scalar (Fin m) (f z : F0) := fun z =>
    Classical.choose_spec (exists_scalar_of_mem_center hσ hm z.2)
  have hinj : Function.Injective f := by
    intro z w hzw
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    rw [hf z, hf w, hzw]
  calc Nat.card (Subgroup.center (Su F0 2 1 m)) ≤ Nat.card F0ˣ :=
        Nat.card_le_card_of_injective f hinj
    _ = 3 := qTwoLMDivKindDiag_card_units hF

end CFSG.StandardType.QTwo

end
