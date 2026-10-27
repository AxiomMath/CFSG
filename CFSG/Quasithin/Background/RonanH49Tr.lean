module

public import CFSG.Quasithin.Background.RonanH49Base
public import CFSG.Quasithin.Background.HL3WrOff

public section

namespace CFSG.Quasithin.RonanH49

open CFSG.Quasithin CFSG.Quasithin.H.L3Wr
open scoped Matrix

theorem toAdd_dWd_tr : Multiplicative.toAdd dWd = (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
  decide

theorem toAdd_eW_tr (i j : Fin 3) : Multiplicative.toAdd (eW i j) = Matrix.single i j 1 := rfl

theorem dWd_mul_self_tr : dWd * dWd = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_mul, toAdd_dWd_tr, toAdd_one]
  decide

theorem dWd_zpow_tr (k : ℤ) : dWd ^ k = 1 ∨ dWd ^ k = dWd := by
  induction k using Int.induction_on with
  | zero => exact Or.inl (zpow_zero dWd)
  | succ i ih =>
    rcases ih with h | h
    · exact Or.inr (by rw [zpow_add_one, h, one_mul])
    · exact Or.inl (by rw [zpow_add_one, h, dWd_mul_self_tr])
  | pred i ih =>
    rcases ih with h | h
    · refine Or.inr ?_
      rw [zpow_sub_one, h, one_mul]
      exact inv_eq_of_mul_eq_one_right dWd_mul_self_tr
    · exact Or.inl (by rw [zpow_sub_one, h, mul_inv_cancel])

theorem trZ_mem_iff {X : WMod} : X ∈ trZ ↔ Matrix.trace (Multiplicative.toAdd X) = 0 :=
  Iff.rfl

theorem det_trSL_ne {i j : Fin 3} (hij : i ≠ j) :
    ((1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) + Matrix.single i j 1).det ≠ 0 := by
  have key : ∀ a b : Fin 3, a ≠ b →
      ((1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) + Matrix.single a b 1).det ≠ 0 := by
    decide
  exact key i j hij

noncomputable def trSL (i j : Fin 3) (hij : i ≠ j) : ↥SL32 :=
  slOfMat ((1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) + Matrix.single i j 1) (det_trSL_ne hij)

theorem mat_trSL {i j : Fin 3} (hij : i ≠ j) :
    mat (trSL i j hij) = (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) + Matrix.single i j 1 :=
  mat_slOfMat _ _

noncomputable def trRho {i j : Fin 3} (hij : i ≠ j) : MulAut WMod :=
  rho (trSL i j hij, trSL j i hij.symm)

theorem toAdd_trRho {i j : Fin 3} (hij : i ≠ j) (X : WMod) :
    Multiplicative.toAdd (trRho hij X) =
      ((1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) + Matrix.single i j 1) * Multiplicative.toAdd X *
        ((1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) + Matrix.single i j 1) := by
  change mat (trSL i j hij) * Multiplicative.toAdd X * (mat (trSL j i hij.symm))ᵀ = _
  rw [mat_trSL, mat_trSL, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_single]

theorem trE_sq : ∀ a b : Fin 3, a ≠ b →
    ((1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) + Matrix.single a b 1) *
      ((1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) + Matrix.single a b 1) = 1 := by
  decide

theorem trA_eq : ∀ a b c : Fin 3, a ≠ b →
    ((1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) + Matrix.single a c 1) * Matrix.single c b 1 *
      ((1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) + Matrix.single a c 1) =
      Matrix.single c b 1 + Matrix.single a b 1 := by
  decide

theorem trB_eq : ∀ a b : Fin 3, a ≠ b →
    ((1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) + Matrix.single a b 1) * Matrix.single b a 1 *
      ((1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) + Matrix.single a b 1) =
      Matrix.single b a 1 + Matrix.single a a 1 + Matrix.single b b 1 + Matrix.single a b 1 := by
  decide

theorem trRho_mem_Cd {i j : Fin 3} (hij : i ≠ j) : trRho hij ∈ Cd := by
  rw [mem_Cd]
  refine ⟨img_le_norm (rho_mem_img _), ?_⟩
  apply Multiplicative.toAdd.injective
  rw [toAdd_trRho, toAdd_dWd_tr, Matrix.mul_one, trE_sq i j hij]

theorem mem_commOnR_tr {a : MulAut WMod} (ha : a ∈ Cd) (w : WMod) :
    a w * w⁻¹ ∈ commOnR ⊤ Cd := by
  unfold commOnR
  exact Subgroup.subset_closure ⟨a, ha, w, Subgroup.mem_top w, rfl⟩

theorem trace_act_Cd_tr {a : MulAut WMod} (ha : a ∈ Cd) (w : WMod) :
    Matrix.trace (Multiplicative.toAdd (a w)) = Matrix.trace (Multiplicative.toAdd w) := by
  obtain ⟨hn, hd⟩ := mem_Cd.1 ha
  obtain ⟨g, hg | hg⟩ := mem_norm_iff.1 hn
  · have key : mat g.1 * (mat g.2)ᵀ = 1 := by
      have h := congrArg Multiplicative.toAdd hd
      rw [hg, toAdd_rho, toAdd_dWd_tr, Matrix.mul_one] at h
      exact h
    have hBA : (mat g.2)ᵀ * mat g.1 = 1 := mul_eq_one_comm.1 key
    rw [hg, toAdd_rho, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hBA, Matrix.one_mul]
  · have htd : tau dWd = dWd := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_tau, toAdd_dWd_tr, Matrix.transpose_one]
    have key : mat g.1 * (mat g.2)ᵀ = 1 := by
      have h := congrArg Multiplicative.toAdd hd
      rw [hg, MulAut.mul_apply, htd, toAdd_rho, toAdd_dWd_tr, Matrix.mul_one] at h
      exact h
    have hBA : (mat g.2)ᵀ * mat g.1 = 1 := mul_eq_one_comm.1 key
    rw [hg, MulAut.mul_apply, toAdd_rho, toAdd_tau, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
      hBA, Matrix.one_mul, Matrix.trace_transpose]

theorem commOnR_le_trZ_tr : commOnR ⊤ Cd ≤ trZ := by
  unfold commOnR
  rw [Subgroup.closure_le]
  rintro u ⟨a, ha, w, -, rfl⟩
  refine trZ_mem_iff.2 ?_
  rw [toAdd_mul, toAdd_inv, Matrix.trace_add]
  have h1 := trace_act_Cd_tr ha w
  have h2 : Matrix.trace (-Multiplicative.toAdd w) = -Matrix.trace (Multiplicative.toAdd w) :=
    Matrix.trace_neg _
  exact (congrArg₂ (· + ·) h1 h2).trans (add_neg_cancel _)

theorem eW_mem_commOnR_tr {i j : Fin 3} (hij : i ≠ j) : eW i j ∈ commOnR ⊤ Cd := by
  obtain ⟨k, hk⟩ := Fintype.exists_ne_of_one_lt_card (by simp) i
  have hik : i ≠ k := hk.symm
  have e : trRho hik (eW k j) * (eW k j)⁻¹ = eW i j := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_mul, toAdd_inv, toAdd_trRho, toAdd_eW_tr]
    rw [trA_eq i j k hij]
    abel
  rw [← e]
  exact mem_commOnR_tr (trRho_mem_Cd hik) _

theorem eW_diag_mem_commOnR_tr {i j : Fin 3} (hij : i ≠ j) :
    eW i i * eW j j ∈ commOnR ⊤ Cd := by
  have h1 : trRho hij (eW j i) * (eW j i)⁻¹ ∈ commOnR ⊤ Cd :=
    mem_commOnR_tr (trRho_mem_Cd hij) _
  have h2 : eW i j ∈ commOnR ⊤ Cd := eW_mem_commOnR_tr hij
  have e : trRho hij (eW j i) * (eW j i)⁻¹ * (eW i j)⁻¹ = eW i i * eW j j := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_mul, toAdd_inv, toAdd_trRho, toAdd_eW_tr]
    rw [trB_eq i j hij]
    abel
  rw [← e]
  exact mul_mem h1 (inv_mem h2)

theorem trZ_eq_prod_tr (X : WMod) (hX : Matrix.trace (Multiplicative.toAdd X) = 0) :
    X = eW 0 1 ^ (Multiplicative.toAdd X 0 1).val * eW 0 2 ^ (Multiplicative.toAdd X 0 2).val *
      eW 1 0 ^ (Multiplicative.toAdd X 1 0).val * eW 1 2 ^ (Multiplicative.toAdd X 1 2).val *
      eW 2 0 ^ (Multiplicative.toAdd X 2 0).val * eW 2 1 ^ (Multiplicative.toAdd X 2 1).val *
      (eW 0 0 * eW 2 2) ^ (Multiplicative.toAdd X 0 0).val *
      (eW 1 1 * eW 2 2) ^ (Multiplicative.toAdd X 1 1).val := by
  have h22 : Multiplicative.toAdd X 2 2 =
      Multiplicative.toAdd X 0 0 + Multiplicative.toAdd X 1 1 := by
    have hs : ∀ a b c : ZMod 2, a + b + c = 0 → c = a + b := by decide
    apply hs
    rw [Matrix.trace_fin_three] at hX
    exact hX
  apply Multiplicative.toAdd.injective
  simp only [toAdd_mul, toAdd_pow, toAdd_eW_tr]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.single_apply, h22, ZMod.natCast_zmod_val]

theorem trZ_le_commOnR_tr : trZ ≤ commOnR ⊤ Cd := by
  intro X hX
  have g01 : eW 0 1 ∈ commOnR ⊤ Cd := eW_mem_commOnR_tr (by decide)
  have g02 : eW 0 2 ∈ commOnR ⊤ Cd := eW_mem_commOnR_tr (by decide)
  have g10 : eW 1 0 ∈ commOnR ⊤ Cd := eW_mem_commOnR_tr (by decide)
  have g12 : eW 1 2 ∈ commOnR ⊤ Cd := eW_mem_commOnR_tr (by decide)
  have g20 : eW 2 0 ∈ commOnR ⊤ Cd := eW_mem_commOnR_tr (by decide)
  have g21 : eW 2 1 ∈ commOnR ⊤ Cd := eW_mem_commOnR_tr (by decide)
  have gd0 : eW 0 0 * eW 2 2 ∈ commOnR ⊤ Cd := eW_diag_mem_commOnR_tr (by decide)
  have gd1 : eW 1 1 * eW 2 2 ∈ commOnR ⊤ Cd := eW_diag_mem_commOnR_tr (by decide)
  rw [trZ_eq_prod_tr X (trZ_mem_iff.1 hX)]
  exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem
    (pow_mem g01 _) (pow_mem g02 _)) (pow_mem g10 _)) (pow_mem g12 _))
    (pow_mem g20 _)) (pow_mem g21 _)) (pow_mem gd0 _)) (pow_mem gd1 _)

theorem card_trZ_tr : Nat.card ↥trZ = 256 := by
  have e : ↥trZ ≃ {M : Matrix (Fin 3) (Fin 3) (ZMod 2) // Matrix.trace M = 0} :=
    { toFun := fun X => ⟨Multiplicative.toAdd (X : WMod), trZ_mem_iff.1 X.2⟩
      invFun := fun M => ⟨Multiplicative.ofAdd M.1, trZ_mem_iff.2 M.2⟩
      left_inv := fun X => Subtype.ext rfl
      right_inv := fun M => Subtype.ext rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

theorem commOnR_Cd_eq : commOnR ⊤ Cd = trZ :=
  le_antisymm commOnR_le_trZ_tr trZ_le_commOnR_tr

theorem trZ_sup_dWd : trZ ⊔ Subgroup.zpowers dWd = ⊤ := by
  rw [eq_top_iff]
  intro X _
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (Matrix.trace (Multiplicative.toAdd X))
    with h | h
  · exact Subgroup.mem_sup_left (trZ_mem_iff.2 h)
  · have hY : X * dWd ∈ trZ := by
      rw [trZ_mem_iff, toAdd_mul, toAdd_dWd_tr, Matrix.trace_add, Matrix.trace_one, h,
        Fintype.card_fin]
      decide
    have hm := mul_mem (Subgroup.mem_sup_left hY)
      (Subgroup.mem_sup_right (inv_mem (Subgroup.mem_zpowers dWd)))
    rwa [mul_inv_cancel_right] at hm

theorem trZ_inf_dWd : trZ ⊓ Subgroup.zpowers dWd = ⊥ := by
  rw [eq_bot_iff]
  rintro X ⟨hX, hZ⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hZ
  rcases dWd_zpow_tr k with h | h
  · rw [h]
    exact Subgroup.mem_bot.2 rfl
  · exfalso
    rw [h] at hX
    have h0 : Matrix.trace (Multiplicative.toAdd dWd) = 0 := trZ_mem_iff.1 hX
    rw [toAdd_dWd_tr] at h0
    exact absurd h0 (by decide)

theorem rk_trZ : rk ↥trZ = 8 := by
  unfold rk
  rw [card_trZ_tr, show (256 : ℕ) = 2 ^ 8 by norm_num, padicValNat.prime_pow]

end CFSG.Quasithin.RonanH49
