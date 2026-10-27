module

public import CFSG.Monster.Spin.OperatorBasis
public import CFSG.Monster.Dyadic

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Spin

open CFSG.Monster.Code CFSG.Monster Matrix

@[expose] def Qmats : Set (Matrix SpinIdx SpinIdx ℚ) :=
  (fun g : GL SpinIdx ℚ => (g : Matrix SpinIdx SpinIdx ℚ)) '' (Q : Set (GL SpinIdx ℚ))

@[expose] def dyadicMatrices : Submodule dyadic (Matrix SpinIdx SpinIdx ℚ) where
  carrier := {M | ∀ i j, M i j ∈ dyadic}
  add_mem' := fun hM hN i j => dyadic.add_mem (hM i j) (hN i j)
  zero_mem' := fun _ _ => dyadic.zero_mem
  smul_mem' := fun c _ hM i j => dyadic.mul_mem c.2 (hM i j)

theorem mem_dyadicMatrices {M : Matrix SpinIdx SpinIdx ℚ} :
    M ∈ dyadicMatrices ↔ ∀ i j, M i j ∈ dyadic := Iff.rfl

theorem qmatR_mem_dyadic (s : ZMod 2) (a : C) (δ : Cocode) (i j : SpinIdx) :
    qmatR ℚ s a δ i j ∈ dyadic := by
  rcases qmatR_apply_mem (R := ℚ) s a δ i j with h | h | h <;> rw [h]
  · exact dyadic.zero_mem
  · exact dyadic.one_mem
  · exact dyadic.neg_mem dyadic.one_mem

theorem Qmats_mem_dyadic {g : Matrix SpinIdx SpinIdx ℚ} (hg : g ∈ Qmats) (i j : SpinIdx) :
    g i j ∈ dyadic := by
  obtain ⟨u, hu, rfl⟩ := hg
  rw [← range_toGL] at hu
  obtain ⟨x, rfl⟩ := hu
  show (toGL x : Matrix SpinIdx SpinIdx ℚ) i j ∈ dyadic
  rw [coe_toGL]
  exact qmatR_mem_dyadic _ _ _ i j

theorem TDR_mem_Qmats (p : C × Cocode) : TDR ℚ p ∈ Qmats :=
  ⟨TU p.1 * DU p.2, Q.mul_mem (TU_mem_Q _) (DU_mem_Q _), rfl⟩

private theorem two_ne_zero_rat' : (2 : ℚ) ≠ 0 := two_ne_zero

theorem eq_sum_trace_smul_TDR (M : Matrix SpinIdx SpinIdx ℚ) :
    M = ∑ p : C × Cocode, (trace ((TDR ℚ p)ᵀ * M) / 4096) • TDR ℚ p := by
  have hb := (TDbasis two_ne_zero_rat').sum_repr M
  rw [coe_TDbasis] at hb
  have hc : ∀ q, trace ((TDR ℚ q)ᵀ * M) = (TDbasis two_ne_zero_rat').repr M q * 4096 := by
    intro q
    conv_lhs => rw [← hb]
    simp only [Matrix.mul_sum, Matrix.mul_smul, trace_sum, trace_smul,
      trace_transpose_TDR_mul two_ne_zero_rat', smul_eq_mul, mul_ite, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  conv_lhs => rw [← hb]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [hc q, mul_div_assoc, div_self (four_thousand_ninety_six_ne_zero two_ne_zero_rat'), mul_one]

theorem trace_transpose_mul_mem_dyadic {M N : Matrix SpinIdx SpinIdx ℚ}
    (hM : ∀ i j, M i j ∈ dyadic) (hN : ∀ i j, N i j ∈ dyadic) : trace (Mᵀ * N) ∈ dyadic := by
  rw [trace]
  refine dyadic.sum_mem fun i _ => ?_
  rw [diag_apply, mul_apply]
  exact dyadic.sum_mem fun j _ => dyadic.mul_mem (hM j i) (hN j i)

theorem inv_4096_mem_dyadic : (4096 : ℚ)⁻¹ ∈ dyadic :=
  ⟨12, by norm_num⟩

theorem span_dyadic_Qmats : Submodule.span dyadic Qmats = dyadicMatrices := by
  apply le_antisymm
  · rw [Submodule.span_le]
    exact fun g hg => Qmats_mem_dyadic hg
  · intro M hM
    have hcoef : ∀ p : C × Cocode, trace ((TDR ℚ p)ᵀ * M) / 4096 ∈ dyadic := fun p => by
      rw [div_eq_mul_inv]
      refine dyadic.mul_mem (trace_transpose_mul_mem_dyadic ?_ hM) inv_4096_mem_dyadic
      intro i j
      rw [TDR_eq_qmatR]
      exact qmatR_mem_dyadic _ _ _ i j
    have hM' : M = ∑ p : C × Cocode, (⟨_, hcoef p⟩ : dyadic) • TDR ℚ p :=
      eq_sum_trace_smul_TDR M
    rw [hM']
    exact Submodule.sum_mem _ fun p _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (TDR_mem_Qmats p))

theorem mem_span_dyadic_Qmats_iff (M : Matrix SpinIdx SpinIdx ℚ) :
    M ∈ Submodule.span dyadic Qmats ↔ ∀ i j, M i j ∈ dyadic := by
  rw [span_dyadic_Qmats, mem_dyadicMatrices]

theorem dyadic_of_conj_Q_subset (s : Matrix SpinIdx SpinIdx ℚ) (hs : sᵀ * s = 1)
    (hconj : ∀ g ∈ Qmats, s⁻¹ * g * s ∈ Qmats) : ∀ i j, s i j ∈ dyadic ∧ s⁻¹ i j ∈ dyadic := by
  have hinv : s⁻¹ = sᵀ := Matrix.inv_eq_left_inv hs
  refine dyadic_entries_of_conj_mem Qmats (fun g hg => Qmats_mem_dyadic hg)
    (fun M hM => (mem_span_dyadic_Qmats_iff M).2 hM) s hs fun g hg => ?_
  rw [← hinv]
  exact hconj g hg

theorem dyadic_of_conj_Q (s : Matrix SpinIdx SpinIdx ℚ) (hs : sᵀ * s = 1)
    (hconj : (fun g => s⁻¹ * g * s) '' Qmats = Qmats) (i j : SpinIdx) : s i j ∈ dyadic :=
  (dyadic_of_conj_Q_subset s hs (fun _ hg => hconj ▸ Set.mem_image_of_mem _ hg) i j).1

theorem spin_rational_normalizers_dyadic :
    Submodule.span dyadic Qmats = dyadicMatrices ∧
    (∀ M : Matrix SpinIdx SpinIdx ℚ, M ∈ Submodule.span dyadic Qmats ↔ ∀ i j, M i j ∈ dyadic) ∧
    ∀ s : Matrix SpinIdx SpinIdx ℚ, sᵀ * s = 1 → (fun g => s⁻¹ * g * s) '' Qmats = Qmats →
      ∀ i j, s i j ∈ dyadic :=
  ⟨span_dyadic_Qmats, mem_span_dyadic_Qmats_iff, dyadic_of_conj_Q⟩

end CFSG.Monster.Spin
