module

public import CFSG.LocalAnalysis.StandardType.GGTPRowDataDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ggTP_qPlus_smul (r : ℕ) (K : Type) [Field K] (c : K) (v : Fin r ⊕ Fin r → K) :
    LargeEvenQPlus K r (c • v) = c ^ 2 * LargeEvenQPlus K r v := by
  rw [largeEvenQPlus_def]
  beta_reduce
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem ggTP_qPlus_eq_one (r : ℕ) [NeZero r] (K : Type) [Field K] :
    ∃ v : Fin r ⊕ Fin r → K, LargeEvenQPlus K r v = 1 := by
  let v : Fin r ⊕ Fin r → K := fun x =>
    match x with
    | Sum.inl i => if i = 0 then 1 else 0
    | Sum.inr i => if i = 0 then 1 else 0
  refine ⟨v, ?_⟩
  rw [largeEvenQPlus_def]
  beta_reduce
  rw [Finset.sum_eq_single (0 : Fin r)]
  · simp [v]
  · intro b _ hb
    simp [v, hb]
  · intro h0
    exact absurd (Finset.mem_univ _) h0

private theorem ggTP_omega_le_orth {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Q : (ι → K) → K) : LargeEvenOmega Q ≤ LargeEvenOrthGroup Q := by
  rw [largeEvenOmega_def]
  exact Subgroup.commutator_le_self _

private theorem ggTP_orth_isometry {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Q : (ι → K) → K) {g : GL ι K} (hg : g ∈ LargeEvenOrthGroup Q) (v : ι → K) :
    Q ((g : Matrix ι ι K).mulVec v) = Q v := by
  rw [largeEvenOrthGroup_def] at hg
  let P : Subgroup (GL ι K) :=
    { carrier := {A | ∀ v, Q ((A : Matrix ι ι K).mulVec v) = Q v}
      mul_mem' := by
        intro A B hA hB v
        rw [Matrix.GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec]
        exact (hA _).trans (hB v)
      one_mem' := by
        intro v
        rw [Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
      inv_mem' := by
        intro A hA v
        rw [Matrix.GeneralLinearGroup.coe_inv]
        have hmul : (A : Matrix ι ι K) * (A : Matrix ι ι K)⁻¹ = 1 := by
          rw [← Matrix.GeneralLinearGroup.coe_inv, ← Matrix.GeneralLinearGroup.coe_mul,
            mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one]
        have h := hA ((A : Matrix ι ι K)⁻¹.mulVec v)
        rw [Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec] at h
        exact h.symm }
  exact ((Subgroup.closure_le P).mpr (fun A hA => hA)) hg v

theorem ggTPRowData_D {r n : ℕ} (hr : r = 6 ∨ r = 7) {Y : Type} [Group Y]
    (hY : GGHasLabel ⟨.D, r, n⟩ Y) : GGTPRowDatum Y := by
  have hr3 : r ≠ 3 := by rintro rfl; omega
  rw [GGHasLabel] at hY
  simp only [CFSG.StandardType.LargeEvenRawDatum] at hY
  rw [if_neg hr3] at hY
  obtain ⟨K, hKf, hKfin, hKcard, he⟩ := hY
  obtain ⟨e⟩ := he
  letI := hKf
  letI := hKfin
  haveI : Fintype K := Fintype.ofFinite K
  haveI : NeZero r := ⟨by omega⟩
  haveI hchar2 : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
    rw [Fintype.card_eq_nat_card, hKcard])
  refine ⟨Fin r ⊕ Fin r, inferInstance, inferInstance, K, hKf, hKfin,
    LargeEvenOmega (LargeEvenQPlus K r), ⟨e⟩, ?_, ?_, ?_⟩
  · rw [Fintype.card_sum, Fintype.card_fin]
    omega
  · exact hchar2
  · have hZbot : (LargeEvenScalars (Fin r ⊕ Fin r) K).subgroupOf
        (LargeEvenOmega (LargeEvenQPlus K r)) = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      rw [Subgroup.mem_subgroupOf] at hx
      rw [largeEvenScalars_def] at hx
      obtain ⟨u, hu⟩ := hx
      apply Subtype.ext
      rw [← hu]
      obtain ⟨v, hv⟩ := ggTP_qPlus_eq_one r K
      have hmem : Matrix.GeneralLinearGroup.scalar (Fin r ⊕ Fin r) u ∈
          LargeEvenOrthGroup (LargeEvenQPlus K r) :=
        ggTP_omega_le_orth _ (by rw [hu]; exact x.2)
      have hiso := ggTP_orth_isometry (LargeEvenQPlus K r) hmem v
      rw [Matrix.GeneralLinearGroup.coe_scalar] at hiso
      have hmat : (Matrix.scalar (Fin r ⊕ Fin r) (u : K)).mulVec v = (u : K) • v := by
        rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mulVec,
          Matrix.one_mulVec]
      rw [hmat, ggTP_qPlus_smul] at hiso
      rw [hv, mul_one] at hiso
      have hu1 : (u : K) = 1 := by
        have hchar : (2 : K) = 0 := CharP.cast_eq_zero K 2
        have h2c : (2 : K) * (u : K) * 1 = 0 := by rw [hchar, zero_mul, zero_mul]
        have h2 : ((u : K) - 1) ^ 2 = 0 := by
          rw [sub_sq, hiso, h2c, one_pow]
          rw [show (1 : K) - 0 + 1 = (2 : K) by ring, hchar]
        have h3 : ((u : K) - 1) * ((u : K) - 1) = 0 := by
          rwa [pow_two] at h2
        exact sub_eq_zero.mp (mul_self_eq_zero.mp h3)
      have hu1' : u = 1 := Units.ext (by rw [hu1, Units.val_one])
      simp [hu1']
    rw [hZbot, Subgroup.card_bot]
    norm_num

end CFSG.StandardType

end
