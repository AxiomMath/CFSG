module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsCoresSkolem
public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism
public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField

public section

namespace CFSG.StandardType

namespace LayerCores

open Matrix CFSG.LocalAnalysis.ComponentInitial

variable {D : Type} [Field D]

theorem exists_unitaryFieldData_of_invol [Finite D] [CharP D 2] (ρ : D →+* D)
    (hρ2 : ∀ c, ρ (ρ c) = c) (hρ1 : ∃ c, ρ c ≠ c) :
    ∃ f : ℕ, ∃ hE : UnitaryFieldData 2 f D, ∀ c, hE.bar c = ρ c := by
  classical
  have := Fintype.ofFinite D
  obtain ⟨n, -, hn⟩ := FiniteField.card D 2
  have hD : Nat.card D = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  obtain ⟨σ, hσ, hord, hzp, hcard, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality Nat.prime_two n.pos hD
  have : Finite (D ≃+* D) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact n.ne_zero)
  let ρe : D ≃+* D := { ρ with invFun := ρ, left_inv := hρ2, right_inv := hρ2 }
  have hρe : ∀ c, ρe c = ρ c := fun _ => rfl
  have hmem : ρe ∈ Subgroup.zpowers σ := hzp ▸ Subgroup.mem_top ρe
  obtain ⟨m, hm⟩ := ((isOfFinOrder_of_finite σ).mem_powers_iff_mem_zpowers).mpr hmem
  have hk : σ ^ (m % n) = ρe := by
    rw [show (m % (n : ℕ)) = m % orderOf σ by rw [hord], pow_mod_orderOf]
    exact hm
  have hkn : m % (n : ℕ) < n := Nat.mod_lt _ n.pos
  have hsq : σ ^ (2 * (m % (n : ℕ))) = 1 := by
    rw [pow_mul', hk]
    ext c
    show ρe (ρe c) = c
    rw [hρe, hρe, hρ2]
  have hdvd : (n : ℕ) ∣ 2 * (m % (n : ℕ)) := by
    have h := orderOf_dvd_of_pow_eq_one hsq
    rwa [hord] at h
  have hk0 : m % (n : ℕ) ≠ 0 := by
    intro h0
    obtain ⟨c, hc⟩ := hρ1
    apply hc
    have h1 : ρe = 1 := by rw [← hk, h0, pow_zero]
    rw [← hρe, h1]
    rfl
  have h2k : 2 * (m % (n : ℕ)) = n := by
    obtain ⟨j, hj⟩ := hdvd
    rcases j with _ | _ | j
    · omega
    · omega
    · nlinarith
  refine ⟨m % n, ⟨Nat.prime_two, Nat.one_le_iff_ne_zero.mpr hk0, by rw [hD, h2k]⟩, fun c => ?_⟩
  rw [UnitaryFieldData.bar_apply]
  have hpow : ∀ j : ℕ, (σ ^ j) c = c ^ 2 ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ']
      show σ ((σ ^ j) c) = _
      rw [ih, hσ, ← pow_mul, pow_succ]
  rw [← hpow, hk, hρe]

theorem exists_hilbert90 [CharP D 2] (ρ : D →+* D) (hρ2 : ∀ c, ρ (ρ c) = c)
    (hρ1 : ∃ c, ρ c ≠ c) {l : D} (hl : ρ l * l = 1) : ∃ μ : D, μ ≠ 0 ∧ ρ μ * l = μ := by
  have key : ∀ c, ρ (c + l * ρ c) * l = c + l * ρ c := by
    intro c
    rw [map_add, map_mul, hρ2, add_mul, mul_assoc, mul_comm c l, ← mul_assoc, hl, one_mul,
      mul_comm, add_comm]
  by_contra h
  push Not at h
  have hall : ∀ c, c + l * ρ c = 0 := fun c => by
    by_contra hne
    exact h _ hne (key c)
  have h1 := hall 1
  rw [map_one, mul_one] at h1
  have hl1 : l = 1 := by
    rw [eq_neg_of_add_eq_zero_right h1, CharTwo.neg_eq]
  obtain ⟨c, hc⟩ := hρ1
  have h2 := hall c
  rw [hl1, one_mul] at h2
  exact hc (by rw [eq_neg_of_add_eq_zero_right h2, CharTwo.neg_eq])

variable {d : ℕ} {T : Matrix (Fin d) (Fin d) D → Matrix (Fin d) (Fin d) D}

theorem exists_ct_gram_eq [NeZero d] (hT : IsInvol T) (ρ : D →+* D) (hρ2 : ∀ c, ρ (ρ c) = c)
    (H : GL (Fin d) D)
    (hH : ∀ x, T x = ((H⁻¹ : GL (Fin d) D) : Matrix (Fin d) (Fin d) D) * (x.map ρ)ᵀ *
      (H : Matrix (Fin d) (Fin d) D)) :
    ∃ l : D, ct ρ (H : Matrix (Fin d) (Fin d) D) = l • (H : Matrix (Fin d) (Fin d) D) ∧
      ρ l * l = 1 := by
  set M : Matrix (Fin d) (Fin d) D := ↑H with hM
  set Mi : Matrix (Fin d) (Fin d) D := ((H⁻¹ : GL (Fin d) D) : Matrix (Fin d) (Fin d) D)
  have hH' : ∀ x, T x = Mi * ct ρ x * M := hH
  have hMMi : M * Mi = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hMiM : Mi * M = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hZ : ∀ x : Matrix (Fin d) (Fin d) D, x * (Mi * ct ρ M) = (Mi * ct ρ M) * x := by
    intro x
    have h1 : x = Mi * ct ρ M * x * (ct ρ Mi * M) := by
      have h0 := hT.invol x
      rw [hH', hH', ct_mul, ct_mul, ct_ct ρ hρ2] at h0
      calc x = Mi * (ct ρ M * (x * ct ρ Mi)) * M := h0.symm
        _ = _ := by simp only [Matrix.mul_assoc]
    have h2 : ct ρ Mi * M * (Mi * ct ρ M) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc M, hMMi, Matrix.one_mul, ← ct_mul, hMMi, ct_one]
    calc x * (Mi * ct ρ M) = Mi * ct ρ M * x * (ct ρ Mi * M * (Mi * ct ρ M)) := by
          conv_lhs => rw [h1]
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h2, Matrix.mul_one]
  have hc : Mi * ct ρ M ∈ Set.center (Matrix (Fin d) (Fin d) D) := by
    rw [Semigroup.mem_center_iff]
    exact hZ
  rw [Matrix.center_eq_range] at hc
  obtain ⟨l, hl⟩ := hc
  have hMt : ct ρ M = l • M := by
    calc ct ρ M = M * (Mi * ct ρ M) := by rw [← Matrix.mul_assoc, hMMi, Matrix.one_mul]
      _ = l • M := by rw [← hl, Matrix.scalar_apply, ← smul_eq_mul_diagonal]
  refine ⟨l, hMt, ?_⟩
  have hll : (ρ l * l) • M = M := by
    calc (ρ l * l) • M = ρ l • ct ρ M := by rw [hMt, smul_smul]
      _ = ct ρ (l • M) := by rw [ct_smul]
      _ = M := by rw [← hMt, ct_ct ρ hρ2]
  have h3 : (ρ l * l) • (1 : Matrix (Fin d) (Fin d) D) = 1 := by
    calc (ρ l * l) • (1 : Matrix (Fin d) (Fin d) D) = ((ρ l * l) • M) * Mi := by
          rw [Matrix.smul_mul, hMMi]
      _ = 1 := by rw [hll, hMMi]
  have h4 := congrFun (congrFun h3 0) 0
  simpa using h4

end LayerCores

end CFSG.StandardType
