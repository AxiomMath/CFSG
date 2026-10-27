module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDCoxMat
public import CFSG.LocalAnalysis.StandardType.GGRCSignedCoxeterD
public import CFSG.LocalAnalysis.StandardType.GGOrthRk1GenComb

public section

namespace CFSG.StandardType.QTwo

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma plh_prod_sign_pair (m : ℕ) {a b : Fin m} (hab : a ≠ b) :
    ∏ i : Fin m, (if i = a ∨ i = b then (-1 : ZMod 3) else 1) = 1 := by
  rw [show (∏ i : Fin m, (if i = a ∨ i = b then (-1 : ZMod 3) else 1)) =
      ∏ i : Fin m, (if i ∈ ({a, b} : Finset (Fin m)) then (-1 : ZMod 3) else 1) by
    apply Finset.prod_congr rfl
    intro i _
    by_cases h : i = a ∨ i = b <;> simp [h, Finset.mem_insert, Finset.mem_singleton]]
  rw [Fintype.prod_ite_mem, Finset.prod_pair hab]
  decide

private lemma plh_sq_unit {x : ZMod 3} (h : x = 1 ∨ x = -1) : x * x = 1 := by
  rcases h with h | h <;> rw [h] <;> decide

private lemma plh_dTau_action (m : ℕ) (ε : Bool) {a b : Fin m} (hab : a ≠ b) (i : Fin m) :
    dTau m ε a b (dBasis m i) =
      (if ε then (if i = a ∨ i = b then (-1 : ZMod 3) else 1) else 1) •
        dBasis m (Equiv.swap a b i) := by
  by_cases hia : i = a
  · subst hia
    rw [dTau_apply_left m ε hab]
    cases ε <;> simp [Equiv.swap_apply_left]
  · by_cases hib : i = b
    · subst hib
      rw [dTau_apply_right m ε hab]
      cases ε <;> simp [Equiv.swap_apply_right]
    · rw [dTau_apply_of_ne m ε hia hib]
      cases ε <;> simp [Equiv.swap_apply_of_ne_of_ne hia hib, hia, hib]

@[expose] def dEven (m : ℕ) : Subgroup (DVec m ≃ₗ[ZMod 3] DVec m) where
  carrier := {a | ∃ (σ : Equiv.Perm (Fin m)) (c : Fin m → ZMod 3),
    (∀ i, c i = 1 ∨ c i = -1) ∧ ∏ i, c i = 1 ∧ ∀ i, a (dBasis m i) = c i • dBasis m (σ i)}
  mul_mem' := by
    intro a₁ a₂ ha₁ ha₂
    rcases ha₁ with ⟨σ₁, c₁, hc₁, hprod₁, hact₁⟩
    rcases ha₂ with ⟨σ₂, c₂, hc₂, hprod₂, hact₂⟩
    refine ⟨σ₁ * σ₂, fun i => c₂ i * c₁ (σ₂ i), ?_, ?_, ?_⟩
    · intro i
      change c₂ i * c₁ (σ₂ i) = 1 ∨ c₂ i * c₁ (σ₂ i) = -1
      rcases hc₂ i with h | h <;> rcases hc₁ (σ₂ i) with h' | h' <;> rw [h, h'] <;> decide
    · rw [Finset.prod_mul_distrib, hprod₂, Equiv.prod_comp σ₂ c₁, hprod₁]
      simp
    · intro i
      rw [LinearEquiv.mul_apply, hact₂ i, map_smul, hact₁ (σ₂ i), smul_smul]
      rfl
  one_mem' := by
    refine ⟨1, fun _ => 1, ?_, ?_, ?_⟩
    · intro i; left; rfl
    · simp
    · intro i; simp
  inv_mem' := by
    intro a ha
    rcases ha with ⟨σ, c, hc, hprod, hact⟩
    refine ⟨σ⁻¹, fun j => c (σ⁻¹ j), ?_, ?_, ?_⟩
    · intro j; exact hc (σ⁻¹ j)
    · rw [Equiv.prod_comp σ⁻¹ c]; exact hprod
    · intro j
      have h1 : a (c (σ⁻¹ j) • dBasis m (σ⁻¹ j)) = dBasis m j := by
        rw [map_smul, hact (σ⁻¹ j), smul_smul, plh_sq_unit (hc (σ⁻¹ j))]
        simp
      have h2 : a.symm (dBasis m j) = c (σ⁻¹ j) • dBasis m (σ⁻¹ j) := by
        rw [← h1, LinearEquiv.symm_apply_apply]
      simpa using h2

theorem dPerm_mem_dEven (m : ℕ) (σ : Equiv.Perm (Fin m)) : dPerm m σ ∈ dEven m := by
  refine ⟨σ, fun _ => 1, ?_, ?_, ?_⟩
  · intro i; left; rfl
  · simp
  · intro i
    rw [dPerm_apply m σ i]
    simp

theorem dTau_mem_dEven (m : ℕ) (ε : Bool) {a b : Fin m} (hab : a ≠ b) :
    dTau m ε a b ∈ dEven m := by
  cases ε
  · refine ⟨Equiv.swap a b, fun _ => 1, ?_, ?_, ?_⟩
    · intro i; left; rfl
    · simp
    · intro i; rw [plh_dTau_action m false hab i]; simp
  · refine ⟨Equiv.swap a b, fun i => if i = a ∨ i = b then (-1 : ZMod 3) else 1, ?_, ?_, ?_⟩
    · intro i; by_cases h : i = a ∨ i = b <;> simp [h]
    · exact plh_prod_sign_pair m hab
    · intro i; rw [plh_dTau_action m true hab i]; simp

@[expose] def IsDEquiv (m : ℕ) (e : (ggCoxeterMatrixD m).Group ≃* dEven m) : Prop :=
  ∀ t : Fin m, ((e ((ggCoxeterMatrixD m).simple t) : dEven m) : DVec m ≃ₗ[ZMod 3] DVec m) =
    dTau m (decide (t.val + 1 = m)) (OrthTorus.simpleLo t) (OrthTorus.simpleHi t)

theorem dEven_equiv {m : ℕ} (hm : 4 ≤ m) :
    ∃ e : (ggCoxeterMatrixD m).Group ≃* dEven m, IsDEquiv m e := by
  haveI : Fact (Nat.Prime 3) := Nat.fact_prime_three
  obtain ⟨e, he⟩ := ggRC_coxeterD_equiv_evenSigned (p := 3) (by decide) hm (dBasis m) (dEven m)
    (fun a => Iff.rfl)
  refine ⟨e, fun t => ?_⟩
  rw [he t]
  by_cases ht : t.val + 1 = m
  · have hlast : t.val = m - 1 := by omega
    have hlo : OrthTorus.simpleLo t = (⟨m - 2, by omega⟩ : Fin m) :=
      Fin.ext (by simp [OrthTorus.simpleLo_of_last ht])
    have hhi : OrthTorus.simpleHi t = (⟨m - 1, by omega⟩ : Fin m) :=
      Fin.ext (by simp [OrthTorus.simpleHi_of_last ht])
    rw [dif_pos hlast, hlo, hhi]
    have hdec : decide (t.val + 1 = m) = true := by simp [ht]
    rw [hdec]
    rfl
  · have hlast : ¬ t.val = m - 1 := by omega
    have hlt : t.val + 1 < m := by have := t.isLt; omega
    have hlo : OrthTorus.simpleLo t = t := Fin.ext (by simp [OrthTorus.simpleLo_of_lt hlt])
    have hhi : OrthTorus.simpleHi t = (⟨t.val + 1, hlt⟩ : Fin m) :=
      Fin.ext (by simp [OrthTorus.simpleHi_of_lt hlt])
    rw [dif_neg hlast, hlo, hhi]
    have hdec : decide (t.val + 1 = m) = false := by simp [ht]
    rw [hdec]
    rfl

end CFSG.StandardType.QTwo

end
