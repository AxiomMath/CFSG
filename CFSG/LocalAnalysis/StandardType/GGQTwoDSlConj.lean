module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDCoxEven

public section

namespace CFSG.StandardType.QTwo

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Sl

theorem dBasis_apply (m : ℕ) (j i : Fin m) : dBasis m j i = if i = j then 1 else 0 := by
  simp [dBasis, Pi.single_apply]

@[expose] def sg (ε : Bool) : ZMod 3 := if ε then -1 else 1

theorem sg_cases (ε : Bool) : sg ε = 1 ∨ sg ε = -1 := by
  cases ε <;> simp [sg]

theorem sg_mul_self (ε : Bool) : sg ε * sg ε = 1 := by
  cases ε <;> decide

theorem sign_prod_cases {x y z : ZMod 3} (hx : x = 1 ∨ x = -1) (hy : y = 1 ∨ y = -1)
    (hz : z = 1 ∨ z = -1) : x * y * z = 1 ∨ x * y * z = -1 := by
  rcases hx with h | h <;> rcases hy with h' | h' <;> rcases hz with h'' | h'' <;>
    rw [h, h', h''] <;> decide

theorem dTau_basis (m : ℕ) (ε : Bool) {a b : Fin m} (hab : a ≠ b) (i : Fin m) :
    dTau m ε a b (dBasis m i) =
      (if i = a ∨ i = b then sg ε else 1) • dBasis m (Equiv.swap a b i) := by
  by_cases hia : i = a
  · rw [hia, dTau_apply_left m ε hab]
    simp [sg, Equiv.swap_apply_left]
  · by_cases hib : i = b
    · rw [hib, dTau_apply_right m ε hab]
      simp [sg, Equiv.swap_apply_right]
    · rw [dTau_apply_of_ne m ε hia hib]
      simp [hia, hib, Equiv.swap_apply_of_ne_of_ne hia hib]

theorem mul_dTau (m : ℕ) {U : DVec m ≃ₗ[ZMod 3] DVec m} {σ : Equiv.Perm (Fin m)}
    {c : Fin m → ZMod 3} (hc : ∀ i, c i = 1 ∨ c i = -1)
    (hU : ∀ i, U (dBasis m i) = c i • dBasis m (σ i)) {a b : Fin m} (hab : a ≠ b)
    (ε ε' : Bool) (hε : sg ε' = c a * c b * sg ε) :
    U * dTau m ε a b * U⁻¹ = dTau m ε' (σ a) (σ b) := by
  have hσab : σ a ≠ σ b := fun h => hab (σ.injective h)
  have hsq : ∀ i, c i * c i = 1 := fun i => by rcases hc i with h | h <;> rw [h] <;> decide
  rw [mul_inv_eq_iff_eq_mul]
  refine (dBasis m).ext' fun k => ?_
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  by_cases hka : k = a
  · rw [hka, dTau_apply_left m ε hab, map_smul, hU b, hU a, map_smul,
      dTau_apply_left m ε' hσab, smul_smul, smul_smul]
    congr 1
    change sg ε * c b = c a * sg ε'
    rw [hε]
    linear_combination (-(sg ε * c b)) * hsq a
  · by_cases hkb : k = b
    · rw [hkb, dTau_apply_right m ε hab, map_smul, hU a, hU b, map_smul,
        dTau_apply_right m ε' hσab, smul_smul, smul_smul]
      congr 1
      change sg ε * c a = c b * sg ε'
      rw [hε]
      linear_combination (-(sg ε * c a)) * hsq b
    · rw [dTau_apply_of_ne m ε hka hkb, hU k, map_smul,
        dTau_apply_of_ne m ε' (fun h => hka (σ.injective h)) (fun h => hkb (σ.injective h))]

theorem conj_dTau_exists (m : ℕ) {U : DVec m ≃ₗ[ZMod 3] DVec m} (hU : U ∈ dEven m) (ε : Bool)
    {a b : Fin m} (hab : a ≠ b) :
    ∃ (ε' : Bool) (a' b' : Fin m), a' ≠ b' ∧ U * dTau m ε a b * U⁻¹ = dTau m ε' a' b' := by
  obtain ⟨σ, c, hc, -, hact⟩ := hU
  have hp := sign_prod_cases (hc a) (hc b) (sg_cases ε)
  have hε : ∃ ε' : Bool, sg ε' = c a * c b * sg ε := by
    rcases hp with hp | hp
    · exact ⟨false, by rw [hp]; simp [sg]⟩
    · exact ⟨true, by rw [hp]; simp [sg]⟩
  obtain ⟨ε', hε'⟩ := hε
  exact ⟨ε', σ a, σ b, fun h => hab (σ.injective h), mul_dTau m hc hact hab ε ε' hε'⟩

private theorem qsl_sign_fun_cases (m : ℕ) (ε : Bool) (a b i : Fin m) :
    (if i = a ∨ i = b then sg ε else 1) = 1 ∨ (if i = a ∨ i = b then sg ε else 1) = -1 := by
  by_cases h : i = a ∨ i = b
  · rw [if_pos h]; exact sg_cases ε
  · rw [if_neg h]; exact Or.inl rfl

theorem comm_of_disjoint (m : ℕ) (ε ε' : Bool) {a b c d : Fin m} (hab : a ≠ b) (hcd : c ≠ d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    dTau m ε a b * dTau m ε' c d = dTau m ε' c d * dTau m ε a b := by
  have hca : ¬ (c = a ∨ c = b) := by
    rintro (h | h)
    · exact hac h.symm
    · exact hbc h.symm
  have hda : ¬ (d = a ∨ d = b) := by
    rintro (h | h)
    · exact had h.symm
    · exact hbd h.symm
  have h := mul_dTau m (U := dTau m ε a b) (σ := Equiv.swap a b)
    (c := fun i => if i = a ∨ i = b then sg ε else 1) (qsl_sign_fun_cases m ε a b)
    (dTau_basis m ε hab) hcd ε' ε' (by simp only [if_neg hca, if_neg hda]; simp)
  rw [Equiv.swap_apply_of_ne_of_ne (fun h => hca (Or.inl h)) (fun h => hca (Or.inr h)),
    Equiv.swap_apply_of_ne_of_ne (fun h => hda (Or.inl h)) (fun h => hda (Or.inr h))] at h
  exact mul_inv_eq_iff_eq_mul.1 h

theorem comm_of_same (m : ℕ) (ε ε' : Bool) {a b : Fin m} (hab : a ≠ b) :
    dTau m ε a b * dTau m ε' a b = dTau m ε' a b * dTau m ε a b := by
  have h := mul_dTau m (U := dTau m ε a b) (σ := Equiv.swap a b)
    (c := fun i => if i = a ∨ i = b then sg ε else 1) (qsl_sign_fun_cases m ε a b)
    (dTau_basis m ε hab) hab ε' ε' (by simp [hab.symm, sg_mul_self])
  rw [Equiv.swap_apply_left, Equiv.swap_apply_right, dTau_symm m ε' b a] at h
  exact mul_inv_eq_iff_eq_mul.1 h

theorem dSign_conj (m : ℕ) {p q a b : Fin m} (hab : a ≠ b) (ε ε' : Bool)
    (hε : sg ε' = (if a = p ∨ a = q then (-1 : ZMod 3) else 1) *
      (if b = p ∨ b = q then (-1 : ZMod 3) else 1) * sg ε) :
    dSign m p q * dTau m ε a b * (dSign m p q)⁻¹ = dTau m ε' a b := by
  have h := mul_dTau m (U := dSign m p q) (σ := 1)
    (c := fun i => if i = p ∨ i = q then (-1 : ZMod 3) else 1)
    (fun i => by by_cases h : i = p ∨ i = q <;> simp [h]) (fun i => by
      rw [dSign_apply]; rfl) hab ε ε' hε
  exact h

theorem dSign_mem_dEven (m : ℕ) {a b : Fin m} (hab : a ≠ b) : dSign m a b ∈ dEven m := by
  have h := (dEven m).mul_mem ((dEven m).inv_mem (dPerm_mem_dEven m (Equiv.swap a b)))
    (dTau_mem_dEven m true hab)
  have hdt : (dPerm m (Equiv.swap a b))⁻¹ * dTau m true a b = dSign m a b := by
    simp [dTau]
  rwa [hdt] at h

theorem dSign_diag (m : ℕ) (p q k : Fin m) :
    ∃ κ : ZMod 3, (κ = 1 ∨ κ = -1) ∧ dSign m p q (dBasis m k) = κ • dBasis m k := by
  rw [dSign_apply]
  by_cases h : k = p ∨ k = q
  · exact ⟨-1, Or.inr rfl, by rw [if_pos h]⟩
  · exact ⟨1, Or.inl rfl, by rw [if_neg h]⟩

theorem exists_conj_pair (m : ℕ) {p₀ p₁ p₂ p₃ : Fin m} (h01 : p₀ ≠ p₁) (h02 : p₀ ≠ p₂)
    (h03 : p₀ ≠ p₃) (h12 : p₁ ≠ p₂) (h13 : p₁ ≠ p₃) (h23 : p₂ ≠ p₃) (ε₁ ε₂ : Bool) :
    ∃ D ∈ dEven m, (∀ k, ∃ κ : ZMod 3, (κ = 1 ∨ κ = -1) ∧ D (dBasis m k) = κ • dBasis m k) ∧
      D * dTau m false p₀ p₁ * D⁻¹ = dTau m ε₁ p₀ p₁ ∧
      D * dTau m false p₁ p₂ * D⁻¹ = dTau m ε₂ p₁ p₂ := by
  cases ε₁ <;> cases ε₂
  · exact ⟨1, (dEven m).one_mem, fun k => ⟨1, Or.inl rfl, by simp⟩, by simp, by simp⟩
  · refine ⟨dSign m p₂ p₃, dSign_mem_dEven m h23, dSign_diag m p₂ p₃, ?_, ?_⟩
    · exact dSign_conj m h01 false false
        (by simp [sg, h02, h03, h12, h13, h02.symm, h03.symm, h12.symm, h13.symm])
    · exact dSign_conj m h12 false true
        (by simp [sg, h02, h03, h12, h13, h02.symm, h03.symm, h12.symm, h13.symm])
  · refine ⟨dSign m p₀ p₃, dSign_mem_dEven m h03, dSign_diag m p₀ p₃, ?_, ?_⟩
    · exact dSign_conj m h01 false true
        (by simp [sg, h01, h03, h12, h13, h01.symm, h03.symm, h12.symm, h13.symm])
    · exact dSign_conj m h12 false false
        (by simp [sg, h01, h02, h03, h12, h13, h23, h01.symm, h02.symm, h03.symm, h12.symm,
          h13.symm, h23.symm])
  · refine ⟨dSign m p₀ p₂, dSign_mem_dEven m h02, dSign_diag m p₀ p₂, ?_, ?_⟩
    · exact dSign_conj m h01 false true
        (by simp [sg, h01, h02, h12, h01.symm, h02.symm, h12.symm])
    · exact dSign_conj m h12 false true
        (by simp [sg, h01, h02, h12, h01.symm, h02.symm, h12.symm])

theorem perm_mul_conj_dTau (m : ℕ) (π : Equiv.Perm (Fin m)) {D : DVec m ≃ₗ[ZMod 3] DVec m}
    {p q : Fin m} {ε ε' : Bool} (hD : D * dTau m ε p q * D⁻¹ = dTau m ε' p q) :
    (dPerm m π * D) * dTau m ε p q * (dPerm m π * D)⁻¹ = dTau m ε' (π p) (π q) := by
  rw [mul_inv_rev, ← dPerm_conj_dTau, ← hD]
  simp only [mul_assoc]

theorem exists_conj_pair_fix (m : ℕ) {p₀ p₁ p₂ p₃ y x z c : Fin m} (h01 : p₀ ≠ p₁)
    (h02 : p₀ ≠ p₂) (h03 : p₀ ≠ p₃) (h12 : p₁ ≠ p₂) (h13 : p₁ ≠ p₃) (h23 : p₂ ≠ p₃)
    (hyx : y ≠ x) (hxz : x ≠ z) (hyz : y ≠ z) (hc0 : c ≠ p₀) (hc1 : c ≠ p₁) (hc2 : c ≠ p₂)
    (hcy : c ≠ y) (hcx : c ≠ x) (hcz : c ≠ z) (ε₁ ε₂ : Bool) :
    ∃ U ∈ dEven m, (∃ κ : ZMod 3, (κ = 1 ∨ κ = -1) ∧ U (dBasis m c) = κ • dBasis m c) ∧
      U * dTau m false p₀ p₁ * U⁻¹ = dTau m ε₁ y x ∧
      U * dTau m false p₁ p₂ * U⁻¹ = dTau m ε₂ x z := by
  obtain ⟨D, hD, hDdiag, hD1, hD2⟩ := exists_conj_pair m h01 h02 h03 h12 h13 h23 ε₁ ε₂
  have hf : Function.Injective ![p₀, p₁, p₂, c] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Ne.symm]
  have hg : Function.Injective ![y, x, z, c] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Ne.symm]
  obtain ⟨π, hπ⟩ := Equiv.Perm.exists_extending_pair _ _ hf hg
  have hπ0 : π p₀ = y := by simpa using hπ 0
  have hπ1 : π p₁ = x := by simpa using hπ 1
  have hπ2 : π p₂ = z := by simpa using hπ 2
  have hπc : π c = c := by simpa using hπ 3
  refine ⟨dPerm m π * D, (dEven m).mul_mem (dPerm_mem_dEven m π) hD, ?_, ?_, ?_⟩
  · obtain ⟨κ, hκ, hDκ⟩ := hDdiag c
    exact ⟨κ, hκ, by rw [LinearEquiv.mul_apply, hDκ, map_smul, dPerm_apply, hπc]⟩
  · rw [perm_mul_conj_dTau m π hD1, hπ0, hπ1]
  · rw [perm_mul_conj_dTau m π hD2, hπ1, hπ2]

end Sl

end CFSG.StandardType.QTwo

end
