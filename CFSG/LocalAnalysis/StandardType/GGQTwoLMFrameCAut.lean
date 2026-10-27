module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMMod
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUCoord

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open CFSG.StandardType.UCoord

theorem qTwoLMFrameC_aut_form {m : ℕ} (hm4 : 4 ≤ m) (h3 : ¬ 3 ∣ m) {VT : Type} [Group VT]
    {ρ : Equiv.Perm (Fin m) →* MulAut VT} (hVT : IsAugModel m VT ρ) {ψ : MulAut VT}
    (hψ : ∀ σ : Equiv.Perm (Fin m), ∃ σ' : Equiv.Perm (Fin m), ψ * ρ σ * ψ⁻¹ = ρ σ') :
    ∃ π : Equiv.Perm (Fin m), (∀ v, ψ v = ρ π v) ∨ ∀ v, ψ v = (ρ π v)⁻¹ := by
  obtain ⟨e, he⟩ := hVT.ex
  have hm2 : 2 ≤ m := by omega
  let φ : MulAut ↥(sumZero m 3) := MulAut.congr (e.symm) ψ
  have hcongr : ∀ σ : Equiv.Perm (Fin m), MulAut.congr (e.symm) (ρ σ) = permAutV σ := by
    intro σ
    refine MulEquiv.ext fun f => ?_
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_symm, ← he σ f, MulEquiv.symm_apply_apply]
  have hφ : ∀ σ : Equiv.Perm (Fin m), ∃ τ, φ * permAutV σ * φ⁻¹ = permAutV τ := by
    intro σ
    obtain ⟨σ', hσ'⟩ := hψ σ
    refine ⟨σ', ?_⟩
    have h1 := congrArg (fun g : MulAut VT => MulAut.congr (e.symm) g) hσ'
    rw [map_mul, map_mul, map_inv, hcongr σ, hcongr σ'] at h1
    exact h1
  obtain ⟨π, hπ⟩ :=
    exists_eq_conj_of_normalizes (d := m) (p := 3) Nat.prime_three (by norm_num) hm4 hφ
  let φ' : MulAut ↥(sumZero m 3) := (permAutV π)⁻¹ * φ
  have hcomm : ∀ σ : Equiv.Perm (Fin m), φ' * permAutV σ * φ'⁻¹ = permAutV σ := by
    intro σ
    have h1 : (permAutV π)⁻¹ * (φ * permAutV σ * φ⁻¹) * permAutV π = permAutV σ := by
      rw [hπ σ, permAutV_mul, permAutV_mul]
      rw [← permAutVHom_apply π⁻¹, map_inv, permAutVHom_apply]
      group
    calc φ' * permAutV σ * φ'⁻¹
        = (permAutV π)⁻¹ * (φ * permAutV σ * φ⁻¹) * permAutV π := by
            dsimp only [φ']
            rw [mul_inv_rev, inv_inv]
            group
      _ = permAutV σ := h1
  have hcomm2 : ∀ σ : Equiv.Perm (Fin m), φ' * permAutV σ = permAutV σ * φ' := by
    intro σ
    exact mul_inv_eq_iff_eq_mul.mp (hcomm σ)
  have hF : ∀ (σ : Equiv.Perm (Fin m)) (f : ↥(sumZero m 3)),
      φ' (permAutV σ f) = permAutV σ (φ' f) := by
    intro σ f
    have h1 := congrArg (fun g : MulAut ↥(sumZero m 3) => g f) (hcomm2 σ)
    simpa only [MulAut.mul_apply] using h1
  obtain ⟨c, hc⟩ := exists_pow_of_commute_permAutV (d := m) (p := 3) Nat.prime_three
    (by norm_num) hm2 h3 φ'.toMonoidHom hF
  have hc' : ∀ f : ↥(sumZero m 3), φ' f = f ^ c := fun f => hc f
  let i0 : Fin m := ⟨0, by omega⟩
  let i1 : Fin m := ⟨1, by omega⟩
  have hi01 : i0 ≠ i1 := by
    intro h
    exact Nat.zero_ne_one (by simpa [i0, i1] using congrArg Fin.val h)
  have hne_one : (rootV i0 i1 : ↥(sumZero m 3)) ≠ 1 := by
    intro h
    have h2 := congrArg (fun f => crd f i0) h
    rw [crd_rootV_left hi01, crd_one] at h2
    exact one_ne_zero h2
  have hc3 : c % 3 = 1 ∨ c % 3 = 2 := by
    have hlt : c % 3 < 3 := Nat.mod_lt c (by norm_num)
    interval_cases hc0 : c % 3
    · exfalso
      have h1 : φ' (rootV i0 i1 : ↥(sumZero m 3)) = 1 := by
        rw [hc', pow_eq_pow_mod c (pow_p_eq_one (rootV i0 i1)), hc0, pow_zero]
      exact hne_one (φ'.injective (by rw [h1, map_one]))
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hφψ : ∀ f : ↥(sumZero m 3), ψ (e f) = e (φ f) := by
    intro f
    have h1 : φ f = e.symm (ψ (e f)) := by
      dsimp only [φ]
      simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_symm]
    rw [h1, MulEquiv.apply_symm_apply]
  have hv : ∀ v : VT, ψ v = e (φ (e.symm v)) := by
    intro v
    have h1 := hφψ (e.symm v)
    rwa [MulEquiv.apply_symm_apply] at h1
  have hφ_eq : φ = permAutV π * φ' := by
    dsimp only [φ']
    group
  refine ⟨π, ?_⟩
  rcases hc3 with hmod | hmod
  · left
    intro v
    have hfix : φ' (e.symm v) = e.symm v := by
      rw [hc', pow_eq_pow_mod c (pow_p_eq_one (e.symm v)), hmod, pow_one]
    calc ψ v = e (φ (e.symm v)) := hv v
      _ = e (permAutV π (e.symm v)) := by rw [hφ_eq, MulAut.mul_apply, hfix]
      _ = ρ π v := by rw [he π (e.symm v), MulEquiv.apply_symm_apply]
  · right
    intro v
    have hfix : φ' (e.symm v) = (e.symm v)⁻¹ := by
      rw [hc', pow_eq_pow_mod c (pow_p_eq_one (e.symm v)), hmod]
      exact mul_eq_one_iff_eq_inv.mp (by rw [← pow_succ, pow_p_eq_one])
    calc ψ v = e (φ (e.symm v)) := hv v
      _ = e ((permAutV π (e.symm v))⁻¹) := by
            rw [hφ_eq, MulAut.mul_apply, hfix, map_inv]
      _ = (e (permAutV π (e.symm v)))⁻¹ := by rw [map_inv]
      _ = (ρ π v)⁻¹ := by rw [he π (e.symm v), MulEquiv.apply_symm_apply]

theorem qTwoLMFrameC_perm_faithful {m : ℕ} {VT : Type} [Group VT]
    {ρ : Equiv.Perm (Fin m) →* MulAut VT} (hVT : IsAugModel m VT ρ) {σ : Equiv.Perm (Fin m)}
    (h : ∀ v, ρ σ v = v) : σ = 1 := by
  obtain ⟨e, he⟩ := hVT.ex
  apply permAutV_injective (d := m) (p := 3) Nat.prime_three (by norm_num)
  refine MulEquiv.ext fun f => ?_
  apply e.injective
  rw [he σ f, h (e f), he 1 f, map_one, MulAut.one_apply]

end CFSG.StandardType.QTwo

end
