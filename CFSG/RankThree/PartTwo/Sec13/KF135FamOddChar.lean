module

public import CFSG.RankThree.Classical.SteinbergBJCharacterSpaces

public section

namespace CFSG.RankThree.PartTwo.Sec13.KF135Proof.FamOdd

open Module CFSG.RankThree.Classical

section Transport

variable {F : Type*} [Field F] {M : Type*} [AddCommGroup M] [Module F M]
variable {Γ : Type*} [Group Γ] {p : ℕ} [NeZero p]
variable {ρ ρ' : Γ →* Module.End F M} {ζ : F}

theorem finrank_charSpace_nsmul₂ (hζ : ζ ^ p = 1) (σ : F ≃+* F) (Φ : M ≃+ M)
    (hΦ : ∀ (c : F) (v : M), Φ (c • v) = σ c • Φ v) (hρ : ∀ g v, Φ (ρ g v) = ρ' g (Φ v))
    (n : ℕ) (hσ : σ ζ = ζ ^ n) (χ : Additive Γ →+ ZMod p) :
    finrank F (charSpace ρ' ζ (n • χ)) = finrank F (charSpace ρ ζ χ) := by
  have hpow : ∀ a : ZMod p, σ (ζ ^ a.val) = ζ ^ (n • a).val := fun a => by
    rw [map_pow, hσ, root_pow_val_nsmul hζ, ← pow_mul, ← pow_mul, mul_comm]
  have hΦ' : ∀ (c : F) (w : M), Φ.symm (c • w) = σ.symm c • Φ.symm w := fun c w => by
    apply Φ.injective
    rw [hΦ, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  have hρ' : ∀ g w, Φ.symm (ρ' g w) = ρ g (Φ.symm w) := fun g w => by
    apply Φ.injective
    rw [hρ, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  have h1 : ∀ v ∈ charSpace ρ ζ χ, Φ v ∈ charSpace ρ' ζ (n • χ) := by
    intro v hv
    rw [mem_charSpace] at hv ⊢
    intro g
    rw [← hρ, hv g, hΦ, hpow, AddMonoidHom.nsmul_apply]
  have h2 : ∀ w ∈ charSpace ρ' ζ (n • χ), Φ.symm w ∈ charSpace ρ ζ χ := by
    intro w hw
    rw [mem_charSpace] at hw ⊢
    intro g
    rw [← hρ', hw g, hΦ', AddMonoidHom.nsmul_apply, ← hpow, RingEquiv.symm_apply_apply]
  let j : charSpace ρ ζ χ ≃+ charSpace ρ' ζ (n • χ) :=
    { toFun := fun v => ⟨Φ v, h1 v v.2⟩
      invFun := fun w => ⟨Φ.symm w, h2 w w.2⟩
      left_inv := fun v => Subtype.ext (Φ.symm_apply_apply v)
      right_inv := fun w => Subtype.ext (Φ.apply_symm_apply w)
      map_add' := fun v v' => Subtype.ext (map_add Φ (v : M) v') }
  have := rank_eq_of_equiv_equiv σ j σ.bijective fun c v => Subtype.ext (hΦ c v)
  unfold Module.finrank
  rw [this]

theorem apply_eq_zero_of_mem_charSpace₂ (hζ : IsPrimitiveRoot ζ p)
    (B : LinearMap.BilinForm F M) (hB : ∀ g v w, B (ρ' g v) (ρ g w) = B v w)
    {χ ψ : Additive Γ →+ ZMod p} (h : χ + ψ ≠ 0) {v w : M} (hv : v ∈ charSpace ρ' ζ χ)
    (hw : w ∈ charSpace ρ ζ ψ) : B v w = 0 := by
  obtain ⟨g, hg⟩ : ∃ g : Γ, (χ + ψ) (Additive.ofMul g) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact h (AddMonoidHom.ext fun x => hcon (Additive.toMul x))
  have h1 : ζ ^ ((χ + ψ) (Additive.ofMul g)).val ≠ 1 := fun h1 =>
    hg ((root_pow_val_eq_one_iff hζ _).mp h1)
  have key : B v w = ζ ^ ((χ + ψ) (Additive.ofMul g)).val * B v w := by
    conv_lhs => rw [← hB g v w, (mem_charSpace.mp hv) g, (mem_charSpace.mp hw) g]
    rw [LinearMap.map_smul₂, LinearMap.map_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
      ← root_pow_val_add hζ.pow_eq_one, AddMonoidHom.add_apply]
  have : (ζ ^ ((χ + ψ) (Additive.ofMul g)).val - 1) * B v w = 0 := by
    rw [sub_mul, ← key, one_mul, sub_self]
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr h1)

end Transport

section Pairing

variable {F : Type*} [Field F] {M : Type*} [AddCommGroup M] [Module F M]
variable {Γ : Type*} [CommGroup Γ] [Fintype Γ] {p : ℕ} [NeZero p]
variable {ρ ρ' : Γ →* Module.End F M} {ζ : F}

theorem finrank_charSpace_le_neg₂ [FiniteDimensional F M] [Fintype (Additive Γ →+ ZMod p)]
    (hp : p.Prime) (hζ : IsPrimitiveRoot ζ p) (hexp : ∀ g : Γ, g ^ p = 1)
    (hΓ : (Fintype.card Γ : F) ≠ 0) (B : LinearMap.BilinForm F M)
    (hB : ∀ g v w, B (ρ' g v) (ρ g w) = B v w) (hBnd : ∀ v, (∀ w, B v w = 0) → v = 0)
    (χ : Additive Γ →+ ZMod p) :
    finrank F (charSpace ρ' ζ χ) ≤ finrank F (charSpace ρ ζ (-χ)) := by
  let f : charSpace ρ' ζ χ →ₗ[F] Module.Dual F (charSpace ρ ζ (-χ)) := B.domRestrict₁₂ _ _
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    apply Subtype.ext
    apply hBnd
    intro w
    rw [eq_sum_charIdem_apply (ρ := ρ) hp hζ hexp hΓ w, map_sum, Finset.sum_eq_single (-χ)]
    · exact LinearMap.congr_fun hv ⟨_, charIdem_apply_mem hζ.pow_eq_one _ w⟩
    · intro ψ _ hψ
      refine apply_eq_zero_of_mem_charSpace₂ hζ B hB (fun h => hψ ?_) v.2
        (charIdem_apply_mem hζ.pow_eq_one ψ w)
      exact eq_neg_of_add_eq_zero_right h
    · simp
  calc finrank F (charSpace ρ' ζ χ) ≤ finrank F (Module.Dual F (charSpace ρ ζ (-χ))) :=
        LinearMap.finrank_le_finrank_of_injective hf
    _ = finrank F (charSpace ρ ζ (-χ)) := Subspace.dual_finrank_eq

end Pairing

end CFSG.RankThree.PartTwo.Sec13.KF135Proof.FamOdd
