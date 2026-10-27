module

public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import Mathlib.LinearAlgebra.Eigenspace.Basic

public section

namespace CFSG.RankThree.Classical

open Module

section Values

variable {F : Type*} [Field F] {p : ℕ} [NeZero p] {ζ : F}

theorem root_pow_val_add (hζ : ζ ^ p = 1) (a b : ZMod p) :
    ζ ^ (a + b).val = ζ ^ a.val * ζ ^ b.val :=
  AddChar.map_add_eq_mul (AddChar.zmodChar p hζ) a b

theorem root_pow_val_neg_mul (hζ : ζ ^ p = 1) (a : ZMod p) :
    ζ ^ (-a).val * ζ ^ a.val = 1 := by
  rw [← root_pow_val_add hζ]
  simp

theorem root_pow_val_nsmul (hζ : ζ ^ p = 1) (n : ℕ) (a : ZMod p) :
    ζ ^ (n • a).val = (ζ ^ a.val) ^ n :=
  AddChar.map_nsmul_eq_pow (AddChar.zmodChar p hζ) n a

theorem root_pow_val_eq_one_iff (hζ : IsPrimitiveRoot ζ p) (a : ZMod p) :
    ζ ^ a.val = 1 ↔ a = 0 :=
  (AddChar.zmodChar_primitive_of_primitive_root p hζ).zmod_char_eq_one_iff p a

theorem sum_pow_val_char_eq_zero {Γ : Type*} [Group Γ] [Fintype Γ] (hζ : IsPrimitiveRoot ζ p)
    {χ : Additive Γ →+ ZMod p} (hχ : χ ≠ 0) :
    ∑ g : Γ, ζ ^ (χ (Additive.ofMul g)).val = 0 := by
  obtain ⟨h, hh⟩ : ∃ h : Γ, χ (Additive.ofMul h) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hχ (AddMonoidHom.ext fun x => hcon (Additive.toMul x))
  have h1 : ζ ^ (χ (Additive.ofMul h)).val ≠ 1 := fun h1 =>
    hh ((root_pow_val_eq_one_iff hζ _).mp h1)
  have key : ζ ^ (χ (Additive.ofMul h)).val * ∑ g : Γ, ζ ^ (χ (Additive.ofMul g)).val =
      ∑ g : Γ, ζ ^ (χ (Additive.ofMul g)).val := by
    rw [Finset.mul_sum]
    exact Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g => by
      rw [Equiv.coe_mulLeft, ofMul_mul, map_add, root_pow_val_add hζ.pow_eq_one]
  have : (ζ ^ (χ (Additive.ofMul h)).val - 1) * ∑ g : Γ, ζ ^ (χ (Additive.ofMul g)).val = 0 := by
    rw [sub_mul, key, one_mul, sub_self]
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr h1)

end Values

section Duality

variable {p : ℕ}

theorem natCard_addMonoidHom_zmod {D : Type*} [AddCommGroup D] [Finite D] (hp : p.Prime)
    (hD : ∀ x : D, p • x = 0) : Nat.card (D →+ ZMod p) = Nat.card D := by
  have : Module (ZMod p) D := AddCommGroup.zmodModule hD
  have h1 : Nat.card (D →+ ZMod p) = Nat.card (D →ₗ[ZMod p] ZMod p) :=
    Nat.card_congr ⟨AddMonoidHom.toZModLinearMap p, fun f => f.toAddMonoidHom, fun _ => rfl,
      fun _ => rfl⟩
  have : Fact p.Prime := ⟨hp⟩
  have : Module.Finite (ZMod p) D := Module.Finite.of_finite
  let b := Module.finBasis (ZMod p) D
  rw [h1, ← Nat.card_congr (b.constr ℕ).toEquiv, Nat.card_fun, Nat.card_fin,
    ← Module.natCard_eq_pow_finrank (K := ZMod p) (V := D)]

theorem finrank_zmod_eq_of_natCard {D : Type*} [AddCommGroup D] [Module (ZMod p) D] [Finite D]
    (hp : p.Prime) {k : ℕ} (hD : Nat.card D = p ^ k) : finrank (ZMod p) D = k := by
  have : Fact p.Prime := ⟨hp⟩
  have : Module.Finite (ZMod p) D := Module.Finite.of_finite
  rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod] at hD
  exact Nat.pow_right_injective hp.two_le hD

theorem span_zmod_eq_top_of_closure_eq_top {D : Type*} [AddCommGroup D] [Module (ZMod p) D]
    {S : Set D} (h : AddSubgroup.closure S = ⊤) : Submodule.span (ZMod p) S = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ AddSubgroup.closure S := h ▸ AddSubgroup.mem_top x
  exact (AddSubgroup.closure_le (Submodule.span (ZMod p) S).toAddSubgroup).mpr
    Submodule.subset_span hx

variable {Γ : Type*} [CommGroup Γ]

theorem nsmul_ofMul_eq_zero_of_pow (hexp : ∀ g : Γ, g ^ p = 1) (x : Additive Γ) : p • x = 0 := by
  rw [← ofMul_toMul x, ← ofMul_pow, hexp, ofMul_one]

theorem natCard_char [Finite Γ] (hp : p.Prime) (hexp : ∀ g : Γ, g ^ p = 1) :
    Nat.card (Additive Γ →+ ZMod p) = Nat.card Γ :=
  (natCard_addMonoidHom_zmod hp (nsmul_ofMul_eq_zero_of_pow hexp)).trans
    (Nat.card_congr Additive.toMul)

theorem exists_char_apply_ne_zero [Finite Γ] (hp : p.Prime) (hexp : ∀ g : Γ, g ^ p = 1) {g : Γ}
    (hg : g ≠ 1) : ∃ χ : Additive Γ →+ ZMod p, χ (Additive.ofMul g) ≠ 0 := by
  have : Module (ZMod p) (Additive Γ) :=
    AddCommGroup.zmodModule (nsmul_ofMul_eq_zero_of_pow hexp)
  have : Fact p.Prime := ⟨hp⟩
  have : Module.Finite (ZMod p) (Additive Γ) := Module.Finite.of_finite
  have hne : Additive.ofMul g ≠ 0 := by
    rwa [Ne, ← ofMul_one, Additive.ofMul.apply_eq_iff_eq]
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual (ZMod p) (Additive Γ), φ (Additive.ofMul g) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hne ((Module.forall_dual_apply_eq_zero_iff (ZMod p) _).mp hcon)
  exact ⟨φ.toAddMonoidHom, hφ⟩

theorem exists_ne_one_of_closure_ne_top [Finite Γ] (hp : p.Prime) (hexp : ∀ g : Γ, g ^ p = 1)
    {S : Set (Additive Γ →+ ZMod p)} (hS : AddSubgroup.closure S ≠ ⊤) :
    ∃ g : Γ, g ≠ 1 ∧ ∀ χ ∈ S, χ (Additive.ofMul g) = 0 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Finite (Additive Γ) := Finite.of_equiv Γ Additive.ofMul
  have : Finite (Additive Γ →+ ZMod p) := Finite.of_injective _ DFunLike.coe_injective
  set N := AddSubgroup.closure S
  have : Finite (N →+ ZMod p) := Finite.of_injective _ DFunLike.coe_injective
  let res : Additive Γ → (N →+ ZMod p) := fun x =>
    { toFun := fun χ => (χ : Additive Γ →+ ZMod p) x
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hN : ∀ χ : N, p • χ = 0 := fun χ => by
    apply Subtype.ext
    apply AddMonoidHom.ext
    intro x
    change p • (χ : Additive Γ →+ ZMod p) x = 0
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  have hlt : Nat.card N < Nat.card (Additive Γ →+ ZMod p) := by
    have hle : Nat.card N ≤ Nat.card (Additive Γ →+ ZMod p) :=
      Nat.card_le_card_of_injective _ Subtype.coe_injective
    refine lt_of_le_of_ne hle fun h => hS ?_
    exact (AddSubgroup.card_eq_iff_eq_top N).mp h
  have hcard : Nat.card (N →+ ZMod p) < Nat.card (Additive Γ) := by
    rw [natCard_addMonoidHom_zmod hp hN, Nat.card_congr Additive.toMul, ← natCard_char hp hexp]
    exact hlt
  have hninj : ¬Function.Injective res := fun hinj =>
    absurd (Nat.card_le_card_of_injective res hinj) (not_le.mpr hcard)
  obtain ⟨x, y, hres, hxy⟩ := Function.not_injective_iff.mp hninj
  refine ⟨Additive.toMul (x - y), ?_, fun χ hχ => ?_⟩
  · rwa [Ne, ← toMul_zero, Additive.toMul.apply_eq_iff_eq, sub_eq_zero]
  · have := DFunLike.congr_fun hres ⟨χ, AddSubgroup.subset_closure hχ⟩
    change χ x = χ y at this
    rw [ofMul_toMul, map_sub, this, sub_self]

theorem sum_char_pow_val_eq_zero {F : Type*} [Field F] [NeZero p] {ζ : F} [Finite Γ]
    [Fintype (Additive Γ →+ ZMod p)] (hp : p.Prime) (hζ : IsPrimitiveRoot ζ p)
    (hexp : ∀ g : Γ, g ^ p = 1) {g : Γ} (hg : g ≠ 1) :
    ∑ χ : Additive Γ →+ ZMod p, ζ ^ (χ (Additive.ofMul g)).val = 0 := by
  obtain ⟨χ₀, hχ₀⟩ := exists_char_apply_ne_zero hp hexp hg
  have h1 : ζ ^ (χ₀ (Additive.ofMul g)).val ≠ 1 := fun h1 =>
    hχ₀ ((root_pow_val_eq_one_iff hζ _).mp h1)
  have key : ζ ^ (χ₀ (Additive.ofMul g)).val *
      ∑ χ : Additive Γ →+ ZMod p, ζ ^ (χ (Additive.ofMul g)).val =
      ∑ χ : Additive Γ →+ ZMod p, ζ ^ (χ (Additive.ofMul g)).val := by
    rw [Finset.mul_sum]
    exact Fintype.sum_equiv (Equiv.addLeft χ₀) _ _ fun χ => by
      rw [Equiv.coe_addLeft, AddMonoidHom.add_apply, root_pow_val_add hζ.pow_eq_one]
  have : (ζ ^ (χ₀ (Additive.ofMul g)).val - 1) *
      ∑ χ : Additive Γ →+ ZMod p, ζ ^ (χ (Additive.ofMul g)).val = 0 := by
    rw [sub_mul, key, one_mul, sub_self]
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr h1)

end Duality

section Idempotents

variable {F : Type*} [Field F] {M : Type*} [AddCommGroup M] [Module F M]
variable {Γ : Type*} [Group Γ] {p : ℕ}

@[expose] def charSpace (ρ : Γ →* Module.End F M) (ζ : F) (χ : Additive Γ →+ ZMod p) :
    Submodule F M :=
  ⨅ g : Γ, Module.End.eigenspace (ρ g) (ζ ^ (χ (Additive.ofMul g)).val)

theorem mem_charSpace {ρ : Γ →* Module.End F M} {ζ : F} {χ : Additive Γ →+ ZMod p} {v : M} :
    v ∈ charSpace ρ ζ χ ↔ ∀ g, ρ g v = ζ ^ (χ (Additive.ofMul g)).val • v := by
  simp [charSpace]

variable [Fintype Γ]

@[expose] noncomputable def charIdem (ρ : Γ →* Module.End F M) (ζ : F)
    (χ : Additive Γ →+ ZMod p) : Module.End F M :=
  (Fintype.card Γ : F)⁻¹ • ∑ g : Γ, ζ ^ ((-χ) (Additive.ofMul g)).val • ρ g

variable {ρ : Γ →* Module.End F M} {ζ : F} [NeZero p]

theorem mul_charIdem (hζ : ζ ^ p = 1) (h : Γ) (χ : Additive Γ →+ ZMod p) :
    ρ h * charIdem ρ ζ χ = ζ ^ (χ (Additive.ofMul h)).val • charIdem ρ ζ χ := by
  have e : ∀ g : Γ, ρ h * (ζ ^ ((-χ) (Additive.ofMul g)).val • ρ g) =
      ζ ^ (χ (Additive.ofMul h)).val •
        (ζ ^ ((-χ) (Additive.ofMul (h * g))).val • ρ (h * g)) := by
    intro g
    rw [mul_smul_comm, ← map_mul, smul_smul]
    congr 1
    rw [ofMul_mul, map_add, root_pow_val_add hζ, ← mul_assoc,
      AddMonoidHom.neg_apply χ (Additive.ofMul h), mul_comm (ζ ^ (χ (Additive.ofMul h)).val),
      root_pow_val_neg_mul hζ, one_mul]
  calc ρ h * charIdem ρ ζ χ
      = (Fintype.card Γ : F)⁻¹ • ∑ g : Γ, ρ h * (ζ ^ ((-χ) (Additive.ofMul g)).val • ρ g) := by
        rw [charIdem, mul_smul_comm, Finset.mul_sum]
    _ = (Fintype.card Γ : F)⁻¹ • ∑ g : Γ, ζ ^ (χ (Additive.ofMul h)).val •
          (ζ ^ ((-χ) (Additive.ofMul g)).val • ρ g) := by
        congr 1
        exact Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g => e g
    _ = ζ ^ (χ (Additive.ofMul h)).val • charIdem ρ ζ χ := by
        rw [← Finset.smul_sum, smul_comm, charIdem]

theorem charIdem_apply_mem (hζ : ζ ^ p = 1) (χ : Additive Γ →+ ZMod p) (v : M) :
    charIdem ρ ζ χ v ∈ charSpace ρ ζ χ :=
  mem_charSpace.mpr fun g => by
    rw [← Module.End.mul_apply, mul_charIdem hζ, LinearMap.smul_apply]

theorem charIdem_apply_of_mem (hζ : ζ ^ p = 1) (hΓ : (Fintype.card Γ : F) ≠ 0)
    {χ : Additive Γ →+ ZMod p} {v : M} (hv : v ∈ charSpace ρ ζ χ) : charIdem ρ ζ χ v = v := by
  have hv' := mem_charSpace.mp hv
  rw [charIdem, LinearMap.smul_apply, LinearMap.sum_apply]
  simp_rw [LinearMap.smul_apply, hv', smul_smul, AddMonoidHom.neg_apply,
    root_pow_val_neg_mul hζ, one_smul, Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul F, smul_smul, inv_mul_cancel₀ hΓ, one_smul]

theorem charIdem_mul_charIdem_eq_smul (hζ : ζ ^ p = 1) (χ ψ : Additive Γ →+ ZMod p) :
    charIdem ρ ζ χ * charIdem ρ ζ ψ =
      ((Fintype.card Γ : F)⁻¹ * ∑ g : Γ, ζ ^ ((ψ - χ) (Additive.ofMul g)).val) •
        charIdem ρ ζ ψ := by
  have e : charIdem ρ ζ χ = (Fintype.card Γ : F)⁻¹ •
      ∑ g : Γ, ζ ^ ((-χ) (Additive.ofMul g)).val • ρ g := rfl
  have hc : ∑ g : Γ, ζ ^ ((-χ) (Additive.ofMul g)).val * ζ ^ (ψ (Additive.ofMul g)).val =
      ∑ g : Γ, ζ ^ ((ψ - χ) (Additive.ofMul g)).val :=
    Finset.sum_congr rfl fun g _ => by
      rw [← root_pow_val_add hζ, AddMonoidHom.sub_apply, AddMonoidHom.neg_apply,
        neg_add_eq_sub]
  rw [e, smul_mul_assoc, Finset.sum_mul,
    Finset.sum_congr rfl fun g _ => by rw [smul_mul_assoc, mul_charIdem hζ, smul_smul],
    ← Finset.sum_smul, smul_smul, hc]

theorem charIdem_mul_self (hζ : ζ ^ p = 1) (hΓ : (Fintype.card Γ : F) ≠ 0)
    (χ : Additive Γ →+ ZMod p) : charIdem ρ ζ χ * charIdem ρ ζ χ = charIdem ρ ζ χ := by
  rw [charIdem_mul_charIdem_eq_smul hζ, sub_self]
  simp only [AddMonoidHom.zero_apply, ZMod.val_zero, pow_zero, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one, inv_mul_cancel₀ hΓ, one_smul]

theorem charIdem_mul_charIdem_of_ne (hζ : IsPrimitiveRoot ζ p) {χ ψ : Additive Γ →+ ZMod p}
    (h : χ ≠ ψ) : charIdem ρ ζ χ * charIdem ρ ζ ψ = 0 := by
  rw [charIdem_mul_charIdem_eq_smul hζ.pow_eq_one,
    sum_pow_val_char_eq_zero hζ (sub_ne_zero.mpr (Ne.symm h)), mul_zero, zero_smul]

theorem charSpace_le_ker_charIdem (hζ : IsPrimitiveRoot ζ p) (hΓ : (Fintype.card Γ : F) ≠ 0)
    {χ ψ : Additive Γ →+ ZMod p} (h : ψ ≠ χ) :
    charSpace ρ ζ ψ ≤ LinearMap.ker (charIdem ρ ζ χ) := by
  intro v hv
  rw [LinearMap.mem_ker, ← charIdem_apply_of_mem hζ.pow_eq_one hΓ hv, ← Module.End.mul_apply,
    charIdem_mul_charIdem_of_ne hζ h.symm, LinearMap.zero_apply]

theorem iSupIndep_charSpace (hζ : IsPrimitiveRoot ζ p) (hΓ : (Fintype.card Γ : F) ≠ 0) :
    iSupIndep (charSpace ρ ζ (p := p)) := by
  rw [iSupIndep_def]
  intro χ
  rw [Submodule.disjoint_def]
  intro v hv hv'
  have h2 : ⨆ ψ, ⨆ (_ : ψ ≠ χ), charSpace ρ ζ ψ ≤ LinearMap.ker (charIdem ρ ζ χ) :=
    iSup₂_le fun ψ hψ => charSpace_le_ker_charIdem hζ hΓ hψ
  rw [← charIdem_apply_of_mem hζ.pow_eq_one hΓ hv]
  exact h2 hv'

end Idempotents

section Decomposition

variable {F : Type*} [Field F] {M : Type*} [AddCommGroup M] [Module F M]
variable {Γ : Type*} [CommGroup Γ] [Fintype Γ] {p : ℕ} [NeZero p]
variable {ρ : Γ →* Module.End F M} {ζ : F}

theorem sum_charIdem [Fintype (Additive Γ →+ ZMod p)] (hp : p.Prime) (hζ : IsPrimitiveRoot ζ p)
    (hexp : ∀ g : Γ, g ^ p = 1) (hΓ : (Fintype.card Γ : F) ≠ 0) :
    ∑ χ : Additive Γ →+ ZMod p, charIdem ρ ζ χ = 1 := by
  have hcard : Fintype.card (Additive Γ →+ ZMod p) = Fintype.card Γ := by
    rw [← Nat.card_eq_fintype_card, natCard_char hp hexp, Nat.card_eq_fintype_card]
  simp only [charIdem]
  rw [← Finset.smul_sum, Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  rw [Finset.sum_eq_single (1 : Γ)]
  · have h1 : ∑ χ : Additive Γ →+ ZMod p, ζ ^ ((-χ) (Additive.ofMul (1 : Γ))).val =
        (Fintype.card Γ : F) := by
      rw [ofMul_one]
      simp only [map_zero, ZMod.val_zero, pow_zero, Finset.sum_const, Finset.card_univ, hcard,
        nsmul_eq_mul, mul_one]
    rw [h1, map_one, smul_smul, inv_mul_cancel₀ hΓ, one_smul]
  · intro g _ hg
    have hneg : ∑ χ : Additive Γ →+ ZMod p, ζ ^ ((-χ) (Additive.ofMul g)).val =
        ∑ χ : Additive Γ →+ ZMod p, ζ ^ (χ (Additive.ofMul g)).val :=
      Fintype.sum_equiv (Equiv.neg _) _ _ fun χ => rfl
    rw [hneg, sum_char_pow_val_eq_zero hp hζ hexp hg, zero_smul]
  · simp

theorem eq_sum_charIdem_apply [Fintype (Additive Γ →+ ZMod p)] (hp : p.Prime)
    (hζ : IsPrimitiveRoot ζ p) (hexp : ∀ g : Γ, g ^ p = 1) (hΓ : (Fintype.card Γ : F) ≠ 0)
    (v : M) : v = ∑ χ : Additive Γ →+ ZMod p, charIdem ρ ζ χ v := by
  rw [← LinearMap.sum_apply, sum_charIdem hp hζ hexp hΓ, Module.End.one_apply]

theorem iSup_charSpace_eq_top [Fintype (Additive Γ →+ ZMod p)] (hp : p.Prime)
    (hζ : IsPrimitiveRoot ζ p) (hexp : ∀ g : Γ, g ^ p = 1) (hΓ : (Fintype.card Γ : F) ≠ 0) :
    ⨆ χ : Additive Γ →+ ZMod p, charSpace ρ ζ χ = ⊤ := by
  rw [eq_top_iff]
  intro v _
  rw [eq_sum_charIdem_apply hp hζ hexp hΓ v]
  exact Submodule.sum_mem_iSup fun χ => charIdem_apply_mem hζ.pow_eq_one χ v

theorem sum_finrank_charSpace [FiniteDimensional F M] [Fintype (Additive Γ →+ ZMod p)]
    (hp : p.Prime) (hζ : IsPrimitiveRoot ζ p) (hexp : ∀ g : Γ, g ^ p = 1)
    (hΓ : (Fintype.card Γ : F) ≠ 0) :
    ∑ χ : Additive Γ →+ ZMod p, finrank F (charSpace ρ ζ χ) = finrank F M := by
  classical
  have hint : DirectSum.IsInternal (charSpace ρ ζ (p := p)) :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr
      ⟨iSupIndep_charSpace hζ hΓ, iSup_charSpace_eq_top hp hζ hexp hΓ⟩
  rw [← (LinearEquiv.ofBijective (DirectSum.coeLinearMap _) hint).finrank_eq,
    Module.finrank_directSum]

end Decomposition

section Transport

variable {F : Type*} [Field F] {M : Type*} [AddCommGroup M] [Module F M]
variable {Γ : Type*} [Group Γ] {p : ℕ} [NeZero p]
variable {ρ : Γ →* Module.End F M} {ζ : F}

theorem finrank_charSpace_nsmul (hζ : ζ ^ p = 1) (σ : F ≃+* F) (Φ : M ≃+ M)
    (hΦ : ∀ (c : F) (v : M), Φ (c • v) = σ c • Φ v) (hρ : ∀ g v, Φ (ρ g v) = ρ g (Φ v))
    (n : ℕ) (hσ : σ ζ = ζ ^ n) (χ : Additive Γ →+ ZMod p) :
    finrank F (charSpace ρ ζ (n • χ)) = finrank F (charSpace ρ ζ χ) := by
  have hpow : ∀ a : ZMod p, σ (ζ ^ a.val) = ζ ^ (n • a).val := fun a => by
    rw [map_pow, hσ, root_pow_val_nsmul hζ, ← pow_mul, ← pow_mul, mul_comm]
  have hΦ' : ∀ (c : F) (w : M), Φ.symm (c • w) = σ.symm c • Φ.symm w := fun c w => by
    apply Φ.injective
    rw [hΦ, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  have hρ' : ∀ g w, Φ.symm (ρ g w) = ρ g (Φ.symm w) := fun g w => by
    apply Φ.injective
    rw [hρ, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  have h1 : ∀ v ∈ charSpace ρ ζ χ, Φ v ∈ charSpace ρ ζ (n • χ) := by
    intro v hv
    rw [mem_charSpace] at hv ⊢
    intro g
    rw [← hρ, hv g, hΦ, hpow, AddMonoidHom.nsmul_apply]
  have h2 : ∀ w ∈ charSpace ρ ζ (n • χ), Φ.symm w ∈ charSpace ρ ζ χ := by
    intro w hw
    rw [mem_charSpace] at hw ⊢
    intro g
    rw [← hρ', hw g, hΦ', AddMonoidHom.nsmul_apply, ← hpow, RingEquiv.symm_apply_apply]
  let j : charSpace ρ ζ χ ≃+ charSpace ρ ζ (n • χ) :=
    { toFun := fun v => ⟨Φ v, h1 v v.2⟩
      invFun := fun w => ⟨Φ.symm w, h2 w w.2⟩
      left_inv := fun v => Subtype.ext (Φ.symm_apply_apply v)
      right_inv := fun w => Subtype.ext (Φ.apply_symm_apply w)
      map_add' := fun v v' => Subtype.ext (map_add Φ (v : M) v') }
  have := rank_eq_of_equiv_equiv σ j σ.bijective fun c v => Subtype.ext (hΦ c v)
  unfold Module.finrank
  rw [this]

theorem apply_eq_zero_of_mem_charSpace (hζ : IsPrimitiveRoot ζ p)
    (B : LinearMap.BilinForm F M) (hB : ∀ g v w, B (ρ g v) (ρ g w) = B v w)
    {χ ψ : Additive Γ →+ ZMod p} (h : χ + ψ ≠ 0) {v w : M} (hv : v ∈ charSpace ρ ζ χ)
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
variable {ρ : Γ →* Module.End F M} {ζ : F}

theorem finrank_charSpace_le_neg [FiniteDimensional F M] [Fintype (Additive Γ →+ ZMod p)]
    (hp : p.Prime) (hζ : IsPrimitiveRoot ζ p) (hexp : ∀ g : Γ, g ^ p = 1)
    (hΓ : (Fintype.card Γ : F) ≠ 0) (B : LinearMap.BilinForm F M)
    (hB : ∀ g v w, B (ρ g v) (ρ g w) = B v w) (hBnd : ∀ v, (∀ w, B v w = 0) → v = 0)
    (χ : Additive Γ →+ ZMod p) :
    finrank F (charSpace ρ ζ χ) ≤ finrank F (charSpace ρ ζ (-χ)) := by
  let f : charSpace ρ ζ χ →ₗ[F] Module.Dual F (charSpace ρ ζ (-χ)) := B.domRestrict₁₂ _ _
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    apply Subtype.ext
    apply hBnd
    intro w
    rw [eq_sum_charIdem_apply hp hζ hexp hΓ w, map_sum, Finset.sum_eq_single (-χ)]
    · exact LinearMap.congr_fun hv ⟨_, charIdem_apply_mem hζ.pow_eq_one _ w⟩
    · intro ψ _ hψ
      refine apply_eq_zero_of_mem_charSpace hζ B hB (fun h => hψ ?_) v.2
        (charIdem_apply_mem hζ.pow_eq_one ψ w)
      exact eq_neg_of_add_eq_zero_right h
    · simp
  calc finrank F (charSpace ρ ζ χ) ≤ finrank F (Module.Dual F (charSpace ρ ζ (-χ))) :=
        LinearMap.finrank_le_finrank_of_injective hf
    _ = finrank F (charSpace ρ ζ (-χ)) := Subspace.dual_finrank_eq

theorem finrank_charSpace_neg [FiniteDimensional F M] [Fintype (Additive Γ →+ ZMod p)]
    (hp : p.Prime) (hζ : IsPrimitiveRoot ζ p) (hexp : ∀ g : Γ, g ^ p = 1)
    (hΓ : (Fintype.card Γ : F) ≠ 0) (B : LinearMap.BilinForm F M)
    (hB : ∀ g v w, B (ρ g v) (ρ g w) = B v w) (hBnd : ∀ v, (∀ w, B v w = 0) → v = 0)
    (χ : Additive Γ →+ ZMod p) :
    finrank F (charSpace ρ ζ (-χ)) = finrank F (charSpace ρ ζ χ) := by
  refine le_antisymm ?_ (finrank_charSpace_le_neg hp hζ hexp hΓ B hB hBnd χ)
  have := finrank_charSpace_le_neg hp hζ hexp hΓ B hB hBnd (-χ)
  rwa [neg_neg] at this

theorem closure_support_charSpace_eq_top [Fintype (Additive Γ →+ ZMod p)] (hp : p.Prime)
    (hζ : IsPrimitiveRoot ζ p) (hexp : ∀ g : Γ, g ^ p = 1) (hΓ : (Fintype.card Γ : F) ≠ 0)
    (hfaith : ∀ g, ρ g = 1 → g = 1) :
    AddSubgroup.closure {χ : Additive Γ →+ ZMod p | χ ≠ 0 ∧ charSpace ρ ζ χ ≠ ⊥} = ⊤ := by
  by_contra h
  obtain ⟨g, hg, hgS⟩ := exists_ne_one_of_closure_ne_top hp hexp h
  apply hg
  apply hfaith
  apply LinearMap.ext
  intro v
  have hv := eq_sum_charIdem_apply (ρ := ρ) hp hζ hexp hΓ v
  have hterm : ∀ χ : Additive Γ →+ ZMod p, ρ g (charIdem ρ ζ χ v) = charIdem ρ ζ χ v := by
    intro χ
    have hmem := charIdem_apply_mem (ρ := ρ) hζ.pow_eq_one χ v
    rw [(mem_charSpace.mp hmem) g]
    by_cases h0 : χ (Additive.ofMul g) = 0
    · rw [h0, ZMod.val_zero, pow_zero, one_smul]
    · have hbot : charSpace ρ ζ χ = ⊥ := by
        by_contra hne
        refine h0 (hgS χ ⟨fun hχ => h0 ?_, hne⟩)
        rw [hχ, AddMonoidHom.zero_apply]
      have : charIdem ρ ζ χ v = 0 := by
        rw [← Submodule.mem_bot F, ← hbot]
        exact hmem
      rw [this, smul_zero]
  calc ρ g v = ρ g (∑ χ : Additive Γ →+ ZMod p, charIdem ρ ζ χ v) := congrArg (ρ g) hv
    _ = ∑ χ : Additive Γ →+ ZMod p, charIdem ρ ζ χ v := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun χ _ => hterm χ
    _ = (1 : Module.End F M) v := by rw [Module.End.one_apply, ← hv]

end Pairing

theorem two_mul_lcm_le_sum {p : ℕ} {D : Type*} [AddCommGroup D] [Module (ZMod p) D] [Fintype D]
    (hp : p.Prime) (hp2 : p ≠ 2) (hD : Nat.card D = p ^ 2) {q : ℕ} (hpq : ¬p ∣ q)
    (m : D → ℕ) (hq : ∀ χ, m (q • χ) = m χ) (hneg : ∀ χ, m (-χ) = m χ)
    (hS : AddSubgroup.closure {χ | χ ≠ 0 ∧ m χ ≠ 0} = ⊤) :
    2 * Nat.lcm (orderOf (q : ZMod p)) 2 ≤ ∑ χ, m χ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp2' := hp.two_le
  have hcop : Nat.Coprime q p :=
    Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpq)
  set u : (ZMod p)ˣ := ZMod.unitOfCoprime q hcop with hudef
  have hu : (u : ZMod p) = q := ZMod.coe_unitOfCoprime q hcop
  set H : Subgroup (ZMod p)ˣ := Subgroup.closure {u, -1} with hHdef
  have hH : ∀ w ∈ H, ∀ χ, m ((w : ZMod p) • χ) = m χ := by
    intro w hw
    induction hw using Subgroup.closure_induction with
    | mem w hw =>
      rcases hw with rfl | hw
      · intro χ
        rw [hu, Nat.cast_smul_eq_nsmul]
        exact hq χ
      · rw [Set.mem_singleton_iff] at hw
        subst hw
        intro χ
        rw [Units.val_neg, Units.val_one, neg_one_smul]
        exact hneg χ
    | one => intro χ; rw [Units.val_one, one_smul]
    | mul w w' _ _ h h' => intro χ; rw [Units.val_mul, mul_smul, h, h']
    | inv w _ h =>
      intro χ
      have := h (((w⁻¹ : (ZMod p)ˣ) : ZMod p) • χ)
      rw [smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul] at this
      exact this.symm
  have hfree : ∀ χ : D, χ ≠ 0 → Function.Injective fun w : (ZMod p)ˣ => (w : ZMod p) • χ := by
    intro χ hχ w w' h
    have h0 : ((w : ZMod p) - w') • χ = 0 := by
      rw [sub_smul]
      exact sub_eq_zero.mpr h
    rcases smul_eq_zero.mp h0 with h1 | h1
    · exact Units.ext (sub_eq_zero.mp h1)
    · exact absurd h1 hχ
  set S := {χ : D | χ ≠ 0 ∧ m χ ≠ 0} with hSdef
  have hpχ : ∀ χ : D, p • χ = 0 := fun χ => by
    rw [← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_self, zero_smul]
  have hzm : ∀ χ : D, Nat.card (AddSubgroup.zmultiples χ) ≤ p := fun χ => by
    rw [Nat.card_zmultiples]
    exact addOrderOf_le_of_nsmul_eq_zero hp.pos (hpχ χ)
  have hp1 : p < p ^ 2 := by nlinarith
  obtain ⟨χ₁, hχ₁⟩ : S.Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    rw [hcon, AddSubgroup.closure_empty] at hS
    have h1 : Nat.card D ≤ 1 := by
      rw [← AddSubgroup.card_top (G := D), ← hS, AddSubgroup.card_bot]
    omega
  obtain ⟨χ₂, hχ₂, hχ₂'⟩ : ∃ χ ∈ S, χ ∉ AddSubgroup.zmultiples χ₁ := by
    by_contra hcon
    push Not at hcon
    have hle : AddSubgroup.closure S ≤ AddSubgroup.zmultiples χ₁ :=
      (AddSubgroup.closure_le _).mpr hcon
    rw [hS] at hle
    have h1 : Nat.card D ≤ p := by
      rw [← AddSubgroup.card_top (G := D)]
      exact (AddSubgroup.card_le_of_le hle).trans (hzm χ₁)
    omega
  have hdisj : ∀ w w' : (ZMod p)ˣ, (w : ZMod p) • χ₁ ≠ (w' : ZMod p) • χ₂ := by
    intro w w' h
    apply hχ₂'
    have : χ₂ = ((w'⁻¹ * w : (ZMod p)ˣ) : ZMod p) • χ₁ := by
      rw [Units.val_mul, mul_smul, h, ← mul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        one_smul]
    rw [this, ← ZMod.natCast_zmod_val ((w'⁻¹ * w : (ZMod p)ˣ) : ZMod p), Nat.cast_smul_eq_nsmul]
    exact AddSubgroup.nsmul_mem_zmultiples _ _
  set T := Finset.univ.filter (· ∈ H) with hTdef
  set O₁ := T.image fun w : (ZMod p)ˣ => (w : ZMod p) • χ₁ with hO₁
  set O₂ := T.image fun w : (ZMod p)ˣ => (w : ZMod p) • χ₂ with hO₂
  have hO : Disjoint O₁ O₂ := by
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hx₁
    obtain ⟨w', -, hw'⟩ := Finset.mem_image.mp hx₂
    exact hdisj w w' hw'.symm
  have hsum : ∀ χ : D, χ ∈ S →
      T.card ≤ ∑ x ∈ T.image (fun w : (ZMod p)ˣ => (w : ZMod p) • χ), m x := by
    intro χ hχ
    rw [Finset.sum_image fun w _ w' _ h => hfree χ hχ.1 h]
    calc T.card = ∑ w ∈ T, 1 := by simp
      _ ≤ ∑ w ∈ T, m ((w : ZMod p) • χ) := by
        refine Finset.sum_le_sum fun w hw => ?_
        rw [hH w (Finset.mem_filter.mp hw).2 χ]
        exact Nat.one_le_iff_ne_zero.mpr hχ.2
  have hT : T.card = Nat.card H := by
    rw [hTdef, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hlcm : Nat.lcm (orderOf (q : ZMod p)) 2 ≤ T.card := by
    rw [hT]
    refine Nat.le_of_dvd Nat.card_pos (Nat.lcm_dvd ?_ ?_)
    · rw [← hu, orderOf_units]
      exact Subgroup.orderOf_dvd_natCard H (Subgroup.subset_closure (Set.mem_insert u _))
    · have h2 : orderOf (-1 : (ZMod p)ˣ) = 2 := by
        rw [← orderOf_units, Units.val_neg, Units.val_one, orderOf_neg_one, ZMod.ringChar_zmod_n,
          ite_eq_right hp2]
      rw [← h2]
      exact Subgroup.orderOf_dvd_natCard H (Subgroup.subset_closure (Set.mem_insert_of_mem u rfl))
  calc 2 * Nat.lcm (orderOf (q : ZMod p)) 2 ≤ T.card + T.card := by omega
    _ ≤ ∑ x ∈ O₁, m x + ∑ x ∈ O₂, m x := add_le_add (hsum χ₁ hχ₁) (hsum χ₂ hχ₂)
    _ = ∑ x ∈ O₁ ∪ O₂, m x := (Finset.sum_union hO).symm
    _ ≤ ∑ χ, m χ := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

end CFSG.RankThree.Classical
