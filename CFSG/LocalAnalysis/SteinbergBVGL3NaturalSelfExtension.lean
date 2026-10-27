module

public import CFSG.LocalAnalysis.SteinbergBVGL3InvolutionDimensionBound

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.SteinbergBV

open Module Matrix CFSG.ProperTwoGeneratedCore.BinaryThreeSpace

namespace SelfExtension

open ThreeInvolutions

theorem T01_eq : T01 = invGL t02 (by decide) * invGL t21 (by decide) *
    (invGL t02 (by decide))⁻¹ * (invGL t21 (by decide))⁻¹ :=
  Units.ext <| by
    change t01 = t02 * t21 * t02 * t21
    decide

theorem T12_eq : T12 = invGL t10 (by decide) * invGL t02 (by decide) *
    (invGL t10 (by decide))⁻¹ * (invGL t02 (by decide))⁻¹ :=
  Units.ext <| by
    change t12 = t10 * t02 * t10 * t02
    decide

theorem T20_eq : T20 = invGL t21 (by decide) * invGL t10 (by decide) *
    (invGL t21 (by decide))⁻¹ * (invGL t10 (by decide))⁻¹ :=
  Units.ext <| by
    change t20 = t21 * t10 * t21 * t10
    decide

theorem eq_zero_of_map_mul {χ : GL (Fin 3) (ZMod 2) → ZMod 2}
    (hχ : ∀ g h, χ (g * h) = χ g + χ h) (g : GL (Fin 3) (ZMod 2)) : χ g = 0 := by
  have h1 : χ 1 = 0 := by
    have h := hχ 1 1
    rw [mul_one] at h
    exact left_eq_add.1 h
  have hinv : ∀ x, χ x⁻¹ = -χ x := fun x => by
    have h := hχ x x⁻¹
    rw [mul_inv_cancel, h1] at h
    exact eq_neg_of_add_eq_zero_right h.symm
  have hcomm : ∀ x y, χ (x * y * x⁻¹ * y⁻¹) = 0 := fun x y => by
    rw [hχ, hχ, hχ, hinv, hinv]
    ring
  have hg : g ∈ Subgroup.closure ({T01, T12, T20} : Set (GL (Fin 3) (ZMod 2))) := by
    rw [closure_tGL_eq_top]
    exact Subgroup.mem_top g
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl | rfl
    · rw [T01_eq]
      exact hcomm _ _
    · rw [T12_eq]
      exact hcomm _ _
    · rw [T20_eq]
      exact hcomm _ _
  | one => exact h1
  | mul x y _ _ hx hy => rw [hχ, hx, hy, add_zero]
  | inv x _ hx => rw [hinv, hx, neg_zero]

theorem index_sylowT : sylowT.index = 21 := by
  have h := sylowT.index_mul_card
  rw [card_sylowT, FixedCodim.card_GL3] at h
  omega

theorem mulVec_inv_mulVec (g : GL (Fin 3) (ZMod 2)) (v : Fin 3 → ZMod 2) :
    (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ
      (((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v) = v := by
  rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]

theorem inv_mulVec_mulVec (g : GL (Fin 3) (ZMod 2)) (v : Fin 3 → ZMod 2) :
    ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ
      ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v) = v := by
  rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

@[expose] def defect (ρ : Representation (ZMod 2) (GL (Fin 3) (ZMod 2)) E)
    (σ : (Fin 3 → ZMod 2) →ₗ[ZMod 2] E) (g : GL (Fin 3) (ZMod 2)) :
    (Fin 3 → ZMod 2) →ₗ[ZMod 2] E :=
  ρ g ∘ₗ σ ∘ₗ Matrix.toLin' ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) - σ

theorem defect_apply (ρ : Representation (ZMod 2) (GL (Fin 3) (ZMod 2)) E)
    (σ : (Fin 3 → ZMod 2) →ₗ[ZMod 2] E) (g : GL (Fin 3) (ZMod 2)) (x : Fin 3 → ZMod 2) :
    defect ρ σ g x =
      ρ g (σ (((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ x)) - σ x :=
  rfl

theorem defect_mul (ρ : Representation (ZMod 2) (GL (Fin 3) (ZMod 2)) E)
    (σ : (Fin 3 → ZMod 2) →ₗ[ZMod 2] E) (g h : GL (Fin 3) (ZMod 2)) (x : Fin 3 → ZMod 2) :
    defect ρ σ (g * h) x = defect ρ σ g x +
      ρ g (defect ρ σ h
        (((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ x)) := by
  rw [defect_apply, defect_apply, defect_apply, map_sub, map_mul, Module.End.mul_apply,
    _root_.mul_inv_rev, Units.val_mul, ← mulVec_mulVec]
  abel

end SelfExtension

open SelfExtension in
theorem natural_binary_three_space_self_extension_splitting {E : Type*} [AddCommGroup E]
    [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]
    (ρ : Representation (ZMod 2) (GL (Fin 3) (ZMod 2)) E)
    (i : (Fin 3 → ZMod 2) →ₗ[ZMod 2] E) (π : E →ₗ[ZMod 2] (Fin 3 → ZMod 2))
    (hi : ∀ (g : GL (Fin 3) (ZMod 2)) (v : Fin 3 → ZMod 2),
      i ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v) = ρ g (i v))
    (hπ : ∀ (g : GL (Fin 3) (ZMod 2)) (e : E),
      π (ρ g e) = (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ π e)
    (hinj : Function.Injective i) (hsurj : Function.Surjective π)
    (hker : LinearMap.ker π = LinearMap.range i) :
    ∃ j : (Fin 3 → ZMod 2) →ₗ[ZMod 2] E,
      (∀ (g : GL (Fin 3) (ZMod 2)) (v : Fin 3 → ZMod 2),
        j ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v) = ρ g (j v)) ∧
      π ∘ₗ j = LinearMap.id ∧
      ∃ φ : ((Fin 3 → ZMod 2) × (Fin 3 → ZMod 2)) ≃ₗ[ZMod 2] E,
        (∀ v w, φ (v, w) = i v + j w) ∧
        ∀ (g : GL (Fin 3) (ZMod 2)) (v w : Fin 3 → ZMod 2),
          φ ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v,
            (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ w) = ρ g (φ (v, w)) := by
  classical
  have hπi : ∀ v, π (i v) = 0 := fun v => by
    have h : i v ∈ LinearMap.ker π := by
      rw [hker]
      exact ⟨v, rfl⟩
    exact h
  obtain ⟨σ, hσ⟩ := LinearMap.exists_rightInverse_of_surjective π (LinearMap.range_eq_top.2 hsurj)
  have hπσ : ∀ v, π (σ v) = v := fun v => LinearMap.congr_fun hσ v
  have hδmem : ∀ g x, defect ρ σ g x ∈ LinearMap.range i := fun g x => by
    rw [← hker, LinearMap.mem_ker, defect_apply, map_sub, hπ, hπσ, hπσ, mulVec_inv_mulVec,
      sub_self]
  let c : GL (Fin 3) (ZMod 2) → (Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2) := fun g =>
    (LinearEquiv.ofInjective i hinj).symm.toLinearMap ∘ₗ
      (defect ρ σ g).codRestrict (LinearMap.range i) (hδmem g)
  have hc : ∀ g x, i (c g x) = defect ρ σ g x := fun g x => by
    simp only [c, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [LinearEquiv.ofInjective_symm_apply]
    rfl
  have hcmul : ∀ g h x, c (g * h) x = c g x + (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ
      c h (((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ x) := by
    intro g h x
    apply hinj
    rw [hc, map_add, hc, hi, hc, defect_mul]
  let C : GL (Fin 3) (ZMod 2) → Matrix (Fin 3) (Fin 3) (ZMod 2) := fun g =>
    LinearMap.toMatrix' (c g)
  have hCx : ∀ g x, C g *ᵥ x = c g x := fun g x => LinearMap.toMatrix'_mulVec _ _
  have hCmul : ∀ g h, C (g * h) = C g + (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * C h *
      ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
    intro g h
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun x => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, add_mulVec, ← mulVec_mulVec, ← mulVec_mulVec,
      hCx, hCx, hCx, hcmul]
  have htr : ∀ g, C g ∈ traceZero := by
    intro g
    have h := eq_zero_of_map_mul (χ := fun g => Matrix.trace (C g)) (fun g h => by
      rw [hCmul, Matrix.trace_add, Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, Matrix.one_mul]) g
    rw [traceZero, LinearMap.mem_ker, Matrix.traceLinearMap_apply]
    exact h
  obtain ⟨-, -, hΦbij, hΦeq⟩ := trace_zero_regular_Sylow_module
  set Φ := Fintype.linearCombination (ZMod 2) conjFamily with hΦ
  let d : sylowT → sylowT → ZMod 2 := fun h =>
    (LinearEquiv.ofBijective Φ hΦbij).symm ⟨C h, htr h⟩
  have hd : ∀ h : sylowT, ((Φ (d h) : traceZero) : Matrix (Fin 3) (Fin 3) (ZMod 2)) = C h :=
    fun h => by
      have h1 := (LinearEquiv.ofBijective Φ hΦbij).apply_symm_apply ⟨C h, htr h⟩
      rw [LinearEquiv.ofBijective_apply] at h1
      exact congrArg Subtype.val h1
  have hdmul : ∀ h k : sylowT, d (h * k) = d h + fun x => d k (h⁻¹ * x) := by
    intro h k
    apply hΦbij.1
    apply Subtype.ext
    rw [map_add, Submodule.coe_add, hd, hΦeq, hd, hd, Subgroup.coe_mul, hCmul]
  set f : sylowT → ZMod 2 := fun x => d x⁻¹ 1 with hf
  have hdf : ∀ h x, d h x = f x + f (h⁻¹ * x) := by
    intro h x
    have h1 := congrFun (hdmul x⁻¹ h) 1
    simp only [Pi.add_apply, inv_inv, mul_one] at h1
    have h2 : f (h⁻¹ * x) = d (x⁻¹ * h) 1 := by
      simp only [hf, _root_.mul_inv_rev, inv_inv]
    have key : ∀ a b c : ZMod 2, a = b + c → c = b + a := by decide
    rw [h2]
    exact key _ _ _ h1
  set A : Matrix (Fin 3) (Fin 3) (ZMod 2) := ((Φ f : traceZero) : Matrix (Fin 3) (Fin 3) (ZMod 2))
    with hA
  have hCA : ∀ h : sylowT, C h = A + ((h : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
      A * (((h : GL (Fin 3) (ZMod 2))⁻¹ : GL (Fin 3) (ZMod 2)) :
        Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
    intro h
    rw [← hd, hA, ← hΦeq]
    have hdh : d h = f + fun x => f (h⁻¹ * x) := funext (hdf h)
    rw [hdh, map_add, Submodule.coe_add]
  set σT : (Fin 3 → ZMod 2) →ₗ[ZMod 2] E := σ + i ∘ₗ Matrix.toLin' A with hσT
  have hπσT : ∀ v, π (σT v) = v := fun v => by
    rw [hσT, LinearMap.add_apply, map_add, LinearMap.comp_apply, hπσ, hπi, add_zero]
  have hσTeq : ∀ h : sylowT, ∀ y, ρ h (σT y) =
      σT (((h : GL (Fin 3) (ZMod 2)) : Mat3) *ᵥ y) := by
    intro h y
    have hHH : (((h : GL (Fin 3) (ZMod 2))⁻¹ : GL (Fin 3) (ZMod 2)) : Mat3) *ᵥ
        (((h : GL (Fin 3) (ZMod 2)) : Mat3) *ᵥ y) = y := inv_mulVec_mulVec _ y
    have hδy : ρ h (σ y) = σ (((h : GL (Fin 3) (ZMod 2)) : Mat3) *ᵥ y) +
        i (C h *ᵥ (((h : GL (Fin 3) (ZMod 2)) : Mat3) *ᵥ y)) := by
      rw [hCx, hc, defect_apply, hHH]
      abel
    have hkey : C h *ᵥ (((h : GL (Fin 3) (ZMod 2)) : Mat3) *ᵥ y) +
        ((h : GL (Fin 3) (ZMod 2)) : Mat3) *ᵥ (A *ᵥ y) =
          A *ᵥ (((h : GL (Fin 3) (ZMod 2)) : Mat3) *ᵥ y) := by
      rw [hCA h, add_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hHH, add_assoc,
        CFSG.ProperTwoGeneratedCore.BinaryThreeSpace.add_self_eq_zero', add_zero]
    calc ρ h (σT y) = ρ h (σ y) + ρ h (i (A *ᵥ y)) := by
          rw [hσT, LinearMap.add_apply, map_add, LinearMap.comp_apply, Matrix.toLin'_apply]
      _ = σ (((h : GL (Fin 3) (ZMod 2)) : Mat3) *ᵥ y) +
          i (C h *ᵥ (((h : GL (Fin 3) (ZMod 2)) : Mat3) *ᵥ y) +
            ((h : GL (Fin 3) (ZMod 2)) : Mat3) *ᵥ (A *ᵥ y)) := by
          rw [hδy, ← hi, map_add, add_assoc]
      _ = σT (((h : GL (Fin 3) (ZMod 2)) : Mat3) *ᵥ y) := by
          rw [hkey, hσT, LinearMap.add_apply, LinearMap.comp_apply, Matrix.toLin'_apply]
  let J : GL (Fin 3) (ZMod 2) → (Fin 3 → ZMod 2) →ₗ[ZMod 2] E := fun g =>
    ρ g ∘ₗ σT ∘ₗ Matrix.toLin' ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))
  have hJx : ∀ g x, J g x = ρ g (σT (((g⁻¹ : GL (Fin 3) (ZMod 2)) :
      Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ x)) := fun g x => rfl
  have hJT : ∀ g, ∀ h ∈ sylowT, J (g * h) = J g := by
    intro g h hh
    refine LinearMap.ext fun x => ?_
    rw [hJx, hJx, map_mul, Module.End.mul_apply, _root_.mul_inv_rev, Units.val_mul,
      ← mulVec_mulVec, hσTeq ⟨h, hh⟩, mulVec_inv_mulVec]
  have hJout : ∀ g : GL (Fin 3) (ZMod 2),
      J (QuotientGroup.mk g : GL (Fin 3) (ZMod 2) ⧸ sylowT).out = J g := by
    intro g
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul sylowT g
    rw [hh, hJT g h h.2]
  have hJs : ∀ (s g : GL (Fin 3) (ZMod 2)) x,
      ρ s (J g x) = J (s * g) ((s : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ x) := by
    intro s g x
    rw [hJx, hJx, map_mul, Module.End.mul_apply, _root_.mul_inv_rev, Units.val_mul,
      ← mulVec_mulVec, inv_mulVec_mulVec]
  have hπJ : ∀ g x, π (J g x) = x := fun g x => by
    rw [hJx, hπ, hπσT, mulVec_inv_mulVec]
  let _ : Fintype (GL (Fin 3) (ZMod 2) ⧸ sylowT) := Fintype.ofFinite _
  let j : (Fin 3 → ZMod 2) →ₗ[ZMod 2] E := ∑ q : GL (Fin 3) (ZMod 2) ⧸ sylowT, J q.out
  have hjx : ∀ x, j x = ∑ q : GL (Fin 3) (ZMod 2) ⧸ sylowT, J q.out x := fun x => by
    simp only [j]
    exact LinearMap.sum_apply _ _ _
  have hjeq : ∀ (g : GL (Fin 3) (ZMod 2)) (v : Fin 3 → ZMod 2),
      j ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v) = ρ g (j v) := by
    intro g v
    rw [hjx, hjx, map_sum,
      ← Equiv.sum_comp (MulAction.toPerm g : Equiv.Perm (GL (Fin 3) (ZMod 2) ⧸ sylowT))]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hJs, ← hJout (g * q.out)]
    have hq : (QuotientGroup.mk (g * q.out) : GL (Fin 3) (ZMod 2) ⧸ sylowT) =
        MulAction.toPerm g q := by
      rw [MulAction.toPerm_apply]
      conv_rhs => rw [← QuotientGroup.out_eq' q]
      rw [MulAction.Quotient.smul_mk, smul_eq_mul]
    rw [hq]
  have hπj : π ∘ₗ j = LinearMap.id := by
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.comp_apply, hjx, map_sum, LinearMap.id_apply]
    simp only [hπJ, Finset.sum_const, Finset.card_univ]
    have hcard : Fintype.card (GL (Fin 3) (ZMod 2) ⧸ sylowT) = 21 := by
      rw [← Nat.card_eq_fintype_card, ← Subgroup.index, index_sylowT]
    rw [hcard, ← Nat.cast_smul_eq_nsmul (ZMod 2), show ((21 : ℕ) : ZMod 2) = 1 from rfl, one_smul]
  have hπjx : ∀ w, π (j w) = w := fun w => LinearMap.congr_fun hπj w
  have hφinj : Function.Injective (LinearMap.coprod i j) := by
    rintro ⟨v, w⟩ ⟨v', w'⟩ h
    simp only [LinearMap.coprod_apply] at h
    have hw : w = w' := by
      have h1 := congrArg π h
      rwa [map_add, map_add, hπi, hπi, zero_add, zero_add, hπjx, hπjx] at h1
    subst hw
    have hv : v = v' := hinj (add_right_cancel h)
    rw [hv]
  have hφsurj : Function.Surjective (LinearMap.coprod i j) := by
    intro e
    have hmem : e - j (π e) ∈ LinearMap.range i := by
      rw [← hker, LinearMap.mem_ker, map_sub, hπjx, sub_self]
    obtain ⟨v, hv⟩ := hmem
    exact ⟨(v, π e), by rw [LinearMap.coprod_apply, hv, sub_add_cancel]⟩
  have hbij : Function.Bijective (LinearMap.coprod i j) := ⟨hφinj, hφsurj⟩
  refine ⟨j, hjeq, hπj, LinearEquiv.ofBijective (LinearMap.coprod i j) hbij,
    fun v w => rfl, fun g v w => ?_⟩
  change LinearMap.coprod i j (_, _) = ρ g (LinearMap.coprod i j (v, w))
  rw [LinearMap.coprod_apply, LinearMap.coprod_apply, hi, hjeq, map_add]

end CFSG.LocalAnalysis.SteinbergBV
