module

public import CFSG.Quasithin.Background.JonesParshallBasic
public import CFSG.Quasithin.Background.A1cModuleDefs

public section

namespace CFSG.Quasithin

open CFSG.Quasithin.JonesParshall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

section ExtDual

variable {Γ : Type*} [Group Γ] {M Q : Type*} [AddCommGroup M] [Module (ZMod 2) M] [AddCommGroup Q]
  [Module (ZMod 2) Q]

@[expose] def extTwist (ρ : Representation (ZMod 2) Γ M) (ρQ : Representation (ZMod 2) Γ Q)
    (s : Q →ₗ[ZMod 2] M) (γ : Γ) : Q →ₗ[ZMod 2] M :=
  (ρ γ).comp (s.comp (ρQ γ⁻¹)) - s

private theorem extTwist_apply (ρ : Representation (ZMod 2) Γ M) (ρQ : Representation (ZMod 2) Γ Q)
    (s : Q →ₗ[ZMod 2] M) (γ : Γ) (x : Q) :
    extTwist ρ ρQ s γ x = ρ γ (s (ρQ γ⁻¹ x)) - s x := rfl

variable (ρ : Representation (ZMod 2) Γ M) (ρQ : Representation (ZMod 2) Γ Q)
  (q : M →ₗ[ZMod 2] Q) (s : Q →ₗ[ZMod 2] M)

private theorem q_extTwist (hqρ : ∀ γ m, q (ρ γ m) = ρQ γ (q m)) (hs : ∀ x, q (s x) = x) (γ : Γ) (x : Q) :
    q (extTwist ρ ρQ s γ x) = 0 := by
  rw [extTwist_apply, map_sub, hqρ, hs, hs, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel,
    map_one, Module.End.one_apply, sub_self]

private theorem extTwist_mul (hqρ : ∀ γ m, q (ρ γ m) = ρQ γ (q m)) (hs : ∀ x, q (s x) = x)
    (hZ : ∀ γ, ∀ m, q m = 0 → ρ γ m = m) (γ δ : Γ) (x : Q) :
    extTwist ρ ρQ s (γ * δ) x = extTwist ρ ρQ s γ x + extTwist ρ ρQ s δ (ρQ γ⁻¹ x) := by
  have h1 := q_extTwist ρ ρQ q s hqρ hs δ (ρQ γ⁻¹ x)
  have h2 := hZ γ _ h1
  rw [extTwist_apply] at h2
  simp only [extTwist_apply]
  have e1 : ρQ (γ * δ)⁻¹ x = ρQ δ⁻¹ (ρQ γ⁻¹ x) := by
    rw [mul_inv_rev, map_mul, Module.End.mul_apply]
  rw [e1, map_mul, Module.End.mul_apply]
  have e2 : ρ γ (ρ δ (s (ρQ δ⁻¹ (ρQ γ⁻¹ x)))) =
      ρ γ (ρ δ (s (ρQ δ⁻¹ (ρQ γ⁻¹ x))) - s (ρQ γ⁻¹ x)) + ρ γ (s (ρQ γ⁻¹ x)) := by
    rw [map_sub]
    abel
  rw [e2, h2]
  abel

@[expose] def extCocycle (ψ : M →ₗ[ZMod 2] ZMod 2) (γ : Γ) : Module.Dual (ZMod 2) Q :=
  ψ.comp (extTwist ρ ρQ s γ)

private theorem extCocycle_mem (hqρ : ∀ γ m, q (ρ γ m) = ρQ γ (q m)) (hs : ∀ x, q (s x) = x)
    (hZ : ∀ γ, ∀ m, q m = 0 → ρ γ m = m) (ψ : M →ₗ[ZMod 2] ZMod 2) :
    extCocycle ρ ρQ s ψ ∈ Z1 (Representation.dual ρQ) := by
  intro γ δ
  ext x
  simp only [extCocycle, LinearMap.comp_apply, LinearMap.add_apply, Representation.dual_apply,
    Module.Dual.transpose_apply]
  rw [extTwist_mul ρ ρQ q s hqρ hs hZ, map_add]

private theorem extCocycle_add (ψ ψ' : M →ₗ[ZMod 2] ZMod 2) (γ : Γ) :
    extCocycle ρ ρQ s (ψ + ψ') γ = extCocycle ρ ρQ s ψ γ + extCocycle ρ ρQ s ψ' γ := by
  ext x
  simp [extCocycle]

private theorem extCocycle_smul (c : ZMod 2) (ψ : M →ₗ[ZMod 2] ZMod 2) (γ : Γ) :
    extCocycle ρ ρQ s (c • ψ) γ = c • extCocycle ρ ρQ s ψ γ := by
  ext x
  simp [extCocycle]

private theorem rep_inv_apply (ρQ : Representation (ZMod 2) Γ Q) (γ : Γ) (y : Q) :
    ρQ γ⁻¹ (ρQ γ y) = y := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

private theorem extCocycle_mem_B1 (hqρ : ∀ γ m, q (ρ γ m) = ρQ γ (q m)) (hs : ∀ x, q (s x) = x)
    (hZ : ∀ γ, ∀ m, q m = 0 → ρ γ m = m)
    (hperf : ∀ ψ : M →ₗ[ZMod 2] ZMod 2, (∀ γ m, ψ (ρ γ m) = ψ m) → ψ = 0)
    (ψ : M →ₗ[ZMod 2] ZMod 2)
    (h : extCocycle ρ ρQ s ψ ∈ B1 (Representation.dual ρQ)) : ∀ m, q m = 0 → ψ m = 0 := by
  obtain ⟨l, hl⟩ := h
  have hl' : ∀ γ x, ψ (extTwist ρ ρQ s γ x) = l (ρQ γ⁻¹ x) - l x := by
    intro γ x
    have := congrArg (fun f => f γ x) hl
    simp only [coboundary, LinearMap.coe_mk, AddHom.coe_mk, Representation.dual_apply,
      LinearMap.sub_apply, Module.Dual.transpose_apply, LinearMap.comp_apply, extCocycle] at this
    exact this.symm
  let ψ' : M →ₗ[ZMod 2] ZMod 2 := ψ - ψ.comp (s.comp q) + l.comp q
  have hinv : ∀ γ m, ψ' (ρ γ m) = ψ' m := by
    intro γ m
    have hm0 : q (m - s (q m)) = 0 := by rw [map_sub, hs, sub_self]
    have hfix := hZ γ _ hm0
    have h1 := hl' γ (ρQ γ (q m))
    rw [extTwist_apply, rep_inv_apply, map_sub] at h1
    have hA : ψ (ρ γ m) = ψ m - ψ (s (q m)) + ψ (ρ γ (s (q m))) := by
      have e : ρ γ m = (m - s (q m)) + ρ γ (s (q m)) := by
        have : m = (m - s (q m)) + s (q m) := by abel
        conv_lhs => rw [this]
        rw [map_add, hfix]
      rw [e, map_add, map_sub]
    simp only [ψ', LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply, hqρ, hA]
    linear_combination (norm := abel_nf) h1
  have h0 := hperf ψ' hinv
  intro m hm
  have := LinearMap.congr_fun h0 m
  simpa [ψ', hm] using this

theorem finrank_ker_le_finrank_H1_dual [Finite Γ] [Finite M] [Finite Q]
    (hq : Function.Surjective q) (hqρ : ∀ γ m, q (ρ γ m) = ρQ γ (q m))
    (hZ : ∀ γ, ∀ m, q m = 0 → ρ γ m = m)
    (hperf : ∀ ψ : M →ₗ[ZMod 2] ZMod 2, (∀ γ m, ψ (ρ γ m) = ψ m) → ψ = 0) :
    Module.finrank (ZMod 2) (LinearMap.ker q) ≤
      Module.finrank (ZMod 2) (H1 (Representation.dual ρQ)) := by
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective q (LinearMap.range_eq_top.mpr hq)
  have hs' : ∀ x, q (s x) = x := fun x => LinearMap.congr_fun hs x
  let Θ0 : Module.Dual (ZMod 2) M →ₗ[ZMod 2] (Γ → Module.Dual (ZMod 2) Q) :=
    { toFun := fun ψ γ => extCocycle ρ ρQ s ψ γ
      map_add' := fun ψ ψ' => funext fun γ => extCocycle_add ρ ρQ s ψ ψ' γ
      map_smul' := fun c ψ => funext fun γ => extCocycle_smul ρ ρQ s c ψ γ }
  let Θ1 : Module.Dual (ZMod 2) M →ₗ[ZMod 2] Z1 (Representation.dual ρQ) :=
    Θ0.codRestrict _ (fun ψ => extCocycle_mem ρ ρQ q s hqρ hs' hZ ψ)
  let Θ : Module.Dual (ZMod 2) M →ₗ[ZMod 2] H1 (Representation.dual ρQ) :=
    (Submodule.mkQ _).comp Θ1
  have hker : LinearMap.ker Θ ≤ (LinearMap.ker q).dualAnnihilator := by
    intro ψ hψ
    rw [LinearMap.mem_ker] at hψ
    have h1 : Θ1 ψ ∈ (B1 (Representation.dual ρQ)).comap (Z1 (Representation.dual ρQ)).subtype :=
      (Submodule.Quotient.mk_eq_zero _).mp hψ
    have h2 : extCocycle ρ ρQ s ψ ∈ B1 (Representation.dual ρQ) := h1
    rw [Submodule.mem_dualAnnihilator]
    intro m hm
    exact extCocycle_mem_B1 ρ ρQ q s hqρ hs' hZ hperf ψ h2 m hm
  have : Module.Finite (ZMod 2) M := Module.Finite.of_finite
  have : Finite (Γ → Module.Dual (ZMod 2) Q) := by
    have : Module.Finite (ZMod 2) Q := Module.Finite.of_finite
    have : Finite (Module.Dual (ZMod 2) Q) := Module.finite_of_finite (ZMod 2)
    exact Pi.finite
  have : Finite (H1 (Representation.dual ρQ)) :=
    Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  have : Module.Finite (ZMod 2) (H1 (Representation.dual ρQ)) := Module.Finite.of_finite
  have hrn := LinearMap.finrank_range_add_finrank_ker Θ
  have hann := Subspace.finrank_add_finrank_dualAnnihilator_eq (LinearMap.ker q)
  have hdual : Module.finrank (ZMod 2) (Module.Dual (ZMod 2) M) = Module.finrank (ZMod 2) M :=
    Subspace.dual_finrank_eq
  have hmono := Submodule.finrank_mono hker
  have hle := Submodule.finrank_le (LinearMap.range Θ)
  omega

end ExtDual

section Bridge

variable {W : Type} [CommGroup W]

theorem card_le_pow_finrank_H1_dual [Finite W] (hexp : ∀ w : W, w ^ 2 = 1) {Γ : Type} [Group Γ]
    [Finite Γ] (L : Subgroup (MulAut W)) (V Z : Subgroup W) (hZV : Z ≤ V)
    (hZfix : ∀ z ∈ Z, ∀ x ∈ L, x z = z) (hinv : ∀ x ∈ L, ∀ v ∈ V, x v ∈ V)
    (hcomm : XMod.commOf ↥L V = V) (π : Γ →* ↥L) (hπ : Function.Surjective π)
    {Q : Type} [AddCommGroup Q] [Module (ZMod 2) Q] [Finite Q]
    (ρQ : Representation (ZMod 2) Γ Q) (β : ↥V →* Multiplicative Q)
    (hβs : Function.Surjective β) (hβk : ∀ v : ↥V, β v = 1 ↔ (v : W) ∈ Z)
    (hβe : ∀ (γ : Γ) (v : ↥V) (hv : (π γ : MulAut W) (v : W) ∈ V),
      β ⟨(π γ : MulAut W) (v : W), hv⟩ =
        Multiplicative.ofAdd (ρQ γ (Multiplicative.toAdd (β v)))) :
    Nat.card ↥Z ≤ 2 ^ Module.finrank (ZMod 2) (H1 (Representation.dual ρQ)) := by
  classical
  have h2 : ∀ x : Additive ↥V, (2 : ℕ) • x = 0 := by
    intro x
    apply Multiplicative.ofAdd.injective
    have := hexp ((Additive.toMul x : ↥V) : W)
    show (Additive.toMul x) ^ 2 = 1
    exact Subtype.ext (by simpa using this)
  let _ : Module (ZMod 2) (Additive ↥V) := AddCommGroup.zmodModule h2
  have hinvπ : ∀ (γ : Γ) (v : W), v ∈ V → (π γ : MulAut W) v ∈ V :=
    fun γ v hv => hinv _ (π γ).2 v hv
  let actHom : Γ → (↥V →* ↥V) := fun γ =>
    { toFun := fun v => ⟨(π γ : MulAut W) (v : W), hinvπ γ v v.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp }
  have actHom_mul : ∀ γ δ v, actHom (γ * δ) v = actHom γ (actHom δ v) := by
    intro γ δ v
    ext
    simp [actHom]
  have actHom_one : ∀ v, actHom 1 v = v := by
    intro v
    ext
    simp [actHom]
  let ρ : Representation (ZMod 2) Γ (Additive ↥V) :=
    { toFun := fun γ => AddMonoidHom.toZModLinearMap 2 (MonoidHom.toAdditive (actHom γ))
      map_one' := by
        ext m
        simp [actHom_one]
      map_mul' := fun γ δ => by
        ext m
        simp [actHom_mul] }
  let qa : Additive ↥V →+ Q :=
    { toFun := fun m => Multiplicative.toAdd (β (Additive.toMul m))
      map_zero' := by simp
      map_add' := fun a b => by simp [map_mul] }
  let q : Additive ↥V →ₗ[ZMod 2] Q := AddMonoidHom.toZModLinearMap 2 qa
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨v, hv⟩ := hβs (Multiplicative.ofAdd y)
    exact ⟨Additive.ofMul v, by simpa [q, qa] using congrArg Multiplicative.toAdd hv⟩
  have hqρ : ∀ γ m, q (ρ γ m) = ρQ γ (q m) := by
    intro γ m
    have := hβe γ (Additive.toMul m) (hinvπ γ _ (Additive.toMul m).2)
    simpa [q, qa, ρ, actHom] using congrArg Multiplicative.toAdd this
  have hZ : ∀ γ, ∀ m, q m = 0 → ρ γ m = m := by
    intro γ m hm
    have h1 : β (Additive.toMul m) = 1 := by
      have : Multiplicative.toAdd (β (Additive.toMul m)) = 0 := hm
      exact Multiplicative.toAdd.injective (by simpa using this)
    have h2' := hZfix _ ((hβk _).mp h1) _ (π γ).2
    apply Additive.toMul.injective
    ext
    simpa [ρ, actHom] using h2'
  have hperf : ∀ ψ : Additive ↥V →ₗ[ZMod 2] ZMod 2, (∀ γ m, ψ (ρ γ m) = ψ m) → ψ = 0 := by
    intro ψ hψ
    have key : ∀ v : W, v ∈ XMod.commOf ↥L V → ∀ hv : v ∈ V, ψ (Additive.ofMul ⟨v, hv⟩) = 0 := by
      intro v hv
      induction hv using Subgroup.closure_induction with
      | mem c hc =>
        obtain ⟨a, l, hl, rfl⟩ := hc
        intro hcV
        obtain ⟨γ, rfl⟩ := hπ a
        have h1 := hψ γ (Additive.ofMul ⟨l, hl⟩)
        have e : Additive.ofMul (⟨((π γ : ↥L) • l) * l⁻¹, hcV⟩ : ↥V) =
            ρ γ (Additive.ofMul ⟨l, hl⟩) - Additive.ofMul ⟨l, hl⟩ := by
          apply Additive.toMul.injective
          ext
          simp [ρ, actHom]
          rw [div_eq_mul_inv]
          rfl
        rw [e, map_sub, h1, sub_self]
      | one =>
        intro hv
        have : (⟨(1 : W), hv⟩ : ↥V) = 1 := rfl
        rw [this]
        exact map_zero ψ
      | mul x y hx hy ihx ihy =>
        intro hxy
        have hxV : x ∈ V := by rw [← hcomm]; exact hx
        have hyV : y ∈ V := by rw [← hcomm]; exact hy
        have e : Additive.ofMul (⟨x * y, hxy⟩ : ↥V) =
            Additive.ofMul ⟨x, hxV⟩ + Additive.ofMul ⟨y, hyV⟩ := rfl
        rw [e, map_add, ihx hxV, ihy hyV, add_zero]
      | inv x hx ih =>
        intro hx'
        have hxV : x ∈ V := by rw [← hcomm]; exact hx
        have e : Additive.ofMul (⟨x⁻¹, hx'⟩ : ↥V) = -Additive.ofMul ⟨x, hxV⟩ := rfl
        rw [e, map_neg, ih hxV, neg_zero]
    ext m
    simp only [LinearMap.zero_apply]
    have hm : ((Additive.toMul m : ↥V) : W) ∈ XMod.commOf ↥L V := by
      rw [hcomm]
      exact (Additive.toMul m).2
    exact key _ hm (Additive.toMul m).2
  have hfin := finrank_ker_le_finrank_H1_dual ρ ρQ q hq hqρ hZ hperf
  have hker : Nat.card ↥Z = Nat.card ↥(LinearMap.ker q) := by
    apply Nat.card_congr
    refine
      { toFun := fun z => ⟨Additive.ofMul ⟨(z : W), hZV z.2⟩, ?_⟩
        invFun := fun m => ⟨((Additive.toMul (m : Additive ↥V) : ↥V) : W), ?_⟩
        left_inv := fun z => rfl
        right_inv := fun m => by
          apply Subtype.ext
          rfl }
    · rw [LinearMap.mem_ker]
      have : β ⟨(z : W), hZV z.2⟩ = 1 := (hβk _).mpr z.2
      show Multiplicative.toAdd (β ⟨(z : W), hZV z.2⟩) = 0
      rw [this]
      rfl
    · have hm : q (m : Additive ↥V) = 0 := m.2
      have h1 : β (Additive.toMul (m : Additive ↥V)) = 1 := by
        have : Multiplicative.toAdd (β (Additive.toMul (m : Additive ↥V))) = 0 := hm
        exact Multiplicative.toAdd.injective (by simpa using this)
      exact (hβk _).mp h1
  have hpow := FiniteField.pow_finrank_eq_natCard 2 ↥(LinearMap.ker q)
  rw [hker, ← hpow]
  exact Nat.pow_le_pow_right (by norm_num) hfin

end Bridge

end CFSG.Quasithin
