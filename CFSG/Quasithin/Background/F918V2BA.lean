module

public import CFSG.Quasithin.Background.A1cModuleDefs
public import CFSG.Quasithin.Background.F918X0

import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin.Z391

open scoped Pointwise

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]

@[expose] def v2bSmulEquiv (γ : Γ) (P : Subgroup Q) : ↥P ≃* ↥(γ • P) where
  toFun x := ⟨γ • (x : Q), Subgroup.smul_mem_pointwise_smul _ _ _ x.2⟩
  invFun y := ⟨γ⁻¹ • (y : Q), Subgroup.mem_pointwise_smul_iff_inv_smul_mem.1 y.2⟩
  left_inv x := Subtype.ext (inv_smul_smul γ (x : Q))
  right_inv y := Subtype.ext (smul_inv_smul γ (y : Q))
  map_mul' x y := Subtype.ext (smul_mul' γ (x : Q) (y : Q))

theorem v2b_coe_smulEquiv_symm (γ : Γ) (P : Subgroup Q) (y : ↥(γ • P)) :
    (((v2bSmulEquiv γ P).symm y : ↥P) : Q) = γ⁻¹ • (y : Q) := rfl

@[expose] def v2bActHom (Λ : Subgroup Γ) (P : Subgroup Q) (hP : ∀ l ∈ Λ, ∀ x ∈ P, l • x ∈ P) :
    ↥Λ →* MulAut ↥P where
  toFun l :=
    { toFun := fun x => ⟨(l : Γ) • (x : Q), hP l l.2 x x.2⟩
      invFun := fun x => ⟨(l : Γ)⁻¹ • (x : Q), hP l⁻¹ l⁻¹.2 x x.2⟩
      left_inv := fun x => Subtype.ext (inv_smul_smul (l : Γ) (x : Q))
      right_inv := fun x => Subtype.ext (smul_inv_smul (l : Γ) (x : Q))
      map_mul' := fun x y => Subtype.ext (smul_mul' (l : Γ) (x : Q) (y : Q)) }
  map_one' := MulEquiv.ext fun x => Subtype.ext (one_smul Γ (x : Q))
  map_mul' := fun a b => MulEquiv.ext fun x => Subtype.ext (mul_smul (a : Γ) (b : Γ) (x : Q))

theorem v2b_coe_actHom (Λ : Subgroup Γ) (P : Subgroup Q) (hP : ∀ l ∈ Λ, ∀ x ∈ P, l • x ∈ P)
    (l : ↥Λ) (x : ↥P) : ((v2bActHom Λ P hP l x : ↥P) : Q) = (l : Γ) • (x : Q) := rfl

theorem iso_realized_of_iso {Λ : Subgroup Γ} (hΛ : ∀ g : Γ, ∀ l ∈ Λ, g * l * g⁻¹ ∈ Λ)
    {P : Subgroup Q} {γ : Γ} (hiso : XMod.Iso ↥Λ (γ • P) P) :
    ∃ h : ↥P ≃* ↥P, ∀ (l : ↥Λ) (x y : ↥P), l • (x : Q) = (y : Q) →
      (γ * (l : Γ) * γ⁻¹) • ((h x : ↥P) : Q) = ((h y : ↥P) : Q) := by
  obtain ⟨φ, hφ⟩ := hiso
  refine ⟨(v2bSmulEquiv γ P).trans φ, fun l x y hxy => ?_⟩
  have hl : γ * (l : Γ) * γ⁻¹ ∈ Λ := hΛ γ l l.2
  refine hφ ⟨γ * (l : Γ) * γ⁻¹, hl⟩ (v2bSmulEquiv γ P x) (v2bSmulEquiv γ P y) ?_
  show (γ * (l : Γ) * γ⁻¹) • (γ • (x : Q)) = γ • (y : Q)
  rw [← hxy, mul_smul, mul_smul, inv_smul_smul]
  rfl

theorem iso_of_twist {Λ : Subgroup Γ} (hΛ : ∀ g : Γ, ∀ l ∈ Λ, g * l * g⁻¹ ∈ Λ)
    {P : Subgroup Q} {γ γ' : Γ} (h : ↥P ≃* ↥P)
    (hh : ∀ (l : ↥Λ) (x y : ↥P), l • (x : Q) = (y : Q) →
      ((γ'⁻¹ * γ) * (l : Γ) * (γ'⁻¹ * γ)⁻¹) • ((h x : ↥P) : Q) = ((h y : ↥P) : Q)) :
    XMod.Iso ↥Λ (γ • P) (γ' • P) := by
  refine ⟨((v2bSmulEquiv γ P).symm.trans h).trans (v2bSmulEquiv γ' P), fun a y₁ y₂ hy => ?_⟩
  set x₁ := (v2bSmulEquiv γ P).symm y₁ with hx₁
  set x₂ := (v2bSmulEquiv γ P).symm y₂ with hx₂
  have hy₁ : (y₁ : Q) = γ • (x₁ : Q) := by
    rw [hx₁, v2b_coe_smulEquiv_symm, smul_inv_smul]
  have hy₂ : (y₂ : Q) = γ • (x₂ : Q) := by
    rw [hx₂, v2b_coe_smulEquiv_symm, smul_inv_smul]
  have hl : γ⁻¹ * (a : Γ) * γ ∈ Λ := by simpa using hΛ γ⁻¹ a a.2
  have hlx : (⟨γ⁻¹ * (a : Γ) * γ, hl⟩ : ↥Λ) • (x₁ : Q) = (x₂ : Q) := by
    have h1 : (a : Γ) • (y₁ : Q) = (y₂ : Q) := hy
    rw [hy₁, hy₂] at h1
    show (γ⁻¹ * (a : Γ) * γ) • (x₁ : Q) = (x₂ : Q)
    calc (γ⁻¹ * (a : Γ) * γ) • (x₁ : Q) = γ⁻¹ • ((a : Γ) • γ • (x₁ : Q)) := by
          rw [mul_smul, mul_smul]
      _ = γ⁻¹ • (γ • (x₂ : Q)) := by rw [h1]
      _ = x₂ := inv_smul_smul γ _
  have key := hh ⟨_, hl⟩ x₁ x₂ hlx
  have e : γ'⁻¹ * γ * (γ⁻¹ * (a : Γ) * γ) * (γ'⁻¹ * γ)⁻¹ = γ'⁻¹ * (a : Γ) * γ' := by group
  show (a : Γ) • (γ' • ((h x₁ : ↥P) : Q)) = γ' • ((h x₂ : ↥P) : Q)
  rw [e] at key
  calc (a : Γ) • (γ' • ((h x₁ : ↥P) : Q)) = γ' • ((γ'⁻¹ * (a : Γ) * γ') • ((h x₁ : ↥P) : Q)) := by
        rw [mul_smul, mul_smul, smul_inv_smul]
    _ = γ' • ((h x₂ : ↥P) : Q) := by rw [key]

theorem v2b_exists_mem_of_index_le_two {G : Type*} [Group G] {R : Subgroup G}
    (hR : R.index ≤ 2) (hne : R.index ≠ 0) (a b c : G) :
    a⁻¹ * b ∈ R ∨ a⁻¹ * c ∈ R ∨ b⁻¹ * c ∈ R := by
  by_cases h1 : a⁻¹ * b ∈ R
  · exact Or.inl h1
  by_cases h2 : a⁻¹ * c ∈ R
  · exact Or.inr (Or.inl h2)
  right; right
  have h3 : R.index = 2 := by
    rcases Nat.lt_or_ge R.index 2 with hlt | hge
    · have h1i : R.index = 1 := by omega
      exact absurd (Subgroup.index_eq_one.mp h1i ▸ Subgroup.mem_top _) h1
    · omega
  have : b⁻¹ * c = (a⁻¹ * b)⁻¹ * (a⁻¹ * c) := by group
  rw [this]
  exact (Subgroup.mul_mem_iff_of_index_two h3).mpr
    (iff_of_false (fun h => h1 (R.inv_mem_iff.mp h)) h2)

section Pigeonhole

variable {Λ : Subgroup Γ} (hΛ : ∀ g : Γ, ∀ l ∈ Λ, g * l * g⁻¹ ∈ Λ) {P : Subgroup Q}
  (hP : ∀ l ∈ Λ, ∀ x ∈ P, l • x ∈ P)

include hΛ

@[expose] noncomputable def v2bTwistAut (hinj : Function.Injective (v2bActHom Λ P hP)) :
    Γ →* MulAut ↥(v2bActHom Λ P hP).range :=
  haveI : Λ.Normal := ⟨fun n hn g => hΛ g n hn⟩
  (MulAut.congr (MonoidHom.ofInjective hinj)).toMonoidHom.comp MulAut.conjNormal

theorem v2b_twistAut_apply (hinj : Function.Injective (v2bActHom Λ P hP)) (δ : Γ) (l : ↥Λ) :
    (((v2bTwistAut hΛ hP hinj δ (MonoidHom.ofInjective hinj l) : ↥(v2bActHom Λ P hP).range) :
        MulAut ↥P)) = v2bActHom Λ P hP ⟨δ * (l : Γ) * δ⁻¹, hΛ δ l l.2⟩ := by
  have : Λ.Normal := ⟨fun n hn g => hΛ g n hn⟩
  show (((MulAut.congr (MonoidHom.ofInjective hinj)) (MulAut.conjNormal δ))
    (MonoidHom.ofInjective hinj l) : MulAut ↥P) = _
  rw [MulAut.congr_apply]
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rw [MonoidHom.ofInjective_apply]
  rfl

theorem iso_of_mem_realized (hinj : Function.Injective (v2bActHom Λ P hP)) {γ γ' : Γ}
    (h : v2bTwistAut hΛ hP hinj (γ'⁻¹ * γ) ∈ F918X.realized (v2bActHom Λ P hP).range) :
    XMod.Iso ↥Λ (γ • P) (γ' • P) := by
  obtain ⟨g, hg⟩ := F918X.mem_realized.1 h
  refine iso_of_twist hΛ g fun l x y hxy => ?_
  have h1 := hg (MonoidHom.ofInjective hinj l)
  rw [v2b_twistAut_apply] at h1
  have h2 := congrArg (fun φ : MulAut ↥P => ((φ (g x) : ↥P) : Q)) h1
  simp only [MulAut.mul_apply, MulAut.inv_apply_self] at h2
  have h3 : ((MonoidHom.ofInjective hinj l : ↥(v2bActHom Λ P hP).range) : MulAut ↥P) x = y := by
    rw [MonoidHom.ofInjective_apply]
    exact Subtype.ext hxy
  rw [h3] at h2
  exact h2.symm

theorem exists_iso_of_twoClass [Finite ↥P] (hinj : Function.Injective (v2bActHom Λ P hP))
    (htc : F918X.TwoClassMod (v2bActHom Λ P hP).range) (γ₀ γ₁ γ₂ : Γ) :
    (XMod.Iso ↥Λ (γ₀ • P) (γ₁ • P) ∧ XMod.Iso ↥Λ (γ₁ • P) (γ₀ • P)) ∨
      (XMod.Iso ↥Λ (γ₀ • P) (γ₂ • P) ∧ XMod.Iso ↥Λ (γ₂ • P) (γ₀ • P)) ∨
      (XMod.Iso ↥Λ (γ₁ • P) (γ₂ • P) ∧ XMod.Iso ↥Λ (γ₂ • P) (γ₁ • P)) := by
  set κ := v2bTwistAut hΛ hP hinj with hκ
  set R := F918X.realized (v2bActHom Λ P hP).range with hR
  have hne : R.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hpair : ∀ a b : Γ, κ (a⁻¹ * b) ∈ R →
      XMod.Iso ↥Λ (a • P) (b • P) ∧ XMod.Iso ↥Λ (b • P) (a • P) := by
    intro a b h
    refine ⟨?_, iso_of_mem_realized hΛ hP hinj h⟩
    refine iso_of_mem_realized hΛ hP hinj ?_
    have : b⁻¹ * a = (a⁻¹ * b)⁻¹ := by group
    rw [this, map_inv]
    exact R.inv_mem h
  have key := v2b_exists_mem_of_index_le_two htc hne (κ γ₀) (κ γ₁) (κ γ₂)
  simp only [← map_inv, ← map_mul] at key
  rcases key with h | h | h
  · exact Or.inl (hpair _ _ h)
  · exact Or.inr (Or.inl (hpair _ _ h))
  · exact Or.inr (Or.inr (hpair _ _ h))

end Pigeonhole

end CFSG.Quasithin.Z391
