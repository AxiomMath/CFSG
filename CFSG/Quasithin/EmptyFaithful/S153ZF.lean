module

public import CFSG.Quasithin.Background.D2Basic
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Quasithin.Z391

variable {Γ : Type*} [Group Γ]

section Hom

variable {P₁ P₂ : Type*} [CommGroup P₁] [CommGroup P₂] [MulDistribMulAction Γ P₁]
  [MulDistribMulAction Γ P₂]

@[expose] def eqvHom (Λ : Subgroup Γ) : Subgroup (P₁ →* P₂) where
  carrier := {φ | ∀ l ∈ Λ, ∀ p, φ (l • p) = l • φ p}
  one_mem' := fun l _ p => by simp
  mul_mem' := fun {φ ψ} hφ hψ l hl p => by
    simp only [MonoidHom.mul_apply]
    rw [hφ l hl p, hψ l hl p, smul_mul']
  inv_mem' := fun {φ} hφ l hl p => by
    simp only [MonoidHom.inv_apply]
    rw [hφ l hl p, smul_inv']

variable (B Λ : Subgroup Γ) (hBΛ : ∀ b ∈ B, ∀ l ∈ Λ, b * l * b⁻¹ ∈ Λ)

@[expose] def conjHom (b : Γ) (φ : P₁ →* P₂) : P₁ →* P₂ :=
  (MulDistribMulAction.toMonoidHom P₂ b).comp (φ.comp (MulDistribMulAction.toMonoidHom P₁ b⁻¹))

theorem conjHom_apply (b : Γ) (φ : P₁ →* P₂) (p : P₁) : conjHom b φ p = b • φ (b⁻¹ • p) := rfl

include hBΛ in
theorem conjHom_mem (b : B) {φ : P₁ →* P₂} (hφ : φ ∈ eqvHom (P₁ := P₁) (P₂ := P₂) Λ) :
    conjHom (b : Γ) φ ∈ eqvHom (P₁ := P₁) (P₂ := P₂) Λ := by
  intro l hl p
  rw [conjHom_apply, conjHom_apply]
  have h1 : (b : Γ)⁻¹ * l * (b : Γ) ∈ Λ := by
    have := hBΛ (b : Γ)⁻¹ (B.inv_mem b.2) l hl
    simpa using this
  have h2 : (b : Γ)⁻¹ • l • p = ((b : Γ)⁻¹ * l * (b : Γ)) • (b : Γ)⁻¹ • p := by
    rw [smul_smul, smul_smul]
    congr 1
    group
  rw [h2, hφ _ h1, smul_smul, smul_smul]
  congr 1
  group

@[instance_reducible] noncomputable def homAct (hBΛ : ∀ b ∈ B, ∀ l ∈ Λ, b * l * b⁻¹ ∈ Λ) :
    MulAction ↥B ↥(eqvHom (P₁ := P₁) (P₂ := P₂) Λ) where
  smul b φ := ⟨conjHom (b : Γ) φ.1, conjHom_mem B Λ hBΛ b φ.2⟩
  one_smul φ := by
    refine Subtype.ext (MonoidHom.ext fun p => ?_)
    show conjHom (((1 : ↥B)) : Γ) φ.1 p = φ.1 p
    rw [conjHom_apply]
    simp
  mul_smul b b' φ := by
    refine Subtype.ext (MonoidHom.ext fun p => ?_)
    show conjHom (((b * b' : ↥B)) : Γ) φ.1 p = conjHom (b : Γ) (conjHom (b' : Γ) φ.1) p
    simp only [conjHom_apply, Subgroup.coe_mul, mul_inv_rev, mul_smul]

end Hom

theorem exists_fixed_hom {P₁ P₂ : Type*} [CommGroup P₁] [CommGroup P₂] [Finite P₁] [Finite P₂]
    [MulDistribMulAction Γ P₁] [MulDistribMulAction Γ P₂] (hP₂ : ∀ p : P₂, p ^ 2 = 1)
    (Λ B : Subgroup Γ) (hB : IsPGroup 2 B) (hBΛ : ∀ b ∈ B, ∀ l ∈ Λ, b * l * b⁻¹ ∈ Λ)
    (φ₀ : P₁ →* P₂) (hφ₀ : ∀ l ∈ Λ, ∀ p, φ₀ (l • p) = l • φ₀ p) (hne : φ₀ ≠ 1) :
    ∃ φ : P₁ →* P₂, φ ≠ 1 ∧ (∀ l ∈ Λ, ∀ p, φ (l • p) = l • φ p) ∧
      ∀ b ∈ B, ∀ p, φ (b • p) = b • φ p := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfin : Finite (P₁ →* P₂) := DFunLike.finite _
  let E := eqvHom (P₁ := P₁) (P₂ := P₂) Λ
  let _ : MulAction ↥B ↥E := homAct B Λ hBΛ
  have hE2 : ∀ x : ↥E, x ^ 2 = 1 := by
    intro x
    apply Subtype.ext
    ext p
    show (x.1 ^ 2) p = 1
    rw [MonoidHom.pow_apply]
    exact hP₂ _
  have hEp : IsPGroup 2 ↥E := isPGroup_two_of_sq_eq_one hE2
  have hEcard : Nat.card ↥E = 2 ^ rk ↥E := card_eq_two_pow_of_isPGroup hEp
  have hone : (1 : ↥E) ≠ ⟨φ₀, hφ₀⟩ := fun h => hne (congrArg Subtype.val h).symm
  have hnt : 1 < Nat.card ↥E := by
    rw [Finite.one_lt_card_iff_nontrivial]
    exact ⟨⟨1, ⟨φ₀, hφ₀⟩, hone⟩⟩
  have hk : 1 ≤ rk ↥E := by
    by_contra h0
    have : rk ↥E = 0 := by omega
    rw [this] at hEcard
    omega
  have hEeven : Nat.card ↥E % 2 = 0 := by
    rw [hEcard]
    obtain ⟨k, hk'⟩ := Nat.exists_eq_add_of_le hk
    rw [hk', pow_add]
    simp
  have hmod := hB.card_modEq_card_fixedPoints (α := ↥E)
  have hfix1 : (1 : ↥E) ∈ MulAction.fixedPoints ↥B ↥E := by
    rw [MulAction.mem_fixedPoints]
    intro b
    refine Subtype.ext (MonoidHom.ext fun p => ?_)
    show conjHom (b : Γ) (1 : P₁ →* P₂) p = 1
    rw [conjHom_apply]
    simp
  have hfixfin : Finite ↥(MulAction.fixedPoints ↥B ↥E) := inferInstance
  have hfixeven : Nat.card ↥(MulAction.fixedPoints ↥B ↥E) % 2 = 0 := by
    have := hmod
    unfold Nat.ModEq at this
    omega
  have hfixpos : 0 < Nat.card ↥(MulAction.fixedPoints ↥B ↥E) := by
    rw [Nat.card_pos_iff]
    exact ⟨⟨⟨1, hfix1⟩⟩, hfixfin⟩
  have hfix2 : 1 < Nat.card ↥(MulAction.fixedPoints ↥B ↥E) := by omega
  rw [Finite.one_lt_card_iff_nontrivial] at hfix2
  obtain ⟨⟨x, hx⟩, hx1⟩ := exists_ne (⟨1, hfix1⟩ : ↥(MulAction.fixedPoints ↥B ↥E))
  refine ⟨x.1, ?_, x.2, ?_⟩
  · intro h
    apply hx1
    apply Subtype.ext
    apply Subtype.ext
    exact h
  · intro b hb p
    have hb' := (MulAction.mem_fixedPoints.1 hx) ⟨b, hb⟩
    have h1 := congrArg (fun φ : ↥E => φ.1 (b • p)) hb'
    change conjHom b x.1 (b • p) = x.1 (b • p) at h1
    rw [conjHom_apply, inv_smul_smul] at h1
    exact h1.symm

end CFSG.Quasithin.Z391
