module

public import CFSG.Quasithin.Background.SmithB45J2Syl
public import Mathlib.GroupTheory.Sylow
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

public section

namespace CFSG.Quasithin.J2Row

open CFSG.Quasithin.J2Bits CFSG.CharacterTheory.SteinbergBY
open CFSG.CharacterTheory.SteinbergBY.FieldFour
open scoped Matrix

@[expose] noncomputable def conjSub (g : GL6) (B : Subgroup GL6) : Subgroup GL6 :=
  B.map (MulAut.conj g).toMonoidHom

theorem mem_conjSub {g x : GL6} {B : Subgroup GL6} : x ∈ conjSub g B ↔ g⁻¹ * x * g ∈ B := by
  constructor
  · rintro ⟨b, hb, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hb
  · intro h
    refine ⟨g⁻¹ * x * g, h, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

theorem card_conjSub (g : GL6) (B : Subgroup GL6) : Nat.card ↥(conjSub g B) = Nat.card B :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem card_mFix_conjSub (g : GL6) (B : Subgroup GL6) :
    Nat.card ↥(mFix (conjSub g B)) = Nat.card ↥(mFix B) := by
  have hg : ∀ v : V6, ((g⁻¹ : GL6) : M6) *ᵥ ((g : M6) *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hg' : ∀ v : V6, (g : M6) *ᵥ (((g⁻¹ : GL6) : M6) *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  refine (Nat.card_congr
    { toFun := fun v => ⟨((g⁻¹ : GL6) : M6) *ᵥ v, fun b hb => ?_⟩
      invFun := fun v => ⟨(g : M6) *ᵥ v, fun x hx => ?_⟩
      left_inv := fun v => Subtype.ext (hg' v)
      right_inv := fun v => Subtype.ext (hg v) })
  · have h := v.2 (g * b * g⁻¹) (mem_conjSub.mpr (by simpa [mul_assoc] using hb))
    have e : ((g * b * g⁻¹ : GL6) : M6) *ᵥ (v : V6) = (v : V6) := h
    rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at e
    have e2 := congrArg (fun w => ((g⁻¹ : GL6) : M6) *ᵥ w) e
    simp only [hg] at e2
    exact e2
  · have h := v.2 (g⁻¹ * x * g) (mem_conjSub.mp hx)
    have e : ((g⁻¹ * x * g : GL6) : M6) *ᵥ (v : V6) = (v : V6) := h
    rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at e
    have e2 := congrArg (fun w => (g : M6) *ᵥ w) e
    simp only [hg'] at e2
    exact e2

theorem factorization_604800 : (604800 : ℕ).factorization 2 = 7 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.factorization_def _ Nat.prime_two, show (604800 : ℕ) = 2 ^ 7 * 4725 by norm_num,
    padicValNat.mul (by positivity) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num)]

theorem exists_conj_le_S₂ (hcard : Nat.card Γ₆ = 604800) {B : Subgroup GL6} (hBΓ : B ≤ Γ₆)
    (hsq : ∀ x ∈ B, x * x = 1) : ∃ g ∈ Γ₆, conjSub g B ≤ S₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite ↥Γ₆ := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  set S' : Subgroup ↥Γ₆ := S₂.subgroupOf Γ₆ with hS'
  have hS'card : Nat.card S' = 2 ^ (Nat.card ↥Γ₆).factorization 2 := by
    rw [hcard, factorization_604800, hS',
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe S₂_le).toEquiv, card_S₂]
    norm_num
  let P : Sylow 2 ↥Γ₆ := Sylow.ofCard S' hS'card
  set B' : Subgroup ↥Γ₆ := B.subgroupOf Γ₆ with hB'
  have hB'p : IsPGroup 2 B' := fun x => ⟨1, by
    apply Subtype.ext
    apply Subtype.ext
    have h := hsq ((x : ↥Γ₆) : GL6) (Subgroup.mem_subgroupOf.mp x.2)
    simpa [pow_one, sq] using h⟩
  obtain ⟨Q, hBQ⟩ := hB'p.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥Γ₆ Q P
  refine ⟨g, g.2, ?_⟩
  rintro _ ⟨b, hb, rfl⟩
  have hbQ : (⟨b, hBΓ hb⟩ : ↥Γ₆) ∈ (Q : Subgroup ↥Γ₆) := hBQ (Subgroup.mem_subgroupOf.mpr hb)
  have hmem : g * ⟨b, hBΓ hb⟩ * g⁻¹ ∈ ((g • Q : Sylow 2 ↥Γ₆) : Subgroup ↥Γ₆) := by
    rw [Sylow.coe_subgroup_smul]
    exact ⟨_, hbQ, rfl⟩
  rw [hg] at hmem
  have h2 : (g * ⟨b, hBΓ hb⟩ * g⁻¹ : ↥Γ₆) ∈ S' := hmem
  rw [hS', Subgroup.mem_subgroupOf] at h2
  simpa [MulAut.conj_apply] using h2

theorem inner_bounds (hcard : Nat.card Γ₆ = 604800) {B : Subgroup GL6} (hBΓ : B ≤ Γ₆)
    (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hsq : ∀ x ∈ B, x * x = 1) :
    (2 ≤ Nat.card B → Nat.card ↥(mFix B) ≤ 256) ∧ (3 ≤ Nat.card B → Nat.card ↥(mFix B) ≤ 64) ∧
      (5 ≤ Nat.card B → Nat.card ↥(mFix B) ≤ 16 ∧
        ∃ x ∈ B, ∃ y ∈ B, ((y : M6) - 1) * ((x : M6) - 1) ≠ 0) := by
  obtain ⟨g, -, hgS⟩ := exists_conj_le_S₂ hcard hBΓ hsq
  set C := conjSub g B with hC
  have hCc : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x := by
    intro x hx y hy
    have h := hcomm _ (mem_conjSub.mp hx) _ (mem_conjSub.mp hy)
    have e : x * y = g * ((g⁻¹ * x * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
    have e' : y * x = g * ((g⁻¹ * y * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
    rw [e, e', h]
  have hCs : ∀ x ∈ C, x * x = 1 := by
    intro x hx
    have h := hsq _ (mem_conjSub.mp hx)
    have e : x * x = g * ((g⁻¹ * x * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
    rw [e, h, mul_one, mul_inv_cancel]
  have hcardC : Nat.card C = Nat.card B := card_conjSub g B
  have hfixC : Nat.card ↥(mFix C) = Nat.card ↥(mFix B) := card_mFix_conjSub g B
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [← hfixC]
    exact card_mFix_of_two hgS hCs (hcardC ▸ h)
  · rw [← hfixC]
    exact card_mFix_of_three hgS hCs (hcardC ▸ h)
  · obtain ⟨h16, x, hx, y, hy, hxy⟩ := card_mFix_of_five hgS hCc hCs (hcardC ▸ h)
    refine ⟨hfixC ▸ h16, g⁻¹ * x * g, mem_conjSub.mp hx, g⁻¹ * y * g, mem_conjSub.mp hy,
      fun h0 => hxy ?_⟩
    have hGG : ∀ M : M6, (g : M6) * (((g⁻¹ : GL6) : M6) * M) = M := fun M => by
      rw [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
    have hGG1 : (g : M6) * ((g⁻¹ : GL6) : M6) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hc : ∀ z : GL6, ((g⁻¹ * z * g : GL6) : M6) - 1 =
        ((g⁻¹ : GL6) : M6) * ((z : M6) - 1) * (g : M6) := fun z => by
      have e1 : ((g⁻¹ : GL6) : M6) * (g : M6) = 1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, e1, Units.val_mul, Units.val_mul]
    rw [hc, hc] at h0
    have h2 := congrArg (fun M => (g : M6) * M * ((g⁻¹ : GL6) : M6)) h0
    simp only [Matrix.mul_assoc, Matrix.mul_zero, Matrix.zero_mul, hGG, hGG1,
      Matrix.mul_one] at h2
    exact h2

end CFSG.Quasithin.J2Row
