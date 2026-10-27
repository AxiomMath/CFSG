module

public import CFSG.Quasithin.Background.F918N0
public import CFSG.Quasithin.Background.SmithB51LnModel

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open CFSG.Quasithin.B5.Ln (mat dmat)
open scoped Matrix

@[expose] def altMat (d : ℕ) : Submodule (ZMod 2) (Matrix (Fin d) (Fin d) (ZMod 2)) where
  carrier := {B | Bᵀ = B ∧ ∀ i, B i i = 0}
  add_mem' := by
    rintro B C ⟨hB1, hB2⟩ ⟨hC1, hC2⟩
    exact ⟨by rw [Matrix.transpose_add, hB1, hC1], fun i => by simp [hB2 i, hC2 i]⟩
  zero_mem' := ⟨Matrix.transpose_zero, fun i => rfl⟩
  smul_mem' := by
    rintro c B ⟨hB1, hB2⟩
    exact ⟨by rw [Matrix.transpose_smul, hB1], fun i => by simp [hB2 i]⟩

theorem mem_altMat {d : ℕ} {B : Matrix (Fin d) (Fin d) (ZMod 2)} :
    B ∈ altMat d ↔ Bᵀ = B ∧ ∀ i, B i i = 0 := Iff.rfl

theorem congr_mem_altMat {d : ℕ} (Q : Matrix (Fin d) (Fin d) (ZMod 2))
    {B : Matrix (Fin d) (Fin d) (ZMod 2)} (hB : B ∈ altMat d) : Q * B * Qᵀ ∈ altMat d := by
  obtain ⟨hB1, hB2⟩ := hB
  refine ⟨?_, fun i => ?_⟩
  · rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hB1, Matrix.mul_assoc]
  · have hsym : ∀ j k, B j k = B k j := fun j k => by
      have := congrFun (congrFun hB1 j) k
      simpa using this.symm
    have h2 : ∀ x : ZMod 2, x + x = 0 := by decide
    have key : (Q * B * Qᵀ) i i = ∑ p : Fin d × Fin d, Q i p.1 * B p.1 p.2 * Q i p.2 := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
      rw [Fintype.sum_prod_type, Finset.sum_comm]
    rw [key]
    refine Finset.sum_involution (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
    · intro p _
      show Q i p.1 * B p.1 p.2 * Q i p.2 + Q i p.2 * B p.2 p.1 * Q i p.1 = 0
      rw [← hsym p.1 p.2]
      have : Q i p.2 * B p.1 p.2 * Q i p.1 = Q i p.1 * B p.1 p.2 * Q i p.2 := by ring
      rw [this]
      exact h2 _
    · intro p _ hp hpp
      apply hp
      have h1 : p.2 = p.1 := (Prod.ext_iff.mp hpp).1
      obtain ⟨a, b⟩ := p
      simp only at h1
      subst h1
      simp [hB2 b]
    · intro p _
      exact Finset.mem_univ _
    · intro p _
      rfl

@[expose] def altMulAct (γ : ↥(StatedSL 5 (ZMod 2))) (B : Multiplicative ↥(altMat 5)) :
    Multiplicative ↥(altMat 5) :=
  Multiplicative.ofAdd ⟨mat γ * ((Multiplicative.toAdd B : ↥(altMat 5)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) *
    (mat γ)ᵀ, congr_mem_altMat _ (Multiplicative.toAdd B).2⟩

@[simp] theorem coe_toAdd_altMulAct (γ : ↥(StatedSL 5 (ZMod 2))) (B : Multiplicative ↥(altMat 5)) :
    (((Multiplicative.toAdd (altMulAct γ B) : ↥(altMat 5))) : Matrix (Fin 5) (Fin 5) (ZMod 2)) =
      mat γ * ((Multiplicative.toAdd B : ↥(altMat 5)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) * (mat γ)ᵀ :=
  rfl

theorem altMulAct_one (B : Multiplicative ↥(altMat 5)) : altMulAct 1 B = B := by
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  simp

theorem altMulAct_mul (γ δ : ↥(StatedSL 5 (ZMod 2))) (B : Multiplicative ↥(altMat 5)) :
    altMulAct (γ * δ) B = altMulAct γ (altMulAct δ B) := by
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  simp [Matrix.transpose_mul, Matrix.mul_assoc]

theorem altMulAct_mul_distrib (γ : ↥(StatedSL 5 (ZMod 2))) (B C : Multiplicative ↥(altMat 5)) :
    altMulAct γ (B * C) = altMulAct γ B * altMulAct γ C := by
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  simp [Matrix.mul_add, Matrix.add_mul]

@[expose] def D35InspExtSq : Prop :=
  ∀ E : Subgroup ↥(StatedSL 5 (ZMod 2)), E ≠ ⊥ → (∀ g ∈ E, ∀ h ∈ E, g * h = h * g) →
    (∀ g ∈ E, g * g = 1) →
    ¬ (2 ^ 10 ≤ Nat.card E *
        Nat.card {B : ↥(altMat 5) //
          ∀ g ∈ E, mat g * (B : Matrix (Fin 5) (Fin 5) (ZMod 2)) * (mat g)ᵀ = B} ∧
      2 ^ 10 ≤ Nat.card E *
        Nat.card {B : ↥(altMat 5) //
          ∀ g ∈ E, dmat g * (B : Matrix (Fin 5) (Fin 5) (ZMod 2)) * (dmat g)ᵀ = B})

@[expose] def D35InspUniq8 : Prop :=
  ∀ (X : Type) [CommGroup X] [Finite X] (Mb Tb Lb : Subgroup (MulAut X)) (V₁ : Subgroup X)
    (A : Subgroup (MulAut X)) (t : MulAut X),
    Z35 Mb Tb Lb V₁ → Mb = Lb → t ∈ Tb → t ∉ stabSub V₁ → A ≤ Tb ⊓ stabSub V₁ →
    A ≤ stabSub (V₁.map t.toMonoidHom) →
    (∃ A₀ : Subgroup (MulAut X),
      B42Case8 (autSub (Lb ⊔ (Tb ⊓ stabSub V₁)) V₁) (autSub Lb V₁) (autSub A₀ V₁)) →
    IsFFStarOffender (autSub (Lb ⊔ (Tb ⊓ stabSub V₁)) V₁) (autSub A V₁) →
    IsFFStarOffender (autSub (Lb ⊔ (Tb ⊓ stabSub (V₁.map t.toMonoidHom))) (V₁.map t.toMonoidHom))
      (autSub A (V₁.map t.toMonoidHom)) → False

@[expose] def D35InspUniq11 : Prop :=
  ∀ (X : Type) [CommGroup X] [Finite X] (Mb Tb Lb : Subgroup (MulAut X)) (V₁ : Subgroup X)
    (A : Subgroup (MulAut X)) (t : MulAut X),
    Z35 Mb Tb Lb V₁ → Mb = Lb → t ∈ Tb → t ∉ stabSub V₁ → A ≤ Tb ⊓ stabSub V₁ →
    A ≤ stabSub (V₁.map t.toMonoidHom) →
    (∃ A₀ : Subgroup (MulAut X),
      B42Case11 (autSub (Lb ⊔ (Tb ⊓ stabSub V₁)) V₁) (autSub Lb V₁) (autSub A₀ V₁)) →
    IsFFStarOffender (autSub (Lb ⊔ (Tb ⊓ stabSub V₁)) V₁) (autSub A V₁) →
    IsFFStarOffender (autSub (Lb ⊔ (Tb ⊓ stabSub (V₁.map t.toMonoidHom))) (V₁.map t.toMonoidHom))
      (autSub A (V₁.map t.toMonoidHom)) → False

theorem d35InspUniq_of_cases (h8 : D35InspUniq8) (h11 : D35InspUniq11) : D35InspUniq := by
  intro X _ _ Mb Tb Lb V₁ A t hZ hML ht htV hA hA2 hcase hoff1 hoff2
  obtain ⟨A₀, h | h⟩ := hcase
  · exact h8 X Mb Tb Lb V₁ A t hZ hML ht htV hA hA2 ⟨A₀, h⟩ hoff1 hoff2
  · exact h11 X Mb Tb Lb V₁ A t hZ hML ht htV hA hA2 ⟨A₀, h⟩ hoff1 hoff2

end CFSG.Quasithin
