module

public import CFSG.Quasithin.Background.C116Two.NatLin2Lines
public import CFSG.Quasithin.Background.C116Two.NatLin2Basic

public section

namespace CFSG.Quasithin.C116Two

open CFSG.QuasithinUnique CFSG.Open

private theorem card_le_two_mul_of_cosets {G : Type} [Group G] [Finite G] (J K : Subgroup G) (x₀ : G)
    (hJ : ∀ x ∈ J, x ∈ K ∨ x₀ * x ∈ K) : Nat.card J ≤ 2 * Nat.card K := by
  classical
  let f : J → Bool × K := fun x =>
    if hx : (x : G) ∈ K then (true, ⟨(x : G), hx⟩)
    else (false, ⟨x₀ * (x : G), (hJ x x.2).resolve_left hx⟩)
  have hf : Function.Injective f := by
    intro x y hxy
    by_cases hx : (x : G) ∈ K <;> by_cases hy : (y : G) ∈ K <;> simp [f, hx, hy] at hxy
    · exact hxy
    · exact hxy
  have h := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at h

private theorem three_involutions_false {F : Type} [Field F] [Finite F] (x y z : F ≃+* F)
    (hx : ∀ c, x (x c) = c) (hy : ∀ c, y (y c) = c) (hz : ∀ c, z (z c) = c)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) : False := by
  haveI : Finite (F ≃+* F) := Finite.of_injective (fun σ : F ≃+* F => (σ : F → F))
    (fun a b h => RingEquiv.ext fun c => congrFun h c)
  have hcard := card_involutions_le_two F
  let v : Fin 3 → {σ : F ≃+* F // ∀ c, σ (σ c) = c} := ![⟨x, hx⟩, ⟨y, hy⟩, ⟨z, hz⟩]
  have hv : Function.Injective v := by
    intro i j hij
    have h' := congrArg Subtype.val hij
    fin_cases i <;> fin_cases j <;> simp [v, hxy, hxz, hyz, hxy.symm, hxz.symm, hyz.symm] at h' ⊢
  have h3 := Nat.card_le_card_of_injective v hv
  rw [Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin] at h3
  omega


theorem exists_linear_subgroup {F : Type} [Field F] [Fintype F] [CharP F 2]
    (B : Subgroup (MulAut (Multiplicative (Fin 2 → F)))) (hB : IsElemAbelian 2 B)
    (hN : ∀ b ∈ B, ∀ l ∈ (slAct F).range, b * l * b⁻¹ ∈ (slAct F).range) :
    ∃ B₁ : Subgroup (MulAut (Multiplicative (Fin 2 → F))), B₁ ≤ B ∧
      (∀ b ∈ B₁, IsSemilinear (RingEquiv.refl F) b) ∧ Nat.card B ≤ 2 * Nat.card B₁ ∧
      (B₁ = B ∨ ∃ φ ∈ B, ∃ σ : F ≃+* F, σ ≠ 1 ∧ (∀ c, σ (σ c) = c) ∧ IsSemilinear σ φ ∧
        φ * φ = 1) := by
  haveI : Finite (Multiplicative (Fin 2 → F)) := inferInstanceAs (Finite (Fin 2 → F))
  haveI : Finite (MulAut (Multiplicative (Fin 2 → F))) := MulEquiv.finite_left
  choose! σ hσ using fun b (hb : b ∈ B) => exists_semilinear_of_normalizer b (hN b hb)
  have hsq1 : ∀ b ∈ B, b * b = 1 := fun b hb => by rw [← sq]; exact hB.2 b hb
  have hone : ∀ τ : F ≃+* F, IsSemilinear τ (1 : MulAut (Multiplicative (Fin 2 → F))) →
      τ = RingEquiv.refl F := fun τ h => semilinear_unique h isSemilinear_one
  have hmul : ∀ x ∈ B, ∀ y ∈ B, σ (x * y) = (σ y).trans (σ x) := fun x hx y hy =>
    semilinear_unique (hσ (x * y) (B.mul_mem hx hy)) (isSemilinear_mul (hσ x hx) (hσ y hy))
  have hinv : ∀ b ∈ B, ∀ c, σ b (σ b c) = c := by
    intro b hb c
    have h1 : (σ b).trans (σ b) = RingEquiv.refl F := by
      rw [← hmul b hb b hb, hsq1 b hb]
      exact hone _ (hσ 1 B.one_mem)
    have h2 := congrArg (fun τ : F ≃+* F => τ c) h1
    simpa using h2
  let B₁ : Subgroup (MulAut (Multiplicative (Fin 2 → F))) :=
    { carrier := {b | b ∈ B ∧ IsSemilinear (RingEquiv.refl F) b}
      mul_mem' := fun {a b} ha hb => ⟨B.mul_mem ha.1 hb.1, isSemilinear_mul ha.2 hb.2⟩
      one_mem' := ⟨B.one_mem, isSemilinear_one⟩
      inv_mem' := fun {a} ha => ⟨B.inv_mem ha.1, by simpa using isSemilinear_inv ha.2⟩ }
  have hB₁B : B₁ ≤ B := fun b hb => hb.1
  have hlin : ∀ b ∈ B₁, IsSemilinear (RingEquiv.refl F) b := fun b hb => hb.2
  have hmem : ∀ b ∈ B, b ∈ B₁ ↔ σ b = RingEquiv.refl F := fun b hb =>
    ⟨fun h => semilinear_unique (hσ b hb) h.2, fun h => ⟨hb, by rw [← h]; exact hσ b hb⟩⟩
  by_cases hall : ∀ b ∈ B, b ∈ B₁
  · exact ⟨B₁, hB₁B, hlin, card_le_two_mul_of_cosets B B₁ 1 (fun x hx => Or.inl (hall x hx)),
      Or.inl (le_antisymm hB₁B fun b hb => hall b hb)⟩
  · push Not at hall
    obtain ⟨φ, hφB, hφB₁⟩ := hall
    have hσφ : σ φ ≠ RingEquiv.refl F := fun h => hφB₁ ((hmem φ hφB).2 h)
    have hcos : ∀ x ∈ B, x ∈ B₁ ∨ φ * x ∈ B₁ := by
      intro x hx
      by_cases hxB₁ : x ∈ B₁
      · exact Or.inl hxB₁
      · refine Or.inr ?_
        have hσx : σ x ≠ RingEquiv.refl F := fun h => hxB₁ ((hmem x hx).2 h)
        have heq : σ x = σ φ := by
          by_contra hne
          exact three_involutions_false (RingEquiv.refl F) (σ x) (σ φ) (fun c => rfl)
            (hinv x hx) (hinv φ hφB) (Ne.symm hσx) (Ne.symm hσφ) hne
        refine (hmem (φ * x) (B.mul_mem hφB hx)).2 ?_
        rw [hmul φ hφB x hx, heq]
        exact RingEquiv.ext fun c => hinv φ hφB c
    exact ⟨B₁, hB₁B, hlin, card_le_two_mul_of_cosets B B₁ φ hcos,
      Or.inr ⟨φ, hφB, σ φ, hσφ, hinv φ hφB, hσ φ hφB, hsq1 φ hφB⟩⟩

end CFSG.Quasithin.C116Two
