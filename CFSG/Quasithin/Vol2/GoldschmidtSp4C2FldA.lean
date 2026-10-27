module

public import Mathlib.FieldTheory.Finite.Extension

public section

namespace CFSG.Quasithin.Ch3E213M.Sp4C2

variable {k : Type} [Field k]

def lineSet (Γ : Subgroup kˣ) : Set k := {y | y = 0 ∨ ∃ γ : Γ, y = ((γ : kˣ) : k)}

def LineAdd (c₀ b₀ : k) (Γ : Subgroup kˣ) (φ : Γ →* kˣ) : Prop :=
  ∀ γ γ' : Γ,
    (∃ δ : Γ, c₀ * ((γ : kˣ) : k) + c₀ * ((γ' : kˣ) : k) = c₀ * ((δ : kˣ) : k) ∧
        b₀ * ((φ γ : kˣ) : k) + b₀ * ((φ γ' : kˣ) : k) = b₀ * ((φ δ : kˣ) : k)) ∨
      (c₀ * ((γ : kˣ) : k) + c₀ * ((γ' : kˣ) : k) = 0 ∧
        b₀ * ((φ γ : kˣ) : k) + b₀ * ((φ γ' : kˣ) : k) = 0)

section Line

variable {c₀ b₀ : k} {Γ : Subgroup kˣ} {φ : Γ →* kˣ}

theorem lineSet_mul {y y' : k} (hy : y ∈ lineSet Γ) (hy' : y' ∈ lineSet Γ) :
    y * y' ∈ lineSet Γ := by
  rcases hy with rfl | ⟨γ, rfl⟩
  · exact Or.inl (zero_mul _)
  rcases hy' with rfl | ⟨γ', rfl⟩
  · exact Or.inl (mul_zero _)
  exact Or.inr ⟨γ * γ', by simp⟩

theorem lineSet_inv {y : k} (hy : y ∈ lineSet Γ) : y⁻¹ ∈ lineSet Γ := by
  rcases hy with rfl | ⟨γ, rfl⟩
  · exact Or.inl inv_zero
  exact Or.inr ⟨γ⁻¹, by simp⟩

theorem lineSet_add (hc₀ : c₀ ≠ 0) (hadd : LineAdd c₀ b₀ Γ φ) {y y' : k} (hy : y ∈ lineSet Γ)
    (hy' : y' ∈ lineSet Γ) : y + y' ∈ lineSet Γ := by
  rcases hy with rfl | ⟨γ, rfl⟩
  · simpa using hy'
  rcases hy' with rfl | ⟨γ', rfl⟩
  · exact Or.inr ⟨γ, by simp⟩
  rcases hadd γ γ' with ⟨δ, hc, -⟩ | ⟨hc, -⟩
  · refine Or.inr ⟨δ, ?_⟩
    exact mul_left_cancel₀ hc₀ (by rw [mul_add]; exact hc)
  · refine Or.inl ?_
    rw [← mul_add] at hc
    exact (mul_eq_zero.1 hc).resolve_left hc₀

def lineField [CharP k 2] (hc₀ : c₀ ≠ 0) (hadd : LineAdd c₀ b₀ Γ φ) : Subfield k where
  carrier := lineSet Γ
  mul_mem' := lineSet_mul
  one_mem' := Or.inr ⟨1, by simp⟩
  add_mem' := lineSet_add hc₀ hadd
  zero_mem' := Or.inl rfl
  neg_mem' := fun {y} hy => by rw [CharTwo.neg_eq]; exact hy
  inv_mem' := fun _ hy => lineSet_inv hy

noncomputable def lineExt (Γ : Subgroup kˣ) (φ : Γ →* kˣ) : k → k :=
  Function.extend (fun γ : Γ => ((γ : kˣ) : k)) (fun γ => ((φ γ : kˣ) : k)) 0

theorem lineExt_coe (γ : Γ) : lineExt Γ φ ((γ : kˣ) : k) = ((φ γ : kˣ) : k) := by
  have hinj : Function.Injective fun γ : Γ => ((γ : kˣ) : k) :=
    fun _ _ h => Subtype.ext (Units.ext h)
  exact hinj.extend_apply _ _ γ

theorem lineExt_zero : lineExt Γ φ 0 = 0 := by
  refine Function.extend_apply' _ _ _ ?_
  rintro ⟨γ, hγ⟩
  exact (γ : kˣ).ne_zero hγ

theorem lineExt_one : lineExt Γ φ 1 = 1 := by
  have := lineExt_coe (φ := φ) 1
  simpa using this

theorem lineExt_mul {y y' : k} (hy : y ∈ lineSet Γ) (hy' : y' ∈ lineSet Γ) :
    lineExt Γ φ (y * y') = lineExt Γ φ y * lineExt Γ φ y' := by
  rcases hy with rfl | ⟨γ, rfl⟩
  · simp [lineExt_zero]
  rcases hy' with rfl | ⟨γ', rfl⟩
  · simp [lineExt_zero]
  have : ((γ : kˣ) : k) * ((γ' : kˣ) : k) = (((γ * γ' : Γ) : kˣ) : k) := by simp
  rw [this, lineExt_coe, lineExt_coe, lineExt_coe]
  simp

theorem lineExt_add (hc₀ : c₀ ≠ 0) (hb₀ : b₀ ≠ 0) (hadd : LineAdd c₀ b₀ Γ φ) {y y' : k}
    (hy : y ∈ lineSet Γ) (hy' : y' ∈ lineSet Γ) :
    lineExt Γ φ (y + y') = lineExt Γ φ y + lineExt Γ φ y' := by
  rcases hy with rfl | ⟨γ, rfl⟩
  · simp [lineExt_zero]
  rcases hy' with rfl | ⟨γ', rfl⟩
  · simp [lineExt_zero]
  rcases hadd γ γ' with ⟨δ, hc, hb⟩ | ⟨hc, hb⟩
  · have h1 : ((γ : kˣ) : k) + ((γ' : kˣ) : k) = ((δ : kˣ) : k) :=
      mul_left_cancel₀ hc₀ (by rw [mul_add]; exact hc)
    have h2 : ((φ γ : kˣ) : k) + ((φ γ' : kˣ) : k) = ((φ δ : kˣ) : k) :=
      mul_left_cancel₀ hb₀ (by rw [mul_add]; exact hb)
    rw [h1, lineExt_coe, lineExt_coe, lineExt_coe, h2]
  · have h1 : ((γ : kˣ) : k) + ((γ' : kˣ) : k) = 0 := by
      rw [← mul_add] at hc
      exact (mul_eq_zero.1 hc).resolve_left hc₀
    have h2 : ((φ γ : kˣ) : k) + ((φ γ' : kˣ) : k) = 0 := by
      rw [← mul_add] at hb
      exact (mul_eq_zero.1 hb).resolve_left hb₀
    rw [h1, lineExt_zero, lineExt_coe, lineExt_coe, h2]

variable [Finite k]

theorem mem_of_pow_card_eq_one (Γ : Subgroup kˣ) {x : kˣ} (hx : x ^ Nat.card Γ = 1) : x ∈ Γ := by
  classical
  have := Fintype.ofFinite k
  have : Fintype kˣ := inferInstance
  have hN : 0 < Nat.card Γ := Nat.card_pos
  have hRle : (Finset.univ.filter fun z : kˣ => z ^ Nat.card Γ = 1).card ≤ Nat.card Γ := by
    have h1 := card_nthRoots_subgroup_units (Units.coeHom k) Units.val_injective hN (1 : kˣ)
    refine h1.trans ?_
    exact Polynomial.card_nthRoots _ _
  have hsub : (Finset.univ.filter fun z : kˣ => z ∈ Γ) ⊆
      Finset.univ.filter fun z : kˣ => z ^ Nat.card Γ = 1 := by
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    have : (⟨z, hz⟩ : Γ) ^ Nat.card Γ = 1 := pow_card_eq_one'
    exact congrArg Subtype.val this
  have hcard : (Finset.univ.filter fun z : kˣ => z ∈ Γ).card = Nat.card Γ := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have heq := Finset.eq_of_subset_of_card_le hsub (hcard ▸ hRle)
  have hxm : x ∈ Finset.univ.filter fun z : kˣ => z ^ Nat.card Γ = 1 :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, hx⟩
  rw [← heq] at hxm
  simpa using hxm

theorem lineExt_mem (Γ : Subgroup kˣ) (φ : Γ →* kˣ) {y : k} (hy : y ∈ lineSet Γ) :
    lineExt Γ φ y ∈ lineSet Γ := by
  rcases hy with rfl | ⟨γ, rfl⟩
  · exact Or.inl lineExt_zero
  rw [lineExt_coe]
  refine Or.inr ⟨⟨φ γ, mem_of_pow_card_eq_one Γ ?_⟩, rfl⟩
  have : (φ γ) ^ Nat.card Γ = 1 := by
    rw [← map_pow, pow_card_eq_one', map_one]
  exact this

end Line

theorem exists_frobenius_pow (K : Type) [Field K] [Finite K] [CharP K 2] (ψ : K →+* K) :
    ∃ s : ℕ, ∀ x : K, ψ x = x ^ 2 ^ s := by
  let _ : Algebra (ZMod 2) K := ZMod.algebra K 2
  have hbij : Function.Bijective ψ := ⟨ψ.injective, Finite.injective_iff_surjective.1 ψ.injective⟩
  let g : K ≃ₐ[ZMod 2] K := AlgEquiv.ofRingEquiv (f := RingEquiv.ofBijective ψ hbij) (fun x => by
    have := congrArg (fun f : ZMod 2 →+* K => f x)
      (RingHom.ext_zmod (ψ.comp (algebraMap (ZMod 2) K)) (algebraMap (ZMod 2) K))
    simpa using this)
  obtain ⟨i, hi⟩ := FiniteField.exists_forall_apply_eq_pow (ZMod 2) 2 K g
  refine ⟨i, fun x => ?_⟩
  have h2 : Nat.card (ZMod 2) = 2 := by simp
  rw [h2] at hi
  exact hi x

variable [CharP k 2] [Finite k]

theorem exists_frobenius_of_lineAdd {c₀ b₀ : k} (hc₀ : c₀ ≠ 0) (hb₀ : b₀ ≠ 0) {Γ : Subgroup kˣ}
    {φ : Γ →* kˣ} (hadd : LineAdd c₀ b₀ Γ φ) :
    ∃ s : ℕ, ∀ γ : Γ, ((φ γ : kˣ) : k) = ((γ : kˣ) : k) ^ 2 ^ s := by
  let K₀ : Subfield k := lineField hc₀ hadd
  let ψ : K₀ →+* k :=
    { toFun := fun y => lineExt Γ φ y
      map_one' := lineExt_one
      map_mul' := fun y y' => lineExt_mul y.2 y'.2
      map_zero' := lineExt_zero
      map_add' := fun y y' => lineExt_add hc₀ hb₀ hadd y.2 y'.2 }
  let ψ' : K₀ →+* K₀ := ψ.codRestrict K₀ fun y => lineExt_mem Γ φ y.2
  obtain ⟨s, hs⟩ := exists_frobenius_pow K₀ ψ'
  refine ⟨s, fun γ => ?_⟩
  have h := congrArg Subtype.val (hs ⟨((γ : kˣ) : k), Or.inr ⟨γ, rfl⟩⟩)
  have h' : lineExt Γ φ ((γ : kˣ) : k) = ((γ : kˣ) : k) ^ 2 ^ s := h
  rw [lineExt_coe] at h'
  exact h'

theorem exists_subfield_line {c₀ b₀ : k} (hc₀ : c₀ ≠ 0) (hb₀ : b₀ ≠ 0) (Γ : Subgroup kˣ)
    (φ : Γ →* kˣ)
    (hadd : ∀ γ γ' : Γ,
      (∃ δ : Γ, c₀ * ((γ : kˣ) : k) + c₀ * ((γ' : kˣ) : k) = c₀ * ((δ : kˣ) : k) ∧
          b₀ * ((φ γ : kˣ) : k) + b₀ * ((φ γ' : kˣ) : k) = b₀ * ((φ δ : kˣ) : k)) ∨
        (c₀ * ((γ : kˣ) : k) + c₀ * ((γ' : kˣ) : k) = 0 ∧
          b₀ * ((φ γ : kˣ) : k) + b₀ * ((φ γ' : kˣ) : k) = 0))
    {P : k → k → Prop}
    (hcov : ∀ b c : k, P b c →
      (b = 0 ∧ c = 0) ∨ ∃ γ : Γ, c = c₀ * ((γ : kˣ) : k) ∧ b = b₀ * ((φ γ : kˣ) : k)) :
    ∃ s : ℕ, ∀ b c : k, P b c → ∃ y : k, c = c₀ * y ∧ b = b₀ * y ^ 2 ^ s := by
  obtain ⟨s, hs⟩ := exists_frobenius_of_lineAdd hc₀ hb₀ hadd
  refine ⟨s, fun b c hP => ?_⟩
  rcases hcov b c hP with ⟨rfl, rfl⟩ | ⟨γ, hc, hb⟩
  · exact ⟨0, by simp, by simp⟩
  · exact ⟨((γ : kˣ) : k), hc, by rw [hb, hs γ]⟩

end CFSG.Quasithin.Ch3E213M.Sp4C2
