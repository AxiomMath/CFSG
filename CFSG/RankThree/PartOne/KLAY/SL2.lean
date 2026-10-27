module

public import CFSG.RankThree.Classical.SL2SemilinearRoots
public import CFSG.LieType.Chevalley.RankOneGaussian

public section

namespace CFSG.RankThree.PartOne.KLAY

open CFSG.LieType.Chevalley CFSG.RankThree.Classical

section Elementary

variable {k : Type} [Field k]

theorem uSL_mul_uSL (a b : k) : (uSL a : SL2 k) * uSL b = uSL (a + b) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_uSL, Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem uSL_zero' : (uSL (0 : k) : SL2 k) = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_uSL]

theorem HSL_mul_HSL (s t : kˣ) : (HSL s : SL2 k) * HSL t = HSL (s * t) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_HSL, Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem HSL_one' : (HSL (1 : kˣ) : SL2 k) = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_HSL]

@[expose] def HSLhom : kˣ →* SL2 k where
  toFun := HSL
  map_one' := HSL_one'
  map_mul' s t := (HSL_mul_HSL s t).symm

theorem HSLhom_apply (t : kˣ) : (HSLhom t : SL2 k) = HSL t := rfl

theorem HSLhom_injective : Function.Injective (HSLhom (k := k)) := by
  intro s t h
  have := congrArg (fun X : SL2 k => (X : Matrix (Fin 2) (Fin 2) k) 0 0) h
  simp only [HSLhom_apply, coe_HSL] at this
  exact Units.ext (by simpa using this)

@[expose] def uHom : Multiplicative k →* SL2 k where
  toFun c := uSL (Multiplicative.toAdd c)
  map_one' := uSL_zero'
  map_mul' _ _ := (uSL_mul_uSL _ _).symm

theorem conjSL_diagUnitOne_uSL (a : kˣ) (c : k) :
    conjSL (diagUnitOne a) (uSL c) = uSL ((a : k) * c) := by
  apply Subtype.ext
  rw [coe_conjSL, coe_diagUnitOne, coe_diagUnitOne_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_uSL, Matrix.mul_apply, Fin.sum_univ_two]

theorem conjSL_diagUnitOne_vSL (a : kˣ) (c : k) :
    conjSL (diagUnitOne a) (vSL c) = vSL (((a⁻¹ : kˣ) : k) * c) := by
  apply Subtype.ext
  rw [coe_conjSL, coe_diagUnitOne, coe_diagUnitOne_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_vSL, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem eq_HSL_of_conj {γ : SL2 k} {χ : kˣ}
    (h : ∀ A : SL2 k, γ * A * γ⁻¹ = conjSL (diagUnitOne χ) A) :
    ∃ t : kˣ, γ = HSL t ∧ t * t = χ := by
  have hu : γ * uSL 1 = uSL (χ : k) * γ := by
    have h1 := h (uSL 1)
    rw [mul_inv_eq_iff_eq_mul, conjSL_diagUnitOne_uSL, mul_one] at h1
    exact h1
  have hv : γ * vSL 1 = vSL (((χ⁻¹ : kˣ) : k)) * γ := by
    have h1 := h (vSL 1)
    rw [mul_inv_eq_iff_eq_mul, conjSL_diagUnitOne_vSL, mul_one] at h1
    exact h1
  have e00 := congrArg (fun X : SL2 k => (X : Matrix (Fin 2) (Fin 2) k) 0 0) hu
  have e01 := congrArg (fun X : SL2 k => (X : Matrix (Fin 2) (Fin 2) k) 0 1) hu
  have e11 := congrArg (fun X : SL2 k => (X : Matrix (Fin 2) (Fin 2) k) 1 1) hu
  have f00 := congrArg (fun X : SL2 k => (X : Matrix (Fin 2) (Fin 2) k) 0 0) hv
  have f10 := congrArg (fun X : SL2 k => (X : Matrix (Fin 2) (Fin 2) k) 1 0) hv
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_uSL, coe_vSL, Matrix.mul_apply,
    Fin.sum_univ_two] at e00 e01 e11 f00 f10
  simp at e00 e01 e11 f00 f10
  have hdet := det_SL2 γ
  set a := (γ : Matrix (Fin 2) (Fin 2) k) 0 0 with ha
  set b := (γ : Matrix (Fin 2) (Fin 2) k) 0 1 with hb
  set c := (γ : Matrix (Fin 2) (Fin 2) k) 1 0 with hc
  set d := (γ : Matrix (Fin 2) (Fin 2) k) 1 1 with hd
  have hχ : (χ : k) ≠ 0 := χ.ne_zero
  have hc0 : c = 0 := by simpa [hχ] using e00
  have hb0 : b = 0 := by simpa using f00
  have had : a = (χ : k) * d := by linear_combination e01
  rw [hb0, hc0] at hdet
  have hne : a ≠ 0 := by
    intro h0
    rw [h0] at hdet
    simp at hdet
  have hd' : d = a⁻¹ := by
    field_simp
    linear_combination hdet
  refine ⟨Units.mk0 a hne, ?_, ?_⟩
  · apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j
    · simp [coe_HSL, ha]
    · simpa [coe_HSL, ← hb] using hb0
    · simpa [coe_HSL, ← hc] using hc0
    · simpa [coe_HSL, ← hd] using hd'
  · apply Units.ext
    simp only [Units.val_mul, Units.val_mk0]
    linear_combination a * had + (χ : k) * hdet

end Elementary

section Package

variable {M : Type} [Group M] {k : Type} [Field k]

structure SL2Torus (p : ℕ) (φ : SL2 k →* M) (T₀ : Subgroup M) : Prop where
  inj : Function.Injective φ
  exp : ∀ t ∈ T₀, t ^ p = 1
  act : ∀ t ∈ T₀, ∃ χ : kˣ, ∀ A : SL2 k, t * φ A * t⁻¹ = φ (conjSL (diagUnitOne χ) A)
  diag : ∀ s : kˣ, s ^ p = 1 → φ (HSL s) ∈ T₀
  move : ∃ t ∈ T₀, t * φ (uSL 1) * t⁻¹ ≠ φ (uSL 1)

namespace SL2Torus

variable {p : ℕ} {φ : SL2 k →* M} {T₀ : Subgroup M}

theorem mem_inf_iff (h : SL2Torus p φ T₀) {g : M} :
    g ∈ T₀ ⊓ φ.range ↔ ∃ s : kˣ, s ^ p = 1 ∧ φ (HSL s) = g := by
  constructor
  · rintro ⟨hgT, γ, rfl⟩
    obtain ⟨χ, hχ⟩ := h.act _ hgT
    have hγ : ∀ A : SL2 k, γ * A * γ⁻¹ = conjSL (diagUnitOne χ) A := fun A => by
      apply h.inj
      rw [map_mul, map_mul, map_inv]
      exact hχ A
    obtain ⟨t, rfl, -⟩ := eq_HSL_of_conj hγ
    refine ⟨t, ?_, rfl⟩
    have h1 := h.exp _ hgT
    have h2 : φ (HSLhom (t ^ p)) = φ 1 := by
      rw [map_pow, map_one, HSLhom_apply, map_pow, h1]
    exact HSLhom_injective (by rw [h.inj h2, map_one])
  · rintro ⟨s, hs, rfl⟩
    exact ⟨h.diag s hs, HSL s, rfl⟩

theorem card_inf [Finite k] (h : SL2Torus p φ T₀) (hp : 0 < p)
    (hζ : ∃ ζ : kˣ, IsPrimitiveRoot ζ p) : Nat.card ↥(T₀ ⊓ φ.range) = p := by
  let ψ : ↥(rootsOfUnity p k) →* M := φ.comp (HSLhom.comp (rootsOfUnity p k).subtype)
  have hψ : Function.Injective ψ := h.inj.comp (HSLhom_injective.comp Subtype.val_injective)
  have hrange : T₀ ⊓ φ.range = ψ.range := by
    ext g
    rw [h.mem_inf_iff]
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨⟨s, (mem_rootsOfUnity p s).2 hs⟩, rfl⟩
    · rintro ⟨⟨s, hs⟩, rfl⟩
      exact ⟨s, (mem_rootsOfUnity p s).1 hs, rfl⟩
  rw [hrange, Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv.symm]
  have : NeZero p := ⟨hp.ne'⟩
  obtain ⟨ζ, hζ⟩ := hζ
  exact IsPrimitiveRoot.card_rootsOfUnity (IsPrimitiveRoot.coe_units_iff.mpr hζ)

theorem exists_upper [CharP k 2] (h : SL2Torus p φ T₀) :
    ∃ U : Subgroup M, U ≤ φ.range ∧ IsPGroup 2 ↥U ∧ T₀ ≤ Subgroup.normalizer (U : Set M) ∧
      ∃ u ∈ U, ∃ t ∈ T₀, u * t ≠ t * u := by
  let U : Subgroup M := (φ.comp uHom).range
  have hmem : ∀ g, g ∈ U ↔ ∃ c : k, φ (uSL c) = g := fun g => by
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨Multiplicative.toAdd x, rfl⟩
    · rintro ⟨c, rfl⟩
      exact ⟨Multiplicative.ofAdd c, rfl⟩
  have key : ∀ t ∈ T₀, ∀ g ∈ U, t * g * t⁻¹ ∈ U := by
    intro t ht g hg
    obtain ⟨c, rfl⟩ := (hmem g).1 hg
    obtain ⟨χ, hχ⟩ := h.act t ht
    rw [hχ, conjSL_diagUnitOne_uSL]
    exact (hmem _).2 ⟨_, rfl⟩
  refine ⟨U, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨uHom x, rfl⟩
  · rintro ⟨g, hg⟩
    obtain ⟨c, rfl⟩ := (hmem g).1 hg
    refine ⟨1, Subtype.ext ?_⟩
    change φ (uSL c) ^ 2 = 1
    rw [sq, ← map_mul, uSL_mul_uSL, CharTwo.add_self_eq_zero, uSL_zero', map_one]
  · intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · exact key t ht g
    · intro hg
      have := key t⁻¹ (T₀.inv_mem ht) _ hg
      simpa [mul_assoc] using this
  · obtain ⟨t, ht, hne⟩ := h.move
    refine ⟨φ (uSL 1), (hmem _).2 ⟨1, rfl⟩, t, ht, fun hcomm => hne ?_⟩
    rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]

end SL2Torus

end Package

end CFSG.RankThree.PartOne.KLAY
