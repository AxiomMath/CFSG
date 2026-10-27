module

public import CFSG.Timmesfeld.Transvection.QuadFormNorm
public import CFSG.LieType.Steinberg.CentralExt.UnitaryField

public section

namespace CFSG.Timmesfeld.Transvection.QuadForm

open QuadraticMap Module CFSG.LieType.BorelTits CFSG.LieType.Steinberg

theorem exists_ringHom_unitary {K : Type*} {F : Type} [Field K] [Finite K] [Field F] [Finite F]
    [CharP F 2] {f : ℕ} (hK : Nat.card K = 2 ^ f) (hF : Nat.card F = (2 ^ f) ^ 2) :
    ∃ j : K →+* F, ∀ z, unitaryInvolution F 2 f z = z ↔ ∃ k, j k = z := by
  have := Fintype.ofFinite K
  have := Fintype.ofFinite (fixedSubfield F 2 f)
  have hcard : Fintype.card K = Fintype.card (fixedSubfield F 2 f) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, card_fixedSubfield hF]
  let e := FiniteField.ringEquivOfCardEq hcard
  refine ⟨(fixedSubfield F 2 f).subtype.comp e.toRingHom, fun z => ⟨fun hz => ?_, ?_⟩⟩
  · exact ⟨e.symm ⟨z, hz⟩, by simp⟩
  · rintro ⟨k, rfl⟩
    exact (e k).2

theorem exists_ringHom_galoisField {f : ℕ} (hf : 1 ≤ f) :
    ∃ j : GaloisField 2 f →+* GaloisField 2 (2 * f),
      ∀ z, unitaryInvolution (GaloisField 2 (2 * f)) 2 f z = z ↔ ∃ k, j k = z :=
  exists_ringHom_unitary (GaloisField.card 2 f (by omega))
    (by rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm])

variable {K X : Type*} [Field K] [Finite K] [CharP K 2] [AddCommGroup X] [Module K X]
  {N : X → K} (hN : ∀ (c : K) (x : X), N (c • x) = c * c * N x)
  (hadd : ∀ x x' y : X, polar N (x + x') y = polar N x y + polar N x' y)
  (hsmul : ∀ (c : K) (x y : X), polar N (c • x) y = c * polar N x y)
  (haniso : ∀ x : X, N x = 0 → x = 0)
include hN hadd hsmul haniso

theorem finiteDimensional_of_quadratic : FiniteDimensional K X :=
  finiteDimensional (Q := QuadraticMap.ofPolar N hN hadd hsmul) haniso

theorem finrank_le_two_of_quadratic : finrank K X ≤ 2 :=
  finrank_le_two (Q := QuadraticMap.ofPolar N hN hadd hsmul) haniso

theorem finrank_eq_one_or_two [Nontrivial X] : finrank K X = 1 ∨ finrank K X = 2 := by
  have := finiteDimensional_of_quadratic hN hadd hsmul haniso
  have h1 := finrank_le_two_of_quadratic hN hadd hsmul haniso
  have h2 := Module.finrank_pos (R := K) (M := X)
  omega

omit hadd hsmul in
theorem exists_eq_one [Nontrivial X] : ∃ x₀ : X, N x₀ = 1 := by
  obtain ⟨x, hx⟩ := exists_ne (0 : X)
  have hx' : N x ≠ 0 := fun h => hx (haniso x h)
  obtain ⟨s, hs⟩ := exists_mul_self_eq (N x)⁻¹
  exact ⟨s • x, by rw [hN, hs, inv_mul_cancel₀ hx']⟩

omit [Finite K] [CharP K 2] hadd hsmul haniso in
theorem exists_addEquiv_of_finrank_eq_one (h1 : finrank K X = 1) {x₀ : X} (hx₀ : x₀ ≠ 0) :
    ∃ ι : K ≃+ X, ι 1 = x₀ ∧ (∀ k z : K, ι (k * z) = k • ι z) ∧
      ∀ z, N (ι z) = N x₀ * (z * z) := by
  have hspan := (finrank_eq_one_iff_of_nonzero' x₀ hx₀).1 h1
  let ψ : K →+ X := AddMonoidHom.mk' (fun z => z • x₀) fun a b => add_smul a b x₀
  have hψ : ∀ z, ψ z = z • x₀ := fun _ => rfl
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    rw [hψ, smul_eq_zero] at hz
    exact hz.resolve_right hx₀
  let e := AddEquiv.ofBijective ψ ⟨hinj, hspan⟩
  have he : ∀ z, e z = z • x₀ := fun _ => rfl
  refine ⟨e, by rw [he, one_smul], fun k z => by rw [he, he, mul_smul], fun z => ?_⟩
  rw [he, hN, mul_comm]

theorem exists_addEquiv_of_finrank_eq_two' {F : Type*} [Field F] (j : K →+* F) (σ : F →+* F)
    (hσ : ∀ z, σ (σ z) = z) (hfix : ∀ z, σ z = z ↔ ∃ k, j k = z) (htr : ∃ τ, τ + σ τ = 1)
    (h2 : finrank K X = 2) {x₀ : X} (hx₀ : x₀ ≠ 0) :
    ∃ ι : F ≃+ X, ι 1 = x₀ ∧ (∀ (k : K) (z : F), ι (j k * z) = k • ι z) ∧
      ∀ z, j (N (ι z)) = j (N x₀) * (σ z * z) :=
  exists_addEquiv_smul_of_finrank_eq_two j σ hσ hfix htr
    (Q := QuadraticMap.ofPolar N hN hadd hsmul) haniso h2 hx₀

theorem exists_addEquiv_of_finrank_eq_two_of_unitary {F : Type} [Field F] [Finite F]
    [CharP F 2] {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2) (j : K →+* F)
    (hj : ∀ z, unitaryInvolution F 2 f z = z ↔ ∃ k, j k = z) (h2 : finrank K X = 2) {x₀ : X}
    (hx₀ : x₀ ≠ 0) :
    ∃ ι : F ≃+ X, ι 1 = x₀ ∧ (∀ (k : K) (z : F), ι (j k * z) = k • ι z) ∧
      ∀ z, j (N (ι z)) = j (N x₀) * (unitaryInvolution F 2 f z * z) :=
  exists_addEquiv_of_finrank_eq_two' hN hadd hsmul haniso j
    (unitaryInvolution F 2 f).toRingHom (unitaryInvolution_involutive hF) hj
    (exists_add_unitaryInvolution_eq hF (map_one _)) h2 hx₀

end CFSG.Timmesfeld.Transvection.QuadForm
