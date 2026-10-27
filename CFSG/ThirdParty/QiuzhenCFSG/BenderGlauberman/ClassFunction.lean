module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character

namespace CFSG
end CFSG
open CFSG

/-!
# Bender--Glauberman character machinery

The base character theory (class functions `G → ℂ`, the scalar product,
characters and irreducible characters, orthonormality, integrality, induction,
and the Brauer--Suzuki pairing) is provided by `Theory.Character`; this file
contains only the Bender--Glauberman-specific additions: the `g⁻¹`-form
`scalarProductInv`, character decomposition, linear characters, the regular
representation, and Frobenius reciprocity.
-/

noncomputable section

open scoped BigOperators
open scoped MonoidAlgebra
open scoped TensorProduct

open Theory.Character

namespace CFSG.BenderGlauberman

universe u v w

-- This file's sums over subgroups need `Fintype ↥H`.  As in
-- `Theory/Character/BrauerSuzuki.lean`, use local instances so that statement
-- and proof contexts synthesize the *same* instance that `Theory.Character`
-- statements embed; deliberately not exported.
attribute [local instance] Fintype.ofFinite
attribute [local instance] Classical.propDecidable


/-! ## Orthonormality of irreducible characters -/

section Orthonormality

variable {G : Type u} [Group G] [Fintype G]

/-- Characters are class functions: `χ (g * x * g⁻¹) = χ x`. -/
public theorem irreducibleCharacter_isClassFunction {G : Type u} [Group G]
    {φ : ClassFunction G} (hφ : IsIrreducibleCharacter φ) : IsClassFunction φ := by
  rcases hφ with ⟨n, ρ, hρ, rfl⟩
  intro x g
  exact Representation.char_conj ρ x g

/-- A character is a class function. -/
public theorem isCharacter_isClassFunction {G : Type u} [Group G]
    {φ : ClassFunction G} (hφ : IsCharacter φ) : IsClassFunction φ := by
  rcases hφ with ⟨n, ρ, hφeq⟩
  intro x g
  rw [hφeq]
  exact Representation.char_conj ρ x g

/-- A generalized character is a class function. -/
public theorem isClassFunction_of_isGeneralizedCharacter {G : Type u} [Group G]
    {φ : ClassFunction G} (hφ : IsGeneralizedCharacter φ) : IsClassFunction φ := by
  rcases hφ with ⟨ξ, ψ, hξ, hψ, hφeq⟩
  intro x g
  rw [hφeq]
  have hξx : ξ (g * x * g⁻¹) = ξ x := isCharacter_isClassFunction hξ x g
  have hψx : ψ (g * x * g⁻¹) = ψ x := isCharacter_isClassFunction hψ x g
  simp [hξx, hψx]


end Orthonormality

/-- The paper's inner product in `g⁻¹`-form: `(φ, ψ)_G = |G|⁻¹ Σ φ(g)·ψ(g⁻¹)`. -/
@[expose] public def scalarProductInv (G : Type u) [Group G] [Fintype G]
    (φ ψ : ClassFunction G) : ℂ :=
  (Nat.card G : ℂ)⁻¹ * ∑ g : G, φ g * ψ g⁻¹

section OrthonormalityInv

variable {G : Type u} [Group G] [Fintype G]

/-- Orthogonality of distinct irreducible characters, in `g⁻¹`-form. -/
public theorem isIrreducible_orthogonal_inv {χ ψ : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ) (hψ : IsIrreducibleCharacter ψ) (hne : χ ≠ ψ) :
    scalarProductInv G χ ψ = 0 := by
  simpa [scalarProductInv, characterProduct] using irreducibleCharacters_orthogonal hχ hψ hne

/-- An irreducible character has norm one, in `g⁻¹`-form. -/
public theorem isIrreducible_norm_inv_one {χ : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ) : scalarProductInv G χ χ = 1 := by
  simpa [scalarProductInv, characterProduct] using irreducibleCharacter_self hχ

/-- A character of norm one (in `g⁻¹`-form) is irreducible. -/
public theorem isIrreducibleCharacter_of_norm_one_inv {χ : ClassFunction G}
    (hχ : IsCharacter χ) (hnorm : scalarProductInv G χ χ = 1) :
    IsIrreducibleCharacter χ := by
  rcases hχ with ⟨n, ρ, hχeq⟩
  refine ⟨n, ρ, ?_, hχeq⟩
  apply (irreducible_iff_character_norm_one ρ).2
  rw [← scalarProduct_ofConjClassFunction,
    ofConjClassFunction_characterClassFunction]
  rw [hχeq] at hnorm
  unfold scalarProduct
  unfold scalarProductInv at hnorm
  convert hnorm using 1
  simp only [Theory.Representation.representation_character_inv_eq_star_character]
  congr 1
  congr 1
  exact Finset.ext fun x => by simp

end OrthonormalityInv

/-! ## Scalar products on products and under isomorphisms -/

section ScalarProductProd

variable {G H : Type u} [Group G] [Group H] [Fintype G] [Fintype H]

/-- The `g⁻¹`-form scalar product of a product character factors as the
product of the scalar products of its factors. -/
public theorem scalarProductInv_prod_mul (α : ClassFunction G) (β : ClassFunction H) :
    scalarProductInv (G × H) (fun p : G × H => α p.1 * β p.2)
      (fun p : G × H => α p.1 * β p.2) =
    scalarProductInv G α α * scalarProductInv H β β := by
  classical
  unfold scalarProductInv
  have hsum : (∑ p : G × H, (α p.1 * β p.2) * (α p.1⁻¹ * β p.2⁻¹)) =
      (∑ g : G, α g * α g⁻¹) * (∑ h : H, β h * β h⁻¹) := by
    rw [Fintype.sum_prod_type]
    calc
      (∑ g : G, ∑ h : H, (α g * β h) * (α g⁻¹ * β h⁻¹))
          = ∑ g : G, (α g * α g⁻¹) * (∑ h : H, β h * β h⁻¹) := by
              refine Finset.sum_congr rfl ?_
              intro g hg
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro h hh
              ring
      _ = (∑ g : G, α g * α g⁻¹) * (∑ h : H, β h * β h⁻¹) := by
              rw [Finset.sum_mul]
  rw [Nat.card_prod]
  change (↑(Nat.card G * Nat.card H))⁻¹ *
      (∑ p : G × H, (α p.1 * β p.2) * (α p.1⁻¹ * β p.2⁻¹)) =
    ((↑(Nat.card G))⁻¹ * (∑ g : G, α g * α g⁻¹)) *
      ((↑(Nat.card H))⁻¹ * (∑ h : H, β h * β h⁻¹))
  rw [hsum]
  have hG0 : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := G)).ne'
  have hH0 : (Nat.card H : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := H)).ne'
  rw [Nat.cast_mul]
  field_simp [hG0, hH0]

/-- The `g⁻¹`-form scalar product is invariant under group isomorphism
(pulling the class functions back along the inverse). -/
public theorem scalarProductInv_congr (e : G ≃* H) (φ ψ : ClassFunction G) :
    scalarProductInv G φ ψ =
      scalarProductInv H (fun h : H => φ (e.symm h)) (fun h : H => ψ (e.symm h)) := by
  classical
  unfold scalarProductInv
  have hcard : Nat.card G = Nat.card H := Nat.card_congr e.toEquiv
  rw [hcard]
  congr 1
  refine Finset.sum_bij (fun g _ => e g) ?_ ?_ ?_ ?_
  · intro h hh
    simp
  · intro a ha b hb hab
    exact e.injective hab
  · intro h hh
    refine ⟨e.symm h, by simp, ?_⟩
    simp
  · intro g hg
    simp

/-- Irreducibility is transported by a group isomorphism. -/
public theorem isIrreducibleCharacter_congr {G H : Type u} [Group G] [Group H]
    [Fintype G] [Fintype H] (e : H ≃* G) {χ : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ) :
    IsIrreducibleCharacter (fun h : H => χ (e h)) := by
  refine isIrreducibleCharacter_of_norm_one_inv ?hchar ?hnorm
  · rcases hχ with ⟨n, ρ, hρ, hχeq⟩
    refine ⟨n, ρ.comp e, ?_⟩
    ext h
    rw [hχeq]
    rfl
  · have hc := scalarProductInv_congr (e := e.symm) (φ := χ) (ψ := χ)
    have he : e.symm.symm = e := by
      ext h
      rfl
    rw [he] at hc
    rw [← hc]
    exact isIrreducible_norm_inv_one hχ

end ScalarProductProd


/-! ## The star--inverse bridge -/

section StarBridge

/-- star (trace (ρ g)) = trace (ρ g⁻¹) for a finite-group representation. -/
public theorem star_trace_char_inv {G : Type u} [Group G] [Fintype G] {V : Type v}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (g : G) :
    star ((LinearMap.trace ℂ V) (ρ g)) = (LinearMap.trace ℂ V) (ρ g⁻¹) :=
  (Theory.Representation.representation_character_inv_eq_star_character ρ g).symm

/-- For a character χ: star (χ g) = χ g⁻¹. -/
public theorem star_char_eq_char_inv {G : Type u} [Group G] [Fintype G] {χ : ClassFunction G}
    (hχ : IsCharacter χ) (g : G) : star (χ g) = χ g⁻¹ := by
  rcases hχ with ⟨n, ρ, hχeq⟩
  rw [hχeq]
  exact (Theory.Representation.representation_character_inv_eq_star_character ρ g).symm

/-- For a character χ, the conjugate scalar product is the g⁻¹-form. -/
public theorem star_scalarProduct_eq_inv_of_char {G : Type u} [Group G] [Fintype G]
    {χ ψ : ClassFunction G} (hχ : IsCharacter χ) :
    star (scalarProduct G χ ψ) = scalarProductInv G χ ψ := by
  classical
  unfold scalarProduct scalarProductInv
  calc
    star ((Nat.card G : ℂ)⁻¹ * ∑ g : G, χ g * star (ψ g))
        = (Nat.card G : ℂ)⁻¹ * ∑ g : G, star (χ g * star (ψ g)) := by simp
    _ = (Nat.card G : ℂ)⁻¹ * ∑ g : G, star (χ g) * ψ g := by
      congr 1
      refine Finset.sum_congr rfl ?_
      intro g _hg
      simp
    _ = (Nat.card G : ℂ)⁻¹ * ∑ g : G, χ g⁻¹ * ψ g := by
      congr 1
      refine Finset.sum_congr rfl ?_
      intro g _hg
      rw [star_char_eq_char_inv hχ g]
    _ = (Nat.card G : ℂ)⁻¹ * ∑ h : G, χ h * ψ h⁻¹ := by
      congr 1
      refine (Finset.sum_bij (fun h hh => h⁻¹) ?_ ?_ ?_ ?_).symm
      · intro h hh
        simp
      · intro h₁ _h₁ h₂ _h₂ hEq
        exact inv_injective hEq
      · intro g _hg
        refine ⟨g⁻¹, by simp, ?_⟩
        simp
      · intro h _hh
        congr 1
        simp

end StarBridge

/-! ## Transport of representations and norm positivity -/

section Transport

variable {G : Type u} [Group G]

/-- Transport of a representation through a linear equivalence. -/
public noncomputable def charTrans {V : Type v} {W : Type w} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (e : V ≃ₗ[ℂ] W) (ρ : Representation ℂ G V) :
    Representation ℂ G W where
  toFun g := e ∘ₗ (ρ g) ∘ₗ (e.symm : W →ₗ[ℂ] V)
  map_one' := by
    ext w
    simp
  map_mul' := by
    intro g h
    ext w
    simp

/-- Transporting a representation through a linear equivalence gives an
equivalent representation. -/
public noncomputable def equiv_charTrans {V : Type v} {W : Type w} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (e : V ≃ₗ[ℂ] W) (ρ : Representation ℂ G V) :
    ρ.Equiv (charTrans e ρ) := by
  refine Representation.Equiv.mk e ?_
  intro g
  ext v
  simp [charTrans]

end Transport

/-! ## Norm positivity and multiplicity integrality -/

section Norms

variable {G : Type u} [Group G] [Fintype G]

/-- `star (φ, ψ₁ - ψ₂) = ...`: the scalar product is additive in the second
argument. -/
public lemma scalarProduct_sub_right [Group G] (φ ψ₁ ψ₂ : ClassFunction G) :
    scalarProduct G φ (ψ₁ - ψ₂) = scalarProduct G φ ψ₁ - scalarProduct G φ ψ₂ := by
  calc
    scalarProduct G φ (ψ₁ - ψ₂) = scalarProduct G φ (ψ₁ + (-1 : ℂ) • ψ₂) := by
      simp [sub_eq_add_neg]
    _ = scalarProduct G φ ψ₁ + scalarProduct G φ ψ₂ * star (-1 : ℂ) := by
      rw [scalarProduct_add_right, scalarProduct_smul_right]
    _ = scalarProduct G φ ψ₁ - scalarProduct G φ ψ₂ := by
      simp
      ring

/-- The character of a direct product representation is the sum of the
characters. -/
public theorem char_prod [Fintype G] {V W : Type v} [AddCommGroup V] [Module ℂ V]
    [Module.Finite ℂ V] [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) :
    (ρ.prod σ).character = ρ.character + σ.character := by
  funext g
  change (LinearMap.trace ℂ (V × W)) ((ρ.prod σ) g) =
    (LinearMap.trace ℂ V) (ρ g) + (LinearMap.trace ℂ W) (σ g)
  change (LinearMap.trace ℂ (V × W)) ((ρ g).prodMap (σ g)) =
    (LinearMap.trace ℂ V) (ρ g) + (LinearMap.trace ℂ W) (σ g)
  exact LinearMap.trace_prodMap' (ρ g) (σ g)

/-- The sum of two characters is a character. -/
public theorem isCharacter_add {φ ψ : ClassFunction G} (hφ : IsCharacter φ)
    (hψ : IsCharacter ψ) : IsCharacter (φ + ψ) := by
  classical
  rcases hφ with ⟨n, ρ, hφeq⟩
  rcases hψ with ⟨m, σ, hψeq⟩
  -- transport the product representation to `Fin (n + m) → ℂ`
  let e : ((Fin n → ℂ) × (Fin m → ℂ)) ≃ₗ[ℂ] (Fin (n + m) → ℂ) :=
    ((LinearEquiv.sumArrowLequivProdArrow (Fin n) (Fin m) ℂ ℂ).symm).trans
      (LinearEquiv.funCongrLeft ℂ ℂ finSumFinEquiv.symm)
  refine ⟨n + m, charTrans e (ρ.prod σ), ?_⟩
  rw [← Representation.char_iso (equiv_charTrans e (ρ.prod σ)), char_prod, hφeq, hψeq]

/-- An irreducible character is a character. -/
public theorem isCharacter_of_isIrreducibleCharacter [Fintype G] {χ : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ) : IsCharacter χ := by
  rcases hχ with ⟨n, ρ, hρ, hχeq⟩
  exact ⟨n, ρ, hχeq⟩

/-- Subtracting a character from a generalized character yields a generalized
character. -/
public theorem isGeneralizedCharacter_sub_char {φ : ClassFunction G}
    (hφ : IsGeneralizedCharacter φ) {χ : ClassFunction G} (hχ : IsCharacter χ) :
    IsGeneralizedCharacter (φ - χ) := by
  rcases hφ with ⟨δ₁, δ₂, hδ₁, hδ₂, hφeq⟩
  refine ⟨δ₁, δ₂ + χ, hδ₁, isCharacter_add hδ₂ hχ, ?_⟩
  rw [hφeq]
  funext x
  simp [Pi.add_apply, Pi.sub_apply]
  ring

/-- Adding a character to a generalized character yields a generalized
character. -/
public theorem isGeneralizedCharacter_add_char {φ : ClassFunction G}
    (hφ : IsGeneralizedCharacter φ) {χ : ClassFunction G} (hχ : IsCharacter χ) :
    IsGeneralizedCharacter (φ + χ) := by
  rcases hφ with ⟨δ₁, δ₂, hδ₁, hδ₂, hφeq⟩
  refine ⟨δ₁ + χ, δ₂, isCharacter_add hδ₁ hχ, hδ₂, ?_⟩
  rw [hφeq]
  funext x
  simp [Pi.add_apply, Pi.sub_apply]
  ring

/-- `(χ,χ) = 1` for an irreducible character, in the star form. -/
public theorem scalarProduct_irreducible_self {χ : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ) : scalarProduct G χ χ = 1 := by
  have hb : star (scalarProduct G χ χ) = scalarProductInv G χ χ :=
    star_scalarProduct_eq_inv_of_char (isCharacter_of_isIrreducibleCharacter hχ)
  have hinv : scalarProductInv G χ χ = 1 := isIrreducible_norm_inv_one hχ
  exact star_inj.mp (by simpa using hb.trans hinv)

/-- Distinct irreducible characters are orthogonal, in the star form. -/
public theorem scalarProduct_irreducible_orthogonal {χ ψ : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ) (hψ : IsIrreducibleCharacter ψ) (hne : χ ≠ ψ) :
    scalarProduct G χ ψ = 0 := by
  have hb : star (scalarProduct G χ ψ) = scalarProductInv G χ ψ :=
    star_scalarProduct_eq_inv_of_char (isCharacter_of_isIrreducibleCharacter hχ)
  have hinv : scalarProductInv G χ ψ = 0 := isIrreducible_orthogonal_inv hχ hψ hne
  exact star_inj.mp (by simpa using hb.trans hinv)

/-- `|φ|²` is a nonnegative real number. -/
public lemma normSq_nonneg [Group G] (φ : ClassFunction G) : 0 ≤ (normSq G φ).re := by
  classical
  have hsum : (∑ g : G, (Complex.normSq (φ g) : ℂ)) = (∑ g : G, φ g * star (φ g)) := by
    refine Finset.sum_congr rfl ?_
    intro g hg
    rw [Complex.normSq_eq_conj_mul_self, mul_comm]
    simp
  have hre : (normSq G φ).re = (Nat.card G : ℝ)⁻¹ * (∑ g : G, Complex.normSq (φ g) : ℝ) := by
    unfold normSq scalarProduct
    rw [← hsum]
    rw [← Complex.ofReal_sum]
    rw [show (Nat.card G : ℂ)⁻¹ = (((Nat.card G : ℝ)⁻¹ : ℝ) : ℂ) by
      norm_num]
    simp
  rw [hre]
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg (Nat.card G)))
    (Finset.sum_nonneg (fun g hg => Complex.normSq_nonneg (φ g)))

/-- `|φ|² = 0` iff `φ = 0`. -/
public lemma normSq_eq_zero_iff (φ : ClassFunction G) : normSq G φ = 0 ↔ φ = 0 := by
  classical
  constructor
  · intro h
    ext g
    have hsum0 : (∑ x : G, φ x * star (φ x)) = (∑ x : G, (Complex.normSq (φ x) : ℂ)) := by
      refine Finset.sum_congr rfl ?_
      intro x hx
      rw [Complex.normSq_eq_conj_mul_self, mul_comm]
      simp
    have h1 : (Nat.card G : ℂ) * normSq G φ = ∑ x : G, (Complex.normSq (φ x) : ℂ) := by
      unfold normSq scalarProduct
      rw [hsum0]
      rw [← mul_assoc, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.card_pos (α := G)).ne'),
        one_mul]
    have hsum : (∑ x : G, (Complex.normSq (φ x) : ℂ)) = 0 := by
      rw [← h1, h]
      simp
    have hsum' : (∑ x : G, Complex.normSq (φ x) : ℝ) = 0 := by
      exact_mod_cast hsum
    have hx : ∀ x : G, Complex.normSq (φ x) = 0 :=
      fun x => (Finset.sum_eq_zero_iff_of_nonneg (fun x hx => Complex.normSq_nonneg (φ x))).1
        hsum' x (Finset.mem_univ x)
    exact (Complex.normSq_eq_zero).1 (hx g)
  · intro h
    simp [h, normSq, scalarProduct]

/-- Multiplicities are integers: `(χ,δ)` is an integer for irreducible `χ` and
generalized `δ`. -/
public theorem multiplicity_int {χ : ClassFunction G} (hχ : IsIrreducibleCharacter χ)
    (δ : ClassFunction G) (hδ : IsGeneralizedCharacter δ) :
    ∃ a : ℤ, scalarProduct G χ δ = (a : ℂ) := by
  classical
  rcases hδ with ⟨δ₁, δ₂, hδ₁, hδ₂, hδeq⟩
  have hmul : ∀ δᵢ : ClassFunction G, IsCharacter δᵢ →
      ∃ a : ℤ, scalarProduct G χ δᵢ = (a : ℂ) := by
    intro δᵢ hδᵢ
    rcases hχ with ⟨n, ρχ, hρχ, hχeq⟩
    rcases hδᵢ with ⟨m, ρδ, hδᵢeq⟩
    have : Invertible (Nat.card G : ℂ) :=
      invertibleOfNonzero (by exact_mod_cast (Nat.card_pos (α := G)).ne')
    have hfin : scalarProductInv G χ δᵢ =
        (Module.finrank ℂ (Representation.IntertwiningMap ρδ ρχ) : ℂ) := by
      have h := Representation.card_inv_mul_sum_char_mul_char_eq_finrank (ρ := ρδ) (σ := ρχ)
      simpa [scalarProductInv, characterProduct, hχeq, hδᵢeq] using h
    have hb : star (scalarProduct G χ δᵢ) = scalarProductInv G χ δᵢ :=
      star_scalarProduct_eq_inv_of_char (isCharacter_of_isIrreducibleCharacter ⟨n, ρχ, ⟨hρχ, hχeq⟩⟩)
    refine ⟨(Module.finrank ℂ (Representation.IntertwiningMap ρδ ρχ) : ℤ), ?_⟩
    calc
      scalarProduct G χ δᵢ = star (scalarProductInv G χ δᵢ) := by
        simpa using congrArg star hb
      _ = star ((Module.finrank ℂ (Representation.IntertwiningMap ρδ ρχ) : ℂ)) := by
            rw [hfin]
      _ = (Module.finrank ℂ (Representation.IntertwiningMap ρδ ρχ) : ℂ) := by simp
      _ = ((Module.finrank ℂ (Representation.IntertwiningMap ρδ ρχ) : ℤ) : ℂ) := by norm_num
  rcases hmul δ₁ hδ₁ with ⟨a₁, ha₁⟩
  rcases hmul δ₂ hδ₂ with ⟨a₂, ha₂⟩
  refine ⟨a₁ - a₂, ?_⟩
  calc
    scalarProduct G χ δ = scalarProduct G χ (δ₁ - δ₂) := by rw [hδeq]
    _ = scalarProduct G χ δ₁ - scalarProduct G χ δ₂ := scalarProduct_sub_right χ δ₁ δ₂
    _ = (a₁ : ℂ) - (a₂ : ℂ) := by rw [ha₁, ha₂]
    _ = ((a₁ - a₂ : ℤ) : ℂ) := by norm_num

/-- The scalar product of an irreducible character with a character is a
nonnegative real number (the multiplicity of the irreducible in the
character). -/
public theorem scalarProduct_irreducible_char_nonneg {G : Type u} [Group G] [Fintype G]
    {χ ψ : ClassFunction G} (hχ : IsIrreducibleCharacter χ) (hψ : IsCharacter ψ) :
    ∃ r : ℝ, 0 ≤ r ∧ scalarProduct G χ ψ = (r : ℂ) := by
  classical
  rcases hχ with ⟨n, ρχ, hρχ, hχeq⟩
  rcases hψ with ⟨m, ρψ, hψeq⟩
  have : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (by exact_mod_cast (Nat.card_pos (α := G)).ne')
  have hfin : scalarProductInv G χ ψ =
      (Module.finrank ℂ (Representation.IntertwiningMap ρψ ρχ) : ℂ) := by
    have h := Representation.card_inv_mul_sum_char_mul_char_eq_finrank (ρ := ρψ) (σ := ρχ)
    simpa [scalarProductInv, characterProduct, hχeq, hψeq] using h
  have hb : star (scalarProduct G χ ψ) = scalarProductInv G χ ψ :=
    star_scalarProduct_eq_inv_of_char (isCharacter_of_isIrreducibleCharacter ⟨n, ρχ, ⟨hρχ, hχeq⟩⟩)
  refine ⟨(Module.finrank ℂ (Representation.IntertwiningMap ρψ ρχ) : ℝ), ?_, ?_⟩
  · exact_mod_cast (Nat.zero_le _)
  · calc
      scalarProduct G χ ψ = star (scalarProductInv G χ ψ) := by
        simpa using congrArg star hb
      _ = star ((Module.finrank ℂ (Representation.IntertwiningMap ρψ ρχ) : ℂ)) := by rw [hfin]
      _ = (Module.finrank ℂ (Representation.IntertwiningMap ρψ ρχ) : ℂ) := by simp
      _ = ((Module.finrank ℂ (Representation.IntertwiningMap ρψ ρχ) : ℝ) : ℂ) := by norm_num

/-- The degree of an irreducible character is nonzero. -/
public lemma irreducible_char_one_ne_zero [Fintype G] {χ : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ) :
    χ 1 ≠ 0 := by
  classical
  rcases hχ with ⟨n, ρ, hρ, hχeq⟩
  have : Representation.IsIrreducible ρ := hρ
  have : Nontrivial (Fin n → ℂ) := by
    exact IsSimpleModule.nontrivial ℂ[G] ρ.asModule
  have hn0 : n ≠ 0 := by
    intro hn0
    have : Subsingleton (Fin n → ℂ) := by
      subst n
      infer_instance
    exact (not_subsingleton (Fin n → ℂ)) (by infer_instance)
  rw [hχeq]
  rw [Representation.char_one]
  rw [Module.finrank_pi, Fintype.card_fin]
  exact_mod_cast hn0

end Norms

/-! ## Scalar products of decomposed functions -/

section DecompScalar

variable {G : Type u} [Group G] [Fintype G]

/-- The scalar product is additive in the first argument. -/
public lemma scalarProduct_sum_left [Group G] {ι : Type*} [Fintype ι]
    (f : ι → ClassFunction G)
    (ψ : ClassFunction G) :
    scalarProduct G (∑ i, f i) ψ = ∑ i, scalarProduct G (f i) ψ := by
  classical
  unfold scalarProduct
  rw [← Finset.mul_sum]
  congr 1
  simp only [Finset.sum_apply]
  calc
    (∑ g : G, (∑ i : ι, f i g) * star (ψ g)) = ∑ g : G, ∑ i : ι, f i g * star (ψ g) := by
      refine Finset.sum_congr rfl ?_
      intro g hg
      rw [Finset.sum_mul]
    _ = ∑ i : ι, ∑ g : G, f i g * star (ψ g) := by
      exact Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
        (f := fun g i => f i g * star (ψ g))

/-- The scalar product is additive in the second argument. -/
public lemma scalarProduct_sum_right [Group G] (φ : ClassFunction G) {ι : Type*} [Fintype ι]
    (g : ι → ClassFunction G) :
    scalarProduct G φ (∑ i, g i) = ∑ i, scalarProduct G φ (g i) := by
  classical
  unfold scalarProduct
  rw [← Finset.mul_sum]
  congr 1
  simp only [Finset.sum_apply]
  calc
    (∑ x : G, φ x * star (∑ i : ι, g i x)) = ∑ x : G, ∑ i : ι, φ x * star (g i x) := by
      refine Finset.sum_congr rfl ?_
      intro x hx
      change φ x * (starRingEnd ℂ) (∑ i : ι, g i x) = ∑ i : ι, φ x * star (g i x)
      rw [map_sum (starRingEnd ℂ), Finset.mul_sum]
      simp
    _ = ∑ i : ι, ∑ x : G, φ x * star (g i x) := by
      exact Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
        (f := fun x i => φ x * star (g i x))

/-- The scalar product of two irreducibles is `1` if they are equal and `0`
otherwise. -/
public theorem scalarProduct_irr_ite {χ ψ : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ) (hψ : IsIrreducibleCharacter ψ) :
    scalarProduct G χ ψ = if χ = ψ then 1 else 0 := by
  classical
  by_cases h : χ = ψ
  · rw [← h]
    simp
    exact scalarProduct_irreducible_self hχ
  · simp [h]
    exact scalarProduct_irreducible_orthogonal hχ hψ h

/-- Expansion of the scalar product of two two-term sums. -/
public theorem scalarProduct_expand_four [Group G] (a b c d : ℂ)
    (χ₁ χ₂ ψ₁ ψ₂ : ClassFunction G) :
    scalarProduct G (a • χ₁ + b • χ₂) (c • ψ₁ + d • ψ₂) =
      a * (scalarProduct G χ₁ ψ₁ * star c + scalarProduct G χ₁ ψ₂ * star d) +
      b * (scalarProduct G χ₂ ψ₁ * star c + scalarProduct G χ₂ ψ₂ * star d) := by
  simp [scalarProduct_add_left, scalarProduct_smul_left, scalarProduct_add_right,
    scalarProduct_smul_right]
  ring

/-- The scalar product of an irreducible with a decomposed generalized
character: `(χ, Σᵢ mᵢ·χᵢ) = Σᵢ mᵢ·(χ,χᵢ)`. -/
public theorem scalarProduct_decomp_left {ι : Type*} [Fintype ι]
    {χs : ι → ClassFunction G} {ms : ι → ℤ} {χ : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ) (hχs : ∀ i, IsIrreducibleCharacter (χs i)) :
    scalarProduct G χ (∑ i, (ms i : ℂ) • χs i) =
      ∑ i, (ms i : ℂ) * (if χs i = χ then 1 else 0) := by
  classical
  rw [scalarProduct_sum_right]
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [scalarProduct_smul_right, scalarProduct_irr_ite hχ (hχs i)]
  by_cases h : χs i = χ
  · simp [h]
  · have hne : χ ≠ χs i := fun h' => h h'.symm
    simp [h, hne]

/-- The scalar product of two decomposed generalized characters. -/
public theorem scalarProduct_decomp_cross {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ]
    {χs : ι → ClassFunction G} {ms : ι → ℤ} {ψs : κ → ClassFunction G} {ns : κ → ℤ}
    (hχ : ∀ i, IsIrreducibleCharacter (χs i)) (hψ : ∀ j, IsIrreducibleCharacter (ψs j)) :
    scalarProduct G (∑ i, (ms i : ℂ) • χs i) (∑ j, (ns j : ℂ) • ψs j) =
      ∑ i, ∑ j, (ms i : ℂ) * (ns j : ℂ) * (if χs i = ψs j then 1 else 0) := by
  classical
  calc
    scalarProduct G (∑ i, (ms i : ℂ) • χs i) (∑ j, (ns j : ℂ) • ψs j)
        = ∑ i, scalarProduct G ((ms i : ℂ) • χs i) (∑ j, (ns j : ℂ) • ψs j) := by
            rw [scalarProduct_sum_left]
    _ = ∑ i, (ms i : ℂ) * scalarProduct G (χs i) (∑ j, (ns j : ℂ) • ψs j) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [scalarProduct_smul_left]
    _ = ∑ i, (ms i : ℂ) * (∑ j, scalarProduct G (χs i) ((ns j : ℂ) • ψs j)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            congr 1
            rw [scalarProduct_sum_right]
    _ = ∑ i, ∑ j, (ms i : ℂ) * (ns j : ℂ) * (if χs i = ψs j then 1 else 0) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro j hj
            rw [scalarProduct_smul_right, scalarProduct_irr_ite (hχ i) (hψ j)]
            by_cases h : χs i = ψs j
            · simp [h]
            · simp [h]

/-- The norm of a decomposed generalized character is the sum of the squared
multiplicities. -/
public theorem normSq_decomp {ι : Type*} [Fintype ι]
    {χs : ι → ClassFunction G} {ms : ι → ℤ}
    (hχ : ∀ i, IsIrreducibleCharacter (χs i)) (hdist : ∀ i j, i ≠ j → χs i ≠ χs j) :
    normSq G (∑ i, (ms i : ℂ) • χs i) = ∑ i, (ms i : ℂ) * (ms i : ℂ) := by
  classical
  unfold normSq
  calc
    scalarProduct G (∑ i, (ms i : ℂ) • χs i) (∑ i, (ms i : ℂ) • χs i)
        = ∑ i, ∑ j, (ms i : ℂ) * (ms j : ℂ) * (if χs i = χs j then 1 else 0) :=
          scalarProduct_decomp_cross hχ hχ
    _ = ∑ i, (ms i : ℂ) * (ms i : ℂ) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        calc
          (∑ j, (ms i : ℂ) * (ms j : ℂ) * (if χs i = χs j then 1 else 0))
              = (ms i : ℂ) * (ms i : ℂ) * (if χs i = χs i then 1 else 0) := by
                  refine Finset.sum_eq_single (s := Finset.univ)
                    (f := fun j => (ms i : ℂ) * (ms j : ℂ) * (if χs i = χs j then 1 else 0)) i ?_ ?_
                  · intro b hb hbi
                    have hne : χs i ≠ χs b := hdist i b hbi.symm
                    simp [hne]
                  · intro hnot
                    exfalso
                    exact hnot (Finset.mem_univ i)
          _ = (ms i : ℂ) * (ms i : ℂ) := by simp

end DecompScalar

/-! ## Decomposition of characters into irreducibles -/

section Decomposition

variable {G : Type u} [Group G]

/-- Irreducibility is preserved by equivalence of representations. -/
public theorem isIrreducible_equiv {V : Type v} {W : Type w} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (φ : ρ.Equiv σ) : Representation.IsIrreducible ρ ↔ Representation.IsIrreducible σ := by
  classical
  have e : ρ.asModule ≃ₗ[ℂ[G]] σ.asModule := by
    refine { toFun := φ, invFun := φ.symm, left_inv := φ.left_inv, right_inv := φ.right_inv,
             map_add' := φ.map_add, map_smul' := ?_ }
    intro a v
    induction a using MonoidAlgebra.induction_linear with
    | zero =>
        exact add_right_cancel (a := φ 0) (b := φ 0) (c := 0)
          (by simpa using (φ.map_add' 0 0).symm)
    | add x y hx hy =>
        rw [add_smul]
        have hsplit : φ (x • v + y • v) = φ (x • v) + φ (y • v) := by
          exact φ.map_add _ _
        rw [hsplit, hx, hy]
        simp only [RingHom.id_apply]
        let wv : σ.asModule := φ v
        exact (add_smul x y wv).symm
    | single g c =>
        simp only [RingHom.id_apply, Representation.single_smul]
        rw [map_smul]
        let wv : σ.asModule := φ v
        have hσ := Representation.single_smul σ c g wv
        have hφ : φ ((ρ g) (ρ.asModuleEquiv v)) = (σ g) (φ (ρ.asModuleEquiv v)) :=
          congrFun (congrArg (fun f : V →ₗ[ℂ] W => (f : V → W)) (φ.isIntertwining' g))
            (ρ.asModuleEquiv v)
        change (c • (φ ((ρ g) (ρ.asModuleEquiv v)) : σ.asModule)) =
          MonoidAlgebra.single g c • wv
        let z : σ.asModule := c • ((σ g) (φ (ρ.asModuleEquiv v)) : σ.asModule)
        have hleft : (c • (φ ((ρ g) (ρ.asModuleEquiv v)) : σ.asModule)) = z := by
          exact congrArg (fun z : W => (c • z : σ.asModule)) hφ
        have hright : z = MonoidAlgebra.single g c • wv := by
          convert hσ.symm using 1 <;> rfl
        exact hleft.trans hright
  rw [Representation.irreducible_iff_isSimpleModule_asModule,
    Representation.irreducible_iff_isSimpleModule_asModule]
  exact LinearEquiv.isSimpleModule_iff e

/-- Given complementary subrepresentations `W`, `W'`, the representation splits
as their direct sum. -/
public lemma coprod_equiv_of_isCompl {V : Type v} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (W W' : Subrepresentation ρ)
    (hcompl : IsCompl (W.asSubmodule) (W'.asSubmodule)) :
    ∃ e : (W.toSubmodule × W'.toSubmodule) ≃ₗ[ℂ] V,
      ∀ g : G, e ∘ₗ ((W.toRepresentation g).prodMap (W'.toRepresentation g)) = (ρ g) ∘ₗ e := by
  classical
  let : Module ℂ[G] V := (inferInstance : Module ℂ[G] ρ.asModule)
  let f : (W.toSubmodule × W'.toSubmodule) →ₗ[ℂ] V :=
    LinearMap.coprod W.toSubmodule.subtype W'.toSubmodule.subtype
  have hinj : Function.Injective f := by
    intro p q hpq
    have hpq' : (p.1 : V) + (p.2 : V) = (q.1 : V) + (q.2 : V) := by
      simpa [f, LinearMap.coprod_apply] using hpq
    have hsub : (p.1 : V) - (q.1 : V) = (q.2 : V) - (p.2 : V) := by
      calc
        (p.1 : V) - (q.1 : V) = (p.1 : V) + (p.2 : V) - (q.1 : V) - (p.2 : V) := by abel
        _ = (q.1 : V) + (q.2 : V) - (q.1 : V) - (p.2 : V) := by rw [hpq']
        _ = (q.2 : V) - (p.2 : V) := by abel
    have hmemW : (p.1 : V) - (q.1 : V) ∈ (W.toSubmodule : Submodule ℂ V) := by
      exact W.toSubmodule.sub_mem p.1.2 q.1.2
    have hmemW' : (p.1 : V) - (q.1 : V) ∈ (W'.toSubmodule : Submodule ℂ V) := by
      rw [hsub]
      exact W'.toSubmodule.sub_mem q.2.2 p.2.2
    have hzero : (p.1 : V) - (q.1 : V) = 0 := by
      have hmem : (p.1 : V) - (q.1 : V) ∈ (W.asSubmodule ⊓ W'.asSubmodule : Submodule ℂ[G] ρ.asModule) := by
        exact (Submodule.mem_inf (R := ℂ[G]) (M := ρ.asModule)).mpr ⟨by simpa [Subrepresentation.mem_asSubmodule_iff],
          by simpa [Subrepresentation.mem_asSubmodule_iff]⟩
      have hinf : W.asSubmodule ⊓ W'.asSubmodule = ⊥ :=
        hcompl.disjoint.eq_bot
      rw [hinf] at hmem
      exact (Submodule.mem_bot (R := ℂ[G]) (M := ρ.asModule)).1 hmem
    have hp1 : p.1 = q.1 := Subtype.ext (sub_eq_zero.mp hzero)
    have hzero' : (q.2 : V) - (p.2 : V) = 0 := by
      simpa [hsub] using hzero
    have hp2 : p.2 = q.2 := Subtype.ext (sub_eq_zero.mp hzero').symm
    exact Prod.ext hp1 hp2
  have hsurj : Function.Surjective f := by
    intro v
    have hv' : (v : ρ.asModule) ∈ (W.asSubmodule ⊔ W'.asSubmodule : Submodule ℂ[G] ρ.asModule) := by
      have hcod : W.asSubmodule ⊔ W'.asSubmodule = ⊤ :=
        top_le_iff.mp hcompl.codisjoint.top_le
      rw [hcod]
      exact Submodule.mem_top (R := ℂ[G]) (M := ρ.asModule)
    rcases (Submodule.mem_sup (R := ℂ[G]) (M := ρ.asModule)).mp hv' with ⟨a, ha, b, hb, hab⟩
    refine ⟨⟨⟨a, by
        change a ∈ (W : Set V)
        exact (Subrepresentation.mem_asSubmodule_iff (σ := W)).mp ha⟩,
             ⟨b, by
        change b ∈ (W' : Set V)
        exact (Subrepresentation.mem_asSubmodule_iff (σ := W')).mp hb⟩⟩, ?_⟩
    change (a : V) + (b : V) = v
    exact hab
  let e : (W.toSubmodule × W'.toSubmodule) ≃ₗ[ℂ] V :=
    LinearEquiv.ofBijective f ⟨hinj, hsurj⟩
  refine ⟨e, ?_⟩
  intro g
  ext p
  · change f (((W.toRepresentation g).prodMap (W'.toRepresentation g)) (p, 0)) =
      (ρ g) (f (p, 0))
    simp [f, LinearMap.coprod_apply, Subrepresentation.toRepresentation]
  · change f (((W.toRepresentation g).prodMap (W'.toRepresentation g)) (0, p)) =
      (ρ g) (f (0, p))
    simp [f, LinearMap.coprod_apply, Subrepresentation.toRepresentation]

/-- The character of a representation with complementary subrepresentations is
the sum of the two sub-characters. -/
public lemma char_eq_add_of_isCompl {V : Type v} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [Fintype G] {ρ : Representation ℂ G V} (W W' : Subrepresentation ρ)
    (hcompl : IsCompl (W.asSubmodule) (W'.asSubmodule)) :
    ρ.character = W.toRepresentation.character + W'.toRepresentation.character := by
  rcases coprod_equiv_of_isCompl W W' hcompl with ⟨e, he⟩
  have he' : ∀ g : G, e ∘ₗ ((W.toRepresentation.prod W'.toRepresentation) g) = (ρ g) ∘ₗ e := by
    intro g
    simpa [Representation.prod] using he g
  have heq : (W.toRepresentation.prod W'.toRepresentation).Equiv ρ :=
    Representation.Equiv.mk e he'
  calc
    ρ.character = (W.toRepresentation.prod W'.toRepresentation).character :=
      (Representation.char_iso heq).symm
    _ = W.toRepresentation.character + W'.toRepresentation.character :=
      char_prod W.toRepresentation W'.toRepresentation

/-- Add a pair `(χ, m)` to a catalog of irreducible characters with
multiplicities, merging with an existing occurrence of `χ`. -/
public noncomputable def addPair [DecidableEq (ClassFunction G)] (χ : ClassFunction G)
    (m : ℕ) : List (ClassFunction G × ℕ) → List (ClassFunction G × ℕ)
  | [] => [(χ, m)]
  | (p, k) :: rest => if p = χ then (p, k + m) :: rest else (p, k) :: addPair χ m rest

/-- The sum over a catalog is increased by `m • χ` after adding `(χ, m)`. -/
public lemma addPair_sum [Group G] [DecidableEq (ClassFunction G)]
    (χ : ClassFunction G) (m : ℕ)
    (acc : List (ClassFunction G × ℕ)) :
    ((addPair χ m acc).map (fun p => (p.2 : ℂ) • p.1)).sum =
      (acc.map (fun p => (p.2 : ℂ) • p.1)).sum + (m : ℂ) • χ := by
  induction acc with
  | nil => simp [addPair]
  | cons p rest ih =>
      by_cases hp : p.1 = χ
      · simp [addPair, hp]
        rw [add_smul]
        ring
      · simp [addPair, hp, ih]
        ring

/-- Membership in the first components of `addPair`: the element is either the
merged character or already present. -/
public lemma mem_map_addPair_fst [Group G] [DecidableEq (ClassFunction G)]
    (χ : ClassFunction G) (m : ℕ)
    {acc : List (ClassFunction G × ℕ)} {x : ClassFunction G} :
    x ∈ (addPair χ m acc).map Prod.fst → x = χ ∨ x ∈ acc.map Prod.fst := by
  induction acc with
  | nil => simp [addPair]
  | cons p rest ih =>
      intro h
      by_cases hp : p.1 = χ
      · have hmem : x ∈ (p.1 :: rest.map Prod.fst) := by
          simpa [addPair, hp] using h
        rcases List.mem_cons.mp hmem with h | h
        · left
          simpa [hp] using h
        · right
          exact List.mem_cons_of_mem p.1 h
      · have hmem : x ∈ (p.1 :: (addPair χ m rest).map Prod.fst) := by
          simpa [addPair, hp] using h
        rcases List.mem_cons.mp hmem with h | h
        · right
          simp [h]
        · rcases ih h with h | h
          · left
            exact h
          · right
            exact List.mem_cons_of_mem p.1 h

/-- The first components of a catalog remain distinct after adding a pair. -/
public lemma addPair_nodup [DecidableEq (ClassFunction G)] (χ : ClassFunction G) (m : ℕ)
    (acc : List (ClassFunction G × ℕ)) (h : (acc.map Prod.fst).Nodup) :
    ((addPair χ m acc).map Prod.fst).Nodup := by
  induction acc with
  | nil => simp [addPair]
  | cons p rest ih =>
      have hrest : (rest.map Prod.fst).Nodup := h.tail
      by_cases hp : p.1 = χ
      · simpa [addPair, hp] using h
      · have hnod : ((addPair χ m rest).map Prod.fst).Nodup := ih hrest
        simp [addPair, hp]
        refine ⟨?_, hnod⟩
        intro x hx
        have hmem' : p.1 ∈ (addPair χ m rest).map Prod.fst :=
          List.mem_map.mpr ⟨(p.1, x), hx, rfl⟩
        rcases mem_map_addPair_fst χ m hmem' with hx | hx
        · exact hp hx
        · exact (List.nodup_cons.mp h).1 hx

/-- Adding a pair preserves the irreducibility of all catalog entries. -/
public lemma addPair_mem [DecidableEq (ClassFunction G)] (χ : ClassFunction G) (m : ℕ)
    (acc : List (ClassFunction G × ℕ)) (hχ : IsIrreducibleCharacter χ)
    (hacc : ∀ p ∈ acc, IsIrreducibleCharacter p.1) :
    ∀ p ∈ addPair χ m acc, IsIrreducibleCharacter p.1 := by
  intro p₀ hp₀
  induction acc with
  | nil =>
      simp [addPair] at hp₀
      rcases hp₀ with rfl
      exact hχ
  | cons q rest ih =>
      by_cases hq : q.1 = χ
      · simp [addPair, hq] at hp₀
        rcases hp₀ with h | hp₀
        · subst p₀
          exact hχ
        · exact hacc p₀ (List.mem_cons_of_mem q hp₀)
      · simp [addPair, hq] at hp₀
        rcases hp₀ with h | hp₀
        · subst p₀
          exact hacc q (by simp)
        · exact ih (fun r hr => hacc r (List.mem_cons_of_mem q hr)) hp₀

/-- Merge two catalogs. -/
public noncomputable def mergeCats [DecidableEq (ClassFunction G)]
    (A B : List (ClassFunction G × ℕ)) : List (ClassFunction G × ℕ) :=
  B.foldl (fun acc q => addPair q.1 q.2 acc) A

/-- The sum over a merged catalog is the sum of the two sums. -/
public lemma mergeCats_sum [DecidableEq (ClassFunction G)]
    (A B : List (ClassFunction G × ℕ)) :
    ((mergeCats A B).map (fun p => (p.2 : ℂ) • p.1)).sum =
      (A.map (fun p => (p.2 : ℂ) • p.1)).sum +
        (B.map (fun p => (p.2 : ℂ) • p.1)).sum := by
  classical
  induction B generalizing A with
  | nil => simp [mergeCats]
  | cons q t ih =>
      rw [mergeCats, List.foldl_cons]
      rw [← mergeCats]
      rw [ih]
      rw [addPair_sum, List.map_cons, List.sum_cons]
      ring

/-- First components remain distinct across a merge. -/
public lemma mergeCats_nodup [DecidableEq (ClassFunction G)]
    (A B : List (ClassFunction G × ℕ)) (hA : (A.map Prod.fst).Nodup)
    (hB : (B.map Prod.fst).Nodup) : ((mergeCats A B).map Prod.fst).Nodup := by
  classical
  induction B generalizing A with
  | nil => simpa [mergeCats] using hA
  | cons q t ih =>
      rw [mergeCats, List.foldl_cons]
      exact ih (addPair q.1 q.2 A) (addPair_nodup q.1 q.2 A hA) hB.tail

/-- The character `χ` itself appears among the first components after adding a pair. -/
public lemma mem_map_addPair_fst_self [Group G] [DecidableEq (ClassFunction G)]
    (χ : ClassFunction G)
    (m : ℕ) (acc : List (ClassFunction G × ℕ)) :
    χ ∈ (addPair χ m acc).map Prod.fst := by
  induction acc with
  | nil => simp [addPair]
  | cons p rest ih =>
      by_cases hp : p.1 = χ
      · simp [addPair, hp]
      · simpa [addPair, hp] using (Or.inr ih)

/-- The first components of `A` are contained in those of the merge. -/
public lemma mergeCats_fst_subset [Group G] [DecidableEq (ClassFunction G)]
    (A B : List (ClassFunction G × ℕ)) :
    A.map Prod.fst ⊆ (mergeCats A B).map Prod.fst := by
  classical
  induction B generalizing A with
  | nil => simp [mergeCats]
  | cons q t ih =>
      rw [mergeCats, List.foldl_cons]
      have hsub1 : A.map Prod.fst ⊆ (addPair q.1 q.2 A).map Prod.fst := by
        induction A with
        | nil => simp [addPair]
        | cons p rest ihA =>
            by_cases hp : p.1 = q.1
            · simp [addPair, hp]
            · simp [addPair, hp]
              intro x hx
              simp at hx ⊢
              rcases hx with ⟨x₁, hx₁⟩
              right
              have hmem : x ∈ rest.map Prod.fst := List.mem_map.mpr ⟨(x, x₁), hx₁, rfl⟩
              simpa using ihA hmem
      exact List.Subset.trans hsub1 (ih (addPair q.1 q.2 A))

/-- Merging preserves the irreducibility of all catalog entries. -/
public lemma mergeCats_mem [DecidableEq (ClassFunction G)]
    (A B : List (ClassFunction G × ℕ))
    (hA : ∀ p ∈ A, IsIrreducibleCharacter p.1)
    (hB : ∀ p ∈ B, IsIrreducibleCharacter p.1) :
    ∀ p ∈ mergeCats A B, IsIrreducibleCharacter p.1 := by
  classical
  induction B generalizing A with
  | nil => simpa [mergeCats] using hA
  | cons q t ih =>
      rw [mergeCats, List.foldl_cons]
      exact ih (addPair q.1 q.2 A) (addPair_mem q.1 q.2 A (hB q (by simp)) hA)
        (fun p hp => hB p (List.mem_cons_of_mem q hp))

/-- The multiplicity of a character in a catalog. -/
public noncomputable def mult [DecidableEq (ClassFunction G)]
    (l : List (ClassFunction G × ℕ)) (χ : ClassFunction G) : ℤ :=
  ((l.filter (fun p => p.1 = χ)).map (fun p => (p.2 : ℤ))).sum

/-- The multiplicity of a character absent from the catalog is zero. -/
public lemma mult_eq_zero [Group G] [DecidableEq (ClassFunction G)]
    {l : List (ClassFunction G × ℕ)}
    {χ : ClassFunction G} (h : χ ∉ l.map Prod.fst) : mult l χ = 0 := by
  unfold mult
  have hf : (l.filter (fun p => p.1 = χ)) = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro p hp
    have hb : decide (p.1 = χ) = true := (List.mem_filter.mp hp).2
    have hpc : p.1 = χ := decide_eq_true_eq.mp hb
    exact h (List.mem_map.mpr ⟨p, (List.mem_filter.mp hp).1, hpc⟩)
  simp [hf]

/-- Reindexing: the sum over a catalog equals the sum over its distinct
characters of (multiplicity · character). -/
public lemma sum_pairs_reindex [Group G] [DecidableEq (ClassFunction G)]
    (l : List (ClassFunction G × ℕ)) (hnod : (l.map Prod.fst).Nodup) :
    (l.map (fun p => (p.2 : ℂ) • p.1)).sum =
      ((l.map Prod.fst).toFinset).sum (fun χ => (mult l χ : ℂ) • χ) := by
  classical
  induction l with
  | nil => simp [mult]
  | cons p rest ih =>
      have hrest : (rest.map Prod.fst).Nodup := hnod.tail
      have hpnot : p.1 ∉ rest.map Prod.fst := (List.nodup_cons.mp hnod).1
      rw [List.map_cons, List.sum_cons, ih hrest]
      rw [List.map_cons]
      rw [List.toFinset_cons]
      rw [Finset.sum_insert (by simpa [List.mem_toFinset] using hpnot)]
      have hmp : mult (p :: rest) p.1 = (p.2 : ℤ) := by
        unfold mult
        have hf : (rest.filter (fun q => q.1 = p.1)) = [] := by
          apply List.eq_nil_iff_forall_not_mem.mpr
          intro q hq
          rw [List.mem_filter] at hq
          rcases hq with ⟨hq, hqdec⟩
          have hqeq : q.1 = p.1 := decide_eq_true_eq.mp hqdec
          exact hpnot (List.mem_map.mpr ⟨q, hq, hqeq⟩)
        rw [List.filter_cons_of_pos]
        · simp [hf]
        · rw [decide_eq_true_eq]
      have hmc : ∀ χ : ClassFunction G, χ ∈ (rest.map Prod.fst).toFinset →
          mult (p :: rest) χ = mult rest χ := by
        intro χ hχ
        have hpχ : p.1 ≠ χ := by
          intro hpc
          exact hpnot (by simpa [hpc] using (List.mem_toFinset.mp hχ))
        unfold mult
        rw [List.filter_cons_of_neg]
        · intro h
          exact hpχ (decide_eq_true_eq.mp h)
      rw [hmp]
      congr 1
      refine Finset.sum_congr rfl ?_
      intro χ hχ
      rw [hmc χ (by simpa [List.mem_toFinset] using hχ)]

/-- Every character is a finite sum of irreducible characters with nonnegative
integer multiplicities; the catalog has distinct entries. -/
public theorem char_decomp {V : Type v} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [Fintype G] (ρ : Representation ℂ G V) :
    ∃ cs : List (ClassFunction G × ℕ),
      (∀ p ∈ cs, IsIrreducibleCharacter p.1) ∧
      (List.Nodup (cs.map Prod.fst)) ∧
      ρ.character = (cs.map (fun p => (p.2 : ℂ) • p.1)).sum := by
  classical
  let P : ℕ → Prop := fun d => ∀ ⦃V : Type v⦄ [AddCommGroup V] [Module ℂ V]
      [FiniteDimensional ℂ V], Module.finrank ℂ V = d → ∀ ρ : Representation ℂ G V,
        ∃ cs : List (ClassFunction G × ℕ),
          (∀ p ∈ cs, IsIrreducibleCharacter p.1) ∧ (List.Nodup (cs.map Prod.fst)) ∧
          ρ.character = (cs.map (fun p => (p.2 : ℂ) • p.1)).sum
  have hP : ∀ d : ℕ, P d := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        intro V _ _ _ hd ρ
        by_cases hsub : Subsingleton V
        · refine ⟨[], by simp, by simp, ?_⟩
          funext g
          have h0 : ρ g = 0 := Subsingleton.elim _ _
          simp [Representation.character, h0]
        · by_cases hρ : Representation.IsIrreducible ρ
          · let n : ℕ := Module.finrank ℂ V
            let b := Module.Free.chooseBasis ℂ V
            let eι : Module.Free.ChooseBasisIndex ℂ V ≃ Fin n :=
              Fintype.equivFinOfCardEq (Module.finrank_eq_card_chooseBasisIndex ℂ V).symm
            let e : V ≃ₗ[ℂ] (Fin n → ℂ) :=
              (b.repr).trans ((Finsupp.linearEquivFunOnFinite ℂ ℂ (Module.Free.ChooseBasisIndex ℂ V)).trans
                (LinearEquiv.funCongrLeft ℂ ℂ eι.symm))
            refine ⟨[(ρ.character, 1)], ?_, by simp, by simp⟩
            intro p hp
            simp at hp
            rcases hp with rfl
            refine ⟨n, charTrans e ρ, ?_, ?_⟩
            · exact (isIrreducible_equiv (equiv_charTrans e ρ)).1 hρ
            · exact Representation.char_iso (equiv_charTrans e ρ)
          · have hρ' : ¬ IsSimpleModule ℂ[G] ρ.asModule := by
              rwa [← Representation.irreducible_iff_isSimpleModule_asModule]
            have hnot : ¬ IsSimpleOrder (Submodule ℂ[G] ρ.asModule) := by
              rwa [isSimpleModule_iff] at hρ'
            have hnon : Nontrivial (Submodule ℂ[G] ρ.asModule) := by
              refine ⟨⊥, ⊤, ?_⟩
              intro h
              apply hsub
              refine ⟨fun x y => ?_⟩
              have hxy : (x - y : V) ∈ (⊥ : Submodule ℂ[G] ρ.asModule) := by
                rw [h]
                exact Submodule.mem_top (R := ℂ[G]) (M := ρ.asModule) (x := x - y)
              exact sub_eq_zero.mp ((Submodule.mem_bot (R := ℂ[G]) (M := ρ.asModule)).1 hxy)
            have hmid : ∃ W : Submodule ℂ[G] ρ.asModule, W ≠ ⊥ ∧ W ≠ ⊤ := by
              by_contra h
              push Not at h
              apply hnot
              let : Nontrivial (Submodule ℂ[G] ρ.asModule) := hnon
              exact IsSimpleOrder.of_forall_eq_top h
            rcases hmid with ⟨W, hWbot, hWtop⟩
            let : Finite G := Finite.of_fintype G
            let W' : Submodule ℂ[G] ρ.asModule := (MonoidAlgebra.Submodule.exists_isCompl W).choose
            have hcompl : IsCompl W W' := (MonoidAlgebra.Submodule.exists_isCompl W).choose_spec
            let Wr : Subrepresentation ρ := Subrepresentation.ofSubmodule' W
            let W'r : Subrepresentation ρ := Subrepresentation.ofSubmodule' W'
            have hWrTop : Wr.toSubmodule ≠ ⊤ := by
              intro h
              apply hWtop
              have htop : Wr = (⊤ : Subrepresentation ρ) := by
                exact Subrepresentation.toSubmodule_injective h
              exact congrArg Subrepresentation.asSubmodule htop
            have hW'top : W' ≠ ⊤ := by
              intro hW'top
              apply hWbot
              have hle : W ≤ (⊥ : Submodule ℂ[G] ρ.asModule) := by
                simpa [hW'top] using hcompl.disjoint
              exact le_bot_iff.mp hle
            have hW'rTop : W'r.toSubmodule ≠ ⊤ := by
              intro h
              apply hW'top
              have htop : W'r = (⊤ : Subrepresentation ρ) := by
                exact Subrepresentation.toSubmodule_injective h
              exact congrArg Subrepresentation.asSubmodule htop
            have hWfin : Module.finrank ℂ Wr.toSubmodule < Module.finrank ℂ V := by
              exact Submodule.finrank_lt hWrTop
            have hW'fin : Module.finrank ℂ W'r.toSubmodule < Module.finrank ℂ V := by
              exact Submodule.finrank_lt hW'rTop
            rcases ih (Module.finrank ℂ Wr.toSubmodule) (by simpa [hd] using hWfin)
              (V := Wr.toSubmodule) rfl (Wr.toRepresentation) with ⟨csW, hcsW, hnodW, hsumW⟩
            rcases ih (Module.finrank ℂ W'r.toSubmodule) (by simpa [hd] using hW'fin)
              (V := W'r.toSubmodule) rfl (W'r.toRepresentation) with ⟨csW', hcsW', hnodW', hsumW'⟩
            refine ⟨mergeCats csW csW', ?_, ?_, ?_⟩
            · exact mergeCats_mem csW csW' hcsW hcsW'
            · exact mergeCats_nodup csW csW' hnodW hnodW'
            · calc
                ρ.character = Wr.toRepresentation.character + W'r.toRepresentation.character :=
                  char_eq_add_of_isCompl Wr W'r hcompl
                _ = (csW.map (fun p => (p.2 : ℂ) • p.1)).sum +
                    (csW'.map (fun p => (p.2 : ℂ) • p.1)).sum := by rw [hsumW, hsumW']
                _ = ((mergeCats csW csW').map (fun p => (p.2 : ℂ) • p.1)).sum := by
                      exact (mergeCats_sum csW csW').symm
  exact hP (Module.finrank ℂ V) (V := V) rfl ρ

-- The first components of `B` are contained in those of the merge.
public lemma mergeCats_snd_subset [DecidableEq (ClassFunction G)]
    (A B : List (ClassFunction G × ℕ)) :
    B.map Prod.fst ⊆ (mergeCats A B).map Prod.fst := by
  classical
  induction B generalizing A with
  | nil => simp [mergeCats]
  | cons q t ih =>
      rw [mergeCats, List.foldl_cons]
      intro x hx
      rw [List.map_cons, List.mem_cons] at hx
      rcases hx with hx | hx
      · rw [hx]
        exact mergeCats_fst_subset (addPair q.1 q.2 A) t
          (mem_map_addPair_fst_self q.1 q.2 A)
      · exact ih (addPair q.1 q.2 A) hx

/-- Every generalized character is a finite sum of distinct irreducible
characters with integer multiplicities. -/
public theorem char_decomp_generalized {G : Type u} [Group G] [Fintype G]
    {φ : ClassFunction G} (hφ : IsGeneralizedCharacter φ) :
    ∃ (ι : Type (max 0 u)) (_ : Fintype ι) (χs : ι → ClassFunction G) (ms : ι → ℤ),
      (∀ i, IsIrreducibleCharacter (χs i)) ∧
      (∀ i j, i ≠ j → χs i ≠ χs j) ∧
      φ = ∑ i, (ms i : ℂ) • χs i := by
  classical
  rcases hφ with ⟨δ₁, δ₂, hδ₁, hδ₂, hφeq⟩
  rcases hδ₁ with ⟨n₁, ρ₁, hρ₁eq⟩
  rcases hδ₂ with ⟨n₂, ρ₂, hρ₂eq⟩
  rcases char_decomp ρ₁ with ⟨cs₁, hcs₁, hnod₁, hsum₁⟩
  rcases char_decomp ρ₂ with ⟨cs₂, hcs₂, hnod₂, hsum₂⟩
  let cs := mergeCats cs₁ cs₂
  have hnod : (cs.map Prod.fst).Nodup := mergeCats_nodup cs₁ cs₂ hnod₁ hnod₂
  let ι : Type (max 0 u) := {χ : ClassFunction G // χ ∈ (cs.map Prod.fst).toFinset}
  let χs : ι → ClassFunction G := fun χ => χ.1
  let ms : ι → ℤ := fun χ => mult cs₁ χ.1 - mult cs₂ χ.1
  have h1 : (cs₁.map (fun p => (p.2 : ℂ) • p.1)).sum =
      ((cs.map Prod.fst).toFinset).sum (fun χ => (mult cs₁ χ : ℂ) • χ) := by
    rw [sum_pairs_reindex cs₁ hnod₁]
    refine Finset.sum_subset ?_ ?_
    · intro χ hχ
      rw [List.mem_toFinset] at hχ ⊢
      exact mergeCats_fst_subset cs₁ cs₂ hχ
    · intro χ hχ hnot
      simp [mult_eq_zero (by simpa [List.mem_toFinset] using hnot)]
  have h2 : (cs₂.map (fun p => (p.2 : ℂ) • p.1)).sum =
      ((cs.map Prod.fst).toFinset).sum (fun χ => (mult cs₂ χ : ℂ) • χ) := by
    rw [sum_pairs_reindex cs₂ hnod₂]
    refine Finset.sum_subset ?_ ?_
    · intro χ hχ
      rw [List.mem_toFinset] at hχ ⊢
      exact mergeCats_snd_subset cs₁ cs₂ hχ
    · intro χ hχ hnot
      simp [mult_eq_zero (by simpa [List.mem_toFinset] using hnot)]
  refine ⟨ι, inferInstance, χs, ms, ?_, ?_, ?_⟩
  · intro i
    rcases List.mem_map.mp (List.mem_toFinset.mp i.2) with ⟨p, hp, hpi⟩
    simpa [χs, hpi] using mergeCats_mem cs₁ cs₂ hcs₁ hcs₂ p hp
  · intro i j hij hEq
    apply hij
    exact Subtype.ext (by simpa [χs] using hEq)
  · calc
      φ = δ₁ - δ₂ := hφeq
      _ = ρ₁.character - ρ₂.character := by rw [hρ₁eq, hρ₂eq]
      _ = (cs₁.map (fun p => (p.2 : ℂ) • p.1)).sum -
          (cs₂.map (fun p => (p.2 : ℂ) • p.1)).sum := by rw [hsum₁, hsum₂]
      _ = ((cs.map Prod.fst).toFinset).sum (fun χ => (mult cs₁ χ : ℂ) • χ) -
          ((cs.map Prod.fst).toFinset).sum (fun χ => (mult cs₂ χ : ℂ) • χ) := by rw [h1, h2]
      _ = ∑ i : ι, (ms i : ℂ) • χs i := by
            rw [← Finset.sum_sub_distrib]
            rw [← Finset.sum_coe_sort]
            congr 1
            funext χ
            simp [ms, χs, ← sub_smul, Int.cast_sub]

/-! ## Decomposition: norms and coefficient extraction -/

variable [Fintype G]

/-- The star-form product equals the `g⁻¹`-form product when the second argument is a character. -/
public lemma scalarProduct_eq_characterProduct_of_char {χ ψ : ClassFunction G}
    (hψ : IsCharacter ψ) : scalarProduct G χ ψ = characterProduct G χ ψ := by
  unfold scalarProduct characterProduct
  congr 1
  refine Finset.sum_congr rfl ?_
  intro g hg
  rw [star_char_eq_char_inv hψ g]

/-- The star-form self-product of an irreducible character is 1. -/
public lemma irreducible_scalarProduct_self {χ : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ) : scalarProduct G χ χ = 1 := by
  rw [scalarProduct_eq_characterProduct_of_char (isCharacter_of_isIrreducibleCharacter hχ)]
  exact irreducibleCharacter_self hχ

/-- Star-form orthogonality of distinct irreducible characters. -/
public lemma irreducible_scalarProduct_of_ne {χ ψ : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ) (hψ : IsIrreducibleCharacter ψ) (h : χ ≠ ψ) :
    scalarProduct G χ ψ = 0 := by
  rw [scalarProduct_eq_characterProduct_of_char (isCharacter_of_isIrreducibleCharacter hψ)]
  exact irreducibleCharacters_orthogonal hχ hψ h

/-- The star-form norm of a decomposition with distinct irreducibles equals the sum of the
squared coefficients. -/
public lemma decomp_scalarProduct {ι : Type v} [Fintype ι]
    {χs : ι → ClassFunction G} {ms : ι → ℤ}
    (hirr : ∀ i, IsIrreducibleCharacter (χs i))
    (hdist : ∀ i j, i ≠ j → χs i ≠ χs j) :
    scalarProduct G (∑ i, (ms i : ℂ) • χs i) (∑ i, (ms i : ℂ) • χs i) =
      ∑ i, ((ms i : ℤ) : ℂ)^2 := by
  classical
  rw [scalarProduct_sum_left]
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [scalarProduct_smul_left]
  rw [scalarProduct_sum_right]
  calc
    (ms i : ℂ) * (∑ j, scalarProduct G (χs i) ((ms j : ℂ) • χs j))
        = (ms i : ℂ) * (∑ j, scalarProduct G (χs i) (χs j) * star (ms j : ℂ)) := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro j hj
            exact scalarProduct_smul_right (ms j : ℂ) (χs i) (χs j)
    _ = (ms i : ℂ) * (scalarProduct G (χs i) (χs i) * star (ms i : ℂ)) := by
            congr 1
            refine Finset.sum_eq_single i ?_ ?_
            · intro j hj hji
              have hsp : scalarProduct G (χs i) (χs j) = 0 := by
                exact irreducible_scalarProduct_of_ne (hirr i) (hirr j) (hdist i j hji.symm)
              simp [hsp]
            · intro hnot
              exact (hnot (Finset.mem_univ i)).elim
    _ = ((ms i : ℤ) : ℂ)^2 := by
            simp [irreducible_scalarProduct_self (hirr i), pow_two]

/-- A sum of squares of integers in `ℂ` equals the same sum in `ℝ`. -/
public lemma int_sq_sum_real {ι : Type v} [Fintype ι] {m : ι → ℤ} {k : ℕ}
    (h : (∑ i, ((m i : ℤ) : ℂ)^2) = (k : ℂ)) :
    (∑ i, ((m i : ℤ) : ℝ)^2) = (k : ℝ) := by
  have hterm : ∀ i, ((m i : ℤ) : ℂ)^2 = (((m i : ℤ) : ℝ)^2 : ℂ) := by
    intro i
    norm_num
  have h' : (∑ i, (((m i : ℤ) : ℝ)^2 : ℂ)) = (k : ℂ) := by
    simpa [hterm] using h
  exact_mod_cast h'

/-- If a sum of squares of integers equals `k`, then each square is at most `k`. -/
public lemma int_sq_sum_bound {ι : Type v} [Fintype ι] {m : ι → ℤ} {k : ℕ}
    (h : (∑ i, ((m i : ℤ) : ℂ)^2) = (k : ℂ)) :
    ∀ i, (m i : ℤ)^2 ≤ (k : ℤ) := by
  intro i
  have hreal : (∑ j, ((m j : ℤ) : ℝ)^2) = (k : ℝ) := int_sq_sum_real h
  have hle : ((m i : ℤ) : ℝ)^2 ≤ (k : ℝ) := by
    have hle' : ((m i : ℤ) : ℝ)^2 ≤ ∑ j, ((m j : ℤ) : ℝ)^2 := by
      exact Finset.single_le_sum (s := Finset.univ) (f := fun j => ((m j : ℤ) : ℝ)^2)
        (fun j hj => sq_nonneg ((m j : ℤ) : ℝ)) (Finset.mem_univ i)
    rw [hreal] at hle'
    exact hle'
  exact_mod_cast hle

/-- If a sum of squares of integers equals `k ≤ 2`, then each integer is `0`, `1`, or `-1`. -/
public lemma int_sq_sum_mem {ι : Type v} [Fintype ι] {m : ι → ℤ} {k : ℕ}
    (hk : k ≤ 2) (h : (∑ i, ((m i : ℤ) : ℂ)^2) = (k : ℂ)) :
    ∀ i, m i = 0 ∨ m i = 1 ∨ m i = -1 := by
  intro i
  have hb := int_sq_sum_bound h i
  have hnat : (m i).natAbs ≤ 1 := by
    have hz : ((m i).natAbs : ℤ)^2 ≤ (k : ℤ) := by
      simpa [Int.natAbs_mul_self] using hb
    have hz' : (m i).natAbs ^ 2 ≤ k := by exact_mod_cast hz
    have hzr : (((m i).natAbs : ℕ) : ℝ)^2 ≤ (k : ℝ) := by exact_mod_cast hz'
    nlinarith [sq_nonneg ((m i).natAbs : ℝ), hk]
  have hcases : (m i).natAbs = 0 ∨ (m i).natAbs = 1 := by omega
  rcases hcases with h0 | h1
  · left
    omega
  · right
    omega

/-- A generalized character of star-norm `1` is a signed irreducible character. -/
public lemma norm_one_signed_irreducible {ψ : ClassFunction G}
    (hψ : IsGeneralizedCharacter ψ) (hnorm : scalarProduct G ψ ψ = 1) :
    ∃ χ, IsIrreducibleCharacter χ ∧ (ψ = χ ∨ ψ = -χ) := by
  classical
  rcases char_decomp_generalized hψ with ⟨ι, _, χs, ms, hirr, hdist, hψsum⟩
  have hsq : (∑ i, ((ms i : ℤ) : ℂ)^2) = ((1 : ℕ) : ℂ) := by
    rw [← decomp_scalarProduct hirr hdist]
    rw [← hψsum]
    simpa using hnorm
  have hmem : ∀ i, ms i = 0 ∨ ms i = 1 ∨ ms i = -1 := int_sq_sum_mem (k := 1) (by norm_num) hsq
  have hex : ∃ i₀, ms i₀ ≠ 0 := by
    by_contra hnone
    have hall : ∀ i, (ms i : ℂ)^2 = 0 := by
      intro i
      rcases hmem i with h | h | h
      · simp [h]
      · exfalso
        apply hnone ⟨i, ?_⟩
        omega
      · exfalso
        apply hnone ⟨i, ?_⟩
        omega
    have hzero : (∑ i, ((ms i : ℤ) : ℂ)^2) = 0 := by simp [hall]
    rw [hsq] at hzero
    norm_num at hzero
  rcases hex with ⟨i₀, hmi₀⟩
  have hmi₀mem : ms i₀ = 1 ∨ ms i₀ = -1 := by
    rcases hmem i₀ with h | h | h
    · contradiction
    · exact Or.inl h
    · exact Or.inr h
  have hone : ∀ i, i ≠ i₀ → ms i = 0 := by
    intro i hi
    by_contra hmi
    have hmi_mem : ms i = 1 ∨ ms i = -1 := by
      rcases hmem i with h | h | h
      · contradiction
      · exact Or.inl h
      · exact Or.inr h
    have hsqR : (∑ j, ((ms j : ℤ) : ℝ)^2) = ((1 : ℕ) : ℝ) := int_sq_sum_real hsq
    have h1 : ((ms i₀ : ℤ) : ℝ)^2 = 1 := by
      rcases hmi₀mem with h | h <;> simp [h]
    have h2 : ((ms i : ℤ) : ℝ)^2 = 1 := by
      rcases hmi_mem with h | h <;> simp [h]
    have hpair : ((ms i₀ : ℤ) : ℝ)^2 + ((ms i : ℤ) : ℝ)^2 ≤ ∑ j, ((ms j : ℤ) : ℝ)^2 := by
      have hsub : ({i₀, i} : Finset ι) ⊆ Finset.univ := by
        intro x hx
        simp
      have hnonneg : ∀ x ∈ Finset.univ, x ∉ ({i₀, i} : Finset ι) → 0 ≤ ((ms x : ℤ) : ℝ)^2 := by
        intro x hx hxnot
        exact sq_nonneg _
      have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg
      rw [Finset.sum_insert] at hle
      · simpa using hle
      · simpa using hi.symm
    norm_num at hsqR
    nlinarith
  refine ⟨χs i₀, hirr i₀, ?_⟩
  rcases hmi₀mem with hmi₀eq | hmi₀eq
  · left
    funext x
    rw [hψsum]
    rw [Finset.sum_apply]
    calc
      ∑ i, ((ms i : ℤ) : ℂ) • χs i x = ((ms i₀ : ℤ) : ℂ) • χs i₀ x := by
            refine Finset.sum_eq_single i₀ ?_ ?_
            · intro j hj hji
              have hmsj : ms j = 0 := hone j hji
              simp [hmsj]
            · intro hnot
              exact (hnot (Finset.mem_univ i₀)).elim
      _ = χs i₀ x := by simp [hmi₀eq]
  · right
    funext x
    rw [hψsum]
    rw [Finset.sum_apply]
    calc
      ∑ i, ((ms i : ℤ) : ℂ) • χs i x = ((ms i₀ : ℤ) : ℂ) • χs i₀ x := by
            refine Finset.sum_eq_single i₀ ?_ ?_
            · intro j hj hji
              have hmsj : ms j = 0 := hone j hji
              simp [hmsj]
            · intro hnot
              exact (hnot (Finset.mem_univ i₀)).elim
      _ = -χs i₀ x := by simp [hmi₀eq]

/-- A character of star-norm two is the sum of two distinct irreducible
characters.  This is the `ν^s = ν` case of Remark 1.4: the induced character
`ν^H` has norm two and splits into two constituents. -/
public theorem char_norm_two_decomp {G : Type u} [Group G] [Fintype G]
    {ψ : ClassFunction G} (hψ : IsCharacter ψ) (hnorm : scalarProduct G ψ ψ = 2) :
    ∃ σ₁ σ₂ : ClassFunction G,
      IsIrreducibleCharacter σ₁ ∧ IsIrreducibleCharacter σ₂ ∧ σ₁ ≠ σ₂ ∧ ψ = σ₁ + σ₂ := by
  classical
  rcases hψ with ⟨n, ρ, hψeq⟩
  rcases char_decomp ρ with ⟨cs, hcs, hnod, hsum⟩
  let ι : Type (max 0 u) := {χ : ClassFunction G // χ ∈ (cs.map Prod.fst).toFinset}
  let χs : ι → ClassFunction G := fun χ => χ.1
  let ms : ι → ℤ := fun χ => mult cs χ.1
  have hψsum : ψ = ∑ i : ι, (ms i : ℂ) • χs i := by
    rw [hψeq, hsum]
    rw [sum_pairs_reindex cs hnod]
    rw [← Finset.sum_coe_sort (s := (cs.map Prod.fst).toFinset)
      (fun χ => (mult cs χ : ℂ) • χ)]
  have hirr : ∀ i : ι, IsIrreducibleCharacter (χs i) := by
    intro i
    rcases List.mem_map.mp (List.mem_toFinset.mp i.2) with ⟨p, hp, hpi⟩
    simpa [χs, hpi] using hcs p hp
  have hdist : ∀ i j : ι, i ≠ j → χs i ≠ χs j := by
    intro i j hij hEq
    apply hij
    exact Subtype.ext (by simpa [χs] using hEq)
  have hsq : (∑ i, ((ms i : ℤ) : ℂ)^2) = (2 : ℂ) := by
    rw [← decomp_scalarProduct (G := G) hirr hdist]
    rw [← hψsum]
    exact hnorm
  have hmem : ∀ i : ι, ms i = 0 ∨ ms i = 1 := by
    intro i
    rcases int_sq_sum_mem (k := 2) (by norm_num) hsq i with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      have hnonneg : 0 ≤ ms i := by
        dsimp [ms]
        dsimp [mult]
        exact List.sum_nonneg (fun x hx => by
          rcases List.mem_map.mp hx with ⟨p, hp, rfl⟩
          exact_mod_cast (Nat.zero_le p.2))
      omega
  have hcard : (Finset.univ.filter (fun i : ι => ms i = 1)).card = 2 := by
    have h2 : ((Finset.univ.filter (fun i : ι => ms i = 1)).card : ℂ) = 2 := by
      calc
        ((Finset.univ.filter (fun i : ι => ms i = 1)).card : ℂ)
            = ∑ i, (if ms i = 1 then (1 : ℂ) else 0) := by
                rw [Finset.sum_boole]
        _ = ∑ i, ((ms i : ℤ) : ℂ)^2 := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                by_cases h : ms i = 1
                · simp [h]
                · have hm : ms i = 0 := (hmem i).resolve_right h
                  simp [hm]
        _ = 2 := hsq
    exact_mod_cast h2
  rcases (Finset.card_eq_two.mp hcard) with ⟨i₀, i₁, hne, hS⟩
  have hi₀ : i₀ ∈ Finset.univ.filter (fun i : ι => ms i = 1) := by
    rw [hS]
    simp
  have hi₁ : i₁ ∈ Finset.univ.filter (fun i : ι => ms i = 1) := by
    rw [hS]
    simp
  have hmi₀ : ms i₀ = 1 := (Finset.mem_filter.mp hi₀).2
  have hmi₁ : ms i₁ = 1 := (Finset.mem_filter.mp hi₁).2
  have hzero : ∀ i : ι, i ≠ i₀ → i ≠ i₁ → ms i = 0 := by
    intro i hi₀' hi₁'
    by_cases h : ms i = 1
    · exfalso
      have hmem : i ∈ Finset.univ.filter (fun j : ι => ms j = 1) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩
      have : i = i₀ ∨ i = i₁ := by
        rw [hS] at hmem
        simpa using hmem
      rcases this with h | h <;> contradiction
    · exact (hmem i).resolve_right h
  refine ⟨χs i₀, χs i₁, hirr i₀, hirr i₁, hdist i₀ i₁ hne, ?_⟩
  have hsum_two : (∑ i, (ms i : ℂ) • χs i) =
      (ms i₀ : ℂ) • χs i₀ + (ms i₁ : ℂ) • χs i₁ := by
    rw [← Finset.sum_subset (s₁ := ({i₀, i₁} : Finset ι)) (s₂ := Finset.univ)
      (fun x hx => by simp) ?_]
    · rw [Finset.sum_insert]
      · simp [hmi₀, hmi₁]
      · simpa [Finset.mem_singleton] using hne
    · intro i hi hi₀₁
      have hz : ms i = 0 := hzero i
        (by intro hEq; exact hi₀₁ (by simp [hEq]))
        (by intro hEq; exact hi₀₁ (by simp [hEq]))
      simp [hz]
  rw [hψsum, hsum_two, hmi₀, hmi₁]
  simp

public lemma decomp_scalarProduct_irreducible {ι : Type v} [Fintype ι]
    {χs : ι → ClassFunction G} {ms : ι → ℤ}
    (hirr : ∀ i, IsIrreducibleCharacter (χs i))
    (hdist : ∀ i j, i ≠ j → χs i ≠ χs j) {χ : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ) (hne : scalarProduct G χ (∑ i, (ms i : ℂ) • χs i) ≠ 0) :
    ∃ i₀, χs i₀ = χ ∧ scalarProduct G χ (∑ i, (ms i : ℂ) • χs i) = (ms i₀ : ℂ) := by
  classical
  have hsum : scalarProduct G χ (∑ i, (ms i : ℂ) • χs i) =
      ∑ i, scalarProduct G χ (χs i) * star (ms i : ℂ) := by
    rw [scalarProduct_sum_right]
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact scalarProduct_smul_right (ms i : ℂ) χ (χs i)
  have hex : ∃ i₀, χs i₀ = χ := by
    by_contra hnone
    have hall : ∀ i, scalarProduct G χ (χs i) = 0 := by
      intro i
      exact irreducible_scalarProduct_of_ne hχ (hirr i) (fun hEq => hnone ⟨i, hEq.symm⟩)
    have hzero : scalarProduct G χ (∑ i, (ms i : ℂ) • χs i) = 0 := by
      rw [hsum]
      simp [hall]
    exact hne hzero
  rcases hex with ⟨i₀, hχi₀⟩
  refine ⟨i₀, hχi₀, ?_⟩
  rw [hsum]
  calc
    ∑ i, scalarProduct G χ (χs i) * star (ms i : ℂ)
        = scalarProduct G χ (χs i₀) * star (ms i₀ : ℂ) := by
            refine Finset.sum_eq_single i₀ ?_ ?_
            · intro j hj hji
              have hsp : scalarProduct G χ (χs j) = 0 := by
                exact irreducible_scalarProduct_of_ne hχ (hirr j)
                  (fun hEq => hdist j i₀ hji (by simpa [hχi₀] using hEq.symm))
              simp [hsp]
            · intro hnot
              exact (hnot (Finset.mem_univ i₀)).elim
    _ = (ms i₀ : ℂ) := by
            rw [hχi₀]
            simp [irreducible_scalarProduct_self hχ]

/-- The decomposition machinery for `(χ, ψ) = 1` with `χ` irreducible and `ψ`
a character: `ψ = Σ ms·χs`, the coefficient of `χ` is `1`, and all
multiplicities are nonnegative integers. -/
private theorem char_decomp_coeff_one {G : Type u} [Group G] [Fintype G]
    {ψ χ : ClassFunction G} (hψ : IsCharacter ψ) (hχ : IsIrreducibleCharacter χ)
    (hsp : scalarProduct G χ ψ = 1) :
    ∃ (ι : Type (max 0 u)) (_ : Fintype ι) (χs : ι → ClassFunction G) (ms : ι → ℤ)
      (i₀ : ι),
      (∀ i, IsIrreducibleCharacter (χs i)) ∧
      (∀ i j, i ≠ j → χs i ≠ χs j) ∧
      (∀ i, 0 ≤ ms i) ∧
      (χs i₀ = χ) ∧ ((ms i₀ : ℂ) = 1) ∧ (ψ = ∑ i, (ms i : ℂ) • χs i) := by
  classical
  rcases hψ with ⟨n, ρ, hψeq⟩
  rcases char_decomp ρ with ⟨cs, hcs, hnod, hsum⟩
  let ι : Type (max 0 u) := {χ₀ : ClassFunction G // χ₀ ∈ (cs.map Prod.fst).toFinset}
  let χs : ι → ClassFunction G := fun χ₀ => χ₀.1
  let ms : ι → ℤ := fun χ₀ => mult cs χ₀.1
  have hψsum : ψ = ∑ i : ι, (ms i : ℂ) • χs i := by
    rw [hψeq, hsum]
    rw [sum_pairs_reindex cs hnod]
    rw [← Finset.sum_coe_sort (s := (cs.map Prod.fst).toFinset)
      (fun χ₀ => (mult cs χ₀ : ℂ) • χ₀)]
  have hirr : ∀ i : ι, IsIrreducibleCharacter (χs i) := by
    intro i
    rcases List.mem_map.mp (List.mem_toFinset.mp i.2) with ⟨p, hp, hpi⟩
    simpa [χs, hpi] using hcs p hp
  have hdist : ∀ i j : ι, i ≠ j → χs i ≠ χs j := by
    intro i j hij hEq
    apply hij
    exact Subtype.ext (by simpa [χs] using hEq)
  have hne : scalarProduct G χ (∑ i, (ms i : ℂ) • χs i) ≠ 0 := by
    rw [← hψsum]
    rw [hsp]
    norm_num
  rcases (decomp_scalarProduct_irreducible (G := G) hirr hdist hχ hne) with ⟨i₀, hχs, hms⟩
  have hms1 : (ms i₀ : ℂ) = 1 := by
    rw [← hψsum] at hms
    exact (hsp.symm.trans hms).symm
  have hms_nonneg : ∀ i : ι, 0 ≤ ms i := by
    intro i
    dsimp [ms]
    dsimp [mult]
    exact List.sum_nonneg (fun x hx => by
      rcases List.mem_map.mp hx with ⟨p, hp, rfl⟩
      exact_mod_cast (Nat.zero_le p.2))
  exact ⟨ι, inferInstance, χs, ms, i₀, hirr, hdist, hms_nonneg, hχs, hms1, hψsum⟩

/-- If an irreducible character occurs in a character with scalar product
`1`, the degree of the character is at least the degree of the irreducible. -/
public theorem irreducible_char_degree_le_of_scalarProduct_one {G : Type u}
    [Group G] [Fintype G] {ψ χ : ClassFunction G} (hψ : IsCharacter ψ)
    (hχ : IsIrreducibleCharacter χ) (hsp : scalarProduct G χ ψ = 1) :
    ∃ rψ rχ : ℕ, ψ 1 = (rψ : ℂ) ∧ χ 1 = (rχ : ℂ) ∧ rχ ≤ rψ := by
  classical
  rcases char_decomp_coeff_one hψ hχ hsp with
    ⟨ι, _, χs, ms, i₀, hirr, hdist, hms_nonneg, hχs, hms1, hψsum⟩
  have hdeg_nat : ∀ i : ι, ∃ r : ℕ, χs i 1 = (r : ℂ) := by
    intro i
    rcases hirr i with ⟨nᵢ, ρᵢ, hρᵢ, hχsEq⟩
    refine ⟨nᵢ, ?_⟩
    rw [hχsEq, Representation.char_one, Module.finrank_pi, Fintype.card_fin]
  have hms_nat : ∀ i : ι, ∃ m : ℕ, ms i = (m : ℤ) := by
    intro i
    refine ⟨(ms i).toNat, ?_⟩
    exact (Int.toNat_of_nonneg (hms_nonneg i)).symm
  let d : ι → ℕ := fun i => Classical.choose (hdeg_nat i)
  let m : ι → ℕ := fun i => Classical.choose (hms_nat i)
  have hd (i : ι) : χs i 1 = (d i : ℂ) := Classical.choose_spec (hdeg_nat i)
  have hm (i : ι) : ms i = (m i : ℤ) := Classical.choose_spec (hms_nat i)
  have hterm_nat (i : ι) : (ms i : ℂ) * χs i 1 = (m i : ℂ) * (d i : ℂ) := by
    rw [hm i, hd i]
    norm_cast
  have hψ1' : ψ 1 = (d i₀ : ℂ) +
      (∑ i ∈ Finset.univ.erase i₀, (m i * d i : ℕ) : ℂ) := by
    calc
      ψ 1 = (∑ i, (ms i : ℂ) • χs i) 1 := by rw [hψsum]
      _ = ∑ i, (ms i : ℂ) • χs i 1 := by simp [Finset.sum_apply]
      _ = (ms i₀ : ℂ) • χs i₀ 1 +
            ∑ i ∈ Finset.univ.erase i₀, (ms i : ℂ) • χs i 1 := by
            have huniv : Finset.univ = insert i₀ (Finset.univ.erase i₀) := by
              rw [Finset.insert_erase]
              exact Finset.mem_univ i₀
            rw [huniv, Finset.sum_insert]
            · simp
            · simp
      _ = (d i₀ : ℂ) + (∑ i ∈ Finset.univ.erase i₀, (m i * d i : ℕ) : ℂ) := by
            rw [hd i₀, hms1]
            simp
            have hsum_all : (∑ x, (ms x : ℂ) * χs x 1) = ∑ x, (m x : ℂ) * (d x : ℂ) :=
              Finset.sum_congr rfl (fun i hi => hterm_nat i)
            have hsub : (ms i₀ : ℂ) * χs i₀ 1 = (m i₀ : ℂ) * (d i₀ : ℂ) := hterm_nat i₀
            rw [hsum_all, hsub]
  have hχ1' : χ 1 = (d i₀ : ℂ) := by
    rw [← hχs]
    exact hd i₀
  refine ⟨d i₀ + ∑ i ∈ Finset.univ.erase i₀, (m i * d i : ℕ), d i₀, ?_, ?_, ?_⟩
  · simpa using hψ1'
  · exact hχ1'
  · omega

/-- If an irreducible character occurs in a character with scalar product
`1` and the degrees agree, the character is the irreducible. -/
public theorem char_eq_irreducible_of_scalarProduct_one_and_degree {G : Type u}
    [Group G] [Fintype G] {ψ χ : ClassFunction G} (hψ : IsCharacter ψ)
    (hχ : IsIrreducibleCharacter χ) (hsp : scalarProduct G χ ψ = 1)
    (hdeg : ψ 1 = χ 1) : ψ = χ := by
  classical
  rcases char_decomp_coeff_one hψ hχ hsp with
    ⟨ι, _, χs, ms, i₀, hirr, hdist, hms_nonneg, hχs, hms1, hψsum⟩
  have hdeg_nat : ∀ i : ι, ∃ r : ℕ, χs i 1 = (r : ℂ) := by
    intro i
    rcases hirr i with ⟨nᵢ, ρᵢ, hρᵢ, hχsEq⟩
    refine ⟨nᵢ, ?_⟩
    rw [hχsEq, Representation.char_one, Module.finrank_pi, Fintype.card_fin]
  have hms_nat : ∀ i : ι, ∃ m : ℕ, ms i = (m : ℤ) := by
    intro i
    refine ⟨(ms i).toNat, ?_⟩
    exact (Int.toNat_of_nonneg (hms_nonneg i)).symm
  let d : ι → ℕ := fun i => Classical.choose (hdeg_nat i)
  let m : ι → ℕ := fun i => Classical.choose (hms_nat i)
  have hd (i : ι) : χs i 1 = (d i : ℂ) := Classical.choose_spec (hdeg_nat i)
  have hm (i : ι) : ms i = (m i : ℤ) := Classical.choose_spec (hms_nat i)
  have hterm_nat (i : ι) : (ms i : ℂ) * χs i 1 = (m i : ℂ) * (d i : ℂ) := by
    rw [hm i, hd i]
    norm_cast
  have hψ1' : ψ 1 = (d i₀ : ℂ) +
      (∑ i ∈ Finset.univ.erase i₀, (m i * d i : ℕ) : ℂ) := by
    calc
      ψ 1 = (∑ i, (ms i : ℂ) • χs i) 1 := by rw [hψsum]
      _ = ∑ i, (ms i : ℂ) • χs i 1 := by simp [Finset.sum_apply]
      _ = (ms i₀ : ℂ) • χs i₀ 1 +
            ∑ i ∈ Finset.univ.erase i₀, (ms i : ℂ) • χs i 1 := by
            have huniv : Finset.univ = insert i₀ (Finset.univ.erase i₀) := by
              rw [Finset.insert_erase]
              exact Finset.mem_univ i₀
            rw [huniv, Finset.sum_insert]
            · simp
            · simp
      _ = (d i₀ : ℂ) + (∑ i ∈ Finset.univ.erase i₀, (m i * d i : ℕ) : ℂ) := by
            rw [hd i₀, hms1]
            simp
            have hsum_all : (∑ x, (ms x : ℂ) * χs x 1) = ∑ x, (m x : ℂ) * (d x : ℂ) :=
              Finset.sum_congr rfl (fun i hi => hterm_nat i)
            have hsub : (ms i₀ : ℂ) * χs i₀ 1 = (m i₀ : ℂ) * (d i₀ : ℂ) := hterm_nat i₀
            rw [hsum_all, hsub]
  have hχ1' : χ 1 = (d i₀ : ℂ) := by
    rw [← hχs]
    exact hd i₀
  have hrest_nat : (∑ i ∈ Finset.univ.erase i₀, (m i * d i : ℕ)) = 0 := by
    have hdeg' : (d i₀ : ℂ) + (∑ i ∈ Finset.univ.erase i₀, (m i * d i : ℕ) : ℂ) = (d i₀ : ℂ) := by
      rw [← hψ1', hdeg, hχ1']
    have hz : (∑ i ∈ Finset.univ.erase i₀, (m i * d i : ℕ) : ℂ) = 0 := by
      have h := congrArg (fun z : ℂ => z - (d i₀ : ℂ)) hdeg'
      simpa using h
    exact_mod_cast hz
  have hterm0 : ∀ i ∈ Finset.univ.erase i₀, m i * d i = 0 := by
    intro i hi
    have hsum_real : (∑ i ∈ Finset.univ.erase i₀, ((m i * d i : ℕ) : ℝ)) = 0 := by
      exact_mod_cast hrest_nat
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i hi => by exact_mod_cast (Nat.zero_le (m i * d i)))).1 hsum_real i hi
    exact_mod_cast hz
  have hms0 : ∀ i : ι, i ≠ i₀ → ms i = 0 := by
    intro i hi
    have hmem : i ∈ Finset.univ.erase i₀ := Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩
    have hmul : m i * d i = 0 := hterm0 i hmem
    have hdne : d i ≠ 0 := by
      intro hd0
      have : χs i 1 = 0 := by rw [hd i, hd0]; norm_num
      exact irreducible_char_one_ne_zero (hirr i) this
    rcases (Nat.mul_eq_zero.mp hmul) with hm0 | hd0
    · rw [hm i, hm0]
      norm_num
    · exact False.elim (hdne hd0)
  funext x
  rw [hψsum]
  have hsum_one : (∑ i, (ms i : ℂ) • χs i) = (ms i₀ : ℂ) • χs i₀ := by
    rw [← Finset.sum_subset (s₁ := ({i₀} : Finset ι)) (s₂ := Finset.univ)
      (fun x hx => by simp) ?_]
    · simp
    · intro i hi hi₀
      have hz : ms i = 0 := hms0 i (by intro hEq; exact hi₀ (by simp [hEq]))
      simp [hz]
  rw [hsum_one, hχs, hms1]
  simp

/-- The scalar product is anti-linear in the first argument. -/
public lemma scalarProduct_neg_left [Group G] (φ ψ : ClassFunction G) :
    scalarProduct G (-φ) ψ = -scalarProduct G φ ψ := by
  calc
    scalarProduct G (-φ) ψ = scalarProduct G ((-1 : ℂ) • φ) ψ := by simp
    _ = (-1 : ℂ) * scalarProduct G φ ψ := scalarProduct_smul_left (-1 : ℂ) φ ψ
    _ = -scalarProduct G φ ψ := by simp

/-- The scalar product is conjugate-linear in the second argument. -/
public lemma scalarProduct_neg_right [Group G] (φ ψ : ClassFunction G) :
    scalarProduct G φ (-ψ) = -scalarProduct G φ ψ := by
  calc
    scalarProduct G φ (-ψ) = scalarProduct G φ ((-1 : ℂ) • ψ) := by simp
    _ = scalarProduct G φ ψ * star (-1 : ℂ) := scalarProduct_smul_right (-1 : ℂ) φ ψ
    _ = -scalarProduct G φ ψ := by simp


end Decomposition

/-! ## Roots of unity and linear characters -/

section LinearCharacter

variable {G : Type u} [Group G] [Fintype G]

/-- A linear character has degree one. -/
private theorem linearChar_finrank_one {G : Type u} [Group G] {lam : ClassFunction G}
    (hlam : IsLinearCharacter lam) : ∃ ρ : Representation ℂ G (Fin 1 → ℂ), lam = ρ.character := by
  rcases hlam.1 with ⟨n, ρ, hρ, hlameq⟩
  have hn : n = 1 := by
    have htr : (LinearMap.trace ℂ (Fin n → ℂ)) (ρ 1) = (n : ℂ) := by
      simpa using (LinearMap.trace_id ℂ (Fin n → ℂ))
    have htr' : (LinearMap.trace ℂ (Fin n → ℂ)) (ρ 1) = (1 : ℂ) := by
      change ρ.character 1 = (1 : ℂ)
      rw [← hlameq]
      exact hlam.2
    exact_mod_cast (htr.symm.trans htr')
  subst n
  exact ⟨ρ, hlameq⟩

/-- A linear character acts by scalar multiplication on its one-dimensional space. -/
private theorem linearChar_scalar {G : Type u} [Group G] {lam : ClassFunction G}
    (_hlam : IsLinearCharacter lam) (ρ : Representation ℂ G (Fin 1 → ℂ))
    (hlameq : lam = ρ.character) :
    ∀ x : G, ρ x = (lam x) • (1 : (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ)) := by
  intro x
  refine LinearMap.ext ?_
  intro v
  have hsplit : v = v 0 • (fun _ : Fin 1 => (1 : ℂ)) := by
    ext i
    fin_cases i
    simp
  have hdiag : (ρ x (fun _ : Fin 1 => (1 : ℂ))) 0 = lam x := by
    have htr : (LinearMap.trace ℂ (Fin 1 → ℂ)) (ρ x) = lam x := by
      rw [hlameq]
      rfl
    have hsc : ρ x = (ρ x (fun _ : Fin 1 => (1 : ℂ))) 0 •
        (1 : (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ)) := by
      refine LinearMap.ext ?_
      intro w
      have hsplit' : w = w 0 • (fun _ : Fin 1 => (1 : ℂ)) := by
        ext i
        fin_cases i
        simp
      have hdiag' : ρ x (fun _ : Fin 1 => (1 : ℂ)) =
          (ρ x (fun _ : Fin 1 => (1 : ℂ))) 0 • (fun _ : Fin 1 => (1 : ℂ)) := by
        ext i
        fin_cases i
        simp
      calc
        ρ x w = ρ x (w 0 • (fun _ : Fin 1 => (1 : ℂ))) := congrArg (ρ x) hsplit'
        _ = w 0 • ρ x (fun _ : Fin 1 => (1 : ℂ)) := by rw [map_smul]
        _ = w 0 • ((ρ x (fun _ : Fin 1 => (1 : ℂ))) 0 • (fun _ : Fin 1 => (1 : ℂ))) := by
                rw [hdiag']
                simp
        _ = (w 0 * (ρ x (fun _ : Fin 1 => (1 : ℂ))) 0) • (fun _ : Fin 1 => (1 : ℂ)) := by
                rw [smul_smul]
        _ = (ρ x (fun _ : Fin 1 => (1 : ℂ))) 0 • (w 0 • (fun _ : Fin 1 => (1 : ℂ))) := by
                rw [mul_comm, ← smul_smul]
        _ = ((ρ x (fun _ : Fin 1 => (1 : ℂ))) 0 •
            (1 : (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ))) w := by
                calc
                  (ρ x (fun _ : Fin 1 => (1 : ℂ))) 0 • (w 0 • (fun _ : Fin 1 => (1 : ℂ)))
                      = (ρ x (fun _ : Fin 1 => (1 : ℂ))) 0 • w := by rw [← hsplit']
                  _ = ((ρ x (fun _ : Fin 1 => (1 : ℂ))) 0 •
                      (1 : (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ))) w := by simp
    have htrsc : (LinearMap.trace ℂ (Fin 1 → ℂ))
        ((ρ x (fun _ : Fin 1 => (1 : ℂ))) 0 • (1 : (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ))) =
        (ρ x (fun _ : Fin 1 => (1 : ℂ))) 0 := by
      rw [map_smul]
      have ht : (LinearMap.trace ℂ (Fin 1 → ℂ)) (1 : (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ)) =
          (1 : ℂ) := by
        simpa using (LinearMap.trace_id ℂ (Fin 1 → ℂ))
      rw [ht]
      simp
    have htr' : (LinearMap.trace ℂ (Fin 1 → ℂ)) (ρ x) = (ρ x (fun _ : Fin 1 => (1 : ℂ))) 0 := by
      rw [hsc, htrsc]
      simp
    rw [← htr']
    exact htr
  calc
    ρ x v = ρ x (v 0 • (fun _ : Fin 1 => (1 : ℂ))) := congrArg (ρ x) hsplit
    _ = v 0 • ρ x (fun _ : Fin 1 => (1 : ℂ)) := by rw [map_smul]
    _ = v 0 • (lam x • (fun _ : Fin 1 => (1 : ℂ))) := by
          congr 1
          ext i
          fin_cases i
          simp [hdiag]
    _ = (v 0 * lam x) • (fun _ : Fin 1 => (1 : ℂ)) := by rw [smul_smul]
    _ = (lam x • (1 : (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ))) v := by
          calc
            (v 0 * lam x) • (fun _ : Fin 1 => (1 : ℂ))
                = (lam x * v 0) • (fun _ : Fin 1 => (1 : ℂ)) := by rw [mul_comm]
            _ = lam x • (v 0 • (fun _ : Fin 1 => (1 : ℂ))) := by rw [smul_smul]
            _ = lam x • v := by rw [← hsplit]
            _ = (lam x • (1 : (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ))) v := by simp

/-- A linear character is multiplicative. -/
public theorem linearChar_mul {G : Type u} [Group G] {lam : ClassFunction G}
    (hlam : IsLinearCharacter lam) (x y : G) : lam (x * y) = lam x * lam y := by
  rcases linearChar_finrank_one hlam with ⟨ρ, hlameq⟩
  have hsc := linearChar_scalar hlam ρ hlameq
  have h' : ρ (x * y) = ρ x * ρ y := ρ.map_mul' x y
  rw [hsc, hsc, hsc] at h'
  have happly : ((lam (x * y)) • (1 : (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ))) (fun _ : Fin 1 => (1 : ℂ)) =
      ((lam x • (1 : (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ))) *
        (lam y • (1 : (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ)))) (fun _ : Fin 1 => (1 : ℂ)) := by
    exact congrArg (fun f : (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ) => f (fun _ : Fin 1 => (1 : ℂ))) h'
  simpa [Pi.smul_apply, smul_smul, mul_comm] using congrFun happly 0

/-- A linear character is nonzero everywhere. -/
public theorem linearChar_ne_zero {G : Type u} [Group G] [Fintype G] {lam : ClassFunction G}
    (hlam : IsLinearCharacter lam) (x : G) : lam x ≠ 0 := by
  rcases linearChar_finrank_one hlam with ⟨ρ, hlameq⟩
  have hsc := linearChar_scalar hlam ρ hlameq
  have hρpow : (ρ x) ^ orderOf x = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  have hscpow : ∀ n : ℕ, ((lam x) • (1 : (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ))) ^ n =
      (lam x) ^ n • (1 : (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          ((lam x) • (1 : (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ))) ^ (n + 1)
              = ((lam x) • (1 : (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ))) ^ n *
                ((lam x) • (1 : (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ))) := by rw [pow_succ]
          _ = ((lam x) ^ n • (1 : (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ))) *
                ((lam x) • (1 : (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ))) := by rw [ih]
          _ = (lam x) • (((lam x) ^ n • (1 : (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ))) *
                (1 : (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ))) := by rw [mul_smul_comm]
          _ = (lam x) • ((lam x) ^ n • (1 : (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ))) := by simp
          _ = ((lam x) * (lam x) ^ n) • (1 : (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ)) := by
                  rw [smul_smul]
          _ = (lam x) ^ (n + 1) • (1 : (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ)) := by
                  rw [mul_comm, ← pow_succ]
  have h' : ((lam x) • (1 : (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ))) ^ orderOf x = 1 := by
    rw [hsc] at hρpow
    exact hρpow
  have hpow : (lam x) ^ orderOf x = 1 := by
    have h1 : (lam x) ^ orderOf x • (fun _ : Fin 1 => (1 : ℂ)) =
        (fun _ : Fin 1 => (1 : ℂ)) := by
      rw [hscpow] at h'
      exact congrArg (fun f : (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ) => f (fun _ : Fin 1 => (1 : ℂ))) h'
    have h0 := congrFun h1 0
    simpa using h0
  intro hz
  rw [hz, zero_pow (orderOf_pos x).ne'] at hpow
  norm_num at hpow

/-- The value of a linear character at an inverse is the inverse value. -/
public theorem linearChar_inv {G : Type u} [Group G] {lam : ClassFunction G}
    (hlam : IsLinearCharacter lam) (x : G) : lam x⁻¹ = (lam x)⁻¹ := by
  have h : lam x * lam x⁻¹ = 1 := by
    rw [← linearChar_mul hlam x x⁻¹]
    rw [mul_inv_cancel, hlam.2]
  exact (inv_eq_of_mul_eq_one_right h).symm

/-- The conjugate of a linear character value is the value at the inverse. -/
public theorem linearChar_star {G : Type u} [Group G] [Fintype G] {lam : ClassFunction G}
    (hlam : IsLinearCharacter lam) (x : G) : star (lam x) = lam x⁻¹ := by
  exact star_char_eq_char_inv (isCharacter_of_isIrreducibleCharacter hlam.1) x

/-- The product of two scalar endomorphisms of a one-dimensional space. -/
private lemma scalar_mul_one (c d : ℂ) :
    (c • (1 : (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ))) * (d • (1 : (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ))) =
      (c * d) • (1 : (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ)) := by
  refine LinearMap.ext ?_
  intro v
  simp [smul_smul, mul_comm]

/-- The class function associated to a group homomorphism into `ℂˣ` is a linear character. -/
public theorem isLinearCharacter_of_hom {G : Type u} [Group G] [Fintype G]
    (φ : G →* ℂˣ) : IsLinearCharacter (fun x : G => ((φ x : ℂˣ) : ℂ)) := by
  let ρ : Representation ℂ G (Fin 1 → ℂ) :=
    { toFun := fun x => ((φ x : ℂˣ) : ℂ) • (1 : (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ))
      map_one' := by
        ext v
        simp
      map_mul' := by
        intro x y
        have hxy : (((φ (x * y) : ℂˣ) : ℂ)) = (((φ x : ℂˣ) : ℂ) * ((φ y : ℂˣ) : ℂ)) := by
          rw [← Units.val_mul]
          congr 1
          exact map_mul φ x y
        calc
          (((φ (x * y) : ℂˣ) : ℂ) • (1 : (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ)))
              = (((φ x : ℂˣ) : ℂ) * ((φ y : ℂˣ) : ℂ)) • (1 : (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ)) := by
                  rw [hxy]
          _ = ((φ x : ℂˣ) : ℂ) • (1 : (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ)) *
              ((φ y : ℂˣ) : ℂ) • (1 : (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ)) := (scalar_mul_one _ _).symm }
  refine ⟨?_, by simp⟩
  refine isIrreducibleCharacter_of_norm_one_inv ?hchar ?hnorm
  · refine ⟨1, ρ, ?_⟩
    ext x
    change ((φ x : ℂˣ) : ℂ) =
      (LinearMap.trace ℂ (Fin 1 → ℂ)) (((φ x : ℂˣ) : ℂ) •
        (1 : (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ)))
    rw [map_smul]
    have ht : (LinearMap.trace ℂ (Fin 1 → ℂ)) (1 : (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ)) = (1 : ℂ) := by
      simpa using (LinearMap.trace_id ℂ (Fin 1 → ℂ))
    rw [ht]
    simp
  · calc
      scalarProductInv G (fun x : G => ((φ x : ℂˣ) : ℂ)) (fun x : G => ((φ x : ℂˣ) : ℂ))
          = (Nat.card G : ℂ)⁻¹ * ∑ g : G, ((φ g : ℂˣ) : ℂ) * ((φ g⁻¹ : ℂˣ) : ℂ) := rfl
      _ = (Nat.card G : ℂ)⁻¹ * ∑ g : G, ((φ g : ℂˣ) : ℂ) * ((φ g : ℂˣ) : ℂ)⁻¹ := by
              congr 1
              refine Finset.sum_congr rfl ?_
              intro g hg
              congr 1
              have h1 : ((φ g : ℂˣ) : ℂ) * ((φ g⁻¹ : ℂˣ) : ℂ) = 1 := by
                rw [← Units.val_mul]
                rw [← map_mul, mul_inv_cancel, map_one]
                simp
              exact (inv_eq_of_mul_eq_one_right h1).symm
      _ = 1 := by
              simp

/-- The group homomorphism into `ℂˣ` corresponding to a linear character. -/
@[expose] public noncomputable def linearCharHom {G : Type u} [Group G] [Fintype G]
    {lam : ClassFunction G} (hlam : IsLinearCharacter lam) : G →* ℂˣ where
  toFun x := Units.mk0 (lam x) (linearChar_ne_zero hlam x)
  map_one' := by
    ext
    exact hlam.2
  map_mul' := by
    intro x y
    ext
    exact linearChar_mul hlam x y

/-- The value of the hom associated to a linear character. -/
public theorem linearCharHom_apply {G : Type u} [Group G] [Fintype G] {lam : ClassFunction G}
    (hlam : IsLinearCharacter lam) (x : G) : (((linearCharHom hlam x : ℂˣ) : ℂ)) = lam x := rfl

/-- The trivial character is linear. -/
public theorem isLinearCharacter_one {G : Type u} [Group G] [Fintype G] :
    IsLinearCharacter (1 : ClassFunction G) := by
  refine ⟨?_, by simp⟩
  refine isIrreducibleCharacter_of_norm_one_inv ?hchar ?hnorm
  · refine ⟨1, { toFun := fun _ => (1 : (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ))
                 map_one' := rfl
                 map_mul' := by intro x y; rfl }, ?_⟩
    ext x
    change (1 : ℂ) =
      (LinearMap.trace ℂ (Fin 1 → ℂ)) (1 : (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ))
    have ht : (LinearMap.trace ℂ (Fin 1 → ℂ)) (1 : (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ)) = (1 : ℂ) := by
      simpa using (LinearMap.trace_id ℂ (Fin 1 → ℂ))
    rw [ht]
  · simp [scalarProductInv]

/-- The product of a linear character and a character is a character. -/
public theorem isCharacter_mul_linear {G : Type u} [Group G] {lam ν : ClassFunction G}
    (hlam : IsLinearCharacter lam) (hν : IsCharacter ν) : IsCharacter (lam * ν) := by
  rcases linearChar_finrank_one hlam with ⟨ρ₁, hlameq⟩
  rcases hν with ⟨n₂, ρ₂, hνeq⟩
  let e : ℂ ⊗[ℂ] (Fin n₂ → ℂ) ≃ₗ[ℂ] (Fin n₂ → ℂ) := TensorProduct.lid ℂ (Fin n₂ → ℂ)
  let e' : (Fin 1 → ℂ) ⊗[ℂ] (Fin n₂ → ℂ) ≃ₗ[ℂ] (Fin n₂ → ℂ) :=
    (TensorProduct.congr (LinearEquiv.funUnique (Fin 1) ℂ ℂ)
      (LinearEquiv.refl ℂ (Fin n₂ → ℂ))).trans e
  refine ⟨n₂, charTrans e' (ρ₁.tprod ρ₂), ?_⟩
  ext x
  calc
    (lam * ν) x
        = (LinearMap.trace ℂ (Fin 1 → ℂ)) (ρ₁ x) *
          (LinearMap.trace ℂ (Fin n₂ → ℂ)) (ρ₂ x) := by
            simp [Pi.mul_apply, hlameq, hνeq, Representation.character]
    _ = (LinearMap.trace ℂ ((Fin 1 → ℂ) ⊗[ℂ] (Fin n₂ → ℂ))) ((ρ₁.tprod ρ₂) x) := by
            exact (congrFun (Representation.char_tensor ρ₁ ρ₂) x).symm
    _ = (charTrans e' (ρ₁.tprod ρ₂)).character x := by
            exact congrFun (Representation.char_iso (equiv_charTrans e' (ρ₁.tprod ρ₂))) x

/-- The product of a linear character and an irreducible character is irreducible. -/
public theorem isIrreducibleCharacter_mul_linear {G : Type u} [Group G] [Fintype G]
    {lam ν : ClassFunction G} (hlam : IsLinearCharacter lam) (hν : IsIrreducibleCharacter ν) :
    IsIrreducibleCharacter (lam * ν) := by
  refine isIrreducibleCharacter_of_norm_one_inv ?hchar ?hnorm
  · exact isCharacter_mul_linear hlam (isCharacter_of_isIrreducibleCharacter hν)
  · calc
      scalarProductInv G (lam * ν) (lam * ν)
          = (Nat.card G : ℂ)⁻¹ * ∑ g : G, (lam g * ν g) * (lam g⁻¹ * ν g⁻¹) := rfl
      _ = (Nat.card G : ℂ)⁻¹ * ∑ g : G, (lam g * lam g⁻¹) * (ν g * ν g⁻¹) := by
              refine congrArg (fun t : ℂ => (Nat.card G : ℂ)⁻¹ * t) ?_
              refine Finset.sum_congr rfl ?_
              intro g hg
              ring
      _ = (Nat.card G : ℂ)⁻¹ * ∑ g : G, (ν g * ν g⁻¹) := by
              refine congrArg (fun t : ℂ => (Nat.card G : ℂ)⁻¹ * t) ?_
              refine Finset.sum_congr rfl ?_
              intro g hg
              have h1 : lam g * lam g⁻¹ = 1 := by
                have h := linearChar_mul hlam g g⁻¹
                rw [← h]
                rw [mul_inv_cancel, hlam.2]
              rw [h1]
              simp
      _ = scalarProductInv G ν ν := rfl
      _ = 1 := isIrreducible_norm_inv_one hν

/-- The zero class function is a character (of the zero-dimensional representation). -/
public theorem isCharacter_zero {G : Type u} [Group G] :
    IsCharacter (0 : ClassFunction G) := by
  refine ⟨0, { toFun := fun _ => 0
               map_one' := by
                 apply LinearMap.ext
                 intro v
                 ext i
                 exact False.elim (Nat.not_lt_zero i.1 i.2)
               map_mul' := by
                 intro x y
                 apply LinearMap.ext
                 intro v
                 ext i
                 exact False.elim (Nat.not_lt_zero i.1 i.2) }, ?_⟩
  ext x
  change (0 : ℂ) = (LinearMap.trace ℂ (Fin 0 → ℂ)) (0 : (Fin 0 → ℂ) →ₗ[ℂ] (Fin 0 → ℂ))
  simp

/-- The restriction of a character to a subgroup is a character. -/
public theorem isCharacter_restrict {G : Type u} [Group G] (H : Subgroup G)
    {χ : ClassFunction G} (hχ : IsCharacter χ) : IsCharacter (fun x : ↥H => χ (x : G)) := by
  rcases hχ with ⟨n, ρ, hχeq⟩
  let ρ' : Representation ℂ (↥H) (Fin n → ℂ) :=
    { toFun := fun x => ρ (x : G)
      map_one' := by
        apply LinearMap.ext
        intro v
        exact congrArg (fun f : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) => f v) (ρ.map_one')
      map_mul' := by
        intro x y
        apply LinearMap.ext
        intro v
        exact congrArg (fun f : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) => f v) (ρ.map_mul' x y) }
  refine ⟨n, ρ', ?_⟩
  ext x
  rw [hχeq]
  change ρ.character (x : G) = (LinearMap.trace ℂ (Fin n → ℂ)) (ρ (x : G))
  rfl

/-- The restriction of a generalized character to a subgroup is a generalized character. -/
public theorem isGeneralizedCharacter_restrict {G : Type u} [Group G] (H : Subgroup G)
    {φ : ClassFunction G} (hφ : IsGeneralizedCharacter φ) :
    IsGeneralizedCharacter (fun x : ↥H => φ (x : G)) := by
  rcases hφ with ⟨ξ, ψ, hξ, hψ, hφeq⟩
  refine ⟨fun x : ↥H => ξ (x : G), fun x : ↥H => ψ (x : G),
    isCharacter_restrict H hξ, isCharacter_restrict H hψ, ?_⟩
  ext x
  simpa using congrFun hφeq (x : G)

end LinearCharacter

/-! ## The regular representation and finiteness of irreducible characters -/

section Regular

/-- The left regular representation of `G` on `G →₀ ℂ`. -/
public def regularRep (G : Type u) [Group G] : Representation ℂ G (G →₀ ℂ) where
  toFun g := Finsupp.lmapDomain ℂ ℂ (fun x : G => g * x)
  map_one' := by
    apply LinearMap.ext
    intro f
    apply Finsupp.ext
    intro x
    rw [Finsupp.lmapDomain_apply]
    have h : (fun x : G => (1 : G) * x) = _root_.id := by
      funext x
      exact one_mul x
    rw [h, Finsupp.mapDomain_id]
    simp
  map_mul' := by
    intro g h
    apply LinearMap.ext
    intro f
    apply Finsupp.ext
    intro x
    change (Finsupp.mapDomain (fun y : G => g * h * y) f) x =
      (Finsupp.lmapDomain ℂ ℂ (fun y : G => g * y))
        ((Finsupp.lmapDomain ℂ ℂ (fun y : G => h * y)) f) x
    rw [Finsupp.lmapDomain_apply, Finsupp.lmapDomain_apply]
    rw [← Finsupp.mapDomain_comp]
    have hf : (fun y : G => g * h * y) = (fun y : G => g * y) ∘ (fun y : G => h * y) := by
      funext y
      change g * h * y = g * (h * y)
      group
    rw [hf]

/-- The regular character at `g` is the number of fixed points of left multiplication by `g`. -/
private theorem regularRep_char_sum {G : Type u} [Group G] [Fintype G] [DecidableEq G] (g : G) :
    (regularRep G).character g = ∑ x : G, (if g * x = x then (1 : ℂ) else 0) := by
  classical
  let e : G ≃ Fin (Nat.card G) :=
    Fintype.equivFinOfCardEq (show Fintype.card G = Nat.card G by rw [Nat.card_eq_fintype_card])
  let b : Module.Basis (Fin (Nat.card G)) ℂ (G →₀ ℂ) :=
    Module.Basis.ofRepr (Finsupp.lcongr e (LinearEquiv.refl ℂ ℂ))
  have hmat : ∀ i j : Fin (Nat.card G),
      (LinearMap.toMatrix b b ((regularRep G) g)) i j =
        if e (g * e.symm j) = i then (1 : ℂ) else 0 := by
    intro i j
    rw [LinearMap.toMatrix_apply]
    have hbj : b j = Finsupp.single (e.symm j) (1 : ℂ) := by
      simp [b]
    rw [hbj]
    change (b.repr (Finsupp.lmapDomain ℂ ℂ (fun x : G => g * x)
      (Finsupp.single (e.symm j) (1 : ℂ)))) i = if e (g * e.symm j) = i then (1 : ℂ) else 0
    rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
    simp [b]
    rw [Finsupp.single_apply]
  calc
    (regularRep G).character g
        = (LinearMap.trace ℂ (G →₀ ℂ)) ((regularRep G) g) := rfl
    _ = (LinearMap.toMatrix b b ((regularRep G) g)).trace := by
            rw [LinearMap.trace_eq_matrix_trace ℂ b]
    _ = ∑ x : Fin (Nat.card G), (LinearMap.toMatrix b b ((regularRep G) g)) x x := rfl
    _ = ∑ x : Fin (Nat.card G), (if e (g * e.symm x) = x then (1 : ℂ) else 0) := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            rw [hmat]
    _ = ∑ x : G, (if g * x = x then (1 : ℂ) else 0) := by
            refine Finset.sum_bij (fun x hx => e.symm x) (by intro x hx; simp) ?_ ?_ ?_
            · intro a ha b hb hEq
              exact e.symm.injective hEq
            · intro x hx
              refine ⟨e x, by simp, ?_⟩
              exact e.symm_apply_apply x
            · intro x hx
              by_cases h : e (g * e.symm x) = x
              · have h' : g * e.symm x = e.symm x := by
                  have := congrArg e.symm h
                  simpa using this
                simp [h']
              · have h' : ¬ g * e.symm x = e.symm x := by
                  intro hq
                  apply h
                  have := congrArg e hq
                  simpa using this
                simp [h, h']

/-- The regular character at the identity: `|G|`. -/
public theorem regularRep_char_one {G : Type u} [Group G] [Fintype G] :
    (regularRep G).character (1 : G) = (Nat.card G : ℂ) := by
  classical
  rw [regularRep_char_sum]
  simp [one_mul, Nat.card_eq_fintype_card]

/-- The regular character vanishes off the identity. -/
public theorem regularRep_char_of_ne {G : Type u} [Group G] [Fintype G] {g : G}
    (hg : g ≠ 1) : (regularRep G).character g = 0 := by
  classical
  rw [regularRep_char_sum]
  have hfp : ∀ x : G, g * x ≠ x := by
    intro x hx
    exact hg (mul_right_cancel (by simpa [one_mul] using hx : g * x = 1 * x))
  simp [hfp]

/-- Every irreducible character occurs as a constituent of the regular character. -/
public theorem irr_occurs_in_regular {G : Type u} [Group G] [Fintype G]
    {ν : ClassFunction G} (hν : IsIrreducibleCharacter ν) :
    scalarProduct G ν (regularRep G).character ≠ 0 := by
  have hdeg : ν 1 ≠ 0 := irreducible_char_one_ne_zero hν
  have hval : scalarProduct G ν (regularRep G).character = ν 1 := by
    calc
      scalarProduct G ν (regularRep G).character
          = (Nat.card G : ℂ)⁻¹ * ∑ g : G, ν g * star ((regularRep G).character g) := rfl
      _ = (Nat.card G : ℂ)⁻¹ * (ν 1 * star ((Nat.card G : ℂ))) := by
              congr 1
              calc
                ∑ g : G, ν g * star ((regularRep G).character g)
                    = ν 1 * star ((regularRep G).character 1) := by
                        refine Finset.sum_eq_single 1 ?_ ?_
                        · intro g hg hg1
                          simp [regularRep_char_of_ne hg1]
                        · intro hnot
                          exact (hnot (Finset.mem_univ 1)).elim
                _ = ν 1 * star ((Nat.card G : ℂ)) := by
                        rw [regularRep_char_one]
      _ = ν 1 := by
            have hc : (Fintype.card G : ℂ) ≠ 0 := by
              exact_mod_cast (Fintype.card_pos (α := G)).ne'
            calc
              (Nat.card G : ℂ)⁻¹ * (ν 1 * star ((Nat.card G : ℂ)))
                  = (Fintype.card G : ℂ)⁻¹ * (ν 1 * (Fintype.card G : ℂ)) := by simp
              _ = (Fintype.card G : ℂ)⁻¹ * (Fintype.card G : ℂ) * ν 1 := by ring
              _ = ν 1 := by
                      rw [inv_mul_cancel₀ hc, one_mul]
  rw [hval]
  exact hdeg

/-- The irreducible characters of a finite group form a finite type. -/
public noncomputable instance instFintypeIrr (G : Type u) [Group G] [Fintype G] :
    Fintype {ν : ClassFunction G // IsIrreducibleCharacter ν} := by
  classical
  let φ : ClassFunction G := (regularRep G).character
  have hφ : IsGeneralizedCharacter φ := by
    refine ⟨φ, 0, ?_, isCharacter_zero, ?_⟩
    · let e : (G →₀ ℂ) ≃ₗ[ℂ] (Fin (Nat.card G) → ℂ) :=
        (Finsupp.linearEquivFunOnFinite ℂ ℂ G).trans
          (LinearEquiv.funCongrLeft ℂ ℂ
            (Fintype.equivFinOfCardEq (show Fintype.card G = Nat.card G by rw [Nat.card_eq_fintype_card])).symm)
      refine ⟨Nat.card G, charTrans e (regularRep G), ?_⟩
      ext x
      simpa [φ] using
        (congrFun (Representation.char_iso (equiv_charTrans e (regularRep G))) x)
    · ext x
      simp
  choose ι instι χs ms hirr hdist hφsum using char_decomp_generalized hφ
  letI : Fintype ι := instι
  have hocc : ∀ ν : {ν : ClassFunction G // IsIrreducibleCharacter ν},
      ∃ i : ι, χs i = ν.1 := by
    intro ν
    have hne : scalarProduct G ν.1 φ ≠ 0 := by
      simpa [φ] using irr_occurs_in_regular ν.2
    have hsp : scalarProduct G ν.1 φ = ∑ i, (ms i : ℂ) * scalarProduct G ν.1 (χs i) := by
      rw [hφsum]
      rw [scalarProduct_sum_right]
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [scalarProduct_smul_right]
      rw [mul_comm]
      simp
    have hne' : (∑ i, (ms i : ℂ) * scalarProduct G ν.1 (χs i)) ≠ 0 := by
      rwa [← hsp]
    have hex : ∃ i, (ms i : ℂ) * scalarProduct G ν.1 (χs i) ≠ 0 := by
      by_contra hnone
      have hall : ∀ i, (ms i : ℂ) * scalarProduct G ν.1 (χs i) = 0 := by
        intro i
        by_contra h
        exact hnone ⟨i, h⟩
      exact hne' (by simp [hall])
    rcases hex with ⟨i, hterm⟩
    have hspi : scalarProduct G ν.1 (χs i) ≠ 0 := by
      intro hsp0
      exact hterm (by simp [hsp0])
    have hEq : χs i = ν.1 := by
      by_contra hnei
      have h0 : scalarProduct G ν.1 (χs i) = 0 :=
        irreducible_scalarProduct_of_ne ν.2 (hirr i) (fun hEq => hnei hEq.symm)
      exact hspi h0
    exact ⟨i, hEq⟩
  refine Fintype.ofSurjective (fun i : ι => ⟨χs i, hirr i⟩) ?_
  intro ν
  rcases hocc ν with ⟨i, hEq⟩
  exact ⟨i, Subtype.ext hEq⟩

/-- Fourier expansion of a generalized character in the irreducible characters. -/
public theorem classFunction_eq_sum_irr_coeffs {G : Type u} [Group G] [Fintype G]
    [Fintype ({ν : ClassFunction G // IsIrreducibleCharacter ν})]
    {φ : ClassFunction G} (hφ : IsGeneralizedCharacter φ) (x : G) :
    φ x = ∑ ν : {ν : ClassFunction G // IsIrreducibleCharacter ν},
      scalarProduct G φ ν.1 * ν.1 x := by
  classical
  rcases char_decomp_generalized hφ with ⟨ι, instι, χs, ms, hirr, hdist, hφsum⟩
  let : Fintype ι := instι
  have hcoeff : ∀ i : ι, scalarProduct G φ (χs i) = (ms i : ℂ) := by
    intro i
    calc
      scalarProduct G φ (χs i) = scalarProduct G (∑ j, (ms j : ℂ) • χs j) (χs i) := by
        rw [hφsum]
      _ = ∑ j, (ms j : ℂ) * scalarProduct G (χs j) (χs i) := by
            rw [scalarProduct_sum_left]
            refine Finset.sum_congr rfl ?_
            intro j hj
            rw [scalarProduct_smul_left]
      _ = (ms i : ℂ) := by
            rw [Finset.sum_eq_single i]
            · simp [irreducible_scalarProduct_self (hirr i)]
            · intro j hj hji
              simp [
                irreducible_scalarProduct_of_ne (hirr j) (hirr i) (hdist j i hji)]
            · intro hnot
              exact (hnot (Finset.mem_univ i)).elim
  have hocc' : ∀ ν : {ν : ClassFunction G // IsIrreducibleCharacter ν},
      scalarProduct G φ ν.1 ≠ 0 → ∃ i : ι, χs i = ν.1 := by
    intro ν hne
    have hsp : scalarProduct G φ ν.1 = ∑ i, (ms i : ℂ) * scalarProduct G (χs i) ν.1 := by
      rw [hφsum]
      rw [scalarProduct_sum_left]
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [scalarProduct_smul_left]
    have hne' : (∑ i, (ms i : ℂ) * scalarProduct G (χs i) ν.1) ≠ 0 := by
      rwa [← hsp]
    have hex : ∃ i, (ms i : ℂ) * scalarProduct G (χs i) ν.1 ≠ 0 := by
      by_contra hnone
      have hall : ∀ i, (ms i : ℂ) * scalarProduct G (χs i) ν.1 = 0 := by
        intro i
        by_contra h
        exact hnone ⟨i, h⟩
      exact hne' (by simp [hall])
    rcases hex with ⟨i, hterm⟩
    have hspi : scalarProduct G (χs i) ν.1 ≠ 0 := by
      intro hsp0
      exact hterm (by simp [hsp0])
    have hEq : χs i = ν.1 := by
      by_contra hnei
      have h0 : scalarProduct G (χs i) ν.1 = 0 :=
        irreducible_scalarProduct_of_ne (hirr i) ν.2 hnei
      exact hspi h0
    exact ⟨i, hEq⟩
  have hsum1 : (∑ ν : {ν : ClassFunction G // IsIrreducibleCharacter ν},
      scalarProduct G φ ν.1 * ν.1 x) = ∑ i : ι, (ms i : ℂ) * χs i x := by
    classical
    let s : Finset {ν : ClassFunction G // IsIrreducibleCharacter ν} :=
      Finset.univ.filter (fun ν => scalarProduct G φ ν.1 ≠ 0)
    let t : Finset ι := Finset.univ.filter (fun i => (ms i : ℂ) ≠ 0)
    have h1 : (∑ ν : {ν : ClassFunction G // IsIrreducibleCharacter ν},
        scalarProduct G φ ν.1 * ν.1 x) = ∑ ν ∈ s, scalarProduct G φ ν.1 * ν.1 x := by
      symm
      exact Finset.sum_subset (Finset.subset_univ _) (by
        intro ν hν hnot
        have hsp0 : scalarProduct G φ ν.1 = 0 := by
          by_contra hsp
          exact hnot (by simpa [s])
        simp [hsp0])
    have h2 : (∑ ν ∈ s, scalarProduct G φ ν.1 * ν.1 x) = ∑ i ∈ t, (ms i : ℂ) * χs i x := by
      symm
      exact Finset.sum_bij (fun i hi => (⟨χs i, hirr i⟩ : {ν : ClassFunction G // IsIrreducibleCharacter ν}))
        (by
          intro i hi
          have hmi : (ms i : ℂ) ≠ 0 := by
            simpa [t] using hi
          simpa [s, hcoeff i] using hmi)
        (by
          intro a ha b hb hEq
          have hχs : χs a = χs b := congrArg Subtype.val hEq
          by_contra hab
          exact (hdist a b hab) hχs)
        (by
          intro ν hν
          have hmem : scalarProduct G φ ν.1 ≠ 0 := (Finset.mem_filter.mp hν).2
          rcases hocc' ν hmem with ⟨i, hEq⟩
          refine ⟨i, ?_, ?_⟩
          · have hspi : (ms i : ℂ) ≠ 0 := by
              rw [← hcoeff i]
              rw [hEq]
              exact hmem
            simpa [t] using hspi
          · exact Subtype.ext hEq)
        (by
          intro i hi
          rw [hcoeff])
    have h3 : (∑ i ∈ t, (ms i : ℂ) * χs i x) = ∑ i : ι, (ms i : ℂ) * χs i x := by
      exact Finset.sum_subset (Finset.subset_univ _) (by
        intro i hi hnot
        have hmi : (ms i : ℂ) = 0 := by
          by_contra hmi'
          exact (hnot (by simpa [t] using hmi')).elim
        simp [hmi])
    calc
      (∑ ν : {ν : ClassFunction G // IsIrreducibleCharacter ν},
          scalarProduct G φ ν.1 * ν.1 x) = ∑ ν ∈ s, scalarProduct G φ ν.1 * ν.1 x := h1
      _ = ∑ i ∈ t, (ms i : ℂ) * χs i x := h2
      _ = ∑ i : ι, (ms i : ℂ) * χs i x := h3
  calc
    φ x = ∑ i : ι, (ms i : ℂ) * χs i x := by
          rw [hφsum]
          simp
    _ = ∑ ν : {ν : ClassFunction G // IsIrreducibleCharacter ν},
          scalarProduct G φ ν.1 * ν.1 x := hsum1.symm

end Regular

/-! ## Frobenius reciprocity and linearity of induction -/

section Reciprocity

/-- The induced class function is additive. -/
public theorem inducedClassFunction_add {G : Type u} [Group G] [Fintype G]
    (H : Subgroup G) (δ₁ δ₂ : ClassFunction (↥H)) :
    inducedClassFunction H (δ₁ + δ₂) = inducedClassFunction H δ₁ + inducedClassFunction H δ₂ := by
  classical
  ext g
  unfold inducedClassFunction
  calc
    (Nat.card (↥H) : ℂ)⁻¹ * ∑ x : G,
        (if hx : x⁻¹ * g * x ∈ H then (δ₁ + δ₂) ⟨x⁻¹ * g * x, hx⟩ else 0)
        = (Nat.card (↥H) : ℂ)⁻¹ * ∑ x : G,
            ((if hx : x⁻¹ * g * x ∈ H then δ₁ ⟨x⁻¹ * g * x, hx⟩ else 0) +
              (if hx : x⁻¹ * g * x ∈ H then δ₂ ⟨x⁻¹ * g * x, hx⟩ else 0)) := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro x hx
            by_cases h : x⁻¹ * g * x ∈ H <;> simp [h]
    _ = (Nat.card (↥H) : ℂ)⁻¹ *
          (∑ x : G, (if hx : x⁻¹ * g * x ∈ H then δ₁ ⟨x⁻¹ * g * x, hx⟩ else 0) +
            ∑ x : G, (if hx : x⁻¹ * g * x ∈ H then δ₂ ⟨x⁻¹ * g * x, hx⟩ else 0)) := by
            rw [Finset.sum_add_distrib]
    _ = (Nat.card (↥H) : ℂ)⁻¹ * ∑ x : G,
          (if hx : x⁻¹ * g * x ∈ H then δ₁ ⟨x⁻¹ * g * x, hx⟩ else 0) +
        (Nat.card (↥H) : ℂ)⁻¹ * ∑ x : G,
          (if hx : x⁻¹ * g * x ∈ H then δ₂ ⟨x⁻¹ * g * x, hx⟩ else 0) := by
            rw [mul_add]

/-- The induced class function is negated under negation. -/
public theorem inducedClassFunction_neg {G : Type u} [Group G] [Fintype G]
    (H : Subgroup G) (δ : ClassFunction (↥H)) :
    inducedClassFunction H (-δ) = -inducedClassFunction H δ := by
  classical
  ext g
  unfold inducedClassFunction
  calc
    (Nat.card (↥H) : ℂ)⁻¹ * ∑ x : G,
        (if hx : x⁻¹ * g * x ∈ H then (-δ) ⟨x⁻¹ * g * x, hx⟩ else 0)
        = (Nat.card (↥H) : ℂ)⁻¹ * ∑ x : G,
            -(if hx : x⁻¹ * g * x ∈ H then δ ⟨x⁻¹ * g * x, hx⟩ else 0) := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro x hx
            by_cases h : x⁻¹ * g * x ∈ H <;> simp [h]
    _ = (Nat.card (↥H) : ℂ)⁻¹ *
          -(∑ x : G, (if hx : x⁻¹ * g * x ∈ H then δ ⟨x⁻¹ * g * x, hx⟩ else 0)) := by
            rw [Finset.sum_neg_distrib]
    _ = -((Nat.card (↥H) : ℂ)⁻¹ *
          (∑ x : G, (if hx : x⁻¹ * g * x ∈ H then δ ⟨x⁻¹ * g * x, hx⟩ else 0))) := by
            rw [mul_neg]

/-- The induced class function is linear in the second argument of the scalar product. -/
public theorem scalarProduct_induced_neg {G : Type u} [Group G] [Fintype G]
    (H : Subgroup G) (χ : ClassFunction G) (δ : ClassFunction (↥H)) :
    scalarProduct G χ (inducedClassFunction H (-δ)) =
      -scalarProduct G χ (inducedClassFunction H δ) := by
  rw [inducedClassFunction_neg, scalarProduct_neg_right]

/-- Frobenius reciprocity: `(δ^G, χ)_G = (δ, χ|_H)_H` for a class function `χ`. -/
public theorem frobenius_reciprocity {G : Type u} [Group G] [Fintype G] (H : Subgroup G)
    (δ : ClassFunction (↥H)) {χ : ClassFunction G} (hχ : IsClassFunction χ) :
    scalarProduct G (inducedClassFunction H δ) χ =
      scalarProduct (↥H) δ (fun x : ↥H => χ (x : G)) := by
  classical
  let F : G → G → ℂ := fun g x =>
    if hx : x⁻¹ * g * x ∈ H then δ ⟨x⁻¹ * g * x, hx⟩ else 0
  calc
    scalarProduct G (inducedClassFunction H δ) χ
        = (Nat.card G : ℂ)⁻¹ * ∑ g : G, (inducedClassFunction H δ) g * star (χ g) := rfl
    _ = (Nat.card G : ℂ)⁻¹ * ∑ g : G,
          ((Nat.card (↥H) : ℂ)⁻¹ * ∑ x : G, F g x) * star (χ g) := rfl
    _ = (Nat.card G : ℂ)⁻¹ * (Nat.card (↥H) : ℂ)⁻¹ *
          ∑ g : G, ∑ x : G, F g x * star (χ g) := by
          calc
            (Nat.card G : ℂ)⁻¹ * ∑ g : G, ((Nat.card (↥H) : ℂ)⁻¹ * ∑ x : G, F g x) * star (χ g)
                = (Nat.card G : ℂ)⁻¹ * ((Nat.card (↥H) : ℂ)⁻¹ *
                    ∑ g : G, ∑ x : G, F g x * star (χ g)) := by
                    congr 1
                    calc
                      (∑ g : G, ((Nat.card (↥H) : ℂ)⁻¹ * ∑ x : G, F g x) * star (χ g))
                          = ∑ g : G, (Nat.card (↥H) : ℂ)⁻¹ *
                              ((∑ x : G, F g x) * star (χ g)) := by
                              refine Finset.sum_congr rfl ?_
                              intro g hg
                              ring
                      _ = (Nat.card (↥H) : ℂ)⁻¹ * ∑ g : G, (∑ x : G, F g x) * star (χ g) := by
                              rw [← Finset.mul_sum]
                      _ = (Nat.card (↥H) : ℂ)⁻¹ * ∑ g : G, ∑ x : G, F g x * star (χ g) := by
                              refine congrArg (fun t : ℂ => (Nat.card (↥H) : ℂ)⁻¹ * t) ?_
                              refine Finset.sum_congr rfl ?_
                              intro g hg
                              rw [Finset.sum_mul]
            _ = (Nat.card G : ℂ)⁻¹ * (Nat.card (↥H) : ℂ)⁻¹ *
                  ∑ g : G, ∑ x : G, F g x * star (χ g) := by
                  rw [← mul_assoc]
    _ = (Nat.card G : ℂ)⁻¹ * (Nat.card (↥H) : ℂ)⁻¹ *
          ∑ x : G, ∑ g : G, F g x * star (χ g) := by
          congr 1
          exact Finset.sum_comm
    _ = (Nat.card G : ℂ)⁻¹ * (Nat.card (↥H) : ℂ)⁻¹ *
          ∑ x : G, ∑ h : ↥H, δ h * star (χ (x * (h : G) * x⁻¹)) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro x hx
          calc
            (∑ g : G, F g x * star (χ g))
                = ∑ g ∈ Finset.univ.filter (fun g : G => x⁻¹ * g * x ∈ H),
                    F g x * star (χ g) := by
                    symm
                    exact Finset.sum_subset (Finset.subset_univ _) (by
                      intro g hg hnot
                      have hg' : ¬ x⁻¹ * g * x ∈ H := by
                        intro h
                        exact hnot (by simpa)
                      simp [F, hg'])
            _ = ∑ h : ↥H, δ h * star (χ (x * (h : G) * x⁻¹)) := by
                    refine Finset.sum_bij (fun g hg => ⟨x⁻¹ * g * x, (Finset.mem_filter.mp hg).2⟩)
                      (by intro g hg; simp)
                      ?_ ?_ ?_
                    · intro a ha b hb hEq
                      have hval : (⟨x⁻¹ * a * x, (Finset.mem_filter.mp ha).2⟩ : ↥H).1 =
                          (⟨x⁻¹ * b * x, (Finset.mem_filter.mp hb).2⟩ : ↥H).1 :=
                        congrArg Subtype.val hEq
                      exact mul_left_cancel (mul_right_cancel hval)
                    · intro h hh
                      refine ⟨x * (h : G) * x⁻¹, ?_, ?_⟩
                      · apply Finset.mem_filter.mpr
                        constructor
                        · exact Finset.mem_univ _
                        · change x⁻¹ * (x * (h : G) * x⁻¹) * x ∈ H
                          rw [show x⁻¹ * (x * (h : G) * x⁻¹) * x = (h : G) by group]
                          exact h.property
                      · apply Subtype.ext
                        group
                    · intro g hg
                      have hmem : x⁻¹ * g * x ∈ H := (Finset.mem_filter.mp hg).2
                      simp [F, hmem]
                      · left
                        congr 2
                        group
    _ = (Nat.card G : ℂ)⁻¹ * (Nat.card (↥H) : ℂ)⁻¹ *
          ((Nat.card G : ℂ) * ∑ h : ↥H, δ h * star (χ h)) := by
          congr 1
          have hinner : ∀ x : G,
              (∑ h : ↥H, δ h * star (χ (x * (h : G) * x⁻¹))) =
                ∑ h : ↥H, δ h * star (χ h) := by
            intro x
            refine Finset.sum_congr rfl ?_
            intro h hh
            congr 2
            exact hχ h x
          calc
            ∑ x : G, ∑ h : ↥H, δ h * star (χ (x * (h : G) * x⁻¹))
                = ∑ x : G, ∑ h : ↥H, δ h * star (χ h) := by
                    refine Finset.sum_congr rfl ?_
                    intro x hx
                    exact hinner x
            _ = (Nat.card G : ℂ) * ∑ h : ↥H, δ h * star (χ h) := by
                    rw [Nat.card_eq_fintype_card]
                    simp
    _ = (Nat.card (↥H) : ℂ)⁻¹ * ∑ h : ↥H, δ h * star (χ h) := by
          let S : ℂ := ∑ h : ↥H, δ h * star (χ h)
          have hc : (Nat.card G : ℂ) ≠ 0 := by
            exact_mod_cast (Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩)
          calc
            (Nat.card G : ℂ)⁻¹ * (Nat.card (↥H) : ℂ)⁻¹ * ((Nat.card G : ℂ) * S)
                = (Nat.card G : ℂ)⁻¹ * (Nat.card G : ℂ) * ((Nat.card (↥H) : ℂ)⁻¹ * S) := by ring
            _ = (Nat.card (↥H) : ℂ)⁻¹ * S := by
                    rw [inv_mul_cancel₀ hc, one_mul]
    _ = scalarProduct (↥H) δ (fun x : ↥H => χ (x : G)) := rfl

/-- Induction is additive on differences: `(δ₁ - δ₂)* = δ₁* - δ₂*`. -/
public theorem inducedClassFunction_sub {G : Type u} [Group G] [Fintype G]
    (H : Subgroup G) (δ₁ δ₂ : ClassFunction (↥H)) :
    inducedClassFunction H (δ₁ - δ₂) = inducedClassFunction H δ₁ - inducedClassFunction H δ₂ := by
  rw [sub_eq_add_neg, inducedClassFunction_add, inducedClassFunction_neg, sub_eq_add_neg]

/-- The induced class function of zero is zero. -/
public theorem inducedClassFunction_zero {G : Type u} [Group G] [Fintype G]
    (H : Subgroup G) : inducedClassFunction H (0 : ClassFunction (↥H)) = 0 := by
  ext g
  unfold inducedClassFunction
  simp

/-- The scalar product against zero vanishes. -/
public theorem scalarProduct_zero_right {G : Type u} [Group G] [Fintype G]
    (φ : ClassFunction G) : scalarProduct G φ 0 = 0 := by
  simp [scalarProduct]

/-- Frobenius reciprocity in the restriction form: `(χ|_{H}, δ)_H = (χ, δ*)_G`. -/
public theorem scalarProduct_restrict_induced {G : Type u} [Group G] [Fintype G]
    (H : Subgroup G) {χ : ClassFunction G} (hχ : IsClassFunction χ)
    (δ : ClassFunction (↥H)) :
    scalarProduct (↥H) (fun x : ↥H => χ (x : G)) δ =
      scalarProduct G χ (inducedClassFunction H δ) := by
  calc
    scalarProduct (↥H) (fun x : ↥H => χ (x : G)) δ
        = star (scalarProduct (↥H) δ (fun x : ↥H => χ (x : G))) := by
            rw [← scalarProduct_conj]
    _ = star (scalarProduct G (inducedClassFunction H δ) χ) := by
            rw [frobenius_reciprocity H δ hχ]
    _ = scalarProduct G χ (inducedClassFunction H δ) := by
            rw [scalarProduct_conj]

end Reciprocity

section CentralValues

variable {G : Type u} [Group G] [Fintype G]

/-- Schur: for a central element `t` with `t² = 1` acting on an irreducible
representation `ρ`, there is a scalar `a` with `a² = 1` and `ρ(t) = a·1`. -/
private theorem rep_apply_central_scalar {t : G} (htc : ∀ g : G, t * g = g * t)
    (ht2 : t ^ 2 = 1) {n : ℕ} (ρ : Representation ℂ G (Fin n → ℂ))
    (hρirr : Representation.IsIrreducible ρ) :
    ∃ a : ℂ, ρ t = a • (1 : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ∧ a ^ 2 = 1 := by
  classical
  let : Representation.IsIrreducible ρ := hρirr
  have hcomm (g : G) : ρ t * ρ g = ρ g * ρ t := by
    rw [← map_mul, ← map_mul, htc g]
  let τ : Representation.IntertwiningMap ρ ρ := ⟨ρ t, by
    intro g
    apply LinearMap.ext
    intro v
    exact congrArg (fun f : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) => f v) (hcomm g)⟩
  have hfin : Module.finrank ℂ (Representation.IntertwiningMap ρ ρ) = 1 :=
    (irreducible_iff_end_dimension_one (ρ := ρ)).1 hρirr
  have : Nontrivial (Fin n → ℂ) := irreducible_nontrivial (ρ := ρ)
  have hone_ne_zero : (1 : Representation.IntertwiningMap ρ ρ) ≠ 0 := by
    intro h
    obtain ⟨v, hv⟩ := exists_ne (0 : Fin n → ℂ)
    have hvzero : v = 0 := by
      simpa using congrArg (fun f : Representation.IntertwiningMap ρ ρ => f v) h
    exact hv hvzero
  obtain ⟨a, ha⟩ : ∃ a : ℂ, a • (1 : Representation.IntertwiningMap ρ ρ) = τ :=
    (finrank_eq_one_iff_of_nonzero' (K := ℂ)
      (V := Representation.IntertwiningMap ρ ρ)
      (1 : Representation.IntertwiningMap ρ ρ) hone_ne_zero).mp hfin τ
  have hscalar : ρ t = a • (1 : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) := by
    have htm := congrArg (fun f : Representation.IntertwiningMap ρ ρ => f.toLinearMap) ha
    change τ.toLinearMap = (a • (1 : Representation.IntertwiningMap ρ ρ)).toLinearMap
    exact htm.symm
  have ha2 : a ^ 2 = 1 := by
    have hunit : (ρ t) * (ρ t) = 1 := by
      rw [← map_mul]
      have ht2' : t * t = 1 := by simpa [pow_two] using ht2
      rw [ht2', map_one]
    have hsq : (a • (1 : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))) * (a • 1) = 1 := by
      rw [← hscalar]
      exact hunit
    obtain ⟨v, hv⟩ := exists_ne (0 : Fin n → ℂ)
    have hv2 : (a • (a • v)) = v := by
      have h := congrArg (fun f : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) => f v) hsq
      simpa using h
    have hsmul : (a ^ 2) • v = v := by
      simpa [smul_smul, pow_two] using hv2
    have hsmul' : (a ^ 2) • v = (1 : ℂ) • v := by
      rw [one_smul]
      exact hsmul
    exact smul_left_injective ℂ hv hsmul'
  exact ⟨a, hscalar, ha2⟩

/-- An irreducible character does not vanish at a central involution:
`ρ(t) = ±1` on an irreducible module by Schur's lemma, so `χ(t) = ±χ(1) ≠ 0`. -/
public theorem char_apply_central_ne_zero {t : G} (htc : ∀ g : G, t * g = g * t)
    (ht2 : t ^ 2 = 1) {ν : ClassFunction G} (hν : IsIrreducibleCharacter ν) :
    ν t ≠ 0 := by
  classical
  rcases hν with ⟨n, ρ, hρirr, hνeq⟩
  let : Representation.IsIrreducible ρ := hρirr
  have : Nontrivial (Fin n → ℂ) := irreducible_nontrivial (ρ := ρ)
  rcases rep_apply_central_scalar htc ht2 ρ hρirr with ⟨a, hscalar, ha2⟩
  have ha_ne : a ≠ 0 := by
    intro ha0
    rw [ha0] at ha2
    norm_num at ha2
  have hdim_pos : 0 < Module.finrank ℂ (Fin n → ℂ) :=
    (Module.finrank_pos_iff (R := ℂ) (M := Fin n → ℂ)).2 inferInstance
  have hdim_ne : (Module.finrank ℂ (Fin n → ℂ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hdim_pos)
  rw [hνeq]
  change LinearMap.trace ℂ (Fin n → ℂ) (ρ t) ≠ 0
  rw [hscalar, map_smul, LinearMap.trace_one]
  simpa using (mul_ne_zero ha_ne hdim_ne)

/-- For a central involution `t` and an irreducible character `ν`:
`ν(t) = ±ν(1)`. -/
public theorem char_apply_central_sign {t : G} (htc : ∀ g : G, t * g = g * t)
    (ht2 : t ^ 2 = 1) {ν : ClassFunction G} (hν : IsIrreducibleCharacter ν) :
    ν t = ν 1 ∨ ν t = -ν 1 := by
  classical
  rcases hν with ⟨n, ρ, hρirr, hνeq⟩
  rcases rep_apply_central_scalar htc ht2 ρ hρirr with ⟨a, hscalar, ha2⟩
  have ha_cases : a = 1 ∨ a = -1 := by
    rw [← sq_eq_one_iff]
    exact ha2
  have hρ1 : ρ (1 : G) = 1 := map_one ρ
  have ht' : ν t = a * ν 1 := by
    rw [hνeq]
    change LinearMap.trace ℂ (Fin n → ℂ) (ρ t) = a * LinearMap.trace ℂ (Fin n → ℂ) (ρ 1)
    rw [hscalar, LinearMap.map_smul, hρ1]
    simp [smul_eq_mul]
  rcases ha_cases with rfl | rfl
  · left
    simpa using ht'
  · right
    simpa using ht'

end CentralValues

end CFSG.BenderGlauberman
