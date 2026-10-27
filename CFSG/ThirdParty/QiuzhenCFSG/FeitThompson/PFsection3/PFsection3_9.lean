module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection3.PFsection3_2
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection3.PFsection3_8
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_9
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.Divisibility

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 3, Proposition (3.9)

This file starts the Lean formalization of PF (3.9).  The first helpers expose
the signed-irreducible inner-product rigidity that will be used in the
uniqueness part `(3.9)(a)`.

No result from BG is imported here.
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section3

universe u v

/-! ## (3.9) -/


/--
`ωk` is the value-wise integer `k`-th power of `ω`.  This is the source-facing
form of the book notation `ω^k` in PF (3.9)(b), where `k ∈ ℤ`.
-/
@[expose] public def classFunctionValueZPow
    {G : Type u} [Group G]
    (ω ωk : Section1.ClassFunction G) (k : ℤ) : Prop :=
  ∀ g : G, ωk g = ω g ^ k

/--
`ψ` is obtained from `φ` by sending each group element to its `e`-th power.
This is the exponent-form avatar of the cyclotomic Galois action used in
PF (1.9)(b).
-/
@[expose] public def classFunctionArgumentPow
    {G : Type u} [Group G]
    (φ ψ : Section1.ClassFunction G) (e : ℕ) : Prop :=
  ∀ g : G, ψ g = φ (g ^ e)

/--
The positive integer `a` is a common order for the values of `ω`: every value
of `ω` is an `a`-th root of unity.
-/
@[expose] public def characterValueOrder
    {G : Type u} [Group G]
    (ω : Section1.ClassFunction G) (a : ℕ) : Prop :=
  0 < a ∧ ∀ g : G, ω g ^ a = 1

/--
`exactCharacterValueOrder ω a` says that `a` is the exact common order for the
values of `ω`: every value of `ω` is an `a`-th root of unity, and every other
common order is divisible by `a`.
-/
@[expose] public def exactCharacterValueOrder
    {G : Type u} [Group G]
    (ω : Section1.ClassFunction G) (a : ℕ) : Prop :=
  characterValueOrder ω a ∧
    ∀ b : ℕ, characterValueOrder ω b → a ∣ b

/--
`valueOrderCardPart a c` says that `c` is the `|G|`-part attached to the
exact value-order parameter `a`: it is divisible by `a` and has exactly the
same prime divisors.  This separates the value-order arithmetic from the CRT
factorization used in PF (1.9)(b).
-/
@[expose] public def valueOrderCardPart (a c : ℕ) : Prop :=
  a ∣ c ∧ ∀ p : ℕ, p.Prime → (p ∣ c ↔ p ∣ a)

/--
The PF (1.9)(b) Galois-side condition used by PF (3.9)(b), with the book's
integer exponent.  The chosen automorphism of the cyclotomic model for
`ℚ_|G|` acts as the `k`-power automorphism on the `c`-part and trivially on
the complementary `b`-part.
-/
@[expose] public def proposition_3_9_galoisCondition_int
    {G : Type u} [Group G] [Finite G]
    {c b : ℕ} {k : ℤ}
    (hcard : Nat.card G = c * b)
    (v : Gal((Section1.CyclotomicABField c b)/ℚ)) : Prop :=
  ∃ hk : IsCoprime k (c : ℤ),
    Section1.proposition_1_9_b_galoisCondition_int
      (G := G) hcard hk v

/--
The Galois conjugate of a class function, used for the source-facing
commutation sentences in PF (3.9).
-/
@[expose] public def classFunctionGaloisConjugate
    {G : Type u} [Group G]
    (τ : Gal(ℂ/ℚ)) (χ : Section1.ClassFunction G) : Section1.ClassFunction G :=
  fun g => τ (χ g)

/--
`τ` represents an automorphism of the cyclotomic field `ℚ_n`, through its
action on the `n`-th roots of unity in `ℂ`; the exponent is a unit modulo
`n`, as for an automorphism of `ℚ_n`.
-/
@[expose] public def cyclotomicGaloisAction
    (n : ℕ) (τ : Gal(ℂ/ℚ)) : Prop :=
  ∃ e : ℕ, e.Coprime n ∧ ∀ z : ℂ, z ^ n = 1 → τ z = z ^ e

/--
Complex-Galois form of Peterfalvi (3.9)(b): for an irreducible character
`ω'` of `W` and the multiplicative order parameter `a`, with integer `k`
prime to `a`, the value-wise `k`-th power `ωk` is an irreducible character and
a compatible Galois automorphism of the `|G|`-cyclotomic values carries
`σ ω'` to `σ ωk`.
-/
@[expose] public def proposition_3_9_statement_b_complex_galois
    {G : Type u} [Group G] [Finite G]
    {W : Subgroup G}
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  ∀ {ω' : Section1.ClassFunction W} {a : ℕ} {k : ℤ},
    Section1.IsIrreducibleCharacterOnGroup ω' →
      exactCharacterValueOrder ω' a →
        IsCoprime k (a : ℤ) →
          ∃ ωk : Section1.ClassFunction W,
            Section1.IsIrreducibleCharacterOnGroup ωk ∧
            classFunctionValueZPow ω' ωk k ∧
              ∃ τ : Gal(ℂ/ℚ),
                cyclotomicGaloisAction (Nat.card G) τ ∧
                σ ωk = classFunctionGaloisConjugate τ (σ ω') ∧
                ∀ g : G, (orderOf g).Coprime a →
                  σ ωk g = σ ω' g

/--
Peterfalvi (3.9)(b), represented by a compatible cyclotomic Galois action on
the `|G|`-cyclotomic values.
-/
@[expose] public def proposition_3_9_statement_b
    {G : Type u} [Group G] [Finite G]
    {W : Subgroup G}
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  proposition_3_9_statement_b_complex_galois σ


/--
Auxiliary PF (3.9)(b) CRT/exponent package.  This records the PF (1.9)
cyclotomic field model, congruences for the chosen power exponent, the
compatible complex root-action used by one proof route, the complex-Galois
equality, and the finite argument-power action on the Dade image.
-/
@[expose] public def proposition_3_9_statement_b_structured
    {G : Type u} [Group G] [Finite G]
    {W : Subgroup G}
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  ∀ {ω' : Section1.ClassFunction W} {a : ℕ} {k : ℤ},
    Section1.IsIrreducibleCharacterOnGroup ω' →
      exactCharacterValueOrder ω' a →
        IsCoprime k (a : ℤ) →
          ∃ ωk : Section1.ClassFunction W,
            Section1.IsIrreducibleCharacterOnGroup ωk ∧
              classFunctionValueZPow ω' ωk k ∧
                ∃ c b : ℕ,
                  valueOrderCardPart a c ∧
                    ∃ hcard : Nat.card G = c * b,
                      c.Coprime b ∧
                        ∃ v : Gal((Section1.CyclotomicABField c b)/ℚ),
                          ∃ τ : Gal(ℂ/ℚ), ∃ e : ℕ,
                          proposition_3_9_galoisCondition_int
                            (G := G) (c := c) (b := b) (k := k) hcard v ∧
                            (∀ z : ℂ, z ^ (c * b) = 1 → τ z = z ^ e) ∧
                            e.Coprime (c * b) ∧
                            (e : ℤ) ≡ k [ZMOD c] ∧
                            (e : ℤ) ≡ (1 : ℤ) [ZMOD b] ∧
                            σ ωk = classFunctionGaloisConjugate τ (σ ω') ∧
                            classFunctionArgumentPow (σ ω') (σ ωk) e ∧
                            ∀ g : G, (orderOf g).Coprime a →
                              σ ωk g = σ ω' g

/-- The structured PF (3.9)(b) package implies the complex-Galois endpoint. -/
public theorem proposition_3_9_statement_b_of_structured
    {G : Type u} [Group G] [Finite G]
    {W : Subgroup G}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    (hstructured : proposition_3_9_statement_b_structured σ) :
    proposition_3_9_statement_b_complex_galois σ := by
  intro ω' a k hω' ha hk
  rcases hstructured (ω' := ω') (a := a) (k := k) hω' ha hk with
    ⟨ωk, hωk, hpow, c, b, _hcpart, hcard, _hcb, _v, τ, e,
      _hgal, hτroot, hecop, _hea, _heb, hσ, _harg, hpoint⟩
  have hcardF : Fintype.card G = c * b := by
    simpa [Nat.card_eq_fintype_card] using hcard
  have hτ : cyclotomicGaloisAction (Nat.card G) τ := by
    refine ⟨e, ?_, ?_⟩
    · simpa [Nat.card_eq_fintype_card, hcardF] using hecop
    · intro z hz
      exact hτroot z (by simpa [Nat.card_eq_fintype_card, hcardF] using hz)
  exact ⟨ωk, hωk, hpow, τ, hτ, hσ, hpoint⟩


/--
Peterfalvi (3.9)(c), isolated as its Lean-side endpoint: if `ω'` is
irreducible on `W`, `a` is the exact common value-order for `ω'`, and `g` has order
coprime to `a`, then the value `σ ω' g` is an ordinary integer.
-/
@[expose] public def proposition_3_9_statement_c
    {G : Type u} [Group G] [Finite G]
    {W : Subgroup G}
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  ∀ {ω' : Section1.ClassFunction W} {a : ℕ},
    Section1.IsIrreducibleCharacterOnGroup ω' →
      exactCharacterValueOrder ω' a →
        ∀ g : G, (orderOf g).Coprime a →
          ∃ n : ℤ, σ ω' g = (n : ℂ)


/--
Peterfalvi (3.9)(a), second sentence, represented by a compatible cyclotomic
Galois action on the `|G|`-cyclotomic values: the Dade isometry commutes with
Galois conjugation on irreducible characters of `W`.
-/
@[expose] public def proposition_3_9_statement_a_galois
    {G : Type u} [Group G] [Finite G]
    {W : Subgroup G}
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  ∀ {ω' : Section1.ClassFunction W} (τ : Gal(ℂ/ℚ)),
    Section1.IsIrreducibleCharacterOnGroup ω' →
      cyclotomicGaloisAction (Nat.card G) τ →
        classFunctionGaloisConjugate τ (σ ω') =
          σ (classFunctionGaloisConjugate τ ω')


/--
Peterfalvi (3.9).  The automorphisms of `ℚ_|G|` are represented by compatible
cyclotomic Galois actions on the `|G|`-cyclotomic values.  Clause `(c)` is the
integer-value conclusion.
-/
@[expose] public def proposition_3_9_statement
    {G : Type u} [Group G] [Finite G]
    (W1 W2 W : Subgroup G)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (_h : hypothesis_3_1_statement W1 W2 W)
    (_hσ : theorem_3_2_map_statement W1 W2 W σ) : Prop :=
  (∀ {ω' : Section1.ClassFunction W},
      Section1.IsIrreducibleCharacterOnGroup ω' →
        ∀ {X : Section1.ClassFunction G},
          IsSignedIrreducibleCharacter X →
            (∀ x : G, ∀ hx : x ∈ cyclicTISet W1 W2 W,
              X x = ω' ⟨x, cyclicTISet_subset W1 W2 W hx⟩) →
            X = σ ω') ∧
  proposition_3_9_statement_a_galois σ ∧
  proposition_3_9_statement_b σ ∧
  proposition_3_9_statement_c σ


private noncomputable def uliftRepresentation_pf39
    {G : Type u} [Group G] {V : Type v}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) :
    Representation ℂ G (ULift.{u} V) := by
  let e : V ≃ₗ[ℂ] ULift.{u} V := ULift.moduleEquiv.symm
  refine
    { toFun := fun g => e.conj (ρ g)
      map_one' := by
        ext x
        simp [LinearEquiv.conj_apply]
      map_mul' := by
        intro g h
        ext x
        simp [LinearEquiv.conj_apply, map_mul] }

private theorem uliftRepresentation_pf39_character
    {G : Type u} [Group G] {V : Type v}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g : G) :
    (uliftRepresentation_pf39 (G := G) (V := V) ρ).character g = ρ.character g := by
  dsimp [uliftRepresentation_pf39, Representation.character]
  exact LinearMap.trace_conj' (R := ℂ) (M := V)
    (N := ULift.{u} V) (ρ g) (ULift.moduleEquiv.symm)

private theorem isBookIrreducibleCharacter_of_group_irreducible_pf39
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    Section1.IsBookIrreducibleCharacter χ := by
  rcases hχ with ⟨n, ρ, hirr, hchar⟩
  constructor
  · refine ⟨ULift.{u} (Fin n → ℂ), inferInstance, inferInstance, inferInstance,
      uliftRepresentation_pf39 (G := G) (V := Fin n → ℂ) ρ, ?_⟩
    ext g
    simpa [hchar] using
      (uliftRepresentation_pf39_character (G := G) (V := Fin n → ℂ) (ρ := ρ) g).symm
  · rw [Section1.IsIrreducibleCharacter]
    have hρclass : Section1.IsClassFunction ρ.character := by
      intro x g
      simpa [mul_assoc] using Representation.char_conj (ρ := ρ) g x
    have htoeq :
        Section1.toConjClassFunction ρ.character hρclass =
          Theory.Character.characterClassFunction ρ := by
      apply Section1.toConjClassFunction_eq_of_apply
      intro g
      rfl
    calc
      Section1.scalarProduct G χ χ =
          Section1.scalarProduct G ρ.character ρ.character := by rw [hchar]
      _ = Theory.Character.classFunctionInner
          (Section1.toConjClassFunction ρ.character hρclass)
          (Section1.toConjClassFunction ρ.character hρclass) :=
        (Section1.classFunctionInner_toConjClassFunction
          ρ.character ρ.character hρclass hρclass).symm
      _ = Theory.Character.classFunctionInner
          (Theory.Character.characterClassFunction ρ)
          (Theory.Character.characterClassFunction ρ) := by rw [htoeq]
      _ = 1 :=
        (Theory.Character.irreducible_iff_character_norm_one (ρ := ρ)).1 hirr

private theorem scalarProduct_signed_irreducible_ne_zero_iff_pf39
    {G : Type u} [Group G] [Finite G]
    {χ ψ : Section1.ClassFunction G}
    (hχ : IsSignedIrreducibleCharacter χ)
    (hψ : Section1.IsIrreducibleCharacterOnGroup ψ) :
    Section1.scalarProduct G χ ψ ≠ 0 ↔
      ∃ ε : ℂ, Section1.IsSign ε ∧ χ = ε • ψ := by
  rcases hχ with ⟨ε, hε, μ, hμ, rfl⟩
  have hμ_book := isBookIrreducibleCharacter_of_group_irreducible_pf39 hμ
  have hψ_book := isBookIrreducibleCharacter_of_group_irreducible_pf39 hψ
  constructor
  · intro hsp
    by_cases hμψ : μ = ψ
    · exact ⟨ε, hε, by simp [hμψ]⟩
    · have hzeroμ : Section1.scalarProduct G μ ψ = 0 := by
        exact Section1.scalarProduct_isBookIrreducible_ne μ ψ hμ_book hψ_book hμψ
      have hzero :
          Section1.scalarProduct G (ε • μ) ψ = 0 := by
        rw [Section1.scalarProduct_smul_left, hzeroμ]
        simp
      exact (hsp hzero).elim
  · rintro ⟨ε', hε', hEq⟩
    rcases hε' with rfl | rfl
    · have hself : Section1.scalarProduct G ψ ψ = (1 : ℂ) := by
        simpa [Section1.IsIrreducibleCharacter] using
          (isBookIrreducibleCharacter_of_group_irreducible_pf39 hψ).2
      have hneq_zero : (ε : ℂ) ≠ 0 := by
        rcases hε with rfl | rfl <;> norm_num
      rw [hEq, Section1.scalarProduct_smul_left, hself]
      norm_num
    · have hself : Section1.scalarProduct G ψ ψ = (1 : ℂ) := by
        simpa [Section1.IsIrreducibleCharacter] using
          (isBookIrreducibleCharacter_of_group_irreducible_pf39 hψ).2
      have hneq_zero : (-1 : ℂ) ≠ 0 := by norm_num
      rw [hEq, Section1.scalarProduct_smul_left, hself]
      exact mul_ne_zero hneq_zero one_ne_zero


private theorem irreducible_representation_witness_pf39
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    ∃ n : ℕ, ∃ ρ : Representation ℂ G (Fin n → ℂ),
      Representation.IsIrreducible ρ ∧ χ = ρ.character := by
  rcases hχ with ⟨n, ρ, hirr, hchar⟩
  exact ⟨n, ρ, hirr, hchar⟩

private theorem signed_irreducible_representation_witness_pf39
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : IsSignedIrreducibleCharacter χ) :
    ∃ ε : ℂ, Section1.IsSign ε ∧
      ∃ n : ℕ, ∃ ρ : Representation ℂ G (Fin n → ℂ),
        Representation.IsIrreducible ρ ∧ χ = ε • ρ.character := by
  rcases hχ with ⟨ε, hε, μ, hμ, rfl⟩
  rcases irreducible_representation_witness_pf39 hμ with ⟨n, ρ, hirr, hchar⟩
  exact ⟨ε, hε, n, ρ, hirr, by simp [hchar]⟩

private theorem isaacs_lemma_3_2_core_pf39
    {z : ℂ} (hzint : IsIntegral ℤ z) (hzrat : ∃ q : ℚ, z = (q : ℂ)) :
    ∃ n : ℤ, z = (n : ℂ) := by
  exact Theory.Character.isaacs_lemma_3_2_core hzint hzrat

private theorem isIntegral_value_of_signed_irreducible_pf39
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : IsSignedIrreducibleCharacter χ) (g : G) :
    IsIntegral ℤ (χ g) := by
  rcases signed_irreducible_representation_witness_pf39 hχ with
    ⟨ε, hε, n, ρ, _hirr, hchar⟩
  rcases hε with rfl | rfl
  · simpa [hchar] using Theory.Character.representation_character_isIntegral (ρ := ρ) g
  · simpa [hchar] using
      (Theory.Character.representation_character_isIntegral (ρ := ρ) g).neg

private theorem exists_int_of_signed_irreducible_value_rat_pf39
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : IsSignedIrreducibleCharacter χ) {g : G}
    (hrat : ∃ q : ℚ, χ g = (q : ℂ)) :
    ∃ n : ℤ, χ g = (n : ℂ) := by
  exact isaacs_lemma_3_2_core_pf39
    (isIntegral_value_of_signed_irreducible_pf39 hχ g) hrat


private theorem signed_irreducible_value_eq_on_coprime_zpow_pf39
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : IsSignedIrreducibleCharacter χ)
    {a b e : ℕ} {k : ℤ} (hcard : Nat.card G = a * b)
    (hea : (e : ℤ) ≡ k [ZMOD a]) (heb : (e : ℤ) ≡ (1 : ℤ) [ZMOD b])
    (g : G) (hg : (orderOf g).Coprime a) :
    χ (g ^ e) = χ g := by
  rcases signed_irreducible_representation_witness_pf39 hχ with
    ⟨ε, hε, n, ρ, _hirr, hchar⟩
  have hpow := (Section1.proposition_1_9_b_trace_zpow
      (G := G) (V := Fin n → ℂ) (a := a) (b := b) (k := k) (e := e)
      hcard hea heb ρ).2 g hg
  rcases hε with rfl | rfl
  · simpa [hchar, Section1.characterGaloisConjugateByExponent] using hpow
  · simpa [hchar, Section1.characterGaloisConjugateByExponent] using
      congrArg (fun z : ℂ => (-1 : ℂ) * z) hpow


private theorem coprime_of_valueOrderCardPart_pf39
    {a c n : ℕ} (hpart : valueOrderCardPart a c)
    (hn : n.Coprime a) :
    n.Coprime c := by
  by_contra hnc
  rcases Nat.Prime.not_coprime_iff_dvd.mp hnc with ⟨p, hp, hpn, hpc⟩
  have hpa : p ∣ a := (hpart.2 p hp).1 hpc
  exact (Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp, hpn, hpa⟩) hn

private theorem natAbs_coprime_of_int_isCoprime_pf39
    {k : ℤ} {a : ℕ} (hk : IsCoprime k (a : ℤ)) :
    k.natAbs.Coprime a := by
  rw [Nat.coprime_iff_gcd_eq_one]
  have hg : k.gcd (a : ℤ) = 1 := Int.isCoprime_iff_gcd_eq_one.mp hk
  rw [Int.gcd_eq_natAbs] at hg
  simpa using hg

private theorem int_isCoprime_of_natAbs_coprime_pf39
    {k : ℤ} {c : ℕ} (hkc : k.natAbs.Coprime c) :
    IsCoprime k (c : ℤ) := by
  rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_eq_natAbs]
  simpa using (Nat.Coprime.gcd_eq_one hkc)

private theorem exists_valueOrderCardPart_factorization_pf39
    {a n : ℕ} (ha0 : 0 < a) (han : a ∣ n) (hn0 : n ≠ 0) :
    ∃ c b : ℕ, valueOrderCardPart a c ∧ n = c * b ∧ c.Coprime b := by
  classical
  let fA : ℕ →₀ ℕ := n.factorization.filter (fun p => p ∣ a)
  let fB : ℕ →₀ ℕ := n.factorization.filter (fun p => ¬ p ∣ a)
  let c : ℕ := fA.prod (fun p e => p ^ e)
  let b : ℕ := fB.prod (fun p e => p ^ e)
  have hfA_le : fA ≤ n.factorization := by
    intro p
    by_cases hp : p ∣ a <;> simp [fA, hp]
  have hfB_le : fB ≤ n.factorization := by
    intro p
    by_cases hp : p ∣ a <;> simp [fB, hp]
  have hc_factor : c.factorization = fA := by
    simpa [c] using Nat.factorization_prod_pow_eq_self_of_le_factorization hfA_le
  have hb_factor : b.factorization = fB := by
    simpa [b] using Nat.factorization_prod_pow_eq_self_of_le_factorization hfB_le
  have hcb : c * b = n := by
    calc
      c * b = n.factorization.prod (fun p e => p ^ e) := by
        simp [c, b, fA, fB, Finsupp.prod_filter_mul_prod_filter_not]
      _ = n := Nat.prod_factorization_pow_eq_self hn0
  have hc0 : c ≠ 0 := by
    intro hc
    apply hn0
    rw [← hcb, hc]
    simp
  have hb0 : b ≠ 0 := by
    intro hb
    apply hn0
    rw [← hcb, hb]
    simp
  have ha_ne : a ≠ 0 := Nat.ne_of_gt ha0
  have ha_fac_le_n : a.factorization ≤ n.factorization :=
    (Nat.factorization_le_iff_dvd ha_ne hn0).2 han
  have ha_fac_le_c : a.factorization ≤ c.factorization := by
    rw [hc_factor]
    intro p
    by_cases hpa : p ∣ a
    · simpa [fA, hpa] using ha_fac_le_n p
    · have hazero : a.factorization p = 0 := by
        by_cases hpprime : p.Prime
        · by_contra hnonzero
          have hone : 1 ≤ a.factorization p := Nat.pos_of_ne_zero hnonzero
          exact hpa ((Nat.Prime.dvd_iff_one_le_factorization hpprime ha_ne).2 hone)
        · exact Nat.factorization_eq_zero_of_not_prime a hpprime
      simp [fA, hpa, hazero]
  have ha_dvd_c : a ∣ c := (Nat.factorization_le_iff_dvd ha_ne hc0).1 ha_fac_le_c
  have hprime_c_iff : ∀ p : ℕ, p.Prime → (p ∣ c ↔ p ∣ a) := by
    intro p hp
    constructor
    · intro hpc
      have hone : 1 ≤ c.factorization p :=
        (Nat.Prime.dvd_iff_one_le_factorization hp hc0).1 hpc
      by_contra hpa
      have hfzero : fA p = 0 := by
        simp [fA, hpa]
      rw [hc_factor, hfzero] at hone
      omega
    · intro hpa
      exact dvd_trans hpa ha_dvd_c
  have hcop : c.Coprime b := by
    by_contra hnot
    rcases Nat.Prime.not_coprime_iff_dvd.mp hnot with ⟨p, hp, hpc, hpb⟩
    have hpa : p ∣ a := (hprime_c_iff p hp).1 hpc
    have hone : 1 ≤ b.factorization p :=
      (Nat.Prime.dvd_iff_one_le_factorization hp hb0).1 hpb
    have hfzero : fB p = 0 := by
      simp [fB, hpa]
    rw [hb_factor, hfzero] at hone
    omega
  exact ⟨c, b, ⟨ha_dvd_c, hprime_c_iff⟩, hcb.symm, hcop⟩

private theorem smul_one_pow_end_pf39
    {n N : ℕ} (c : ℂ) :
    ((c • (1 : Module.End ℂ (Fin n → ℂ))) ^ N) =
      (c ^ N) • (1 : Module.End ℂ (Fin n → ℂ)) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [pow_succ, ih, pow_succ]
      ext v i
      simp [mul_smul]
      ring

private theorem characterValueOrder_natCard_of_irreducible_comm_pf39
    {H : Type*} [CommGroup H] [Finite H]
    {χ : Section1.ClassFunction H}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    characterValueOrder χ (Nat.card H) := by
  constructor
  · exact Nat.card_pos
  · intro g
    rcases hχ with ⟨n, ρ, hirr, hχeq⟩
    haveI : IsMulCommutative H := ⟨⟨mul_comm⟩⟩
    haveI : Representation.IsIrreducible ρ := hirr
    have hdim : Module.finrank ℂ (Fin n → ℂ) = 1 := by
      exact Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative (ρ := ρ)
    obtain ⟨c, hc, _hcuniq⟩ :=
      LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdim (ρ g)
    have hχc : χ g = c := by
      rw [hχeq, Representation.character, hc]
      simp [hdim]
    have hpow : (ρ g) ^ Nat.card H = 1 := by
      rw [← MonoidHom.map_pow, pow_card_eq_one', MonoidHom.map_one]
    have hsmul :
        (c ^ Nat.card H) • (1 : Module.End ℂ (Fin n → ℂ)) =
          (1 : Module.End ℂ (Fin n → ℂ)) := by
      calc
        (c ^ Nat.card H) • (1 : Module.End ℂ (Fin n → ℂ)) =
            ((c • (1 : Module.End ℂ (Fin n → ℂ))) ^ Nat.card H) := by
              rw [smul_one_pow_end_pf39]
        _ = (ρ g) ^ Nat.card H := by
              rw [hc]
              rfl
        _ = 1 := hpow
    have htrace := congrArg (LinearMap.trace ℂ (Fin n → ℂ)) hsmul
    have hcpow : c ^ Nat.card H = 1 := by
      simpa [hdim] using htrace
    simpa [hχc] using hcpow

private theorem exactCharacterValueOrder_dvd_natCard_of_pf39
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    (h : hypothesis_3_1_statement W1 W2 W)
    {ω' : Section1.ClassFunction W} {a : ℕ}
    (hω' : Section1.IsIrreducibleCharacterOnGroup ω')
    (ha : exactCharacterValueOrder ω' a) :
    a ∣ Nat.card G := by
  rcases h with ⟨_hW1, _hW2, _hIP, hcyc, _hodd, _hcard1, _hcard2, _hTI⟩
  letI : IsCyclic W := hcyc
  letI : CommGroup W := IsCyclic.commGroup
  have horderW : characterValueOrder ω' (Nat.card W) :=
    characterValueOrder_natCard_of_irreducible_comm_pf39 hω'
  exact dvd_trans (ha.2 (Nat.card W) horderW) (Subgroup.card_subgroup_dvd_card W)

private theorem irreducibleCharacterOnGroup_value_pow_eq_argument_pow_comm_pf39
    {H : Type*} [CommGroup H] [Finite H]
    {χ : Section1.ClassFunction H}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ)
    (g : H) (e : ℕ) :
    χ (g ^ e) = χ g ^ e := by
  rcases hχ with ⟨n, ρ, hirr, hχeq⟩
  haveI : IsMulCommutative H := ⟨⟨mul_comm⟩⟩
  haveI : Representation.IsIrreducible ρ := hirr
  have hdim : Module.finrank ℂ (Fin n → ℂ) = 1 := by
    exact Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative (ρ := ρ)
  obtain ⟨c, hc, _hcuniq⟩ :=
    LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdim (ρ g)
  have hχc : χ g = c := by
    rw [hχeq, Representation.character, hc]
    simp [hdim]
  have hρge : ρ (g ^ e) = (c ^ e) • (1 : Module.End ℂ (Fin n → ℂ)) := by
    calc
      ρ (g ^ e) = (ρ g) ^ e := by rw [MonoidHom.map_pow]
      _ = (c • (1 : Module.End ℂ (Fin n → ℂ))) ^ e := by
            rw [hc]
            rfl
      _ = (c ^ e) • (1 : Module.End ℂ (Fin n → ℂ)) := smul_one_pow_end_pf39 c
  calc
    χ (g ^ e) = LinearMap.trace ℂ (Fin n → ℂ) (ρ (g ^ e)) := by
      rw [hχeq, Representation.character]
    _ = c ^ e := by
      rw [hρge]
      simp [hdim]
    _ = χ g ^ e := by rw [hχc]

private theorem classFunctionValueZPow_of_argumentPow_congr_pf39
    {H : Type*} [CommGroup H] [Finite H]
    {χ χe : Section1.ClassFunction H}
    {a c e : ℕ} {k : ℤ}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ)
    (ha : exactCharacterValueOrder χ a)
    (hcpart : valueOrderCardPart a c)
    (hea : (e : ℤ) ≡ k [ZMOD c])
    (harg : classFunctionArgumentPow χ χe e) :
    classFunctionValueZPow χ χe k := by
  intro g
  have ha0 : 0 < a := ha.1.1
  have hroot : χ g ^ a = 1 := ha.1.2 g
  have hzg_ne : χ g ≠ 0 := by
    intro hzero
    rw [hzero] at hroot
    simp [ha0.ne'] at hroot
  let u : ℂˣ := Units.mk0 (χ g) hzg_ne
  have horder_dvd_a : orderOf u ∣ a := by
    apply orderOf_dvd_of_pow_eq_one
    ext
    simpa [u] using hroot
  have hmoda : (e : ℤ) ≡ k [ZMOD a] := by
    have hdvd : (a : ℤ) ∣ (c : ℤ) := by exact_mod_cast hcpart.1
    exact Int.ModEq.of_dvd hdvd hea
  have hmod_order : (e : ℤ) ≡ k [ZMOD orderOf u] := by
    have hdvd : (orderOf u : ℤ) ∣ (a : ℤ) := by exact_mod_cast horder_dvd_a
    exact Int.ModEq.of_dvd hdvd hmoda
  have hzpow : (χ g) ^ (e : ℤ) = (χ g) ^ k := by
    have hu : u ^ (e : ℤ) = u ^ k := by
      rw [zpow_eq_zpow_iff_modEq]
      exact hmod_order
    simpa [u] using congrArg (fun x : ℂˣ => (x : ℂ)) hu
  calc
    χe g = χ (g ^ e) := harg g
    _ = χ g ^ e := irreducibleCharacterOnGroup_value_pow_eq_argument_pow_comm_pf39 hχ g e
    _ = χ g ^ (e : ℤ) := by rw [zpow_natCast]
    _ = χ g ^ k := hzpow


private theorem pow_surjective_of_coprime_natCard_pf39
    {G : Type u} [Group G] [Finite G] {e : ℕ}
    (he : e.Coprime (Nat.card G)) :
    Function.Surjective (fun g : G => g ^ e) := by
  intro g
  have hcop_order : e.Coprime (orderOf g) :=
    Nat.Coprime.of_dvd_right (orderOf_dvd_natCard g) he
  by_cases h1 : orderOf g = 1
  · refine ⟨1, ?_⟩
    simp [orderOf_eq_one_iff.mp h1]
  have hlt : 1 < orderOf g := by
    exact lt_of_le_of_ne (Nat.succ_le_of_lt (orderOf_pos g)) (Ne.symm h1)
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop_order hlt
  refine ⟨g ^ m, ?_⟩
  change (g ^ m) ^ e = g
  rw [← pow_mul, Nat.mul_comm, ← pow_mod_orderOf, hm, pow_one]

private theorem pow_bijective_of_coprime_natCard_pf39
    {G : Type u} [Group G] [Finite G] {e : ℕ}
    (he : e.Coprime (Nat.card G)) :
    Function.Bijective (fun g : G => g ^ e) := by
  have hsurj : Function.Surjective (fun g : G => g ^ e) :=
    pow_surjective_of_coprime_natCard_pf39 he
  refine ⟨?_, hsurj⟩
  rw [Finite.injective_iff_surjective]
  exact hsurj

private noncomputable def powMulEquivOfCoprime_natCard_pf39
    {H : Type*} [CommGroup H] [Finite H] (e : ℕ)
    (he : e.Coprime (Nat.card H)) : H ≃* H := by
  let powHom : H →* H :=
    { toFun := fun h => h ^ e
      map_one' := by simp
      map_mul' := by
        intro a b
        simpa [mul_comm, mul_left_comm, mul_assoc] using mul_pow a b e }
  exact MulEquiv.ofBijective powHom
    (pow_bijective_of_coprime_natCard_pf39 (G := H) he)

private noncomputable def subrepresentationOrderIso_compMulEquiv_pf39
    {H W : Type*} [Group H] [AddCommGroup W] [Module ℂ W]
    (rho : Representation ℂ H W) (e : H ≃* H) :
    Subrepresentation rho ≃o Subrepresentation (rho.comp e.toMonoidHom) where
  toFun S :=
    { toSubmodule := S.toSubmodule
      apply_mem_toSubmodule := by
        intro h v hv
        exact S.apply_mem_toSubmodule (e h) hv }
  invFun T :=
    { toSubmodule := T.toSubmodule
      apply_mem_toSubmodule := by
        intro h v hv
        have hmem := T.apply_mem_toSubmodule (e.symm h) hv
        simpa using hmem }
  left_inv S := by
    apply Subrepresentation.toSubmodule_injective
    rfl
  right_inv T := by
    apply Subrepresentation.toSubmodule_injective
    rfl
  map_rel_iff' := by
    intro S T
    rfl

private theorem irreducible_compMulEquiv_pf39
    {H W : Type*} [Group H] [AddCommGroup W] [Module ℂ W]
    (rho : Representation ℂ H W) (e : H ≃* H)
    [Representation.IsIrreducible rho] :
    Representation.IsIrreducible (rho.comp e.toMonoidHom) := by
  exact (OrderIso.isSimpleOrder_iff
    (subrepresentationOrderIso_compMulEquiv_pf39 rho e)).mp inferInstance

private theorem irreducibleCharacterOnGroup_argumentPow_of_coprime_natCard_comm_pf39
    {H : Type*} [CommGroup H] [Finite H]
    {χ : Section1.ClassFunction H}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ)
    {e : ℕ} (he : e.Coprime (Nat.card H)) :
    Section1.IsIrreducibleCharacterOnGroup (fun h : H => χ (h ^ e)) := by
  rcases hχ with ⟨n, ρ, hirr, hchar⟩
  let powEquiv : H ≃* H := powMulEquivOfCoprime_natCard_pf39 (H := H) e he
  haveI : Representation.IsIrreducible ρ := hirr
  refine ⟨n, ρ.comp powEquiv.toMonoidHom, irreducible_compMulEquiv_pf39 ρ powEquiv, ?_⟩
  ext h
  rw [hchar]
  rfl


private theorem scalarProduct_argumentPow_eq_of_coprime_natCard_pf39
    {G : Type u} [Group G] [Finite G]
    {φ ψ : Section1.ClassFunction G} {e : ℕ}
    (he : e.Coprime (Nat.card G)) :
    Section1.scalarProduct G (fun g : G => φ (g ^ e)) (fun g : G => ψ (g ^ e)) =
      Section1.scalarProduct G φ ψ := by
  classical
  let pe : G ≃ G :=
    Equiv.ofBijective (fun g : G => g ^ e)
      (pow_bijective_of_coprime_natCard_pf39 (G := G) he)
  have hsum :
      ∑ g : G, φ (g ^ e) * star (ψ (g ^ e)) =
        ∑ g : G, φ g * star (ψ g) := by
    simpa [pe] using
      (Equiv.sum_comp pe (fun g : G => φ g * star (ψ g)))
  unfold Section1.scalarProduct
  rw [hsum]

private noncomputable def matrixMapRepresentation_pf39
    {G : Type u} [Group G] (τ : ℂ ≃+* ℂ)
    {n : ℕ} (ρ : Representation ℂ G (Fin n → ℂ)) :
    Representation ℂ G (Fin n → ℂ) := by
  refine
    { toFun := fun g =>
        Matrix.toLin' ((LinearMap.toMatrix' (ρ g)).map τ.toRingHom)
      map_one' := ?_
      map_mul' := ?_ }
  · apply LinearMap.toMatrix'.injective
    simp [LinearMap.toMatrix'_one]
  · intro g h
    have hmat :
        ((LinearMap.toMatrix' (ρ (g * h))).map τ.toRingHom) =
          ((LinearMap.toMatrix' (ρ g)).map τ.toRingHom) *
            ((LinearMap.toMatrix' (ρ h)).map τ.toRingHom) := by
      simp [LinearMap.toMatrix'_mul, map_mul]
    calc
      Matrix.toLin' ((LinearMap.toMatrix' (ρ (g * h))).map τ.toRingHom)
          = Matrix.toLin'
              (((LinearMap.toMatrix' (ρ g)).map τ.toRingHom) *
                ((LinearMap.toMatrix' (ρ h)).map τ.toRingHom)) := by
              rw [hmat]
      _ = Matrix.toLin' ((LinearMap.toMatrix' (ρ g)).map τ.toRingHom) ∘ₗ
            Matrix.toLin' ((LinearMap.toMatrix' (ρ h)).map τ.toRingHom) := by
              rw [Matrix.toLin'_mul]
      _ = Matrix.toLin' ((LinearMap.toMatrix' (ρ g)).map τ.toRingHom) *
            Matrix.toLin' ((LinearMap.toMatrix' (ρ h)).map τ.toRingHom) := by
              rw [Module.End.mul_eq_comp]

private theorem matrixMapRepresentation_pf39_character
    {G : Type u} [Group G] (τ : ℂ ≃+* ℂ)
    {n : ℕ} (ρ : Representation ℂ G (Fin n → ℂ)) (g : G) :
    (matrixMapRepresentation_pf39 (G := G) τ ρ).character g = τ (ρ.character g) := by
  unfold matrixMapRepresentation_pf39
  change
    LinearMap.trace ℂ (Fin n → ℂ)
        (Matrix.toLin' ((LinearMap.toMatrix' (ρ g)).map τ.toRingHom)) =
      τ (ρ.character g)
  calc
    LinearMap.trace ℂ (Fin n → ℂ)
        (Matrix.toLin' ((LinearMap.toMatrix' (ρ g)).map τ.toRingHom))
        = τ ((LinearMap.toMatrix' (ρ g)).trace) := by
            rw [Matrix.trace_toLin'_eq]
            simp [Matrix.trace]
    _ = τ (LinearMap.trace ℂ (Fin n → ℂ) (ρ g)) := by
          congr 1
          exact (LinearMap.trace_eq_matrix_trace ℂ
            (Pi.basisFun ℂ (Fin n)) (ρ g)).symm
    _ = τ (ρ.character g) := by
          rw [Representation.character]

private theorem irreducibleCharacterOnGroup_argumentPow_of_ringEquiv_pf39
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ)
    {e : ℕ} (he : e.Coprime (Nat.card G))
    (τ : ℂ ≃+* ℂ)
    (hτ : ∀ g : G, τ (χ g) = χ (g ^ e)) :
    Section1.IsIrreducibleCharacterOnGroup (fun g : G => χ (g ^ e)) := by
  have hχ_book := isBookIrreducibleCharacter_of_group_irreducible_pf39 hχ
  rcases hχ with ⟨n, ρ, _hirr, hchar⟩
  let ρτ : Representation ℂ G (Fin n → ℂ) := matrixMapRepresentation_pf39 τ ρ
  have hcharτ : ∀ g : G, ρτ.character g = χ (g ^ e) := by
    intro g
    have hτρ : τ (ρ.character g) = ρ.character (g ^ e) := by
      simpa [hchar] using hτ g
    calc
      ρτ.character g = τ (ρ.character g) := by
        simpa [ρτ] using matrixMapRepresentation_pf39_character (G := G) τ ρ g
      _ = ρ.character (g ^ e) := hτρ
      _ = χ (g ^ e) := by rw [hchar]
  have hnorm :
      Section1.scalarProduct G (fun g : G => χ (g ^ e)) (fun g : G => χ (g ^ e)) = 1 := by
    calc
      Section1.scalarProduct G (fun g : G => χ (g ^ e)) (fun g : G => χ (g ^ e)) =
        Section1.scalarProduct G χ χ :=
          scalarProduct_argumentPow_eq_of_coprime_natCard_pf39
            (G := G) (φ := χ) (ψ := χ) (e := e) he
      _ = 1 := by
          simpa [Section1.IsIrreducibleCharacter] using
            hχ_book.2
  have hcfτ : Section1.IsClassFunction ρτ.character := by
    intro x g
    simpa [mul_assoc] using Representation.char_conj (ρ := ρτ) g x
  have hinnerτ :
      Theory.Character.classFunctionInner (Theory.Character.characterClassFunction ρτ) (Theory.Character.characterClassFunction ρτ) =
        Section1.scalarProduct G (fun g : G => χ (g ^ e)) (fun g : G => χ (g ^ e)) := by
    calc
      Theory.Character.classFunctionInner (Theory.Character.characterClassFunction ρτ) (Theory.Character.characterClassFunction ρτ) =
          Section1.scalarProduct G ρτ.character ρτ.character := by
            change Theory.Character.classFunctionInner
                (Section1.toConjClassFunction ρτ.character hcfτ)
                (Section1.toConjClassFunction ρτ.character hcfτ) =
              Section1.scalarProduct G ρτ.character ρτ.character
            exact Section1.classFunctionInner_toConjClassFunction
              ρτ.character ρτ.character hcfτ hcfτ
      _ = Section1.scalarProduct G (fun g : G => χ (g ^ e)) (fun g : G => χ (g ^ e)) := by
            congr 1 <;> ext g <;> exact hcharτ g
  have hirrτ : Representation.IsIrreducible ρτ := by
    apply (Theory.Character.irreducible_iff_character_norm_one (ρ := ρτ)).2
    rw [hinnerτ]
    exact hnorm
  exact ⟨n, ρτ, hirrτ, (funext hcharτ).symm⟩

public theorem irreducibleCharacterOnGroup_galoisConjugate_of_cyclotomicAction_pf39
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G} (τ : Gal(ℂ/ℚ))
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ)
    (hτ : cyclotomicGaloisAction (Nat.card G) τ) :
    Section1.IsIrreducibleCharacterOnGroup (classFunctionGaloisConjugate τ χ) := by
  rcases hτ with ⟨e, he, hτroot⟩
  rcases hχ with ⟨n, ρ, hirr, hχeq⟩
  have hτχ : ∀ g : G, τ (χ g) = χ (g ^ e) := by
    intro g
    have hchar :=
      Section1.representation_character_apply_galois_eq_argumentPow
        (G := G) (V := Fin n → ℂ) (N := Nat.card G) (e := e)
        (τ := τ) hτroot ρ (dvd_refl (Nat.card G)) g
    simpa [hχeq, Section1.characterGaloisConjugateByAutomorphism] using hchar
  have hpow :
      Section1.IsIrreducibleCharacterOnGroup (fun g : G => χ (g ^ e)) := by
    exact irreducibleCharacterOnGroup_argumentPow_of_ringEquiv_pf39
      (G := G) (χ := χ) ⟨n, ρ, hirr, hχeq⟩ he τ.toRingEquiv
      (by
        intro g
        exact hτχ g)
  have hEq : classFunctionGaloisConjugate τ χ = fun g : G => χ (g ^ e) := by
    ext g
    exact hτχ g
  simpa [hEq] using hpow

public theorem cyclotomicGaloisAction_subgroup_pf39
    {G : Type u} [Group G] [Finite G] (W : Subgroup G)
    {τ : Gal(ℂ/ℚ)}
    (hτ : cyclotomicGaloisAction (Nat.card G) τ) :
    cyclotomicGaloisAction (Nat.card W) τ := by
  rcases hτ with ⟨e, he, hτroot⟩
  refine ⟨e, ?_, ?_⟩
  · exact Nat.Coprime.of_dvd_right (Subgroup.card_subgroup_dvd_card W) he
  · intro z hz
    exact hτroot z (by
      rcases Subgroup.card_subgroup_dvd_card W with ⟨m, hm⟩
      rw [hm, pow_mul, hz, one_pow])

private theorem signedIrreducibleCharacter_galoisConjugate_of_cyclotomicAction_pf39
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G} (τ : Gal(ℂ/ℚ))
    (hχ : IsSignedIrreducibleCharacter χ)
    (hτ : cyclotomicGaloisAction (Nat.card G) τ) :
    IsSignedIrreducibleCharacter (classFunctionGaloisConjugate τ χ) := by
  rcases hχ with ⟨ε, hε, μ, hμ, rfl⟩
  rcases hε with rfl | rfl
  · refine ⟨1, Or.inl rfl, classFunctionGaloisConjugate τ μ, ?_, ?_⟩
    · exact irreducibleCharacterOnGroup_galoisConjugate_of_cyclotomicAction_pf39
        (G := G) (χ := μ) τ hμ hτ
    · ext g
      simp [classFunctionGaloisConjugate]
  · refine ⟨-1, Or.inr rfl, classFunctionGaloisConjugate τ μ, ?_, ?_⟩
    · exact irreducibleCharacterOnGroup_galoisConjugate_of_cyclotomicAction_pf39
        (G := G) (χ := μ) τ hμ hτ
    · ext g
      simp [classFunctionGaloisConjugate]

private theorem classFunctionArgumentPow_galoisConjugate_of_rootAction_pf39
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G} (τ : Gal(ℂ/ℚ))
    (hχ : IsSignedIrreducibleCharacter χ)
    {N e : ℕ}
    (hdiv : Nat.card G ∣ N)
    (hτroot : ∀ z : ℂ, z ^ N = 1 → τ z = z ^ e) :
    classFunctionArgumentPow χ (classFunctionGaloisConjugate τ χ) e := by
  intro g
  rcases hχ with ⟨ε, hε, μ, hμ, rfl⟩
  rcases hμ with ⟨n, ρ, _hirr, hμeq⟩
  have hτμ :=
    Section1.representation_character_apply_galois_eq_argumentPow
      (G := G) (V := Fin n → ℂ) (N := N) (e := e)
      (τ := τ) hτroot ρ hdiv g
  rcases hε with rfl | rfl
  · simpa [classFunctionGaloisConjugate, hμeq] using hτμ
  · simpa [classFunctionGaloisConjugate, hμeq] using congrArg Neg.neg hτμ


private theorem classFunctionGaloisConjugate_eq_of_argumentPow_rootAction_pf39
    {G : Type u} [Group G] [Finite G]
    {χ χe : Section1.ClassFunction G} (τ : Gal(ℂ/ℚ))
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ)
    {N e : ℕ}
    (hdiv : Nat.card G ∣ N)
    (hτroot : ∀ z : ℂ, z ^ N = 1 → τ z = z ^ e)
    (harg : classFunctionArgumentPow χ χe e) :
    classFunctionGaloisConjugate τ χ = χe := by
  rcases hχ with ⟨n, ρ, _hirr, hχeq⟩
  ext g
  have hτχ :=
    Section1.representation_character_apply_galois_eq_argumentPow
      (G := G) (V := Fin n → ℂ) (N := N) (e := e)
      (τ := τ) hτroot ρ hdiv g
  calc
    classFunctionGaloisConjugate τ χ g = τ (χ g) := rfl
    _ = χ (g ^ e) := by
      simpa [hχeq, Section1.characterGaloisConjugateByAutomorphism] using hτχ
    _ = χe g := (harg g).symm


private theorem scalarProduct_self_signed_irreducible_pf39
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : IsSignedIrreducibleCharacter χ) :
    Section1.scalarProduct G χ χ = 1 := by
  rcases hχ with ⟨ε, hε, ψ, hψ, rfl⟩
  have hself : Section1.scalarProduct G ψ ψ = (1 : ℂ) := by
    simpa [Section1.IsIrreducibleCharacter] using
      (isBookIrreducibleCharacter_of_group_irreducible_pf39 hψ).2
  rcases hε with rfl | rfl
  · simpa using hself
  · rw [Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_right]
    simp [hself]

private theorem isClassFunction_of_signed_irreducible_pf39
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : IsSignedIrreducibleCharacter χ) :
    Section1.IsClassFunction χ := by
  exact isVirtualCharacter_isClassFunction
    (by
      rcases hχ with ⟨ε, hε, ψ, hψ, rfl⟩
      rcases hε with rfl | rfl
      · simpa using isVirtualCharacter_of_irreducibleCharacterOnGroup hψ
      · simpa using isVirtualCharacter_neg
          (isVirtualCharacter_of_irreducibleCharacterOnGroup hψ))

private theorem isClassFunction_of_irreducibleCharacterOnGroup_pf39
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    Section1.IsClassFunction χ := by
  exact isVirtualCharacter_isClassFunction
    (isVirtualCharacter_of_irreducibleCharacterOnGroup hχ)

private theorem isVirtualCharacter_zsmul_pf39
    {G : Type u} [Group G] (n : ℤ) {χ : G → ℂ}
    (hχ : Theory.Character.IsVirtualCharacter χ) :
    Theory.Character.IsVirtualCharacter (n • χ) := by
  classical
  rcases hχ with ⟨r, m, k, ρ, rfl⟩
  refine ⟨r, fun i => n * m i, k, ρ, ?_⟩
  ext g
  simp [Theory.Character.virtualCharacterOfRepresentations, Finset.mul_sum, mul_assoc]

private theorem isVirtualCharacter_finset_sum_pf39
    {G : Type u} [Group G] {ι : Type*} [Fintype ι]
    (s : Finset ι) (χ : ι → G → ℂ)
    (hχ : ∀ i ∈ s, Theory.Character.IsVirtualCharacter (χ i)) :
    Theory.Character.IsVirtualCharacter (fun g => ∑ i ∈ s, χ i g) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨0, (fun i : Fin 0 => nomatch i), (fun i : Fin 0 => nomatch i),
        (fun i : Fin 0 => nomatch i), ?_⟩
      ext g
      simp [Theory.Character.virtualCharacterOfRepresentations]
  | @insert i s hi hs =>
      have htail :
          Theory.Character.IsVirtualCharacter (fun g => ∑ j ∈ s, χ j g) := by
        exact hs (by
          intro j hj
          exact hχ j (by simp [hj]))
      have hheadTail :=
        isVirtualCharacter_add (hχ i (by simp)) htail
      convert hheadTail using 1
      ext g
      simp [hi]


private theorem int_sq_sum_eq_zero_all_zero_pf39
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (z : ι → ℤ)
    (hsum : Finset.sum s (fun i => z i * z i) = 0) :
    ∀ i, i ∈ s → z i = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro i hi
      simp at hi
  | @insert a s ha ih =>
      intro i hi
      have hnonneg_a : 0 ≤ z a * z a := by
        simpa [pow_two] using (sq_nonneg (z a))
      have hnonneg_s : 0 ≤ Finset.sum s (fun j => z j * z j) := by
        exact Finset.sum_nonneg (by
          intro j _hj
          simpa [pow_two] using (sq_nonneg (z j)))
      have hsplit : z a * z a + Finset.sum s (fun j => z j * z j) = 0 := by
        simpa [Finset.sum_insert ha, add_assoc, add_left_comm, add_comm] using hsum
      have hsq_a : z a * z a = 0 := by
        nlinarith
      have hsq_s : Finset.sum s (fun j => z j * z j) = 0 := by
        nlinarith
      rcases Finset.mem_insert.mp hi with rfl | hi'
      · exact sq_eq_zero_iff.mp (by simpa [pow_two] using hsq_a)
      · exact ih hsq_s i hi'

private theorem exists_sign_of_int_sq_sum_eq_one_pf39
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (z : ι → ℤ)
    (hsum : Finset.sum s (fun i => z i * z i) = 1) :
    ∃ i, i ∈ s ∧ (z i = 1 ∨ z i = -1) ∧
      ∀ j, j ∈ s → j ≠ i → z j = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp at hsum
  | @insert a s ha ih =>
      have hnonneg_a : 0 ≤ z a * z a := by
        simpa [pow_two] using (sq_nonneg (z a))
      have hnonneg_s : 0 ≤ Finset.sum s (fun j => z j * z j) := by
        exact Finset.sum_nonneg (by
          intro j _hj
          simpa [pow_two] using (sq_nonneg (z j)))
      have hsplit : z a * z a + Finset.sum s (fun j => z j * z j) = 1 := by
        simpa [Finset.sum_insert ha, add_assoc, add_left_comm, add_comm] using hsum
      by_cases hza : z a = 0
      · have hsq_s : Finset.sum s (fun j => z j * z j) = 1 := by
          nlinarith [hsplit]
        rcases ih hsq_s with ⟨i, hi, hsign, hzero⟩
        refine ⟨i, Finset.mem_insert_of_mem hi, hsign, ?_⟩
        intro j hj hji
        rcases Finset.mem_insert.mp hj with rfl | hj'
        · exact hza
        · exact hzero j hj' hji
      · have hsq_pos : 0 < z a * z a := by
          have hsq_ne : z a * z a ≠ 0 := by
            intro hsq
            exact hza (sq_eq_zero_iff.mp (by simpa [pow_two] using hsq))
          exact lt_of_le_of_ne hnonneg_a (Ne.symm hsq_ne)
        have hsq_a : z a * z a = 1 := by
          nlinarith [hsplit, hnonneg_s]
        have hsq_s : Finset.sum s (fun j => z j * z j) = 0 := by
          nlinarith [hsplit, hsq_a]
        have hsign_a : z a = 1 ∨ z a = -1 := by
          exact sq_eq_one_iff.mp (by simpa [pow_two] using hsq_a)
        have hzero_s : ∀ j ∈ s, z j = 0 :=
          int_sq_sum_eq_zero_all_zero_pf39 s z hsq_s
        refine ⟨a, Finset.mem_insert_self a s, hsign_a, ?_⟩
        intro j hj hja
        rcases Finset.mem_insert.mp hj with rfl | hj'
        · exact False.elim (hja rfl)
        · exact hzero_s j hj'

public theorem signed_irreducible_of_virtual_norm_one_pf39
    {G : Type u} [Group G] [Finite G]
    {φ : Section1.ClassFunction G}
    (hvirt : Theory.Character.IsVirtualCharacter φ)
    (hself : Section1.scalarProduct G φ φ = 1) :
    IsSignedIrreducibleCharacter φ := by
  classical
  have hφclass : Section1.IsClassFunction φ :=
    isVirtualCharacter_isClassFunction hvirt
  rcases Theory.Character.irreducible_characters_form_basis (G := G) with
    ⟨ι, hι, χ, hχ, _b, _hb⟩
  letI : Fintype ι := hι
  letI : Finite ι := Finite.of_fintype ι
  letI : Fintype ι := Fintype.ofFinite ι
  rcases hχ with ⟨hirr, hall, _hinj⟩
  let ψ : ι → Section1.ClassFunction G := fun i => Section1.ofConjClassFunction (χ i)
  have hψclass : ∀ i, Section1.IsClassFunction (ψ i) := by
    intro i
    exact Section1.ofConjClassFunction_isClassFunction (χ i)
  have hψirr : ∀ i, Section1.IsIrreducibleCharacterOnGroup (ψ i) := by
    intro i
    exact ofConjClassFunction_isIrreducibleCharacterOnGroup (hirr i)
  have horthψ :
      ∀ i j,
        Section1.scalarProduct G (ψ i) (ψ j) = if i = j then 1 else 0 := by
    intro i j
    have hto :
        ∀ k, Section1.toConjClassFunction (ψ k) (hψclass k) = χ k := by
      intro k
      apply Section1.toConjClassFunction_eq_of_apply
      intro g
      rfl
    calc
      Section1.scalarProduct G (ψ i) (ψ j) =
          Theory.Character.classFunctionInner
            (Section1.toConjClassFunction (ψ i) (hψclass i))
            (Section1.toConjClassFunction (ψ j) (hψclass j)) :=
        (Section1.classFunctionInner_toConjClassFunction
          (ψ i) (ψ j) (hψclass i) (hψclass j)).symm
      _ = Theory.Character.classFunctionInner (χ i) (χ j) := by
        rw [hto i, hto j]
      _ = if i = j then 1 else 0 :=
        Section1.representation_completeFamily_orthonormal
          (chi := χ) ⟨hirr, hall, _hinj⟩ i j
  have hcoeff_int :
      ∀ i, ∃ z : ℤ, Section1.scalarProduct G φ (ψ i) = (z : ℂ) := by
    intro i
    exact scalarProduct_isVirtualCharacter_eq_int
      hvirt
      (isVirtualCharacter_of_irreducibleCharacterOnGroup (hψirr i))
  let a : ι → ℤ := fun i => Classical.choose (hcoeff_int i)
  have ha : ∀ i, Section1.scalarProduct G φ (ψ i) = (a i : ℂ) := by
    intro i
    exact Classical.choose_spec (hcoeff_int i)
  let φsum : Section1.ClassFunction G :=
    Section1.weightedFamilySum (fun i => (a i : ℂ)) ψ
  have hφsumclass : Section1.IsClassFunction φsum := by
    intro x g
    unfold φsum Section1.weightedFamilySum
    refine Finset.sum_congr rfl ?_
    intro i _hi
    simp [hψclass i x g]
  have hEq : φsum = φ := by
    apply Section1.classFunction_eq_of_inner_irreducible
      (phi := φsum) (psi := φ) hφsumclass hφclass
    intro ξ hξ
    rcases hall ξ hξ with ⟨i, rfl⟩
    calc
      Theory.Character.classFunctionInner
          (Section1.toConjClassFunction φsum hφsumclass) (χ i) =
        Section1.scalarProduct G φsum (ψ i) := by
          rw [← Section1.toConjClassFunction_ofConjClassFunction (χ i)]
          exact Section1.classFunctionInner_toConjClassFunction
            φsum (ψ i) hφsumclass (hψclass i)
      _ = (a i : ℂ) := by
          exact Section1.scalarProduct_weightedFamilySum_left_orthonormal
            (w := fun i => (a i : ℂ)) (chi := ψ) horthψ i
      _ = Section1.scalarProduct G φ (ψ i) := (ha i).symm
      _ = Theory.Character.classFunctionInner
          (Section1.toConjClassFunction φ hφclass) (χ i) := by
          rw [← Section1.toConjClassFunction_ofConjClassFunction (χ i)]
          exact (Section1.classFunctionInner_toConjClassFunction
            φ (ψ i) hφclass (hψclass i)).symm
  have hcoeff_sum :
      Section1.scalarProduct G φsum φsum =
        ∑ i : ι, star ((a i : ℂ)) * (a i : ℂ) := by
    calc
      Section1.scalarProduct G φsum φsum =
        ∑ i : ι, star ((a i : ℂ)) * Section1.scalarProduct G φsum (ψ i) := by
          unfold φsum Section1.weightedFamilySum
          rw [Section1.scalarProduct_fintype_sum_right]
          refine Finset.sum_congr rfl ?_
          intro i _hi
          change
            Section1.scalarProduct G
                (fun g => ∑ i, (a i : ℂ) * ψ i g)
                (((a i : ℂ)) • ψ i) =
              star ((a i : ℂ)) *
                Section1.scalarProduct G
                  (fun g => ∑ i, (a i : ℂ) * ψ i g) (ψ i)
          rw [Section1.scalarProduct_smul_right]
      _ = ∑ i : ι, star ((a i : ℂ)) * (a i : ℂ) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [Section1.scalarProduct_weightedFamilySum_left_orthonormal
            (w := fun i => (a i : ℂ)) (chi := ψ) horthψ i]
  have hsq_complex : ((∑ i : ι, a i * a i : ℤ) : ℂ) = 1 := by
    calc
      ((∑ i : ι, a i * a i : ℤ) : ℂ) =
        ∑ i : ι, star ((a i : ℂ)) * (a i : ℂ) := by
          simp [Int.cast_sum, Int.cast_mul]
      _ = Section1.scalarProduct G φsum φsum := hcoeff_sum.symm
      _ = 1 := by
          simpa [hEq] using hself
  have hsq_int : ∑ i : ι, a i * a i = 1 := by
    exact_mod_cast hsq_complex
  rcases exists_sign_of_int_sq_sum_eq_one_pf39 (Finset.univ) a hsq_int with
    ⟨i0, _hi0, hsign0, hzero0⟩
  have hsingle :
      φsum = (a i0 : ℂ) • ψ i0 := by
    ext g
    unfold φsum Section1.weightedFamilySum
    rw [Finset.sum_eq_single i0]
    · simp
    · intro j _hj hji
      simp [hzero0 j (by simp) hji]
    · intro hi0not
      exact False.elim (hi0not (by simp))
  rcases hsign0 with hi0 | hi0
  · refine ⟨1, Or.inl rfl, ψ i0, hψirr i0, ?_⟩
    calc
      φ = φsum := hEq.symm
      _ = (a i0 : ℂ) • ψ i0 := hsingle
      _ = (1 : ℂ) • ψ i0 := by simp [hi0]
  · refine ⟨-1, Or.inr rfl, ψ i0, hψirr i0, ?_⟩
    calc
      φ = φsum := hEq.symm
      _ = (a i0 : ℂ) • ψ i0 := hsingle
      _ = (-1 : ℂ) • ψ i0 := by simp [hi0]

private theorem signed_irreducible_eq_sign_smul_of_scalarProduct_ne_zero_pf39
    {G : Type u} [Group G] [Finite G]
    {X Y : Section1.ClassFunction G}
    (hX : IsSignedIrreducibleCharacter X)
    (hY : IsSignedIrreducibleCharacter Y)
    (hXY : Section1.scalarProduct G X Y ≠ 0) :
    ∃ ε : ℂ, Section1.IsSign ε ∧ X = ε • Y := by
  rcases hY with ⟨δ, hδ, ψ, hψ, rfl⟩
  have hXψ : Section1.scalarProduct G X ψ ≠ 0 := by
    intro hzero
    apply hXY
    rw [Section1.scalarProduct_smul_right, hzero]
    simp
  rcases (scalarProduct_signed_irreducible_ne_zero_iff_pf39 hX hψ).1 hXψ with
    ⟨ε, hε, hEq⟩
  rcases hδ with rfl | rfl
  · exact ⟨ε, hε, by simpa using hEq⟩
  · refine ⟨-ε, ?_, ?_⟩
    · rcases hε with rfl | rfl <;> simp [Section1.IsSign]
    · simpa [smul_smul] using hEq

private theorem nonzero_scalarProduct_family_index_unique_pf39
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (χ : I → J → Section1.ClassFunction G)
    (horth : IsOrthonormalDoubleFamily χ)
    (hsigned : ∀ i j, IsSignedIrreducibleCharacter (χ i j))
    {X : Section1.ClassFunction G}
    (hX : IsSignedIrreducibleCharacter X)
    {i i' : I} {j j' : J}
    (hij : Section1.scalarProduct G X (χ i j) ≠ 0)
    (hi'j' : Section1.scalarProduct G X (χ i' j') ≠ 0) :
    (i, j) = (i', j') := by
  rcases signed_irreducible_eq_sign_smul_of_scalarProduct_ne_zero_pf39
      hX (hsigned i j) hij with
    ⟨ε, hε, hEq⟩
  have hcross : Section1.scalarProduct G (χ i j) (χ i' j') ≠ 0 := by
    intro hzero
    apply hi'j'
    rw [hEq, Section1.scalarProduct_smul_left, hzero]
    simp
  by_cases hpair : (i, j) = (i', j')
  · exact hpair
  · have horth_zero :
        Section1.scalarProduct G (χ i j) (χ i' j') = 0 := by
      simpa [hpair] using horth (i, j) (i', j')
    exact (hcross horth_zero).elim

private theorem signed_irreducible_eq_of_scalarProduct_eq_one_pf39
    {G : Type u} [Group G] [Finite G]
    {X Y : Section1.ClassFunction G}
    (hX : IsSignedIrreducibleCharacter X)
    (hY : IsSignedIrreducibleCharacter Y)
    (hXY : Section1.scalarProduct G X Y = 1) :
    X = Y := by
  have hXY_ne : Section1.scalarProduct G X Y ≠ 0 := by
    rw [hXY]
    exact one_ne_zero
  rcases signed_irreducible_eq_sign_smul_of_scalarProduct_ne_zero_pf39 hX hY hXY_ne with
    ⟨ε, hε, hEq⟩
  have hself : Section1.scalarProduct G Y Y = 1 :=
    scalarProduct_self_signed_irreducible_pf39 hY
  have hεeq : ε = 1 := by
    rw [hEq, Section1.scalarProduct_smul_left, hself] at hXY
    simpa using hXY
  simpa [hεeq] using hEq

private theorem sigmaOfPF35_signed_image
    {G : Type u} [Group G] [Finite G]
    {W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (ω : I → J → Section1.ClassFunction W)
    (χ : I → J → Section1.ClassFunction G)
    (hω : IsOrthonormalDoubleFamily ω)
    (hsigned : ∀ i j, IsSignedIrreducibleCharacter (χ i j))
    (i : I) (j : J) :
    IsSignedIrreducibleCharacter (sigmaOfPF35 ω χ (ω i j)) := by
  simpa [sigmaOfPF35_apply_omega ω χ hω i j] using hsigned i j

private theorem coefficientNonzeroCount_le_two_of_projection_diff_pf39
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (χ : I → J → Section1.ClassFunction G)
    (horth : IsOrthonormalDoubleFamily χ)
    (hsigned : ∀ i j, IsSignedIrreducibleCharacter (χ i j))
    {X : Section1.ClassFunction G}
    (hX : IsSignedIrreducibleCharacter X)
    (i : I) (j : J) :
    let ψ : Section1.ClassFunction G := χ i j - X
    let a : I → J → ℂ := fun p q => Section1.scalarProduct G ψ (χ p q)
    coefficientNonzeroCount a ≤ 2 := by
  classical
  intro ψ a
  have ha_formula :
      ∀ p q,
        a p q =
          (if (p, q) = (i, j) then (1 : ℂ) else 0) -
            Section1.scalarProduct G X (χ p q) := by
    intro p q
    dsimp [a, ψ]
    rw [sub_eq_add_neg, Section1.scalarProduct_add_left]
    have hneg : (-X : Section1.ClassFunction G) = (-1 : ℂ) • X := by
      ext g
      simp
    rw [hneg, Section1.scalarProduct_smul_left]
    have hχ :
        Section1.scalarProduct G (χ i j) (χ p q) =
          if (p, q) = (i, j) then (1 : ℂ) else 0 := by
      simpa [Prod.mk.injEq, eq_comm, and_left_comm, and_assoc] using
        horth (i, j) (p, q)
    rw [hχ]
    simp [sub_eq_add_neg]
  have hXcoeff :
      ∀ {p : I × J}, p ≠ (i, j) → a p.1 p.2 ≠ 0 →
        Section1.scalarProduct G X (χ p.1 p.2) ≠ 0 := by
    intro p hp hnon hzero
    rw [ha_formula p.1 p.2, if_neg hp, hzero] at hnon
    simp at hnon
  let f : {p : I × J // a p.1 p.2 ≠ 0} → Bool := fun p =>
    decide (p.1 = (i, j))
  have hf : Function.Injective f := by
    intro p q hpq
    by_cases hp : p.1 = (i, j)
    · by_cases hq : q.1 = (i, j)
      · apply Subtype.ext
        exact hp.trans hq.symm
      · have : f p ≠ f q := by
          simp [f, hp, hq]
        exact (this hpq).elim
    · by_cases hq : q.1 = (i, j)
      · have : f p ≠ f q := by
          simp [f, hp, hq]
        exact (this hpq).elim
      · apply Subtype.ext
        exact nonzero_scalarProduct_family_index_unique_pf39
          (χ := χ) (horth := horth) (hsigned := hsigned) (X := X) hX
          (hXcoeff hp p.2) (hXcoeff hq q.2)
  have hcard := Fintype.card_le_of_injective f hf
  simpa [coefficientNonzeroCount, f] using hcard

private theorem scalarProduct_projection_residual_sigmaOfPF35_zero_pf39
    {G : Type u} [Group G] [Finite G]
    {W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (ω : I → J → Section1.ClassFunction W)
    (χ : I → J → Section1.ClassFunction G)
    (horth : IsOrthonormalDoubleFamily χ)
    (ψ : Section1.ClassFunction G)
    (α : Section1.ClassFunction W) :
    let a : I → J → ℂ := fun i j => Section1.scalarProduct G ψ (χ i j)
    let β : Section1.ClassFunction G :=
      ψ - ∑ p : I × J, a p.1 p.2 • χ p.1 p.2
    Section1.scalarProduct G β (sigmaOfPF35 ω χ α) = 0 := by
  classical
  intro a β
  have hbeta :
      ∀ p : I × J, Section1.scalarProduct G β (χ p.1 p.2) = 0 := by
    intro p
    have hsum :
        (∑ q : I × J, a q.1 q.2 • χ q.1 q.2) =
          Section1.weightedFamilySum
            (fun q : I × J => a q.1 q.2)
            (fun q : I × J => χ q.1 q.2) := by
      ext g
      have : instFintypeProd I J = Fintype.ofFinite (I × J) := by exact of_decide_eq_true rfl
      rw [this]
      simp [Section1.weightedFamilySum, smul_eq_mul]
    have hproj :
        Section1.scalarProduct G
            (∑ q : I × J, a q.1 q.2 • χ q.1 q.2)
            (χ p.1 p.2) =
          a p.1 p.2 := by
      rw [hsum]
      simpa [a] using
        (Section1.scalarProduct_weightedFamilySum_left_orthonormal
          (G := G)
          (w := fun q : I × J => a q.1 q.2)
          (chi := fun q : I × J => χ q.1 q.2)
          (horth := horth) (j := p))
    have hnegSum :
        (-(∑ q : I × J, a q.1 q.2 • χ q.1 q.2) : Section1.ClassFunction G) =
          (-1 : ℂ) • ∑ q : I × J, a q.1 q.2 • χ q.1 q.2 := by
      ext g
      simp
    dsimp [β]
    rw [sub_eq_add_neg, Section1.scalarProduct_add_left, hnegSum,
      Section1.scalarProduct_smul_left, hproj]
    ring
  have hsigma :
      sigmaOfPF35 ω χ α =
        Section1.weightedFamilySum
          (fun p : I × J => Section1.scalarProduct W α (ω p.1 p.2))
          (fun p : I × J => χ p.1 p.2) := by
    ext g
    simp [sigmaOfPF35, Section1.weightedFamilySum]
  rw [hsigma, Section1.scalarProduct_weightedFamilySum_right]
  simp [hbeta]

private theorem supportedOn_apply_pf32
    {H : Type*} {A : Set H} {phi : Section1.ClassFunction H}
    (h : Section1.supportedOn phi A) :
    ∀ g, g ∉ A → phi g = 0 := by
  rw [Section1.supportedOn_iff] at h
  exact h

private noncomputable def deltaFunction_pf32
    {H : Type*} [DecidableEq H] (a : H) : Section1.ClassFunction H :=
  fun x => if x = a then 1 else 0

private theorem supportedOn_basis_pf32
    {H J : Type*} [Finite H] [Fintype J]
    {A : Set H} (basis : Module.Basis J ℂ (Section1.classFunctionsOn H A)) (j : J) :
    Section1.supportedOn (basis j : Section1.ClassFunction H) A := by
  exact (Section1.mem_classFunctionsOn).1 (basis j).property

private theorem scalarProduct_add_right_pf32
    {H : Type*} [Finite H] (phi psi1 psi2 : Section1.ClassFunction H) :
    Section1.scalarProduct H phi (psi1 + psi2) =
      Section1.scalarProduct H phi psi1 + Section1.scalarProduct H phi psi2 := by
  simp [Section1.scalarProduct, mul_add, Finset.sum_add_distrib]

private theorem scalarProduct_smul_right_pf32
    {H : Type*} [Finite H] (z : ℂ) (phi psi : Section1.ClassFunction H) :
    Section1.scalarProduct H phi (z • psi) = Section1.scalarProduct H phi psi * star z := by
  calc
    Section1.scalarProduct H phi (z • psi)
        = (Nat.card H : ℂ)⁻¹ * ∑ g : H, (phi g * star (psi g)) * star z := by
            rw [Section1.scalarProduct]
            congr 1
            refine Finset.sum_congr rfl ?_
            intro g hg
            simp [mul_left_comm, mul_comm]
    _ = (Nat.card H : ℂ)⁻¹ * ((∑ g : H, phi g * star (psi g)) * star z) := by
          rw [Finset.sum_mul]
    _ = Section1.scalarProduct H phi psi * star z := by
          simp [Section1.scalarProduct, mul_left_comm, mul_comm]

private theorem scalarProduct_sub_right_pf32
    {H : Type*} [Finite H] (phi psi1 psi2 : Section1.ClassFunction H) :
    Section1.scalarProduct H phi (psi1 - psi2) =
      Section1.scalarProduct H phi psi1 - Section1.scalarProduct H phi psi2 := by
  calc
    Section1.scalarProduct H phi (psi1 - psi2)
        = Section1.scalarProduct H phi (psi1 + (-1 : ℂ) • psi2) := by
            congr 1
            ext g
            simp [sub_eq_add_neg]
    _ = Section1.scalarProduct H phi psi1 +
          Section1.scalarProduct H phi ((-1 : ℂ) • psi2) := by
          rw [scalarProduct_add_right_pf32]
    _ = Section1.scalarProduct H phi psi1 - Section1.scalarProduct H phi psi2 := by
          rw [scalarProduct_smul_right_pf32]
          simp [sub_eq_add_neg]

private theorem scalarProduct_sum_left_pf32
    {H I : Type*} [Finite H] [Fintype I]
    (psi : Section1.ClassFunction H) (d : I → ℂ) (phi : I → Section1.ClassFunction H) :
    Section1.scalarProduct H (∑ i, d i • phi i) psi =
      ∑ i, d i * Section1.scalarProduct H (phi i) psi := by
  classical
  induction (Finset.univ : Finset I) using Finset.induction_on with
  | empty =>
      simp [Section1.scalarProduct]
  | @insert i s hi hs =>
      simp [hi, Section1.scalarProduct_add_left, Section1.scalarProduct_smul_left, hs]

private theorem scalarProduct_sum_right_pf32
    {H I : Type*} [Finite H] [Fintype I]
    (phi : Section1.ClassFunction H) (d : I → ℂ) (psi : I → Section1.ClassFunction H) :
    Section1.scalarProduct H phi (∑ i, d i • psi i) =
      ∑ i, Section1.scalarProduct H phi (psi i) * star (d i) := by
  classical
  induction (Finset.univ : Finset I) using Finset.induction_on with
  | empty =>
      simp [Section1.scalarProduct]
  | @insert i s hi hs =>
      simp [hi, scalarProduct_add_right_pf32, scalarProduct_smul_right_pf32, hs]

private theorem scalarProduct_eq_zero_of_support_disjoint_pf32
    {H : Type*} [Finite H]
    {A : Set H} {phi psi : Section1.ClassFunction H}
    (hphi : Section1.supportedOn phi A)
    (hpsi : Section1.supportedOn psi Aᶜ) :
    Section1.scalarProduct H phi psi = 0 := by
  have hsum : ∑ g : H, phi g * star (psi g) = 0 := by
    classical
    refine Finset.sum_eq_zero ?_
    intro g hg
    by_cases hgA : g ∈ A
    · have hgAc : g ∉ Aᶜ := by simpa using hgA
      have hpsi' := supportedOn_apply_pf32 hpsi
      have hzero : psi g = 0 := hpsi' g hgAc
      simp [hzero]
    · have hphi' := supportedOn_apply_pf32 hphi
      have hzero : phi g = 0 := hphi' g hgA
      simp [hzero]
  rw [Section1.scalarProduct, hsum]
  simp

private theorem basis_test_iff_orthogonalTo_subspace_pf32
    {H J : Type*} [Finite H] [Fintype J]
    {A : Set H} (basis : Module.Basis J ℂ (Section1.classFunctionsOn H A))
    (eta : Section1.ClassFunction H) :
    (∀ j, Section1.scalarProduct H (basis j : Section1.ClassFunction H) eta = 0) ↔
      ∀ phi ∈ Section1.classFunctionsOn H A, Section1.scalarProduct H phi eta = 0 := by
  constructor
  · intro h phi hphi
    let x : Section1.classFunctionsOn H A := ⟨phi, hphi⟩
    let L : Section1.classFunctionsOn H A →ₗ[ℂ] ℂ :=
      { toFun := fun psi => Section1.scalarProduct H (psi : Section1.ClassFunction H) eta
        map_add' := by
          intro psi1 psi2
          exact Section1.scalarProduct_add_left
            (psi1 : Section1.ClassFunction H) (psi2 : Section1.ClassFunction H) eta
        map_smul' := by
          intro z psi
          exact Section1.scalarProduct_smul_left z (psi : Section1.ClassFunction H) eta }
    have hLbasis : ∀ j, L (basis j) = 0 := by
      intro j
      simpa [L] using h j
    change L x = 0
    calc
      L x = L (∑ j, basis.repr x j • basis j) := by rw [basis.sum_repr x]
      _ = ∑ j, L (basis.repr x j • basis j) := by rw [map_sum]
      _ = ∑ j, basis.repr x j • L (basis j) := by simp
      _ = 0 := by simp [hLbasis]
  · intro h j
    exact h (basis j) (by simp)

private theorem deltaFunction_supportedOn_pf32
    {H : Type*} [Finite H] [DecidableEq H]
    {A : Set H} {a : H} (ha : a ∈ A) :
    Section1.supportedOn (deltaFunction_pf32 a) A := by
  rw [Section1.supportedOn_iff]
  intro g hg
  by_cases hga : g = a
  · exfalso
    apply hg
    simpa [hga] using ha
  · simp [deltaFunction_pf32, hga]

private theorem scalarProduct_delta_left_pf32
    {H : Type*} [Finite H] [DecidableEq H]
    (a : H) (phi : Section1.ClassFunction H) :
    Section1.scalarProduct H (deltaFunction_pf32 a) phi =
      (Nat.card H : ℂ)⁻¹ * star (phi a) := by
  simp [Section1.scalarProduct, deltaFunction_pf32]

private theorem proposition_1_3_a_special_pf32
    {G : Type*} [Group G] [Finite G]
    {H : Subgroup G} [Finite H]
    {A : Set H}
    {I J : Type*} [Fintype I] [Fintype J]
    (basis : Module.Basis J ℂ (Section1.classFunctionsOn H A))
    (chi : I → Section1.ClassFunction H)
    (ind : Section1.ClassFunction H →ₗ[ℂ] Section1.ClassFunction G)
    (mu : Section1.ClassFunction G)
    (hfrob : ∀ alpha,
      Section1.scalarProduct G (ind alpha) mu =
        Section1.scalarProduct H alpha (Section1.subgroupRestriction H mu))
    (d : I → ℂ) :
    (∀ g ∈ A, Section1.subgroupRestriction H mu g = (∑ i, d i • chi i) g) ↔
      ∀ j,
        ∑ i, Section1.scalarProduct H (basis j : Section1.ClassFunction H) (chi i) * star (d i) =
          Section1.scalarProduct G (ind (basis j : Section1.ClassFunction H)) mu := by
  let rhs : Section1.ClassFunction H := ∑ i, d i • chi i
  let diff : Section1.ClassFunction H := Section1.subgroupRestriction H mu - rhs
  have hsupport :
      (∀ g ∈ A, Section1.subgroupRestriction H mu g = rhs g) ↔
        Section1.supportedOn diff Aᶜ := by
    constructor
    · intro h
      rw [Section1.supportedOn_iff]
      intro g hg
      have hgA : g ∈ A := by simpa using hg
      simpa [diff, rhs, Pi.sub_apply, sub_eq_zero] using h g hgA
    · intro h g hg
      rw [Section1.supportedOn_iff] at h
      have hgc : g ∉ Aᶜ := by simpa using hg
      simpa [diff, rhs, Pi.sub_apply, sub_eq_zero] using h g hgc
  constructor
  · intro hEq j
    have hzero :
        Section1.scalarProduct H (basis j : Section1.ClassFunction H) diff = 0 := by
      exact scalarProduct_eq_zero_of_support_disjoint_pf32
        (supportedOn_basis_pf32 basis j) ((hsupport.mp hEq))
    have hexpand :
        Section1.scalarProduct H (basis j : Section1.ClassFunction H) diff =
          Section1.scalarProduct G (ind (basis j : Section1.ClassFunction H)) mu -
            ∑ i, Section1.scalarProduct H (basis j : Section1.ClassFunction H) (chi i) *
              star (d i) := by
      simp [diff, rhs, hfrob, scalarProduct_sub_right_pf32,
        scalarProduct_sum_right_pf32]
    have hmain :
        Section1.scalarProduct G (ind (basis j : Section1.ClassFunction H)) mu -
          ∑ i, Section1.scalarProduct H (basis j : Section1.ClassFunction H) (chi i) *
            star (d i) = 0 := by
      simpa [hexpand] using hzero
    exact (sub_eq_zero.mp hmain).symm
  · intro hCoeff
    have hBasisZero :
        ∀ j, Section1.scalarProduct H (basis j : Section1.ClassFunction H) diff = 0 := by
      intro j
      have hj := hCoeff j
      have hmain :
          Section1.scalarProduct G (ind (basis j : Section1.ClassFunction H)) mu -
            ∑ i, Section1.scalarProduct H (basis j : Section1.ClassFunction H) (chi i) *
              star (d i) = 0 := by
        exact sub_eq_zero.mpr hj.symm
      simpa [diff, rhs, hfrob, scalarProduct_sub_right_pf32,
        scalarProduct_sum_right_pf32] using hmain
    have hAllZero :
        ∀ phi ∈ Section1.classFunctionsOn H A, Section1.scalarProduct H phi diff = 0 :=
        (basis_test_iff_orthogonalTo_subspace_pf32 basis diff).mp hBasisZero
    have hcard : (Nat.card H : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩ : Nat.card H ≠ 0)
    have hSuppCompl : Section1.supportedOn diff Aᶜ := by
      rw [Section1.supportedOn_iff]
      intro a ha
      classical
      have haA : a ∈ A := by simpa using ha
      have hdelta :
          Section1.scalarProduct H (deltaFunction_pf32 a) diff = 0 := by
        exact hAllZero (deltaFunction_pf32 a)
          ((Section1.mem_classFunctionsOn).2 (deltaFunction_supportedOn_pf32 haA))
      have hpoint :
          diff a = 0 := by
        rw [scalarProduct_delta_left_pf32] at hdelta
        rcases mul_eq_zero.mp hdelta with hbad | hstar
        · exact (inv_ne_zero hcard hbad).elim
        · exact star_eq_zero.mp hstar
      exact hpoint
    exact (hsupport).2 hSuppCompl

private theorem isClassFunction_of_commGroup_pf39
    {A : Type*} [CommGroup A] (φ : Section1.ClassFunction A) :
    Section1.IsClassFunction φ := by
  intro x g
  simp [mul_assoc]

public theorem weightedFamilySum_eq_of_inner_omega_pf39
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (α : Section1.ClassFunction W) :
    Section1.weightedFamilySum
        (fun p : I × J => Section1.scalarProduct W α (ω p.1 p.2))
        (fun p : I × J => ω p.1 p.2) = α := by
  classical
  rcases h with ⟨_hW1, _hW2, _hIP, hcyc, _hodd, _hcard1, _hcard2, _hTI⟩
  letI : IsCyclic W := hcyc
  letI : CommGroup W := IsCyclic.commGroup
  have hαclass : Section1.IsClassFunction α := isClassFunction_of_commGroup_pf39 α
  have hsumclass :
      Section1.IsClassFunction
        (Section1.weightedFamilySum
          (fun p : I × J => Section1.scalarProduct W α (ω p.1 p.2))
          (fun p : I × J => ω p.1 p.2)) := by
    intro x g
    simp [Section1.weightedFamilySum, mul_assoc]
  apply Section1.classFunction_eq_of_inner_irreducible
    (phi :=
      Section1.weightedFamilySum
        (fun p : I × J => Section1.scalarProduct W α (ω p.1 p.2))
        (fun p : I × J => ω p.1 p.2))
    (psi := α) hsumclass hαclass
  intro ψ hψ
  rcases hω.all_irreducibles
      (Section1.ofConjClassFunction ψ)
      (ofConjClassFunction_isIrreducibleCharacterOnGroup hψ) with
    ⟨i, j, hψeq⟩
  have hψeq' : Section1.toConjClassFunction (ω i j) (hω.is_class i j) = ψ := by
    apply Section1.toConjClassFunction_eq_of_apply
    intro g
    simpa [Section1.ofConjClassFunction_apply] using congrFun hψeq g
  rw [← hψeq']
  calc
    Theory.Character.classFunctionInner
        (Section1.toConjClassFunction
          (Section1.weightedFamilySum
            (fun p : I × J => Section1.scalarProduct W α (ω p.1 p.2))
            (fun p : I × J => ω p.1 p.2)) hsumclass)
        (Section1.toConjClassFunction (ω i j) (hω.is_class i j)) =
      Section1.scalarProduct W
        (Section1.weightedFamilySum
          (fun p : I × J => Section1.scalarProduct W α (ω p.1 p.2))
          (fun p : I × J => ω p.1 p.2))
        (ω i j) := by
          simpa using
            (Section1.classFunctionInner_toConjClassFunction
              (Section1.weightedFamilySum
                (fun p : I × J => Section1.scalarProduct W α (ω p.1 p.2))
                (fun p : I × J => ω p.1 p.2))
              (ω i j) hsumclass (hω.is_class i j))
    _ = Section1.scalarProduct W α (ω i j) := by
          simpa [Section1.weightedFamilySum] using
            (Section1.scalarProduct_weightedFamilySum_left_orthonormal
              (w := fun p : I × J => Section1.scalarProduct W α (ω p.1 p.2))
              (chi := fun p : I × J => ω p.1 p.2)
              (horth := hω.orthonormal) (j := (i, j)))
    _ =
      Theory.Character.classFunctionInner
        (Section1.toConjClassFunction α hαclass)
        (Section1.toConjClassFunction (ω i j) (hω.is_class i j)) := by
          symm
          simpa using
            (Section1.classFunctionInner_toConjClassFunction
              α (ω i j) hαclass (hω.is_class i j))

private theorem exists_alpha_basis_pf39
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω) :
    ∃ basis : Module.Basis {p : I × J // p.1 ≠ i0 ∧ p.2 ≠ j0} ℂ
        (Section1.classFunctionsOn W (cyclicTISetSubgroup W1 W2 W)),
      ∀ p,
        (basis p : Section1.ClassFunction W) = alphaIJ W i0 j0 ω p.1.1 p.1.2 := by
  classical
  have h34 := proposition_3_4 (W1 := W1) (W2 := W2) (W := W)
    (I := I) (J := J) (i0 := i0) (j0 := j0) (omega := ω) h hω
  let alpha :
      {p : I × J // p.1 ≠ i0 ∧ p.2 ≠ j0} → Section1.ClassFunction W :=
    fun p => alphaIJ W i0 j0 ω p.1.1 p.1.2
  let e :
      {p : I × J // p.1 ≠ i0 ∧ p.2 ≠ j0} →
        Section1.classFunctionsOn W (cyclicTISetSubgroup W1 W2 W) :=
    fun p => by
      refine ⟨alpha p, ?_⟩
      rw [Section1.mem_classFunctionsOn, Section1.supportedOn_iff]
      exact fun x : W => fun hx => by
        have hx' : (x : G) ∉ cyclicTISet W1 W2 W := by
          simpa [cyclicTISetSubgroup] using hx
        exact (h34.1 p).2 x hx'
  have he_li : LinearIndependent ℂ e := by
    have hcomp : LinearIndependent ℂ ((Submodule.subtype _) ∘ e) := by
      have heq : (Submodule.subtype _ ∘ e) = alpha := by
        funext p
        rfl
      rw [heq]
      exact h34.2.1
    exact ((Submodule.subtype _).linearIndependent_iff
      (Submodule.ker_subtype _)).mp hcomp
  have he_span : ⊤ ≤ Submodule.span ℂ (Set.range e) := by
    rintro ⟨φ, hφsupp⟩ hy
    have hφsupp' := (Section1.mem_classFunctionsOn).mp hφsupp
    rcases h with ⟨_hW1, _hW2, _hIP, hcyc, _hodd, _hcard1, _hcard2, _hTI⟩
    letI : IsCyclic W := hcyc
    letI : CommGroup W := IsCyclic.commGroup
    rcases h34.2.2 φ
        (by
          constructor
          · exact isClassFunction_of_commGroup_pf39 φ
          · intro x hx
            exact supportedOn_apply_pf32 hφsupp' x (by simpa [cyclicTISetSubgroup] using hx)) with
      ⟨c, hc⟩
    have hy' : (⟨φ, hφsupp⟩ : Section1.classFunctionsOn W (cyclicTISetSubgroup W1 W2 W)) =
        ∑ p, c p • e p := by
      apply Subtype.ext
      simpa [e, alpha] using hc
    rw [hy']
    exact Submodule.sum_mem _ (fun p _hp =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩))
  refine ⟨Module.Basis.mk he_li he_span, ?_⟩
  intro p
  have h := congrArg
    (fun z : Section1.classFunctionsOn W (cyclicTISetSubgroup W1 W2 W) =>
      (z : Section1.ClassFunction W))
    (Module.Basis.mk_apply he_li he_span p)
  exact h.trans rfl

private theorem isCFLinearIsometry_sigmaOfPF35_pf39
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : I → J → Section1.ClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (horth : IsOrthonormalDoubleFamily χ)
    (_hsigned : ∀ i j, IsSignedIrreducibleCharacter (χ i j))
    (_h00 : χ i0 j0 = Section1.principalCharacter G)
    (_hInd : ∀ i j, i ≠ i0 → j ≠ j0 →
      Section1.inducedCF W (alphaIJ W i0 j0 ω i j) =
        Section1.principalCharacter G - χ i j0 - χ i0 j + χ i j) :
    IsCFLinearIsometry (sigmaOfPF35 ω χ) := by
  classical
  let σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G :=
    sigmaOfPF35 ω χ
  have hσ_omega : ∀ i j, σ (ω i j) = χ i j := by
    intro i j
    simp [σ, sigmaOfPF35_apply_omega ω χ hω.orthonormal i j]
  intro α β _hα _hβ
  have hσα :
      σ α =
        Section1.weightedFamilySum
          (fun p : I × J => Section1.scalarProduct W α (ω p.1 p.2))
          (fun p : I × J => χ p.1 p.2) := by
    rfl
  have hσβ :
      σ β =
        Section1.weightedFamilySum
          (fun p : I × J => Section1.scalarProduct W β (ω p.1 p.2))
          (fun p : I × J => χ p.1 p.2) := by
    rfl
  have hωexpandβ :
      Section1.weightedFamilySum
        (fun p : I × J => Section1.scalarProduct W β (ω p.1 p.2))
        (fun p : I × J => ω p.1 p.2) = β :=
    weightedFamilySum_eq_of_inner_omega_pf39
      (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0) (ω := ω) h hω β
  have hσβ_inner :
      Section1.scalarProduct G (σ α)
        (Section1.weightedFamilySum
          (fun p : I × J => Section1.scalarProduct W β (ω p.1 p.2))
          (fun p : I × J => χ p.1 p.2)) =
      Section1.scalarProduct W α
        (Section1.weightedFamilySum
          (fun p : I × J => Section1.scalarProduct W β (ω p.1 p.2))
          (fun p : I × J => ω p.1 p.2)) := by
    rw [Section1.scalarProduct_weightedFamilySum_right,
      Section1.scalarProduct_weightedFamilySum_right]
    refine Finset.sum_congr rfl ?_
    intro p hp
    have hinner :
        Section1.scalarProduct G (σ α) (χ p.1 p.2) =
          Section1.scalarProduct W α (ω p.1 p.2) := by
      rw [hσα]
      simpa [Section1.weightedFamilySum] using
        (Section1.scalarProduct_weightedFamilySum_left_orthonormal
          (w := fun q : I × J => Section1.scalarProduct W α (ω q.1 q.2))
          (chi := fun q : I × J => χ q.1 q.2)
          (horth := horth) (j := p))
    simp [hinner, mul_comm]
  calc
    Section1.scalarProduct G (σ α) (σ β) =
      Section1.scalarProduct G (σ α)
        (Section1.weightedFamilySum
          (fun p : I × J => Section1.scalarProduct W β (ω p.1 p.2))
          (fun p : I × J => χ p.1 p.2)) := by
        rw [hσβ]
    _ = Section1.scalarProduct W α
        (Section1.weightedFamilySum
          (fun p : I × J => Section1.scalarProduct W β (ω p.1 p.2))
          (fun p : I × J => ω p.1 p.2)) := hσβ_inner
    _ = Section1.scalarProduct W α β := by rw [hωexpandβ]
    _ = Section1.scalarProduct W α β := rfl

private theorem mapsVirtualCharacters_sigmaOfPF35_pf39
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : I → J → Section1.ClassFunction G}
    (_hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hsigned : ∀ i j, IsSignedIrreducibleCharacter (χ i j)) :
    MapsVirtualCharacters (sigmaOfPF35 ω χ) := by
  intro α hα
  have hint :
      ∀ p : I × J,
        ∃ z : ℤ,
          Section1.scalarProduct W α (ω p.1 p.2) = (z : ℂ) := by
    intro p
    exact scalarProduct_isVirtualCharacter_eq_int hα
      (isVirtualCharacter_of_irreducibleCharacterOnGroup
        (_hω.irreducible p.1 p.2))
  have hterm :
      ∀ p : I × J,
        Theory.Character.IsVirtualCharacter
          (Section1.scalarProduct W α (ω p.1 p.2) • χ p.1 p.2) := by
    intro p
    rcases hint p with ⟨z, hz⟩
    rw [hz]
    have hχvirt : Theory.Character.IsVirtualCharacter (χ p.1 p.2) := by
      rcases hsigned p.1 p.2 with ⟨ε, hε, ψ, hψ, hEq⟩
      rcases hε with rfl | rfl
      · simpa [hEq] using isVirtualCharacter_of_irreducibleCharacterOnGroup hψ
      · simpa [hEq] using isVirtualCharacter_neg
          (isVirtualCharacter_of_irreducibleCharacterOnGroup hψ)
    have hsmul :
        (z : ℂ) • χ p.1 p.2 =
          (z • χ p.1 p.2 : Section1.ClassFunction G) := by
      ext g
      simp [zsmul_eq_mul]
    rw [hsmul]
    exact isVirtualCharacter_zsmul_pf39 z hχvirt
  have hsum :
      Theory.Character.IsVirtualCharacter
        (Section1.weightedFamilySum
          (fun p : I × J => Section1.scalarProduct W α (ω p.1 p.2))
          (fun p : I × J => χ p.1 p.2)) := by
    unfold Section1.weightedFamilySum
    rw [show (@Finset.univ (I × J) (Fintype.ofFinite (I × J))) = (Finset.univ : Finset (I × J)) by
      ext p
      simp]
    simpa using
      isVirtualCharacter_finset_sum_pf39
        (G := G)
        (s := (Finset.univ : Finset (I × J)))
        (χ := fun p => Section1.scalarProduct W α (ω p.1 p.2) • χ p.1 p.2)
        (by
          intro p _hp
          exact hterm p)
  simpa [sigmaOfPF35] using hsum

private theorem mapsClassFunctions_sigmaOfPF35_pf39
    {G : Type u} [Group G] [Finite G]
    {W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J]
    {ω : I → J → Section1.ClassFunction W}
    {χ : I → J → Section1.ClassFunction G}
    (hsigned : ∀ i j, IsSignedIrreducibleCharacter (χ i j)) :
    MapsClassFunctions (sigmaOfPF35 ω χ) := by
  intro α _hα x g
  change
    Section1.weightedFamilySum
        (fun p : I × J => Section1.scalarProduct W α (ω p.1 p.2))
        (fun p : I × J => χ p.1 p.2) (x * g * x⁻¹) =
      Section1.weightedFamilySum
        (fun p : I × J => Section1.scalarProduct W α (ω p.1 p.2))
        (fun p : I × J => χ p.1 p.2) g
  unfold Section1.weightedFamilySum
  refine Finset.sum_congr rfl ?_
  intro p _hp
  simp [isClassFunction_of_signed_irreducible_pf39 (hsigned p.1 p.2) x g]

private theorem sigmaOfPF35_eq_inducedCF_on_CFOn_pf39
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : I → J → Section1.ClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (_horth : IsOrthonormalDoubleFamily χ)
    (_hsigned : ∀ i j, IsSignedIrreducibleCharacter (χ i j))
    (h00 : χ i0 j0 = Section1.principalCharacter G)
    (hInd : ∀ i j, i ≠ i0 → j ≠ j0 →
      Section1.inducedCF W (alphaIJ W i0 j0 ω i j) =
        Section1.principalCharacter G - χ i j0 - χ i0 j + χ i j)
    (α : Section1.ClassFunction W)
    (hα : Section2.CFOn W (cyclicTISet W1 W2 W) α) :
    sigmaOfPF35 ω χ α = Section1.inducedCF W α := by
  classical
  let σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G :=
    sigmaOfPF35 ω χ
  have hσ_omega : ∀ i j, σ (ω i j) = χ i j := by
    intro i j
    simpa [σ] using sigmaOfPF35_apply_omega ω χ hω.orthonormal i j
  have hαbasis := proposition_3_4
    (W1 := W1) (W2 := W2) (W := W)
    (I := I) (J := J) (i0 := i0) (j0 := j0) (omega := ω) h hω
  rcases hαbasis.2.2 α hα with ⟨c, rfl⟩
  have hbase :
      ∀ p : {p : I × J // p.1 ≠ i0 ∧ p.2 ≠ j0},
        σ (alphaIJ W i0 j0 ω p.1.1 p.1.2) =
          Section1.inducedCF W (alphaIJ W i0 j0 ω p.1.1 p.1.2) := by
    rintro ⟨⟨i, j⟩, hi, hj⟩
    have hσprincipal : σ (Section1.principalCharacter W) = Section1.principalCharacter G := by
      calc
        σ (Section1.principalCharacter W) = σ (ω i0 j0) := by rw [hω.principal]
        _ = χ i0 j0 := hσ_omega i0 j0
        _ = Section1.principalCharacter G := h00
    calc
      σ (alphaIJ W i0 j0 ω i j) =
          σ (Section1.principalCharacter W) - σ (ω i j0) - σ (ω i0 j) + σ (ω i j) := by
        simp [alphaIJ, map_sub, map_add]
      _ = Section1.principalCharacter G - χ i j0 - χ i0 j + χ i j := by
        rw [hσprincipal, hσ_omega i j0, hσ_omega i0 j, hσ_omega i j]
      _ = Section1.inducedCF W (alphaIJ W i0 j0 ω i j) := by
        symm
        exact hInd i j hi hj
  calc
    σ (∑ p : {p : I × J // p.1 ≠ i0 ∧ p.2 ≠ j0},
        c p • alphaIJ W i0 j0 ω p.1.1 p.1.2) =
      ∑ p : {p : I × J // p.1 ≠ i0 ∧ p.2 ≠ j0},
        c p • σ (alphaIJ W i0 j0 ω p.1.1 p.1.2) := by
          rw [map_sum]
          refine Finset.sum_congr rfl ?_
          intro p hp
          simp
    _ =
      ∑ p : {p : I × J // p.1 ≠ i0 ∧ p.2 ≠ j0},
        c p • Section1.inducedCF W (alphaIJ W i0 j0 ω p.1.1 p.1.2) := by
          refine Finset.sum_congr rfl ?_
          intro p hp
          rw [hbase p]
    _ =
      Section1.inducedCFLinear W
        (∑ p : {p : I × J // p.1 ≠ i0 ∧ p.2 ≠ j0},
          c p • alphaIJ W i0 j0 ω p.1.1 p.1.2) := by
        rw [map_sum]
        refine Finset.sum_congr rfl ?_
        intro p hp
        exact (map_smul (Section1.inducedCFLinear W) (c p)
          (alphaIJ W i0 j0 ω p.1.1 p.1.2)).symm
    _ =
      Section1.inducedCF W
        (∑ p : {p : I × J // p.1 ≠ i0 ∧ p.2 ≠ j0},
          c p • alphaIJ W i0 j0 ω p.1.1 p.1.2) := by
        rfl

private theorem agreesOnCyclicTISet_sigmaOfPF35_pf39
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : I → J → Section1.ClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (horth : IsOrthonormalDoubleFamily χ)
    (hsigned : ∀ i j, IsSignedIrreducibleCharacter (χ i j))
    (h00 : χ i0 j0 = Section1.principalCharacter G)
    (hInd : ∀ i j, i ≠ i0 → j ≠ j0 →
      Section1.inducedCF W (alphaIJ W i0 j0 ω i j) =
        Section1.principalCharacter G - χ i j0 - χ i0 j + χ i j) :
    AgreesOnCyclicTISet W1 W2 W (sigmaOfPF35 ω χ) := by
  classical
  let σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G :=
    sigmaOfPF35 ω χ
  intro α hαclass x hx
  rcases exists_alpha_basis_pf39
      (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0) (ω := ω) h hω with
    ⟨basis, hbasis⟩
  have huniv_prod :
      (@Finset.univ (I × J) (Fintype.ofFinite (I × J))) = (Finset.univ : Finset (I × J)) := by
    ext q
    simp
  have sigma_expand (β : Section1.ClassFunction W) :
      σ β =
        ∑ p : I × J, Section1.scalarProduct W β (ω p.1 p.2) • χ p.1 p.2 := by
    rw [show σ β =
      Section1.weightedFamilySum
        (fun p : I × J => Section1.scalarProduct W β (ω p.1 p.2))
        (fun p : I × J => χ p.1 p.2) by
      rfl]
    ext g
    unfold Section1.weightedFamilySum
    rw [huniv_prod]
    simp [smul_eq_mul]
  have hσ_omega : ∀ i j, σ (ω i j) = χ i j := by
    intro i j
    simpa [σ] using sigmaOfPF35_apply_omega ω χ hω.orthonormal i j
  have hexpand :
      ∀ p : {p : I × J // p.1 ≠ i0 ∧ p.2 ≠ j0},
        Section1.inducedCFLinear W (basis p : Section1.ClassFunction W) =
          ∑ q : I × J,
            Section1.scalarProduct W (basis p : Section1.ClassFunction W) (ω q.1 q.2) •
              χ q.1 q.2 := by
    intro p
    rcases p with ⟨⟨i, j⟩, hi, hj⟩
    rw [hbasis ⟨(i, j), hi, hj⟩]
    have hσprincipal : σ (Section1.principalCharacter W) = Section1.principalCharacter G := by
      calc
        σ (Section1.principalCharacter W) = σ (ω i0 j0) := by rw [hω.principal]
        _ = χ i0 j0 := hσ_omega i0 j0
        _ = Section1.principalCharacter G := h00
    calc
      Section1.inducedCFLinear W (alphaIJ W i0 j0 ω i j) =
          Section1.inducedCF W (alphaIJ W i0 j0 ω i j) := by
        rfl
      _ = Section1.principalCharacter G - χ i j0 - χ i0 j + χ i j := by
        rw [hInd i j hi hj]
      _ = σ (alphaIJ W i0 j0 ω i j) := by
        symm
        calc
          σ (alphaIJ W i0 j0 ω i j) =
              σ (Section1.principalCharacter W) - σ (ω i j0) - σ (ω i0 j) + σ (ω i j) := by
            simp [alphaIJ, map_sub, map_add]
          _ = Section1.principalCharacter G - χ i j0 - χ i0 j + χ i j := by
            rw [hσprincipal, hσ_omega i j0, hσ_omega i0 j, hσ_omega i j]
      _ =
          ∑ q : I × J,
            Section1.scalarProduct W (alphaIJ W i0 j0 ω i j) (ω q.1 q.2) •
              χ q.1 q.2 := by
        exact sigma_expand (alphaIJ W i0 j0 ω i j)
  have hωeq :
      ∀ q : I × J, ∀ y ∈ cyclicTISetSubgroup W1 W2 W,
        Section1.subgroupRestriction W (χ q.1 q.2) y = ω q.1 q.2 y := by
    intro q
    have hχclass : Section1.IsClassFunction (χ q.1 q.2) :=
      isClassFunction_of_signed_irreducible_pf39 (hsigned q.1 q.2)
    have hfrob_q :
        ∀ α0,
          Section1.scalarProduct G (Section1.inducedCFLinear W α0) (χ q.1 q.2) =
            Section1.scalarProduct W α0
              (Section1.subgroupRestriction W (χ q.1 q.2)) := by
      intro α0
      rw [Section1.inducedCFLinear_apply]
      exact Section1.scalarProduct_inducedCF_left W α0 (χ q.1 q.2) hχclass
    have hEq :
        ∀ y ∈ cyclicTISetSubgroup W1 W2 W,
          Section1.subgroupRestriction W (χ q.1 q.2) y =
            (∑ k : I × J, (if k = q then (1 : ℂ) else 0) • ω k.1 k.2) y := by
      refine (proposition_1_3_a_special_pf32
        (basis := basis)
        (chi := fun k : I × J => ω k.1 k.2)
        (ind := Section1.inducedCFLinear W)
        (mu := χ q.1 q.2)
        (hfrob := hfrob_q)
        (d := fun k : I × J => if k = q then (1 : ℂ) else 0)).mpr ?_
      intro j
      calc
        ∑ k : I × J,
            Section1.scalarProduct W (basis j : Section1.ClassFunction W) (ω k.1 k.2) *
              star (if k = q then (1 : ℂ) else 0) =
          ∑ k : I × J,
            Section1.scalarProduct W (basis j : Section1.ClassFunction W) (ω k.1 k.2) *
              Section1.scalarProduct G (χ k.1 k.2) (χ q.1 q.2) := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            by_cases hkq : k = q
            · have hqq :
                  Section1.scalarProduct G (χ q.1 q.2) (χ q.1 q.2) = 1 := by
                simpa using horth q q
              simp [hkq, hqq]
            · have hk0 :
                  Section1.scalarProduct G (χ k.1 k.2) (χ q.1 q.2) = 0 := by
                simpa [hkq] using horth k q
              simp [hkq, hk0]
        _ = Section1.scalarProduct G
            (∑ k : I × J,
              Section1.scalarProduct W (basis j : Section1.ClassFunction W) (ω k.1 k.2) •
                χ k.1 k.2) (χ q.1 q.2) := by
            rw [scalarProduct_sum_left_pf32]
        _ = Section1.scalarProduct G
            (Section1.inducedCFLinear W (basis j : Section1.ClassFunction W))
            (χ q.1 q.2) := by
            rw [hexpand j]
    have hs :
        (∑ k : I × J, (if k = q then (1 : ℂ) else 0) • ω k.1 k.2) = ω q.1 q.2 := by
      simp
    intro y hy
    have hy' := hEq y hy
    exact hy'.trans (congrArg (fun f : Section1.ClassFunction W => f y) hs)
  have hσeq :
      ∀ y ∈ cyclicTISetSubgroup W1 W2 W, σ α y = α y := by
    intro y hy
    have hσα' :
        σ α =
          Section1.weightedFamilySum
            (fun q : I × J => Section1.scalarProduct W α (ω q.1 q.2))
            (fun q : I × J => χ q.1 q.2) := by
      rfl
    rw [hσα']
    change Section1.subgroupRestriction W
      (Section1.weightedFamilySum
        (fun q : I × J => Section1.scalarProduct W α (ω q.1 q.2))
        (fun q : I × J => χ q.1 q.2)) y = α y
    have hsumω :
        Section1.subgroupRestriction W
          (Section1.weightedFamilySum
            (fun q : I × J => Section1.scalarProduct W α (ω q.1 q.2))
            (fun q : I × J => χ q.1 q.2)) y =
          Section1.weightedFamilySum
            (fun q : I × J => Section1.scalarProduct W α (ω q.1 q.2))
            (fun q : I × J => ω q.1 q.2) y := by
      simp [Section1.subgroupRestriction, Section1.weightedFamilySum]
      refine Finset.sum_congr rfl ?_
      intro q hq
      exact congrArg
        (fun z : ℂ => Section1.scalarProduct W α (ω q.1 q.2) * z)
        (by simpa [Section1.subgroupRestriction] using hωeq q y hy)
    rw [hsumω]
    exact congrFun
      (weightedFamilySum_eq_of_inner_omega_pf39
        (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (i0 := i0) (j0 := j0) (ω := ω) h hω α) y
  simpa [Section1.subgroupRestriction] using
    hσeq ⟨x, cyclicTISet_subset W1 W2 W hx⟩ hx

public theorem vanishesOn_of_orthogonal_sigmaOfPF35_basis_pf39
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : I → J → Section1.ClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h00 : χ i0 j0 = Section1.principalCharacter G)
    (hInd : ∀ i j, i ≠ i0 → j ≠ j0 →
      Section1.inducedCF W (alphaIJ W i0 j0 ω i j) =
        Section1.principalCharacter G - χ i j0 - χ i0 j + χ i j)
    {ψ : Section1.ClassFunction G}
    (hψclass : Section1.IsClassFunction ψ)
    (horth_to_zero :
      ∀ q : I × J, Section1.scalarProduct G (χ q.1 q.2) ψ = 0) :
    VanishesOn ψ (cyclicTISet W1 W2 W) := by
  classical
  let σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G :=
    sigmaOfPF35 ω χ
  rcases exists_alpha_basis_pf39
      (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0) (ω := ω) h hω with
    ⟨basis, hbasis⟩
  have huniv_prod :
      (@Finset.univ (I × J) (Fintype.ofFinite (I × J))) = (Finset.univ : Finset (I × J)) := by
    ext q
    simp
  have sigma_expand (β : Section1.ClassFunction W) :
      σ β =
        ∑ p : I × J, Section1.scalarProduct W β (ω p.1 p.2) • χ p.1 p.2 := by
    rw [show σ β =
      Section1.weightedFamilySum
        (fun p : I × J => Section1.scalarProduct W β (ω p.1 p.2))
        (fun p : I × J => χ p.1 p.2) by
      rfl]
    ext g
    unfold Section1.weightedFamilySum
    rw [huniv_prod]
    simp [smul_eq_mul]
  have hσ_omega : ∀ i j, σ (ω i j) = χ i j := by
    intro i j
    simpa [σ] using sigmaOfPF35_apply_omega ω χ hω.orthonormal i j
  have hexpand :
      ∀ p : {p : I × J // p.1 ≠ i0 ∧ p.2 ≠ j0},
        Section1.inducedCFLinear W (basis p : Section1.ClassFunction W) =
          ∑ q : I × J,
            Section1.scalarProduct W (basis p : Section1.ClassFunction W) (ω q.1 q.2) •
              χ q.1 q.2 := by
    intro p
    rcases p with ⟨⟨i, j⟩, hi, hj⟩
    rw [hbasis ⟨(i, j), hi, hj⟩]
    calc
      Section1.inducedCFLinear W (alphaIJ W i0 j0 ω i j) =
          Section1.inducedCF W (alphaIJ W i0 j0 ω i j) := by
        rfl
      _ = Section1.principalCharacter G - χ i j0 - χ i0 j + χ i j := by
        rw [hInd i j hi hj]
      _ = σ (alphaIJ W i0 j0 ω i j) := by
        symm
        have hσprincipal : σ (Section1.principalCharacter W) = Section1.principalCharacter G := by
          calc
            σ (Section1.principalCharacter W) = σ (ω i0 j0) := by rw [hω.principal]
            _ = χ i0 j0 := hσ_omega i0 j0
            _ = Section1.principalCharacter G := h00
        calc
          σ (alphaIJ W i0 j0 ω i j) =
              σ (Section1.principalCharacter W) - σ (ω i j0) - σ (ω i0 j) + σ (ω i j) := by
            simp [alphaIJ, map_sub, map_add]
          _ = Section1.principalCharacter G - χ i j0 - χ i0 j + χ i j := by
            rw [hσprincipal, hσ_omega i j0, hσ_omega i0 j, hσ_omega i j]
      _ =
          ∑ q : I × J,
            Section1.scalarProduct W (alphaIJ W i0 j0 ω i j) (ω q.1 q.2) •
              χ q.1 q.2 := by
        exact sigma_expand (alphaIJ W i0 j0 ω i j)
  have hzero :
      ∀ y ∈ cyclicTISetSubgroup W1 W2 W,
        Section1.subgroupRestriction W ψ y = 0 := by
    have hfrob_ψ :
        ∀ α0,
          Section1.scalarProduct G (Section1.inducedCFLinear W α0) ψ =
            Section1.scalarProduct W α0 (Section1.subgroupRestriction W ψ) := by
      intro α0
      rw [Section1.inducedCFLinear_apply]
      exact Section1.scalarProduct_inducedCF_left W α0 ψ hψclass
    have hzero' :
        ∀ y ∈ cyclicTISetSubgroup W1 W2 W,
          Section1.subgroupRestriction W ψ y =
            (∑ i : I × J, (0 : ℂ) • ω i.1 i.2) y := by
      refine (proposition_1_3_a_special_pf32
        (basis := basis)
        (chi := fun q : I × J => ω q.1 q.2)
        (ind := Section1.inducedCFLinear W)
        (mu := ψ)
        (hfrob := hfrob_ψ)
        (d := fun _ : I × J => 0)).mpr ?_
      intro j
      calc
        ∑ i : I × J,
            Section1.scalarProduct W (basis j : Section1.ClassFunction W) (ω i.1 i.2) *
              star (0 : ℂ) = 0 := by
            simp
        _ = Section1.scalarProduct G
            (∑ i : I × J,
              Section1.scalarProduct W (basis j : Section1.ClassFunction W) (ω i.1 i.2) •
                χ i.1 i.2) ψ := by
            rw [scalarProduct_sum_left_pf32]
            simp [horth_to_zero]
        _ = Section1.scalarProduct G
            (Section1.inducedCFLinear W (basis j : Section1.ClassFunction W)) ψ := by
            rw [hexpand j]
    have hs0 : (∑ i : I × J, (0 : ℂ) • ω i.1 i.2) = 0 := by
      simp
    intro y hy
    have hy' := hzero' y hy
    simpa [hs0] using hy'
  intro g hg
  have hgW : g ∈ (W : Set G) := cyclicTISet_subset W1 W2 W hg
  have hval := hzero ⟨g, hgW⟩ hg
  simpa [Section1.subgroupRestriction] using hval

private theorem vanishesOn_outside_image_sigmaOfPF35_pf39
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : I → J → Section1.ClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (horth : IsOrthonormalDoubleFamily χ)
    (hsigned : ∀ i j, IsSignedIrreducibleCharacter (χ i j))
    (h00 : χ i0 j0 = Section1.principalCharacter G)
    (hInd : ∀ i j, i ≠ i0 → j ≠ j0 →
      Section1.inducedCF W (alphaIJ W i0 j0 ω i j) =
        Section1.principalCharacter G - χ i j0 - χ i0 j + χ i j)
    {ψ : Section1.ClassFunction G}
    (hψ : Section1.IsIrreducibleCharacterOnGroup ψ)
    (hnot : ψ ∉ classFunctionImage (sigmaOfPF35 ω χ)) :
    VanishesOn ψ (cyclicTISet W1 W2 W) := by
  classical
  let σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G :=
    sigmaOfPF35 ω χ
  rcases exists_alpha_basis_pf39
      (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0) (ω := ω) h hω with
    ⟨basis, hbasis⟩
  have huniv_prod :
      (@Finset.univ (I × J) (Fintype.ofFinite (I × J))) = (Finset.univ : Finset (I × J)) := by
    ext q
    simp
  have sigma_expand (β : Section1.ClassFunction W) :
      σ β =
        ∑ p : I × J, Section1.scalarProduct W β (ω p.1 p.2) • χ p.1 p.2 := by
    rw [show σ β =
      Section1.weightedFamilySum
        (fun p : I × J => Section1.scalarProduct W β (ω p.1 p.2))
        (fun p : I × J => χ p.1 p.2) by
      rfl]
    ext g
    unfold Section1.weightedFamilySum
    rw [huniv_prod]
    simp [smul_eq_mul]
  have hσ_omega : ∀ i j, σ (ω i j) = χ i j := by
    intro i j
    simpa [σ] using sigmaOfPF35_apply_omega ω χ hω.orthonormal i j
  have hexpand :
      ∀ p : {p : I × J // p.1 ≠ i0 ∧ p.2 ≠ j0},
        Section1.inducedCFLinear W (basis p : Section1.ClassFunction W) =
          ∑ q : I × J,
            Section1.scalarProduct W (basis p : Section1.ClassFunction W) (ω q.1 q.2) •
              χ q.1 q.2 := by
    intro p
    rcases p with ⟨⟨i, j⟩, hi, hj⟩
    rw [hbasis ⟨(i, j), hi, hj⟩]
    calc
      Section1.inducedCFLinear W (alphaIJ W i0 j0 ω i j) =
          Section1.inducedCF W (alphaIJ W i0 j0 ω i j) := by
        rfl
      _ = Section1.principalCharacter G - χ i j0 - χ i0 j + χ i j := by
        rw [hInd i j hi hj]
      _ = σ (alphaIJ W i0 j0 ω i j) := by
        symm
        have hσprincipal : σ (Section1.principalCharacter W) = Section1.principalCharacter G := by
          calc
            σ (Section1.principalCharacter W) = σ (ω i0 j0) := by rw [hω.principal]
            _ = χ i0 j0 := hσ_omega i0 j0
            _ = Section1.principalCharacter G := h00
        calc
          σ (alphaIJ W i0 j0 ω i j) =
              σ (Section1.principalCharacter W) - σ (ω i j0) - σ (ω i0 j) + σ (ω i j) := by
            simp [alphaIJ, map_sub, map_add]
          _ = Section1.principalCharacter G - χ i j0 - χ i0 j + χ i j := by
            rw [hσprincipal, hσ_omega i j0, hσ_omega i0 j, hσ_omega i j]
      _ =
          ∑ q : I × J,
            Section1.scalarProduct W (alphaIJ W i0 j0 ω i j) (ω q.1 q.2) •
              χ q.1 q.2 := by
        exact sigma_expand (alphaIJ W i0 j0 ω i j)
  have hωeq :
      ∀ q : I × J, ∀ y ∈ cyclicTISetSubgroup W1 W2 W,
        Section1.subgroupRestriction W (χ q.1 q.2) y = ω q.1 q.2 y := by
    intro q y hy
    have hy' : (y : G) ∈ cyclicTISet W1 W2 W := by
      simpa [cyclicTISetSubgroup] using hy
    have hσV :=
      agreesOnCyclicTISet_sigmaOfPF35_pf39
        (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω horth hsigned h00 hInd
    have hval := hσV (ω q.1 q.2) (hω.is_class q.1 q.2) (y : G) hy'
    simpa [σ, Section1.subgroupRestriction, hσ_omega q.1 q.2] using hval
  have horth_to_zero :
      ∀ q : I × J, Section1.scalarProduct G (χ q.1 q.2) ψ = 0 := by
    intro q
    by_contra hneq
    have hin : ψ ∈ classFunctionImage σ := by
      have hsign := hsigned q.1 q.2
      rcases (scalarProduct_signed_irreducible_ne_zero_iff_pf39 hsign hψ).1 hneq with
        ⟨ε, hε, hEq⟩
      rcases hε with rfl | rfl
      · refine ⟨⟨ω q.1 q.2, hω.is_class q.1 q.2⟩, ?_⟩
        simpa [hEq] using hσ_omega q.1 q.2
      · have hnegclass : Section1.IsClassFunction (-ω q.1 q.2) := by
          intro x g
          simp [hω.is_class q.1 q.2 x g]
        refine ⟨⟨-ω q.1 q.2, hnegclass⟩, ?_⟩
        change σ (-ω q.1 q.2) = ψ
        rw [map_neg, hσ_omega q.1 q.2]
        simp [hEq]
    exact hnot hin
  have hzero :
      ∀ y ∈ cyclicTISetSubgroup W1 W2 W,
        Section1.subgroupRestriction W ψ y = 0 := by
    have hψclass : Section1.IsClassFunction ψ :=
      isClassFunction_of_irreducibleCharacterOnGroup_pf39 hψ
    have hfrob_ψ :
        ∀ α0,
          Section1.scalarProduct G (Section1.inducedCFLinear W α0) ψ =
            Section1.scalarProduct W α0 (Section1.subgroupRestriction W ψ) := by
      intro α0
      rw [Section1.inducedCFLinear_apply]
      exact Section1.scalarProduct_inducedCF_left W α0 ψ hψclass
    have hzero' :
        ∀ y ∈ cyclicTISetSubgroup W1 W2 W,
          Section1.subgroupRestriction W ψ y =
            (∑ i : I × J, (0 : ℂ) • ω i.1 i.2) y := by
      refine (proposition_1_3_a_special_pf32
        (basis := basis)
        (chi := fun q : I × J => ω q.1 q.2)
        (ind := Section1.inducedCFLinear W)
        (mu := ψ)
        (hfrob := hfrob_ψ)
        (d := fun _ : I × J => 0)).mpr ?_
      intro j
      calc
        ∑ i : I × J,
            Section1.scalarProduct W (basis j : Section1.ClassFunction W) (ω i.1 i.2) *
              star (0 : ℂ) = 0 := by
            simp
        _ = Section1.scalarProduct G
            (∑ i : I × J,
              Section1.scalarProduct W (basis j : Section1.ClassFunction W) (ω i.1 i.2) •
                χ i.1 i.2) ψ := by
            rw [scalarProduct_sum_left_pf32]
            simp [horth_to_zero]
        _ = Section1.scalarProduct G
            (Section1.inducedCFLinear W (basis j : Section1.ClassFunction W)) ψ := by
            rw [hexpand j]
    have hs0 : (∑ i : I × J, (0 : ℂ) • ω i.1 i.2) = 0 := by
      simp
    intro y hy
    have hy' := hzero' y hy
    simpa [hs0] using hy'
  intro g hg
  have hgW : g ∈ (W : Set G) := cyclicTISet_subset W1 W2 W hg
  have hval := hzero ⟨g, hgW⟩ hg
  simpa [Section1.subgroupRestriction] using hval

private theorem theorem_3_2_map_statement_sigmaOfPF35_pf39
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : I → J → Section1.ClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (horth : IsOrthonormalDoubleFamily χ)
    (hsigned : ∀ i j, IsSignedIrreducibleCharacter (χ i j))
    (h00 : χ i0 j0 = Section1.principalCharacter G)
    (hInd : ∀ i j, i ≠ i0 → j ≠ j0 →
      Section1.inducedCF W (alphaIJ W i0 j0 ω i j) =
        Section1.principalCharacter G - χ i j0 - χ i0 j + χ i j) :
    theorem_3_2_map_statement W1 W2 W (sigmaOfPF35 ω χ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact isCFLinearIsometry_sigmaOfPF35_pf39
      (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω horth hsigned h00 hInd
  · exact mapsVirtualCharacters_sigmaOfPF35_pf39
      (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) hω hsigned
  · intro α hα
    exact sigmaOfPF35_eq_inducedCF_on_CFOn_pf39
      (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω horth hsigned h00 hInd α hα
  · exact mapsClassFunctions_sigmaOfPF35_pf39 (ω := ω) (χ := χ) hsigned
  · simpa [hω.principal, h00] using
      sigmaOfPF35_apply_omega ω χ hω.orthonormal i0 j0
  · exact agreesOnCyclicTISet_sigmaOfPF35_pf39
      (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω horth hsigned h00 hInd
  · intro ψ hψ hnot
    exact vanishesOn_outside_image_sigmaOfPF35_pf39
      (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω horth hsigned h00 hInd hψ hnot

/--
If a linear map agrees with the PF `(3.5)` model map on every `ωᵢⱼ`, then it
is definitionally the same linear map as `sigmaOfPF35`.
-/
public theorem sigma_eq_sigmaOfPF35_of_sigma_eq_omega_pf39
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {χ : I → J → Section1.ClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hσeq : ∀ i j, σ (ω i j) = χ i j) :
    σ = sigmaOfPF35 ω χ := by
  ext α g
  have huniv_prod :
      (@Finset.univ (I × J) (Fintype.ofFinite (I × J))) =
        (Finset.univ : Finset (I × J)) := by
    ext q
    simp
  have hα := weightedFamilySum_eq_of_inner_omega_pf39
    (W1 := W1) (W2 := W2) (W := W)
    (I := I) (J := J) (i0 := i0) (j0 := j0) (ω := ω) h hω α
  calc
    σ α g = σ (Section1.weightedFamilySum
        (fun p : I × J => Section1.scalarProduct W α (ω p.1 p.2))
        (fun p : I × J => ω p.1 p.2)) g := by rw [hα]
    _ = sigmaOfPF35 ω χ α g := by
      dsimp [sigmaOfPF35, Section1.weightedFamilySum]
      have hweighted :
          Section1.weightedFamilySum
            (fun p : I × J => Section1.scalarProduct W α (ω p.1 p.2))
            (fun p : I × J => ω p.1 p.2) =
          ∑ p : I × J, Section1.scalarProduct W α (ω p.1 p.2) • ω p.1 p.2 := by
        ext x
        simp [Section1.weightedFamilySum, Finset.sum_apply, huniv_prod]
      rw [hweighted, map_sum]
      simp [hσeq, huniv_prod]


/-- A PF `(3.2)` map and a Section `(3.3)` table determine the explicit PF
`(3.5)` data by taking `χᵢⱼ = σ(ωᵢⱼ)`. This is the data-construction step
used before invoking PF `(3.9)`. -/
public theorem pf35_data_of_theorem_3_2_map_statement
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (hσ : theorem_3_2_map_statement W1 W2 W σ) :
    ∃ χ : I → J → Section1.ClassFunction G,
      IsOrthonormalDoubleFamily χ ∧
        (∀ i j, IsSignedIrreducibleCharacter (χ i j)) ∧
          χ i0 j0 = Section1.principalCharacter G ∧
            (∀ i j, i ≠ i0 → j ≠ j0 →
              Section1.inducedCF W (alphaIJ W i0 j0 ω i j) =
                Section1.principalCharacter G - χ i j0 - χ i0 j + χ i j) ∧
              ∀ i j, σ (ω i j) = χ i j := by
  rcases hσ with ⟨hisom, hvirt, hind, _hclass, hprincipal, _hagrees, _hvanish⟩
  let χ : I → J → Section1.ClassFunction G := fun i j => σ (ω i j)
  refine ⟨χ, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    calc
      Section1.scalarProduct G (χ x.1 x.2) (χ y.1 y.2) =
          Section1.scalarProduct W (ω x.1 x.2) (ω y.1 y.2) :=
        hisom _ _ (hω.is_class x.1 x.2) (hω.is_class y.1 y.2)
      _ = if x = y then 1 else 0 := by
        simpa using hω.orthonormal x y
  · intro i j
    have hvirtW : Theory.Character.IsVirtualCharacter (ω i j) :=
      isVirtualCharacter_of_irreducibleCharacterOnGroup (hω.irreducible i j)
    have hvirtG : Theory.Character.IsVirtualCharacter (σ (ω i j)) :=
      hvirt (ω i j) hvirtW
    have hself :
        Section1.scalarProduct G (σ (ω i j)) (σ (ω i j)) = 1 := by
      calc
        Section1.scalarProduct G (σ (ω i j)) (σ (ω i j)) =
            Section1.scalarProduct W (ω i j) (ω i j) :=
          hisom _ _ (hω.is_class i j) (hω.is_class i j)
        _ = 1 := by
          simpa using hω.orthonormal (i, j) (i, j)
    exact signed_irreducible_of_virtual_norm_one_pf39 hvirtG hself
  · change σ (ω i0 j0) = Section1.principalCharacter G
    rw [hω.principal]
    exact hprincipal
  · intro i j hi hj
    change Section1.inducedCF W (alphaIJ W i0 j0 ω i j) =
      Section1.principalCharacter G - σ (ω i j0) - σ (ω i0 j) + σ (ω i j)
    have hcf :
        Section2.CFOn W (cyclicTISet W1 W2 W)
          (alphaIJ W i0 j0 ω i j) :=
      alphaIJ_CFOn_cyclicTISet W1 W2 W I J i0 j0 ω hω i j
    calc
      Section1.inducedCF W (alphaIJ W i0 j0 ω i j) =
          σ (alphaIJ W i0 j0 ω i j) := (hind _ hcf).symm
      _ = σ (Section1.principalCharacter W) - σ (ω i j0) -
            σ (ω i0 j) + σ (ω i j) := by
        simp [alphaIJ, map_sub, map_add]
      _ = Section1.principalCharacter G - σ (ω i j0) -
            σ (ω i0 j) + σ (ω i j) := by
        rw [hprincipal]
  · intro i j
    rfl

public theorem vanishesOn_of_orthogonal_theorem_3_2_basis
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (hσ : theorem_3_2_map_statement W1 W2 W σ)
    {ψ : Section1.ClassFunction G}
    (hψclass : Section1.IsClassFunction ψ)
    (horth_basis :
      ∀ i j, Section1.scalarProduct G ψ (σ (ω i j)) = 0) :
    VanishesOn ψ (cyclicTISet W1 W2 W) := by
  classical
  rcases pf35_data_of_theorem_3_2_map_statement hω σ hσ with
    ⟨χ, _horth, _hsigned, h00, hInd, hσeq⟩
  have horth_to_zero :
      ∀ q : I × J, Section1.scalarProduct G (χ q.1 q.2) ψ = 0 := by
    intro q
    have hzero : Section1.scalarProduct G ψ (χ q.1 q.2) = 0 := by
      simpa [hσeq q.1 q.2] using horth_basis q.1 q.2
    simpa [Section1.scalarProduct_star_swap] using congrArg star hzero
  exact vanishesOn_of_orthogonal_sigmaOfPF35_basis_pf39
    (W1 := W1) (W2 := W2) (W := W)
    (I := I) (J := J) (i0 := i0) (j0 := j0)
    (ω := ω) (χ := χ) h hω h00 hInd hψclass horth_to_zero

/-! ### The PF `(3.8)` signed-difference uniqueness corollary -/

private def cfNormSq_pf39
    {G : Type u} [Group G] [Finite G]
    (φ : Section1.ClassFunction G) : ℝ :=
  Complex.re (Section1.scalarProduct G φ φ)

private theorem cfNormSq_eq_inv_card_mul_sum_normSq_pf39
    {G : Type u} [Group G] [Finite G]
    (φ : Section1.ClassFunction G) :
    cfNormSq_pf39 φ = (Nat.card G : ℝ)⁻¹ * ∑ g : G, Complex.normSq (φ g) := by
  unfold cfNormSq_pf39 Section1.scalarProduct
  have hcast : ((Nat.card G : ℂ)⁻¹) = (((Nat.card G : ℝ)⁻¹ : ℝ) : ℂ) := by
    simp
  rw [hcast, Complex.re_ofReal_mul, Complex.re_sum]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro g _hg
  calc
    Complex.re (φ g * star (φ g)) = Complex.re (star (φ g) * φ g) := by
      rw [mul_comm]
    _ = Complex.re ((Complex.normSq (φ g) : ℝ) : ℂ) := by
      congr 1
      simpa using (Complex.normSq_eq_conj_mul_self (z := φ g)).symm
    _ = Complex.normSq (φ g) := by simp

private theorem cfNormSq_nonneg_pf39
    {G : Type u} [Group G] [Finite G]
    (φ : Section1.ClassFunction G) :
    0 ≤ cfNormSq_pf39 φ := by
  rw [cfNormSq_eq_inv_card_mul_sum_normSq_pf39]
  exact mul_nonneg (by positivity)
    (Finset.sum_nonneg (fun g _hg => Complex.normSq_nonneg (φ g)))

private theorem cfNormSq_eq_zero_pf39
    {G : Type u} [Group G] [Finite G]
    {φ : Section1.ClassFunction G}
    (hφ : cfNormSq_pf39 φ = 0) :
    φ = 0 := by
  rw [cfNormSq_eq_inv_card_mul_sum_normSq_pf39] at hφ
  have hcardNat : 0 < Nat.card G := Nat.card_pos
  have hcardReal : 0 < (Nat.card G : ℝ) := by exact_mod_cast hcardNat
  have hcard : 0 < (Nat.card G : ℝ)⁻¹ := inv_pos.mpr hcardReal
  have hsumZero : (∑ g : G, Complex.normSq (φ g)) = 0 := by
    nlinarith
  have hzeroAll : ∀ g ∈ (Finset.univ : Finset G), Complex.normSq (φ g) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun g _hg => Complex.normSq_nonneg (φ g))).mp hsumZero
  ext g
  simpa using (Complex.normSq_eq_zero.mp (hzeroAll g (Finset.mem_univ g)))

private theorem scalarProduct_add_right_pf39
    {G : Type*} [Finite G]
    (φ ψ₁ ψ₂ : Section1.ClassFunction G) :
    Section1.scalarProduct G φ (ψ₁ + ψ₂) =
      Section1.scalarProduct G φ ψ₁ + Section1.scalarProduct G φ ψ₂ := by
  simp [Section1.scalarProduct, mul_add, Finset.sum_add_distrib]

private theorem scalarProduct_sub_left_pf39
    {G : Type*} [Finite G]
    (φ₁ φ₂ ψ : Section1.ClassFunction G) :
    Section1.scalarProduct G (φ₁ - φ₂) ψ =
      Section1.scalarProduct G φ₁ ψ - Section1.scalarProduct G φ₂ ψ := by
  rw [sub_eq_add_neg, Section1.scalarProduct_add_left]
  rw [show -φ₂ = (-1 : ℂ) • φ₂ by ext g; simp]
  rw [Section1.scalarProduct_smul_left]
  ring

private theorem scalarProduct_sub_right_pf39
    {G : Type*} [Finite G]
    (φ ψ₁ ψ₂ : Section1.ClassFunction G) :
    Section1.scalarProduct G φ (ψ₁ - ψ₂) =
      Section1.scalarProduct G φ ψ₁ - Section1.scalarProduct G φ ψ₂ := by
  rw [sub_eq_add_neg, scalarProduct_add_right_pf39]
  rw [show -ψ₂ = (-1 : ℂ) • ψ₂ by ext g; simp]
  rw [Section1.scalarProduct_smul_right]
  simp [sub_eq_add_neg]

private theorem cfNormSq_add_eq_add_of_orthogonal_pf39
    {G : Type*} [Group G] [Finite G]
    {φ ψ : Section1.ClassFunction G}
    (hφψ : Section1.scalarProduct G φ ψ = 0)
    (hψφ : Section1.scalarProduct G ψ φ = 0) :
    cfNormSq_pf39 (φ + ψ) = cfNormSq_pf39 φ + cfNormSq_pf39 ψ := by
  unfold cfNormSq_pf39
  rw [Section1.scalarProduct_add_left, scalarProduct_add_right_pf39,
    scalarProduct_add_right_pf39, hφψ, hψφ]
  norm_num


private theorem cfNormSq_smul_pf39
    {G : Type*} [Group G] [Finite G]
    (z : ℂ) (φ : Section1.ClassFunction G) :
    cfNormSq_pf39 (z • φ) = Complex.normSq z * cfNormSq_pf39 φ := by
  unfold cfNormSq_pf39
  rw [Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_right]
  have hnorm : z * star z = (Complex.normSq z : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self]
    simp [mul_comm]
  rw [← mul_assoc, hnorm]
  simp

private theorem one_le_normSq_intCast_of_ne_zero_pf39
    (z : ℤ) (hz : (z : ℂ) ≠ 0) :
    (1 : ℝ) ≤ Complex.normSq (z : ℂ) := by
  have hz0 : z ≠ 0 := by
    intro hz0
    apply hz
    simp [hz0]
  have hzz : (1 : ℤ) ≤ z * z := by
    have hpos : 0 < z * z := (mul_self_pos).2 hz0
    omega
  have hreal : (1 : ℝ) ≤ (z : ℝ) * (z : ℝ) := by exact_mod_cast hzz
  simpa [Complex.normSq, pow_two] using hreal

private theorem cfNormSq_weightedFamilySum_orthonormal_eq_sum_normSq_pf39
    {G ι : Type*} [Group G] [Finite G] [Fintype ι] [DecidableEq ι]
    (w : ι → ℂ) (χ : ι → Section1.ClassFunction G)
    (horth : ∀ i j : ι,
      Section1.scalarProduct G (χ i) (χ j) = if i = j then 1 else 0) :
    cfNormSq_pf39 (Section1.weightedFamilySum w χ) =
      ∑ i : ι, Complex.normSq (w i) := by
  classical
  have hself :
      Section1.scalarProduct G (Section1.weightedFamilySum w χ)
          (Section1.weightedFamilySum w χ) =
        ∑ i : ι, star (w i) * w i := by
    calc
      Section1.scalarProduct G (Section1.weightedFamilySum w χ)
          (Section1.weightedFamilySum w χ) =
          ∑ i : ι, star (w i) *
            Section1.scalarProduct G (Section1.weightedFamilySum w χ) (χ i) := by
              rw [Section1.scalarProduct_weightedFamilySum_right]
              apply Finset.sum_congr
              · ext i
                simp
              · intro i _hi
                rfl
      _ = ∑ i : ι, star (w i) * w i := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [Section1.scalarProduct_weightedFamilySum_left_orthonormal w χ horth i]
  unfold cfNormSq_pf39
  rw [hself, Complex.re_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  have hnorm : star (w i) * w i = ((Complex.normSq (w i) : ℝ) : ℂ) := by
    simp [Complex.normSq_eq_conj_mul_self]
  rw [hnorm]
  simp

private theorem finite_orthonormal_virtual_coeff_support_card_le_two_pf39
    {G ι : Type*} [Group G] [Finite G] [Fintype ι] [DecidableEq ι]
    (χ : ι → Section1.ClassFunction G)
    (horth : ∀ i j : ι,
      Section1.scalarProduct G (χ i) (χ j) = if i = j then 1 else 0)
    (hχvirt : ∀ i, Theory.Character.IsVirtualCharacter (χ i))
    {Y : Section1.ClassFunction G}
    (hYvirt : Theory.Character.IsVirtualCharacter Y)
    (hYself : Section1.scalarProduct G Y Y = 2) :
    Fintype.card {i : ι // Section1.scalarProduct G Y (χ i) ≠ 0} ≤ 2 := by
  classical
  let nz : Finset ι :=
    Finset.univ.filter fun i : ι => Section1.scalarProduct G Y (χ i) ≠ 0
  let w : ι → ℂ := fun i => Section1.scalarProduct G Y (χ i)
  let P : Section1.ClassFunction G := Section1.weightedFamilySum w χ
  let R : Section1.ClassFunction G := Y - P
  have hPχ : ∀ i : ι, Section1.scalarProduct G P (χ i) = w i := by
    intro i
    dsimp [P]
    exact Section1.scalarProduct_weightedFamilySum_left_orthonormal w χ horth i
  have hRχ : ∀ i : ι, Section1.scalarProduct G R (χ i) = 0 := by
    intro i
    dsimp [R]
    rw [scalarProduct_sub_left_pf39, hPχ i]
    simp [w]
  have hRP : Section1.scalarProduct G R P = 0 := by
    dsimp [P]
    rw [Section1.scalarProduct_weightedFamilySum_right]
    refine Finset.sum_eq_zero ?_
    intro i _hi
    rw [hRχ i]
    simp
  have hPR : Section1.scalarProduct G P R = 0 := by
    simpa [Section1.scalarProduct_star_swap] using congrArg star hRP
  have hdecomp : Y = R + P := by
    dsimp [R, P]
    ext g
    simp [Pi.sub_apply, Pi.add_apply]
  have hnorm_decomp :
      cfNormSq_pf39 Y = cfNormSq_pf39 R + cfNormSq_pf39 P := by
    rw [hdecomp]
    exact cfNormSq_add_eq_add_of_orthogonal_pf39 hRP hPR
  have hYnorm : cfNormSq_pf39 Y = 2 := by simp [cfNormSq_pf39, hYself]
  have hPnorm_le : cfNormSq_pf39 P ≤ 2 := by
    have hRnonneg : 0 ≤ cfNormSq_pf39 R := cfNormSq_nonneg_pf39 R
    rw [hYnorm] at hnorm_decomp
    nlinarith
  have hPnorm : cfNormSq_pf39 P = ∑ i : ι, Complex.normSq (w i) := by
    dsimp [P]
    exact cfNormSq_weightedFamilySum_orthonormal_eq_sum_normSq_pf39 w χ horth
  have hterms : ∀ i ∈ nz, (1 : ℝ) ≤ Complex.normSq (w i) := by
    intro i hi
    have hi_ne : Section1.scalarProduct G Y (χ i) ≠ 0 := by
      change i ∈ Finset.univ.filter
        (fun i : ι => Section1.scalarProduct G Y (χ i) ≠ 0) at hi
      exact (Finset.mem_filter.mp hi).2
    rcases Section3.scalarProduct_isVirtualCharacter_eq_int
        hYvirt (hχvirt i) with ⟨z, hz⟩
    have hz_ne : (z : ℂ) ≠ 0 := by
      intro hz0
      exact hi_ne (by simpa [hz] using hz0)
    dsimp [w]
    rw [hz]
    exact one_le_normSq_intCast_of_ne_zero_pf39 z hz_ne
  have hcard_le_sum_nz :
      (nz.card : ℝ) ≤ ∑ i ∈ nz, Complex.normSq (w i) := by
    calc
      (nz.card : ℝ) = ∑ _i ∈ nz, (1 : ℝ) := by simp
      _ ≤ ∑ i ∈ nz, Complex.normSq (w i) :=
        Finset.sum_le_sum (fun i hi => hterms i hi)
  have hsum_nz_le_univ :
      ∑ i ∈ nz, Complex.normSq (w i) ≤
        ∑ i : ι, Complex.normSq (w i) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (by intro i hi; simp)
      (by intro i _hiuniv _hinz; exact Complex.normSq_nonneg (w i))
  have hcard_real_le_two : (nz.card : ℝ) ≤ 2 := by
    rw [← hPnorm] at hsum_nz_le_univ
    nlinarith
  have hcard_nat : nz.card ≤ 2 := by exact_mod_cast hcard_real_le_two
  have hcard_eq :
      Fintype.card {i : ι // Section1.scalarProduct G Y (χ i) ≠ 0} = nz.card := by
    dsimp [nz]
    rw [Fintype.card_subtype]
  simpa [hcard_eq]

private theorem finite_orthonormal_coeff_normSq_sum_le_two_pf39
    {G ι : Type*} [Group G] [Finite G] [Fintype ι] [DecidableEq ι]
    (χ : ι → Section1.ClassFunction G)
    (horth : ∀ i j : ι,
      Section1.scalarProduct G (χ i) (χ j) = if i = j then 1 else 0)
    {Y : Section1.ClassFunction G}
    (hYself : Section1.scalarProduct G Y Y = 2) :
    (∑ i : ι, Complex.normSq (Section1.scalarProduct G Y (χ i))) ≤ 2 := by
  classical
  let w : ι → ℂ := fun i => Section1.scalarProduct G Y (χ i)
  let P : Section1.ClassFunction G := Section1.weightedFamilySum w χ
  let R : Section1.ClassFunction G := Y - P
  have hPχ : ∀ i : ι, Section1.scalarProduct G P (χ i) = w i := by
    intro i
    dsimp [P]
    exact Section1.scalarProduct_weightedFamilySum_left_orthonormal w χ horth i
  have hRχ : ∀ i : ι, Section1.scalarProduct G R (χ i) = 0 := by
    intro i
    dsimp [R]
    rw [scalarProduct_sub_left_pf39, hPχ i]
    simp [w]
  have hRP : Section1.scalarProduct G R P = 0 := by
    dsimp [P]
    rw [Section1.scalarProduct_weightedFamilySum_right]
    refine Finset.sum_eq_zero ?_
    intro i _hi
    rw [hRχ i]
    simp
  have hPR : Section1.scalarProduct G P R = 0 := by
    simpa [Section1.scalarProduct_star_swap] using congrArg star hRP
  have hdecomp : Y = R + P := by
    dsimp [R, P]
    ext g
    simp [Pi.sub_apply, Pi.add_apply]
  have hnorm_decomp :
      cfNormSq_pf39 Y = cfNormSq_pf39 R + cfNormSq_pf39 P := by
    rw [hdecomp]
    exact cfNormSq_add_eq_add_of_orthogonal_pf39 hRP hPR
  have hYnorm : cfNormSq_pf39 Y = 2 := by simp [cfNormSq_pf39, hYself]
  have hPnorm_le : cfNormSq_pf39 P ≤ 2 := by
    have hRnonneg : 0 ≤ cfNormSq_pf39 R := cfNormSq_nonneg_pf39 R
    rw [hYnorm] at hnorm_decomp
    nlinarith
  have hPnorm : cfNormSq_pf39 P = ∑ i : ι, Complex.normSq (w i) := by
    dsimp [P]
    exact cfNormSq_weightedFamilySum_orthonormal_eq_sum_normSq_pf39 w χ horth
  simpa [w, hPnorm] using hPnorm_le

private theorem classFunction_eq_of_norm_eq_and_sub_orthogonal_pf39
    {G : Type u} [Group G] [Finite G]
    {Y Z : Section1.ClassFunction G}
    (hYnorm : cfNormSq_pf39 Y = cfNormSq_pf39 Z)
    (hYZ : Section1.scalarProduct G (Y - Z) Z = 0)
    (hZY : Section1.scalarProduct G Z (Y - Z) = 0) :
    Y = Z := by
  let R : Section1.ClassFunction G := Y - Z
  have hRZ : Section1.scalarProduct G R Z = 0 := by
    dsimp [R]
    exact hYZ
  have hZR : Section1.scalarProduct G Z R = 0 := by
    dsimp [R]
    exact hZY
  have hdecomp : Y = R + Z := by
    dsimp [R]
    ext g
    simp [Pi.sub_apply, Pi.add_apply]
  have hnorm :
      cfNormSq_pf39 Y = cfNormSq_pf39 R + cfNormSq_pf39 Z := by
    rw [hdecomp]
    exact cfNormSq_add_eq_add_of_orthogonal_pf39 hRZ hZR
  have hRnorm : cfNormSq_pf39 R = 0 := by
    have hRnonneg : 0 ≤ cfNormSq_pf39 R := cfNormSq_nonneg_pf39 R
    nlinarith
  have hRzero : R = 0 := cfNormSq_eq_zero_pf39 hRnorm
  change Y - Z = 0 at hRzero
  exact sub_eq_zero.mp hRzero

private theorem classFunction_eq_signed_sub_of_norm_two_pf39
    {G : Type u} [Group G] [Finite G]
    {Y φ ψ : Section1.ClassFunction G}
    {δ : ℂ}
    (hδnorm : Complex.normSq δ = 1)
    (hφφ : Section1.scalarProduct G φ φ = 1)
    (hψψ : Section1.scalarProduct G ψ ψ = 1)
    (hφψ : Section1.scalarProduct G φ ψ = 0)
    (hψφ : Section1.scalarProduct G ψ φ = 0)
    (hYnorm : cfNormSq_pf39 Y = 2)
    (hRφ : Section1.scalarProduct G (Y - δ • (φ - ψ)) φ = 0)
    (hRψ : Section1.scalarProduct G (Y - δ • (φ - ψ)) ψ = 0) :
    Y = δ • (φ - ψ) := by
  let Z : Section1.ClassFunction G := δ • (φ - ψ)
  have hdiffnorm : cfNormSq_pf39 (φ - ψ) = 2 := by
    unfold cfNormSq_pf39
    rw [scalarProduct_sub_left_pf39, scalarProduct_sub_right_pf39,
      scalarProduct_sub_right_pf39, hφφ, hφψ, hψφ, hψψ]
    norm_num
  have hZnorm : cfNormSq_pf39 Z = 2 := by
    dsimp [Z]
    rw [cfNormSq_smul_pf39, hdiffnorm, hδnorm]
    norm_num
  have hRZ : Section1.scalarProduct G (Y - Z) Z = 0 := by
    dsimp [Z]
    rw [Section1.scalarProduct_smul_right, scalarProduct_sub_right_pf39,
      hRφ, hRψ]
    simp
  have hZR : Section1.scalarProduct G Z (Y - Z) = 0 := by
    simpa [Section1.scalarProduct_star_swap] using congrArg star hRZ
  exact classFunction_eq_of_norm_eq_and_sub_orthogonal_pf39
    (Y := Y) (Z := Z) (by rw [hYnorm, hZnorm]) hRZ hZR

private theorem coefficientNonzeroCount_le_four_of_two_cell_update_pf39
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (a b : I → J → ℂ) {i0 : I} {j1 j2 : J}
    (hzero : ∀ i j, b i j ≠ 0 →
      a i j ≠ 0 ∨ (i, j) = (i0, j1) ∨ (i, j) = (i0, j2))
    (ha : coefficientNonzeroCount a ≤ 2) :
    coefficientNonzeroCount b ≤ 4 := by
  classical
  let suppA : Finset (I × J) :=
    Finset.univ.filter fun p : I × J => a p.1 p.2 ≠ 0
  let suppB : Finset (I × J) :=
    Finset.univ.filter fun p : I × J => b p.1 p.2 ≠ 0
  let extra : Finset (I × J) := {(i0, j1), (i0, j2)}
  have hsubset : suppB ⊆ suppA ∪ extra := by
    intro p hp
    rcases p with ⟨i, j⟩
    have hb : b i j ≠ 0 := (Finset.mem_filter.mp hp).2
    rcases hzero i j hb with haij | hcell | hcell
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨by simp, haij⟩)
    · exact Finset.mem_union_right _ (by simp [extra, hcell])
    · exact Finset.mem_union_right _ (by simp [extra, hcell])
  have hcardB : suppB.card ≤ (suppA ∪ extra).card :=
    Finset.card_le_card hsubset
  have hcard_union : (suppA ∪ extra).card ≤ suppA.card + extra.card :=
    Finset.card_union_le suppA extra
  have hextra : extra.card ≤ 2 := by
    dsimp [extra]
    by_cases h : (i0, j1) = (i0, j2)
    · simp [h]
    · simp [h]
  have hsuppA : coefficientNonzeroCount a = suppA.card := by
    dsimp [coefficientNonzeroCount, suppA]
    rw [Fintype.card_subtype]
  have hsuppB : coefficientNonzeroCount b = suppB.card := by
    dsimp [coefficientNonzeroCount, suppB]
    rw [Fintype.card_subtype]
  rw [hsuppB]
  rw [hsuppA] at ha
  omega

private theorem exists_two_ne_of_card_ge_three_pf39
    {I : Type*} [Fintype I] [DecidableEq I]
    (i0 : I) (hI3 : 3 ≤ Fintype.card I) :
    ∃ i1 i2 : I, i1 ≠ i0 ∧ i2 ≠ i0 ∧ i2 ≠ i1 := by
  classical
  let rows : Finset I := Finset.univ.erase i0
  have hrows_card : rows.card = Fintype.card I - 1 := by
    dsimp [rows]
    rw [Finset.card_erase_of_mem (by simp : i0 ∈ (Finset.univ : Finset I))]
    simp
  have hrows_two : 2 ≤ rows.card := by
    rw [hrows_card]
    omega
  have hrows_pos : 0 < rows.card := by omega
  rcases Finset.card_pos.mp hrows_pos with ⟨i1, hi1rows⟩
  let rows' : Finset I := rows.erase i1
  have hrows'_card : rows'.card = rows.card - 1 := by
    dsimp [rows']
    exact Finset.card_erase_of_mem hi1rows
  have hrows'_pos : 0 < rows'.card := by
    rw [hrows'_card]
    omega
  rcases Finset.card_pos.mp hrows'_pos with ⟨i2, hi2rows'⟩
  have hi1_ne : i1 ≠ i0 := (Finset.mem_erase.mp hi1rows).1
  have hi2_ne_i1 : i2 ≠ i1 := (Finset.mem_erase.mp hi2rows').1
  have hi2rows : i2 ∈ rows := (Finset.mem_erase.mp hi2rows').2
  have hi2_ne_i0 : i2 ≠ i0 := (Finset.mem_erase.mp hi2rows).1
  exact ⟨i1, i2, hi1_ne, hi2_ne_i0, hi2_ne_i1⟩

private theorem three_le_coefficientNonzeroCount_of_three_nonzero_cells_pf39
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (a : I → J → ℂ) (p q r : I × J)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hp : a p.1 p.2 ≠ 0) (hq : a q.1 q.2 ≠ 0)
    (hr : a r.1 r.2 ≠ 0) :
    3 ≤ coefficientNonzeroCount a := by
  classical
  let s : Finset (I × J) := {p, q, r}
  have hs : ∀ x ∈ s, a x.1 x.2 ≠ 0 := by
    intro x hx
    simp [s] at hx
    rcases hx with rfl | rfl | rfl
    · exact hp
    · exact hq
    · exact hr
  have hcard : s.card = 3 := by
    simp [s, hpq, hpr, hqr]
  rw [← hcard]
  exact finset_card_le_coefficientNonzeroCount a s hs

private theorem normSq_add_sub_self_gt_two_of_normSq_one_pf39
    {c δ : ℂ} (hc : c ≠ 0) (hδ : Complex.normSq δ = 1) :
    (2 : ℝ) < Complex.normSq (c + δ) + Complex.normSq (c - δ) +
      Complex.normSq c := by
  have hcpos : 0 < Complex.normSq c := by
    have hnonneg := Complex.normSq_nonneg c
    have hne : Complex.normSq c ≠ 0 := by
      intro h0
      exact hc ((Complex.normSq_eq_zero).mp h0)
    exact lt_of_le_of_ne hnonneg (Ne.symm hne)
  rw [Complex.normSq_add, Complex.normSq_sub, hδ]
  nlinarith

private theorem normSq_three_cells_le_sum_pf39
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (a : I → J → ℂ) (p q r : I × J)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    Complex.normSq (a p.1 p.2) + Complex.normSq (a q.1 q.2) +
      Complex.normSq (a r.1 r.2) ≤
        ∑ x : I × J, Complex.normSq (a x.1 x.2) := by
  classical
  let s : Finset (I × J) := {p, q, r}
  have hs_sub : s ⊆ Finset.univ := by
    intro x _hx
    simp
  have hsum_s :
      Finset.sum s (fun x => Complex.normSq (a x.1 x.2)) =
        Complex.normSq (a p.1 p.2) + Complex.normSq (a q.1 q.2) +
          Complex.normSq (a r.1 r.2) := by
    simp [s, hpq, hpr, hqr, add_comm, add_left_comm]
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hs_sub
    (by intro x _hxuniv _hxs; exact Complex.normSq_nonneg (a x.1 x.2))
  rw [← hsum_s]
  exact hle

private theorem two_cell_update_base_row_vanish_of_small_shape_pf39
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (a b : I → J → ℂ) {i0 : I} {j j0 : J} {δ : ℂ}
    (hj : j ≠ j0)
    (hδnorm : Complex.normSq δ = 1)
    (hI3 : 3 ≤ Fintype.card I)
    (hJ3 : 3 ≤ Fintype.card J)
    (ha_count : coefficientNonzeroCount a ≤ 2)
    (ha_norm : (∑ p : I × J, Complex.normSq (a p.1 p.2)) ≤ 2)
    (hshape :
      (∀ i k, b i k = 0) ∨
        (∃ c : ℂ, c ≠ 0 ∧ ∃ k : J,
          ∀ i q, b i q = if q = k then c else 0) ∨
        (∃ c : ℂ, c ≠ 0 ∧ ∃ i : I,
          ∀ p q, b p q = if p = i then c else 0))
    (hupdate_j : a i0 j = b i0 j + δ)
    (hupdate_j0 : a i0 j0 = b i0 j0 - δ)
    (hupdate_other : ∀ i k, (i, k) ≠ (i0, j) → (i, k) ≠ (i0, j0) →
      a i k = b i k) :
    b i0 j = 0 ∧ b i0 j0 = 0 := by
  classical
  have hδne : δ ≠ 0 := by
    intro hδ0
    subst δ
    norm_num at hδnorm
  rcases hshape with hzero | hshape
  · exact ⟨hzero i0 j, hzero i0 j0⟩
  rcases hshape with hcol | hrow
  · rcases hcol with ⟨c, hc, k, hcol⟩
    by_cases hkj : k = j
    · subst k
      rcases exists_two_ne_of_card_ge_three_pf39 i0 hI3 with
        ⟨i1, i2, hi1, hi2, hi21⟩
      have hi1j_ne_active : (i1, j) ≠ (i0, j) := by
        intro hp
        exact hi1 (congrArg Prod.fst hp)
      have hi1j_ne_base : (i1, j) ≠ (i0, j0) := by
        intro hp
        exact hi1 (congrArg Prod.fst hp)
      have hi2j_ne_active : (i2, j) ≠ (i0, j) := by
        intro hp
        exact hi2 (congrArg Prod.fst hp)
      have hi2j_ne_base : (i2, j) ≠ (i0, j0) := by
        intro hp
        exact hi2 (congrArg Prod.fst hp)
      have h1 : a i1 j ≠ 0 := by
        rw [hupdate_other i1 j hi1j_ne_active hi1j_ne_base, hcol i1 j,
          if_pos rfl]
        exact hc
      have h2 : a i2 j ≠ 0 := by
        rw [hupdate_other i2 j hi2j_ne_active hi2j_ne_base, hcol i2 j,
          if_pos rfl]
        exact hc
      have hbase : a i0 j0 ≠ 0 := by
        rw [hupdate_j0, hcol i0 j0, if_neg (fun h => hj h.symm)]
        simpa using (neg_ne_zero.mpr hδne)
      have hthree : 3 ≤ coefficientNonzeroCount a :=
        three_le_coefficientNonzeroCount_of_three_nonzero_cells_pf39
          a (i1, j) (i2, j) (i0, j0)
          (by intro hp; exact hi21 (congrArg Prod.fst hp).symm)
          (by intro hp; exact hi1 (congrArg Prod.fst hp))
          (by intro hp; exact hi2 (congrArg Prod.fst hp))
          h1 h2 hbase
      omega
    · by_cases hkj0 : k = j0
      · subst k
        rcases exists_two_ne_of_card_ge_three_pf39 i0 hI3 with
          ⟨i1, i2, hi1, hi2, hi21⟩
        have hi1j0_ne_active : (i1, j0) ≠ (i0, j) := by
          intro hp
          exact hi1 (congrArg Prod.fst hp)
        have hi1j0_ne_base : (i1, j0) ≠ (i0, j0) := by
          intro hp
          exact hi1 (congrArg Prod.fst hp)
        have hi2j0_ne_active : (i2, j0) ≠ (i0, j) := by
          intro hp
          exact hi2 (congrArg Prod.fst hp)
        have hi2j0_ne_base : (i2, j0) ≠ (i0, j0) := by
          intro hp
          exact hi2 (congrArg Prod.fst hp)
        have h1 : a i1 j0 ≠ 0 := by
          rw [hupdate_other i1 j0 hi1j0_ne_active hi1j0_ne_base,
            hcol i1 j0, if_pos rfl]
          exact hc
        have h2 : a i2 j0 ≠ 0 := by
          rw [hupdate_other i2 j0 hi2j0_ne_active hi2j0_ne_base,
            hcol i2 j0, if_pos rfl]
          exact hc
        have hbase : a i0 j ≠ 0 := by
          rw [hupdate_j, hcol i0 j, if_neg hj]
          simpa using hδne
        have hthree : 3 ≤ coefficientNonzeroCount a :=
          three_le_coefficientNonzeroCount_of_three_nonzero_cells_pf39
            a (i1, j0) (i2, j0) (i0, j)
            (by intro hp; exact hi21 (congrArg Prod.fst hp).symm)
            (by intro hp; exact hi1 (congrArg Prod.fst hp))
            (by intro hp; exact hi2 (congrArg Prod.fst hp))
            h1 h2 hbase
        omega
      · constructor
        · rw [hcol i0 j, if_neg (fun h => hkj h.symm)]
        · rw [hcol i0 j0, if_neg (fun h => hkj0 h.symm)]
  · rcases hrow with ⟨c, hc, i, hrow⟩
    by_cases hii0 : i = i0
    · subst i
      rcases exists_other_ne_base_of_fintype_card_ge_three j0 j hj hJ3 with
        ⟨k, hk0, hkj⟩
      have hcell_kj : (i0, k) ≠ (i0, j) := by
        intro hp
        exact hkj (congrArg Prod.snd hp)
      have hcell_kj0 : (i0, k) ≠ (i0, j0) := by
        intro hp
        exact hk0 (congrArg Prod.snd hp)
      have haj : a i0 j = c + δ := by
        rw [hupdate_j, hrow i0 j, if_pos rfl]
      have haj0 : a i0 j0 = c - δ := by
        rw [hupdate_j0, hrow i0 j0, if_pos rfl]
      have hak : a i0 k = c := by
        rw [hupdate_other i0 k hcell_kj hcell_kj0, hrow i0 k, if_pos rfl]
      have hpq : (i0, j) ≠ (i0, j0) := by
        intro hp
        exact hj (congrArg Prod.snd hp)
      have hpr : (i0, j) ≠ (i0, k) := by
        intro hp
        exact hkj (congrArg Prod.snd hp).symm
      have hqr : (i0, j0) ≠ (i0, k) := by
        intro hp
        exact hk0 (congrArg Prod.snd hp).symm
      have hle :=
        normSq_three_cells_le_sum_pf39 a (i0, j) (i0, j0) (i0, k)
          hpq hpr hqr
      have hgt :
          (2 : ℝ) <
            Complex.normSq (a i0 j) + Complex.normSq (a i0 j0) +
              Complex.normSq (a i0 k) := by
        rw [haj, haj0, hak]
        exact normSq_add_sub_self_gt_two_of_normSq_one_pf39 hc hδnorm
      have hsum_gt : (2 : ℝ) <
          ∑ p : I × J, Complex.normSq (a p.1 p.2) :=
        lt_of_lt_of_le hgt hle
      exact False.elim ((not_lt_of_ge ha_norm) hsum_gt)
    · have hi0_ne_i : i0 ≠ i := fun h => hii0 h.symm
      exact ⟨by rw [hrow i0 j, if_neg hi0_ne_i],
        by rw [hrow i0 j0, if_neg hi0_ne_i]⟩


public theorem eq_signed_sub_cTIiso
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    (h31 : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hσ : theorem_3_2_map_statement W1 W2 W σ)
    {φ : Section1.ClassFunction G}
    (hφvirt : Theory.Character.IsVirtualCharacter φ)
    (hφnorm : Section1.scalarProduct G φ φ = 2)
    {δ : ℂ} (hδnorm : Complex.normSq δ = 1)
    (i : I) {j1 j2 : J} (hj : j1 ≠ j2)
    (hagrees : ∀ x : G, ∀ _hx : x ∈ cyclicTISet W1 W2 W,
      φ x = (δ • (σ (ω i j1) - σ (ω i j2))) x) :
    φ = δ • (σ (ω i j1) - σ (ω i j2)) := by
  classical
  let Z : Section1.ClassFunction G := δ • (σ (ω i j1) - σ (ω i j2))
  let R : Section1.ClassFunction G := φ - Z
  let a : I → J → ℂ := fun p q =>
    Section1.scalarProduct G φ (σ (ω p q))
  let b : I → J → ℂ := fun p q =>
    Section1.scalarProduct G R (σ (ω p q))
  rcases hσ with
    ⟨hIso, hMapVirt, hInd, hMapClass, _hPrincipal, _hAgree, _hOutside⟩
  have hσωorth : ∀ p q : I × J,
      Section1.scalarProduct G (σ (ω p.1 p.2)) (σ (ω q.1 q.2)) =
        if p = q then 1 else 0 := by
    intro p q
    exact (hIso (ω p.1 p.2) (ω q.1 q.2)
      (hω.is_class p.1 p.2) (hω.is_class q.1 q.2)).trans
        (hω.orthonormal p q)
  have hσωvirt : ∀ p : I × J,
      Theory.Character.IsVirtualCharacter (σ (ω p.1 p.2)) := by
    intro p
    exact hMapVirt (ω p.1 p.2)
      (isVirtualCharacter_of_irreducibleCharacterOnGroup
        (hω.irreducible p.1 p.2))
  have hσωclass : ∀ p q,
      Section1.IsClassFunction (σ (ω p q)) := by
    intro p q
    exact hMapClass (ω p q) (hω.is_class p q)
  have hφclass : Section1.IsClassFunction φ :=
    Section1.isVirtualCharacter_isClassFunction hφvirt
  have hZclass : Section1.IsClassFunction Z := by
    intro x g
    simp [Z, hσωclass i j1 x g, hσωclass i j2 x g]
  have hRclass : Section1.IsClassFunction R := by
    intro x g
    simp [R, hφclass x g, hZclass x g]
  have hRvanish : VanishesOn R (cyclicTISet W1 W2 W) := by
    intro x hx
    dsimp [R, Z]
    rw [hagrees x hx]
    simp
  have hI3 : 3 ≤ Fintype.card I := by
    rw [hω.card_left]
    exact natCard_left_ge_three_of_hypothesis_3_1 h31
  have hJ3 : 3 ≤ Fintype.card J := by
    rw [hω.card_right]
    exact natCard_right_ge_three_of_hypothesis_3_1 h31
  have hoddI : Odd (Fintype.card I) := by
    rw [hω.card_left]
    exact odd_natCard_left_of_hypothesis_3_1 h31
  have hoddJ : Odd (Fintype.card J) := by
    rw [hω.card_right]
    exact odd_natCard_right_of_hypothesis_3_1 h31
  have hcards_ne : Fintype.card I ≠ Fintype.card J := by
    intro hEq
    have hcop : Nat.Coprime (Fintype.card I) (Fintype.card J) := by
      simpa [hω.card_left, hω.card_right] using
        natCard_left_right_coprime_of_hypothesis_3_1 h31
    rw [hEq] at hcop
    have hgt : 1 < Fintype.card J := by omega
    exact (Nat.not_coprime_of_dvd_of_dvd hgt (dvd_refl _) (dvd_refl _)) hcop
  have ha_count : coefficientNonzeroCount a ≤ 2 := by
    simpa [coefficientNonzeroCount, a] using
      finite_orthonormal_virtual_coeff_support_card_le_two_pf39
        (fun p : I × J => σ (ω p.1 p.2)) hσωorth hσωvirt hφvirt hφnorm
  have ha_norm :
      (∑ p : I × J, Complex.normSq (a p.1 p.2)) ≤ 2 := by
    simpa [a] using
      finite_orthonormal_coeff_normSq_sum_le_two_pf39
        (fun p : I × J => σ (ω p.1 p.2)) hσωorth hφnorm
  have hzero : ∀ p q, b p q ≠ 0 →
      a p q ≠ 0 ∨ (p, q) = (i, j1) ∨ (p, q) = (i, j2) := by
    intro p q hb
    by_cases hcell1 : (p, q) = (i, j1)
    · exact Or.inr (Or.inl hcell1)
    by_cases hcell2 : (p, q) = (i, j2)
    · exact Or.inr (Or.inr hcell2)
    left
    intro ha0
    have hZpq : Section1.scalarProduct G Z (σ (ω p q)) = 0 := by
      have hleft :
          Section1.scalarProduct G (σ (ω i j1)) (σ (ω p q)) = 0 := by
        have hnot : (i, j1) ≠ (p, q) := fun h => hcell1 h.symm
        simpa [hnot] using hσωorth (i, j1) (p, q)
      have hright :
          Section1.scalarProduct G (σ (ω i j2)) (σ (ω p q)) = 0 := by
        have hnot : (i, j2) ≠ (p, q) := fun h => hcell2 h.symm
        simpa [hnot] using hσωorth (i, j2) (p, q)
      dsimp [Z]
      rw [Section1.scalarProduct_smul_left, scalarProduct_sub_left_pf39,
        hleft, hright]
      simp
    apply hb
    dsimp [b, R, a] at ha0 ⊢
    rw [scalarProduct_sub_left_pf39, ha0, hZpq]
    simp
  have hb_count : coefficientNonzeroCount b ≤ 4 :=
    coefficientNonzeroCount_le_four_of_two_cell_update_pf39 a b hzero ha_count
  have hrect : ∀ p p' q q', b p q + b p' q' = b p q' + b p' q := by
    intro p p' q q'
    have hz := scalarProduct_vanishes_rectangle_eq_zero_of_agrees
      hω hInd hRclass hRvanish p p' q q'
    have hz' : b p q + b p' q' - b p q' - b p' q = 0 := by
      dsimp [b]
      simpa [omegaRectangle, scalarProduct_add_right_pf39,
        scalarProduct_sub_right_pf39] using hz
    linear_combination hz'
  have hshape :
      (∀ p q, b p q = 0) ∨
        (∃ c : ℂ, c ≠ 0 ∧ ∃ q : J,
          ∀ p r, b p r = if r = q then c else 0) ∨
        (∃ c : ℂ, c ≠ 0 ∧ ∃ p : I,
          ∀ r q, b r q = if r = p then c else 0) := by
    by_cases hltIJ : Fintype.card I < Fintype.card J
    · have hb_lt : coefficientNonzeroCount b < 2 * Fintype.card I := by
        omega
      exact coefficient_rectangle_small_shape b hrect hb_lt hoddI hoddJ
        hltIJ hI3
    · have hltJI : Fintype.card J < Fintype.card I := by omega
      let bT : J → I → ℂ := fun q p => b p q
      have hrectT : ∀ q q' p p', bT q p + bT q' p' = bT q p' + bT q' p := by
        intro q q' p p'
        simpa [bT, add_comm, add_left_comm] using hrect p p' q q'
      have hcountT : coefficientNonzeroCount bT = coefficientNonzeroCount b := by
        simpa [bT] using coefficientNonzeroCount_swap b
      have hbT_lt : coefficientNonzeroCount bT < 2 * Fintype.card J := by
        rw [hcountT]
        omega
      rcases coefficient_rectangle_small_shape bT hrectT hbT_lt hoddJ hoddI
          hltJI hJ3 with hzeroT | hshapeT
      · exact Or.inl (fun p q => hzeroT q p)
      · rcases hshapeT with hcolT | hrowT
        · rcases hcolT with ⟨c, hc, p, hcolT⟩
          exact Or.inr <| Or.inr ⟨c, hc, p, fun r q => hcolT q r⟩
        · rcases hrowT with ⟨c, hc, q, hrowT⟩
          exact Or.inr <| Or.inl ⟨c, hc, q, fun p r => hrowT r p⟩
  have hZ_j1 : Section1.scalarProduct G Z (σ (ω i j1)) = δ := by
    have hself :
        Section1.scalarProduct G (σ (ω i j1)) (σ (ω i j1)) = 1 := by
      simpa using hσωorth (i, j1) (i, j1)
    have hcross :
        Section1.scalarProduct G (σ (ω i j2)) (σ (ω i j1)) = 0 := by
      have hne : (i, j2) ≠ (i, j1) := by
        intro hEq
        exact hj (congrArg Prod.snd hEq).symm
      simpa [hne] using hσωorth (i, j2) (i, j1)
    dsimp [Z]
    rw [Section1.scalarProduct_smul_left, scalarProduct_sub_left_pf39,
      hself, hcross]
    ring
  have hZ_j2 : Section1.scalarProduct G Z (σ (ω i j2)) = -δ := by
    have hcross :
        Section1.scalarProduct G (σ (ω i j1)) (σ (ω i j2)) = 0 := by
      have hne : (i, j1) ≠ (i, j2) := by
        intro hEq
        exact hj (congrArg Prod.snd hEq)
      simpa [hne] using hσωorth (i, j1) (i, j2)
    have hself :
        Section1.scalarProduct G (σ (ω i j2)) (σ (ω i j2)) = 1 := by
      simpa using hσωorth (i, j2) (i, j2)
    dsimp [Z]
    rw [Section1.scalarProduct_smul_left, scalarProduct_sub_left_pf39,
      hcross, hself]
    ring
  have hupdate_j1 : a i j1 = b i j1 + δ := by
    dsimp [a, b, R]
    rw [scalarProduct_sub_left_pf39, hZ_j1]
    ring
  have hupdate_j2 : a i j2 = b i j2 - δ := by
    dsimp [a, b, R]
    rw [scalarProduct_sub_left_pf39, hZ_j2]
    ring
  have hupdate_other : ∀ p q, (p, q) ≠ (i, j1) → (p, q) ≠ (i, j2) →
      a p q = b p q := by
    intro p q hcell1 hcell2
    have hZpq : Section1.scalarProduct G Z (σ (ω p q)) = 0 := by
      have hleft :
          Section1.scalarProduct G (σ (ω i j1)) (σ (ω p q)) = 0 := by
        have hnot : (i, j1) ≠ (p, q) := fun h => hcell1 h.symm
        simpa [hnot] using hσωorth (i, j1) (p, q)
      have hright :
          Section1.scalarProduct G (σ (ω i j2)) (σ (ω p q)) = 0 := by
        have hnot : (i, j2) ≠ (p, q) := fun h => hcell2 h.symm
        simpa [hnot] using hσωorth (i, j2) (p, q)
      dsimp [Z]
      rw [Section1.scalarProduct_smul_left, scalarProduct_sub_left_pf39,
        hleft, hright]
      simp
    dsimp [a, b, R]
    rw [scalarProduct_sub_left_pf39, hZpq]
    simp
  have hresidual := two_cell_update_base_row_vanish_of_small_shape_pf39
    a b hj hδnorm hI3 hJ3 ha_count ha_norm hshape
    hupdate_j1 hupdate_j2 hupdate_other
  have hφφ : Section1.scalarProduct G (σ (ω i j1)) (σ (ω i j1)) = 1 := by
    simpa using hσωorth (i, j1) (i, j1)
  have hψψ : Section1.scalarProduct G (σ (ω i j2)) (σ (ω i j2)) = 1 := by
    simpa using hσωorth (i, j2) (i, j2)
  have hφψ : Section1.scalarProduct G (σ (ω i j1)) (σ (ω i j2)) = 0 := by
    have hne : (i, j1) ≠ (i, j2) := by
      intro hEq
      exact hj (congrArg Prod.snd hEq)
    simpa [hne] using hσωorth (i, j1) (i, j2)
  have hψφ : Section1.scalarProduct G (σ (ω i j2)) (σ (ω i j1)) = 0 := by
    have hne : (i, j2) ≠ (i, j1) := by
      intro hEq
      exact hj (congrArg Prod.snd hEq).symm
    simpa [hne] using hσωorth (i, j2) (i, j1)
  have hφnormReal : cfNormSq_pf39 φ = 2 := by
    simp [cfNormSq_pf39, hφnorm]
  exact classFunction_eq_signed_sub_of_norm_two_pf39
    hδnorm hφφ hψψ hφψ hψφ hφnormReal
    (by simpa [b, R, Z] using hresidual.1)
    (by simpa [b, R, Z] using hresidual.2)

private theorem hypothesis_3_6_of_projection_diff_pf39
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : I → J → Section1.ClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (horth : IsOrthonormalDoubleFamily χ)
    (hsigned : ∀ i j, IsSignedIrreducibleCharacter (χ i j))
    (h00 : χ i0 j0 = Section1.principalCharacter G)
    (hInd : ∀ i j, i ≠ i0 → j ≠ j0 →
      Section1.inducedCF W (alphaIJ W i0 j0 ω i j) =
        Section1.principalCharacter G - χ i j0 - χ i0 j + χ i j)
    {X : Section1.ClassFunction G}
    (hX : IsSignedIrreducibleCharacter X)
    (i : I) (j : J)
    (hXV :
      ∀ x : G, ∀ hx : x ∈ cyclicTISet W1 W2 W,
        X x = ω i j ⟨x, cyclicTISet_subset W1 W2 W hx⟩) :
    let σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G :=
      sigmaOfPF35 ω χ
    let ψ : Section1.ClassFunction G := σ (ω i j) - X
    let a : I → J → ℂ := fun p q => Section1.scalarProduct G ψ (χ p q)
    let β : Section1.ClassFunction G :=
      ψ - ∑ p : I × J, a p.1 p.2 • χ p.1 p.2
    hypothesis_3_6_statement W1 W2 W I J i0 j0 ω σ ψ β a h hω := by
  classical
  intro σ ψ a β
  refine ⟨
    theorem_3_2_map_statement_sigmaOfPF35_pf39
      (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω horth hsigned h00 hInd,
    ?_⟩
  refine ⟨?_, ?_⟩
  · intro α _hα
    exact scalarProduct_projection_residual_sigmaOfPF35_zero_pf39
      (ω := ω) (χ := χ) horth ψ α
  refine ⟨?_, ?_⟩
  · have hsumσχ :
        ∑ p : I × J, a p.1 p.2 • σ (ω p.1 p.2) =
          ∑ p : I × J, a p.1 p.2 • χ p.1 p.2 := by
      refine Finset.sum_congr rfl ?_
      intro p hp
      simp [σ, sigmaOfPF35_apply_omega ω χ hω.orthonormal p.1 p.2]
    calc
      ψ = (∑ p : I × J, a p.1 p.2 • χ p.1 p.2) + β := by
        simp [β]
      _ = (∑ p : I × J, a p.1 p.2 • σ (ω p.1 p.2)) + β := by
        rw [hsumσχ]
  refine ⟨?_, ?_⟩
  · have hχclass : ∀ p : I × J, Section1.IsClassFunction (χ p.1 p.2) := by
      intro p
      exact isClassFunction_of_signed_irreducible_pf39 (hsigned p.1 p.2)
    have hψclass : Section1.IsClassFunction ψ := by
      have hχijclass : Section1.IsClassFunction (χ i j) := hχclass (i, j)
      have hXclass : Section1.IsClassFunction X :=
        isClassFunction_of_signed_irreducible_pf39 hX
      intro x g
      simp [ψ, σ, sigmaOfPF35_apply_omega ω χ hω.orthonormal i j,
        hχijclass x g, hXclass x g]
    intro x g
    simp [β, hψclass x g]
    refine Finset.sum_congr rfl ?_
    intro p hp
    simp [hχclass p x g]
  refine ⟨?_, ?_⟩
  · have hχclass : Section1.IsClassFunction (χ i j) :=
      isClassFunction_of_signed_irreducible_pf39 (hsigned i j)
    have hXclass : Section1.IsClassFunction X :=
      isClassFunction_of_signed_irreducible_pf39 hX
    intro x g
    simp [ψ, σ, sigmaOfPF35_apply_omega ω χ hω.orthonormal i j,
      hχclass x g, hXclass x g]
  · intro x hx
    have hσV := agreesOnCyclicTISet_sigmaOfPF35_pf39
      (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω horth hsigned h00 hInd (ω i j)
      (hω.is_class i j) x hx
    subst ψ
    rw [Pi.sub_apply, hσV, hXV x hx, sub_self]

private theorem signed_irreducible_eq_sigmaOfPF35_of_agrees_ordered_pf39
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : I → J → Section1.ClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (horth : IsOrthonormalDoubleFamily χ)
    (hsigned : ∀ i j, IsSignedIrreducibleCharacter (χ i j))
    (h00 : χ i0 j0 = Section1.principalCharacter G)
    (hInd : ∀ i j, i ≠ i0 → j ≠ j0 →
      Section1.inducedCF W (alphaIJ W i0 j0 ω i j) =
        Section1.principalCharacter G - χ i j0 - χ i0 j + χ i j)
    (hlt : Nat.card W1 < Nat.card W2)
    {X : Section1.ClassFunction G}
    (hX : IsSignedIrreducibleCharacter X)
    (i : I) (j : J)
    (hXV :
      ∀ x : G, ∀ hx : x ∈ cyclicTISet W1 W2 W,
        X x = ω i j ⟨x, cyclicTISet_subset W1 W2 W hx⟩) :
    X = sigmaOfPF35 ω χ (ω i j) := by
  classical
  let σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G :=
    sigmaOfPF35 ω χ
  let ψ : Section1.ClassFunction G := σ (ω i j) - X
  let a : I → J → ℂ := fun p q => Section1.scalarProduct G ψ (χ p q)
  let β : Section1.ClassFunction G :=
    ψ - ∑ p : I × J, a p.1 p.2 • χ p.1 p.2
  have h36 : hypothesis_3_6_statement W1 W2 W I J i0 j0 ω σ ψ β a h hω := by
    exact hypothesis_3_6_of_projection_diff_pf39
      (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω horth hsigned h00 hInd hX i j hXV
  have hcount_le2 : coefficientNonzeroCount a ≤ 2 := by
    dsimp [a, ψ, σ]
    simpa [sigmaOfPF35_apply_omega ω χ hω.orthonormal i j] using
      (coefficientNonzeroCount_le_two_of_projection_diff_pf39
        (χ := χ) horth hsigned hX i j)
  have hcount_lt : coefficientNonzeroCount a < 2 * Nat.card W1 := by
    have hleft3 : 3 ≤ Nat.card W1 := natCard_left_ge_three_of_hypothesis_3_1 h
    omega
  have h38 := proposition_3_8
    (W1 := W1) (W2 := W2) (W := W)
    (I := I) (J := J) (i0 := i0) (j0 := j0)
    (ω := ω) (σ := σ) (ψ := ψ) (β := β) (a := a) h hω h36 hlt hcount_lt
  have horthψ :
      Section1.scalarProduct G ψ (σ (ω i j)) = 0 := by
    have h38strong := proposition_3_8_strong
      (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0)
      (ω := ω) (σ := σ) (ψ := ψ) (β := β) (a := a) h hω h36 hlt hcount_lt
    have hβorth := h36.2.1
    rcases h38strong with hψeq | hcol | hrow
    · rw [hψeq]
      exact hβorth (ω i j) (hω.is_class i j)
    · rcases hcol with ⟨hcountEq, c, _hc, j', _hshape⟩
      have hleft3 : 3 ≤ Nat.card W1 := natCard_left_ge_three_of_hypothesis_3_1 h
      omega
    · rcases hrow with ⟨hcountEq, c, _hc, i', _hshape⟩
      have hright3 : 3 ≤ Nat.card W2 := natCard_right_ge_three_of_hypothesis_3_1 h
      omega
  have hselfσ : Section1.scalarProduct G (σ (ω i j)) (σ (ω i j)) = 1 := by
    calc
      Section1.scalarProduct G (σ (ω i j)) (σ (ω i j)) =
        Section1.scalarProduct W (ω i j) (ω i j) := by
          exact isCFLinearIsometry_sigmaOfPF35_pf39
            (W1 := W1) (W2 := W2) (W := W)
            (I := I) (J := J) (i0 := i0) (j0 := j0)
            (ω := ω) (χ := χ) h hω horth hsigned h00 hInd
            (ω i j) (ω i j) (hω.is_class i j) (hω.is_class i j)
      _ = 1 := by
          simpa using hω.orthonormal (i, j) (i, j)
  have hcross : Section1.scalarProduct G X (σ (ω i j)) = 1 := by
    have hz :
        (1 : ℂ) - Section1.scalarProduct G X (σ (ω i j)) = 0 := by
      rw [show ψ = σ (ω i j) - X by rfl] at horthψ
      have hneg : (-X : Section1.ClassFunction G) = (-1 : ℂ) • X := by
        ext g
        simp
      rw [sub_eq_add_neg, Section1.scalarProduct_add_left, hneg,
        Section1.scalarProduct_smul_left, hselfσ] at horthψ
      rw [neg_one_mul] at horthψ
      simpa only [sub_eq_add_neg] using horthψ
    exact (sub_eq_zero.mp hz).symm
  exact signed_irreducible_eq_of_scalarProduct_eq_one_pf39
    hX
    (sigmaOfPF35_signed_image ω χ hω.orthonormal hsigned i j)
    hcross

private theorem signed_irreducible_eq_sigmaOfPF35_of_irreducible_agrees_ordered_pf39
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : I → J → Section1.ClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (horth : IsOrthonormalDoubleFamily χ)
    (hsigned : ∀ i j, IsSignedIrreducibleCharacter (χ i j))
    (h00 : χ i0 j0 = Section1.principalCharacter G)
    (hInd : ∀ i j, i ≠ i0 → j ≠ j0 →
      Section1.inducedCF W (alphaIJ W i0 j0 ω i j) =
        Section1.principalCharacter G - χ i j0 - χ i0 j + χ i j)
    (hlt : Nat.card W1 < Nat.card W2)
    {ω' : Section1.ClassFunction W}
    (hω' : Section1.IsIrreducibleCharacterOnGroup ω')
    {X : Section1.ClassFunction G}
    (hX : IsSignedIrreducibleCharacter X)
    (hXV :
      ∀ x : G, ∀ hx : x ∈ cyclicTISet W1 W2 W,
        X x = ω' ⟨x, cyclicTISet_subset W1 W2 W hx⟩) :
    X = sigmaOfPF35 ω χ ω' := by
  rcases hω.all_irreducibles ω' hω' with ⟨i, j, rfl⟩
  simpa using signed_irreducible_eq_sigmaOfPF35_of_agrees_ordered_pf39
    (W1 := W1) (W2 := W2) (W := W)
    (I := I) (J := J) (i0 := i0) (j0 := j0)
    (ω := ω) (χ := χ) h hω horth hsigned h00 hInd hlt hX i j hXV

private theorem isOrthonormalDoubleFamily_swap_pf39
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [DecidableEq I] [DecidableEq J]
    {χ : I → J → Section1.ClassFunction G}
    (hχ : IsOrthonormalDoubleFamily χ) :
    IsOrthonormalDoubleFamily (fun j i => χ i j) := by
  intro p q
  rcases p with ⟨j, i⟩
  rcases q with ⟨j', i'⟩
  simpa [Prod.ext_iff, Prod.mk.injEq, eq_comm, and_left_comm, and_assoc, and_comm] using
    hχ (i, j) (i', j')

private theorem sigmaOfPF35_swap_pf39
    {G : Type u} [Group G] [Finite G]
    {W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J]
    (ω : I → J → Section1.ClassFunction W)
    (χ : I → J → Section1.ClassFunction G)
    (α : Section1.ClassFunction W) :
    sigmaOfPF35 (fun j i => ω i j) (fun j i => χ i j) α =
      sigmaOfPF35 ω χ α := by
  ext g
  unfold sigmaOfPF35 Section1.weightedFamilySum
  simp
  have : instFintypeProd J I = Fintype.ofFinite (J × I) := by exact of_decide_eq_true rfl
  have : @Finset.univ (J × I) (Fintype.ofFinite (J × I)) = @Finset.univ (J × I) (instFintypeProd J I) := by rw [this]
  rw [this, Fintype.sum_prod_type, Finset.sum_comm]
  have : instFintypeProd I J = Fintype.ofFinite (I × J) := by exact of_decide_eq_true rfl
  have : @Finset.univ (I × J) (Fintype.ofFinite (I × J)) = @Finset.univ (I × J) (instFintypeProd I J) := by rw [this]
  rw [this, Fintype.sum_prod_type]


public theorem sigmaOfPF35_swap_apply_table
    {G : Type u} [Group G] [Finite G]
    {W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J]
    (ω : I → J → Section1.ClassFunction W)
    (χ : I → J → Section1.ClassFunction G)
    (i : I) (j : J) :
    sigmaOfPF35 ω χ (ω i j) =
      sigmaOfPF35 (fun j i => ω i j) (fun j i => χ i j)
        ((fun j i => ω i j) j i) := by
  exact (sigmaOfPF35_swap_pf39 ω χ (ω i j)).symm


private theorem signed_irreducible_eq_sigmaOfPF35_of_irreducible_agrees_pf39
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : I → J → Section1.ClassFunction G}
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (horth : IsOrthonormalDoubleFamily χ)
    (hsigned : ∀ i j, IsSignedIrreducibleCharacter (χ i j))
    (h00 : χ i0 j0 = Section1.principalCharacter G)
    (hInd : ∀ i j, i ≠ i0 → j ≠ j0 →
      Section1.inducedCF W (alphaIJ W i0 j0 ω i j) =
        Section1.principalCharacter G - χ i j0 - χ i0 j + χ i j)
    {ω' : Section1.ClassFunction W}
    (hω' : Section1.IsIrreducibleCharacterOnGroup ω')
    {X : Section1.ClassFunction G}
    (hX : IsSignedIrreducibleCharacter X)
    (hXV :
      ∀ x : G, ∀ hx : x ∈ cyclicTISet W1 W2 W,
        X x = ω' ⟨x, cyclicTISet_subset W1 W2 W hx⟩) :
    X = sigmaOfPF35 ω χ ω' := by
  have hne : Nat.card W1 ≠ Nat.card W2 := by
    intro hEq
    have hcop := natCard_left_right_coprime_of_hypothesis_3_1 h
    rw [hEq] at hcop
    have hgt1 : 1 < Nat.card W2 := by
      have hleft3 : 3 ≤ Nat.card W1 := natCard_left_ge_three_of_hypothesis_3_1 h
      have hright3 : 3 ≤ Nat.card W2 := by rw [← hEq]; exact hleft3
      omega
    exact (Nat.not_coprime_of_dvd_of_dvd hgt1 (dvd_refl _) (dvd_refl _)) hcop
  by_cases hlt : Nat.card W1 < Nat.card W2
  · exact signed_irreducible_eq_sigmaOfPF35_of_irreducible_agrees_ordered_pf39
      (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω horth hsigned h00 hInd hlt hω' hX hXV
  · have hgt : Nat.card W2 < Nat.card W1 := by
      omega
    have hInd_swap :
        ∀ j i, j ≠ j0 → i ≠ i0 →
          Section1.inducedCF W
              (alphaIJ W j0 i0 (fun j i => ω i j) j i) =
            Section1.principalCharacter G -
              (fun j i => χ i j) j i0 -
              (fun j i => χ i j) j0 i +
              (fun j i => χ i j) j i := by
      intro j i hj hi
      rw [alphaIJ_swap_eq (W := W) (ω := ω) i j]
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hInd i j hi hj
    have hXV_swap :
        ∀ x : G, ∀ hx : x ∈ cyclicTISet W2 W1 W,
          X x = ω' ⟨x, cyclicTISet_subset W2 W1 W hx⟩ := by
      intro x hx
      have hx' : x ∈ cyclicTISet W1 W2 W := by
        simpa [cyclicTISet_swap W1 W2 W] using hx
      simpa [cyclicTISet_swap W1 W2 W] using hXV x hx'
    have hswap := signed_irreducible_eq_sigmaOfPF35_of_irreducible_agrees_ordered_pf39
      (W1 := W2) (W2 := W1) (W := W)
      (I := J) (J := I) (i0 := j0) (j0 := i0)
      (ω := fun j i => ω i j) (χ := fun j i => χ i j)
      (hypothesis_3_1_statement_swap h)
      (notation_3_3_statement_swap hω)
      (isOrthonormalDoubleFamily_swap_pf39 horth)
      (fun j i => hsigned i j)
      (by simpa using h00)
      hInd_swap hgt hω' hX hXV_swap
    simpa [sigmaOfPF35_swap_pf39] using hswap

/--
Peterfalvi (3.9)(a), uniqueness clause, in the explicit PF (3.5) setting:
if a signed irreducible character of `G` agrees with an irreducible character
`ω'` of `W` on `V = W \ (W₁ ∪ W₂)`, then it is the `sigmaOfPF35` image of `ω'`.
-/
public theorem proposition_3_9_a_uniqueness_of_pf35
    {G : Type u} [Group G] [Finite G]
    (W1 W2 W : Subgroup G)
    (I J : Type*) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → Section1.ClassFunction W)
    (χ : I → J → Section1.ClassFunction G)
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (horth : IsOrthonormalDoubleFamily χ)
    (hsigned : ∀ i j, IsSignedIrreducibleCharacter (χ i j))
    (h00 : χ i0 j0 = Section1.principalCharacter G)
    (hInd : ∀ i j, i ≠ i0 → j ≠ j0 →
      Section1.inducedCF W (alphaIJ W i0 j0 ω i j) =
        Section1.principalCharacter G - χ i j0 - χ i0 j + χ i j)
    {ω' : Section1.ClassFunction W}
    (hω' : Section1.IsIrreducibleCharacterOnGroup ω')
    {X : Section1.ClassFunction G}
    (hX : IsSignedIrreducibleCharacter X)
    (hXV :
      ∀ x : G, ∀ hx : x ∈ cyclicTISet W1 W2 W,
        X x = ω' ⟨x, cyclicTISet_subset W1 W2 W hx⟩) :
    X = sigmaOfPF35 ω χ ω' := by
  exact signed_irreducible_eq_sigmaOfPF35_of_irreducible_agrees_pf39
    (W1 := W1) (W2 := W2) (W := W)
    (I := I) (J := J) (i0 := i0) (j0 := j0)
    (ω := ω) (χ := χ) h hω horth hsigned h00 hInd hω' hX hXV


/-- A PF `(3.2)` map commutes with complex conjugation on irreducible
characters.  This is the complex-conjugation instance of PF `(3.9.a)`, proved
from cyclic-TI agreement and the uniqueness of the signed irreducible image. -/
public theorem theorem_3_2_map_conjugateCharacter_of_irreducible
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (h31 : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (hσ : theorem_3_2_map_statement W1 W2 W σ)
    {η : Section1.ClassFunction W}
    (hη : Section1.IsIrreducibleCharacterOnGroup η) :
    σ (Section1.conjugateCharacter η) =
      Section1.conjugateCharacter (σ η) := by
  classical
  have hσcopy := hσ
  rcases pf35_data_of_theorem_3_2_map_statement hω σ hσ with
    ⟨χ, horth, hsigned, h00, hInd, hσω⟩
  have hσeq : σ = sigmaOfPF35 ω χ :=
    sigma_eq_sigmaOfPF35_of_sigma_eq_omega_pf39
      (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h31 hω hσω
  have hηbar : Section1.IsIrreducibleCharacterOnGroup
      (Section1.conjugateCharacter η) :=
    Section1.isIrreducibleCharacterOnGroup_conjugateCharacter hη
  rcases hσcopy with
    ⟨hiso, hvirt, _hind, _hclass, _hprincipal, hagree, _hvanish⟩
  have hηclass : Section1.IsClassFunction η :=
    isVirtualCharacter_isClassFunction
      (isVirtualCharacter_of_irreducibleCharacterOnGroup hη)
  have hσηsigned : IsSignedIrreducibleCharacter (σ η) := by
    have hvirtη : Theory.Character.IsVirtualCharacter η :=
      isVirtualCharacter_of_irreducibleCharacterOnGroup hη
    have hvirtση : Theory.Character.IsVirtualCharacter (σ η) := hvirt η hvirtη
    have hself : Section1.scalarProduct G (σ η) (σ η) = 1 := by
      calc
        Section1.scalarProduct G (σ η) (σ η) =
            Section1.scalarProduct W η η := hiso η η hηclass hηclass
        _ = 1 := Section1.scalarProduct_irreducibleCharacter_self hη
    exact signed_irreducible_of_virtual_norm_one_pf39 hvirtση hself
  have hbarSigned :
      IsSignedIrreducibleCharacter (Section1.conjugateCharacter (σ η)) := by
    rcases hσηsigned with ⟨ε, hε, μ, hμ, hEq⟩
    refine ⟨ε, hε, Section1.conjugateCharacter μ,
      Section1.isIrreducibleCharacterOnGroup_conjugateCharacter hμ, ?_⟩
    rw [hEq]
    rcases hε with rfl | rfl <;>
      ext g <;> simp [Section1.conjugateCharacter]
  have hagreeBar : ∀ x : G, ∀ hx : x ∈ cyclicTISet W1 W2 W,
      Section1.conjugateCharacter (σ η) x =
        Section1.conjugateCharacter η
          ⟨x, cyclicTISet_subset W1 W2 W hx⟩ := by
    intro x hx
    simp only [Section1.conjugateCharacter]
    rw [hagree η hηclass x hx]
  have hmodel :
      Section1.conjugateCharacter (σ η) =
        sigmaOfPF35 ω χ (Section1.conjugateCharacter η) :=
    proposition_3_9_a_uniqueness_of_pf35
      (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h31 hω horth hsigned h00 hInd
      hηbar hbarSigned hagreeBar
  calc
    σ (Section1.conjugateCharacter η) =
        sigmaOfPF35 ω χ (Section1.conjugateCharacter η) := by rw [hσeq]
    _ = Section1.conjugateCharacter (σ η) := hmodel.symm

/-- The first clause of `proposition_3_9_statement` in the explicit PF (3.5)
setting. -/
public theorem proposition_3_9_statement_a_uniqueness_of_pf35
    {G : Type u} [Group G] [Finite G]
    (W1 W2 W : Subgroup G)
    (I J : Type*) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → Section1.ClassFunction W)
    (χ : I → J → Section1.ClassFunction G)
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (horth : IsOrthonormalDoubleFamily χ)
    (hsigned : ∀ i j, IsSignedIrreducibleCharacter (χ i j))
    (h00 : χ i0 j0 = Section1.principalCharacter G)
    (hInd : ∀ i j, i ≠ i0 → j ≠ j0 →
      Section1.inducedCF W (alphaIJ W i0 j0 ω i j) =
        Section1.principalCharacter G - χ i j0 - χ i0 j + χ i j) :
    ∀ {ω' : Section1.ClassFunction W},
      Section1.IsIrreducibleCharacterOnGroup ω' →
        ∀ {X : Section1.ClassFunction G},
          IsSignedIrreducibleCharacter X →
            (∀ x : G, ∀ hx : x ∈ cyclicTISet W1 W2 W,
              X x = ω' ⟨x, cyclicTISet_subset W1 W2 W hx⟩) →
            X = sigmaOfPF35 ω χ ω' := by
  intro ω' hω' X hX hXV
  exact proposition_3_9_a_uniqueness_of_pf35
    (W1 := W1) (W2 := W2) (W := W)
    (I := I) (J := J) (i0 := i0) (j0 := j0)
    (ω := ω) (χ := χ) h hω horth hsigned h00 hInd hω' hX hXV

/--
The PF (3.5) realization of the Dade map has the restriction property from
PF (3.2)(c): on `V = W \ (W₁ ∪ W₂)`, `sigmaOfPF35 ω χ α` agrees with `α`.
This is the reusable interface used in PF (3.9) and in the beginning of
Section 4.
-/
public theorem sigmaOfPF35_agreesOnCyclicTISet_of_pf35
    {G : Type u} [Group G] [Finite G]
    (W1 W2 W : Subgroup G)
    (I J : Type*) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → Section1.ClassFunction W)
    (χ : I → J → Section1.ClassFunction G)
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (horth : IsOrthonormalDoubleFamily χ)
    (hsigned : ∀ i j, IsSignedIrreducibleCharacter (χ i j))
    (h00 : χ i0 j0 = Section1.principalCharacter G)
    (hInd : ∀ i j, i ≠ i0 → j ≠ j0 →
      Section1.inducedCF W (alphaIJ W i0 j0 ω i j) =
        Section1.principalCharacter G - χ i j0 - χ i0 j + χ i j) :
    AgreesOnCyclicTISet W1 W2 W (sigmaOfPF35 ω χ) := by
  exact agreesOnCyclicTISet_sigmaOfPF35_pf39
    (W1 := W1) (W2 := W2) (W := W)
    (I := I) (J := J) (i0 := i0) (j0 := j0)
    (ω := ω) (χ := χ) h hω horth hsigned h00 hInd

/-- The PF (3.5) realization of the Dade map is a scalar-product isometry. -/
public theorem sigmaOfPF35_isCFLinearIsometry_of_pf35
    {G : Type u} [Group G] [Finite G]
    (W1 W2 W : Subgroup G)
    (I J : Type*) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → Section1.ClassFunction W)
    (χ : I → J → Section1.ClassFunction G)
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (horth : IsOrthonormalDoubleFamily χ)
    (hsigned : ∀ i j, IsSignedIrreducibleCharacter (χ i j))
    (h00 : χ i0 j0 = Section1.principalCharacter G)
    (hInd : ∀ i j, i ≠ i0 → j ≠ j0 →
      Section1.inducedCF W (alphaIJ W i0 j0 ω i j) =
        Section1.principalCharacter G - χ i j0 - χ i0 j + χ i j) :
    IsCFLinearIsometry (sigmaOfPF35 ω χ) := by
  exact isCFLinearIsometry_sigmaOfPF35_pf39
    (W1 := W1) (W2 := W2) (W := W)
    (I := I) (J := J) (i0 := i0) (j0 := j0)
    (ω := ω) (χ := χ) h hω horth hsigned h00 hInd

/-- In the explicit PF (3.5) setting, `sigmaOfPF35` sends irreducibles of `W`
to signed irreducibles of `G`. -/
public theorem sigmaOfPF35_signed_irreducible_of_irreducible
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : I → J → Section1.ClassFunction G}
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hsigned : ∀ i j, IsSignedIrreducibleCharacter (χ i j))
    {ω' : Section1.ClassFunction W}
    (hω' : Section1.IsIrreducibleCharacterOnGroup ω') :
    IsSignedIrreducibleCharacter (sigmaOfPF35 ω χ ω') := by
  rcases hω.all_irreducibles ω' hω' with ⟨i, j, rfl⟩
  exact sigmaOfPF35_signed_image ω χ hω.orthonormal hsigned i j


/--
PF (3.9)(a), Galois-commutation clause in the explicit PF (3.5) setting.
The cyclotomic action hypothesis is exactly the book's restriction to
automorphisms of `ℚ_|G|`; under that hypothesis, Galois conjugation preserves
the irreducible/signed-irreducible character conditions needed by uniqueness.
-/
public theorem proposition_3_9_a_galois_of_pf35
    {G : Type u} [Group G] [Finite G]
    (W1 W2 W : Subgroup G)
    (I J : Type*) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → Section1.ClassFunction W)
    (χ : I → J → Section1.ClassFunction G)
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (horth : IsOrthonormalDoubleFamily χ)
    (hsigned : ∀ i j, IsSignedIrreducibleCharacter (χ i j))
    (h00 : χ i0 j0 = Section1.principalCharacter G)
    (hInd : ∀ i j, i ≠ i0 → j ≠ j0 →
      Section1.inducedCF W (alphaIJ W i0 j0 ω i j) =
        Section1.principalCharacter G - χ i j0 - χ i0 j + χ i j) :
    proposition_3_9_statement_a_galois (sigmaOfPF35 ω χ) := by
  intro ω' τ hω' hτ
  have hωτ :
      Section1.IsIrreducibleCharacterOnGroup
        (classFunctionGaloisConjugate τ ω') :=
    irreducibleCharacterOnGroup_galoisConjugate_of_cyclotomicAction_pf39
      (G := W) (χ := ω') τ hω'
      (cyclotomicGaloisAction_subgroup_pf39 W hτ)
  have hσsigned : IsSignedIrreducibleCharacter (sigmaOfPF35 ω χ ω') :=
    sigmaOfPF35_signed_irreducible_of_irreducible
      (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) hω hsigned hω'
  have hX :
      IsSignedIrreducibleCharacter
        (classFunctionGaloisConjugate τ (sigmaOfPF35 ω χ ω')) :=
    signedIrreducibleCharacter_galoisConjugate_of_cyclotomicAction_pf39
      (G := G) (χ := sigmaOfPF35 ω χ ω') τ hσsigned hτ
  have hagree :
      ∀ x : G, ∀ hx : x ∈ cyclicTISet W1 W2 W,
        classFunctionGaloisConjugate τ (sigmaOfPF35 ω χ ω') x =
          classFunctionGaloisConjugate τ ω'
            ⟨x, cyclicTISet_subset W1 W2 W hx⟩ := by
    intro x hx
    unfold classFunctionGaloisConjugate
    congr 1
    exact
      (sigmaOfPF35_agreesOnCyclicTISet_of_pf35
        (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (i0 := i0) (j0 := j0)
        (ω := ω) (χ := χ) h hω horth hsigned h00 hInd)
        ω' (isClassFunction_of_irreducibleCharacterOnGroup_pf39 hω') x hx
  exact proposition_3_9_a_uniqueness_of_pf35
    (W1 := W1) (W2 := W2) (W := W)
    (I := I) (J := J) (i0 := i0) (j0 := j0)
    (ω := ω) (χ := χ) h hω horth hsigned h00 hInd
    hωτ hX hagree


/--
PF (3.9)(b), Galois-identification bridge in the explicit PF (3.5) setting:
if the selected automorphism acts as the `e`-power map on `|G|`-th roots and
`ωk(w) = ω'(w ^ e)`, then `σ(ωk)` is the Galois conjugate of `σ(ω')`.
-/
public theorem proposition_3_9_b_galois_identification_of_pf35
    {G : Type u} [Group G] [Finite G]
    (W1 W2 W : Subgroup G)
    (I J : Type*) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → Section1.ClassFunction W)
    (χ : I → J → Section1.ClassFunction G)
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (horth : IsOrthonormalDoubleFamily χ)
    (hsigned : ∀ i j, IsSignedIrreducibleCharacter (χ i j))
    (h00 : χ i0 j0 = Section1.principalCharacter G)
    (hInd : ∀ i j, i ≠ i0 → j ≠ j0 →
      Section1.inducedCF W (alphaIJ W i0 j0 ω i j) =
        Section1.principalCharacter G - χ i j0 - χ i0 j + χ i j)
    {ω' ωk : Section1.ClassFunction W}
    (hω' : Section1.IsIrreducibleCharacterOnGroup ω')
    {τ : Gal(ℂ/ℚ)} {e : ℕ}
    (hτ : cyclotomicGaloisAction (Nat.card G) τ)
    (hτroot : ∀ z : ℂ, z ^ Nat.card G = 1 → τ z = z ^ e)
    (hargW : classFunctionArgumentPow ω' ωk e) :
    sigmaOfPF35 ω χ ωk =
      classFunctionGaloisConjugate τ (sigmaOfPF35 ω χ ω') := by
  have hWconj :
      classFunctionGaloisConjugate τ ω' = ωk := by
    exact classFunctionGaloisConjugate_eq_of_argumentPow_rootAction_pf39
      (G := W) (χ := ω') (χe := ωk) τ hω'
      (N := Nat.card G) (e := e)
      (Subgroup.card_subgroup_dvd_card W) hτroot hargW
  have hcomm :
      classFunctionGaloisConjugate τ (sigmaOfPF35 ω χ ω') =
        sigmaOfPF35 ω χ (classFunctionGaloisConjugate τ ω') :=
    proposition_3_9_a_galois_of_pf35
      (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω horth hsigned h00 hInd
      (ω' := ω') τ hω' hτ
  calc
    sigmaOfPF35 ω χ ωk =
        sigmaOfPF35 ω χ (classFunctionGaloisConjugate τ ω') := by
          simp [hWconj]
    _ = classFunctionGaloisConjugate τ (sigmaOfPF35 ω χ ω') := hcomm.symm

/--
PF `(3.9)(b)` argument-power bridge in the explicit PF `(3.5)` setting.  A
compatible root-action automorphism gives the argument-power action on the
G-side Galois conjugate, and the Galois-identification bridge transfers it to
`σ(ωk)`.
-/
public theorem proposition_3_9_b_argument_pow_of_rootAction_pf35
    {G : Type u} [Group G] [Finite G]
    (W1 W2 W : Subgroup G)
    (I J : Type*) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → Section1.ClassFunction W)
    (χ : I → J → Section1.ClassFunction G)
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (horth : IsOrthonormalDoubleFamily χ)
    (hsigned : ∀ i j, IsSignedIrreducibleCharacter (χ i j))
    (h00 : χ i0 j0 = Section1.principalCharacter G)
    (hInd : ∀ i j, i ≠ i0 → j ≠ j0 →
      Section1.inducedCF W (alphaIJ W i0 j0 ω i j) =
        Section1.principalCharacter G - χ i j0 - χ i0 j + χ i j)
    {ω' ωk : Section1.ClassFunction W}
    (hω' : Section1.IsIrreducibleCharacterOnGroup ω')
    {τ : Gal(ℂ/ℚ)} {e : ℕ}
    (hτ : cyclotomicGaloisAction (Nat.card G) τ)
    (hτroot : ∀ z : ℂ, z ^ Nat.card G = 1 → τ z = z ^ e)
    (hargW : classFunctionArgumentPow ω' ωk e) :
    classFunctionArgumentPow
      (sigmaOfPF35 ω χ ω') (sigmaOfPF35 ω χ ωk) e := by
  have hσ :
      sigmaOfPF35 ω χ ωk =
        classFunctionGaloisConjugate τ (sigmaOfPF35 ω χ ω') :=
    proposition_3_9_b_galois_identification_of_pf35
      (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω horth hsigned h00 hInd hω'
      hτ hτroot hargW
  have hσsigned : IsSignedIrreducibleCharacter (sigmaOfPF35 ω χ ω') :=
    sigmaOfPF35_signed_irreducible_of_irreducible
      (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) hω hsigned hω'
  have hargConj :
      classFunctionArgumentPow
        (sigmaOfPF35 ω χ ω')
        (classFunctionGaloisConjugate τ (sigmaOfPF35 ω χ ω')) e :=
    classFunctionArgumentPow_galoisConjugate_of_rootAction_pf39
      (G := G) (χ := sigmaOfPF35 ω χ ω') τ hσsigned
      (N := Nat.card G) (e := e) (dvd_refl (Nat.card G)) hτroot
  intro g
  calc
    sigmaOfPF35 ω χ ωk g =
        classFunctionGaloisConjugate τ (sigmaOfPF35 ω χ ω') g := by
          rw [hσ]
    _ = sigmaOfPF35 ω χ ω' (g ^ e) := hargConj g


/--
PF `(3.9)(b)` pointwise equality in the integer-congruence form used by the
structured statement.  The value-order part `c` has the same prime divisors as
the multiplicative order parameter `a`, so an element whose order is coprime to
`a` is also coprime to `c`.
-/
public theorem proposition_3_9_b_pointwise_of_argument_pow_int_pf35
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : I → J → Section1.ClassFunction G}
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hsigned : ∀ i j, IsSignedIrreducibleCharacter (χ i j))
    {ω' ωk : Section1.ClassFunction W}
    (hω' : Section1.IsIrreducibleCharacterOnGroup ω')
    {a c b e : ℕ} {k : ℤ}
    (hcpart : valueOrderCardPart a c)
    (hcard : Nat.card G = c * b)
    (hea : (e : ℤ) ≡ k [ZMOD c])
    (heb : (e : ℤ) ≡ (1 : ℤ) [ZMOD b])
    (harg :
      classFunctionArgumentPow
        (sigmaOfPF35 ω χ ω') (sigmaOfPF35 ω χ ωk) e)
    (g : G) (hg : (orderOf g).Coprime a) :
    sigmaOfPF35 ω χ ωk g = sigmaOfPF35 ω χ ω' g := by
  have hgc : (orderOf g).Coprime c :=
    coprime_of_valueOrderCardPart_pf39 hcpart hg
  calc
    sigmaOfPF35 ω χ ωk g = sigmaOfPF35 ω χ ω' (g ^ e) := harg g
    _ = sigmaOfPF35 ω χ ω' g :=
        signed_irreducible_value_eq_on_coprime_zpow_pf39
          (sigmaOfPF35_signed_irreducible_of_irreducible
            (W1 := W1) (W2 := W2) (W := W)
            (I := I) (J := J) (i0 := i0) (j0 := j0)
            (ω := ω) (χ := χ) hω hsigned hω')
          hcard hea heb g hgc

/--
PF `(3.9)(b)` transport-field package for the structured statement.  Once the
CRT/root-action data and the W-side argument-power witness are available, this
produces the Galois equality, the G-side argument-power field, and the
coprime-order pointwise equality.
-/
public theorem proposition_3_9_b_transport_fields_of_rootAction_pf35
    {G : Type u} [Group G] [Finite G]
    (W1 W2 W : Subgroup G)
    (I J : Type*) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → Section1.ClassFunction W)
    (χ : I → J → Section1.ClassFunction G)
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (horth : IsOrthonormalDoubleFamily χ)
    (hsigned : ∀ i j, IsSignedIrreducibleCharacter (χ i j))
    (h00 : χ i0 j0 = Section1.principalCharacter G)
    (hInd : ∀ i j, i ≠ i0 → j ≠ j0 →
      Section1.inducedCF W (alphaIJ W i0 j0 ω i j) =
        Section1.principalCharacter G - χ i j0 - χ i0 j + χ i j)
    {ω' ωk : Section1.ClassFunction W}
    (hω' : Section1.IsIrreducibleCharacterOnGroup ω')
    {a c b e : ℕ} {k : ℤ} {τ : Gal(ℂ/ℚ)}
    (hcpart : valueOrderCardPart a c)
    (hcard : Nat.card G = c * b)
    (hτroot : ∀ z : ℂ, z ^ (c * b) = 1 → τ z = z ^ e)
    (hecop : e.Coprime (c * b))
    (hea : (e : ℤ) ≡ k [ZMOD c])
    (heb : (e : ℤ) ≡ (1 : ℤ) [ZMOD b])
    (hargW : classFunctionArgumentPow ω' ωk e) :
    sigmaOfPF35 ω χ ωk =
        classFunctionGaloisConjugate τ (sigmaOfPF35 ω χ ω') ∧
      classFunctionArgumentPow
        (sigmaOfPF35 ω χ ω') (sigmaOfPF35 ω χ ωk) e ∧
      ∀ g : G, (orderOf g).Coprime a →
        sigmaOfPF35 ω χ ωk g = sigmaOfPF35 ω χ ω' g := by
  have hcard' : Fintype.card G = c * b := by
    simpa [Nat.card_eq_fintype_card] using hcard
  have hτrootNat :
      ∀ z : ℂ, z ^ Nat.card G = 1 → τ z = z ^ e := by
    intro z hz
    exact hτroot z (by simpa [hcard'] using hz)
  have hτ : cyclotomicGaloisAction (Nat.card G) τ := by
    refine ⟨e, ?_, hτrootNat⟩
    simpa [hcard'] using hecop
  have hσ :
      sigmaOfPF35 ω χ ωk =
        classFunctionGaloisConjugate τ (sigmaOfPF35 ω χ ω') :=
    proposition_3_9_b_galois_identification_of_pf35
      (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω horth hsigned h00 hInd hω'
      hτ hτrootNat hargW
  have harg :
      classFunctionArgumentPow
        (sigmaOfPF35 ω χ ω') (sigmaOfPF35 ω χ ωk) e :=
    proposition_3_9_b_argument_pow_of_rootAction_pf35
      (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω horth hsigned h00 hInd hω'
      hτ hτrootNat hargW
  refine ⟨hσ, harg, ?_⟩
  intro g hg
  exact proposition_3_9_b_pointwise_of_argument_pow_int_pf35
    (W1 := W1) (W2 := W2) (W := W)
    (I := I) (J := J) (i0 := i0) (j0 := j0)
    (ω := ω) (χ := χ) hω hsigned hω'
    hcpart hcard hea heb harg g hg


private theorem exists_irreducible_argumentPow_on_cyclic_subgroup_pf39
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    (h : hypothesis_3_1_statement W1 W2 W)
    {ω' : Section1.ClassFunction W}
    (hω' : Section1.IsIrreducibleCharacterOnGroup ω')
    {e : ℕ} (he : e.Coprime (Nat.card G)) :
    ∃ ωk : Section1.ClassFunction W,
      Section1.IsIrreducibleCharacterOnGroup ωk ∧
      classFunctionArgumentPow ω' ωk e := by
  rcases h with ⟨_hW1, _hW2, _hIP, hcyc, _hodd, _hcard1, _hcard2, _hTI⟩
  letI : IsCyclic W := hcyc
  letI : CommGroup W := IsCyclic.commGroup
  have heW : e.Coprime (Nat.card W) := by
    exact Nat.Coprime.of_dvd_right (Subgroup.card_subgroup_dvd_card W) he
  refine ⟨fun w : W => ω' (w ^ e), ?_, ?_⟩
  · exact irreducibleCharacterOnGroup_argumentPow_of_coprime_natCard_comm_pf39 hω' heW
  · intro w
    rfl

/--
PF `(3.9)(b)` structured assembly from the current PF `(3.5)` realization,
assuming the standard complex extension of a coprime root-power action.  This
keeps the remaining global cyclotomic-to-`ℂ` extension fact explicit rather
than hiding it in the PF `(3.9)` proof.
-/
public theorem proposition_3_9_b_structured_of_rootAction_pf35
    {G : Type u} [Group G] [Finite G]
    (W1 W2 W : Subgroup G)
    (I J : Type*) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → Section1.ClassFunction W)
    (χ : I → J → Section1.ClassFunction G)
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (horth : IsOrthonormalDoubleFamily χ)
    (hsigned : ∀ i j, IsSignedIrreducibleCharacter (χ i j))
    (h00 : χ i0 j0 = Section1.principalCharacter G)
    (hInd : ∀ i j, i ≠ i0 → j ≠ j0 →
      Section1.inducedCF W (alphaIJ W i0 j0 ω i j) =
        Section1.principalCharacter G - χ i j0 - χ i0 j + χ i j)
    (hroot :
      ∀ {c b e : ℕ}, e.Coprime (c * b) →
        ∃ τ : Gal(ℂ/ℚ), ∀ z : ℂ, z ^ (c * b) = 1 → τ z = z ^ e) :
    proposition_3_9_statement_b_structured (sigmaOfPF35 ω χ) := by
  classical
  intro ω' a k hω' ha hk
  have ha0 : 0 < a := ha.1.1
  have ha_dvd_card : a ∣ Nat.card G :=
    exactCharacterValueOrder_dvd_natCard_of_pf39
      (G := G) (W1 := W1) (W2 := W2) (W := W) h hω' ha
  have hcard_ne : Nat.card G ≠ 0 := Nat.card_pos.ne'
  obtain ⟨c, b, hcpart, hcard, hcop⟩ :=
    exists_valueOrderCardPart_factorization_pf39 ha0 ha_dvd_card hcard_ne
  have hkc_nat : k.natAbs.Coprime c :=
    coprime_of_valueOrderCardPart_pf39 hcpart
      (natAbs_coprime_of_int_isCoprime_pf39 hk)
  have hkc : IsCoprime k (c : ℤ) :=
    int_isCoprime_of_natAbs_coprime_pf39 hkc_nat
  have hn : c * b ≠ 0 :=
    Section1.nat_card_factor_ne_zero (G := G) hcard
  haveI : NeZero c := ⟨left_ne_zero_of_mul hn⟩
  obtain ⟨v, hv⟩ :=
    Section1.proposition_1_9_b_galois_automorphism_int
      (a := c) (b := b) (k := k) hn hcop hkc
  obtain ⟨w, hwa, hwb⟩ :=
    Section1.zmod_units_crt_exists_of_coprime hcop (ZMod.unitOfIsCoprime k hkc)
  let e : ℕ := (w : ZMod (c * b)).val
  have hea : (e : ℤ) ≡ k [ZMOD c] :=
    Section1.zmod_units_crt_val_modEq_left_int hn hkc hwa
  have heb : (e : ℤ) ≡ (1 : ℤ) [ZMOD b] :=
    Section1.zmod_units_crt_val_modEq_right_one hn hwb
  have hecop : e.Coprime (c * b) := by
    simpa [e] using ZMod.val_coe_unit_coprime w
  obtain ⟨τ, hτroot⟩ := hroot (c := c) (b := b) (e := e) hecop
  haveI : IsCyclic W := by
    rcases h with ⟨_hW1, _hW2, _hIP, hcyc, _hodd, _hcard1, _hcard2, _hTI⟩
    exact hcyc
  letI : CommGroup W := IsCyclic.commGroup
  have hcardF : Fintype.card G = c * b := by
    simpa [Nat.card_eq_fintype_card] using hcard
  have hecopG : e.Coprime (Nat.card G) := by
    simpa [Nat.card_eq_fintype_card, hcardF] using hecop
  obtain ⟨ωk, hωk, hargW⟩ :=
    exists_irreducible_argumentPow_on_cyclic_subgroup_pf39
      (G := G) (W1 := W1) (W2 := W2) (W := W) h hω' hecopG
  have hvalue : classFunctionValueZPow ω' ωk k :=
    classFunctionValueZPow_of_argumentPow_congr_pf39
      (H := W) hω' ha hcpart hea hargW
  have hgal :
      proposition_3_9_galoisCondition_int
        (G := G) (c := c) (b := b) (k := k) hcard v := by
    exact ⟨hkc, by
      dsimp [Section1.proposition_1_9_b_galoisCondition_int]
      exact hv⟩
  rcases proposition_3_9_b_transport_fields_of_rootAction_pf35
      (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω horth hsigned h00 hInd
      (ω' := ω') (ωk := ωk) (a := a) (c := c) (b := b)
      (e := e) (k := k) (τ := τ)
      hω' hcpart hcard hτroot hecop hea heb hargW with
    ⟨hσ, hargG, hpoint⟩
  refine ⟨ωk, hωk, hvalue, c, b, hcpart, hcard, hcop, v, τ, e,
    hgal, hτroot, hecop, hea, heb, hσ, hargG, hpoint⟩

/--
Auxiliary complex-Galois PF `(3.9)(b)` endpoint, from the structured proof
route plus the explicit global root-action extension hypothesis.
-/
public theorem proposition_3_9_b_of_rootAction_pf35
    {G : Type u} [Group G] [Finite G]
    (W1 W2 W : Subgroup G)
    (I J : Type*) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → Section1.ClassFunction W)
    (χ : I → J → Section1.ClassFunction G)
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (horth : IsOrthonormalDoubleFamily χ)
    (hsigned : ∀ i j, IsSignedIrreducibleCharacter (χ i j))
    (h00 : χ i0 j0 = Section1.principalCharacter G)
    (hInd : ∀ i j, i ≠ i0 → j ≠ j0 →
      Section1.inducedCF W (alphaIJ W i0 j0 ω i j) =
        Section1.principalCharacter G - χ i j0 - χ i0 j + χ i j)
    (hroot :
      ∀ {c b e : ℕ}, e.Coprime (c * b) →
        ∃ τ : Gal(ℂ/ℚ), ∀ z : ℂ, z ^ (c * b) = 1 → τ z = z ^ e) :
    proposition_3_9_statement_b_complex_galois (sigmaOfPF35 ω χ) := by
  exact proposition_3_9_statement_b_of_structured
    (proposition_3_9_b_structured_of_rootAction_pf35
      (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω horth hsigned h00 hInd hroot)


/--
PF (3.9)(c), final algebraic-integer step: once the Galois argument has shown
that a `sigmaOfPF35` value is rational, signed irreducibility makes it an
ordinary integer.
-/
public theorem proposition_3_9_c_of_rational_value_pf35
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : I → J → Section1.ClassFunction G}
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hsigned : ∀ i j, IsSignedIrreducibleCharacter (χ i j))
    {ω' : Section1.ClassFunction W}
    (hω' : Section1.IsIrreducibleCharacterOnGroup ω')
    {g : G}
    (hrat : ∃ q : ℚ, sigmaOfPF35 ω χ ω' g = (q : ℂ)) :
    ∃ n : ℤ, sigmaOfPF35 ω χ ω' g = (n : ℂ) := by
  exact exists_int_of_signed_irreducible_value_rat_pf39
    (sigmaOfPF35_signed_irreducible_of_irreducible
      (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) hω hsigned hω')
    hrat

/--
Auxiliary PF `(3.9)(c)` endpoint: once a `sigmaOfPF35` value is known to be
rational, it is in fact an ordinary integer.  The full book-facing statement
is `proposition_3_9_statement_c`.
-/
public theorem proposition_3_9_c_integer_of_rational_value_pf35
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : I → J → Section1.ClassFunction G}
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hsigned : ∀ i j, IsSignedIrreducibleCharacter (χ i j))
    {ω' : Section1.ClassFunction W}
    (hω' : Section1.IsIrreducibleCharacterOnGroup ω')
    {g : G}
    (hrat : ∃ q : ℚ, sigmaOfPF35 ω χ ω' g = (q : ℂ)) :
    ∃ n : ℤ, sigmaOfPF35 ω χ ω' g = (n : ℂ) := by
  exact proposition_3_9_c_of_rational_value_pf35
    (W1 := W1) (W2 := W2) (W := W)
    (I := I) (J := J) (i0 := i0) (j0 := j0)
    (ω := ω) (χ := χ) hω hsigned hω' hrat


/--
PF `(3.9)(c)` cyclotomic-field precursor: every value of a `sigmaOfPF35`
image of an irreducible character of `W` lies in the cyclotomic order
generated by a primitive `|G|`-th root.
-/
public theorem proposition_3_9_c_value_mem_cyclotomicOrder_pf35
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : I → J → Section1.ClassFunction G}
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hsigned : ∀ i j, IsSignedIrreducibleCharacter (χ i j))
    {ω' : Section1.ClassFunction W}
    (hω' : Section1.IsIrreducibleCharacterOnGroup ω')
    {η : ℂ} (hη : IsPrimitiveRoot η (Nat.card G)) (g : G) :
    sigmaOfPF35 ω χ ω' g ∈ Theory.Character.cyclotomicOrder η := by
  have hsignedImage :
      IsSignedIrreducibleCharacter (sigmaOfPF35 ω χ ω') :=
    sigmaOfPF35_signed_irreducible_of_irreducible
      (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) hω hsigned hω'
  exact Theory.Character.virtualCharacter_mem_cyclotomicOrder
    (isVirtualCharacter_of_signedIrreducible_pf35 hsignedImage) hη g

/-- Build a concrete cyclotomic-field model for a value known to lie in the
cyclotomic order generated by a primitive `(c * b)`-th root. -/
public theorem pf39_cyclotomic_model_of_mem_cyclotomicOrder
    {c b : ℕ} (hn : c * b ≠ 0) {η z : ℂ}
    (hη : IsPrimitiveRoot η (c * b))
    (hz : z ∈ Theory.Character.cyclotomicOrder η) :
    ∃ ι : Section1.CyclotomicABField c b →ₐ[ℚ] ℂ,
    ∃ P : Polynomial ℤ,
    ∃ x : Section1.CyclotomicABField c b,
      z = ι x ∧
        x = Polynomial.eval₂ (Int.castRingHom (Section1.CyclotomicABField c b))
          (Section1.cyclotomicABRoot c b hn) P ∧
        ι (Section1.cyclotomicABRoot c b hn) = η := by
  letI : NeZero (c * b) := ⟨hn⟩
  let K := Section1.CyclotomicABField c b
  let ζ : K := Section1.cyclotomicABRoot c b hn
  have hζ : IsPrimitiveRoot ζ (c * b) := by
    dsimp [ζ, Section1.cyclotomicABRoot, K, Section1.CyclotomicABField]
    exact IsCyclotomicExtension.zeta_spec (c * b) ℚ (CyclotomicField (c * b) ℚ)
  have hirr : Irreducible (Polynomial.cyclotomic (c * b) ℚ) :=
    Polynomial.cyclotomic.irreducible_rat (NeZero.pos (c * b))
  let ηroot : primitiveRoots (c * b) ℂ := ⟨η, by
    rw [mem_primitiveRoots (NeZero.pos (c * b))]
    exact hη⟩
  let ι : K →ₐ[ℚ] ℂ := (hζ.embeddingsEquivPrimitiveRoots ℂ hirr).symm ηroot
  have hιζ : ι ζ = η := by
    change ((hζ.embeddingsEquivPrimitiveRoots ℂ hirr) ι : ℂ) = η
    simp [ι, ηroot]
  rcases Theory.Character.mem_cyclotomicOrder_iff_exists_intPolynomial_eval.mp hz with
    ⟨P, hP⟩
  let x : K := Polynomial.eval₂ (Int.castRingHom K) ζ P
  refine ⟨ι, P, x, ?_, ?_, ?_⟩
  · rw [← hP]
    change Polynomial.eval₂ (Int.castRingHom ℂ) η P = ι x
    rw [← hιζ]
    dsimp [x]
    exact (Polynomial.ringHom_eval₂_intCastRingHom P ι.toRingHom ζ).symm
  · rfl
  · exact hιζ

public theorem pf39_complex_eval_of_cyclotomicAB_aut
    {c b : ℕ} (hn : c * b ≠ 0)
    (ι : Section1.CyclotomicABField c b →ₐ[ℚ] ℂ)
    (P : Polynomial ℤ)
    (v : Gal((Section1.CyclotomicABField c b)/ℚ)) :
    ι (v (Polynomial.eval₂ (Int.castRingHom (Section1.CyclotomicABField c b))
      (Section1.cyclotomicABRoot c b hn) P)) =
      Polynomial.eval₂ (Int.castRingHom ℂ)
        (ι (v (Section1.cyclotomicABRoot c b hn))) P := by
  let K := Section1.CyclotomicABField c b
  let ζ : K := Section1.cyclotomicABRoot c b hn
  change ι (v (Polynomial.eval₂ (Int.castRingHom K) ζ P)) =
    Polynomial.eval₂ (Int.castRingHom ℂ) (ι (v ζ)) P
  have hvEval :
      v (Polynomial.eval₂ (Int.castRingHom K) ζ P) =
        Polynomial.eval₂ (Int.castRingHom K) (v ζ) P :=
    Polynomial.ringHom_eval₂_intCastRingHom P v.toRingEquiv.toRingHom ζ
  rw [hvEval]
  exact Polynomial.ringHom_eval₂_intCastRingHom P ι.toRingHom (v ζ)

public theorem pf39_fixed_intPolynomial_of_complex_eval_fixed
    {c b : ℕ} (hn : c * b ≠ 0)
    (ι : Section1.CyclotomicABField c b →ₐ[ℚ] ℂ)
    (P : Polynomial ℤ)
    (v : Gal((Section1.CyclotomicABField c b)/ℚ))
    (hfixed :
      Polynomial.eval₂ (Int.castRingHom ℂ)
        (ι (v (Section1.cyclotomicABRoot c b hn))) P =
      Polynomial.eval₂ (Int.castRingHom ℂ)
        (ι (Section1.cyclotomicABRoot c b hn)) P) :
    v (Polynomial.eval₂ (Int.castRingHom (Section1.CyclotomicABField c b))
        (Section1.cyclotomicABRoot c b hn) P) =
      Polynomial.eval₂ (Int.castRingHom (Section1.CyclotomicABField c b))
        (Section1.cyclotomicABRoot c b hn) P := by
  apply ι.injective
  change ι (v (Polynomial.eval₂ (Int.castRingHom (Section1.CyclotomicABField c b))
      (Section1.cyclotomicABRoot c b hn) P)) =
    ι (Polynomial.eval₂ (Int.castRingHom (Section1.CyclotomicABField c b))
      (Section1.cyclotomicABRoot c b hn) P)
  rw [pf39_complex_eval_of_cyclotomicAB_aut hn ι P v]
  exact hfixed.trans
    (Polynomial.ringHom_eval₂_intCastRingHom P ι.toRingHom
      (Section1.cyclotomicABRoot c b hn)).symm

public theorem pf39_complex_image_aut_root_eq_pow
    {c b : ℕ} (hn : c * b ≠ 0)
    (ι : Section1.CyclotomicABField c b →ₐ[ℚ] ℂ)
    (v : Gal((Section1.CyclotomicABField c b)/ℚ)) :
    ∃ e : ℕ, e.Coprime (c * b) ∧
      ι (v (Section1.cyclotomicABRoot c b hn)) =
        ι (Section1.cyclotomicABRoot c b hn) ^ e := by
  letI : NeZero (c * b) := ⟨hn⟩
  let K := Section1.CyclotomicABField c b
  let ζ : K := Section1.cyclotomicABRoot c b hn
  let u : (ZMod (c * b))ˣ :=
    IsCyclotomicExtension.Rat.galEquivZMod (c * b) K v
  let e : ℕ := (u : ZMod (c * b)).val
  have hecop : e.Coprime (c * b) := by
    simpa [e] using ZMod.val_coe_unit_coprime u
  have hζ : IsPrimitiveRoot ζ (c * b) := by
    dsimp [ζ, Section1.cyclotomicABRoot, K, Section1.CyclotomicABField]
    exact IsCyclotomicExtension.zeta_spec (c * b) ℚ (CyclotomicField (c * b) ℚ)
  have hvζ : v ζ = ζ ^ e := by
    rw [IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq
      (c * b) K v hζ.pow_eq_one]
  refine ⟨e, hecop, ?_⟩
  rw [hvζ]
  exact map_pow ι ζ e

/-- PF `(3.9)(c)` rationality precursor from the structured PF `(3.9)(b)`
data: the cyclotomic model of a `sigmaOfPF35` value is fixed by every
automorphism, hence the value is rational. -/
public theorem pf39_fixed_cyclotomic_model_from_structured_b
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    (ω : I → J → Section1.ClassFunction W)
    (χ : I → J → Section1.ClassFunction G)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hsigned : ∀ i j, IsSignedIrreducibleCharacter (χ i j))
    (hA : proposition_3_9_statement_a_galois (sigmaOfPF35 ω χ))
    (hstructured : proposition_3_9_statement_b_structured (sigmaOfPF35 ω χ))
    {ω' : Section1.ClassFunction W} {a : ℕ}
    (hω' : Section1.IsIrreducibleCharacterOnGroup ω')
    (ha : exactCharacterValueOrder ω' a)
    (g : G) (hg : (orderOf g).Coprime a) :
    ∃ c b : ℕ,
    ∃ _ : c * b ≠ 0,
    ∃ ι : Section1.CyclotomicABField c b →ₐ[ℚ] ℂ,
    ∃ x : Section1.CyclotomicABField c b,
      sigmaOfPF35 ω χ ω' g = ι x ∧
        (∀ v : Gal((Section1.CyclotomicABField c b)/ℚ), v x = x) := by
  have hk1 : IsCoprime (1 : ℤ) (a : ℤ) := by
    exact isCoprime_one_left
  rcases hstructured (ω' := ω') (a := a) (k := (1 : ℤ)) hω' ha hk1 with
    ⟨ωk, _hωk, hpow, c, b, hcpart, hcard, _hcop, _v, _τ, _e,
      _hgal, _hτroot, _hecop, _hea, _heb, _hσ, _hargG, _hpoint⟩
  have hn : c * b ≠ 0 := Section1.nat_card_factor_ne_zero (G := G) hcard
  have hωk_eq : ωk = ω' := by
    ext x
    have hx := hpow x
    simpa using hx
  clear hpow hωk_eq
  let η : ℂ := Complex.exp (2 * Real.pi * Complex.I / (c * b))
  have hη : IsPrimitiveRoot η (c * b) :=
    by simpa [η] using Complex.isPrimitiveRoot_exp (c * b) hn
  have hcardF : Fintype.card G = c * b := by
    simpa [Nat.card_eq_fintype_card] using hcard
  have hηG : IsPrimitiveRoot η (Nat.card G) := by
    simpa [Nat.card_eq_fintype_card, hcardF] using hη
  have hz :
      sigmaOfPF35 ω χ ω' g ∈ Theory.Character.cyclotomicOrder η := by
    exact proposition_3_9_c_value_mem_cyclotomicOrder_pf35
      (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) hω hsigned hω' hηG g
  refine ⟨c, b, hn, ?_⟩
  rcases pf39_cyclotomic_model_of_mem_cyclotomicOrder hn hη hz with
    ⟨ι, P, x, hvalue, hx, hιζ⟩
  refine ⟨ι, x, hvalue, ?_⟩
  intro v
  rw [hx]
  refine pf39_fixed_intPolynomial_of_complex_eval_fixed hn ι P v ?_
  rcases pf39_complex_image_aut_root_eq_pow hn ι v with ⟨e, hecop, hvroot⟩
  rw [hvroot]
  rw [hιζ]
  obtain ⟨τ, hτroot⟩ := Section1.complex_galois_aut_pow_on_roots hecop
  have hecopG : e.Coprime (Nat.card G) := by
    simpa [Nat.card_eq_fintype_card, hcardF] using hecop
  have hτrootNat : ∀ z : ℂ, z ^ Nat.card G = 1 → τ z = z ^ e := by
    intro z hz
    exact hτroot z (by simpa [Nat.card_eq_fintype_card, hcardF] using hz)
  have hτcyc : cyclotomicGaloisAction (Nat.card G) τ :=
    ⟨e, hecopG, hτrootNat⟩
  have hec : e.Coprime c :=
    Nat.Coprime.of_dvd_right (Nat.dvd_mul_right c b) hecop
  have hea_nat : e.Coprime a :=
    Nat.Coprime.of_dvd_right hcpart.1 hec
  have hk : IsCoprime (e : ℤ) (a : ℤ) := by
    rw [Int.isCoprime_iff_nat_coprime]
    simpa using hea_nat
  rcases hstructured (ω' := ω') (a := a) (k := (e : ℤ)) hω' ha hk with
    ⟨ωe, _hωe, hpowe, _ce, _be, _hcpart_e, _hcard_e, _hcop_e, _ve, _τe, _ee,
      _hgal_e, _hτroot_e, _hecop_e, _hea_e, _heb_e, _hσ_e, _harg_e,
      hpoint_e⟩
  have ha_dvd_card : a ∣ Nat.card G := by
    rw [hcard]
    exact dvd_mul_of_dvd_left hcpart.1 b
  have hωroot_card : ∀ y : W, (ω' y) ^ Nat.card G = 1 := by
    intro y
    rcases ha_dvd_card with ⟨m, hm⟩
    rw [hm, pow_mul, ha.1.2 y, one_pow]
  have hconj_eq : classFunctionGaloisConjugate τ ω' = ωe := by
    ext y
    calc
      τ (ω' y) = (ω' y) ^ e := hτrootNat (ω' y) (hωroot_card y)
      _ = (ω' y) ^ (e : ℤ) := by simp
      _ = ωe y := (hpowe y).symm
  have hcomm := hA (ω' := ω') τ hω' hτcyc
  have hτ_value :
      τ (sigmaOfPF35 ω χ ω' g) = sigmaOfPF35 ω χ ω' g := by
    calc
      τ (sigmaOfPF35 ω χ ω' g) =
          classFunctionGaloisConjugate τ (sigmaOfPF35 ω χ ω') g := rfl
      _ = sigmaOfPF35 ω χ (classFunctionGaloisConjugate τ ω') g := by
            rw [hcomm]
      _ = sigmaOfPF35 ω χ ωe g := by rw [hconj_eq]
      _ = sigmaOfPF35 ω χ ω' g := hpoint_e g hg
  have hvalue_eval :
      sigmaOfPF35 ω χ ω' g =
        Polynomial.eval₂ (Int.castRingHom ℂ) η P := by
    rw [hvalue, hx]
    rw [← hιζ]
    exact Polynomial.ringHom_eval₂_intCastRingHom P ι.toRingHom
      (Section1.cyclotomicABRoot c b hn)
  have hτ_eta : τ η = η ^ e := hτroot η hη.pow_eq_one
  have hτ_eval :
      τ (Polynomial.eval₂ (Int.castRingHom ℂ) η P) =
        Polynomial.eval₂ (Int.castRingHom ℂ) (η ^ e) P := by
    rw [← hτ_eta]
    exact Polynomial.ringHom_eval₂_intCastRingHom P τ.toRingEquiv.toRingHom η
  calc
    Polynomial.eval₂ (Int.castRingHom ℂ) (η ^ e) P =
        τ (Polynomial.eval₂ (Int.castRingHom ℂ) η P) := hτ_eval.symm
    _ = τ (sigmaOfPF35 ω χ ω' g) := by rw [hvalue_eval]
    _ = sigmaOfPF35 ω χ ω' g := hτ_value
    _ = Polynomial.eval₂ (Int.castRingHom ℂ) η P := hvalue_eval

public theorem pf39_rationality_of_fixed_cyclotomic_model
    {G : Type u} [Group G] [Finite G]
    {W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (ω : I → J → Section1.ClassFunction W)
    (χ : I → J → Section1.ClassFunction G)
    {ω' : Section1.ClassFunction W} (g : G)
    {c b : ℕ}
    (hn : c * b ≠ 0)
    (ι : Section1.CyclotomicABField c b →ₐ[ℚ] ℂ)
    (x : Section1.CyclotomicABField c b)
    (hvalue : sigmaOfPF35 ω χ ω' g = ι x)
    (hfixed : ∀ v : Gal((Section1.CyclotomicABField c b)/ℚ), v x = x) :
    ∃ r : ℚ, sigmaOfPF35 ω χ ω' g = (r : ℂ) := by
  letI : NeZero (c * b) := ⟨hn⟩
  exact Section1.cyclotomicABField_complex_rat_of_fixed_gal ι x
    (sigmaOfPF35 ω χ ω' g) hvalue hfixed

/-- Generic source-facing rationality bridge for PF `(3.9)(c)`.  A Section
`(3.2)` map together with the Section `(3.3)` table determines PF `(3.5)`
data; the structured PF `(3.9)(b)` package then proves the rationality
precursor used by `(3.9)(c)`. -/
public theorem pf39_rationality_of_theorem_3_2_map_statement
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (h31 : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hσ : theorem_3_2_map_statement W1 W2 W σ) :
    ∀ {ω' : Section1.ClassFunction W} {a : ℕ},
      Section1.IsIrreducibleCharacterOnGroup ω' →
        exactCharacterValueOrder ω' a →
          ∀ g : G, (orderOf g).Coprime a →
            ∃ r : ℚ, σ ω' g = (r : ℂ) := by
  rcases pf35_data_of_theorem_3_2_map_statement hω σ hσ with
    ⟨χ, horth, hsigned, h00, hInd, hσeq⟩
  have hroot :
      ∀ {c b e : ℕ}, e.Coprime (c * b) →
        ∃ τ : Gal(ℂ/ℚ), ∀ z : ℂ, z ^ (c * b) = 1 → τ z = z ^ e := by
    intro c b e he
    exact Section1.complex_galois_aut_pow_on_roots he
  have hσ_eq : σ = sigmaOfPF35 ω χ :=
    sigma_eq_sigmaOfPF35_of_sigma_eq_omega_pf39
      (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h31 hω hσeq
  have hstructured :
      proposition_3_9_statement_b_structured (sigmaOfPF35 ω χ) :=
    proposition_3_9_b_structured_of_rootAction_pf35
      (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h31 hω horth hsigned h00 hInd hroot
  have hA : proposition_3_9_statement_a_galois (sigmaOfPF35 ω χ) :=
    proposition_3_9_a_galois_of_pf35
      (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h31 hω horth hsigned h00 hInd
  intro ω' a hω' ha g hg
  have hrat_pf35 : ∃ r : ℚ, sigmaOfPF35 ω χ ω' g = (r : ℂ) := by
    rcases pf39_fixed_cyclotomic_model_from_structured_b
        (W1 := W1) (W2 := W2) (W := W)
        (I := I) (J := J) (i0 := i0) (j0 := j0)
        ω χ hω hsigned hA hstructured hω' ha g hg with
      ⟨c, b, hn, ι, x, hvalue, hfixed⟩
    exact pf39_rationality_of_fixed_cyclotomic_model
      ω χ g hn ι x hvalue hfixed
  rcases hrat_pf35 with ⟨r, hr⟩
  exact ⟨r, by simpa [hσ_eq] using hr⟩

/--
PF `(3.9)(c)` in source-facing statement form, once the source Galois
rationality argument has supplied rationality of the relevant values.
-/
public theorem proposition_3_9_c_of_rationality_pf35
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {χ : I → J → Section1.ClassFunction G}
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hsigned : ∀ i j, IsSignedIrreducibleCharacter (χ i j))
    (hrat :
      ∀ {ω' : Section1.ClassFunction W} {a : ℕ},
        Section1.IsIrreducibleCharacterOnGroup ω' →
          exactCharacterValueOrder ω' a →
            ∀ g : G, (orderOf g).Coprime a →
              ∃ q : ℚ, sigmaOfPF35 ω χ ω' g = (q : ℂ)) :
    proposition_3_9_statement_c (sigmaOfPF35 ω χ) := by
  intro ω' a hω' ha g hg
  exact proposition_3_9_c_integer_of_rational_value_pf35
    (W1 := W1) (W2 := W2) (W := W)
    (I := I) (J := J) (i0 := i0) (j0 := j0)
    (ω := ω) (χ := χ) hω hsigned hω'
    (hrat hω' ha g hg)


/--
Conditional full PF `(3.9)` assembly for the explicit PF `(3.5)` realization.
The global complex root-action extension supplies the direct cyclotomic-Galois
clause in `(b)`; `hrat` supplies the Galois-fixed rationality argument used in
`(c)`.
-/
public theorem proposition_3_9_of_rootAction_and_rationality_pf35
    {G : Type u} [Group G] [Finite G]
    (W1 W2 W : Subgroup G)
    (I J : Type*) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → Section1.ClassFunction W)
    (χ : I → J → Section1.ClassFunction G)
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (horth : IsOrthonormalDoubleFamily χ)
    (hsigned : ∀ i j, IsSignedIrreducibleCharacter (χ i j))
    (h00 : χ i0 j0 = Section1.principalCharacter G)
    (hInd : ∀ i j, i ≠ i0 → j ≠ j0 →
      Section1.inducedCF W (alphaIJ W i0 j0 ω i j) =
        Section1.principalCharacter G - χ i j0 - χ i0 j + χ i j)
    (hroot :
      ∀ {c b e : ℕ}, e.Coprime (c * b) →
        ∃ τ : Gal(ℂ/ℚ), ∀ z : ℂ, z ^ (c * b) = 1 → τ z = z ^ e)
    (hrat :
      ∀ {ω' : Section1.ClassFunction W} {a : ℕ},
        Section1.IsIrreducibleCharacterOnGroup ω' →
          exactCharacterValueOrder ω' a →
            ∀ g : G, (orderOf g).Coprime a →
              ∃ q : ℚ, sigmaOfPF35 ω χ ω' g = (q : ℂ)) :
    ∀ hσ : theorem_3_2_map_statement W1 W2 W (sigmaOfPF35 ω χ),
      proposition_3_9_statement W1 W2 W (sigmaOfPF35 ω χ) h hσ := by
  intro _hσ
  have hGaloisA :
      proposition_3_9_statement_a_galois (sigmaOfPF35 ω χ) :=
    proposition_3_9_a_galois_of_pf35
      (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω horth hsigned h00 hInd
  have hGaloisB_aux :
      proposition_3_9_statement_b_complex_galois (sigmaOfPF35 ω χ) :=
    proposition_3_9_b_of_rootAction_pf35
      (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω horth hsigned h00 hInd hroot
  have hGaloisB :
      proposition_3_9_statement_b (sigmaOfPF35 ω χ) := by
    intro ω' a k hω' ha hk
    rcases hGaloisB_aux (ω' := ω') (a := a) (k := k) hω' ha hk with
      ⟨ωk, hωk, hpow, τ, hτ, hσ, hpoint⟩
    refine ⟨ωk, hωk, hpow, τ, ?_, hσ, hpoint⟩
    simpa [proposition_3_9_statement_b, Nat.card_eq_fintype_card] using hτ
  refine ⟨?_, hGaloisA, hGaloisB, ?_⟩
  · exact proposition_3_9_statement_a_uniqueness_of_pf35
      (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) h hω horth hsigned h00 hInd
  · exact proposition_3_9_c_of_rationality_pf35
      (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0)
      (ω := ω) (χ := χ) hω hsigned hrat

/--
Auxiliary PF `(3.9)(a)` uniqueness endpoint, packaged directly after PF
`(3.5)`: there is a PF `(3.5)` family `χᵢⱼ` such that every signed
irreducible character of `G` agreeing on `V = W \ (W₁ ∪ W₂)` with an
irreducible character `ω'` of `W` is exactly the `sigmaOfPF35` image of `ω'`.
The full book-facing statement is `proposition_3_9_statement`.
-/
public theorem proposition_3_9_a_uniqueness
    {G : Type u} [Group G] [Finite G]
    (W1 W2 W : Subgroup G)
    (I J : Type*) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → Section1.ClassFunction W)
    (h : hypothesis_3_1_statement W1 W2 W)
    (hω : notation_3_3_statement W1 W2 W I J i0 j0 ω) :
    ∃ χ : I → J → Section1.ClassFunction G,
      IsOrthonormalDoubleFamily χ ∧
        (∀ i j, Theory.Character.IsVirtualCharacter (χ i j)) ∧
        (∀ i j, IsSignedIrreducibleCharacter (χ i j)) ∧
        χ i0 j0 = Section1.principalCharacter G ∧
        (∀ i j, i ≠ i0 → j ≠ j0 →
          Section1.inducedCF W (alphaIJ W i0 j0 ω i j) =
            Section1.principalCharacter G - χ i j0 - χ i0 j + χ i j) ∧
        ∀ {ω' : Section1.ClassFunction W},
          Section1.IsIrreducibleCharacterOnGroup ω' →
          ∀ {X : Section1.ClassFunction G},
            IsSignedIrreducibleCharacter X →
            (∀ x : G, ∀ hx : x ∈ cyclicTISet W1 W2 W,
              X x = ω' ⟨x, cyclicTISet_subset W1 W2 W hx⟩) →
            X = sigmaOfPF35 ω χ ω' := by
  classical
  rcases proposition_3_5_signed
      (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0) (ω := ω) h hω with
    ⟨χ, horth, _hvirt, hsigned, h00, hInd⟩
  refine ⟨χ, horth, _hvirt, hsigned, h00, hInd, ?_⟩
  intro ω' hω' X hX hXV
  exact proposition_3_9_a_uniqueness_of_pf35
    (W1 := W1) (W2 := W2) (W := W)
    (I := I) (J := J) (i0 := i0) (j0 := j0)
    (ω := ω) (χ := χ) h hω horth hsigned h00 hInd hω' hX hXV

end CFSG.Section3
