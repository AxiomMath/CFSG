module

public import CFSG.Quasithin.Vol2.Ch10SecKGCFa
public import CFSG.Quasithin.Vol2.Ch10SecQ34MI

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10KG

open CFSG.Quasithin
open scoped Matrix

variable {K : Type} [Field K] [CharP K 2] (a : ℕ)

@[expose] noncomputable def frobAut [Finite K] : K ≃+* K :=
  RingEquiv.ofBijective (iterateFrobenius K 2 a) ⟨(iterateFrobenius K 2 a).injective,
    Finite.injective_iff_surjective.mp (iterateFrobenius K 2 a).injective⟩

theorem frobAut_apply [Finite K] (x : K) : frobAut a x = x ^ 2 ^ a :=
  rfl

theorem frobAut_sq [Finite K] (hK : Nat.card K = 2 ^ (2 * a)) : frobAut (K := K) a ^ 2 = 1 := by
  ext x
  change frobAut a (frobAut a x) = x
  rw [frobAut_apply, frobAut_apply, C10P34.frob_frob a hK]

theorem frobAut_ne_one [Finite K] (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a)) :
    frobAut (K := K) a ≠ 1 := by
  intro h
  obtain ⟨t, ht⟩ := C10P34.exists_trace_eq_one a ha hK
  have h1 : t ^ 2 ^ a = t := by
    rw [← frobAut_apply, h]
    rfl
  rw [h1, CharTwo.add_self_eq_zero] at ht
  exact zero_ne_one ht

theorem exists_fq [Finite K] (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a)) :
    ∃ S : Subfield K, (∀ c, c ∈ S ↔ c ^ 2 ^ a = c) ∧
      (∀ c, (∀ τ ∈ Subgroup.zpowers (frobAut (K := K) a), τ c = c) ↔ c ^ 2 ^ a = c) ∧
      Nat.card S = 2 ^ a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf (frobAut (K := K) a) = 2 := orderOf_eq_prime (frobAut_sq a hK)
    (frobAut_ne_one a ha hK)
  have hfix : ∀ c, (∀ τ ∈ Subgroup.zpowers (frobAut (K := K) a), τ c = c) ↔ c ^ 2 ^ a = c := by
    intro c
    constructor
    · intro h
      rw [← frobAut_apply]
      exact h _ (Subgroup.mem_zpowers _)
    · intro h τ hτ
      have hle : Subgroup.zpowers (frobAut (K := K) a) ≤ MulAction.stabilizer (K ≃+* K) c :=
        Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr (by
          change frobAut a c = c
          rw [frobAut_apply, h]))
      exact MulAction.mem_stabilizer_iff.mp (hle hτ)
  obtain ⟨-, -, -, -, -, hA⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two (by omega : 1 ≤ 2 * a) hK
  obtain ⟨-, S, hS, hcS⟩ := hA (Subgroup.zpowers (frobAut a))
  refine ⟨S, fun c => ?_, hfix, ?_⟩
  · rw [← SetLike.mem_coe, hS, Set.mem_ofPred_eq, hfix]
  · rw [hcS, Nat.card_zpowers, hord, Nat.mul_div_cancel_left a (by norm_num : 0 < 2)]

theorem smul_mem_hermSub {c : K} (hc : c ^ 2 ^ a = c)
    {X : Multiplicative (Matrix (Fin 2) (Fin 2) K)} (hX : X ∈ hermSub a (Fin 2) K) :
    Multiplicative.ofAdd (c • Multiplicative.toAdd X) ∈ hermSub a (Fin 2) K := by
  have hX' : (frobPow a (Multiplicative.toAdd X))ᵀ = Multiplicative.toAdd X := hX
  change (frobPow a (Multiplicative.toAdd (Multiplicative.ofAdd (c • Multiplicative.toAdd X))))ᵀ =
    Multiplicative.toAdd (Multiplicative.ofAdd (c • Multiplicative.toAdd X))
  have h1 : frobPow a (c • Multiplicative.toAdd X) = c • frobPow a (Multiplicative.toAdd X) := by
    ext i j
    simp [frobPow, mul_pow, hc]
  rw [toAdd_ofAdd, h1, Matrix.transpose_smul, hX']

abbrev smat (γ : ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 K)) : Matrix (Fin 2) (Fin 2) K :=
  ((γ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)

abbrev hmat (w : ↥(hermSub a (Fin 2) K)) : Matrix (Fin 2) (Fin 2) K :=
  Multiplicative.toAdd (w : Multiplicative (Matrix (Fin 2) (Fin 2) K))

theorem hmat_injective : Function.Injective (hmat (K := K) a) := fun _ _ h =>
  Subtype.ext (Multiplicative.toAdd.injective h)

theorem hmat_mul (w₁ w₂ : ↥(hermSub a (Fin 2) K)) : hmat a (w₁ * w₂) = hmat a w₁ + hmat a w₂ :=
  rfl

theorem hmat_one : hmat a (1 : ↥(hermSub a (Fin 2) K)) = 0 := rfl

@[expose] def hermSm {c : K} (hc : c ^ 2 ^ a = c) :
    ↥(hermSub a (Fin 2) K) →* ↥(hermSub a (Fin 2) K) where
  toFun w := ⟨Multiplicative.ofAdd (c • hmat a w), smul_mem_hermSub a hc w.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' w₁ w₂ := Subtype.ext (by simp [hmat_mul, smul_add])

variable {V : Type} [CommGroup V] (BE : V ≃* ↥(hermSub a (Fin 2) K))

@[expose] def smH (S : Subfield K) (hS : ∀ c, c ∈ S ↔ c ^ 2 ^ a = c) (c : S) : V →* V :=
  BE.symm.toMonoidHom.comp ((hermSm a ((hS c).mp c.2)).comp BE.toMonoidHom)

theorem hmat_smH (S : Subfield K) (hS : ∀ c, c ∈ S ↔ c ^ 2 ^ a = c) (c : S) (v : V) :
    hmat a (BE (smH a BE S hS c v)) = (c : K) • hmat a (BE v) := by
  change hmat a (BE (BE.symm _)) = _
  rw [MulEquiv.apply_symm_apply]
  rfl

theorem isScalarAct_smH (S : Subfield K) (hS : ∀ c, c ∈ S ↔ c ^ 2 ^ a = c) :
    IsScalarAct (smH a BE S hS) where
  add c d v := BE.injective (hmat_injective a (by
    rw [map_mul, hmat_mul, hmat_smH, hmat_smH, hmat_smH, Subfield.coe_add, add_smul]))
  mul c d v := BE.injective (hmat_injective a (by
    rw [hmat_smH, hmat_smH, hmat_smH, Subfield.coe_mul, mul_smul]))
  one v := BE.injective (hmat_injective a (by rw [hmat_smH, Subfield.coe_one, one_smul]))

end CFSG.Quasithin.Vol2.Ch10.SecB.C10KG
