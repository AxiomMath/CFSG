module

public import CFSG.OddTranspositions.O4Minus5Pair

public section

namespace CFSG.OddTranspositions.QZ

local instance factPrimeFive : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

open Polynomial

noncomputable section

@[expose] def poly25 : (ZMod 5)[X] := X ^ 2 - C 3

theorem hns : ¬ IsSquare (3 : ZMod 5) := by
  rintro ⟨b, hb⟩
  have h : ∀ b : ZMod 5, b ^ 2 ≠ 3 := by decide
  exact h b (by simpa [pow_two] using hb.symm)

instance : Fact (Irreducible poly25) :=
  ⟨(X_pow_sub_C_irreducible_iff_of_prime (K := ZMod 5) Nat.prime_two).2 (by
    intro b hb
    exact hns ⟨b, by simpa [pow_two] using hb.symm⟩)⟩

theorem natDegree_poly25 : poly25.natDegree = 2 := by
  rw [poly25, Polynomial.natDegree_X_pow_sub_C]

abbrev F25c := AdjoinRoot poly25

instance : Field F25c := AdjoinRoot.instField

theorem card_F25c : Nat.card F25c = 25 := by
  have hf : poly25 ≠ 0 := by
    intro h
    have h2 : poly25.natDegree = 2 := by
      rw [poly25, Polynomial.natDegree_X_pow_sub_C]
    rw [h, Polynomial.natDegree_zero] at h2
    omega
  haveI : Module.Finite (ZMod 5) F25c := (AdjoinRoot.powerBasis (f := poly25) hf).finite
  rw [Module.natCard_eq_pow_finrank (K := ZMod 5) (V := F25c),
    (AdjoinRoot.powerBasis (f := poly25) hf).finrank, AdjoinRoot.powerBasis_dim hf]
  rw [show poly25.natDegree = 2 from by rw [poly25, Polynomial.natDegree_X_pow_sub_C]]
  have hz : Nat.card (ZMod 5) = 5 := by
    rw [Nat.card_eq_fintype_card]
    exact ZMod.card 5
  rw [hz]
  norm_num

noncomputable def algEquiv_F25c : F25c ≃ₐ[ZMod 5] K25 :=
  GaloisField.algEquivGaloisField (p := 5) (n := 2) card_F25c

noncomputable def ringEquiv_F25c : F25c ≃+* K25 :=
  (algEquiv_F25c).toRingEquiv

end

end CFSG.OddTranspositions.QZ
