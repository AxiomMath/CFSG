module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.Classical2.MatrixFrobeniusLang

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.RankThree.Classical2

variable {Ω : Type} [Field Ω]

@[expose] def cubicSubfield (ℓ f : ℕ) [Fact ℓ.Prime] [CharP Ω ℓ] : Subfield Ω :=
  RingHom.eqLocusField (iterateFrobenius Ω ℓ (3 * f)) (RingHom.id Ω)

theorem mem_cubicSubfield {ℓ f : ℕ} [Fact ℓ.Prime] [CharP Ω ℓ] (c : Ω) :
    c ∈ cubicSubfield (Ω := Ω) ℓ f ↔ c ^ ((ℓ ^ f) ^ 3) = c := by
  rw [cubicSubfield, RingHom.mem_eqLocusField, iterateFrobenius_def, RingHom.id_apply, ← pow_mul,
    mul_comm]

theorem natCard_cubicSubfield {ℓ f : ℕ} [Fact ℓ.Prime] [CharP Ω ℓ] [IsAlgClosed Ω] (hf : 1 ≤ f) :
    Nat.card (cubicSubfield (Ω := Ω) ℓ f) = (ℓ ^ f) ^ 3 := by
  have h := natCard_setOf_pow_eq_self (Ω := Ω) (ℓ := ℓ) (e := 3 * f) (by omega)
  rw [← pow_mul, mul_comm]
  rw [← h]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun c => by
    rw [mem_cubicSubfield, ← pow_mul, mul_comm]
    exact Iff.rfl)

theorem isAlgebraic_cubicSubfield {K : Type} [Field K] [Finite K] [Algebra K Ω]
    [IsAlgClosure K Ω] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP Ω ℓ] (hK : Nat.card K = ℓ ^ f) :
    Algebra.IsAlgebraic (cubicSubfield (Ω := Ω) ℓ f) Ω := by
  have : Fintype K := Fintype.ofFinite K
  have hmem : ∀ c : K, algebraMap K Ω c ∈ cubicSubfield (Ω := Ω) ℓ f := fun c => by
    rw [mem_cubicSubfield, ← map_pow]
    congr 1
    have h1 : c ^ (ℓ ^ f) = c := by
      rw [← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]
    have : ∀ n : ℕ, c ^ ((ℓ ^ f) ^ n) = c := fun n => by
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ, pow_mul, ih, h1]
    exact this 3
  let φ : K →+* cubicSubfield (Ω := Ω) ℓ f := (algebraMap K Ω).codRestrict _ hmem
  let _ : Algebra K (cubicSubfield (Ω := Ω) ℓ f) := φ.toAlgebra
  have : IsScalarTower K (cubicSubfield (Ω := Ω) ℓ f) Ω :=
    IsScalarTower.of_algebraMap_eq fun c => rfl
  have : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  exact Algebra.IsAlgebraic.tower_top (K := K) (cubicSubfield (Ω := Ω) ℓ f)

end CFSG.RankThree.PartOne.KE6
