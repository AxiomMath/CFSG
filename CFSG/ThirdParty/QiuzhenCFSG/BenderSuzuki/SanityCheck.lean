module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.FinalTheorem

namespace CFSG
end CFSG
open CFSG

noncomputable section

open Matrix
open BenderSuzuki.MatrixGroups

/-- The order of the concrete `PSL(2, 2ⁿ)` model used by the final theorem. -/
public theorem CFSG.psl2Model_card (n : ℕ) (hn : 2 ≤ n) :
    Nat.card (PSL2Model n) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  simpa [PSL2Model] using
    BenderSuzuki.lemma115_psl2Binary_card_formula n (by omega)

/-- The order of the concrete `Sz(2^(2n+1))` model used by the final theorem. -/
public theorem CFSG.szModel_card (n : ℕ) (hn : 1 ≤ n) :
    Nat.card (SzModel n) =
      ((2 ^ (2 * n + 1)) ^ 2 + 1) *
        (2 ^ (2 * n + 1)) ^ 2 *
          (2 ^ (2 * n + 1) - 1) := by
  rw [szModel_eq_suzukiMatrixGroup]
  exact BenderSuzuki.lemma115_suzukiMatrixGroup_card_formula n (by omega)

/-- The order of the concrete `PSU(3, 2ⁿ)` model used by the final theorem. -/
public theorem CFSG.psu3Model_card (n : ℕ) (hn : 2 ≤ n) :
    Nat.card (PSU3Model n) =
      ((2 ^ n) ^ 3 + 1) * (2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1) /
        Nat.gcd 3 (2 ^ n + 1) := by
  let k := GaloisField 2 n
  let E := FiniteField.Extension k 2 2
  letI : Fintype E := Fintype.ofFinite E
  let sigma : E ≃+* E :=
    (FiniteField.Extension.frob k 2 2).toRingEquiv
  have hsigma_involutive : Function.Involutive sigma := by
    intro x
    have hfrob_sq : (FiniteField.Extension.frob k 2 2) ^ 2 = 1 := by
      ext y
      rw [FiniteField.Extension.frob_iterate_apply]
      rw [← FiniteField.natCard_extension k 2 2]
      simpa [Nat.card_eq_fintype_card] using FiniteField.pow_card y
    have hx := DFunLike.congr_fun hfrob_sq x
    simpa [sigma, pow_two] using hx
  have hfixed_range :
      {x : E | sigma x = x} = Set.range (algebraMap k E) := by
    ext x
    constructor
    · intro hx
      apply (IsGalois.mem_range_algebraMap_iff_fixed x).2
      intro g
      obtain ⟨i, hi, rfl⟩ :=
        FiniteField.Extension.exists_frob_pow_eq k 2 2 g
      have hfx : FiniteField.Extension.frob k 2 2 x = x := by
        change FiniteField.Extension.frob k 2 2 x = x at hx
        exact hx
      clear hi
      induction i with
      | zero => simp
      | succ i ih =>
          rw [pow_succ, AlgEquiv.mul_apply, hfx, ih]
    · rintro ⟨a, rfl⟩
      change FiniteField.Extension.frob k 2 2
          (algebraMap k (FiniteField.Extension k 2 2) a) = _
      exact (FiniteField.Extension.frob k 2 2).commutes a
  let rangeEquiv : k ≃ Set.range (algebraMap k E) :=
    Equiv.ofInjective (algebraMap k E) (algebraMap k E).injective
  have hfixedCard : Nat.card {x : E // sigma x = x} = Nat.card k :=
    Nat.card_congr ((Set.equivOfEq hfixed_range).trans rangeEquiv.symm)
  let J : HermitianForm 3 E :=
    { conj := sigma
      conj_involutive := hsigma_involutive
      form := !![0, 0, 1; 0, 1, 0; 1, 0, 0]
      form_hermitian := by
        intro i j
        fin_cases i <;> fin_cases j <;> simp
      form_nondegenerate := by
        simp [Matrix.det_fin_three] }
  have hkcard : Nat.card k = 2 ^ n := by
    simpa [k] using GaloisField.card 2 n (by omega)
  have hEcard : Nat.card E = (2 ^ n) ^ 2 := by
    rw [FiniteField.natCard_extension, hkcard]
  have hfixedCardJ : Nat.card {x : E // J.conj x = x} = 2 ^ n := by
    simpa [J] using hfixedCard.trans hkcard
  rcases BenderSuzuki.External.huppert_II_10_12 J (2 ^ n)
      hEcard hfixedCardJ (by rfl) with
    ⟨_, _rho, _pinf, _hrho, _hnatural, _hUcard, _hroot,
      _htwo, hcard, _hthree⟩
  rcases projectiveSpecialUnitary_equiv_psu3Model
      J n hn (by rfl) hEcard hfixedCardJ with ⟨e⟩
  calc
    Nat.card (PSU3Model n) =
        Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) :=
      (Nat.card_congr e.toEquiv).symm
    _ = ((2 ^ n) ^ 3 + 1) * (2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1) /
        Nat.gcd 3 (2 ^ n + 1) := hcard
