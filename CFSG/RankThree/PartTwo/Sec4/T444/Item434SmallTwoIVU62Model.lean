module

public import CFSG.RankThree.PartTwo.Sec4.Item47Unitary
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryDiagonalOuterOrder
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherIsotropicRadical

public noncomputable section

namespace CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU62

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Assembly.RankThreeEven (projSU)

abbrev F4 : Type := GaloisField 2 (2 * 1)

theorem card_F4 : Nat.card F4 = 4 := by
  rw [GaloisField.card 2 (2 * 1) (by norm_num)]
  norm_num

theorem uData : UnitaryFieldData 2 1 F4 := ⟨Nat.prime_two, le_rfl, by rw [card_F4]; norm_num⟩

instance : Finite F4 := uData.finite

theorem card_units_F4 : Nat.card F4ˣ = 3 := by
  rw [Nat.card_units, card_F4]

theorem pow_three_F4 {x : F4} (hx : x ≠ 0) : x ^ 3 = 1 := by
  have := Fintype.ofFinite F4
  have h := FiniteField.pow_card_sub_one_eq_one x hx
  rwa [← Nat.card_eq_fintype_card, card_F4] at h

theorem two_eq_zero_F4 : (2 : F4) = 0 := by
  have := uData.charP
  have h : ((2 : ℕ) : F4) = 0 := CharP.cast_eq_zero F4 2
  simpa using h

theorem norm_F4 (c : F4) : uData.norm c = c ^ 3 := by
  rw [UnitaryFieldData.norm, UnitaryFieldData.bar_apply]
  ring

theorem norm_eq_one (c : F4ˣ) : uData.norm (c : F4) = 1 := by
  rw [norm_F4]
  exact pow_three_F4 c.ne_zero

abbrev M6 : Matrix (Fin 6) (Fin 6) F4 := ((1 : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)

theorem M6_eq_one : M6 = 1 := Units.val_one

theorem hC6 : IsPrimeFormGram (1 : GL (Fin 6) F4) := isPrimeFormGram_one_GL

abbrev GU6 : Subgroup (GL (Fin 6) F4) := primeFormUnitary uData M6

abbrev P6 : Type := primeFormP uData M6

abbrev conj6 : GU6 →* MulAut P6 := primeFormConjHom uData M6

theorem hn6 : 3 ≤ 6 := by norm_num

theorem hq6 : ¬(6 = 3 ∧ 2 ^ 1 = 2) := by norm_num

@[expose] def u6Equiv : projSU 6 2 1 ≃* P6 :=
  (projSUEquivStatedProj 6 2 1).trans
    ((unitaryPSUEquiv uData (by norm_num)).symm.trans
      (Classical.choice (unitary_prime_form_full_semilinear_realization uData hC6 hn6 hq6).1).symm)

instance : Finite P6 := by
  have : Finite (GL (Fin 6) F4) := Finite.of_injective _ Units.val_injective
  exact Finite.of_surjective (QuotientGroup.mk' (normOneScalars uData (gramSU uData M6) 6))
    (QuotientGroup.mk'_surjective _)

theorem card_ringAut_F4 : Nat.card (F4 ≃+* F4) = 2 :=
  (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two F4 (n := 2)
    (by rw [card_F4]; norm_num)).1

theorem eq_one_of_pow_three_eq_one {φ : F4 ≃+* F4} (h : φ ^ 3 = 1) : φ = 1 := by
  have : Finite (F4 ≃+* F4) := Nat.finite_of_card_ne_zero (by rw [card_ringAut_F4]; norm_num)
  have h2 : φ ^ 2 = 1 := by
    have := pow_card_eq_one' (G := F4 ≃+* F4) (x := φ)
    rwa [card_ringAut_F4] at this
  calc φ = φ ^ 2 * φ := by rw [h2, one_mul]
    _ = 1 := by rw [← pow_succ]; exact h

theorem exists_conj6_eq_of_pow_three {α : MulAut P6} (hα : α ^ 3 = 1) :
    ∃ A : GU6, conj6 A = α := by
  obtain ⟨-, -, -, -, -, -, -, hker, -, -, -⟩ :=
    unitary_prime_form_full_semilinear_realization uData hC6 hn6 hq6
  have h1 : primeFormFieldFactor uData hC6 hn6 hq6 α ^ 3 = 1 := by
    rw [← map_pow, hα, map_one]
  have h2 : α ∈ (primeFormFieldFactor uData hC6 hn6 hq6).ker :=
    (MonoidHom.mem_ker).2 (eq_one_of_pow_three_eq_one h1)
  rw [hker] at h2
  exact h2

@[expose] def scalarGU6 : F4ˣ →* GU6 :=
  (GeneralLinearGroup.scalar (Fin 6)).codRestrict GU6 fun c =>
    scalar_mem_primeFormUnitary_one uData (norm_eq_one c)

theorem coe_scalarGU6 (c : F4ˣ) :
    ((scalarGU6 c : GU6) : GL (Fin 6) F4) = GeneralLinearGroup.scalar (Fin 6) c :=
  rfl

theorem scalarGU6_injective : Function.Injective scalarGU6 := by
  intro c d h
  have h1 := congrArg (fun g : GU6 => ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) 0 0) h
  simp only [coe_scalarGU6, GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_eq] at h1
  exact Units.ext h1

theorem conj6_scalarGU6 (c : F4ˣ) : conj6 (scalarGU6 c) = 1 := by
  refine MulEquiv.ext fun x => QuotientGroup.induction_on x fun g => ?_
  rw [primeFormConjHom_mk, MulAut.one_apply]
  congr 1
  apply Subtype.ext
  change GeneralLinearGroup.scalar (Fin 6) c * (g : GL (Fin 6) F4) *
    (GeneralLinearGroup.scalar (Fin 6) c)⁻¹ = g
  rw [← (commute_scalar c (g : GL (Fin 6) F4)).eq, mul_inv_cancel_right]

theorem ker_conj6 : conj6.ker = scalarGU6.range := by
  ext A
  constructor
  · intro hA
    obtain ⟨c, -, hc⟩ := eq_scalar_of_primeFormConjHom_eq_one uData hC6 hn6 hA
    exact ⟨c, Subtype.ext hc.symm⟩
  · rintro ⟨c, rfl⟩
    exact conj6_scalarGU6 c

theorem card_ker_conj6 : Nat.card conj6.ker = 3 := by
  rw [ker_conj6, ← Nat.card_congr (MonoidHom.ofInjective scalarGU6_injective).toEquiv,
    card_units_F4]

theorem ker_conj6_le_center : conj6.ker ≤ Subgroup.center GU6 := by
  rw [ker_conj6]
  rintro _ ⟨c, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (commute_scalar c (g : GL (Fin 6) F4)).eq

end CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU62
