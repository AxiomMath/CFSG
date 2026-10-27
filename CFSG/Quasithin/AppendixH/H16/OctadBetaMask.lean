module

public import CFSG.Quasithin.Background.H156Gen
public import CFSG.Quasithin.AppendixH.H16.OctadGroup
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.AppendixH.H15.Vocab

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI.H16

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H16Pf
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Coc CFSG.Quasithin.H.FixSyl CFSG.Quasithin.H.LU24
  CFSG.Monster.Code CFSG.ASVolI.AppH CFSG.Quasithin.H156

@[expose] def octBetaCols : List ℕ := [5, 5, 7, 7, 7, 14, 58, 46, 30, 0, 0]

@[expose] noncomputable def octBeta : W11 →* Wn 6 := maskHom 11 6 octBetaCols

theorem octBeta_toW (m : ℕ) : octBeta (toW 11 m) = toW 6 (actM octBetaCols m) :=
  maskHom_toW (by rfl) m

theorem octBetaCols_lt : ∀ c ∈ octBetaCols, c < 2 ^ 6 := by decide

theorem octBeta_ker_masks : ∀ m < 2 ^ 11, (actM octBetaCols m = 0 ↔ m ∈ combos oct5Basis) := by
  decide +kernel

theorem octBeta_surj_masks : ∀ w < 2 ^ 6, ∃ m < 2 ^ 11, actM octBetaCols m = w := by
  decide +kernel

theorem octBeta_eq_one_iff (x : W11) : octBeta x = 1 ↔ x ∈ octV5 := by
  obtain ⟨m, hm, rfl⟩ := toW_surj 11 x
  rw [octBeta_toW]
  have hy : actM octBetaCols m < 2 ^ 6 := actM_lt octBetaCols_lt m
  have h6 : (toW 6 (actM octBetaCols m) = 1 ↔ actM octBetaCols m = 0) :=
    ⟨fun h => toW_inj hy (Nat.two_pow_pos 6) (by rw [h, toW_zero]),
      fun h => by rw [h, toW_zero]⟩
  rw [h6, octBeta_ker_masks m hm, octV5, toW_mem_maskSub_iff_of_lt oct5Basis_lt hm]

theorem octBeta_surjective : Function.Surjective octBeta := by
  intro w
  obtain ⟨w', hw', rfl⟩ := toW_surj 6 w
  obtain ⟨m, hm, hmw⟩ := octBeta_surj_masks w' hw'
  exact ⟨toW 11 m, by rw [octBeta_toW, hmw]⟩

@[expose] def octQmask (c : ℕ) : ℕ := popc 8 c / 2 % 2

@[expose] def qMask6 (y : ℕ) : ℕ :=
  ((y.testBit 0 && y.testBit 1) ^^ (y.testBit 2 && y.testBit 3) ^^ (y.testBit 4 && y.testBit 5)).toNat

theorem qPlus6_toW (y : ℕ) : qPlus6 (Multiplicative.toAdd (toW 6 y)) = (qMask6 y : ZMod 2) := by
  rw [toAdd_toW]
  have hq : (qMask6 y : ZMod 2) =
      (((y.testBit ((0 : Fin 6) : ℕ) && y.testBit ((1 : Fin 6) : ℕ)) ^^
        (y.testBit ((2 : Fin 6) : ℕ) && y.testBit ((3 : Fin 6) : ℕ)) ^^
        (y.testBit ((4 : Fin 6) : ℕ) && y.testBit ((5 : Fin 6) : ℕ))).toNat : ℕ) := rfl
  rw [qPlus6, hq]
  cases h0 : y.testBit ((0 : Fin 6) : ℕ) <;> cases h1 : y.testBit ((1 : Fin 6) : ℕ) <;>
    cases h2 : y.testBit ((2 : Fin 6) : ℕ) <;> cases h3 : y.testBit ((3 : Fin 6) : ℕ) <;>
    cases h4 : y.testBit ((4 : Fin 6) : ℕ) <;> cases h5 : y.testBit ((5 : Fin 6) : ℕ) <;>
    simp only [bvec_apply, h0, h1, h2, h3, h4, h5] <;> decide

theorem octBeta_q_masks :
    ∀ m < 2 ^ 11, qMask6 (actM octBetaCols m) = octQmask (actM liftCCols m) := by
  decide +kernel

theorem octWeight_even_masks : ∀ m < 2 ^ 11, popc 8 (actM liftCCols m) % 2 = 0 := by
  decide +kernel

theorem octG1_acts_nontrivially_masks :
    ∃ m < 2 ^ 11, actM octBetaCols (actC11 octG1Arr m) ≠ actM octBetaCols m := by
  decide +kernel

end CFSG.ASVolI.H16
