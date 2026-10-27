module

public import CFSG.RankThree.PartTwo.Sec4.HeringK419UnitaryU4Outer
import CFSG.RankThree.PartTwo.Sec4.Item426A6Outer
import CFSG.RankThree.PartTwo.Sec4.Item417Res6ProofU4
import CFSG.RankThree.PartOne.KF.UnitaryModel

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open Matrix CFSG CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.GH74.GLS.IVK (fixedField mem_fixedField_iff fixedField_apply)
open CFSG.RankThree.PartTwo.KFacts (IsInnerAut isInnerAut_congr)
open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.Assembly.LowTwoRank (StatedSU StatedProj StatedScalars)
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.Item419Res3
open CFSG.RankThree.PartTwo.Sec4.HeringUnitary

theorem outer_fixSub_simple {n : ℕ} (hn1 : 1 ≤ n) {α : MulAut (projSU 4 2 n)}
    (hα3 : α ^ 3 = 1) (hout : ¬ IsInnerAut α) :
    IsSimpleGroup (Item426.fixSub α) ∧ ∃ k : ℕ, 1 ≤ k ∧ Nat.card (Item426.fixSub α) =
      (2 ^ k) ^ 6 * (((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 3 + 1) * ((2 ^ k) ^ 4 - 1)) := by
  have hU := unitaryFieldData_galoisField 2 n hn1
  have hC : IsPrimeFormGram (1 : GL (Fin 4) (GaloisField 2 (2 * n))) := isPrimeFormGram_one_GL
  obtain ⟨⟨e₃⟩, -⟩ := unitary_prime_form_full_semilinear_realization hU hC (by norm_num)
    (fun h' => absurd h'.1 (by norm_num))
  set P := primeFormP hU ((1 : GL (Fin 4) (GaloisField 2 (2 * n))) :
    Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * n))) with hPdef
  let e : projSU 4 2 n ≃* P :=
    (projSUEquivStatedProj 4 2 n).trans ((unitaryPSUEquiv hU (by norm_num)).symm.trans e₃.symm)
  set β := MulAut.congr e α with hβdef
  have hβ : β ^ 3 = 1 := by rw [hβdef, ← map_pow, hα3, map_one]
  have hβout : ¬ IsInnerAut β := fun h' => hout ((isInnerAut_congr e α).mp h')
  obtain ⟨φ, H, hφ3, hβeq⟩ := WitnessU4.exists_eq_conj_primeFormFieldHom hU hC β hβ hβout
  have hφ1 : φ ≠ 1 := by
    rintro rfl
    apply hβout
    rw [hβeq, map_one, mul_one, mul_inv_cancel]
    exact ⟨1, map_one _⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hσ : orderOf φ = 3 := orderOf_eq_prime hφ3 hφ1
  obtain ⟨f₀, hf, hf₀, hcard⟩ := KFacts.exists_card_fixedField_of_orderOf_eq_three hU hσ
  have h₀ : UnitaryFieldData 2 f₀ (fixedField φ) := ⟨Nat.prime_two, hf₀, hcard⟩
  have hbar := KFacts.bar_coe_fixedField hU hf h₀
  have := h₀.finite
  set Y := unitarySU 2 f₀ (fixedField φ) 4 with hYdef
  have hK₀ : Nat.card (fixedField φ) = (2 ^ f₀) ^ 2 := by rw [hcard, ← pow_mul, mul_comm]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsimp : IsSimpleGroup (StatedProj (StatedSU 4 (2 ^ f₀) (fixedField φ))) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU (fixedField φ) 2 f₀ hK₀ 4
      (by norm_num) (by simp)
  have hYs : IsSimpleGroup Y :=
    (CFSG.RankThree.PartOne.KFU.projEquivOfBot
      (CFSG.RankThree.PartOne.KFU.scalars_subgroupOf_eq_bot hK₀ (by norm_num)
        (Res417Six.gcd_four_two_pow_add_one hf₀))).symm.isSimpleGroup
  set fφ := primeFormFieldHom hU hC φ
  set σS := primeFormFieldSU hU hC φ
  set cH := primeFormConjHom hU ((1 : GL (Fin 4) (GaloisField 2 (2 * n))) :
    Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * n))) H
  have h1 : (Item426.fixSub α).map e.toMonoidHom = Item426.fixSub β := Item426.map_fixSub_eq e α
  have h2 : Item426.fixSub β = (Item426.fixSub fφ).map cH.toMonoidHom := by
    rw [hβeq, fixSub_conj]
  have h3 : Item426.fixSub fφ = (Item426.fixSub σS).map (primeFormPEquiv hU _).toMonoidHom :=
    fixSub_primeFormFieldHom_eq hU hC φ
  have hSeq : unitarySU 2 n (GaloisField 2 (2 * n)) 4 = gramSU hU
      ((1 : GL (Fin 4) (GaloisField 2 (2 * n))) :
        Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * n))) := by
    rw [Units.val_one]
    exact unitarySU_eq_gramSU hU 4
  set ι : Y →* gramSU hU ((1 : GL (Fin 4) (GaloisField 2 (2 * n))) :
      Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * n))) :=
    (MulEquiv.subgroupCongr hSeq).toMonoidHom.comp (suInclFix hU h₀ hbar) with hιdef
  have hιinj : Function.Injective ι :=
    (MulEquiv.subgroupCongr hSeq).injective.comp (suInclFix_injective hU h₀ hbar)
  have hrange : ι.range = Item426.fixSub σS := by
    ext y
    rw [Item426.mem_fixSub]
    constructor
    · rintro ⟨g₀, rfl⟩
      apply Subtype.ext
      change glAut φ ((suInclFix hU h₀ hbar g₀ : unitarySU 2 n _ 4) : GL (Fin 4) _) = _
      exact (mem_range_suInclFix_iff hU h₀ hbar _).mp ⟨g₀, rfl⟩
    · intro hy
      have hy' : glAut φ (y : GL (Fin 4) (GaloisField 2 (2 * n))) = y := congrArg Subtype.val hy
      have hy2 : (y : GL (Fin 4) (GaloisField 2 (2 * n))) ∈
          unitarySU 2 n (GaloisField 2 (2 * n)) 4 := by
        rw [hSeq]
        exact y.2
      obtain ⟨g₀, hg₀⟩ := (mem_range_suInclFix_iff hU h₀ hbar
        (⟨(y : GL (Fin 4) (GaloisField 2 (2 * n))), hy2⟩ :
          unitarySU 2 n (GaloisField 2 (2 * n)) 4)).mpr hy'
      refine ⟨g₀, Subtype.ext ?_⟩
      change ((suInclFix hU h₀ hbar g₀ : unitarySU 2 n (GaloisField 2 (2 * n)) 4) :
        GL (Fin 4) (GaloisField 2 (2 * n))) = (y : GL (Fin 4) (GaloisField 2 (2 * n)))
      rw [hg₀]
  set Φ : Item426.fixSub α ≃* Y :=
    (((Item426.fixSub α).equivMapOfInjective e.toMonoidHom e.injective).trans
      ((MulEquiv.subgroupCongr (h1.trans h2)).trans
        ((Item426.fixSub fφ).equivMapOfInjective cH.toMonoidHom cH.injective).symm)).trans
      (((MulEquiv.subgroupCongr h3).trans
        ((Item426.fixSub σS).equivMapOfInjective _ (primeFormPEquiv hU _).injective).symm).trans
        ((MulEquiv.subgroupCongr hrange.symm).trans (MonoidHom.ofInjective hιinj).symm))
  refine ⟨Φ.isSimpleGroup, f₀, hf₀, ?_⟩
  rw [Nat.card_congr Φ.toEquiv]
  exact card_unitarySU_four h₀

end CFSG.RankThree.PartTwo.Sec8.Hering611
