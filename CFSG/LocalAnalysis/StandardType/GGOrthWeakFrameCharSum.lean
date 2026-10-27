module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutNonsplitOmChar
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
public import Mathlib.Data.ZMod.Defs
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorusCore
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorusForms
public import CFSG.ClassicalInvolution.Orders.OrthogonalCount
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.SectionRank.SignLines
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.StandardType

namespace OrthTorus

open Module
open CFSG.RankThree.Classical2 (orthDerived)

theorem torus_rank_eq {p : ℕ} [Fact p.Prime] {H : Type} [Group H] {A : Subgroup H} {r r' : ℕ}
    {τ : (Fin r → Multiplicative (ZMod p)) →* H} {τ' : (Fin r' → Multiplicative (ZMod p)) →* H}
    (hτ : Function.Injective τ) (hτ' : Function.Injective τ') (hr : τ.range = A)
    (hr' : τ'.range = A) : r = r' := by
  have hcard : Nat.card A = p ^ r := by
    rw [← hr, ← Nat.card_congr (MonoidHom.ofInjective hτ).toEquiv,
      Nat.card_fun, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, Nat.card_fin]
  have hcard' : Nat.card A = p ^ r' := by
    rw [← hr', ← Nat.card_congr (MonoidHom.ofInjective hτ').toEquiv,
      Nat.card_fun, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, Nat.card_fin]
  exact Nat.pow_right_injective (Fact.out : p.Prime).two_le (hcard.symm.trans hcard')

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V]

private theorem charSum_top_congr {K : Type} [Field K] [CharP K 2] {V V' : Type}
    [AddCommGroup V] [Module K V] [Fintype V] [AddCommGroup V'] [Module K V'] [Fintype V']
    {Q : QuadraticForm K V} {Q' : QuadraticForm K V'} (e : Q.IsometryEquiv Q') :
    OrdPNsOm.charSum Q ⊤ = OrdPNsOm.charSum Q' ⊤ := by
  have hftV : Fintype ↥(⊤ : Submodule K V) := Fintype.ofFinite _
  have hftV' : Fintype ↥(⊤ : Submodule K V') := Fintype.ofFinite _
  let f : ↥(⊤ : Submodule K V) ≃ ↥(⊤ : Submodule K V') :=
    { toFun := fun v => ⟨e v, Submodule.mem_top⟩
      invFun := fun w => ⟨e.symm w, Submodule.mem_top⟩
      left_inv := fun v => Subtype.ext (by simp)
      right_inv := fun w => Subtype.ext (by simp) }
  rw [OrdPNsOm.charSum_eq, OrdPNsOm.charSum_eq]
  exact Fintype.sum_equiv f _ _ (fun v => congrArg OrdPNsOm.chi (e.map_app v).symm)

private theorem charSum_quadPlus_top {K : Type} [Field K] [Finite K] [CharP K 2] {r : ℕ}
    (hr : 1 ≤ r) :
    OrdPNsOm.charSum (CFSG.LieType.Universal.Spin.quadPlus r K) ⊤ = (Nat.card K : ℤ) ^ r := by
  haveI : Fintype K := Fintype.ofFinite K
  have h := charSum_qPlusForm (K := K) (r - 1)
  rw [Nat.sub_add_cancel hr] at h
  simpa only [TableBOrth.qPlusForm] using h

private theorem charSum_quadMinus_top {K : Type} [Field K] [Finite K] [CharP K 2] {r : ℕ}
    (hr : 1 ≤ r) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    OrdPNsOm.charSum (CFSG.LieType.Universal.Spin.quadMinus r K b c) ⊤ =
      -((Nat.card K : ℤ) ^ r) := by
  haveI : Fintype K := Fintype.ofFinite K
  have h := (charSum_qMinusForm (K := K) (r - 1) (b := b) (c := c) hirr).1
  rw [charSum_top_congr (TableBOrth.qMinusIsometry (r - 1) b c)] at h
  rw [Nat.sub_add_cancel hr] at h
  exact h

theorem charSum_top_modEq_one_of_witt {Q : QuadraticForm F V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {r : ℕ} (hr : 1 ≤ r)
    (hdim : finrank F V = 2 * r) {p : ℕ} (hpq : p ∣ Nat.card F + 1)
    (htype : (CFSG.GroupTheory.WeirSylow.IsPlusType Q ∧ Even r) ∨
      (¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q ∧ Odd r)) :
    OrdPNsOm.charSum Q ⊤ ≡ 1 [ZMOD p] := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Finite V := Module.finite_of_finite F
  haveI : Fintype V := Fintype.ofFinite V
  have hq : (Nat.card F : ℤ) ≡ -1 [ZMOD p] :=
    modEq_neg_one_of_dvd (p := p) (q := Nat.card F) hpq
  rcases htype with ⟨hplus, heven⟩ | ⟨hminus, hodd⟩
  · obtain ⟨e⟩ := CFSG.GroupTheory.WeirSylow.nonempty_isometry_quadPlus hQ hdim hplus
    have hsum : OrdPNsOm.charSum Q ⊤ = (Nat.card F : ℤ) ^ r := by
      rw [charSum_top_congr e]
      exact charSum_quadPlus_top (K := F) hr
    calc
      OrdPNsOm.charSum Q ⊤ = (Nat.card F : ℤ) ^ r := hsum
      _ ≡ (-1 : ℤ) ^ r [ZMOD p] := Int.ModEq.pow r hq
      _ = 1 := Even.neg_one_pow heven
  · rcases CFSG.GroupTheory.WeirSylow.exists_isometry_quadPlus_or_quadMinus Q hQ hr hdim with
      hplus | ⟨b, c, hirr, ⟨e⟩⟩
    · obtain ⟨e⟩ := hplus
      exact absurd (CFSG.GroupTheory.WeirSylow.IsPlusType.of_isometryEquiv e.symm
        (CFSG.GroupTheory.WeirSylow.isPlusType_quadPlus F r)) hminus
    · have hsum : OrdPNsOm.charSum Q ⊤ = -((Nat.card F : ℤ) ^ r) := by
        rw [charSum_top_congr e, charSum_quadMinus_top (K := F) hr hirr]
      calc
        OrdPNsOm.charSum Q ⊤ = -((Nat.card F : ℤ) ^ r) := hsum
        _ ≡ -((-1 : ℤ) ^ r) [ZMOD p] := (Int.ModEq.pow r hq).neg
        _ = 1 := by rw [Odd.neg_one_pow hodd]; norm_num

theorem charSum_top_modEq_neg_one_of_witt {Q : QuadraticForm F V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {r : ℕ} (hr : 1 ≤ r)
    (hdim : finrank F V = 2 * r) {p : ℕ} (hpq : p ∣ Nat.card F + 1)
    (htype : (CFSG.GroupTheory.WeirSylow.IsPlusType Q ∧ Odd r) ∨
      (¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q ∧ Even r)) :
    OrdPNsOm.charSum Q ⊤ ≡ -1 [ZMOD p] := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Finite V := Module.finite_of_finite F
  haveI : Fintype V := Fintype.ofFinite V
  have hq : (Nat.card F : ℤ) ≡ -1 [ZMOD p] :=
    modEq_neg_one_of_dvd (p := p) (q := Nat.card F) hpq
  rcases htype with ⟨hplus, hodd⟩ | ⟨hminus, heven⟩
  · obtain ⟨e⟩ := CFSG.GroupTheory.WeirSylow.nonempty_isometry_quadPlus hQ hdim hplus
    calc
      OrdPNsOm.charSum Q ⊤ = (Nat.card F : ℤ) ^ r := by
        rw [charSum_top_congr e]
        exact charSum_quadPlus_top (K := F) hr
      _ ≡ (-1 : ℤ) ^ r [ZMOD p] := Int.ModEq.pow r hq
      _ = -1 := Odd.neg_one_pow hodd
  · rcases CFSG.GroupTheory.WeirSylow.exists_isometry_quadPlus_or_quadMinus Q hQ hr hdim with
      hplus | ⟨b, c, hirr, ⟨e⟩⟩
    · obtain ⟨e⟩ := hplus
      exact absurd (CFSG.GroupTheory.WeirSylow.IsPlusType.of_isometryEquiv e.symm
        (CFSG.GroupTheory.WeirSylow.isPlusType_quadPlus F r)) hminus
    · calc
        OrdPNsOm.charSum Q ⊤ = -((Nat.card F : ℤ) ^ r) := by
          rw [charSum_top_congr e, charSum_quadMinus_top (K := F) hr hirr]
        _ ≡ -((-1 : ℤ) ^ r) [ZMOD p] := (Int.ModEq.pow r hq).neg
        _ = -1 := by rw [Even.neg_one_pow heven]

theorem finrank_eq_two_mul_of_charSum {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F - 1 ∨ p ∣ Nat.card F + 1) {Q : QuadraticForm F V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule F V, finrank F T = 3 ∧ ∀ v ∈ T, Q v = 0)
    {A : Subgroup (V ≃ₗ[F] V)} (hAΩ : A ≤ orthDerived Q) (hApow : ∀ a ∈ A, a ^ p = 1)
    (hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hmax : ∀ g ∈ orthDerived Q, g ^ p = 1 → (∀ c ∈ A, g * c = c * g) → g ∈ A)
    (hne : ∃ b ∈ A, b ≠ 1) {r : ℕ} {τ : (Fin r → Multiplicative (ZMod p)) →* (V ≃ₗ[F] V)}
    (hτ : Function.Injective τ) (hτr : τ.range = A)
    (hchar : OrdPNsOm.charSum Q ⊤ ≡ 1 [ZMOD p]) : finrank F V = 2 * r := by
  obtain ⟨r', τ', hτ', hτr', -, -, -, hchar'⟩ :=
    exists_torus (K := F) (V := V) hp2 hpq hQ hT hAΩ hApow hAcomm hmax hne
  have hfirst : OrdPNsOm.charSum Q ⊤ ≡ 1 [ZMOD p] ∧ finrank F V = 2 * r' := by
    rcases hchar' with h | h
    · exact h
    · exact absurd (hchar.symm.trans h.1) (one_not_modEq_neg_one (Fact.out) hp2)
  have hrr : r = r' := torus_rank_eq hτ hτ' hτr hτr'
  rw [hfirst.2, hrr]

end OrthTorus

end CFSG.StandardType

end
