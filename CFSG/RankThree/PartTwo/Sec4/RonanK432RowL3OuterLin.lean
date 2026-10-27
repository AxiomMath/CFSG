module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowL3OuterMat
public import CFSG.RankThree.PartTwo.Sec4.RonanK432L3HardRow
import CFSG.RankThree.PartTwo.KFacts.AutPSLOrderThree
import CFSG.RankThree.PartTwo.KFacts.L34Sections
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherOuterQuotients

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartTwo.KFacts

theorem no_field_aut_order_three {p n : ℕ} [Fact p.Prime] (hn : ¬ 3 ∣ n) (hn0 : n ≠ 0) :
    ∀ σ : GaloisField p n ≃+* GaloisField p n, orderOf σ ≠ 3 := fun σ hσ =>
  hn (eq_frobenius_pow_of_orderOf_eq_three Fact.out (Nat.one_le_iff_ne_zero.mpr hn0)
    (GaloisField.card p n hn0) hσ).1

namespace L3Outer

theorem exists_piField_true {K : Type} [Field K] [Finite K] (hK : Nat.card K % 3 = 1) :
    ∃ p f : ℕ, PiField true p f K ∧ ModThree true (p ^ f) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hp, hcard⟩ := FiniteField.card K (ringChar K)
  have hcard' : Nat.card K = ringChar K ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card, hcard]
  refine ⟨ringChar K, n, ⟨hp, n.pos, by simpa [piCard] using hcard'⟩, ?_⟩
  change ringChar K ^ (n : ℕ) % 3 = 1
  rw [← hcard']
  exact hK

theorem conjAut_eq_one_iff {K : Type} [Field K] [Finite K] (g : GL (Fin 3) K) :
    conjAut 3 K g = 1 ↔ Matrix.ProjGenLinGroup.mk g = 1 := by
  constructor
  · intro h
    obtain ⟨-, c, rfl⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (n := 3) (by norm_num) g 1
      (by rw [map_one, mul_one]; exact h)
    exact Matrix.ProjGenLinGroup.mk_scalar c
  · intro h
    obtain ⟨c, rfl⟩ := mk_eq_one_iff_mem_statedScalars.mp h
    exact conjAut_scalar c

theorem conjAut_mem_range_conj_of_slPi {K : Type} [Field K] {q : ℕ} {g : GL (Fin 3) K}
    (hg : g ∈ slPi true 3 q K) :
    conjAut 3 K g ∈ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range := by
  have hdet := (mem_slPi_true q).mp hg
  set g' : Matrix.SpecialLinearGroup (Fin 3) K := ⟨(g : Matrix (Fin 3) (Fin 3) K), hdet⟩ with hg'
  have hg'g : Matrix.SpecialLinearGroup.toGL g' = g := Units.ext rfl
  refine ⟨proj 3 K g', ?_⟩
  rw [← conjAut_toGL, hg'g]

theorem outerRow_projectiveSL_three {K : Type} [Field K] [Finite K]
    [Finite (projectiveSL 3 K)] (hK : Nat.card K % 3 = 1) (hnf : ∀ σ : K ≃+* K, orderOf σ ≠ 3) :
    OuterRow (projectiveSL 3 K) := by
  intro _ σ hσ hout
  have hD : σ ∈ linearAutGroup 3 K := by
    by_contra hD
    obtain ⟨τ, hτ, -⟩ := linear_order_three_field_descent (by norm_num) σ hσ hD
    exact hnf τ hτ
  obtain ⟨A, rfl⟩ := mem_linearAutGroup_iff.mp hD
  obtain ⟨p, f, hPi, hq⟩ := exists_piField_true hK
  have hker := conjAut_eq_one_iff (K := K)
  refine not_autWeaklyClosed_of_diagonal hPi hq (conjAut 3 K) (MonoidHom.id (GL (Fin 3) K))
    hker (fun g => mem_glPi_true _ g) (fun g hg => conjAut_mem_range_conj_of_slPi hg)
    (fun t ht => ⟨t, rfl⟩) (y := A) ?_ ?_
  · intro hA
    obtain ⟨c, rfl⟩ := hA
    exact hout (by rw [conjAut_scalar]; exact one_mem _)
  · refine mk_eq_one_iff_mem_statedScalars.mp ((hker _).mp ?_)
    rw [map_pow, MonoidHom.id_apply]
    exact hσ

end L3Outer

open L3Outer

theorem outerRow_projSL_three_of_mod_one {K : Type} [Field K] [Finite K]
    (hK : Nat.card K % 3 = 1) (hnf : ∀ σ : K ≃+* K, orderOf σ ≠ 3) :
    OuterRow (projSL 3 K) := by
  haveI : Finite (projectiveSL 3 K) :=
    Finite.of_equiv _ (KFacts.L34.projSLEquivProjectiveSL 3 K).toEquiv
  exact OuterRow.of_mulEquiv (KFacts.L34.projSLEquivProjectiveSL 3 K).symm
    (outerRow_projectiveSL_three hK hnf)

theorem rowOf_two_SL_of_mod_one : ∀ (p e : ℕ) [Fact p.Prime], 3 < p → 1 ≤ e → e ≤ 2 →
    p ^ e % 3 = 1 → RowOf (projSL 3 (GaloisField p e)) := by
  intro p e _ _ he he2 hmod S _ _ _ _ ⟨eS⟩
  have hK : Nat.card (GaloisField p e) % 3 = 1 := by
    rw [GaloisField.card p e (by omega)]
    exact hmod
  exact GoodRow.of_mulEquiv eS.symm
    ⟨listRow_projSL_three_galoisField_of_mod_one (by omega) hmod,
      outerRow_projSL_three_of_mod_one hK (no_field_aut_order_three (by omega) (by omega))⟩

theorem rowOf_seven_SL3_of_even_of_not_three_dvd : ∀ n : ℕ, 1 ≤ n → n % 2 = 0 → n % 3 ≠ 0 →
    RowOf (projSL 3 (GaloisField 2 n)) := by
  intro n hn heven h3 S _ _ _ _ ⟨eS⟩
  have hmod : 2 ^ n % 3 = 1 := two_pow_mod_three_of_even (Nat.even_iff.mpr heven)
  have hK : Nat.card (GaloisField 2 n) % 3 = 1 := by
    rw [GaloisField.card 2 n (by omega)]
    exact hmod
  exact GoodRow.of_mulEquiv eS.symm
    ⟨listRow_projSL_three_galoisField_of_mod_one (by omega) hmod,
      outerRow_projSL_three_of_mod_one hK (no_field_aut_order_three (by omega) (by omega))⟩

end CFSG.RankThree.PartTwo.Sec4.RonanK432
