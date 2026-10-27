module

public import CFSG.Quasithin.EmptyFaithful.T1515eA
public import CFSG.RankThree.SteinbergR3ELinearUnitaryOuterOrder
public import CFSG.LieType.Simplicity.Classical
public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open CFSG.Assembly.LowTwoRank (StatedLieAdmissible StatedProj StatedSL projectiveSpecialLinearGroupEquivStatedProj)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

namespace He8

theorem three_dvd_card_psl_two (F : Type) [Field F] [Finite F] :
    3 ∣ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := by
  rw [Nat.card_congr (projectiveSpecialLinearGroupEquivStatedProj 2 F).toEquiv]
  have hdiv := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (K := F) (n := 2)
    (by norm_num)
  rw [show 2 * (2 - 1) / 2 = 1 from rfl, show Finset.Icc 2 2 = ({2} : Finset ℕ) by decide,
    Finset.prod_singleton, pow_one] at hdiv
  set q := Nat.card F with hq
  have hq1 : 1 ≤ q := Nat.card_pos
  have hgd : Nat.gcd 2 (q - 1) ∣ q * (q ^ 2 - 1) :=
    Dvd.dvd.mul_left ((Nat.gcd_dvd_right 2 _).trans (Nat.sub_one_dvd_pow_sub_one _ 2)) _
  have h := Nat.div_mul_cancel hgd
  rw [← hdiv] at h
  have h3 : 3 ∣ q * (q ^ 2 - 1) := by
    have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq1
    rcases (show q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 by omega) with h0 | h0 | h0
    · exact Dvd.dvd.mul_right (Nat.dvd_of_mod_eq_zero h0) _
    · refine Dvd.dvd.mul_left (Nat.dvd_of_mod_eq_zero ?_) _
      have : q ^ 2 % 3 = 1 := by rw [Nat.pow_mod, h0]
      omega
    · refine Dvd.dvd.mul_left (Nat.dvd_of_mod_eq_zero ?_) _
      have : q ^ 2 % 3 = 1 := by rw [Nat.pow_mod, h0]
      omega
  rw [← h] at h3
  have hg : Nat.gcd 2 (q - 1) ∣ 2 := Nat.gcd_dvd_left _ _
  have hcop : Nat.Coprime 3 (Nat.gcd 2 (q - 1)) :=
    Nat.Coprime.coprime_dvd_right hg (by norm_num)
  exact hcop.dvd_of_dvd_mul_right h3

theorem statedModel_psl_two_n {n : ℕ} (hn : 3 ≤ n) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2))
      .PSL n 2 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine CFSG.LieType.Universal.SpecialLinear.statedClassicalModel_center_quotient m (ZMod 2)
    ?_ (by rw [Nat.card_zmod, pow_one])
  refine ⟨Nat.prime_two, le_rfl, by omega, ?_, ?_⟩
  · intro h
    simp only [Prod.mk.injEq] at h
    omega
  · intro h
    simp only [Prod.mk.injEq] at h
    omega

theorem isSolvable_outer_psl_two_n {n : ℕ} (hn : 3 ≤ n) :
    Group.IsSolvable (Outer (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2))) := by
  have hmod := statedModel_psl_two_n hn
  have : Finite (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2)) :=
    CFSG.LieType.Simplicity.finite_of_statedClassicalModel hmod
  obtain ⟨hout, -⟩ := CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
    (τ := .PSL) (Or.inl rfl) hn Nat.prime_two le_rfl hmod
  have hd : CFSG.RankThree.OuterOrder.determinantParameter .PSL n (2 ^ 1) = 1 := by
    unfold CFSG.RankThree.OuterOrder.determinantParameter
    show Nat.gcd n (2 ^ 1 - 1) = 1
    rw [show 2 ^ 1 - 1 = 1 by norm_num, Nat.gcd_one_right]
  rw [hd] at hout
  have h2 : Nat.card (Outer (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2))) ∣ 2 := by
    simpa using hout
  have hp : IsPGroup 2 (Outer (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2))) := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [h]; rfl)
    · exact IsPGroup.of_card (n := 1) (by rw [h]; rfl)
  have : Finite (Outer (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2))) := inferInstance
  have : Group.IsNilpotent (Outer (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2))) :=
    hp.isNilpotent
  infer_instance


theorem exists_noncomm_of_exclusion {S : Type} [Group S] [Finite S] (h : A318Exclusion S) :
    ∃ a b : S, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have := h.simple
  let _ : CommGroup S := { ‹Group S› with mul_comm := hcon }
  have hp : Nat.Prime (Nat.card S) := IsSimpleGroup.prime_card
  have h9 := h.nine_dvd_card
  have h3 : 3 ∣ Nat.card S := dvd_trans (by norm_num) h9
  rcases (Nat.dvd_prime hp).mp h3 with h1 | h1
  · omega
  · rw [← h1] at h9
    omega

theorem isQuasisimple_of_exclusion {Q S : Type} [Group Q] [Group S] [Finite S] (e : Q ≃* S)
    (hS : A318Exclusion S) : CFSG.IsQuasisimple Q := by
  have := hS.simple
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup (exists_noncomm_of_exclusion hS)).1

end He8

end CFSG.Quasithin
