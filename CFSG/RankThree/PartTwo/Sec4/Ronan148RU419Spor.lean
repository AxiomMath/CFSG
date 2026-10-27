module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148RU419Odd
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LRowL2ON
public import CFSG.RankThree.PartTwo.Sec6.BThreeCensusOrders

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148R

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.GorensteinWalter (PSL2)

variable {X : Type} [Group X]

theorem dvd_card_projSU_three_two_five : 331 ∣ Nat.card (projSU 3 2 5) := by
  have h := Item419Res3.card_projSU_three_two_mul_three (m := 5) ⟨2, rfl⟩
  norm_num at h
  omega

theorem dvd_card_projSU_three_two_seven : 127 ∣ Nat.card (projSU 3 2 7) := by
  have h := Item419Res3.card_projSU_three_two_mul_three (m := 7) ⟨3, rfl⟩
  norm_num at h
  omega

theorem noCfgU419_of_j4_arith [Finite X] {M : ℕ} (hM : Nat.card X ∣ M) (h19 : ¬ 19 ∣ M)
    (h331 : ¬ 331 ∣ M) (h127 : ¬ 127 ∣ M) (h27 : ¬ 2 ^ 27 ∣ M) : NoCfgU419 X := by
  intro α Y m hc
  have hd := (card_dvd_of_cfg hc).trans hM
  have hm := hc.odd
  rcases (show m = 3 ∨ m = 5 ∨ m = 7 ∨ 9 ≤ m by obtain ⟨j, rfl⟩ := hm; have := hc.one_lt; omega)
    with rfl | rfl | rfl | h9
  · rw [Item419Res3.card_projSU_three_two_three] at hd
    exact h19 ((show (19 : ℕ) ∣ 5515776 by norm_num).trans hd)
  · exact h331 (dvd_card_projSU_three_two_five.trans hd)
  · exact h127 (dvd_card_projSU_three_two_seven.trans hd)
  · exact h27 ((pow_dvd_pow 2 (by omega)).trans
      ((Item419Res3.two_pow_dvd_card_projSU_three_two hm).trans hd))

theorem exists_ne_of_isExtOf {Q B : Type*} [Group Q] [Group B] [Nontrivial Q]
    (hq : IsQuasisimple X) (h : IsExtOf X Q B) : ∃ a b : Q, a * b ≠ b * a := by
  obtain ⟨K, hK, -, ⟨eQ⟩⟩ := h
  haveI : Group.IsPerfect X := hq.1
  have hQp : Group.IsPerfect Q :=
    Group.IsPerfect.ofSurjective (f := eQ.toMonoidHom.comp (QuotientGroup.mk' K))
      (eQ.surjective.comp (QuotientGroup.mk'_surjective K))
  by_contra hall
  push Not at hall
  haveI : Group.IsSolvable Q := isSolvable_of_comm hall
  exact Group.IsPerfect.not_isSolvable Q inferInstance

section Rows


theorem rowsU419One : RowsU419One := by
  intro X _ _ hq _ hX
  apply NoCfgU419.rowU419
  obtain ⟨p, e, _, hp2, he, ⟨φ⟩⟩ := hX
  by_cases hp3 : p = 3
  · subst hp3
    set F := GaloisField 3 e with hF
    have hcard : Nat.card F = 3 ^ e := GaloisField.card 3 e (by omega)
    rcases (show e = 1 ∨ 2 ≤ e by omega) with rfl | he2
    · have hc := RonanK432.card_psl2_mul_gcd F
      rw [hcard] at hc
      norm_num at hc
      refine noCfgU419_of_two_pow_nine (M := 24) ?_ (by decide)
      rw [Nat.card_congr (φ.trans (projSLEquivPSL F)).toEquiv]
      exact Dvd.intro _ hc
    · have h9 : 9 ≤ Nat.card F := by
        rw [hcard]
        calc 9 = 3 ^ 2 := by norm_num
          _ ≤ 3 ^ e := Nat.pow_le_pow_right (by norm_num) he2
      have hs : IsSimpleGroup X := by
        haveI := CFSG.PGLModel.isSimpleGroup_projSL_of_two_le F (n := 2) le_rfl
          (Or.inr (by omega)) (Or.inr (by omega))
        exact φ.isSimpleGroup
      intro α Y m hc
      haveI := hc.isPerfect
      obtain ⟨π, hπ, hker⟩ := hc.cover
      exact Ronan148L.rowU3_L2char3 hs (Census.exists_ne_of_isQuasisimple hq)
        (φ.trans (projSLEquivPSL F)) hc.pow_three hc.ne_one hc.le_autFix hc.isSubnormal hc.odd
        hc.one_lt π hπ hker
  · exact noCfgU419_projSL_two hp3 φ

theorem noCfgU419_on : NoCfgU419 (Blueprint.NativeSporadic.Carrier .ONan) := by
  haveI : Finite (Blueprint.NativeSporadic.Carrier .ONan) :=
    Nat.finite_of_card_ne_zero (by
      show Nat.card Blueprint.NativeSporadic.ON ≠ 0
      rw [CFSG.Sporadic.ON.card_ON]; norm_num)
  haveI hs : IsSimpleGroup (Blueprint.NativeSporadic.Carrier .ONan) :=
    CFSG.Sporadic.ON.isSimpleGroup_ON
  intro α Y m hc
  haveI := hc.isPerfect
  obtain ⟨π, hπ, hker⟩ := hc.cover
  have hna : ∃ a b : Blueprint.NativeSporadic.Carrier .ONan, a * b ≠ b * a := by
    by_contra hall
    push Not at hall
    obtain ⟨E, hEY, -, -, hE9, hEZ⟩ := exists_e9_of_cfg hc
    haveI : Nontrivial E := by
      rw [← Finite.one_lt_card_iff_nontrivial, hE9]
      norm_num
    obtain ⟨⟨z, hz⟩, hz1⟩ := exists_ne (1 : E)
    exact hz1 (Subtype.ext (hEZ z hz (fun k _ => hall z k)))
  exact Ronan148L.rowU3_ON hs hna (MulEquiv.refl _) hc.pow_three hc.ne_one hc.le_autFix
    hc.isSubnormal hc.odd hc.one_lt π hπ hker

theorem card_of_isExtOf_three {S : Type} [Group S] (h : IsExtOf X S (Multiplicative (ZMod 3))) :
    Nat.card X = Nat.card S * 3 := by
  rw [Sec6.BThreeCensus.card_of_isExtOf h, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

theorem rowsU419Five : RowsU419Five := by
  intro X _ _ hq _ hX
  apply NoCfgU419.rowU419
  rcases hX with ⟨s, hs, ⟨φ⟩⟩ | ⟨s, hs, hext⟩
  · have hc : ∀ {N : ℕ}, Nat.card (Blueprint.NativeSporadic.Carrier s) = N → Nat.card X ∣ N :=
      fun h => by rw [Nat.card_congr φ.toEquiv, h]
    simp only [sporadics46, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact noCfgU419_of_two_pow_nine (hc CFSG.Sporadic.Mathieu.card_M11) (by decide)
    · exact noCfgU419_of_two_pow_nine (hc KFacts.KS14.card_nativeM12) (by decide)
    · exact noCfgU419_of_two_pow_nine (hc KFacts.KS14.card_nativeM22) (by decide)
    · exact noCfgU419_of_two_pow_nine
        (hc (CFSG.Sporadic.Schreier.fam_m23_order).choose_spec.2.2.2.choose_spec.2.2.2.2)
        (by decide)
    · exact noCfgU419_of_two_pow_fifteen (hc CFSG.Sporadic.Mathieu.card_M24) (by decide)
        (by decide)
    · exact noCfgU419_of_two_pow_nine (hc CFSG.Sporadic.J1.card_J1) (by decide)
    · exact noCfgU419_of_two_pow_nine (hc CFSG.Sporadic.J2.card_J2) (by decide)
    · exact noCfgU419_of_two_pow_nine (hc CFSG.Sporadic.J3.card_J3) (by decide)
    · exact noCfgU419_of_j4_arith (hc CFSG.Sporadic.J4.card_J4) (by decide) (by decide)
        (by decide) (by decide)
    · exact noCfgU419_of_two_pow_nine (hc CFSG.Sporadic.McL.card_McL) (by decide)
    · exact noCfgU419_of_two_pow_fifteen (hc CFSG.Sporadic.HS.card_HS) (by decide) (by decide)
    · exact noCfgU419_of_two_pow_fifteen (hc CFSG.Sporadic.He.card_He) (by decide) (by decide)
    · exact noCfgU419_of_two_pow_fifteen (hc CFSG.Sporadic.Ru.card_Ru) (by decide) (by decide)
  · simp only [sporadicCovers46, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · refine noCfgU419_of_two_pow_nine (M := 443520 * 3) ?_ (by decide)
      rw [card_of_isExtOf_three hext, show Nat.card (Blueprint.NativeSporadic.Carrier .M22) =
        443520 from KFacts.KS14.card_nativeM22]
    · refine noCfgU419_of_two_pow_nine (M := 50232960 * 3) ?_ (by decide)
      rw [card_of_isExtOf_three hext, show Nat.card (Blueprint.NativeSporadic.Carrier .J3) =
        50232960 from CFSG.Sporadic.J3.card_J3]
    · refine noCfgU419_of_two_pow_nine (M := 898128000 * 3) ?_ (by decide)
      rw [card_of_isExtOf_three hext, show Nat.card (Blueprint.NativeSporadic.Carrier .McL) =
        898128000 from CFSG.Sporadic.McL.card_McL]
    · haveI : Finite (Blueprint.NativeSporadic.Carrier .ONan) :=
        Nat.finite_of_card_ne_zero (by
          show Nat.card Blueprint.NativeSporadic.ON ≠ 0
          rw [CFSG.Sporadic.ON.card_ON]; norm_num)
      haveI : Nontrivial (Blueprint.NativeSporadic.Carrier .ONan) := by
        rw [← Finite.one_lt_card_iff_nontrivial]
        show 1 < Nat.card Blueprint.NativeSporadic.ON
        rw [CFSG.Sporadic.ON.card_ON]; norm_num
      have hQ : Subgroup.center (Blueprint.NativeSporadic.Carrier .ONan) = ⊥ :=
        RonanK429.center_eq_bot_of_isSimpleGroup CFSG.Sporadic.ON.isSimpleGroup_ON
          (exists_ne_of_isExtOf hq hext)
      exact noCfgU419_of_isExtOf hq hext hQ noCfgU419_on

end Rows

end CFSG.RankThree.PartTwo.Sec4.Ronan148R
