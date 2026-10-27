module

public import CFSG.Permutation.FiveTransitive.Degree25DoubleElevenLocalSupport
public import CFSG.Permutation.FiveTransitive.Degree25StabilizerFinalFactor

public section

namespace CFSG

namespace FiveTransitive.Degree25

open MulAction SubMulAction Subgroup

theorem five_point_stabilizer_mod_eleven_cases
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 25)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    let h := Nat.card (fixingSubgroup P s)
    h % 11 = 1 ∨ h % 11 = 3 ∨ h % 11 = 5 ∨
      h % 11 = 6 ∨ h % 11 = 9 ∨ h % 11 = 10 := by
  classical
  let H : Subgroup P := fixingSubgroup P s
  let h := Nat.card H
  change
    h % 11 = 1 ∨ h % 11 = 3 ∨ h % 11 = 5 ∨
      h % 11 = 6 ∨ h % 11 = 9 ∨ h % 11 = 10
  have hh : h ≠ 0 := Nat.card_pos.ne'
  have hdiv : h ∣ 10450944000 := by
    simpa only [H, h] using
      five_point_stabilizer_card_dvd_final
        X P hcard h5 hnotAlt s hs
  have hnotEleven : ¬11 ∣ h := by
    intro hdvd
    have : 11 ∣ 10450944000 := hdvd.trans hdiv
    norm_num at this
  have hP5 : MulAction.IsMultiplyPretransitive P X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨q, hq⟩ :=
      h5 a b a.injective b.injective
    refine ⟨q, ?_⟩
    ext i
    exact hq i
  have hP3 : MulAction.IsMultiplyPretransitive P X 3 := by
    letI : MulAction.IsMultiplyPretransitive P X 5 := hP5
    exact MulAction.isMultiplyPretransitive_of_le
      (G := P) (α := X) (m := 3) (n := 5)
        (by omega) (by
          rw [Nat.card_eq_fintype_card, hcard]
          omega)
  have hHindexRaw :=
    hP5.index_of_fixingSubgroup_mul hs
  rw [Nat.card_eq_fintype_card, hcard] at hHindexRaw
  norm_num at hHindexRaw
  have hHindex : H.index = 6375600 := by
    change (fixingSubgroup P s).index = 6375600
    omega
  have hHindexCard := H.index_mul_card
  have hPcard : Nat.card P = 6375600 * h := by
    rw [hHindex] at hHindexCard
    exact hHindexCard.symm
  have heNonempty : Nonempty (Fin 3 ↪ X) :=
    Fintype.card_pos_iff.mp (by
      rw [Fintype.card_embedding_eq,
        Fintype.card_fin, hcard]
      norm_num)
  let e : Fin 3 ↪ X := Classical.choice heNonempty
  let J : Subgroup P :=
    fixingSubgroup P (Set.range e)
  have hecard : (Set.range e).ncard = 3 := by
    rw [Set.ncard_range_of_injective e.injective,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  have hJindexRaw :=
    hP3.index_of_fixingSubgroup_mul hecard
  rw [Nat.card_eq_fintype_card, hcard] at hJindexRaw
  norm_num at hJindexRaw
  have hJindex : J.index = 13800 := by
    change
      (fixingSubgroup P (Set.range e)).index = 13800
    omega
  have hJindexCard := J.index_mul_card
  have hJcard : Nat.card J = 462 * h := by
    rw [hJindex, hPcard] at hJindexCard
    omega
  letI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hJfactorization :
      (462 * h).factorization 11 = 1 := by
    rw [show 462 = 11 * 42 by norm_num,
      Nat.mul_assoc,
      Nat.factorization_mul (by norm_num)
        (Nat.mul_ne_zero (by norm_num) hh),
      Finsupp.add_apply,
      (show Nat.Prime 11 by norm_num).factorization,
      Finsupp.single_eq_same,
      Nat.factorization_mul (by norm_num) hh,
      Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num),
      Nat.factorization_eq_zero_of_not_dvd hnotEleven]
    norm_num
  let T : Sylow 11 J := Sylow.nonempty.some
  have hTcard : Nat.card T = 11 := by
    rw [T.card_eq_multiplicity, hJcard,
      hJfactorization]
    norm_num
  let CJ : Subgroup J :=
    Subgroup.centralizer ((T : Subgroup J) : Set J)
  have hCJdvdTwoFortyTwo : Nat.card CJ ∣ 242 := by
    simpa only [CJ] using
      local_sylow_eleven_centralizer_card_dvd_two_hundred_forty_two
        X P hcard h5 hnotAlt e J rfl T hTcard
  have hCJJ : Nat.card CJ ∣ Nat.card J :=
    Subgroup.card_subgroup_dvd_card CJ
  have hnotJ : ¬121 ∣ Nat.card J := by
    intro hdvd
    have hge :
        2 ≤ (Nat.card J).factorization 11 :=
      (show Nat.Prime 11 by norm_num).pow_dvd_iff_le_factorization
        Nat.card_pos.ne' |>.mp hdvd
    rw [hJcard, hJfactorization] at hge
    omega
  have hnotCJ : ¬121 ∣ Nat.card CJ := by
    intro hdvd
    exact hnotJ (hdvd.trans hCJJ)
  have hCJdvdTwentyTwo : Nat.card CJ ∣ 22 :=
    dvd_twenty_two_of_dvd_two_hundred_forty_two
      hCJdvdTwoFortyTwo hnotCJ
  let NJ : Subgroup J :=
    Subgroup.normalizer ((T : Subgroup J) : Set J)
  let c := (T : Subgroup J).relIndex CJ
  let r := CJ.relIndex NJ
  have hconstraints :
      c ∣ 2 ∧ r ∣ 10 ∧ 0 < c ∧ 0 < r ∧
        NJ.index % 11 = 1 ∧
        c * r * NJ.index * 11 = Nat.card J := by
    simpa only [CJ, NJ, c, r] using
      sylow_eleven_normalizer_constraints_of_centralizer_card_dvd
        J 2 T hTcard (by
          simpa only [CJ] using hCJdvdTwentyTwo)
  have hdivided :
      c * r * NJ.index = 42 * h := by
    rw [hJcard] at hconstraints
    nlinarith [hconstraints.2.2.2.2.2]
  have hmod :
      (9 * h) % 11 = (c * r) % 11 := by
    calc
      (9 * h) % 11 = (42 * h) % 11 := by
        simp [Nat.mul_mod]
      _ = (c * r * NJ.index) % 11 :=
        congrArg (fun n => n % 11) hdivided.symm
      _ = (c * r) % 11 := by
        rw [Nat.mul_mod, hconstraints.2.2.2.2.1]
        simp
  have hresidue :
      h % 11 = (5 * (c * r)) % 11 := by
    have hm : 9 * h ≡ c * r [MOD 11] := hmod
    have hm' := hm.mul_left 5
    calc
      h % 11 = (11 * (4 * h) + h) % 11 := by
        simp
      _ = (5 * (9 * h)) % 11 := by
        congr 1
        ring
      _ = (5 * (c * r)) % 11 := hm'
  have hcCases : c = 1 ∨ c = 2 := by
    have hcLe : c ≤ 2 :=
      Nat.le_of_dvd (by norm_num) hconstraints.1
    interval_cases c
    all_goals try norm_num at hconstraints
    all_goals omega
  have hrCases :
      r = 1 ∨ r = 2 ∨ r = 5 ∨ r = 10 := by
    have hrLe : r ≤ 10 :=
      Nat.le_of_dvd (by norm_num) hconstraints.2.1
    interval_cases r
    all_goals try norm_num at hconstraints
    all_goals omega
  rcases hcCases with hc | hc
  all_goals rcases hrCases with hr | hr | hr | hr
  all_goals rw [hc, hr] at hresidue
  all_goals norm_num at hresidue ⊢
  all_goals omega

end FiveTransitive.Degree25

end CFSG
