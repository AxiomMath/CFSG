module

public import CFSG.Permutation.FiveTransitive.Degree25DoubleElevenLocalSupport
public import CFSG.Permutation.FiveTransitive.Degree25StabilizerFinalFactor

public section

namespace CFSG

namespace FiveTransitive.Degree25

open MulAction SubMulAction Subgroup

private theorem eleven_residue_forces_indices_one
    (h c r : ℕ) (hc : c ∣ 2) (hr : r ∣ 10)
    (hfive : h % 11 = 5) (hresidue : h % 11 = (5 * (c * r)) % 11) :
    c = 1 ∧ r = 1 := by
  have hcLe : c ≤ 2 := Nat.le_of_dvd (by omega) hc
  have hrLe : r ≤ 10 := Nat.le_of_dvd (by omega) hr
  interval_cases c
  all_goals norm_num at hc
  all_goals interval_cases r
  all_goals norm_num at hr
  all_goals norm_num at hresidue
  all_goals omega

private theorem eleven_transfer_contradiction
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 25)
    (hP5 : MulAction.IsMultiplyPretransitive P X 5)
    (h : ℕ) (hnotEleven : ¬11 ∣ h)
    (e : Fin 3 ↪ X)
    (hJcard : Nat.card (fixingSubgroup P (Set.range e)) = 462 * h)
    (T : Sylow 11 (fixingSubgroup P (Set.range e)))
    (hTcard : Nat.card T = 11)
    (hnormalizer : Subgroup.normalizer (T : Set (fixingSubgroup P (Set.range e))) ≤
      Subgroup.centralizer (T : Set (fixingSubgroup P (Set.range e)))) : False := by
  classical
  letI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  let J := fixingSubgroup P (Set.range e)
  have hh : h ≠ 0 := by
    rintro rfl
    exact hnotEleven (dvd_zero 11)
  have hecard : (Set.range e).ncard = 3 := by
    rw [Set.ncard_range_of_injective e.injective,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  let transfer : J →* T :=
    MonoidHom.transferSylow T hnormalizer
  let Q : Subgroup J := transfer.ker
  letI : Q.Normal := by
    dsimp only [Q, transfer]
    infer_instance
  have hcomplement : IsComplement' Q T := by
    simpa only [Q, transfer] using
      MonoidHom.ker_transferSylow_isComplement'
        T hnormalizer
  have hcardMul := hcomplement.card_mul
  have hQcard : Nat.card Q = 42 * h := by
    rw [hTcard, hJcard] at hcardMul
    nlinarith only [hcardMul]
  let Z := SubMulAction.ofFixingSubgroup P (Set.range e)
  have hZcard : Nat.card Z = 22 := by
    change Nat.card ↥((Set.range e)ᶜ : Set X) = 22
    rw [Nat.card_coe_set_eq]
    have htotal :=
      Set.ncard_add_ncard_compl (Set.range e)
    rw [Nat.card_eq_fintype_card, hcard,
      hecard] at htotal
    omega
  have hJ2 :
      MulAction.IsMultiplyPretransitive J Z 2 := by
    letI : MulAction.IsMultiplyPretransitive P X 5 := hP5
    change
      MulAction.IsMultiplyPretransitive
        (fixingSubgroup P (Set.range e))
        (SubMulAction.ofFixingSubgroup P (Set.range e)) 2
    apply SubMulAction.ofFixingSubgroup.isMultiplyPretransitive
      (m := 2) (n := 5) P (Set.range e)
    omega
  letI : MulAction.IsPreprimitive J Z :=
    MulAction.isPreprimitive_of_is_two_pretransitive hJ2
  letI : Nonempty Z :=
    Fintype.card_pos_iff.mp (by
      rw [← Nat.card_eq_fintype_card, hZcard]
      norm_num)
  have hfaithfulJ :
      ∀ j : J, (∀ z : Z, j • z = z) → j = 1 := by
    intro j hj
    apply Subtype.ext
    apply P.subtype_injective
    ext x
    by_cases hx : x ∈ Set.range e
    · have hfix :=
        (mem_fixingSubgroup_iff P).mp j.prop x hx
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def]
        using hfix
    · let z : Z := ⟨x, hx⟩
      have hz := hj z
      have hz' := congrArg Subtype.val hz
      simpa [z, Subgroup.smul_def, Equiv.Perm.smul_def]
        using hz'
  have hnormalCases :=
    OrbitBounds.normal_subgroup_card_eq_one_or_degree_dvd
      J Z hfaithfulJ Q
  have hQneOne : Nat.card Q ≠ 1 := by
    rw [hQcard]
    omega
  have htwentyTwoQ : 22 ∣ Nat.card Q := by
    rcases hnormalCases with hQone | hZdvd
    · exact (hQneOne hQone).elim
    · rwa [hZcard] at hZdvd
  have helevenQ : 11 ∣ Nat.card Q :=
    (by norm_num : 11 ∣ 22).trans htwentyTwoQ
  rw [hQcard] at helevenQ
  rcases (show Nat.Prime 11 by norm_num).dvd_mul.mp
      helevenQ with heleven | heleven
  · norm_num at heleven
  · exact hnotEleven heleven

theorem five_point_stabilizer_mod_eleven_ne_five
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 25)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    Nat.card (fixingSubgroup P s) % 11 ≠ 5 := by
  classical
  let H : Subgroup P := fixingSubgroup P s
  let h := Nat.card H
  change h % 11 ≠ 5
  intro hfive
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
  have hJfactorization : (462 * h).factorization 11 = 1 := by
    simpa only [show 11 * 42 = 462 by norm_num] using
      LongPrimeArithmetic.factorization_prime_mul_once 11 42 h
        (by decide) (by norm_num) hnotEleven
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
    nlinarith only [hconstraints.2.2.2.2.2]
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
  have hcrOne : c = 1 ∧ r = 1 :=
    eleven_residue_forces_indices_one h c r hconstraints.1 hconstraints.2.1
      hfive hresidue
  have hnormalizer :
      Subgroup.normalizer ((T : Subgroup J) : Set J) ≤
        Subgroup.centralizer ((T : Subgroup J) : Set J) := by
    exact Subgroup.relIndex_eq_one.mp
      (show CJ.relIndex NJ = 1 by
        simpa only [CJ, NJ, r] using hcrOne.2)
  exact eleven_transfer_contradiction X P hcard hP5 h hnotEleven e hJcard T
    hTcard hnormalizer

end FiveTransitive.Degree25

end CFSG
