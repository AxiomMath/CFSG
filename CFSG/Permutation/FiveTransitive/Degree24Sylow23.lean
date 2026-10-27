module

public import CFSG.Permutation.FiveTransitive.Degree19LongPrimeNormalizers

public section

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction SubMulAction Subgroup

theorem five_point_stabilizer_mod_twentyThree_cases
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    let h := Nat.card (fixingSubgroup P s)
    h % 23 = 19 ∨ h % 23 = 15 ∨
      h % 23 = 2 ∨ h % 23 = 4 := by
  classical
  dsimp
  let H : Subgroup P := fixingSubgroup P s
  let h := Nat.card H
  change
    h % 23 = 19 ∨ h % 23 = 15 ∨
      h % 23 = 2 ∨ h % 23 = 4
  have hh : h ≠ 0 := Nat.ne_of_gt Nat.card_pos
  let Y := SubMulAction.ofFixingSubgroup P s
  have hYcard : Nat.card Y = 19 := by
    change Nat.card ↥(sᶜ : Set X) = 19
    rw [Nat.card_coe_set_eq]
    have htotal := Set.ncard_add_ncard_compl s
    rw [Nat.card_eq_fintype_card, hcard, hs] at htotal
    omega
  have hfaithful :
      Function.Injective (MulAction.toPermHom H Y) := by
    intro a b hab
    apply Subtype.ext
    apply P.subtype_injective
    ext x
    by_cases hx : x ∈ s
    · have ha :=
        (mem_fixingSubgroup_iff P).mp a.prop x hx
      have hb :=
        (mem_fixingSubgroup_iff P).mp b.prop x hx
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using
        ha.trans hb.symm
    · let y : Y := ⟨x, hx⟩
      have hy :=
        congrArg (fun q : Equiv.Perm Y => q y) hab
      have hy' := congrArg Subtype.val hy
      simpa [y, Subgroup.smul_def, Equiv.Perm.smul_def] using
        hy'
  have hHdvdFactorial : h ∣ (19 : ℕ).factorial := by
    have hdvd :=
      Subgroup.card_dvd_of_injective
        (MulAction.toPermHom H Y) hfaithful
    rw [Nat.card_perm, Nat.card_eq_fintype_card,
      ← Nat.card_eq_fintype_card, hYcard] at hdvd
    exact hdvd
  have hnotTwentyThree : ¬23 ∣ h := by
    intro hdvd
    have : 23 ∣ (19 : ℕ).factorial :=
      hdvd.trans hHdvdFactorial
    norm_num at this
  have hP5 : MulAction.IsMultiplyPretransitive P X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨g, hg⟩ :=
      h5 a b a.injective b.injective
    refine ⟨g, ?_⟩
    ext i
    exact hg i
  have hHindexRaw :=
    hP5.index_of_fixingSubgroup_mul hs
  rw [Nat.card_eq_fintype_card, hcard] at hHindexRaw
  norm_num at hHindexRaw
  have hHindex : H.index = 5100480 := by
    change (fixingSubgroup P s).index = 5100480
    omega
  have hHindexCard := H.index_mul_card
  have hPcard : Nat.card P = 5100480 * h := by
    rw [hHindex] at hHindexCard
    exact hHindexCard.symm
  letI : Fact (Nat.Prime 23) := ⟨by norm_num⟩
  have hPfactorization :
      (5100480 * h).factorization 23 = 1 := by
    rw [show 5100480 = 23 * 221760 by norm_num,
      Nat.mul_assoc,
      Nat.factorization_mul (by norm_num)
        (Nat.mul_ne_zero (by norm_num) hh),
      Finsupp.add_apply,
      (show Nat.Prime 23 by norm_num).factorization,
      Finsupp.single_eq_same,
      Nat.factorization_mul (by norm_num) hh,
      Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num),
      Nat.factorization_eq_zero_of_not_dvd hnotTwentyThree]
    norm_num
  let S : Sylow 23 P := Sylow.nonempty.some
  have hScard : Nat.card S = 23 := by
    rw [S.card_eq_multiplicity, hPcard,
      hPfactorization]
    norm_num
  let C : Subgroup P :=
    Subgroup.centralizer (S : Set P)
  let N : Subgroup P :=
    Subgroup.normalizer (S : Set P)
  let r := C.relIndex N
  have hglobal :
      r ∣ 22 ∧
        0 < r ∧
        N.index % 23 = 1 ∧
        r * N.index * 23 = Nat.card P := by
    simpa only [C, N, r] using
      Degree19.long_prime_normalizer_constraints
        X P h5 hnotAlt (p := 23) (f := 1)
          (by norm_num) (by norm_num) (by norm_num)
          (by omega) S hScard
  have hglobalDivided :
      r * N.index = 221760 * h := by
    rw [hPcard] at hglobal
    nlinarith [hglobal.2.2.2]
  have hglobalMod :
      (17 * h) % 23 = r % 23 := by
    calc
      (17 * h) % 23 = (221760 * h) % 23 := by
        simp [Nat.mul_mod]
      _ = (r * N.index) % 23 :=
        congrArg (fun n => n % 23)
          hglobalDivided.symm
      _ = r % 23 := by
        rw [Nat.mul_mod, hglobal.2.2.1]
        simp
  have hresidue :
      h % 23 = (19 * r) % 23 := by
    have hm : 17 * h ≡ r [MOD 23] :=
      hglobalMod
    have hm' := hm.mul_left 19
    change
      (19 * (17 * h)) % 23 =
        (19 * r) % 23 at hm'
    calc
      h % 23 = (23 * (14 * h) + h) % 23 := by
        simp
      _ = (19 * (17 * h)) % 23 := by
        congr 1
        ring
      _ = (19 * r) % 23 := hm'
  have hrLe : r ≤ 22 :=
    Nat.le_of_dvd (by norm_num) hglobal.1
  have hrCases :
      r = 1 ∨ r = 2 ∨ r = 11 ∨ r = 22 := by
    interval_cases r
    all_goals try norm_num at hglobal
    all_goals omega
  rcases hrCases with hr | hr | hr | hr
  all_goals rw [hr] at hresidue
  all_goals norm_num at hresidue
  all_goals omega

end FiveTransitive.Degree24

end CFSG
