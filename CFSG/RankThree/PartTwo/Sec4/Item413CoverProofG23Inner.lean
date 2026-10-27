module

public import CFSG.RankThree.PartTwo.Sec4.Item413CoverProofU43McL
public import CFSG.LieType.Multipliers.G23Bridge

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

@[expose] def Inputs413CoverG23Inner : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L A E : Subgroup G) (c : G), Hyp413 L A E c →
    Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) = 3 →
    Blueprint.ChevalleyExceptionalModel ((L ⧸ aschbacherSolvableCore 3 L) ⧸
      Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) .G2 3 1 →
    aschbacherSolvableCore 3 L = ⊥ ∧
      (Subgroup.center L).map L.subtype = Subgroup.zpowers c ∧
      ∀ a ∈ A, ∃ l ∈ L, ∀ y ∈ L, a * y * a⁻¹ = l * y * l⁻¹

namespace Res413Cover

variable {G : Type} [Group G] [Finite G]

theorem theta_eq_bot_of_g23 {L : Subgroup G} (hL : CFSG.IsQuasisimple L)
    (hZodd : Odd (Nat.card (Subgroup.center L)))
    (hcard : Nat.card (L ⧸ Subgroup.center L) = 4245696) : aschbacherSolvableCore 3 L = ⊥ := by
  have hθ3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 L) :=
    (solvable_prime_complement_core_characterization Nat.prime_three).2.2.1
  have hdvd : Nat.card (aschbacherSolvableCore 3 L) ∣ Nat.card (Subgroup.center L) :=
    Subgroup.card_dvd_of_le (aschbacherSolvableCore_le_center hL)
  by_contra hne
  have h1 : Nat.card (aschbacherSolvableCore 3 L) ≠ 1 := fun h =>
    hne (Subgroup.eq_bot_of_card_eq _ h)
  set p := (Nat.card (aschbacherSolvableCore 3 L)).minFac with hp
  have hpp : p.Prime := Nat.minFac_prime h1
  have hpθ : p ∣ Nat.card (aschbacherSolvableCore 3 L) := Nat.minFac_dvd _
  have hpZ : p ∣ Nat.card (Subgroup.center L) := hpθ.trans hdvd
  have hp2 : p ≠ 2 := by
    rintro h2
    rw [h2] at hpZ
    obtain ⟨k, hk⟩ := hZodd
    omega
  have hp3 : p ≠ 3 := by
    rintro h3
    rw [h3] at hpθ
    exact hθ3 hpθ
  refine Res4Three.not_dvd_card_center_of_not_sq_dvd hL.1.commutator_eq_top hpp ?_ hpZ
  rw [hcard]
  exact Res4Three.not_sq_dvd_of_eq_mul (i := 6) (j := 6) (m := 91) (by norm_num) hpp hp2 hp3
    (Res4Three.no_sq_of_le (by norm_num) (by norm_num) (by decide))

end Res413Cover

open Res413Cover

section Of


theorem inputs413CoverG23Inner_of (h45 : Item4_5) : Inputs413CoverG23Inner := by
  intro G _ _ L A E c hyp hZ3 hM
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hL := hyp.2.1
  have hZodd := odd_card_center_of_hyp413 h45 hyp
  obtain ⟨hG, -, hT, hr⟩ := hyp
  obtain ⟨hAmax, hAc, hc3, -, -, -⟩ := hT
  have hA := hAmax.prop
  obtain ⟨m, hm5, hm⟩ := exists_card_eq_of_four_lt_pRank hA hr
  have hAN : A ≤ Subgroup.normalizer (L : Set G) :=
    h45 G hG A (isPGroup_of_isElemAbelian hA) (Or.inr ⟨hA, m, by omega, hm⟩) L
      (mem_thetaComponents_of_isComponent3 hL)
  have hperf : Group.IsPerfect L := hL.1.1
  set eL := (Res417Three.thetaQuotCenterEquiv hL.1).symm with heL
  obtain ⟨K, _, _, hK, ⟨eK⟩⟩ := exists_mulEquiv_adjointGroup_G2 hM
  have hcard : Nat.card (L ⧸ Subgroup.center L) = 4245696 := by
    rw [Nat.card_congr eL.toEquiv, Nat.card_congr eK.toEquiv]
    exact CFSG.LieType.Multipliers.G23.card_adjointGroup_G2_eq (by rw [hK, pow_one])
  have hθ := theta_eq_bot_of_g23 hL.1 hZodd hcard
  have hZL3 : Nat.card (Subgroup.center L) = 3 := by
    have hmkinj : Function.Injective (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) := by
      rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
      exact hθ
    have hbij : Function.Bijective (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) :=
      ⟨hmkinj, QuotientGroup.mk'_surjective _⟩
    set e := MulEquiv.ofBijective (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) hbij
    rw [← hZ3, ← Subgroup.map_center_eq e]
    exact (Subgroup.card_map_of_injective e.injective).symm
  have hOut : ¬ 3 ∣ Nat.card (Outer L) :=
    not_three_dvd_card_outer_of_quotient eL (inputs47Core_outG23 _ hM)
  have hinner : ∀ a ∈ A, ∃ l ∈ L, ∀ y ∈ L, a * y * a⁻¹ = l * y * l⁻¹ := by
    intro a haA
    have ha3 : a ^ 3 = 1 := hA.2 a haA
    set σ := L.normalizerMonoidHom ⟨a, hAN haA⟩ with hσ
    have hσ3 : σ ^ 3 = 1 := by
      have h1 : (⟨a, hAN haA⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
        Subtype.ext (by simpa using ha3)
      rw [hσ, ← map_pow, h1, map_one]
    obtain ⟨l, hl⟩ := mem_range_conj_of_pow_three hOut hσ3
    refine ⟨l, l.2, fun y hy => ?_⟩
    have h1 := congrArg (fun τ : MulAut L => ((τ ⟨y, hy⟩ : L) : G)) hl
    exact h1.symm
  have hle : (Subgroup.center L).map L.subtype ≤ Subgroup.zpowers c := by
    rintro _ ⟨z, hz, rfl⟩
    have hz3 : (z : G) ^ 3 = 1 := by
      have h := pow_card_eq_one' (G := Subgroup.center L) (x := ⟨z, hz⟩)
      rw [hZL3] at h
      exact congrArg Subtype.val (congrArg Subtype.val h)
    have hzC : (z : G) ∈ Subgroup.centralizer (L : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun y hy =>
        (congrArg Subtype.val ((Subgroup.mem_center_iff.mp hz) ⟨y, hy⟩))
    have hzA : (z : G) ∈ A := mem_of_maximal_of_commute hAmax hz3 fun a ha => by
      obtain ⟨l, hlL, hal⟩ := hinner a ha
      have h1 := hal z z.2
      have h2 : l * (z : G) = z * l := Subgroup.mem_centralizer_iff.mp hzC l hlL
      have h3 : a * (z : G) * a⁻¹ = z := by rw [h1, h2, mul_inv_cancel_right]
      calc a * (z : G) = a * z * a⁻¹ * a := by group
        _ = z * a := by rw [h3]
    rw [← hAc]
    exact ⟨hzA, hzC⟩
  refine ⟨hθ, Subgroup.eq_of_le_of_card_ge hle ?_, hinner⟩
  rw [Nat.card_zpowers, hc3, Subgroup.card_map_of_injective L.subtype_injective, hZL3]

end Of

section Holds

theorem inputs413CoverG23Inner_holds
    : Inputs413CoverG23Inner :=
  inputs413CoverG23Inner_of rank3II_4_5

end Holds

end CFSG.RankThree.PartTwo.Sec4
