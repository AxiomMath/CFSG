module

public import CFSG.RankThree.PartTwo.Sec16.Item1617StepsProofTools
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
public import CFSG.RankThree.PartTwo.Sec16.Item16Tail19

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS

@[expose] def KS1619AutPerfect : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), 2 ≤ n → Sec4.IsoLThreePi X 2 n →
    ∀ J : Subgroup (MulAut X), Group.IsPerfect J → ¬ 3 ∣ Nat.card J → J = ⊥

theorem ks1619LCen_of (hK : KS1619AutPerfect) : KS1619LCen := by
  intro G _ _ L J n hL hn hiso hJN hJp hJ3
  have hθ := Proof1617.theta_eq_bot_of_isSimpleGroup hL hn hiso
  have hn2 : 2 ≤ n := by
    by_contra hlt
    have hn1 : n = 1 := by omega
    subst hn1
    rcases hiso with ⟨h3, -⟩ | ⟨-, ⟨φ⟩⟩
    · norm_num at h3
    · have hLiso : ↥L ≃* CFSG.Assembly.RankThreeEven.projSU 3 2 1 :=
        ((QuotientGroup.quotientMulEquivOfEq hθ).trans QuotientGroup.quotientBot).symm.trans φ
      have : Group.IsSolvable (CFSG.Assembly.RankThreeEven.projSU 3 2 1) :=
        Sec13.isSolvable_projSU_two
      have : Group.IsSolvable ↥L :=
        Group.isSolvable_of_isSolvable_injective (f := hLiso.toMonoidHom) hLiso.injective
      have hcomm : commutator ↥L = ⊥ := by
        have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial ↥L
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator ↥L) with h | h
        · exact h
        · exact absurd h hlt.ne
      have hab : ∀ a b : ↥L, a * b = b * a := by
        intro a b
        have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp
          (by rw [← commutator_def]; exact hcomm) (Subgroup.mem_top a)
        exact (Subgroup.mem_centralizer_iff.mp h1 b (Subgroup.mem_top b)).symm
      let _ : CommGroup ↥L := { mul_comm := hab }
      have hp := IsSimpleGroup.prime_card (α := ↥L)
      have hc := KFacts.KS14.card_projSU_three_mul_gcd 2 1 le_rfl
      norm_num at hc
      rw [Nat.card_congr hLiso.toEquiv] at hp
      have h72 : Nat.card (CFSG.Assembly.RankThreeEven.projSU 3 2 1) = 72 := by omega
      rw [h72] at hp
      norm_num at hp
  set N := Subgroup.normalizer (L : Set G) with hN
  set ρ : N →* MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
    (Sec4.thetaQuotMulAut ↥L).comp L.normalizerMonoidHom with hρ
  set J' : Subgroup N := J.subgroupOf N with hJ'
  have e : J' ≃* J := Subgroup.subgroupOfEquivOfLe hJN
  have : Group.IsPerfect J' := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom)
    e.symm.surjective
  have hperf : Group.IsPerfect (J'.map ρ) := Group.IsPerfect.map ρ
  have hcard : ¬ 3 ∣ Nat.card (J'.map ρ) := by
    intro h3
    apply hJ3
    refine h3.trans ((Subgroup.card_map_dvd (H := J') ρ).trans ?_)
    rw [Nat.card_congr e.toEquiv]
  have hbot := hK _ n hn2 hiso _ hperf hcard
  intro j hj
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have hρj : ρ ⟨j, hJN hj⟩ = 1 := by
    have hmem : ρ ⟨j, hJN hj⟩ ∈ J'.map ρ :=
      Subgroup.mem_map_of_mem ρ (Subgroup.mem_subgroupOf.mpr hj)
    rw [hbot] at hmem
    exact Subgroup.mem_bot.mp hmem
  have h1 := congrArg (fun σ : MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L) =>
    σ ((⟨l, hl⟩ : ↥L) : ↥L ⧸ aschbacherSolvableCore 3 ↥L)) hρj
  simp only [hρ, MonoidHom.coe_comp, Function.comp_apply, Sec4.thetaQuotMulAut_mk,
    MulAut.one_apply] at h1
  rw [QuotientGroup.eq, hθ, Subgroup.mem_bot] at h1
  have h2 : (((L.normalizerMonoidHom ⟨j, hJN hj⟩) ⟨l, hl⟩ : ↥L) : G) = l := by
    have h3 := congrArg Subtype.val h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one] at h3
    exact inv_mul_eq_one.mp h3
  rw [Sec4.normalizerMonoidHom_apply_coe] at h2
  calc l * j = j * l * j⁻¹ * j := by rw [h2]
    _ = j * l := by group

end CFSG.RankThree.PartTwo.Sec16
