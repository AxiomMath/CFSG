module

public import CFSG.Quasithin.H13.NQCatT513Inner
public import CFSG.Sporadic.Schreier.J1Outer
public import CFSG.Sporadic.Schreier.PairJ2Pairs
public import CFSG.Sporadic.Schreier.J4SOutOdd
public import CFSG.Sporadic.SmallOddCore.HSAut
public import CFSG.Sporadic.Schreier.RuAutInner
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115SporadicMathieu
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965

public section

namespace CFSG.Quasithin.H13.NQCat.T513P

open CFSG.Open CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms

theorem finite_mulAut (X : Type) [Group X] [Finite X] : Finite (MulAut X) :=
  Finite.of_injective (fun f : MulAut X => (f : X → X)) fun _ _ h => MulEquiv.ext (congrFun h)

theorem finite_outer (X : Type) [Group X] [Finite X] : Finite (Outer X) := by
  have := finite_mulAut X
  exact Finite.of_surjective _ (QuotientGroup.mk'_surjective (inner X))

theorem oddAutThreeInner_of_card_outer_le_two {X : Type} [Group X] [Finite X]
    (h : Nat.card (Outer X) ≤ 2) : OddAutThreeInner X := by
  have := finite_outer X
  have hpos : 0 < Nat.card (Outer X) := Nat.card_pos
  refine oddAutThreeInner_of_card_outer_dvd (a := 1) (b := 0) ?_
  interval_cases (Nat.card (Outer X)) <;> norm_num

theorem oddAut_alt7 : OddAutThreeInner (alternatingGroup (Fin 7)) :=
  oddAutThreeInner_of_inner fun φ hφ => by
    obtain ⟨g, rfl⟩ :=
      CFSG.GorensteinWalter.gw_lemma_3_2_ix_a7_no_outer_automorphisms_odd_order φ hφ
    exact ⟨g, rfl⟩

theorem oddAut_m22 :
    OddAutThreeInner (NativeSporadic.Carrier .M22) := by
  have : Finite (NativeSporadic.Carrier .M22) := (CFSG.Sporadic.Mathieu.fam_m22_simplicity).1
  have hc : Subgroup.center ↥NativeSporadic.M22 = ⊥ := CFSG.Sporadic.Schreier.m22_center_eq_bot'
  have hinner : Nat.card ↥(inner ↥NativeSporadic.M22) = Nat.card ↥NativeSporadic.M22 := by
    rw [Nat.card_congr ((innerEquivQuot _).trans (quotCenterEquivOfBot hc)).toEquiv]
  have := finite_mulAut ↥NativeSporadic.M22
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (inner ↥NativeSporadic.M22)
  have h2 := CFSG.Sporadic.Schreier.m22_mulAut_card
  rw [h1, hinner] at h2
  have hpos : 0 < Nat.card ↥NativeSporadic.M22 := Nat.card_pos
  refine oddAutThreeInner_of_card_outer_le_two ?_
  exact Nat.le_of_mul_le_mul_right h2 hpos

theorem oddAut_m23 :
    OddAutThreeInner (NativeSporadic.Carrier .M23) :=
  oddAutThreeInner_of_inner fun φ _ => CFSG.QuasithinUnique.Ch1.m23_all_inner φ

theorem allInner_j1
    (φ : MulAut (NativeSporadic.Carrier .J1)) : φ ∈ inner (NativeSporadic.Carrier .J1) := by
  obtain ⟨g, rfl⟩ := CFSG.Sporadic.Schreier.at_j1_schreier.2.1 φ
  exact ⟨g, rfl⟩

theorem oddAut_j1 :
    OddAutThreeInner (NativeSporadic.Carrier .J1) :=
  oddAutThreeInner_of_inner fun φ _ => allInner_j1 φ

theorem oddAut_j2 :
    OddAutThreeInner (NativeSporadic.Carrier .J2) := by
  have : Finite (NativeSporadic.Carrier .J2) := (CFSG.Sporadic.J2.fam_j2_simplicity).1
  exact oddAutThreeInner_of_card_outer_le_two CFSG.Sporadic.Schreier.AT_J2_Schreier.1

theorem oddAut_hs :
    OddAutThreeInner (NativeSporadic.Carrier .HS) := by
  have : Finite (NativeSporadic.Carrier .HS) := (CFSG.Sporadic.HS.fam_hs_simplicity).1
  exact oddAutThreeInner_of_card_outer_le_two
    (CFSG.Sporadic.Schreier.outer_card_le_of_equiv CFSG.Sporadic.SmallOddCore.hs_outer_card_le
      CFSG.Sporadic.Schreier.hsPermEquiv)

theorem odd_card_outer_j4
    {T : Type} [Group T] (e : T ≃* NativeSporadic.Carrier .J4) : Odd (Nat.card (Outer T)) := by
  rw [@CFSG.Sporadic.J4Schreier.card_outer_congr T CFSG.Sporadic.J4.J _ (Subgroup.toGroup _)
    (e.trans (CFSG.Sporadic.J4.seedEquiv CFSG.Sporadic.J4.j4Facts.mat))]
  exact CFSG.Sporadic.J4Schreier.CTU_J4_outer_automorphism_group_odd_order

theorem oddAut_j4 :
    OddAutThreeInner (NativeSporadic.Carrier .J4) := by
  have : Finite (NativeSporadic.Carrier .J4) := (CFSG.Sporadic.J4.fam_j4_simplicity).1
  have hodd : Odd (Nat.card (Outer (NativeSporadic.Carrier .J4))) :=
    odd_card_outer_j4 (MulEquiv.refl _)
  have hJ4 : Nonempty (NativeSporadic.Carrier .J4 ≃* NativeSporadic.J4) := ⟨MulEquiv.refl _⟩
  have hprimes := (CFSG.Sporadic.J4Schreier.R3E_J4_outer_automorphism_group_no_large_primes
    (T := NativeSporadic.Carrier .J4) hJ4).1
  have := finite_outer (NativeSporadic.Carrier .J4)
  have hpos : Nat.card (Outer (NativeSporadic.Carrier .J4)) ≠ 0 := Nat.card_pos.ne'
  have h3 : Nat.card (Outer (NativeSporadic.Carrier .J4)) =
      3 ^ (Nat.card (Outer (NativeSporadic.Carrier .J4))).primeFactorsList.length := by
    refine Nat.eq_prime_pow_of_unique_prime_dvd hpos fun {d} hd hdvd => ?_
    rcases hprimes d hd hdvd with rfl | rfl
    · exact absurd (hodd.not_two_dvd_nat hdvd) (by simp)
    · rfl
  refine oddAutThreeInner_of_card_outer_dvd (a := 0)
    (b := (Nat.card (Outer (NativeSporadic.Carrier .J4))).primeFactorsList.length) ?_
  rw [pow_zero, one_mul, ← h3]

theorem oddAut_ru :
    OddAutThreeInner (NativeSporadic.Carrier .Ru) := by
  have : Finite (NativeSporadic.Carrier .Ru) := (CFSG.Sporadic.Ru.fam_ru_simplicity).1
  exact oddAutThreeInner_of_card_outer_le_two
    (CFSG.Sporadic.Schreier.outer_card_le_of_equiv
      (by rw [CFSG.Sporadic.RuSchreier.card_outer_ruP]; norm_num) CFSG.Sporadic.RuSchreier.ruEquivP)

end CFSG.Quasithin.H13.NQCat.T513P
