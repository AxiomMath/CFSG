module

public import CFSG.RankThree.PartTwo.Sec15.KL3Sub2ProofUni
public import CFSG.RankThree.PartTwo.Sec15.Item15Res5ProofNorm
public import CFSG.LocalAnalysis.ComponentInitial.LinearModelOuterTwoPart
public import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
public import CFSG.RankThree.PartTwo.Sec4.Item462AltProofCases
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P47Rank3

public section

namespace CFSG.RankThree.PartTwo.Sec15

namespace KL3Sub2Proof

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartTwo.KFacts
  CFSG.RankThree.PartTwo.Sec16.Proof166Res6

theorem pRank_two_specialLinear_three_le_two {F : Type} [Field F] [Finite F] (h2 : (2 : F) ≠ 0) :
    CFSG.Open.pRank 2 (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)) ≤ 2 :=
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87.pRank_two_sl3_le_two h2

theorem card_le_four_of_sq_eq_one_projectiveSL {X : Type*} [Group X] [Finite X] {F : Type}
    [Field F] [Finite F] (h2 : (2 : F) ≠ 0) (e : X ≃* projectiveSL 3 F) (E : Subgroup X)
    (hE : ∀ x ∈ E, x * x = 1) : Nat.card E ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    have hab := hE _ (E.mul_mem ha hb)
    have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hE a ha)
    have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hE b hb)
    have : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right hab
    rw [_root_.mul_inv_rev, ha', hb'] at this
    exact this.symm
  have hEl : CFSG.Open.IsElemAbelian 2 E :=
    ⟨⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩, fun x hx => by rw [sq]; exact hE x hx⟩
  have hP : IsPGroup 2 ↥E := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, sq, Subgroup.coe_one]
    exact hE x x.2)⟩
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hkle : k ≤ CFSG.Open.pRank 2 (⊤ : Subgroup X) :=
    CFSG.SectionRank.le_pRank (by norm_num) le_top hEl hk
  have hZ : ¬ 2 ∣ Nat.card (scalars 3 F) := by
    rw [card_scalars_eq_gcd F (by norm_num : 1 ≤ 3)]
    intro h
    have := Nat.dvd_trans h (Nat.gcd_dvd_left 3 (Nat.card F - 1))
    omega
  have hrank : CFSG.Open.pRank 2 (⊤ : Subgroup X) ≤ 2 := by
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e,
      CFSG.SectionRank.pRank_quotient_eq (G := Matrix.SpecialLinearGroup (Fin 3) F)
        (scalars 3 F) hZ]
    exact pRank_two_specialLinear_three_le_two h2
  rw [hk]
  calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (hkle.trans hrank)
    _ = 4 := by norm_num

theorem eq_one_of_forall_commute {G : Type*} [Group G] [IsSimpleGroup G] [Finite G]
    {V : Subgroup G} (hV2 : ∀ v ∈ V, v * v = 1) (hV3 : 2 < Nat.card V) {z : G}
    (hz : ∀ x : G, z * x = x * z) : z = 1 := by
  have hzc : z ∈ Subgroup.center G := Subgroup.mem_center_iff.mpr fun x => (hz x).symm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with hb | ht
  · rw [hb, Subgroup.mem_bot] at hzc
    exact hzc
  · exfalso
    have hab : ∀ a b : G, a * b = b * a := fun a b => by
      have ha : a ∈ Subgroup.center G := ht ▸ Subgroup.mem_top a
      exact ((Subgroup.mem_center_iff.mp ha) b).symm
    obtain ⟨v, hv, hv1⟩ : ∃ v ∈ V, v ≠ 1 := by
      by_contra hno
      push Not at hno
      have : V = ⊥ := (Subgroup.eq_bot_iff_forall V).mpr hno
      rw [this, Subgroup.card_bot] at hV3
      omega
    have hN : (Subgroup.zpowers v).Normal :=
      ⟨fun n hn g => by rw [hab g n, mul_inv_cancel_right]; exact hn⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers v) with hb | ht'
    · apply hv1
      have : v ∈ Subgroup.zpowers v := Subgroup.mem_zpowers v
      rw [hb, Subgroup.mem_bot] at this
      exact this
    · have hcard : Nat.card (Subgroup.zpowers v) ≤ 2 := by
        rw [Nat.card_zpowers]
        exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hV2 v hv))
      have hle : Nat.card V ≤ Nat.card (Subgroup.zpowers v) := by
        rw [ht']
        exact Subgroup.card_le_card_group V |>.trans_eq Subgroup.card_top.symm
      omega

theorem ks1518Norm : KS1518Norm := by
  intro X _ _ r _ hr2 hiso M hM U hU hUM u hu
  have hr : r.Prime := Fact.out
  obtain ⟨eX⟩ : Nonempty (X ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField r 2)) := by
    rcases hiso with ⟨-, he⟩ | ⟨h3, -⟩
    · exact he
    · exfalso
      have hr3 : r ^ 2 % 3 = 0 ∨ r ^ 2 % 3 = 1 := by
        have : r % 3 = 0 ∨ r % 3 = 1 ∨ r % 3 = 2 := by omega
        rcases this with h0 | h0 | h0 <;> simp [Nat.pow_mod, h0]
      omega
  have h2X : (2 : GaloisField r 2) ≠ 0 := by
    intro h0
    have h2r : (r : ℕ) ∣ 2 := (CharP.cast_eq_zero_iff (GaloisField r 2) r 2).mp
      (by exact_mod_cast h0)
    have := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h2r
    exact hr2 this
  have hE := card_le_four_of_sq_eq_one_projectiveSL h2X
    (eX.trans (CFSG.RankThree.PartTwo.Sec4.projSLEquivProjectiveSL 3 (GaloisField r 2)))
  obtain ⟨j, hj⟩ := hU ⟨u, hu⟩
  have huj : u ^ 2 ^ j = 1 := by
    have := congrArg Subtype.val hj
    simpa using this
  have huN := hUM hu
  rcases hM with ⟨eM⟩ | ⟨hr1, ⟨eM⟩⟩
  ·
    obtain ⟨eM⟩ := eM
    set e : ↥M ≃* projectiveSL 3 (GaloisField r 1) :=
      eM.trans (CFSG.RankThree.PartTwo.Sec4.projSLEquivProjectiveSL 3 (GaloisField r 1)) with he
    have hcard1 : Nat.card (GaloisField r 1) = r := by
      rw [GaloisField.card r 1 one_ne_zero, pow_one]
    have hV4 : Nat.card (fourPSL (K := GaloisField r 1)) = 4 := card_fourPSL hr2
    have : IsSimpleGroup (projectiveSL 3 (GaloisField r 1)) := by
      have := CFSG.RankThree.PartTwo.Sec4.Item462AltProof.isSimpleGroup_projSL_three
        (GaloisField r 1)
      exact
        (CFSG.RankThree.PartTwo.Sec4.projSLEquivProjectiveSL 3 (GaloisField r 1)).symm.isSimpleGroup
    refine mem_of_pow_two_pow_eq_one e hE (V := fourPSL (K := GaloisField r 1))
      (fun v hv => mul_self_of_mem_fourPSL hv) (by omega) ?_
      (aut_cases_projectiveSL (ringEquiv_eq_one_of_card_prime hr hcard1)) huN huj
    intro m hm
    apply e.injective
    rw [map_one]
    refine eq_one_of_forall_commute (V := fourPSL (K := GaloisField r 1))
      (fun v hv => mul_self_of_mem_fourPSL hv) (by omega) fun x => ?_
    obtain ⟨y, rfl⟩ := e.surjective x
    rw [← map_mul, ← map_mul, hm y]
  ·
    have hu1 : UnitaryFieldData r 1 (GaloisField r (2 * 1)) :=
      CFSG.RankThree.PartTwo.Sec4.unitaryFieldData_galoisField r 1 le_rfl
    set e : ↥M ≃* unitaryPSU hu1 3 :=
      eM.trans (CFSG.RankThree.PartTwo.Sec4.projSUEquivUnitaryPSU r 1 hu1) with he
    have hV4 : Nat.card (fourPSU hu1) = 4 := card_fourPSU hu1 hr2
    have : IsSimpleGroup (unitaryPSU hu1 3) := by
      have := CFSG.RankThree.PartTwo.Sec4.Item462AltProof.isSimpleGroup_projSU_three r 1 le_rfl
        (by omega)
      exact (CFSG.RankThree.PartTwo.Sec4.projSUEquivUnitaryPSU r 1 hu1).symm.isSimpleGroup
    have : Finite (unitaryPSU hu1 3) := Finite.of_equiv _ e.toEquiv
    refine mem_of_pow_two_pow_eq_one e hE (V := fourPSU hu1)
      (fun v hv => mul_self_of_mem_fourPSU hu1 hv) (by omega) ?_
      (aut_cases_unitaryPSU hu1 hr1) huN huj
    intro m hm
    apply e.injective
    rw [map_one]
    refine eq_one_of_forall_commute (V := fourPSU hu1)
      (fun v hv => mul_self_of_mem_fourPSU hu1 hv) (by omega) fun x => ?_
    obtain ⟨y, rfl⟩ := e.surjective x
    rw [← map_mul, ← map_mul, hm y]

end KL3Sub2Proof

end CFSG.RankThree.PartTwo.Sec15
