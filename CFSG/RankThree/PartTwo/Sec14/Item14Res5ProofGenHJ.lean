module

public import CFSG.RankThree.PartTwo.Sec14.Item14Res5ProofGenM12
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
import CFSG.RankThree.PartTwo.KFacts.KS14HJSignalizer
import CFSG.RankThree.PartTwo.Sec14.Item148PtRes2ProofTypes
import CFSG.RankThree.PartTwo.Sec14.Concl142NHJInner
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearInnerFixed

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

@[expose] def KS142J2Order : Prop :=
  ∀ H : Subgroup CFSG.Blueprint.NativeSporadic.J2, 2 ^ 6 * 3 ^ 3 ∣ Nat.card H → H = ⊤

namespace Res5GenHJ

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
set_option maxHeartbeats 1000000 in
theorem eq_top_of_dvd_of_mulEquiv (hord : KS142J2Order)
    (φ : X ≃* CFSG.Blueprint.NativeSporadic.J2) {H : Subgroup X}
    (h : 2 ^ 6 * 3 ^ 3 ∣ Nat.card H) : H = ⊤ := by
  have h1 : H.map φ.toMonoidHom = ⊤ := by
    apply hord
    rw [Subgroup.card_map_of_injective φ.injective]
    exact h
  rw [← Subgroup.map_top_of_surjective φ.toMonoidHom φ.surjective] at h1
  exact Subgroup.map_injective φ.injective h1

theorem sSup_eq_top_of_item415 (h415 : Sec4.Item4_15)
    (hX : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2)) [IsSimpleGroup X]
    (hord : ∀ H : Subgroup X, 2 ^ 6 * 3 ^ 3 ∣ Nat.card H → H = ⊤) {E : Subgroup X}
    (hE9 : Nat.card E = 9) :
    sSup {Y : Subgroup X | ¬ 3 ∣ Nat.card Y ∧ E ≤ Subgroup.normalizer (Y : Set X)} = ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE3 : IsPGroup 3 E := IsPGroup.of_card (n := 2) (by rw [hE9]; norm_num)
  obtain ⟨P, hEP⟩ := hE3.exists_le_sylow
  obtain ⟨⟨hHeis, -⟩, -, -, -, h5⟩ := h415 X hX P _ rfl _ rfl
  have hP27 : Nat.card (P : Subgroup X) = 27 := hHeis.2.1
  obtain ⟨S, hS, hSset, -, ⟨T, ⟨e⟩⟩, -⟩ := h5 E ⟨hEP, hE9⟩
  have hS64 : 2 ^ 6 ∣ Nat.card S := by
    rw [Nat.card_congr e.toEquiv]
    exact T.pow_dvd_card_of_pow_dvd_card (by rw [KFacts.KS14.card_projSL_three_four]; norm_num)
  set 𝒮 := maxInvariantPiSubgroups ⊤ E (piOf 2) with h𝒮
  set T₀ := sSup 𝒮 with hT₀
  have hST₀ : S ≤ T₀ := le_sSup hS
  have hPN : (P : Subgroup X) ≤ Subgroup.normalizer (T₀ : Set X) := by
    intro x hx
    refine Subgroup.mem_normalizer_fintype fun t ht => ?_
    have hle : T₀ ≤ T₀.comap (MulAut.conj x).toMonoidHom := by
      refine sSup_le fun M hM => ?_
      rw [hSset] at hM
      obtain ⟨y, hy, rfl⟩ := hM
      intro m hm
      obtain ⟨s, hs, rfl⟩ := hm
      show x * ((MulAut.conj y⁻¹).toMonoidHom s) * x⁻¹ ∈ T₀
      have hmem : conjugate S (y * x⁻¹) ∈ 𝒮 := by
        rw [hSset]
        exact ⟨y * x⁻¹, mul_mem hy (inv_mem hx), rfl⟩
      refine le_sSup hmem ⟨s, hs, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev, inv_inv]
      group
    exact hle ht
  have hdvd : 2 ^ 6 * 3 ^ 3 ∣ Nat.card ↥(T₀ ⊔ (P : Subgroup X)) := by
    refine Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) ?_ ?_
    · exact hS64.trans ((Subgroup.card_dvd_of_le hST₀).trans
        (Subgroup.card_dvd_of_le le_sup_left))
    · rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hP27]
      exact Subgroup.card_dvd_of_le le_sup_right
  have htop : T₀ ⊔ (P : Subgroup X) = ⊤ := hord _ hdvd
  have hT₀n : T₀.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← htop]
    exact sup_le Subgroup.le_normalizer hPN
  have hT₀top : T₀ = ⊤ := by
    rcases hT₀n.eq_bot_or_eq_top with hb | ht
    · exfalso
      have h1 : Nat.card S ∣ 1 := by
        have := Subgroup.card_dvd_of_le hST₀
        rwa [hb, Subgroup.card_bot] at this
      have h64 : 2 ^ 6 ∣ 1 := hS64.trans h1
      norm_num at h64
    · exact ht
  refine eq_top_iff.mpr (hT₀top.ge.trans (sSup_le_sSup fun M hM => ⟨?_, hM.prop.2.2⟩))
  have hM2 : IsPGroup 2 M := (isPiSubgroup_piOf_iff Nat.prime_two M).mp hM.prop.2.1
  obtain ⟨k, hk⟩ := hM2.exists_card_eq
  rw [hk]
  intro h3
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
    (Nat.prime_three.dvd_of_dvd_pow h3)
  norm_num at this

set_option maxHeartbeats 1000000 in
theorem sSup_eq_top_of_mulEquiv_J2 (h415 : Sec4.Item4_15)
    (hJs : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J2) (hord : KS142J2Order)
    (φ : X ≃* CFSG.Blueprint.NativeSporadic.J2) {E : Subgroup X} (hE9 : Nat.card E = 9) :
    sSup {Y : Subgroup X | ¬ 3 ∣ Nat.card Y ∧ E ≤ Subgroup.normalizer (Y : Set X)} = ⊤ := by
  have : IsSimpleGroup X := @MulEquiv.isSimpleGroup _ _ _ _ hJs φ
  exact sSup_eq_top_of_item415 h415 ⟨φ⟩ (fun H h => eq_top_of_dvd_of_mulEquiv hord φ h) hE9

end Res5GenHJ

open Res5Gen Res5GenHJ in
set_option maxHeartbeats 2000000 in
theorem step142LowerGenHJ_of
    (h131 : Item131) (hord : KS142J2Order) :
    Step142LowerGenHJ := by
  intro G _ _ A c L h ⟨φ⟩
  have hspor := Sec13.sporadicModels131
  obtain ⟨-, h9, hAc⟩ := point_facts_of_inner h131 hspor h.toSec13Data
    (center_eq_bot_of_mulEquiv φ hspor.2.2.2)
    (not_isLThreePi_of_mulEquiv φ Item148PtRes2.not_isoLThreePi_J2)
  exact sSup_autThetaQuot_eq_top_of_inner h hAc
    (sSup_eq_top_of_mulEquiv_J2 Sec4.Sporadic.rank3II_4_15 CFSG.Sporadic.J2.isSimpleGroup_J2 hord
      φ (card_image_inf h h9))

theorem step142LowerGenNA7_of_L3
    (h131 : Item131) (hord : KS142J2Order) (hL3 : Step142LowerGenL3) : Step142LowerGenNA7 :=
  step142LowerGenNA7_of_types h131 (step142LowerGenM12_of h131) (step142LowerGenHJ_of h131 hord) hL3

end CFSG.RankThree.PartTwo.Sec14
