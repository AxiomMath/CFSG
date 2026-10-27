module

import CFSG.RankThree.PartTwo.Sec16.Item163StepsAltProofTools
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization
public import CFSG.RankThree.PartTwo.Sec17.Item17TailData

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
open CFSG.RankThreeEvenClassification.Helpers
  (exists_centralizer_with_same_image_of_trivial_quotient_action)
open Equiv
open scoped commutatorElement

namespace Proof17Res2

variable {G : Type} [Group G] [Finite G]

theorem false_of_mem_centralizerSection_of_not_mem {Y : Subgroup G}
    (hmax : ∀ E ∈ partTwoE G, ∀ B : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B → E ≤ B → B = E)
    (hO : CFSG.Open.pCoreOf 2 Y ≠ ⊥) (φ : ↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 10))
    {e : G} (he3 : e ^ 3 = 1)
    (hecs : e ∈ CFSG.GH74.GLS.centralizerSection Y (CFSG.Open.pCoreOf 2 Y)) (heY : e ∉ Y) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := CFSG.pCore 2 ↥Y with hN
  set π := QuotientGroup.mk' N with hπ
  set O := CFSG.Open.pCoreOf 2 Y with hOdef
  have hOp : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y
  have hYO : Y ≤ Subgroup.normalizer (O : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y
  have heN : e ∈ Subgroup.normalizer (Y : Set G) := hecs.1
  have hep : IsPGroup 3 (Subgroup.zpowers e) := by
    rintro ⟨g, hg⟩
    obtain ⟨t, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, he3, one_zpow]
  have hzN : Subgroup.zpowers e ≤ Subgroup.normalizer (Y : Set G) := Subgroup.zpowers_le.mpr heN
  have hzcs : Subgroup.zpowers e ≤ CFSG.GH74.GLS.centralizerSection Y O :=
    Subgroup.zpowers_le.mpr hecs
  have hker3 : ¬ 3 ∣ Nat.card π.ker := by
    rw [hπ, QuotientGroup.ker_mk']
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥Y))
    rw [hm]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hlift : ∀ y : ↥Y, ∃ y' : ↥Y,
      (y' : G) ∈ Subgroup.centralizer (Subgroup.zpowers e : Set G) ∧ π y' = π y := by
    intro y
    refine exists_centralizer_with_same_image_of_trivial_quotient_action
      3 Nat.prime_three (Subgroup.zpowers e) Y hep hzN π hker3 (fun member element => ?_) y
    have h := (hzcs member.2).2.2 (element⁻¹ : ↥Y) (element⁻¹ : ↥Y).2
    rw [hπ, eq_comm, Sec16.Step163Alt.mk_eq_mk_iff]
    simpa only [commutatorElement_def, Subgroup.coe_inv, mul_assoc, inv_inv] using h
  set K := Y ⊓ Subgroup.centralizer (Subgroup.zpowers e : Set G) with hK
  set κ : ↥Y →* Perm (Fin 10) :=
    (alternatingGroup (Fin 10)).subtype.comp (φ.toMonoidHom.comp π) with hκ
  set f : ↥K →* Perm (Fin 10) := κ.comp (Subgroup.inclusion inf_le_left) with hf
  have hfker : IsPGroup 2 f.ker := by
    rintro ⟨z, hz⟩
    have hz1 : π (Subgroup.inclusion inf_le_left z) = 1 := by
      have h1 : φ (π (Subgroup.inclusion inf_le_left z)) = 1 :=
        Subtype.ext (by simpa [hf, hκ] using hz)
      rw [← map_one φ] at h1
      exact φ.injective h1
    have hzO : (z : G) ∈ O := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
        Sec16.Step163Alt.mem_pCore_two_iff] at hz1
      exact hz1
    obtain ⟨n, hn⟩ := hOp ⟨z, hzO⟩
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hn
    simpa using this
  have hEf : CFSG.RankThree.PartTwo.KFacts.KP2.eTwentySeven ≤ f.range := by
    intro z hz
    have hzA := CFSG.RankThree.PartTwo.KFacts.KP2.eTwentySeven_le_alternatingGroup hz
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective N (φ.symm ⟨z, hzA⟩)
    obtain ⟨y', hy'C, hy'⟩ := hlift y
    refine ⟨⟨y', y'.2, hy'C⟩, ?_⟩
    change ((φ (π y') : alternatingGroup (Fin 10)) : Perm (Fin 10)) = z
    rw [hy', show π y = φ.symm ⟨z, hzA⟩ from hy, MulEquiv.apply_symm_apply]
  obtain ⟨S, hSK, hS, hS27⟩ := Sec16.Step163Alt.exists_elemAbelian_lift f hfker
    Sec16.Step163Alt.isElemAbelian_eTwentySeven hEf
  rw [CFSG.RankThree.PartTwo.KFacts.K412.card_eTwentySeven] at hS27
  have hSE : S ∈ partTwoE G :=
    ⟨hS, hS27, O, hO, hOp, (hSK.trans inf_le_left).trans hYO⟩
  have hSe : ∀ x ∈ S, x * e = e * x := fun x hx =>
    (Subgroup.mem_centralizer_iff.mp (hSK hx).2 e (Subgroup.mem_zpowers e)).symm
  have hsup := hmax S hSE (S ⊔ Subgroup.zpowers e) (Sec15.isElemAbelian_sup_zpowers hS he3 hSe)
    le_sup_left
  have heS : e ∈ S := hsup ▸ (le_sup_right : Subgroup.zpowers e ≤ S ⊔ Subgroup.zpowers e)
    (Subgroup.mem_zpowers e)
  exact heY ((hSK heS).1)

theorem not_three_dvd_card_cQuot {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
    (h : Sec17Std G A c L Y₀)
    (hA10 : Nonempty (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀ ≃* alternatingGroup (Fin 10))) :
    ¬ 3 ∣ Nat.card (cQuot Y₀) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨φ⟩ := hA10
  have hFE : partTwoF G = partTwoE G :=
    (h.toTheoremFourHyp.partTwoF_eq_partTwoE h.partTwoS_eq).1
  have hmax : ∀ E ∈ partTwoE G, ∀ B : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B → E ≤ B →
      B = E := fun E hE B hB hEB => (hFE ▸ hE : E ∈ partTwoF G).2.1 B hB hEB
  have hO : CFSG.Open.pCoreOf 2 Y₀ ≠ ⊥ := h.mem_y0Star.prop.2.2
  have hZ := Sec16.Step163Alt.center_eq_bot_of_ten φ
  intro h3
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(cQuot Y₀)) 3 h3
  set e : G := (x : G) with he
  have heo : orderOf e = 3 := by rw [he, Subgroup.orderOf_coe, hx]
  have he3 : e ^ 3 = 1 := by rw [← heo]; exact pow_orderOf_eq_one e
  have hex : e ∈ (cQuot Y₀ : Set G) := x.2
  rw [coe_cQuot] at hex
  obtain ⟨heN, hecomm⟩ := hex
  have hecs : e ∈ CFSG.GH74.GLS.centralizerSection Y₀ (CFSG.Open.pCoreOf 2 Y₀) := by
    refine ⟨heN, CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y₀ heN,
      fun k hk => ?_⟩
    have h1 := Subgroup.inv_mem _ (hecomm k hk)
    have e1 : (e * k * e⁻¹ * k⁻¹)⁻¹ = ⁅k, e⁆ := by
      rw [commutatorElement_def]
      group
    rwa [e1] at h1
  by_cases heY : e ∈ Y₀
  · have heO := Sec16.Step163Alt.mem_pCoreOf_of_mem_centralizerSection hZ heY hecs
    obtain ⟨j, hj⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y₀) ⟨e, heO⟩
    have hj' : e ^ 2 ^ j = 1 := by
      have := congrArg Subtype.val hj
      simpa using this
    have h1 : e = 1 := Sec16.Step163Alt.eq_one_of_two_three hj' (by rwa [pow_one])
    rw [h1, orderOf_one] at heo
    omega
  · exact false_of_mem_centralizerSection_of_not_mem hmax hO φ he3 hecs heY

end Proof17Res2

end CFSG.RankThree.PartTwo.Sec17
