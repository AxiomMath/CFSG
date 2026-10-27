module

import CFSG.Goldschmidt.Steps.G310Basic
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.PartTwo.Sec16.Item167Proof
public import CFSG.RankThree.PartTwo.Sec14.Item1411Strong
public import CFSG.RankThree.PartTwo.Sec15.Item152Proof
public import CFSG.RankThree.PartTwo.Sec17.Item17Setup

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof165

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec17
  CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem sylow_of_fusionIsSylowIn {p : ℕ} [Fact p.Prime] {T U : Subgroup G}
    (h : CFSG.Open.fusionIsSylowIn p T U) :
    ∃ P : Sylow p ↥U, (P : Subgroup ↥U) = T.subgroupOf U := by
  obtain ⟨hTU, hT, hmax⟩ := h
  refine ⟨⟨T.subgroupOf U, hT.comap_subtype, fun {Q} hQ hTQ => ?_⟩, rfl⟩
  have h1 := hmax (Q.map U.subtype) (Subgroup.map_subtype_le Q) (hQ.map U.subtype) fun s hs =>
    ⟨⟨s, hTU hs⟩, hTQ (show (⟨s, hTU hs⟩ : U) ∈ T.subgroupOf U from hs), rfl⟩
  rw [← h1]
  exact (Subgroup.comap_map_eq_self_of_injective U.subtype_injective Q).symm

omit [Finite G] in
theorem fusionIsSylowIn_of_not_dvd_index {p : ℕ} [Fact p.Prime] {T U : Subgroup G}
    (hTU : T ≤ U) (hT : IsPGroup p T) (hidx : ¬ p ∣ (T.subgroupOf U).index) :
    CFSG.Open.fusionIsSylowIn p T U := by
  have h := CFSG.Goldschmidt.G310.fusionIsSylowIn_map (hT.comap_subtype.toSylow hidx)
  have heq : (((hT.comap_subtype (K := U)).toSylow hidx : Sylow p ↥U) : Subgroup ↥U).map
      U.subtype = T := by
    change (T.subgroupOf U).map U.subtype = T
    exact Subgroup.map_subgroupOf_eq_of_le hTU
  rwa [heq] at h

omit [Finite G] in
theorem exists_mk_eq_of_le_normalizer {D T : Subgroup G}
    (hTD : T ≤ Subgroup.normalizer (D : Set G)) (x : ↥(D ⊔ T)) :
    ∃ t ∈ T, ∃ ht : t ∈ D ⊔ T,
      (QuotientGroup.mk x : ↥(D ⊔ T) ⧸ D.subgroupOf (D ⊔ T)) = QuotientGroup.mk ⟨t, ht⟩ := by
  have hx : (x : G) ∈ ((D ⊔ T : Subgroup G) : Set G) := x.2
  rw [Subgroup.coe_mul_of_right_le_normalizer_left D T hTD] at hx
  obtain ⟨d, hd, t, ht, hdt⟩ := hx
  have htDT : t ∈ D ⊔ T := (le_sup_right : T ≤ D ⊔ T) ht
  refine ⟨t, ht, htDT, ?_⟩
  rw [QuotientGroup.eq]
  refine Subgroup.mem_subgroupOf.mpr ?_
  have : ((x⁻¹ * ⟨t, htDT⟩ : ↥(D ⊔ T)) : G) = (t⁻¹ * d * t)⁻¹ := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, ← hdt]
    change (d * t)⁻¹ * t = (t⁻¹ * d * t)⁻¹
    group
  rw [this]
  refine D.inv_mem ?_
  have := (Subgroup.mem_normalizer_iff.mp (hTD (T.inv_mem ht)) d).mp hd
  simpa [mul_assoc] using this

omit [Finite G] in
theorem isCharacteristicP_sup {D T : Subgroup G} (hTD : T ≤ Subgroup.normalizer (D : Set G))
    (hT : IsPGroup 2 T) (hD : IsCharacteristicP 2 ↥D) : IsCharacteristicP 2 ↥(D ⊔ T) := by
  have hN : (D.subgroupOf (D ⊔ T)).Normal := by
    rw [sup_comm]
    exact Subgroup.normal_subgroupOf_sup_of_le_normalizer hTD
  have hq : IsPGroup 2 (↥(D ⊔ T) ⧸ D.subgroupOf (D ⊔ T)) := by
    intro g
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨t, ht, htDT, hxt⟩ := exists_mk_eq_of_le_normalizer hTD x
    obtain ⟨k, hk⟩ := hT ⟨t, ht⟩
    refine ⟨k, ?_⟩
    rw [hxt, ← QuotientGroup.mk_pow]
    have : (⟨t, htDT⟩ : ↥(D ⊔ T)) ^ 2 ^ k = 1 := by
      apply Subtype.ext
      have := congrArg Subtype.val hk
      simpa using this
    rw [this, QuotientGroup.mk_one]
  have hDc : IsCharacteristicP 2 ↥(D.subgroupOf (D ⊔ T)) :=
    Sec14.isCharacteristicP_of_mulEquiv' (Subgroup.subgroupOfEquivOfLe le_sup_left).symm hD
  exact Sec14.isCharacteristicP_of_isPGroup_quotient (D.subgroupOf (D ⊔ T)) hq hDc

@[expose] noncomputable def stellmacherSub (T : Subgroup G) : Subgroup G :=
  (S4Free.stellmacherWSz.{0, 0} ↥T).map T.subtype

theorem stellmacherSub_spec (hst : StellmacherKP) (hR : TheoremFourHyp G) {T : Subgroup G}
    (hT2 : IsPGroup 2 T) (hT1 : T ≠ ⊥) :
    stellmacherSub T ≤ T ∧ stellmacherSub T ≠ ⊥ ∧
      Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (stellmacherSub T : Set G) ∧
      ∀ U : Subgroup G, T ≤ U → ¬ 3 ∣ Nat.card U → CFSG.Open.fusionIsSylowIn 2 T U →
        IsCharacteristicP 2 ↥U → U ≤ Subgroup.normalizer (stellmacherSub T : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnt : Nontrivial ↥T := (Subgroup.nontrivial_iff_ne_bot T).mpr hT1
  set W := S4Free.stellmacherWSz.{0, 0} ↥T with hW
  have hW1 : W ≠ ⊥ := S4Free.stellmacherClauseSz_iff.mp (hst.1 ↥T hT2 hnt)
  refine ⟨Subgroup.map_subtype_le W, ?_, ?_, ?_⟩
  · intro h
    exact hW1 ((Subgroup.map_eq_bot_iff_of_injective _ T.subtype_injective).mp h)
  · have := S4Free.stellmacherWSz_characteristic (S := ↥T)
    exact CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic W
  · intro U hTU hU3 hsyl hchar
    set ι : ↥T →* ↥U := Subgroup.inclusion hTU with hι
    have hrange : ι.range = T.subgroupOf U := by
      ext x
      constructor
      · rintro ⟨s, rfl⟩
        exact Subgroup.mem_subgroupOf.mpr s.2
      · intro hx
        exact ⟨⟨x, Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩
    obtain ⟨P, hP⟩ := sylow_of_fusionIsSylowIn hsyl
    have hC : Subgroup.centralizer (S4Free.oTwo ↥U : Set ↥U) ≤ S4Free.oTwo ↥U := by
      rw [Sec15.oTwo_eq_pCore]
      exact hchar
    have hadm : S4Free.IsAdmissibleHost ι :=
      S4Free.isAdmissibleHost_of_not_three_dvd hU3 (Subgroup.inclusion_injective hTU)
        ⟨P, by rw [hrange, hP]⟩ hC
    have hWU : (W.map ι).Normal := S4Free.stellmacherWSz_normal hadm (hR.szSections hst.2 hU3)
    have hCU : W.map T.subtype ≤ U := (Subgroup.map_subtype_le W).trans hTU
    have heq : (W.map T.subtype).subgroupOf U = W.map ι := by
      ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
      constructor
      · rintro ⟨w, hw, hwx⟩
        exact ⟨w, hw, Subtype.ext hwx⟩
      · rintro ⟨w, hw, rfl⟩
        exact ⟨w, hw, rfl⟩
    rw [stellmacherSub, ← Subgroup.normal_subgroupOf_iff_le_normalizer hCU, heq]
    exact hWU

theorem exists_stellmacher (hst : StellmacherKP) (hR : TheoremFourHyp G) {T : Subgroup G}
    (hT2 : IsPGroup 2 T) (hT1 : T ≠ ⊥) :
    ∃ C : Subgroup G, C ≤ T ∧ C ≠ ⊥ ∧
      Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (C : Set G) ∧
      ∀ U : Subgroup G, T ≤ U → ¬ 3 ∣ Nat.card U → CFSG.Open.fusionIsSylowIn 2 T U →
        IsCharacteristicP 2 ↥U → U ≤ Subgroup.normalizer (C : Set G) :=
  ⟨stellmacherSub T, stellmacherSub_spec hst hR hT2 hT1⟩

variable {A : Subgroup G}

theorem mem_scriptQ_of_three (hA : IsE27 A) (h146 : Item146 A (lB A)) {X : Subgroup G}
    (hXΔ : X = delta A (lB A) X) (hAX : A ≤ Subgroup.normalizer (X : Set G))
    (hX3 : ¬ 3 ∣ Nat.card X) : X ∈ scriptQ A (lB A) := by
  have hinv : X ∈ invariantPiSubgroups ⊤ A (piCompl 3) :=
    ⟨le_top, (isPiSubgroup_piCompl_iff Nat.prime_three X).mpr hX3, hAX⟩
  have := delta_mem_scriptQ hA h146 hinv
  rwa [← hXΔ] at this

theorem delta_mem_scriptQ_of_three (hA : IsE27 A) (h146 : Item146 A (lB A)) (Z : Subgroup G)
    (hZ3 : ¬ 3 ∣ Nat.card (delta A (lB A) Z)) : delta A (lB A) Z ∈ scriptQ A (lB A) :=
  mem_scriptQ_of_three hA h146 (delta_delta Z).symm (le_normalizer_delta Z) hZ3

theorem fusionIsSylowIn_of_mem_scriptQPiStar (hA : IsE27 A) {X S : Subgroup G}
    (hXQ : X ∈ scriptQ A (lB A)) (hX3 : ¬ 3 ∣ Nat.card X)
    (hS : S ∈ scriptQPiStar A (lB A) X (piOf 2)) : CFSG.Open.fusionIsSylowIn 2 S X := by
  have hS2 : IsPGroup 2 S := isPGroup_of_mem_scriptQPi Nat.prime_two hS.prop
  have hAS : A ≤ Subgroup.normalizer (S : Set G) := hS.prop.1.1.1.2.2
  obtain ⟨S', hS', hSS', hAS'⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
    Nat.prime_three Nat.prime_two hA.isPGroup hX3 hXQ.1.2.2 hS.prop.1.2 hS2 hAS
  have hS'mem : S' ∈ scriptQPi A (lB A) X (piOf 2) :=
    ⟨⟨mem_scriptQ_of_le hXQ hS'.1 hAS', hS'.1⟩,
      (isPiSubgroup_piOf_iff Nat.prime_two S').mpr hS'.2.1⟩
  have := hS.eq_of_le hS'mem hSS'
  exact this ▸ hS'

theorem mem_scriptY1_of_three {X : Subgroup G} (hX : X ∈ scriptY3 A (lB A))
    (hX3 : ¬ 3 ∣ Nat.card X) : X ∈ scriptY1 A (lB A) :=
  ⟨hX, oPrimeResidualOf_three_eq_bot_of_not_dvd hX3⟩

theorem not_three_dvd_of_mem_scriptY1 {X : Subgroup G} (hX : X ∈ scriptY1 A (lB A)) :
    ¬ 3 ∣ Nat.card X :=
  not_three_dvd_of_oPrimeResidualOf_eq_bot hX.2

theorem delta_normalizer_mem_scriptY3 (hsimp : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) {C : Subgroup G} (hC1 : C ≠ ⊥) (hC2 : IsPGroup 2 C)
    (hCQ : C ∈ scriptQ A (lB A)) :
    delta A (lB A) (Subgroup.normalizer (C : Set G)) ∈ scriptY3 A (lB A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := Subgroup.normalizer (C : Set G) with hK
  have hKtop : K ≠ ⊤ := normalizer_ne_top_of_isPGroup hsimp hnab hC1 hC2
  have hCD : C ≤ delta A (lB A) K := le_delta hCQ Subgroup.le_normalizer
  have hCO : C ≤ CFSG.Open.pCoreOf 2 (delta A (lB A) K) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hCD (delta_le K) hC2
  refine ⟨⟨⟨fun h => hKtop (top_le_iff.mp (h ▸ delta_le K)), le_normalizer_delta K⟩, ?_⟩,
    (delta_delta K).symm⟩
  intro h0
  rw [h0] at hCO
  exact hC1 (le_bot_iff.mp hCO)

variable {c : G} {L Y₀ : Subgroup G}

theorem normalizer_le_M (h : Sec17Std G A c L Y₀) {C : Subgroup G} (hC1 : C ≠ ⊥)
    (hC2 : IsPGroup 2 C) (hYC : Y₀ ⊔ A ≤ Subgroup.normalizer (C : Set G)) :
    Subgroup.normalizer (C : Set G) ≤ Subgroup.normalizer (Y₀ : Set G) := by
  have hloc : CFSG.Assembly.IsTwoLocal (Subgroup.normalizer (C : Set G)) := ⟨C, hC1, hC2, rfl⟩
  obtain ⟨M', hM', hle⟩ := exists_mem_scriptM_of_isTwoLocal hloc (SetLike.coe_subset_coe.mpr hYC)
  change M' ∈ CFSG.maximalTwoLocalsContaining _ at hM'
  rw [h.scriptM_eq] at hM'
  rw [← Set.mem_singleton_iff.mp hM']
  exact hle

end CFSG.RankThree.PartTwo.Sec16.Proof165
