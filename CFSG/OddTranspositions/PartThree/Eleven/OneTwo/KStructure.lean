module

public import CFSG.OddTranspositions.PartThree.Eleven.Statements
public import CFSG.OddTranspositions.PartThree.Eleven.OneOne.Hyp
public import CFSG.OddTranspositions.PartThree.Eleven.Minus.Pair
public import CFSG.OddTranspositions.PartThree.Eleven.Minus.Quandle
public import CFSG.OddTranspositions.PartThree.EightFive.KBarSetup
public import Certificates.Certificate2326
public import CFSG.OddTranspositions.PartThree.Eleven.OneTwo.KBar
public import CFSG.OddTranspositions.PartThree.Eleven.OneTwo.KBarLocal
public import CFSG.OddTranspositions.PartThree.Eleven.OneTwo.Conn
public import CFSG.OddTranspositions.PartThree.Eleven.OneTwo.Wreath
public import CFSG.OddTranspositions.PartThree.Eleven.OneTwo.WreathFactors
public import CFSG.Timmesfeld.Bridge.OddTranspGenL2
public import CFSG.Timmesfeld.Bridge.Asc72ZMain
public import CFSG.OddTranspositions.PartThree.Nine.Setup
public import CFSG.GH74.Generic.BProg.B2.L2Cover
public import CFSG.LieType.Steinberg.CentralExt.PSL2Multiplier
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LinearCentralCover

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.QZ

section KStructure

variable {G : Type} [Group G] [Finite G] {D : Set G}

namespace ElevenTwoFrame

variable {hC : HypothesisC D} {S : Sylow 2 G} {T : Sylow 2 (Halpha D hC.alpha)}
  {r : Fin 3 → Halpha D hC.alpha}

private theorem kbar_rad_eq_bot {hC : HypothesisC D} {r : Fin 3 → Halpha D hC.alpha}
    (N : Subgroup (localGroup D (frameE hC r) ⧸
      CFSG.solvableRadical (localGroup D (frameE hC r))))
    (hN : N.Normal) (hNs : Group.IsSolvable N) : N = ⊥ := by
  have hle : N ≤ CFSG.solvableRadical (localGroup D (frameE hC r) ⧸
      CFSG.solvableRadical (localGroup D (frameE hC r))) :=
    CFSG.SignalizerFunctorTheorem.Nonsolvable.le_solvableRadical hN hNs
  rw [CFSG.SignalizerFunctorTheorem.Nonsolvable.solvableRadical_quotient] at hle
  exact eq_bot_iff.mpr hle

theorem conn_kbar (h91 : Theorem9_1) (h : ElevenTwoHyp hC) (hF : ElevenTwoFrame hC S T r) :
    ¬ Disconnected (centSetBar D (frameE hC r)) := by
  have hu : hC.d ∈ centSet D (frameE hC r) := d_mem_centSet h hF
  refine not_disconnected_of_localTwoA5 h91 (setup_kbar h hF)
    (fun N hN hNs => kbar_rad_eq_bot N hN hNs)
    (not_mul_mem_kbar h hF) (not_dvd_card_kbar h hF)
    (mem_centSetBar_mkCentSet hu) (localTwoA5_kbar h hF hu)

private theorem frameE_mem_commutator {hC : HypothesisC D} {S : Sylow 2 G}
    {T : Sylow 2 (Halpha D hC.alpha)} {r : Fin 3 → Halpha D hC.alpha}
    (h : ElevenTwoHyp hC) (hF : ElevenTwoFrame hC S T r) :
    (⟨frameE hC r, frameE_mem_localGroup h hF⟩ :
        localGroup D (frameE hC r)) ∈ commutator (localGroup D (frameE hC r)) := by
  rw [← Abelianization.ker_of, MonoidHom.mem_ker]
  have hu : hC.d ∈ centSet D (frameE hC r) := d_mem_centSet h hF
  let uK : localGroup D (frameE hC r) := ⟨hC.d, mem_localGroup_of_mem hu⟩
  let rK : Fin 3 → localGroup D (frameE hC r) := fun i =>
    ⟨((r i : Halpha D hC.alpha) : G), mem_localGroup_of_mem (mem_centSet h hF i)⟩
  have hx : ∀ x : localGroup D (frameE hC r), (x : G) ∈ centSet D (frameE hC r) →
      Abelianization.of x = Abelianization.of uK := by
    intro x hx
    obtain ⟨k, hk, hkx⟩ := transitive h hF (x : G) hx
    have hkK : (⟨k, hk⟩ : localGroup D (frameE hC r)) * uK *
        (⟨k, hk⟩ : localGroup D (frameE hC r))⁻¹ = x := by
      apply Subtype.ext
      exact hkx
    calc Abelianization.of x = Abelianization.of
          ((⟨k, hk⟩ : localGroup D (frameE hC r)) * uK *
            (⟨k, hk⟩ : localGroup D (frameE hC r))⁻¹) := by rw [hkK]
      _ = Abelianization.of uK := by simp [map_mul, map_inv]
  have hu2 : Abelianization.of uK * Abelianization.of uK = 1 := by
    rw [← map_mul, show uK * uK = 1 from Subtype.ext (hC.setup.oddT.mul_self_eq_one hu.1),
      map_one]
  have he : (⟨frameE hC r, frameE_mem_localGroup h hF⟩ :
      localGroup D (frameE hC r)) = uK * rK 0 * rK 1 * rK 2 := by
    apply Subtype.ext
    push_cast
    simp only [frameE, frameT, uK, rK, Subgroup.coe_mul]
    group
  rw [he]
  simp only [map_mul]
  rw [hx uK hu, hx (rK 0) (mem_centSet h hF 0), hx (rK 1) (mem_centSet h hF 1),
    hx (rK 2) (mem_centSet h hF 2)]
  simpa [hu2, mul_assoc]

private theorem map_commutator_kbar {hC : HypothesisC D} {S : Sylow 2 G}
    {T : Sylow 2 (Halpha D hC.alpha)} {r : Fin 3 → Halpha D hC.alpha}
    (hF : ElevenTwoFrame hC S T r) :
    (commutator (localGroup D (frameE hC r))).map
        (QuotientGroup.mk' (CFSG.solvableRadical (localGroup D (frameE hC r)))) =
      commutator (localGroup D (frameE hC r) ⧸
        CFSG.solvableRadical (localGroup D (frameE hC r))) :=
  TauCeti.Subgroup.map_commutator_eq_commutator (QuotientGroup.mk'_surjective _)

private theorem map_commutator_commutator_kbar {hC : HypothesisC D} {S : Sylow 2 G}
    {T : Sylow 2 (Halpha D hC.alpha)} {r : Fin 3 → Halpha D hC.alpha}
    (hF : ElevenTwoFrame hC S T r) :
    (⁅commutator (localGroup D (frameE hC r)),
        commutator (localGroup D (frameE hC r))⁆).map
        (QuotientGroup.mk' (CFSG.solvableRadical (localGroup D (frameE hC r)))) =
      ⁅commutator (localGroup D (frameE hC r) ⧸
          CFSG.solvableRadical (localGroup D (frameE hC r))),
        commutator (localGroup D (frameE hC r) ⧸
          CFSG.solvableRadical (localGroup D (frameE hC r)))⁆ := by
  rw [Subgroup.map_commutator, map_commutator_kbar hF]

private theorem sup_commutator_commutator_eq_sup {hC : HypothesisC D} {S : Sylow 2 G}
    {T : Sylow 2 (Halpha D hC.alpha)} {r : Fin 3 → Halpha D hC.alpha}
    (hF : ElevenTwoFrame hC S T r)
    (hperf : Group.IsPerfect (commutator (localGroup D (frameE hC r) ⧸
      CFSG.solvableRadical (localGroup D (frameE hC r))))) :
    ⁅commutator (localGroup D (frameE hC r)),
        commutator (localGroup D (frameE hC r))⁆ ⊔
        CFSG.solvableRadical (localGroup D (frameE hC r)) =
      commutator (localGroup D (frameE hC r)) ⊔
        CFSG.solvableRadical (localGroup D (frameE hC r)) := by
  have hmap : (⁅commutator (localGroup D (frameE hC r)),
        commutator (localGroup D (frameE hC r))⁆).map
        (QuotientGroup.mk' (CFSG.solvableRadical (localGroup D (frameE hC r)))) =
      (commutator (localGroup D (frameE hC r))).map
        (QuotientGroup.mk' (CFSG.solvableRadical (localGroup D (frameE hC r)))) := by
    rw [map_commutator_commutator_kbar hF, map_commutator_kbar hF]
    exact Subgroup.isPerfect_iff.mp hperf
  have hker : (QuotientGroup.mk'
      (CFSG.solvableRadical (localGroup D (frameE hC r)))).ker =
      CFSG.solvableRadical (localGroup D (frameE hC r)) := QuotientGroup.ker_mk' _
  rw [← hker]
  exact (Subgroup.map_eq_map_iff (f := QuotientGroup.mk'
    (CFSG.solvableRadical (localGroup D (frameE hC r))))).mp hmap

private theorem solvableRadical_le_commutator {hC : HypothesisC D} {S : Sylow 2 G}
    {T : Sylow 2 (Halpha D hC.alpha)} {r : Fin 3 → Halpha D hC.alpha}
    (h : ElevenTwoHyp hC) (hF : ElevenTwoFrame hC S T r) :
    CFSG.solvableRadical (localGroup D (frameE hC r)) ≤
      commutator (localGroup D (frameE hC r)) := by
  rw [← Subgroup.map_subtype_le_map_subtype (G' := localGroup D (frameE hC r))]
  rw [solvableRadical_localGroup h hF]
  exact Subgroup.zpowers_le.mpr
    (Subgroup.mem_map_of_mem (localGroup D (frameE hC r)).subtype
      (frameE_mem_commutator h hF))

private theorem index_commutator_eq_two {hC : HypothesisC D} {S : Sylow 2 G}
    {T : Sylow 2 (Halpha D hC.alpha)} {r : Fin 3 → Halpha D hC.alpha}
    (h : ElevenTwoHyp hC) (hF : ElevenTwoFrame hC S T r)
    (hidx : (commutator (localGroup D (frameE hC r) ⧸
      CFSG.solvableRadical (localGroup D (frameE hC r)))).index = 2) :
    (commutator (localGroup D (frameE hC r))).index = 2 := by
  have hker : (QuotientGroup.mk'
      (CFSG.solvableRadical (localGroup D (frameE hC r)))).ker ≤
      commutator (localGroup D (frameE hC r)) := by
    rw [QuotientGroup.ker_mk']
    exact solvableRadical_le_commutator h hF
  have hmap := Subgroup.index_map_eq (H := commutator (localGroup D (frameE hC r)))
      (f := QuotientGroup.mk'
        (CFSG.solvableRadical (localGroup D (frameE hC r))))
      (QuotientGroup.mk'_surjective _) hker
  rw [map_commutator_kbar hF] at hmap
  rw [← hmap]
  exact hidx

private theorem solvableRadical_card {hC : HypothesisC D} {S : Sylow 2 G}
    {T : Sylow 2 (Halpha D hC.alpha)} {r : Fin 3 → Halpha D hC.alpha}
    (h : ElevenTwoHyp hC) (hF : ElevenTwoFrame hC S T r) :
    Nat.card (CFSG.solvableRadical (localGroup D (frameE hC r))) = 2 := by
  rw [← Subgroup.card_map_of_injective
    (K := CFSG.solvableRadical (localGroup D (frameE hC r)))
    (localGroup D (frameE hC r)).subtype_injective]
  rw [solvableRadical_localGroup h hF, Nat.card_zpowers, orderOf_frameE h hF]

private theorem solvableRadical_le_double_commutator_of_disjoint {hC : HypothesisC D}
    {S : Sylow 2 G} {T : Sylow 2 (Halpha D hC.alpha)} {r : Fin 3 → Halpha D hC.alpha}
    (h : ElevenTwoHyp hC) (hF : ElevenTwoFrame hC S T r)
    (hidx : (commutator (localGroup D (frameE hC r) ⧸
      CFSG.solvableRadical (localGroup D (frameE hC r)))).index = 2)
    (hperf : Group.IsPerfect (commutator (localGroup D (frameE hC r) ⧸
      CFSG.solvableRadical (localGroup D (frameE hC r)))))
    (hD : CFSG.solvableRadical (localGroup D (frameE hC r)) ⊓
      ⁅commutator (localGroup D (frameE hC r)),
        commutator (localGroup D (frameE hC r))⁆ = ⊥) :
    CFSG.solvableRadical (localGroup D (frameE hC r)) ≤
      ⁅commutator (localGroup D (frameE hC r)),
        commutator (localGroup D (frameE hC r))⁆ := by
  have hKK : ⁅commutator (localGroup D (frameE hC r)),
        commutator (localGroup D (frameE hC r))⁆ ⊔
        CFSG.solvableRadical (localGroup D (frameE hC r)) =
      commutator (localGroup D (frameE hC r)) := by
    rw [sup_commutator_commutator_eq_sup hF hperf]
    exact sup_eq_left.mpr (solvableRadical_le_commutator h hF)
  have hD' : ⁅commutator (localGroup D (frameE hC r)),
        commutator (localGroup D (frameE hC r))⁆ ⊓
        CFSG.solvableRadical (localGroup D (frameE hC r)) = ⊥ := by
    rwa [inf_comm] at hD
  have hrel : (⁅commutator (localGroup D (frameE hC r)),
        commutator (localGroup D (frameE hC r))⁆).relIndex
        (commutator (localGroup D (frameE hC r))) = 2 := by
    rw [congrArg (fun X => (⁅commutator (localGroup D (frameE hC r)),
        commutator (localGroup D (frameE hC r))⁆).relIndex X) hKK.symm]
    rw [sup_comm, Subgroup.relIndex_sup_right]
    change ((⁅commutator (localGroup D (frameE hC r)),
      commutator (localGroup D (frameE hC r))⁆ : Subgroup (localGroup D (frameE hC r))).subgroupOf
        (CFSG.solvableRadical (localGroup D (frameE hC r)))).index = 2
    rw [show (⁅commutator (localGroup D (frameE hC r)),
          commutator (localGroup D (frameE hC r))⁆).subgroupOf
          (CFSG.solvableRadical (localGroup D (frameE hC r))) = ⊥ from
      (Subgroup.subgroupOf_eq_bot).mpr (disjoint_iff.mpr hD')]
    rw [Subgroup.index_bot, solvableRadical_card h hF]
  have hKdoubleindex : (⁅commutator (localGroup D (frameE hC r)),
        commutator (localGroup D (frameE hC r))⁆).index = 4 := by
    have hle : ⁅commutator (localGroup D (frameE hC r)),
        commutator (localGroup D (frameE hC r))⁆ ≤
        commutator (localGroup D (frameE hC r)) :=
      Subgroup.commutator_le_left _ _
    rw [← Subgroup.relIndex_mul_index hle, hrel, index_commutator_eq_two h hF hidx]
  have hcard : Nat.card (localGroup D (frameE hC r) ⧸
      ⁅commutator (localGroup D (frameE hC r)),
        commutator (localGroup D (frameE hC r))⁆) = 4 := by
    rw [← Subgroup.index_eq_card]
    exact hKdoubleindex
  have hcomm : IsMulCommutative (localGroup D (frameE hC r) ⧸
      ⁅commutator (localGroup D (frameE hC r)),
        commutator (localGroup D (frameE hC r))⁆) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by rw [hcard]; norm_num)
  have hcommbot : commutator (localGroup D (frameE hC r) ⧸
      ⁅commutator (localGroup D (frameE hC r)),
        commutator (localGroup D (frameE hC r))⁆) = ⊥ :=
    (commutator_eq_bot_iff _).mpr hcomm
  have hmap : (commutator (localGroup D (frameE hC r))).map
        (QuotientGroup.mk' (⁅commutator (localGroup D (frameE hC r)),
          commutator (localGroup D (frameE hC r))⁆)) = ⊥ := by
    rw [TauCeti.Subgroup.map_commutator_eq_commutator (QuotientGroup.mk'_surjective _),
      hcommbot]
  have hK'le : commutator (localGroup D (frameE hC r)) ≤
      ⁅commutator (localGroup D (frameE hC r)),
        commutator (localGroup D (frameE hC r))⁆ := by
    have hh := (Subgroup.map_eq_bot_iff (H := commutator (localGroup D (frameE hC r)))
      (f := QuotientGroup.mk' (⁅commutator (localGroup D (frameE hC r)),
        commutator (localGroup D (frameE hC r))⁆))).mp hmap
    rwa [QuotientGroup.ker_mk'] at hh
  exact (solvableRadical_le_commutator h hF).trans hK'le

private theorem le_center_of_card_eq_two {A : Type*} [Group A] [Finite A] (N : Subgroup A)
    [N.Normal] (hN : Nat.card N = 2) : N ≤ Subgroup.center A := by
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro g
  by_cases hx1 : x = 1
  · subst hx1; simp
  have hzp : Nat.card (Subgroup.zpowers x) = 2 := by
    have hdvd : Nat.card (Subgroup.zpowers x) ∣ Nat.card N :=
      Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hx)
    rw [hN] at hdvd
    have hgt : 1 < Nat.card (Subgroup.zpowers x) := by
      rw [Subgroup.one_lt_card_iff_ne_bot]
      intro hbot
      exact hx1 (Subgroup.mem_bot.mp (hbot ▸ Subgroup.mem_zpowers x))
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · omega
    · exact h
  have heq : Subgroup.zpowers x = N :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hx) (by rw [hzp, hN])
  have hord : orderOf x = 2 := by rw [← Nat.card_zpowers]; exact hzp
  have hconj : g * x * g⁻¹ ∈ Subgroup.zpowers x :=
    heq ▸ (inferInstance : N.Normal).conj_mem x hx g
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hconj
  have hk2 : g * x * g⁻¹ = x ^ (k % (2 : ℤ)) := by
    rw [← hk, ← zpow_mod_orderOf x k, hord]
    norm_num
  have hneq : g * x * g⁻¹ ≠ 1 := by
    intro h
    apply hx1
    have h' := congrArg (fun z => g⁻¹ * z * g) h
    group at h'
    exact h'
  have hconj' : g * x * g⁻¹ = x := by
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · rw [hk2, h, zpow_zero] at hneq
      exact absurd rfl hneq
    · rw [hk2, h, zpow_one]
  have h2 := congrArg (fun z => z * g) hconj'
  simpa [mul_assoc] using h2

private theorem solvableRadical_le_double_commutator {hC : HypothesisC D} {S : Sylow 2 G}
    {T : Sylow 2 (Halpha D hC.alpha)} {r : Fin 3 → Halpha D hC.alpha}
    (h : ElevenTwoHyp hC) (hF : ElevenTwoFrame hC S T r)
    (hidx : (commutator (localGroup D (frameE hC r) ⧸
      CFSG.solvableRadical (localGroup D (frameE hC r)))).index = 2)
    (hperf : Group.IsPerfect (commutator (localGroup D (frameE hC r) ⧸
      CFSG.solvableRadical (localGroup D (frameE hC r))))) :
    CFSG.solvableRadical (localGroup D (frameE hC r)) ≤
      ⁅commutator (localGroup D (frameE hC r)),
        commutator (localGroup D (frameE hC r))⁆ := by
  by_cases hD : CFSG.solvableRadical (localGroup D (frameE hC r)) ⊓
      ⁅commutator (localGroup D (frameE hC r)),
        commutator (localGroup D (frameE hC r))⁆ = ⊥
  · exact solvableRadical_le_double_commutator_of_disjoint h hF hidx hperf hD
  · have hcard : Nat.card (↥(CFSG.solvableRadical (localGroup D (frameE hC r)) ⊓
        ⁅commutator (localGroup D (frameE hC r)),
          commutator (localGroup D (frameE hC r))⁆)) = 2 := by
      have hdvd : Nat.card (↥(CFSG.solvableRadical (localGroup D (frameE hC r)) ⊓
          ⁅commutator (localGroup D (frameE hC r)),
            commutator (localGroup D (frameE hC r))⁆)) ∣
          Nat.card (CFSG.solvableRadical (localGroup D (frameE hC r))) :=
        Subgroup.card_dvd_of_le inf_le_left
      rw [solvableRadical_card h hF] at hdvd
      rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
      · exact absurd (Subgroup.eq_bot_of_card_eq _ h1) hD
      · exact h2
    have heq : CFSG.solvableRadical (localGroup D (frameE hC r)) ⊓
        ⁅commutator (localGroup D (frameE hC r)),
          commutator (localGroup D (frameE hC r))⁆ =
        CFSG.solvableRadical (localGroup D (frameE hC r)) :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcard, solvableRadical_card h hF])
    exact inf_eq_left.mp heq

theorem not_psl2Model_kbar (h : ElevenTwoHyp hC) (hF : ElevenTwoFrame hC S T r) {f : ℕ}
    (hf : 2 ≤ f) :
    ¬ (Nonempty (↥(commutator (localGroup D (frameE hC r) ⧸
          CFSG.solvableRadical (localGroup D (frameE hC r)))) ≃*
        CFSG.Theory.Comparator.PSL2Model (2 * f)) ∧
      (commutator (localGroup D (frameE hC r) ⧸
        CFSG.solvableRadical (localGroup D (frameE hC r)))).index = 2) := by
  rintro ⟨⟨eL⟩, hidx⟩
  haveI hperfL : Group.IsPerfect (CFSG.Theory.Comparator.PSL2Model (2 * f)) := by
    have hcard : 3 < Nat.card (GaloisField 2 (2 * f)) := by
      rw [GaloisField.card 2 (2 * f) (by omega)]
      calc 3 < 16 := by norm_num
        _ = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact CFSG.GorensteinWalter.psl2_isPerfect_of_card_gt_three
      (GaloisField 2 (2 * f)) hcard
  have hperfbar : Group.IsPerfect (↥(commutator (localGroup D (frameE hC r) ⧸
      CFSG.solvableRadical (localGroup D (frameE hC r))))) :=
    Group.IsPerfect.ofSurjective (f := eL.symm.toMonoidHom) eL.symm.surjective
  have hRle : CFSG.solvableRadical (localGroup D (frameE hC r)) ≤
      ⁅commutator (localGroup D (frameE hC r)),
        commutator (localGroup D (frameE hC r))⁆ :=
    solvableRadical_le_double_commutator h hF hidx hperfbar
  have hK'double : ⁅commutator (localGroup D (frameE hC r)),
        commutator (localGroup D (frameE hC r))⁆ =
      commutator (localGroup D (frameE hC r)) := by
    have hsup := sup_commutator_commutator_eq_sup hF hperfbar
    rwa [sup_eq_left.mpr hRle,
      sup_eq_left.mpr (solvableRadical_le_commutator h hF)] at hsup
  have hperfK' : Group.IsPerfect ↥(commutator (localGroup D (frameE hC r))) := by
    rw [Subgroup.isPerfect_iff]
    exact hK'double
  let q : ↥(commutator (localGroup D (frameE hC r))) →*
      ↥(commutator (localGroup D (frameE hC r) ⧸
        CFSG.solvableRadical (localGroup D (frameE hC r)))) :=
    MonoidHom.codRestrict
      ((QuotientGroup.mk' (CFSG.solvableRadical (localGroup D (frameE hC r)))).comp
        (commutator (localGroup D (frameE hC r))).subtype)
      (commutator (localGroup D (frameE hC r) ⧸
        CFSG.solvableRadical (localGroup D (frameE hC r))))
      (fun x => by
        change QuotientGroup.mk' (CFSG.solvableRadical (localGroup D (frameE hC r)))
          ((x : localGroup D (frameE hC r))) ∈ _
        rw [← map_commutator_kbar hF]
        exact Subgroup.mem_map_of_mem _ x.2)
  have hq_surj : Function.Surjective q := by
    intro y
    have hy : (y : localGroup D (frameE hC r) ⧸
        CFSG.solvableRadical (localGroup D (frameE hC r))) ∈
        Subgroup.map (QuotientGroup.mk'
          (CFSG.solvableRadical (localGroup D (frameE hC r))))
          (commutator (localGroup D (frameE hC r))) := by
      rw [map_commutator_kbar hF]
      exact y.2
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hq_ker : q.ker = (CFSG.solvableRadical (localGroup D (frameE hC r))).subgroupOf
      (commutator (localGroup D (frameE hC r))) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      rw [← QuotientGroup.ker_mk'
        (CFSG.solvableRadical (localGroup D (frameE hC r)))]
      exact MonoidHom.mem_ker.mpr (congrArg Subtype.val hx)
    · intro hx
      apply Subtype.ext
      rw [← QuotientGroup.ker_mk'
        (CFSG.solvableRadical (localGroup D (frameE hC r)))] at hx
      exact MonoidHom.mem_ker.mp hx
  have hRleK' : CFSG.solvableRadical (localGroup D (frameE hC r)) ≤
      commutator (localGroup D (frameE hC r)) :=
    solvableRadical_le_commutator h hF
  have hcardker : Nat.card ↥(q.ker) = 2 := by
    rw [hq_ker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRleK').toEquiv]
    exact solvableRadical_card h hF
  have hcentral : q.ker ≤ Subgroup.center ↥(commutator (localGroup D (frameE hC r))) := by
    rw [hq_ker]
    exact le_center_of_card_eq_two _ (by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRleK').toEquiv]
      exact solvableRadical_card h hF)
  have hpker : IsPGroup 2 ↥(q.ker) :=
    IsPGroup.of_card (n := 1) (by rw [hcardker, pow_one])
  let η : ↥(commutator (localGroup D (frameE hC r))) →*
      Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 (2 * f)) :=
    (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := GaloisField 2 (2 * f))).toMonoidHom.comp
      (eL.toMonoidHom.comp q)
  have hη_surj : Function.Surjective η :=
    (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := GaloisField 2 (2 * f))).surjective.comp
      (eL.surjective.comp hq_surj)
  have hη_ker : η.ker = q.ker := by
    have h1 := MonoidHom.ker_comp_of_injective (eL.toMonoidHom.comp q)
      (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := GaloisField 2 (2 * f))).toMonoidHom
      (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := GaloisField 2 (2 * f))).injective
    have h2 := MonoidHom.ker_comp_of_injective q eL.toMonoidHom eL.injective
    rw [h1, h2]
  have hbot : η.ker = ⊥ :=
    CFSG.ShultStronglyClosedTI.large_even_linear_central_two_cover_kernel_eq_bot
      (2 * f) (by omega) (GaloisField.card 2 (2 * f) (by omega)) η hη_surj
      (hη_ker.symm ▸ hcentral) (hη_ker.symm ▸ hpker)
  have h2 : Nat.card ↥(η.ker) = 2 := by rw [hη_ker]; exact hcardker
  rw [hbot, Subgroup.card_bot] at h2
  omega

theorem nonempty_kbar_mulEquiv (h91 : Theorem9_1) (h : ElevenTwoHyp hC)
    (hF : ElevenTwoFrame hC S T r) :
    Nonempty ((localGroup D (frameE hC r) ⧸ CFSG.solvableRadical (localGroup D (frameE hC r)))
      ≃* L2Wreath 2 2) := by
  let K := localGroup D (frameE hC r)
  let R := CFSG.solvableRadical K
  let Kbar := K ⧸ R
  let Λ := centSetBar D (frameE hC r)
  let d := mkCentSet D (frameE hC r) hC.d (d_mem_centSet h hF)
  have hu : hC.d ∈ centSet D (frameE hC r) := d_mem_centSet h hF
  have hS : Setup Kbar Λ := setup_kbar h hF
  have hconn : ¬ Disconnected Λ := conn_kbar h91 h hF
  have hL : LocalTwoA5 Λ d := localTwoA5_kbar h hF hu
  obtain ⟨hC₁, hd₁, halpha₁, hrad₁, hbender₁⟩ :=
    exists_hypC_of_localTwoA5 hS hconn (mem_centSetBar_mkCentSet hu) hL
  obtain ⟨f, hf, hPSL, hdisj⟩ :=
    h91 Kbar Λ hC₁ (fun N hN hNs => kbar_rad_eq_bot N hN hNs) hrad₁ hbender₁
  have hαd : hC₁.alpha = {hC₁.d} := by rw [halpha₁, hd₁]
  have hHalpha : Halpha Λ hC₁.alpha = Subgroup.closure (commSet Λ d) := by
    rw [Halpha, Nine.DalphaStar_eq_commSet hC₁ hαd, hd₁]
  have hf2 : f = 2 := by
    obtain ⟨eH⟩ := hPSL
    obtain ⟨e2⟩ := hL.bender
    rw [← hHalpha] at e2
    have hcard : Nat.card (CFSG.Theory.Comparator.PSL2Model f) = 60 := by
      rw [Nat.card_congr (eH.symm.trans e2).toEquiv]
      rw [CFSG.Timmesfeld.Bridge.OddTransp.card_psl2Model (by norm_num)]
      norm_num
    rw [CFSG.Timmesfeld.Bridge.OddTransp.card_psl2Model (by omega)] at hcard
    by_contra hne
    have h3 : 3 ≤ f := by omega
    have h2f : 8 ≤ 2 ^ f := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h3
    have h63 : 63 ≤ (2 ^ f) ^ 2 - 1 := by
      have h64 : 64 ≤ (2 ^ f) ^ 2 := by
        calc 64 = 8 ^ 2 := by norm_num
          _ ≤ (2 ^ f) ^ 2 := Nat.pow_le_pow_left h2f 2
      omega
    have hbound : 8 * 63 ≤ 2 ^ f * ((2 ^ f) ^ 2 - 1) := Nat.mul_le_mul h2f h63
    omega
  subst hf2
  rcases hdisj with he | ⟨e, hidx⟩
  · exact he
  · exact (not_psl2Model_kbar h hF (by norm_num) ⟨e, hidx⟩).elim

theorem card_localGroup (h91 : Theorem9_1) (h : ElevenTwoHyp hC)
    (hF : ElevenTwoFrame hC S T r) : Nat.card (localGroup D (frameE hC r)) = 14400 := by
  obtain ⟨φ⟩ := nonempty_kbar_mulEquiv h91 h hF
  have hcardKbar : Nat.card (localGroup D (frameE hC r) ⧸
      CFSG.solvableRadical (localGroup D (frameE hC r))) = 7200 := by
    rw [Nat.card_congr φ.toEquiv, card_l2Wreath_two_two]
  have hcardR : Nat.card (CFSG.solvableRadical (localGroup D (frameE hC r))) = 2 := by
    rw [← Subgroup.card_map_of_injective
      (K := CFSG.solvableRadical (localGroup D (frameE hC r)))
      (localGroup D (frameE hC r)).subtype_injective]
    rw [solvableRadical_localGroup h hF, Nat.card_zpowers, orderOf_frameE h hF]
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
    (CFSG.solvableRadical (localGroup D (frameE hC r))), hcardKbar, hcardR]

theorem card_centralizer_kbar (h91 : Theorem9_1) (h : ElevenTwoHyp hC)
    (hF : ElevenTwoFrame hC S T r) (hu : hC.d ∈ centSet D (frameE hC r)) :
    Nat.card (Subgroup.centralizer {mkCentSet D (frameE hC r) hC.d hu}) = 120 := by
  obtain ⟨φ⟩ := nonempty_kbar_mulEquiv h91 h hF
  exact card_centralizer_l2Wreath_two φ (setup_kbar h hF) (mem_centSetBar_mkCentSet hu)

end ElevenTwoFrame

end KStructure

end CFSG.OddTranspositions.PartThree
