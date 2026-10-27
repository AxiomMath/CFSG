module

public import CFSG.OddTranspositions.PartThree.Eleven.Statements
public import CFSG.OddTranspositions.PartThree.Eleven.OneOne.Hyp
public import CFSG.OddTranspositions.PartThree.Eleven.Minus.Pair
public import CFSG.OddTranspositions.PartThree.Eleven.Minus.Quandle
public import CFSG.OddTranspositions.PartThree.EightFive.KBarSetup
public import Certificates.Certificate2326
public import CFSG.OddTranspositions.PartThree.Eleven.OneTwo.KOddCore
import CFSG.OddTranspositions.PartThree.Nine.Setup
import CFSG.OddTranspositions.PartThree.CardWidth

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.QZ

section KBar

variable {G : Type} [Group G] [Finite G] {D : Set G}

namespace ElevenTwoFrame

variable {hC : HypothesisC D} {S : Sylow 2 G} {T : Sylow 2 (Halpha D hC.alpha)}
  {r : Fin 3 → Halpha D hC.alpha}

private theorem setup_localSet (h : ElevenTwoHyp hC) (hF : ElevenTwoFrame hC S T r) :
    Setup (localGroup D (frameE hC r)) (localSet D (frameE hC r)) := by
  classical
  let e := frameE hC r
  let K : Subgroup G := localGroup D e
  have hd₀ := hF.d_mem_centSet h
  have hd₀H : hC.d ∈ K := mem_localGroup_of_mem hd₀
  refine ⟨⟨⟨hC.d, hd₀H⟩, ?_⟩, ?_, ?_⟩
  · ext g
    constructor
    · intro hg
      obtain ⟨k, hk, hkg⟩ := transitive h hF (g : G) hg
      exact isConj_iff.mpr ⟨⟨k, hk⟩, Subtype.ext hkg⟩
    · intro hg
      obtain ⟨k, hk⟩ := isConj_iff.mp hg
      have hkg : (k : G) * hC.d * (k : G)⁻¹ = (g : G) := congrArg Subtype.val hk
      refine ⟨?_, ?_⟩
      · rw [← hkg]
        exact hC.setup.normal (k : G) hC.d hd₀.1
      · rw [← hkg]
        exact ((commute_of_mem_localGroup k.2).mul_left hd₀.2).mul_left
          (commute_of_mem_localGroup k.2).inv_left
  · exact (hC.setup.oddT.preimage K).mono (fun x hx => hx.1)
  · exact Subgroup.closure_closure_coe_preimage

theorem setup_kbar (h : ElevenTwoHyp hC) (hF : ElevenTwoFrame hC S T r) :
    Setup (localGroup D (frameE hC r) ⧸ CFSG.solvableRadical (localGroup D (frameE hC r)))
      (centSetBar D (frameE hC r)) := by
  classical
  let e := frameE hC r
  let K : Subgroup G := localGroup D e
  let R : Subgroup K := CFSG.solvableRadical K
  have hSetupK : Setup K (localSet D e) := setup_localSet h hF
  have hne : ∀ d ∈ localSet D e, QuotientGroup.mk' R d ≠ 1 := by
    intro d hd hd1
    have hdR : d ∈ R := (QuotientGroup.eq_one_iff d).mp hd1
    have hmem : ((d : K) : G) ∈ Subgroup.zpowers e := by
      rw [← solvableRadical_localGroup h hF]
      exact ⟨d, hdR, rfl⟩
    have hdD : ((d : K) : G) ∈ D := hd.1
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have he2 : e ^ 2 = 1 := by
      rw [← hF.orderOf_frameE h]
      exact pow_orderOf_eq_one _
    have hmod : e ^ n = e ^ (n % 2) := zpow_eq_zpow_emod' n he2
    rw [hn] at hmod
    rcases Int.emod_two_eq_zero_or_one n with h0 | h1mod
    · have hd1' : ((d : K) : G) = 1 := by simpa [h0] using hmod
      exact hC.setup.oddT.ne_one hdD hd1'
    · have hde : ((d : K) : G) = e := by simpa [h1mod] using hmod
      rw [hde] at hdD
      exact hF.frameE_not_mem h hdD
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨d₀, hd₀⟩ := hSetupK.isClass
    simpa only [centSetBar, K, R, e] using image_isClass_quotient hd₀ R
  · simpa only [centSetBar, K, R, e] using image_isOddTransp_quotient R hSetupK.oddT hne
  · simpa only [centSetBar, K, R, e] using image_closure_eq_top_quotient R hSetupK.gen

theorem injOn_kbar (h : ElevenTwoHyp hC) (hF : ElevenTwoFrame hC S T r) :
    Set.InjOn (QuotientGroup.mk' (CFSG.solvableRadical (localGroup D (frameE hC r))))
      (localSet D (frameE hC r)) := by
  intro x hx y hy hxy
  let e := frameE hC r
  let K : Subgroup G := localGroup D e
  let R : Subgroup K := CFSG.solvableRadical K
  have hxyR : x * y⁻¹ ∈ R := by
    have h2 : QuotientGroup.mk' R (x * y⁻¹) = 1 := by
      rw [map_mul, map_inv, hxy, mul_inv_cancel]
    exact (QuotientGroup.eq_one_iff (x * y⁻¹)).mp h2
  have hxy_zpow : ((x * y⁻¹ : K) : G) ∈ Subgroup.zpowers e := by
    rw [← solvableRadical_localGroup h hF]
    exact ⟨x * y⁻¹, hxyR, rfl⟩
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hxy_zpow
  have he2 : e ^ 2 = 1 := by
    rw [← hF.orderOf_frameE h]
    exact pow_orderOf_eq_one _
  have hmod : e ^ n = e ^ (n % 2) := zpow_eq_zpow_emod' n he2
  rw [hn] at hmod
  rcases Int.emod_two_eq_zero_or_one n with h0 | h1mod
  · have hxy1 : ((x * y⁻¹ : K) : G) = 1 := by simpa [h0] using hmod
    have hxy1' : x * y⁻¹ = 1 := Subtype.ext hxy1
    exact mul_inv_eq_one.mp hxy1'
  · exfalso
    have hxye : ((x * y⁻¹ : K) : G) = e := by simpa [h1mod] using hmod
    have hyD : (y : G) ∈ D := hy.1
    have hyinv : (y : G)⁻¹ = (y : G) := hC.setup.oddT.inv_eq hyD
    have h1 : (x : G) * (y : G) = e := by simpa [hyinv] using hxye
    have hxG : (x : G) = e * (y : G) := by
      calc (x : G) = (x : G) * (y : G) * (y : G)⁻¹ := by group
        _ = e * (y : G)⁻¹ := by rw [h1]
        _ = e * (y : G) := by rw [hyinv]
    have hcomm : Commute e (y : G) := hy.2.symm
    have hxG' : (x : G) = (y : G) * e := by
      rw [hxG]
      exact hcomm.eq
    exact hF.mul_frameE_not_mem h (y : G) hy (hxG' ▸ hx.1)

private theorem commute_d_of_mul_sq (h : ElevenTwoHyp hC) (hF : ElevenTwoFrame hC S T r)
    {b₀ : G} (hb₀ : b₀ ∈ centSet D (frameE hC r)) (hb₀_ne_u : b₀ ≠ hC.d)
    (hbb : hC.d * b₀ * hC.d * b₀ = 1 ∨
      hC.d * b₀ * hC.d * b₀ = frameE hC r) :
    Commute hC.d b₀ := by
  have hu2 : hC.d * hC.d = 1 := hC.setup.oddT.mul_self_eq_one hC.hd
  have hb2 : b₀ * b₀ = 1 := hC.setup.oddT.mul_self_eq_one hb₀.1
  rcases hbb with h1 | he
  · exact (commute_iff_mul_sq_eq_one hu2 hb2).mpr
      (by simpa only [pow_two, mul_assoc] using h1)
  · exfalso
    have h2 : (hC.d * b₀) ^ 2 = frameE hC r := by
      simpa only [pow_two, mul_assoc] using he
    have h4 : (hC.d * b₀) ^ 4 = 1 := by
      calc (hC.d * b₀) ^ 4 = (hC.d * b₀) ^ (2 * 2) := by norm_num
        _ = ((hC.d * b₀) ^ 2) ^ 2 := by rw [pow_mul]
        _ = (frameE hC r) ^ 2 := by rw [h2]
        _ = 1 := by rw [← hF.orderOf_frameE h]; exact pow_orderOf_eq_one _
    have hnot : ¬ (hC.d * b₀) ^ 2 = 1 := by
      rw [pow_two]
      intro hh
      have hh' : hC.d * b₀ * hC.d * b₀ = 1 := by
        simpa only [mul_assoc] using hh
      have he1 : frameE hC r = 1 := he.symm.trans hh'
      have h2' := hF.orderOf_frameE h
      rw [he1, orderOf_one] at h2'
      exact absurd h2' (by norm_num)
    have hord4 : orderOf (hC.d * b₀) = 4 := by
      have hnot' : ¬ (hC.d * b₀) ^ 2 ^ 1 = 1 := by simpa using hnot
      have hfin : (hC.d * b₀) ^ 2 ^ (1 + 1) = 1 := by simpa using h4
      simpa using orderOf_eq_prime_pow (p := 2) (n := 1) hnot' hfin
    have hodd := hC.setup.oddT.2 hC.d hC.hd b₀ hb₀.1
    rw [hord4] at hodd
    rcases hodd with h | h
    · omega
    · exact absurd h (by norm_num)

private theorem false_of_d_mul (h : ElevenTwoHyp hC) (hF : ElevenTwoFrame hC S T r)
    {b₀ c₀ : G}
    (hb₀ : b₀ ∈ centSet D (frameE hC r))
    (hc₀ : c₀ ∈ centSet D (frameE hC r))
    (hb₀_ne_u : b₀ ≠ hC.d)
    (hb₀_ne_ue : b₀ ≠ hC.d * frameE hC r)
    (hbb : hC.d * b₀ * hC.d * b₀ = 1 ∨
      hC.d * b₀ * hC.d * b₀ = frameE hC r)
    (hmul : hC.d * b₀ = c₀ ∨ hC.d * b₀ = c₀ * frameE hC r) :
    False := by
  have hcomm : Commute hC.d b₀ := commute_d_of_mul_sq h hF hb₀ hb₀_ne_u hbb
  have hb₀_in_Du : b₀ ∈ commSet D hC.d := ⟨hb₀.1, hcomm.symm, hb₀_ne_u⟩
  rcases hmul with hmul | hmul
  ·
    have hc₀_ne_u : c₀ ≠ hC.d := by
      intro hc₀u
      have hb_eq_one : b₀ = 1 := by
        have : hC.d * b₀ = hC.d * 1 := by rw [hmul, hc₀u, mul_one]
        exact mul_left_cancel this
      exact hC.setup.oddT.ne_one hb₀.1 hb_eq_one
    have hc₀_comm_u : Commute c₀ hC.d := by
      rw [← hmul]
      exact (Commute.refl hC.d).mul_left hcomm.symm
    have hc₀_in_Du : c₀ ∈ commSet D hC.d := ⟨hc₀.1, hc₀_comm_u, hc₀_ne_u⟩
    have hu_eq : hC.d = c₀ * b₀ := by
      calc hC.d = (hC.d * b₀) * b₀ := by
            rw [mul_assoc, hC.setup.oddT.mul_self_eq_one hb₀.1, mul_one]
        _ = c₀ * b₀ := by rw [hmul]
    have hc₀_Dα : c₀ ∈ DalphaStar D hC.alpha := by
      rw [Nine.DalphaStar_eq_commSet hC h.alpha_eq]
      exact hc₀_in_Du
    have hb₀_Dα : b₀ ∈ DalphaStar D hC.alpha := by
      rw [Nine.DalphaStar_eq_commSet hC h.alpha_eq]
      exact hb₀_in_Du
    have hu_mem_H : hC.d ∈ Halpha D hC.alpha := by
      rw [Halpha, hu_eq]
      exact Subgroup.mul_mem _
        (Subgroup.subset_closure hc₀_Dα) (Subgroup.subset_closure hb₀_Dα)
    let uH : Halpha D hC.alpha := ⟨hC.d, hu_mem_H⟩
    have huH_center : Subgroup.zpowers uH ≤ Subgroup.center (Halpha D hC.alpha) := by
      rw [Subgroup.zpowers_le, Subgroup.mem_center_iff]
      intro g
      have hg : (g : G) ∈ Subgroup.centralizer ({hC.d} : Set G) :=
        Halpha_le_centralizer_d hC g.2
      have hgu : Commute (g : G) hC.d :=
        Subgroup.mem_centralizer_singleton_iff.mp hg
      exact Subtype.ext hgu.eq
    haveI : (Subgroup.zpowers uH).Normal := Subgroup.normal_of_le_center huH_center
    have hsolv : Group.IsSolvable (Subgroup.zpowers uH) := inferInstance
    have hle : Subgroup.zpowers uH ≤ CFSG.solvableRadical (Halpha D hC.alpha) :=
      CFSG.Timmesfeld.Bridge.OddTransp.le_solvableRadical inferInstance hsolv
    rw [h.radical_eq_bot] at hle
    have hu_one : uH = 1 := by
      have : uH ∈ (⊥ : Subgroup (Halpha D hC.alpha)) :=
        hle (Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩)
      simpa using this
    have hu_eq_one : hC.d = 1 := congrArg Subtype.val hu_one
    have hord := hC.setup.oddT.1 hC.d hC.hd
    rw [hu_eq_one, orderOf_one] at hord
    exact absurd hord (by norm_num)
  ·
    have hc₀_ne_u : c₀ ≠ hC.d := by
      intro hc₀u
      have hb_eq_e : b₀ = frameE hC r := by
        have : hC.d * b₀ = hC.d * frameE hC r := by rw [hmul, hc₀u]
        exact mul_left_cancel this
      exact hF.frameE_not_mem h (hb_eq_e ▸ hb₀.1)
    have ht_comm_u : Commute (frameT hC r) hC.d := by
      rw [frameT]
      exact (((mem_commSet h hF 0).2.1.mul_left (mem_commSet h hF 1).2.1).mul_left
        (mem_commSet h hF 2).2.1)
    have hb₀_comm_t : Commute b₀ (frameT hC r) := by
      have h1 : Commute b₀ (hC.d * frameT hC r) := by
        rw [← frameE]
        exact hb₀.2
      have h2 : Commute b₀ hC.d := hcomm.symm
      have h4 : frameT hC r = hC.d⁻¹ * (hC.d * frameT hC r) := by group
      rw [h4]
      exact h2.inv_right.mul_right h1
    have he2 : frameE hC r * frameE hC r = 1 := by
      rw [← pow_two, ← hF.orderOf_frameE h]
      exact pow_orderOf_eq_one _
    have he_inv : (frameE hC r)⁻¹ = frameE hC r :=
      inv_eq_of_mul_eq_one_right he2
    have hc₀_eq : c₀ = b₀ * frameT hC r := by
      calc c₀ = c₀ * frameE hC r * (frameE hC r)⁻¹ := by group
        _ = hC.d * b₀ * (frameE hC r)⁻¹ := by rw [← hmul]
        _ = hC.d * b₀ * frameE hC r := by rw [he_inv]
        _ = hC.d * b₀ * (hC.d * frameT hC r) := by rw [frameE]
        _ = b₀ * frameT hC r := by
              rw [hcomm.eq]
              rw [show b₀ * hC.d * (hC.d * frameT hC r) =
                b₀ * (hC.d * hC.d) * frameT hC r by group]
              rw [hC.setup.oddT.mul_self_eq_one hC.hd, mul_one]
    have ht_eq : frameT hC r = b₀ * c₀ := by
      rw [hc₀_eq]
      rw [← mul_assoc, hC.setup.oddT.mul_self_eq_one hb₀.1, one_mul]
    have hc₀_comm_t : Commute c₀ (frameT hC r) := by
      rw [hc₀_eq]
      exact hb₀_comm_t.mul_left (Commute.refl (frameT hC r))
    have hc₀_comm_u : Commute c₀ hC.d := by
      rw [hc₀_eq]
      exact hcomm.symm.mul_left ht_comm_u
    have hb₀_Dα : b₀ ∈ DalphaStar D hC.alpha := by
      rw [Nine.DalphaStar_eq_commSet hC h.alpha_eq]
      exact hb₀_in_Du
    have hc₀_in_Du : c₀ ∈ commSet D hC.d := ⟨hc₀.1, hc₀_comm_u, hc₀_ne_u⟩
    have hc₀_Dα : c₀ ∈ DalphaStar D hC.alpha := by
      rw [Nine.DalphaStar_eq_commSet hC h.alpha_eq]
      exact hc₀_in_Du
    let b₀H : Halpha D hC.alpha := ⟨b₀, by
      rw [Halpha]; exact Subgroup.subset_closure hb₀_Dα⟩
    let c₀H : Halpha D hC.alpha := ⟨c₀, by
      rw [Halpha]; exact Subgroup.subset_closure hc₀_Dα⟩
    have hb₀H_mem : b₀H ∈ DstarH hC := (mem_DstarH_iff hC).mpr hb₀_Dα
    have hc₀H_mem : c₀H ∈ DstarH hC := (mem_DstarH_iff hC).mpr hc₀_Dα
    have hb₀H_comm : Commute b₀H (r 0 * r 1 * r 2) := by
      apply Subtype.ext
      exact hb₀_comm_t.eq
    have hc₀H_comm : Commute c₀H (r 0 * r 1 * r 2) := by
      apply Subtype.ext
      exact hc₀_comm_t.eq
    have hbc : b₀H * c₀H = r 0 * r 1 * r 2 := by
      apply Subtype.ext
      show b₀ * c₀ = ((r 0 * r 1 * r 2 : Halpha D hC.alpha) : G)
      rw [← ht_eq]
      rfl
    exact hF.frame.not_mul b₀H ⟨hb₀H_mem, hb₀H_comm⟩ c₀H
      ⟨hc₀H_mem, hc₀H_comm⟩ hbc

theorem not_mul_mem_kbar (h : ElevenTwoHyp hC) (hF : ElevenTwoFrame hC S T r) :
    ¬ ∃ a ∈ centSetBar D (frameE hC r), ∃ b ∈ centSetBar D (frameE hC r),
      a ≠ b ∧ Commute a b ∧ a * b ∈ centSetBar D (frameE hC r) := by
  rintro ⟨a, ha, b, hb, hne, hcomm, hab⟩
  let e := frameE hC r
  let K : Subgroup G := localGroup D e
  let R : Subgroup K := CFSG.solvableRadical K
  obtain ⟨A, hA, rfl⟩ := ha
  obtain ⟨B, hB, rfl⟩ := hb
  obtain ⟨C, hC', hCeq⟩ := hab
  have hABR : A * B * C⁻¹ ∈ R := by
    have h1 : QuotientGroup.mk' R (A * B * C⁻¹) = 1 := by
      rw [map_mul, map_mul, map_inv, ← hCeq, mul_inv_cancel]
    exact (QuotientGroup.eq_one_iff (A * B * C⁻¹)).mp h1
  have hAB_zpow : ((A * B * C⁻¹ : K) : G) ∈ Subgroup.zpowers e := by
    rw [← solvableRadical_localGroup h hF]
    exact ⟨A * B * C⁻¹, hABR, rfl⟩
  have he2 : e ^ 2 = 1 := by
    rw [← hF.orderOf_frameE h]
    exact pow_orderOf_eq_one _
  have hCinv : (C : G)⁻¹ = (C : G) := hC.setup.oddT.inv_eq hC'.1
  have hCcomm : Commute (C : G) e := hC'.2
  have hC2 : (C : G) * (C : G) = 1 := hC.setup.oddT.mul_self_eq_one hC'.1
  have hABG : (A : G) * (B : G) = (C : G) ∨ (A : G) * (B : G) = (C : G) * e := by
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hAB_zpow
    have hmod : e ^ n = e ^ (n % 2) := zpow_eq_zpow_emod' n he2
    rw [hn] at hmod
    rcases Int.emod_two_eq_zero_or_one n with h0 | h1mod
    · left
      have h1 : ((A * B * C⁻¹ : K) : G) = 1 := by simpa [h0] using hmod
      have h2 : (A : G) * (B : G) * (C : G)⁻¹ = 1 := by
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h1
      exact mul_inv_eq_one.mp h2
    · right
      have h1 : ((A * B * C⁻¹ : K) : G) = e := by simpa [h1mod] using hmod
      have h2 : (A : G) * (B : G) * (C : G)⁻¹ = e := by
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h1
      rw [hCinv] at h2
      calc (A : G) * (B : G) = (A : G) * (B : G) * (C : G) * (C : G) := by
            rw [mul_assoc, hC2, mul_one]
        _ = e * (C : G) := by rw [h2]
        _ = (C : G) * e := hCcomm.eq.symm
  have hbbG : (A : G) * (B : G) * (A : G) * (B : G) = 1 ∨
      (A : G) * (B : G) * (A : G) * (B : G) = e := by
    have hA2K : A * A = 1 := Subtype.ext (hC.setup.oddT.mul_self_eq_one hA.1)
    have hB2K : B * B = 1 := Subtype.ext (hC.setup.oddT.mul_self_eq_one hB.1)
    have hA2 : QuotientGroup.mk' R A * QuotientGroup.mk' R A = 1 := by
      rw [← map_mul, hA2K, map_one]
    have hB2 : QuotientGroup.mk' R B * QuotientGroup.mk' R B = 1 := by
      rw [← map_mul, hB2K, map_one]
    have h1 : QuotientGroup.mk' R (A * B * A * B) = 1 := by
      rw [map_mul, map_mul, map_mul]
      calc QuotientGroup.mk' R A * QuotientGroup.mk' R B *
            QuotientGroup.mk' R A * QuotientGroup.mk' R B
          = QuotientGroup.mk' R A * (QuotientGroup.mk' R B * QuotientGroup.mk' R A) *
            QuotientGroup.mk' R B := by group
        _ = QuotientGroup.mk' R A * (QuotientGroup.mk' R A * QuotientGroup.mk' R B) *
            QuotientGroup.mk' R B := by rw [hcomm.eq]
        _ = (QuotientGroup.mk' R A * QuotientGroup.mk' R A) *
            (QuotientGroup.mk' R B * QuotientGroup.mk' R B) := by group
        _ = 1 := by rw [hA2, hB2, one_mul]
    have hR : A * B * A * B ∈ R := (QuotientGroup.eq_one_iff _).mp h1
    have hzp : ((A * B * A * B : K) : G) ∈ Subgroup.zpowers e := by
      rw [← solvableRadical_localGroup h hF]
      exact ⟨A * B * A * B, hR, rfl⟩
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hzp
    have hmod : e ^ m = e ^ (m % 2) := zpow_eq_zpow_emod' m he2
    rw [hm] at hmod
    rcases Int.emod_two_eq_zero_or_one m with h0 | h1mod
    · left
      have h2 : ((A * B * A * B : K) : G) = 1 := by simpa [h0] using hmod
      simpa only [Subgroup.coe_mul] using h2
    · right
      have h2 : ((A * B * A * B : K) : G) = e := by simpa [h1mod] using hmod
      simpa only [Subgroup.coe_mul] using h2
  obtain ⟨k, hk, hkA⟩ := transitive h hF (A : G) hA
  have hkcommG : Commute k e := commute_of_mem_localGroup hk
  have hkek : k * e = e * k := hkcommG.eq
  have hkek_inv : k⁻¹ * e = e * k⁻¹ := by
    calc k⁻¹ * e = k⁻¹ * e * k * k⁻¹ := by group
      _ = k⁻¹ * (e * k) * k⁻¹ := by group
      _ = k⁻¹ * (k * e) * k⁻¹ := by rw [← hkek]
      _ = e * k⁻¹ := by group
  have hke : k * e * k⁻¹ = e := by rw [hkek]; group
  let kK : K := ⟨k, hk⟩
  let B' : K := kK⁻¹ * B * kK
  let C' : K := kK⁻¹ * C * kK
  have hB'G : (B' : G) = k⁻¹ * (B : G) * k := rfl
  have hC'G : (C' : G) = k⁻¹ * (C : G) * k := rfl
  have hA_eq : (A : G) = (k : G) * hC.d * (k : G)⁻¹ := hkA.symm
  have hB_eq : (B : G) = (k : G) * (B' : G) * (k : G)⁻¹ := by
    rw [hB'G]; group
  have hC_eq : (C : G) = (k : G) * (C' : G) * (k : G)⁻¹ := by
    rw [hC'G]; group
  have hmul' : hC.d * (B' : G) = (C' : G) ∨ hC.d * (B' : G) = (C' : G) * e := by
    rcases hABG with h | h
    · left
      have h' : (k : G) * (hC.d * (B' : G)) * (k : G)⁻¹ =
          (k : G) * (C' : G) * (k : G)⁻¹ := by
        calc (k : G) * (hC.d * (B' : G)) * (k : G)⁻¹
            = (k : G) * hC.d * (k : G)⁻¹ * ((k : G) * (B' : G) * (k : G)⁻¹) := by
              group
          _ = (A : G) * (B : G) := by rw [hA_eq, hB_eq]
          _ = (C : G) := h
          _ = (k : G) * (C' : G) * (k : G)⁻¹ := by rw [hC_eq]
      exact mul_left_cancel (mul_right_cancel h')
    · right
      have h' : (k : G) * (hC.d * (B' : G)) * (k : G)⁻¹ =
          (k : G) * ((C' : G) * e) * (k : G)⁻¹ := by
        calc (k : G) * (hC.d * (B' : G)) * (k : G)⁻¹
            = (A : G) * (B : G) := by rw [hA_eq, hB_eq]; group
          _ = (C : G) * e := h
          _ = (k : G) * (C' : G) * (k : G)⁻¹ * e := by rw [hC_eq]
          _ = (k : G) * (C' : G) * ((k : G)⁻¹ * e) := by rw [mul_assoc]
          _ = (k : G) * (C' : G) * (e * (k : G)⁻¹) := by rw [hkek_inv]
          _ = (k : G) * ((C' : G) * e) * (k : G)⁻¹ := by group
      exact mul_left_cancel (mul_right_cancel h')
  have hbb' : hC.d * (B' : G) * hC.d * (B' : G) = 1 ∨
      hC.d * (B' : G) * hC.d * (B' : G) = e := by
    rcases hbbG with h | h
    · left
      have h' : (k : G) * (hC.d * (B' : G) * hC.d * (B' : G)) * (k : G)⁻¹ =
          (k : G) * 1 * (k : G)⁻¹ := by
        rw [mul_one, mul_inv_cancel]
        calc (k : G) * (hC.d * (B' : G) * hC.d * (B' : G)) * (k : G)⁻¹
            = (A : G) * (B : G) * (A : G) * (B : G) := by rw [hA_eq, hB_eq]; group
          _ = 1 := h
      exact mul_left_cancel (mul_right_cancel h')
    · right
      have h' : (k : G) * (hC.d * (B' : G) * hC.d * (B' : G)) * (k : G)⁻¹ =
          (k : G) * e * (k : G)⁻¹ := by
        rw [hke]
        calc (k : G) * (hC.d * (B' : G) * hC.d * (B' : G)) * (k : G)⁻¹
            = (A : G) * (B : G) * (A : G) * (B : G) := by rw [hA_eq, hB_eq]; group
          _ = e := h
      exact mul_left_cancel (mul_right_cancel h')
  have huK : hC.d ∈ K := mem_localGroup_of_mem (hF.d_mem_centSet h)
  have heK : e ∈ K := frameE_mem_localGroup h hF
  have hB'_D : (B' : G) ∈ D := by
    rw [hB'G]
    simpa only [inv_inv] using hC.setup.normal (k : G)⁻¹ (B : G) hB.1
  have hB'_comm_e : Commute (B' : G) e := by
    rw [hB'G]
    exact (hkcommG.inv_left.mul_left hB.2).mul_left hkcommG
  have hC'_D : (C' : G) ∈ D := by
    rw [hC'G]
    simpa only [inv_inv] using hC.setup.normal (k : G)⁻¹ (C : G) hC'.1
  have hC'_comm_e : Commute (C' : G) e := by
    rw [hC'G]
    exact (hkcommG.inv_left.mul_left hC'.2).mul_left hkcommG
  have hB'_ne_u : (B' : G) ≠ hC.d := by
    intro hB'u
    apply hne
    have hB'_eq : B' = (⟨hC.d, huK⟩ : K) := Subtype.ext hB'u
    have hBA : B = A := by
      have h1 : B = kK * B' * kK⁻¹ := by rw [show B' = kK⁻¹ * B * kK from rfl]; group
      rw [h1, hB'_eq]
      apply Subtype.ext
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hkA
    rw [hBA]
  have hB'_ne_ue : (B' : G) ≠ hC.d * e := by
    intro hB'ue
    apply hne
    have hB'_eq : B' = (⟨hC.d, huK⟩ : K) * ⟨e, heK⟩ := Subtype.ext hB'ue
    have hBAe : B = A * ⟨e, heK⟩ := by
      have h1 : B = kK * B' * kK⁻¹ := by rw [show B' = kK⁻¹ * B * kK from rfl]; group
      rw [h1, hB'_eq]
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      calc (k : G) * (hC.d * e) * (k : G)⁻¹
          = (k : G) * hC.d * (k : G)⁻¹ * ((k : G) * e * (k : G)⁻¹) := by group
        _ = (A : G) * e := by rw [hA_eq, hke]
    rw [hBAe, map_mul]
    have heK1 : QuotientGroup.mk' R ⟨e, heK⟩ = 1 := by
      change ((⟨e, heK⟩ : K) : K ⧸ R) = 1
      rw [QuotientGroup.eq_one_iff]
      have hmem : ((⟨e, heK⟩ : K) : G) ∈ (solvableRadical K).map K.subtype := by
        rw [solvableRadical_localGroup h hF]
        exact Subgroup.mem_zpowers_iff.mpr ⟨1, by rw [zpow_one]⟩
      obtain ⟨r, hr, hre⟩ := Subgroup.mem_map.mp hmem
      have hreq : r = ⟨e, heK⟩ := Subtype.ext hre
      rwa [hreq] at hr
    rw [heK1, mul_one]
  exact false_of_d_mul h hF ⟨hB'_D, hB'_comm_e⟩ ⟨hC'_D, hC'_comm_e⟩
    hB'_ne_u hB'_ne_ue hbb' hmul'

private theorem exists_sylow_localSet (h : ElevenTwoHyp hC) (hF : ElevenTwoFrame hC S T r) :
    ∃ P : Sylow 2 (localGroup D (frameE hC r)),
      ((P : Set (localGroup D (frameE hC r))) ∩ localSet D (frameE hC r)).ncard = 4 := by
  classical
  let e := frameE hC r
  let K : Subgroup G := localGroup D e
  let Δ : Set G := (S : Set G) ∩ D
  have hΔ_centSet : Δ ⊆ centSet D e := by
    intro δ hδ
    have hδ' : δ ∈ (S : Set G) ∩ D := hδ
    rw [hF.inter_eq] at hδ'
    rcases hδ' with rfl | ⟨i, rfl⟩
    · exact hF.d_mem_centSet h
    · exact hF.mem_centSet h i
  have hΔ_K : Δ ⊆ K := fun δ hδ => mem_localGroup_of_mem (hΔ_centSet hδ)
  let L : Subgroup G := Subgroup.closure Δ
  have hL_le_S : L ≤ (S : Subgroup G) :=
    (Subgroup.closure_le (S : Subgroup G)).mpr (fun x hx => hx.1)
  have hL_p : IsPGroup 2 L := (S : Sylow 2 G).isPGroup'.to_le hL_le_S
  let P₀ : Subgroup K := L.comap K.subtype
  have hP₀_p : IsPGroup 2 P₀ := hL_p.comap_subtype (K := K)
  obtain ⟨P, hP₀_le_P⟩ := hP₀_p.exists_le_sylow
  have hP_p : IsPGroup 2 ((P : Subgroup K).map K.subtype) := (P.isPGroup').map K.subtype
  obtain ⟨S', hS'_le⟩ := hP_p.exists_le_sylow
  let E : Set K := (P : Set K) ∩ localSet D e
  have hΔ_image : Δ ⊆ (Subgroup.subtype K) '' E := by
    intro δ hδ
    refine ⟨⟨δ, hΔ_K hδ⟩, ⟨?_, ?_⟩, rfl⟩
    · exact hP₀_le_P (Subgroup.mem_comap.mpr (Subgroup.subset_closure hδ))
    · exact hΔ_centSet hδ
  have hE_image_le : (Subgroup.subtype K) '' E ⊆ (S' : Set G) ∩ D := by
    rintro y ⟨x, hx, rfl⟩
    exact ⟨hS'_le (Subgroup.mem_map.mpr ⟨x, hx.1, rfl⟩), hx.2.1⟩
  have hE_ncard : E.ncard = 4 := by
    have himg : ((Subgroup.subtype K) '' E).ncard = E.ncard :=
      Set.ncard_image_of_injective E (Subgroup.subtype_injective K)
    have h4a : Δ.ncard = 4 := hF.ncard_inter h
    have h4b : ((S' : Set G) ∩ D).ncard = 4 := hF.ncard_inter_sylow h S'
    have hle1 : Δ.ncard ≤ ((Subgroup.subtype K) '' E).ncard := Set.ncard_le_ncard hΔ_image
    have hle2 : ((Subgroup.subtype K) '' E).ncard ≤ ((S' : Set G) ∩ D).ncard :=
      Set.ncard_le_ncard hE_image_le
    omega
  exact ⟨P, by simpa only [K, e, E] using hE_ncard⟩

theorem not_dvd_card_kbar (h : ElevenTwoHyp hC) (hF : ElevenTwoFrame hC S T r) :
    ¬ 128 ∣ Nat.card
      (localGroup D (frameE hC r) ⧸ CFSG.solvableRadical (localGroup D (frameE hC r))) := by
  classical
  let e := frameE hC r
  let K : Subgroup G := localGroup D e
  let R : Subgroup K := CFSG.solvableRadical K
  have hSetupK : Setup K (localSet D e) := setup_localSet h hF
  obtain ⟨P, hP4⟩ := exists_sylow_localSet h hF
  have hP4' : ((P : Set K) ∩ localSet D e).ncard = 4 := by simpa [K, e] using hP4
  have hright : Nat.card ↥((P : Set K) ∩ localSet D e) = 4 := by
    rw [Nat.card_coe_set_eq]
    exact hP4'
  have hΓval : padicValNat 2 (Nat.card ↥(localSet D e)) = 2 := by
    have hle := padicValNat_two_card_eq_width hSetupK.isClass hSetupK.oddT P
    have h2 : padicValNat 2 (4 : ℕ) = 2 := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, padicValNat.prime_pow]
    rw [hright, h2] at hle
    exact hle
  haveI hnorm : CFSG.GroupTheory.NormalizesSet (⊤ : Subgroup K) (localSet D e) :=
    ⟨fun a _ x hx => hSetupK.normal a x hx⟩
  have hpre : MulAction.IsPretransitive K ↥(localSet D e) := by
    refine ⟨fun x y => ?_⟩
    obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_of_isClass hSetupK.isClass x.2 y.2)
    exact ⟨c, by
      apply Subtype.ext
      change (c : K) * (x : K) * (c : K)⁻¹ = (y : K)
      exact hc⟩
  let uK : K := ⟨hC.d, mem_localGroup_of_mem (hF.d_mem_centSet h)⟩
  have huΓ : uK ∈ localSet D e := by simpa [localSet, uK, e] using hF.d_mem_centSet h
  let xu : ↥(localSet D e) := ⟨uK, huΓ⟩
  have hcardK : Nat.card K =
      Nat.card (Subgroup.centralizer ({uK} : Set K)) * Nat.card ↥(localSet D e) :=
    (card_centralizer_mul_card_of_pretransitive hpre xu).symm
  let CKu : Subgroup K := Subgroup.centralizer ({uK} : Set K)
  let CKuG : Subgroup G :=
    Subgroup.centralizer ({hC.d} : Set G) ⊓ Subgroup.centralizer ({e} : Set G)
  have hCKu_dvd : Nat.card CKu ∣ Nat.card CKuG := by
    let f : ↥CKu →* ↥CKuG :=
      { toFun := fun x => ⟨(x.1 : G), by
          refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
          · rw [Subgroup.mem_centralizer_singleton_iff]
            have hx := (Subgroup.mem_centralizer_singleton_iff.mp x.2 : x.1 * uK = uK * x.1)
            simpa [uK] using congrArg (fun z : K => (z : G)) hx
          · rw [Subgroup.mem_centralizer_singleton_iff]
            exact (commute_of_mem_localGroup x.1.2).eq⟩
        map_one' := by ext; rfl
        map_mul' := by intro x y; ext; rfl }
    exact Subgroup.card_dvd_of_injective f (by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : ↥CKuG => (z : G)) hxy)
  have h480 : Nat.card CKuG = 480 := by simpa [CKuG, e] using hF.card_centralizer_d_inf h
  have hCKu_val : padicValNat 2 (Nat.card CKu) ≤ 5 := by
    have hpow : 2 ^ padicValNat 2 (Nat.card CKu) ∣ 480 := by
      rw [← h480]
      exact (pow_padicValNat_dvd).trans hCKu_dvd
    have hle := (padicValNat_dvd_iff_le (show (480 : ℕ) ≠ 0 by norm_num)).mp hpow
    have h480val : padicValNat 2 (480 : ℕ) = 5 := by
      rw [show (480 : ℕ) = 2 ^ 5 * 15 by norm_num,
        padicValNat.mul (pow_ne_zero _ (by norm_num)) (by norm_num),
        padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 15),
        add_zero]
    omega
  have hKval : padicValNat 2 (Nat.card K) ≤ 7 := by
    have hC0 : Nat.card CKu ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨1, CKu.one_mem⟩, inferInstance⟩
    have hΓ0 : Nat.card ↥(localSet D e) ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨xu⟩, inferInstance⟩
    rw [hcardK, padicValNat.mul hC0 hΓ0, hΓval]
    omega
  have hRcard : Nat.card R = 2 := by
    have hmap : Nat.card (R.map K.subtype) = Nat.card R :=
      Subgroup.card_map_of_injective K.subtype_injective
    have hh : Nat.card (R.map K.subtype) = Nat.card (Subgroup.zpowers (frameE hC r)) :=
      congrArg (fun s : Subgroup G => Nat.card s) (solvableRadical_localGroup h hF)
    rw [hmap, Nat.card_zpowers, hF.orderOf_frameE h] at hh
    exact hh
  intro hdvd
  have hK_eq : Nat.card K = Nat.card (K ⧸ R) * Nat.card R :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup R
  have h256 : 2 ^ 8 ∣ Nat.card K := by
    rw [hK_eq, hRcard]
    have hdvd' : 2 ^ 7 ∣ Nat.card (K ⧸ R) := by
      have h128 : (128 : ℕ) = 2 ^ 7 := by norm_num
      rwa [h128] at hdvd
    have hmul := mul_dvd_mul_right hdvd' 2
    have hpow : (2 : ℕ) ^ 8 = 2 ^ 7 * 2 := by norm_num
    rwa [hpow]
  have hK0 : Nat.card K ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨1, K.one_mem⟩, inferInstance⟩
  have h8 : 8 ≤ padicValNat 2 (Nat.card K) := (padicValNat_dvd_iff_le hK0).mp h256
  omega

end ElevenTwoFrame

end KBar

end CFSG.OddTranspositions.PartThree
