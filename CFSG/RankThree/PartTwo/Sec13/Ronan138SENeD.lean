module

public import CFSG.RankThree.PartTwo.Sec13.Ronan138SBase
import CFSG.RankThree.PartTwo.Sec13.Naturality
import CFSG.RankThree.PartTwo.Sec13.Item137ProofOrbit
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec13.Item13SetupAt
import CFSG.RankThree.PartTwo.Sec13.Item13Theta
import CFSG.RankThree.PartTwo.Sec14.Item143StepsProofBalTools

public section

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_mem_lA_of_not_mem {E K : Subgroup G} {e : G} (hK : K ∈ lA E e)
    {b : G} (hbE : b ∈ E) (hbK : b ∈ K) (hbe : b ∉ Subgroup.zpowers e)
    {x : G} (hxE : x ∈ Subgroup.normalizer (E : Set G))
    (hxe : x ∈ Subgroup.normalizer (Subgroup.zpowers e : Set G)) :
    x ∈ Subgroup.normalizer (K : Set G) := by
  by_contra hxK
  set K' := K.map (MulAut.conj x).toMonoidHom with hK'
  have hzx : Subgroup.zpowers (x * e * x⁻¹) = Subgroup.zpowers e := by
    have h := Subgroup.mem_normalizer_iff_map_conj_eq.mp hxe
    rw [MonoidHom.map_zpowers] at h
    exact h
  have hK'1 : K' ∈ thetaComponentsIn (Subgroup.centralizer ({e} : Set G)) := by
    have h := ((map_conj_mem_lA_iff (c := e) (L := K) hxE).mpr hK).1
    rw [thetaComponentsAt_eq_thetaComponentsIn, centralizer_singleton_eq_of_zpowers_eq hzx] at h
    exact h
  have hK1 : K ∈ thetaComponentsIn (Subgroup.centralizer ({e} : Set G)) := hK.1
  have hne : K' ≠ K := fun h => hxK (map_conj_eq_iff_mem_normalizer.mp h)
  have hK'C : K' ≤ Sec4.thetaQuotCentralizer K :=
    Sec14.BalTools.le_thetaQuotCentralizer_of_ne_in hK'1 hK1 hne
  have hCE := sectionCentralizer_eq_inf hK.2.1
  rw [hK.2.2.1] at hCE
  have hb' : x * b * x⁻¹ ∈ ((E ⊓ Sec4.thetaQuotCentralizer K : Subgroup G) : Set G) :=
    Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hxE b).mp hbE,
      hK'C (Subgroup.mem_map.mpr ⟨b, hbK, rfl⟩)⟩
  rw [← hCE] at hb'
  apply hbe
  have := (Subgroup.mem_normalizer_iff.mp (inv_mem hxe) _).mp (show x * b * x⁻¹ ∈
    Subgroup.zpowers e from hb')
  rwa [show x⁻¹ * (x * b * x⁻¹) * x⁻¹⁻¹ = b by group] at this

theorem normalizer_of_mem_lA_d {A L E F : Subgroup G} {c x y t : G}
    (hfr : Frame138Base A L E F c x y t) {K : Subgroup G} (hK : K ∈ lA E ⁅x, y⁆)
    (hEK : ¬ E ⊓ K ≤ Subgroup.zpowers ⁅x, y⁆) :
    F ≤ Subgroup.normalizer (K : Set G) ∧ t ∈ Subgroup.normalizer (K : Set G) := by
  obtain ⟨b, hbEK, hbd⟩ := SetLike.not_le_iff_exists.mp hEK
  obtain ⟨hbE, hbK⟩ := Subgroup.mem_inf.mp hbEK
  refine ⟨fun f hf => mem_normalizer_of_mem_lA_of_not_mem hK hbE hbK hbd (hfr.hFN hf) ?_,
    mem_normalizer_of_mem_lA_of_not_mem hK hbE hbK hbd hfr.htE ?_⟩
  · have hfd : ⁅x, y⁆ * f = f * ⁅x, y⁆ := hfr.hFab _ (Subgroup.mem_inf.mp hfr.hdZ).2 f hf
    exact centralizer_le_normalizer_zpowers _ (Subgroup.mem_centralizer_singleton_iff.mpr hfd.symm)
  · rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    change Subgroup.zpowers (t * ⁅x, y⁆ * t⁻¹) = _
    rw [hfr.htd, Subgroup.zpowers_inv]

theorem inf_eq_zpowers_of_not_mem {A L E F : Subgroup G} {c x y t : G}
    (hfr : Frame138Base A L E F c x y t) {K : Subgroup G} (hK : K ∈ lA E ⁅x, y⁆)
    (hEK : E ⊓ K ≠ ⊥) (hdK : ⁅x, y⁆ ∉ K) : E ⊓ K = Subgroup.zpowers c := by
  set d := ⁅x, y⁆ with hd
  have hd3 : d ^ 3 = 1 := hfr.hd3
  have hdK' : Subgroup.zpowers d ⊓ K = ⊥ := zpowers_inf_eq_bot hd3 hdK
  have hEKd : ¬ E ⊓ K ≤ Subgroup.zpowers d := by
    intro hle
    apply hEK
    rw [eq_bot_iff, ← hdK']
    exact le_inf hle inf_le_right
  obtain ⟨hFK, htK⟩ := normalizer_of_mem_lA_d hfr hK hEKd
  have htc : t * c * t⁻¹ = c := by rw [hfr.htc, mul_inv_cancel_right]
  have hle : E ⊓ K ≤ Subgroup.zpowers c := by
    intro k hk
    obtain ⟨hkE, hkK⟩ := Subgroup.mem_inf.mp hk
    have hkF : k ∈ F := by
      by_contra hkF
      obtain ⟨m, hm, hym⟩ := conj_y_eq_of_not_mem hfr.frame hfr.hxE hfr.hyF hfr.hE27 hfr.hF27
        hfr.h9 hfr.hFN hfr.hEab hkE hkF
      have hyk : y * k * y⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hFK hfr.hyF) k).mp hkK
      have hdm : d ^ m ∈ K := by
        have := K.mul_mem (K.inv_mem hkK) hyk
        rwa [hym, inv_mul_cancel_left] at this
      exact hdK (Subgroup.zpowers_le.mpr hdm (mem_zpowers_pow_of_not_dvd hd3 hm))
    obtain ⟨α, β, rfl⟩ := hfr.hZgen _ (Subgroup.mem_inf.mpr ⟨hkE, hkF⟩)
    have htk : t * (c ^ α * d ^ β) * t⁻¹ = c ^ α * d⁻¹ ^ β := by
      rw [show t * (c ^ α * d ^ β) * t⁻¹ = (t * c * t⁻¹) ^ α * (t * d * t⁻¹) ^ β by
        rw [conj_pow, conj_pow]; group, htc, hfr.htd]
    have hu : d ^ β * d ^ β ∈ K := by
      have h1 : t * (c ^ α * d ^ β) * t⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp htK _).mp hkK
      have h2 := K.mul_mem (K.inv_mem h1) hkK
      rwa [htk, show (c ^ α * d⁻¹ ^ β)⁻¹ * (c ^ α * d ^ β) = d ^ β * d ^ β by
        rw [inv_pow, mul_inv_rev, inv_inv]; group] at h2
    have hu1 : d ^ β * d ^ β = 1 := by
      have : d ^ β * d ^ β ∈ Subgroup.zpowers d ⊓ K :=
        Subgroup.mem_inf.mpr ⟨mul_mem (pow_mem (Subgroup.mem_zpowers d) β)
          (pow_mem (Subgroup.mem_zpowers d) β), hu⟩
      rwa [hdK', Subgroup.mem_bot] at this
    have hβ : d ^ β = 1 := by
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have h3 : orderOf d ∣ β + β := orderOf_dvd_of_pow_eq_one (by rw [pow_add]; exact hu1)
      rw [orderOf_eq_prime hd3 hfr.hd1] at h3
      have h3' : 3 ∣ β := by omega
      obtain ⟨j, rfl⟩ := h3'
      rw [pow_mul, hd3, one_pow]
    rw [hβ, mul_one]
    exact pow_mem (Subgroup.mem_zpowers c) α
  obtain ⟨⟨b, hb⟩, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hEK
  have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hbc := zpowers_eq_of_mem (hfr.hE3 b (Subgroup.mem_inf.mp hb).1) hb1' hfr.hc3 hfr.hc1
    (hle hb)
  refine le_antisymm hle ?_
  rw [← hbc]
  exact Subgroup.zpowers_le.mpr hb

end CFSG.RankThree.PartTwo.Sec13.Ronan138S
