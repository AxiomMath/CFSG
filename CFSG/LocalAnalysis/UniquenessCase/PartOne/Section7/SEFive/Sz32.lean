module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.CoverLift
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SzFiveTrans
import CFSG.RankThree.PartOne.S12.Sec1511SPEFStar
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.SPEBasics
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive

open CFSG.LieType.Ree

theorem exists_elemAbelian_two_of_isoLie_sz32
    {L : Type} [Group L] [Finite L]
    (hL : CFSG.RankThree.PartOne.Census3.IsoLie L (.suzuki 2)) :
    ∃ E : Subgroup L, (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ (∀ a ∈ E, a ^ 2 = 1) ∧
      Nat.card E = 32 := by
  obtain ⟨-, a, ha, K, hKfield, hKfin, hfa, hKcard, ⟨e⟩⟩ :=
    CFSG.RankThree.PartOne.CTP.suzukiModel_of_isoLie 2 hL
  letI : Field K := hKfield
  letI : Finite K := hKfin
  obtain rfl : a = 2 := by omega
  obtain ⟨hZab, hZexp⟩ :=
    CFSG.ShultStronglyClosedTI.SuzukiModel.isElemAbelian_suzukiZ0 (a := 2) (K := K) hKcard
  refine ⟨(suzukiZ0 2 K).map e.symm.toMonoidHom, ?_, ?_, ?_⟩
  · intro x hx y hy
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
    rw [← map_mul, ← map_mul]
    exact congrArg e.symm (congrArg Subtype.val (hZab.is_comm.comm ⟨x', hx'⟩ ⟨y', hy'⟩))
  · intro x hx
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
    rw [← map_pow]
    simpa using congrArg e.symm (hZexp x' hx')
  · rw [Subgroup.card_map_of_injective e.symm.injective,
      CFSG.ShultStronglyClosedTI.SuzukiModel.card_suzukiZ0 (a := 2) (K := K) hKcard]
    norm_num


theorem coverActsTriviallyOnSmall_sz32 {p : ℕ} {L : Type}
    [Group L] [Finite L] [IsSimpleGroup L]
    (hL : CFSG.RankThree.PartOne.Census3.IsoLie L (.suzuki 2)) :
    CoverActsTriviallyOnSmall p L := by
  obtain ⟨E, hcomm, hexp, hcard⟩ := exists_elemAbelian_two_of_isoLie_sz32 hL
  exact coverActsTriviallyOnSmall_of_elemAbelian hcomm hexp (by rw [hcard])

theorem good_sz32
    {X : Type} [Group X] [Finite X]
    (hO : CFSG.pPrimeCore 5 X = ⊥)
    (h2 : 2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup X)) {N : Subgroup X}
    (hN : CFSG.RankThree.PartOne.IsStronglyPEmbedded 5 N)
    (hL : CFSG.RankThree.PartOne.Census3.IsoLie ↥(CFSG.generalizedFitting X) (.suzuki 2)) :
    Good 5 N := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set K : Subgroup X := CFSG.generalizedFitting X with hKdef
  obtain ⟨hKs, hKnab, hKn, hKC⟩ :=
    CFSG.RankThree.PartOne.Sec1511.spe_fstar (p := 5) (by norm_num) hO hN
  haveI : K.Normal := hKn
  haveI : IsSimpleGroup ↥K := hKs
  obtain ⟨hv, ⟨e⟩⟩ := hL
  have hSz := CFSG.AGLEmbeddingD2.sz32Normal_of_mulEquiv ⟨.suzuki 2, hv⟩ rfl hKn hKC e
  obtain ⟨P, hP, hPN⟩ := hN.exists_isSylowOf_le
  let R : Sylow 5 X := hP.2.1.toSylow (by simpa [Subgroup.relIndex_top_right] using hP.2.2)
  have hRcoe : (R : Subgroup X) = P :=
    IsPGroup.toSylow_coe hP.2.1 (by simpa [Subgroup.relIndex_top_right] using hP.2.2)
  have hRN : (R : Subgroup X) ≤ N := hRcoe ▸ hPN
  have hRrank : 2 ≤ CFSG.Open.pRank 5 (R : Subgroup X) := by
    rw [(CFSG.SectionRank.pRank_sylow R).1]
    exact h2
  obtain ⟨E, hER, hEea, hEcard⟩ :=
    CFSG.SectionRank.exists_pRank (p := 5) (by norm_num) (R : Subgroup X)
  have h25dvd : 5 ^ 2 ∣ Nat.card ↥E := by
    rw [hEcard]
    exact pow_dvd_pow 5 hRrank
  obtain ⟨C, hCcard⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥E) 5 (n := 2) h25dvd
  let A : Subgroup X := C.map E.subtype
  have hAE : A ≤ E := Subgroup.map_subtype_le C
  have hAea : CFSG.Open.IsElemAbelian 5 A := hEea.mono hAE
  have hAcard : Nat.card A = 5 ^ 2 := by
    rw [Subgroup.card_map_of_injective E.subtype_injective, hCcard]
  have hAR : A ≤ (R : Subgroup X) := hAE.trans hER
  have hAdvdR : Nat.card A ∣ Nat.card (R : Subgroup X) := Subgroup.card_dvd_of_le hAR
  obtain ⟨z, hzA, hzord, hzK, hzZ, hmax, hmaxW, hCZ, hsol, hb, hb5, ht, hcyc⟩ :=
    hSz.transLocal R A hAR hAea hAcard
  let M : Subgroup X := Subgroup.normalizer ((R : Subgroup X) : Set X)
  have hMleN : M ≤ N := by
    intro g hg
    by_contra hgN
    have hgmap : (R : Subgroup X).map (MulAut.conj g).toMonoidHom = R :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
    have hle : (R : Subgroup X) ≤ N ⊓ N.map (MulAut.conj g).toMonoidHom := by
      refine le_inf hRN ?_
      rw [← hgmap]
      exact Subgroup.map_mono hRN
    have hAcard5 : 5 ∣ Nat.card A := by rw [hAcard]; norm_num
    exact hN.2.2 g hgN ((hAcard5.trans hAdvdR).trans (Subgroup.card_dvd_of_le hle))
  have hNM : N = M := by
    rcases hmax N hMleN with h | h
    · exact h
    · exact absurd h hN.1
  have hNnorm : N ≤ Subgroup.normalizer ((R : Subgroup X) : Set X) := hNM.le
  have hzRC : z ∈ (R : Subgroup X) ⊓
      Subgroup.centralizer ((R : Subgroup X) : Set X) := by
    rw [← hzZ]
    exact Subgroup.mem_zpowers z
  have hzR : z ∈ (R : Subgroup X) := hzRC.1
  have hCXR : Subgroup.centralizer ((R : Subgroup X) : Set X) ≤ R := by
    intro x hx
    refine hCZ ⟨Subgroup.centralizer_le_normalizer _ hx, ?_⟩
    change x ∈ Subgroup.centralizer ({z} : Set X)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((Subgroup.mem_centralizer_iff.mp hx) z hzR).symm
  constructor
  · exact pPrimeCore_eq_bot_of_centralizer_le hRN R.isPGroup' hNnorm hCXR
  ·
    intro x y hxN hyN hx1 hxp hyprime hy2 hyp hxy
    exfalso
    have hyM : y ∈ M := hNM ▸ hyN
    have hRmap : (R : Subgroup X).map (MulAut.conj y).toMonoidHom = R :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hyM
    have hyinv : y⁻¹ ∈ M := Subgroup.inv_mem _ hyM
    have hCmap_le : (Subgroup.centralizer ((R : Subgroup X) : Set X)).map
        (MulAut.conj y).toMonoidHom ≤
        Subgroup.centralizer ((R : Subgroup X) : Set X) := by
      rintro w ⟨c, hc, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      have hr' : y⁻¹ * r * y ∈ (R : Subgroup X) := by
        simpa using (Subgroup.mem_normalizer_iff.mp hyinv r).mp hr
      have hc' := (Subgroup.mem_centralizer_iff.mp hc) (y⁻¹ * r * y) hr'
      show r * (y * (c : X) * y⁻¹) = y * (c : X) * y⁻¹ * r
      calc r * (y * (c : X) * y⁻¹) = y * ((y⁻¹ * r * y) * (c : X)) * y⁻¹ := by group
        _ = y * ((c : X) * (y⁻¹ * r * y)) * y⁻¹ := by rw [hc']
        _ = y * (c : X) * y⁻¹ * r := by group
    have hCmap : (Subgroup.centralizer ((R : Subgroup X) : Set X)).map
        (MulAut.conj y).toMonoidHom =
        Subgroup.centralizer ((R : Subgroup X) : Set X) :=
      Subgroup.eq_of_le_of_card_ge hCmap_le (by
        rw [Subgroup.card_map_of_injective (MulAut.conj y).injective])
    have hZmap : (Subgroup.zpowers z).map (MulAut.conj y).toMonoidHom =
        Subgroup.zpowers z := by
      rw [hzZ, Subgroup.map_inf _ _ _ (MulAut.conj y).injective, hRmap, hCmap]
    have hyNormZ : y ∈ Subgroup.normalizer (Subgroup.zpowers z) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr hZmap
    let β : MulAut ↥(Subgroup.zpowers z) :=
      (Subgroup.zpowers z).normalizerMonoidHom ⟨y, hyNormZ⟩
    have hβapp : ∀ w : ↥(Subgroup.zpowers z),
        ((β w : ↥(Subgroup.zpowers z)) : X) = y * w * y⁻¹ := fun w => rfl
    have hZcard : Nat.card ↥(Subgroup.zpowers z) = 5 := by
      rw [Nat.card_zpowers, hzord]
    have hAutcard : Nat.card (MulAut ↥(Subgroup.zpowers z)) = 4 := by
      rw [IsCyclic.card_mulAut, hZcard]
      rfl
    have horder_coe :
        orderOf (⟨y, hyNormZ⟩ :
          ↥(Subgroup.normalizer (Subgroup.zpowers z))) = orderOf y :=
      (Subgroup.orderOf_coe _).symm
    have hβdvd_r : orderOf β ∣ orderOf y := by
      have h := orderOf_map_dvd (Subgroup.zpowers z).normalizerMonoidHom ⟨y, hyNormZ⟩
      simpa [β, horder_coe] using h
    have hβdvd_4 : orderOf β ∣ 4 := by
      have h := orderOf_dvd_natCard β
      rwa [hAutcard] at h
    have hcop4 : Nat.Coprime (orderOf y) 4 := by
      have hodd := hyprime.odd_of_ne_two hy2
      simpa using hodd.coprime_two_right.pow_right 2
    have hβ1 : β = 1 := by
      have hdvd : orderOf β ∣ Nat.gcd (orderOf y) 4 := Nat.dvd_gcd hβdvd_r hβdvd_4
      rw [Nat.coprime_iff_gcd_eq_one.mp hcop4] at hdvd
      exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd)
    have hyz : y * z = z * y := by
      have h := hβapp ⟨z, Subgroup.mem_zpowers z⟩
      rw [hβ1, MulAut.one_apply] at h
      rw [show ((⟨z, Subgroup.mem_zpowers z⟩ : Subgroup.zpowers z) : X) = z from rfl] at h
      calc y * z = (y * z * y⁻¹) * y := by group
        _ = z * y := by rw [← h]
    have hyC : y ∈ Subgroup.centralizer ({z} : Set X) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hyz
    have hyR : y ∈ (R : Subgroup X) := hCZ ⟨hyM, hyC⟩
    have h5order : 5 ∣ orderOf y := by
      obtain ⟨n, hn⟩ :=
        (IsPGroup.iff_orderOf (p := 5) (G := ↥(R : Subgroup X))).mp R.isPGroup'
          ⟨y, hyR⟩
      have hyord : orderOf y = 5 ^ n := by simpa [Subgroup.orderOf_coe] using hn
      have hn0 : n ≠ 0 := by
        rintro rfl
        rw [hyord] at hyprime
        norm_num at hyprime
      rw [hyord]
      exact dvd_pow_self 5 hn0
    have h5eq : 5 = orderOf y :=
      Nat.prime_eq_prime_of_dvd_pow (m := 1) (by norm_num : Nat.Prime 5) hyprime
        (by simpa using h5order)
    exact hyp h5eq.symm

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive
