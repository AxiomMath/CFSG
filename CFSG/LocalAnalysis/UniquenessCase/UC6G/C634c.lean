module

public import CFSG.LocalAnalysis.UniquenessCase.UC6G.C632d
public import CFSG.LocalAnalysis.UniquenessCase.UC6C634b
public import CFSG.GroupTheory.BaerSuzuki.Helpers
public import CFSG.LocalAnalysis.UniquenessCase.UC6O633Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase

open Subgroup CFSG.Open CFSG.ABGLocalTools
open scoped IsMulCommutative
open CFSG.RankThree.FFModules (fixSub)

namespace UC6G

open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

namespace Mz614

variable {G : Type} [Group G] [Finite G] {Dat : Data G} (m : Mz614 Dat)

theorem tail_false (hr3 : m.r = 3) (hK : UCK.K634)
    (hQ : CFSG.Open.IsQuasisimple (CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 m.K))
    (h625 : m.C625) (h626 : m.C626) (hVC : m.V ⊓ centralizer (m.Z : Set G) = ⊥) : False := by
  haveI := Dat.standing.simple
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hMg : CFSG.Open.IsKGroup ↥m.M := Dat.standing.kProper.isKGroup m.M m.M_ne_top
  haveI hQn : (CFSG.pCore 2 ↥m.M).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hQ2 : IsPGroup 2 (CFSG.pCore 2 ↥m.M) := CFSG.LieType.BorelTits.pCore_isPGroup 2
  have hchar : centralizer ((CFSG.pCore 2 ↥m.M : Subgroup ↥m.M) : Set ↥m.M) ≤
      CFSG.pCore 2 ↥m.M := by
    intro x hx
    have h1 := Dat.standing.charTwo m.M Dat.maxLocal.1
    have hxG : (x : G) ∈ m.M ⊓ centralizer (pCoreOf 2 m.M : Set G) := by
      refine ⟨x.2, ?_⟩
      show (x : G) ∈ centralizer (pCoreOf 2 m.M : Set G)
      rw [mem_centralizer_iff]
      rintro _ ⟨q, hq, rfl⟩
      have := mem_centralizer_iff.1 hx q hq
      exact congrArg Subtype.val this
    obtain ⟨q, hq, hqx⟩ := h1 hxG
    have : q = x := Subtype.ext hqx
    exact this ▸ hq
  haveI : IsElementaryAbelian 2 (↥(CFSG.pCore 2 ↥m.M) ⧸ frattini ↥(CFSG.pCore 2 ↥m.M)) :=
    (CFSG.GroupTheory.frattini_elementary_quotient hQ2).2.2.2.1
  set Q₀ : Subgroup ↥m.M := CFSG.pCore 2 ↥m.M with hQ₀
  set ρ := frattiniRep Q₀ with hρ
  set ι : ↥m.K →* ↥m.M := Subgroup.inclusion m.K_le_M with hιdef
  have hι : Function.Injective ι := Subgroup.inclusion_injective m.K_le_M
  set ρK := MonoidHom.comp ρ ι with hρK
  haveI hTn : (CFSG.pCore 2 ↥m.K).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hTp : IsPGroup 2 (CFSG.pCore 2 ↥m.K) := CFSG.LieType.BorelTits.pCore_isPGroup 2
  have hOK : pCoreOf 2 m.K ≤ pCoreOf 2 m.M := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 m.K).trans m.K_le_M) ?_
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 m.K)
    intro g hg
    exact CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (CFSG.pCore 2 ↥m.K) (m.mem_normalizer_K hg)
  have hTker : CFSG.pCore 2 ↥m.K ≤ ρK.ker := by
    intro k hk
    obtain ⟨q, hq, hqk⟩ := hOK ⟨k, hk, rfl⟩
    have hιk : ι k = q := Subtype.ext hqk.symm
    rw [MonoidHom.mem_ker, hρK, MonoidHom.comp_apply, hιk]
    exact frattiniRep_eq_one_of_mem_uc6 Q₀ hq
  set ρX := QuotientGroup.lift (CFSG.pCore 2 ↥m.K) ρK hTker with hρX
  have hker2 : ∀ k : ↥m.K, ρK k = 1 → ∃ c : ℕ, orderOf k = 2 ^ c := by
    intro k hk
    obtain ⟨c, hc⟩ := exists_two_pow_orderOf_of_rep_eq_one_uc6 Q₀ hQ2 hchar (x := ι k) hk
    exact ⟨c, by rw [← hc]; exact (orderOf_injective ι hι k).symm⟩
  have hkerp : IsPGroup 2 ρK.ker := IsPGroup.iff_orderOf.2 fun x => by
    obtain ⟨c, hc⟩ := hker2 x.1 x.2
    exact ⟨c, by rw [← hc]; exact (Subgroup.orderOf_coe x).symm⟩
  have hkerle : ρK.ker ≤ CFSG.pCore 2 ↥m.K :=
    CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup (MonoidHom.normal_ker ρK) hkerp
  have hinj : Function.Injective ρX := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
    exact (QuotientGroup.eq_one_iff k).2 (hkerle (show ρK k = 1 from hx))
  set Z' : Subgroup ↥m.K := m.Z.subgroupOf m.K with hZ'
  set D : Subgroup (↥m.K ⧸ CFSG.pCore 2 ↥m.K) := Z'.map (QuotientGroup.mk' _) with hD
  have hZ'card : Nat.card Z' = 3 := by
    rw [hZ', Nat.card_congr (Subgroup.subgroupOfEquivOfLe m.Z_le_K).toEquiv, m.card_Z, hr3]
  have hDcard : Nat.card D = 3 := by
    have hdvd : Nat.card D ∣ Nat.card Z' := Subgroup.card_map_dvd Z' _
    rw [hZ'card] at hdvd
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h1
    · exfalso
      have hDbot : D = ⊥ := Subgroup.card_eq_one.1 h1
      have hZT : Z' ≤ CFSG.pCore 2 ↥m.K := fun z hz => by
        have : QuotientGroup.mk' (CFSG.pCore 2 ↥m.K) z ∈ D := ⟨z, hz, rfl⟩
        rw [hDbot, Subgroup.mem_bot] at this
        exact (QuotientGroup.eq_one_iff z).1 this
      have h3 : 3 ∣ Nat.card (CFSG.pCore 2 ↥m.K) := hZ'card ▸ Subgroup.card_dvd_of_le hZT
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hTp
      rw [hn] at h3
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
      omega
    · exact h1
  have hZ3 : IsPGroup 3 (m.Z.subgroupOf m.M) := IsPGroup.of_card (n := 1) (by
    rw [pow_one, Nat.card_congr (Subgroup.subgroupOfEquivOfLe m.Z_le_M).toEquiv, m.card_Z, hr3])
  have hfixQ : Q₀ ⊓ centralizer ((m.Z.subgroupOf m.M : Subgroup ↥m.M) : Set ↥m.M) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxG : (x : G) ∈ m.V ⊓ centralizer (m.Z : Set G) := by
      refine ⟨⟨x, hx.1, rfl⟩, ?_⟩
      show (x : G) ∈ centralizer (m.Z : Set G)
      rw [mem_centralizer_iff]
      intro h hh
      have := mem_centralizer_iff.1 hx.2 ⟨h, m.Z_le_M hh⟩ hh
      exact congrArg Subtype.val this
    rw [hVC] at hxG
    exact Subgroup.mem_bot.2 (Subtype.ext (Subgroup.mem_bot.1 hxG))
  have hfix0 : fixSub ρ (m.Z.subgroupOf m.M) = ⊥ :=
    fixSub_frattini_eq_bot_uc6 Q₀ hQ2 (p := 3) (by norm_num) _ hZ3 hfixQ
  have hfixD : fixSub ρX D = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    have hv' : v ∈ fixSub ρ (m.Z.subgroupOf m.M) := by
      intro z hz
      have hzK : (⟨z.1, m.Z_le_K hz⟩ : ↥m.K) ∈ Z' := hz
      have := hv (QuotientGroup.mk' (CFSG.pCore 2 ↥m.K) ⟨z.1, m.Z_le_K hz⟩) ⟨_, hzK, rfl⟩
      exact this
    rw [hfix0] at hv'
    exact hv'
  have hK1 : CFSG.Open.IsKGroup ↥m.K := CFSG.Open.IsKGroup.of_injective hMg ι hι
  have hKgrp : CFSG.Open.IsKGroup (↥m.K ⧸ CFSG.pCore 2 ↥m.K) := hK1.quotient _
  have hrankK : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p
      (⊤ : Subgroup (↥m.K ⧸ CFSG.pCore 2 ↥m.K)) = CFSG.Open.pRank p m.K := by
    intro p hp hp2
    haveI : Fact p.Prime := ⟨hp⟩
    have hnd : ¬ p ∣ Nat.card (CFSG.pCore 2 ↥m.K) := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hTp
      rw [hn]
      intro hd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))
    have e1 := CFSG.SectionRank.pRank_quotient_eq (CFSG.pCore 2 ↥m.K) hnd
    rw [e1]
    have h1 := pRank_map_subtype_uc6 hp m.K (⊤ : Subgroup ↥m.K)
    have h2 : (⊤ : Subgroup ↥m.K).map m.K.subtype = m.K := by
      rw [← MonoidHom.range_eq_map]; exact Subgroup.range_subtype _
    rw [h2] at h1
    exact h1.symm
  have hrank3 : CFSG.Open.pRank 3 (⊤ : Subgroup (↥m.K ⧸ CFSG.pCore 2 ↥m.K)) = 1 := by
    rw [hrankK 3 Nat.prime_three (by norm_num)]
    have h625' : CFSG.Open.pRank m.r m.K = 1 := h625
    rw [hr3] at h625'
    exact h625'
  obtain ⟨p, hp⟩ := m.hk.nonempty
  have hpr : (p).Prime := (Dat.sig_prime _ hp).1
  have hp2 : p ≠ 2 := (Dat.sig_prime _ hp).2
  have hp3 : p ≠ 3 := fun h => m.hrσ (by rw [hr3, ← h]; exact hp)
  haveI : Fact (p).Prime := ⟨hpr⟩
  obtain ⟨P, hP⟩ := exists_isSylowOf p m.M
  have hodd : Odd m.r := m.hr.odd_of_ne_two m.d.odd
  have hPK : P ≤ m.K := m.sylow_le_K hp (m.sylow_cyclic_of_pRank_eq_one h625 hodd) h626 hP
  have h4 : 3 ≤ CFSG.Open.pRank p P := m.three_le_pRank_sylow_M hp hP
  obtain ⟨E, hEP, hEel, hEcard⟩ := CFSG.PreuniquenessRankFour.Helpers.pRank_attained p hpr P
  have h4K : 3 ≤ CFSG.Open.pRank p m.K := by
    have := CFSG.SectionRank.le_pRank hpr.one_lt (hEP.trans hPK) hEel hEcard
    omega
  have hle := hK _ hKgrp hQ hrank3 (Additive (↥Q₀ ⧸ frattini ↥Q₀)) ρX hinj D hDcard hfixD
    p hpr hp2 hp3
  rw [hrankK _ hpr hp2] at hle
  omega

end Mz614

end UC6G

end CFSG.LocalAnalysis.UniquenessCase
