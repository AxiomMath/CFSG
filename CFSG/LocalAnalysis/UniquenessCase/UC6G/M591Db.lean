module

public import CFSG.LocalAnalysis.UniquenessCase.UC6G.K591Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC6C634b
public import CFSG.Quasithin.Vol2.Ch5Sec1L34OddAbel
public import CFSG.LocalAnalysis.UniquenessCase.UC6K591Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6G

open Subgroup CFSG.Open CFSG.ABGLocalTools
open scoped IsMulCommutative
open CFSG.RankThree.FFModules (fixSub)
open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

theorem Mz614.c628a'_of {G : Type} [Group G] [Finite G] {Dat : Data G} (m : Mz614 Dat) (hr3 : m.r = 3)
    (hK42 : UCK.K42) (hC : UCK.LemmaC) : m.C628a' := by
  intro hVC
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
  set ρ := UC6.frattiniRep Q₀ with hρ
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
    exact UC6.frattiniRep_eq_one_of_mem_uc6 Q₀ hq
  set ρX := QuotientGroup.lift (CFSG.pCore 2 ↥m.K) ρK hTker with hρX
  have hker2 : ∀ k : ↥m.K, ρK k = 1 → ∃ c : ℕ, orderOf k = 2 ^ c := by
    intro k hk
    obtain ⟨c, hc⟩ := UC6.exists_two_pow_orderOf_of_rep_eq_one_uc6 Q₀ hQ2 hchar (x := ι k) hk
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
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥m.K) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  set Z' : Subgroup ↥m.K := m.Z.subgroupOf m.K with hZ'
  set D : Subgroup (↥m.K ⧸ CFSG.pCore 2 ↥m.K) := Z'.map π with hD
  have hZ'card : Nat.card Z' = 3 := by
    rw [hZ', Nat.card_congr (Subgroup.subgroupOfEquivOfLe m.Z_le_K).toEquiv, m.card_Z, hr3]
  have hDcard : Nat.card D = 3 := by
    have hdvd : Nat.card D ∣ Nat.card Z' := Subgroup.card_map_dvd Z' _
    rw [hZ'card] at hdvd
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h1
    · exfalso
      have hDbot : D = ⊥ := Subgroup.card_eq_one.1 h1
      have hZT : Z' ≤ CFSG.pCore 2 ↥m.K := fun z hz => by
        have : π z ∈ D := ⟨z, hz, rfl⟩
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
    UC6.fixSub_frattini_eq_bot_uc6 Q₀ hQ2 (p := 3) (by norm_num) _ hZ3 hfixQ
  have hfixD : UCK.fixV ρX D = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    have hv' : v ∈ fixSub ρ (m.Z.subgroupOf m.M) := by
      intro z hz
      have hzK : (⟨z.1, m.Z_le_K hz⟩ : ↥m.K) ∈ Z' := hz
      exact hv (π ⟨z.1, m.Z_le_K hz⟩) ⟨_, hzK, rfl⟩
    rw [hfix0] at hv'
    exact hv'
  set U' : Subgroup ↥m.K := CFSG.pPrimeCore m.r ↥m.K with hU'
  set N : Subgroup (↥m.K ⧸ CFSG.pCore 2 ↥m.K) := U'.map π with hN
  haveI : U'.Normal := CFSG.pPrimeCore_normal
  have hNn : N.Normal := Subgroup.Normal.map inferInstance π hπs
  have hDN : D ≤ normalizer (N : Set (↥m.K ⧸ CFSG.pCore 2 ↥m.K)) := by
    rw [normalizer_eq_top_iff.2 hNn]
    exact le_top
  have hcopN : Nat.Coprime 3 (Nat.card N) := by
    have hcop : Nat.Coprime 3 (Nat.card U') := by
      rw [← hr3, ← m.card_U]
      exact m.coprime_card_U
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd U' π) hcop
  have hKgrp : CFSG.Open.IsKGroup (↥m.K ⧸ CFSG.pCore 2 ↥m.K) :=
    (CFSG.Open.IsKGroup.of_injective hMg ι hι).quotient _
  have hb : ∀ q : ℕ, q.Prime → q ≠ 2 → ∀ Q : Subgroup (↥m.K ⧸ CFSG.pCore 2 ↥m.K), Q ≤ N → IsPGroup q Q →
      D ≤ normalizer (Q : Set (↥m.K ⧸ CFSG.pCore 2 ↥m.K)) →
        Q ≤ centralizer (D : Set (↥m.K ⧸ CFSG.pCore 2 ↥m.K)) := by
    intro q hq hq2 Q hQN hQ hDQ
    haveI : Fact q.Prime := ⟨hq⟩
    by_cases hq3 : q = 3
    · subst hq3
      have hQ1 : Q = ⊥ := by
        obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hQ
        have hdvd : 3 ^ n ∣ Nat.card N := hn ▸ Subgroup.card_dvd_of_le hQN
        have hn0 : n = 0 := by
          by_contra hn0
          exact Nat.Prime.coprime_iff_not_dvd Nat.prime_three |>.1 hcopN
            ((dvd_pow_self 3 hn0).trans hdvd)
        rw [hn0, pow_zero] at hn
        exact Subgroup.card_eq_one.1 hn
      rw [hQ1]
      exact bot_le
    · rw [← commutator_eq_bot_iff_le_centralizer]
      by_contra hne
      set Q' := ⁅D, Q⁆ with hQ'
      have hQ'Q : Q' ≤ Q := le_normalizer_iff_commutator_le_right.1 hDQ
      have hQ'p : IsPGroup q Q' := hQ.to_le hQ'Q
      have hQ'ne : Q' ≠ ⊥ := by rwa [hQ', commutator_comm]
      have hDQ' : D ≤ normalizer (Q' : Set (↥m.K ⧸ CFSG.pCore 2 ↥m.K)) :=
        normalizer_commutator_ge_left D Q
      have hcopDQ : Nat.Coprime (Nat.card D) (Nat.card Q) := by
        obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hQ
        rw [hDcard, hn]
        exact Nat.Coprime.pow_right n ((Nat.coprime_primes Nat.prime_three hq).2 (Ne.symm hq3))
      have hQ'eq : ⁅D, Q'⁆ = Q' := by
        have h := CFSG.Quasithin.H13.coprime_commutator_commutator_eq hDQ hcopDQ
        rw [hQ', commutator_comm D ⁅D, Q⁆, commutator_comm D Q]
        exact h
      obtain ⟨-, hq2', -⟩ := hK42 2 Nat.prime_two (↥m.K ⧸ CFSG.pCore 2 ↥m.K) hKgrp
        (Additive (↥Q₀ ⧸ frattini ↥Q₀)) ρX hinj q 3 hq Nat.prime_three hq2 (by norm_num) hq3 D hDcard
        hfixD Q' hQ'p hQ'ne hDQ' hQ'eq
      exact hq2 hq2'
  obtain ⟨k, hk⟩ := hC _ hKgrp N D hDN hDcard hcopN hb
  have hND2 : IsPGroup 2 ↥⁅N, D⁆ := IsPGroup.of_card hk
  have hmapc : ⁅Z', U'⁆.map π = ⁅N, D⁆ := by
    rw [map_commutator, commutator_comm]
  have hC2' : IsPGroup 2 ↥⁅Z', U'⁆ := by
    intro x
    obtain ⟨a, ha⟩ := hND2 ⟨π x, hmapc ▸ mem_map_of_mem π x.2⟩
    have hxa : ((x : ↥m.K) ^ (2 ^ a)) ∈ CFSG.pCore 2 ↥m.K := by
      have h1 : π ((x : ↥m.K) ^ (2 ^ a)) = 1 := by
        rw [map_pow]
        have := congrArg Subtype.val ha
        simpa using this
      exact (QuotientGroup.eq_one_iff _).1 h1
    obtain ⟨b, hb'⟩ := hTp ⟨_, hxa⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have := congrArg Subtype.val hb'
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at this ⊢
    rw [pow_add, pow_mul, this]
  have hZU : ⁅m.Z, m.U⁆ = ⁅Z', U'⁆.map m.K.subtype := by
    rw [map_commutator, hZ', Subgroup.map_subgroupOf_eq_of_le m.Z_le_K]
    rfl
  have hC2 : IsPGroup 2 ↥⁅m.Z, m.U⁆ := hZU ▸ hC2'.map m.K.subtype
  have hCU : ⁅m.Z, m.U⁆ ≤ m.U :=
    le_normalizer_iff_commutator_le_right.1 (m.Z_le_K.trans m.K_le_normalizer_U)
  have h1 : ⁅m.Z, m.U⁆ ≤ pCoreOf 2 m.U :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hCU (normalizer_commutator_ge_right m.Z m.U) hC2
  have h2 : pCoreOf 2 m.U ≤ pCoreOf 2 m.K :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 m.U).trans m.U_le_K)
      (fun g hg => CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
        (CFSG.pCore 2 ↥m.U) (m.K_le_normalizer_U hg))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 m.U)
  exact h1.trans h2

end CFSG.LocalAnalysis.UniquenessCase.UC6G
