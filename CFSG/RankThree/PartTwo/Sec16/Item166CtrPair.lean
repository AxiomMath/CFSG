module

public import CFSG.RankThree.PartTwo.Sec16.Item166CtrT
public import CFSG.RankThree.PartTwo.Sec16.Item166CtrStar
public import CFSG.RankThree.PartTwo.Sec16.Item166ThreeSix
public import CFSG.RankThree.PartTwo.Sec17.Item1712StepsProofClaims

public section

namespace CFSG.RankThree.PartTwo.Sec16.Ctr166

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec17
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
  CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ X J : Subgroup G}

structure Max166 (A : Subgroup G) (c : G) (L Y₀ X J S C XC : Subgroup G) : Prop where
  conf : Conf166A5 A c L Y₀ X J
  card_le : ∀ X' J' : Subgroup G, Conf166A5 A c L Y₀ X' J' → Nat.card J' ≤ Nat.card J
  factorization_le : ∀ X' : Subgroup G, Conf166A5 A c L Y₀ X' J →
    (Nat.card ↥(delta A (lB A) (pPrimeCoreOf 3 X'))).factorization 2 ≤
      (Nat.card ↥(delta A (lB A) (pPrimeCoreOf 3 X))).factorization 2
  sylow_le : S ≤ delta A (lB A) (pPrimeCoreOf 3 X)
  sylow_isPGroup : IsPGroup 2 S
  sylow_not_dvd : ¬ 2 ∣ S.relIndex (delta A (lB A) (pPrimeCoreOf 3 X))
  sylow_inv : A ≤ Subgroup.normalizer (S : Set G)
  normalizer_le : Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (C : Set G)
  mem_y3Star : XC ∈ scriptY3Star A (lB A)
  delta_le : delta A (lB A) (Subgroup.normalizer (C : Set G)) ≤ XC
  not_le : ¬ XC ≤ Subgroup.normalizer (Y₀ : Set G)

theorem Conf166A5.comp3In_eq_of_ks
    (hC : Conf166A5 A c L Y₀ X J) (hRead : Sec15.Y4CoreReadR)
    (hMem : Sec15.Y4CoreMemR) (h1523 : Item1523R) (hK : KFacts.KS166J2A5) :
    Sec15.comp3In X = {J} := by
  have hperf : Group.IsPerfect ↥J := isPerfect_of_mem_thetaComponentsIn hC.mem_theta
  have hAJ : A ≤ Subgroup.normalizer (J : Set G) := hC.mem_y0.1.1.2
  exact hC.comp3In_eq hRead hMem
    (pCoreOf_le_pCoreOf_y0 hC.std hC.j2 h1523 hK hC.le_y0 hperf hC.quot_a5 hAJ)
    (isSolvable_centralizer_star hC.std hC.j2 h1523 hK hC.le_y0 hperf hC.quot_a5 hAJ)

theorem exists_conf_max (hne : ∃ X J : Subgroup G, Conf166A5 A c L Y₀ X J) :
    ∃ X J : Subgroup G, Conf166A5 A c L Y₀ X J ∧
      (∀ X' J' : Subgroup G, Conf166A5 A c L Y₀ X' J' → Nat.card J' ≤ Nat.card J) ∧
      ∀ X' : Subgroup G, Conf166A5 A c L Y₀ X' J →
        (Nat.card ↥(delta A (lB A) (pPrimeCoreOf 3 X'))).factorization 2 ≤
          (Nat.card ↥(delta A (lB A) (pPrimeCoreOf 3 X))).factorization 2 := by
  classical
  let F : Set (Subgroup G × Subgroup G) := {p | Conf166A5 A c L Y₀ p.1 p.2}
  have hF : F.Nonempty := by
    obtain ⟨X, J, h⟩ := hne
    exact ⟨(X, J), h⟩
  let key : Subgroup G × Subgroup G → ℕ ×ₗ ℕ := fun p =>
    toLex (Nat.card p.2,
      (Nat.card ↥(delta A (lB A) (pPrimeCoreOf 3 p.1))).factorization 2)
  obtain ⟨⟨X, J⟩, hp, hmax⟩ := Set.exists_max_image F key (Set.toFinite F) hF
  refine ⟨X, J, hp, ?_, ?_⟩
  · intro X' J' h'
    exact Prod.Lex.monotone_fst (key (X', J')) (key (X, J)) (hmax (X', J') h')
  · intro X' h'
    have hk : key (X', J) ≤ key (X, J) := hmax (X', J) h'
    rcases Prod.Lex.toLex_le_toLex.mp hk with hlt | ⟨-, hle⟩
    · exact absurd hlt (lt_irrefl _)
    · exact hle

theorem mem_scriptQ_delta (hC : Conf166A5 A c L Y₀ X J) (h146 : Item146S14) :
    delta A (lB A) (pPrimeCoreOf 3 X) ∈ scriptQ A (lB A) := by
  have h146' : Item146 A (lB A) := h146 G A c L hC.std.toSec14Std
  have h3 : ¬ 3 ∣ Nat.card (delta A (lB A) (pPrimeCoreOf 3 X)) := fun h =>
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (coprime_card_pPrimeCoreOf 3 X)) (h.trans (Subgroup.card_dvd_of_le (delta_le _)))
  exact Proof165.delta_mem_scriptQ_of_three hC.std.toSec14Std.isE27 h146' _ h3

private theorem exists_C_of_sylow (hC : Conf166A5 A c L Y₀ X J) (hbot : Item145BotS17)
    (hRead : Sec15.Y4CoreReadR) (h146 : Item146S14) (h149 : Item149S14) (h1523 : Item1523R)
    (hU : Sec15.comp3In X = {J}) {S : Subgroup G}
    (hST : S ≤ delta A (lB A) (pPrimeCoreOf 3 X)) (hS2 : IsPGroup 2 S)
    (hSidx : ¬ 2 ∣ S.relIndex (delta A (lB A) (pPrimeCoreOf 3 X)))
    (hAS : A ≤ Subgroup.normalizer (S : Set G)) :
    ∃ C : Subgroup G, (C = jOf S ∨ C = omegaOneZ (jOneOf S)) ∧ C ≠ ⊥ ∧
      IsPGroup 2 C ∧ C ∈ scriptQ A (lB A) ∧
      Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (C : Set G) ∧
      ¬ delta A (lB A) (Subgroup.normalizer (C : Set G)) ≤
        Subgroup.normalizer (Y₀ : Set G) := by
  classical
  have hSne : S ≠ ⊥ :=
    Conf166A5.ne_bot_of_not_dvd_relIndex hC hbot hRead h146 h149 h1523 hU hSidx
  have hSQ : S ∈ scriptQ A (lB A) :=
    mem_scriptQ_of_le (mem_scriptQ_delta hC h146) hST hAS
  rcases Conf166A5.exists_delta_normalizer_not_le hC hbot hRead h146 h149 h1523 hU hST
    hS2 hSidx hAS with
    hJ | hΩ
  · refine ⟨jOf S, Or.inl rfl, Sec7.jOf_ne_bot hS2 hSne, hS2.to_le (Sec7.jOf_le S),
      jOf_mem_scriptQ hSQ, ?_, hJ⟩
    simpa only [Sec7.tripleOf_zero] using Sec7.normalizer_le_normalizer_tripleOf S 0
  · refine ⟨omegaOneZ (jOneOf S), Or.inr rfl,
      Sec7.omegaOneZ_ne_bot (hS2.to_le (Sec7.jOneOf_le S))
        (Sec7.jOneOf_ne_bot hS2 hSne),
      hS2.to_le (Sec7.omegaOneZ_jOneOf_le S),
      omegaOneZ_jOneOf_mem_scriptQ hSQ, ?_, hΩ⟩
    simpa only [Sec7.tripleOf_one] using Sec7.normalizer_le_normalizer_tripleOf S 1

theorem exists_max166
    (hbot : Item145BotS17) (hRead : Sec15.Y4CoreReadR)
    (hMem : Sec15.Y4CoreMemR) (h146 : Item146S14) (h149 : Item149S14) (h1523 : Item1523R)
    (hK : KFacts.KS166J2A5) (hne : ∃ X J : Subgroup G, Conf166A5 A c L Y₀ X J) :
    ∃ X J S C XC : Subgroup G, Max166 A c L Y₀ X J S C XC ∧
      ¬ delta A (lB A) (Subgroup.normalizer (C : Set G)) ≤ Subgroup.normalizer (Y₀ : Set G) ∧
      (C = jOf S ∨ C = omegaOneZ (jOneOf S)) := by
  obtain ⟨X, J, hconf, hmaxJ, hmaxT⟩ := exists_conf_max hne
  have hU : Sec15.comp3In X = {J} :=
    Conf166A5.comp3In_eq_of_ks hconf hRead hMem h1523 hK
  obtain ⟨S, hST, hS2, hSidx, hAS⟩ :=
    exists_sylow_two_delta hconf.std hconf.mem_y3Star.prop.1.1.2
  obtain ⟨C, hCor, hC1, hC2, hCQ, hNC, hCM⟩ :=
    exists_C_of_sylow hconf hbot hRead h146 h149 h1523 hU hST hS2 hSidx hAS
  obtain ⟨XC, hXC3, hDXC, hXCM⟩ :=
    exists_mem_scriptY3Star_of_not_le hconf.std hC1 hC2 hCQ hCM
  refine ⟨X, J, S, C, XC, ?_, hCM, hCor⟩
  exact
    { conf := hconf
      card_le := hmaxJ
      factorization_le := hmaxT
      sylow_le := hST
      sylow_isPGroup := hS2
      sylow_not_dvd := hSidx
      sylow_inv := hAS
      normalizer_le := hNC
      mem_y3Star := hXC3
      delta_le := hDXC
      not_le := hXCM }

namespace Max166

variable {S C XC : Subgroup G}

theorem commutator_le (hM : Max166 A c L Y₀ X J S C XC) :
    ⁅S, J⁆ ≤ CFSG.Open.pCoreOf 2 J := by
  have hTR : delta A (lB A) (pPrimeCoreOf 3 X) ≤ pPrimeCoreOf 3 X := Sec14.delta_le _
  calc ⁅S, J⁆ ≤ ⁅delta A (lB A) (pPrimeCoreOf 3 X), J⁆ :=
        Subgroup.commutator_mono hM.sylow_le le_rfl
    _ = ⁅J, delta A (lB A) (pPrimeCoreOf 3 X)⁆ := Subgroup.commutator_comm _ _
    _ ≤ ⁅J, pPrimeCoreOf 3 X⁆ := Subgroup.commutator_mono le_rfl hTR
    _ ≤ CFSG.Open.pCoreOf 2 J := hM.conf.commutator_pPrimeCore_le

theorem pCoreOf_le
    (hM : Max166 A c L Y₀ X J S C XC)
    (hRead : Sec15.Y4CoreReadR) (hMem : Sec15.Y4CoreMemR) (h1523 : Item1523R)
    (hK : KFacts.KS166J2A5) (hQ0 : Claim17Q0) : CFSG.Open.pCoreOf 2 J ≤ S := by
  classical
  set R := CFSG.Open.pCoreOf 2 J with hR
  set T := delta A (lB A) (pPrimeCoreOf 3 X) with hT
  have hJQ : R ≤ CFSG.Open.pCoreOf 2 Y₀ :=
    pCoreOf_le_pCoreOf_y0 hM.conf.std hM.conf.j2 h1523 hK hM.conf.le_y0
      (isPerfect_of_mem_thetaComponentsIn hM.conf.mem_theta) hM.conf.quot_a5
      hM.conf.mem_y0.1.1.2
  have hRQ : R ∈ scriptQ A (lB A) := by
    refine mem_scriptQ_of_le (hQ0 G A c L Y₀ hM.conf.std) hJQ ?_
    exact hM.conf.mem_y0.1.1.2.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 J)
  have hRT : R ≤ T := le_delta hRQ hM.conf.pCoreOf_le_pPrimeCore
  have hU : Sec15.comp3In X = {J} :=
    Conf166A5.comp3In_eq_of_ks hM.conf hRead hMem h1523 hK
  have hXNR : X ≤ Subgroup.normalizer (R : Set G) :=
    (Conf166A5.le_normalizer hM.conf hU).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 J)
  have hSNR : S ≤ Subgroup.normalizer (R : Set G) :=
    (hM.sylow_le.trans (Sec14.delta_le _)).trans ((pPrimeCoreOf_le 3 X).trans hXNR)
  have hZ2 : IsPGroup 2 (R ⊔ S : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 J)
      hM.sylow_isPGroup hSNR
  have hZT : R ⊔ S ≤ T := sup_le hRT hM.sylow_le
  have hSz : S ≤ R ⊔ S := le_sup_right
  have hidxZ : ¬ 2 ∣ S.relIndex (R ⊔ S) := by
    intro h2
    apply hM.sylow_not_dvd
    change 2 ∣ S.relIndex T
    rw [← Subgroup.relIndex_mul_relIndex S (R ⊔ S) T hSz hZT]
    exact dvd_mul_of_dvd_left h2 _
  have hrel : S.relIndex (R ⊔ S) = 1 := by
    obtain ⟨n, hn⟩ := hZ2.exists_card_eq
    have hdvd : S.relIndex (R ⊔ S) ∣ 2 ^ n := by
      rw [← hn]
      exact Subgroup.relIndex_dvd_card S (R ⊔ S)
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have hk0 : k = 0 := by
      by_contra hkne
      exact hidxZ (hk ▸ dvd_pow_self 2 hkne)
    rw [hk, hk0, pow_zero]
  exact le_sup_left.trans (Subgroup.relIndex_eq_one.mp hrel)

theorem le_normalizer
    (hM : Max166 A c L Y₀ X J S C XC)
    (hRead : Sec15.Y4CoreReadR) (hMem : Sec15.Y4CoreMemR) (h1523 : Item1523R)
    (hK : KFacts.KS166J2A5) (hQ0 : Claim17Q0) : J ≤ Subgroup.normalizer (S : Set G) := by
  have hOS : CFSG.Open.pCoreOf 2 J ≤ S :=
    pCoreOf_le hM hRead hMem h1523 hK hQ0
  have hJS : ⁅J, S⁆ ≤ CFSG.Open.pCoreOf 2 J := by
    rw [Subgroup.commutator_comm]
    exact hM.commutator_le
  have hconj : ∀ j ∈ J, ∀ s ∈ S, j * s * j⁻¹ ∈ S := by
    intro j hj s hs
    have hmem : ⁅j, s⁆ ∈ CFSG.Open.pCoreOf 2 J :=
      (Subgroup.commutator_le.mp hJS) j hj s hs
    have hcalc : j * s * j⁻¹ = ⁅j, s⁆ * s := by rw [commutatorElement_def]; group
    rw [hcalc]
    exact S.mul_mem (hOS hmem) hs
  intro j hj
  refine Subgroup.mem_normalizer_iff.mpr fun s => ⟨hconj j hj s, ?_⟩
  intro hs
  have h1 := hconj j⁻¹ (J.inv_mem hj) (j * s * j⁻¹) hs
  have h2 : j⁻¹ * (j * s * j⁻¹) * (j⁻¹)⁻¹ = s := by group
  rwa [h2] at h1

theorem le_xc
    (hM : Max166 A c L Y₀ X J S C XC)
    (hRead : Sec15.Y4CoreReadR) (hMem : Sec15.Y4CoreMemR) (h1523 : Item1523R)
    (hK : KFacts.KS166J2A5) (hQ0 : Claim17Q0) : J ≤ XC := by
  have hJN : J ≤ Subgroup.normalizer (S : Set G) :=
    le_normalizer hM hRead hMem h1523 hK hQ0
  have hJC : J ≤ Subgroup.normalizer (C : Set G) := hJN.trans hM.normalizer_le
  calc J = delta A (lB A) J := hM.conf.mem_y0.1.2.2.1
    _ ≤ delta A (lB A) (Subgroup.normalizer (C : Set G)) := delta_mono hJC
    _ ≤ XC := hM.delta_le

private theorem mem_theta_xc (hM : Max166 A c L Y₀ X J S C XC)
    (hOmg : Step166OmgNotA5HJ) (h152 : Item152R) (h155 : Item155R) (hJXC : J ≤ XC)
    (hXns : ¬ Group.IsSolvable ↥XC)
    (hsolc : Group.IsSolvable ↥(pPrimeCoreOf 3 XC))
    (hres : oPrimeResidualOf 3 XC ≠ ⊥) :
    J ∈ thetaComponentsIn (Subgroup.normalizer (CFSG.Open.pCoreOf 2 XC : Set G)) := by
  classical
  set N : Subgroup G := Subgroup.normalizer (CFSG.Open.pCoreOf 2 XC : Set G) with hN
  have hJ4 : J ∈ scriptY4 A (lB A) := hM.conf.mem_y0.1
  by_cases hA5 : ∃ J₀ : Subgroup G, J₀ ∈ thetaComponentsIn N ∧
      J₀ ∈ scriptY0 A (lB A) ∧ J ≤ J₀ ∧
        Nonempty (↥J₀ ⧸ CFSG.pCore 2 ↥J₀ ≃* alternatingGroup (Fin 5))
  · obtain ⟨J₀, hth, hY0, hle, hquot⟩ := hA5
    have hconf : Conf166A5 A c L Y₀ XC J₀ :=
      { std := hM.conf.std
        j2 := hM.conf.j2
        mem_y3Star := hM.mem_y3Star
        not_solvable := hXns
        solvable_core := hsolc
        residual_ne_bot := hres
        mem_theta := hth
        mem_y0 := hY0
        quot_a5 := hquot
        not_le := hM.not_le }
    have hcard : Nat.card J₀ ≤ Nat.card J := hM.card_le XC J₀ hconf
    have hJeq : J = J₀ := Subgroup.eq_of_le_of_card_ge hle hcard
    exact hJeq ▸ hth
  · have hN2 : N ∈ scriptY2 A :=
      normalizer_pCoreOf_mem_scriptY2 hM.conf.std.isSimpleGroup hM.conf.std.nonabelian
        hM.mem_y3Star.prop.1
    have hloc : IsPLocal 2 N :=
      CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 XC) hM.mem_y3Star.prop.1.2
    have hF : generalizedFitting ↥N = CFSG.pCore 2 ↥N :=
      (isCharacteristicP_iff_generalizedFitting_eq_pCore ↥N 2).mp
        (CFSG.CGT.PushingUp.isCharacteristicP_of_isPLocal hM.conf.std.charTwoType hloc)
    have h152' : Item152 A (lB A) := h152 G A c L hM.conf.std.toSec15R
    have h155' : Item155 A (lB A) := h155 G A c L hM.conf.std.toSec15R
    have homg : ∀ J₀ ∈ thetaComponentsIn N, J₀ ∈ scriptY0 A (lB A) → J ≤ J₀ →
        omg155 A J₀ := by
      intro J₀ hth hY0 hle
      exact hOmg G A c L Y₀ hM.conf.std hM.conf.j2 XC hM.mem_y3Star hres hM.not_le
        J hJ4 hJXC J₀ hth hY0 hle
        (not_nonempty_iff.mp fun hq => hA5 ⟨J₀, hth, hY0, hle, hq⟩)
    exact absurd (Proof166Res3.le_M_of_omg hM.conf.std h152' h155'
      hM.mem_y3Star.prop hJ4 hJXC homg) hM.not_le

theorem conf_xc
    (hM : Max166 A c L Y₀ X J S C XC)
    (hRead : Sec15.Y4CoreReadR) (hMem : Sec15.Y4CoreMemR) (h1523 : Item1523R)
    (hK : KFacts.KS166J2A5) (hQ0 : Claim17Q0) (hsol : Step166SolHJ)
    (hΩ : Step166OmegaHJ) (hOmg : Step166OmgNotA5HJ) (h152 : Item152R) (h155 : Item155R) :
    Conf166A5 A c L Y₀ XC J := by
  have hJXC : J ≤ XC := le_xc hM hRead hMem h1523 hK hQ0
  have hJns : ¬ Group.IsSolvable ↥J := by
    intro hs
    have hA5ns : ¬ Group.IsSolvable ↥(alternatingGroup (Fin 5)) := by
      intro hsA
      haveI : Group.IsPerfect ↥(alternatingGroup (Fin 5)) :=
        ⟨commutator_alternatingGroup_eq_top (α := Fin 5) (by simp)⟩
      exact Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 5)) hsA
    haveI : Group.IsSolvable ↥J := hs
    obtain ⟨e⟩ := hM.conf.quot_a5
    have hq : Group.IsSolvable (↥J ⧸ CFSG.pCore 2 ↥J) :=
      Group.isSolvable_of_surjective (f := QuotientGroup.mk' (CFSG.pCore 2 ↥J))
        (QuotientGroup.mk'_surjective _)
    haveI : Group.IsSolvable (↥J ⧸ CFSG.pCore 2 ↥J) := hq
    exact hA5ns (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)
  have hXns : ¬ Group.IsSolvable ↥XC := by
    intro hs
    haveI : Group.IsSolvable ↥XC := hs
    exact hJns (Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective hJXC))
  have hJne : J ≠ ⊥ := Sec15.ne_bot_of_mem_scriptY4 hM.conf.mem_y0.1
  have hres : oPrimeResidualOf 3 XC ≠ ⊥ := by
    intro hbot
    apply hJne
    have hle : J ≤ oPrimeResidualOf 3 XC := by
      rw [hM.conf.mem_y0.1.2.1]
      exact oPrimeResidualOf_mono 3 hJXC
    rw [hbot] at hle
    exact le_bot_iff.mp hle
  have hsolc : Group.IsSolvable ↥(pPrimeCoreOf 3 XC) :=
    hsol G A c L Y₀ hM.conf.std hM.conf.j2
      (hΩ G A c L Y₀ hM.conf.std hM.conf.j2) XC hM.mem_y3Star hXns hM.not_le
  exact
    { std := hM.conf.std
      j2 := hM.conf.j2
      mem_y3Star := hM.mem_y3Star
      not_solvable := hXns
      solvable_core := hsolc
      residual_ne_bot := hres
      mem_theta := mem_theta_xc hM hOmg h152 h155 hJXC hXns hsolc hres
      mem_y0 := hM.conf.mem_y0
      quot_a5 := hM.conf.quot_a5
      not_le := hM.not_le }

theorem le_delta_xc
    (hM : Max166 A c L Y₀ X J S C XC)
    (hbot : Item145BotS17) (hRead : Sec15.Y4CoreReadR) (hMem : Sec15.Y4CoreMemR)
    (h146 : Item146S14) (h1523 : Item1523R) (hK : KFacts.KS166J2A5) (hQ0 : Claim17Q0)
    (hsol : Step166SolHJ) (hΩ : Step166OmegaHJ) (hOmg : Step166OmgNotA5HJ) (h152 : Item152R)
    (h155 : Item155R) : S ≤ delta A (lB A) (pPrimeCoreOf 3 XC) := by
  have hconfC : Conf166A5 A c L Y₀ XC J :=
    conf_xc hM hRead hMem h1523 hK hQ0 hsol hΩ hOmg h152 h155
  have hUC : Sec15.comp3In XC = {J} :=
    Conf166A5.comp3In_eq_of_ks hconfC hRead hMem h1523 hK
  have hSQ : S ∈ scriptQ A (lB A) :=
    mem_scriptQ_of_le (mem_scriptQ_delta hM.conf h146) hM.sylow_le hM.sylow_inv
  have hSXC : S ≤ XC :=
    (le_delta hSQ (Subgroup.le_normalizer.trans hM.normalizer_le)).trans hM.delta_le
  have hSR : S ≤ pPrimeCoreOf 3 XC :=
    Conf166A5.le_pPrimeCore_of_commutator_le hconfC hbot hRead hUC hSXC hM.commutator_le
  exact le_delta hSQ hSR

theorem spade
    (hM : Max166 A c L Y₀ X J S C XC)
    (hbot : Item145BotS17) (hRead : Sec15.Y4CoreReadR) (hMem : Sec15.Y4CoreMemR)
    (h146 : Item146S14) (h1523 : Item1523R) (hK : KFacts.KS166J2A5) (hQ0 : Claim17Q0)
    (hsol : Step166SolHJ) (hΩ : Step166OmegaHJ) (hOmg : Step166OmgNotA5HJ) (h152 : Item152R)
    (h155 : Item155R) :
    ∀ U : Subgroup G, U ≤ Subgroup.normalizer (S : Set G) → U ∈ scriptQ A (lB A) →
      IsPGroup 2 U → U ≤ Subgroup.normalizer (J : Set G) ∧
        (⁅U, J⁆ ≤ CFSG.Open.pCoreOf 2 J → U ≤ S) := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro U hUNS hUQ hU2
  have hconfC : Conf166A5 A c L Y₀ XC J :=
    conf_xc hM hRead hMem h1523 hK hQ0 hsol hΩ hOmg h152 h155
  have hUC : Sec15.comp3In XC = {J} :=
    Conf166A5.comp3In_eq_of_ks hconfC hRead hMem h1523 hK
  have hUXC : U ≤ XC :=
    (le_delta hUQ (hUNS.trans hM.normalizer_le)).trans hM.delta_le
  constructor
  · exact hUXC.trans (Conf166A5.le_normalizer hconfC hUC)
  · intro hcommU
    have hUR : U ≤ pPrimeCoreOf 3 XC :=
      Conf166A5.le_pPrimeCore_of_commutator_le hconfC hbot hRead hUC hUXC hcommU
    have hUT : U ≤ delta A (lB A) (pPrimeCoreOf 3 XC) := le_delta hUQ hUR
    have hST : S ≤ delta A (lB A) (pPrimeCoreOf 3 XC) :=
      le_delta_xc hM hbot hRead hMem h146 h1523 hK hQ0 hsol hΩ hOmg h152 h155
    have hZ2 : IsPGroup 2 (U ⊔ S : Subgroup G) :=
      IsPGroup.to_sup_of_normal_right' hU2 hM.sylow_isPGroup hUNS
    have hZT : U ⊔ S ≤ delta A (lB A) (pPrimeCoreOf 3 XC) := sup_le hUT hST
    have hcard : Nat.card ↥(U ⊔ S) ≤ Nat.card S :=
      Proof166Three.card_le_of_factorization_le (p := 2) hM.sylow_le
        hM.sylow_isPGroup hM.sylow_not_dvd hZT hZ2 (hM.factorization_le XC hconfC)
    have hZeq : S = U ⊔ S := Subgroup.eq_of_le_of_card_ge le_sup_right hcard
    rw [hZeq]
    exact le_sup_left

end Max166

end CFSG.RankThree.PartTwo.Sec16.Ctr166
