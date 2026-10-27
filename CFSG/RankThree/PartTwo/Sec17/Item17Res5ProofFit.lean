module

public import CFSG.RankThree.PartTwo.Sec17.Item171StepsProofFit
public import CFSG.RankThree.PartTwo.KFacts.KS14Sz
import CFSG.CGT.PushingUpLit.ThmOne.ThreeOneFStar
import CFSG.RankThree.PartTwo.Sec4.Item413Setup
import CFSG.RankThree.PartTwo.Sec14.Item14Tools

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.GH74.GLS

namespace Proof17Res5

theorem not_three_dvd_card_of_isPerfect {J : Type*} [Group J] [Finite J] [Group.IsPerfect J]
    (h : ∀ x : J, (∃ k : ℕ, x ^ 3 ^ k = 1) → x ∈ Subgroup.center J) : ¬ 3 ∣ Nat.card J := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P⟩ : Nonempty (Sylow 3 J) := inferInstance
  have hPZ : ∀ x ∈ (P : Subgroup J), x ∈ Subgroup.center J := by
    intro x hx
    obtain ⟨k, hk⟩ := P.2 ⟨x, hx⟩
    exact h x ⟨k, congrArg Subtype.val hk⟩
  have hP : Subgroup.normalizer (P : Set J) ≤ Subgroup.centralizer (P : Set J) := by
    intro g _
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_center_iff.mp (hPZ x hx) g).symm
  set f := MonoidHom.transferSylow P hP with hf
  have hker : f.ker = ⊤ := by
    rw [eq_top_iff, ← (Group.isPerfect_def.mp inferInstance : commutator J = ⊤),
      commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      exact Subgroup.mem_center_iff.mp (hPZ _ (f y).2) (f x : J))
  have h3 := MonoidHom.not_dvd_card_ker_transferSylow P hP
  rwa [← hf, hker, Subgroup.card_top] at h3

section Quasisimple

variable {Q : Type} [Group Q] [Finite Q]

theorem aschbacherSolvableCore_eq_center (hQ : CFSG.IsQuasisimple Q) (h3 : ¬ 3 ∣ Nat.card Q) :
    aschbacherSolvableCore 3 Q = Subgroup.center Q := by
  refine le_antisymm (Sec4.aschbacherSolvableCore_le_center hQ) ?_
  obtain ⟨-, -, -, hmax, -⟩ := solvable_prime_complement_core_characterization (H := Q)
    Nat.prime_three
  exact hmax _ inferInstance inferInstance fun hd =>
    h3 (hd.trans (Subgroup.card_subgroup_dvd_card _))

section Certified

theorem suzukiModel_quot_theta (hQ : CFSG.IsQuasisimple Q) (h3 : ¬ 3 ∣ Nat.card Q)
    (hK : CFSG.IsKGroup Q) :
    ∃ n : ℕ, CFSG.Blueprint.SuzukiModel (Q ⧸ aschbacherSolvableCore 3 Q) 2 n := by
  obtain ⟨a, b, hab⟩ := hQ.2.2
  have := hQ.2.1
  set e : Q ⧸ aschbacherSolvableCore 3 Q ≃* Q ⧸ Subgroup.center Q :=
    QuotientGroup.quotientMulEquivOfEq (aschbacherSolvableCore_eq_center hQ h3) with he
  have : IsSimpleGroup (Q ⧸ aschbacherSolvableCore 3 Q) := e.isSimpleGroup
  have hnab : ∃ x y : Q ⧸ aschbacherSolvableCore 3 Q, x * y ≠ y * x :=
    ⟨e.symm a, e.symm b, fun hxy => hab (e.symm.injective (by rw [map_mul, map_mul, hxy]))⟩
  set π : (⊤ : Subgroup Q) →* Q ⧸ aschbacherSolvableCore 3 Q :=
    (QuotientGroup.mk' _).comp (⊤ : Subgroup Q).subtype with hπ
  have hπs : Function.Surjective π := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ y
    exact ⟨⟨x, Subgroup.mem_top x⟩, rfl⟩
  have hcat := CFSG.ComponentClassification.CatalogueKProper.simple_quotient_of_isKGroup hK ⊤
    _ π hπs
  refine KFacts.KS14.suzukiModel_of_inCatalog_of_not_three_dvd _ hnab hcat fun hd => h3 ?_
  exact hd.trans (Subgroup.card_quotient_dvd_card _)

end Certified

end Quasisimple

end Proof17Res5

section Main

namespace Proof17Res5

theorem eq_bot_of_commutator_pCoreOf {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G}
    {L Y₀ : Subgroup G} (h : Sec17Std G A c L Y₀) (h166 : Item166 A (lB A)) {b : G}
    (hb1 : b ≠ 1) {U : Subgroup G} (hU2 : IsPGroup 2 U)
    (hUD : U ≤ delta A (lB A) (Subgroup.centralizer ({b} : Set G)))
    (hUO2 : U ≤ CFSG.Open.pCoreOf 2 (Subgroup.normalizer (Y₀ : Set G)))
    (hO2 : CFSG.Open.pCoreOf 2 (delta A (lB A) (Subgroup.centralizer ({b} : Set G))) = ⊥)
    (hcomm : ⁅k1711 A b, U⁆ ≤ pPrimeCoreOf 3 (k1711 A b))
    (hp5 : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 →
      ⁅CFSG.Open.pCoreOf p (delta A (lB A) (Subgroup.centralizer ({b} : Set G))), U⁆ = ⊥) :
    U = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set D := delta A (lB A) (Subgroup.centralizer ({b} : Set G)) with hD
  set M := Subgroup.normalizer (Y₀ : Set G) with hM
  set K := k1711 A b with hK
  set O := pPrimeCoreOf 3 K with hO
  have hG := h.toTheoremFourHyp
  have hDtop : D ≠ ⊤ := by
    intro htop
    apply Proof1711.centralizer_ne_top hG hb1
    rw [eq_top_iff, ← htop]
    exact delta_le _
  have hAD : A ≤ Subgroup.normalizer (D : Set G) := le_normalizer_sSup fun Q hQ => hQ.1.1.2.2
  have hDK : D ≤ Subgroup.normalizer (K : Set G) :=
    le_normalizer_oPrimeResidualOf Subgroup.le_normalizer
  have hDO : D ≤ Subgroup.normalizer (O : Set G) :=
    hDK.trans (normalizer_le_normalizer_pPrimeCoreOf 3 K)
  have hO3 : Nat.Coprime 3 (Nat.card O) := coprime_card_pPrimeCoreOf 3 K
  have hp3 : ⁅CFSG.Open.pCoreOf 3 D, U⁆ = ⊥ := by
    set Z := CFSG.Open.pCoreOf 3 D with hZ
    have hZp : IsPGroup 3 Z := CFSG.LieType.BorelTits.pCoreOf_isPGroup 3 D
    have hZK : Z ≤ K := by
      intro x hx
      rw [hK, k1711, oPrimeResidualOf_eq_closure]
      obtain ⟨k, hk⟩ := hZp ⟨x, hx⟩
      exact Subgroup.subset_closure
        ⟨CFSG.LieType.BorelTits.pCoreOf_le 3 D hx, k, congrArg Subtype.val hk⟩
    have h1 : ⁅Z, U⁆ ≤ Z := Subgroup.le_normalizer_iff_commutator_le_left.mp
      (hUD.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 3 D))
    have h2 : ⁅Z, U⁆ ≤ O := (Subgroup.commutator_mono hZK le_rfl).trans hcomm
    have hZO : Z ⊓ O = ⊥ := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hZp
      refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
      rw [hn]
      exact Nat.Coprime.pow_left n hO3
    exact le_bot_iff.mp (hZO ▸ le_inf h1 h2)
  set U' : Subgroup D := U.subgroupOf D with hU'
  have hU'map : U'.map D.subtype = U := by
    rw [hU', Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hUD]
  have h2 : CFSG.pCore 2 D = ⊥ := by
    exact (Subgroup.map_eq_bot_iff_of_injective _ D.subtype_injective).mp hO2
  have hcomm_iff : ∀ X Y : Subgroup D,
      ⁅X, Y⁆ = ⊥ ↔ ⁅X.map D.subtype, Y.map D.subtype⁆ = ⊥ := by
    intro X Y
    rw [← Subgroup.map_commutator, Subgroup.map_eq_bot_iff_of_injective _ D.subtype_injective]
  have hF : ⁅CFSG.fittingSubgroup D, U'⁆ = ⊥ := by
    rw [CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore,
      Subgroup.commutator_eq_bot_iff_le_centralizer]
    refine iSup_le fun p => ?_
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, hcomm_iff, hU'map]
    have hp : (p : ℕ).Prime := Nat.prime_of_mem_primeFactors p.2
    by_cases hp2 : (p : ℕ) = 2
    · have h0 : (CFSG.Open.pCore (p : ℕ) D).map D.subtype = ⊥ := by
        rw [hp2]
        exact hO2
      rw [h0, Subgroup.commutator_bot_left]
    by_cases hp3' : (p : ℕ) = 3
    · rw [hp3']
      exact hp3
    exact hp5 p hp hp2 hp3'
  have hE : ∀ J : Subgroup D, CFSG.IsComponent J → ⁅J, U'⁆ = ⊥ := by
    intro J hJ
    have hJperf : Group.IsPerfect J := hJ.1.1
    by_cases h3J : 3 ∣ Nat.card J
    ·
      set K' : Subgroup D := oPrimeResidual 3 D with hK'
      have hK'K : K'.map D.subtype = K := rfl
      have hJK' : J ≤ K' := by
        rcases CFSG.LocalCores.component_normal_subgroup hJ (Sec15.oPrimeResidual_normal 3 D)
          with hle | hc
        · exact hle
        · exfalso
          refine not_three_dvd_card_of_isPerfect (J := J) ?_ h3J
          rintro x ⟨k, hk⟩
          rw [Subgroup.mem_center_iff]
          intro y
          have hxK : (x : D) ∈ K' :=
            Subgroup.subset_closure ⟨k, by simpa using congrArg Subtype.val hk⟩
          have hyC := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc y.2
          exact Subtype.ext (by
            rw [Subgroup.coe_mul, Subgroup.coe_mul]
            exact (Subgroup.mem_centralizer_iff.mp hyC _ hxK).symm)
      set O' : Subgroup D := O.subgroupOf D with hO'
      have hO'n : O'.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hDO
      have hJO' : ⁅J, O'⁆ = ⊥ := by
        rcases CFSG.LocalCores.component_normal_subgroup hJ hO'n with hle | hc
        · exfalso
          have hJO : J.map D.subtype ≤ O := by
            rw [Subgroup.map_le_iff_le_comap, Subgroup.comap_subtype]
            exact hle
          have hdvd : Nat.card J ∣ Nat.card O := by
            rw [← Subgroup.card_map_of_injective D.subtype_injective]
            exact Subgroup.card_dvd_of_le hJO
          exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hO3 (h3J.trans hdvd)
        · exact hc
      have hJU : ⁅J, U'⁆ ≤ O' := by
        rw [hO', ← Subgroup.comap_subtype, ← Subgroup.map_le_iff_le_comap,
          Subgroup.map_commutator, hU'map]
        refine (Subgroup.commutator_mono ?_ le_rfl).trans hcomm
        rw [← hK'K]
        exact Subgroup.map_mono hJK'
      refine CFSG.LocalCores.perfect_double_commutator hJperf (le_bot_iff.mp ?_)
      calc ⁅⁅J, U'⁆, J⁆ ≤ ⁅O', J⁆ := Subgroup.commutator_mono hJU le_rfl
        _ = ⁅J, O'⁆ := Subgroup.commutator_comm _ _
        _ ≤ ⊥ := hJO'.le
    ·
      set JG := J.map D.subtype with hJG
      have hJGθ : JG ∈ thetaComponentsIn D :=
        ⟨J, Sec4.mem_thetaComponents_of_isComponent3 hJ, rfl⟩
      have hJGq : CFSG.IsQuasisimple JG := CFSG.LocalCores.isQuasisimple_of_mulEquiv
        (J.equivMapOfInjective _ D.subtype_injective) hJ.1
      have hJG3 : ¬ 3 ∣ Nat.card JG := by
        rwa [hJG, Subgroup.card_map_of_injective D.subtype_injective]
      have hJGtop : JG ≠ ⊤ := fun htop =>
        hDtop (top_le_iff.mp (htop ▸ Subgroup.map_subtype_le J))
      have hJGK : CFSG.IsKGroup JG := (hG.sectionFourHyp hJGtop).kGroup
      have hSz := suzukiModel_quot_theta hJGq hJG3 hJGK
      have hJGM : JG ≤ M := by
        have h1 := ((h166 Y₀ h.mem_y0Star).1 D ⟨hDtop, hAD⟩ (delta_delta _).symm
          JG hJGθ hSz).2
        exact fun x hx => (h1 hx).1
      set P' : Subgroup D := (CFSG.Open.pCoreOf 2 M).subgroupOf D with hP'
      have hP'2 : IsPGroup 2 P' := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).comap_subtype
      have hJP' : J ≤ Subgroup.normalizer (P' : Set D) := by
        refine le_trans ?_ (Subgroup.le_normalizer_comap D.subtype)
        rw [← Subgroup.map_le_iff_le_comap]
        exact hJGM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)
      have hJP'c := CFSG.CGT.PushingUpLit.ThmOne.commutator_eq_bot_of_isComponent_of_le_normalizer
        hJ hP'2 hJP'
      have hU'P' : U' ≤ P' := fun x hx => hUO2 hx
      exact le_bot_iff.mp (hJP'c ▸ Subgroup.commutator_mono le_rfl hU'P')
  have hU'bot : U' = ⊥ :=
    CFSG.CGT.PushingUpLit.ThmOne.eq_bot_of_commutator_eq_bot h2 hU2.comap_subtype hE hF
  rw [← hU'map, hU'bot, Subgroup.map_bot]

end Proof17Res5

theorem step1711FitP_of (h166 : Sec16.Item166S17) : Step1711FitP := by
  intro G _ _ A c L Y₀ h a ha ha1 b hb hb1 U hU hUa hUQ hO2 hDM hcomm
  set D := delta A (lB A) (Subgroup.centralizer ({b} : Set G)) with hD
  have hAD : A ≤ Subgroup.normalizer (D : Set G) := le_normalizer_sSup fun Q hQ => hQ.1.1.2.2
  have hUD : U ≤ D := le_delta hUQ.1 (hUQ.2.trans inf_le_right)
  have hU4 : Nat.card U = 4 := (mem_fourGroups_iff.mp hU).2.2
  have hU2 : IsPGroup 2 U := IsPGroup.of_card (n := 2) (by rw [hU4]; norm_num)
  by_contra hcon
  have hp5 : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 → ⁅CFSG.Open.pCoreOf p D, U⁆ = ⊥ := by
    intro p hp hp2 hp3
    have : Fact p.Prime := ⟨hp⟩
    by_contra hne
    exact hcon ⟨p, CFSG.Open.pCoreOf p D, hp, hp2, hp3,
      CFSG.LieType.BorelTits.pCoreOf_isPGroup p D, CFSG.LieType.BorelTits.pCoreOf_le p D,
      hAD.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf p D),
      hUD.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf p D), hne⟩
  have hUbot := Proof17Res5.eq_bot_of_commutator_pCoreOf h (h166 G A c L Y₀ h) hb1 hU2 hUD
    (hUQ.2.trans inf_le_left) hO2 hcomm hp5
  rw [hUbot, Subgroup.card_bot] at hU4
  omega

end Main

end CFSG.RankThree.PartTwo.Sec17
