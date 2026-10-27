module

public import CFSG.RankThree.PartTwo.Sec18.Item189QModule
public import CFSG.RankThree.PartTwo.Sec18.Item189QKernel
public import CFSG.RankThree.PartTwo.Sec18.Item189StepProofO3
public import CFSG.RankThree.PartTwo.Sec18.Item189StepProofO2Direct
public import CFSG.RankThree.PartTwo.Sec18.Item189KTypeProof
import CFSG.RankThree.PartTwo.Sec6.Item612Basic
import CFSG.RankThree.PartTwo.Sec18.Item189KType
import CFSG.RankThree.PartTwo.Sec20.OneTools
import CFSG.RankThree.PartTwo.Sec18.SylowPlane
import CFSG.RankThree.PartTwo.Sec18.Transport
import CFSG.RankThree.PartTwo.Sec20.Contra
import CFSG.RankThree.PartTwo.Sec19.SimsTheoremCTI
import CFSG.RankThree.PartTwo.Sec19.O2Centralizer
public import CFSG.ClassicalInvolution.WeakCT.Main
public import CFSG.LieType.SeitzGeneration.OrthExLift
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ExcTwistedE6
public import CFSG.RankThree.PartOne.CTP.SeitzOrthModel
public import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
public import CFSG.RankThree.PartOne.CTP.StrongPFinal
public import CFSG.RankThree.PartTwo.KFacts.KS14SzLie

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late

namespace Item189QProof

variable {G : Type} [Group G] [Finite G]

theorem inSubgroup_theta_le_pPrimeCore (K : Subgroup G) :
    inSubgroup (aschbacherSolvableCore 3) K ≤ inSubgroup (CFSG.pPrimeCore 3) K := by
  obtain ⟨-, -, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥K) Nat.prime_three
  have : (aschbacherSolvableCore 3 ↥K).Normal := Subgroup.normal_of_characteristic _
  exact Subgroup.map_mono
    (le_sSup ⟨inferInstance, (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ3⟩)

theorem conj_eq_of_card_le_two {R : Subgroup G} (hR : Nat.card R ≤ 2) {g x : G}
    (hg : g ∈ Subgroup.normalizer (R : Set G)) (hx : x ∈ R) : g * x * g⁻¹ = x := by
  classical
  by_contra hne
  have hy : g * x * g⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hg x).mp hx
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hne (by group)
  have hy1 : g * x * g⁻¹ ≠ 1 := by
    intro h
    apply hx1
    have : x = g⁻¹ * (g * x * g⁻¹) * g := by group
    rw [this, h]
    group
  let f : Fin 3 → R := ![1, ⟨x, hx⟩, ⟨g * x * g⁻¹, hy⟩]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f, Subtype.ext_iff, eq_comm]
  have := Nat.card_le_card_of_injective f hf
  simp at this
  omega

end Item189QProof

section Certified


theorem step189Q_of (h1812 : Item181_2) (h184 : Item184_1) (h1842 : Item184_2)
    (h187 : Item187) : Step189Q := by
  intro G _ _ A M H c hH h7 hK hr hO2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set K := normalClosureIn M c with hKdef
  have hO3 := inSubgroup_pPrimeCore_normalClosureIn_eq_pCoreOf h1812 h184 h187 hH h7
  refine ⟨hO3, ?_⟩
  set P := CFSG.Open.pCoreOf 2 M with hPdef
  have hAM : A ≤ M := sec18Std_le hH.toSec18Std
  have hKM : K ≤ M := normalClosureIn_le_of_sec18H189 hH
  have hMK : M ≤ Subgroup.normalizer (K : Set G) := Sec20.le_normalizer_normalClosureIn M c
  have hMP : M ≤ Subgroup.normalizer (P : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M
  have hP2 : IsPGroup 2 P := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have hOK : CFSG.Open.pCoreOf 2 K ≤ P :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans hKM)
      (hMK.trans (Sec19.SimsTheoremC.normalizer_le_normalizer_pCoreOf K))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
  have hsimple : IsSimpleGroup (↥K ⧸ aschbacherSolvableCore 3 ↥K) := ktype_simple hK hr
  have hnab : ∃ a b : ↥K ⧸ aschbacherSolvableCore 3 ↥K, a * b ≠ b * a := by
    obtain ⟨-, -, a, b, hab⟩ := quasisimple_of_mem_thetaComponentsIn hK
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    refine ⟨a, b, fun h => hab ?_⟩
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h]
  have h3 : CFSG.Open.pRank 3 (⊤ : Subgroup (↥K ⧸ aschbacherSolvableCore 3 ↥K)) ≤ 1 :=
    (pRank_three_top_quotient_theta.trans
      ((CFSG.RankThreeCoreUniqueness.Helpers.pRank_subgroup_eq_internal_top 3 (by norm_num)
        K).symm.trans hr)).le
  have : IsSimpleGroup G := hH.isSimpleGroup
  have hMtop : M ≠ ⊤ :=
    ne_top_of_pCoreOf_ne_bot hH.nonabelian (pCoreOf_ne_bot_of_isMaximalTwoLocal hH.mem_scriptM.1)
  have hKtop : K ≠ ⊤ := ne_top_of_le_ne_top hMtop (mem_thetaComponentsIn_iff.mp hK).1
  have hKG : IsKGroup ↥K := (hH.toTheoremFourHyp.sectionFourHyp hKtop).kGroup
  obtain ⟨i, ⟨e⟩⟩ : Assembly.InCatalog (↥K ⧸ aschbacherSolvableCore 3 ↥K) :=
    KCore.KGroupAllSimple.catalogue_self (C := Assembly.InCatalog)
      Assembly.inCatalog_isoInvariant (hKG.quotient _)
  have hcat : CFSG.Open.IsCatalogGroup (↥K ⧸ aschbacherSolvableCore 3 ↥K) := ⟨i, ⟨e⟩⟩
  have hA := isE27_of_mem_partTwoE hH.mem_partTwoE
  obtain ⟨d, hdA, hd1, hdD⟩ :=
    Item189QProof.exists_mem_thetaQuotCentralizer_of_card hsimple hnab hcat h3 hA.1 hA.2
      (hAM.trans hMK)
  have hdM : d ∈ M := hAM hdA
  have hd3 : d ^ 3 = 1 := hA.1.2 d hdA
  have hc3 : c ^ 3 = 1 := by
    rw [← orderOf_eq_three_of_sec18H h184 hH]
    exact pow_orderOf_eq_one c
  obtain ⟨hcA, -⟩ := mem_and_commutator_mem_of_sec18H hH
  have hdnt : ∃ x ∈ P, d * x * d⁻¹ ≠ x := by
    by_contra hcon
    push Not at hcon
    have hM2 : CFSG.Open.IsTwoLocal M := (mem_scriptM_iff.mp hH.mem_scriptM).1.1
    have hdC : d ∈ M ⊓ Subgroup.centralizer (P : Set G) := by
      refine ⟨hdM, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
      have h := hcon x hx
      calc x * d = d * x * d⁻¹ * d := by rw [h]
        _ = d * x := by group
    have hdP : d ∈ P := hH.charTwoType M hM2 hdC
    obtain ⟨n, hn⟩ := hP2 ⟨d, hdP⟩
    have hn' : d ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have h1 : orderOf d ∣ 3 := orderOf_dvd_of_pow_eq_one hd3
    have h2 : orderOf d ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn'
    have h3' : orderOf d ∣ Nat.gcd 3 (2 ^ n) := Nat.dvd_gcd h1 h2
    have hcop : Nat.gcd 3 (2 ^ n) = 1 :=
      Nat.Coprime.pow_right n (by norm_num : Nat.Coprime 3 2)
    rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at h3'
    exact hd1 h3'
  have hθK : inSubgroup (aschbacherSolvableCore 3) K ≤ P :=
    (Item189QProof.inSubgroup_theta_le_pPrimeCore K).trans (hO3.le.trans hOK)
  have hdK : ∀ k ∈ K, d * k * d⁻¹ * k⁻¹ ∈ P := by
    intro k hk
    have h1 : k⁻¹ * (d * k * d⁻¹) ∈ P :=
      hθK ((Sec6.mem_thetaQuotCentralizer_iff.mp hdD).2 k hk)
    have h2 := (Subgroup.mem_normalizer_iff.mp (hMP (hKM hk)) _).mp h1
    have h3 : k * (k⁻¹ * (d * k * d⁻¹)) * k⁻¹ = d * k * d⁻¹ * k⁻¹ := by group
    rwa [h3] at h2
  have hcd : ∀ x ∈ P, c * x * c⁻¹ = x → d * x * d⁻¹ = x := by
    intro x hxP hxc
    have hR := card_pCoreOf_inf_centralizer_le_two189 h1812 h184 h1842 hH h7 hO2
    have hAC : A ≤ Subgroup.centralizer ({c} : Set G) := Sec19.le_centralizer_of_mem hA.1.1 hcA
    have hdN : d ∈ Subgroup.normalizer
        ((CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer ({c} : Set G) : Subgroup G) : Set G) :=
      Late.le_normalizer_inf (hAM.trans hMP) (hAC.trans Subgroup.le_normalizer) hdA
    have hxC : x ∈ Subgroup.centralizer ({c} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      calc y * x = y * x * y⁻¹ * y := by group
        _ = x * y := by rw [hxc]
    exact Item189QProof.conj_eq_of_card_le_two hR hdN ⟨hxP, hxC⟩
  exact Item189QProof.exists_rep_fpf_of_kernel hP2 (hKM.trans hMP) hOK
    (Sec20.self_mem_normalClosureIn M c) hc3 hd3 (hMP hdM) hdnt hdK hcd

end Certified

end CFSG.RankThree.PartTwo.Sec18
