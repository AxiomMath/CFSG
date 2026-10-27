module

public import CFSG.RankThree.PartOne.S9.OddCore.RecognitionCritical
public import CFSG.RankThree.PartTwo.Sec11.Item116R1StarDefs
public import CFSG.RankThree.PartTwo.Sec3.TwoGroupPrimeFiveAction
public import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical
public import CFSG.RankThree.PartTwo.Sec16.Item166Res2ProofSix
public import CFSG.RankThree.Coprime.InvolutionFixedRankBound
public import CFSG.RankThree.Coprime.ThompsonElementaryComplement
public import CFSG.RankThree.GroupTheory.SteinbergBMClassTwoExtraspecialAction
public import CFSG.Assembly.OrderReductions.FrattiniAutomorphisms
public import CFSG.Assembly.OrderReductions.FrattiniElementary
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core
public import CFSG.LinearAlgebra.OddSolvableUnitary.CommutatorForm
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.SignalizerFunctor.Maximality
public import CFSG.RankThree.PartOne.S9.OddCore.TorsionBridge
public import CFSG.RankThree.PartOne.S9.MinTwoAction.LiftingSelectedBase
public import CFSG.RankThree.PartTwo.Sec11.Item116R1StarMod
public import CFSG.RankThree.PartTwo.Sec11.Item116R1E1
public import CFSG.LocalAnalysis.SectionRank.AmbientRank
public import CFSG.Goldschmidt.Statements
public import CFSG.Goldschmidt.StatementsG2
public import CFSG.Goldschmidt.StatementsG3
public import CFSG.Goldschmidt.StatementsH
public import CFSG.Goldschmidt.Steps.G37Core
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
public import CFSG.RankThree.PartTwo.Sec11.Item116E2
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.SubnormalPSubgroupLeQCore
public import CFSG.Walter.Bender1970.S2
public import CFSG.Walter.Bender1970.S3.Basic
public import CFSG.Walter.Bender1970.S3.OStar
public import CFSG.Walter.PSL2Facts
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99

public section

section

open CFSG CFSG.SectionRank.Ccomm Subgroup
open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec11

theorem exists_critical_commutator_pow {G : Type*} [Group G] [Finite G] {a : G}
    (ha : IsPGroup 5 (zpowers a)) {R : Subgroup G} (hR2 : IsPGroup 2 R)
    (hRA : zpowers a ≤ normalizer (R : Set G)) (hcomm : ⁅R, zpowers a⁆ = R) (hRne : R ≠ ⊥) :
    ∃ T : Subgroup G, T ≤ R ∧ ThompsonCritical (T.subgroupOf R) ∧
      zpowers a ≤ normalizer (T : Set G) ∧ ⁅T, zpowers a⁆ ≠ ⊥ ∧
      ⁅⁅T, zpowers a⁆, zpowers a⁆ = ⁅T, zpowers a⁆ ∧
      zpowers a ≤ normalizer ((⁅T, zpowers a⁆ : Subgroup G) : Set G) ∧ ⁅T, zpowers a⁆ ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨T₀, hT₀⟩, hne⟩ := thompson_critical_subgroup (p := 2) (P := ↥R) hR2
  set T : Subgroup G := T₀.map R.subtype with hT
  have hTR : T ≤ R := Subgroup.map_subtype_le _
  have hTsub : T.subgroupOf R = T₀ :=
    Subgroup.comap_map_eq_self_of_injective R.subtype_injective T₀
  have hTcrit : ThompsonCritical (T.subgroupOf R) := hTsub ▸ hT₀
  have hAT : zpowers a ≤ Subgroup.normalizer (T : Set G) :=
    CFSG.RankThree.PartOne.OddCore37.le_normalizer_of_characteristic hRA hTR (hTsub ▸ hT₀.1)
  have h52 : Nat.Coprime 5 2 := (Nat.coprime_primes Nat.prime_five Nat.prime_two).2 (by norm_num)
  have hcop : Nat.Coprime 5 (Nat.card R) := by
    obtain ⟨k, hk⟩ := hR2.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k h52
  have hcopT : Nat.Coprime 5 (Nat.card T) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hTR) hcop
  have hTA : ⁅T, zpowers a⁆ ≠ ⊥ := by
    intro hbot
    have hAcT : zpowers a ≤ Subgroup.centralizer (T : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 (by rw [Subgroup.commutator_comm]; exact hbot)
    have hself : Subgroup.centralizer (T₀ : Set ↥R) ≤ T₀ := fun x hx => (hT₀.2.2.2 ▸ hx).1
    have hall : zpowers a ≤ Subgroup.centralizer (R : Set G) := by
      intro a' ha'
      have hcon : CFSG.RankThree.PartOne.OddCore37.conjHom (zpowers a) R hRA ⟨a', ha'⟩ = 1 := by
        obtain ⟨k', hk'⟩ := ha ⟨a', ha'⟩
        refine CFSG.ComponentClassification.CoprimeAutomorphisms.eq_one_of_self_centralizing
          2 hR2 T₀ hself _ (5 ^ k') ?_ (hcop.pow_left k') ?_
        · rw [← map_pow, hk', map_one]
        · intro x hx
          apply Subtype.ext
          have hxT : (x : G) ∈ T := ⟨x, hx, rfl⟩
          have h1 : (x : G) * a' = a' * x := Subgroup.mem_centralizer_iff.1 (hAcT ha') _ hxT
          change a' * x * a'⁻¹ = x
          rw [← h1]
          group
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      have h := congrArg (fun f : MulAut ↥R => ((f ⟨r, hr⟩ : ↥R) : G)) hcon
      change a' * r * a'⁻¹ = r at h
      calc r * a' = a' * r * a'⁻¹ * a' := by rw [h]
        _ = a' * r := by group
    have hbot' : ⁅R, zpowers a⁆ = ⊥ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 hall
    exact hRne (by rw [← hcomm, hbot'])
  exact ⟨T, hTR, hTcrit, hAT, hTA,
    CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_idempotent 5 Nat.prime_five
      (zpowers a) T ha hAT hcopT,
    CFSG.SignalizerFunctor.Helpers.normalized_commutator_normalized (zpowers a) T hAT,
    CFSG.SignalizerFunctor.Helpers.commutator_le_of_normalizing T (zpowers a) hAT⟩

end CFSG.RankThree.PartTwo.Sec11

end

section

open CFSG Subgroup
open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec11

theorem exists_critical_subgroup_fix {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) {P : Subgroup G} (hP : IsPGroup p P) (hPne : P ≠ ⊥) :
    ∃ D : Subgroup G, D ≤ P ∧ normalizer (P : Set G) ≤ normalizer (D : Set G) ∧
      (∀ d ∈ D, d ^ p = 1) ∧ (∀ a ∈ D, ∀ b ∈ D, ∀ c ∈ D, ⁅a, b⁆ * c = c * ⁅a, b⁆) ∧
      (∀ u ∈ normalizer (P : Set G), IsPGroup 2 (zpowers u) →
        u ∈ centralizer (D : Set G) → u ∈ centralizer (P : Set G)) := by
  have hnt : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).mpr hPne
  obtain ⟨D', hD'char, -, hD'comm, hD'exp, hD'fix⟩ :=
    CFSG.SectionRank.Ccomm.odd_critical_exponent_subgroup hp2 hP
  refine ⟨D'.map P.subtype, map_subtype_le D', ?_, ?_, ?_, ?_⟩
  · intro g hg
    apply CFSG.RankThree.PartTwo.Sec3.mem_normalizer_of_forall_conj_mem
    rintro _ ⟨d, hd, rfl⟩
    have h := Subgroup.characteristic_iff_map_eq.mp hD'char (P.normalizerMonoidHom ⟨g, hg⟩)
    have hσd : P.normalizerMonoidHom ⟨g, hg⟩ d ∈ D' := by
      rw [← h]
      exact mem_map_of_mem _ hd
    exact ⟨_, hσd, normalizerMonoidHom_apply_apply_coe _ _ _⟩
  · rintro _ ⟨d, hd, rfl⟩
    rw [← map_pow, hD'exp d hd, map_one]
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩
    have h := hD'comm (commutator_mem_commutator ha (mem_top b))
    have h2 := mem_centralizer_iff.mp h.2 c hc
    have h3 : ((c * ⁅a, b⁆ : P) : G) = ((⁅a, b⁆ * c : P) : G) := congrArg Subtype.val h2
    simp only [Subgroup.coe_mul, commutatorElement_def, Subgroup.coe_inv] at h3
    simp only [Subgroup.coe_subtype, commutatorElement_def]
    exact h3.symm
  · intro u hu hU2 huc
    have hσfix : P.normalizerMonoidHom ⟨u, hu⟩ ∈ fixingSubgroup (MulAut P) (D' : Set P) := by
      rw [mem_fixingSubgroup_iff]
      intro y hy
      apply Subtype.ext
      change ((P.normalizerMonoidHom ⟨u, hu⟩ y : P) : G) = y
      rw [normalizerMonoidHom_apply_apply_coe]
      have := mem_centralizer_iff.mp huc (y : G) ⟨y, hy, rfl⟩
      rw [← this, mul_inv_cancel_right]
    obtain ⟨k, hk⟩ := hD'fix ⟨_, hσfix⟩
    have hσk : P.normalizerMonoidHom ⟨u, hu⟩ ^ p ^ k = 1 := by
      have := congrArg Subtype.val hk
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
    obtain ⟨m, hm⟩ := hU2 ⟨u, mem_zpowers u⟩
    have hum : u ^ 2 ^ m = 1 := by
      have := congrArg Subtype.val hm
      simpa using this
    have hσm : P.normalizerMonoidHom ⟨u, hu⟩ ^ 2 ^ m = 1 := by
      rw [← map_pow]
      have : (⟨u, hu⟩ : normalizer (P : Set G)) ^ 2 ^ m = 1 := by
        apply Subtype.ext
        simpa using hum
      rw [this, map_one]
    have hdvd : orderOf (P.normalizerMonoidHom ⟨u, hu⟩) ∣ Nat.gcd (p ^ k) (2 ^ m) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hσk) (orderOf_dvd_of_pow_eq_one hσm)
    have hcop : Nat.Coprime (p ^ k) (2 ^ m) :=
      Nat.Coprime.pow k m ((Nat.coprime_primes hp.out Nat.prime_two).mpr hp2)
    rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at hdvd
    rw [mem_centralizer_iff]
    intro g hg
    have := congrArg (fun τ : MulAut P => ((τ ⟨g, hg⟩ : P) : G)) hdvd
    simp only [MulAut.one_apply] at this
    rw [normalizerMonoidHom_apply_apply_coe, mul_inv_eq_iff_eq_mul] at this
    exact this.symm

end CFSG.RankThree.PartTwo.Sec11

end

section

open Subgroup CFSG.RankThree.PartTwo.Sec3 CFSG.RankThree.PartTwo.Sec16.Proof166Res2
open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec11

variable {G : Type*} [Group G]

section Cases

variable [Finite G]

theorem n_eq_two_of_extraspecial_action_pow {p k : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {D : Type*} [Group D] [Finite D] (hD : IsPGroup p D)
    (hexp : ∀ x : D, x ^ p = 1) (hclass : commutator D ≤ Subgroup.center D)
    {S : Type*} [Group S] [Finite S] {n : ℕ} (hS : IsExtraspecialPGroup 2 S)
    (hcard : Nat.card S = 2 ^ (1 + 2 * n)) (hn : 1 ≤ n) {z : S}
    (hz : Subgroup.center S = zpowers z) (ρ : S →* MulAut D) (hρ : Function.Injective ρ)
    (hfix : ∀ s : S, s ≠ 1 → CFSG.pRank p (fixedSubgroupOf (ρ s)) ≤ 2)
    (γ : MulAut S) (hγq : γ ^ (5 ^ k) = 1)
    (hγfix : ∀ s, γ s * s⁻¹ ∈ Subgroup.center S → s ∈ Subgroup.center S) : n = 2 := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hbound := CFSG.RankThree.GroupTheory.SteinbergBM.class_two_extraspecial_action_bound hp2
    hD hexp hclass hS hcard hz ρ hρ (fun s hs => (hfix s hs).trans (by norm_num))
  have hn2 : n ≤ 2 := by
    by_contra h
    have hn3 : n = 3 := by have := hbound.1; omega
    obtain ⟨s, hs, hs2⟩ :=
      CFSG.RankThree.GroupTheory.SteinbergBM.exists_noncentral_involution hS hcard (by omega) hz
    have h3 := hbound.2.1 hn3 s hs hs2
    have hs1 : s ≠ 1 := fun h1 => hs (h1 ▸ one_mem _)
    have := hfix s hs1
    omega
  let ψ := CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism (Subgroup.center S)
  have hψ : ∀ s : S, ψ γ (s : S ⧸ Subgroup.center S) = ((γ s : S) : S ⧸ Subgroup.center S) :=
    fun s => CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism_apply _ γ s
  let Γ := zpowers (ψ γ)
  have hΓ : IsPGroup 5 Γ := isPGroup_zpowers_of_pow_eq_one (by rw [← map_pow, hγq, map_one])
  have h := hΓ.card_modEq_card_fixedPoints (S ⧸ Subgroup.center S)
  have hfp : Nat.card (MulAction.fixedPoints Γ (S ⧸ Subgroup.center S)) = 1 := by
    rw [Nat.card_eq_one_iff_exists]
    refine ⟨⟨1, fun g => map_one (g : MulAut (S ⧸ Subgroup.center S))⟩, fun ⟨c, hc⟩ =>
      Subtype.ext ?_⟩
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective c
    have h1 := hc ⟨ψ γ, mem_zpowers _⟩
    change ψ γ (s : S ⧸ Subgroup.center S) = (s : S ⧸ Subgroup.center S) at h1
    rw [hψ, QuotientGroup.eq] at h1
    change (s : S ⧸ Subgroup.center S) = 1
    rw [QuotientGroup.eq_one_iff]
    apply hγfix
    have h2 : γ s * s⁻¹ = s * ((γ s)⁻¹ * s)⁻¹ * s⁻¹ := by group
    rw [h2]
    exact Subgroup.Normal.conj_mem inferInstance _ (inv_mem h1) s
  rw [hfp] at h
  have hZ2 : Nat.card (Subgroup.center S) = 2 := hS.2.2.2
  have hquot : Nat.card (S ⧸ Subgroup.center S) = 2 ^ (2 * n) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center S)
    rw [hcard, hZ2, pow_add, pow_one] at h1
    omega
  rw [hquot] at h
  have hq1 : 5 ∣ 2 ^ (2 * n) - 1 := (Nat.modEq_iff_dvd' Nat.one_le_two_pow).mp h.symm
  interval_cases n
  · norm_num at hq1
  · rfl

theorem extraspecial_section_pow_struct {p k : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {P D U Z : Subgroup G} (hP : IsPGroup p P) (hDP : D ≤ P)
    (hDexp : ∀ d ∈ D, d ^ p = 1) (hDcl : ∀ a ∈ D, ∀ b ∈ D, ∀ c ∈ D, ⁅a, b⁆ * c = c * ⁅a, b⁆)
    (hUD : U ≤ normalizer (D : Set G)) {x : G} (hxD : x ∈ normalizer (D : Set G))
    (hxU : x ∈ normalizer (U : Set G)) (hxq : x ^ (5 ^ k) = 1) (hU2 : IsPGroup 2 U)
    (hZU : Z ≤ U) (hZc : ∀ z ∈ Z, ∀ v ∈ U, z * v = v * z) (hUUZ : ⁅U, U⁆ = Z)
    (hsqZ : ∀ u ∈ U, u ^ 2 ∈ Z) (hUZ : U ≠ Z) (hKZ : U ⊓ centralizer (D : Set G) ≤ Z)
    (hK2 : Nat.card Z = 2 * Nat.card ↥(U ⊓ centralizer (D : Set G)))
    (hcen : ∀ u ∈ U, (∀ v ∈ U, ⁅u, v⁆ ∈ centralizer (D : Set G)) → u ∈ Z)
    (hfpf : ∀ u ∈ U, x * u * x⁻¹ * u⁻¹ ∈ Z → u ∈ Z)
    (hfix : ∀ u ∈ U, u ≠ 1 →
      CFSG.Assembly.pRank p (P ⊓ centralizer ({u} : Set G)) ≤ 2) :
    U ⊓ centralizer (D : Set G) = ⊥ ∧ Nat.card U = 32 ∧ IsExtraspecialPGroup 2 U := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ := conjAction D U hUD with hφ
  set K := φ.ker with hK
  set S := U ⧸ K
  set π := QuotientGroup.mk' K with hπ
  set Z' := Z.subgroupOf U with hZ'
  have hmemK : ∀ u : U, u ∈ K ↔ (u : G) ∈ centralizer (D : Set G) := fun u => mem_ker_conjAction
  have hKZ' : K ≤ Z' := fun u hu => hKZ ⟨u.2, (hmemK u).mp hu⟩
  have hmemZ : ∀ w : U, π w ∈ Z'.map π → w ∈ Z' := by
    intro w ⟨z, hz, hzw⟩
    have h1 : z⁻¹ * w ∈ K := by
      rw [← QuotientGroup.eq]
      exact hzw
    have := Z'.mul_mem hz (hKZ' h1)
    rwa [mul_inv_cancel_left] at this
  have hS2 : IsPGroup 2 S := (hU2.to_quotient K)
  have hZS : Subgroup.center S = Z'.map π := by
    apply le_antisymm
    · intro s hs
      obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective K s
      refine ⟨u, ?_, rfl⟩
      show (u : G) ∈ Z
      apply hcen u u.2
      intro v hv
      have h1 := Subgroup.mem_center_iff.mp hs (π ⟨v, hv⟩)
      rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq, hmemK] at h1
      have : (((⟨v, hv⟩ * u : U)⁻¹ * (u * ⟨v, hv⟩) : U) : G) = ⁅(u : G)⁻¹, v⁻¹⁆ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
        group
      rw [this] at h1
      have h2 := (mem_normalizer_iff.mp
        (mem_normalizer_centralizer (hUD (mul_mem u.2 hv))) _).mp h1
      rwa [show (u : G) * v * ⁅(u : G)⁻¹, v⁻¹⁆ * ((u : G) * v)⁻¹ = ⁅(u : G), v⁆ by
        simp only [commutatorElement_def]; group] at h2
    · rintro _ ⟨z, hz, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro s
      obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective K s
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext ((hZc z hz v v.2).symm)
  have hcomU : commutator U = Z' := by
    apply map_injective U.subtype_injective
    rw [_root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype, hUUZ,
      subgroupOf_map_subtype, inf_of_le_left hZU]
  have hcomS : commutator S = Z'.map π := by
    rw [← hcomU, _root_.commutator_def, _root_.commutator_def, map_commutator,
      map_top_of_surjective _ (QuotientGroup.mk'_surjective K)]
  have hfrS : frattini S = Z'.map π := by
    have : Fact (IsPGroup 2 S) := ⟨hS2⟩
    apply le_antisymm
    · rw [CFSG.frattini_eq_closure_commutator_union_powers (p := 2), closure_le]
      rintro s (hs | ⟨t, rfl⟩)
      · rw [← hcomS]
        exact hs
      · obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective K t
        refine ⟨u ^ 2, ?_, by rw [map_pow]⟩
        show ((u ^ 2 : U) : G) ∈ Z
        rw [Subgroup.coe_pow]
        exact hsqZ _ u.2
    · rw [← hcomS]
      exact CFSG.OrderReductions.FrattiniElementary.commutator_le_frattini 2 hS2
  have hcardZS : Nat.card (Subgroup.center S) = 2 := by
    rw [hZS, ← relIndex_ker, QuotientGroup.ker_mk']
    have h := relIndex_mul_card (H := K) (K := Z')
    rw [inf_of_le_left hKZ'] at h
    have hZ'c : Nat.card Z' = Nat.card Z := Nat.card_congr (subgroupOfEquivOfLe hZU).toEquiv
    have hKc : Nat.card K = Nat.card ↥(U ⊓ centralizer (D : Set G)) := by
      refine Nat.card_congr ?_
      exact
        { toFun := fun k => ⟨(k : U), (k : U).2, (hmemK k).mp k.2⟩
          invFun := fun g => ⟨⟨g, g.2.1⟩, (hmemK _).mpr g.2.2⟩
          left_inv := fun k => rfl
          right_inv := fun g => rfl }
    rw [hZ'c, hK2, hKc] at h
    have hpos : 0 < Nat.card ↥(U ⊓ centralizer (D : Set G)) := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos h
  have hZcom : Subgroup.center S = commutator S := hZS.trans hcomS.symm
  have hSx : IsExtraspecialPGroup 2 S :=
    ⟨hS2, hZcom.symm, hfrS.trans hZS.symm, hcardZS⟩
  obtain ⟨n, hn⟩ : ∃ n : ℕ, Nat.card S = 2 ^ (1 + 2 * n) := by
    obtain ⟨ε⟩ := CFSG.OddSolvableUnitary.nonempty_center_mulEquiv hcardZS
    let _ : Module (ZMod 2) (Additive (Abelianization S)) := AddCommGroup.zmodModule fun v => by
      obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
      change Additive.ofMul ((Abelianization.of t) ^ 2) = Additive.ofMul 1
      congr 1
      rw [← map_pow, ← MonoidHom.mem_ker, Abelianization.ker_of, hcomS]
      obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective K t
      refine ⟨u ^ 2, ?_, by rw [map_pow]⟩
      show ((u ^ 2 : U) : G) ∈ Z
      rw [Subgroup.coe_pow]
      exact hsqZ _ u.2
    obtain ⟨B, hBa, hBn, -⟩ := CFSG.OddSolvableUnitary.exists_commForm hZcom ε
    have : Finite (Additive (Abelianization S)) :=
      Finite.of_surjective (fun x : S => Additive.ofMul (Abelianization.of x))
        fun v => QuotientGroup.mk_surjective (Additive.toMul v)
    have : Module.Finite (ZMod 2) (Additive (Abelianization S)) := Module.Finite.of_finite
    obtain ⟨a, ha⟩ := LinearMap.BilinForm.IsAlt.even_finrank (K := ZMod 2) hBa hBn
    refine ⟨a, ?_⟩
    rw [CFSG.OddSolvableUnitary.card_eq_card_abelianization_mul hZcom hcardZS]
    change Nat.card (Additive (Abelianization S)) * 2 = _
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, ha, ← two_mul, pow_add,
      pow_one, mul_comm]
  have hn1 : 1 ≤ n := by
    by_contra h
    have hn0 : n = 0 := by omega
    rw [hn0, mul_zero, add_zero, pow_one] at hn
    have htop : Subgroup.center S = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (hcardZS.trans hn.symm)
    apply hUZ
    refine le_antisymm (fun u hu => ?_) hZU
    have h := hmemZ ⟨u, hu⟩ (by rw [← hZS, htop]; exact mem_top _)
    exact h
  obtain ⟨z, hz⟩ : ∃ z : S, Subgroup.center S = zpowers z := by
    have : IsCyclic (Subgroup.center S) := isCyclic_of_prime_card hcardZS
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Subgroup.center S)
    refine ⟨g, le_antisymm (fun s hs => ?_) (zpowers_le.mpr g.2)⟩
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hg ⟨s, hs⟩)
    exact mem_zpowers_iff.mpr ⟨k, by
      have := congrArg Subtype.val hk
      simpa using this⟩
  let ρ : S →* MulAut D := QuotientGroup.kerLift φ
  have hρ : Function.Injective ρ := QuotientGroup.kerLift_injective φ
  have hfixS : ∀ s : S, s ≠ 1 → CFSG.pRank p (fixedSubgroupOf (ρ s)) ≤ 2 := by
    intro s hs
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective s
    have hu : (u : G) ∉ centralizer (D : Set G) := fun h =>
      hs ((QuotientGroup.eq_one_iff u).mpr (mem_ker_conjAction.mpr h))
    change CFSG.pRank p (fixedSubgroupOf (QuotientGroup.kerLift φ (u : U ⧸ φ.ker))) ≤ 2
    rw [QuotientGroup.kerLift_mk]
    exact (pRank_fixedSubgroupOf_le hp.out.one_lt hDP u).trans (hfix u u.2 (fun h1 => hu (h1 ▸ one_mem _)))
  let γ : MulAut S := conjQuot hUD hxD hxU
  have hγfix : ∀ s, γ s * s⁻¹ ∈ Subgroup.center S → s ∈ Subgroup.center S := by
    intro s hs
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective s
    obtain ⟨hu, he⟩ := conjQuot_mk hUD hxD hxU u
    change conjQuot hUD hxD hxU (u : U ⧸ φ.ker) * _ ∈ _ at hs
    rw [he, hZS, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul] at hs
    have h1 := hmemZ _ hs
    rw [mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at h1
    have h2 := hfpf u u.2 h1
    rw [hZS]
    exact ⟨u, h2, rfl⟩
  have hDp : IsPGroup p D := hP.to_le hDP
  have hDexp' : ∀ d : D, d ^ p = 1 := fun d =>
    Subtype.ext (by rw [Subgroup.coe_pow, hDexp d d.2, Subgroup.coe_one])
  have hclassD : commutator D ≤ Subgroup.center D := commutator_le_center_of_forall hDcl
  have hn2 : n = 2 := n_eq_two_of_extraspecial_action_pow hp2 hDp hDexp' hclassD hSx hn hn1 hz ρ hρ
    hfixS γ (conjQuot_pow_eq_one hUD hxD hxU hxq) hγfix
  subst hn2
  have hcard32 : Nat.card S = 32 := by rw [hn]; norm_num
  have hγ5 : γ ^ 5 = 1 := pow_five_eq_one_of_fpf hSx hcard32 γ (conjQuot_pow_eq_one hUD hxD hxU hxq) hγfix
  obtain ⟨hcardfrat, hrank3⟩ := ext32_module_data hp2 hDp hDexp' hclassD hSx hcard32 γ hγ5 hγfix ρ hρ hfixS
  have hK1 : U ⊓ centralizer (D : Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro k hk
    by_contra hk1
    have hk1' : k ≠ 1 := fun h => hk1 (by rw [h]; exact one_mem _)
    have h2 := hfix k hk.1 hk1'
    have hle : D ≤ P ⊓ centralizer ({k} : Set G) := fun d hd =>
      ⟨hDP hd, mem_centralizer_singleton_iff.2 ((mem_centralizer_iff.1 hk.2) d hd)⟩
    have h3 : CFSG.Open.pRank p D ≤ CFSG.Open.pRank p (P ⊓ centralizer ({k} : Set G)) :=
      CFSG.SectionRank.pRank_mono hp.out.one_lt hle
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank] at hrank3
    rw [r116_assembly_pRank_eq, CFSG.SectionRank.pRank_coe_eq_openPRank] at h2
    omega
  have hKbot : K = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    have : (u : G) ∈ U ⊓ centralizer (D : Set G) := ⟨u.2, (hmemK u).mp hu⟩
    rw [hK1, mem_bot] at this
    exact (Subgroup.mem_bot).2 (Subtype.ext this)
  have hinj : Function.Injective π := by
    rw [← MonoidHom.ker_eq_bot_iff, hπ, QuotientGroup.ker_mk']
    exact hKbot
  let e : U ≃* S := MulEquiv.ofBijective π ⟨hinj, QuotientGroup.mk'_surjective K⟩
  refine ⟨hK1, ?_, ?_⟩
  · rw [Nat.card_congr e.toEquiv]
    exact hcard32
  · exact CFSG.RankThree.PartOne.Lifting36.isExtraspecialPGroup_of_mulEquiv e.symm hSx

theorem inSubgroup_center_eq_of_central {U Z D : Subgroup G} (hZU : Z ≤ U)
    (hZc : ∀ z ∈ Z, ∀ v ∈ U, z * v = v * z)
    (hcen : ∀ u ∈ U, (∀ v ∈ U, ⁅u, v⁆ ∈ centralizer (D : Set G)) → u ∈ Z) :
    CFSG.inSubgroup Subgroup.center U = Z := by
  ext g
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine hcen c c.2 (fun v hv => ?_)
    have h1 : (⟨v, hv⟩ : U) * c = c * ⟨v, hv⟩ := (Subgroup.mem_center_iff.mp hc ⟨v, hv⟩)
    have h2 : v * (c : G) = (c : G) * v := congrArg Subtype.val h1
    have : ⁅(c : G), v⁆ = 1 := by
      rw [commutatorElement_def, ← h2]
      group
    rw [this]
    exact one_mem _
  · intro hg
    have hmem : (⟨g, hZU hg⟩ : U) ∈ Subgroup.center U := by
      rw [Subgroup.mem_center_iff]
      intro v
      exact Subtype.ext (hZc g hg v v.2).symm
    exact ⟨⟨g, hZU hg⟩, hmem, rfl⟩

theorem exists_extraspecial_below {G : Type*} [Group G] [Finite G] {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hq : q.Prime) (hq3 : 3 < q) (hq5 : q = 5) {P U X : Subgroup G} {x : G} (hP : IsPGroup p P)
    (hU : IsPGroup 2 U) (hXx : X = zpowers x) (hX : IsPGroup q X) (hUX : ⁅U, X⁆ = U)
    (hU1 : U ≠ ⊥) (hUP : U ≤ normalizer (P : Set G)) (hXP : X ≤ normalizer (P : Set G))
    (hfaith : U ⊓ centralizer (P : Set G) = ⊥)
    (hfix : ∀ u ∈ U, u ≠ 1 → CFSG.Assembly.pRank p (P ⊓ centralizer ({u} : Set G)) ≤ 2) :
    ∃ U₀ : Subgroup G, U₀ ≤ U ∧ x ∈ normalizer (U₀ : Set G) ∧ ⁅U₀, zpowers x⁆ = U₀ ∧ U₀ ≠ ⊥ ∧
      IsExtraspecialPGroup 2 U₀ ∧ Nat.card U₀ = 32 ∧
      (∀ u ∈ U₀, x * u * x⁻¹ * u⁻¹ ∈ CFSG.inSubgroup Subgroup.center U₀ →
        u ∈ CFSG.inSubgroup Subgroup.center U₀) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact q.Prime := ⟨hq⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq2 : q ≠ 2 := by omega
  have hxX : x ∈ X := hXx ▸ mem_zpowers x
  obtain ⟨k, hk⟩ := hX ⟨x, hxX⟩
  have hxq : x ^ (q ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  obtain ⟨U₀, ⟨hU₀U, hU₀X, hU₀1⟩, hU₀min⟩ := (wellFounded_lt (α := Subgroup G)).has_min
    {V | V ≤ U ∧ ⁅V, X⁆ = V ∧ V ≠ ⊥} ⟨U, le_rfl, hUX, hU1⟩
  have hmin : ∀ V ≤ U₀, ⁅V, X⁆ = V → V ≠ ⊥ → V = U₀ := fun V hV hVX hV1 =>
    by_contra fun hne => hU₀min V ⟨hV.trans hU₀U, hVX, hV1⟩ (lt_of_le_of_ne hV hne)
  have hU₀2 : IsPGroup 2 U₀ := hU.to_le hU₀U
  have hXU₀ : X ≤ normalizer (U₀ : Set G) := by
    rw [← hU₀X]
    exact normalizer_commutator_ge_right U₀ X
  obtain ⟨D, hDP, hND, hDexp, hDcl, hDfaith⟩ := exists_critical_subgroup hp2 hP hU hUP hfaith hU1
  have hU₀D : U₀ ≤ normalizer (D : Set G) := (hU₀U.trans hUP).trans hND
  have hxD : x ∈ normalizer (D : Set G) := hND (hXP hxX)
  have hxU₀ : x ∈ normalizer (U₀ : Set G) := hXU₀ hxX
  have hfaith₀ : ∀ u ∈ U₀, u ∈ centralizer (D : Set G) → u = 1 := fun u hu hc => by
    have : u ∈ U ⊓ centralizer (D : Set G) := ⟨hU₀U hu, hc⟩
    rwa [hDfaith, mem_bot] at this
  have hfix₀ : ∀ D₀ : Subgroup G, ∀ u ∈ U₀, u ∉ centralizer (D₀ : Set G) →
      CFSG.Assembly.pRank p (P ⊓ centralizer ({u} : Set G)) ≤ 2 := fun D₀ u hu hc =>
    hfix u (hU₀U hu) (fun h => hc (h ▸ one_mem _))
  have hfpf : ∀ u ∈ U₀, x * u * x⁻¹ * u⁻¹ ∈ squares U₀ → u ∈ squares U₀ := fun u hu h =>
    mem_squares_of_conj_mul_inv_mem_pow hq hq2 hXx hX hU₀2 hXU₀ hU₀X hu h
  by_cases hab : ∀ a ∈ U₀, ∀ b ∈ U₀, a * b = b * a
  ·
    exfalso
    have hsq1 : ∀ u ∈ U₀, u ^ 2 = 1 := fun u hu =>
      sq_eq_one_of_commute hq hq2 hX hU₀2 hXU₀ hU₀X hU₀1 hmin hab hu
    have hF : squares U₀ = ⊥ := by
      rw [eq_bot_iff, squares, closure_le]
      rintro _ ⟨w, hw, rfl⟩
      rw [hsq1 w hw]
      exact one_mem _
    refine false_of_elemAbelian_section_pow hp2 hq hq3 hP hDP hDexp hDcl hU₀D hxD hxU₀ hxq ?_ ?_
      ?_ ?_ (hfix₀ D)
    · intro a ha b hb
      rw [commutatorElement_eq_one_iff_mul_comm.mpr (hab a ha b hb)]
      exact one_mem _
    · intro a ha
      rw [hsq1 a ha]
      exact one_mem _
    · by_contra h
      push Not at h
      apply hU₀1
      rw [eq_bot_iff]
      intro u hu
      rw [mem_bot]
      exact hfaith₀ u hu (h u hu)
    · intro u hu hc
      have hw : x * u * x⁻¹ * u⁻¹ ∈ U₀ :=
        mul_mem ((mem_normalizer_iff.mp hxU₀ u).mp hu) (inv_mem hu)
      have h2 := hfpf u hu (by rw [hfaith₀ _ hw hc]; exact one_mem _)
      rw [hF, mem_bot] at h2
      rw [h2]
      exact one_mem _
  ·
    set Z := squares U₀ with hZdef
    have hZU₀ : Z ≤ U₀ := squares_le U₀
    have hZc : ∀ z ∈ Z, ∀ v ∈ U₀, z * v = v * z := fun z hz v hv =>
      squares_commute hq hq2 hX hU₀2 hXU₀ hU₀X hU₀1 hmin hz hv
    have hUUZ : ⁅U₀, U₀⁆ = Z := commutator_eq_squares hq hq2 hX hU₀2 hXU₀ hU₀X hU₀1 hmin
    have hZ2 : ∀ z ∈ Z, z ^ 2 = 1 := fun z hz =>
      sq_eq_one_of_mem_squares hq hq2 hX hU₀2 hXU₀ hU₀X hU₀1 hmin hz
    have hZne : Z ≠ U₀ := squares_ne hU₀2 hU₀1
    have hxZ : ∀ z ∈ Z, x * z * x⁻¹ = z := fun z hz =>
      conj_eq_of_mem_squares hq hq2 hX hU₀2 hXU₀ hU₀1 hmin hxX hz
    have hZbot : Z ≠ ⊥ := fun h => hab fun a ha b hb => by
      have : ⁅a, b⁆ ∈ ⁅U₀, U₀⁆ := commutator_mem_commutator ha hb
      rwa [hUUZ, h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    obtain ⟨r, hr⟩ := (hU₀2.to_le hZU₀).exists_card_eq
    have hr1 : 1 ≤ r := by
      rcases Nat.eq_zero_or_pos r with h | h
      · rw [h, pow_zero, card_eq_one] at hr
        exact absurd hr hZbot
      · exact h
    have hZel : CFSG.Open.IsElemAbelian 2 Z :=
      ⟨⟨⟨fun a b => Subtype.ext (hZc a a.2 b (hZU₀ b.2))⟩⟩, hZ2⟩
    have hcopD : Nat.Coprime 2 (Nat.card D) := by
      obtain ⟨k, hk⟩ := (hP.to_le hDP).exists_card_eq
      rw [hk]
      exact Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_two hp).mpr hp2.symm)
    have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2
      (r - 1) Nat.prime_two Z D hZel (by rw [hr, show r - 1 + 1 = r by omega])
      (hZU₀.trans hU₀D) hcopD
    obtain ⟨Z₀, ⟨hZ₀Z, hZ₀card⟩, hZ₀act⟩ : ∃ Z₀ ∈ CFSG.Open.signalizerFunctorEk 2 (r - 1) Z,
        ¬ U₀ ≤ centralizer ((D ⊓ centralizer (Z₀ : Set G) : Subgroup G) : Set G) := by
      by_contra h
      push Not at h
      apply hU₀1
      have hle : D ≤ centralizer (U₀ : Set G) := by
        rw [← hgen]
        exact iSup₂_le fun Z₀ hZ₀ => (le_centralizer_iff.mp (h Z₀ hZ₀))
      rw [eq_bot_iff]
      intro u hu
      rw [mem_bot]
      exact hfaith₀ u hu (le_centralizer_iff.mp hle hu)
    set D₀ := D ⊓ centralizer (Z₀ : Set G) with hD₀
    have hD₀P : D₀ ≤ P := inf_le_left.trans hDP
    have hU₀D₀ : U₀ ≤ normalizer (D₀ : Set G) := fun u hu =>
      mem_normalizer_inf (hU₀D hu) (mem_normalizer_centralizer (mem_normalizer_of_forall_commute
        fun z hz => (hZc z (hZ₀Z hz) u hu).symm))
    have hxD₀ : x ∈ normalizer (D₀ : Set G) :=
      mem_normalizer_inf hxD (mem_normalizer_centralizer (mem_normalizer_of_forall_commute
        fun z hz => by
          have := hxZ z (hZ₀Z hz)
          calc x * z = x * z * x⁻¹ * x := by group
            _ = z * x := by rw [this]))
    set K := U₀ ⊓ centralizer (D₀ : Set G) with hKdef
    have hKne : K ≠ U₀ := fun h => hZ₀act (h ▸ inf_le_right)
    have hXK : X ≤ normalizer (K : Set G) := by
      intro y hy
      have hyZ₀ : ∀ z ∈ Z₀, y * z = z * y := fun z hz => by
        have := conj_eq_of_mem_squares hq hq2 hX hU₀2 hXU₀ hU₀1 hmin hy (hZ₀Z hz)
        calc y * z = y * z * y⁻¹ * y := by group
          _ = z * y := by rw [this]
      exact mem_normalizer_inf (hXU₀ hy) (mem_normalizer_centralizer (mem_normalizer_inf
        (hND (hXP hy)) (mem_normalizer_centralizer (mem_normalizer_of_forall_commute hyZ₀))))
    have hKX := commutator_eq_bot_of_ne hq hq2 hX hU₀2 hmin inf_le_left hXK hKne
    have hKZ : K ≤ Z := fun k hk => hfpf k hk.1 (by
      have : ⁅k, x⁆ ∈ ⁅K, X⁆ := commutator_mem_commutator hk hxX
      rw [hKX, mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      rw [← this, mul_inv_cancel_right, mul_inv_cancel]
      exact one_mem _)
    have hZ₀K : Z₀ ≤ K := fun z hz => ⟨hZU₀ (hZ₀Z hz), mem_centralizer_iff.mpr fun d hd =>
      (mem_centralizer_iff.mp hd.2 z hz).symm⟩
    have hKcard : Nat.card K = 2 ^ (r - 1) ∨ Nat.card K = 2 ^ r := by
      have h1 : Nat.card Z₀ ∣ Nat.card K := card_dvd_of_le hZ₀K
      have h2 : Nat.card K ∣ Nat.card Z := card_dvd_of_le hKZ
      rw [hZ₀card] at h1
      rw [hr] at h2
      obtain ⟨j, hj, hjK⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
      rw [hjK] at h1
      have : r - 1 ≤ j := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h1
      rcases (show j = r - 1 ∨ j = r by omega) with h | h
      · left
        rw [hjK, h]
      · right
        rw [hjK, h]
    rcases hKcard with hK1 | hK2
    ·
      have hKZ₀ : K = Z₀ := (eq_of_le_of_card_ge hZ₀K (by rw [hK1, hZ₀card])).symm
      have hZ₀ne : Z₀ ≠ Z := fun h => by
        have := congrArg (fun H : Subgroup G => Nat.card H) h
        simp only [hZ₀card, hr] at this
        have := Nat.pow_right_injective (le_refl 2) this
        omega
      have hxq5 : x ^ (5 ^ k) = 1 := by rw [← hq5]; exact hxq
      have hKcard' : Nat.card Z = 2 * Nat.card ↥(U₀ ⊓ centralizer (D₀ : Set G)) := by
        rw [hr, hK1, ← pow_succ']
        congr 1
        omega
      have hcen₀ : ∀ u ∈ U₀, (∀ v ∈ U₀, ⁅u, v⁆ ∈ centralizer (D₀ : Set G)) → u ∈ Z := by
        intro u hu hc
        apply mem_squares_of_commutator_mem_pow hq hq2 hXx hX hU₀2 hXU₀ hU₀X hU₀1 hmin hZ₀Z
          hZ₀ne hu
        intro v hv
        have : ⁅u, v⁆ ∈ K :=
          ⟨le_normalizer_iff_commutator_le_left.mp le_normalizer
            (commutator_mem_commutator hu hv), hc v hv⟩
        rwa [hKZ₀] at this
      obtain ⟨hKbot, hcard32, hext⟩ := extraspecial_section_pow_struct hp2 hP hD₀P
        (fun d hd => hDexp d hd.1) (fun a ha b hb c hc => hDcl a ha.1 b hb.1 c hc.1) hU₀D₀ hxD₀
        hxU₀ hxq5 hU₀2 hZU₀ hZc hUUZ (fun u hu => sq_mem_squares hu) hZne.symm hKZ hKcard' hcen₀
        hfpf (fun u hu h1 => hfix u (hU₀U hu) h1)
      refine ⟨U₀, hU₀U, hxU₀, ?_, hU₀1, hext, hcard32, ?_⟩
      · rw [← hXx]
        exact hU₀X
      have hcenter : CFSG.inSubgroup Subgroup.center U₀ = Z :=
        inSubgroup_center_eq_of_central hZU₀ hZc hcen₀
      intro u hu hmem
      rw [hcenter] at hmem ⊢
      exact hfpf u hu hmem
    ·
      exfalso
      have hKZeq : K = Z := eq_of_le_of_card_ge hKZ (by rw [hK2, hr])
      refine false_of_elemAbelian_section_pow hp2 hq hq3 hP hD₀P (fun d hd => hDexp d hd.1)
        (fun a ha b hb c hc => hDcl a ha.1 b hb.1 c hc.1) hU₀D₀ hxD₀ hxU₀ hxq ?_ ?_ ?_ ?_
        (hfix₀ D₀)
      · intro a ha b hb
        have : ⁅a, b⁆ ∈ K := by
          rw [hKZeq, ← hUUZ]
          exact commutator_mem_commutator ha hb
        exact this.2
      · intro a ha
        have : a ^ 2 ∈ K := by
          rw [hKZeq]
          exact sq_mem_squares ha
        exact this.2
      · by_contra h
        push Not at h
        exact hZ₀act fun u hu => h u hu
      · intro u hu hc
        have hw : x * u * x⁻¹ * u⁻¹ ∈ K := Subgroup.mem_inf.mpr
          ⟨mul_mem ((mem_normalizer_iff.mp hxU₀ u).mp hu) (inv_mem hu), hc⟩
        rw [hKZeq] at hw
        have := hfpf u hu hw
        rw [← hKZeq] at this
        exact this.2


end Cases

end CFSG.RankThree.PartTwo.Sec11

end
