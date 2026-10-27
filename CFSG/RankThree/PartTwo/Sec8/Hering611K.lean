module

public import CFSG.RankThree.PartTwo.Sec8.Hering611Defs
public import CFSG.RankThree.PartTwo.Sec8.Hering611Frame
public import CFSG.RankThree.PartTwo.Sec6.Item611Res7ProofKField
public import CFSG.RankThree.PartTwo.Sec6.Item611Res6ProofFieldD
public import CFSG.RankThree.PartTwo.Sec6.Item611Res6ProofField
import CFSG.RankThree.PartTwo.Sec6.Item611Res4ProofUPlusTools
import CFSG.RankThree.PartTwo.Sec12.Item125Act
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Center
import CFSG.RankThree.PartTwo.Sec6.Item611Res3ProofTools
import CFSG.RankThree.PartTwo.Sec6.Item612Local
import CFSG.RankThree.PartTwo.Sec6.Item612Basic
import CFSG.RankThree.PartTwo.Sec6.Item612Core
import CFSG.RankThree.PartTwo.Sec6.Item612
import CFSG.RankThree.PartTwo.Sec6.Item64
import CFSG.RankThree.PartTwo.Sec6.Item65Tools
import CFSG.RankThree.PartTwo.Sec11.Item112
import CFSG.RankThree.PartTwo.Sec11.Item119K
import CFSG.RankThree.PartTwo.Sec11.FieldCentRigidProof
import CFSG.RankThree.PartTwo.KFacts.K72FixL2
import CFSG.RankThree.PartTwo.KFacts.AutKindsUnique
import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverRanks
import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
import CFSG.RankThree.GroupTheory.ThetaQuotientTransport
import CFSG.RankThree.GroupTheory.SteinbergBYHyperplaneResidual
import CFSG.LocalAnalysis.RankThreeEvenClassification.InvariantSylow
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.Coprime.ThompsonElementaryComplement
import CFSG.RankThree.PartOne.S11c.CentralWitness
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.RankThree.PartTwo.Sec11.Theorem1134
public import CFSG.RankThree.PartTwo.Sec21.Item21Late2ProofList
public import CFSG.RankThree.PartTwo.Sec4.Item47CasesExc
public import CFSG.RankThree.PartTwo.Sec6.Item611Res7ProofKStar
public import CFSG.RankThree.PartTwo.Sec6.Item611Res7ProofSK
public import CFSG.RankThree.PartTwo.Sec8.Item812Res12ProofPSL2
public import CFSG.RankThree.PartTwo.Sec8.Item86ResProofTwo
public import CFSG.RankThree.PartTwo.Sec8.Steps
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
import CFSG.RankThree.LocalRank.SelectorCases
import CFSG.RankThree.PartOne.Assembly
import CFSG.RankThree.PartTwo.KFacts.KS12MovesSL
import CFSG.RankThree.PartTwo.Sec11.Item118
import CFSG.RankThree.PartTwo.Sec4.Statements423
import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent

public section

namespace CFSG.RankThree.PartTwo.Sec6.Hering611

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL)

open CFSG.RankThree.PartTwo.Sec8.Hering611
open scoped commutatorElement

section Certs

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L E T : Subgroup G} {d a : G}

theorem fieldCent_facts_two {L : Subgroup G} {d : G}
    (φ : L ⧸ aschbacherSolvableCore 3 L ≃* projSL 2 (GaloisField 3 (3 * 2)))
    (hdF : KFacts.InducesStdKind L d .field) (hd3 : d ^ 3 = 1) :
    ∃ hdN : d ∈ Subgroup.normalizer (L : Set G),
      IsQuasisimple ((Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨d, hdN⟩)).toMonoidHom.eqLocus
        (MonoidHom.id (L ⧸ aschbacherSolvableCore 3 L))) ∧
      Subgroup.center ((Sec4.thetaQuotMulAut L
        (Sec4.compAction L ⟨d, hdN⟩)).toMonoidHom.eqLocus
          (MonoidHom.id (L ⧸ aschbacherSolvableCore 3 L))) = ⊥ := by
  obtain ⟨hdN, hnot⟩ := KFacts.InducesStdKind.inducesOuterTheta L hdF (by decide)
  set α := Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨d, hdN⟩) with hα
  have hα3 : α ^ 3 = 1 := by
    have h1 : (⟨d, hdN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hd3)
    rw [hα, ← map_pow, ← map_pow, h1, map_one, map_one]
  have hcard : Nat.card (GaloisField 3 (3 * 2)) = (3 ^ 2) ^ 3 := by
    rw [GaloisField.card 3 (3 * 2) (by omega), ← pow_mul, mul_comm]
  have hq : 4 ≤ 3 ^ 2 := by norm_num
  obtain ⟨hZ, hQ, -, -⟩ := KFacts.fixedPoints_facts_of_mulEquiv_psl2
    (φ.trans (Sec4.projSLEquivPSL (GaloisField 3 (3 * 2)))) hq hcard hα3 hnot
  exact ⟨hdN, hQ, hZ⟩

theorem exists_elemAbelian_le_sec11K_two {L : Subgroup G} {d : G}
    (φ : L ⧸ aschbacherSolvableCore 3 L ≃* projSL 2 (GaloisField 3 (3 * 2)))
    (hdF : KFacts.InducesStdKind L d .field) (hd3 : d ^ 3 = 1) :
    ∃ F₀ : Subgroup G, F₀ ≤ Sec11.sec11K L d ∧ CFSG.Assembly.IsElemAbelian 3 F₀ ∧
      9 ≤ Nat.card F₀ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hdN, hnot⟩ := KFacts.InducesStdKind.inducesOuterTheta L hdF (by decide)
  set α := Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨d, hdN⟩) with hα
  have hα3 : α ^ 3 = 1 := by
    have h1 : (⟨d, hdN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hd3)
    rw [hα, ← map_pow, ← map_pow, h1, map_one, map_one]
  have hcard : Nat.card (GaloisField 3 (3 * 2)) = (3 ^ 2) ^ 3 := by
    rw [GaloisField.card 3 (3 * 2) (by omega), ← pow_mul, mul_comm]
  have hq : 4 ≤ 3 ^ 2 := by norm_num
  set ψ := φ.trans (Sec4.projSLEquivPSL (GaloisField 3 (3 * 2))) with hψ
  obtain ⟨hZ, hQ, -, -⟩ := KFacts.fixedPoints_facts_of_mulEquiv_psl2 ψ hq hcard hα3 hnot
  set β := MulAut.congr ψ α with hβ
  have hβ3 : β ^ 3 = 1 := by rw [hβ, ← map_pow, hα3, map_one]
  have hβout : ¬ KFacts.IsInnerAut β := by rwa [hβ, KFacts.isInnerAut_congr]
  obtain ⟨σ, hσ3, ⟨e⟩⟩ := KFacts.exists_eqLocus_mulEquiv_psl2 hβ3 hβout
  have hσcard : Nat.card (GH74.GLS.IVK.fixedField σ) = 3 ^ 2 :=
    KFacts.card_fixedField_of_orderOf_eq_three hσ3 hcard
  have hp : ∀ x : GH74.GLS.IVK.fixedField σ, (3 : ℕ) • x = 0 := by
    intro x
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_nsmul, ZeroMemClass.coe_zero, nsmul_eq_mul, CharP.cast_eq_zero,
      zero_mul]
  have h1 : 2 ≤ CFSG.pRank 3 (projSL 2 (GH74.GLS.IVK.fixedField σ)) :=
    Res611Res7.le_pRank_projSL_two_of_card hp hσcard
  obtain ⟨e1⟩ := Sec11.nonempty_sec11K_quotient_mulEquiv hdN hd3 hQ hZ
  obtain ⟨e2⟩ := Sec11.fieldCent_nonempty_eqLocus_congr ψ α
  have h2 := CFSG.RankThree.Coprime.pRank_eq_of_mulEquiv
    (e1.trans (e2.trans (e.trans (Sec4.projSLEquivPSL _).symm))) 3
  have h3 := (CFSG.RankThree.theta_quotient_core_and_ranks (G := ↥(Sec11.sec11K L d))).2.2.1.1
  obtain ⟨B', hB', hB'card⟩ :=
    CFSG.RankThree.PartOne.exists_isElementaryAbelian_card_pRank (p := 3) (by norm_num)
      (H := ↥(Sec11.sec11K L d))
  have hB'e : CFSG.Assembly.IsElemAbelian 3 B' :=
    ⟨hB'.toIsMulCommutative, fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx⟩
  refine ⟨B'.map (Sec11.sec11K L d).subtype, Subgroup.map_subtype_le _,
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ B' hB'e, ?_⟩
  rw [Subgroup.card_map_of_injective (Sec11.sec11K L d).subtype_injective, hB'card]
  calc 9 = 3 ^ 2 := by norm_num
    _ ≤ 3 ^ CFSG.pRank 3 ↥(Sec11.sec11K L d) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)

theorem not_mem_sup_zpowers_of_outer {L F₀ : Subgroup G} (hF₀L : F₀ ≤ L) {c d : G}
    (hcC : c ∈ thetaQuotCentralizer L) (hF₀c : ∀ f ∈ F₀, f * c = c * f)
    (hout : Sec4.InducesOuterTheta d L) : d ∉ F₀ ⊔ Subgroup.zpowers c := by
  intro hd
  obtain ⟨hdN, hnot⟩ := hout
  have hN : F₀ ≤ Subgroup.normalizer ((Subgroup.zpowers c : Subgroup G) : Set G) := by
    intro f hf
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    rintro _ rfl
    exact (hF₀c f hf).symm
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN] at hd
  obtain ⟨f, hf, z, hz, hdfz⟩ := hd
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  apply hnot
  have hfL : f ∈ L := hF₀L hf
  have hfN : f ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hfL
  obtain ⟨y, hy, hyc⟩ := hcC
  have hcN : c ∈ Subgroup.normalizer (L : Set G) := hyc ▸ y.2
  have hy' : y = ⟨c, hcN⟩ := Subtype.ext hyc
  have hc1 : thetaQuotMulAut L (compAction L ⟨c, hcN⟩) = 1 := by
    rw [← hy']; exact MonoidHom.mem_ker.mp hy
  have hprod : (⟨d, hdN⟩ : Subgroup.normalizer (L : Set G)) =
      ⟨f, hfN⟩ * (⟨c, hcN⟩ : Subgroup.normalizer (L : Set G)) ^ k :=
    Subtype.ext (by simpa using hdfz.symm)
  have : thetaQuotMulAut L (compAction L ⟨d, hdN⟩) =
      MulAut.conj (QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨f, hfL⟩) := by
    rw [hprod, map_mul, map_mul, map_zpow, map_zpow, hc1, one_zpow, mul_one,
      KFacts.thetaQuotMulAut_compAction_of_mem hfL hfN]
  rw [this]
  exact ⟨_, rfl⟩

theorem exists_K_SK (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (F : Frame611 G A c L E T d)
    {S : Subgroup G}
    (hS : S ∈ invariantPiSubgroups (Subgroup.centralizer {d} ⊓ Subgroup.centralizer (T : Set G))
      E (piOf 2)) (hS1 : S ≠ ⊥) (hSc : ⁅S, Subgroup.zpowers c⁆ = S) :
    ∃ K ∈ thetaComponentsAt 3 d,
      inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ≤ K ∧
      S ≤ Subgroup.normalizer (K : Set G) ∧
      ¬ ⁅S, K⁆ ≤ inSubgroup (aschbacherSolvableCore 3) K ∧ c ∉ thetaQuotCentralizer K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hst := F.standing
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := F.mem_S.1.1
  have hcA := F.c_mem
  have hc1 := F.c_ne_one
  have hdE : d ∈ E := F.d_mem.1
  have hdA : d ∈ A := F.mem_E.2 hdE
  have hd1 : d ≠ 1 := fun h => F.d_not_mem (h ▸ Subgroup.one_mem _)
  have hd3 : d ^ 3 = 1 := hAe.2 d hdA
  have hcE := F.c_mem_E
  have hLc : L ∈ thetaComponentsAt 3 c := lZeroStarAt_subset A c F.mem_L
  obtain ⟨φ⟩ := F.iso_L
  have hA81 : Nat.card A = 3 ^ 4 := by rw [F.card_A]; norm_num
  obtain ⟨hdN, hQ, hZ⟩ := fieldCent_facts_two φ F.d_field hd3
  have hY := Res611Res7.sec11K_mem_thetaComponentsIn_centralizer hLc hdN hd3 hQ hZ
  have hM : SectionFourHyp (Subgroup.centralizer ({d} : Set G)) :=
    hst.toTheoremFourHyp.sectionFourHyp (centralizer_ne_top_of_ne_one hst.toTheoremFourHyp hd1)
  have hAd : A ≤ Subgroup.centralizer ({d} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hAe.1.is_comm.comm ⟨a, ha⟩ ⟨d, hdA⟩))
  obtain ⟨K, hKd, hLK⟩ := exists_le_mem_thetaComponentsIn h48 hM hAd hAe ⟨4, by norm_num, hA81⟩
    hcA hc1 hY
  have hS' := hS
  rw [mem_invariantPiSubgroups_piOf_iff Nat.prime_two] at hS'
  obtain ⟨hSle, hS2, hES⟩ := hS'
  have hSd : S ≤ Subgroup.centralizer ({d} : Set G) := hSle.trans inf_le_left
  have hAN := le_normalizer_of_mem_thetaComponentsAt h45 hst.toTheoremFourHyp hAe hdA hd1
  have hcN : Subgroup.zpowers c ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.zpowers_le.mpr hcA).trans (hAN K hKd)
  have hSK : S ≤ Subgroup.normalizer (K : Set G) := by
    have h := commutator_le_normalizer_of_mem_thetaComponentsAt (X := S)
      (F := Subgroup.zpowers c) hSd
      (fun L' hL' => (Subgroup.zpowers_le.mpr hcA).trans (hAN L' hL')) hKd
    rwa [hSc] at h
  have hSKθ : ¬ ⁅S, K⁆ ≤ inSubgroup (aschbacherSolvableCore 3) K := by
    intro hSKθ
    obtain ⟨F₀, hF₀, hF₀e, hF₀9⟩ := exists_elemAbelian_le_sec11K_two φ F.d_field hd3
    have hF₀L : F₀ ≤ L := hF₀.trans (Sec11.sec11K_le L d)
    have hF₀K : F₀ ≤ K := hF₀.trans hLK
    have hF₀d : F₀ ≤ Subgroup.centralizer ({d} : Set G) :=
      (hF₀.trans (Subgroup.map_subtype_le _)).trans inf_le_right
    have hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥ :=
      CFSG.GorensteinWalter.center_eq_bot_of_mulEquiv
        (φ.trans (Sec4.projSLEquivPSL (GaloisField 3 (3 * 2))))
        (CFSG.GorensteinWalter.psl2_center_eq_bot (GaloisField 3 (3 * 2)))
    have hcC : c ∈ thetaQuotCentralizer L := by
      have h : c ∈ A ⊓ thetaQuotCentralizer L := by rw [F.cent_L]; exact Subgroup.mem_zpowers c
      exact h.2
    have hc3 : c ^ 3 = 1 := hAe.2 c hcA
    have hcL : c ∉ L := by
      intro hcL
      have hc3' : CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers c) :=
        Sec5.isElemAbelian_of_le hAe (Subgroup.zpowers_le.mpr hcA)
      have hbot := Res611Res7.inf_thetaQuotCentralizer_eq_bot_of_center
        (Subgroup.zpowers_le.mpr hcL) hc3' hZ
      have hmem : c ∈ Subgroup.zpowers c ⊓ thetaQuotCentralizer L :=
        ⟨Subgroup.mem_zpowers c, hcC⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hc1 hmem
    have hLcC : L ≤ Subgroup.centralizer ({c} : Set G) :=
      le_centralizer_of_mem_thetaComponentsAt hLc
    have hF₀c : ∀ a ∈ F₀, a * c = c * a := fun a ha =>
      Subgroup.mem_centralizer_singleton_iff.mp (hLcC (hF₀L ha))
    obtain ⟨hBe, hBcard⟩ := Sec5.isElemAbelian_sup_zpowers hF₀e (fun h => hcL (hF₀L h)) hc3 hF₀c
    set B1 := F₀ ⊔ Subgroup.zpowers c with hB1
    have hB1d : B1 ≤ Subgroup.centralizer ({d} : Set G) :=
      sup_le hF₀d (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (hAe.1.is_comm.comm ⟨c, hcA⟩ ⟨d, hdA⟩))))
    have hdB1 : d ∉ B1 := not_mem_sup_zpowers_of_outer hF₀L hcC hF₀c
      (KFacts.InducesStdKind.inducesOuterTheta L F.d_field (by decide))
    obtain ⟨hBe', hBcard'⟩ := Sec5.isElemAbelian_sup_zpowers hBe hdB1 hd3
      (fun u hu => (Subgroup.mem_centralizer_singleton_iff.mp (hB1d hu)))
    set B := B1 ⊔ Subgroup.zpowers d with hB
    have hB81 : 81 ≤ Nat.card B := by
      rw [hBcard', hBcard]
      omega
    set θK := inSubgroup (aschbacherSolvableCore 3) K with hθK
    set N := S ⊔ θK with hNdef
    have hSθ : S ≤ Subgroup.normalizer (θK : Set G) :=
      hSK.trans (normalizer_le_normalizer_theta K)
    have hN3 : ¬ 3 ∣ Nat.card N :=
      not_dvd_card_sup_of_isPGroup Nat.prime_three (by norm_num) hS2 hSθ
        (theta_solvable_and_not_dvd K).2
    have hF₀N : F₀ ≤ Subgroup.normalizer (N : Set G) := by
      apply le_normalizer_sup_of_conj
      · intro f hf s hs
        have h1 : f * s * f⁻¹ * s⁻¹ ∈ θK := by
          have h2 : ⁅f, s⁆ ∈ ⁅K, S⁆ := Subgroup.commutator_mem_commutator (hF₀K hf) hs
          rw [Subgroup.commutator_comm] at h2
          exact hSKθ h2
        rw [show f * s * f⁻¹ = (f * s * f⁻¹ * s⁻¹) * s by group]
        exact N.mul_mem (Subgroup.mem_sup_right h1) (Subgroup.mem_sup_left hs)
      · intro f hf y hy
        exact Subgroup.mem_sup_right
          ((Subgroup.mem_normalizer_iff.mp (le_normalizer_theta K (hF₀K hf)) y).mp hy)
    have hcNN : Subgroup.zpowers c ≤ Subgroup.normalizer (N : Set G) := by
      rw [Subgroup.zpowers_le]
      exact Subgroup.inf_normalizer_le_normalizer_sup S θK
        ⟨hES hcE, normalizer_le_normalizer_theta K (hcN (Subgroup.mem_zpowers c))⟩
    have hdNN : Subgroup.zpowers d ≤ Subgroup.normalizer (N : Set G) := by
      rw [Subgroup.zpowers_le]
      have hNd : N ≤ Subgroup.centralizer ({d} : Set G) :=
        sup_le hSd ((Subgroup.map_subtype_le _).trans (le_centralizer_of_mem_thetaComponentsAt hKd))
      refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
      intro n hn
      exact Subgroup.mem_centralizer_singleton_iff.mp (hNd hn)
    have hBN : B ≤ Subgroup.normalizer (N : Set G) := sup_le (sup_le hF₀N hcNN) hdNN
    have hB3 : IsPGroup 3 B := Sec5.isPGroup_of_isElemAbelian hBe'
    obtain ⟨R, hBR⟩ :=
      CFSG.RankThreeEvenClassification.Helpers.exists_normalized_sylow_in_prime_complement_subgroup
        3 Nat.prime_three B N hB3 hN3 hBN 2 Nat.prime_two
    set RG := (R : Subgroup N).map N.subtype with hRG
    have hRG2 : IsPGroup 2 RG := R.isPGroup'.map N.subtype
    have hRG1 : RG ≠ ⊥ := by
      intro hbot
      obtain ⟨y, -, hle⟩ := exists_le_conj_sylow R (le_sup_left : S ≤ N) hS2
      rw [← hRG, hbot, Subgroup.map_bot] at hle
      exact hS1 (le_bot_iff.mp hle)
    have hle := Sec5.card_le_of_le_normalizer hst.evenRank_eq hRG1 hRG2 hBe' hBR
    omega
  refine ⟨K, hKd, hLK, hSK, hSKθ, fun hcK => hSKθ ?_⟩
  rw [Subgroup.commutator_comm, commutator_le_theta_iff hSK, ← hSc, Subgroup.commutator_le]
  intro s hs y hy
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hck : c ^ k ∈ thetaQuotCentralizer K := zpow_mem hcK k
  rw [commutatorElement_def]
  exact Subgroup.mul_mem _ (conj_mem_thetaQuotCentralizer hck (hSK hs)) (inv_mem hck)

theorem exists_cfg_KStar (h45 : Sec4.Item4_5) (h49 : Sec4.Item4_9) (F : Frame611 G A c L E T d)
    {S : Subgroup G}
    (hS : S ∈ invariantPiSubgroups (Subgroup.centralizer {d} ⊓ Subgroup.centralizer (T : Set G))
      E (piOf 2)) (hSc : ⁅S, Subgroup.zpowers c⁆ = S) {K : Subgroup G}
    (hKd : K ∈ thetaComponentsAt 3 d)
    (hLK : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ≤ K)
    (hSK : S ≤ Subgroup.normalizer (K : Set G))
    (hSKθ : ¬ ⁅S, K⁆ ≤ inSubgroup (aschbacherSolvableCore 3) K)
    (hcK : c ∉ thetaQuotCentralizer K) :
    A ⊓ thetaQuotCentralizer K = Subgroup.zpowers d ∧ K ∈ lZeroStarAt A d := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hst := F.standing
  have hA := F.mem_S
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hA.1.1
  have hcA := F.c_mem
  have hc1 := F.c_ne_one
  have hdE : d ∈ E := F.d_mem.1
  have hdA : d ∈ A := F.mem_E.2 hdE
  have hd1 : d ≠ 1 := fun h => F.d_not_mem (h ▸ Subgroup.one_mem _)
  have hd3 : d ^ 3 = 1 := hAe.2 d hdA
  have hcE := F.c_mem_E
  have hE := F.mem_E
  have hLc : L ∈ thetaComponentsAt 3 c := lZeroStarAt_subset A c F.mem_L
  obtain ⟨φ⟩ := F.iso_L
  have hS' := hS
  rw [mem_invariantPiSubgroups_piOf_iff Nat.prime_two] at hS'
  obtain ⟨hSle, hS2, hES⟩ := hS'
  have hSd : S ≤ Subgroup.centralizer ({d} : Set G) := hSle.trans inf_le_left
  have hSE : S ≤ ⁅S, E⁆ := by
    calc S = ⁅S, Subgroup.zpowers c⁆ := hSc.symm
      _ ≤ ⁅S, E⁆ := Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hcE)
  have hKS : ¬ ⁅K, S⁆ ≤ inSubgroup (aschbacherSolvableCore 3) K := by
    rwa [Subgroup.commutator_comm]
  obtain ⟨-, -, -, hK0, -⟩ := props_of_moved hst h45 h49 hA hE hdE hd1 hKd hS2 hSd hES hSE hSK
    hKS
  have hdC : d ∈ thetaQuotCentralizer K := mem_thetaQuotCentralizer_of_mem_thetaComponentsAt hKd
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    le_normalizer_of_mem_thetaComponentsAt h45 hst.toTheoremFourHyp hAe hcA hc1 L hLc
  obtain ⟨hdN, hQ, hZ⟩ := fieldCent_facts_two φ F.d_field hd3
  have hKmem := Res611Res7.sec11K_mem_thetaComponentsIn_inf hdN hd3 hQ hZ
  have hY : Sec11.IsFieldCentClassical (L ⧸ aschbacherSolvableCore 3 L) :=
    Or.inl ⟨GaloisField 3 (3 * 2), inferInstance, inferInstance,
      ⟨φ.trans (Sec4.projSLEquivPSL (GaloisField 3 (3 * 2)))⟩⟩
  have hout : Sec4.InducesOuterTheta d L :=
    KFacts.InducesStdKind.inducesOuterTheta L F.d_field (by decide)
  have hcK' : Subgroup.zpowers c ⊓ thetaQuotCentralizer K = ⊥ :=
    Res611Res7.zpowers_inf_eq_bot (hAe.2 c hcA) hc1 hcK
  have hle : A ⊓ thetaQuotCentralizer K ≤ Subgroup.zpowers d := by
    rintro a ⟨haA, haC⟩
    have haN : a ∈ Subgroup.normalizer (L : Set G) := hAL haA
    have hadC : a ∈ Subgroup.centralizer ({d} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (hAe.1.is_comm.comm ⟨a, haA⟩ ⟨d, hdA⟩))
    have haM : a ∈ Subgroup.normalizer
        ((L ⊓ Subgroup.centralizer ({d} : Set G) : Subgroup G) : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_inf ⟨haN, Subgroup.le_normalizer hadC⟩
    have haK : a ∈ Subgroup.normalizer (Sec11.sec11K L d : Set G) :=
      GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual _ haM
    have htK := Res611Res7.commutator_mem_theta_of_mem_thetaQuotCentralizer hLK haC haK
    obtain ⟨i, hi⟩ := Sec11.exists_mul_pow_mem_thetaQuotCentralizer_of_classical hY hout hd3
      hKmem haN htK
    have hcmem : a * d ^ i ∈ Subgroup.zpowers c := by
      rw [← F.cent_L]
      exact ⟨A.mul_mem haA (A.pow_mem hdA i), hi⟩
    have hKC : a * d ^ i ∈ thetaQuotCentralizer K :=
      (thetaQuotCentralizer K).mul_mem haC ((thetaQuotCentralizer K).pow_mem hdC i)
    have h1 : a * d ^ i = 1 := by
      have hmem : a * d ^ i ∈ Subgroup.zpowers c ⊓ thetaQuotCentralizer K := ⟨hcmem, hKC⟩
      rwa [hcK', Subgroup.mem_bot] at hmem
    have h2 : a = (d ^ i)⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [h2]
    exact (Subgroup.zpowers d).inv_mem ((Subgroup.zpowers d).pow_mem (Subgroup.mem_zpowers d) i)
  have hge : Subgroup.zpowers d ≤ A ⊓ thetaQuotCentralizer K :=
    Subgroup.zpowers_le.mpr ⟨hdA, hdC⟩
  exact ⟨le_antisymm hle hge,
    mem_lZeroStarAt_of_inf_le_zpowers h45 hst hA hE hdE hd1 hKd hK0 hle⟩

theorem exists_cfg (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h49 : Sec4.Item4_9)
    (h : Sec8.Hyp81 G A c L a) (h81 : Nat.card A = 81)
    (hAN : A ≤ Subgroup.normalizer (L : Set G))
    (e₁ : L ⧸ aschbacherSolvableCore 3 L ≃* projSL 2 (GaloisField 3 (3 * 2)))
    (h9 : Nat.card (autThetaQuot A L ⊓ (MulAut.conj : (L ⧸ aschbacherSolvableCore 3 L) →*
      MulAut (L ⧸ aschbacherSolvableCore 3 L)).range : Subgroup _) = 9) :
    ∃ (E T : Subgroup G) (d : G) (S K : Subgroup G), Cfg611 G A c L E T d S K := by
  obtain ⟨E, T, F, hfield⟩ := exists_frame_all h45 h h81 hAN e₁ h9
  have hLc : L ∈ thetaComponentsAt 3 c := lZeroStarAt_subset A c F.mem_L
  have hcT : c ∈ Subgroup.centralizer (T : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun t ht =>
      Subgroup.mem_centralizer_singleton_iff.mp
        (le_centralizer_of_mem_thetaComponentsAt hLc (F.T_le_L ht))
  obtain ⟨d, hd, hdc, S, hS, hS1, hSc⟩ := Res611Field.exists_d_S F.standing.charTwoType
    F.mem_E.1 F.mem_T F.c_mem_E F.c_ne_one hcT
  set F' : Frame611 G A c L E T d :=
    { F with d_mem := hd, d_not_mem := hdc, d_field := hfield d hd hdc } with hF'
  obtain ⟨K, hKd, hLK, hSK, hSKθ, hcK⟩ := exists_K_SK h45 h48 F' hS hS1 hSc
  obtain ⟨hCAK, hK⟩ := exists_cfg_KStar h45 h49 F' hS hSc hKd hLK hSK hSKθ hcK
  exact ⟨E, T, d, S, K, { F' with
    mem_Sub := hS, S_ne_bot := hS1, S_comm := hSc, mem_K := hK, cent_K := hCAK, perf_le := hLK,
    c_not_cent := hcK, S_norm := hSK, S_not_theta := hSKθ }⟩

theorem exists_big_elemAbelian (h45 : Sec4.Item4_5) {S K : Subgroup G}
    (C : Cfg611 G A c L E T d S K) :
    ∃ B : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B ∧ 81 ≤ Nat.card B ∧
      B ≤ Subgroup.normalizer (K : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hst := C.standing
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := C.mem_S.1.1
  have hcA := C.c_mem
  have hc1 := C.c_ne_one
  have hdE : d ∈ E := C.d_mem.1
  have hdA : d ∈ A := C.mem_E.2 hdE
  have hd1 : d ≠ 1 := fun h => C.d_not_mem (h ▸ Subgroup.one_mem _)
  have hd3 : d ^ 3 = 1 := hAe.2 d hdA
  have hLc : L ∈ thetaComponentsAt 3 c := lZeroStarAt_subset A c C.mem_L
  have hKd : K ∈ thetaComponentsAt 3 d := lZeroStarAt_subset A d C.mem_K
  obtain ⟨φ⟩ := C.iso_L
  obtain ⟨F₀, hF₀, hF₀e, hF₀9⟩ := exists_elemAbelian_le_sec11K_two φ C.d_field hd3
  have hF₀L : F₀ ≤ L := hF₀.trans (Sec11.sec11K_le L d)
  have hF₀K : F₀ ≤ K := hF₀.trans C.perf_le
  have hF₀d : F₀ ≤ Subgroup.centralizer ({d} : Set G) :=
    (hF₀.trans (Subgroup.map_subtype_le _)).trans inf_le_right
  have hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥ :=
    CFSG.GorensteinWalter.center_eq_bot_of_mulEquiv
      (φ.trans (Sec4.projSLEquivPSL (GaloisField 3 (3 * 2))))
      (CFSG.GorensteinWalter.psl2_center_eq_bot (GaloisField 3 (3 * 2)))
  have hcC : c ∈ thetaQuotCentralizer L := by
    have h : c ∈ A ⊓ thetaQuotCentralizer L := by rw [C.cent_L]; exact Subgroup.mem_zpowers c
    exact h.2
  have hc3 : c ^ 3 = 1 := hAe.2 c hcA
  have hcL : c ∉ L := by
    intro hcL
    have hc3' : CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers c) :=
      Sec5.isElemAbelian_of_le hAe (Subgroup.zpowers_le.mpr hcA)
    have hbot := Res611Res7.inf_thetaQuotCentralizer_eq_bot_of_center
      (Subgroup.zpowers_le.mpr hcL) hc3' hZ
    have hmem : c ∈ Subgroup.zpowers c ⊓ thetaQuotCentralizer L :=
      ⟨Subgroup.mem_zpowers c, hcC⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hc1 hmem
  have hLcC : L ≤ Subgroup.centralizer ({c} : Set G) :=
    le_centralizer_of_mem_thetaComponentsAt hLc
  have hF₀c : ∀ a ∈ F₀, a * c = c * a := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mp (hLcC (hF₀L ha))
  obtain ⟨hBe, hBcard⟩ := Sec5.isElemAbelian_sup_zpowers hF₀e (fun h => hcL (hF₀L h)) hc3 hF₀c
  set B1 := F₀ ⊔ Subgroup.zpowers c with hB1
  have hB1d : B1 ≤ Subgroup.centralizer ({d} : Set G) :=
    sup_le hF₀d (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hAe.1.is_comm.comm ⟨c, hcA⟩ ⟨d, hdA⟩))))
  have hdB1 : d ∉ B1 := not_mem_sup_zpowers_of_outer hF₀L hcC hF₀c
    (KFacts.InducesStdKind.inducesOuterTheta L C.d_field (by decide))
  obtain ⟨hBe', hBcard'⟩ := Sec5.isElemAbelian_sup_zpowers hBe hdB1 hd3
    (fun u hu => (Subgroup.mem_centralizer_singleton_iff.mp (hB1d hu)))
  have hAN := le_normalizer_of_mem_thetaComponentsAt h45 hst.toTheoremFourHyp hAe hdA hd1
  refine ⟨B1 ⊔ Subgroup.zpowers d, hBe', ?_, sup_le (sup_le (hF₀K.trans Subgroup.le_normalizer)
    ((Subgroup.zpowers_le.mpr hcA).trans (hAN K hKd)))
    ((Subgroup.zpowers_le.mpr hdA).trans (hAN K hKd))⟩
  rw [hBcard', hBcard]
  omega

end Certs

end CFSG.RankThree.PartTwo.Sec6.Hering611
