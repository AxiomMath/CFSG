module

public import CFSG.LocalAnalysis.StandardType.GGSixLSixFiveBasic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.LocalAnalysis.ComponentInitial.CentralSL2Semilinear
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Basic
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
import CFSG.FeitThompson.OddOrderTheorem
import CFSG.LocalAnalysis.StandardType.GGStdTypeOddConj
import CFSG.GroupTheory.GroupAction.PerfectCommutingSL2
import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCShortRoot
import CFSG.ClassicalGroups.Symplectic.ComponentCartanRank
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.ClassicalInvolution.SL2Facts
import CFSG.ClassicalGroups.Symplectic.DiagonalTorusRank
import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
import CFSG.ClassicalInvolution.WeakCT.StandardPair
import CFSG.GroupTheory.HallHigmanPiCore
import CFSG.LieType.Steinberg.CentralExt.SpCentrallyClosed
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
import CFSG.RankThree.PartTwo.Sec4.Census.Interface
import CFSG.SignalizerFunctorTheorem.NonLocal.Cross
import CFSG.SignalizerFunctorTheorem.NonLocal.SpData
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement
import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.StandardType

open CFSG.Assembly

open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem ggPComponent_radical_eq_commutator {p : ℕ} [Fact p.Prime] {H A J : Subgroup G} {x : G}
    (hA : LargeEvenPComponent p H A) (hJA : J ≤ A)
    (hJ : IsComponentOf J (H ⊓ Subgroup.centralizer {x})) (hpJ : p ∣ Nat.card J)
    (hJZ : Subgroup.center ↥J = ⊥)
    (hxA : x ∈ Subgroup.normalizer (A : Set G)) (hxp : x ^ p = 1)
    (hxc : ⁅A, Subgroup.zpowers x⁆ ≤ LargeEvenPPrimeCoreOf p A)
    (hodd : Odd (Nat.card ↥⁅J, LargeEvenPPrimeCoreOf p H⁆)) :
    A = J ⊔ LargeEvenPPrimeCoreOf p A ∧ J ⊓ LargeEvenPPrimeCoreOf p A = ⊥ ∧
      LargeEvenPPrimeCoreOf p A = ⁅LargeEvenPPrimeCoreOf p A, J⁆ ∧
      Odd (Nat.card ↥(LargeEvenPPrimeCoreOf p A)) := by
  set N := LargeEvenPPrimeCoreOf p A with hNdef
  set O := LargeEvenPPrimeCoreOf p H with hOdef
  have hAeq : A = J ⊔ N := ggEq_sup_pPrimeCoreOf_of_centralizes hA hJA hJ hpJ hxA hxp hxc
  have hAH : A ≤ H := hA.1
  have hNA : N ≤ A := Subgroup.map_subtype_le _
  have hNO : N ≤ O := ggPPrimeCoreOf_le_of_isSubnormal hA.2.1
  have hJq : CFSG.Assembly.IsQuasisimple ↥J := hJ.2.2
  have hAN : A ≤ Subgroup.normalizer (N : Set G) := fun a ha =>
    ggNormalizer_le_normalizer_pPrimeCoreOf p A (Subgroup.le_normalizer ha)
  have hJN' : J ≤ Subgroup.normalizer (N : Set G) := hJA.trans hAN
  have hJNbot : J ⊓ N = ⊥ := by
    have hX : J ≤ Subgroup.normalizer ((J ⊓ N : Subgroup G) : Set G) := fun j hj =>
      ggMem_normalizer_inf_of (Subgroup.le_normalizer hj) (hJN' hj)
    rcases ggLe_center_or_eq_of_normalized hJq inf_le_left hX with hc | heq
    · rw [eq_bot_iff]
      intro z hz
      have hzZ : (⟨z, hz.1⟩ : ↥J) ∈ Subgroup.center ↥J := Subgroup.mem_center_iff.mpr fun w =>
        Subtype.ext (Subgroup.mem_centralizer_iff.mp (hc hz) w w.2)
      rw [hJZ] at hzZ
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val (Subgroup.mem_bot.mp hzZ))
    · exfalso
      have hJN : J ≤ N := heq ▸ inf_le_right
      exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mp
        ((ggPPrimeCoreOf_coprime A).coprime_dvd_right (Subgroup.card_dvd_of_le hJN)) hpJ
  set M := ⁅N, J⁆ with hMdef
  have hMN : M ≤ N := Subgroup.commutator_le.mpr fun n hn j hj => by
    have hjn : j * n⁻¹ * j⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hJN' hj) n⁻¹).mp (N.inv_mem hn)
    have h : ⁅n, j⁆ = n * (j * n⁻¹ * j⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [h]
    exact N.mul_mem hn hjn
  have hMnorm' : N ⊔ J ≤ Subgroup.normalizer (M : Set G) :=
    Subgroup.le_normalizer_of_normal_subgroupOf (hK := Subgroup.normal_subgroupOf_commutator_sup N J)
      (hMN.trans le_sup_left)
  have hNMn : N ≤ Subgroup.normalizer (M : Set G) := le_sup_left.trans hMnorm'
  have hJMn : J ≤ Subgroup.normalizer (M : Set G) := le_sup_right.trans hMnorm'
  have hModd : Odd (Nat.card M) :=
    Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le
      ((Subgroup.commutator_comm N J).le.trans (Subgroup.commutator_mono le_rfl hNO)))
  have hJMA : J ⊔ M ≤ A := sup_le hJA (hMN.trans hNA)
  have hAnorm : A ≤ Subgroup.normalizer ((J ⊔ M : Subgroup G) : Set G) := by
    rw [hAeq]
    refine sup_le (fun j hj => ?_) (fun n hn => ?_)
    · rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hj),
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (hJMn hj)]
    · rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      refine Subgroup.eq_of_le_of_card_ge ?_
        (by rw [Subgroup.card_map_of_injective (MulAut.conj n).injective])
      rw [Subgroup.map_sup, Subgroup.mem_normalizer_iff_map_conj_eq.mp (hNMn hn)]
      refine sup_le ?_ le_sup_right
      rintro _ ⟨j, hj, rfl⟩
      have h : (MulAut.conj n) j = ⁅n, j⁆ * j := by
        simp only [MulAut.conj_apply, commutatorElement_def]
        group
      erw [h]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.commutator_mem_commutator hn hj))
        (Subgroup.mem_sup_left hj)
  have hJMnormal : ((J ⊔ M).subgroupOf A).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hJMA]
    intro h k hh hk
    exact (Subgroup.mem_normalizer_iff.mp (hAnorm hk) h).mp hh
  have hJMsub : IsSubnormal (J ⊔ M) H := IsSubnormal.step hJMA hJMnormal hA.2.1
  set π := QuotientGroup.mk' (LargeEvenPPrimeCore p ↥H) with hπ
  have himg : ((J ⊔ M).subgroupOf H).map π = (A.subgroupOf H).map π := by
    refine le_antisymm (Subgroup.map_mono (Subgroup.subgroupOf_mono H hJMA)) ?_
    rintro _ ⟨⟨a, haH⟩, ha, rfl⟩
    have ha' : a ∈ J ⊔ N := hAeq ▸ (Subgroup.mem_subgroupOf.mp ha)
    obtain ⟨j, hj, n, hn, rfl⟩ := ggExists_mul_of_mem_sup_of_le_normalizer hJN' ha'
    obtain ⟨w, hw, hwn⟩ := hNO hn
    refine ⟨⟨j, hAH (hJA hj)⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left hj), ?_⟩
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have h : (⟨j, hAH (hJA hj)⟩ : ↥H)⁻¹ * ⟨j * n, haH⟩ = w :=
      Subtype.ext (by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_cancel_left]
        exact hwn.symm)
    rw [h]
    exact hw
  have hJMeq : J ⊔ M = A := by
    by_contra hne
    exact hA.2.2.2 (J ⊔ M) (lt_of_le_of_ne hJMA hne) hJMsub himg
  have hNM : N = M := by
    refine le_antisymm (fun n hn => ?_) hMN
    have hn' : n ∈ J ⊔ M := hJMeq ▸ hNA hn
    obtain ⟨j, hj, m, hm, hjm⟩ := ggExists_mul_of_mem_sup_of_le_normalizer hJMn hn'
    have hjN : j ∈ N := by
      have h : j = n * m⁻¹ := by rw [← hjm]; group
      rw [h]
      exact N.mul_mem hn (N.inv_mem (hMN hm))
    have hj1 : j ∈ J ⊓ N := ⟨hj, hjN⟩
    rw [hJNbot, Subgroup.mem_bot] at hj1
    rw [← hjm, hj1, one_mul]
    exact hm
  refine ⟨hAeq, hJNbot, hNM, ?_⟩
  rw [hNM]
  exact hModd

theorem ggPComponent_eq_of_oddRadical_of_actor {p : ℕ} [Fact p.Prime] {H A J Q₂ C : Subgroup G}
    {x e₁ : G} (hA : LargeEvenPComponent p H A) (hJA : J ≤ A)
    (hJ : IsComponentOf J (H ⊓ Subgroup.centralizer {x})) (hpJ : p ∣ Nat.card J)
    (hJZ : Subgroup.center ↥J = ⊥)
    (hxA : x ∈ Subgroup.normalizer (A : Set G)) (hxp : x ^ p = 1)
    (hxc : ⁅A, Subgroup.zpowers x⁆ ≤ LargeEvenPPrimeCoreOf p A)
    (hodd : Odd (Nat.card ↥⁅J, LargeEvenPPrimeCoreOf p H⁆))
    (hQ₂J : Q₂ ≤ J) (hQ₂ : IsComponentOf Q₂ (H ⊓ Subgroup.centralizer {e₁})) (hCJ : C ≤ J)
    (hC : C ≠ ⊥)
    (hact : ∀ N : Subgroup G, Group.IsSolvable ↥N → Nat.Coprime (Nat.card N) (2 * p) →
      J ≤ Subgroup.normalizer (N : Set G) →
      (∀ s ∈ Q₂, ∀ n ∈ N ⊓ Subgroup.centralizer {e₁}, s * n = n * s) →
      ∀ s ∈ C, ∀ n ∈ N, s * n = n * s) :
    A = J ∧ IsComponentOf J H := by
  obtain ⟨hAeq, hJNbot, hNM, hNodd⟩ :=
    ggPComponent_radical_eq_commutator hA hJA hJ hpJ hJZ hxA hxp hxc hodd
  set N := LargeEvenPPrimeCoreOf p A with hNdef
  have hNA : N ≤ A := Subgroup.map_subtype_le _
  have hAN : A ≤ Subgroup.normalizer (N : Set G) := fun a ha =>
    ggNormalizer_le_normalizer_pPrimeCoreOf p A (Subgroup.le_normalizer ha)
  have hJN' : J ≤ Subgroup.normalizer (N : Set G) := hJA.trans hAN
  have hQ₂ne : Q₂ ≠ ⊥ := fun h => commutator_ne_bot_of_isQuasisimple hQ₂.2.2 (by rw [h, Subgroup.commutator_bot_left])
  have hNnormal : (N.subgroupOf A).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hNA]
    intro h k hh hk
    exact (Subgroup.mem_normalizer_iff.mp (hAN hk) h).mp hh
  have hNe : IsSubnormal (N ⊓ Subgroup.centralizer {e₁}) (H ⊓ Subgroup.centralizer {e₁}) :=
    ggIsSubnormal_inf (IsSubnormal.step hNA hNnormal hA.2.1) _
  have hcent : ∀ s ∈ Q₂, ∀ n ∈ N ⊓ Subgroup.centralizer {e₁}, s * n = n * s := by
    rcases isComponentOf_le_or_commutator_eq_bot hQ₂ hNe with hle | hbot
    · refine absurd (eq_bot_iff.mpr ?_) hQ₂ne
      rw [← hJNbot]
      exact le_inf hQ₂J (hle.trans inf_le_left)
    · intro s hs n hn
      have h := Subgroup.commutator_mem_commutator hs hn
      rw [hbot, Subgroup.mem_bot] at h
      exact commutatorElement_eq_one_iff_mul_comm.mp h
  have hcop : Nat.Coprime (Nat.card N) (2 * p) :=
    Nat.Coprime.mul_right hNodd.coprime_two_right (ggPPrimeCoreOf_coprime (p := p) A).symm
  have hQN := hact N (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hNodd) hcop hJN' hcent
  have hCn : Subgroup.normalizer (N : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (N : Set G) : Set G) :=
    Subgroup.le_normalizer_of_normal_subgroupOf
      (hK := Subgroup.normal_subgroupOf_centralizer_normalizer _) (Subgroup.centralizer_le_normalizer _)
  have hQC : C ≤ J ⊓ Subgroup.centralizer (N : Set G) := le_inf hCJ fun s hs =>
    Subgroup.mem_centralizer_iff.mpr fun n hn => (hQN s hs n hn).symm
  have hJN1 : N = ⊥ := by
    rcases ggLe_center_or_eq_of_normalized hJ.2.2 inf_le_left
        (fun j hj => ggMem_normalizer_inf_of (Subgroup.le_normalizer hj) (hCn (hJN' hj))) with hc | heq
    · refine absurd (eq_bot_iff.mpr fun s hs => ?_) hC
      have hsZ : (⟨s, hCJ hs⟩ : ↥J) ∈ Subgroup.center ↥J := Subgroup.mem_center_iff.mpr fun w =>
        Subtype.ext (Subgroup.mem_centralizer_iff.mp (hc (hQC hs)) w w.2)
      rw [hJZ] at hsZ
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val (Subgroup.mem_bot.mp hsZ))
    · rw [hNM, Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact heq.symm.le.trans inf_le_right
  have hAJ : A = J := by rw [hAeq, hJN1, sup_bot_eq]
  exact ⟨hAJ, ⟨hJA.trans hA.1, hAJ ▸ hA.2.1, hJ.2.2⟩⟩

theorem ggPComponent_eq_of_oddRadical {p : ℕ} [Fact p.Prime] {H A J Q₂ : Subgroup G} {x e₁ : G}
    (hA : LargeEvenPComponent p H A) (hJA : J ≤ A)
    (hJ : IsComponentOf J (H ⊓ Subgroup.centralizer {x})) (hpJ : p ∣ Nat.card J)
    (hJZ : Subgroup.center ↥J = ⊥)
    (hxA : x ∈ Subgroup.normalizer (A : Set G)) (hxp : x ^ p = 1)
    (hxc : ⁅A, Subgroup.zpowers x⁆ ≤ LargeEvenPPrimeCoreOf p A)
    (hodd : Odd (Nat.card ↥⁅J, LargeEvenPPrimeCoreOf p H⁆))
    (hQ₂J : Q₂ ≤ J) (hQ₂ : IsComponentOf Q₂ (H ⊓ Subgroup.centralizer {e₁}))
    (hact : ∀ N : Subgroup G, Group.IsSolvable ↥N → Nat.Coprime (Nat.card N) (2 * p) →
      J ≤ Subgroup.normalizer (N : Set G) →
      (∀ s ∈ Q₂, ∀ n ∈ N ⊓ Subgroup.centralizer {e₁}, s * n = n * s) →
      ∀ s ∈ Q₂, ∀ n ∈ N, s * n = n * s) :
    A = J ∧ IsComponentOf J H :=
  ggPComponent_eq_of_oddRadical_of_actor hA hJA hJ hpJ hJZ hxA hxp hxc hodd hQ₂J hQ₂ hQ₂J
    (fun h => commutator_ne_bot_of_isQuasisimple hQ₂.2.2 (by rw [h, Subgroup.commutator_bot_left]))
    hact

theorem ggPComponent_eq_of_oddRadical_of_SL2 {p : ℕ} [Fact p.Prime] {H A J Q₂ : Subgroup G} {x e₁ : G}
    {F : Type*} [Field F] [Fintype F] [CharP F 2] (ψ : SL(2, F) →* G) (lam : Fˣ)
    (hlam : orderOf lam = p) (t : SL(2, F))
    (ht : IsConj t (CFSG.LocalAnalysis.ComponentInitial.sl2Diag F lam)) (he₁ : ψ t = e₁)
    (hA : LargeEvenPComponent p H A) (hJA : J ≤ A)
    (hJ : IsComponentOf J (H ⊓ Subgroup.centralizer {x})) (hpJ : p ∣ Nat.card J)
    (hJZ : Subgroup.center ↥J = ⊥)
    (hxA : x ∈ Subgroup.normalizer (A : Set G)) (hxp : x ^ p = 1)
    (hxc : ⁅A, Subgroup.zpowers x⁆ ≤ LargeEvenPPrimeCoreOf p A)
    (hodd : Odd (Nat.card ↥⁅J, LargeEvenPPrimeCoreOf p H⁆))
    (hQ₁J : ψ.range ≤ J) (hQ₂J : Q₂ ≤ J) (hQ₁₂ : ∀ a ∈ ψ.range, ∀ b ∈ Q₂, a * b = b * a)
    (hQ₂ : IsComponentOf Q₂ (H ⊓ Subgroup.centralizer {e₁})) :
    A = J ∧ IsComponentOf J H :=
  ggPComponent_eq_of_oddRadical hA hJA hJ hpJ hJZ hxA hxp hxc hodd hQ₂J hQ₂
    (CFSG.commute_of_perfect_of_sl2Diag_of_le ψ le_rfl lam hlam t ht he₁ hQ₁J hQ₂J hQ₁₂ ⟨hQ₂.2.2.1⟩)

theorem ggPComponent_eq_of_oddRadical_of_SL2_of_pGroup {p : ℕ} [Fact p.Prime]
    {H A J Q₂ C : Subgroup G} {x e₁ : G} {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (ψ : SL(2, F) →* G) (lam : Fˣ) (hlam : orderOf lam = p) (t : SL(2, F))
    (ht : IsConj t (CFSG.LocalAnalysis.ComponentInitial.sl2Diag F lam)) (he₁ : ψ t = e₁)
    (hA : LargeEvenPComponent p H A) (hJA : J ≤ A)
    (hJ : IsComponentOf J (H ⊓ Subgroup.centralizer {x})) (hpJ : p ∣ Nat.card J)
    (hJZ : Subgroup.center ↥J = ⊥)
    (hxA : x ∈ Subgroup.normalizer (A : Set G)) (hxp : x ^ p = 1)
    (hxc : ⁅A, Subgroup.zpowers x⁆ ≤ LargeEvenPPrimeCoreOf p A)
    (hodd : Odd (Nat.card ↥⁅J, LargeEvenPPrimeCoreOf p H⁆))
    (hQ₁J : ψ.range ≤ J) (hQ₂J : Q₂ ≤ J) (hQ₂ : IsComponentOf Q₂ (H ⊓ Subgroup.centralizer {e₁}))
    (hCQ₂ : C ≤ Q₂) (hC : C ≠ ⊥) (hCp : IsPGroup p C)
    (hQ₁C : ∀ a ∈ ψ.range, ∀ b ∈ C, a * b = b * a) :
    A = J ∧ IsComponentOf J H :=
  ggPComponent_eq_of_oddRadical_of_actor hA hJA hJ hpJ hJZ hxA hxp hxc hodd hQ₂J hQ₂ (hCQ₂.trans hQ₂J) hC
    fun N hN hcop hJN hcent =>
      CFSG.commute_of_perfect_or_pGroup_of_sl2Diag_of_le ψ le_rfl lam hlam t ht he₁ hQ₁J (hCQ₂.trans hQ₂J)
        hQ₁C (Or.inr ⟨Fact.out, hCp⟩) N hN hcop hJN fun s hs n hn => hcent s (hCQ₂ hs) n hn

theorem ggPComponent_eq_of_oddRadical_of_Sp4 {p : ℕ} [Fact p.Prime] {H A J : Subgroup G} {x e₁ : G}
    {F : Type} [Field F] [Fintype F] [CharP F 2] (κ : CFSG.Open.StatedSp 2 F →* G)
    (hκ : Function.Injective κ) (hκJ : κ.range = J) (lam : Fˣ) (hlam : orderOf lam = p)
    (he₁ : κ (CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlock F 2 0
      (CFSG.LocalAnalysis.ComponentInitial.sl2Diag F lam)) = e₁)
    (hA : LargeEvenPComponent p H A) (hJA : J ≤ A)
    (hJ : IsComponentOf J (H ⊓ Subgroup.centralizer {x})) (hpJ : p ∣ Nat.card J)
    (hxA : x ∈ Subgroup.normalizer (A : Set G)) (hxp : x ^ p = 1)
    (hxc : ⁅A, Subgroup.zpowers x⁆ ≤ LargeEvenPPrimeCoreOf p A)
    (hodd : Odd (Nat.card ↥⁅J, LargeEvenPPrimeCoreOf p H⁆))
    (hQ₂ : IsComponentOf (κ.comp (CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlock F 2 1)).range
      (H ⊓ Subgroup.centralizer {e₁})) :
    A = J ∧ IsComponentOf J H := by
  have hle : ∀ k : Fin 2,
      (κ.comp (CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlock F 2 k)).range ≤ J := fun k => by
    rw [← hκJ, MonoidHom.range_comp]
    exact Subgroup.map_le_range κ _
  have hJZ : Subgroup.center ↥J = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨s, hs⟩ : (z : G) ∈ κ.range := hκJ ▸ z.2
    have hsZ : s ∈ Subgroup.center (CFSG.Open.StatedSp 2 F) := Subgroup.mem_center_iff.mpr fun g => hκ (by
      have h := congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨κ g, hκJ ▸ MonoidHom.mem_range.mpr ⟨g, rfl⟩⟩)
      simp only [map_mul, hs]
      exact h)
    rw [CFSG.ClassicalGroups.Symplectic.center_statedSp_eq_bot_of_charP_two (by norm_num),
      Subgroup.mem_bot] at hsZ
    exact Subgroup.mem_bot.mpr (Subtype.ext (by rw [← hs, hsZ, map_one, OneMemClass.coe_one]))
  refine ggPComponent_eq_of_oddRadical_of_SL2 _ lam hlam _ (IsConj.refl _) he₁ hA hJA hJ hpJ hJZ hxA hxp hxc
    hodd (hle 0) (hle 1) ?_ hQ₂
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  simp only [MonoidHom.comp_apply, ← map_mul]
  rw [(CFSG.ClassicalInvolution.Models.SymplecticPairs.commute_longBlock_longBlock
    (by decide : (0 : Fin 2) ≠ 1) a b).eq]

end CFSG.StandardType

end
