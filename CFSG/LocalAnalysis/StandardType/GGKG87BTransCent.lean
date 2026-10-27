module

public import CFSG.LocalAnalysis.StandardType.GGKG87BTransDefs
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6Order3Defs
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate118
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate13657
import CFSG.RankThree.PartOne.KE8F.FamBruhat
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24CentreStab
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompChain
import CFSG.RankThree.PartOne.KE.SigmaCentralizer
import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
import CFSG.HardMathSupport.Timmesfeld.CrossChar.Families
import CFSG.HardMathSupport.Timmesfeld.Proving.ExistsOrderPCentralizer
import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
import CFSG.LieType.Ree.LargeReeSylowOpposition
import CFSG.LinearAlgebra.LinearGroups.LinearTwo
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
import CFSG.Monster.B.Geometry.CoxeterWords
import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
import CFSG.RankThree.PartOne.KD4T.Certs
import CFSG.RankThree.PartOne.KE.A1Action
import CFSG.RankThree.PartOne.KE.A1Levi
import CFSG.RankThree.PartOne.KE.A1TwistedE6
import CFSG.RankThree.PartOne.KE.E7FiveBlock
import CFSG.RankThree.PartOne.KE.SLnShape
import CFSG.RankThree.PartOne.KE.SigmaUntwisted
import CFSG.RankThree.PartOne.KE.StabGeneral
import CFSG.RankThree.PartOne.KE.ThreeA1Group
import CFSG.RankThree.PartOne.KGD.D4Frame
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
import CFSG.Walter.Defs

public section

namespace CFSG.StandardType.KG87B

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE8F CFSG.RankThree.PartOne.KE CFSG.RankThree.Chevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

private theorem root_coeff_one : ∀ α ∈ rootFinset Tag.E6, -2 ≤ α 1 ∧ α 1 ≤ 2 := by
  decide +kernel

private theorem root_coeff_three : ∀ α ∈ rootFinset Tag.E6, α 1 = 0 → -1 ≤ α 3 ∧ α 3 ≤ 1 := by
  decide +kernel

private theorem card_root_coeff_one :
    ((rootFinset Tag.E6).filter fun α => α 1 = 0).card = 30 := by
  decide +kernel

private theorem coeff_one_eq_zero {α : Fin Tag.E6.rank → ℤ}
    (hα : IsRoot Tag.E6 α) (h : (3 : ℤ) ∣ α 1) : α 1 = 0 := by
  have := root_coeff_one α (mem_rootFinset.2 hα)
  omega

private theorem rootChar_mulSingle {Ω : Type} [Field Ω] (j : Fin Tag.E6.rank) (c : Ωˣ)
    (v : Fin Tag.E6.rank → ℤ) : rootChar (Pi.mulSingle j c) v = c ^ v j := by
  rw [rootChar, Finset.prod_eq_single j (fun i _ hij => by rw [Pi.mulSingle_eq_of_ne hij, one_zpow])
    (fun h => absurd (Finset.mem_univ j) h), Pi.mulSingle_eq_same]

private theorem rootChar_mul_tuple {Ω : Type} [Field Ω] (a b : Fin Tag.E6.rank → Ωˣ)
    (v : Fin Tag.E6.rank → ℤ) : rootChar (a * b) v = rootChar a v * rootChar b v := by
  simp only [rootChar, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

private theorem rootChar_xtd {Ω : Type} [Field Ω] (ω : Ωˣ) (v : Fin Tag.E6.rank → ℤ) :
    rootChar (Pi.mulSingle 1 ω * Pi.mulSingle 3 (ω ^ 2) : Fin Tag.E6.rank → Ωˣ) v =
      ω ^ (v 1 + 2 * v 3) := by
  rw [rootChar_mul_tuple, rootChar_mulSingle, rootChar_mulSingle, ← zpow_natCast, ← zpow_mul,
    ← zpow_add]
  norm_num

private theorem zpow_eq_one_iff_three {Ω : Type} [Field Ω] {ω : Ωˣ} (hω : orderOf ω = 3)
    (k : ℤ) : ω ^ k = 1 ↔ (3 : ℤ) ∣ k := by
  rw [← orderOf_dvd_iff_zpow_eq_one, hω]
  norm_num

private def fixTwo : Subgroup (WeylGroup Tag.E6) where
  carrier := {w | ∀ v : Fin Tag.E6.rank → ℤ, (w • v) 1 = v 1}
  mul_mem' {w w'} hw hw' v := by
    simp only [Set.mem_setOf_eq] at hw hw'
    rw [mul_smul, hw, hw']
  one_mem' v := by rw [one_smul]
  inv_mem' {w} hw v := by
    simp only [Set.mem_setOf_eq] at hw
    rw [← hw (w⁻¹ • v), smul_inv_smul]

private theorem fixTwo_of_stab
    {Ω : Type} [Field Ω] {ω : Ωˣ}
    (hω : orderOf ω = 3) {w : WeylGroup Tag.E6}
    (hw : w ∈ rootCharStabilizer (Pi.mulSingle 1 ω : Fin Tag.E6.rank → Ωˣ)) :
    ∀ v : Fin Tag.E6.rank → ℤ, (w • v) 1 = v 1 := by
  have h3 : ∀ i, (Pi.mulSingle 1 ω : Fin Tag.E6.rank → Ωˣ) i ^ 3 = 1 := by
    intro i
    by_cases hi : i = 1
    · subst hi
      rw [Pi.mulSingle_eq_same, ← hω, pow_orderOf_eq_one]
    · rw [Pi.mulSingle_eq_of_ne hi, one_pow]
  have hker : kernelRoots (rootCharHom (Pi.mulSingle 1 ω : Fin Tag.E6.rank → Ωˣ)) =
      ↑((rootFinset Tag.E6).filter fun α => α 1 = 0) := by
    rw [kernelRoots_rootCharHom]
    ext α
    simp only [Set.mem_setOf_eq, Finset.coe_filter, mem_rootFinset, rootChar_mulSingle,
      zpow_eq_one_iff_three hω]
    exact ⟨fun h => ⟨h.1, coeff_one_eq_zero h.1 h.2⟩, fun h => ⟨h.1, h.2 ▸ dvd_zero 3⟩⟩
  have hk : (kernelRoots (rootCharHom (Pi.mulSingle 1 ω : Fin Tag.E6.rank → Ωˣ))).ncard ∈
      ({22, 30, 40} : Set ℕ) := by
    rw [hker, Set.ncard_coe_finset, card_root_coeff_one]
    simp
  have hle : kernelReflectionGroup (Pi.mulSingle 1 ω : Fin Tag.E6.rank → Ωˣ) ≤ fixTwo := by
    rw [kernelReflectionGroup, Subgroup.closure_le]
    rintro _ ⟨u, i, hu, rfl⟩ v
    have hu1 : (u • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) 1 = 0 := by
      obtain ⟨hr, hc⟩ := hu
      rw [rootChar_mulSingle, zpow_eq_one_iff_three hω] at hc
      exact coeff_one_eq_zero hr hc
    rw [mul_smul, mul_smul, simple_smul, reflect, smul_sub, smul_inv_smul, smul_comm u]
    simp [hu1]
  exact hle (KSConn.e6_stab_le_kernelReflectionGroup_of_conn _ h3 hk hw)

private theorem mem_closure_of_fix
    (S : Set (WeylGroup Tag.E6))
    (hS : ∀ i : Fin Tag.E6.rank, i ≠ 1 → i ≠ 3 → simple Tag.E6 i ∈ Subgroup.closure S) :
    ∀ w : WeylGroup Tag.E6, (∀ v : Fin Tag.E6.rank → ℤ, (w • v) 1 = v 1) →
      (∀ v : Fin Tag.E6.rank → ℤ, (3 : ℤ) ∣ (w • v) 3 - v 3) → w ∈ Subgroup.closure S := by
  suffices h : ∀ n, ∀ w : WeylGroup Tag.E6, (coxeterSystem Tag.E6).length w = n →
      (∀ v : Fin Tag.E6.rank → ℤ, (w • v) 1 = v 1) →
      (∀ v : Fin Tag.E6.rank → ℤ, (3 : ℤ) ∣ (w • v) 3 - v 3) → w ∈ Subgroup.closure S from
    fun w => h _ w rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro w hn h1 h3
    by_cases hw1 : w = 1
    · rw [hw1]
      exact one_mem _
    obtain ⟨i, hi⟩ := (coxeterSystem Tag.E6).exists_leftDescent_of_ne_one hw1
    have hlen : (coxeterSystem Tag.E6).length (simple Tag.E6 i * w) < n := by
      rw [← hn]
      exact hi
    have hneg : w⁻¹ • (Pi.single i 1 : Fin Tag.E6.rank → ℤ) ≤ 0 :=
      (CFSG.LieType.RootSystem.isRightDescent_iff (isFiniteType_cartan Tag.E6) w⁻¹ i).1
        ((coxeterSystem Tag.E6).isRightDescent_inv_iff.2 hi)
    have h1' : ∀ v : Fin Tag.E6.rank → ℤ, (w⁻¹ • v) 1 = v 1 := fun v => by
      rw [← h1 (w⁻¹ • v), smul_inv_smul]
    have h3' : ∀ v : Fin Tag.E6.rank → ℤ, (3 : ℤ) ∣ (w⁻¹ • v) 3 - v 3 := fun v => by
      have := h3 (w⁻¹ • v)
      rw [smul_inv_smul] at this
      omega
    by_cases hi1 : i = 1
    · subst hi1
      have := hneg 1
      rw [h1'] at this
      simp at this
    by_cases hi3 : i = 3
    · subst hi3
      have hr : IsRoot Tag.E6 (w⁻¹ • (Pi.single 3 1 : Fin Tag.E6.rank → ℤ)) :=
        IsRoot.smul (isRoot_single _ _) _
      have hc1 : (w⁻¹ • (Pi.single 3 1 : Fin Tag.E6.rank → ℤ)) 1 = 0 := by
        rw [h1']
        decide
      have hb := root_coeff_three _ (mem_rootFinset.2 hr) hc1
      have hd := h3' (Pi.single 3 1)
      have hn3 := hneg 3
      simp only [Pi.single_eq_same, Pi.zero_apply] at hd hn3
      omega
    have hs : simple Tag.E6 i * w ∈ Subgroup.closure S := by
      refine ih _ hlen _ rfl (fun v => ?_) (fun v => ?_)
      · rw [mul_smul, simple_smul, reflect]
        simp [Ne.symm hi1, h1]
      · rw [mul_smul, simple_smul, reflect]
        simpa [Pi.single_apply, Ne.symm hi3] using h3 v
    have hw : w = simple Tag.E6 i * (simple Tag.E6 i * w) := by
      rw [← mul_assoc, (coxeterSystem Tag.E6).simple_mul_simple_self, one_mul]
    rw [hw]
    exact mul_mem (hS i hi1 hi3) hs

private theorem block_pow_eq {G : Type*} [CommGroup G] (u v : G) :
    (u ^ 2 * v) ^ (2 : ℤ) * (u * v ^ 2) ^ (-1 : ℤ) = u ^ 3 ∧
      (u ^ 2 * v) ^ (-1 : ℤ) * (u * v ^ 2) ^ (2 : ℤ) = v ^ 3 := by
  constructor <;>
  · apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow, ofMul_pow]
    abel


private theorem corootPair_blocks :
    corootPair (Pi.single 0 1 : Fin Tag.E6.rank → ℤ) (Pi.single 0 1) = 2 ∧
    corootPair (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) (Pi.single 0 1) = -1 ∧
    corootPair (Pi.single 4 1 : Fin Tag.E6.rank → ℤ) (Pi.single 0 1) = 0 ∧
    corootPair (Pi.single 5 1 : Fin Tag.E6.rank → ℤ) (Pi.single 0 1) = 0 ∧
    corootPair (Pi.single 0 1 : Fin Tag.E6.rank → ℤ) (Pi.single 2 1) = -1 ∧
    corootPair (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) (Pi.single 2 1) = 2 ∧
    corootPair (Pi.single 4 1 : Fin Tag.E6.rank → ℤ) (Pi.single 2 1) = 0 ∧
    corootPair (Pi.single 5 1 : Fin Tag.E6.rank → ℤ) (Pi.single 2 1) = 0 ∧
    corootPair (Pi.single 0 1 : Fin Tag.E6.rank → ℤ) (Pi.single 4 1) = 0 ∧
    corootPair (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) (Pi.single 4 1) = 0 ∧
    corootPair (Pi.single 4 1 : Fin Tag.E6.rank → ℤ) (Pi.single 4 1) = 2 ∧
    corootPair (Pi.single 5 1 : Fin Tag.E6.rank → ℤ) (Pi.single 4 1) = -1 ∧
    corootPair (Pi.single 0 1 : Fin Tag.E6.rank → ℤ) (Pi.single 5 1) = 0 ∧
    corootPair (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) (Pi.single 5 1) = 0 ∧
    corootPair (Pi.single 4 1 : Fin Tag.E6.rank → ℤ) (Pi.single 5 1) = -1 ∧
    corootPair (Pi.single 5 1 : Fin Tag.E6.rank → ℤ) (Pi.single 5 1) = 2 := by
  decide +kernel

private theorem torus_le_thirdTorus_sup_blockGroup
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] :
    torusGroup Tag.E6 Ω ≤ thirdTorus Ω ⊔ blockGroup Ω := by
  intro t ht
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  have hcube : ∀ x : Ωˣ, ∃ u : Ωˣ, u ^ 3 = x := fun x => by
    obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (x : Ω) (by norm_num : 0 < 3)
    have hu0 : u ≠ 0 := by
      rintro rfl
      exact x.ne_zero (by rw [← hu]; norm_num)
    exact ⟨Units.mk0 u hu0, Units.ext (by simp [hu])⟩
  obtain ⟨u0, hu0⟩ := hcube (a 0)
  obtain ⟨u2, hu2⟩ := hcube (a 2)
  obtain ⟨u4, hu4⟩ := hcube (a 4)
  obtain ⟨u5, hu5⟩ := hcube (a 5)
  have hroot : ∀ j : Fin Tag.E6.rank, j ≠ 1 → j ≠ 3 → Pi.single j 1 ∈ blockRoots := by
    intro j h1 h3
    refine ⟨isRoot_single _ _, ?_, ?_⟩
    · show (Pi.single j 1 : Fin Tag.E6.rank → ℤ) 1 = 0
      simp [Ne.symm h1]
    · show (Pi.single j 1 : Fin Tag.E6.rank → ℤ) 3 = 0
      simp [Ne.symm h3]
  have hrank : ∀ (j : Fin Tag.E6.rank) (s : Ωˣ), j ≠ 1 → j ≠ 3 →
      rootDiagUnit Tag.E6 (fun i => s ^ corootPair (Pi.single j 1) (Pi.single i 1)) ∈
        blockGroup Ω := by
    intro j s h1 h3
    rw [← rootSL2_HSL_eq (isRoot_single _ _)]
    have hn : -(Pi.single j 1 : Fin Tag.E6.rank → ℤ) ∈ blockRoots := by
      obtain ⟨hr, h1', h3'⟩ := hroot j h1 h3
      exact ⟨IsRoot.neg hr, by simp [h1'], by simp [h3']⟩
    exact rootRankOneGroup_le_rootSpan (isRoot_single _ _) (hroot j h1 h3) hn ⟨_, rfl⟩
  set c : Fin Tag.E6.rank → Ωˣ :=
    (fun i => (u0 ^ 2 * u2) ^ corootPair (Pi.single 0 1) (Pi.single i 1)) *
      (fun i => (u0 * u2 ^ 2) ^ corootPair (Pi.single 2 1) (Pi.single i 1)) *
      (fun i => (u4 ^ 2 * u5) ^ corootPair (Pi.single 4 1) (Pi.single i 1)) *
      (fun i => (u4 * u5 ^ 2) ^ corootPair (Pi.single 5 1) (Pi.single i 1)) with hc
  have hcmem : rootDiagUnit Tag.E6 c ∈ blockGroup Ω := by
    rw [hc, rootDiagUnit_mul, rootDiagUnit_mul, rootDiagUnit_mul]
    exact mul_mem (mul_mem (mul_mem (hrank _ _ (by decide) (by decide))
      (hrank _ _ (by decide) (by decide))) (hrank _ _ (by decide) (by decide)))
      (hrank _ _ (by decide) (by decide))
  obtain ⟨e00, e20, e40, e50, e02, e22, e42, e52, e04, e24, e44, e54, e05, e25, e45, e55⟩ :=
    corootPair_blocks
  have hc0 : c 0 = a 0 := by
    simp only [hc, Pi.mul_apply, e00, e20, e40, e50, zpow_zero, mul_one]
    rw [(block_pow_eq u0 u2).1, hu0]
  have hc2 : c 2 = a 2 := by
    simp only [hc, Pi.mul_apply, e02, e22, e42, e52, zpow_zero, mul_one]
    rw [(block_pow_eq u0 u2).2, hu2]
  have hc4 : c 4 = a 4 := by
    simp only [hc, Pi.mul_apply, e04, e24, e44, e54, zpow_zero, one_mul]
    rw [(block_pow_eq u4 u5).1, hu4]
  have hc5 : c 5 = a 5 := by
    simp only [hc, Pi.mul_apply, e05, e25, e45, e55, zpow_zero, one_mul]
    rw [(block_pow_eq u4 u5).2, hu5]
  have hS : rootDiagUnit Tag.E6 (a * c⁻¹) ∈ thirdTorus Ω :=
    ⟨a * c⁻¹, show (a * c⁻¹) 0 = 1 by simp [hc0], show (a * c⁻¹) 2 = 1 by simp [hc2],
      show (a * c⁻¹) 4 = 1 by simp [hc4], show (a * c⁻¹) 5 = 1 by simp [hc5], rfl⟩
  have he : rootDiagUnit Tag.E6 a = rootDiagUnit Tag.E6 (a * c⁻¹) * rootDiagUnit Tag.E6 c := by
    rw [← rootDiagUnit_mul, inv_mul_cancel_right]
  rw [he]
  exact mul_mem (Subgroup.mem_sup_left hS) (Subgroup.mem_sup_right hcmem)

theorem mem_thirdTorus_sup_blockGroup_of_commute
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] {ω : Ωˣ} (hω : orderOf ω = 3)
    {g : ModGL Tag.E6 Ω} (hg : g ∈ adjointGroup Tag.E6 Ω)
    (h1 : g * rootDiagUnit Tag.E6 (Pi.mulSingle 1 ω) = rootDiagUnit Tag.E6 (Pi.mulSingle 1 ω) * g)
    (h2 : g * rootDiagUnit Tag.E6 (Pi.mulSingle 1 ω * Pi.mulSingle 3 (ω ^ 2)) =
      rootDiagUnit Tag.E6 (Pi.mulSingle 1 ω * Pi.mulSingle 3 (ω ^ 2)) * g) :
    g ∈ thirdTorus Ω ⊔ blockGroup Ω := by
  set F : Set (Fin Tag.E6.rank → Ωˣ) :=
    {Pi.mulSingle 1 ω, Pi.mulSingle 1 ω * Pi.mulSingle 3 (ω ^ 2)} with hF
  have hker : famKernel F ⊆ blockRoots := by
    rintro α ⟨hα, hχ⟩
    have hc1 := hχ _ (Set.mem_insert _ _)
    have hc2 := hχ _ (Set.mem_insert_of_mem _ rfl)
    rw [rootChar_mulSingle, zpow_eq_one_iff_three hω] at hc1
    rw [rootChar_xtd, zpow_eq_one_iff_three hω] at hc2
    have h0 := coeff_one_eq_zero hα hc1
    have hb := root_coeff_three α (mem_rootFinset.2 hα) h0
    refine ⟨hα, h0, ?_⟩
    show α 3 = 0
    omega
  have hstab : famStabilizer F ⊆ (Subgroup.closure
      {s | ∃ α ∈ famKernel F, s = rootReflection α} : Set (WeylGroup Tag.E6)) := by
    intro w hw
    have hw1 : w ∈ rootCharStabilizer (Pi.mulSingle 1 ω : Fin Tag.E6.rank → Ωˣ) :=
      hw _ (Set.mem_insert _ _)
    have hw2 : w ∈ rootCharStabilizer
        (Pi.mulSingle 1 ω * Pi.mulSingle 3 (ω ^ 2) : Fin Tag.E6.rank → Ωˣ) :=
      hw _ (Set.mem_insert_of_mem _ rfl)
    have hP := fixTwo_of_stab hω hw1
    refine mem_closure_of_fix _ (fun i hi1 hi3 => ?_) w hP (fun v => ?_)
    · have hi1' : (Pi.single i 1 : Fin Tag.E6.rank → ℤ) 1 = 0 := by
        simp [Ne.symm hi1]
      have hi3' : (Pi.single i 1 : Fin Tag.E6.rank → ℤ) 3 = 0 := by
        simp [Ne.symm hi3]
      refine Subgroup.subset_closure ⟨Pi.single i 1, ⟨isRoot_single _ _, ?_⟩, ?_⟩
      · rintro a (rfl | rfl)
        · rw [rootChar_mulSingle, hi1', zpow_zero]
        · rw [rootChar_xtd, hi1', hi3', mul_zero, add_zero, zpow_zero]
      · rw [rootReflection_eq_conj (w := 1) (j := i) (one_smul _ _), one_mul, inv_one, mul_one]
    · have h := hw2 v
      rw [rootChar_xtd, rootChar_xtd] at h
      have h' : ω ^ (((w • v) 1 + 2 * (w • v) 3) - (v 1 + 2 * v 3)) = 1 := by
        rw [zpow_sub, h, mul_inv_cancel]
      rw [zpow_eq_one_iff_three hω, hP v] at h'
      omega
  have hS : ∀ α ∈ blockRoots, IsRoot Tag.E6 α := fun α h => h.1
  have hSn : ∀ α ∈ blockRoots, -α ∈ blockRoots := fun α ⟨hr, h1', h3'⟩ =>
    ⟨IsRoot.neg hr, by simp [h1'], by simp [h3']⟩
  have hcomm : ∀ a ∈ F, g * rootDiagUnit Tag.E6 a = rootDiagUnit Tag.E6 a * g := by
    rintro a (rfl | rfl)
    exacts [h1, h2]
  obtain ⟨t, ht, r, hr, rfl⟩ :=
    Set.mem_mul.1 (mem_torus_mul_rootSpan_of_commute_fam F hstab hS hSn hker hg hcomm)
  exact mul_mem (torus_le_thirdTorus_sup_blockGroup ht) (Subgroup.mem_sup_right hr)

end CFSG.StandardType.KG87B

end
