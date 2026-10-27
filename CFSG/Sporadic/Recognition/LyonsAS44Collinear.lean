module

public import CFSG.Sporadic.Recognition.LyonsAS44McL
public import CFSG.Sporadic.Recognition.LyonsLocalTorus
public import CFSG.Certificates.Kernel.ThDemp.OrbBound
public import CFSG.CharacterTheory.CyclicBlocks.Family
public import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizers
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignment
public import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagon
public import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusion
public import CFSG.Combinatorics.AperiodicCentralInvolution
public import CFSG.Combinatorics.AperiodicFiveOfSix
public import CFSG.Combinatorics.AperiodicOppositeComponents
public import CFSG.Combinatorics.AperiodicSixteenGraphDistances
public import CFSG.Combinatorics.OuterLayerPredecessors
public import CFSG.GH74.GLS.Bg.Statements
public import CFSG.GH74.GLS.Defs
public import CFSG.GH74.Statements
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitThm47Statement
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Critical
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.Permutation.UnitaryThreeRecognition.Model
public import CFSG.Sporadic.Recognition.CoverTransferWords
public import CFSG.Sporadic.Recognition.McLASThreeCount
public import CFSG.Sporadic.Recognition.McLMultiplierMatrix
public import CFSG.Sporadic.Schreier.J4SSylow
public import CFSG.StronglyEmbedded.TheoremSE.BenderLowRank
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_1_12
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount

public section

namespace CFSG.Sporadic.Recognition.McLAS

open Subgroup CFSG.Sporadic.Recognition.LyonsSims

variable {K : Type*} [Group K] {y : K} {A : Subgroup K} {Y : Fin 10 → K}

theorem injective_vec3 {a b c : Fin 10} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Function.Injective ![a, b, c] := by
  intro p q hpq
  fin_cases p <;> fin_cases q <;> simp_all

theorem NormFacts.mem_closure_of_mem_closure (hN : NormFacts K y A Y) {a b c a' b' c' : Fin 10}
    (ha : Function.Injective ![a, b, c]) (hb : Function.Injective ![a', b', c'])
    (h : Y c ∈ closure ({Y a, Y b} : Set K)) : Y c' ∈ closure ({Y a', Y b'} : Set K) := by
  obtain ⟨g, -, hg⟩ := hN.trans3 ![a, b, c] ![a', b', c'] ha hb
  have h0 : g * Y a * g⁻¹ = Y a' ∨ g * Y a * g⁻¹ = (Y a')⁻¹ := hg 0
  have h1 : g * Y b * g⁻¹ = Y b' ∨ g * Y b * g⁻¹ = (Y b')⁻¹ := hg 1
  have h2 : g * Y c * g⁻¹ = Y c' ∨ g * Y c * g⁻¹ = (Y c')⁻¹ := hg 2
  have hL : ∀ u ∈ closure ({Y a, Y b} : Set K),
      g * u * g⁻¹ ∈ closure ({Y a', Y b'} : Set K) := by
    intro u hu
    induction hu using Subgroup.closure_induction with
    | mem u hu =>
      rcases hu with rfl | rfl
      · rcases h0 with h0 | h0
        · rw [h0]; exact subset_closure (by simp)
        · rw [h0]; exact Subgroup.inv_mem _ (subset_closure (by simp))
      · rcases h1 with h1 | h1
        · rw [h1]; exact subset_closure (by simp)
        · rw [h1]; exact Subgroup.inv_mem _ (subset_closure (by simp))
    | one => simp
    | mul u v _ _ hu hv =>
      have : g * (u * v) * g⁻¹ = (g * u * g⁻¹) * (g * v * g⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ hu hv
    | inv u _ hu =>
      have : g * u⁻¹ * g⁻¹ = (g * u * g⁻¹)⁻¹ := by group
      rw [this]
      exact Subgroup.inv_mem _ hu
  have h3 := hL _ h
  rcases h2 with h2 | h2
  · rwa [h2] at h3
  · rw [h2] at h3
    exact (Subgroup.inv_mem_iff _).1 h3

theorem NormFacts.not_mem_closure (hN : NormFacts K y A Y) (hY3 : ∀ i, Y i ^ 3 = 1)
    (hcomm : ∀ i j, Commute (Y i) (Y j)) {j i : Fin 10} (hj : j ≠ 0) (hi0 : i ≠ 0)
    (hij : i ≠ j) : Y i ∉ closure ({Y 0, Y j} : Set K) := by
  intro h
  have hall : ∀ c : Fin 10, Y c ∈ closure ({Y 0, Y 1} : Set K) := by
    intro c
    by_cases hc0 : c = 0
    · subst hc0; exact subset_closure (by simp)
    by_cases hc1 : c = 1
    · subst hc1; exact subset_closure (by simp)
    exact hN.mem_closure_of_mem_closure (a := 0) (b := j) (c := i) (a' := 0) (b' := 1) (c' := c)
      (injective_vec3 hj.symm hi0.symm hij.symm)
      (injective_vec3 (by decide) (Ne.symm hc0) (Ne.symm hc1)) h
  have hex : ∀ c : Fin 10, ∃ p : Fin 3 × Fin 3, Y c = Y 0 ^ (p.1 : ℕ) * Y 1 ^ (p.2 : ℕ) := by
    intro c
    obtain ⟨a, b, hab⟩ := exists_zpow_mul_of_mem_closure_pair (hcomm 0 1) (hall c)
    obtain ⟨i₁, hi₁⟩ := exists_fin_pow_of_pow_three (hY3 0) a
    obtain ⟨i₂, hi₂⟩ := exists_fin_pow_of_pow_three (hY3 1) b
    exact ⟨(i₁, i₂), by rw [hab, hi₁, hi₂]⟩
  choose φ hφ using hex
  have hinj : Function.Injective φ := by
    intro c c' hcc
    apply hN.distinct c c'
    left
    rw [hφ c, hφ c', hcc]
  have := Fintype.card_le_of_injective φ hinj
  simp at this

variable [CFSG.IsElementaryAbelian 3 ↥A]

theorem NormFacts.not_isConj_mul (hN : NormFacts K y A Y) {z : K} (hzA : z ∈ A)
    (hzc : IsConj y z) (hz : z ∉ zpowers y) : ¬ IsConj y (y * z) := by
  intro hc
  have hyA : y ∈ A := hN.zero ▸ hN.mem_A 0
  have hY3 : ∀ i, Y i ^ 3 = 1 := fun i =>
    CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 3) (A := A) (Y i) (hN.mem_A i)
  have hcomm : ∀ i j, Commute (Y i) (Y j) := fun i j => by
    exact congrArg Subtype.val
      ((IsMulCommutative.is_comm (M := A)).comm ⟨Y i, hN.mem_A i⟩ ⟨Y j, hN.mem_A j⟩)
  obtain ⟨j, hj⟩ := hN.cover z hzA hzc
  obtain ⟨i, hi⟩ := hN.cover (y * z) (Subgroup.mul_mem _ hyA hzA) hc
  have hy0 : Y 0 = y := hN.zero
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [hy0] at hj
    apply hz
    rcases hj with h | h
    · rw [h]; exact mem_zpowers y
    · rw [h]; exact Subgroup.inv_mem _ (mem_zpowers y)
  have hy1 : y ≠ 1 := by
    intro h1
    have hc1 := hN.isConj 1
    rw [h1, isConj_one_right] at hc1
    have : Y 1 = Y 0 := by rw [hc1, hy0, h1]
    exact absurd (hN.distinct 1 0 (Or.inl this)) (by decide)
  have hi0 : i ≠ 0 := by
    rintro rfl
    rw [hy0] at hi
    apply hz
    have hzy : z = y⁻¹ * (y * z) := by group
    rcases hi with h | h
    · rw [hzy, h]; simp
    · rw [hzy, h]; exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (mem_zpowers y))
        (Subgroup.inv_mem _ (mem_zpowers y))
  have hij : i ≠ j := by
    rintro rfl
    have hyi : y ∈ zpowers (Y i) := by
      have hyz : y = (y * z) * z⁻¹ := by group
      have hzi : z ∈ zpowers (Y i) := by
        rcases hj with h | h
        · rw [h]; exact mem_zpowers _
        · rw [h]; exact Subgroup.inv_mem _ (mem_zpowers _)
      have hyzi : y * z ∈ zpowers (Y i) := by
        rcases hi with h | h
        · rw [h]; exact mem_zpowers _
        · rw [h]; exact Subgroup.inv_mem _ (mem_zpowers _)
      rw [hyz]
      exact Subgroup.mul_mem _ hyzi (Subgroup.inv_mem _ hzi)
    obtain ⟨a, ha⟩ := mem_zpowers_iff.1 hyi
    obtain ⟨k, hk⟩ := exists_fin_pow_of_pow_three (hY3 i) a
    have hy : y = Y i ^ (k : ℕ) := by rw [← ha, hk]
    fin_cases k
    · exact hy1 (by simpa using hy)
    · apply hj0
      have : Y 0 = Y i := by rw [hy0, hy]; simp
      exact (hN.distinct 0 i (Or.inl this)).symm
    · apply hj0
      have : Y 0 = (Y i)⁻¹ := by
        rw [hy0, hy]
        have h3 := hY3 i
        calc Y i ^ 2 = Y i ^ 2 * (Y i ^ 3)⁻¹ ^ 1 := by rw [h3]; simp
          _ = (Y i)⁻¹ := by group
      exact (hN.distinct 0 i (Or.inr this)).symm
  have hmem : Y i ∈ closure ({Y 0, Y j} : Set K) := by
    have hzc' : z ∈ closure ({Y 0, Y j} : Set K) := by
      rcases hj with h | h
      · rw [h]; exact subset_closure (by simp)
      · rw [h]; exact Subgroup.inv_mem _ (subset_closure (by simp))
    have hy' : y ∈ closure ({Y 0, Y j} : Set K) := by
      rw [← hy0]; exact subset_closure (by simp)
    have hyz' : y * z ∈ closure ({Y 0, Y j} : Set K) := Subgroup.mul_mem _ hy' hzc'
    rcases hi with h | h
    · rwa [h] at hyz'
    · rw [h] at hyz'
      exact (Subgroup.inv_mem_iff _).1 hyz'
  exact hN.not_mem_closure hY3 hcomm hj0 hi0 hij hmem

end CFSG.Sporadic.Recognition.McLAS
