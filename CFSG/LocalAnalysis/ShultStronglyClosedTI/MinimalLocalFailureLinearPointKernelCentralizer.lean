module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLinearPointKernelBasic
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthCentralizer

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.LinearChain

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ShultStronglyClosedTI.ProperPairModel
open CFSG.ShultStronglyClosedTI.PairInvolutionFixedField
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open scoped Pointwise

variable {G : Type} [Group G]

theorem card_sup_mul_card_inf_of_le_normalizer {A B : Subgroup G}
    (hB : B ≤ Subgroup.normalizer (A : Set G)) :
    Nat.card (A ⊔ B : Subgroup G) * Nat.card (A ⊓ B : Subgroup G) =
      Nat.card A * Nat.card B := by
  have hrel := Subgroup.relIndex_mul_card A B
  have hrel' := Subgroup.relIndex_mul_card A (A ⊔ B)
  rw [inf_eq_left.mpr le_sup_left] at hrel'
  have : (A.subgroupOf (B ⊔ A)).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hB
  have : (A.subgroupOf B).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hB
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient B A hB
  have hidx : A.relIndex B = A.relIndex (A ⊔ B) := by
    rw [Subgroup.relIndex, Subgroup.relIndex, Subgroup.index, Subgroup.index, sup_comm]
    exact Nat.card_congr e.toEquiv
  rw [← hrel', ← hrel, hidx, inf_comm]
  ring

theorem centralizer_hull_le_pair_stabilizer {H : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) {beta : rightCosetSpace H} {t : G}
    (ht : t ∈ rightPairFlipFiber H z beta) :
    Subgroup.centralizer (minimalLocalFailureProperPairHull H z beta t : Set G) ≤
      pairPointStabilizer H beta := by
  intro c hc
  have hcz : c ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hc z
      (minimalLocalFailureProperPair_distinguished_mem H z beta t)).symm
  have hcH : c ∈ H := point_centralizer_le h hcz
  have hct : t * c = c * t :=
    Subgroup.mem_centralizer_iff.mp hc t (minimalLocalFailureProperPair_flip_mem H z beta t)
  refine ⟨(mem_rightCosetStabilizer_iff H _ c).mpr ((translate_base_iff H c).mpr hcH),
    (mem_rightCosetStabilizer_iff H beta c).mpr ?_⟩
  rw [← ht.2, rightCosetTranslate_mul, hct, ← rightCosetTranslate_mul,
    (translate_base_iff H c).mpr hcH]

theorem sup_inf_eq_of_le_normalizer {Q B L : Subgroup G}
    (hB : B ≤ Subgroup.normalizer (Q : Set G)) (hQL : Q ≤ L) :
    (Q ⊔ B) ⊓ L = Q ⊔ (B ⊓ L) := by
  apply le_antisymm
  · rintro x ⟨hx, hxL⟩
    have hx' : x ∈ (Q : Set G) * (B : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left Q B hB]
      exact hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx'
    have hbL : b ∈ L := by
      have hmem := L.mul_mem (L.inv_mem (hQL ha)) hxL
      rwa [inv_mul_cancel_left] at hmem
    exact Subgroup.mul_mem_sup ha ⟨hb, hbL⟩
  · exact sup_le (le_inf le_sup_left hQL) (inf_le_inf_right L le_sup_right)

variable [Finite G]

theorem pair_hull_centralizer_eq
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (hlin : ∃ (k : Type) (_ : Field k) (_ : Finite k),
      Nat.card k = Nat.card (minimalLocalFailurePairActionPointHull H z) ∧
      Nonempty (minimalLocalFailureProperPairHull H z beta t ≃* PSL2MatrixGroup k)) :
    Subgroup.centralizer (minimalLocalFailureProperPairHull H z beta t : Set G) =
      pairPointStabilizer H beta ⊓
        Subgroup.centralizer (minimalLocalFailurePairActionPointHull H z : Set G) := by
  set B := pairPointStabilizer H beta with hBdef
  set K := minimalLocalFailureProperPairHull H z beta t with hKdef
  set Q := minimalLocalFailurePairActionPointHull H z with hQdef
  obtain ⟨-, hQK, -⟩ := CyclicPair.proper_pair_point_root h hcomm hbeta ht hproper
  obtain ⟨-, -, -, -, hBK, -⟩ :=
    minimalLocalFailure_proper_pair_hull_linear_or_suzuki h hcomm hsmallerR1 hbeta ht hproper
  obtain ⟨-, -, hreg⟩ :=
    point_normalizer_eq_root_sup h hcomm hsmallerR1 hbeta ht hproper hlin
  apply le_antisymm
  · exact le_inf (centralizer_hull_le_pair_stabilizer h.local_datum ht)
      (Subgroup.centralizer_le hQK)
  rintro b ⟨hbB, hbQ⟩
  have hbH : b ∈ H := pairPointStabilizer_le_point H beta hbB
  have hbα : rightCosetTranslate H (rightCosetMk H 1) b = rightCosetMk H 1 :=
    (translate_base_iff H b).mpr hbH
  have hbβ : rightCosetTranslate H beta b = beta :=
    (mem_rightCosetStabilizer_iff H beta b).mp hbB.2
  have hβK : beta ∈ baseOrbit H K := ⟨t, minimalLocalFailureProperPair_flip_mem H z beta t,
    (flip_coset_eq H ht).symm⟩
  have hfixb : ∀ y ∈ K, rightCosetTranslate H (rightCosetMk H y) b = rightCosetMk H y := by
    intro y hyK
    by_cases hyα : rightCosetMk H y = rightCosetMk H 1
    · rw [hyα]
      exact hbα
    obtain ⟨s, hs, -⟩ := hreg beta hβK (rightCosetMk H y) ⟨y, hyK, rfl⟩ hbeta hyα
    have hsb : (s : G) * b = b * s := (Subgroup.mem_centralizer_iff.mp hbQ s s.2)
    rw [← hs, rightCosetTranslate_mul, hsb, ← rightCosetTranslate_mul, hbβ]
  have hfixb' : ∀ y ∈ K, rightCosetTranslate H (rightCosetMk H y) b⁻¹ = rightCosetMk H y := by
    intro y hyK
    calc rightCosetTranslate H (rightCosetMk H y) b⁻¹ =
          rightCosetTranslate H (rightCosetTranslate H (rightCosetMk H y) b) b⁻¹ := by
            rw [hfixb y hyK]
      _ = rightCosetMk H y := by
            rw [rightCosetTranslate_mul, mul_inv_cancel, rightCosetTranslate_one]
  rw [Subgroup.mem_centralizer_iff]
  intro x hxK
  have hconjK : b⁻¹ * x⁻¹ * b ∈ K := by
    have hmem := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hBK hbB)) x⁻¹).mp
      (K.inv_mem hxK)
    simpa only [inv_inv] using hmem
  have hcK : b⁻¹ * x⁻¹ * b * x ∈ K := K.mul_mem hconjK hxK
  have hcfix : ∀ y ∈ K, rightCosetTranslate H (rightCosetMk H y) (b⁻¹ * x⁻¹ * b * x) =
      rightCosetMk H y := by
    intro y hyK
    have hyx : y * x⁻¹ ∈ K := K.mul_mem hyK (K.inv_mem hxK)
    have h1 := hfixb' y hyK
    have h2 := hfixb (y * x⁻¹) hyx
    rw [← rightCosetTranslate_mul, ← rightCosetTranslate_mul, ← rightCosetTranslate_mul, h1,
      rightCosetTranslate_mk, h2, rightCosetTranslate_mk, inv_mul_cancel_right]
  have hc1 := proper_pair_hull_faithful_on_orbit h hcomm hsmallerR1 hbeta ht hproper hlin hcK
    hcfix
  calc x * b = x * b * (b⁻¹ * x⁻¹ * b * x) := by rw [hc1, mul_one]
    _ = b * x := by group

theorem root_centralizer_normalizer_and_index
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (hlin : ∃ (k : Type) (_ : Field k) (_ : Finite k),
      Nat.card k = Nat.card (minimalLocalFailurePairActionPointHull H z) ∧
      Nonempty (minimalLocalFailureProperPairHull H z beta t ≃* PSL2MatrixGroup k))
    (hindex : (pairPointStabilizer H beta).relIndex H =
      Nat.card (minimalLocalFailurePairActionPointHull H z) ^ 3) :
    let K := minimalLocalFailureProperPairHull H z beta t
    let Q := minimalLocalFailurePairActionPointHull H z
    let J := Subgroup.centralizer (K : Set G)
    let C := H ⊓ Subgroup.centralizer (Q : Set G)
    Subgroup.normalizer (K : Set G) ⊓ C = Q ⊔ J ∧ Q ⊓ J = ⊥ ∧
      J ≤ Subgroup.centralizer (Q : Set G) ∧
      (Q ⊔ J).relIndex C ∣ Nat.card Q ^ 2 := by
  intro K Q J C
  set B := pairPointStabilizer H beta with hBdef
  obtain ⟨hQH, hQK, hQnormal, hQab, -, -, -⟩ :=
    CyclicPair.proper_pair_point_root h hcomm hbeta ht hproper
  obtain ⟨hNeq, hQB, -⟩ := point_normalizer_eq_root_sup h hcomm hsmallerR1 hbeta ht hproper hlin
  have hJ : J = B ⊓ Subgroup.centralizer (Q : Set G) :=
    pair_hull_centralizer_eq h hcomm hsmallerR1 hbeta ht hproper hlin
  have hBH : B ≤ H := pairPointStabilizer_le_point H beta
  have hHQ : H ≤ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQH).mp hQnormal
  have hQQ : Q ≤ Subgroup.centralizer (Q : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact congrArg Subtype.val (hQab.1.is_comm.comm ⟨b, hb⟩ ⟨a, ha⟩)
  have hJQ : J ≤ Subgroup.centralizer (Q : Set G) := hJ ▸ inf_le_right
  have hJB : J ≤ B := hJ ▸ inf_le_left
  have hQJ : Q ⊓ J = ⊥ := le_bot_iff.mp (hQB ▸ inf_le_inf_left Q hJB)
  have hNC : Subgroup.normalizer (K : Set G) ⊓ C = Q ⊔ J := by
    change Subgroup.normalizer (K : Set G) ⊓ (H ⊓ Subgroup.centralizer (Q : Set G)) = Q ⊔ J
    rw [← inf_assoc, hNeq, sup_inf_eq_of_le_normalizer (hBH.trans hHQ) hQQ, hJ]
  refine ⟨hNC, hQJ, hJQ, ?_⟩
  have hCB : C ⊓ B = J := by
    rw [hJ]
    change H ⊓ Subgroup.centralizer (Q : Set G) ⊓ B = B ⊓ Subgroup.centralizer (Q : Set G)
    rw [inf_comm, ← inf_assoc, inf_eq_left.mpr hBH]
  have hCnormal : (C.subgroupOf H).Normal :=
    (TwoCoreGrowth.point_two_core_of_normal_root_centralizer H Q hQH hQnormal
      (TwoCoreGrowth.original_point_hull_centralizes_two_core h.local_datum h.central_sylow)).1
  have hBC : B ≤ Subgroup.normalizer (C : Set G) :=
    hBH.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mp hCnormal)
  have hprod := card_sup_mul_card_inf_of_le_normalizer hBC
  rw [hCB] at hprod
  have hCBH : C ⊔ B ≤ H := sup_le inf_le_left hBH
  have hHcard : Nat.card H = Nat.card Q ^ 3 * Nat.card B := by
    have h1 := Subgroup.relIndex_mul_card B H
    rw [inf_eq_left.mpr hBH, hindex] at h1
    exact h1.symm
  have hdvdH : Nat.card (C ⊔ B : Subgroup G) ∣ Nat.card H := Subgroup.card_dvd_of_le hCBH
  have hQJcard : Nat.card (Q ⊔ J : Subgroup G) = Nat.card Q * Nat.card J := by
    have h1 := card_sup_mul_card_inf_of_le_normalizer
      (hJQ.trans (Subgroup.centralizer_le_normalizer (s := (Q : Set G))))
    rwa [hQJ, Subgroup.card_bot, mul_one] at h1
  have hQJC : Q ⊔ J ≤ C := sup_le (le_inf hQH hQQ) (le_inf (hJB.trans hBH) hJQ)
  have hrel := Subgroup.relIndex_mul_card (Q ⊔ J) C
  rw [inf_eq_left.mpr hQJC, hQJcard] at hrel
  obtain ⟨m, hm⟩ := hdvdH
  have hpos : 0 < Nat.card Q * Nat.card J * Nat.card B :=
    Nat.mul_pos (Nat.mul_pos Nat.card_pos Nat.card_pos) Nat.card_pos
  have hkey : (Q ⊔ J).relIndex C * m * (Nat.card Q * Nat.card J * Nat.card B) =
      Nat.card Q ^ 2 * (Nat.card Q * Nat.card J * Nat.card B) := by
    calc _ = (Nat.card C * Nat.card B) * m := by rw [← hrel]; ring
      _ = Nat.card (C ⊔ B : Subgroup G) * m * Nat.card J := by rw [← hprod]; ring
      _ = Nat.card H * Nat.card J := by rw [hm]
      _ = _ := by rw [hHcard]; ring
  exact ⟨m, (Nat.eq_of_mul_eq_mul_right hpos hkey).symm⟩

end CFSG.ShultStronglyClosedTI.LinearChain
