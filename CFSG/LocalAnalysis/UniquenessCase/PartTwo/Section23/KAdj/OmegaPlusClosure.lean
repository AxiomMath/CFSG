module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.OmegaPlusBar2
import CFSG.RankThree.PartTwo.Sec18.Components
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.NormalClosure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

open CFSG.AGLEmbedding.LeviBlock
open scoped MatrixGroups
open scoped commutatorElement

private theorem center_specialLinear_E09 {K : Type} [Field K] [CharP K 2] {A : SL(2, K)}
    (hA : ∀ A' : SL(2, K), Commute A A') : A = 1 := by
  have hcenter : A ∈ Subgroup.center (SL(2, K)) :=
    Subgroup.mem_center_iff.mpr fun B => (hA B).eq.symm
  obtain ⟨r, hrpow, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hcenter
  have hr1 : r = 1 := CharTwo.sq_injective (by simpa using hrpow)
  refine Subtype.ext ?_
  rw [← hr, hr1]
  simp

private theorem noncommCoprod_injective_E09 {H S : Type} [Group H] [Group S]
    (P : Subgroup H) [P.Normal] (φ₁ φ₂ : S →* H)
    (h₁ : Function.Injective φ₁) (h₂ : Function.Injective φ₂)
    (hc : ∀ A B, Commute (φ₁ A) (φ₂ B))
    (hP₁ : φ₁.range ⊓ P = ⊥) (hP₂ : φ₂.range ⊓ P = ⊥)
    (hz : ∀ A : S, (∀ A' : S, Commute A A') → A = 1) :
    Function.Injective (MonoidHom.noncommCoprod ((QuotientGroup.mk' P).comp φ₁)
      ((QuotientGroup.mk' P).comp φ₂) (fun A B => (hc A B).map (QuotientGroup.mk' P))) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨A, B⟩ hAB
  have hAB' : QuotientGroup.mk' P (φ₁ A) * QuotientGroup.mk' P (φ₂ B) = 1 := hAB
  have hz_eq : QuotientGroup.mk' P (φ₁ A) = QuotientGroup.mk' P (φ₂ B⁻¹) := by
    rw [map_inv]
    exact eq_inv_of_mul_eq_one_left hAB'
  have hcentralA : ∀ A' : S, Commute A A' := by
    intro A'
    have hcomm : Commute (QuotientGroup.mk' P (φ₁ A)) (QuotientGroup.mk' P (φ₁ A')) := by
      have h1 := ((hc A' B⁻¹).map (QuotientGroup.mk' P)).symm
      rwa [← hz_eq] at h1
    have hmem : φ₁ ⁅A, A'⁆ ∈ P := by
      have h1 : ((QuotientGroup.mk' P).comp φ₁) ⁅A, A'⁆ = 1 := by
        rw [map_commutatorElement]
        exact hcomm.commutator_eq
      exact (QuotientGroup.eq_one_iff (N := P) (φ₁ ⁅A, A'⁆)).mp h1
    have hone : φ₁ ⁅A, A'⁆ = 1 := by
      have hbot : φ₁ ⁅A, A'⁆ ∈ (⊥ : Subgroup H) := by
        rw [← hP₁]
        exact ⟨MonoidHom.mem_range.mpr ⟨⁅A, A'⁆, rfl⟩, hmem⟩
      exact Subgroup.mem_bot.mp hbot
    exact commutatorElement_eq_one_iff_commute.mp (h₁ (by rw [hone, map_one]))
  have hA : A = 1 := hz A hcentralA
  have hB : B = 1 := by
    have hmem : φ₂ B ∈ P := by
      have h1 : ((QuotientGroup.mk' P).comp φ₂) B = 1 := by
        have h := hAB
        rw [hA] at h
        simpa only [MonoidHom.noncommCoprod_apply, MonoidHom.comp_apply, map_one,
          one_mul] using h
      exact (QuotientGroup.eq_one_iff (N := P) (φ₂ B)).mp h1
    have hone : φ₂ B = 1 := by
      have hbot : φ₂ B ∈ (⊥ : Subgroup H) := by
        rw [← hP₂]
        exact ⟨MonoidHom.mem_range.mpr ⟨B, rfl⟩, hmem⟩
      exact Subgroup.mem_bot.mp hbot
    exact h₂ (by rw [hone, map_one])
  rw [hA, hB]
  rfl

private theorem map_eq_top_of_card_E09 {H S : Type} [Group H] [Finite H] [Group S] [Finite S]
    (P : Subgroup H) [P.Normal] (φ₁ φ₂ : S →* H) (h₁ : Function.Injective φ₁)
    (h₂ : Function.Injective φ₂) (hc : ∀ A B, Commute (φ₁ A) (φ₂ B))
    (hP₁ : φ₁.range ⊓ P = ⊥) (hP₂ : φ₂.range ⊓ P = ⊥)
    (hz : ∀ A : S, (∀ A' : S, Commute A A') → A = 1)
    (hcard : Nat.card (H ⧸ P) = Nat.card S ^ 2) {N : Subgroup H}
    (hN₁ : φ₁.range ≤ N) (hN₂ : φ₂.range ≤ N) :
    N.map (QuotientGroup.mk' P) = ⊤ := by
  haveI : Finite (H ⧸ P) :=
    Finite.of_surjective (QuotientGroup.mk' P) (QuotientGroup.mk'_surjective P)
  have hinj : Function.Injective (MonoidHom.noncommCoprod
      ((QuotientGroup.mk' P).comp φ₁) ((QuotientGroup.mk' P).comp φ₂)
      (fun A B => (hc A B).map (QuotientGroup.mk' P))) :=
    noncommCoprod_injective_E09 P φ₁ φ₂ h₁ h₂ hc hP₁ hP₂ hz
  have hcard' : Nat.card (H ⧸ P) ≤ Nat.card (S × S) := by
    rw [Nat.card_prod, hcard]
    exact le_of_eq (pow_two (Nat.card S))
  have hsurj : Function.Surjective (MonoidHom.noncommCoprod
      ((QuotientGroup.mk' P).comp φ₁) ((QuotientGroup.mk' P).comp φ₂)
      (fun A B => (hc A B).map (QuotientGroup.mk' P))) :=
    (hinj.bijective_of_nat_card_le hcard').surjective
  rw [eq_top_iff]
  rintro y -
  obtain ⟨⟨A, B⟩, hxy⟩ := hsurj y
  rw [Subgroup.mem_map]
  refine ⟨φ₁ A * φ₂ B, N.mul_mem (hN₁ (MonoidHom.mem_range.mpr ⟨A, rfl⟩))
    (hN₂ (MonoidHom.mem_range.mpr ⟨B, rfl⟩)), ?_⟩
  rw [map_mul, ← hxy]
  simp only [MonoidHom.noncommCoprod_apply, MonoidHom.comp_apply]

private noncomputable def rootEmbTwoCore_E09 {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K) :
    SL(2, K) →* ↥(Hinf (plusFlagStab K 3 ({1} : Finset ℕ))) :=
  (plusRootEmbTwo K).codRestrict _
    (fun A => plusRootEmbTwo_range_le_hinf hK (MonoidHom.mem_range.mpr ⟨A, rfl⟩))

private noncomputable def rootEmbOneCore_E09 {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K) :
    SL(2, K) →* ↥(Hinf (plusFlagStab K 3 ({1} : Finset ℕ))) :=
  (plusRootEmbOne K).codRestrict _
    (fun A => plusRootEmbOne_range_le_hinf hK (MonoidHom.mem_range.mpr ⟨A, rfl⟩))

private theorem injective_rootEmbTwoCore_E09 {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K) : Function.Injective (rootEmbTwoCore_E09 hK) :=
  (MonoidHom.injective_codRestrict (plusRootEmbTwo K) _ _).mpr (plusRootEmbTwo_injective K)

private theorem injective_rootEmbOneCore_E09 {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K) : Function.Injective (rootEmbOneCore_E09 hK) :=
  (MonoidHom.injective_codRestrict (plusRootEmbOne K) _ _).mpr (plusRootEmbOne_injective K)

private theorem range_rootEmbTwoCore_E09 {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K) :
    (rootEmbTwoCore_E09 hK).range =
      (plusRootEmbTwo K).range.subgroupOf (Hinf (plusFlagStab K 3 ({1} : Finset ℕ))) := by
  ext x
  constructor
  · intro hx
    obtain ⟨A, hA⟩ := MonoidHom.mem_range.mp hx
    exact MonoidHom.mem_range.mpr ⟨A, congrArg Subtype.val hA⟩
  · intro hx
    obtain ⟨A, hA⟩ := MonoidHom.mem_range.mp (Subgroup.mem_subgroupOf.mp hx)
    exact MonoidHom.mem_range.mpr ⟨A, Subtype.ext hA⟩

private theorem range_rootEmbOneCore_E09 {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K) :
    (rootEmbOneCore_E09 hK).range =
      (plusRootEmbOne K).range.subgroupOf (Hinf (plusFlagStab K 3 ({1} : Finset ℕ))) := by
  ext x
  constructor
  · intro hx
    obtain ⟨A, hA⟩ := MonoidHom.mem_range.mp hx
    exact MonoidHom.mem_range.mpr ⟨A, congrArg Subtype.val hA⟩
  · intro hx
    obtain ⟨A, hA⟩ := MonoidHom.mem_range.mp (Subgroup.mem_subgroupOf.mp hx)
    exact MonoidHom.mem_range.mpr ⟨A, Subtype.ext hA⟩

private theorem inf_pCore_rootEmbTwoCore_E09 {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K) :
    (rootEmbTwoCore_E09 hK).range ⊓
      CFSG.pCore 2 ↥(Hinf (plusFlagStab K 3 ({1} : Finset ℕ))) = ⊥ := by
  rw [range_rootEmbTwoCore_E09]
  exact plusRootEmbTwo_inf_pCore hK

private theorem inf_pCore_rootEmbOneCore_E09 {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K) :
    (rootEmbOneCore_E09 hK).range ⊓
      CFSG.pCore 2 ↥(Hinf (plusFlagStab K 3 ({1} : Finset ℕ))) = ⊥ := by
  rw [range_rootEmbOneCore_E09]
  exact plusRootEmbOne_inf_pCore hK

theorem normal_closure_plusRoots {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K) (N : Subgroup (PlusLin K))
    (hNK : N ≤ Hinf (plusFlagStab K 3 ({1} : Finset ℕ)))
    (hnorm : Hinf (plusFlagStab K 3 ({1} : Finset ℕ)) ≤ Subgroup.normalizer (N : Set (PlusLin K)))
    (h₂ : (plusRootEmbTwo K).range ≤ N) (h₁ : (plusRootEmbOne K).range ≤ N) :
    N = Hinf (plusFlagStab K 3 ({1} : Finset ℕ)) := by
  haveI : Finite (PlusLin K) :=
    Finite.of_injective (fun g : PlusLin K => (g : (Fin 3 ⊕ Fin 3 → K) → (Fin 3 ⊕ Fin 3 → K)))
      DFunLike.coe_injective
  let P : Subgroup ↥(Hinf (plusFlagStab K 3 ({1} : Finset ℕ))) :=
    CFSG.pCore 2 ↥(Hinf (plusFlagStab K 3 ({1} : Finset ℕ)))
  haveI hPnorm : P.Normal := CFSG.pCore_normal
  have hNj : (N.subgroupOf (Hinf (plusFlagStab K 3 ({1} : Finset ℕ)))).map
      (QuotientGroup.mk' P) = ⊤ :=
    map_eq_top_of_card_E09 P (rootEmbTwoCore_E09 hK) (rootEmbOneCore_E09 hK)
      (injective_rootEmbTwoCore_E09 hK) (injective_rootEmbOneCore_E09 hK)
      (fun A B => Subtype.ext (commute_plusRootEmbTwo_plusRootEmbOne K A B).eq)
      (inf_pCore_rootEmbTwoCore_E09 hK) (inf_pCore_rootEmbOneCore_E09 hK)
      (fun A hA => center_specialLinear_E09 (A := A) hA)
      (card_bar2_hinf_plusFlagStab hK)
      ((le_of_eq (range_rootEmbTwoCore_E09 hK)).trans (Subgroup.subgroupOf_mono _ h₂))
      ((le_of_eq (range_rootEmbOneCore_E09 hK)).trans (Subgroup.subgroupOf_mono _ h₁))
  exact eq_of_map_pCore_eq_top
    (K := Hinf (plusFlagStab K 3 ({1} : Finset ℕ)))
    (CFSG.RankThree.PartTwo.Sec18.commutator_inSubgroup_perfectResidual _) hNK hnorm hNj

end CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE
