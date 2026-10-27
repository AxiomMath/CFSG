module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Quasithin.Background.B6Sections
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22p22r_isPerfect_subgroupOf {K H : Subgroup G} (hKH : K ≤ H) (hK : ⁅K, K⁆ = K) :
    Group.IsPerfect ↥(K.subgroupOf H) := by
  rw [Subgroup.isPerfect_iff]
  apply Subgroup.map_injective H.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hKH, hK]

noncomputable def uc22p22rPhi {K H : Subgroup G} (hKH : K ≤ H) : ↥(K.subgroupOf H) →* Bar2 K :=
  (QuotientGroup.mk' (CFSG.pCore 2 ↥K)).comp (Subgroup.subgroupOfEquivOfLe hKH).toMonoidHom

theorem uc22p22rPhi_surjective {K H : Subgroup G} (hKH : K ≤ H) :
    Function.Surjective (uc22p22rPhi hKH) :=
  (QuotientGroup.mk'_surjective _).comp (Subgroup.subgroupOfEquivOfLe hKH).surjective

theorem uc22p22rPhi_ker {K H : Subgroup G} (hKH : K ≤ H) (n : ↥(K.subgroupOf H))
    (hn : n ∈ (uc22p22rPhi hKH).ker) : (((n : ↥H) : H) : G) ∈ pCoreOf 2 K := by
  have h : (Subgroup.subgroupOfEquivOfLe hKH n) ∈ CFSG.pCore 2 ↥K := by
    have h1 : (uc22p22rPhi hKH) n = 1 := hn
    exact (QuotientGroup.eq_one_iff _).1 h1
  exact ⟨_, h, rfl⟩

theorem uc22p22r_quasisimple_quot {K H : Subgroup G} (hKH : K ≤ H)
    (hKq : CFSG.Open.IsQuasisimple (Bar2 K)) :
    CFSG.Open.IsQuasisimple (↥(K.subgroupOf H) ⧸ (uc22p22rPhi hKH).ker) :=
  CFSG.Open.IsQuasisimple.of_mulEquiv
    (QuotientGroup.quotientKerEquivOfSurjective _ (uc22p22rPhi_surjective hKH)) hKq

theorem uc22p22r_mem_normalizer_of_subgroupOf {K H : Subgroup G} (hKH : K ≤ H) {x : G} (hxH : x ∈ H)
    (h : (⟨x, hxH⟩ : ↥H) ∈ normalizer ((K.subgroupOf H : Subgroup ↥H) : Set ↥H)) :
    x ∈ normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro k
  have hmem : ∀ y : ↥H, (y : G) ∈ K ↔ ((⟨x, hxH⟩ * y * ⟨x, hxH⟩⁻¹ : ↥H) : G) ∈ K := fun y =>
    Subgroup.mem_normalizer_iff.1 h y
  constructor
  · intro hk
    exact (hmem ⟨k, hKH hk⟩).1 hk
  · intro hk
    have hkH : k ∈ H := by
      have : x⁻¹ * (x * k * x⁻¹) * x ∈ H := H.mul_mem (H.mul_mem (H.inv_mem hxH) (hKH hk)) hxH
      simpa [mul_assoc] using this
    exact (hmem ⟨k, hkH⟩).2 hk

end CFSG.LocalAnalysis.UniquenessCase.UC22
