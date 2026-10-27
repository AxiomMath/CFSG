module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K316

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem isCatalogGroup_quotient_center_of_component (hK : CFSG.Open.IsKGroup G) {L : Subgroup G}
    (hL : CFSG.IsComponent L) : CFSG.Open.IsCatalogGroup (↥L ⧸ Subgroup.center ↥L) := by
  haveI := hL.1.2.1
  exact hK.isCatalogGroup_of_surjective L hL.1.2.2 (QuotientGroup.mk' (Subgroup.center ↥L))
    (QuotientGroup.mk'_surjective _)

section Cat


theorem Hyp36.concl_of_catalog {M E : Subgroup G} {p : ℕ} (hS : AGLEmbeddingD2.KFactSeitzRankTwo)
    (hR : K36OddDefChar) (h : Hyp36 G M p E) {L : Subgroup G} [L.Normal] (hL : CFSG.IsComponent L)
    (hne : ⁅L, pCoreOf 2 M⁆ ≠ ⊥) (hLM : L ⊔ M = ⊤)
    (hcat : CFSG.Open.IsCatalogGroup (↥L ⧸ Subgroup.center ↥L))
    (hAlt : ∀ n : ℕ, 5 ≤ n → Nonempty (↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin n)) →
      K36Concl M p)
    (hSpor : ∀ s : TauCeti.SporadicName,
      Nonempty (↥L ⧸ Subgroup.center ↥L ≃* (TauCeti.CFSGIndex.sporadic s).Group) → K36Concl M p) :
    K36Concl M p := by
  obtain ⟨i, ⟨φ⟩⟩ := hcat
  cases i with
  | cyclic r hr =>
    obtain ⟨a, b, hab⟩ := hL.1.2.2
    have hc : ∀ x y : (TauCeti.CFSGIndex.cyclic r hr).Group, x * y = y * x := fun x y => mul_comm x y
    exact absurd (φ.injective (by rw [map_mul, map_mul]; exact hc (φ a) (φ b))) hab
  | alternating n hn => exact hAlt n hn ⟨φ⟩
  | lie d =>
    by_cases h2 : d.1.characteristic = 2
    · exact h.concl_of_lieEven hS hL hLM hne d φ h2
    · exact (h.false_of_oddLie hS hR hL hne d φ h2).elim
  | sporadic s => exact hSpor s ⟨φ⟩

end Cat

end CFSG.LocalAnalysis.UniquenessCase.UCK
