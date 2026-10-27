module

public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagProj

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.ComponentClassification.PresentationLocal
open scoped commutatorElement

namespace TableB

section B2der

variable {K : Type} [Field K] [Finite K]

theorem index_commutator_largeEvenSpGroup (hK : Nat.card K = 2) :
    (commutator (LargeEvenSpGroup K 2)).index = 2 := by
  obtain ⟨e⟩ := nonempty_largeEvenSpGroup_equiv_sympFour hK
  have hmap : (commutator (LargeEvenSpGroup K 2)).map e.toMonoidHom = commutator sympFour := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.2 e.surjective]
  rw [← Subgroup.index_map_equiv _ e,
    show ((e : LargeEvenSpGroup K 2 ≃* sympFour) : LargeEvenSpGroup K 2 →* sympFour) =
      e.toMonoidHom from rfl, hmap, commutator_sympFour,
    Subgroup.index_comap_of_surjective _ omegaPerm_surjective, alternatingGroup.index_eq_two]

theorem mem_largeEvenSpGroup_of_gsp (hK : Nat.card K = 2) {A : GL (Fin 2 ⊕ Fin 2) K}
    (hA : A ∈ LargeEvenGSpSet K 2) : A ∈ LargeEvenSpGroup K 2 := by
  obtain ⟨μ, hμ0, hA⟩ := hA
  have hμ : μ = 1 := by
    have := CFSG.Monster.Existence.Compat.subsingleton_units_of_card_two hK
    exact congrArg Units.val (Subsingleton.elim (Units.mk0 μ hμ0) 1)
  apply Subgroup.subset_closure
  show Matrix.transpose (A : Matrix _ _ K) * LargeEvenSpForm K 2 * (A : Matrix _ _ K) =
    LargeEvenSpForm K 2
  rw [hA, hμ, one_smul]

theorem mem_normalizer_commutator {G : Type*} [Group G] {S : Subgroup G} {A : G} (hA : A ∈ S) :
    A ∈ Subgroup.normalizer ((⁅S, S⁆ : Subgroup G) : Set G) := by
  have hle : ∀ B ∈ S, ⁅S, S⁆ ≤ ⁅S, S⁆.comap (MulAut.conj B).toMonoidHom := by
    intro B hB
    rw [Subgroup.commutator_le]
    intro x hx y hy
    show B * ⁅x, y⁆ * B⁻¹ ∈ ⁅S, S⁆
    have h : B * ⁅x, y⁆ * B⁻¹ = ⁅B * x * B⁻¹, B * y * B⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    rw [h]
    exact Subgroup.commutator_mem_commutator (S.mul_mem (S.mul_mem hB hx) (S.inv_mem hB))
      (S.mul_mem (S.mul_mem hB hy) (S.inv_mem hB))
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => hle A hA hh, fun hh => ?_⟩
  have := hle A⁻¹ (S.inv_mem hA) hh
  simpa [mul_assoc] using this

theorem mem_commutator_iff_coe {G : Type*} [Group G] {S : Subgroup G} (b : S) :
    b ∈ commutator S ↔ (b : G) ∈ ⁅S, S⁆ := by
  rw [← Subgroup.map_subtype_commutator]
  constructor
  · intro hb
    exact ⟨b, hb, rfl⟩
  · rintro ⟨c, hc, hcb⟩
    rwa [← Subtype.ext hcb]

theorem ggOutdiagCyclic_b2der (hK : Nat.card K = 2) :
    GGOutdiagCyclic (LargeEvenProj ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆)
      (LargeEvenMatConjImage (LargeEvenProjMk ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆)
        (LargeEvenGSpSet K 2)) := by
  obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.mp (index_commutator_largeEvenSpGroup hK)
  refine ggOutdiagCyclic_of_decomp
    (fun A hA => mem_normalizer_commutator (mem_largeEvenSpGroup_of_gsp hK hA))
    ⟨a, mem_normalizer_commutator a.2⟩ ?_
  intro A hA
  have hASp := mem_largeEvenSpGroup_of_gsp hK hA
  rcases ha ⟨A, hASp⟩ with ⟨h1, -⟩ | ⟨h1, -⟩
  · refine ⟨A * a, -1, 1, (mem_commutator_iff_coe (⟨A, hASp⟩ * a)).mp h1, one_mem _, ?_⟩
    simp
  · refine ⟨A, 0, 1, (mem_commutator_iff_coe ⟨A, hASp⟩).mp h1, one_mem _, ?_⟩
    simp

end B2der

end TableB

theorem recipeB2der_outdiag {Q : LargeEvenRawCont} (h : LargeEvenRecipeSymplectic 2 2 true Q) :
    LargeEvenRecipeSymplectic 2 2 true fun R _ I F => Q R I F ∧ GGOutdiagCyclic R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, hQ, TableB.ggOutdiagCyclic_b2der hK⟩

end CFSG.StandardType
