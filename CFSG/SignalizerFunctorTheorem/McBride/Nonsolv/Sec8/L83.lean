module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.L82
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.L83.Comm
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.L83.Gen
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.L83.Hat
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.L83.Simple
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.L83.ZW

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}
  {r : ℕ} {S : Subgroup G}

theorem lemma_8_3
    (h : Counterexample p A θ) (hr : InPiTheta A θ r) (hS : IsSr p A θ r S)
    {E K : Subgroup G} (hB : TypeB p A θ E K) {B : Subgroup G}
    (hB2 : B ∈ signalizerFunctorEk p 2 A) (hEB : E ≤ B) {L : Subgroup G}
    (hL : L ∈ Ind (thetaOf θ B)) : lHat (thetaOf θ E) L ≤ zOf S ⊔ L := by
  obtain ⟨F, hF, -, hFE, hsup⟩ := h.exists_line_sup_eq_of_mem_E2 hB2 hB.mem hEB
  have hΩB : IsRegFam A (thetaOf θ B) (Ind (thetaOf θ B)) B := by
    have h1 := h.isRegFam_ind_plane_of_typeB hB.toTypeBCore hF hFE
    rwa [hsup] at h1
  have hcomm : ∀ K₁ ∈ Ind (thetaOf θ B), ∀ K₂ ∈ Ind (thetaOf θ B), K₁ ≠ K₂ →
      K₁ ≤ Subgroup.centralizer (K₂ : Set G) := by
    intro K₁ hK₁ K₂ hK₂ hne x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hΩB.isDirectProduct.commute K₁ hK₁ K₂ hK₂ hne x hx y hy).eq.symm
  obtain ⟨hLZ, hN⟩ := L83.commutator_normalized hcomm (L83.vOf_le_centralizer S E)
    (L83.zOf_le_vOf S E) (L83.zOf_le_iSup_vK h hr hS hB.toTypeBCore hB2 hEB) hL
  obtain ⟨Q₀, hQ₀, rfl⟩ : ∃ Q₀ ∈ Ind (thetaOf θ E), L = smear Q₀ F := by
    have hL' := hL
    rw [← hsup, h.ind_plane_eq_smear_of_typeB hB.toTypeBCore hF hFE] at hL'
    obtain ⟨Q₀, hQ₀, hLQ⟩ := hL'
    exact ⟨Q₀, hQ₀, hLQ⟩
  have hFst : CFSG.inSubgroup CFSG.generalizedFitting (thetaOf θ E) ≤
      thetaOf θ A ⊔ zOf S := h.lemma_8_2 hr hS hB
  have hHB : sSup (Ind (thetaOf θ B)) = thetaOf θ B := hΩB.isDirectProduct.sSup_eq
  have hDle : thetaOf θ A ≤ thetaOf θ B := thetaOf_anti hB2.1
  have hHEB : thetaOf θ B ≤ thetaOf θ E := thetaOf_anti hEB
  have hNB : thetaOf θ B ⊔ zOf S ≤
      Subgroup.normalizer ((⁅smear Q₀ F ⊔ zOf S, smear Q₀ F ⊔ zOf S⁆ : Subgroup G) : Set G) := by
    have hN' := hN
    rw [hHB] at hN'
    exact (sup_comm _ _).le.trans hN'
  unfold lHat
  refine sSup_le ?_
  rintro R ⟨hR, hRL⟩
  have hRle : R ≤ ⁅smear Q₀ F ⊔ zOf S, smear Q₀ F ⊔ zOf S⁆ := by
    refine L83.le_of_isSimpleGroup_of_commutator_ne_one
      (X := ⁅smear Q₀ F, smear Q₀ F⁆) ?_ ?_ ?_ ?_ ?_
    · exact (mem_lcal_iff.mp hR).2.2.1
    · intro x hx
      exact hNB (sup_le_sup_right hDle _
        (hFst (L83.le_inSubgroup_generalizedFitting_of_mem_lcal hR hx)))
    · intro x hx
      have hxL : x ∈ smear Q₀ F := L83.commutator_self_le _ hx
      exact L83.le_normalizer_of_mem_lcal_E h hB.toTypeBCore hR
        (hHEB (hΩB.isDirectProduct.le hL hxL))
    · exact Subgroup.commutator_mono le_sup_left le_sup_left
    · have hnot := L83.not_commutator_le_centralizer h hB.toTypeBCore hF hFE hQ₀ hR hRL
      rw [IsConcreteLE.not_le_iff_exists] at hnot
      obtain ⟨x, hx, hxn⟩ := hnot
      rw [Subgroup.mem_centralizer_iff] at hxn
      push Not at hxn
      obtain ⟨r', hr', hne⟩ := hxn
      exact ⟨x, hx, r', hr', fun h1 => hne (commutatorElement_eq_one_iff_mul_comm.mp h1).symm⟩
  exact hRle.trans (hLZ.trans (sup_comm _ _).le)

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
