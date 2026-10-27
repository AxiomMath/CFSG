module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.L83.Gen
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec7.L74

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace L83

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}
  {r : ℕ} {S : Subgroup G} {E K : Subgroup G}

theorem zOf_inf_centralizer_le_of_mem
    (h : Counterexample p A θ) (hr : InPiTheta A θ r)
    (hS : IsSr p A θ r S) (hB : TypeBCore p A θ E K) {B : Subgroup G}
    (hB2 : B ∈ signalizerFunctorEk p 2 A) (hEB : E ≤ B) {a : G} (haB : a ∈ B) (haE : a ∉ E)
    (ha1 : a ≠ 1) :
    zOf S ⊓ Subgroup.centralizer {a} ≤
      ⨆ K' ∈ Ind (thetaOf θ B), vK (Ind (thetaOf θ B)) (vOf S E) K' := by
  have haA : a ∈ A := hB2.1 haB
  have hF₁ := h.zpowers_mem_E1 haA ha1
  have hF₁E : Subgroup.zpowers a ≠ E := fun heq => haE (heq ▸ Subgroup.mem_zpowers a)
  have hsup : E ⊔ Subgroup.zpowers a = B := by
    have hP := h.sup_mem_E2_of_ne hB.mem hF₁ hF₁E.symm
    exact Subgroup.eq_of_le_of_card_ge (sup_le hEB (Subgroup.zpowers_le.mpr haB))
      (by rw [hB2.2, hP.2])
  have hdp := h.lemma_7_4_c hr hS haA ha1 (Or.inr ⟨E, K, hB, haE⟩)
  have h1 : zOf S ⊓ Subgroup.centralizer {a} ≤ zOf S ⊓ θ a :=
    le_inf inf_le_left fun x hx =>
      Counterexample.inf_centralizer_le_of_isSr hS haA ha1 ⟨zOf_le S hx.1, hx.2⟩
  refine h1.trans ?_
  rw [← hdp.sSup_eq]
  refine sSup_le ?_
  rintro _ ⟨L', hL', rfl⟩
  have hθa : thetaOf θ (Subgroup.zpowers a) = θ a := h.isFunctor.thetaOf_zpowers haA ha1
  have hIndEq : Ind (θ a) = lcal (θ a) := by
    rw [← hθa]
    exact h.ind_eq_lcal_line_of_typeB hB hF₁ hF₁E
  have hΩa : IsRegFam A (θ a) (lcal (θ a)) (E ⊔ Subgroup.zpowers a) := by
    rw [← hθa]
    exact h.isRegFam_line_of_typeB hB hF₁ hF₁E
  have hIndB : Ind (thetaOf θ B) =
      {C | ∃ R ∈ lcal (θ a), C = R ⊓ Subgroup.centralizer (E : Set G)} := by
    rw [← hsup, h.ind_plane_eq_inf_centralizer_of_typeB hB hF₁ hF₁E, hθa]
  rw [hIndEq] at hL'
  have hK' : L' ⊓ Subgroup.centralizer (E : Set G) ∈ Ind (thetaOf θ B) := by
    rw [hIndB]
    exact ⟨L', hL', rfl⟩
  refine le_trans ?_ (le_iSup₂_of_le _ hK' le_rfl)
  refine le_vK (inf_le_left.trans (zOf_le_vOf S E)) ?_
  intro K'' hK'' hne
  rw [hIndB] at hK''
  obtain ⟨L'', hL'', rfl⟩ := hK''
  have hne' : L'' ≠ L' := fun heq => hne (by rw [heq])
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (hΩa.isDirectProduct.commute L'' hL'' L' hL' hne' x (Subgroup.mem_inf.mp hx).1 y
    (Subgroup.mem_inf.mp hy).2).eq.symm

end L83

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
