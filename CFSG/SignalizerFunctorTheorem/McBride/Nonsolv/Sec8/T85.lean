module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.T85.Hat
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.T85.Setup
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.T85.Gen

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}
  {r : ℕ} {S : Subgroup G}

theorem theorem_8_5
    (h : Counterexample p A θ) {E K : Subgroup G} (hB : TypeB p A θ E K)
    {F : Subgroup G} (hF : F ∈ signalizerFunctorEk p 1 A) (hFE : F ≠ E) :
    IsDirectProduct {Y | ∃ K' ∈ Ind (thetaOf θ F), Y = wK θ E K'} (sSup (Msig p A θ)) ∧
      (∀ K' ∈ Ind (thetaOf θ F), ∀ K'' ∈ Ind (thetaOf θ F),
        ∃ a ∈ A, wK θ E K'' = (wK θ E K').map (MulAut.conj a).toMonoidHom) ∧
      ∀ K' ∈ Ind (thetaOf θ F), A ⊓ Subgroup.normalizer (wK θ E K' : Set G) = E ⊔ F := by
  have hBc := hB.toTypeBCore
  have hΛ := isRegFam_line_of_typeB h hBc hF hFE
  rw [ind_eq_lcal_line_of_typeB h hBc hF hFE]
  refine ⟨?_, ?_, ?_⟩
  · refine T85.isDirectProduct_of_commute ?_ ?_ h.lemma_6_4
    · rintro _ ⟨K₁, hK₁, rfl⟩ _ ⟨K₂, hK₂, rfl⟩ hne
      exact T85.commute_wK h hB hF hFE hK₁ hK₂ fun heq => hne (by rw [heq])
    · rw [T85.sSup_wK_eq h hBc hF hFE, T85.sSup_msig_eq h hB hF hFE]
  · intro K' hK' K'' hK''
    obtain ⟨a, ha, rfl⟩ := hΛ.transitive K' hK' K'' hK''
    exact ⟨a, ha, (T85.map_conj_wK h hBc ha K').symm⟩
  · intro K' hK'
    refine le_antisymm (fun a ha => ?_) (fun a ha => ?_)
    · obtain ⟨haA, haN⟩ := Subgroup.mem_inf.mp ha
      have h1 : (wK θ E K').map (MulAut.conj a).toMonoidHom = wK θ E K' :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp haN
      rw [T85.map_conj_wK h hBc haA K'] at h1
      have h2 := T85.wK_injOn h hB hF hFE (hΛ.map_conj_mem a haA K' hK') hK' h1
      rw [← hΛ.stabilizer K' hK']
      exact Subgroup.mem_inf.mpr ⟨haA, Subgroup.mem_normalizer_iff_map_conj_eq.mpr h2⟩
    · rw [← hΛ.stabilizer K' hK'] at ha
      obtain ⟨haA, haN⟩ := Subgroup.mem_inf.mp ha
      have h4 : K'.map (MulAut.conj a).toMonoidHom = K' :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp haN
      have h3 : (wK θ E K').map (MulAut.conj a).toMonoidHom = wK θ E K' := by
        rw [T85.map_conj_wK h hBc haA K', h4]
      exact Subgroup.mem_inf.mpr ⟨haA, Subgroup.mem_normalizer_iff_map_conj_eq.mpr h3⟩

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
