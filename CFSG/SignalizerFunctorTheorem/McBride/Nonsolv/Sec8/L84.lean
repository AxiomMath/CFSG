module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.L83
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.L84.Gen
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.L84.Sylow

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}
  {r : ℕ} {S : Subgroup G}

theorem lemma_8_4
    (h : Counterexample p A θ) {E K : Subgroup G} (hB : TypeB p A θ E K)
    {F : Subgroup G} (hF : F ∈ signalizerFunctorEk p 1 A) (hFE : F ≠ E) {L : Subgroup G}
    (hL : L ∈ Ind (thetaOf θ (E ⊔ F))) {K' : Subgroup G} (hK' : K' ∈ Ind (thetaOf θ F))
    (hne : K' ⊓ Subgroup.centralizer (E : Set G) ≠ L) :
    lHat (thetaOf θ E) L ≤ Subgroup.centralizer (K' : Set G) := by
  have hP2 : E ⊔ F ∈ signalizerFunctorEk p 2 A := h.sup_mem_E2_of_ne hB.mem hF hFE.symm
  have hΩF := h.isRegFam_line_of_typeB hB.toTypeBCore hF hFE
  rw [h.ind_eq_lcal_line_of_typeB hB.toTypeBCore hF hFE] at hK'
  have hL' := hL
  rw [h.ind_plane_eq_inf_centralizer_of_typeB hB.toTypeBCore hF hFE] at hL'
  obtain ⟨L₁, hL₁, rfl⟩ := hL'
  have hL₁K' : L₁ ≠ K' := fun heq => hne (by rw [heq])
  have hLK' : L₁ ⊓ Subgroup.centralizer (E : Set G) ≤ Subgroup.centralizer (K' : Set G) := by
    refine inf_le_left.trans ?_
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hΩF.isDirectProduct.commute L₁ hL₁ K' hK' hL₁K' x hx y hy).eq.symm
  have key : ∀ (r' : ℕ) (S' : Subgroup G), InPiTheta A θ r' → IsSr p A θ r' S' →
      lHat (thetaOf θ E) (L₁ ⊓ Subgroup.centralizer (E : Set G)) ≤
        Subgroup.centralizer ((K' ⊓ S' : Subgroup G) : Set G) := by
    intro r' S' hr' hS'
    refine (h.lemma_8_3 hr' hS' hB hP2 le_sup_left hL).trans (sup_le ?_ ?_)
    · exact L83.zOf_le_centralizer inf_le_right
    · exact hLK'.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr inf_le_left))
  obtain ⟨a, haA, ha1, hFa⟩ := exists_zpowers_eq_of_mem_signalizerFunctorEk_one h.prime hF
  have haF : a ∈ F := hFa ▸ Subgroup.mem_zpowers a
  have hθa : thetaOf θ F = θ a := h.thetaOf_line hF haF ha1
  have hK'H : K' ≤ thetaOf θ F := lcal_le hK'
  have hXK : K' ⊓ Subgroup.centralizer
      ((lHat (thetaOf θ E) (L₁ ⊓ Subgroup.centralizer (E : Set G)) : Subgroup G) : Set G) = K' := by
    refine L84.eq_of_forall_coprime_relIndex inf_le_left ?_
    intro r' hr' hdvd
    have hdvd' : r' ∣ Nat.card (θ a) := by
      rw [← hθa]
      exact hdvd.trans (Subgroup.card_dvd_of_le hK'H)
    have hπ : InPiTheta A θ r' := ⟨hr', a, haA, ha1, hdvd'⟩
    obtain ⟨R, S', hRH, hRp, hidx, hRS', hS'⟩ :=
      L84.exists_isSr_of_sylow h hF hr' (InPiTheta.ne_p h hπ)
    refine ⟨R ⊓ K', le_inf inf_le_right ?_, ?_⟩
    · have h1 := Subgroup.le_centralizer_iff.mp (key r' S' hπ hS')
      have h2 : R ⊓ K' ≤ K' ⊓ S' := fun x hx => ⟨hx.2, hRS' hx.1⟩
      exact h2.trans h1
    · exact (IsDirectProduct.sylow_decomp hΩF.isDirectProduct hr' hRH hRp hidx).2 K' hK'
  exact Subgroup.le_centralizer_iff.mp (hXK.symm.le.trans inf_le_right)

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
