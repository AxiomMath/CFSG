module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.L83.Gen
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.L83.Simple
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec7.Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec7.L74.Center
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec7.StructB

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace L83

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}
  {r : ℕ} {S : Subgroup G} {E K : Subgroup G}

theorem zOf_inf_centralizer_le
    (h : Counterexample p A θ) (hr : InPiTheta A θ r)
    (hS : IsSr p A θ r S) (hB : TypeBCore p A θ E K) {B : Subgroup G}
    (hB2 : B ∈ signalizerFunctorEk p 2 A) (hEB : E ≤ B) :
    zOf (S ⊓ Subgroup.centralizer (E : Set G)) ≤
      ⨆ K' ∈ Ind (thetaOf θ B), vK (Ind (thetaOf θ B)) (vOf S E) K' := by
  obtain ⟨F, hF, -, hFE, hsup⟩ := h.exists_line_sup_eq_of_mem_E2 hB2 hB.mem hEB
  obtain ⟨e, he, he1, hEe⟩ := exists_zpowers_eq_of_mem_signalizerFunctorEk_one h.prime hB.mem
  have heE : e ∈ E := hEe ▸ Subgroup.mem_zpowers e
  have hθe : thetaOf θ E = θ e := h.thetaOf_line hB.mem heE he1
  have hCe : S ⊓ Subgroup.centralizer (E : Set G) = S ⊓ Subgroup.centralizer {e} := by
    rw [← hEe, centralizer_zpowers_eq_singleton]
  obtain ⟨hPθ, hPp, hidx, -⟩ := h.sylow_of_isSr hr hS he he1
  have hPH : S ⊓ Subgroup.centralizer (E : Set G) ≤ thetaOf θ E := by
    rw [hCe, hθe]
    exact hPθ
  have hPp' : IsPGroup r ↥(S ⊓ Subgroup.centralizer (E : Set G)) := by
    rw [hCe]
    exact hPp
  have hidx' : Nat.Coprime ((S ⊓ Subgroup.centralizer (E : Set G)).relIndex (thetaOf θ E)) r := by
    rw [hCe, hθe]
    exact hidx
  have hΩ := h.isRegFam_ind_E_of_typeB hB
  have hF' : ∀ f ∈ F, ∀ J ∈ Ind (thetaOf θ E), J.map (MulAut.conj f).toMonoidHom ∈
      Ind (thetaOf θ E) := fun f hf J hJ => hΩ.map_conj_mem f (hF.1 hf) J hJ
  obtain ⟨hdpP, -⟩ := IsDirectProduct.sylow_decomp hΩ.isDirectProduct hr.1 hPH hPp' hidx'
  have hdpZ := L74.isDirectProduct_zOf hdpP
  rw [← hdpZ.sSup_eq]
  refine sSup_le ?_
  rintro _ ⟨_, ⟨Q, hQ, rfl⟩, rfl⟩
  have hK₀ : smear Q F ∈ Ind (thetaOf θ B) := by
    rw [← hsup, h.ind_plane_eq_smear_of_typeB hB hF hFE]
    exact ⟨Q, hQ, rfl⟩
  refine le_trans ?_ (le_iSup₂_of_le (smear Q F) hK₀ le_rfl)
  have hQP : zOf (S ⊓ Subgroup.centralizer (E : Set G) ⊓ Q) ≤
      zOf (S ⊓ Subgroup.centralizer (E : Set G)) :=
    L74.zOf_le_zOf_of_mem hdpP ⟨Q, hQ, rfl⟩
  refine le_vK (hQP.trans (zOf_inf_centralizer_le_vOf S E)) ?_
  intro K' hK' hne
  rw [← hsup, h.ind_plane_eq_smear_of_typeB hB hF hFE] at hK'
  obtain ⟨Q', hQ', rfl⟩ := hK'
  have hQnot : Q ∉ RegFam.conjOrbit Q' F := fun hmem =>
    hne (smear_eq_of_mem_conjOrbit hmem).symm
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hyQ : y ∈ Q := (inf_le_right : S ⊓ Subgroup.centralizer (E : Set G) ⊓ Q ≤ Q)
    (zOf_le _ hy)
  exact (RegFam.commute_orbitClosure hΩ.isDirectProduct hF' hQ' hQ hQnot x
    (smear_le_orbitClosure Q' F hx) y (le_orbitClosure Q F hyQ)).eq.symm

end L83

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
