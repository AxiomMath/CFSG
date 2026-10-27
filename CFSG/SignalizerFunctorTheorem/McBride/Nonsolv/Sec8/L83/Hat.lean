module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.L83.Comm
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.L83.Simple
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec7.StructB

public section

open CFSG.Open
open scoped commutatorElement

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace L83

section Generic

variable {G : Type*} [Group G]

theorem le_inSubgroup_generalizedFitting_of_mem_lcal {Y J : Subgroup G} (hJ : J ∈ lcal Y) :
    J ≤ CFSG.inSubgroup CFSG.generalizedFitting Y := by
  have h1 := CFSG.LocalCores.component_le_layer (T515f.isComponent_of_mem_lcal hJ)
  have h2 : CFSG.layer ↥Y ≤ CFSG.generalizedFitting ↥Y := le_sup_right
  calc J = (J.subgroupOf Y).map Y.subtype := (Subgroup.map_subgroupOf_eq_of_le (lcal_le hJ)).symm
    _ ≤ (CFSG.generalizedFitting ↥Y).map Y.subtype := Subgroup.map_mono (h1.trans h2)

theorem not_isMulCommutative_of_le {X Y : Subgroup G} (hXY : X ≤ Y) (hX : ¬ IsMulCommutative X) :
    ¬ IsMulCommutative Y := by
  intro hY
  apply hX
  refine isMulCommutative_iff.mpr fun a b => Subtype.ext ?_
  have h1 := congrArg Subtype.val (isMulCommutative_iff.mp hY ⟨a, hXY a.2⟩ ⟨b, hXY b.2⟩)
  exact h1

end Generic

section Setting

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}
  {E K : Subgroup G}

theorem le_normalizer_of_mem_lcal_E
    (h : Counterexample p A θ) (hB : TypeBCore p A θ E K)
    {R : Subgroup G} (hR : R ∈ lcal (thetaOf θ E)) :
    thetaOf θ E ≤ Subgroup.normalizer (R : Set G) := by
  have hΩ := h.isRegFam_ind_E_of_typeB hB
  obtain ⟨Q, hQ, hRQ⟩ := exists_le_of_mem_lcal_of_isDirectProduct hΩ.isDirectProduct hR
  have hQE : Q ≤ thetaOf θ E := hΩ.isDirectProduct.le hQ
  have hRc : R ∈ lcal Q := L511.mem_lcal_of_le hR hRQ hQE
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have h1 : R.map (MulAut.conj g).toMonoidHom ∈ lcal (thetaOf θ E) :=
    map_conj_mem_lcal hR (Subgroup.le_normalizer hg)
  have h2 : R.map (MulAut.conj g).toMonoidHom ≤ Q := by
    rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hΩ.isDirectProduct.le_normalizer hQ hg) x).mp
      (hRQ hx)
  have h3 := L511.mem_lcal_of_le h1 h2 hQE
  rw [h.lcal_of_mem_ind_E_of_typeB hB hQ] at hRc h3
  exact (Set.mem_singleton_iff.mp h3).trans (Set.mem_singleton_iff.mp hRc).symm

theorem not_commutator_le_centralizer
    (h : Counterexample p A θ) (hB : TypeBCore p A θ E K)
    {F : Subgroup G} (hF : F ∈ signalizerFunctorEk p 1 A) (hFE : F ≠ E) {Q₀ : Subgroup G}
    (hQ₀ : Q₀ ∈ Ind (thetaOf θ E)) {R : Subgroup G} (hR : R ∈ lcal (thetaOf θ E))
    (hRL : ¬ smear Q₀ F ≤ Subgroup.centralizer (R : Set G)) :
    ¬ ⁅smear Q₀ F, smear Q₀ F⁆ ≤ Subgroup.centralizer (R : Set G) := by
  have hΩ := h.isRegFam_ind_E_of_typeB hB
  have hR' := hR
  rw [h.lcal_E_eq_of_typeB hB] at hR'
  obtain ⟨Q, hQ, hRQ'⟩ := hR'
  have hRQ : R ≤ Q := hRQ' ▸ Subgroup.map_subtype_le _
  have hRlc : R ∈ lcal Q := by
    rw [h.lcal_of_mem_ind_E_of_typeB hB hQ, hRQ']
    rfl
  obtain ⟨-, -, hRs, hRnc⟩ := mem_lcal_iff.mp hRlc
  have hQR : Q ⊓ Subgroup.centralizer (R : Set G) = ⊥ := by
    rw [eq_bot_iff, ← inf_centralizer_self_eq_bot hRs hRnc]
    refine le_inf ?_ inf_le_right
    have h1 := inf_centralizer_generalizedFitting_le Q
    rw [hRQ']
    exact h1
  have hF' : ∀ f ∈ F, ∀ J ∈ Ind (thetaOf θ E), J.map (MulAut.conj f).toMonoidHom ∈
      Ind (thetaOf θ E) := fun f hf J hJ => hΩ.map_conj_mem f (hF.1 hf) J hJ
  have hbot := smear_inf_centralizer_eq_bot hΩ.isDirectProduct hF' hQ₀ hQ hRQ hQR hRL
  have hLnc : ¬ IsMulCommutative (smear Q₀ F) := by
    obtain ⟨e⟩ := hΩ.nonempty_mulEquiv_smear hF.1 (h.inf_line_eq_bot_of_typeB hB hF hFE) hQ₀
    intro hc
    have hQ₀c : IsMulCommutative Q₀ := (isMulCommutative_congr e).mp hc
    have h1 : CFSG.inSubgroup CFSG.generalizedFitting Q₀ ∈ lcal Q₀ := by
      rw [h.lcal_of_mem_ind_E_of_typeB hB hQ₀]
      rfl
    exact not_isMulCommutative_of_le (Subgroup.map_subtype_le _) (mem_lcal_iff.mp h1).2.2.2 hQ₀c
  intro hcomm
  apply hLnc
  refine isMulCommutative_iff.mpr fun a b => Subtype.ext ?_
  have hab : ⁅(a : G), (b : G)⁆ ∈ ⁅smear Q₀ F, smear Q₀ F⁆ :=
    Subgroup.commutator_mem_commutator a.2 b.2
  have h1 : ⁅(a : G), (b : G)⁆ ∈ smear Q₀ F ⊓ Subgroup.centralizer (R : Set G) :=
    Subgroup.mem_inf.mpr ⟨commutator_self_le _ hab, hcomm hab⟩
  rw [hbot, Subgroup.mem_bot] at h1
  exact commutatorElement_eq_one_iff_mul_comm.mp h1

end Setting

end L83

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
