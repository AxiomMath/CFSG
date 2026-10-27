module

public import CFSG.RankThree.GF2n.Stroth80.Sec717RepFieldsGroup
public import CFSG.RankThree.GF2n.Stroth80.Sec717RepFieldsLinear
public import CFSG.GroupTheory.SylowNormalElements

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup

theorem two_elements_of_sylow {X : Type*} [Group X] [Finite X] {V Rb : Subgroup X}
    (hRN : Rb ≤ normalizer (V : Set X)) (hNR : ∀ k ∈ normalizer (V : Set X), k ∈ normalizer (Rb : Set X))
    (S : Sylow 2 X) (hSR : (S : Subgroup X) ≤ Rb) :
    ∀ k ∈ normalizer (V : Set X), (∀ a ∈ V, k * a = a * k) → IsPGroup 2 (zpowers k) → k ∈ Rb := by
  intro k hk _ hk2
  have hS : CFSG.ABGLocalTools.IsSylowOf 2 (S : Subgroup X) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_top, S.isPGroup', ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact S.not_dvd_index
  have hS' := hS.of_le (hSR.trans hRN) le_top
  have hnorm : (Rb.subgroupOf (normalizer (V : Set X))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRN).mpr fun x hx => hNR x hx
  obtain ⟨e, he⟩ := (IsPGroup.iff_orderOf.mp hk2) ⟨k, mem_zpowers k⟩
  have hord : orderOf k = 2 ^ e := by
    rw [← he, Subgroup.orderOf_mk]
  exact CFSG.GroupTheory.mem_of_normal_of_isSylowOf hnorm hS' hSR hk hord

namespace Sec717RepInputs

variable {K E X : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E] [Group X]
  {B : LinearMap.BilinForm K E} {Qf : E → K} {φ : X →* (E ≃ₗ[K] E)}
  {V L Nb Rb : Subgroup X} {T : Submodule K E}

theorem moveFrameRep (I : Sec717RepInputs B Qf φ V L Nb Rb T) {Tt : X → Submodule K E}
    (hTt : ∀ g a : X, a ∈ V → a ≠ 1 → LinearMap.range (opm (φ (g * a * g⁻¹))) = Tt g) :
    MoveFrameRep B φ V L Nb Rb Tt where
  Nb_semi := I.nb_semi
  semilinear := I.semilinear
  two_elements := I.two
  CL := I.cl
  quad := I.quad
  pair_dim := I.pair_dim hTt
  image_dim := I.image_dim hTt
  no_isotropic := I.no_isotropic hTt
  transvection := I.transvection

end Sec717RepInputs

end CFSG.RankThree.GF2n.Stroth80
