module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P20p
public import CFSG.GroupTheory.ConjClosureCentralProduct
import CFSG.LocalAnalysis.UniquenessCase.UC22P20m
import CFSG.LocalAnalysis.UniquenessCase.UC22P21c
import CFSG.LocalAnalysis.UniquenessCase.UC22P22l

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem uc22r3t_layer_bar2_eq_top (D : Data G) {K₁ : Subgroup G}
    (hK₁ : K₁ ∈ calL D.T D.M) : CFSG.layer (Bar2 K₁) = ⊤ := by
  have h1 : (CFSG.layer (Bar2 K₁)).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥K₁)) = ⊤ :=
    uc22p20o_oTwoE_top D hK₁
  have h2 := Subgroup.map_comap_eq_self_of_surjective
    (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K₁)) (CFSG.layer (Bar2 K₁))
  rw [h1, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h2
  exact h2.symm

theorem uc22r3t_component_equiv (D : Data G) {K₁ K : Subgroup G} (hK₁ : K₁ ∈ calL D.T D.M)
    (hK : K ∈ calC K₁) (hLK : K₁ = uc22p20bOrb D.T K)
    (C : CFSG.LocalCores.ComponentIndex (Bar2 K₁)) : Nonempty (Bar2 K ≃* ↥C.1) := by
  obtain ⟨L', hL', hLC⟩ := uc22p21c_exists_calC_of_component K₁ C.2
  have hm := uc22p20e_cComp_of_calC hL'
  rw [uc22p20p_cComp_eq_range D hK₁ hK hLK] at hm
  obtain ⟨t, rfl⟩ := hm
  obtain ⟨e1⟩ := uc22p20d_bar2_conj (t : G) K
  obtain ⟨e2, -⟩ := uc22p22l_barImage_equiv hL'
  exact ⟨(e1.trans e2).trans (MulEquiv.subgroupCongr hLC)⟩

theorem uc22r3t_commutator_mem_T_of_isMulCommutative (D : Data G) {K₁ : Subgroup G}
    (hK₁ : K₁ ∈ calL D.T D.M)
    (hab : IsMulCommutative (TauCeti.Subgroup.normalizerQuotient (uc22p20iSylowBar D K₁)))
    {x y : G} (hx : x ∈ K₁) (hy : y ∈ K₁) (hxT : x ∈ normalizer (D.T : Set G))
    (hyT : y ∈ normalizer (D.T : Set G)) : x * y * x⁻¹ * y⁻¹ ∈ D.T := by
  have hxN : QuotientGroup.mk' (CFSG.pCore 2 ↥K₁) ⟨x, hx⟩ ∈
      normalizer ((uc22p20iSylowBar D K₁ : Subgroup (Bar2 K₁)) : Set (Bar2 K₁)) := by
    rw [uc22p20m_mem_normalizer_bar_iff D hK₁]
    exact Subgroup.inf_normalizer_le_normalizer_inf
      (Subgroup.mem_inf.2 ⟨hxT, Subgroup.le_normalizer hx⟩)
  have hyN : QuotientGroup.mk' (CFSG.pCore 2 ↥K₁) ⟨y, hy⟩ ∈
      normalizer ((uc22p20iSylowBar D K₁ : Subgroup (Bar2 K₁)) : Set (Bar2 K₁)) := by
    rw [uc22p20m_mem_normalizer_bar_iff D hK₁]
    exact Subgroup.inf_normalizer_le_normalizer_inf
      (Subgroup.mem_inf.2 ⟨hyT, Subgroup.le_normalizer hy⟩)
  have h := CFSG.GroupTheory.commutatorElement_mem_of_isMulCommutative_normalizerQuotient
    hab hxN hyN
  rw [← map_commutatorElement] at h
  have h' := (Subgroup.mem_inf.1 ((uc22p20i_mem_sylowBar_iff D hK₁ _).1 h)).1
  simpa [commutatorElement_def] using h'

theorem uc22r3t_commutator_mem_T_of_mem_center (D : Data G) {K₁ : Subgroup G}
    (hK₁ : K₁ ∈ calL D.T D.M) {x y : G} (hx : x ∈ K₁) (hy : y ∈ K₁)
    (hc : QuotientGroup.mk' (CFSG.pCore 2 ↥K₁) ⟨y, hy⟩ ∈ Subgroup.center (Bar2 K₁)) :
    x * y * x⁻¹ * y⁻¹ ∈ D.T := by
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥K₁) ⁅(⟨x, hx⟩ : ↥K₁), ⟨y, hy⟩⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact Subgroup.mem_center_iff.mp hc _
  have h2 : QuotientGroup.mk' (CFSG.pCore 2 ↥K₁) ⁅(⟨x, hx⟩ : ↥K₁), ⟨y, hy⟩⁆ ∈
      uc22p20iSylowBar D K₁ := by
    rw [h1]
    exact one_mem _
  have h' := (Subgroup.mem_inf.1 ((uc22p20i_mem_sylowBar_iff D hK₁ _).1 h2)).1
  simpa [commutatorElement_def] using h'

end CFSG.LocalAnalysis.UniquenessCase.UC22
