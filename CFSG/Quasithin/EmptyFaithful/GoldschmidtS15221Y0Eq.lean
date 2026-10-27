module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15221Y0
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15221Alt8
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15221Quot

public section

namespace CFSG.Quasithin.S15221

open CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem oTwoUpper_idem_eq (X : Subgroup G) : oTwoUpper (oTwoUpper X) = oTwoUpper X := by
  apply le_antisymm (oTwoUpper_le _)
  refine (Subgroup.closure_le _).mpr fun x hx => ?_
  exact mem_oTwoUpper_of_odd (mem_oTwoUpper_of_odd hx.1 hx.2) hx.2

theorem exists_Y0_eq {K D : Subgroup G} (hDK : D ≤ K) (hD2 : IsPGroup 2 D)
    (hDi : ¬ 2 ∣ (D.subgroupOf K).index)
    (hK : Nonempty (OTwoQuot K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2))) :
    ∃ Y : Subgroup G, Y ≤ K ∧ Y = oTwoUpper Y ∧
      (∀ g : G, g ∈ Subgroup.normalizer (K : Set G) → g ∈ Subgroup.normalizer (D : Set G) →
        g ∈ Subgroup.normalizer (Y : Set G)) ∧
      (pCoreOf 2 Y).relIndex Y = 3 ∧ pCoreOf 2 Y ≠ ⊥ ∧
      ∃ d ∈ D, ∀ y ∈ Y, y ∉ pCoreOf 2 Y → d * y * d⁻¹ * y⁻¹ ∉ pCoreOf 2 Y := by
  obtain ⟨e⟩ := isLnTwo_four_alt8 hK
  obtain ⟨C, hDC, hCK, hnorm, σ, hσ, hker⟩ := exists_Ctilde hDK hD2 hDi e
  obtain ⟨h1, h2, h3⟩ := s4Quot_oTwoUpper s4Like_perm_fin4 σ hσ hker
  refine ⟨oTwoUpper C, (oTwoUpper_le C).trans hCK, (oTwoUpper_idem_eq C).symm,
    fun g hgK hgD => normalizer_le_normalizer_oTwoUpper C (hnorm g hgK hgD), h1, h2, ?_⟩
  refine h3 D hDC hD2 fun h => hDi (h.trans ?_)
  exact Dvd.intro _ (Subgroup.relIndex_mul_relIndex D C K hDC hCK)

end CFSG.Quasithin.S15221
