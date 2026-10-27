module

public import CFSG.Quasithin.Background.C126Defs
public import CFSG.Quasithin.Background.C1PackC126Solv

public section

namespace CFSG.Quasithin.C126

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_uFamHat_self {H T M : Subgroup G} (h : MinParabolic H T M) : H ∈ uFamHat H T := by
  refine ⟨⟨le_rfl, h.lt, ?_⟩, h.not_normal⟩
  have : maxOver H T = {M} := h.uniqueMax
  rw [this]
  exact Set.ncard_singleton M

theorem concl1_of_perfectCore_le {C₁ C₂ : Subgroup G → Subgroup G} (hC : IsGNChoice C₁ C₂)
    {H T M : Subgroup G} (hmin : MinParabolic H T M) (hSQ : IsSQTKTC H) (hF : CharTwo H)
    (hsolv : perfectCore H ≤ Subgroup.centralizer (VZ T H : Set G)) : Concl1 C₁ C₂ H T := by
  have hT := hmin.isSylow
  have hT0 : T ≠ ⊥ := C1Pack.minParabolic_ne_bot hmin
  obtain ⟨-, h1Z, -, -, h2B, h2char, -⟩ := hC.pair T hT.2.1 hT0
  by_cases h1 : C₁ T ≤ centerOf H
  · exact Or.inl h1
  by_cases h2 : H ≤ Subgroup.normalizer (C₂ T : Set G)
  · exact Or.inr (Or.inl h2)
  refine Or.inr (Or.inr ?_)
  have hTH : T ≤ H := hT.1
  have hC1T : C₁ T ≤ T := h1Z.trans ((Subgroup.closure_le T).mpr fun x hx => hx.1.1)
  have hC1cent : ∀ t ∈ T, ∀ c ∈ C₁ T, c * t = t * c := fun t ht c hc =>
    ((Subgroup.mem_centralizer_iff.mp (B2F.omegaOneCenterOf_le_centerOf T (h1Z hc)).2 t ht)).symm
  have hA1 : H ⊓ Subgroup.centralizer (C₁ T : Set G) ≤ M := by
    refine hmin.le_of_lt (le_inf hTH fun t ht => Subgroup.mem_centralizer_iff.mpr fun c hc =>
      hC1cent t ht c hc) (lt_of_le_of_ne inf_le_left fun he => h1 ?_)
    have hHC : H ≤ Subgroup.centralizer (C₁ T : Set G) := by
      calc H = H ⊓ Subgroup.centralizer (C₁ T : Set G) := he.symm
        _ ≤ _ := inf_le_right
    refine le_inf (hC1T.trans hTH) fun c hc => Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
    exact ((Subgroup.mem_centralizer_iff.mp (hHC hh) c hc)).symm
  have hTS : T ≤ Subgroup.normalizer (baum T : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_baum T)
  have hTN2 : T ≤ Subgroup.normalizer (C₂ T : Set G) :=
    hTS.trans (normalizer_le_normalizer_of_characteristic_subgroupOf h2B h2char)
  have hA2 : H ⊓ Subgroup.normalizer (C₂ T : Set G) ≤ M := by
    refine hmin.le_of_lt (le_inf hTH hTN2) (lt_of_le_of_ne inf_le_left fun he => h2 ?_)
    calc H = H ⊓ Subgroup.normalizer (C₂ T : Set G) := he.symm
      _ ≤ _ := inf_le_right
  have hUM : ¬ H ≤ M := fun hle => absurd (lt_of_le_of_lt hle hmin.maximal.1) (lt_irrefl _)
  obtain ⟨K, hKb, -, hKJ, hKH, -⟩ := C1Pack.exists_a3Block_of_not_le hC hF hSQ hT hsolv
    (mem_uFamHat_self hmin) (sup_le hA1 hA2) hmin.le hUM
  exact ⟨K, hKb, hKJ, hKH⟩

end CFSG.Quasithin.C126
