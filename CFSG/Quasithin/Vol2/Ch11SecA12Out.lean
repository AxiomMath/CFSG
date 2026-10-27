module

public import CFSG.Quasithin.Vol2.Ch11SecAFacts12b
public import CFSG.Quasithin.Vol2.Ch11SecSPGL
public import CFSG.Quasithin.Vol2.Ch11SecA11Bar

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin SecS
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I V₁ V₂ X K : Subgroup G} {n i : ℕ}

theorem isSylowTwoOf_inf_K (h : Hyp11 G T L I n) {U : Subgroup G} (hU : IsVi T L I n i U)
    (hK : K ∈ cComp (Subgroup.normalizer (U : Set G)))
    (hNK : Subgroup.normalizer (U : Set G) ≤ Subgroup.normalizer (K : Set G)) :
    QuasithinUnique.IsSylowTwoOf (T ⊓ K) K :=
  A4.isSylowTwoOf_inf_normal
    (isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow (IsVi.le_normalizer hU))
    (le_of_mem_cComp hK) hNK

theorem exists_outer (hFb : Facts12b) (hN : NatFacts) (h1102 : Stmt11_0_2)
    (h : Hyp11 G T L I 2) (hV₁ : IsVi T L I 2 1 V₁)
    (hK : K ∈ cComp (Subgroup.normalizer (V₁ : Set G)))
    (hNK : Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hLK : LOf L V₁ ≤ K)
    (hS : IsPSL 2 5 2 (↥K ⧸ CFSG.pCore 2 ↥K) ∨ IsSLEps3 true 5 (↥K ⧸ CFSG.pCore 2 ↥K) ∨
      IsPSLEps3 true 5 1 (↥K ⧸ CFSG.pCore 2 ↥K) ∨ IsPSLEps3 false 5 1 (↥K ⧸ CFSG.pCore 2 ↥K)) :
    ∃ t ∈ T ⊓ K, ∀ l ∈ LOf L V₁, ∃ y ∈ LOf L V₁,
      t * y * t⁻¹ * (l * y * l⁻¹)⁻¹ ∉ pCoreOf 2 (LOf L V₁) := by
  have hSyl := isSylowTwoOf_inf_K h hV₁ hK hNK
  have hTL₁ : T ≤ Subgroup.normalizer (LOf L V₁ : Set G) :=
    T_le_normalizer_lOf h.normal (IsVi.le_normalizer hV₁)
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := lOf_quot_SL2 hN h1102 h (Or.inl rfl) hV₁
  obtain ⟨e₁⟩ := modO2Image_quotEquiv hLK
  obtain ⟨r, hr, hrout⟩ := hFb.outer _ hS (modO2Image K (T ⊓ K)) (modO2Image K (LOf L V₁))
    (isSylowTwoOf_modO2Image hSyl) (modO2Image_le_normalizer (inf_le_left.trans hTL₁))
    (modO2Image_perfect hLK (perfectCore_perfect _))
    ⟨F, inferInstance, inferInstance, hF.trans (by norm_num), ⟨e₁.symm.trans e⟩⟩
  obtain ⟨t', ht', rfl⟩ := hr
  refine ⟨t', Subgroup.mem_subgroupOf.mp ht', fun l hl => ?_⟩
  obtain ⟨y, hy, hyout⟩ := hrout _ ⟨⟨l, hLK hl⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
  obtain ⟨y', hy', rfl⟩ := hy
  refine ⟨y', Subgroup.mem_subgroupOf.mp hy', fun hmem => hyout ?_⟩
  apply modO2Image_pCoreOf_le hLK
  refine ⟨t' * y' * t'⁻¹ * (⟨l, hLK hl⟩ * y' * (⟨l, hLK hl⟩ : ↥K)⁻¹)⁻¹, ?_, ?_⟩
  · exact Subgroup.mem_subgroupOf.mpr (by simpa using hmem)
  · simp

end CFSG.Quasithin.Vol2.Ch11.SecA
