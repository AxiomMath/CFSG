module

public import CFSG.Quasithin.Background.A3StructureBasic
public import CFSG.Quasithin.Background.A3Structure312Nonquasi

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.SectionRank CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

@[expose] def A312Refined (G : Type) [Group G] : Prop :=
  ∀ T : Subgroup G, IsSylowTwoOf T ⊤ → ∀ B ∈ lFamily T,
    ∃ L ∈ cComp (⊤ : Subgroup G), B ≤ L ∧ (∀ L' ∈ cComp (⊤ : Subgroup G), B ≤ L' → L' = L) ∧
      (B = L ∨ (CFSG.IsQuasisimple ↥L ∧ A312Case B L) ∨
        (¬ CFSG.IsQuasisimple ↥L ∧ A312Nonquasi B L))

theorem A312Refined.statement {G : Type} [Group G] (h : A312Refined G) : A312Statement G := by
  intro T hT B hB
  obtain ⟨L, hL, hBL, huniq, hcases⟩ := h T hT B hB
  refine ⟨L, hL, hBL, huniq, ?_⟩
  rcases hcases with h | ⟨-, h⟩ | ⟨-, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem a312_refined (hF : A312Facts) {G : Type} [Group G] (hG : SQTKHyp G)
    (h36 : A36Statement G) (h37 : A37Statement G) (h39 : A39Statement G) : A312Refined G := by
  have : Finite G := hG.finite
  intro T hT B hB
  obtain ⟨L, hL, hBL⟩ := A312.exists_le_cComp hT hB h37 h39
  have hBne : B ≠ ⊥ := ne_bot_of_mem_cComp (show B ∈ cComp (B ⊔ T) from hB)
  have hperf : ⁅B, B⁆ = B := perfect_of_mem_cComp (show B ∈ cComp (B ⊔ T) from hB)
  refine ⟨L, hL, hBL, fun L' hL' hBL' => A312.eq_of_le_of_le h37 hBne hperf hL hL' hBL hBL', ?_⟩
  by_cases hq : CFSG.IsQuasisimple ↥L
  · by_cases hBeq : B = L
    · exact Or.inl hBeq
    · right
      left
      refine ⟨hq, A312Case.of_subgroupOf hBL ?_⟩
      have hLsub : IsSubnormal L ⊤ := subnormal_of_mem_cComp hL
      have hL' : SQTKHyp ↥L := hG.of_subnormal hLsub
      obtain ⟨hT', hB'⟩ := A312.isSylowTwoOf_lFamily_subgroupOf hT hL hBL hB
      have hne : B.subgroupOf L ≠ ⊤ := by
        intro h
        apply hBeq
        exact le_antisymm hBL (fun x hx => by
          have : (⟨x, hx⟩ : ↥L) ∈ B.subgroupOf L := by rw [h]; trivial
          exact this)
      exact hF.list ↥L hq ⟨hL'.sqt, hL'.kgroup⟩ hL'.o2 _ hT' _ hB' hne
  · right
    right
    exact ⟨hq, A312.nonquasi_of_lFamily hF.sl2 hT hL hBL hB (h36 L hL) hq⟩

theorem a312 (hF : A312Facts) {G : Type} [Group G] (hG : SQTKHyp G) (h36 : A36Statement G)
    (h37 : A37Statement G) (_h38 : A38Part3 G) (h39 : A39Statement G) : A312Statement G :=
  (a312_refined hF hG h36 h37 h39).statement

end CFSG.Quasithin
