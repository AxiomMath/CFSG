module

public import CFSG.Quasithin.EmptyFaithful.T1515cE

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G]

structure Ctx15122 (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G) : Prop where
  ctx : Ctx1515 T Mc M Z₁ Z₂ V₁ V₂
  h17 : Lemma15117Concl T M Z₁
  h18 : Lemma15118Concl T Mc M Z₁
  h19 : Lemma15119Used T Mc M Z₁ V₂
  hL : IsL1519 Mc Z₁ L
  h20 : Lemma15120Concl T Mc M Z₁ L
  h21 : Lemma15121Concl Mc Z₁ L

@[expose] def Input15122Dichotomy : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15122 T Mc M Z₁ Z₂ V₁ V₂ L → CharTwo L ∨ IsComponentOf L (g1_1516 Z₁)

omit [Finite G] in
theorem not_caseTwoA_15122 {T Mc Z₁ L : Subgroup G} (hL : IsL1519 Mc Z₁ L)
    (h21 : Lemma15121Concl Mc Z₁ L) (hchar : CharTwo L) : ¬ Case15120TwoA T Mc Z₁ L := by
  rintro ⟨hblock, htype, -⟩
  apply hL.not_le
  exact h21 hL.comp (Or.inl ⟨hchar, ⟨hblock.1, le_of_mem_cComp hL.comp,
    (isSubnormal_iff_subgroupOf (le_of_mem_cComp hL.comp)).mp (subnormal_of_mem_cComp hL.comp)⟩,
    htype⟩)

@[expose] def Input15122NoBorel : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15122 T Mc M Z₁ Z₂ V₁ V₂ L → IsComponentOf L (g1_1516 Z₁) →
    ¬ Case15120ThreeA Mc Z₁ L ∧ ¬ Case15120ThreeB Mc Z₁ L

@[expose] def Input15122A7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15122 T Mc M Z₁ Z₂ V₁ V₂ L → Case15120TwoB T Mc Z₁ L → IsAltBlockType L 7 →
    Case15122One T M Mc Z₁ L

@[expose] def Input15122Rank2Block : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15122 T Mc M Z₁ Z₂ V₁ V₂ L → Case15120TwoB T Mc Z₁ L →
    (IsLnBlock L 3 ∨ IsAltBlockType L 6 ∨ IsG2Block L) → Case15122Two T M Mc Z₁ L

@[expose] def Input15122L45Block : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15122 T Mc M Z₁ Z₂ V₁ V₂ L → Case15120TwoC Mc Z₁ L → Case15122Three M Mc Z₁ L

@[expose] def Input15122ThreeC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15122 T Mc M Z₁ Z₂ V₁ V₂ L → Case15120ThreeC T Mc Z₁ L → Case15122Four T M Mc Z₁ L

@[expose] def Input15122ThreeD : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15122 T Mc M Z₁ Z₂ V₁ V₂ L → Case15120ThreeD T Mc Z₁ L →
    Case15122Five T M Mc Z₁ L ∨ Case15122Six T Mc Z₁ L

@[expose] def Input15122ThreeE : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15122 T Mc M Z₁ Z₂ V₁ V₂ L → Case15120ThreeE T Mc Z₁ L → Case15122Seven T M Mc Z₁ L

theorem lemma15122InputU_of_named_inputs (nDich : Input15122Dichotomy) (nNoB : Input15122NoBorel)
    (nA7 : Input15122A7) (nR2 : Input15122Rank2Block) (nL45 : Input15122L45Block)
    (nC : Input15122ThreeC) (nD : Input15122ThreeD) (nE : Input15122ThreeE) : Lemma15122InputU := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18 h19 hL h20 h21 _
  have hc : Ctx15122 T Mc M Z₁ Z₂ V₁ V₂ L := ⟨hC, h17, h18, h19, hL, h20, h21⟩
  rcases nDich G T Mc M Z₁ Z₂ V₁ V₂ L hc with hchar | hcomp
  · obtain ⟨-, hcases⟩ := h20.two hchar
    rcases hcases with h | h | h
    · exact (not_caseTwoA_15122 hL h21 hchar h).elim
    · rcases h.2.1 hL.comp with h7 | h3 | h6 | hg
      · exact Or.inl (nA7 G T Mc M Z₁ Z₂ V₁ V₂ L hc h h7)
      · exact Or.inr (Or.inl (nR2 G T Mc M Z₁ Z₂ V₁ V₂ L hc h (Or.inl h3)))
      · exact Or.inr (Or.inl (nR2 G T Mc M Z₁ Z₂ V₁ V₂ L hc h (Or.inr (Or.inl h6))))
      · exact Or.inr (Or.inl (nR2 G T Mc M Z₁ Z₂ V₁ V₂ L hc h (Or.inr (Or.inr hg))))
    · exact Or.inr (Or.inr (Or.inl (nL45 G T Mc M Z₁ Z₂ V₁ V₂ L hc h)))
  · obtain ⟨-, hcases⟩ := h20.three hcomp
    rcases hcases with h | h | h | h | h
    · exact ((nNoB G T Mc M Z₁ Z₂ V₁ V₂ L hc hcomp).1 h).elim
    · exact ((nNoB G T Mc M Z₁ Z₂ V₁ V₂ L hc hcomp).2 h).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inl (nC G T Mc M Z₁ Z₂ V₁ V₂ L hc h))))
    · rcases nD G T Mc M Z₁ Z₂ V₁ V₂ L hc h with h5 | h6
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h6)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (nE G T Mc M Z₁ Z₂ V₁ V₂ L hc h))))))

end CFSG.Quasithin
