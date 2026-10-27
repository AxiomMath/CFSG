module

public import CFSG.Quasithin.EmptyFaithful.T1515cE

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G]

structure Ctx15120 (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G) : Prop where
  ctx : Ctx1515 T Mc M Z₁ Z₂ V₁ V₂
  h17 : Lemma15117Concl T M Z₁
  h18 : Lemma15118Concl T Mc M Z₁
  h19 : Lemma15119Used T Mc M Z₁ V₂
  hL : IsL1520 T Mc Z₁ L

@[expose] def ListA15120 (L : Subgroup G) : Prop :=
  ∃ n : ℕ, 2 ≤ n ∧ IsPSL 2 2 n (↥L ⧸ CFSG.pCore 2 ↥L)

@[expose] def ListB15120 (L : Subgroup G) : Prop :=
  (∃ n : ℕ, 2 ≤ n ∧ IsPSL 3 2 n (↥L ⧸ CFSG.pCore 2 ↥L)) ∨
    (∃ n : ℕ, 2 ≤ n ∧ IsPSp4 2 n (↥L ⧸ CFSG.pCore 2 ↥L)) ∨
    ∃ n : ℕ, 2 ≤ n ∧ IsG2 2 n (↥L ⧸ CFSG.pCore 2 ↥L)

@[expose] def ListC15120 (L : Subgroup G) : Prop :=
  IsPSL 4 2 1 (↥L ⧸ CFSG.pCore 2 ↥L) ∨ IsPSL 5 2 1 (↥L ⧸ CFSG.pCore 2 ↥L)

@[expose] def ListD15120 (L : Subgroup G) : Prop :=
  IsAlt 7 ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) ∨
    IsPSL 3 2 1 ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) ∨
    IsAlt 6 ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) ∨
    IsPSU 3 3 1 ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L))

@[expose] def Input15120LJ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L → CharTwo L → ⁅L, thompsonJ (s1516 T Z₁)⁆ = L

@[expose] def Input15120B42List : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L → CharTwo L →
    ListA15120 L ∨ ListB15120 L ∨ ListC15120 L ∨ ListD15120 L

@[expose] def Input15120L2Block : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L → CharTwo L → ListA15120 L →
    IsBlock2 (L ⊔ s1516 T Z₁) L ∧ (L ∈ cComp (g1_1516 Z₁) → Case15120TwoA T Mc Z₁ L)

@[expose] def Input15120RankTwoExcl : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L → CharTwo L → ListB15120 L → False

@[expose] def Input15120L45 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L → CharTwo L → ListC15120 L → Case15120TwoC Mc Z₁ L

@[expose] def Input15120TwoB : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L → CharTwo L → ListD15120 L → Case15120TwoB T Mc Z₁ L

@[expose] def CompTypeA15120 (L : Subgroup G) : Prop :=
  IsBender1516 ↥L ∨ IsSz 3 (↥L ⧸ CFSG.pCore 2 ↥L)

@[expose] def CompTypeB15120 (L : Subgroup G) : Prop :=
  (∃ n : ℕ, 1 < n ∧ IsPSL 3 2 n ↥L) ∨ (∃ n : ℕ, 1 < n ∧ IsPSp4 2 n ↥L) ∨
    IsPSL 3 2 2 (↥L ⧸ CFSG.pCore 2 ↥L)

@[expose] def CompTypeC15120 (L : Subgroup G) : Prop :=
  IsPSU 3 3 1 ↥L ∨ IsTits ↥L ∨ Is3D4 2 1 ↥L

@[expose] def CompTypeD15120 (L : Subgroup G) : Prop :=
  IsSporadic .M11 (↥L ⧸ CFSG.pCore 2 ↥L) ∨ IsSporadic .M12 (↥L ⧸ CFSG.pCore 2 ↥L) ∨
    IsSporadic .M22 (↥L ⧸ CFSG.pCore 2 ↥L) ∨ IsSporadic .M23 (↥L ⧸ CFSG.pCore 2 ↥L) ∨
    IsSporadic .M24 (↥L ⧸ CFSG.pCore 2 ↥L) ∨ IsSporadic .J2 (↥L ⧸ CFSG.pCore 2 ↥L) ∨
    IsSporadic .HS (↥L ⧸ CFSG.pCore 2 ↥L) ∨ IsSporadic .He (↥L ⧸ CFSG.pCore 2 ↥L) ∨
    IsSporadic .Ru (↥L ⧸ CFSG.pCore 2 ↥L)

@[expose] def CompTypeE15120 (L : Subgroup G) : Prop :=
  IsPSL 4 2 1 ↥L ∨ IsPSL 5 2 1 ↥L

@[expose] def Input15120CompList : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L → IsComponentOf L (g1_1516 Z₁) → Lemma15118Extra T Mc M Z₁ →
    CompTypeA15120 L ∨ CompTypeB15120 L ∨ CompTypeC15120 L ∨ CompTypeD15120 L ∨ CompTypeE15120 L

@[expose] def Input15120MLA : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L → IsComponentOf L (g1_1516 Z₁) → CompTypeA15120 L →
    IsBorelIn L (mZ1516 Mc Z₁ ⊓ L)

@[expose] def Input15120MLB : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L → IsComponentOf L (g1_1516 Z₁) → CompTypeB15120 L →
    IsBorelIn L (mZ1516 Mc Z₁ ⊓ L) ∨ IsMaxParabolic2 L (mZ1516 Mc Z₁ ⊓ L)

@[expose] def Input15120MLC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L → IsComponentOf L (g1_1516 Z₁) → CompTypeC15120 L →
    mZ1516 Mc Z₁ ⊓ L = L ⊓ Subgroup.centralizer (centerOf (s1516 T Z₁ ⊓ L) : Set G)

@[expose] def Input15120MLD : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L → IsComponentOf L (g1_1516 Z₁) → CompTypeD15120 L →
    Lemma15118Extra T Mc M Z₁ →
    mZ1516 Mc Z₁ ⊓ L = L ⊓ Subgroup.centralizer (centerOf (s1516 T Z₁ ⊓ L) : Set G)

@[expose] def Input15120MLE : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L → IsComponentOf L (g1_1516 Z₁) → CompTypeE15120 L →
    IsParabolic2 L (mZ1516 Mc Z₁ ⊓ L) ∧ mZ1516 Mc Z₁ ⊓ L ≠ L ∧
      L ⊓ Subgroup.centralizer (centerOf (s1516 T Z₁ ⊓ L) : Set G) ≤ mZ1516 Mc Z₁ ⊓ L

theorem lemma15120InputU_of_named_inputs (nLJ : Input15120LJ) (nB42 : Input15120B42List)
    (nA : Input15120L2Block) (nB : Input15120RankTwoExcl) (nC : Input15120L45)
    (nD : Input15120TwoB) (nCL : Input15120CompList) (mA : Input15120MLA) (mB : Input15120MLB)
    (mC : Input15120MLC) (mD : Input15120MLD) (mE : Input15120MLE) : Lemma15120InputU := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18 h19 hL hx
  have hc : Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L :=
    ⟨hC, h17, h18, h19, hL.isL1520 h18.four (hC.setting.pCore_g1_ne_bot hC.qtfe hC.mf)⟩
  refine ⟨fun hchar => ⟨nLJ G T Mc M Z₁ Z₂ V₁ V₂ L hc hchar, ?_⟩, fun hcomp => ?_⟩
  · rcases nB42 G T Mc M Z₁ Z₂ V₁ V₂ L hc hchar with h | h | h | h
    · exact Or.inl ((nA G T Mc M Z₁ Z₂ V₁ V₂ L hc hchar h).2 hL.comp)
    · exact (nB G T Mc M Z₁ Z₂ V₁ V₂ L hc hchar h).elim
    · exact Or.inr (Or.inr (nC G T Mc M Z₁ Z₂ V₁ V₂ L hc hchar h))
    · exact Or.inr (Or.inl (nD G T Mc M Z₁ Z₂ V₁ V₂ L hc hchar h))
  · rcases nCL G T Mc M Z₁ Z₂ V₁ V₂ L hc hcomp hx with h | h | h | h | h
    · exact Or.inl ⟨h, mA G T Mc M Z₁ Z₂ V₁ V₂ L hc hcomp h⟩
    · exact Or.inr (Or.inl ⟨h, mB G T Mc M Z₁ Z₂ V₁ V₂ L hc hcomp h⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨h, mC G T Mc M Z₁ Z₂ V₁ V₂ L hc hcomp h⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h, mD G T Mc M Z₁ Z₂ V₁ V₂ L hc hcomp h hx⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h, mE G T Mc M Z₁ Z₂ V₁ V₂ L hc hcomp h⟩)))

end CFSG.Quasithin
