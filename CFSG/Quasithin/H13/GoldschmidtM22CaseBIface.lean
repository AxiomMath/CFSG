module

public import CFSG.Quasithin.H13.GoldschmidtM22EndN4

public section

namespace CFSG.Quasithin.H13.GM22

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin

structure M22LemmasG : Prop where
  g64 : G64Out
  h612 : Stmt6_1_2
  h616 : Stmt6_1_6
  h6110 : Stmt6_1_10
  h621 : Stmt6_2_1
  h622 : Stmt6_2_2
  h625 : Stmt6_2_5
  h626 : Stmt6_2_6
  h627 : Stmt6_2_7
  h629 : Stmt6_2_9
  h6210 : Stmt6_2_10
  h6211 : Stmt6_2_11
  h6212 : Stmt6_2_12

section Data

variable {G : Type} [Group G] [Finite G]

structure EndN4Concl (T L V : Subgroup G) (g : G) (D : Subgroup G) : Prop where
  kData : KData T L V g D
  hZS : ch6ZS T L V = V ⊓ UU T L V
  centralizer_eq_mul : ∀ q ∈ Subgroup.centralizer (V : Set G), ∃ v ∈ V,
    ∃ c ∈ Subgroup.centralizer (D : Set G) ⊓ CHU T L V, q = v * c
  E_le_centralizer : Subgroup.centralizer (D : Set G) ⊓ CHU T L V ≤ Subgroup.centralizer (V : Set G)
  centralizer_inf_HH_le : Subgroup.centralizer (D : Set G) ⊓ HH T ≤ CHU T L V
  normalizer_eq : Subgroup.normalizer (V : Set G) = L ⊔ T
  centralizer_le_T : Subgroup.centralizer (V : Set G) ≤ T
  pCoreOf_normalizer :
    pCoreOf 2 (Subgroup.normalizer (V : Set G)) = Subgroup.centralizer (V : Set G)
  oTwoUpper_normalizer : oTwoUpper (Subgroup.normalizer (V : Set G)) = L

variable {T M L V : Subgroup G}

theorem endN4_concl (hl : M22LemmasG) (h : Hyp6Sec2 G T M L V)
    (hZS : ch6ZS T L V = V ⊓ UU T L V) : ∃ (g : G) (D : Subgroup G), EndN4Concl T L V g D := by
  obtain ⟨g, D, hk, h2, h3, h4, h5, h6, h7, h8⟩ := endN4 hl.g64 hl.h621 hl.h622 hl.h626
    hl.h629 hl.h6210 hl.h6211 hl.h6212 hl.h6110 h hZS
  exact ⟨g, D, ⟨hk, hZS, h2, h3, h4, h5, h6, h7, h8⟩⟩

end Data

@[expose] def M22CaseBOne : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V : Subgroup G) (g : G) (D : Subgroup G),
    M22LemmasG → Hyp6Sec2 G T M L V → EndN4Concl T L V g D →
      IsElemAbelian 2 (Subgroup.centralizer (V : Set G)) ∧
        V.relIndex (Subgroup.centralizer (V : Set G)) ≤ 2

@[expose] def M22CaseBTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V : Subgroup G) (g : G) (D : Subgroup G),
    M22LemmasG → Hyp6Sec2 G T M L V → EndN4Concl T L V g D →
      IsElemAbelian 2 (Subgroup.centralizer (V : Set G)) →
      V.relIndex (Subgroup.centralizer (V : Set G)) = 2 → False

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G} {g : G} {D : Subgroup G}

theorem centralizer_le_of_caseB (h1 : M22CaseBOne) (h2 : M22CaseBTwo) (hl : M22LemmasG)
    (h : Hyp6Sec2 G T M L V) (hk : EndN4Concl T L V g D) :
    Subgroup.centralizer (V : Set G) ≤ V := by
  obtain ⟨hab, hle⟩ := h1 G T M L V g D hl h hk
  by_contra hne
  have hne1 : V.relIndex (Subgroup.centralizer (V : Set G)) ≠ 1 := fun h1 =>
    hne (Subgroup.relIndex_eq_one.mp h1)
  have hne0 : V.relIndex (Subgroup.centralizer (V : Set G)) ≠ 0 :=
    Subgroup.index_ne_zero_of_finite
  exact h2 G T M L V g D hl h hk hab (by omega)

end CFSG.Quasithin.H13.GM22
