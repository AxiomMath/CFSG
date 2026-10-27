module

public import CFSG.Quasithin.Vol2.Ch12Sec5Frame
public import CFSG.Quasithin.Vol2.Ch12Sec4Statements
public import CFSG.Quasithin.Vol2.Ch12Sec9List
public import CFSG.Quasithin.Vol2.Ch11StatementsInputs
public import CFSG.Quasithin.Background.B4ModelsLie
public import CFSG.Quasithin.Background.A3Structure312Defs
public import CFSG.Quasithin.Background.B2FactorizationResidual
public import CFSG.Quasithin.Background.F9Basic
public import CFSG.Quasithin.Background.JonesParshallNatural
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch11StatementsF
public import CFSG.Quasithin.Vol2.Ch11StatementsG
public import CFSG.Quasithin.Vol2.Ch11StatementsH
public import CFSG.Quasithin.Vol2.Ch12Sec5Statements
public import CFSG.Timmesfeld.Orders.ClassicalLinear

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S125
open scoped IsMulCommutative

variable {G : Type} [Group G]

@[expose] def Frame125Exists : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp125 G T L V →
    Nonempty (Frame125 T L V)

@[expose] def Frame125ZV : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (F : Frame125 T L V),
    Hyp125 G T L V → V ⊓ quasithinOmegaOneCenter T = F.V1

@[expose] def Concl12_5_2 (T L V : Subgroup G) (F : Frame125 T L V) : Prop :=
  (F.IsStab (mi T L F.V1) 2 ∧
    Nonempty (↥(autOn (mi T L F.V1) V) ⧸ CFSG.pCore 2 ↥(autOn (mi T L F.V1) V) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) × Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) ∧
    QuotSL (li L F.V1) (ri T L F.V1) V 3 ∧
    IrrSection (mi T L F.V1) ⊥ F.V1 ∧ IrrSection (mi T L F.V1) F.V1 F.V7 ∧
    IrrSection (mi T L F.V1) F.V7 V) ∧
  (F.IsStab (mi T L F.V3) 3 ∧
    Nonempty (↥(autOn (mi T L F.V3) V) ⧸ CFSG.pCore 2 ↥(autOn (mi T L F.V3) V) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) × Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∧
    QuotSL (li L F.V3) (ri T L F.V3) V 3 ∧
    ri T L F.V3 ≤ Subgroup.centralizer (F.V3 : Set G) ∧
    ∃ _ : IsMulCommutative ↥F.V3, BinaryNaturalSL (V := ↥F.V3) (autOn (li L F.V3) F.V3) ⊤ ⊥ 3 1) ∧
  (autOn (mi T L F.V4) V = autOn (li L F.V4) V ∧ F.IsStab (mi T L F.V4) 1 ∧
    QuotSL (li L F.V4) (ri T L F.V4) V 4 ∧
    ri T L F.V4 ≤ Subgroup.centralizer (F.V4 : Set G) ∧
    ∃ _ : IsMulCommutative ↥F.V4, BinaryNaturalSL (V := ↥F.V4) (autOn (li L F.V4) F.V4) ⊤ ⊥ 4 1) ∧
  (autOn (mi T L F.V6) V = autOn (li L F.V6) V ∧ F.IsStab (mi T L F.V6) 4 ∧
    QuotSL (li L F.V6) (ri T L F.V6) V 4 ∧
    ri T L F.V6 ≤ Subgroup.centralizer (F.V6 : Set G) ∧
    (∃ _ : IsMulCommutative ↥F.V6, SLExteriorTwo (V := ↥F.V6) (autOn (li L F.V6) F.V6) ⊤ ⊥ 4) ∧
    ∃ f : ↥V →* ↥(autOn (ri T L F.V6) V), Function.Surjective f ∧
      (∀ v : ↥V, f v = 1 ↔ (v : G) ∈ F.V6) ∧
      (∀ (h : ↥(autOn (li L F.V6) V)) (v : ↥V),
        ((f ((h : MulAut ↥V) v) : MulAut ↥V)) = (h : MulAut ↥V) * f v * (h : MulAut ↥V)⁻¹) ∧
      ∀ r : ↥(autOn (ri T L F.V6) V), r ≠ 1 → ∀ v : ↥V,
        (r : MulAut ↥V) v = v ↔ (f v = 1 ∨ f v = r))

@[expose] def Lemma12_5_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (F : Frame125 T L V),
    Hyp125 G T L V → Concl12_5_2 T L V F

@[expose] def Concl12_5_6 (L V : Subgroup G) : Prop :=
  ∀ hV : IsElemAbelian 2 V, 3 < E3.rParam V ∧
    E3.mParam (autI hV (Subgroup.normalizer (L : Set G))) = 3 ∧ E3.sParam hV = 3

@[expose] def Lemma12_5_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp125 G T L V → Concl12_5_6 L V

@[expose] def Concl12_5_7 (T L V : Subgroup G) : Prop :=
  E3.wClos V 0 T ≤ Subgroup.centralizer (V : Set G) ∧ 0 < E3.wParam T V ∧
    Subgroup.normalizer (E3.wClos V 0 T : Set G) ≤ Subgroup.normalizer (L : Set G)

@[expose] def Lemma12_5_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp125 G T L V → Concl12_5_7 T L V

@[expose] def Concl12_5_8 (T L V : Subgroup G) (F : Frame125 T L V) : Prop :=
  V ≤ pCoreOf 2 (Subgroup.normalizer (F.V1 : Set G)) ∧ IsElemAbelian 2 (u128 V F.V1)

@[expose] def Lemma12_5_8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (F : Frame125 T L V),
    Hyp125 G T L V → Concl12_5_8 T L V F

@[expose] def Concl12_5_9 (T L V : Subgroup G) (F : Frame125 T L V) : Prop :=
  (∀ V₁' : Subgroup G, V₁' ≤ V → Nat.card V₁' = 2 →
    (¬ ∃ l ∈ L, CFSG.conjugate F.V1 l = V₁') →
    QuasithinUnique.IsSylowTwoOf (T ⊓ Subgroup.centralizer (V₁' : Set G))
      (Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (V₁' : Set G)) →
      (T ⊓ Subgroup.centralizer (V₁' : Set G)).relIndex T = 4 ∧
      QuasithinUnique.IsSylowTwoOf (T ⊓ Subgroup.centralizer (V₁' : Set G))
        (Subgroup.centralizer (V₁' : Set G)) ∧
      ∀ g : G, CFSG.conjugate F.V1 g ≠ V₁') ∧
  (∀ g : G, CFSG.conjugate F.V1 g ≤ V → ∃ l ∈ L, CFSG.conjugate F.V1 g = CFSG.conjugate F.V1 l) ∧
  ∀ g : G, g ∉ Subgroup.normalizer (V : Set G) → F.V1 ≤ CFSG.conjugate V g →
    (∃ h ∈ Subgroup.normalizer (F.V1 : Set G), CFSG.conjugate V g = CFSG.conjugate V h) ∧
      ⁅V, CFSG.conjugate V g⁆ = ⊥

@[expose] def Lemma12_5_9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (F : Frame125 T L V),
    Hyp125 G T L V → Concl12_5_9 T L V F

@[expose] def Concl12_5_10 (T L V : Subgroup G) (F : Frame125 T L V) : Prop :=
  (E3.wClos V 1 T ≤ Subgroup.centralizer (V : Set G) ∨
    autOn (E3.wClos V 1 T) V = autOn (ri T L F.V6) V) ∧
  Subgroup.centralizer (E3.cClos V 1 T : Set G) ≤ Subgroup.normalizer (L : Set G)

@[expose] def Lemma12_5_10 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (F : Frame125 T L V),
    Hyp125 G T L V → Concl12_5_10 T L V F

@[expose] def Concl12_5_12 (T L V : Subgroup G) (F : Frame125 T L V) : Prop :=
  ∀ H : Subgroup G, IsHStar T (Subgroup.normalizer (L : Set G)) H →
    H ≤ Subgroup.normalizer (F.V1 : Set G) →
      E1.nParam H = 2 ∧
        ∀ C : Subgroup G, C ≤ H ⊓ Subgroup.normalizer (L : Set G) → Odd (Nat.card C) →
          (∃ k : ℕ, C.relIndex (H ⊓ Subgroup.normalizer (L : Set G)) = 2 ^ k) →
            C ≠ ⊥ ∧ IsPGroup 3 C

@[expose] def Lemma12_5_12 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (F : Frame125 T L V),
    Hyp125 G T L V → Concl12_5_12 T L V F

end CFSG.Quasithin.H13
