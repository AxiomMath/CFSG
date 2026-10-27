module

public import CFSG.Quasithin.Recognition.Stroth.WeissMoufang
public import CFSG.Quasithin.Recognition.Stroth.WeissQuotient
public import CFSG.Quasithin.Recognition.F4Basic
public import CFSG.Quasithin.EmptyFaithful.S1421Inputs
public import CFSG.Quasithin.Recognition.Stroth.WeissStrothLeaves
public import CFSG.Geometry.GeneralizedPolygons.Basic
public import CFSG.GH74.GLS.SP.GlueDefs
public import CFSG.GH74.BNPair.Defs
public import CFSG.GH74.BNPair.Statements
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4OctSys
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5System
public import CFSG.Quasithin.Background.SimsG4Defs
public import Mathlib.Combinatorics.SimpleGraph.Girth
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.GH74.GLS.Classes
public import CFSG.GH74.Statements
public import CFSG.LieType.Simplicity.Classical
public import CFSG.Quasithin.Background.F3
public import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112SliceSolv
public import CFSG.Quasithin.Recognition.F4Main
public import CFSG.Quasithin.Recognition.Stroth.SliceSzUReduction
public import CFSG.Quasithin.Vol2.GoldschmidtF112SliceDS
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4OctSpec
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4Simple
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModF4

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Stroth CFSG.Geometry.GeneralizedPolygons
  CFSG.GH74.GLS.SP CFSG.GH74.BNPair CFSG.QuasithinUnique
  CFSG.Quasithin.H13.F431.TwoF4 CFSG.Quasithin.H13.F431.Un
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

@[expose] def FGQHermitianUnique : Prop :=
  ∀ (q : ℕ) (V₁ V₂ : Type) [Fintype V₁] [Fintype V₂]
    (Γ₁ : SimpleGraph V₁) (Γ₂ : SimpleGraph V₂) [DecidableRel Γ₁.Adj] [DecidableRel Γ₂.Adj]
    (H₁ H₂ : Type) [Group H₁] [Group H₂] [MulAction H₁ V₁] [MulAction H₂ V₂]
    [FaithfulSMul H₁ V₁] [FaithfulSMul H₂ V₂] [GraphAction H₁ Γ₁] [GraphAction H₂ Γ₂],
    2 ≤ q → IsGeneralizedPolygon Γ₁ 4 → IsThick Γ₁ →
    IsGeneralizedPolygon Γ₂ 4 → IsThick Γ₂ →
    MoufangCondition H₁ Γ₁ 4 → MoufangCondition H₂ Γ₂ 4 →
    (∀ v : V₁, Γ₁.degree v = q ^ 2 + 1 ∨ Γ₁.degree v = q ^ 3 + 1) →
    (∀ v : V₂, Γ₂.degree v = q ^ 2 + 1 ∨ Γ₂.degree v = q ^ 3 + 1) →
    (∃ v : V₁, Γ₁.degree v = q ^ 2 + 1) → (∃ v : V₁, Γ₁.degree v = q ^ 3 + 1) →
    (∃ v : V₂, Γ₂.degree v = q ^ 2 + 1) → (∃ v : V₂, Γ₂.degree v = q ^ 3 + 1) →
    ∃ φ : Γ₁ ≃g Γ₂, ∀ v : V₁, Γ₂.degree (φ v) = Γ₁.degree v

@[expose] def FGQRootsAbelian : Prop :=
  ∀ (V : Type) [Fintype V] (Γ : SimpleGraph V) [DecidableRel Γ.Adj]
    (H : Type) [Group H] [MulAction H V] [FaithfulSMul H V] [GraphAction H Γ],
    IsGeneralizedPolygon Γ 4 → IsThick Γ → MoufangCondition H Γ 4 →
    ∀ (s t : ℕ), 1 < s → s ≤ t →
    (∀ v : V, Γ.degree v = s + 1 ∨ Γ.degree v = t + 1) →
    (¬ ∃ q : ℕ, s = q ^ 2 ∧ t = q ^ 3) →
    ∀ p : GPath Γ 4, p.NoBack →
    ∀ a b : H,
      a ∈ fixingSubgroup H (Γ.neighborSet (p 1)) ⊓ fixingSubgroup H (Γ.neighborSet (p 2)) ⊓
        fixingSubgroup H (Γ.neighborSet (p 3)) →
      b ∈ fixingSubgroup H (Γ.neighborSet (p 1)) ⊓ fixingSubgroup H (Γ.neighborSet (p 2)) ⊓
        fixingSubgroup H (Γ.neighborSet (p 3)) →
      a * b = b * a

@[expose] def Tits83T8System : Prop :=
  ∀ (X X' : Type) [Group X] [Group X'] [Finite X] [Finite X']
    (D : CFSG.GH74.BNPair.RankTwoSystem X 8)
    (D' : CFSG.GH74.BNPair.RankTwoSystem X' 8),
    (∀ i : ℤ, 1 ≤ i → i ≤ 8 → Nat.card (D.root i) = Nat.card (D'.root i)) →
    ∃ φ : D.U ≃* D'.U, ∀ (i : ℤ), 1 ≤ i → i ≤ 8 → ∀ x : D.U,
      ((x : X) ∈ D.root i ↔ ((φ x : D'.U) : X') ∈ D'.root i)

section EdgeBall

universe u w

variable {α : RankTwoAmalgam.{u}} {Y : Type w} [Group Y]

@[expose] def edgeBall (r : ℕ) (c : α.Completion Y) : Set c.Γ :=
  {w | c.graph.dist c.xv w ≤ r ∨ c.graph.dist c.lv w ≤ r}

end EdgeBall

abbrev psiB {X : Type} [Group X] {P1 : Subgroup X} (P2 : Subgroup X) {D : Type} [Group D]
    (ψ₁ : ↥P1 →* D) : ↥(P1 ⊓ P2) →* D :=
  ψ₁.comp (Subgroup.inclusion (inf_le_left : P1 ⊓ P2 ≤ P1))

@[expose] def IsWeissEmbedding (n : ℕ) {X : Type} [Group X] {P1 P2 : Subgroup X}
    {Y : Type} [Group Y] (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y)
    {V : Type} (Δ : SimpleGraph V) {D : Type} [Group D] [MulAction D V]
    (u v : V) (ψ₁ : ↥P1 →* D) (ψ₂ : ↥P2 →* D) (ι : c.Γ → V) : Prop :=
  Function.Injective ψ₁ ∧ Function.Injective ψ₂ ∧
    (∀ g : ↥(P1 ⊓ P2),
      ψ₁ (Subgroup.inclusion (show P1 ⊓ P2 ≤ P1 from inf_le_left) g) =
        ψ₂ (Subgroup.inclusion (show P1 ⊓ P2 ≤ P2 from inf_le_right) g)) ∧
    ψ₁.range ⊔ ψ₂.range = ⊤ ∧
    ι c.xv = u ∧ ι c.lv = v ∧
    Set.BijOn ι (edgeBall (n - 1) c) Set.univ ∧
    (∀ w w', w ∈ edgeBall (n - 2) c → w' ∈ edgeBall (n - 1) c →
      (Δ.Adj (ι w) (ι w') ↔ c.graph.Adj w w')) ∧
    (∀ (g : ↥P1) (h : ↥(c.φ1.range ⊔ c.φ2.range)), (h : Y) = c.φ1 g →
      ∀ w, c.graph.dist c.xv w ≤ n - 1 → ψ₁ g • ι w = ι (h • w)) ∧
    (∀ (g : ↥P2) (h : ↥(c.φ1.range ⊔ c.φ2.range)), (h : Y) = c.φ2 g →
      ∀ w, c.graph.dist c.lv w ≤ n - 1 → ψ₂ g • ι w = ι (h • w))

@[expose] def Weiss80Polygon8Fin : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (P1 P2 : Subgroup X) (a m : ℕ), 1 ≤ a → 2 ≤ m →
    ¬ IsPGroup 2 ↥((P1 ⊓ P2).subgroupOf P1).normalCore →
    ¬ IsPGroup 2 ↥((P2 ⊓ P1).subgroupOf P2).normalCore →
    HasNormalCopy (Subconst P1 P2) ↥(Sz a) →
    HasNormalCopy (Subconst P2 P1)
      (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 m)) →
    (∃ e : ℕ, 1 ≤ e ∧ (P1 ⊓ P2).relIndex P1 = 2 ^ e + 1) →
    (∃ e : ℕ, 1 ≤ e ∧ (P1 ⊓ P2).relIndex P2 = 2 ^ e + 1) →
    ∀ (Y : Type) [Group Y] [Finite Y] (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y),
      c.IsFaithful →
      MoufangCondition ↥(c.φ1.range ⊔ c.φ2.range) c.graph 8 →
      WeissFree ↥(c.φ1.range ⊔ c.φ2.range) c.graph 8 →
      ((2 * 8 + 2 : ℕ) : ℕ∞) < c.graph.egirth →
      ∃ (V : Type) (_ : Fintype V) (Δ : SimpleGraph V) (_ : DecidableRel Δ.Adj)
        (D : Type) (_ : Group D) (_ : Finite D) (_ : MulAction D V) (_ : FaithfulSMul D V)
        (_ : GraphAction D Δ) (u v : V) (ψ₁ : ↥P1 →* D) (ψ₂ : ↥P2 →* D) (ι : c.Γ → V),
        IsGeneralizedPolygon Δ 8 ∧ IsThick Δ ∧ Δ.Adj u v ∧ MoufangCondition D Δ 8 ∧
          ψ₁.range ≤ MulAction.stabilizer D u ∧ ψ₂.range ≤ MulAction.stabilizer D v ∧
          IsWeissEmbedding 8 c Δ u v ψ₁ ψ₂ ι ∧
          (∃ e : ℕ, 1 ≤ e ∧ Δ.degree u = 2 ^ e + 1) ∧
          (∃ e : ℕ, 1 ≤ e ∧ Δ.degree v = 2 ^ e + 1)

@[expose] def Weiss80Polygon4Fin : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (P1 P2 : Subgroup X) (k m : ℕ) (F : Type) [Field F]
    [Finite F], 2 ≤ k → 3 ≤ m → Nat.card F = (2 ^ k) ^ 2 → m = 2 * k →
    HasNormalCopy (Subconst P1 P2) (StatedProj (StatedSU 3 (2 ^ k) F)) →
    HasNormalCopy (Subconst P2 P1)
      (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 m)) →
    (∃ e : ℕ, 1 ≤ e ∧ (P1 ⊓ P2).relIndex P1 = 2 ^ e + 1) →
    (∃ e : ℕ, 1 ≤ e ∧ (P1 ⊓ P2).relIndex P2 = 2 ^ e + 1) →
    ∀ (Y : Type) [Group Y] [Finite Y] (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y),
      c.IsFaithful →
      MoufangCondition ↥(c.φ1.range ⊔ c.φ2.range) c.graph 4 →
      WeissFree ↥(c.φ1.range ⊔ c.φ2.range) c.graph 4 →
      ((2 * 4 + 2 : ℕ) : ℕ∞) < c.graph.egirth →
      ∃ (V : Type) (_ : Fintype V) (Δ : SimpleGraph V) (_ : DecidableRel Δ.Adj)
        (D : Type) (_ : Group D) (_ : Finite D) (_ : MulAction D V) (_ : FaithfulSMul D V)
        (_ : GraphAction D Δ) (u v : V) (ψ₁ : ↥P1 →* D) (ψ₂ : ↥P2 →* D) (ι : c.Γ → V),
        IsGeneralizedPolygon Δ 4 ∧ IsThick Δ ∧ Δ.Adj u v ∧ MoufangCondition D Δ 4 ∧
          ψ₁.range ≤ MulAction.stabilizer D u ∧ ψ₂.range ≤ MulAction.stabilizer D v ∧
          IsWeissEmbedding 4 c Δ u v ψ₁ ψ₂ ι ∧
          (∃ e : ℕ, 1 ≤ e ∧ Δ.degree u = 2 ^ e + 1) ∧
          (∃ e : ℕ, 1 ≤ e ∧ Δ.degree v = 2 ^ e + 1)

@[expose] def Tits83Orders : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (D : CFSG.GH74.BNPair.RankTwoSystem X 8),
    ∃ f : ℕ, Odd f ∧
      (((∀ i : ℤ, 1 ≤ i → i ≤ 8 → Odd i → Nat.card (D.root i) = 2 ^ f) ∧
          (∀ i : ℤ, 1 ≤ i → i ≤ 8 → Even i → Nat.card (D.root i) = 2 ^ (2 * f))) ∨
        ((∀ i : ℤ, 1 ≤ i → i ≤ 8 → Even i → Nat.card (D.root i) = 2 ^ f) ∧
          (∀ i : ℤ, 1 ≤ i → i ≤ 8 → Odd i → Nat.card (D.root i) = 2 ^ (2 * f))))

@[expose] def SubconstUnitaryNonabelian : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Ω : Type) [Fintype Ω] [MulAction Y Ω] [FaithfulSMul Y Ω]
    (k : ℕ) (F : Type) [Field F] [Finite F], 2 ≤ k → Nat.card F = (2 ^ k) ^ 2 →
    MulAction.IsMultiplyPretransitive Y Ω 2 →
    (∃ e : ℕ, 1 ≤ e ∧ Fintype.card Ω = 1 + 2 ^ e) →
    HasNormalCopy Y (StatedProj (StatedSU 3 (2 ^ k) F)) →
    ∀ (ω : Ω) (R : Subgroup Y), R ≤ MulAction.stabilizer Y ω →
      (∀ ω₁ ω₂ : Ω, ω₁ ≠ ω → ω₂ ≠ ω → ∃! r : ↥R, (r : Y) • ω₁ = ω₂) →
      ∃ a ∈ R, ∃ b ∈ R, a * b ≠ b * a

@[expose] def BorelResidualSplit {G : Type} [Group G] {n : ℕ} (R : RankTwoSystem G n) : Prop :=
  R.B ≤ (CFSG.Quasithin.SimsG4.twoPrimeResidualOf R.P₁ ⊓ R.P₂) ⊔
    (CFSG.Quasithin.SimsG4.twoPrimeResidualOf R.P₂ ⊓ R.P₁)

@[expose] def BorelResidualSplitTransport : Prop :=
  ∀ (G G₀ : Type) [Group G] [Group G₀] [Finite G] (n : ℕ)
    (R : RankTwoSystem G n) (R₀ : RankTwoSystem G₀ n), Nonempty (G ≃* G₀) →
    IsSylowTwoOf R.U ⊤ → IsSylowTwoOf R₀.U ⊤ → BorelResidualSplit R₀ → BorelResidualSplit R

@[expose] def ExtensionOfStabilizers : Prop :=
  ∀ (X : Type) [Group X] (P1 P2 : Subgroup X) (D : Type) [Group D] (L Du Dv : Subgroup D)
    (ψ₁ : ↥P1 →* D) (ψ₂ : ↥P2 →* D),
    L.Normal → Function.Injective ψ₁ → Function.Injective ψ₂ →
    (∀ g : ↥(P1 ⊓ P2),
      ψ₁ (Subgroup.inclusion (show P1 ⊓ P2 ≤ P1 from inf_le_left) g) =
        ψ₂ (Subgroup.inclusion (show P1 ⊓ P2 ≤ P2 from inf_le_right) g)) →
    ψ₁.range = Du → ψ₂.range = Dv → (psiB P2 ψ₁).range = Du ⊓ Dv →
    Subgroup.centralizer (L : Set D) = ⊥ →
    Subgroup.normalizer ((L ⊓ Du : Subgroup D) : Set D) = Du →
    Subgroup.normalizer ((L ⊓ Dv : Subgroup D) : Set D) = Dv →
    Subgroup.normalizer ((L ⊓ Du ⊓ Dv : Subgroup D) : Set D) ≤ Du →
    ∀ (L₀ : Type) [Group L₀] (κ : ↥L ≃* L₀) (TD : Subgroup L₀),
      IsYAmalgamPair TD ((Du.subgroupOf L).map κ.toMonoidHom)
        ((Dv.subgroupOf L).map κ.toMonoidHom) →
      IsExtensionOfLieAmalgam L₀ P1 P2

@[expose] def aptRoot {V : Type} (D : Type) [Group D] [MulAction D V] (Γ : SimpleGraph V)
    (n : ℕ) (t : ZMod (2 * n) → V) (k : ℤ) : Subgroup D :=
  ⨅ i ∈ Set.Icc (1 : ℤ) ((n : ℤ) - 1),
    fixingSubgroup D (Γ.neighborSet (t ((k + i : ℤ) : ZMod (2 * n))))

@[expose] def IsPolygonApartment {V : Type} (Γ : SimpleGraph V) (n : ℕ)
    (t : ZMod (2 * n) → V) : Prop :=
  Function.Injective t ∧ ∀ k : ZMod (2 * n), Γ.Adj (t k) (t (k + 1))

@[expose] def pathRootGroup {V : Type} (D : Type) [Group D] [MulAction D V] (Γ : SimpleGraph V)
    {n : ℕ} (p : GPath Γ n) : Subgroup D :=
  ⨅ i ∈ Set.Icc (1 : ℕ) (n - 1), fixingSubgroup D (Γ.neighborSet (p i))

@[expose] def littleGroup {V : Type} (D : Type) [Group D] [MulAction D V] (Γ : SimpleGraph V)
    (n : ℕ) : Subgroup D :=
  ⨆ (p : GPath Γ n) (_ : p.NoBack), pathRootGroup D Γ p

@[expose] def MoufangTitsAxioms (n : ℕ) : Prop :=
  ∀ (V : Type) [Fintype V] (Γ : SimpleGraph V) [DecidableRel Γ.Adj]
    (D : Type) [Group D] [MulAction D V] [FaithfulSMul D V] [GraphAction D Γ],
    3 ≤ n → IsGeneralizedPolygon Γ n → IsThick Γ → MoufangCondition D Γ n →
      ∀ t : ZMod (2 * n) → V, IsPolygonApartment Γ n t →
        let U : ℤ → Subgroup D := aptRoot D Γ n t;
        (∀ k : ℤ, U k ≠ ⊥) ∧
          (∀ i j : ℤ, i < j → j < i + (n : ℤ) → ∀ u ∈ U i, ∀ v ∈ U j,
            u * v * u⁻¹ * v⁻¹ ∈ ⨆ k ∈ Set.Ioo i j, U k) ∧
          (∀ i : ℤ, ∀ f g : ℤ → D,
            (∀ k ∈ intList (i + 1) (i + (n : ℤ)), f k ∈ U k) →
            (∀ k ∈ intList (i + 1) (i + (n : ℤ)), g k ∈ U k) →
            ((intList (i + 1) (i + (n : ℤ))).map f).prod =
              ((intList (i + 1) (i + (n : ℤ))).map g).prod →
            ∀ k ∈ intList (i + 1) (i + (n : ℤ)), f k = g k) ∧
          (∀ i : ℤ, ∀ u ∈ U i, u ≠ 1 →
            ∃ v ∈ U (i + (n : ℤ)), ∃ w ∈ U (i + (n : ℤ)),
              ∀ j : ℤ,
                (U j).map (MulAut.conj (v * u * w)).toMonoidHom =
                  U (2 * i + (n : ℤ) - j))

@[expose] def RootGroupRegular (n : ℕ) : Prop :=
  ∀ (V : Type) [Fintype V] (Γ : SimpleGraph V) [DecidableRel Γ.Adj]
    (D : Type) [Group D] [MulAction D V] [FaithfulSMul D V] [GraphAction D Γ],
    3 ≤ n → IsGeneralizedPolygon Γ n → IsThick Γ → MoufangCondition D Γ n →
      ∀ p : GPath Γ n, p.NoBack → ∀ y y' : V, Γ.Adj (p n) y → Γ.Adj (p n) y' →
        y ≠ p (n - 1) → y' ≠ p (n - 1) →
        ∃! g : ↥(pathRootGroup D Γ p), (g : D) • y = y'

@[expose] def WeissEmbeddingFacts (n : ℕ) : Prop :=
  ∀ (X : Type) [Group X] (P1 P2 : Subgroup X) (Y : Type) [Group Y]
    (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y),
    3 ≤ n → c.IsFaithful → MoufangCondition ↥(c.φ1.range ⊔ c.φ2.range) c.graph n →
    ∀ (V : Type) [Fintype V] (Δ : SimpleGraph V) [DecidableRel Δ.Adj]
      (D : Type) [Group D] [MulAction D V] [FaithfulSMul D V] [GraphAction D Δ]
      (u v : V) (ψ₁ : ↥P1 →* D) (ψ₂ : ↥P2 →* D) (ι : c.Γ → V),
      IsGeneralizedPolygon Δ n → IsThick Δ → MoufangCondition D Δ n →
      IsWeissEmbedding n c Δ u v ψ₁ ψ₂ ι →
        Δ.Adj u v ∧
          ψ₁.range ≤ MulAction.stabilizer D u ∧ ψ₂.range ≤ MulAction.stabilizer D v ∧
          ψ₁.range ⊓ MulAction.stabilizer D v = (psiB P2 ψ₁).range ∧
          ψ₂.range ⊓ MulAction.stabilizer D u = (psiB P2 ψ₁).range ∧
          (∀ w, Δ.Adj u w → ∃ g : ↥P1, ψ₁ g • v = w) ∧
          (∀ w, Δ.Adj v w → ∃ g : ↥P2, ψ₂ g • u = w) ∧
          Δ.degree u = (P1 ⊓ P2).relIndex P1 ∧ Δ.degree v = (P1 ⊓ P2).relIndex P2 ∧
          (∀ p : GPath Δ n, p.NoBack → ∀ j : ℕ, j + 1 ≤ n →
            ((p j = u ∧ p (j + 1) = v) ∨ (p j = v ∧ p (j + 1) = u)) →
            pathRootGroup D Δ p ≤ (psiB P2 ψ₁).range)

@[expose] def MoufangRankTwoSystem (n : ℕ) : Prop :=
  ∀ (V : Type) [Fintype V] (Γ : SimpleGraph V) [DecidableRel Γ.Adj]
    (D : Type) [Group D] [MulAction D V] [FaithfulSMul D V] [GraphAction D Γ],
    3 ≤ n → IsGeneralizedPolygon Γ n → IsThick Γ → MoufangCondition D Γ n →
      (∀ v : V, ∃ e : ℕ, Γ.degree v = 2 ^ e + 1) →
      ∀ t : ZMod (2 * n) → V, IsPolygonApartment Γ n t →
        ∃ R : RankTwoSystem ↥(littleGroup D Γ n) n,
          (∀ i : ℤ, 1 ≤ i → i ≤ (n : ℤ) →
            (R.root i).map (littleGroup D Γ n).subtype = aptRoot D Γ n t i ∧
              (R.root (-i)).map (littleGroup D Γ n).subtype =
                aptRoot D Γ n t (i + (n : ℤ))) ∧
          R.Xplus = ⊤ ∧
          R.B = (MulAction.stabilizer D (t n) ⊓ MulAction.stabilizer D (t (n + 1))).subgroupOf
            (littleGroup D Γ n) ∧
          R.P₁ = (MulAction.stabilizer D (t (n + 1))).subgroupOf (littleGroup D Γ n) ∧
          R.P₂ = (MulAction.stabilizer D (t n)).subgroupOf (littleGroup D Γ n)

@[expose] def MoufangLittleNormal (n : ℕ) : Prop :=
  ∀ (V : Type) [Fintype V] (Γ : SimpleGraph V) [DecidableRel Γ.Adj]
    (D : Type) [Group D] [MulAction D V] [FaithfulSMul D V] [GraphAction D Γ],
    3 ≤ n → IsGeneralizedPolygon Γ n → IsThick Γ → MoufangCondition D Γ n →
      (littleGroup D Γ n).Normal ∧
        Subgroup.centralizer (littleGroup D Γ n : Set D) = ⊥ ∧
        (∀ z : V, Subgroup.normalizer
            ((littleGroup D Γ n ⊓ MulAction.stabilizer D z : Subgroup D) : Set D) =
          MulAction.stabilizer D z) ∧
        (∀ z z' : V, Γ.Adj z z' → ∀ d ∈ Subgroup.normalizer
            ((littleGroup D Γ n ⊓ MulAction.stabilizer D z ⊓ MulAction.stabilizer D z' :
              Subgroup D) : Set D),
          (d • z = z ∧ d • z' = z') ∨ (d • z = z' ∧ d • z' = z))

@[expose] def OctagonIdentification : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (R : RankTwoSystem X 8)
    (K : Type) [Field K] [Finite K] [CharP K F4.prime] (a : ℕ)
    (hR : RGD2 8 (octH K a) (octR1 K a) (octR2 K a) (Ug K a) (octRoot K a))
    [IsSimpleGroup (Gm K a)],
    1 ≤ a → Nat.card K = 2 ^ (2 * a + 1) →
      (∀ i : ℤ, 1 ≤ i → i ≤ 8 →
        Nat.card (R.root i) = Nat.card ((octSystemOf hR).root i)) →
      Nonempty (R.Xplus ≃* Gm K a)

@[expose] def SubconstNatural : Prop :=
  (∀ (Y : Type) [Group Y] [Finite Y] (Ω : Type) [Fintype Ω] [MulAction Y Ω]
      [FaithfulSMul Y Ω] (a : ℕ), 1 ≤ a →
      MulAction.IsMultiplyPretransitive Y Ω 2 →
      (∃ e : ℕ, 1 ≤ e ∧ Fintype.card Ω = 1 + 2 ^ e) →
      HasNormalCopy Y ↥(Sz a) → Fintype.card Ω = 2 ^ (2 * (2 * a + 1)) + 1) ∧
    (∀ (Y : Type) [Group Y] [Finite Y] (Ω : Type) [Fintype Ω] [MulAction Y Ω]
      [FaithfulSMul Y Ω] (m : ℕ), 2 ≤ m →
      MulAction.IsMultiplyPretransitive Y Ω 2 →
      (∃ e : ℕ, 1 ≤ e ∧ Fintype.card Ω = 1 + 2 ^ e) →
      HasNormalCopy Y (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 m)) →
      Fintype.card Ω = 2 ^ m + 1) ∧
    (∀ (Y : Type) [Group Y] [Finite Y] (Ω : Type) [Fintype Ω] [MulAction Y Ω]
      [FaithfulSMul Y Ω] (k : ℕ) (F : Type) [Field F] [Finite F], 2 ≤ k →
      Nat.card F = (2 ^ k) ^ 2 →
      MulAction.IsMultiplyPretransitive Y Ω 2 →
      (∃ e : ℕ, 1 ≤ e ∧ Fintype.card Ω = 1 + 2 ^ e) →
      HasNormalCopy Y (StatedProj (StatedSU 3 (2 ^ k) F)) →
      Fintype.card Ω = 2 ^ (3 * k) + 1)

@[expose] def QuadrangleIdentification : Prop :=
  ∀ (V : Type) [Fintype V] (Γ : SimpleGraph V) [DecidableRel Γ.Adj]
    (D : Type) [Group D] [MulAction D V] [FaithfulSMul D V] [GraphAction D Γ],
    IsGeneralizedPolygon Γ 4 → IsThick Γ → MoufangCondition D Γ 4 →
      ∀ (k m : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2] [Fact (Nat.Prime 2)]
        (hF : Nat.card F = (2 ^ k) ^ 2) (ζ : traceZero (unitaryInvolution F 2 k))
        [Fact ((ζ : F) ≠ 0)],
        2 ≤ k → 3 ≤ m →
          (∀ v : V, Γ.degree v = 2 ^ m + 1 ∨ Γ.degree v = 2 ^ (3 * k) + 1) →
          (∃ v : V, Γ.degree v = 2 ^ m + 1) →
          (∃ v : V, Γ.degree v = 2 ^ (3 * k) + 1) →
          (∃ p : GPath Γ 4, p.NoBack ∧ Γ.degree (p 0) = 2 ^ (3 * k) + 1 ∧
            ∃ a ∈ pathRootGroup D Γ p, ∃ b ∈ pathRootGroup D Γ p, a * b ≠ b * a) →
          m = 2 * k ∧
            ∃ (φ : Γ ≃g (un5System hF ζ).graph)
              (κ : ↥(littleGroup D Γ 4) ≃*
                (SU (unitaryInvolution F 2 k) 5 ⧸
                  Subgroup.center (SU (unitaryInvolution F 2 k) 5))),
              ∀ (g : ↥(littleGroup D Γ 4)) (v : V),
                φ ((g : D) • v) = (un5System hF ζ).action (κ g) (φ v)

@[expose] def StabilizersOfPolygon (n : ℕ) : Prop :=
  ∀ (X : Type) [Group X] (P1 P2 : Subgroup X)
    (V : Type) [Fintype V] (Γ : SimpleGraph V) [DecidableRel Γ.Adj]
    (D : Type) [Group D] [Finite D] [MulAction D V] [GraphAction D Γ],
    3 ≤ n → IsGeneralizedPolygon Γ n → IsThick Γ → MoufangCondition D Γ n →
    (littleGroup D Γ n).Normal →
    ∀ (u v : V) (ψ₁ : ↥P1 →* D) (ψ₂ : ↥P2 →* D),
      (∀ g : ↥(P1 ⊓ P2),
        ψ₁ (Subgroup.inclusion (show P1 ⊓ P2 ≤ P1 from inf_le_left) g) =
          ψ₂ (Subgroup.inclusion (show P1 ⊓ P2 ≤ P2 from inf_le_right) g)) →
      ψ₁.range ≤ MulAction.stabilizer D u → ψ₂.range ≤ MulAction.stabilizer D v →
      ψ₁.range ⊔ ψ₂.range = ⊤ →
      ψ₁.range ⊓ MulAction.stabilizer D v = (psiB P2 ψ₁).range →
      ψ₂.range ⊓ MulAction.stabilizer D u = (psiB P2 ψ₁).range →
      (∀ w, Γ.Adj u w → ∃ g : ↥P1, ψ₁ g • v = w) →
      (∀ w, Γ.Adj v w → ∃ g : ↥P2, ψ₂ g • u = w) →
      ∀ R : RankTwoSystem ↥(littleGroup D Γ n) n,
        R.B = (MulAction.stabilizer D u ⊓ MulAction.stabilizer D v).subgroupOf
          (littleGroup D Γ n) →
        ((R.P₁ = (MulAction.stabilizer D u).subgroupOf (littleGroup D Γ n) ∧
            R.P₂ = (MulAction.stabilizer D v).subgroupOf (littleGroup D Γ n)) ∨
          (R.P₁ = (MulAction.stabilizer D v).subgroupOf (littleGroup D Γ n) ∧
            R.P₂ = (MulAction.stabilizer D u).subgroupOf (littleGroup D Γ n))) →
        R.U.map (littleGroup D Γ n).subtype ≤ (psiB P2 ψ₁).range →
        IsSylowTwoOf R.U ⊤ →
        BorelResidualSplit R →
          ψ₁.range = MulAction.stabilizer D u ∧ ψ₂.range = MulAction.stabilizer D v ∧
            (psiB P2 ψ₁).range = MulAction.stabilizer D u ⊓ MulAction.stabilizer D v

@[expose] def OctBorelResidualSplit : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K F4.prime] (a : ℕ)
    (hR : RGD2 8 (octH K a) (octR1 K a) (octR2 K a) (Ug K a) (octRoot K a))
    [IsSimpleGroup (Gm K a)], 1 ≤ a → Nat.card K = 2 ^ (2 * a + 1) →
      BorelResidualSplit (octSystemOf hR)

@[expose] def Un5BorelResidualSplit : Prop :=
  ∀ (k : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2] [Fact (Nat.Prime 2)]
    (hF : Nat.card F = (2 ^ k) ^ 2) (ζ : traceZero (unitaryInvolution F 2 k))
    [Fact ((ζ : F) ≠ 0)], 2 ≤ k → BorelResidualSplit (un5System hF ζ)

@[expose] def OctLieModel : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K F4.prime] (a : ℕ), 1 ≤ a →
    Nat.card K = 2 ^ (2 * a + 1) → IsTwistedF4Over (2 * a + 1) (Gm K a)

@[expose] def Weiss80OctagonOfLeaves : Prop :=
  Weiss80Polygon8Fin → Tits83T8System → Tits83Orders → SubconstNatural → Weiss80Octagon

@[expose] def Weiss80UnitaryOfLeaves : Prop :=
  Weiss80Polygon4Fin → FGQHermitianUnique → FGQRootsAbelian → SubconstNatural →
    SubconstUnitaryNonabelian → Weiss80UnitaryQuadrangle

end CFSG.Quasithin.Stroth
