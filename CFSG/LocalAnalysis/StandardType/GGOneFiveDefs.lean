module

public import CFSG.LocalAnalysis.StandardType.GGSkeleton
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLDType

public section

namespace CFSG.StandardType

open CFSG.Assembly

section Defs

variable {G : Type} [Group G] [Finite G]

@[expose] def GGThmIHyp (p : ℕ) (B : Subgroup G) (x : G) (L : Subgroup G) : Prop :=
  IsSimpleGroup G ∧ (∃ a b : G, a * b ≠ b * a) ∧ KProper InCatalog G ∧ IsCharTwoType G ∧
    4 ≤ evenRank G ∧ p ∈ LargeEvenBeta 4 G ∧ LargeEvenSStar p B x L ∧
    LargeEvenStandardType p B x L

@[expose] def GGBstar (p : ℕ) (B Bs : Subgroup G) : Prop :=
  B ≤ Bs ∧ IsElemAbelian p Bs ∧ Nat.card Bs ≤ p * Nat.card B ∧
    ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs

@[expose] def GGConfig (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) : Prop :=
  GGThmIHyp p B x L ∧ GGBstar p B Bs ∧ LargeEvenStdSub p B x L D J

@[expose] def GGNbr (p : ℕ) (B : Subgroup G) (x : G) (D J : Subgroup G) (y : G) (K : Subgroup G) :
    Prop :=
  LargeEvenSHat p B y K ∧ LargeEvenNeighbor p x y K D J

@[expose] def GGOpAutTrivial (p : ℕ) (Bs : Subgroup G) : Prop :=
  ∀ X : Subgroup G, X ≤ Subgroup.normalizer (Bs : Set G) →
    Subgroup.centralizer (Bs : Set G) ≤ X →
    (X.subgroupOf (Subgroup.normalizer (Bs : Set G))).Normal →
    (∀ g ∈ X, ∃ k : ℕ, g ^ p ^ k ∈ Subgroup.centralizer (Bs : Set G)) →
    X ≤ Subgroup.centralizer (Bs : Set G)

@[expose] def GGInnerDiagOn (Bs X : Subgroup G) : Prop :=
  LargeEvenMarking X (fun _ _ _ I _ θ => Bs ≤ Subgroup.normalizer (X : Set G) ∧
    ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)

@[expose] def GGInnerDiagAll (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) : Prop :=
  GGInnerDiagOn Bs L ∧ ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K → GGInnerDiagOn Bs K

@[expose] def ggInduced (H Bs : Subgroup G) : Set (MulAut ↥Bs) :=
  {φ | ∃ g ∈ H, g ∈ Subgroup.normalizer (Bs : Set G) ∧
    ∀ b : ↥Bs, ((φ b : ↥Bs) : G) = g * b * g⁻¹}

@[expose] def ggAutomizer (H Bs : Subgroup G) : Subgroup (MulAut ↥Bs) :=
  Subgroup.closure (ggInduced H Bs)

@[expose] def GGIsReflection (p : ℕ) {Bs : Subgroup G} (φ : MulAut ↥Bs) : Prop :=
  φ ^ 2 = 1 ∧ Nat.card {b : ↥Bs // φ b = b} * p = Nat.card ↥Bs

@[expose] def GGIsTransvection (p : ℕ) {Bs : Subgroup G} (φ : MulAut ↥Bs) : Prop :=
  Nat.card {b : ↥Bs // φ b = b} * p = Nat.card ↥Bs ∧ ∀ b : ↥Bs, φ (b⁻¹ * φ b) = b⁻¹ * φ b

@[expose] def GGNoTransvection (p : ℕ) (Bs : Subgroup G) : Prop :=
  ∀ φ ∈ ggInduced ⊤ Bs, ¬ GGIsTransvection p φ

@[expose] def GGScalarsPmOne (Bs : Subgroup G) : Prop :=
  ∀ φ ∈ ggInduced ⊤ Bs, (∃ k : ℕ, ∀ b : ↥Bs, φ b = b ^ k) → φ ^ 2 = 1

@[expose] def GGReflGenerated (p : ℕ) {Bs : Subgroup G} (A : Subgroup (MulAut ↥Bs)) : Prop :=
  A = Subgroup.closure {φ | φ ∈ A ∧ GGIsReflection p φ}

end Defs

@[expose] def GGIsWeylMatrix {ι : Type} (M : CoxeterMatrix ι) : Prop :=
  (∃ (n : ℕ) (e : Fin n ≃ ι), 1 ≤ n ∧ (M = (CoxeterMatrix.A n).reindex e ∨
      (2 ≤ n ∧ M = (CoxeterMatrix.B n).reindex e) ∨
      (4 ≤ n ∧ M = (ggCoxeterMatrixD n).reindex e))) ∨
    (∃ e : Fin 6 ≃ ι, M = CoxeterMatrix.E₆.reindex e) ∨
    (∃ e : Fin 7 ≃ ι, M = CoxeterMatrix.E₇.reindex e) ∨
    (∃ e : Fin 8 ≃ ι, M = CoxeterMatrix.E₈.reindex e) ∨
    (∃ e : Fin 4 ≃ ι, M = CoxeterMatrix.F₄.reindex e) ∨
    (∃ e : Fin 2 ≃ ι, M = CoxeterMatrix.G₂.reindex e)

section Defs2

variable {G : Type} [Group G] [Finite G]

@[expose] def GGWeylReflectionGroup (p : ℕ) {Bs : Subgroup G} (A : Subgroup (MulAut ↥Bs)) : Prop :=
  ∃ (ι : Type) (M : CoxeterMatrix ι), GGIsWeylMatrix M ∧
    ∃ f : M.Group ≃* ↥A, ∀ i : ι, GGIsReflection p ((f (M.simple i) : ↥A) : MulAut ↥Bs)

@[expose] def GGFieldNbrCanonical (p : ℕ) (B Bs : Subgroup G) (x : G) (D J : Subgroup G) : Prop :=
  ∀ X : Subgroup G, X ≤ Subgroup.normalizer (Bs : Set G) →
    Subgroup.centralizer (Bs : Set G) ≤ X →
    (X.subgroupOf (Subgroup.normalizer (Bs : Set G))).Normal →
    (∀ g ∈ X, ∃ k : ℕ, g ^ p ^ k ∈ Subgroup.centralizer (Bs : Set G)) →
    ¬ X ≤ Subgroup.centralizer (Bs : Set G) →
    ∀ d ∈ D ⊓ (Bs ⊓ Subgroup.centralizer (X : Set G)), d ≠ 1 →
    ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      Subgroup.zpowers y = Subgroup.zpowers d →
      Subgroup.normalizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) ⊓
          Subgroup.normalizer (Subgroup.zpowers d : Set G) ≤
        Subgroup.normalizer (K : Set G)

@[expose] def GGSixHypPre (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) : Prop :=
  GGBstar p B Bs ∧ LargeEvenStdSub p B x L D J ∧ GGInnerDiagOn Bs (ggG0 p B x L D J) ∧
    Subgroup.normalizer (B : Set G) ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G) ∧
    Subgroup.normalizer (Bs : Set G) ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G)

end Defs2

section Elementary

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_stdSub_of_stdSubPre {p : ℕ} {B : Subgroup G} {x : G} {L : Subgroup G}
    (h : ∃ D K : Subgroup G, LargeEvenStdSubPre p B x L D K) :
    ∃ D K : Subgroup G, LargeEvenStdSub p B x L D K := by
  by_cases h3 : p = 3 ∧ ∃ D₁ K₁ : Subgroup G, LargeEvenStdSubPre p B x L D₁ K₁ ∧
      ¬ LargeEvenSmall K₁
  · obtain ⟨-, D₁, K₁, hT, hns⟩ := h3
    exact ⟨D₁, K₁, hT, fun _ => hns⟩
  · obtain ⟨D, K, hT⟩ := h
    exact ⟨D, K, hT, fun h' => absurd h' h3⟩

theorem exists_ggNbr {p : ℕ} {B : Subgroup G} {x : G} {L D J : Subgroup G}
    (hst : LargeEvenStandardType p B x L) (hDJ : LargeEvenStdSub p B x L D J) :
    ∃ (y : G) (K : Subgroup G), GGNbr p B x D J y K :=
  (hst.2.2.2 D J hDJ).1

theorem le_ggG0_left (p : ℕ) (B : Subgroup G) (x : G) (L D J : Subgroup G) :
    L ≤ ggG0 p B x L D J :=
  le_sup_left

theorem le_ggG0_of_ggNbr {p : ℕ} {B : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (h : GGNbr p B x D J y K) : K ≤ ggG0 p B x L D J :=
  le_sup_of_le_right (le_iSup_of_le y (le_iSup_of_le K (le_iSup_of_le h le_rfl)))

omit [Finite G] in
theorem GGBstar.le_centralizer {p : ℕ} {B Bs : Subgroup G} (h : GGBstar p B Bs) :
    Bs ≤ Subgroup.centralizer (B : Set G) := by
  intro g hg
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  have hc := h.2.1.1.is_comm.comm (⟨b, h.1 hb⟩ : ↥Bs) ⟨g, hg⟩
  exact congrArg Subtype.val hc

end Elementary

theorem largeEvenRawDatum_mono {lab : LargeEvenLabel} {Q Q' : LargeEvenRawCont}
    (hQQ' : ∀ (R : Type) [Group R] (I F : Set (MulAut R)), Q R I F → Q' R I F)
    (h : LargeEvenRawDatum lab Q) : LargeEvenRawDatum lab Q' := by
  obtain ⟨t, l, n⟩ := lab
  cases t
  all_goals dsimp only [LargeEvenRawDatum] at h ⊢
  all_goals try split_ifs at h ⊢
  all_goals first
    | (obtain ⟨K, i1, i2, hK, b, c, hbc, hq⟩ := h
       exact ⟨K, i1, i2, hK, b, c, hbc, hQQ' _ _ _ hq⟩)
    | (obtain ⟨K, i1, i2, hK, hq⟩ := h
       exact ⟨K, i1, i2, hK, hQQ' _ _ _ hq⟩)

theorem largeEvenMarking_mono {X : Type*} [Group X] {P P' : LargeEvenMarkProp X}
    (hPP' : ∀ (lab : LargeEvenLabel) (R : Type) [Group R] (I F : Set (MulAut R))
      (θ : X ⧸ Subgroup.center X ≃* R), P lab R I F θ → P' lab R I F θ)
    (h : LargeEvenMarking X P) : LargeEvenMarking X P' := by
  obtain ⟨hX, lab, hlab, hraw⟩ := h
  refine ⟨hX, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, hθ⟩
  exact ⟨hs, hna, θ, hPP' lab R I F θ hθ⟩

namespace Legacy
abbrev largeEvenRawDatum_mono := @CFSG.StandardType.largeEvenRawDatum_mono
abbrev largeEvenMarking_mono := @CFSG.StandardType.largeEvenMarking_mono
end Legacy

namespace Canonical
theorem largeEvenRawDatum_mono {lab : LargeEvenLabel} {Q Q' : LargeEvenRawCont}
    (hQQ' : ∀ (R : Type) [Group R] (I F : Set (MulAut R)), Q R I F → Q' R I F)
    (h : CFSG.Assembly.LargeEvenRawDatum lab Q) :
    CFSG.Assembly.LargeEvenRawDatum lab Q' := by
  obtain ⟨t, l, n⟩ := lab
  cases t
  all_goals dsimp only [CFSG.Assembly.LargeEvenRawDatum] at h ⊢
  all_goals try split_ifs at h ⊢
  all_goals first
    | (obtain ⟨K, i1, i2, hK, b, c, hbc, hq⟩ := h
       exact ⟨K, i1, i2, hK, b, c, hbc, hQQ' _ _ _ hq⟩)
    | (obtain ⟨K, i1, i2, hK, hq⟩ := h
       exact ⟨K, i1, i2, hK, hQQ' _ _ _ hq⟩)

theorem largeEvenMarking_mono {X : Type*} [Group X] {P P' : LargeEvenMarkProp X}
    (hPP' : ∀ (lab : LargeEvenLabel) (R : Type) [Group R] (I F : Set (MulAut R))
      (θ : X ⧸ Subgroup.center X ≃* R), P lab R I F θ → P' lab R I F θ)
    (h : CFSG.Assembly.LargeEvenMarking X P) :
    CFSG.Assembly.LargeEvenMarking X P' := by
  obtain ⟨hX, lab, hlab, hraw⟩ := h
  refine ⟨hX, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, hθ⟩
  exact ⟨hs, hna, θ, hPP' lab R I F θ hθ⟩
end Canonical

end CFSG.StandardType
