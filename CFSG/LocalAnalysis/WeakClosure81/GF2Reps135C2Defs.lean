module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsC

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

@[expose] def LEnd {W : Type} [CommGroup W] (L : Subgroup (MulAut W)) :
    Subring (AddMonoid.End (Additive W)) where
  carrier := {φ | ∀ g ∈ L, ∀ w : Additive W,
    φ (Additive.ofMul (g (Additive.toMul w))) = Additive.ofMul (g (Additive.toMul (φ w)))}
  zero_mem' := fun g _ w => by simp
  one_mem' := fun g _ w => by simp
  add_mem' := by
    intro a b ha hb g hg w
    show a _ + b _ = _
    rw [ha g hg w, hb g hg w]
    show _ = Additive.ofMul (g (Additive.toMul (a w) * Additive.toMul (b w)))
    rw [map_mul]
    rfl
  neg_mem' := by
    intro a ha g hg w
    show -(a _) = _
    rw [ha g hg w]
    show _ = Additive.ofMul (g (Additive.toMul (a w))⁻¹)
    rw [map_inv]
    rfl
  mul_mem' := by
    intro a b ha hb g hg w
    show a (b _) = _
    rw [hb g hg w, ha g hg]
    rfl

@[expose] def gs03Bound : StatedLieTag → ℕ → ℕ → ℕ
  | .PSL, 2, f => if Even f then 4 else 3
  | .PSL, 3, f => if f = 1 then 3 else 4
  | .PSL, 4, f => if f = 1 then 7 else 6
  | .PSL, n, _ => n
  | .PSU, 3, _ => 3
  | .PSU, 4, _ => 6
  | .PSU, n, _ => n
  | .PSp, 2, _ => 5
  | .PSp, n, _ => 2 * n + 1
  | .POmegaPlus, n, _ => 2 * n
  | .POmegaMinus, n, _ => 2 * n
  | .G2, _, _ => 5
  | .F4, _, _ => 8
  | .E6, _, _ => 9
  | .E7, _, _ => 10
  | .E8, _, _ => 11
  | .twistedE6, _, _ => 9
  | .trialityD4, _, _ => 7
  | .twistedB2, _, _ => 3
  | .twistedF4, _, _ => 7
  | .Tits, _, _ => 7
  | _, _, _ => 0

@[expose] def InnerDirectTag (t : StatedLieTag) : Prop := t = .PSL ∨ t = .PSU

@[expose] def OmQFamilyTag (t : StatedLieTag) (n f : ℕ) : Prop :=
  (t = .POmegaPlus ∧ 4 ≤ n ∧ 2 ≤ f) ∨ (t = .POmegaMinus ∧ 4 ≤ n ∧ 2 ≤ f)

@[expose] def Chev2ExcDirectTag (t : StatedLieTag) : Prop :=
  t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6

@[expose] def AlphaCase (S : Type) [Group S] (A : ℕ) : Prop :=
  (Nonempty (S ≃* alternatingGroup (Fin 6)) ∧ A = 5) ∨ (LieModel S .PSU 3 3 1 ∧ A = 4)

@[expose] def GS03AlphaFor (R : StatedLieTag → ℕ → ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Subgroup G), S.Normal →
    Subgroup.centralizer (S : Set G) = ⊥ → ∀ (t : StatedLieTag) (n f : ℕ), R t n f →
    LieModel ↥S t n 2 f → ∀ x : G, orderOf x = 2 →
      ∃ T : Finset G, T.card ≤ gs03Bound t n f ∧ (∀ y ∈ T, ∃ s ∈ S, y = s * x * s⁻¹) ∧
        S ≤ Subgroup.closure (T : Set G)

@[expose] def GS03AlphaOuterFor (R : StatedLieTag → ℕ → ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Subgroup G), S.Normal →
    Subgroup.centralizer (S : Set G) = ⊥ → ∀ (t : StatedLieTag) (n f : ℕ), R t n f →
    LieModel ↥S t n 2 f → ∀ x : G, orderOf x = 2 → x ∉ S →
      ∃ T : Finset G, T.card ≤ gs03Bound t n f ∧ (∀ y ∈ T, ∃ s ∈ S, y = s * x * s⁻¹) ∧
        S ≤ Subgroup.closure (T : Set G)

@[expose] def GS03AlphaL4 : Prop := GS03AlphaOuterFor fun t n f => t = .PSL ∧ n = 4 ∧ f = 1

@[expose] def GS03AlphaU6 : Prop := GS03AlphaOuterFor fun t n f => t = .PSU ∧ n = 6 ∧ f = 1

@[expose] def GS03AlphaA6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Subgroup G), S.Normal →
    Subgroup.centralizer (S : Set G) = ⊥ → Nonempty (↥S ≃* alternatingGroup (Fin 6)) →
    ∀ x : G, orderOf x = 2 →
      ∃ T : Finset G, T.card ≤ 5 ∧ (∀ y ∈ T, ∃ s ∈ S, y = s * x * s⁻¹) ∧
        S ≤ Subgroup.closure (T : Set G)

@[expose] def GS03AlphaU33 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Subgroup G), S.Normal →
    Subgroup.centralizer (S : Set G) = ⊥ → LieModel ↥S .PSU 3 3 1 →
    ∀ x : G, orderOf x = 2 →
      ∃ T : Finset G, T.card ≤ 4 ∧ (∀ y ∈ T, ∃ s ∈ S, y = s * x * s⁻¹) ∧
        S ≤ Subgroup.closure (T : Set G)

@[expose] def GS03AlphaOuterGeneral : Prop :=
  GS03AlphaOuterFor fun t n f => t = .PSL ∧ n = 4 ∧ f = 1

@[expose] def Chev2Natural (W : Type) [CommGroup W] (L : Subgroup (MulAut W)) : Prop :=
  (∃ n a : ℕ, (IsSLn ↥L n a ∧ BinaryNaturalSL L ⊤ ⊥ n a) ∨ (IsSpn ↥L n a ∧ NatSpn L ⊤ ⊥ n a) ∨
      (IsOmegaPlus ↥L n a ∧ NatOmegaPlus L ⊤ ⊥ n a) ∨
      (IsOmegaMinus ↥L n a ∧ NatOmegaMinus L ⊤ ⊥ n a)) ∨
    (∃ n : ℕ, IsSUn ↥L n 1 ∧ NatSUn L ⊤ ⊥ n 1)

@[expose] def Chev2Item3 (W : Type) [CommGroup W] [Finite W] (L : Subgroup (MulAut W)) : Prop :=
  (IsSpn ↥L 6 1 ∧ Nat.card W = 2 ^ 8) ∨ (IsSLn ↥L 5 1 ∧ Nat.card W = 2 ^ 10) ∨
    (LieModel ↥L .PSL 3 2 2 ∧ Nat.card W = 2 ^ 9) ∨ (IsL3 ↥L 1 ∧ Nat.card W = 2 ^ 8)

@[expose] def Chev2RowIdx : StatedLieTag → ℕ → ℕ → ℕ → Prop
  | .PSL, 2, 3, 8 => True
  | .PSL, 4, 1, 14 => True
  | .PSL, 4, 1, 20 => True
  | .PSL, 4, 2, 16 => True
  | .PSL, 6, 1, 15 => True
  | .PSL, 7, 1, 21 => True
  | .PSU, 4, 1, 14 => True
  | .E6, 0, 1, 27 => True
  | _, _, _, _ => False

@[expose] def FinRowStmt (t : StatedLieTag) (n f D : ℕ) : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (Y L : Subgroup (MulAut W)) (g : MulAut W),
      Is135Context Y L → g ∈ Y → orderOf g = 2 →
      LieModel (↥L ⧸ Subgroup.center ↥L) t n 2 f → Nat.card W = 2 ^ D →
      4 ≤ E3.mQuot ⊤ (fixV (Subgroup.zpowers g))

@[expose] def FinL28Steinberg : Prop := FinRowStmt .PSL 2 3 8

@[expose] def FinL4Two14 : Prop := FinRowStmt .PSL 4 1 14

@[expose] def FinL4Two20 : Prop := FinRowStmt .PSL 4 1 20

@[expose] def FinL4Four16 : Prop := FinRowStmt .PSL 4 2 16

@[expose] def FinL6Two15 : Prop := FinRowStmt .PSL 6 1 15

@[expose] def FinL7Two21 : Prop := FinRowStmt .PSL 7 1 21

@[expose] def FinU4Two14 : Prop := FinRowStmt .PSU 4 1 14

@[expose] def FinE6Two27 : Prop := FinRowStmt .E6 0 1 27

@[expose] def Chev135Rows : Prop :=
  FinL28Steinberg ∧ FinL4Two14 ∧ FinL4Two20 ∧ FinL4Four16 ∧ FinL6Two15 ∧ FinL7Two21 ∧
    FinU4Two14 ∧ FinE6Two27

@[expose] def U33SmallModules : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ L : Subgroup (MulAut W), IsQuasisimple ↥L → IsIrrOn L ⊤ ⊥ →
    LieModel (↥L ⧸ Subgroup.center ↥L) .PSU 3 3 1 → rk W ≤ 12 →
    LieModel ↥L .PSU 3 3 1 ∧ G2NaturalDerived L ⊤ ⊥ 1

end CFSG.LocalAnalysis.WeakClosure81
