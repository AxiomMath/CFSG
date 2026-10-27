module

public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenCls
public import CFSG.LocalAnalysis.WeakClosure81.SevenKSymplectic
public import CFSG.LocalAnalysis.WeakClosure81.SevenKUnitary
public import CFSG.LocalAnalysis.WeakClosure81.SevenNineDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open
open CFSG.LocalAnalysis.WeakClosure81.SevenK

@[expose] def OddTranspListAlt (X : Type) [Group X] (s : X) : Prop :=
  (∃ m n : ℕ,
      (IsSpGp (X ⧸ Subgroup.center X) m n ∧ IsSymplecticTransvection X m n s) ∨
      (IsPSUGp (X ⧸ Subgroup.center X) m n ∧ IsUnitaryTransvection X m n s) ∨
      IsOrthReflection X m n s ∨ IsWreathTransposition X n m s) ∨
    (∃ n : ℕ, IsSymTransposition X n s) ∨
    IsOrth63Reflection X s ∨
    (∃ L : Subgroup X, s ∈ L ∧
      IsSevenNineGroup ↥L {x : ↥L | (x : X) ∈ Subgroup.zpowers s ∧ x ≠ 1}) ∨
    (∃ n : ℕ, 1 < n ∧ CFSG.Quasithin.IsSz n (X ⧸ fusionZStar X))

@[expose] def OddTranspListExt (X : Type) [Group X] (s : X) : Prop :=
  ∃ (M : Subgroup (X ⧸ Subgroup.center X)) (_ : M.Normal),
    CFSG.Timmesfeld.Bridge.Asc72.IsMinimalNormal M ∧
    (∀ N : Subgroup (X ⧸ Subgroup.center X), CFSG.Timmesfeld.Bridge.Asc72.IsMinimalNormal N →
      N = M) ∧
    IsSimpleGroup M ∧ Subgroup.centralizer (M : Set (X ⧸ Subgroup.center X)) = ⊥ ∧
    2 < M.index ∧
    CFSG.Timmesfeld.Bridge.Asc72.WidthOne (QuotientGroup.mk' M ''
      {x : X ⧸ Subgroup.center X | IsConj (QuotientGroup.mk s) x}) ∧
    CFSG.Timmesfeld.Bridge.Asc72.IsOddTranspClass
      (CFSG.Timmesfeld.Bridge.Asc72.conjSet M (QuotientGroup.mk s)) ∧
    OddTranspListAlt ↥(M ⊔ Subgroup.zpowers (QuotientGroup.mk s : X ⧸ Subgroup.center X))
      ⟨QuotientGroup.mk s, Subgroup.mem_sup_right (Subgroup.mem_zpowers _)⟩

@[expose] def OddTranspositionListInputClsCorrected : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (s : X), orderOf s = 2 →
    CFSG.Timmesfeld.Bridge.Asc72.IsOddTransp {x : X | IsConj s x} →
    Subgroup.normalClosure ({s} : Set X) = ⊤ → CFSG.pCore 2 X = ⊥ →
    fusionOddCore X ≤ Subgroup.center X →
    OddTranspListAlt X s ∨ OddTranspListExt X s

@[expose] def OddTranspositionListInputClsDerivedEq : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (s : X), orderOf s = 2 →
    CFSG.Timmesfeld.Bridge.Asc72.IsOddTransp {x : X | IsConj s x} →
    Subgroup.normalClosure ({s} : Set X) = ⊤ → CFSG.pCore 2 X = ⊥ →
    fusionOddCore X ≤ Subgroup.center X →
    derivedSeries (X ⧸ Subgroup.center X) 1 = derivedSeries (X ⧸ Subgroup.center X) 2 →
    OddTranspListAlt X s

end CFSG.LocalAnalysis.WeakClosure81
