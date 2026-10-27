module

public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenTriDefs
public import CFSG.LocalAnalysis.WeakClosure81.SevenKSymplectic
public import CFSG.LocalAnalysis.WeakClosure81.SevenKUnitary
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Timmesfeld.Bridge.Asc72Basic

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld.Bridge CFSG.LocalAnalysis.WeakClosure81 CFSG.Open
open CFSG.LocalAnalysis.WeakClosure81.SevenK

structure ExtSetting (G : Type) [Group G] (t : G) (M : Subgroup G) [M.Normal] : Prop where
  setup : Asc72.Setup G {x | IsConj t x}
  rad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥
  minimal : Asc72.IsMinimalNormal M
  unique : ∀ N : Subgroup G, Asc72.IsMinimalNormal N → N = M
  simple : IsSimpleGroup M
  centralizer : Subgroup.centralizer (M : Set G) = ⊥
  index : 2 < M.index
  width : Asc72.WidthOne (QuotientGroup.mk' M '' {x | IsConj t x})
  cls : Asc72.IsOddTranspClass (Asc72.conjSet M t)

structure ExtLiftData (G : Type) [Group G] (t : G) (M : Subgroup G) (Y₀ : Type) [Group Y₀]
    (s₀ : Y₀) : Prop where
  order : orderOf s₀ = 2
  oddT : Asc72.IsOddTransp {y : Y₀ | IsConj s₀ y}
  gen : Subgroup.normalClosure ({s₀} : Set Y₀) = ⊤
  pCore : CFSG.pCore 2 Y₀ = ⊥
  oddCore : fusionOddCore Y₀ = Subgroup.center Y₀
  equiv : ∃ e : Y₀ ⧸ Subgroup.center Y₀ ≃* ↥(M ⊔ Subgroup.zpowers t),
    e (QuotientGroup.mk s₀) = ⟨t, Subgroup.mem_sup_right (Subgroup.mem_zpowers t)⟩

@[expose] def IsOrthPlusReflectionAt (X : Type) [Group X] (k n : ℕ) (s : X) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
    ∃ e : (X ⧸ Subgroup.center X) ≃* ↥(CFSG.PGLModel.orthogonalPlus k F),
      haveI := Fintype.ofFinite F
      IsRankOneIn ((e (QuotientGroup.mk s) : GL (Fin k ⊕ Fin k) F))

@[expose] def IsOrthMinusReflectionAt (X : Type) [Group X] (k n : ℕ) (s : X) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
    ∃ b c : F, (∀ t : F, t ^ 2 + b * t + c ≠ 0) ∧
      ∃ e : (X ⧸ Subgroup.center X) ≃* ↥(CFSG.PGLModel.orthogonalMinus k F b c),
        haveI := Fintype.ofFinite F
        IsRankOneIn ((e (QuotientGroup.mk s) : GL (Fin k ⊕ Fin k ⊕ Fin 2) F))

theorem isOrthReflection_iff {X : Type} [Group X] {m n : ℕ} {s : X} :
    IsOrthReflection X m n s ↔
      (∃ k : ℕ, 2 ≤ k ∧ m = 2 * k ∧ IsOrthPlusReflectionAt X k n s) ∨
        (∃ k : ℕ, 1 ≤ k ∧ m = 2 * k + 2 ∧ IsOrthMinusReflectionAt X k n s) :=
  Iff.rfl

@[expose] def ExtTrialityOrthPlusFour : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (M : Subgroup G) [M.Normal], ExtSetting G t M →
    ∀ (Y₀ : Type) [Group Y₀] [Finite Y₀] (s₀ : Y₀) (n : ℕ), ExtLiftData G t M Y₀ s₀ →
      IsOrthPlusReflectionAt Y₀ 4 n s₀ → IsTrialityOddTransp G t

@[expose] def ExtTrialityOrthOther : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (M : Subgroup G) [M.Normal], ExtSetting G t M →
    ∀ (Y₀ : Type) [Group Y₀] [Finite Y₀] (s₀ : Y₀) (n : ℕ), ExtLiftData G t M Y₀ s₀ →
      (∃ k : ℕ, 2 ≤ k ∧ k ≠ 4 ∧ IsOrthPlusReflectionAt Y₀ k n s₀) ∨
        (∃ k : ℕ, 1 ≤ k ∧ IsOrthMinusReflectionAt Y₀ k n s₀) → False

@[expose] def ExtTrialityNonOrth : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (M : Subgroup G) [M.Normal], ExtSetting G t M →
    ∀ (Y₀ : Type) [Group Y₀] [Finite Y₀] (s₀ : Y₀), ExtLiftData G t M Y₀ s₀ →
      (∃ m n : ℕ,
          (IsSpGp (Y₀ ⧸ Subgroup.center Y₀) m n ∧ IsSymplecticTransvection Y₀ m n s₀) ∨
          (IsPSUGp (Y₀ ⧸ Subgroup.center Y₀) m n ∧ IsUnitaryTransvection Y₀ m n s₀) ∨
          IsWreathTransposition Y₀ n m s₀) ∨
        (∃ n : ℕ, IsSymTransposition Y₀ n s₀) ∨ IsOrth63Reflection Y₀ s₀ ∨
        (∃ n : ℕ, 1 < n ∧ CFSG.Quasithin.IsSz n (Y₀ ⧸ fusionZStar Y₀)) → False

end CFSG.OddTranspositions.PartFour
