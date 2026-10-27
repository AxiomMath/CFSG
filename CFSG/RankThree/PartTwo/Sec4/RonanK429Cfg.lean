module

public import CFSG.RankThree.PartTwo.Sec4.Item47Inputs

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)
open CFSG.ClassicalGroups.UnitaryFlag (unitaryPSU)

@[expose] def IsType429 (X : Type) [Group X] : Prop :=
  (∃ (p e : ℕ) (_ : Fact p.Prime), 1 ≤ e ∧ IsoLThreePi X p e) ∨
    Nonempty (X ≃* alternatingGroup (Fin 7)) ∨
    Nonempty (X ≃* Blueprint.NativeSporadic.M12) ∨
    Nonempty (X ≃* Blueprint.NativeSporadic.M22) ∨
    Nonempty (X ≃* Blueprint.NativeSporadic.J2)

structure CfgS429 (S : Type) [Group S] [Finite S] (A : Subgroup (MulAut S)) (σ : MulAut S)
    (K : Subgroup S) : Prop where
  isE27 : Late.IsE27 A
  mem : σ ∈ A
  ne_one : σ ≠ 1
  le_autFix : K ≤ autFix σ
  isSubnormal : (K.subgroupOf (autFix σ)).IsSubnormal
  isPerfect : Group.IsPerfect K
  map_mem : ∀ a ∈ A, ∀ k ∈ K, (a : MulAut S) k ∈ K
  isType : IsType429 (K ⧸ CFSG.pCore 2 K)
  faithful : ∀ a ∈ A, (∀ k ∈ K, (a : MulAut S) k * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K) →
    a ∈ Subgroup.zpowers σ

@[expose] def IsFieldAutL3 {S : Type} [Group S] (σ : MulAut S) : Prop :=
  (∃ (F : Type) (_ : Field F) (_ : Finite F) (e : S ≃* projectiveSL 3 F),
      (stdPinnedPSL 3 F).HasKind (MulAut.congr e σ) .field) ∨
    ∃ (p f : ℕ) (F : Type) (_ : Field F) (h : UnitaryFieldData p f F) (_ : 2 < p ^ f)
      (e : S ≃* unitaryPSU h 3), (stdPinnedPSU3 h).HasKind (MulAut.congr e σ) .field

@[expose] def SurvA10D4 (S : Type) [Group S] (σ : MulAut S) (K : Subgroup S) : Prop :=
  (Nonempty (K ≃* alternatingGroup (Fin 7)) ∧ Nonempty (S ≃* alternatingGroup (Fin 10))) ∨
    ∃ n : ℕ, 1 ≤ n ∧ IsoLThreePi K 2 n ∧
      Blueprint.ChevalleyExceptionalModel S .trialityD4 2 n ∧ ¬ IsInnerAut σ

@[expose] def SurvL3 (S : Type) [Group S] (σ : MulAut S) (K : Subgroup S) : Prop :=
  ∃ n : ℕ, 1 ≤ n ∧ IsoLThreePi K 2 n ∧ IsoLThreePi S 2 (3 * n) ∧ IsFieldAutL3 σ

@[expose] def ConclS429 (S : Type) [Group S] [Finite S] (σ : MulAut S) (K : Subgroup S) : Prop :=
  CFSG.pCore 2 (autFix σ) = ⊥ ∧ (SurvA10D4 S σ K ∨ SurvL3 S σ K)

@[expose] def RowS429 (S : Type) [Group S] [Finite S] : Prop :=
  ∀ (A : Subgroup (MulAut S)) (σ : MulAut S) (K : Subgroup S), CfgS429 S A σ K →
    ConclS429 S σ K

@[expose] def RowS429NoL3 (S : Type) [Group S] [Finite S] : Prop :=
  ∀ (A : Subgroup (MulAut S)) (σ : MulAut S) (K : Subgroup S), CfgS429 S A σ K →
    CFSG.pCore 2 (autFix σ) = ⊥ ∧ SurvA10D4 S σ K

@[expose] def NoCfgS429 (S : Type) [Group S] [Finite S] : Prop :=
  ∀ (A : Subgroup (MulAut S)) (σ : MulAut S) (K : Subgroup S), ¬ CfgS429 S A σ K

theorem NoCfgS429.rowS429NoL3 {S : Type} [Group S] [Finite S] (h : NoCfgS429 S) :
    RowS429NoL3 S :=
  fun A σ K hc => absurd hc (h A σ K)

theorem RowS429NoL3.rowS429 {S : Type} [Group S] [Finite S] (h : RowS429NoL3 S) : RowS429 S :=
  fun A σ K hc => ⟨(h A σ K hc).1, Or.inl (h A σ K hc).2⟩

theorem NoCfgS429.rowS429 {S : Type} [Group S] [Finite S] (h : NoCfgS429 S) : RowS429 S :=
  h.rowS429NoL3.rowS429

@[expose] def K429CoverL3 : Prop :=
  ∀ (L : Type) [Group L] [Finite L], IsQuasisimple L → IsPGroup 3 (Subgroup.center L) →
    ∀ n : ℕ, 1 ≤ n → IsoLThreePi (L ⧸ Subgroup.center L) 2 (3 * n) →
    ∀ α : MulAut L, α ^ 3 = 1 → IsFieldAutL3 (centerDescend L α) →
    ∀ K : Subgroup L, K ≤ autFix α → IsQuasisimple K → (K.subgroupOf (autFix α)).IsSubnormal →
      K ⊓ Subgroup.center L = ⊥ → Subgroup.center L = ⊥

end CFSG.RankThree.PartTwo.Sec4.RonanK429
