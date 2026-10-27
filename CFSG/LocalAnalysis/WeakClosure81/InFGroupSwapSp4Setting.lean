module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs
public import CFSG.Quasithin.Vol2.Ch4Sec3L436Sp4Defs
public import CFSG.Quasithin.EmptyFaithful.T1521SSp4Act
public import CFSG.Quasithin.Vol2.Ch4Sec1Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81.SwapSp4

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13.Ch4 CFSG.Quasithin.H13.Ch4.L436
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17 (IsMaxParabolicOver SwapsParabolics)

structure Setting {Q : Type} [Group Q] [Finite Q] (L T P₀ P₁ : Subgroup Q) (n : ℕ)
    {F : Type} [Field F] [Finite F] (w : F × F → Q) : Prop where
  normal : L.Normal
  simple : IsSimpleGroup ↥L
  nonabelian : ∃ a b : ↥L, a * b ≠ b * a
  centralizer_eq : centralizer (L : Set Q) = ⊥
  two_le : 2 ≤ n
  sylow : IsSylowIn 2 T ⊤
  sup_eq : L ⊔ T = ⊤
  par₀ : IsMaxParabolicOver L (T ⊓ L) P₀
  par₁ : IsMaxParabolicOver L (T ⊓ L) P₁
  par_ne : P₀ ≠ P₁
  le_or_le : ∀ Y : Subgroup Q, T ⊓ L ≤ Y → Y < L → Y ≤ P₀ ∨ Y ≤ P₁
  inf_le : P₀ ⊓ P₁ ≤ normalizer ((T ⊓ L : Subgroup Q) : Set Q)
  swaps : SwapsParabolics T L
  concl₀ : Sp4ParConcl n L P₀ (T ⊓ L) (pCoreOf 2 (perfectCore P₀))
  concl₁ : Sp4ParConcl n L P₁ (T ⊓ L) (pCoreOf 2 (perfectCore P₁))
  k₂₀ : sp4K₂ L P₀ (T ⊓ L) (pCoreOf 2 (perfectCore P₀)) = perfectCore P₁
  k₂₁ : sp4K₂ L P₁ (T ⊓ L) (pCoreOf 2 (perfectCore P₁)) = perfectCore P₀
  card_F : Nat.card F = 2 ^ n
  w_injective : Function.Injective w
  w_add : ∀ x y : F × F, w (x + y) = w x * w y
  w_fst : ∀ b : F, w (b, 0) ∈ sp4C P₀ (pCoreOf 2 (perfectCore P₀))
  w_snd : ∀ c : F, w (0, c) ∈ sp4C P₁ (pCoreOf 2 (perfectCore P₁))
  act : ∀ x ∈ T, ∃ (l₁ l₂ : F) (σ : F ≃+* F) (ε : Bool), l₁ ≠ 0 ∧ l₂ ≠ 0 ∧
    (∀ v : F × F, x * w v * x⁻¹ = w (Sp4.vAct l₁ l₂ σ ε v)) ∧
    ((∀ v : F × F, Sp4.vAct l₁ l₂ σ ε v = v) → x ∈ L)
  out : ∀ A : Subgroup Q, A ≤ T → IsElemAbelian 2 A → Nat.card ↥A ≤ 2 * Nat.card ↥(A ⊓ L)
  index_odd : Odd n → L.index ≤ 2
  suzuki : Odd n → ∀ a ∈ T, a ∉ L → a * a = 1 →
    IsSimpleGroup ↥(L ⊓ centralizer ({a} : Set Q)) ∧
      ∃ x y : ↥(L ⊓ centralizer ({a} : Set Q)), x * y ≠ y * x

end CFSG.LocalAnalysis.WeakClosure81.SwapSp4
