module

public import CFSG.LocalAnalysis.StandardType.GGTWPat2Ends
public import CFSG.LocalAnalysis.StandardType.GGTWPat2Adj
public import CFSG.LocalAnalysis.StandardType.GGTwoDepSmallS0
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLDType
public import CFSG.LocalAnalysis.StandardType.GGResLeaf

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
theorem ggTW_pattern2 {N : ℕ} (hN : 5 ≤ N) (pos : GGTWPos) {Λa : Type} [Fintype Λa]
    [DecidableEq Λa] (hΛa : Nat.card Λa = 2)
    {MK : CoxeterMatrix ({c : Fin (N - 1) // ggTWInJ N pos c.val} ⊕ Λa)}
    {CK : Matrix ({c : Fin (N - 1) // ggTWInJ N pos c.val} ⊕ Λa)
      ({c : Fin (N - 1) // ggTWInJ N pos c.val} ⊕ Λa) ℤ}
    (hWK : GGIsWeylMatrix MK) (hCK : GGIntCartan MK CK)
    (hA : ∃ e : Fin (N - 1) ≃ ({c : Fin (N - 1) // ggTWInJ N pos c.val} ⊕ Λa),
      MK = (CoxeterMatrix.A (N - 1)).reindex e)
    (hJ : ∀ i j : {c : Fin (N - 1) // ggTWInJ N pos c.val},
      CK (Sum.inl i) (Sum.inl j) = CartanMatrix.A (N - 1) i.1 j.1) :
    ∃ (a₁ a₂ : Λa) (c : Fin (N - 1)) (c₂ : Option (Fin (N - 1))), a₁ ≠ a₂ ∧
      GGTWPat2 N pos c.val (c₂.map Fin.val) ∧
      (∀ j : {c : Fin (N - 1) // ggTWInJ N pos c.val},
        CK (Sum.inr a₁) (Sum.inl j) = (if j.1 = c then -1 else 0) ∧
          CK (Sum.inl j) (Sum.inr a₁) = (if j.1 = c then -1 else 0) ∧
          CK (Sum.inr a₂) (Sum.inl j) = (if some j.1 = c₂ then -1 else 0) ∧
          CK (Sum.inl j) (Sum.inr a₂) = (if some j.1 = c₂ then -1 else 0)) ∧
      CK (Sum.inr a₁) (Sum.inr a₂) = (if c₂ = none then -1 else 0) ∧
      CK (Sum.inr a₂) (Sum.inr a₁) = (if c₂ = none then -1 else 0) ∧
      CK (Sum.inr a₁) (Sum.inr a₁) = 2 ∧ CK (Sum.inr a₂) (Sum.inr a₂) = 2 := by
  cases pos
  · exact ggTWPat2_ends hN hΛa hCK hA hJ
  · exact ggTWPat2_adj hN hΛa hCK hA hJ

end CFSG.StandardType
