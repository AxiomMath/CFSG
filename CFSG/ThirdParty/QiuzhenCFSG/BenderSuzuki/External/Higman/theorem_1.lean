module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.lemma_11
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.lemma_12
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.lemma_13
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.theorem_1a
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.theorem_1b
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.theorem_1c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.theorem_1d
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.theorem_1e_isomorphic_summands
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.theorem_1e_scalar_coordinates

namespace CFSG
end CFSG
open CFSG

/-!
# Higman's classification theorem for Suzuki 2-groups
-/

namespace CFSG.BenderSuzuki
namespace External
namespace Higman

open PFAppendixIII

universe u

/-- Higman, *Suzuki 2-groups*, Theorem 1. -/
public theorem theorem1_abcdAlternatives_of_suzukiTwoGroup
    {P : Type u} [Group P] (hP : IsSuzukiTwoGroup P) :
    IsSuzukiTwoTypeA (⊤ : Subgroup P) ∨
      IsSuzukiTwoTypeB (⊤ : Subgroup P) ∨
      IsSuzukiTwoTypeC (⊤ : Subgroup P) ∨
      IsSuzukiTwoTypeD (⊤ : Subgroup P) := by
  rcases hP.2.2.2 with
    ⟨X, hXGroup, hXAction, hXcyclic, hXfaithful, hXregular⟩
  letI : Group X := hXGroup
  letI : MulDistribMulAction X P := hXAction
  have hXtrans : ∀ x : P, x ∈ involutions P →
      ∀ y : P, y ∈ involutions P → ∃ k : X, y = k • x := by
    intro x hx y hy
    rcases hXregular.2 x hx y hy with ⟨k, hk, _huniq⟩
    exact ⟨k, hk⟩
  have hXprimeSupport : ∀ p : ℕ, p.Prime → p ∣ Nat.card X →
      p ∣ Nat.card {x : P // x ∈ involutions P} := by
    obtain ⟨x0, _y0, hx0, _hy0, _hxy0⟩ := hP.2.2.1
    let orbit : X → {x : P // x ∈ involutions P} :=
      fun k => ⟨k • x0, hXregular.1 x0 hx0 k⟩
    have horbit_injective : Function.Injective orbit := by
      intro k l hkl
      have heq : k • x0 = l • x0 := congrArg Subtype.val hkl
      rcases hXregular.2 x0 hx0 (k • x0)
          (hXregular.1 x0 hx0 k) with ⟨a, _ha, huniq⟩
      exact (huniq k rfl).trans (huniq l heq).symm
    have horbit_surjective : Function.Surjective orbit := by
      rintro ⟨y, hy⟩
      rcases hXregular.2 x0 hx0 y hy with ⟨k, hk, _huniq⟩
      exact ⟨k, Subtype.ext hk.symm⟩
    have hcard : Nat.card X =
        Nat.card {x : P // x ∈ involutions P} :=
      Nat.card_congr (Equiv.ofBijective orbit
        ⟨horbit_injective, horbit_surjective⟩)
    intro p _hp hpdiv
    rw [← hcard]
    exact hpdiv
  rcases omegaLength_trichotomy_of_exists_omegaLength (X := X) (P := P) hP
      (exists_omegaLength_of_isSuzukiTwoGroup (X := X) (P := P) hP) with h2 | h3 | hlong
  · exact Or.inl (lemma11_length_two_typeA hP hXcyclic hXfaithful hXregular h2)
  · rcases lemma12_length_three_typeBCD hP hXcyclic hXfaithful hXtrans
      hXprimeSupport h3 with hB | hC | hD
    · exact Or.inr <| Or.inl hB
    · exact Or.inr <| Or.inr <| Or.inl hC
    · exact Or.inr <| Or.inr <| Or.inr hD
  · exact False.elim ((lemma13_no_length_greater_than_three
      hP hXcyclic hXfaithful hXregular hXtrans hXprimeSupport) hlong)

end Higman
end External
end CFSG.BenderSuzuki
