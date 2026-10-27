module

public import CFSG.LocalAnalysis.StandardType.GGL45NtExcBridgeDefs
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcBridgeU
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcBridgeE6
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcBridgeTwE6
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcBridgeTriD4
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcBridgeTwF4

public section

namespace CFSG.HardMathSupport.C14Exc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.Assembly CFSG.StandardType
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


theorem excBridge_U
    (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] :
    GGL45NtOn (fun _ lab => lab.tag = .G2 ∨ lab.tag = .F4 ∨ lab.tag = .E7 ∨ lab.tag = .E8)
      fun p lab => ExcBridgeCont p L lab.tag := by
  intro p hp hp2 lab hlab hkg hS Q hQ
  obtain ⟨tag, rank, n⟩ := lab
  have hn : 1 ≤ n := hlab.1
  dsimp only at hS
  rcases hS with h | h | h | h <;> subst tag <;>
    dsimp only [CFSG.StandardType.LargeEvenRawDatum, LargeEvenRecipeChevalley] at hQ ⊢ <;>
    obtain ⟨K, hf, hfin, hK, hQ⟩ := hQ <;>
    haveI : Finite K := hfin <;>
    haveI : CharP K 2 := CFSG.StandardType.charP_two_of_card hK <;>
    refine ⟨K, hf, hfin, hK, hQ, fun _ hf => ?_⟩
  · obtain ⟨e, Q, h1, h2, h3, h4, h5⟩ := C14ExcBridgeU.bridge_untwisted (τ := .G2) (Or.inl rfl)
      (TableB.torusSubgroup_eq_top_of_mul_eq_smul _ K TableB.cartanG2_inv fun s => ⟨s, pow_one s⟩)
      hn hK L hp hf
    exact ⟨e, Q, h1, h2, h3, h4, h5⟩
  · obtain ⟨e, Q, h1, h2, h3, h4, h5⟩ := C14ExcBridgeU.bridge_untwisted (τ := .F4) (Or.inr (Or.inl rfl))
      (TableB.torusSubgroup_eq_top_of_mul_eq_smul _ K TableB.cartanF4_inv fun s => ⟨s, pow_one s⟩)
      hn hK L hp hf
    exact ⟨e, Q, h1, h2, h3, h4, h5⟩
  · obtain ⟨e, Q, h1, h2, h3, h4, h5⟩ := C14ExcBridgeU.bridge_untwisted (τ := .E7) (Or.inr (Or.inr (Or.inl rfl)))
      (TableB.torusSubgroup_eq_top_of_mul_eq_smul _ K TableB.cartanE7_adj
        (TableB.exists_sq_eq_of_charTwo K)) hn hK L hp hf
    exact ⟨e, Q, h1, h2, h3, h4, h5⟩
  · obtain ⟨e, Q, h1, h2, h3, h4, h5⟩ := C14ExcBridgeU.bridge_untwisted (τ := .E8) (Or.inr (Or.inr (Or.inr rfl)))
      (TableB.torusSubgroup_eq_top_of_mul_eq_smul _ K TableB.cartanE8_inv fun s => ⟨s, pow_one s⟩)
      hn hK L hp hf
    exact ⟨e, Q, h1, h2, h3, h4, h5⟩

theorem excBridge_E6
    (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] :
    GGL45NtOn (fun _ lab => lab.tag = .E6) fun p lab => ExcBridgeCont p L lab.tag := by
  intro p hp hp2 lab hlab hkg hS Q hQ
  obtain ⟨tag, rank, n⟩ := lab
  have hn : 1 ≤ n := hlab.1
  dsimp only at hS
  subst tag
  dsimp only [CFSG.StandardType.LargeEvenRawDatum, LargeEvenRecipeChevalley] at hQ ⊢
  obtain ⟨K, hf, hfin, hK, hQ⟩ := hQ
  haveI : Finite K := hfin
  haveI : CharP K 2 := CFSG.StandardType.charP_two_of_card hK
  refine ⟨K, hf, hfin, hK, hQ, fun _ hf => ?_⟩
  obtain ⟨e, Q, h1, h2, h3, h4, h5⟩ := C14ExcBridgeE6.bridge_chev (τ := .E6) hn hK L hp hf
  exact ⟨e, Q, h1, h2, h3, h4, h5⟩

theorem excBridge_twE6
    (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] :
    GGL45NtOn (fun _ lab => lab.tag = .twE6) fun p lab => ExcBridgeCont p L lab.tag := by
  intro p hp hp2 lab hlab hkg hS Q hQ
  obtain ⟨tag, rank, n⟩ := lab
  have hn : 1 ≤ n := hlab.1
  dsimp only at hS
  subst tag
  dsimp only [CFSG.StandardType.LargeEvenRawDatum, LargeEvenRecipeTwisted] at hQ ⊢
  obtain ⟨K, hf, hfin, hK, hQ⟩ := hQ
  haveI : Finite K := hfin
  refine ⟨K, hf, hfin, hK, hQ, fun _ hf => ?_⟩
  obtain ⟨e, Q, h1, h2, h3, h4, h5⟩ := C14ExcBridgeTwE6.bridge_twE6_chev hn hK L hp hp2 hf
  exact ⟨e, Q, h1, h2, h3, h4, h5⟩

theorem excBridge_triD4
    (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] :
    GGL45NtOn (fun p lab => GGL45NtFamExTw p lab ∧ lab.tag = .triD4)
      fun p lab => ExcBridgeCont p L lab.tag := by
  intro p hp hp2 lab hlab hkg hS Q hQ
  obtain ⟨tag, rank, n⟩ := lab
  have hn : 1 ≤ n := hlab.1
  obtain ⟨hfam, ht⟩ := hS
  dsimp only at ht
  subst tag
  have hp3 : p ≠ 3 := hfam.1.1
  dsimp only [CFSG.StandardType.LargeEvenRawDatum, LargeEvenRecipeTwisted] at hQ ⊢
  obtain ⟨K, hf, hfin, hK, hQ⟩ := hQ
  haveI : Finite K := hfin
  refine ⟨K, hf, hfin, hK, hQ, fun _ hf => ?_⟩
  obtain ⟨e, Q, h1, h2, h3, h4, h5⟩ := C14ExcBridgeTriD4.bridge_triD4_chev hn hK L hp hp3 hf
  exact ⟨e, Q, h1, h2, h3, h4, h5⟩


theorem excBridge_twF4
    (L : Type) [Field L] [IsAlgClosed L]
    [CharP L CFSG.LieType.Ree.ReeTag.F4.prime]
    [Algebra (ZMod 2) L] [Algebra.IsAlgebraic (ZMod 2) L] :
    GGL45NtOn (fun p lab => GGL45NtFamExTw p lab ∧ lab.tag = .twF4)
      fun p _ R _ I F => IsSimpleGroup R → (∃ f ∈ F, orderOf f = p) →
        ∃ (hf : CFSG.LieType.Ree.ReeTag.F4.ShortFaithful L) (a₀ : ℕ),
          IsExcBridgeSub p I F CFSG.LieType.Ree.ReeTag.F4.tag L
            (CFSG.LieType.Ree.ReeTag.F4.reeEndo L hf a₀) := by
  intro p hp hp2 lab hlab hkg hS Q hQ
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨-, ht⟩ := hS
  dsimp only at ht
  subst ht
  have ha : 1 ≤ (n - 1) / 2 := by have h3 : 3 ≤ n := hlab.2.2.2; omega
  dsimp only [CFSG.StandardType.LargeEvenRawDatum, LargeEvenRecipeTwF4] at hQ ⊢
  obtain ⟨K, hf, hfin, hK, hQ⟩ := hQ
  haveI : Finite K := hfin
  refine ⟨K, hf, hfin, hK, hQ, fun _ hfp => ?_⟩
  exact C14ExcBridgeTwF4.bridge_twF4_chev ha hK L hp hp2 hfp

end CFSG.HardMathSupport.C14Exc
