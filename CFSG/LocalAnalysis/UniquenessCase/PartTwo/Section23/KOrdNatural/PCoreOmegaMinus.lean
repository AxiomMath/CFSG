module

public import CFSG.Open.StatedDefs
public import CFSG.GroupTheory.PCore.Construction
import CFSG.ClassicalGroups.Orthogonal.StatedOmegaElementary
import CFSG.RankThree.GF2n.Stroth80.Sec78NatIrredOmegaTwo
import CFSG.Quasithin.H13.GoldschmidtG52Sec
import CFSG.LocalAnalysis.RankThreeUC.Section5.PCoreEqBotOfFaithfulIrreducible
import CFSG.Assembly.OrderReductions.InvertedSubgroup
import CFSG.Assembly.QuasithinDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KOrdNat

open CFSG.Open
open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap Matrix

private noncomputable def minusRep (K : Type) [Field K] {m : ℕ} (b c : K) :
    Representation K ↥(StatedOmega (StatedQuadMinus m K b c))
      (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) where
  toFun g := Matrix.toLin' ((g : GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K) :
    Matrix (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K)
  map_one' := by ext x; simp
  map_mul' := by intro a b; ext x; simp

private theorem minusRep_apply {K : Type} [Field K] {m : ℕ} (b c : K)
    (g : ↥(StatedOmega (StatedQuadMinus m K b c)))
    (v : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) :
    minusRep K b c g v = ((g : GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K) :
      Matrix (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K) *ᵥ v :=
  Matrix.toLin'_apply _ _

private theorem minusRep_injective {K : Type} [Field K] {m : ℕ} (b c : K) :
    Function.Injective (minusRep (m := m) K b c) := by
  intro g h heq
  refine Subtype.ext (Units.ext ?_)
  exact Matrix.toLin'.injective (by simpa [minusRep] using heq)

private theorem mem_statedOmega_of_mem_elementaryGroup {K : Type} [Field K] [Finite K] {m : ℕ}
    (hm : 2 ≤ m) {b c : K} (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {g : GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K}
    (hg : toLinEquiv (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K g ∈
      elementaryGroup (quadMinus m K b c)) :
    g ∈ StatedOmega (StatedQuadMinus m K b c) := by
  rw [statedOmega_eq_comap (coe_quadMinus m K b c), Subgroup.mem_comap]
  exact elementaryGroup_quadMinus_le_commutator hm hbc hg

private theorem natIrred_statedOmegaMinus {K : Type} [Field K] [Finite K] {m : ℕ} (hm : 2 ≤ m)
    {b c : K} (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    CFSG.RankThree.GF2n.Stroth80.NatIrred (StatedOmega (StatedQuadMinus m K b c)) := by
  intro U hU
  have hQ := CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite m K hbc
  let i0 : Fin (m - 1) := ⟨0, by omega⟩
  let a : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K := Pi.single (Sum.inr (Sum.inr 0)) 1
  have ha0 : a ≠ 0 := by
    intro h
    have h1 := congrFun h (Sum.inr (Sum.inr 0))
    simp [a] at h1
  have hae : polar (quadMinus m K b c) (minusPair K b c i0).e a = 0 := by
    rw [minusPair_e, polar_single_inl_quadMinus]
    simp [a, Pi.single_apply]
  have haf : polar (quadMinus m K b c) (minusPair K b c i0).f a = 0 := by
    rw [minusPair_f, polar_single_inr_quadMinus]
    simp [a, Pi.single_apply]
  have hW : ∀ u w : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K, ∀ x ∈ U,
      eichler (quadMinus m K b c) u w x ∈ U := by
    intro u w x hx
    have hg : (toLinEquiv (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K).symm
        (eichler (quadMinus m K b c) u w) ∈ StatedOmega (StatedQuadMinus m K b c) := by
      apply mem_statedOmega_of_mem_elementaryGroup hm hbc
      rw [MulEquiv.apply_symm_apply]
      exact eichler_mem_elementaryGroup (quadMinus m K b c) u w
    have hAx := hU _ hg x hx
    have h1 : ((toLinEquiv (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K).symm
        (eichler (quadMinus m K b c) u w) :
        Matrix (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K) *ᵥ x
        = eichler (quadMinus m K b c) u w x := by
      rw [← toLinEquiv_apply, MulEquiv.apply_symm_apply]
    rwa [h1] at hAx
  exact CFSG.RankThree.GF2n.Stroth80.submodule_eq_bot_or_top_of_eichler_invariant
    (Q := quadMinus m K b c) (e := (minusPair K b c i0).e) (f := (minusPair K b c i0).f)
    (minusPair K b c i0).Q_e (minusPair K b c i0).Q_f (minusPair K b c i0).polar_ef hQ
    ha0 hae haf hW

private theorem isIrreducible_minusRep {K : Type} [Field K] [Finite K] {m : ℕ} (hm : 2 ≤ m)
    {b c : K} (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (minusRep K b c (m := m)).IsIrreducible := by
  refine CFSG.Quasithin.H13.A6.G52.isIrreducible_of_forall_submodule
    (minusRep K b c) fun U hU => ?_
  exact natIrred_statedOmegaMinus hm hbc U fun g hg x hx => by
    have h := hU ⟨g, hg⟩ x hx
    rwa [minusRep_apply] at h

theorem pCore_statedOmega_minus_eq_bot {K : Type} [Field K] [Finite K] (p : ℕ) [Fact p.Prime]
    [CharP K p] {m : ℕ} (hm : 2 ≤ m) {b c : K} (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    CFSG.pCore p ↥(StatedOmega (StatedQuadMinus m K b c)) = ⊥ :=
  CFSG.LocalAnalysis.RankThreeUC.Section5.pCore_eq_bot_of_faithful_irreducible p
    (minusRep K b c (m := m)) (minusRep_injective b c) (isIrreducible_minusRep hm hbc)

end CFSG.LocalAnalysis.UniquenessCase.UC22.KOrdNat
