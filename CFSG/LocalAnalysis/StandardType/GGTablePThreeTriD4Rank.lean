module

public import CFSG.LocalAnalysis.StandardType.GGTriD4KnownInputsModel
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section Model

section TriD4CardAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

private theorem ggTriD4_card_le_of_isElemAbelian_aux :
    ∀ n : ℕ, 1 ≤ n →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = (2 ^ n) ^ 3 →
      IsSimpleGroup (GGTriD4R n K) →
        ∀ E : Subgroup (GGTriD4R n K), IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 2 := by
  intro n hn K _ _ hK _
  have : CharP K 2 := charP_two_of_card (m := n * 3) (by rw [hK, pow_mul])
  set σ := iterateFrobeniusEquiv K 2 n with hσdef
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => by
    rw [hσdef, iterateFrobeniusEquiv_apply, iterateFrobenius_def]
  obtain ⟨e⟩ := TableBExcSmallRest.nonempty_triD4_equiv hn K hK σ hσ
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have : Finite (GGTriD4R n K) := Finite.of_equiv _ e.symm.toEquiv
  intro E hE
  have h1 := TableBExcSmallRanks.card_lt_of_isElemAbelian_triD4 hn K hK σ hσ
    (CFSG.Open.IsElemAbelian.map hE e.toMonoidHom)
  rw [Subgroup.card_map_of_injective e.injective] at h1
  obtain ⟨k, hk⟩ := (CFSG.Open.IsElemAbelian.isPGroup hE).exists_card_eq
  rw [hk] at h1 ⊢
  exact Nat.pow_le_pow_right (by norm_num)
    (Nat.lt_succ_iff.mp ((Nat.pow_lt_pow_iff_right (by norm_num)).mp h1))

end TriD4CardAux

theorem ggTriD4_card_le_of_isElemAbelian :
    ∀ n : ℕ, 1 ≤ n → ∀ (K : Type) [Field K] [Finite K],
    Nat.card K = (2 ^ n) ^ 3 → IsSimpleGroup (GGTriD4R n K) →
      ∀ E : Subgroup (GGTriD4R n K), IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 2 :=
  ggTriD4_card_le_of_isElemAbelian_aux

theorem largeEvenLabelAll_triD4_innRank
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (ht : lab.tag = .triD4) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ =>
      I = Set.range (MulAut.conj : R →* MulAut R) ∧
        ∀ E : Subgroup R, IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 2) := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, -⟩ := hlab
  dsimp only at ht
  subst ht
  intro Q hQ
  exact recipeTwisted_and (P := LargeEvenSimpleGuard fun R _ I _ =>
      I = Set.range (MulAut.conj : R →* MulAut R) ∧
        ∀ E : Subgroup R, IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 2)
    (fun K _ _ hK hs _ =>
      ⟨ggTriD4InnDiagInput_holds n hn K hK hs,
        ggTriD4_card_le_of_isElemAbelian n hn K hK hs⟩) hQ

theorem largeEvenMarking_triD4_innRank
    {Y : Type*} [Group Y] {P : LargeEvenMarkProp Y}
    (h : LargeEvenMarking Y fun lab R _ I F θ => lab.tag = .triD4 ∧ P lab R I F θ) :
    LargeEvenMarking Y fun lab R _ I F θ => P lab R I F θ ∧
      I = Set.range (MulAut.conj : R →* MulAut R) ∧
        ∀ E : Subgroup R, IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 2 := by
  refine largeEvenMarking_mono
    (P := fun lab R _ I F θ => (lab.tag = .triD4 ∧ P lab R I F θ) ∧
      (lab.tag = .triD4 → I = Set.range (MulAut.conj : R →* MulAut R) ∧
        ∀ E : Subgroup R, IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 2))
    (P' := fun lab R _ I F θ => P lab R I F θ ∧
      I = Set.range (MulAut.conj : R →* MulAut R) ∧
        ∀ E : Subgroup R, IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 2) ?_
    (largeEvenMarking_and_labelAll_simple_imp
      (S := fun lab => lab.tag = .triD4)
      (P' := fun R _ I _ => I = Set.range (MulAut.conj : R →* MulAut R) ∧
        ∀ E : Subgroup R, IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 2)
      (fun lab hlab hS => largeEvenLabelAll_triD4_innRank hlab hS) h)
  rintro lab R _ I F θ ⟨⟨ht, hP⟩, hI⟩
  exact ⟨hP, (hI ht).1, (hI ht).2⟩

end Model

end CFSG.StandardType
