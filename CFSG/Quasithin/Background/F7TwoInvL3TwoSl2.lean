module

public import CFSG.Quasithin.Background.F7TwoInvL2Even
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphAction

public section

namespace CFSG.Quasithin.F7Two

open scoped MatrixGroups
open CFSG.CGT.Timmesfeld75 CFSG.ComponentClassification.CatalogueBGraphForm

variable {K : Type} [Field K]

theorem invAutGen_sl2_involution [Finite K] (hK : ∃ f : ℕ, 2 ≤ f ∧ Nat.card K = 2 ^ f) :
    ∀ φ : MulAut SL(2, K), φ * φ = 1 → φ ≠ 1 → InvAutGen SL(2, K) φ := by
  obtain ⟨f, -, hKf⟩ := id hK
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card]; exact hKf)
  exact invAutGen_of_mulEquiv_forall (pslMulEquivSL (F := K)).symm (invAutGen_psl2_even hK)

theorem slGraphAut_two_apply_01 (g : SL(2, K)) : slGraphAut 2 K g 0 1 = g⁻¹ 1 0 := rfl

theorem slGraphAut_two_ne_one : (slGraphAut 2 K : MulAut SL(2, K)) ≠ 1 := by
  intro h
  have h1 := congrArg (fun a : MulAut SL(2, K) => (a (utriElt 1) : SL(2, K)) 0 1) h
  simp only [slGraphAut_two_apply_01, MulAut.one_apply, inv_apply_10, utriElt_apply_10,
    utriElt_apply_01, neg_zero] at h1
  exact zero_ne_one h1

theorem slGraphAut_two_mul_self : (slGraphAut 2 K : MulAut SL(2, K)) * slGraphAut 2 K = 1 := by
  rw [← pow_two]
  exact slGraphAut_sq 2 K

theorem sl2FieldAut_mul_self {σ : K ≃+* K} (hσ : ∀ x, σ (σ x) = x) :
    (sl2FieldAut σ : MulAut SL(2, K)) * sl2FieldAut σ = 1 :=
  MulEquiv.ext fun _ => Matrix.SpecialLinearGroup.ext _ _ fun _ _ => hσ _

theorem sl2FieldAut_ne_one {σ : K ≃+* K} (hσ : σ ≠ RingEquiv.refl K) :
    (sl2FieldAut σ : MulAut SL(2, K)) ≠ 1 := by
  intro h
  obtain ⟨t, ht⟩ : ∃ t : K, σ t ≠ t := by
    by_contra hall
    push Not at hall
    exact hσ (RingEquiv.ext hall)
  apply ht
  have h1 := MulEquiv.congr_fun h (utriElt t)
  rw [MulAut.one_apply, sl2FieldAut_utriElt] at h1
  exact utriElt_injective h1

theorem sl2FieldAut_commute_slGraphAut (σ : K ≃+* K) :
    Commute (sl2FieldAut σ : MulAut SL(2, K)) (slGraphAut 2 K) := by
  refine MulEquiv.ext fun g => Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  have h : sl2FieldAut σ (g⁻¹) = (sl2FieldAut σ g)⁻¹ := map_inv (sl2FieldAut σ) g
  change σ (g⁻¹ j i) = (sl2FieldAut σ g)⁻¹ j i
  rw [← h]
  rfl

@[expose] def sl2FieldGraph (σ : K ≃+* K) : MulAut SL(2, K) := sl2FieldAut σ * slGraphAut 2 K

theorem sl2FieldGraph_mul_self {σ : K ≃+* K} (hσ : ∀ x, σ (σ x) = x) :
    sl2FieldGraph σ * sl2FieldGraph σ = 1 := by
  unfold sl2FieldGraph
  rw [← pow_two, (sl2FieldAut_commute_slGraphAut σ).mul_pow, pow_two, pow_two,
    sl2FieldAut_mul_self hσ, slGraphAut_two_mul_self, one_mul]

theorem sl2FieldGraph_ne_one (σ : K ≃+* K) : sl2FieldGraph σ ≠ 1 := by
  intro h
  have h1 := congrArg (fun a : MulAut SL(2, K) => (a (utriElt 1) : SL(2, K)) 0 1) h
  simp only [sl2FieldGraph, MulAut.mul_apply, sl2FieldAut_apply_01, slGraphAut_two_apply_01,
    MulAut.one_apply, inv_apply_10, utriElt_apply_10, utriElt_apply_01, neg_zero, map_zero] at h1
  exact zero_ne_one h1

end CFSG.Quasithin.F7Two
