module

public import CFSG.RankThree.PartOne.AUTSL.FrobPair
public import CFSG.RankThree.PartOne.AUTSL.OmegaDickson
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataEmbedding

public section

namespace CFSG.RankThree.PartOne.AUTSL

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.RankThree.OrthogonalInvolutions
  Matrix

section FrobDickson

variable {K : Type} [Field K] [Finite K] [CharP K 2] (n : ℕ) (hn : 1 ≤ n) (b c : K) (hb : b ≠ 0)

omit [Finite K] [CharP K 2] in
theorem form_single_tailZero :
    coordinateQuadMinus n K hn b c (Pi.single (tailZero n hn) (1 : K)) = 1 := by
  rw [coordQuadMinus_apply']
  have h1 : ∀ i : Fin (n - 1), (Pi.single (tailZero n hn) (1 : K) : Fin (2 * n) → K)
      (minusIndexEquiv n hn (.inl i)) = 0 := fun i =>
    Pi.single_eq_of_ne (tailZero_ne_inl n hn i) _
  have h2 : ∀ i : Fin (n - 1), (Pi.single (tailZero n hn) (1 : K) : Fin (2 * n) → K)
      (minusIndexEquiv n hn (.inr (.inl i))) = 0 := fun i =>
    Pi.single_eq_of_ne (tailZero_ne_inr n hn i) _
  simp [h1, h2, Pi.single_eq_of_ne (tailZero_ne_tailOne n hn).symm]

theorem frobPair_pow_f_eq_inclusion {f : ℕ} (hf : Nat.card K = 2 ^ f)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hnd : (coordinateQuadMinus n K hn b c).polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧
      ∀ x ∈ T, coordinateQuadMinus n K hn b c x = 0) :
    ∃ (A : GL (Fin (2 * n)) K) (hA : A ∈ matrixIsometries (coordinateQuadMinus n K hn b c)),
      A ∉ matrixDerived (coordinateQuadMinus n K hn b c) ∧
        (frobPair n hn b c hb) ^ f =
          matrixIsometryInclusion (coordinateQuadMinus n K hn b c) ⟨A, hA⟩ := by
  obtain ⟨p, hp0, hright, hform⟩ := frobPair_pow_f n hn b c hb hf hirr
  set g := ((frobPair n hn b c hb) ^ f).val with hg
  have hvec : ∀ v : Fin (2 * n) → K, g.left.val *ᵥ v =
      v + (p * v (tailOne n hn)) • (Pi.single (tailZero n hn) (1 : K) : Fin (2 * n) → K) := by
    intro v
    funext k
    have h := hform v k
    rw [coordinateSemilinearMap_apply] at h
    have e : (fun i => g.right (v i)) = v := by
      funext i
      rw [hright]
      rfl
    rw [e] at h
    rw [h]
    by_cases hk : k = tailZero n hn
    · subst hk
      simp
    · simp [hk]
  have hA : g.left ∈ matrixIsometries (coordinateQuadMinus n K hn b c) := by
    obtain ⟨mu, hmu⟩ := ((frobPair n hn b c hb) ^ f).prop
    have h1 := hmu (Pi.single (tailZero n hn) (1 : K))
    rw [coordinateSemilinearMap_apply] at h1
    have hv1 : (Pi.single (tailZero n hn) (1 : K) : Fin (2 * n) → K) (tailOne n hn) = 0 :=
      Pi.single_eq_of_ne (tailZero_ne_tailOne n hn).symm _
    have e : (fun i => g.right ((Pi.single (tailZero n hn) (1 : K) : Fin (2 * n) → K) i)) =
        Pi.single (tailZero n hn) (1 : K) := by
      funext i
      rw [hright]
      rfl
    rw [e, hvec, hv1, mul_zero, zero_smul, add_zero, form_single_tailZero, hright] at h1
    have hmu1 : (mu : K) = 1 := by
      change (1 : K) = (mu : K) * 1 at h1
      rw [mul_one] at h1
      exact h1.symm
    rw [mem_matrixIsometries_iff]
    intro v
    have h2 := hmu v
    rw [coordinateSemilinearMap_apply] at h2
    have e2 : (fun i => g.right (v i)) = v := by
      funext i
      rw [hright]
      rfl
    rw [e2, hright, hmu1] at h2
    change coordinateQuadMinus n K hn b c (g.left.val *ᵥ v) = _
    rw [h2]
    simp
  refine ⟨g.left, hA, ?_, ?_⟩
  · rw [mem_matrixDerived_iff_even hnd hT hA]
    have hcomm : commSpace (matrixLinearIso g.left) =
        Submodule.span K {(Pi.single (tailZero n hn) (1 : K) : Fin (2 * n) → K)} := by
      ext x
      rw [mem_commSpace, Submodule.mem_span_singleton]
      constructor
      · rintro ⟨v, rfl⟩
        refine ⟨p * v (tailOne n hn), ?_⟩
        rw [matrixLinearIso_apply, hvec]
        abel
      · rintro ⟨a, rfl⟩
        refine ⟨(Pi.single (tailOne n hn) (a / p) : Fin (2 * n) → K), ?_⟩
        rw [matrixLinearIso_apply, hvec, Pi.single_eq_same, add_sub_cancel_left]
        congr 1
        field_simp
    rw [hcomm, finrank_span_singleton]
    · decide
    · intro h
      have := congrFun h (tailZero n hn)
      simp at this
  · refine Subtype.ext (SemidirectProduct.ext rfl ?_)
    change g.right = 1
    exact hright

end FrobDickson

end CFSG.RankThree.PartOne.AUTSL
