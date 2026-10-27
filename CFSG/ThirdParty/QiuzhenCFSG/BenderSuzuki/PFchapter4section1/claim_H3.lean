module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section1.claim_H1

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter4section1

open PFchapter1section1 PFAppendixIII

/-! # Peterfalvi, Part II, Chapter IV, Section 1, (H3) -/

public theorem canonical_compare_rightConjugate_D
    {L X : Type*} [Group L] [Finite L] [MulAction L X] [Finite X]
    (M Q D : Subgroup L) (t : L) (f g h : L → L)
    (htwo_transitive : MulAction.IsMultiplyPretransitive L X 2)
    (hpoint_stabilizer : ∃ x : X, M = MulAction.stabilizer L x)
    (ht_involution : IsInvolution t) (ht_not_mem_M : t ∉ M)
    (hD_eq : D = M ⊓ rightConjugate M t)
    (hQ_normal_in_M : (Q.subgroupOf M).Normal)
    (hQ_disjoint_D : Disjoint Q D) (hQ_sup_D : Q ⊔ D = M)
    (hf_mem : ∀ x : L, x ∈ Q → x ≠ 1 → f x ∈ Q ∧ f x ≠ 1)
    (hg_mem : ∀ x : L, x ∈ Q → x ≠ 1 → g x ∈ Q ∧ g x ≠ 1)
    (hh_mem : ∀ x : L, x ∈ Q → x ≠ 1 → h x ∈ D)
    (hcanonical_eq : ∀ x : L, x ∈ Q → x ≠ 1 → t * x * t = g x * h x * t * f x)
    {x a : L} (hxQ : x ∈ Q) (hx1 : x ≠ 1) (haD : a ∈ D) :
    let A := rightConjugateElem a t
    g (rightConjugateElem x a) = rightConjugateElem (g x) A ∧
      h (rightConjugateElem x a) = A⁻¹ * h x * a ∧
        f (rightConjugateElem x a) = rightConjugateElem (f x) A := by
  have _ := htwo_transitive
  have _ := hpoint_stabilizer
  have _ := ht_not_mem_M
  let A := rightConjugateElem a t
  have htinv : t⁻¹ = t := ht_involution.inv_eq_self
  have ht2 : t * t = 1 := by
    calc
      t * t = t⁻¹ * t := by rw [htinv]
      _ = 1 := inv_mul_cancel t
  have htt_mul : ∀ y : L, t * (t * y) = y := by
    intro y
    rw [← mul_assoc, ht2, one_mul]
  have hA_eq : A = t * a * t := by
    simp [A, rightConjugateElem, htinv]
  have hA_inv_eq : A⁻¹ = t * a⁻¹ * t := by
    simp [hA_eq, htinv, mul_assoc]
  have hatA_inv : a * t * A⁻¹ = t := by
    rw [hA_inv_eq]
    calc
      a * t * (t * a⁻¹ * t) = a * (t * (t * (a⁻¹ * t))) := by
        simp [mul_assoc]
      _ = a * (a⁻¹ * t) := by rw [htt_mul]
      _ = t := by simp
  have hfmem := hf_mem x hxQ hx1
  have hgmem := hg_mem x hxQ hx1
  have hhmem := hh_mem x hxQ hx1
  have hA_D : A ∈ D := by
    exact rightConjugateElem_mem_D (M := M) (D := D) htinv hD_eq haD
  have hyQ : rightConjugateElem x a ∈ Q := by
    have hxM :
        (⟨x, (rankOneSplit_Q_le_M hQ_sup_D) hxQ⟩ : M) ∈ Q.subgroupOf M := by
      exact hxQ
    have hconj :=
      hQ_normal_in_M.conj_mem'
        (⟨x, (rankOneSplit_Q_le_M hQ_sup_D) hxQ⟩ : M)
        hxM
        (⟨a, (rankOneSplit_D_le_M hD_eq) haD⟩ : M)
    simpa [rightConjugateElem, Subgroup.mem_subgroupOf, mul_assoc] using hconj
  have hy1 : rightConjugateElem x a ≠ 1 := by
    intro hy
    apply hx1
    have hcancel := congrArg (fun z => a * z * a⁻¹) hy
    simpa [rightConjugateElem, mul_assoc] using hcancel
  have hg_y_mem := hg_mem (rightConjugateElem x a) hyQ hy1
  have hh_y_mem := hh_mem (rightConjugateElem x a) hyQ hy1
  have hf_y_mem := hf_mem (rightConjugateElem x a) hyQ hy1
  have hq_gA : rightConjugateElem (g x) A ∈ Q := by
    have hgM :
        (⟨g x, (rankOneSplit_Q_le_M hQ_sup_D) hgmem.1⟩ : M) ∈ Q.subgroupOf M := by
      exact hgmem.1
    have hconj :=
      hQ_normal_in_M.conj_mem'
        (⟨g x, (rankOneSplit_Q_le_M hQ_sup_D) hgmem.1⟩ : M)
        hgM
        (⟨A, (rankOneSplit_D_le_M hD_eq) hA_D⟩ : M)
    simpa [rightConjugateElem, Subgroup.mem_subgroupOf, mul_assoc] using hconj
  have hq_fA : rightConjugateElem (f x) A ∈ Q := by
    have hfM :
        (⟨f x, (rankOneSplit_Q_le_M hQ_sup_D) hfmem.1⟩ : M) ∈ Q.subgroupOf M := by
      exact hfmem.1
    have hconj :=
      hQ_normal_in_M.conj_mem'
        (⟨f x, (rankOneSplit_Q_le_M hQ_sup_D) hfmem.1⟩ : M)
        hfM
        (⟨A, (rankOneSplit_D_le_M hD_eq) hA_D⟩ : M)
    simpa [rightConjugateElem, Subgroup.mem_subgroupOf, mul_assoc] using hconj
  have hd_Aha : A⁻¹ * h x * a ∈ D := by
    exact D.mul_mem (D.mul_mem (D.inv_mem hA_D) hhmem) haD
  have hcan_x := hcanonical_eq x hxQ hx1
  have hcan_y := hcanonical_eq (rightConjugateElem x a) hyQ hy1
  have hcandidate :
      t * rightConjugateElem x a * t =
        rightConjugateElem (g x) A * (A⁻¹ * h x * a) * t *
          rightConjugateElem (f x) A := by
    calc
      t * rightConjugateElem x a * t = A⁻¹ * (t * x * t) * A := by
        calc
          t * rightConjugateElem x a * t = t * (a⁻¹ * x * a) * t := by
            rw [rightConjugateElem]
          _ = (t * a⁻¹ * t) * (t * x * t) * (t * a * t) := by
            simp [htt_mul, mul_assoc]
          _ = A⁻¹ * (t * x * t) * A := by
            rw [hA_inv_eq, hA_eq]
      _ = A⁻¹ * (g x * h x * t * f x) * A := by
        rw [hcan_x]
      _ =
          rightConjugateElem (g x) A * (A⁻¹ * h x * a) * t *
            rightConjugateElem (f x) A := by
        have hfactor :
            rightConjugateElem (g x) A * (A⁻¹ * h x * a) * t *
                rightConjugateElem (f x) A =
              A⁻¹ * (g x * h x * t * f x) * A := by
          rw [rightConjugateElem, rightConjugateElem]
          calc
            (A⁻¹ * g x * A) * (A⁻¹ * h x * a) * t *
                (A⁻¹ * f x * A) =
              A⁻¹ * g x * h x * (a * t * A⁻¹) * f x * A := by
                simp [mul_assoc]
            _ = A⁻¹ * g x * h x * t * f x * A := by
                rw [hatA_inv]
            _ = A⁻¹ * (g x * h x * t * f x) * A := by
                simp [mul_assoc]
        exact hfactor.symm
  have hcompare :
      g (rightConjugateElem x a) * h (rightConjugateElem x a) * t *
          f (rightConjugateElem x a) =
        rightConjugateElem (g x) A * (A⁻¹ * h x * a) * t *
          rightConjugateElem (f x) A :=
    hcan_y.symm.trans hcandidate
  exact qd_t_q_unique (M := M) (Q := Q) (D := D) (t := t)
    (q₁ := g (rightConjugateElem x a))
    (d₁ := h (rightConjugateElem x a))
    (r₁ := f (rightConjugateElem x a))
    (q₂ := rightConjugateElem (g x) A)
    (d₂ := A⁻¹ * h x * a)
    (r₂ := rightConjugateElem (f x) A)
    htinv hD_eq (rankOneSplit_Q_le_M hQ_sup_D) (rankOneSplit_D_le_M hD_eq) hQ_disjoint_D
    hg_y_mem.1 hh_y_mem hf_y_mem.1 hq_gA hd_Aha hq_fA hcompare

public theorem claim_H3
    {L X : Type*} [Group L] [Finite L] [MulAction L X] [Finite X]
    (M Q D : Subgroup L) (t : L) (f g h : L → L)
    (htwo_transitive : MulAction.IsMultiplyPretransitive L X 2)
    (hpoint_stabilizer : ∃ x : X, M = MulAction.stabilizer L x)
    (ht_involution : IsInvolution t) (ht_not_mem_M : t ∉ M)
    (hD_eq : D = M ⊓ rightConjugate M t)
    (hQ_normal_in_M : (Q.subgroupOf M).Normal)
    (hQ_disjoint_D : Disjoint Q D) (hQ_sup_D : Q ⊔ D = M)
    (hf_mem : ∀ x : L, x ∈ Q → x ≠ 1 → f x ∈ Q ∧ f x ≠ 1)
    (hg_mem : ∀ x : L, x ∈ Q → x ≠ 1 → g x ∈ Q ∧ g x ≠ 1)
    (hh_mem : ∀ x : L, x ∈ Q → x ≠ 1 → h x ∈ D)
    (hcanonical_eq : ∀ x : L, x ∈ Q → x ≠ 1 → t * x * t = g x * h x * t * f x) :
    ∀ x a : L, x ∈ Q → x ≠ 1 → a ∈ D →
      f (rightConjugateElem x a) =
        rightConjugateElem (f x) (rightConjugateElem a t) := by
  intro x a hxQ hx1 haD
  exact (canonical_compare_rightConjugate_D M Q D t f g h htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_M hD_eq hQ_normal_in_M hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq hxQ hx1 haD).2.2

end PFchapter4section1
end CFSG.BenderSuzuki

