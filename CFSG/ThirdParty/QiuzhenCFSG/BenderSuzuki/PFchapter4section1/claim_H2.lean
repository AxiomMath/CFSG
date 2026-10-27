module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section1.claim_H1

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter4section1

open PFchapter1section1 PFAppendixIII

/-! # Peterfalvi, Part II, Chapter IV, Section 1, (H2) -/

public theorem canonical_compare_f
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
    {x : L} (hxQ : x ∈ Q) (hx1 : x ≠ 1) :
    g (f x) = rightConjugateElem (g x)⁻¹ (h x) ∧
      h (f x) = (h x)⁻¹ ∧ f (f x) = x := by
  have _ := htwo_transitive
  have _ := hpoint_stabilizer
  have _ := ht_not_mem_M
  have htinv : t⁻¹ = t := ht_involution.inv_eq_self
  have ht2 : t * t = 1 := by
    calc
      t * t = t⁻¹ * t := by rw [htinv]
      _ = 1 := inv_mul_cancel t
  have hfmem := hf_mem x hxQ hx1
  have hgmem := hg_mem x hxQ hx1
  have hhmem := hh_mem x hxQ hx1
  have hg_fx_mem := hg_mem (f x) hfmem.1 hfmem.2
  have hh_fx_mem := hh_mem (f x) hfmem.1 hfmem.2
  have hf_fx_mem := hf_mem (f x) hfmem.1 hfmem.2
  have hq_conj :
      rightConjugateElem (g x)⁻¹ (h x) ∈ Q := by
    have hn :
        (⟨(g x)⁻¹, (rankOneSplit_Q_le_M hQ_sup_D) (Q.inv_mem hgmem.1)⟩ : M) ∈
          Q.subgroupOf M := by
      exact Q.inv_mem hgmem.1
    have hconj :=
      hQ_normal_in_M.conj_mem'
        (⟨(g x)⁻¹, (rankOneSplit_Q_le_M hQ_sup_D) (Q.inv_mem hgmem.1)⟩ : M)
        hn
        (⟨h x, (rankOneSplit_D_le_M hD_eq) hhmem⟩ : M)
    simpa [rightConjugateElem, Subgroup.mem_subgroupOf, mul_assoc] using hconj
  have hcan_x := hcanonical_eq x hxQ hx1
  have hcan_fx := hcanonical_eq (f x) hfmem.1 hfmem.2
  have hleft :
      t * f x * t = (h x)⁻¹ * (g x)⁻¹ * t * x := by
    have htmp :
        (h x)⁻¹ * (g x)⁻¹ * (t * x * t) = t * f x := by
      calc
        (h x)⁻¹ * (g x)⁻¹ * (t * x * t)
            = (h x)⁻¹ * (g x)⁻¹ * (g x * h x * t * f x) := by
                rw [hcan_x]
        _ = t * f x := by simp [mul_assoc]
    have h := congrArg (fun z => z * t) htmp
    simpa [ht2, mul_assoc] using h.symm
  have hcandidate :
      t * f x * t =
        rightConjugateElem (g x)⁻¹ (h x) * (h x)⁻¹ * t * x := by
    calc
      t * f x * t = (h x)⁻¹ * (g x)⁻¹ * t * x := hleft
      _ = rightConjugateElem (g x)⁻¹ (h x) * (h x)⁻¹ * t * x := by
          simp [rightConjugateElem, mul_assoc]
  have hcompare :
      g (f x) * h (f x) * t * f (f x) =
        rightConjugateElem (g x)⁻¹ (h x) * (h x)⁻¹ * t * x :=
    hcan_fx.symm.trans hcandidate
  exact qd_t_q_unique (M := M) (Q := Q) (D := D) (t := t)
    (q₁ := g (f x)) (d₁ := h (f x)) (r₁ := f (f x))
    (q₂ := rightConjugateElem (g x)⁻¹ (h x)) (d₂ := (h x)⁻¹)
    (r₂ := x)
    htinv hD_eq (rankOneSplit_Q_le_M hQ_sup_D) (rankOneSplit_D_le_M hD_eq) hQ_disjoint_D
    hg_fx_mem.1 hh_fx_mem hf_fx_mem.1
    hq_conj (D.inv_mem hhmem) hxQ hcompare

public theorem claim_H2
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
    ∀ x : L, x ∈ Q → x ≠ 1 → f (f x) = x := by
  intro x hxQ hx1
  exact (canonical_compare_f M Q D t f g h htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_M hD_eq hQ_normal_in_M hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq hxQ hx1).2.2

end PFchapter4section1
end CFSG.BenderSuzuki

