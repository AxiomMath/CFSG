module

public import Mathlib.GroupTheory.IsSubnormal
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.Quasithin.C58

open Subgroup

variable {G : Type*} [Group G]

theorem isSubnormal_of_normalizerCondition [Finite G] (hNC : NormalizerCondition G)
    (H : Subgroup G) : H.IsSubnormal := by
  classical
  suffices h : ∀ n : ℕ, ∀ H : Subgroup G, H.index = n → H.IsSubnormal from h _ H rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro H hn
    by_cases htop : H = ⊤
    · rw [htop]; exact IsSubnormal.top
    · set N := normalizer (H : Set G) with hNdef
      have hlt : H < N := hNC H (lt_top_iff_ne_top.mpr htop)
      have hle : H ≤ N := hlt.le
      have hNn : (H.subgroupOf N).Normal :=
        (normal_subgroupOf_iff_le_normalizer hle).mpr le_rfl
      have hrel : H.relIndex N * N.index = H.index := relIndex_mul_index hle
      have h2 : 2 ≤ H.relIndex N := by
        have hne : H.subgroupOf N ≠ ⊤ := fun h =>
          (ne_of_lt hlt) (le_antisymm hle ((subgroupOf_eq_top (H := H) (K := N)).mp h))
        exact one_lt_index_of_ne_top hne
      have hpos : 0 < N.index := Nat.pos_of_ne_zero (index_ne_zero_of_finite (H := N))
      have hind : N.index < n := by
        rw [← hn, ← hrel]
        nlinarith
      exact IsSubnormal.step H N hle (ih N.index hind N rfl) hNn

theorem isSubnormal_of_isNilpotent [Finite G] [Group.IsNilpotent G] (H : Subgroup G) :
    H.IsSubnormal :=
  isSubnormal_of_normalizerCondition Group.normalizerCondition_of_isNilpotent H

theorem isSubnormal_subgroupOf_of_pow_mem [Finite G] {p : ℕ} [Fact p.Prime]
    {N A B : Subgroup G} (hNA : N ≤ A) (hAB : A ≤ B) (hBN : B ≤ normalizer (N : Set G))
    (hp : ∀ b ∈ B, ∃ k : ℕ, b ^ p ^ k ∈ N) : (A.subgroupOf B).IsSubnormal := by
  set N' : Subgroup B := N.subgroupOf B with hN'
  have hN'n : N'.Normal := (normal_subgroupOf_iff_le_normalizer (hNA.trans hAB)).mpr hBN
  have hp' : IsPGroup p (↥B ⧸ N') := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H b =>
      obtain ⟨k, hk⟩ := hp b b.2
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact hk
  have : Group.IsNilpotent (↥B ⧸ N') := hp'.isNilpotent
  have h1 := (isSubnormal_of_isNilpotent ((A.subgroupOf B).map (QuotientGroup.mk' N'))).comap
    (QuotientGroup.mk' N')
  rwa [comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr
    (fun x hx => (mem_subgroupOf.mpr (hNA (mem_subgroupOf.mp hx))))] at h1

theorem isSubnormal_subgroupOf_trans {A B C : Subgroup G} (hAB : A ≤ B)
    (hA : (A.subgroupOf B).IsSubnormal) (hB : (B.subgroupOf C).IsSubnormal) :
    (A.subgroupOf C).IsSubnormal := by
  have hle : A.subgroupOf C ≤ B.subgroupOf C := fun x hx =>
    mem_subgroupOf.mpr (hAB (mem_subgroupOf.mp hx))
  refine IsSubnormal.trans hle ?_ hB
  let f : ↥(B.subgroupOf C) →* ↥B :=
    { toFun := fun k => ⟨((k : C) : G), mem_subgroupOf.mp k.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have e : (A.subgroupOf C).subgroupOf (B.subgroupOf C) = (A.subgroupOf B).comap f := by
    ext x
    simp only [mem_subgroupOf, mem_comap]
    rfl
  rw [e]
  exact hA.comap f

theorem isSubnormal_subgroupOf_of_le {A B C : Subgroup G} (hBC : B ≤ C)
    (hA : (A.subgroupOf C).IsSubnormal) : (A.subgroupOf B).IsSubnormal := by
  have h := hA.comap (inclusion hBC)
  have e : (A.subgroupOf C).comap (inclusion hBC) = A.subgroupOf B := by
    ext x
    simp only [mem_comap, mem_subgroupOf]
    rfl
  rwa [e] at h

theorem isSubnormal_subgroupOf_of_le_normalizer {A B : Subgroup G} (hAB : A ≤ B)
    (hBN : B ≤ normalizer (A : Set G)) : (A.subgroupOf B).IsSubnormal :=
  ((normal_subgroupOf_iff_le_normalizer hAB).mpr hBN).isSubnormal

end CFSG.Quasithin.C58
