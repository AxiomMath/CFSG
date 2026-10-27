module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.ThirdParty.BrauerInduction.Background.Group.PDecomposition

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Subgroup

variable {G : Type} [Group G]

theorem le_of_isPGroup_le_normalizer_of_isSylowOf {p : ℕ} [Fact p.Prime] [Finite G]
    {A B L : Subgroup G}
    (hA : CFSG.ABGLocalTools.IsSylowOf p A L)
    (hB : IsPGroup p B) (hBL : B ≤ L)
    (hBN : B ≤ Subgroup.normalizer (A : Set G)) : B ≤ A := by
  have hsup : IsPGroup p ↥(A ⊔ B) := hA.isPGroup.to_sup_of_normal_left' hB hBN
  have heq : A ⊔ B = A := hA.eq_of_le le_sup_left (sup_le hA.le hBL) hsup
  intro b hb
  rw [← heq]
  exact Subgroup.mem_sup_right hb

theorem mem_centralizer_of_isPRegular_of_pow {p : ℕ} [Fact p.Prime]
    {A : Subgroup G} {t : G} (ht : IsPRegular p t) {k : ℕ}
    (hk : t ^ (p ^ k) ∈ Subgroup.centralizer (A : Set G)) :
    t ∈ Subgroup.centralizer (A : Set G) := by
  have hmem : t ∈ Subgroup.zpowers (t ^ (p ^ k)) :=
    mem_zpowers_pow_iff.mpr (Nat.Coprime.symm (ht.pow_right k))
  exact Subgroup.zpowers_le.mpr hk hmem

theorem mem_centralizer_of_isSylowOf_of_pow_mem_centralizer [Finite G]
    {L A : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hA : CFSG.ABGLocalTools.IsSylowOf p A L)
    (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    {x : G} (hxL : x ∈ L) (hxA : x ∈ Subgroup.normalizer (A : Set G))
    {k : ℕ} (hk : x ^ (p ^ k) ∈ Subgroup.centralizer (A : Set G)) :
    x ∈ Subgroup.centralizer (A : Set G) := by
  classical
  let s := Group.pSingular p x
  let t := Group.pRegular p x
  have hfin : IsOfFinOrder x := isOfFinOrder_of_finite x
  have hdecomp : t * s = x := Group.pDecomp' p hfin
  have hsing : IsPSingular p s := Group.isPSingular_pSingular p x
  have hreg : IsPRegular p t := Group.isPRegular_pRegular p hfin
  have hs_mem : s ∈ Subgroup.zpowers x := by
    change Group.pSingular p x ∈ Subgroup.zpowers x
    unfold Group.pSingular
    exact Subgroup.zpow_mem_zpowers x _
  have ht_mem : t ∈ Subgroup.zpowers x := by
    change Group.pRegular p x ∈ Subgroup.zpowers x
    unfold Group.pRegular
    exact Subgroup.zpow_mem_zpowers x _
  have hsL : s ∈ L := Subgroup.zpowers_le.mpr hxL hs_mem
  have hsN : s ∈ Subgroup.normalizer (A : Set G) :=
    Subgroup.zpowers_le.mpr hxA hs_mem
  have hsing_grp : IsPGroup p (Subgroup.zpowers s) :=
    (IsPSingular.iff_zpowers_isPGroup p s).mp hsing
  have hsA : s ∈ A :=
    le_of_isPGroup_le_normalizer_of_isSylowOf hA hsing_grp
      (Subgroup.zpowers_le.mpr hsL) (Subgroup.zpowers_le.mpr hsN)
      (Subgroup.mem_zpowers s)
  have hs_cent : s ∈ Subgroup.centralizer (A : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (hAab s hsA a ha).symm
  have ht_pow_cent : t ^ (p ^ k) ∈ Subgroup.centralizer (A : Set G) := by
    obtain ⟨e, he⟩ := Subgroup.mem_zpowers_iff.mp ht_mem
    rw [← he, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
    exact Subgroup.zpow_mem _ hk e
  have ht_cent : t ∈ Subgroup.centralizer (A : Set G) :=
    mem_centralizer_of_isPRegular_of_pow hreg ht_pow_cent
  rw [← hdecomp]
  exact Subgroup.mul_mem (Subgroup.centralizer (A : Set G)) ht_cent hs_cent

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
