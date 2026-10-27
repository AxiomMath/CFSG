module

public import CFSG.Permutation.FiveTransitive.FixedSetNormalizerPerm
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Data.Set.Card
public import Mathlib.Algebra.Group.Subgroup.Basic

public section

namespace CFSG

namespace FiveTransitive.ConjugateFixedNormalizer

open MulAction FixedSetNormalizerPerm

theorem fixed_mem_iff
    (G X : Type*) [Group G] [MulAction G X]
    (Q R : Subgroup G) (c : G) (hc : Q.map (MulAut.conj c).toMonoidHom = R)
    (x : X) : x ∈ fixedPoints Q X ↔ c • x ∈ fixedPoints R X := by
  constructor
  · intro hx
    rw [mem_fixedPoints]
    intro q
    have hq : (q : G) ∈ Q.map (MulAut.conj c).toMonoidHom := hc.symm ▸ q.property
    obtain ⟨r, hr, hqr⟩ := Subgroup.mem_map.mp hq
    have hrx : r • x = x := mem_fixedPoints.mp hx ⟨r, hr⟩
    change (q : G) • (c • x) = c • x
    rw [← hqr]
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply,
      mul_smul, inv_smul_smul, hrx]
  · intro hx
    rw [mem_fixedPoints]
    intro q
    have hq : c * (q : G) * c⁻¹ ∈ R := by
      rw [← hc]
      exact Subgroup.mem_map_of_mem (MulAut.conj c).toMonoidHom q.property
    have h := mem_fixedPoints.mp hx ⟨c * (q : G) * c⁻¹, hq⟩
    change (c * (q : G) * c⁻¹) • (c • x) = c • x at h
    change (q : G) • x = x
    simpa only [mul_smul, inv_smul_smul, smul_left_cancel_iff] using h

@[expose] def fixedEquiv
    (G X : Type*) [Group G] [MulAction G X]
    (Q R : Subgroup G) (c : G) (hc : Q.map (MulAut.conj c).toMonoidHom = R) :
    fixedPoints Q X ≃ fixedPoints R X :=
  Equiv.subtypeEquiv (MulAction.toPerm c) (fixed_mem_iff G X Q R c hc)

theorem normalizer_conj_back
    (G : Type*) [Group G] (Q R : Subgroup G) (c : G)
    (hc : Q.map (MulAut.conj c).toMonoidHom = R)
    (b : G) (hb : b ∈ Subgroup.normalizer (R : Set G)) :
    c⁻¹ * b * c ∈ Subgroup.normalizer (Q : Set G) := by
  have hmap := Q.map_normalizer_eq_of_bijective (f := (MulAut.conj c).toMonoidHom)
    (MulAut.conj c).bijective
  rw [hc] at hmap
  have hmem : b ∈ (Subgroup.normalizer (Q : Set G)).map (MulAut.conj c).toMonoidHom :=
    hmap.symm ▸ hb
  exact Subgroup.mem_map_equiv.mp hmem

theorem permCongr_fixedPerm
    (G X : Type*) [Group G] [MulAction G X]
    (Q R : Subgroup G) (c : G) (hc : Q.map (MulAut.conj c).toMonoidHom = R)
    (b : G) (hb : b ∈ Subgroup.normalizer (R : Set G)) :
    (fixedEquiv G X Q R c hc).permCongr
      (fixedPerm G X Q (c⁻¹ * b * c) (normalizer_conj_back G Q R c hc b hb)) =
      fixedPerm G X R b hb := by
  apply Equiv.ext
  intro x
  apply Subtype.ext
  change c • ((c⁻¹ * b * c) • (c⁻¹ • x.val)) = b • x.val
  simp only [mul_smul, smul_inv_smul]

theorem six_even_of_conjugate
    (G X : Type*) [Group G] [Fintype X] [MulAction G X]
    (Q R : Subgroup G) (c : G) (hc : Q.map (MulAut.conj c).toMonoidHom = R)
    (hcard : (fixedPoints Q X).ncard = 6)
    (heven : ∀ (a : G) (ha : a ∈ Subgroup.normalizer (Q : Set G)),
      letI := Fintype.ofFinite (fixedPoints Q X)
      letI := Classical.decEq (fixedPoints Q X)
      (fixedPerm G X Q a ha).sign = 1) :
    (fixedPoints R X).ncard = 6 ∧
    ∀ (b : G) (hb : b ∈ Subgroup.normalizer (R : Set G)),
      letI := Fintype.ofFinite (fixedPoints R X)
      letI := Classical.decEq (fixedPoints R X)
      (fixedPerm G X R b hb).sign = 1 := by
  refine ⟨?_, ?_⟩
  · rw [← Nat.card_coe_set_eq, ← hcard, ← Nat.card_coe_set_eq]
    exact (Nat.card_congr (fixedEquiv G X Q R c hc)).symm
  · intro b hb
    let _ := Fintype.ofFinite (fixedPoints Q X)
    let _ : DecidableEq (fixedPoints Q X) := Classical.decEq _
    let _ := Fintype.ofFinite (fixedPoints R X)
    let _ : DecidableEq (fixedPoints R X) := Classical.decEq _
    rw [← permCongr_fixedPerm G X Q R c hc b hb, Equiv.Perm.sign_permCongr]
    exact heven (c⁻¹ * b * c) (normalizer_conj_back G Q R c hc b hb)

end FiveTransitive.ConjugateFixedNormalizer

end CFSG
