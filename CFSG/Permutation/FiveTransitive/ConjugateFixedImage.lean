module

public import CFSG.Permutation.FiveTransitive.ConjugateFixedNormalizer
public import CFSG.Permutation.FiveTransitive.FixedSetNormalizerHom
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG

namespace FiveTransitive.ConjugateFixedImage

open MulAction FixedSetNormalizerPerm FixedSetNormalizerHom ConjugateFixedNormalizer

private theorem normalizer_conj_forward
    (G : Type*) [Group G] (Q R : Subgroup G) (c : G)
    (hc : Q.map (MulAut.conj c).toMonoidHom = R)
    (a : G) (ha : a ∈ Subgroup.normalizer (Q : Set G)) :
    c * a * c⁻¹ ∈ Subgroup.normalizer (R : Set G) := by
  have hmap := Q.map_normalizer_eq_of_bijective (f := (MulAut.conj c).toMonoidHom)
    (MulAut.conj c).bijective
  rw [hc] at hmap
  rw [← hmap]
  exact Subgroup.mem_map_of_mem (MulAut.conj c).toMonoidHom ha

private theorem permCongr_forward
    (G X : Type*) [Group G] [MulAction G X]
    (Q R : Subgroup G) (c : G) (hc : Q.map (MulAut.conj c).toMonoidHom = R)
    (a : G) (ha : a ∈ Subgroup.normalizer (Q : Set G)) :
    (fixedEquiv G X Q R c hc).permCongr (fixedPerm G X Q a ha) =
      fixedPerm G X R (c * a * c⁻¹) (normalizer_conj_forward G Q R c hc a ha) := by
  apply Equiv.ext
  intro x
  apply Subtype.ext
  change c • (a • (c⁻¹ • x.val)) = (c * a * c⁻¹) • x.val
  simp only [mul_smul]

theorem alternating_image_of_conjugate
    (G X : Type*) [Group G] [Fintype X] [MulAction G X]
    (Q R : Subgroup G) (c : G) (hc : Q.map (MulAut.conj c).toMonoidHom = R)
    (himage : letI := Fintype.ofFinite (fixedPoints Q X)
      letI := Classical.decEq (fixedPoints Q X)
      (fixedPermHom G X Q).range = alternatingGroup (fixedPoints Q X)) :
    letI := Fintype.ofFinite (fixedPoints R X)
    letI := Classical.decEq (fixedPoints R X)
    (fixedPermHom G X R).range = alternatingGroup (fixedPoints R X) := by
  classical
  let _ := Fintype.ofFinite (fixedPoints Q X)
  let _ : DecidableEq (fixedPoints Q X) := Classical.decEq _
  let _ := Fintype.ofFinite (fixedPoints R X)
  let _ : DecidableEq (fixedPoints R X) := Classical.decEq _
  let e := fixedEquiv G X Q R c hc
  apply Subgroup.ext
  intro g
  constructor
  · rintro ⟨b, rfl⟩
    apply Equiv.Perm.mem_alternatingGroup.mpr
    change (fixedPerm G X R (b : G) b.property).sign = 1
    rw [← permCongr_fixedPerm G X Q R c hc b b.property, Equiv.Perm.sign_permCongr]
    apply Equiv.Perm.mem_alternatingGroup.mp
    rw [← himage]
    exact ⟨⟨c⁻¹ * (b : G) * c, normalizer_conj_back G Q R c hc b b.property⟩, rfl⟩
  · intro hg
    let f := e.permCongr.symm g
    have hf : f ∈ alternatingGroup (fixedPoints Q X) := by
      apply Equiv.Perm.mem_alternatingGroup.mpr
      rw [← Equiv.Perm.sign_permCongr e f]
      change (e.permCongr (e.permCongr.symm g)).sign = 1
      rw [e.permCongr.apply_symm_apply]
      exact Equiv.Perm.mem_alternatingGroup.mp hg
    rw [← himage] at hf
    obtain ⟨a, ha⟩ := hf
    let b : Subgroup.normalizer (R : Set G) :=
      ⟨c * (a : G) * c⁻¹, normalizer_conj_forward G Q R c hc a a.property⟩
    refine ⟨b, ?_⟩
    change fixedPerm G X R (c * (a : G) * c⁻¹) (normalizer_conj_forward G Q R c hc a a.property) = g
    rw [← permCongr_forward G X Q R c hc a a.property]
    change e.permCongr ((fixedPermHom G X Q) a) = g
    rw [ha]
    exact e.permCongr.apply_symm_apply g

end FiveTransitive.ConjugateFixedImage

end CFSG
