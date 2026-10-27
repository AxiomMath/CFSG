module

public import CFSG.Permutation.FiveTransitive.CompatiblePreimageSylow
public import CFSG.Permutation.FiveTransitive.FixedNormalizerCyclicPreimageSylow

public section

namespace CFSG

namespace FiveTransitive.FixedNormalizerCompatibleSylow

open MulAction FixedNormalizerAction

variable {G X : Type*} [Group G] [MulAction G X] (Q : Subgroup G)

theorem exists_kernel_sylow {p : ℕ}
    (S : Sylow p (fixingSubgroup G (fixedPoints Q X)))
    (hS : (S : Subgroup (fixingSubgroup G (fixedPoints Q X))).map
      (fixingSubgroup G (fixedPoints Q X)).subtype = Q) :
    ∃ T : Sylow p (toPermHom (Normalizer Q) (Fixed (X := X) Q)).ker,
      (T : Subgroup (toPermHom (Normalizer Q) (Fixed (X := X) Q)).ker).map
        (toPermHom (Normalizer Q) (Fixed (X := X) Q)).ker.subtype = Inside Q := by
  let f := toPermHom (Normalizer Q) (Fixed (X := X) Q)
  have hQp : IsPGroup p Q := by rw [← hS]; exact S.isPGroup'.map _
  have hIp : IsPGroup p (Inside Q) := hQp.comap_subtype
  have hIK : Inside Q ≤ f.ker := FixedNormalizerCyclicPreimageSylow.inside_le_kernel Q
  have hIKp : IsPGroup p ((Inside Q).subgroupOf f.ker) := hIp.comap_subtype
  obtain ⟨T, hIT⟩ := hIKp.exists_le_sylow
  let B := (T : Subgroup f.ker).map f.ker.subtype
  have hIB : Inside Q ≤ B := by
    intro q hq
    exact ⟨⟨q, hIK hq⟩, hIT hq, rfl⟩
  have hBK : B ≤ f.ker := by
    rintro b ⟨t, ht, rfl⟩
    exact t.property
  have hBI : B ≤ Inside Q := FixedNormalizerCyclicPreimageSylow.kernel_pgroup_le_inside
    Q S hS B hBK (T.isPGroup'.map f.ker.subtype)
  exact ⟨T, le_antisymm hBI hIB⟩

theorem exists_with_element [Finite G] [Finite X]
    (S : Sylow 2 (fixingSubgroup G (fixedPoints Q X)))
    (hS : (S : Subgroup (fixingSubgroup G (fixedPoints Q X))).map
      (fixingSubgroup G (fixedPoints Q X)).subtype = Q)
    (himage : Image (X := X) Q = ⊤)
    (V : Subgroup (Equiv.Perm (Fixed (X := X) Q))) (hV : IsPGroup 2 V)
    (A : Subgroup G) (hA : IsPGroup 2 A) (hQA : Q ≤ A)
    (x : Normalizer Q) (hxA : (x : G) ∈ A)
    (hxV : toPermHom (Normalizer Q) (Fixed (X := X) Q) x ∈ V) :
    ∃ P : Sylow 2 (V.comap (toPermHom (Normalizer Q) (Fixed (X := X) Q))),
      let f := toPermHom (Normalizer Q) (Fixed (X := X) Q)
      let B := SylowPreimageNormalizer.ambient f V P
      IsPGroup 2 B ∧ Inside Q ≤ B ∧ x ∈ B ∧ B.map f = V ∧ B ⊓ f.ker = Inside Q ∧
      (f.comp B.subtype).ker = (Inside Q).subgroupOf B ∧
      (Subgroup.normalizer (B : Set (Normalizer Q))).map f =
        Subgroup.normalizer (V : Set (Equiv.Perm (Fixed (X := X) Q))) := by
  let f := toPermHom (Normalizer Q) (Fixed (X := X) Q)
  obtain ⟨P, hIP, hxP, hm, hk, hkr, hn⟩ := CompatiblePreimageSylow.exists_with_element
    f (MonoidHom.range_eq_top.mp himage) (Inside Q)
    (FixedNormalizerCyclicPreimageSylow.inside_le_kernel Q)
    (FixedNormalizerCyclicPreimageSylow.kernel_pgroup_le_inside Q S hS)
    V hV (A.subgroupOf (Normalizer Q)) hA.comap_subtype (fun _ hq => hQA hq) x hxA hxV
  exact ⟨P, P.isPGroup'.map (V.comap f).subtype, hIP, hxP, hm, hk, hkr, hn⟩

theorem exists_preimage [Finite G] [Finite X]
    (S : Sylow 2 (fixingSubgroup G (fixedPoints Q X)))
    (hS : (S : Subgroup (fixingSubgroup G (fixedPoints Q X))).map
      (fixingSubgroup G (fixedPoints Q X)).subtype = Q)
    (himage : Image (X := X) Q = ⊤)
    (V : Subgroup (Equiv.Perm (Fixed (X := X) Q))) (hV : IsPGroup 2 V) :
    ∃ P : Sylow 2 (V.comap (toPermHom (Normalizer Q) (Fixed (X := X) Q))),
      let f := toPermHom (Normalizer Q) (Fixed (X := X) Q)
      let B := SylowPreimageNormalizer.ambient f V P
      IsPGroup 2 B ∧ Inside Q ≤ B ∧ B.map f = V ∧ B ⊓ f.ker = Inside Q ∧
      (f.comp B.subtype).ker = (Inside Q).subgroupOf B ∧
      (Subgroup.normalizer (B : Set (Normalizer Q))).map f =
        Subgroup.normalizer (V : Set (Equiv.Perm (Fixed (X := X) Q))) := by
  have hQp : IsPGroup 2 Q := by rw [← hS]; exact S.isPGroup'.map _
  obtain ⟨P, hp, hIP, _, hm, hk, hkr, hn⟩ := exists_with_element Q S hS himage V hV
    Q hQp le_rfl 1 Q.one_mem (by
      change toPermHom (Normalizer Q) (Fixed (X := X) Q) 1 ∈ V
      rw [map_one]
      exact V.one_mem)
  exact ⟨P, hp, hIP, hm, hk, hkr, hn⟩

end FiveTransitive.FixedNormalizerCompatibleSylow

end CFSG
