module

public import CFSG.Permutation.FiveTransitive.NormalSylowFixedDegreeSharpened

public section

namespace CFSG

namespace FiveTransitive.NormalSylowInternalImage
open MulAction Subgroup GenericSylowFixedAction NormalSylowFixedFive NormalSylowFixedDegreeSharpened

theorem exists_five_transitive_normal_overgroup
    (G X : Type) [Group G] [Finite G] [Fintype X] [MulAction G X]
    (h5 : IsMultiplyPretransitive G X 5)
    (N : Subgroup G) [N.Normal] (s : Set X) (hs : s.ncard = 4)
    {p : ℕ} [Fact p.Prime] (S : Sylow p (fixingSubgroup N s)) :
    let F := sylowFixedPoints N X s S
    let L := (MulAction.toPermHom (sylowNormalizer N X s S) F).range
    ∃ J : Subgroup (Equiv.Perm F), L ≤ J ∧ (L.subgroupOf J).Normal ∧
      IsMultiplyPretransitive J F 5 := by
  classical
  dsimp only
  let F := sylowFixedPoints N X s S
  let _ : Fintype F := Fintype.ofFinite F
  let A := sylowNormalizer N X s S
  let K := normalSylowNormalizer G X N s S
  let phi : K →* Equiv.Perm F := ComplementRestriction.restrictHom
    (MulAction.toPermHom K X) F (internal_fixed_invariant G X N s S)
  let psi : A →* Equiv.Perm F := MulAction.toPermHom A F
  let J := phi.range
  let L := psi.range
  let R := N.subgroupOf K
  let _ : R.Normal := inferInstance
  have hcomap := normalizer_comap_eq_internal G X N s S
  change K.comap N.subtype = A at hcomap
  let toK : A →* K :=
    { toFun := fun a => ⟨a.val.val, by
        change a.val ∈ K.comap N.subtype
        rw [hcomap]
        exact a.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hrange : toK.range = R := by
    ext k
    constructor
    · rintro ⟨a, rfl⟩
      exact a.val.property
    · intro hk
      let n : N := ⟨k.val, hk⟩
      have hn : n ∈ A := by
        rw [← hcomap]
        exact k.property
      exact ⟨⟨n, hn⟩, rfl⟩
  have hcomp : phi.comp toK = psi := by
    ext a x
    rfl
  have hLP : L ≤ J := by
    rintro q ⟨a, rfl⟩
    exact ⟨toK a, DFunLike.congr_fun hcomp a⟩
  let M := R.map phi.rangeRestrict
  let _ : M.Normal := (inferInstance : R.Normal).map _ phi.rangeRestrict_surjective
  have hML : M.map J.subtype = L := by
    rw [show M = R.map phi.rangeRestrict from rfl, Subgroup.map_map]
    change R.map phi = psi.range
    rw [← hrange, ← MonoidHom.range_comp, hcomp]
  have hLM : L.subgroupOf J = M := by
    apply Subgroup.map_injective J.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hLP, hML]
  let _ : (L.subgroupOf J).Normal := by rw [hLM]; infer_instance
  have hJ5 : IsMultiplyPretransitive J F 5 := by
    rw [isMultiplyPretransitive_iff]
    intro a b
    have hfix : ∀ c : Fin 5 ↪ F, ∀ r ∈ normalSylowImage G X N s S,
        ∀ i, r • (c i).val = (c i).val := by
      intro c r hr i
      have hx : (c i).val ∈ normalSylowFixedPoints G X N s S := by
        rw [NormalSylowFixedDegree.normal_fixedPoints_eq_internal]
        exact (c i).property
      exact hx (⟨⟨r, Subgroup.le_normalizer hr⟩, hr⟩ : normalSylowInNormalizer G X N s S)
    obtain ⟨g, hg, hgab⟩ := exists_mem_normalizer_maps_fixed_five G X h5 N s hs S
      (fun i => (a i).val) (fun i => (b i).val)
      (fun i j h => a.injective (Subtype.ext h))
      (fun i j h => b.injective (Subtype.ext h)) (hfix a) (hfix b)
    refine ⟨⟨phi ⟨g, hg⟩, ⟨⟨g, hg⟩, rfl⟩⟩, ?_⟩
    ext i
    exact hgab i
  exact ⟨J, hLP, inferInstance, hJ5⟩

end FiveTransitive.NormalSylowInternalImage

end CFSG
