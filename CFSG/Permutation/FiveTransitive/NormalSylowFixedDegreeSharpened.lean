module

public import CFSG.Permutation.FiveTransitive.NormalOddFourDegree
public import CFSG.Permutation.FiveTransitive.NormalSylowFixedDegree
public import CFSG.Permutation.FiveTransitive.ComplementRestriction
public import Mathlib.Topology.Sheaves.Presheaf

public section

namespace CFSG

namespace FiveTransitive.NormalSylowFixedDegreeSharpened
open MulAction Subgroup GenericSylowFixedAction NormalSylowFixedFive

theorem normalizer_comap_eq_internal
    (G X : Type) [Group G] [MulAction G X]
    (N : Subgroup G) (s : Set X) {p : ℕ} (S : Sylow p (fixingSubgroup N s)) :
    (normalSylowNormalizer G X N s S).comap N.subtype = sylowNormalizer N X s S := by
  have himage : normalSylowImage G X N s S = (sylowImage N X s S).map N.subtype := by
    simp only [normalSylowImage, sylowImage, Subgroup.map_map]
  change (Subgroup.normalizer (normalSylowImage G X N s S)).comap N.subtype = _
  rw [Subgroup.comap_normalizer_eq_of_le_range (by rw [himage]; exact Subgroup.map_le_range _ _)]
  rw [himage, Subgroup.comap_map_eq_self (by simp)]

theorem internal_fixed_invariant
    (G X : Type) [Group G] [MulAction G X]
    (N : Subgroup G) (s : Set X) {p : ℕ} (S : Sylow p (fixingSubgroup N s)) :
    ∀ (g : normalSylowNormalizer G X N s S) (x : X),
      g • x ∈ sylowFixedPoints N X s S ↔ x ∈ sylowFixedPoints N X s S := by
  rw [← NormalSylowFixedDegree.normal_fixedPoints_eq_internal G X N s S]
  intro g x
  constructor
  · intro hx
    have h := smul_mem_fixedPoints_of_normal g⁻¹ hx
    simpa only [inv_smul_smul] using h
  · exact smul_mem_fixedPoints_of_normal g

theorem fixed_degree_cases
    (G X : Type) [Group G] [Finite G] [Fintype X] [MulAction G X]
    (h5 : IsMultiplyPretransitive G X 5)
    (N : Subgroup G) [N.Normal] (hN4 : IsMultiplyPretransitive N X 4)
    (s : Set X) (hs : s.ncard = 4) (S : Sylow 2 (fixingSubgroup N s)) :
    let F := normalSylowFixedPoints G X N s S
    Nat.card F ≤ 7 ∨ Nat.card F = 12 ∨ Nat.card F = 24 := by
  classical
  dsimp only
  rw [NormalSylowFixedDegree.normal_fixedPoints_eq_internal]
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
  have hL4 : IsMultiplyPretransitive L F 4 :=
    FiveTransitive.isMultiplyPretransitive_range_toPermHom A F 4
      (NormalSylowFixedDegree.internal_normalizer_four_transitive N X hN4 s hs S)
  let sF : Set F := {x | (x : X) ∈ s}
  have hbase : s ⊆ (F : Set X) := base_subset_fixedPoints N X s S
  let e : s ≃ sF :=
    { toFun := fun x => ⟨⟨x.val, hbase x.property⟩, x.property⟩
      invFun := fun x => ⟨x.val.val, x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hsF : sF.ncard = 4 := by
    rw [← Nat.card_coe_set_eq, Nat.card_congr e.symm, Nat.card_coe_set_eq, hs]
  have hodd := prime_not_dvd_fixedAction_stabilizer_card N X s S
  have hbound := NormalSylowFixedDegree.fixed_degree_le_twentySix N X hN4 s hs S
  have hout := NormalOddFourDegree.degree_cases F J L hLP
    (by change Nat.card F ≤ 26 at hbound; rw [Nat.card_eq_fintype_card] at hbound; omega)
    hJ5 hL4 sF hsF hodd
  simpa only [Nat.card_eq_fintype_card] using hout

end FiveTransitive.NormalSylowFixedDegreeSharpened

end CFSG
