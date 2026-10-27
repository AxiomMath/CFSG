module

public import CFSG.Permutation.FiveTransitive.CentralExtensionUniqueSquare

public section

namespace CFSG

namespace FiveTransitive.CentralExtensionSylowOrder

theorem card_eq_sixteen
    {G X : Type*} [Group G] [Finite G] [Fintype X] [DecidableEq X]
    (f : G →* Equiv.Perm X) (hX : Fintype.card X = 6)
    (hf : f.range = alternatingGroup X)
    (Q : Subgroup G) [Q.Normal] (hQ : Q ≤ f.ker) (hcard : Nat.card Q = 2)
    (hodd : Odd (Nat.card (f.ker.map (QuotientGroup.mk' Q))))
    (P : Sylow 2 G) : Nat.card P = 16 := by
  classical
  let fA : G →* alternatingGroup X := f.codRestrict _ (by
    intro g
    rw [← hf]
    exact ⟨g, rfl⟩)
  have hfA : Function.Surjective fA := by
    intro y
    have hm : y.val ∈ f.range := by rw [hf]; exact y.property
    obtain ⟨g, hg⟩ := hm
    exact ⟨g, Subtype.ext hg⟩
  let D : Sylow 2 (alternatingGroup X) := Sylow.mapSurjective hfA P
  have hD : (D : Subgroup (alternatingGroup X)) = (P : Subgroup G).map fA :=
    Sylow.coe_mapSurjective hfA P
  have him (y : P) : fA y ∈ D := by
    change fA y ∈ (D : Subgroup (alternatingGroup X))
    rw [hD]
    exact Subgroup.mem_map_of_mem fA y.property
  let phi : P →* D :=
    { toFun := fun y => ⟨fA y, him y⟩
      map_one' := Subtype.ext (map_one fA)
      map_mul' := fun y z => Subtype.ext (map_mul fA (y : G) (z : G)) }
  have hphisur : Function.Surjective phi := by
    intro y
    have hy : (y : alternatingGroup X) ∈ (P : Subgroup G).map fA := hD ▸ y.property
    obtain ⟨g, hg, heq⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨g, hg⟩, Subtype.ext heq⟩
  have hkernel (y : P) (hy : phi y = 1) : (y : G) ∈ Q := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp P.isPGroup' y
    apply CentralExtensionUniqueSquare.mem_of_two_element_mem_kernel f Q hodd y k
    · have hp : y ^ (2 ^ k) = 1 := by rw [← hk]; exact pow_orderOf_eq_one y
      exact congrArg Subtype.val hp
    · exact congrArg (fun d : D => ((d : alternatingGroup X) : Equiv.Perm X)) hy
  have hQp : IsPGroup 2 Q := IsPGroup.of_card (n := 1) (by simpa using hcard)
  have hQP : Q ≤ (P : Subgroup G) := hQp.le_sylow_of_normal P
  let e : phi.ker ≃ Q :=
    { toFun := fun y => ⟨y.val.val, hkernel y.val y.property⟩
      invFun := fun q => ⟨⟨q.val, hQP q.property⟩, by
        apply Subtype.ext
        apply Subtype.ext
        exact hQ q.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hkcard : Nat.card phi.ker = 2 := (Nat.card_congr e).trans hcard
  have hdcard : Nat.card D = 8 := by
    obtain ⟨d⟩ := EvenSixSylowDihedral.nonempty_equiv_dihedral X hX D
    rw [Nat.card_congr d.toEquiv, Nat.card_eq_fintype_card, DihedralGroup.card]
  have hi : phi.ker.index = 8 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hphisur, Subgroup.card_top]
    exact hdcard
  have hc := phi.ker.card_mul_index
  rw [hkcard, hi] at hc
  exact hc.symm

end FiveTransitive.CentralExtensionSylowOrder

end CFSG
