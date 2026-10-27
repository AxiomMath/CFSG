module

public import CFSG.Permutation.FiveTransitive.CentralExtensionUniqueSquare
public import CFSG.Permutation.FiveTransitive.EvenSixSylowCenter

public section

namespace CFSG

namespace FiveTransitive.CentralExtensionSylowCenter

theorem center_cases
    {G X : Type*} [Group G] [Finite G] [Fintype X] [DecidableEq X]
    (f : G →* Equiv.Perm X) (hX : Fintype.card X = 6)
    (hf : f.range = alternatingGroup X)
    (Q : Subgroup G) [Q.Normal] (hcard : Nat.card Q = 2)
    (hodd : Odd (Nat.card (f.ker.map (QuotientGroup.mk' Q))))
    (q : Q) (hq : q ≠ 1) (P : Sylow 2 G) (a x : P)
    (hfa : orderOf (f a) = 4) (hx : ∀ y : P, x * y = y * x) :
    (x : G) = 1 ∨ (x : G) = (q : G) ∨
      (x : G) = (a : G) ^ 2 ∨ (x : G) = (q : G) * (a : G) ^ 2 := by
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
  have hphi : orderOf (phi a) = 4 := by
    rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
    exact hfa
  have hcentral (y : D) : phi x * y = y * phi x := by
    obtain ⟨z, rfl⟩ := hphisur y
    simpa only [map_mul] using congrArg phi (hx z)
  have hkernel (y : P) (hy : f y = 1) : (y : G) ∈ Q := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp P.isPGroup' y
    apply CentralExtensionUniqueSquare.mem_of_two_element_mem_kernel f Q hodd y k _ hy
    have hp : y ^ (2 ^ k) = 1 := by rw [← hk]; exact pow_orderOf_eq_one y
    exact congrArg Subtype.val hp
  rcases EvenSixSylowCenter.eq_one_or_square X hX D (phi a) (phi x) hphi hcentral with he | he
  · have hxker : f x = 1 := congrArg (fun y : D => ((y : alternatingGroup X) : Equiv.Perm X)) he
    let r : Q := ⟨x, hkernel x hxker⟩
    rcases Research.OddIndexTwoConjugacy.eq_one_or_eq_of_natCard_eq_two hcard q hq r with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (Or.inl (congrArg Subtype.val h))
  · have heq : f x = (f a) ^ 2 :=
      congrArg (fun y : D => ((y : alternatingGroup X) : Equiv.Perm X)) he
    have hy : f ((x * (a ^ 2)⁻¹ : P) : G) = 1 := by
      change f ((x : G) * ((a : G) ^ 2)⁻¹) = 1
      rw [map_mul, map_inv, map_pow, heq, mul_inv_cancel]
    let r : Q := ⟨(x * (a ^ 2)⁻¹ : P), hkernel _ hy⟩
    rcases Research.OddIndexTwoConjugacy.eq_one_or_eq_of_natCard_eq_two hcard q hq r with h | h
    · right; right; left
      have h' : (x : G) * ((a : G) ^ 2)⁻¹ = 1 := congrArg Subtype.val h
      simpa only [one_mul] using (mul_inv_eq_iff_eq_mul).mp h'
    · right; right; right
      have h' : (x : G) * ((a : G) ^ 2)⁻¹ = (q : G) := congrArg Subtype.val h
      exact (mul_inv_eq_iff_eq_mul).mp h'

end FiveTransitive.CentralExtensionSylowCenter

end CFSG
