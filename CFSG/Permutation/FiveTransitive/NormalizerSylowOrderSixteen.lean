module

public import CFSG.Permutation.FiveTransitive.CentralExtensionSylowOrder
public import CFSG.Permutation.FiveTransitive.NormalizerKernelQuotientOdd

public section

namespace CFSG

namespace FiveTransitive.NormalizerSylowOrderSixteen

open MulAction FixedSetNormalizerHom

theorem card_eq_sixteen
    (G X : Type*) [Group G] [Finite G] [Finite X] [MulAction G X]
    (s : Set X) (S : Sylow 2 (fixingSubgroup G s)) (hS : Nat.card S = 2)
    (Q : Subgroup G)
    (hQ : (S : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype = Q)
    (hsix : (fixedPoints Q X).ncard = 6)
    (himage : letI := Fintype.ofFinite (fixedPoints Q X)
      letI := Classical.decEq (fixedPoints Q X)
      (fixedPermHom G X Q).range = alternatingGroup (fixedPoints Q X))
    (P : Sylow 2 (Subgroup.normalizer (Q : Set G))) : Nat.card P = 16 := by
  classical
  let N := Subgroup.normalizer (Q : Set G)
  let U : Subgroup N := Q.subgroupOf N
  let f := fixedPermHom G X Q
  let _ := Fintype.ofFinite (fixedPoints Q X)
  let _ : DecidableEq (fixedPoints Q X) := Classical.decEq _
  have hcard : Nat.card Q = 2 := by
    rw [← hQ, Subgroup.card_map_of_injective (fixingSubgroup G s).subtype_injective]
    exact hS
  have hUcard : Nat.card U = 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Q.le_normalizer).toEquiv]
    exact hcard
  have hU : U ≤ f.ker := by
    intro u hu
    apply (mem_ker_iff G X Q u).mpr
    intro x hx
    exact mem_fixedPoints.mp hx ⟨u.val, hu⟩
  have hodd : Odd (Nat.card (f.ker.map (QuotientGroup.mk' U))) := by
    apply Nat.not_even_iff_odd.mp
    rw [even_iff_two_dvd]
    subst Q
    exact NormalizerKernelQuotientOdd.prime_not_dvd_kernel_quotient G X s S
  have hsize : Fintype.card (fixedPoints Q X) = 6 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    exact hsix
  exact CentralExtensionSylowOrder.card_eq_sixteen f hsize himage U hU hUcard hodd P

end FiveTransitive.NormalizerSylowOrderSixteen

end CFSG
