module

public import CFSG.Permutation.FiveTransitive.OddQuotientEvenSixFusion
public import CFSG.Permutation.FiveTransitive.NormalizerKernelQuotientOdd

public section

namespace CFSG

namespace FiveTransitive.NormalizerInvolutionModuloSylow

open MulAction FixedSetNormalizerHom

theorem exists_conjugator
    (G X : Type*) [Group G] [Finite G] [Finite X] [MulAction G X]
    (s : Set X) (S : Sylow 2 (fixingSubgroup G s))
    (Q : Subgroup G)
    (hQ : (S : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype = Q)
    (hsix : (fixedPoints Q X).ncard = 6)
    (himage : letI := Fintype.ofFinite (fixedPoints Q X)
      letI := Classical.decEq (fixedPoints Q X)
      (fixedPermHom G X Q).range = alternatingGroup (fixedPoints Q X))
    (a b : G) (haN : a ∈ Subgroup.normalizer (Q : Set G))
    (hbN : b ∈ Subgroup.normalizer (Q : Set G))
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
    (hfa : fixedPermHom G X Q ⟨a, haN⟩ ≠ 1)
    (hfb : fixedPermHom G X Q ⟨b, hbN⟩ ≠ 1) :
    ∃ c : Subgroup.normalizer (Q : Set G),
      ((c : G) * a * (c : G)⁻¹) * b⁻¹ ∈ Q := by
  classical
  let N := Subgroup.normalizer (Q : Set G)
  let U : Subgroup N := Q.subgroupOf N
  let f := fixedPermHom G X Q
  let _ := Fintype.ofFinite (fixedPoints Q X)
  let _ : DecidableEq (fixedPoints Q X) := Classical.decEq _
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
  obtain ⟨c, hc⟩ := OddQuotientEvenSixFusion.exists_conjugator_mod_subgroup N (fixedPoints Q X)
    f hsize himage U hU hodd ⟨a, haN⟩ ⟨b, hbN⟩ (Subtype.ext ha) (Subtype.ext hb) hfa hfb
  exact ⟨c, hc⟩

end FiveTransitive.NormalizerInvolutionModuloSylow

end CFSG
