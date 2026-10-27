module

public import CFSG.Permutation.FiveTransitive.CyclicCentralCommutatorPair

public section

namespace CFSG

namespace FiveTransitive.TwoFourCentralizerCard

theorem eight_le_card
    {G : Type*} [Group G] [Finite G] (C : Subgroup G) (x y : G)
    (hx : orderOf x = 4) (hy : orderOf y = 2) (hyx : y ≠ x ^ 2)
    (hxC : x ∈ C) (hyC : y ∈ C) : 8 ≤ Nat.card C := by
  let H := Subgroup.zpowers x
  let K := Subgroup.zpowers y
  have hH : Nat.card H = 4 := (Nat.card_zpowers x).trans hx
  have hK : Nat.card K = 2 := (Nat.card_zpowers y).trans hy
  have hx2ne : x ^ 2 ≠ 1 := by
    intro h
    have hd := orderOf_dvd_of_pow_eq_one h
    rw [hx] at hd
    norm_num at hd
  have hx4 : x ^ 4 = 1 := hx ▸ pow_orderOf_eq_one x
  have hy2 : y ^ 2 = 1 := hy ▸ pow_orderOf_eq_one y
  have hyne : y ≠ 1 := by intro he; simp [he] at hy
  have hdis : Disjoint H K := by
    apply Subgroup.disjoint_def.mpr
    intro z hzH hzK
    by_contra hz
    let zK : K := ⟨z,hzK⟩
    have hz2 : z ^ 2 = 1 := congrArg Subtype.val (show zK ^ 2 = 1 by
      rw [← hK]; exact pow_card_eq_one' (x := zK))
    have heH : z = x ^ 2 := congrArg Subtype.val
      (CyclicCentralCommutatorPair.unique_square_one
        (⟨z,hzH⟩ : H) ⟨x ^ 2,H.pow_mem (Subgroup.mem_zpowers x) 2⟩
        (Subtype.ext hz2) (Subtype.ext (by change (x ^ 2) ^ 2 = 1; rw [← pow_mul]; exact hx4))
        (fun he => hz (congrArg Subtype.val he))
        (fun he => hx2ne (congrArg Subtype.val he)))
    have heK : z = y := congrArg Subtype.val
      (CyclicCentralCommutatorPair.unique_square_one zK ⟨y,Subgroup.mem_zpowers y⟩
        (Subtype.ext hz2) (Subtype.ext hy2)
        (fun he => hz (congrArg Subtype.val he))
        (fun he => hyne (congrArg Subtype.val he)))
    exact hyx (heK.symm.trans heH)
  have hHC : H ≤ C := Subgroup.zpowers_le.mpr hxC
  have hKC : K ≤ C := Subgroup.zpowers_le.mpr hyC
  let φ : H × K → C := fun p => ⟨p.1.val * p.2.val,C.mul_mem (hHC p.1.property) (hKC p.2.property)⟩
  have hi : Function.Injective φ := by
    intro p q he
    exact Subgroup.mul_injective_of_disjoint hdis (congrArg Subtype.val he)
  have hc := Nat.card_le_card_of_injective φ hi
  simpa only [Nat.card_prod,hH,hK] using hc

end FiveTransitive.TwoFourCentralizerCard

end CFSG
