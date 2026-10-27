module

public import CFSG.Permutation.FiveTransitive.Degree67TwoKernelNumeric
public import CFSG.Permutation.FiveTransitive.Degree67TwoKernelFirstMoment

public section

namespace CFSG

namespace FiveTransitive.Degree67TwoKernelMoments
open MulAction
open scoped BigOperators

private theorem card_dvd_sum_fixed
    {G Y : Type*} [Group G] [Fintype G] [Finite Y] [MulAction G Y] :
    Nat.card G ∣ ∑ g : G, Nat.card (fixedBy Y g) := by
  classical
  let _ : Fintype Y := Fintype.ofFinite _
  have he := sum_card_fixedBy_eq_card_orbits_mul_card_group G Y
  simp only [← Nat.card_eq_fintype_card] at he
  exact ⟨_,by rw [he,Nat.mul_comm]⟩

private theorem card_dvd_sum_fixed_sq
    {G X : Type*} [Group G] [Fintype G] [Finite X] [MulAction G X] :
    Nat.card G ∣ ∑ g : G, (Nat.card (fixedBy X g))^2 := by
  have he (g : G) : Nat.card (fixedBy (X × X) g) = (Nat.card (fixedBy X g))^2 := by
    let e : fixedBy (X × X) g ≃ fixedBy X g × fixedBy X g :=
      { toFun := fun x => (⟨x.val.1,congrArg Prod.fst x.property⟩,
          ⟨x.val.2,congrArg Prod.snd x.property⟩)
        invFun := fun x => ⟨(x.1.val,x.2.val),Prod.ext x.1.property x.2.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Nat.card_congr e,Nat.card_prod,pow_two]
  simpa only [he] using (card_dvd_sum_fixed (G := G) (Y := X × X))

theorem card_ne_thirty_two
    {G X : Type*} [Group G] [Finite G] [Fintype X] [MulAction G X]
    (hX : Fintype.card X = 67)
    (s : Finset X) (hs : s.card = 23) (hfixed : ∀ g : G, ∀ x ∈ s, g • x = x)
    (horbit : ∀ x : X, Nat.card (orbit G x) ≤ 4)
    (hbound : ∀ g : G, g ≠ 1 → Nat.card (fixedBy X g) ≤ 33) : Nat.card G ≠ 32 := by
  classical
  let _ : Fintype G := Fintype.ofFinite _
  intro hG
  obtain ⟨hlow,hupper⟩ := Degree67TwoKernelFirstMoment.sum_bounds hX s hs hfixed horbit hbound
  rw [hG] at hlow hupper
  have hdiv := card_dvd_sum_fixed (G := G) (Y := X)
  rw [hG] at hdiv
  have hsum : (∑ g : G, Nat.card (fixedBy X g)) = 1088 := by
    obtain ⟨k,hk⟩ := hdiv
    omega
  have hone : Nat.card (fixedBy X (1 : G)) = 67 := by
    rw [fixedBy_one_eq_univ,Nat.card_coe_set_eq,Set.ncard_univ,Nat.card_eq_fintype_card,hX]
  let T := (Finset.univ : Finset G).erase 1
  have hT : T.card = 31 := by
    simp only [T,Finset.card_erase_of_mem (Finset.mem_univ (1 : G)),Finset.card_univ,
      ← Nat.card_eq_fintype_card,hG]
  have hsumT : (∑ g ∈ T, Nat.card (fixedBy X g)) = 1021 := by
    have he := Finset.sum_erase_add (Finset.univ : Finset G)
      (fun g => Nat.card (fixedBy X g)) (Finset.mem_univ (1 : G))
    rw [hone,hsum] at he
    change (∑ g ∈ T, Nat.card (fixedBy X g)) + 67 = 1088 at he
    omega
  have hdivT : 32 ∣ 4489 + ∑ g ∈ T, (Nat.card (fixedBy X g))^2 := by
    have hd := card_dvd_sum_fixed_sq (G := G) (X := X)
    rw [hG,← Finset.sum_erase_add _ _ (Finset.mem_univ (1 : G)),hone] at hd
    simpa only [T,Nat.add_comm,show (67 : ℕ)^2 = 4489 by norm_num] using hd
  exact Degree67TwoKernelNumeric.excluded T (fun g => Nat.card (fixedBy X g)) hT
    (fun g hg => hbound g (Finset.mem_erase.mp hg).1) hsumT hdivT

end FiveTransitive.Degree67TwoKernelMoments

end CFSG
