module

public import CFSG.Permutation.FiveTransitive.A9FourteenNineOrbit

public section

namespace CFSG

namespace FiveTransitive.A9FourteenQuotientSupport
open MulAction

private theorem support_eq_seven
    {F E : Type} [Fintype F] [DecidableEq F] [Fintype E] [DecidableEq E]
    (hF : Nat.card F = 9) (hE : Nat.card E ≤ 14)
    (B : Subgroup (Equiv.Perm E)) (tau : B →* alternatingGroup F)
    (htau : Function.Surjective tau) (b : B) (hb : orderOf b = 7) :
    (b : Equiv.Perm E).support.card = 7 := by
  classical
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨x,hx⟩ := A9FourteenNineOrbit.exists_nine_orbit hF hE B tau htau
  let C := OrbitRestrictionKernel.Complement B x
  let sigma := toPermHom B C
  have hC : Nat.card C ≤ 5 := by
    rw [OrbitRestrictionKernel.card_complement,hx]
    omega
  have hz : sigma b = 1 := by
    by_contra hn
    have hp : sigma b ^ 7 = 1 := by
      rw [← map_pow,show b ^ 7 = 1 by rw [← hb,pow_orderOf_eq_one],map_one]
    have ho : orderOf (sigma b) = 7 := orderOf_eq_prime hp hn
    have hd : 7 ∣ (Nat.card C).factorial := by
      rw [← Nat.card_perm]
      exact ho ▸ orderOf_dvd_natCard (sigma b)
    have hle := (Nat.Prime.dvd_factorial (by decide : Nat.Prime 7)).mp hd
    omega
  have hsub : ((b : Equiv.Perm E).support : Set E) ⊆ orbit B x := by
    intro y hy
    by_contra hn
    have he : (b : Equiv.Perm E) y = y :=
      congrArg (fun f : Equiv.Perm C => (f ⟨y,hn⟩).val) hz
    exact (Equiv.Perm.mem_support.mp hy) he
  have hs := Set.ncard_le_ncard hsub
  rw [Set.ncard_coe_finset,← Nat.card_coe_set_eq,hx] at hs
  have hg : orderOf (b : Equiv.Perm E) = 7 := (Subgroup.orderOf_coe b).trans hb
  have hc : (b : Equiv.Perm E).IsCycle := Equiv.Perm.isCycle_of_prime_order
    (by rw [hg]; decide) (by rw [hg]; omega)
  exact hc.orderOf.symm.trans hg

theorem support_le_seven
    {F E : Type} [Fintype F] [DecidableEq F] [Fintype E] [DecidableEq E]
    (hF : Nat.card F = 9) (hE : Nat.card E ≤ 14)
    (B : Subgroup (Equiv.Perm E)) (tau : B →* alternatingGroup F)
    (htau : Function.Surjective tau) (b : B) (hb : orderOf b = 7) :
    (b : Equiv.Perm E).support.card ≤ 7 := by
  exact (support_eq_seven hF hE B tau htau b hb).le

end FiveTransitive.A9FourteenQuotientSupport

end CFSG
