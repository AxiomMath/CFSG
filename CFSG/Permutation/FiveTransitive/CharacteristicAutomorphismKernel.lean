module

public import CFSG.Permutation.FiveTransitive.CharacteristicAutomorphism
public import CFSG.Permutation.FiveTransitive.CoprimeAutomorphismDisplacement
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG

namespace FiveTransitive.CharacteristicAutomorphismKernel

open CharacteristicAutomorphism

theorem prime_not_dvd
    {G : Type*} [Group G] [Finite G] (N : Subgroup G) [N.Characteristic]
    (p : ℕ) (hp : p.Prime) (hcop : p.Coprime (Nat.card N)) :
    ¬ p ∣ Nat.card ↥((restrict N).ker ⊓ (quotient N).ker) := by
  classical
  let _ : Fact p.Prime := ⟨hp⟩
  let K := (restrict N).ker ⊓ (quotient N).ker
  intro hd
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := K) p hd
  have hak : (a.val : MulAut G) ^ p = 1 := by
    have ho : orderOf (a.val : MulAut G) = p := by rw [Subgroup.orderOf_coe,ha]
    rw [← ho]
    exact pow_orderOf_eq_one _
  have hf : ∀ z ∈ N, a.val z = z := by
    intro z hz
    have he : restrict N a.val = 1 := a.property.1
    have hh := congrArg (fun f : MulAut N => ((f ⟨z,hz⟩ : N) : G)) he
    exact hh
  have hq : ∀ x : G, (QuotientGroup.mk' N) (a.val x) = (QuotientGroup.mk' N) x := by
    intro x
    have he : quotient N a.val = 1 := a.property.2
    have hh := congrArg (fun f : MulAut (G ⧸ N) => f ((QuotientGroup.mk' N) x)) he
    simpa only [quotient_apply_mk,MulAut.one_apply] using hh
  have he := CoprimeAutomorphismDisplacement.eq_one_of_quotient N a.val p hak hcop hf hq
  have ha1 : a = 1 := Subtype.ext he
  rw [ha1,orderOf_one] at ha
  exact hp.ne_one ha.symm

end FiveTransitive.CharacteristicAutomorphismKernel

end CFSG
