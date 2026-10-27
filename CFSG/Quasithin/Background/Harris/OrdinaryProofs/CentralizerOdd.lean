module

public import CFSG.Quasithin.Background.Harris.OrdinaryProofs.SchurEnd

public section

namespace CFSG.Quasithin.Background.Harris.OrdinaryProofs

open CFSG.Quasithin.G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

lemma two_eq_zero_module_end : (2 : Module.End (ZMod 2) V) = 0 := by
  calc (2 : Module.End (ZMod 2) V) = algebraMap (ZMod 2) (Module.End (ZMod 2) V) (2 : ZMod 2) :=
        (map_ofNat _ 2).symm
    _ = 0 := by
        rw [show (2 : ZMod 2) = 0 from by decide, map_zero]

lemma eq_one_of_sq_eq_one_mem_centralizer {H : Subgroup (GLV V)} (hH : IsIrr H ⊤)
    {g : GLV V} (hg : g ∈ Subgroup.centralizer (H : Set (GLV V))) (hsq : g * g = 1) :
    g = 1 := by
  have := endCommutant_noZeroDivisors hH
  set f : Module.End (ZMod 2) V := (g : V →ₗ[ZMod 2] V) with hfdef
  have hfmem : f ∈ endCommutant H := by
    rw [endCommutant, Subalgebra.mem_centralizer_iff]
    rintro _ ⟨h, hh, rfl⟩
    have hc : h * g = g * h := (Subgroup.mem_centralizer_iff.mp hg) h hh
    apply LinearMap.ext
    intro v
    have hv := congrArg (fun x : GLV V => (x : V →ₗ[ZMod 2] V) v) hc
    simpa [Module.End.mul_apply, hfdef] using hv
  have hff : f * f = 1 := by
    apply LinearMap.ext
    intro v
    have hv := congrArg (fun x : GLV V => (x : V →ₗ[ZMod 2] V) v) hsq
    simpa [Module.End.mul_apply, hfdef] using hv
  have h2f : f + f = 0 := by rw [← two_mul, two_eq_zero_module_end, zero_mul]
  let a : endCommutant H := ⟨f - 1, Subalgebra.sub_mem _ hfmem (Subalgebra.one_mem _)⟩
  have ha2 : a * a = 0 := by
    apply Subtype.ext
    change (f - 1) * (f - 1) = 0
    calc (f - 1) * (f - 1) = f * f - (f + f) + 1 := by noncomm_ring
      _ = 0 := by rw [hff, h2f, sub_zero, one_add_one_eq_two, two_eq_zero_module_end]
  have ha0 : a = 0 := mul_self_eq_zero.mp ha2
  have hf1 : f = 1 := by
    have := congrArg Subtype.val ha0
    change f - 1 = 0 at this
    exact sub_eq_zero.mp this
  apply LinearEquiv.ext
  intro v
  have := congrArg (fun F : Module.End (ZMod 2) V => F v) hf1
  simpa [hfdef] using this

lemma centralizer_card_odd {H : Subgroup (GLV V)} (hH : IsIrr H ⊤) [Finite V] :
    Odd (Nat.card (Subgroup.centralizer (H : Set (GLV V)))) := by
  classical
  have : Finite (GLV V) :=
    Finite.of_injective (fun e : GLV V => (e : V → V)) (fun a b h => LinearEquiv.ext (fun x => congrFun h x))
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hodd
  rw [Nat.not_odd_iff_even, even_iff_two_dvd] at hodd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.centralizer (H : Set (GLV V))))
    2 hodd
  have hx1 : (x : GLV V) ≠ 1 := by
    intro h
    have hx' : x = 1 := Subtype.ext h
    rw [hx', orderOf_one] at hx
    exact absurd hx (by decide)
  have hsq : (x : GLV V) * (x : GLV V) = 1 := by
    rw [← pow_two, ← Subgroup.coe_pow]
    have h2 : x ^ 2 = 1 := by
      have := pow_orderOf_eq_one x
      rwa [hx] at this
    rw [h2]
    rfl
  exact hx1 (eq_one_of_sq_eq_one_mem_centralizer hH x.2 hsq)

lemma disjoint_of_two_group_odd {G : Type*} [Group G] [Finite G] {P K : Subgroup G}
    (hP : IsPGroup 2 ↥P) (hK : Odd (Nat.card K)) : Disjoint P K := by
  obtain ⟨n, hn⟩ := (isPGroup_iff_card_dvd_pow).mp hP
  have hcop : Nat.Coprime (Nat.card P) (Nat.card K) :=
    Nat.Coprime.coprime_dvd_left hn (Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hK))
  exact Subgroup.disjoint_of_coprime_natCard hcop

end CFSG.Quasithin.Background.Harris.OrdinaryProofs

end
