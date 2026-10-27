module

public import CFSG.Quasithin.EmptyFaithful.S153E58N
public import CFSG.Quasithin.EmptyFaithful.S153E61BA

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits
open scoped commutatorElement

namespace S153E61B

open S153E58

section Conj

variable {W : Type} [CommGroup W] [Finite W] {H K : Subgroup (MulAut W)} {W₁ W₂ : Subgroup W}
  {bil : W → W → ZMod 2}

theorem invol_conj_oTwoUpper (hS : Setup58 H K W₁ W₂ bil) {π : ↥(StatedSL 3 (ZMod 2)) →* ↥K}
    (hπ : (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia K W₁ ⊥ π) (hperf : ⁅K, K⁆ = K)
    {p q : MulAut W} (hp : p ∈ oTwoUpper H) (hp1 : p ≠ 1) (hp2 : p * p = 1)
    (hq : q ∈ oTwoUpper H) (hq1 : q ≠ 1) (hq2 : q * q = 1) :
    ∃ r ∈ oTwoUpper H, r * p * r⁻¹ = q := by
  have hK : oTwoUpper H = K := hS.oTwoUpper_eq hπ hperf
  rw [hK] at hp hq ⊢
  have hinj := hS.pi_injective hπ
  obtain ⟨A, hA⟩ : ∃ A : ↥(StatedSL 3 (ZMod 2)), π A = ⟨p, hp⟩ := hπ.1 ⟨p, hp⟩
  obtain ⟨B, hB⟩ : ∃ B : ↥(StatedSL 3 (ZMod 2)), π B = ⟨q, hq⟩ := hπ.1 ⟨q, hq⟩
  have hA1 : A ≠ 1 := fun h => hp1 (congrArg Subtype.val (by rw [← hA, h, map_one] : (⟨p, hp⟩ : ↥K) = 1))
  have hB1 : B ≠ 1 := fun h => hq1 (congrArg Subtype.val (by rw [← hB, h, map_one] : (⟨q, hq⟩ : ↥K) = 1))
  have hA2 : A * A = 1 := hinj (by rw [map_mul, hA, map_one]; exact Subtype.ext hp2)
  have hB2 : B * B = 1 := hinj (by rw [map_mul, hB, map_one]; exact Subtype.ext hq2)
  obtain ⟨C, hC⟩ := statedSL_invol_conj A B hA1 hA2 hB1 hB2
  refine ⟨((π C : ↥K) : MulAut W), (π C).2, ?_⟩
  have h : π (C * A * C⁻¹) = π B := by rw [hC]
  rw [map_mul, map_mul, map_inv, hA, hB] at h
  exact congrArg Subtype.val h

end Conj

end S153E61B

end CFSG.Quasithin
