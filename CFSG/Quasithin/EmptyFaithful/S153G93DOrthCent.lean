module

public import CFSG.Quasithin.EmptyFaithful.S153G93DUtil

public section

namespace CFSG.Quasithin

namespace S153G93D

namespace Orth

open CFSG.Open CFSG.QuasithinUnique

variable {W : Type} [CommGroup W] [Finite W]

theorem eq_of_inner {K S : Subgroup (MulAut W)} {a q : MulAut W} (hW : ∀ w : W, w ^ 2 = 1)
    (hirr : IsIrrOn153 K ⊤) (ha2 : a ^ 2 = 1) (hS : IsSylowTwoOf S K)
    (hcent : ∀ x ∈ S, x * a = a * x) (hq : q ∈ S)
    (hinner : ∀ k ∈ K, a * k * a⁻¹ = q * k * q⁻¹) : a = q := by
  obtain ⟨j, hj⟩ := hS.2.1 ⟨q, hq⟩
  have hqj : q ^ 2 ^ j = 1 := by
    have := congrArg Subtype.val hj
    simpa using this
  have hcomm : Commute q a := hcent q hq
  have hc : (q⁻¹ * a) ^ 2 ^ (j + 1) = 1 := by
    rw [hcomm.inv_left.mul_pow, inv_pow, pow_succ, pow_mul, pow_mul', hqj, ha2]
    simp
  have hk : ∀ k ∈ K, k * (q⁻¹ * a) = (q⁻¹ * a) * k := by
    intro k hk
    have h := hinner k hk
    calc k * (q⁻¹ * a) = q⁻¹ * (q * k * q⁻¹) * a := by group
      _ = q⁻¹ * (a * k * a⁻¹) * a := by rw [h]
      _ = (q⁻¹ * a) * k := by group
  have h1 : q⁻¹ * a = 1 := eq_one_of_commute_irr hW hirr hc hk
  exact (inv_mul_eq_one.mp h1).symm

theorem mem_of_inner {K S : Subgroup (MulAut W)} {a : MulAut W} (h : Ctx2 W K a S)
    (hinner : ∃ q ∈ S, ∀ k ∈ K, a * k * a⁻¹ = q * k * q⁻¹) : a ∈ S := by
  obtain ⟨q, hq, hqk⟩ := hinner
  rw [eq_of_inner h.exp h.irr h.a2 h.syl h.cent hq hqk]
  exact hq

end Orth

end S153G93D

end CFSG.Quasithin
