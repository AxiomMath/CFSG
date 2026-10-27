module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.ConfinedInvolution

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Open CFSG.QuasithinUnique
open scoped Pointwise

theorem oddCoreIn_inf_two_eq_bot {G : Type*} [Group G] [Finite G] {Q : Subgroup G}
    (hQ : IsPGroup 2 Q) (H : Subgroup G) : oddCoreIn H ⊓ Q = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hQ.exists_card_eq
  have hcop : Nat.Coprime (Nat.card (oddCoreIn H)) (Nat.card Q) := by
    rw [hn]
    exact Nat.Coprime.pow_right n (Nat.coprime_two_right.mpr (odd_card_oddCoreIn H))
  exact disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hcop)

theorem centric_of_isAGMember {G : Type*} [Group G] [Finite G] {T D : Subgroup G}
    (hT : IsPGroup 2 T) (hD : IsAGMember T D) :
    ∀ t ∈ T, (∀ d ∈ D, t * d = d * t) → t ∈ D := by
  obtain ⟨hDT, hD1, hsyl, hi, hCD, hRC, hRD⟩ := hD
  intro t htT hc
  have htC : t ∈ Subgroup.centralizer (D : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact (hc d hd).symm
  have hRN : oddCoreIn (Subgroup.normalizer (D : Set G)) ≤ Subgroup.normalizer (D : Set G) :=
    oddCoreIn_le _
  have htRD : t ∈ ((oddCoreIn (Subgroup.normalizer (D : Set G)) : Set G) * (D : Set G)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hRN]
    exact hCD htC
  obtain ⟨r, hr, d, hd, hrd⟩ := htRD
  have hrd' : r * d = t := hrd
  have hrT : r ∈ T := by
    have : r = t * d⁻¹ := by
      rw [← hrd', mul_inv_cancel_right]
    rw [this]
    exact T.mul_mem htT (T.inv_mem (hDT hd))
  have hr1 : r = 1 := by
    have hmem : r ∈ oddCoreIn (Subgroup.normalizer (D : Set G)) ⊓ T := ⟨hr, hrT⟩
    rw [oddCoreIn_inf_two_eq_bot hT _] at hmem
    exact hmem
  rw [← hrd', hr1, one_mul]
  exact hd

end CFSG.Quasithin.H13.F431.U42
