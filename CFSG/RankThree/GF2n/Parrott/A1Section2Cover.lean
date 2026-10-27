module

public import CFSG.RankThree.GF2n.Parrott.A1LocalData
public import CFSG.RankThree.GF2n.Parrott.A1ModelFacts

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open
open CFSG.ComponentClassification.CatFactsSmall.PSp43

variable {G : Type} [Group G] [Finite G] {z : G}

theorem exists_conj_mem_tJ_or_utJ_A1
    [hN : ((J z).subgroupOf (H z)).Normal]
    (D : QuotientDataPSp (z := z) hN) {x : G} (hxH : x ∈ H z) (hxJ : x ∉ J z)
    (hx2 : orderOf x = 2) :
    ∃ k ∈ H z, (∃ j ∈ J z, k * x * k⁻¹ = (tHP D : G) * j) ∨
      ∃ j ∈ J z, k * x * k⁻¹ = ((uHP D * tHP D : ↥(H z)) : G) * j := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker : ∀ y : ↥(H z), qHP D y = 1 → (y : G) ∈ J z := fun y hy =>
    Subgroup.mem_subgroupOf.mp (by rw [← ker_qHP D]; exact MonoidHom.mem_ker.mpr hy)
  have hxq2 : orderOf (qHP D ⟨x, hxH⟩) = 2 := by
    apply orderOf_eq_prime
    · have hsq : (⟨x, hxH⟩ : ↥(H z)) ^ 2 = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow, ← hx2]
        exact pow_orderOf_eq_one x)
      rw [← map_pow, hsq, map_one]
    · exact fun h1 => hxJ (hker _ h1)
  have key : ∀ s : ↥(H z), IsConj (qHP D ⟨x, hxH⟩) (qHP D s) →
      ∃ k ∈ H z, ∃ j ∈ J z, k * x * k⁻¹ = (s : G) * j := by
    intro s hs
    obtain ⟨c, hc⟩ := isConj_iff.mp hs
    obtain ⟨k, rfl⟩ := qHP_surjective D c
    have h1 : qHP D (s⁻¹ * (k * ⟨x, hxH⟩ * k⁻¹)) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul, map_inv, hc, inv_mul_cancel]
    refine ⟨k, k.2, _, hker _ h1, ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rcases qp45_involution_classes (qHP D ⟨x, hxH⟩) hxq2 with h1 | h2
  · obtain ⟨k, hk, j, hj, hc⟩ := key (tHP D) (by rw [qHP_tHP]; exact h1)
    exact ⟨k, hk, Or.inl ⟨j, hj, hc⟩⟩
  · obtain ⟨k, hk, j, hj, hc⟩ := key (uHP D * tHP D)
      (by rw [map_mul, qHP_uHP, qHP_tHP]; exact h2)
    exact ⟨k, hk, Or.inr ⟨j, hj, hc⟩⟩

end CFSG.RankThree.GF2n.Parrott
