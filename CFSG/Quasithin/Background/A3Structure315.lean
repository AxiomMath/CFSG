module

import CFSG.Quasithin.Background.A3Structure36AList
public import CFSG.Quasithin.Background.A3Structure315Defs
public import CFSG.Quasithin.Background.A3StructureFacts

public section

namespace CFSG.Quasithin

namespace A315

open CFSG.Open CFSG.Assembly.LowTwoRank

theorem pResidualOf_eq_bot_of_isPGroup {G : Type*} [Group G] {p : ℕ} {B : Subgroup G}
    (hB : IsPGroup p ↥B) : pResidualOf p B = ⊥ := by
  have h : pResidual p ↥B = ⊥ := by
    refine le_bot_iff.1 (pResidual_le (N := ⊥) fun x => ?_)
    obtain ⟨k, hk⟩ := hB x
    exact ⟨k, by rw [hk]; exact Subgroup.one_mem _⟩
  unfold pResidualOf
  rw [h, Subgroup.map_bot]

theorem three_lt_of_residual {G : Type*} [Group G] {B : Subgroup G}
    (hodd : Odd (Nat.card ↥B)) (hres : pResidualOf 3 B ≠ ⊥) {r : ℕ} (hr : r.Prime)
    (hB : IsPGroup r ↥B) : 3 < r := by
  by_contra hlt
  have h2 := hr.two_le
  have hr' : r = 2 ∨ r = 3 := by omega
  rcases hr' with rfl | rfl
  · refine hres (pResidualOf_eq_bot_of_isPGroup fun x => ⟨0, ?_⟩)
    have hx : x = 1 := by
      obtain ⟨k, hk⟩ := hB x
      have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
      have h3 : orderOf x ∣ Nat.card ↥B := orderOf_dvd_natCard x
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
      have hodd' : ¬ Even (orderOf x) := Nat.not_even_iff_odd.2 (Odd.of_dvd_nat hodd h3)
      have hj0 : j = 0 := by
        by_contra hne
        rw [hj] at hodd'
        exact hodd' (Nat.even_pow.2 ⟨even_two, hne⟩)
      rw [hj0, pow_zero] at hj
      exact orderOf_eq_one_iff.1 hj
    simp [hx]
  · exact hres (pResidualOf_eq_bot_of_isPGroup hB)

theorem a23List_of_hyp (hF : A23SQTKListFact) {G : Type} [Group G] {L T B : Subgroup G}
    (h : A315Hyp L T B) : A23List ↥L := by
  have : Finite G := h.sqtk.finite
  have hS : SQTKGroup G := ⟨h.sqtk.sqt, h.sqtk.kgroup⟩
  have := h.simple
  have hsimple : IsSimpleGroup (↥L ⧸ (⊥ : Subgroup ↥L)) :=
    (QuotientGroup.quotientBot (G := ↥L)).isSimpleGroup
  have hnon : ∃ a b : ↥L ⧸ (⊥ : Subgroup ↥L), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := h.nonabelian
    let e : ↥L ≃* (↥L ⧸ (⊥ : Subgroup ↥L)) := (QuotientGroup.quotientBot (G := ↥L)).symm
    refine ⟨e a, e b, fun hc => hab (e.injective ?_)⟩
    rw [map_mul, map_mul]
    exact hc
  exact CFSG.Quasithin.A36A.a23List_of_mulEquiv (QuotientGroup.quotientBot (G := ↥L)).symm
    (hF G hS L ⊥ hsimple hnon)

end A315

end CFSG.Quasithin
