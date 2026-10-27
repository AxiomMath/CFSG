module

public import CFSG.Quasithin.Vol2.Ch10SecV1G
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2

public section

namespace CFSG.Quasithin.Vol2.Ch10

open CFSG.Quasithin Vol2.Ch10.V1C

theorem as_B_4_8_four_holds : ASInputs.AS_B_4_8_four := by
  rintro V _ _ hV G - hind ⟨W₁, W₂, -, hW₁F, hUW, hnat⟩
  obtain ⟨D⟩ := hnat.toL3Coord
  have hU8 := card_commV D hUW
  have hUU : commV G ≤ commSub (commV G) G := (commSub_commV D).ge
  have hUc : ∀ g ∈ G, ∀ v, g v * v⁻¹ ∈ commV G := fun g hg v =>
    Subgroup.subset_closure ⟨g, hg, v, rfl⟩
  have hC₀F : commV G ⊓ W₁ ≤ fixV G := inf_le_right.trans hW₁F
  have hUFC : commV G ⊓ fixV G ≤ commV G ⊓ W₁ := by
    rintro u ⟨hu, huF⟩
    refine ⟨hu, mem_of_forall D (hUW hu) fun g hg => ?_⟩
    rw [huF g hg, mul_inv_cancel]
    exact W₁.one_mem
  have h2 := card_eq_two_pow hV (commV G ⊓ W₁)
  rcases (by omega : rk ↥(commV G ⊓ W₁) = 0 ∨ rk ↥(commV G ⊓ W₁) = 1 ∨
      2 ≤ rk ↥(commV G ⊓ W₁)) with h0 | h1 | h4
  ·
    rw [h0, pow_zero] at h2
    have hUF : commV G ⊓ fixV G = ⊥ := by
      rw [eq_bot_iff, ← Subgroup.card_eq_one.mp h2]
      exact hUFC
    have hUt : ∃ u ∈ commV G, D.rho L3.x12 u ≠ u := by
      have hx : ∃ n, L3.act L3.x12 n ≠ n := by
        by_contra hc
        exact L3.x12_invol.2 (L3.act_injective _ fun v => by
          by_contra hv
          exact hc ⟨v, hv⟩)
      obtain ⟨n, hn⟩ := hx
      obtain ⟨u, hu, huW, hβ⟩ := exists_mem_commV D n
      refine ⟨u, hu, fun htu => hn ?_⟩
      have hmem : D.rho L3.x12 u ∈ W₂ := by rw [htu]; exact huW
      have h := D.β_rho L3.x12 u huW hmem
      have e : (⟨D.rho L3.x12 u, hmem⟩ : ↥W₂) = ⟨u, huW⟩ := Subtype.ext htu
      rw [e, hβ, toAdd_ofAdd] at h
      exact (Multiplicative.ofAdd.injective h).symm
    exact card_of_natural hV D hUc (by rw [hU8, h2, mul_one]) hUF hUt hind
  ·
    rw [h1, pow_one] at h2
    exact Or.inr (card_of_two hV D hUc hUU (by rw [hU8, h2]) inf_le_left hC₀F h2 hUFC hind)
  ·
    have h4' : 4 ≤ Nat.card ↥(commV G ⊓ W₁) := by
      rw [h2]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ rk ↥(commV G ⊓ W₁) := Nat.pow_le_pow_right (by norm_num) h4
    exact (false_of_four_le_aux hV D (invariant_of_commV_le le_rfl) hUU inf_le_left hC₀F hU8
      h4').elim

end CFSG.Quasithin.Vol2.Ch10
