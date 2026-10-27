module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_16FactsA6Model

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts CFSG.QuasithinUnique.Unc25K1.A6Model

theorem exists_conj_eq_of_odd_orderOf_alt_six {α : MulAut (alternatingGroup (Fin 6))}
    (hα : Odd (orderOf α)) : ∃ l : alternatingGroup (Fin 6), α = MulAut.conj l := by
  obtain ⟨-, ψ, -, -⟩ := exists_pslEquiv
  set φ : alternatingGroup (Fin 6) ≃* ↥A6Models.psl29 := ψ.symm with hφ
  set b : ↥A6Models.autA6 := thetaEquiv φ α with hb
  have hbodd : Odd (orderOf b) := by
    rw [hb, MulEquiv.orderOf_eq]
    exact hα
  have hmem : (b : P10) ∈ A6Models.psl29 := by
    let N : Subgroup ↥A6Models.autA6 := A6Models.psl29.subgroupOf A6Models.autA6
    haveI hN : N.Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simpa using psl29_normal (g : P10) g.2 (n : P10) hn⟩
    have hcardN : Nat.card N = 360 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe psl29_le_autA6).toEquiv, card_psl29]
    have hQ : Nat.card (↥A6Models.autA6 ⧸ N) = 4 := by
      have := Subgroup.card_eq_card_quotient_mul_card_subgroup N
      rw [card_autA6, hcardN] at this
      omega
    have h1 : orderOf (QuotientGroup.mk b : ↥A6Models.autA6 ⧸ N) ∣ orderOf b :=
      orderOf_map_dvd (QuotientGroup.mk' N) b
    have h2 : orderOf (QuotientGroup.mk b : ↥A6Models.autA6 ⧸ N) ∣ 4 := by
      rw [← hQ]
      exact orderOf_dvd_natCard _
    have h3 : orderOf (QuotientGroup.mk b : ↥A6Models.autA6 ⧸ N) = 1 := by
      have hodd := Odd.of_dvd_nat hbodd h1
      have hle := Nat.le_of_dvd (by norm_num) h2
      have hpos := orderOf_pos (QuotientGroup.mk b : ↥A6Models.autA6 ⧸ N)
      have hdiv : ∀ m, m ∣ 4 → m = 1 ∨ m = 2 ∨ m = 4 := by
        intro m hm
        have := Nat.le_of_dvd (by norm_num) hm
        interval_cases m <;> simp_all
      rcases hdiv _ h2 with h | h | h
      · exact h
      · rw [h] at hodd; exact absurd hodd (by decide)
      · rw [h] at hodd; exact absurd hodd (by decide)
    rw [orderOf_eq_one_iff] at h3
    have := (QuotientGroup.eq_one_iff b).1 h3
    exact Subgroup.mem_subgroupOf.1 this
  refine ⟨ψ ⟨(b : P10), hmem⟩, MulEquiv.ext fun k => ?_⟩
  apply φ.injective
  apply Subtype.ext
  have hspec := thetaEquiv_spec φ α k
  rw [← hb] at hspec
  rw [hspec, MulAut.conj_apply, map_mul, map_mul, map_inv]
  have : φ (ψ ⟨(b : P10), hmem⟩) = ⟨(b : P10), hmem⟩ := by simp [hφ]
  rw [this]
  rfl

end CFSG.LocalAnalysis.WeakClosure81
