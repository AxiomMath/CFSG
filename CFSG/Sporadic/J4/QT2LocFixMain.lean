
module

public import CFSG.Sporadic.J4.QT2LocFixMainBase
import all CFSG.Sporadic.J4.QT2LocFixMainBase

public import CFSG.Sporadic.J4.QT2LocProof

public section

namespace CFSG.Sporadic.J4.QT2

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT Matrix
open scoped Classical

theorem fix2B_subset (hF : J4Facts) {c : ℕ} (hc : c ∈ tMasks) {g : J}
    (hfix : eta uJ 11 c • (g • w₀) = g • w₀) :
    g • w₀ = w₀ ∨ g • w₀ ∈ Dlt 5 ∨ g • w₀ ∈ Dlt 6 := by
  have hM := hF.mat
  obtain ⟨ℓ, hℓ, h, hh, h', hh', rfl⟩ := exists_rep hF g
  rw [smul_rep_form hM hh'] at hfix ⊢
  have h1 : (h⁻¹ * eta uJ 11 c * h) • rep ℓ = rep ℓ := by
    rw [mul_smul, mul_smul, hfix, inv_smul_smul]
  obtain ⟨c', hc', hc'e⟩ := (tSet_conj hM h hh).2 _ (⟨c, hc, rfl⟩ : eta uJ 11 c ∈ tSet)
  rw [hc'e] at h1
  interval_cases ℓ
  · left
    rw [rep_zero]
    exact smul_root_of_mem_Hj hM hh
  · exact absurd h1 (eta_moves_rep hM (by norm_num) (fix2B_facts _ (by decide) c' hc'))
  · exact absurd h1 (eta_moves_rep hM (by norm_num) (fix2B_facts _ (by decide) c' hc'))
  · exact absurd h1 (eta_moves_rep hM (by norm_num) (fix2B_facts _ (by decide) c' hc'))
  · exact absurd h1 (eta_moves_rep hM (by norm_num) (fix2B_facts _ (by decide) c' hc'))
  · exact Or.inr (Or.inl ⟨h, hh, rfl⟩)
  · exact Or.inr (Or.inr ⟨h, hh, rfl⟩)

end CFSG.Sporadic.J4.QT2
