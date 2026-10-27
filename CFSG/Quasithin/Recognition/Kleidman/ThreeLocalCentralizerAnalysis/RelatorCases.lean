module

public import CFSG.Quasithin.Recognition.Kleidman.ThreeLocalCentralizerAnalysis.SevenArgument
public import CFSG.Quasithin.Recognition.Kleidman.ThreeLocalCentralizerAnalysis.PowDichotomy

public section

namespace CFSG.Quasithin.Kleidman.ThreeLocal

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

theorem sq_mem_CK_of_inv {G : Type} [Group G] {y g : G} (hg : g * y * g⁻¹ = y⁻¹) :
    g ^ 2 ∈ CK y := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hc2 : g ^ 2 * y * (g ^ 2)⁻¹ = y := by
    calc g ^ 2 * y * (g ^ 2)⁻¹ = g * (g * y * g⁻¹) * g⁻¹ := by
          simp only [pow_two, mul_inv_rev, mul_assoc]
      _ = g * y⁻¹ * g⁻¹ := by rw [hg]
      _ = (g * y * g⁻¹)⁻¹ := by group
      _ = y := by rw [hg]; simp
  calc g ^ 2 * y = (g ^ 2 * y * (g ^ 2)⁻¹) * g ^ 2 := by simp only [mul_assoc, inv_mul_cancel,
        mul_one]
    _ = y * g ^ 2 := by rw [hc2]

theorem _root_.CFSG.Quasithin.IsTypeH2.relator_cases
    {G : Type} [Group G] [Finite G] {z : G} (h : IsTypeH2 G z) (hone : involutionClassCount G = 1)
    {y : G} (hy : y ∈ Subgroup.centralizer ({z} : Set G)) (hy3 : orderOf y = 3)
    {w g : G} (hw : w ∈ CK y) (hg : g * y * g⁻¹ = y⁻¹) :
    (∃ o ∈ ({3, 4, 5} : Finset ℕ), ∃ k ∈ ({0, 1, 2} : Finset ℕ), w ^ o = y ^ k) ∨
      (∃ o ∈ ({3, 4} : Finset ℕ), ∃ k ∈ ({0, 1, 2} : Finset ℕ), (g ^ 2) ^ o = y ^ k) := by
  have hpow : ∀ {x : G} {o : ℕ}, x ^ o ∈ Subgroup.zpowers y → ∃ k ∈ ({0, 1, 2} : Finset ℕ),
      x ^ o = y ^ k := by
    intro x o hx
    rcases exists_pow_eq_of_mem_zpowers hy3 hx with h0 | h0 | h0
    · exact ⟨0, by simp, by rw [h0]; simp⟩
    · exact ⟨1, by simp, by rw [h0]; simp⟩
    · exact ⟨2, by simp, h0⟩
  rcases h.pow_dichotomy hone hy hy3 with hA | hB
  · left
    rcases hA w hw with h3 | h4 | h5
    · obtain ⟨k, hk, hwk⟩ := hpow h3
      exact ⟨3, by simp, k, hk, hwk⟩
    · obtain ⟨k, hk, hwk⟩ := hpow h4
      exact ⟨4, by simp, k, hk, hwk⟩
    · obtain ⟨k, hk, hwk⟩ := hpow h5
      exact ⟨5, by simp, k, hk, hwk⟩
  · right
    rcases hB (g ^ 2) (sq_mem_CK_of_inv hg) with h3 | h4 | h7
    · obtain ⟨k, hk, hwk⟩ := hpow h3
      exact ⟨3, by simp, k, hk, hwk⟩
    · obtain ⟨k, hk, hwk⟩ := hpow h4
      exact ⟨4, by simp, k, hk, hwk⟩
    · by_cases hg2 : g ^ 2 = 1
      · exact ⟨3, by simp, 0, by simp, by rw [hg2]; simp⟩
      · exact (h.false_of_pow_seven_mem_zpowers hone hy3 hg hg2 h7).elim

end CFSG.Quasithin.Kleidman.ThreeLocal
