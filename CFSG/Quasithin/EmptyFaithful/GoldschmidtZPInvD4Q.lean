module

public import CFSG.LargeExtraspecial.S63CD4A

public section

namespace CFSG.Quasithin.ZPInv

open CFSG.LargeExtraspecial.S63 CFSG.Sporadic.SmallF2.Native Subgroup

set_option maxRecDepth 100000 in
theorem qGens_not_comm : mulR qGens[0]! qGens[1]! ≠ mulR qGens[1]! qGens[0]! := by
  decide +kernel

theorem d4Q_nonabelian : ∃ x ∈ d4Q, ∃ y ∈ d4Q, x * y ≠ y * x := by
  have h0 : 0 < qGens.size := by rw [qGens_size]; norm_num
  have h1 : 1 < qGens.size := by rw [qGens_size]; norm_num
  refine ⟨qGH 0, subset_closure ⟨0, h0, rfl⟩, qGH 1, subset_closure ⟨1, h1, rfl⟩, fun h => ?_⟩
  have e1 := repE_mul (repE_qGens h0) (repE_qGens h1)
  have e2 := repE_mul (repE_qGens h1) (repE_qGens h0)
  rw [h] at e1
  exact qGens_not_comm (arr_eq_of_repE
    (validR_mulR (size_of_validR (validR_qGens h0)) (validR_qGens h1))
    (validR_mulR (size_of_validR (validR_qGens h1)) (validR_qGens h0)) e1 e2)


theorem centralizer_d4z_le_normalizer_d4Q :
    centralizer ({d4z} : Set trialityGroup8) ≤ normalizer (d4Q : Set trialityGroup8) := by
  have hnorm : ∀ c ∈ centralizer ({d4z} : Set trialityGroup8), ∀ x ∈ d4Q,
      c * x * c⁻¹ ∈ d4Q := by
    intro c hc x hx
    obtain ⟨q, hq, l, hl, rfl⟩ := exists_of_mem_centralizer_d4z hc
    have h1 := d4Q.mul_mem (d4Q.mul_mem hq (d4L_normalizes l hl x hx)) (d4Q.inv_mem hq)
    have e : q * l * x * (q * l)⁻¹ = q * (l * x * l⁻¹) * q⁻¹ := by group
    rw [e]
    exact h1
  intro c hc
  rw [mem_normalizer_iff]
  intro x
  refine ⟨hnorm c hc x, fun hx => ?_⟩
  have h1 := hnorm c⁻¹ (inv_mem hc) _ hx
  have e : c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x := by group
  rwa [e] at h1

theorem d4Q_central_eq {m : trialityGroup8} (hm : m ∈ d4Q) (hc : ∀ x ∈ d4Q, x * m = m * x) :
    m = 1 ∨ m = d4z := by
  by_contra hne
  push Not at hne
  obtain ⟨x, hx, y, hy, hxy⟩ := d4Q_nonabelian
  have hmem : ∀ n ∈ d4Q, (∀ q ∈ d4Q, q * n = n * q) → n ∈ d4Q ⊓ centralizer (d4Q : Set _) :=
    fun n hn hcn => ⟨hn, mem_centralizer_iff.2 fun q hq => hcn q hq⟩
  have hQM : d4Q ≤ d4Q ⊓ centralizer (d4Q : Set trialityGroup8) := by
    refine d4Q_irred _ inf_le_left ?_ (hmem _ d4z_mem_d4Q fun q hq => ?_)
      ⟨m, hmem m hm hc, hne.1, hne.2⟩
    · intro l hl n hn
      have hn' := (mem_inf.1 hn)
      refine hmem _ (d4L_normalizes l hl n hn'.1) fun q hq => ?_
      have hq' := d4L_normalizes l⁻¹ (d4L.inv_mem hl) q hq
      have := mem_centralizer_iff.1 hn'.2 _ hq'
      calc q * (l * n * l⁻¹) = l * ((l⁻¹ * q * l⁻¹⁻¹) * n) * l⁻¹ := by group
        _ = l * (n * (l⁻¹ * q * l⁻¹⁻¹)) * l⁻¹ := by rw [this]
        _ = (l * n * l⁻¹) * q := by group
    · exact mem_centralizer_singleton_iff.1 (d4Q_le_centralizer hq)
  exact hxy (mem_centralizer_iff.1 (mem_inf.1 (hQM hx)).2 y hy).symm

end CFSG.Quasithin.ZPInv
