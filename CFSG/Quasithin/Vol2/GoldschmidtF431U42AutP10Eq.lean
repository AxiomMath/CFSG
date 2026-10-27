module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP10Tri

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin U42F431
open CFSG.Quasithin.H13.F431.U42 (P45)

namespace RhoData

variable {G : Type} [Group G] (d : RhoData G)

theorem alpha_three {k : Ah}
    (hk : k ∈ p10Kh) {l : PL} (hl : RepL l (k : P45)) :
    ∃ k' ∈ p10Kh, RepL (alphaL (alphaL (alphaL l))) (k' : P45) ∧
      (d.ρ * d.ι p10hA) ^ 3 * d.ι k * ((d.ρ * d.ι p10hA) ^ 3)⁻¹ = d.ι k' := by
  obtain ⟨k₁, hk₁, hl₁, e₁⟩ := d.alpha_step hk hl
  obtain ⟨k₂, hk₂, hl₂, e₂⟩ := d.alpha_step hk₁ hl₁
  obtain ⟨k₃, hk₃, hl₃, e₃⟩ := d.alpha_step hk₂ hl₂
  refine ⟨k₃, hk₃, hl₃, ?_⟩
  rw [← e₃, ← e₂, ← e₁]
  generalize d.ρ * d.ι p10hA = g
  rw [pow_three']
  group

theorem triangle [Finite G]
    (hH : Nat.card d.H = 576) : (d.ρ * d.ι p10hA) ^ 3 = 1 := by
  have hu : (d.ρ * d.ι p10hA) ^ 3 ∈ p10Kh.map d.ι := d.triangle_mem hH
  obtain ⟨n, hn, hnu⟩ := Subgroup.mem_map.1 hu
  obtain ⟨ln, hlnK, hln⟩ := rep_mem_Kh n hn
  have hc5 : ∀ l ∈ p10Kg, comp ln l = comp (alphaL (alphaL (alphaL l))) ln := by
    intro l hl
    obtain ⟨k, hk, hlk⟩ := exists_Kh_rep (p10_uniq_check.1 l hl)
    obtain ⟨k₃, hk₃, hl₃, e⟩ := d.alpha_three hk hlk
    rw [← hnu, ← map_inv, ← map_mul, ← map_mul] at e
    have h1 : n * k * n⁻¹ = k₃ := d.inj e
    have h2 : n * k = k₃ * n := by rw [← h1]; group
    have h3 : RepL (comp ln l) ((n * k : Ah) : P45) := repL_mul hln hlk
    have h4 : RepL (comp (alphaL (alphaL (alphaL l))) ln) ((k₃ * n : Ah) : P45) :=
      repL_mul hl₃ hln
    rw [h2] at h3
    exact repL_unique h3 h4
  have hc2 : alphaL ln = ln := by
    obtain ⟨n', hn', hln', e⟩ := d.alpha_step hn hln
    have e2 : (d.ρ * d.ι p10hA) * d.ι n * (d.ρ * d.ι p10hA)⁻¹ = d.ι n := by
      rw [hnu]
      generalize d.ρ * d.ι p10hA = g
      rw [pow_three']
      group
    have : n' = n := d.inj (e.symm.trans e2)
    rw [this] at hln'
    exact repL_unique hln' hln
  have hid : ln = idL := (p10_uniq_check.2 ln hlnK hc5 hc2)
  have hn1 : n = 1 := Subtype.ext (eq_of_repL hln (hid ▸ repL_one 45))
  rw [← hnu, hn1, map_one]

end RhoData

end CFSG.Quasithin.H13.F431.U42Aut
