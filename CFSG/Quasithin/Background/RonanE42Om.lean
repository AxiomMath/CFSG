module

public import CFSG.Quasithin.Background.RonanE42Basic

public section

namespace CFSG.Quasithin.RonanE42

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3

variable {G V : Type} [Group G] [CommGroup V]

theorem Om_conjSubgroup {ρ : G →* MulAut V} {n : ℕ} {A : Subgroup G} (hA : Om ρ n A) (g : G) :
    Om ρ n (conjSubgroup A g) := by
  obtain ⟨hne, h2, hc, hfix⟩ := hA
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hbot
    apply hne
    rw [eq_bot_iff]
    intro a ha
    have : g⁻¹ * a * g ∈ conjSubgroup A g := by
      rw [mem_conjSubgroup_iff]
      simpa [mul_assoc] using ha
    rw [hbot, Subgroup.mem_bot] at this
    have h1 : a = 1 := by
      have := congrArg (fun x => g * x * g⁻¹) this
      simpa [mul_assoc] using this
    rw [h1]
    exact Subgroup.one_mem _
  · intro a ha
    have ha' : g * a * g⁻¹ ∈ A := mem_conjSubgroup_iff.1 ha
    have := h2 _ ha'
    have e : (g * a * g⁻¹) ^ 2 = g * a ^ 2 * g⁻¹ := by
      simp [pow_two, mul_assoc]
    rw [e] at this
    have h3 : a ^ 2 = 1 := by
      have := congrArg (fun x => g⁻¹ * x * g) this
      simpa [mul_assoc] using this
    exact h3
  · intro a ha b hb
    have ha' : g * a * g⁻¹ ∈ A := mem_conjSubgroup_iff.1 ha
    have hb' : g * b * g⁻¹ ∈ A := mem_conjSubgroup_iff.1 hb
    have := hc _ ha' _ hb'
    have h3 : g * (a * b) * g⁻¹ = g * (b * a) * g⁻¹ := by
      simpa [mul_assoc] using this
    simpa using h3
  · intro B hB hm
    obtain ⟨B', hB'⟩ : ∃ B', B' = conjSubgroup B g⁻¹ := ⟨_, rfl⟩
    have hB'A : B' ≤ A := by
      intro x hx
      have hx' : g⁻¹ * x * g⁻¹⁻¹ ∈ B := mem_conjSubgroup_iff.1 (hB' ▸ hx)
      have := hB hx'
      have := mem_conjSubgroup_iff.1 this
      simpa [mul_assoc] using this
    have hBB' : conjSubgroup B' g = B := by
      rw [hB', conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
    have hmB' : mQuot A B' < n := by
      have h1 := mQuot_conjSubgroup A B' g
      rw [hBB'] at h1
      omega
    have hFB' : Fx ρ B' = Fx ρ A := hfix B' hB'A hmB'
    have hFB : Fx ρ B = Fx ρ (conjSubgroup B' g) := by rw [hBB']
    ext v
    rw [hFB, mem_Fx_conjSubgroup, mem_Fx_conjSubgroup, hFB']

end CFSG.Quasithin.RonanE42
