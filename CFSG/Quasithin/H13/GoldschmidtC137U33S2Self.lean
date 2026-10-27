module

public import CFSG.Quasithin.H13.GoldschmidtC137U33S2Ppt

public section

namespace CFSG.Quasithin.H13.U3.GC137.S2

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.Orbit
  CFSG.Quasithin.H13.G2Dat

theorem sM_unique_fix : ∀ c ∈ omegaL, (∀ i < 64, mact (sM i) c = c) → c = 8 := by
  decide +kernel

theorem b₀_not_normalizes : ∃ i < 64, ∀ k < 64,
    mmul (mmul bCode (sM i)) (mmul bCode bCode) ≠ sM k := by
  decide +kernel

theorem b₀_not_mem_normalizer : b₀ ∉ Subgroup.normalizer (sSubG : Set Gam) := by
  intro h
  obtain ⟨i, hi, hik⟩ := b₀_not_normalizes
  have h1 : sEltG i ∈ sSubG := mem_sSubG.2 ⟨i, hi, rfl⟩
  have h2 : b₀ * sEltG i * b₀⁻¹ ∈ sSubG := (Subgroup.mem_normalizer_iff.1 h _).1 h1
  obtain ⟨k, hk, hkk⟩ := mem_sSubG.1 h2
  have := congrArg (fun g : Gam => matCode g.1) hkk
  simp only [matCode_sEltG hk, matCode_mulG, matCode_sEltG hi, matCode_b₀, b₀_inv] at this
  exact hik k hk this.symm

theorem fix_of_normalizer {g : Gam} (hg : g ∈ Subgroup.normalizer (sSubG : Set Gam)) :
    act g 8 = 8 := by
  have hc : act g 8 ∈ omegaL := by
    have h8 : isPt 8 = true := by decide
    have hlt : (8 : ℕ) ∈ o0Codes := by decide
    exact isPt_iff_mem _ (mact_mem_o0Codes g.2 hlt) (isPt_act g (by norm_num) h8)
  refine sM_unique_fix _ hc fun i hi => ?_
  have hs : sEltG i ∈ sSubG := mem_sSubG.2 ⟨i, hi, rfl⟩
  have hs' : g⁻¹ * sEltG i * g ∈ sSubG := by
    have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer (sSubG : Set Gam)).inv_mem hg)
      (sEltG i)).1 hs
    simpa using this
  have h1 : act (sEltG i * g) 8 = act (g * (g⁻¹ * sEltG i * g)) 8 := by
    congr 1
    group
  rw [act_mul _ _ (by norm_num), act_mul _ _ (by norm_num), sSubG_fix _ hs'] at h1
  rw [← act_sEltG hi]
  exact h1

theorem normalizer_S_le : Subgroup.normalizer (sSubG : Set Gam) ≤ sSubG := by
  intro g hg
  have hP : g ∈ Ppt := mem_Ppt.2 (fix_of_normalizer hg)
  rcases mem_Ppt_iff.1 hP with h | ⟨s₁, hs₁, s₂, hs₂, rfl⟩
  · exact h
  · exfalso
    apply b₀_not_mem_normalizer
    have hN : sSubG ≤ Subgroup.normalizer (sSubG : Set Gam) := Subgroup.le_normalizer
    have : b₀ = s₁⁻¹ * (s₁ * b₀ * s₂) * s₂⁻¹ := by group
    rw [this]
    exact mul_mem (mul_mem (inv_mem (hN hs₁)) hg) (inv_mem (hN hs₂))

end CFSG.Quasithin.H13.U3.GC137.S2
