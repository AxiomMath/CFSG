module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveQ5
public import CFSG.Quasithin.H13.NQCatT513U35
public import Certificates.Certificate7170

public section

namespace CFSG.Quasithin.H13.FiveNorm.U35F

open CFSG.Quasithin.H13.NQCat.T513 CFSG.Quasithin.H13.NQCat.T513.U35
open CFSG.Quasithin.H13.KGU35 (f25Data)
open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartTwo.KFacts

theorem fiveInner_PU : FiveInner PU := by
  intro α hα
  have hodd : Odd (orderOf α) := Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hα)
  obtain ⟨A, rfl⟩ := mem_range_psuConj_of_odd hodd
  obtain ⟨y, hy⟩ := psuConj_pow_three A
  refine ⟨y ^ 2, ?_⟩
  calc psuConj f25Data A = psuConj f25Data A ^ 6 := by
        rw [show (6 : ℕ) = 5 + 1 from rfl, pow_succ, hα, one_mul]
    _ = (psuConj f25Data A ^ 3) ^ 2 := by rw [← pow_mul]
    _ = MulAut.conj (y ^ 2) := by rw [hy, map_pow]

theorem noFiveOver_PU : NoFiveOver PU := by
  intro S H hS hSH hcard
  have hk := Certificates.certificate7170.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨h1, h2⟩ := isSylowTwoOf_top_index hS
  obtain ⟨⟨g, hgH⟩, hg5⟩ := exists_prime_orderOf_dvd_card' (G := ↥H) 5
    (by rw [hcard]; exact dvd_mul_right 5 _)
  have hgo : orderOf g = 5 := by rw [← Subgroup.orderOf_mk g hgH]; exact hg5
  have hprod := exists_zpow_mul_of_card h1 hSH hcard hgH hgo
  obtain ⟨c, hcT⟩ := MulAction.exists_smul_eq PU (h1.toSylow h2)
    ((isPGroup_T0' hk).toSylow (not_two_dvd_index_T0' hk))
  have hmap : S.map (MulAut.conj c).toMonoidHom = T0 := by
    have h3 := congrArg (fun P : Sylow 2 PU => (P : Subgroup PU)) hcT
    simp only [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] at h3
    rw [← h3, Subgroup.pointwise_smul_def]
    rfl
  have hmemT0 : ∀ t₀ ∈ T0, c⁻¹ * t₀ * c ∈ S := by
    intro t₀ ht₀
    rw [← hmap] at ht₀
    obtain ⟨t, ht, rfl⟩ := ht₀
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show c⁻¹ * (c * t * c⁻¹) * c = t by group]
    exact ht
  have hT0mem : ∀ t ∈ S, c * t * c⁻¹ ∈ T0 := by
    intro t ht
    rw [← hmap]
    exact ⟨t, ht, rfl⟩
  set g₀ := c * g * c⁻¹ with hg₀
  have hg₀o : orderOf g₀ = 5 := by
    rw [hg₀, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hgo]
  have hperm₀ : ∀ t ∈ T0, ∃ a : ℤ, ∃ t' ∈ T0, t * g₀ = g₀ ^ a * t' := by
    intro t₀ ht₀
    have hu := hmemT0 t₀ ht₀
    obtain ⟨a, s, hs, he⟩ := hprod _ (H.mul_mem (hSH hu) hgH)
    refine ⟨a, c * s * c⁻¹, hT0mem s hs, ?_⟩
    have hg₀a : g₀ ^ a = c * g ^ a * c⁻¹ := by
      rw [hg₀, ← MulAut.conj_apply, ← map_zpow, MulAut.conj_apply]
    rw [hg₀a]
    calc t₀ * g₀ = c * (c⁻¹ * t₀ * c * g) * c⁻¹ := by rw [hg₀]; group
      _ = c * (g ^ a * s) * c⁻¹ := by rw [he]
      _ = c * g ^ a * c⁻¹ * (c * s * c⁻¹) := by group
  refine Certificates.certificate7170.2 _ (conj_mem_range g₀)
    (by rw [orderOf_injective _ conj_injective_PU, hg₀o]) fun t ht => ?_
  obtain ⟨a, t', ht', he⟩ := hperm₀ t ht
  exact ⟨a, t', ht', by rw [← map_mul, he, map_mul, map_zpow]⟩

theorem fiveRigid_PU : FiveRigid PU :=
  ⟨center_PU, fiveInner_PU, noFiveOver_PU⟩

end CFSG.Quasithin.H13.FiveNorm.U35F
