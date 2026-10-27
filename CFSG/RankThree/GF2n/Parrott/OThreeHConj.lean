module

public import CFSG.RankThree.GF2n.Parrott.OThreeH

import CFSG.RankThree.GF2n.Stroth80.Sec7TailCoprimeAdjust

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.GH74.KGroups

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal]

theorem exists_conj_sigma1_mul_sigma2_inv_of_mem_O3subA {y : QA45.originalSubgroup}
    (hy : y ∈ O3subA)
    (hy1 : (y : Equiv.Perm (Fin 45)) ∉
      ({1, sigma1, sigma1 * sigma1} : Finset (Equiv.Perm (Fin 45)))) :
    ∃ c : QA45.originalSubgroup,
      c * ((⟨sigma1, sigma1_mem_A⟩ : QA45.originalSubgroup) *
        (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup)⁻¹) * c⁻¹ = y := by
  classical
  have hyO : (y : Equiv.Perm (Fin 45)) ∈ O3 () := hy
  have hmem : (y : Equiv.Perm (Fin 45)) ∈ o3CenterComplement () := by
    simp only [o3CenterComplement, List.mem_toFinset, List.mem_filter]
    exact ⟨hyO, by simpa using hy1⟩
  rw [← Certificates.certificate946016.class_of_sigma1sigma2inv.2.2] at hmem
  simp only [classInO3, List.mem_toFinset, List.mem_filter, List.mem_map] at hmem
  obtain ⟨⟨c, hc, hcy⟩, -⟩ := hmem
  have hcA : c ∈ QA45.originalSubgroup := (mem_elemsT QA45 QA45_ok c).mp hc
  refine ⟨⟨c, hcA⟩, ?_⟩
  apply Subtype.ext
  simpa using hcy

theorem exists_conj_eq_sigma1Nine_mul_inv_of_mem_O3H (h : Tim79a.ParrottHyp z)
    (D : QuotientData (z := z) hN) {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {x : ↥(H z)} (hx : x ∈ O3H D) (hx1 : x ∉ Subgroup.zpowers (sigma1Nine (z := z) D)) :
    ∃ g : ↥(H z), g * x * g⁻¹ = sigma1Nine (z := z) D * σ₂⁻¹ := by
  classical
  set s := sigma1Nine (z := z) D with hs_def
  have hsO : s ∈ O3H D := sigma1Nine_mem_O3H (z := z) D
  have hqs : qH D s = (⟨sigma1, sigma1_mem_A⟩ : QA45.originalSubgroup) := qH_sigma1Nine D
  have hyA : qH D x ∈ O3subA := by
    rw [← map_O3H h D]
    exact Subgroup.mem_map_of_mem _ hx
  have hy1 : ((qH D x : QA45.originalSubgroup) : Equiv.Perm (Fin 45)) ∉
      ({1, sigma1, sigma1 * sigma1} : Finset (Equiv.Perm (Fin 45))) := by
    intro hmem
    have hinj := (eHom_bijective h D).1
    have key : ∀ k : ℕ, k ≤ 2 →
        ((qH D x : QA45.originalSubgroup) : Equiv.Perm (Fin 45)) = sigma1 ^ k → False := by
      intro k _ hk
      have hsk : s ^ k ∈ O3H D := pow_mem hsO k
      have heq : eHom D ⟨x, hx⟩ = eHom D ⟨s ^ k, hsk⟩ := by
        apply Subtype.ext
        rw [eHom_val, eHom_val, hk, map_pow, hqs]
        rfl
      have := congrArg Subtype.val (hinj heq)
      exact hx1 ⟨(k : ℤ), by simpa using this.symm⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h0 | h1 | h2
    · exact key 0 (by norm_num) (by simpa using h0)
    · exact key 1 (by norm_num) (by simpa using h1)
    · exact key 2 (by norm_num) (by simpa [pow_two] using h2)
  obtain ⟨c, hc⟩ := exists_conj_sigma1_mul_sigma2_inv_of_mem_O3subA hyA hy1
  obtain ⟨g₀, hg₀⟩ := qH_surjective D c
  set w : ↥(H z) := g₀ * (s * σ₂⁻¹) * g₀⁻¹ with hw_def
  have hqw : qH D w = qH D x := by
    rw [hw_def, map_mul, map_mul, map_inv, map_mul, map_inv, hg₀, hqs, hq₂, hc]
  have hxw : x⁻¹ * w ∈ (J z).subgroupOf (H z) := by
    rw [← ker_qH D, MonoidHom.mem_ker, map_mul, map_inv, hqw, inv_mul_cancel]
  have hx3 : x ^ 3 = 1 := by
    have := (isHeisenberg_O3H h D).1 ⟨x, hx⟩
    exact congrArg Subtype.val this
  have hxne : x ≠ 1 := by
    rintro rfl
    exact hx1 (Subgroup.one_mem _)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hox : orderOf x = 3 := orderOf_eq_prime hx3 hxne
  have hs3 : s ^ 3 = 1 := by
    rw [← sigma1Nine_order (z := z) D]
    exact pow_orderOf_eq_one s
  have hσ3 : σ₂ ^ 3 = 1 := by
    rw [← hσ₂]
    exact pow_orderOf_eq_one σ₂
  have hcomm : Commute s σ₂⁻¹ := (Commute.inv_right (show Commute s σ₂ from hc₂.symm))
  have hu3 : (s * σ₂⁻¹) ^ 3 = 1 := by
    rw [hcomm.mul_pow, hs3, inv_pow, hσ3, inv_one, one_mul]
  have hune : s * σ₂⁻¹ ≠ 1 := by
    intro h1
    have hq1 := congrArg (fun t => ((qH D t : QA45.originalSubgroup) : Equiv.Perm (Fin 45))) h1
    simp only [map_mul, map_inv, hqs, hq₂, map_one, Subgroup.coe_mul, Subgroup.coe_inv,
      OneMemClass.coe_one] at hq1
    apply Certificates.certificate946016.sigma2inv_not_mem_O3
    rw [hq1]
    exact Certificates.certificate946016.o3_one_mem
  have hou : orderOf (s * σ₂⁻¹) = 3 := orderOf_eq_prime hu3 hune
  have how : orderOf w = 3 := by
    have hsc : SemiconjBy g₀ (s * σ₂⁻¹) w := by
      rw [SemiconjBy, hw_def]
      group
    rw [← hsc.orderOf_eq]
    exact hou
  have hJ3 : ¬ 3 ∣ Nat.card ((J z).subgroupOf (H z)) := by
    obtain ⟨n, hn⟩ := (isPGroup_J_subgroupOf (z := z)).exists_card_eq
    rw [hn]
    intro h3
    have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
    omega
  obtain ⟨k, -, hk⟩ :=
    CFSG.RankThree.GF2n.Stroth80.exists_conj_mem_sup_zpowers ((J z).subgroupOf (H z)) hJ3
      hox how hxw
  refine ⟨(k * g₀)⁻¹, ?_⟩
  rw [← hk, hw_def]
  group

end CFSG.RankThree.GF2n.Parrott
