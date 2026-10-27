module

public import CFSG.RankThree.GF2n.Parrott.Section2Cases
public import CFSG.RankThree.GF2n.Parrott.Section1Fusion

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {z : G}

theorem not_conj_of_mem_cosetCJ_exists_sylow {t : ↥(H z)} {σ : G}
    (htJ : (t : G) ∉ J z)
    (hFacts : ∀ ⦃x : G⦄, (∃ c ∈ CJ z σ, x = (t : G) * c) → orderOf x = 2 →
      ∃ K : Subgroup G, K ≤ H z ∧
        IsSylowOf 2 K (Subgroup.centralizer ({x} : Set G) ⊓
          Subgroup.centralizer ({σ} : Set G)) ∧
        z ∈ ⁅K, K⁆ ∧ ⁅K, K⁆ ≤ J z)
    {x : G} (hxCJ : ∃ c ∈ CJ z σ, x = (t : G) * c) (hx2 : orderOf x = 2) :
    ¬ ∃ m ∈ Subgroup.centralizer ({σ} : Set G), m * z * m⁻¹ = x := by
  obtain ⟨K, hKH, hK, hzK, hK'J⟩ := hFacts hxCJ hx2
  obtain ⟨c, hcCJ, hxc⟩ := hxCJ
  have hcJ : c ∈ J z := (mem_CJ.mp hcCJ).2
  have hxJ : x ∉ J z := by
    intro hxJmem
    apply htJ
    have ht_eq : (t : G) = x * c⁻¹ := by
      rw [hxc]
      group
    rw [ht_eq]
    exact (J z).mul_mem hxJmem ((J z).inv_mem hcJ)
  have hzcent : z ∈ Subgroup.centralizer (K : Set G) :=
    Subgroup.centralizer_le hKH (z_centralizes_H_A (z := z))
  exact not_conj_of_isSylowOf_centralizer_of_commutator_le
    (L := Subgroup.centralizer ({σ} : Set G)) (K := K) (J := J z) hK hzK hK'J hxJ hzcent

theorem no_conj_z_eq_of_mem_tJ_exists_sylow {t : ↥(H z)} {σ : G}
    (htσ : (t : G) * σ = σ * (t : G)) (htJ : (t : G) ∉ J z)
    (hσH : σ ∈ H z) (hσ3 : orderOf σ = 3)
    (hReduce : ∀ ⦃x : G⦄, (∃ j ∈ J z, x = (t : G) * j) → orderOf x = 2 →
      ∃ h ∈ H z, ∃ c ∈ CJ z σ, h * x * h⁻¹ = (t : G) * c)
    (hFacts : ∀ ⦃x : G⦄, (∃ c ∈ CJ z σ, x = (t : G) * c) → orderOf x = 2 →
      ∃ K : Subgroup G, K ≤ H z ∧
        IsSylowOf 2 K (Subgroup.centralizer ({x} : Set G) ⊓
          Subgroup.centralizer ({σ} : Set G)) ∧
        z ∈ ⁅K, K⁆ ∧ ⁅K, K⁆ ≤ J z)
    (hstar : ∀ g : G, CFSG.conjugate (Subgroup.zpowers σ) g ≤ H z →
      ∃ h ∈ H z, CFSG.conjugate (Subgroup.zpowers σ) g =
        CFSG.conjugate (Subgroup.zpowers σ) h)
    (hN : ∀ n ∈ Subgroup.normalizer (Subgroup.zpowers σ : Set G),
      ∃ h ∈ Subgroup.normalizer (Subgroup.zpowers σ : Set G) ⊓ H z,
      ∃ c ∈ Subgroup.centralizer (Subgroup.zpowers σ : Set G), h * c = n) :
    ∀ x : G, (∃ j ∈ J z, x = (t : G) * j) → orderOf x = 2 → ∀ g : G, g * z * g⁻¹ ≠ x := by
  intro x₀ hx₀J hx₀2 g₀ hg₀
  obtain ⟨h', -, c, hcCJ, hhx⟩ := hReduce hx₀J hx₀2
  set x := h' * x₀ * h'⁻¹ with hx
  have hx2 : orderOf x = 2 := by
    rw [hx, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hx₀2]
  have hxCJ : ∃ c ∈ CJ z σ, x = (t : G) * c := ⟨c, hcCJ, hhx⟩
  have hrel := not_conj_of_mem_cosetCJ_exists_sylow htJ hFacts hxCJ hx2
  have hcJ : c ∈ J z := (mem_CJ.mp hcCJ).2
  have hcσ : c * σ = σ * c := Subgroup.mem_centralizer_singleton_iff.mp (mem_CJ.mp hcCJ).1
  have hxH : x ∈ H z := by
    rw [hhx]
    exact (H z).mul_mem t.2 (J_le_H (z := z) hcJ)
  have hxσ : x * σ = σ * x := by
    rw [hhx]
    calc (t : G) * c * σ = (t : G) * (c * σ) := by group
      _ = (t : G) * (σ * c) := by rw [hcσ]
      _ = σ * ((t : G) * c) := by rw [← mul_assoc, htσ, mul_assoc]
  have hP3 : IsPGroup 3 (Subgroup.zpowers σ) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hσ3, pow_one]
  have hPne : Subgroup.zpowers σ ≠ ⊥ := by
    intro hbot
    have hσmem : σ ∈ Subgroup.zpowers σ := Subgroup.mem_zpowers σ
    rw [hbot] at hσmem
    have hσ1 : σ = 1 := Subgroup.mem_bot.mp hσmem
    rw [hσ1, orderOf_one] at hσ3
    omega
  have hxP : ∀ y ∈ Subgroup.zpowers σ, x * y = y * x := by
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_right (show Commute x σ from hxσ) k).eq
  obtain ⟨c', hc'C, hc'z⟩ :=
    (prop4_fusion_centralizer (p := 3) (by norm_num) (by norm_num) hP3 hPne
      (Subgroup.zpowers_le.mpr hσH) hstar hN hx2 hxH hxP).mp
      ⟨h' * g₀, by rw [hx, ← hg₀]; group⟩
  have hc'σ : c' * σ = σ * c' :=
    (Subgroup.mem_centralizer_iff.mp hc'C σ (Subgroup.mem_zpowers σ)).symm
  have hc'invσ : c'⁻¹ * σ = σ * c'⁻¹ := by
    calc c'⁻¹ * σ = c'⁻¹ * (σ * c') * c'⁻¹ := by group
      _ = c'⁻¹ * (c' * σ) * c'⁻¹ := by rw [← hc'σ]
      _ = σ * c'⁻¹ := by group
  apply hrel
  refine ⟨c'⁻¹, Subgroup.mem_centralizer_singleton_iff.mpr hc'invσ, ?_⟩
  calc c'⁻¹ * z * (c'⁻¹)⁻¹ = c'⁻¹ * z * c' := by rw [inv_inv]
    _ = c'⁻¹ * (c' * x * c'⁻¹) * c' := by rw [hc'z]
    _ = x := by group

end CFSG.RankThree.GF2n.Parrott
