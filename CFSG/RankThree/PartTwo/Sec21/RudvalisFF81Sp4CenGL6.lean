module

public import CFSG.RankThree.PartTwo.Sec21.FF81Sec56Defs
public import CFSG.RankThree.PartTwo.Sec21.RudvalisFF81Sp4CenTup
public import CFSG.RankThree.PartTwo.Sec21.RudvalisFF81Sp4CenBlk
public import CFSG.RankThree.PartTwo.Sec21.RudvalisFF81Sp4CenNF

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.Sp4Cen

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF81
open CFSG.Quasithin.G2U CFSG.Quasithin.H13.MatNCert Matrix
private theorem adj01_pow_three : (adj 0 * adj 1) ^ 3 = 1 := by decide

private theorem adj01_conj : adj 0 * (adj 0 * adj 1) * (adj 0)⁻¹ = (adj 0 * adj 1)⁻¹ := by decide

section Cert


theorem exists_F5X3 : ∃ F X : GL4, orderOf F = 5 ∧ orderOf X = 3 ∧ F * X = X * F :=
  Certificates.certificate899110.2.2.2.2

theorem main_u0 {Y : Subgroup GL6} {φ : Equiv.Perm (Fin 6) →* GL6} (huY : u0 ∈ Y)
    (hYC : Y ≤ Subgroup.centralizer {u0}) (hφY : ∀ σ, φ σ ∈ Y)
    (hφ3 : φ (adj 0 * adj 1) ≠ 1) :
    Y = φ.range ⊔ Subgroup.zpowers u0 ∨
      (Nat.card Y = 60480 ∧ ∃ f ∈ Y, ∃ x ∈ Y, orderOf f = 5 ∧ orderOf x = 3 ∧
        x ∉ Subgroup.zpowers u0 ∧ f * x = x * f) := by
  have hφC : ∀ σ, φ σ ∈ C0 := fun σ => hYC (hφY σ)
  set φc : Equiv.Perm (Fin 6) →* ↥C0 := φ.codRestrict C0 hφC with hφc
  set ψ : Equiv.Perm (Fin 6) →* GL4 := tau.comp φc with hψ
  have hψ3 : ψ (adj 0 * adj 1) ≠ 1 := by
    intro h
    have hz : φ (adj 0 * adj 1) ∈ Subgroup.zpowers u0 :=
      (tau_eq_one_iff (φc (adj 0 * adj 1))).mp h
    obtain ⟨k, hk⟩ := hz
    have hgu : φ (adj 0) * u0 = u0 * φ (adj 0) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hφC (adj 0))
    have hc : φ (adj 0) * φ (adj 0 * adj 1) = φ (adj 0 * adj 1) * φ (adj 0) := by
      rw [← hk]
      exact ((Commute.zpow_right (show Commute (φ (adj 0)) u0 from hgu) k)).eq
    have h2 : (φ (adj 0 * adj 1))⁻¹ = φ (adj 0 * adj 1) := by
      calc (φ (adj 0 * adj 1))⁻¹ = φ ((adj 0 * adj 1)⁻¹) := (map_inv φ _).symm
        _ = φ (adj 0 * (adj 0 * adj 1) * (adj 0)⁻¹) := by rw [adj01_conj]
        _ = φ (adj 0) * φ (adj 0 * adj 1) * (φ (adj 0))⁻¹ := by
          rw [map_mul φ (adj 0 * (adj 0 * adj 1)), map_mul φ (adj 0), map_inv]
        _ = φ (adj 0 * adj 1) := by rw [hc, mul_inv_cancel_right]
    have hz2 : φ (adj 0 * adj 1) * φ (adj 0 * adj 1) = 1 := mul_eq_one_iff_eq_inv.mpr h2.symm
    have h3 : φ (adj 0 * adj 1) ^ 3 = 1 := by rw [← map_pow, adj01_pow_three, map_one]
    rw [pow_succ, pow_two, hz2, one_mul] at h3
    exact hφ3 h3
  set H : Subgroup GL4 := (Y.subgroupOf C0).map tau with hHdef
  have hH : ψ.range ≤ H := by
    rintro _ ⟨σ, rfl⟩
    exact ⟨φc σ, Subgroup.mem_subgroupOf.mpr (hφY σ), rfl⟩
  rcases max_of_ne hψ3 hH with hH1 | hH2
  · left
    apply le_antisymm
    · intro y hy
      have hyC : y ∈ C0 := hYC hy
      have hmem : tau ⟨y, hyC⟩ ∈ H := ⟨⟨y, hyC⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
      rw [hH1] at hmem
      obtain ⟨σ, hσ⟩ := hmem
      have h1 : tau ((φc σ)⁻¹ * ⟨y, hyC⟩) = 1 := by
        rw [map_mul, map_inv, ← hσ]
        exact inv_mul_cancel _
      have h2 : (φ σ)⁻¹ * y ∈ Subgroup.zpowers u0 := (tau_eq_one_iff _).mp h1
      have e : y = φ σ * ((φ σ)⁻¹ * y) := by group
      rw [e]
      exact mul_mem (Subgroup.mem_sup_left ⟨σ, rfl⟩) (Subgroup.mem_sup_right h2)
    · exact sup_le (by rintro _ ⟨σ, rfl⟩; exact hφY σ) ((Subgroup.zpowers_le).mpr huY)
  · right
    have hYeq : Y = C0 := by
      refine le_antisymm hYC fun g hg => ?_
      have hmem : tau ⟨g, hg⟩ ∈ H := by rw [hH2]; trivial
      obtain ⟨y, hy, hyg⟩ := hmem
      have h1 : tau (y⁻¹ * ⟨g, hg⟩) = 1 := by rw [map_mul, map_inv, hyg, inv_mul_cancel]
      have h2 : (y : GL6)⁻¹ * g ∈ Subgroup.zpowers u0 := (tau_eq_one_iff _).mp h1
      have e : g = (y : GL6) * ((y : GL6)⁻¹ * g) := by group
      rw [e]
      exact mul_mem (Subgroup.mem_subgroupOf.mp hy) ((Subgroup.zpowers_le).mpr huY h2)
    obtain ⟨F, X, hF, hX, hFX⟩ := exists_F5X3
    have hFY : iota F ∈ Y := by rw [hYeq]; exact iota_mem F
    have hXY : iota X ∈ Y := by rw [hYeq]; exact iota_mem X
    refine ⟨by rw [hYeq, card_C0], iota F, hFY, iota X, hXY, ?_, ?_, ?_, ?_⟩
    · rw [orderOf_injective iota iota_injective, hF]
    · rw [orderOf_injective iota iota_injective, hX]
    · intro hx
      have h1 := (tau_eq_one_iff ⟨iota X, iota_mem X⟩).mpr hx
      rw [tau_iota] at h1
      rw [h1, orderOf_one] at hX
      exact absurd hX (by norm_num)
    · rw [← map_mul, hFX, map_mul]

theorem kf_sp4CenGL6 : KF_Sp4CenGL6 := by
  intro Y u φ h3 hfix huY hYC hφY hφ3
  obtain ⟨P, hP⟩ := exists_conj_u0 h3 hfix
  set e : GL6 ≃* GL6 := MulAut.conj P with he
  have heu : e.toMonoidHom u = u0 := by
    rw [MulEquiv.coe_toMonoidHom, he, MulAut.conj_apply, hP]
  have huY' : u0 ∈ Y.map e.toMonoidHom := ⟨u, huY, heu⟩
  have hYC' : Y.map e.toMonoidHom ≤ Subgroup.centralizer {u0} := by
    rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← heu, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.mp (hYC hy)]
  have hφY' : ∀ σ, (e.toMonoidHom.comp φ) σ ∈ Y.map e.toMonoidHom :=
    fun σ => ⟨φ σ, hφY σ, rfl⟩
  have hφ3' : (e.toMonoidHom.comp φ) (adj 0 * adj 1) ≠ 1 := by
    intro h
    apply hφ3
    apply e.injective
    rw [map_one, ← adj01_eq]
    exact h
  rcases main_u0 huY' hYC' hφY' hφ3' with h | ⟨hc, f, hf, x, hx, h5, h3', hxu, hfx⟩
  · left
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [h, Subgroup.map_sup, ← MonoidHom.range_comp, MonoidHom.map_zpowers, heu]
  · right
    obtain ⟨f₀, hf₀, rfl⟩ := hf
    obtain ⟨x₀, hx₀, rfl⟩ := hx
    refine ⟨by rwa [Subgroup.card_map_of_injective e.injective] at hc, f₀, hf₀, x₀, hx₀,
      ?_, ?_, ?_, ?_⟩
    · rwa [orderOf_injective e.toMonoidHom e.injective] at h5
    · rwa [orderOf_injective e.toMonoidHom e.injective] at h3'
    · intro hm
      apply hxu
      have hm' := Subgroup.mem_map_of_mem e.toMonoidHom hm
      rwa [MonoidHom.map_zpowers, heu] at hm'
    · apply e.injective
      have := hfx
      simp only [MulEquiv.coe_toMonoidHom] at this
      rw [map_mul, map_mul, this]

end Cert

end CFSG.RankThree.PartTwo.Sec21.FF81.Sp4Cen
