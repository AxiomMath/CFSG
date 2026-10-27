module

public import CFSG.Walter.Bender1970.S3.Basic

public section

namespace CFSG.Walter

open CFSG.GorensteinWalter

variable {G : Type} [Group G] [Finite G]

theorem exists_involution_not_conj_of_centralizer_le (hG : BenderCounterexample G) {t : G}
    (ht : orderOf t = 2) {H : Subgroup G} (hHtop : H ≠ ⊤)
    (hCH : Subgroup.centralizer ({t} : Set G) ≤ H) :
    ∃ y ∈ H, orderOf y = 2 ∧ ∀ h ∈ H, h * t * h⁻¹ ≠ y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htH : t ∈ H := hCH (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  by_contra hcon
  push Not at hcon
  apply hG.not_stronglyEmbedded
  refine ⟨H, hHtop, ?_, fun g hg => ?_⟩
  · have h2 : orderOf (⟨t, htH⟩ : H) ∣ Nat.card H := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, ht] at h2
    exact even_iff_two_dvd.mpr h2
  · by_contra hodd
    rw [Nat.not_odd_iff_even] at hodd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(H ⊓ H.map (MulAut.conj g).toMonoidHom))
      2 (even_iff_two_dvd.mp hodd)
    have hxs : orderOf (x : G) = 2 := by rw [← hx, Subgroup.orderOf_coe]
    obtain ⟨hxH, hxHg⟩ := x.2
    obtain ⟨y, hyH, hyx⟩ := hxHg
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
    have hy : orderOf y = 2 := by
      rw [← hxs, ← hyx, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
    obtain ⟨h, hh, hht⟩ := hcon (x : G) hxH hxs
    obtain ⟨h', hh', hh't⟩ := hcon y hyH hy
    have hc : h⁻¹ * g * h' ∈ Subgroup.centralizer ({t} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : g * (h' * t * h'⁻¹) * g⁻¹ = h * t * h⁻¹ := by rw [hh't, hyx, hht]
      calc h⁻¹ * g * h' * t = h⁻¹ * (g * (h' * t * h'⁻¹) * g⁻¹) * (g * h') := by group
        _ = h⁻¹ * (h * t * h⁻¹) * (g * h') := by rw [h1]
        _ = t * (h⁻¹ * g * h') := by group
    have hgH : g = h * (h⁻¹ * g * h') * h'⁻¹ := by group
    exact hg (hgH ▸ H.mul_mem (H.mul_mem hh (hCH hc)) (H.inv_mem hh'))

theorem bender1970_3_2 (hG : BenderCounterexample G) {t : G} (ht : orderOf t = 2)
    {H : Subgroup G} (hH : H ∈ benderM t) :
    ∃ x ∈ H, ∃ y ∈ H, orderOf x = 2 ∧ orderOf y = 2 ∧ ∀ h ∈ H, h * x * h⁻¹ ≠ y := by
  obtain ⟨y, hyH, hy, hne⟩ := exists_involution_not_conj_of_centralizer_le hG ht
    (ne_top_of_mem_benderM hH) (centralizer_le_of_mem_benderM hH)
  exact ⟨t, mem_of_mem_benderM hH, y, hyH, ht, hy, hne⟩

end CFSG.Walter
