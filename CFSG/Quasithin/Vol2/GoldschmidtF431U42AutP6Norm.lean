module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutIface

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431
open CFSG.Quasithin.H13.F431.U42 (P45)

section Conj

variable {G : Type} [Group G]

theorem conjSub_card (g : G) (X : Subgroup G) : Nat.card ↥(B6.conjSub g X) = Nat.card ↥X :=
  Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective

theorem conjSub_cenOf (g f : G) : B6.conjSub g (cenOf f) = cenOf (g * f * g⁻¹) := by
  ext x
  rw [B6.mem_conjSub, cenOf, cenOf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc x * (g * f * g⁻¹) = g * (g⁻¹ * x * g * f) * g⁻¹ := by group
      _ = g * (f * (g⁻¹ * x * g)) * g⁻¹ := by rw [h]
      _ = g * f * g⁻¹ * x := by group
  · intro h
    calc g⁻¹ * x * g * f = g⁻¹ * (x * (g * f * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * f * g⁻¹) * x) * g := by rw [h]
      _ = f * (g⁻¹ * x * g) := by group

theorem Conf437.of_conj {z F : G} {T R : Subgroup G} (g : G) (hgz : g * z * g⁻¹ = z)
    (h : Conf437 z F T R) :
    Conf437 z (g * F * g⁻¹) (B6.conjSub g T) (B6.conjSub g R) := by
  obtain ⟨hR, hFz, hFzz, ⟨t, htT, ht2, htc, htF⟩, hall⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [conjSub_card]
    exact hR
  · intro hc
    obtain ⟨c, hc⟩ := isConj_iff.1 hc
    exact hFz (isConj_iff.2 ⟨c * g, by rw [← hc]; group⟩)
  · obtain ⟨c, hc⟩ := isConj_iff.1 hFzz
    refine isConj_iff.2 ⟨c * g⁻¹, ?_⟩
    calc c * g⁻¹ * (g * F * g⁻¹ * z) * (c * g⁻¹)⁻¹ = c * (F * z) * c⁻¹ := by
          have : g * F * g⁻¹ * z = g * F * g⁻¹ * (g * z * g⁻¹) := by rw [hgz]
          rw [this]
          group
      _ = z := hc
  · refine ⟨g * t * g⁻¹, B6.mem_conjSub.2 (by simpa [mul_assoc] using htT), ?_, ?_, ?_⟩
    · calc (g * t * g⁻¹) ^ 2 = g * t ^ 2 * g⁻¹ := by rw [pow_two, pow_two]; group
        _ = 1 := by rw [ht2]; group
    · have e : B6.conjSub g (T ⊓ cenOf t) = B6.conjSub g T ⊓ cenOf (g * t * g⁻¹) := by
        rw [(B6.conjSub g).map_inf, conjSub_cenOf]
      rw [← e, conjSub_card]
      exact htc
    · obtain ⟨c, hc⟩ := isConj_iff.1 htF
      exact isConj_iff.2 ⟨g * c * g⁻¹ * 1, by
        calc g * c * g⁻¹ * 1 * (g * t * g⁻¹) * (g * c * g⁻¹ * 1)⁻¹
            = g * (c * t * c⁻¹) * g⁻¹ := by group
          _ = g * F * g⁻¹ := by rw [hc]⟩
  · intro u hu2 hu1
    have hu2' : (g⁻¹ * u * g) ^ 2 = 1 := by
      calc (g⁻¹ * u * g) ^ 2 = g⁻¹ * u ^ 2 * g := by rw [pow_two, pow_two]; group
        _ = 1 := by rw [hu2]; group
    have hu1' : g⁻¹ * u * g ≠ 1 := fun h1 => hu1 (by
      calc u = g * (g⁻¹ * u * g) * g⁻¹ := by group
        _ = 1 := by rw [h1]; group)
    rcases hall _ hu2' hu1' with hc | hc
    · left
      obtain ⟨c, hc⟩ := isConj_iff.1 hc
      exact isConj_iff.2 ⟨c * g⁻¹, by
        calc c * g⁻¹ * u * (c * g⁻¹)⁻¹ = c * (g⁻¹ * u * g) * c⁻¹ := by group
          _ = z := hc⟩
    · right
      obtain ⟨c, hc⟩ := isConj_iff.1 hc
      exact isConj_iff.2 ⟨g * c * g⁻¹, by
        calc g * c * g⁻¹ * u * (g * c * g⁻¹)⁻¹ = g * (c * (g⁻¹ * u * g) * c⁻¹) * g⁻¹ := by group
          _ = g * F * g⁻¹ := by rw [hc]⟩

end Conj

end CFSG.Quasithin.H13.F431.U42Aut
