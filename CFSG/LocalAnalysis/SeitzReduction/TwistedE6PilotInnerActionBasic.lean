module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotInnerActionCore

public section

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.EvenSmallLie
open CFSG.ComponentClassification (OuterAutomorphisms.inner)
open CFSG.SeitzReduction.E6Pilot (normalizerAut restrictAut card_eq_two_mul_card_range
  map_conj_inf_centralizer mulAut_conj_injective_of_center normalizerAut_of_mem
  normalizerAut_eq_one_iff coe_symm_normalizerAut_apply)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_inner_of_not_dvd_of_eq (hset : StandardSetting G L) {C : Type*} [Group C]
    (e : L ≃* C) (hZ : center C = ⊥) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {x : C} {g : G} (hg : g⁻¹ * t * g = (e.symm x : G) ∨ g⁻¹ * t * g = t * (e.symm x : G))
    (hne : g⁻¹ * t * g ≠ t)
    (hcmp : ∀ β : MulAut C, orderOf β = 2 → β ∉ OuterAutomorphisms.inner C →
      ¬ Nat.card (centralizer ({x} : Set C)) ∣
        Nat.card (centralizer ({β} : Set (MulAut C)))) :
    ∃ w' ∈ CFSG.conjugate L g, ∀ l ∈ CFSG.conjugate L g, t * l * t⁻¹ = w' * l * w'⁻¹ := by
  have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hKt ▸ mem_zpowers t
  have htC : t ∈ centralizer (L : Set G) := htK.1
  have hN : centralizer ({t} : Set G) ≤ normalizer (L : Set G) :=
    centralizer_le_normalizer_of_standard hset.standard htC ht
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  set w : G := (e.symm x : G) with hwdef
  have hwL : w ∈ L := (e.symm x).2
  set t' := g⁻¹ * t * g with ht'def
  have htt' : t ∈ centralizer ({t'} : Set G) :=
    EPilot.mem_centralizer_of_eq_or_eq_mul htC hwL hg
  set s := g * t * g⁻¹ with hsdef
  have hst : s ∈ centralizer ({t} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have h := mem_centralizer_singleton_iff.1 htt'
    rw [ht'def] at h
    calc s * t = g * (t * (g⁻¹ * t * g)) * g⁻¹ := by rw [hsdef]; group
      _ = g * ((g⁻¹ * t * g) * t) * g⁻¹ := by rw [h]
      _ = t * s := by rw [hsdef]; group
  set Y := centralizer ({t} : Set G) ⊓ centralizer ({t'} : Set G) with hYdef
  set Y' := centralizer ({t} : Set G) ⊓ centralizer ({s} : Set G) with hY'def
  have hYt : Y ≤ centralizer ({t} : Set G) := inf_le_left
  have hY't : Y' ≤ centralizer ({t} : Set G) := inf_le_left
  have hYN : Y ≤ normalizer (L : Set G) := hYt.trans hN
  have hY'N : Y' ≤ normalizer (L : Set G) := hY't.trans hN
  have htY : t ∈ Y := mem_inf.2 ⟨mem_centralizer_singleton_iff.2 rfl, htt'⟩
  have htY' : t ∈ Y' := mem_inf.2 ⟨mem_centralizer_singleton_iff.2 rfl,
    (EPilot.mem_centralizer_singleton_comm).1 hst⟩
  have hYY' : Nat.card Y = Nat.card Y' := by
    have e1 : g * t' * g⁻¹ = t := by rw [ht'def]; group
    have h : Y.map (MulAut.conj g).toMonoidHom = Y' := by
      rw [hYdef, hY'def, map_conj_inf_centralizer, e1, inf_comm]
    rw [← h, card_map_of_injective (MulAut.conj g).injective]
  have hρ : Nat.card (restrictAut e hYN).range = Nat.card (restrictAut e hY'N).range := by
    have h1 := card_eq_two_mul_card_range e ht hKt hYN hYt htY
    have h2 := card_eq_two_mul_card_range e ht hKt hY'N hY't htY'
    omega
  have hle1 : (centralizer ({x} : Set C)).map (MulAut.conj : C →* MulAut C) ≤
      (restrictAut e hYN).range := by
    rintro _ ⟨c, hc, rfl⟩
    have hcx : c * x = x * c := mem_centralizer_singleton_iff.1 hc
    set l := e.symm c with hldef
    have hlw : (l : G) * w = w * l := by
      have h := congrArg (fun y => ((e.symm y : L) : G)) hcx
      simp only [map_mul, Subgroup.coe_mul] at h
      exact h
    have hlt : (l : G) ∈ centralizer ({t} : Set G) := le_centralizer_of_mem_centralizer htC l.2
    have hlt' : (l : G) ∈ centralizer ({t'} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      rcases hg with h | h
      · rw [h, hlw]
      · rw [h, ← mul_assoc, (mem_centralizer_singleton_iff.1 hlt), mul_assoc, hlw, mul_assoc]
    have hlY : (l : G) ∈ Y := mem_inf.2 ⟨hlt, hlt'⟩
    refine ⟨⟨l, hlY⟩, ?_⟩
    change normalizerAut e (Subgroup.inclusion hYN ⟨l, hlY⟩) = MulAut.conj c
    rw [normalizerAut_of_mem e _ l rfl, hldef, MulEquiv.apply_symm_apply]
  have hdvd1 : Nat.card (centralizer ({x} : Set C)) ∣ Nat.card (restrictAut e hYN).range := by
    rw [← card_map_of_injective (mulAut_conj_injective_of_center hZ)]
    exact card_dvd_of_le hle1
  set β := normalizerAut e ⟨s, hN hst⟩ with hβdef
  have hle2 : (restrictAut e hY'N).range ≤ centralizer ({β} : Set (MulAut C)) := by
    rintro _ ⟨y, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have hys : (y : G) * s = s * y := mem_centralizer_singleton_iff.1 (mem_inf.1 y.2).2
    change normalizerAut e (Subgroup.inclusion hY'N y) * β =
      β * normalizerAut e (Subgroup.inclusion hY'N y)
    rw [hβdef, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hys
  have hdvd : Nat.card (centralizer ({x} : Set C)) ∣
      Nat.card (centralizer ({β} : Set (MulAut C))) :=
    (hdvd1.trans (hρ ▸ dvd_refl _)).trans (card_dvd_of_le hle2)
  have hs2 : s * s = 1 := by
    calc s * s = g * (t * t) * g⁻¹ := by rw [hsdef]; group
      _ = 1 := by rw [ht2]; group
  have hβ2 : orderOf β = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [hβdef, ← map_pow]
      have : (⟨s, hN hst⟩ : normalizer (L : Set G)) ^ 2 = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow, sq, hs2, Subgroup.coe_one])
      rw [this, map_one]
    · intro h1
      rw [hβdef, normalizerAut_eq_one_iff] at h1
      have hsK : s ∈ zpowers t := hKt ▸ mem_inf.2 ⟨h1, hst⟩
      rcases F4Pilot.eq_one_or_eq_of_mem_zpowers ht hsK with h | h
      · have : t = 1 := by
          have e1 : t = g⁻¹ * s * g := by rw [hsdef]; group
          rw [e1, h]
          group
        rw [this, orderOf_one] at ht
        exact absurd ht (by norm_num)
      · apply hne
        have h' : g * t * g⁻¹ = t := h
        calc g⁻¹ * t * g = g⁻¹ * (g * t * g⁻¹) * g := by rw [h']
          _ = t := by group
  have hβI : β ∈ OuterAutomorphisms.inner C := by
    by_contra hβI
    exact hcmp β hβ2 hβI hdvd
  obtain ⟨c, hc⟩ := hβI
  set l := e.symm c with hldef
  have hsl : ∀ y ∈ L, s * y * s⁻¹ = (l : G) * y * (l : G)⁻¹ := by
    intro y hy
    have h := coe_symm_normalizerAut_apply e ⟨s, hN hst⟩ (e ⟨y, hy⟩)
    rw [← hβdef, ← hc, MulAut.conj_apply, MulEquiv.symm_apply_apply, map_mul, map_mul, map_inv,
      MulEquiv.symm_apply_apply] at h
    simpa [hldef] using h.symm
  refine ⟨g⁻¹ * l * g, EPilot.conj_mem_conjugate l.2 g, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  have hy' : (MulAut.conj g⁻¹).toMonoidHom y = g⁻¹ * y * g := by
    simp
  rw [hy']
  have et : t = g⁻¹ * s * g := by rw [hsdef]; group
  calc t * (g⁻¹ * y * g) * t⁻¹ = g⁻¹ * (s * y * s⁻¹) * g := by rw [et]; group
    _ = g⁻¹ * ((l : G) * y * (l : G)⁻¹) * g := by rw [hsl y hy]
    _ = g⁻¹ * l * g * (g⁻¹ * y * g) * (g⁻¹ * l * g)⁻¹ := by group

theorem exists_inner_of_two_pow_dvd_of_eq (hset : StandardSetting G L) {C : Type*} [Group C]
    (e : L ≃* C) (hZ : center C = ⊥) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) (a : ℕ)
    (hB : ∀ β : MulAut C, orderOf β = 2 → β ∉ OuterAutomorphisms.inner C →
      ¬ 2 ^ a ∣ Nat.card (centralizer ({β} : Set (MulAut C))))
    {x : C} (hx : 2 ^ a ∣ Nat.card (centralizer ({x} : Set C))) {g : G}
    (hg : g⁻¹ * t * g = (e.symm x : G) ∨ g⁻¹ * t * g = t * (e.symm x : G))
    (hne : g⁻¹ * t * g ≠ t) :
    ∃ w' ∈ CFSG.conjugate L g, ∀ l ∈ CFSG.conjugate L g, t * l * t⁻¹ = w' * l * w'⁻¹ :=
  exists_inner_of_not_dvd_of_eq hset e hZ ht hKt hg hne fun β hβ hβI hdvd =>
    hB β hβ hβI (hx.trans hdvd)

end CFSG.SeitzReduction.TwistedE6Pilot
