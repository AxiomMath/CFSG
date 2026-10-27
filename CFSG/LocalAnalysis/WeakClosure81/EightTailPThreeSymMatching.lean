module

public import CFSG.LocalAnalysis.WeakClosure81.EightTailPThreeSymDefs
import CFSG.LocalAnalysis.WeakClosure81.EightTailPThreeSymA
import CFSG.Timmesfeld.Bridge.Asc72Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Equiv Equiv.Perm CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.Timmesfeld.Bridge.Asc72

theorem symT_matching {Y : Type} [Group Y] [Finite Y] {m : ℕ}
    {e : Y ⧸ fusionOddCore Y ≃* Perm (Fin m)} {t : Y} {P : Sylow 2 Y}
    (h : SymSetting e t P) :
    Set.InjOn (symPi e) (symT t (P : Subgroup Y)) ∧
      (∀ x ∈ symT t (P : Subgroup Y), ∀ y ∈ symT t (P : Subgroup Y), x * y = y * x) ∧
      (∀ x ∈ symT t (P : Subgroup Y), (symPi e x).IsSwap) ∧
      (∀ a b : Fin m, a ≠ b → Equiv.swap a b ∈ (P : Subgroup Y).map (symPi e) →
        Equiv.swap a b ∈ symPi e '' symT t (P : Subgroup Y)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker : (symPi e).ker = fusionOddCore Y := by
    rw [symPi]
    ext z
    simp [MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  have hP2 : IsPGroup 2 (P : Subgroup Y) := P.isPGroup'
  have htriv : (P : Subgroup Y) ⊓ fusionOddCore Y = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxP, hxO⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hP2) (⟨x, hxP⟩ : ↥(P : Subgroup Y))
    rw [Subgroup.orderOf_mk] at hk
    have hdvd : orderOf x ∣ Nat.card (fusionOddCore Y) :=
      Subgroup.orderOf_dvd_natCard (fusionOddCore Y) hxO
    have hodd : Odd (orderOf x) :=
      Odd.of_dvd_nat (CFSG.EvenSporadicStandard.Fin76b.odd_natCard_fusionOddCore Y) hdvd
    have hk1 : orderOf x = 1 := by
      rcases k with _ | k
      · simpa using hk
      · exfalso
        have heven : Even (orderOf x) := by
          rw [hk, pow_succ, mul_comm]
          exact even_iff_two_dvd.mpr (dvd_mul_right 2 _)
        exact (Nat.not_even_iff_odd.mpr hodd) heven
    rw [Subgroup.mem_bot, orderOf_eq_one_iff.mp hk1]
  have himgD : symPi e '' {y : Y | IsConj t y} =
      {y : Perm (Fin m) | IsConj (symPi e t) y} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨u, rfl⟩ := isConj_iff.mp hx
      exact isConj_iff.mpr ⟨symPi e u, by rw [map_mul, map_mul, map_inv]⟩
    · intro hy
      obtain ⟨c, hc⟩ := isConj_iff.mp hy
      obtain ⟨u, hu⟩ := w85g_symPi_surjective e c
      have hu' : symPi e u = c := hu
      refine ⟨u * t * u⁻¹, isConj_iff.mpr ⟨u, rfl⟩, ?_⟩
      rw [map_mul, map_mul, map_inv, hu']
      exact hc
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    have hxO : x⁻¹ * y ∈ fusionOddCore Y := by
      have h1 : symPi e (x⁻¹ * y) = 1 := by
        rw [map_mul, map_inv, hxy, inv_mul_cancel]
      rwa [← MonoidHom.mem_ker, hker] at h1
    have hxQ : x⁻¹ * y ∈ (P : Subgroup Y) :=
      (P : Subgroup Y).mul_mem ((P : Subgroup Y).inv_mem hx.2) hy.2
    have hbot : x⁻¹ * y ∈ (P : Subgroup Y) ⊓ fusionOddCore Y :=
      Subgroup.mem_inf.mpr ⟨hxQ, hxO⟩
    rw [htriv, Subgroup.mem_bot] at hbot
    exact inv_mul_eq_one.mp hbot
  · intro x hx y hy
    exact h.oddClass.2.1.commute_of_isPGroup hP2 hx.1 hy.1 hx.2 hy.2
  · intro x hx
    obtain ⟨u, rfl⟩ := isConj_iff.mp hx.1
    have hconj : symPi e (u * t * u⁻¹) = symPi e u * symPi e t * (symPi e u)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    rw [hconj]
    exact (b5_FiveSixPart_isSwap_conj_iff (symPi e u) (symPi e t)).mp h.swap
  · intro a b hab hσ
    obtain ⟨d₁, hd₁Q, hd₁π⟩ := Subgroup.mem_map.mp hσ
    obtain ⟨i, j, hij, hπt⟩ := h.swap
    have hconjab : IsConj (symPi e t) (Equiv.swap a b) := by
      rw [hπt]
      exact Equiv.Perm.isConj_swap hij hab
    have hmem : Equiv.swap a b ∈ symPi e '' {y : Y | IsConj t y} := by
      rw [himgD]
      exact hconjab
    obtain ⟨d₀, hd₀D, hd₀π⟩ := hmem
    have hxO : d₀⁻¹ * d₁ ∈ fusionOddCore Y := by
      have h1 : symPi e (d₀⁻¹ * d₁) = 1 := by
        rw [map_mul, map_inv, hd₀π, hd₁π]
        simp
      rwa [← MonoidHom.mem_ker, hker] at h1
    have hd₀inv : d₀ * d₀ = 1 := h.oddClass.2.1.mul_self_eq_one hd₀D
    have hd₁inv : d₁ * d₁ = 1 := by
      have hmem' : d₁ * d₁ ∈ (P : Subgroup Y) ⊓ fusionOddCore Y := by
        refine Subgroup.mem_inf.mpr ⟨(P : Subgroup Y).mul_mem hd₁Q hd₁Q, ?_⟩
        have h1 : symPi e (d₁ * d₁) = 1 := by
          rw [map_mul, hd₁π, Equiv.swap_mul_self]
        rwa [← MonoidHom.mem_ker, hker] at h1
      rwa [htriv, Subgroup.mem_bot] at hmem'
    have hcO : d₀ * d₁ ∈ fusionOddCore Y := by
      rwa [inv_eq_of_mul_eq_one_right hd₀inv] at hxO
    obtain ⟨o, _, hoo⟩ := w85g_exists_conj_mem_fusionOddCore hd₀inv hd₁inv hcO
    have hd₁D : IsConj t d₁ := by
      obtain ⟨u, hu⟩ := isConj_iff.mp hd₀D
      refine isConj_iff.mpr ⟨o * u, ?_⟩
      rw [← hoo, ← hu]
      group
    exact ⟨d₁, ⟨hd₁D, hd₁Q⟩, hd₁π⟩

theorem symT_image_eq_swaps {Y : Type} [Group Y] [Finite Y] {m : ℕ}
    {e : Y ⧸ fusionOddCore Y ≃* Perm (Fin m)} {t : Y} {P : Sylow 2 Y} (h : SymSetting e t P) :
    symPi e '' symT t (P : Subgroup Y) =
      {σ : Perm (Fin m) | σ.IsSwap ∧ σ ∈ (P : Subgroup Y).map (symPi e)} := by
  have hmatch := symT_matching h
  ext σ
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hmatch.2.2.1 x hx, Subgroup.mem_map_of_mem (symPi e) hx.2⟩
  · rintro ⟨hσ, hσP⟩
    obtain ⟨a, b, hab, rfl⟩ := hσ
    exact hmatch.2.2.2 a b hab hσP

end CFSG.LocalAnalysis.WeakClosure81

end
