module

public import CFSG.LocalAnalysis.WeakClosure81.W16LBorelSz
public import CFSG.LocalAnalysis.WeakClosure81.W16LBorelU3
import CFSG.GroupTheory.OddOrderLift
import CFSG.LocalAnalysis.WeakClosure81.TwelveSubgroup
import CFSG.LocalAnalysis.EvenBN.GMSK.CatSporadicBenderLarge
import CFSG.LocalAnalysis.ComponentClassification.AS81L34Transport
public import CFSG.LocalAnalysis.WeakClosure81.W16QDInputs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open
open CFSG.GH74.Uniqueness.Bender
open Subgroup

theorem borel166Conclusion_of_map {X K : Type} [Group X] [Finite X] [Group K] (π : X →* K)
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center X)
    (hodd : Odd (Nat.card π.ker)) {Y P : Subgroup X} (hYP : Y ≤ P) (hP : IsPGroup 2 P)
    (h : Borel166Conclusion (Y.map π) (P.map π)) : Borel166Conclusion Y P := by
  classical
  obtain ⟨b, hbY, hbP, hbodd, hirr, hfpf⟩ := h
  obtain ⟨g, hg, hgodd⟩ := CFSG.GroupTheory.exists_odd_orderOf_preimage π hπ hbodd
  have hnormP : g ∈ Subgroup.normalizer (P : Set X) :=
    CFSG.ComponentClassification.AS81.mem_normalizer_of_map π hcen hodd hP (by rw [hg]; exact hbP)
  have hnormY : g ∈ Subgroup.normalizer (Y : Set X) :=
    CFSG.ComponentClassification.AS81.mem_normalizer_of_map π hcen hodd (hP.to_le hYP)
      (by rw [hg]; exact hbY)
  have hInj : ∀ {y x : X}, y ∈ P → x ∈ P → π y = π x → y = x :=
    fun hy hx hyx =>
      CFSG.ComponentClassification.AS81.eq_of_map_eq_of_isPGroup π hodd hP hy hx hyx
  refine ⟨g, hnormY, hnormP, hgodd, ?_, ?_⟩
  ·
    intro P₀ hYP₀ hP₀P hinv
    have hinvmap : ∀ x ∈ P₀.map π, b * x * b⁻¹ ∈ P₀.map π := by
      rintro _ ⟨x, hxP₀, rfl⟩
      have h1 : π (g * x * g⁻¹) = b * π x * b⁻¹ := by
        simp only [map_mul, map_inv, hg]
      rw [← h1]
      exact Subgroup.mem_map_of_mem π (hinv x hxP₀)
    rcases hirr (P₀.map π) (Subgroup.map_mono hYP₀) (Subgroup.map_mono hP₀P) hinvmap with
      hEq | hEq
    · left
      refine le_antisymm ?_ hYP₀
      intro x hxP₀
      have hxmap : π x ∈ Y.map π := by
        rw [← hEq]
        exact Subgroup.mem_map_of_mem π hxP₀
      obtain ⟨y, hyY, hyx⟩ := Subgroup.mem_map.mp hxmap
      have heq : y = x := hInj (hYP hyY) (hP₀P hxP₀) hyx
      rwa [← heq]
    · right
      refine le_antisymm hP₀P ?_
      intro x hxP
      have hxmap : π x ∈ P₀.map π := by
        rw [hEq]
        exact Subgroup.mem_map_of_mem π hxP
      obtain ⟨y, hyP₀, hyx⟩ := Subgroup.mem_map.mp hxmap
      have heq : y = x := hInj (hP₀P hyP₀) hxP hyx
      rwa [heq] at hyP₀
  ·
    intro x hxP hdx
    have hmem : b * π x * b⁻¹ * (π x)⁻¹ ∈ Y.map π := by
      have h1 : π (g * x * g⁻¹ * x⁻¹) = b * π x * b⁻¹ * (π x)⁻¹ := by
        simp only [map_mul, map_inv, hg]
      rw [← h1]
      exact Subgroup.mem_map_of_mem π hdx
    obtain ⟨y, hyY, hyx⟩ :=
      Subgroup.mem_map.mp (hfpf (π x) (Subgroup.mem_map_of_mem π hxP) hmem)
    have heq : y = x := hInj (hYP hyY) hxP hyx
    rwa [heq] at hyY

section Certified


theorem borel166Input_holds : Borel166Input := by
  classical
  intro X _ _ Y P n _ hY hYe hYP hP hidx hX
  change Borel166Conclusion Y P
  rcases hX with hSz | hU3
  · have hB : BenderType X n 2 1 := rankOne_benderType_sz hSz
    let Q : Sylow 2 X := hP.toSylow hidx
    have hQ : (Q : Subgroup X) = P := IsPGroup.toSylow_coe hP hidx
    have hconcl : Borel166Conclusion Y (Q : Subgroup X) :=
      borel166Conclusion_of_benderType_sz hB Q hY hYe (by rw [hQ]; exact hYP)
    rwa [hQ] at hconcl
  ·
    let Z := Subgroup.center X
    let π : X →* X ⧸ Z := QuotientGroup.mk' Z
    have hZodd : Odd (Nat.card Z) := by
      change Odd (Nat.card (Subgroup.center X))
      rcases (Nat.dvd_prime Nat.prime_three).1 hU3.2.2 with h | h <;> rw [h] <;> decide
    have hoddker : Odd (Nat.card π.ker) := by
      rw [QuotientGroup.ker_mk']
      exact hZodd
    have hB : BenderType (X ⧸ Z) n 3 ((2 ^ n + 1) / Nat.gcd 3 (2 ^ n + 1)) :=
      CFSG.LocalAnalysis.EvenBN.GMSK.SporadicBender.benderType_of_lieModel_PSU3 hU3.2.1
    let Q : Sylow 2 X := hP.toSylow hidx
    have hQ : (Q : Subgroup X) = P := IsPGroup.toSylow_coe hP hidx
    let Qbar : Sylow 2 (X ⧸ Z) := Sylow.mapSurjective (QuotientGroup.mk'_surjective Z) Q
    have hQbar : (Qbar : Subgroup (X ⧸ Z)) = P.map π := by
      change (Q : Subgroup X).map π = P.map π
      rw [hQ]
    have hYcard : Nat.card (Y.map π) = 2 ^ n := by
      rw [CFSG.ComponentClassification.AS81.card_map_of_isPGroup π hoddker (hP.to_le hYP), hY]
    have hYe' : IsElemAbelian 2 (Y.map π) := hYe.map π
    have hYle : Y.map π ≤ (Qbar : Subgroup (X ⧸ Z)) := by
      rw [hQbar]
      exact Subgroup.map_mono hYP
    have hconcl : Borel166Conclusion (Y.map π) (Qbar : Subgroup (X ⧸ Z)) :=
      borel166Conclusion_of_benderType_u3 hB Qbar hYcard hYe' hYle
    have hconcl' : Borel166Conclusion (Y.map π) (P.map π) := by
      rwa [hQbar] at hconcl
    exact borel166Conclusion_of_map π (QuotientGroup.mk'_surjective Z)
      (le_of_eq (QuotientGroup.ker_mk' Z)) hoddker hYP hP hconcl'

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end
