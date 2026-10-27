module

public import CFSG.Timmesfeld.Bridge.Asc72Basic

import CFSG.GroupTheory.InvolutionClassProducts
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore
public import Certificates.Certificate43

public section

namespace CFSG.OddTranspositions.PartThree.EightEight

open CFSG.Timmesfeld.Bridge.Asc72
open CFSG.GroupTheory

variable {X : Type*} [Group X] {E : Set X}

theorem mk_mul_self_eq_one_of_mem (hS : Setup X E) {x : X} (hx : x ∈ E) :
    QuotientGroup.mk' (derivedSeries X 2) x * QuotientGroup.mk' (derivedSeries X 2) x = 1 := by
  rw [← map_mul, hS.oddT.mul_self_eq_one hx, map_one]

theorem closure_mk_image_eq_top (hS : Setup X E) :
    Subgroup.closure (QuotientGroup.mk' (derivedSeries X 2) '' E) = ⊤ := by
  rw [← MonoidHom.map_closure, hS.gen,
    Subgroup.map_top_of_surjective (QuotientGroup.mk' (derivedSeries X 2))
      (QuotientGroup.mk'_surjective (derivedSeries X 2))]

theorem derivedSeries_two_quotient_eq_bot :
    derivedSeries (X ⧸ derivedSeries X 2) 2 = ⊥ := by
  rw [← map_derivedSeries_eq (QuotientGroup.mk'_surjective (derivedSeries X 2)) 2]
  apply le_antisymm _ bot_le
  intro z hz
  rw [Subgroup.mem_bot]
  rw [Subgroup.mem_map] at hz
  obtain ⟨x, hx, rfl⟩ := hz
  exact (QuotientGroup.eq_one_iff x).mpr hx

theorem orderOf_dvd_two_or_odd_mk_mul (hS : Setup X E) {x y : X} (hx : x ∈ E) (hy : y ∈ E) :
    orderOf (QuotientGroup.mk' (derivedSeries X 2) x *
        QuotientGroup.mk' (derivedSeries X 2) y) ∣ 2 ∨
      Odd (orderOf (QuotientGroup.mk' (derivedSeries X 2) x *
        QuotientGroup.mk' (derivedSeries X 2) y)) := by
  have hdvd : orderOf (QuotientGroup.mk' (derivedSeries X 2) (x * y)) ∣ orderOf (x * y) :=
    orderOf_map_dvd (QuotientGroup.mk' (derivedSeries X 2)) (x * y)
  rw [← map_mul]
  rcases hS.oddT.2 x hx y hy with h | h
  · exact Or.inl (hdvd.trans h)
  · exact Or.inr (Odd.of_dvd_nat h hdvd)

theorem odd_orderOf_mk_mul (hS : Setup X E) {x y : X} (hx : x ∈ E) (hy : y ∈ E) :
    Odd (orderOf (QuotientGroup.mk' (derivedSeries X 2) (x * y))) := by
  obtain ⟨x₀, hx₀⟩ := hS.nonempty
  have hsq : ∀ e ∈ QuotientGroup.mk' (derivedSeries X 2) '' E, e * e = 1 := by
    rintro _ ⟨z, hz, rfl⟩
    exact mk_mul_self_eq_one_of_mem hS hz
  have hprod : ∀ e ∈ QuotientGroup.mk' (derivedSeries X 2) '' E,
      ∀ e' ∈ QuotientGroup.mk' (derivedSeries X 2) '' E,
      orderOf (e * e') ∣ 2 ∨ Odd (orderOf (e * e')) := by
    rintro _ ⟨z, hz, rfl⟩ _ ⟨w, hw, rfl⟩
    exact orderOf_dvd_two_or_odd_mk_mul hS hz hw
  have hodd := odd_orderOf_mul_of_isConj
    (T := QuotientGroup.mk' (derivedSeries X 2) '' E)
    (t := QuotientGroup.mk' (derivedSeries X 2) x₀) ⟨x₀, hx₀, rfl⟩
    (fun e he => by
      rcases he with ⟨z, hz, rfl⟩
      exact (QuotientGroup.mk' (derivedSeries X 2)).map_isConj (hS.isConj hx₀ hz))
    hsq (closure_mk_image_eq_top hS) derivedSeries_two_quotient_eq_bot hprod
    (QuotientGroup.mk' (derivedSeries X 2) x) ⟨x, hx, rfl⟩
    (QuotientGroup.mk' (derivedSeries X 2) y) ⟨y, hy, rfl⟩
  rwa [← map_mul] at hodd

theorem mk_eq_mk_of_commute (hS : Setup X E) {x y : X} (hx : x ∈ E) (hy : y ∈ E)
    (hxy : Commute x y) :
    QuotientGroup.mk' (derivedSeries X 2) x = QuotientGroup.mk' (derivedSeries X 2) y := by
  let π : X →* X ⧸ derivedSeries X 2 := QuotientGroup.mk' (derivedSeries X 2)
  have hodd : Odd (orderOf (π (x * y))) := odd_orderOf_mk_mul hS hx hy
  have hsq : (π (x * y)) ^ 2 = 1 := by
    have hxy2 : (x * y) * (x * y) = 1 := by
      rw [← pow_two, hxy.mul_pow 2, pow_two x, pow_two y,
        hS.oddT.mul_self_eq_one hx, hS.oddT.mul_self_eq_one hy, mul_one]
    rw [pow_two, ← map_mul, hxy2, map_one]
  have hdvd : orderOf (π (x * y)) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  have hord : orderOf (π (x * y)) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  have hmul : π (x * y) = 1 := by
    rwa [orderOf_eq_one_iff] at hord
  have h1 : π x * π y = 1 := by
    rw [← map_mul]
    exact hmul
  have hysq : π y * π y = 1 := by
    rw [← map_mul, hS.oddT.mul_self_eq_one hy, map_one]
  have hyinv : (π y)⁻¹ = π y := inv_eq_of_mul_eq_one_right hysq
  rw [eq_inv_of_mul_eq_one_left h1, hyinv]

theorem mul_mem_derivedSeries_two_of_commute (hS : Setup X E) {x y : X} (hx : x ∈ E)
    (hy : y ∈ E) (hxy : Commute x y) : x * y ∈ derivedSeries X 2 := by
  have hmk := mk_eq_mk_of_commute hS hx hy hxy
  have h1 : QuotientGroup.mk' (derivedSeries X 2) (x * y) = 1 := by
    rw [map_mul, hmk, ← map_mul, hS.oddT.mul_self_eq_one hy, map_one]
  exact (QuotientGroup.eq_one_iff (x * y)).mp h1

theorem exists_mk_ne_of_derivedSeries_ne (hS : Setup X E)
    (hne : derivedSeries X 1 ≠ derivedSeries X 2) :
    ∃ x ∈ E, ∃ y ∈ E,
      QuotientGroup.mk' (derivedSeries X 2) x ≠ QuotientGroup.mk' (derivedSeries X 2) y := by
  by_contra h
  push Not at h
  obtain ⟨x₀, hx₀⟩ := hS.nonempty
  let π : X →* X ⧸ derivedSeries X 2 := QuotientGroup.mk' (derivedSeries X 2)
  have hsingle : ∀ e ∈ E, π e = π x₀ := fun e he => h e he x₀ hx₀
  have hT : π '' E = {π x₀} := by
    ext z
    constructor
    · rintro ⟨e, he, rfl⟩
      exact hsingle e he
    · rintro rfl
      exact ⟨x₀, hx₀, rfl⟩
  have hzp : Subgroup.zpowers (π x₀) = ⊤ := by
    rw [Subgroup.zpowers_eq_closure, ← hT, ← MonoidHom.map_closure, hS.gen,
      Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective (derivedSeries X 2))]
  have hY : IsMulCommutative (X ⧸ derivedSeries X 2) := by
    have htop : IsMulCommutative (⊤ : Subgroup (X ⧸ derivedSeries X 2)) := by
      rw [← hzp]
      exact Subgroup.zpowers_isMulCommutative (π x₀)
    exact Function.Surjective.isMulCommutative
      (f := Subgroup.subtype (⊤ : Subgroup (X ⧸ derivedSeries X 2)))
      (fun x => ⟨⟨x, Subgroup.mem_top x⟩, rfl⟩) htop
  have hbot : derivedSeries (X ⧸ derivedSeries X 2) 1 = ⊥ := by
    rw [derivedSeries_one]
    exact (commutator_eq_bot_iff (X ⧸ derivedSeries X 2)).mpr hY
  have hmap : (derivedSeries X 1).map π = ⊥ := by
    rw [map_derivedSeries_eq (QuotientGroup.mk'_surjective (derivedSeries X 2)) 1]
    exact hbot
  have hle : derivedSeries X 1 ≤ derivedSeries X 2 := by
    have h := (Subgroup.map_eq_bot_iff (f := π) (derivedSeries X 1)).mp hmap
    rwa [QuotientGroup.ker_mk'] at h
  have hle' : derivedSeries X 2 ≤ derivedSeries X 1 := by
    rw [derivedSeries_succ X 1]
    exact Subgroup.commutator_le_self _
  exact hne (le_antisymm hle hle')

end CFSG.OddTranspositions.PartThree.EightEight
