module

public import CFSG.RankThree.GF2n.Tim78S412Weyl

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n CFSG.Timmesfeld
open CFSG.Timmesfeld.ARS.NaturalModule CFSG.Timmesfeld.RankOne
open scoped commutatorElement

namespace PairData

variable {G : Type} [Group G] {P B : Subgroup G} {g : G} {n : ℕ} (D : PairData P B g n)

theorem transport {w τ : ↥(P ⊔ conjSubgroup g P)} {c : (GaloisField 2 n)ˣ}
    (hw : D.φ w = weylElt (GaloisField 2 n)) (hτ : D.φ τ = diagElt c) {l : G}
    (hl : l ∈ B ⊔ conjSubgroup g B) (hlτ : (τ : G) * l = l * τ) :
    (τ : G) * ((w : G) * l * (w : G)⁻¹) = ((w : G) * l * (w : G)⁻¹) * τ := by
  have hκ : D.φ (w⁻¹ * τ * w * τ) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, hw, hτ, weyl_diag_weyl', diagElt_mul_diagElt,
      inv_mul_cancel, diagElt_one]
  have hκ' := Subgroup.mem_centralizer_iff.mp ((D.ker _).mp hκ) l hl
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hκ'
  have hTinv : (τ : G)⁻¹ * l = l * (τ : G)⁻¹ := by
    calc (τ : G)⁻¹ * l = (τ : G)⁻¹ * l * τ * (τ : G)⁻¹ := by group
      _ = (τ : G)⁻¹ * (l * τ) * (τ : G)⁻¹ := by group
      _ = (τ : G)⁻¹ * (τ * l) * (τ : G)⁻¹ := by rw [hlτ]
      _ = l * (τ : G)⁻¹ := by group
  have hu : ((w : G)⁻¹ * τ * w) * l = l * ((w : G)⁻¹ * τ * w) := by
    calc (w : G)⁻¹ * τ * w * l = ((w : G)⁻¹ * τ * w * τ) * ((τ : G)⁻¹ * l) := by group
      _ = ((w : G)⁻¹ * τ * w * τ) * (l * (τ : G)⁻¹) := by rw [hTinv]
      _ = (((w : G)⁻¹ * τ * w * τ) * l) * (τ : G)⁻¹ := by group
      _ = (l * ((w : G)⁻¹ * τ * w * τ)) * (τ : G)⁻¹ := by rw [← hκ']
      _ = l * ((w : G)⁻¹ * τ * w) := by group
  calc (τ : G) * ((w : G) * l * (w : G)⁻¹)
      = (w : G) * (((w : G)⁻¹ * τ * w) * l) * (w : G)⁻¹ := by group
    _ = (w : G) * (l * ((w : G)⁻¹ * τ * w)) * (w : G)⁻¹ := by rw [hu]
    _ = ((w : G) * l * (w : G)⁻¹) * τ := by group

end PairData

namespace Hyp4

variable {G : Type} [Group G] [Finite G] {M B Q P T : Subgroup G} (H : Hyp4 M B Q P T) {g : G}
include H

section Root


section Mutual

variable (hmut : MutualPFull M B P g)
include hmut

theorem pair_fixed_B_trivial {n : ℕ} (D : PairData P B g n) (hCen : BenderCenterInput)
    (hU : UnitaryTwoGenerationInput) {τ : ↥(P ⊔ conjSubgroup g P)} {c : (GaloisField 2 n)ˣ}
    (hτ : D.φ τ = diagElt c) (hc : c ≠ 1) {y : G} (hy : y ∈ conjSubgroup g B) (hy1 : y ≠ 1)
    (hyτ : (τ : G) * y = y * τ) {b : G} (hb : b ∈ B) (hbτ : (τ : G) * b = b * τ) : b = 1 := by
  have hg := hmut.outer
  have hyL : y ∈ B ⊔ conjSubgroup g B := Subgroup.mem_sup_right hy
  obtain ⟨p, hp, hpb⟩ := H.outer_surj_P hg hCen hU hy hy1 b hb
  obtain ⟨p'', hp'', k, hk, hpk⟩ := D.diag_P_factor hτ p hp
  have hyk : y * k = k * y := Subgroup.mem_centralizer_iff.mp hk y hyL
  have hyτ' : (τ : G)⁻¹ * y * τ = y := by
    calc (τ : G)⁻¹ * y * τ = (τ : G)⁻¹ * (y * τ) := by group
      _ = (τ : G)⁻¹ * (τ * y) := by rw [hyτ]
      _ = y := by group
  have hbτ' : (τ : G)⁻¹ * b * τ = b := by
    calc (τ : G)⁻¹ * b * τ = (τ : G)⁻¹ * (b * τ) := by group
      _ = (τ : G)⁻¹ * (τ * b) := by rw [hbτ]
      _ = b := by group
  have e1 : ⁅y, (τ : G)⁻¹ * p * τ⁆ = b := by
    have e : ⁅(τ : G)⁻¹ * y * τ, (τ : G)⁻¹ * p * τ⁆ = (τ : G)⁻¹ * ⁅y, p⁆ * τ := by
      simp only [commutatorElement_def]; group
    rw [hyτ', hpb, hbτ'] at e
    exact e
  rw [hpk] at e1
  have e2 : ⁅y, p'' * k⁆ = ⁅y, p''⁆ := by
    have e : ⁅y, p'' * k⁆ = ⁅y, p''⁆ * (p'' * ⁅y, k⁆ * p''⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e, commutatorElement_eq_one_iff_mul_comm.mpr hyk]
    group
  have e3 : ⁅y, p''⁆ = ⁅y, p⁆ := (e2.symm.trans e1).trans hpb.symm
  have hκ : ⁅y, p''⁻¹ * p⁆ = 1 := by
    rw [H.outer_commutator_mul hg hy (P.inv_mem hp'') hp, H.outer_commutator_inv hg hy hp'', e3]
    exact inv_mul_cancel _
  have hκP : p''⁻¹ * p ∈ P := P.mul_mem (P.inv_mem hp'') hp
  have hκK : p''⁻¹ * p ∈ Subgroup.centralizer ((B ⊔ conjSubgroup g B : Subgroup G) : Set G) :=
    H.pair_centP_cen hmut (mem_centP.mpr ⟨hκP, H.outer_comm_of_comm_one hg hCen hU hκP hy hy1
      (commutatorElement_eq_one_iff_mul_comm.mp hκ).symm⟩)
  have hpH : p ∈ P ⊔ conjSubgroup g P := Subgroup.mem_sup_left hp
  have hφ : D.φ (τ⁻¹ * ⟨p, hpH⟩ * τ) = D.φ ⟨p, hpH⟩ := by
    have h1 : D.φ ((τ⁻¹ * ⟨p, hpH⟩ * τ)⁻¹ * ⟨p, hpH⟩) = 1 := by
      rw [D.ker]
      have e : (((τ⁻¹ * ⟨p, hpH⟩ * τ)⁻¹ * ⟨p, hpH⟩ : ↥(P ⊔ conjSubgroup g P)) : G) =
          k⁻¹ * (p''⁻¹ * p) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk]
        rw [hpk]
        group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hk) hκK
    rwa [map_mul, map_inv, inv_mul_eq_one] at h1
  have hupper : D.φ ⟨p, hpH⟩ ∈ upperUnipotent (GaloisField 2 n) := by
    rw [← D.upper]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hp)
  obtain ⟨t, ht⟩ := (mem_upperUnipotent_iff _).mp hupper
  rw [map_mul, map_mul, map_inv, hτ, ht] at hφ
  have h2 : upperElt (GaloisField 2 n) ((c : GaloisField 2 n) ^ 2 * t) =
      upperElt (GaloisField 2 n) t := by
    rw [← diag_upper_conj' c t]
    calc diagElt c * upperElt (GaloisField 2 n) t * (diagElt c)⁻¹
        = diagElt c * ((diagElt c)⁻¹ * upperElt (GaloisField 2 n) t * diagElt c) *
          (diagElt c)⁻¹ := by rw [hφ]
      _ = upperElt (GaloisField 2 n) t := by group
  have h3 : (c : GaloisField 2 n) ^ 2 * t = t := upperElt_injective _ h2
  have ht0 : t = 0 := by
    have h4 : ((c : GaloisField 2 n) ^ 2 - 1) * t = 0 := by linear_combination h3
    rcases mul_eq_zero.mp h4 with h5 | h5
    · exact absurd (sub_eq_zero.mp h5) (sq_ne_one_of_ne_one' c hc)
    · exact h5
  have hpK : p ∈ Subgroup.centralizer ((B ⊔ conjSubgroup g B : Subgroup G) : Set G) := by
    refine (D.ker ⟨p, hpH⟩).mp ?_
    rw [ht, ht0, upperElt_zero]
  rw [← hpb]
  exact commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_centralizer_iff.mp hpK y hyL)

theorem pair_torus_fixed {n : ℕ} (D : PairData P B g n) (hCen : BenderCenterInput)
    (hU : UnitaryTwoGenerationInput) {w τ : ↥(P ⊔ conjSubgroup g P)} {c : (GaloisField 2 n)ˣ}
    (hw : D.φ w = weylElt (GaloisField 2 n)) (hτ : D.φ τ = diagElt c) (hc : c ≠ 1) :
    ∀ l ∈ B ⊔ conjSubgroup g B, (τ : G) * l * (τ : G)⁻¹ = l → l = 1 := by
  have hτBA := H.pair_diag_normalizes hmut D hCen hU hτ
  have hCA : ∀ a ∈ conjSubgroup g B, (τ : G) * a = a * τ → a = 1 := by
    intro a ha haτ
    by_contra ha1
    have hb₀ : (w : G) * a * (w : G)⁻¹ ∈ B := by
      have := mem_conjSubgroup_of_mem (w := (w : G)) ha
      rwa [(H.pair_swap hmut D hCen hU hw).2] at this
    have h1 : (w : G) * a * (w : G)⁻¹ = 1 :=
      H.pair_fixed_B_trivial hmut D hCen hU hτ hc ha ha1 haτ hb₀
        (D.transport hw hτ (Subgroup.mem_sup_right ha) haτ)
    apply ha1
    calc a = (w : G)⁻¹ * ((w : G) * a * (w : G)⁻¹) * (w : G) := by group
      _ = 1 := by rw [h1]; group
  have hCB : ∀ b ∈ B, (τ : G) * b = b * τ → b = 1 := by
    intro b hb hbτ
    have hw' : D.φ w⁻¹ = weylElt (GaloisField 2 n) := by rw [map_inv, hw, weylElt_inv']
    have ha₀ : (w : G)⁻¹ * b * ((w : G)⁻¹)⁻¹ ∈ conjSubgroup g B := by
      have := mem_conjSubgroup_of_mem (w := ((w⁻¹ : ↥(P ⊔ conjSubgroup g P)) : G)) hb
      rwa [(H.pair_swap hmut D hCen hU hw').1] at this
    have h1 : (w : G)⁻¹ * b * ((w : G)⁻¹)⁻¹ = 1 :=
      hCA _ ha₀ (D.transport hw' hτ (Subgroup.mem_sup_left hb) hbτ)
    calc b = (w : G) * ((w : G)⁻¹ * b * ((w : G)⁻¹)⁻¹) * (w : G)⁻¹ := by group
      _ = 1 := by rw [h1]; group
  intro l hl hlτ
  have hAB : conjSubgroup g B ≤ Subgroup.normalizer (B : Set G) :=
    le_normalizer_of_comm fun a ha b hb => (H.outer_comm_B hmut.outer b hb a ha).symm
  obtain ⟨b, hb, a, ha, rfl⟩ := exists_mul_of_mem_sup hAB hl
  have hb' : (τ : G) * b * (τ : G)⁻¹ ∈ B := by
    have := mem_conjSubgroup_of_mem (w := (τ : G)) hb
    rwa [hτBA.1] at this
  have ha' : (τ : G) * a * (τ : G)⁻¹ ∈ conjSubgroup g B := by
    have := mem_conjSubgroup_of_mem (w := (τ : G)) ha
    rwa [hτBA.2] at this
  have h1 : (τ : G) * b * (τ : G)⁻¹ * ((τ : G) * a * (τ : G)⁻¹) = b * a := by
    calc _ = (τ : G) * (b * a) * (τ : G)⁻¹ := by group
      _ = b * a := hlτ
  have e : ((τ : G) * b * (τ : G)⁻¹)⁻¹ * b = ((τ : G) * a * (τ : G)⁻¹) * a⁻¹ := by
    calc ((τ : G) * b * (τ : G)⁻¹)⁻¹ * b = ((τ : G) * b * (τ : G)⁻¹)⁻¹ * (b * a) * a⁻¹ := by
          group
      _ = ((τ : G) * b * (τ : G)⁻¹)⁻¹ * ((τ : G) * b * (τ : G)⁻¹ *
          ((τ : G) * a * (τ : G)⁻¹)) * a⁻¹ := by rw [h1]
      _ = ((τ : G) * a * (τ : G)⁻¹) * a⁻¹ := by group
  have hx : ((τ : G) * b * (τ : G)⁻¹)⁻¹ * b ∈ B ⊓ conjSubgroup g B :=
    ⟨B.mul_mem (B.inv_mem hb') hb, by
      rw [e]
      exact (conjSubgroup g B).mul_mem ha' ((conjSubgroup g B).inv_mem ha)⟩
  rw [H.outer_inf_B hmut.outer, Subgroup.mem_bot] at hx
  have hb1 : (τ : G) * b * (τ : G)⁻¹ = b := inv_mul_eq_one.mp hx
  have ha1 : (τ : G) * a * (τ : G)⁻¹ = a := by
    apply mul_inv_eq_one.mp
    rw [← e]
    exact hx
  have hb2 := hCB b hb (mul_inv_eq_iff_eq_mul.mp hb1)
  have ha2 := hCA a ha (mul_inv_eq_iff_eq_mul.mp ha1)
  rw [hb2, ha2, mul_one]

theorem pair_weyl_torus (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput) :
    ∃ w ∈ P ⊔ conjSubgroup g P, ∃ τ ∈ P ⊔ conjSubgroup g P,
      (conjSubgroup w B = conjSubgroup g B ∧ conjSubgroup w (conjSubgroup g B) = B) ∧
      (conjSubgroup τ B = B ∧ conjSubgroup τ (conjSubgroup g B) = conjSubgroup g B ∧
        ∀ l ∈ B ⊔ conjSubgroup g B, τ * l * τ⁻¹ = l → l = 1) := by
  obtain ⟨n, hn2, -, φ, hs, hker, hPφ, hPgφ⟩ := H.pair_rankOne hmut hCen hU
  let D : PairData P B g n := ⟨φ, hs, hker, hPφ, hPgφ⟩
  obtain ⟨w, hw⟩ := D.surj (weylElt (GaloisField 2 n))
  obtain ⟨c, hc⟩ : ∃ c : (GaloisField 2 n)ˣ, c ≠ 1 := by
    have h4 : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    have hcard : Nat.card (GaloisField 2 n)ˣ = 2 ^ n - 1 := by
      rw [Nat.card_units, GaloisField.card 2 n (by omega)]
    haveI : Nontrivial (GaloisField 2 n)ˣ := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    exact exists_ne (1 : (GaloisField 2 n)ˣ)
  obtain ⟨τ, hτ⟩ := D.surj (diagElt c)
  exact ⟨w, w.2, τ, τ.2, H.pair_swap hmut D hCen hU hw,
    (H.pair_diag_normalizes hmut D hCen hU hτ).1, (H.pair_diag_normalizes hmut D hCen hU hτ).2,
    H.pair_torus_fixed hmut D hCen hU hw hτ hc⟩

end Mutual

end Root

end Hyp4

end CFSG.RankThree.GF2n.Tim78
