module

public import CFSG.RankThree.GF2n.Tim78S412Pair
public import CFSG.Timmesfeld.ARS.NaturalModule

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n CFSG.Timmesfeld
open CFSG.Timmesfeld.ARS.NaturalModule CFSG.Timmesfeld.RankOne
open scoped commutatorElement

section SL2

variable {K : Type*} [Field K] [CharP K 2]

theorem weylElt_inv' : (weylElt K)⁻¹ = weylElt K :=
  inv_eq_of_mul_eq_one_right weylElt_mul_self

theorem weyl_conj_upper' {x : Matrix.SpecialLinearGroup (Fin 2) K} (hx : x ∈ upperUnipotent K) :
    (weylElt K)⁻¹ * x * weylElt K ∈ lowerUnipotent K := by
  obtain ⟨t, rfl⟩ := (mem_upperUnipotent_iff K).mp hx
  rw [weylElt_inv', weylElt_mul_upperElt_mul_weylElt]
  exact (mem_lowerUnipotent_iff K).mpr ⟨t, rfl⟩

theorem weyl_conj_lower' {x : Matrix.SpecialLinearGroup (Fin 2) K} (hx : x ∈ lowerUnipotent K) :
    (weylElt K)⁻¹ * x * weylElt K ∈ upperUnipotent K := by
  obtain ⟨t, rfl⟩ := (mem_lowerUnipotent_iff K).mp hx
  rw [weylElt_inv', ← weylElt_mul_upperElt_mul_weylElt t]
  have : weylElt K * (weylElt K * upperElt K t * weylElt K) * weylElt K = upperElt K t := by
    calc _ = (weylElt K * weylElt K) * upperElt K t * (weylElt K * weylElt K) := by group
      _ = upperElt K t := by rw [weylElt_mul_self]; group
  rw [this]
  exact (mem_upperUnipotent_iff K).mpr ⟨t, rfl⟩

theorem diag_conj_upper' (c : Kˣ) {x : Matrix.SpecialLinearGroup (Fin 2) K}
    (hx : x ∈ upperUnipotent K) : (diagElt c)⁻¹ * x * diagElt c ∈ upperUnipotent K := by
  have h := (Subgroup.mem_normalizer_iff.mp
    (Subgroup.inv_mem _ (diagElt_mem_normalizer_upperUnipotent c)) x).mp hx
  simpa using h

theorem diag_conj_lower' (c : Kˣ) {x : Matrix.SpecialLinearGroup (Fin 2) K}
    (hx : x ∈ lowerUnipotent K) : (diagElt c)⁻¹ * x * diagElt c ∈ lowerUnipotent K := by
  have h := (Subgroup.mem_normalizer_iff.mp
    (Subgroup.inv_mem _ (diagElt_mem_normalizer_lowerUnipotent c)) x).mp hx
  simpa using h

theorem weyl_diag_weyl' (c : Kˣ) :
    (weylElt K)⁻¹ * diagElt c * weylElt K = diagElt c⁻¹ := by
  rw [weylElt_inv']
  calc weylElt K * diagElt c * weylElt K = (diagElt c⁻¹ * weylElt K) * weylElt K := by
        rw [weylElt_mul_diagElt]
    _ = diagElt c⁻¹ := by rw [mul_assoc, weylElt_mul_self, mul_one]

theorem diag_upper_conj' (c : Kˣ) (t : K) :
    diagElt c * upperElt K t * (diagElt c)⁻¹ = upperElt K ((c : K) ^ 2 * t) := by
  rw [diagElt_mul_upperElt]
  group

theorem sq_ne_one_of_ne_one' (c : Kˣ) (hc : c ≠ 1) : (c : K) ^ 2 ≠ 1 := by
  intro hsq
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h0 : ((c : K) - 1) ^ 2 = 0 := by linear_combination hsq - ((c : K) - 1) * h2
  exact hc (Units.ext (sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h0)))

end SL2

section Data

variable {G : Type} [Group G]

theorem mem_conjSubgroup_of_mem {X : Subgroup G} {w x : G} (hx : x ∈ X) :
    w * x * w⁻¹ ∈ conjSubgroup w X := by
  rw [mem_conjSubgroup, show w⁻¹ * (w * x * w⁻¹) * w = x by group]
  exact hx

theorem conjSubgroup_eq_of_forall_mem [Finite G] {X Y : Subgroup G} (z : G)
    (h : ∀ x ∈ X, z * x * z⁻¹ ∈ Y) (hcard : Nat.card Y ≤ Nat.card X) :
    conjSubgroup z X = Y := by
  refine Subgroup.eq_of_le_of_card_ge (fun x hx => ?_) (by rw [card_conjSubgroup]; exact hcard)
  have := h _ (mem_conjSubgroup.mp hx)
  rwa [show z * (z⁻¹ * x * z) * z⁻¹ = x by group] at this

structure PairData (P B : Subgroup G) (g : G) (n : ℕ) where
  φ : ↥(P ⊔ conjSubgroup g P) →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)
  surj : Function.Surjective φ
  ker : ∀ z : ↥(P ⊔ conjSubgroup g P), φ z = 1 ↔
    (z : G) ∈ Subgroup.centralizer ((B ⊔ conjSubgroup g B : Subgroup G) : Set G)
  upper : (P.subgroupOf (P ⊔ conjSubgroup g P)).map φ = upperUnipotent (GaloisField 2 n)
  lower : ((conjSubgroup g P).subgroupOf (P ⊔ conjSubgroup g P)).map φ =
    lowerUnipotent (GaloisField 2 n)

namespace PairData

variable {P B : Subgroup G} {g : G} {n : ℕ} (D : PairData P B g n)

theorem factor {S : Subgroup G}
    {U : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))}
    (hS : (S.subgroupOf (P ⊔ conjSubgroup g P)).map D.φ = U)
    {x : ↥(P ⊔ conjSubgroup g P)} (hx : D.φ x ∈ U) :
    ∃ y ∈ S, ∃ k ∈ Subgroup.centralizer ((B ⊔ conjSubgroup g B : Subgroup G) : Set G),
      (x : G) = y * k := by
  rw [← hS] at hx
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
  refine ⟨(y : G), Subgroup.mem_subgroupOf.mp hy, ((y⁻¹ * x : ↥(P ⊔ conjSubgroup g P)) : G),
    (D.ker _).mp ?_, by simp⟩
  rw [map_mul, map_inv, hyx, inv_mul_cancel]

theorem conj_factor {S S' : Subgroup G}
    {U U' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))}
    (hS : (S.subgroupOf (P ⊔ conjSubgroup g P)).map D.φ = U)
    (hS' : (S'.subgroupOf (P ⊔ conjSubgroup g P)).map D.φ = U')
    (hSH : S ≤ P ⊔ conjSubgroup g P) (z : ↥(P ⊔ conjSubgroup g P))
    (hz : ∀ x ∈ U, (D.φ z)⁻¹ * x * D.φ z ∈ U') :
    ∀ x ∈ S, ∃ y ∈ S', ∃ k ∈ Subgroup.centralizer ((B ⊔ conjSubgroup g B : Subgroup G) : Set G),
      (z : G)⁻¹ * x * z = y * k := by
  intro x hx
  have h1 : D.φ ⟨x, hSH hx⟩ ∈ U := by
    rw [← hS]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx)
  have h2 : D.φ (z⁻¹ * ⟨x, hSH hx⟩ * z) ∈ U' := by
    rw [map_mul, map_mul, map_inv]
    exact hz _ h1
  obtain ⟨y, hy, k, hk, hyk⟩ := D.factor hS' h2
  exact ⟨y, hy, k, hk, by simpa using hyk⟩

theorem weyl_Pg_factor {w : ↥(P ⊔ conjSubgroup g P)}
    (hw : D.φ w = weylElt (GaloisField 2 n)) :
    ∀ x ∈ conjSubgroup g P, ∃ y ∈ P,
      ∃ k ∈ Subgroup.centralizer ((B ⊔ conjSubgroup g B : Subgroup G) : Set G),
        (w : G)⁻¹ * x * w = y * k :=
  D.conj_factor D.lower D.upper le_sup_right w fun x hx => by
    rw [hw]
    exact weyl_conj_lower' hx

theorem weyl_P_factor {w : ↥(P ⊔ conjSubgroup g P)}
    (hw : D.φ w = weylElt (GaloisField 2 n)) :
    ∀ x ∈ P, ∃ y ∈ conjSubgroup g P,
      ∃ k ∈ Subgroup.centralizer ((B ⊔ conjSubgroup g B : Subgroup G) : Set G),
        (w : G)⁻¹ * x * w = y * k :=
  D.conj_factor D.upper D.lower le_sup_left w fun x hx => by
    rw [hw]
    exact weyl_conj_upper' hx

theorem diag_P_factor {τ : ↥(P ⊔ conjSubgroup g P)} {c : (GaloisField 2 n)ˣ}
    (hτ : D.φ τ = diagElt c) :
    ∀ x ∈ P, ∃ y ∈ P,
      ∃ k ∈ Subgroup.centralizer ((B ⊔ conjSubgroup g B : Subgroup G) : Set G),
        (τ : G)⁻¹ * x * τ = y * k :=
  D.conj_factor D.upper D.upper le_sup_left τ fun x hx => by
    rw [hτ]
    exact diag_conj_upper' c hx

theorem diag_Pg_factor {τ : ↥(P ⊔ conjSubgroup g P)} {c : (GaloisField 2 n)ˣ}
    (hτ : D.φ τ = diagElt c) :
    ∀ x ∈ conjSubgroup g P, ∃ y ∈ conjSubgroup g P,
      ∃ k ∈ Subgroup.centralizer ((B ⊔ conjSubgroup g B : Subgroup G) : Set G),
        (τ : G)⁻¹ * x * τ = y * k :=
  D.conj_factor D.lower D.lower le_sup_right τ fun x hx => by
    rw [hτ]
    exact diag_conj_lower' c hx

end PairData

end Data

namespace Hyp4

variable {G : Type} [Group G] [Finite G] {M B Q P T : Subgroup G} (H : Hyp4 M B Q P T) {g : G}
include H

section Root


theorem outer_centralizer_L (hg : OuterPFull M B P g) (hCen : BenderCenterInput)
    (hU : UnitaryTwoGenerationInput) {l : G} (hl : l ∈ B ⊔ conjSubgroup g B)
    (hc : ∀ p ∈ P, p * l = l * p) : l ∈ B := by
  have hAB : conjSubgroup g B ≤ Subgroup.normalizer (B : Set G) :=
    le_normalizer_of_comm fun a ha b hb => (H.outer_comm_B hg b hb a ha).symm
  obtain ⟨b, hb, a, ha, rfl⟩ := exists_mul_of_mem_sup hAB hl
  by_cases ha1 : a = 1
  · rw [ha1, mul_one]
    exact hb
  exfalso
  obtain ⟨b', hb', hb'1⟩ := H.exists_ne_one_mem_conj 1
  rw [conjSubgroup_one] at hb'
  obtain ⟨p, hp, hpa⟩ := H.outer_surj_P hg hCen hU ha ha1 b' hb'
  have h1 := hc p hp
  have h2 : p * a = a * p := by
    have h3 : b * (p * a) = b * (a * p) := by
      calc b * (p * a) = (b * p) * a := by group
        _ = (p * b) * a := by rw [H.center_Q hb (H.P_le_Q hp)]
        _ = p * (b * a) := by group
        _ = (b * a) * p := h1
        _ = b * (a * p) := by group
    exact mul_left_cancel h3
  apply hb'1
  rw [← hpa]
  exact commutatorElement_eq_one_iff_mul_comm.mpr h2.symm

section Mutual

variable (hmut : MutualPFull M B P g)
include hmut

theorem pair_centralizer_Pg (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput) {l : G}
    (hl : l ∈ B ⊔ conjSubgroup g B) (hc : ∀ u ∈ conjSubgroup g P, u * l = l * u) :
    l ∈ conjSubgroup g B := by
  refine (H.conj g).outer_centralizer_L (H.outer_conj_of_mutual hmut) hCen hU ?_ hc
  rw [H.pair_L_conj_eq hmut]
  exact hl

theorem pair_le_normalizer_L :
    P ⊔ conjSubgroup g P ≤ Subgroup.normalizer ((B ⊔ conjSubgroup g B : Subgroup G) : Set G) :=
  sup_le (H.outer_P_le_normalizer_L hmut.outer) (H.pair_Pg_le_normalizer_L hmut)

theorem pair_swap {n : ℕ} (D : PairData P B g n) (hCen : BenderCenterInput)
    (hU : UnitaryTwoGenerationInput) {w : ↥(P ⊔ conjSubgroup g P)}
    (hw : D.φ w = weylElt (GaloisField 2 n)) :
    conjSubgroup (w : G) B = conjSubgroup g B ∧ conjSubgroup (w : G) (conjSubgroup g B) = B := by
  have hwN : (w : G) ∈ Subgroup.normalizer ((B ⊔ conjSubgroup g B : Subgroup G) : Set G) :=
    H.pair_le_normalizer_L hmut w.2
  refine ⟨conjSubgroup_eq_of_forall_mem _ (fun b hb => ?_) (card_conjSubgroup g B).le,
    conjSubgroup_eq_of_forall_mem _ (fun a ha => ?_) (card_conjSubgroup g B).symm.le⟩
  · obtain ⟨hl, hc⟩ := conj_comm_of_factor hwN (D.weyl_Pg_factor hw) (Subgroup.mem_sup_left hb)
      (fun y hy => (H.center_Q hb (H.P_le_Q hy)).symm)
    exact H.pair_centralizer_Pg hmut hCen hU hl (fun u hu => hc u hu)
  · obtain ⟨hl, hc⟩ := conj_comm_of_factor hwN (D.weyl_P_factor hw) (Subgroup.mem_sup_right ha)
      (fun u hu => (H.pair_Pg_comm_A hmut hu ha).symm)
    exact H.outer_centralizer_L hmut.outer hCen hU hl (fun p hp => hc p hp)

theorem pair_diag_normalizes {n : ℕ} (D : PairData P B g n) (hCen : BenderCenterInput)
    (hU : UnitaryTwoGenerationInput) {τ : ↥(P ⊔ conjSubgroup g P)} {c : (GaloisField 2 n)ˣ}
    (hτ : D.φ τ = diagElt c) :
    conjSubgroup (τ : G) B = B ∧
      conjSubgroup (τ : G) (conjSubgroup g B) = conjSubgroup g B := by
  have hτN : (τ : G) ∈ Subgroup.normalizer ((B ⊔ conjSubgroup g B : Subgroup G) : Set G) :=
    H.pair_le_normalizer_L hmut τ.2
  refine ⟨conjSubgroup_eq_of_forall_mem _ (fun b hb => ?_) le_rfl,
    conjSubgroup_eq_of_forall_mem _ (fun a ha => ?_) le_rfl⟩
  · obtain ⟨hl, hc⟩ := conj_comm_of_factor hτN (D.diag_P_factor hτ) (Subgroup.mem_sup_left hb)
      (fun y hy => (H.center_Q hb (H.P_le_Q hy)).symm)
    exact H.outer_centralizer_L hmut.outer hCen hU hl (fun p hp => hc p hp)
  · obtain ⟨hl, hc⟩ := conj_comm_of_factor hτN (D.diag_Pg_factor hτ) (Subgroup.mem_sup_right ha)
      (fun u hu => (H.pair_Pg_comm_A hmut hu ha).symm)
    exact H.pair_centralizer_Pg hmut hCen hU hl (fun u hu => hc u hu)

end Mutual

end Root

end Hyp4

end CFSG.RankThree.GF2n.Tim78
