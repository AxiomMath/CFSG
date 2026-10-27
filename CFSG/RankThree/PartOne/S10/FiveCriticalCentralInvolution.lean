module

import CFSG.RankThree.PartOne.S10.FiveCriticalFrattini
import CFSG.RankThree.PartOne.S9.OddCore.TorsionQD32
import CFSG.RankThree.PartOne.S9.OddCore.TorsionModule
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Foundations.Basic
public import CFSG.RankThree.GroupTheory.SteinbergCEQuaternionDihedral

public section

namespace CFSG.RankThree.PartOne.FiveCritical

open Subgroup CFSG CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne.FixedRank36
  CFSG.RankThree.PartOne.Torsion37
open scoped commutatorElement IsMulCommutative

variable {G : Type} [Group G] [Finite G]

theorem five_faithful_and_central_involution_inverts {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {D R : Subgroup G} (hD : IsPGroup q D) (hRN : R ≤ normalizer (D : Set G))
    (hRD : R ⊓ centralizer (D : Set G) = ⊥)
    (hrel : (inSubgroup frattini D).relIndex D = q ^ 4) (hS : Nonempty (R ≃* QD32)) :
    (∀ r ∈ R, (∀ d ∈ D, (r * d * r⁻¹)⁻¹ * d ∈ inSubgroup frattini D) → r = 1) ∧
    ∀ z ∈ R, z ≠ 1 → z ∈ inSubgroup Subgroup.center R →
      ∀ d ∈ D, z * d * z⁻¹ * d ∈ inSubgroup frattini D := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  have hel : IsElementaryAbelian q (↥D ⧸ frattini ↥D) :=
    (CFSG.GroupTheory.frattini_elementary_quotient hD).2.2.2.1
  obtain ⟨hRext, hR32, -⟩ := qd32_facts hS
  have hR2 : IsPGroup 2 R := hRext.1
  set ρ : ↥R →* MulAut ↥D := D.normalizerMonoidHom.comp (Subgroup.inclusion hRN) with hρ
  have hdim : Module.finrank (ZMod q) (Additive (↥D ⧸ frattini ↥D)) = 4 := by
    have h1 : Nat.card (↥D ⧸ frattini ↥D) = q ^ 4 := by
      rw [← relIndex_inSubgroup_frattini_eq_card, hrel]
    have h2 : Nat.card (Additive (↥D ⧸ frattini ↥D)) = q ^ 4 := by
      rw [← h1]
      exact Nat.card_congr Additive.toMul
    rw [Module.natCard_eq_pow_finrank (K := ZMod q), Nat.card_zmod] at h2
    exact Nat.pow_right_injective hq.two_le h2
  have hinj : Function.Injective (frattiniRep q ρ) := by
    rw [injective_iff_map_eq_one]
    intro r hr
    have h1 : ρ r = 1 := frattiniRep_eq_one hD hq2 ρ r (isPGroup_zpowers_map hR2 ρ r) hr
    have hmem : (r : G) ∈ R ⊓ centralizer (D : Set G) := by
      refine ⟨r.2, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
      have h := congrArg (fun f : MulAut ↥D => ((f ⟨g, hg⟩ : ↥D) : G)) h1
      simp only [hρ, MonoidHom.comp_apply, Subgroup.normalizerMonoidHom_apply_apply_coe,
        MulAut.one_apply] at h
      change (r : G) * g * (r : G)⁻¹ = g at h
      calc g * (r : G) = ((r : G) * g * (r : G)⁻¹) * r := by rw [h]
        _ = r * g := by group
    rw [hRD, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  obtain ⟨hz, -, -⟩ := minimal_module_facts (two_ne_zero_zmod hq hq2) hRext hR32
    (frattiniRep q ρ) hinj hdim
  have hcoe : ∀ (b : R) (x : ↥D), ((ρ b x : ↥D) : G) = (b : G) * x * (b : G)⁻¹ := fun _ _ => rfl
  refine ⟨fun r hr h => ?_, fun z hzR hz1 hzc d hd => ?_⟩
  · have hone : frattiniRep q ρ ⟨r, hr⟩ = 1 := by
      apply LinearMap.ext
      intro v
      obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
      have hv : v = Additive.ofMul (x : ↥D ⧸ frattini ↥D) := by rw [hx]; rfl
      rw [hv, frattiniRep_apply, Module.End.one_apply]
      congr 1
      rw [frattini_class_eq_iff]
      exact h x x.2
    exact congrArg Subtype.val (hinj (hone.trans (map_one _).symm))
  · obtain ⟨z₀, hz₀c, hz₀1⟩ := exists_center_generator_of_extraspecial hRext
    have hz₀ord : orderOf z₀ = 2 := by
      rw [← Nat.card_zpowers, ← hz₀c]
      exact hRext.2.2.2
    have hzmem : (⟨z, hzR⟩ : ↥R) ∈ Subgroup.center ↥R := by
      obtain ⟨c, hc, hcz⟩ := hzc
      have : c = ⟨z, hzR⟩ := Subtype.ext hcz
      rwa [← this]
    have hzeq : (⟨z, hzR⟩ : ↥R) = z₀ := by
      rw [hz₀c, SteinbergBY.mem_zpowers_of_orderOf_eq_two hz₀ord] at hzmem
      rcases hzmem with h | h
      · exact absurd (congrArg Subtype.val h) hz1
      · exact h
    have hρz := hz z₀ hz₀c hz₀1
    rw [← hzeq] at hρz
    have h := congrArg (fun f : Module.End (ZMod q) (Additive (↥D ⧸ frattini ↥D)) =>
      f (Additive.ofMul ((⟨d, hd⟩ : ↥D) : ↥D ⧸ frattini ↥D))) hρz
    simp only [frattiniRep_apply, LinearMap.neg_apply, Module.End.one_apply] at h
    have h' : ((ρ ⟨z, hzR⟩ ⟨d, hd⟩ : ↥D) : ↥D ⧸ frattini ↥D) =
        ((⟨d, hd⟩ : ↥D) : ↥D ⧸ frattini ↥D)⁻¹ := by
      have := congrArg Additive.toMul h
      simpa using this
    have h3 : ((ρ ⟨z, hzR⟩ ⟨d, hd⟩ * ⟨d, hd⟩ : ↥D) : ↥D ⧸ frattini ↥D) = 1 := by
      rw [QuotientGroup.mk_mul, h', inv_mul_cancel]
    exact ⟨_, (QuotientGroup.eq_one_iff _).mp h3, rfl⟩

omit [Finite G] in
theorem scalar_pred_of_inverts {q : ℕ} (hq : q.Prime) {D : Subgroup G} {z : G}
    (hexp : ∀ x ∈ D, x ^ q = 1) (hzN : z ∈ normalizer (D : Set G))
    (hinv : ∀ d ∈ D, z * d * z⁻¹ * d ∈ inSubgroup frattini D) :
    ∀ d ∈ D, (z * d * z⁻¹)⁻¹ * d ^ (q - 1) ∈ inSubgroup frattini D := by
  intro d hd
  have hw : z * d * z⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp hzN d).mp hd
  set u : ↥D := ⟨d, hd⟩ with hu
  set w : ↥D := ⟨z * d * z⁻¹, hw⟩ with hw'
  have h1 : (w * u : ↥D) ∈ frattini ↥D :=
    (Subgroup.mem_map_iff_mem D.subtype_injective).mp (hinv d hd)
  have h2 : (w : ↥D ⧸ frattini ↥D) = (u : ↥D ⧸ frattini ↥D)⁻¹ := by
    have h : ((w * u : ↥D) : ↥D ⧸ frattini ↥D) = 1 := (QuotientGroup.eq_one_iff _).mpr h1
    rw [QuotientGroup.mk_mul] at h
    exact eq_inv_of_mul_eq_one_left h
  have h3 : u ^ (q - 1) = u⁻¹ := by
    have hu1 : u ^ q = 1 := Subtype.ext (hexp d hd)
    have h : u ^ (q - 1) * u = 1 := by
      rw [← pow_succ, Nat.sub_add_cancel hq.one_lt.le]
      exact hu1
    exact eq_inv_of_mul_eq_one_left h
  exact (frattini_class_eq_iff w (u ^ (q - 1))).mp (by rw [h3, QuotientGroup.mk_inv, h2])

theorem exists_five_central_involution {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {A D R : Subgroup G} (hD : IsPGroup q D) (hexp : ∀ x ∈ D, x ^ q = 1)
    (hRN : R ≤ normalizer (D : Set G)) (hAR : A ≤ normalizer (R : Set G))
    (hRD : R ⊓ centralizer (D : Set G) = ⊥) (hrel : (inSubgroup frattini D).relIndex D = q ^ 4)
    (hS : Nonempty (R ≃* QD32)) :
    ∃ z ∈ R, z ≠ 1 ∧ z ^ 2 = 1 ∧ inSubgroup Subgroup.center R = zpowers z ∧
      A ≤ centralizer ({z} : Set G) ∧
      (∀ d ∈ D, z * d * z⁻¹ * d ∈ inSubgroup frattini D) ∧
      ∃ k : ℕ, ∀ d ∈ D, (z * d * z⁻¹)⁻¹ * d ^ k ∈ inSubgroup frattini D := by
  classical
  obtain ⟨-, hinv⟩ := five_faithful_and_central_involution_inverts hq hq2 hD hRN hRD hrel hS
  obtain ⟨hRext, hR32, -⟩ := qd32_facts hS
  obtain ⟨z₀, hz₀c, hz₀1⟩ := exists_center_generator_of_extraspecial hRext
  have hz₀ord : orderOf z₀ = 2 := by
    rw [← Nat.card_zpowers, ← hz₀c]
    exact hRext.2.2.2
  have hz₀mem : z₀ ∈ Subgroup.center ↥R := by
    rw [hz₀c]
    exact Subgroup.mem_zpowers z₀
  have hzR : (z₀ : G) ∈ R := z₀.2
  have hz1 : (z₀ : G) ≠ 1 := fun h => hz₀1 (Subtype.ext h)
  have hzcen : (z₀ : G) ∈ inSubgroup Subgroup.center R := ⟨z₀, hz₀mem, rfl⟩
  have hinv' := hinv (z₀ : G) hzR hz1 hzcen
  refine ⟨(z₀ : G), hzR, hz1, ?_, ?_, ?_, hinv', q - 1, ?_⟩
  · have h := pow_orderOf_eq_one z₀
    rw [hz₀ord] at h
    exact congrArg Subtype.val h
  · show (Subgroup.center ↥R).map R.subtype = zpowers (z₀ : G)
    rw [hz₀c, MonoidHom.map_zpowers]
    rfl
  · intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hzcomm : ∀ r : ↥R, r * z₀ = z₀ * r := fun r => Subgroup.mem_center_iff.mp hz₀mem r
    have hw : a * (z₀ : G) * a⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp (hAR ha) _).mp hzR
    have hwc : (⟨a * z₀ * a⁻¹, hw⟩ : ↥R) ∈ Subgroup.center ↥R := by
      rw [Subgroup.mem_center_iff]
      intro r
      apply Subtype.ext
      have hr' : a⁻¹ * (r : G) * a ∈ R :=
        (Subgroup.mem_normalizer_iff''.mp (hAR ha) _).mp r.2
      have h1 := congrArg Subtype.val (hzcomm ⟨a⁻¹ * r * a, hr'⟩)
      have h1' : (a⁻¹ * (r : G) * a) * (z₀ : G) = (z₀ : G) * (a⁻¹ * r * a) := h1
      change (r : G) * (a * z₀ * a⁻¹) = (a * z₀ * a⁻¹) * r
      calc (r : G) * (a * z₀ * a⁻¹) = a * ((a⁻¹ * r * a) * z₀) * a⁻¹ := by group
        _ = a * (z₀ * (a⁻¹ * r * a)) * a⁻¹ := by rw [h1']
        _ = (a * z₀ * a⁻¹) * r := by group
    rw [hz₀c, SteinbergBY.mem_zpowers_of_orderOf_eq_two hz₀ord] at hwc
    rcases hwc with h | h
    · exfalso
      apply hz1
      have h' : a * (z₀ : G) * a⁻¹ = 1 := congrArg Subtype.val h
      calc (z₀ : G) = a⁻¹ * (a * z₀ * a⁻¹) * a := by group
        _ = 1 := by rw [h']; group
    · have h' : a * (z₀ : G) * a⁻¹ = z₀ := congrArg Subtype.val h
      calc a * (z₀ : G) = (a * z₀ * a⁻¹) * a := by group
        _ = z₀ * a := by rw [h']
  · exact scalar_pred_of_inverts hq hexp (hRN hzR) hinv'

end CFSG.RankThree.PartOne.FiveCritical
