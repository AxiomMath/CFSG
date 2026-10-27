
module

public import CFSG.Sporadic.SmallOddCore.J3
public import CFSG.Sporadic.SmallOddCore.AutCount
public import CFSG.Sporadic.Schreier.PairJ3Pairs
public meta import CFSG.Sporadic.Schreier.PairJ3Check
public meta import Certificates.Data.CFSGNative.PairSchreier.Preds
public import CFSG.Sporadic.Schreier.PairJ3CertInputs
public import CFSG.Sporadic.Schreier.PairJ3CheckInputs
public meta import CFSG.Sporadic.Schreier.PairJ3Cert
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import CFSG.Sporadic.Schreier.PairJ3Check
public import Certificates.Data.CFSGNative.PairSchreier.Preds
public import CFSG.Sporadic.SmallOddCore.J3WordBoundInputs
public import CFSG.Sporadic.SmallOddCore.J3CentFacts

@[expose] public section

namespace CFSG.Sporadic.SmallOddCore

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative
open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

def WordConds {G : Type*} [Group G] (x y : G) : Prop :=
  orderOf y = 3 ∧ orderOf (x * y) = 19 ∧ orderOf (x * y * x⁻¹ * y⁻¹) = 9 ∧
    orderOf (x * y * x * y * x * y ^ 2) = 17

theorem wordConds_map {G H : Type*} [Group G] [Group H] (f : G →* H) (hf : Function.Injective f)
    (x y : G) : WordConds (f x) (f y) ↔ WordConds x y := by
  simp only [WordConds, ← map_mul, ← map_inv, ← map_pow, orderOf_injective f hf]

theorem j3WPat_prod {G : Type*} [Group G] (x y : G) :
    (j3WPat.map fun b => if b then y else x).prod = x * y * x * y * x * y ^ 2 := by
  simp [j3WPat, pow_two, mul_assoc]

theorem wordConds_iff {G : Type*} [Group G] {x y : G} (hx : orderOf x = 2) :
    (orderOf y = 3 ∧ ∀ c ∈ j3WConds, orderOf (c.1.map fun b => if b then y else x).prod = c.2) ↔
      WordConds x y := by
  have hxi : x⁻¹ = x := by
    rw [inv_eq_iff_mul_eq_one, ← pow_two, ← hx, pow_orderOf_eq_one]
  simp only [WordConds, j3WConds, List.forall_mem_cons, List.not_mem_nil, false_implies,
    implies_true, and_true, j3WPat_prod, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, Bool.false_eq_true, ite_false, ite_true]
  constructor
  · rintro ⟨hy, h1, h2, h3⟩
    have hy3 : y ^ 3 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
    have hyi : y⁻¹ = y * y := by
      rw [inv_eq_iff_mul_eq_one]
      rw [← pow_three]
      exact hy3
    refine ⟨hy, h1, ?_, h3⟩
    rw [hxi, hyi]
    simpa only [mul_assoc] using h2
  · rintro ⟨hy, h1, h2, h3⟩
    have hy3 : y ^ 3 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
    have hyi : y⁻¹ = y * y := by
      rw [inv_eq_iff_mul_eq_one]
      rw [← pow_three]
      exact hy3
    refine ⟨hy, h1, ?_, h3⟩
    rw [hxi, hyi] at h2
    simpa only [mul_assoc] using h2

theorem j3_involution_conj_a {t : j3P} (ht : orderOf t = 2) : ∃ g : j3P, t = g * j3a * g⁻¹ := by
  obtain ⟨-, -, -, hrows, hcover, -, -, -⟩ :=
    ctuc_j3_all_involution_fixed_subgroups_odd_core_trivial
  have hPR : j3P ≤ j3R := le_sup_left
  have hinner : ∀ x ∈ j3P, orderOf x = 2 →
      ∃ g ∈ j3P, x = g * tp 6156 (j3Rows[0]'(by simp [j3Rows])).rep * g⁻¹ := by
    intro x hx hx2
    obtain ⟨r, hr, g, hg, rfl⟩ := hcover x (hPR hx) hx2
    have hrP : tp 6156 r.rep ∈ j3P := by
      have := j3P.mul_mem (j3P.mul_mem (j3P.inv_mem hg) hx) hg
      rwa [show g⁻¹ * (g * tp 6156 r.rep * g⁻¹) * g = tp 6156 r.rep by group] at this
    have hout : r.outer = false := by
      by_contra h
      rw [Bool.not_eq_false] at h
      exact (hrows r hr).2.2.1.1 h hrP
    have hr0 : r = j3Rows[0]'(by simp [j3Rows]) := by
      simp only [j3Rows, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rfl
      · exact absurd hout (by decide)
    exact ⟨g, hg, by rw [hr0]⟩
  obtain ⟨g, hg, hgt⟩ := hinner t t.2 (by rw [Subgroup.orderOf_coe]; exact ht)
  obtain ⟨g', hg', hga⟩ := hinner (j3Gen 0) (j3Gen_mem_P 0 (by norm_num))
    AT_J3_image_pair_count.1
  refine ⟨⟨g, hg⟩ * ⟨g', hg'⟩⁻¹, Subtype.ext ?_⟩
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hgt, show (j3a : Equiv.Perm (Fin 6156)) = j3Gen 0 from rfl, hga]
  group

end CFSG.Sporadic.SmallOddCore
