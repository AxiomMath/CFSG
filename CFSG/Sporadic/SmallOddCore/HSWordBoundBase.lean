
module

public import CFSG.Sporadic.SmallOddCore.HS
public import CFSG.Sporadic.SmallOddCore.AutCount
public import CFSG.Sporadic.Schreier.PairHSPairs
public import CFSG.Sporadic.Schreier.PairCounts
public meta import CFSG.Sporadic.Schreier.PairHSCheck
public meta import Certificates.Data.CFSGNative.PairSchreier.Counts
public import CFSG.Sporadic.Schreier.PairHSCertInputs
public import CFSG.Sporadic.Schreier.PairHSCheckInputs
public meta import CFSG.Sporadic.Schreier.PairHSCert
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import CFSG.Sporadic.SmallOddCore.HSWordBoundInputs
public import CFSG.Sporadic.Schreier.PairHSCheck
public import Certificates.Data.CFSGNative.PairSchreier.Counts
public import CFSG.Sporadic.SmallOddCore.HSCheckInputs

@[expose] public section

namespace CFSG.Sporadic.SmallOddCore

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative
open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native

def HSWordConds {G : Type*} [Group G] (x y : G) : Prop :=
  orderOf y = 5 ∧ orderOf (x * y) = 11 ∧ orderOf (x * y * x⁻¹ * y⁻¹) = 5 ∧
    orderOf (x * y ^ 2) = 10

theorem hsWordConds_map {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) (x y : G) : HSWordConds (f x) (f y) ↔ HSWordConds x y := by
  simp only [HSWordConds, ← map_mul, ← map_inv, ← map_pow, orderOf_injective f hf]

theorem hsWordConds_iff {G : Type*} [Group G] {x y : G} (hx : orderOf x = 2) :
    (orderOf y = 5 ∧ ∀ c ∈ hsWConds, orderOf (c.1.map fun b => if b then y else x).prod = c.2) ↔
      HSWordConds x y := by
  have hxi : x⁻¹ = x := by
    rw [inv_eq_iff_mul_eq_one, ← pow_two, ← hx, pow_orderOf_eq_one]
  simp only [HSWordConds, hsWConds, List.forall_mem_cons, List.not_mem_nil, false_implies,
    implies_true, and_true, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    Bool.false_eq_true, ite_false, ite_true]
  constructor
  · rintro ⟨hy, h1, h2, h3⟩
    have hy5 : y ^ 5 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
    have hyi : y⁻¹ = y * y * y * y := by
      rw [inv_eq_iff_mul_eq_one, ← hy5]
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    refine ⟨hy, h1, ?_, by rwa [pow_two]⟩
    rw [hxi, hyi]
    simpa only [mul_assoc] using h2
  · rintro ⟨hy, h1, h2, h3⟩
    have hy5 : y ^ 5 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
    have hyi : y⁻¹ = y * y * y * y := by
      rw [inv_eq_iff_mul_eq_one, ← hy5]
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    refine ⟨hy, h1, ?_, by rwa [pow_two] at h3⟩
    rw [hxi, hyi] at h2
    simpa only [mul_assoc] using h2

theorem map_subtype_centralizer {M : Type*} [Group M] (H : Subgroup M) (x : H) :
    (centralizer ({x} : Set H)).map H.subtype = H ⊓ centralizer ({(x : M)} : Set M) := by
  ext y
  simp only [mem_map, mem_inf, mem_centralizer_iff, Set.mem_singleton_iff, forall_eq,
    Subgroup.coe_subtype]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z.2, congrArg Subtype.val hz⟩
  · rintro ⟨hy, hyx⟩
    exact ⟨⟨y, hy⟩, Subtype.ext hyx, rfl⟩

theorem card_centralizer_mulAut {G : Type*} [Group G] (φ : MulAut G) (x : G) :
    Nat.card (centralizer ({φ x} : Set G)) = Nat.card (centralizer ({x} : Set G)) := by
  have e : (centralizer ({x} : Set G)).map φ.toMonoidHom = centralizer ({φ x} : Set G) := by
    ext y
    rw [Subgroup.mem_map_equiv, mem_centralizer_iff, mem_centralizer_iff]
    simp only [Set.mem_singleton_iff, forall_eq]
    constructor
    · intro h
      have := congrArg φ h
      simpa using this
    · intro h
      have := congrArg φ.symm h
      simpa using this
  rw [← e, Subgroup.card_map_of_injective φ.injective]

theorem ncard_conj_set_eq {M : Type*} [Group M] (H : Subgroup M) (a : H) :
    {x : H | ∃ g : H, x = g * a * g⁻¹}.ncard = (conjClass H (a : M)).ncard := by
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective]
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_ofPred_eq, mem_conjClass]
  constructor
  · rintro ⟨x, ⟨g, rfl⟩, rfl⟩
    exact ⟨g, g.2, by simp⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, hg⟩ * a * ⟨g, hg⟩⁻¹, ⟨⟨g, hg⟩, rfl⟩, by simp⟩

theorem hs_tp_rep_a : tp 3850 (hsCentTbl 5) = hsGen 0 := by
  have h := hs_rep_a
  rw [Bool.and_eq_true] at h
  exact (tblEq_iff_eq (rep_tp h.1) (hs_groupData.rep 0 (by simp [hsPGTbls]))).1 h.2

theorem hs_aut_conj_a (φ : MulAut hsP) : ∃ g : hsP, φ hsa0 = g * hsa0 * g⁻¹ := by
  obtain ⟨-, -, -, hrows, hcover, -, -, -⟩ := hs_involution_centralizers
  have hPR : hsP ≤ hsR := le_sup_left
  have key : ∀ x ∈ hsP, orderOf x = 2 → ∃ r ∈ hsRows, ∃ g ∈ hsP,
      x = g * tp 3850 r.rep * g⁻¹ ∧ r.outer = false ∧
      Nat.card ↥(hsP ⊓ centralizer ({x} : Set (Equiv.Perm (Fin 3850)))) = r.centOrder := by
    intro x hx hx2
    obtain ⟨r, hr, g, hg, rfl⟩ := hcover x (hPR hx) hx2
    have hrP : tp 3850 r.rep ∈ hsP := by
      have := hsP.mul_mem (hsP.mul_mem (hsP.inv_mem hg) hx) hg
      rwa [show g⁻¹ * (g * tp 3850 r.rep * g⁻¹) * g = tp 3850 r.rep by group] at this
    refine ⟨r, hr, g, hg, rfl, ?_, ?_⟩
    · by_contra h
      rw [Bool.not_eq_false] at h
      exact (hrows r hr).2.2.1.1 h hrP
    · rw [inf_centralizer_conj hsP hg, Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact (hrows r hr).2.2.2.2.1
  have hCa : Nat.card ↥(hsP ⊓ centralizer ({hsGen 0} : Set (Equiv.Perm (Fin 3850)))) = 7680 := by
    have h := (hrows _ List.mem_cons_self).2.2.2.2.1
    dsimp only at h
    rwa [hs_tp_rep_a] at h
  have hφa : orderOf ((φ hsa0 : hsP) : Equiv.Perm (Fin 3850)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
    exact hs_word_orders.1
  obtain ⟨r, hr, g, hg, hφ, hout, hcent⟩ := key _ (φ hsa0).2 hφa
  have hc : Nat.card ↥(hsP ⊓ centralizer ({((φ hsa0 : hsP) : Equiv.Perm (Fin 3850))} :
      Set (Equiv.Perm (Fin 3850)))) = 7680 := by
    rw [← map_subtype_centralizer, Subgroup.card_map_of_injective hsP.subtype_injective,
      card_centralizer_mulAut, ← Subgroup.card_map_of_injective hsP.subtype_injective,
      map_subtype_centralizer]
    exact hCa
  have hrc : r.centOrder = 7680 := hcent.symm.trans hc
  simp only [hsRows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · refine ⟨⟨g, hg⟩, Subtype.ext ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    show _ = g * hsGen 0 * g⁻¹
    dsimp only at hφ
    rw [hφ, hs_tp_rep_a]
  · simp at hrc
  · exact absurd hout (by decide)
  · exact absurd hout (by decide)

end CFSG.Sporadic.SmallOddCore
