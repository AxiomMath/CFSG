module

import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_1_12
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_14
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.theorem_3_3
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.InvariantIndexTwo
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.NormalComplement
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.OrderThree
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.TopResidual
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.theorem_2_5
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.theorem_2_6
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.theorem_6_1
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.theorem_6_8
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.theorem_9_1
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.theorem_11_15
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.V.theorem_8_15
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Remaining
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixII.proposition_2
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.SharpNearField
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.PSL2
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.Suzuki

namespace CFSG
end CFSG
open CFSG

/-!
# Huppert-Blackburn XI.11.16

The statement follows Volume III, printed page 286.  In particular, the
source has four alternatives (`PGL`, `PSL`, `M`, and `Sz`); it is not the
two-alternative odd-degree recognition statement previously recorded here.
The `FaithfulSMul` assumption records that the source's permutation group is
a faithful subgroup of the symmetric group on its permuted symbols.
-/

namespace CFSG.BenderSuzuki
namespace External

open _root_.CFSG.BenderSuzuki.MatrixGroups
open PFAppendixIII

universe u v w

private theorem huppert_XI_2_1_fixedPointFree_of_odd_card_fixed_triple
    {G : Type u} [Group G] [Finite G]
    (phi : MulAut G) (hodd : Odd (Nat.card G))
    (hfixed3 : ∀ x y z : G,
      phi x = x → phi y = y → phi z = z →
        x = y ∨ x = z ∨ y = z) :
    MonoidHom.FixedPointFree phi := by
  intro x hx
  by_contra hx1
  have hxpow : phi (x ^ 2) = x ^ 2 := by simp [hx]
  rcases hfixed3 1 x (x ^ 2) (by simp) hx hxpow with
    h1x | h1sq | hxsq
  · exact hx1 h1x.symm
  · have hsq : x ^ 2 = 1 := h1sq.symm
    have hord_dvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
    rcases (Nat.dvd_prime Nat.prime_two).mp hord_dvd with hord | hord
    · exact hx1 (orderOf_eq_one_iff.mp hord)
    · exact hodd.not_two_dvd_nat (hord ▸ orderOf_dvd_natCard x)
  · have hx_eq_one : x = 1 := by
      apply mul_left_cancel (a := x)
      simpa [pow_two] using hxsq
    exact hx1 hx_eq_one

private theorem huppert_XI_2_4_quaternionGroup_eq_a_parameter_of_orderOf_eq_two
    (m : ℕ) [NeZero m] {q : QuaternionGroup m} (hq : orderOf q = 2) :
    q = QuaternionGroup.a (m : ZMod (2 * m)) := by
  have hm_pos : 0 < m := NeZero.pos m
  have hm_lt : m < 2 * m := by omega
  cases q with
  | xa i =>
      rw [QuaternionGroup.orderOf_xa] at hq
      omega
  | a i =>
      rw [QuaternionGroup.orderOf_a] at hq
      have hdiv_mul := Nat.div_mul_cancel (Nat.gcd_dvd_left (2 * m) i.val)
      rw [hq] at hdiv_mul
      have hgcd : Nat.gcd (2 * m) i.val = m := by omega
      have hm_dvd_i : m ∣ i.val := by
        obtain ⟨k, hk⟩ := Nat.gcd_dvd_right (2 * m) i.val
        refine ⟨k, ?_⟩
        calc
          i.val = Nat.gcd (2 * m) i.val * k := hk
          _ = m * k := by rw [hgcd]
      obtain ⟨k, hk⟩ := hm_dvd_i
      have hi_lt : i.val < 2 * m := ZMod.val_lt i
      have hi_ne_zero : i.val ≠ 0 := by
        intro hi_zero
        have hi : i = 0 := (ZMod.val_eq_zero i).mp hi_zero
        have hq' : 2 * m / (2 * m) = 2 := by simpa [hi] using hq
        have hone : 2 * m / (2 * m) = 1 := Nat.div_self (by omega)
        omega
      have hk_ne_zero : k ≠ 0 := by
        intro hk_zero
        apply hi_ne_zero
        simp [hk, hk_zero]
      have hk_lt_two : k < 2 := by
        apply (Nat.mul_lt_mul_right hm_pos).mp
        simpa [Nat.mul_comm, hk] using hi_lt
      have hk_eq : k = 1 := by omega
      congr 1
      apply ZMod.val_injective
      simp [hk, hk_eq, ZMod.val_natCast, Nat.mod_eq_of_lt hm_lt]

private theorem huppert_XI_2_4_isCyclic_of_isMulCommutative_unique_order_two
    {G : Type u} [Group G] [Finite G]
    (hGp : IsPGroup 2 G)
    (hunique_order_two : ∀ x y : G, orderOf x = 2 → orderOf y = 2 → x = y)
    (A : Subgroup G) (hAcomm : IsMulCommutative A) :
    IsCyclic A := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : IsMulCommutative A := hAcomm
  have hAp : IsPGroup 2 A := hGp.to_subgroup A
  haveI : Fact (IsPGroup 2 A) := ⟨hAp⟩
  let Ω : Subgroup A := omega₁ (G := A) (p := 2)
  have hΩelem : IsElementaryAbelian 2 Ω := by
    simpa [Ω] using IsElementaryAbelian.omega₁_of_isMulCommutative (p := 2) (G := A)
  haveI : IsElementaryAbelian 2 Ω := hΩelem
  have hΩ_card_le_two : Nat.card Ω ≤ 2 := by
    let f : Ω → Bool := fun x => decide (x = 1)
    have hf_inj : Function.Injective f := by
      intro x y hxy
      by_cases hx1 : x = 1
      · have hy1 : y = 1 := by
          by_contra hy1
          have hxval : f x = true := by simp [f, hx1]
          have hyval : f y = false := by simp [f, hy1]
          simp [hxval, hyval] at hxy
        simp [hx1, hy1]
      · have hy1 : y ≠ 1 := by
          intro hy1
          have hxval : f x = false := by simp [f, hx1]
          have hyval : f y = true := by simp [f, hy1]
          simp [hxval, hyval] at hxy
        apply Subtype.ext
        apply Subtype.ext
        have hxpow : x ^ (2 : ℕ) = 1 := by
          exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
            (IsElementaryAbelian.exponent_dvd_p 2 Ω) x
        have hypow : y ^ (2 : ℕ) = 1 := by
          exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
            (IsElementaryAbelian.exponent_dvd_p 2 Ω) y
        have hxord : orderOf ((x : Ω) : A) = 2 := by
          refine (orderOf_eq_prime_iff (x := ((x : Ω) : A)) (p := 2)).2 ⟨?_, ?_⟩
          · simpa using congrArg Subtype.val hxpow
          · intro hxA1
            exact hx1 (Subtype.ext hxA1)
        have hyord : orderOf ((y : Ω) : A) = 2 := by
          refine (orderOf_eq_prime_iff (x := ((y : Ω) : A)) (p := 2)).2 ⟨?_, ?_⟩
          · simpa using congrArg Subtype.val hypow
          · intro hyA1
            exact hy1 (Subtype.ext hyA1)
        have hxordG : orderOf (((x : Ω) : A) : G) = 2 := by
          simpa [Subgroup.orderOf_coe] using hxord
        have hyordG : orderOf (((y : Ω) : A) : G) = 2 := by
          simpa [Subgroup.orderOf_coe] using hyord
        exact hunique_order_two (((x : Ω) : A) : G) (((y : Ω) : A) : G) hxordG hyordG
    have hcard_le : Nat.card Ω ≤ Nat.card Bool := Nat.card_le_card_of_injective f hf_inj
    simpa using hcard_le
  have hquot_card_le_two : Nat.card (A ⧸ frattini A) ≤ 2 := by
    have hΩ_card_eq_quot : Nat.card Ω = Nat.card (A ⧸ frattini A) := by
      simpa [Ω] using
        section9_c92_omega1_card_eq_card_quotient_frattini_of_commutative (p := 2) A
    simpa [hΩ_card_eq_quot] using hΩ_card_le_two
  have hquot_elem : IsElementaryAbelian 2 (A ⧸ frattini A) := by
    exact isElementaryAbelian_quotient_frattini (R := A) (p := 2)
  haveI : IsElementaryAbelian 2 (A ⧸ frattini A) := hquot_elem
  have hquot_rank_le_one : generatorRank (A ⧸ frattini A) ≤ 1 := by
    have hquot_card_eq : Nat.card (A ⧸ frattini A) = 2 ^ generatorRank (A ⧸ frattini A) := by
      simpa using elementaryAbelian_card_eq_pow_generatorRank (p := 2) (A ⧸ frattini A)
    by_contra hle
    have htwo_le : 2 ≤ generatorRank (A ⧸ frattini A) :=
      Nat.succ_le_of_lt (Nat.lt_of_not_ge hle)
    have hpow_ge : 2 ^ 2 ≤ 2 ^ generatorRank (A ⧸ frattini A) :=
      Nat.pow_le_pow_right (by decide : 0 < 2) htwo_le
    have hpow_le_two : 2 ^ generatorRank (A ⧸ frattini A) ≤ 2 := by
      simpa [hquot_card_eq] using hquot_card_le_two
    have : 4 ≤ 2 := by
      simpa using hpow_ge.trans hpow_le_two
    omega
  have hrank_le_one : generatorRank A ≤ 1 :=
    (generatorRank_le_generatorRank_quotient_frattini (p := 2) A).trans hquot_rank_le_one
  exact isCyclic_of_generatorRank_le_one (G := A) hrank_le_one


private theorem huppert_XI_2_4_invariantNormal_inversion_and_cyclic
    {G : Type u} [Group G] [Finite G]
    (phi : G ≃* G) (hphi : Function.Involutive phi)
    (hfixed3 : ∀ x y z : G,
      phi x = x → phi y = y → phi z = z → x = y ∨ x = z ∨ y = z)
    (H : Subgroup G) [H.Normal]
    (hHphi : ∀ g : G, g ∈ H ↔ phi g ∈ H)
    (hindexEven : Even H.index)
    (hodd : ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 →
      ∀ Q : Sylow q G, IsCyclic Q)
    (htwo : ∀ Q : Sylow 2 G,
      IsCyclic Q ∨
        ∃ k : ℕ, 2 ≤ k ∧ IsPGroup 2 (QuaternionGroup k) ∧
          Nonempty (Q ≃* QuaternionGroup k)) :
    (∀ h : H, phi (h : G) = (h : G)⁻¹) ∧ IsCyclic H := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  letI : Fintype H := Fintype.ofFinite H
  letI : Fintype (G ⧸ H) := Fintype.ofFinite (G ⧸ H)
  let phiQ : MulAut (G ⧸ H) :=
    BenderSuzuki.External.invariantQuotientAut phi H hHphi
  have hphiQ : Function.Involutive phiQ := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective H q
    simp only [phiQ, BenderSuzuki.External.invariantQuotientAut_mk']
    rw [hphi g]
  let sigma : Equiv.Perm (G ⧸ H) := phiQ.toEquiv
  have hsigma_sq : sigma ^ 2 ^ 1 = 1 := by
    simp only [pow_one, pow_two]
    ext q
    exact hphiQ q
  have hquot_even : 2 ∣ Fintype.card (G ⧸ H) := by
    rw [← Nat.card_eq_fintype_card, ← H.index_eq_card]
    exact even_iff_two_dvd.mp hindexEven
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨q, hqfixed, hqne⟩ :=
    Equiv.Perm.exists_fixed_point_of_prime'
      (p := 2) (n := 1) hquot_even hsigma_sq
      (a := (1 : G ⧸ H)) (by simp [sigma, phiQ])
  obtain ⟨x, hxq⟩ := QuotientGroup.mk'_surjective H q
  subst q
  have hxcoset :
      (QuotientGroup.mk' H) (phi x) = (QuotientGroup.mk' H) x := by
    change
      BenderSuzuki.External.invariantQuotientAut phi H hHphi
          (QuotientGroup.mk' H x) =
        QuotientGroup.mk' H x at hqfixed
    rw [BenderSuzuki.External.invariantQuotientAut_mk'] at hqfixed
    exact hqfixed
  have htheta_x : phi x / x ∈ H :=
    QuotientGroup.eq_iff_div_mem.mp hxcoset
  have hx_not_mem : x ∉ H := by
    intro hx
    apply hqne
    exact (QuotientGroup.eq_one_iff x).mpr hx
  let rep : H ⊕ H → G
    | Sum.inl h => h
    | Sum.inr h => (h : G) * x
  have hrep_injective : Function.Injective rep := by
    intro a b hab
    cases a with
    | inl a =>
        cases b with
        | inl b =>
            apply congrArg Sum.inl
            apply Subtype.ext
            simpa [rep] using hab
        | inr b =>
            exfalso
            apply hx_not_mem
            change (a : G) = (b : G) * x at hab
            have hx_eq : x = (b : G)⁻¹ * (a : G) := by
              calc
                x = (b : G)⁻¹ * ((b : G) * x) := by simp
                _ = (b : G)⁻¹ * (a : G) := by rw [hab]
            rw [hx_eq]
            exact H.mul_mem (H.inv_mem b.property) a.property
    | inr a =>
        cases b with
        | inl b =>
            exfalso
            apply hx_not_mem
            change (a : G) * x = (b : G) at hab
            have hx_eq : x = (a : G)⁻¹ * (b : G) := by
              calc
                x = (a : G)⁻¹ * ((a : G) * x) := by simp
                _ = (a : G)⁻¹ * (b : G) := by rw [hab]
            rw [hx_eq]
            exact H.mul_mem (H.inv_mem a.property) b.property
        | inr b =>
            apply congrArg Sum.inr
            apply Subtype.ext
            have : (a : G) = (b : G) := by
              exact mul_right_cancel hab
            exact this
  let theta : G → G := fun g => phi g / g
  have htheta_rep_mem (z : H ⊕ H) : theta (rep z) ∈ H := by
    cases z with
    | inl h =>
        exact H.div_mem ((hHphi h).mp h.property) h.property
    | inr h =>
        have hphih : phi (h : G) ∈ H := (hHphi h).mp h.property
        change phi ((h : G) * x) / ((h : G) * x) ∈ H
        rw [map_mul]
        simpa [div_eq_mul_inv, mul_assoc] using
          H.mul_mem (H.mul_mem hphih htheta_x) (H.inv_mem h.property)
  let thetaH : H ⊕ H → H := fun z => ⟨theta (rep z), htheta_rep_mem z⟩
  have htheta_eq_fixed {a b : H ⊕ H} (hab : thetaH a = thetaH b) :
      phi ((rep a)⁻¹ * rep b) = (rep a)⁻¹ * rep b := by
    have habv : theta (rep a) = theta (rep b) := congrArg Subtype.val hab
    rw [map_mul, map_inv]
    calc
      (phi (rep a))⁻¹ * phi (rep b) =
          (phi (rep a))⁻¹ * (phi (rep b) * (rep b)⁻¹) * rep b := by group
      _ = (phi (rep a))⁻¹ * (phi (rep a) * (rep a)⁻¹) * rep b := by
        rw [show phi (rep b) * (rep b)⁻¹ = phi (rep a) * (rep a)⁻¹ by
          simpa [theta, div_eq_mul_inv] using habv.symm]
      _ = (rep a)⁻¹ * rep b := by group
  have hfiber : ∀ y : H,
      ((Finset.univ : Finset (H ⊕ H)).filter fun z => thetaH z = y).card ≤ 2 := by
    intro y
    by_contra hle
    have hthree : 3 ≤
        ((Finset.univ : Finset (H ⊕ H)).filter fun z => thetaH z = y).card := by
      omega
    obtain ⟨s, hs, hscard⟩ := Finset.exists_subset_card_eq hthree
    rw [Finset.card_eq_three] at hscard
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := hscard
    have ha_mem := hs (by simp : a ∈ ({a, b, c} : Finset (H ⊕ H)))
    have hb_mem := hs (by simp : b ∈ ({a, b, c} : Finset (H ⊕ H)))
    have hc_mem := hs (by simp : c ∈ ({a, b, c} : Finset (H ⊕ H)))
    have ha : thetaH a = y := (Finset.mem_filter.mp ha_mem).2
    have hb : thetaH b = y := (Finset.mem_filter.mp hb_mem).2
    have hc : thetaH c = y := (Finset.mem_filter.mp hc_mem).2
    have hfixab := htheta_eq_fixed (ha.trans hb.symm)
    have hfixac := htheta_eq_fixed (ha.trans hc.symm)
    rcases hfixed3 1 ((rep a)⁻¹ * rep b) ((rep a)⁻¹ * rep c)
        (by simp) hfixab hfixac with h | h | h
    · apply hab
      apply hrep_injective
      calc
        rep a = rep a * 1 := by simp
        _ = rep a * ((rep a)⁻¹ * rep b) := by rw [h]
        _ = rep b := by group
    · apply hac
      apply hrep_injective
      calc
        rep a = rep a * 1 := by simp
        _ = rep a * ((rep a)⁻¹ * rep c) := by rw [h]
        _ = rep c := by group
    · apply hbc
      apply hrep_injective
      exact mul_left_cancel h
  have hcard_bound :=
    Finset.card_le_mul_card_image
      (f := thetaH) (Finset.univ : Finset (H ⊕ H)) 2
      (fun y _ => hfiber y)
  have himage_card :
      (Finset.image thetaH (Finset.univ : Finset (H ⊕ H))).card =
        Fintype.card H := by
    have himage_le :
        (Finset.image thetaH (Finset.univ : Finset (H ⊕ H))).card ≤
          Fintype.card H := Finset.card_le_univ _
    have hcard_bound' :
        2 * Fintype.card H ≤
          2 * (Finset.image thetaH (Finset.univ : Finset (H ⊕ H))).card := by
      simpa [two_mul] using hcard_bound
    omega
  have himage_univ :
      Finset.image thetaH (Finset.univ : Finset (H ⊕ H)) = Finset.univ :=
    Finset.eq_univ_of_card _ himage_card
  have htheta_surjective : Function.Surjective thetaH := by
    intro y
    have hy : y ∈ Finset.image thetaH (Finset.univ : Finset (H ⊕ H)) := by
      rw [himage_univ]
      simp
    obtain ⟨z, -, hz⟩ := Finset.mem_image.mp hy
    exact ⟨z, hz⟩
  have htheta_inv (g : G) : phi (theta g) = (theta g)⁻¹ := by
    change phi (phi g / g) = (phi g / g)⁻¹
    rw [map_div, hphi g]
    simp
  have hphi_inv_on_H (h : H) : phi (h : G) = (h : G)⁻¹ := by
    obtain ⟨z, hz⟩ := htheta_surjective h
    have hzv : theta (rep z) = (h : G) := congrArg Subtype.val hz
    rw [← hzv]
    exact htheta_inv (rep z)
  have hcomm : ∀ a b : H, a * b = b * a := by
    intro a b
    apply Subtype.ext
    have hab := hphi_inv_on_H (a * b)
    change phi ((a : G) * (b : G)) = ((a : G) * (b : G))⁻¹ at hab
    rw [map_mul, hphi_inv_on_H a, hphi_inv_on_H b, mul_inv_rev] at hab
    have h := congrArg Inv.inv hab
    simpa using h.symm
  letI : IsMulCommutative H := ⟨⟨hcomm⟩⟩
  letI : CommGroup H := IsMulCommutative.instCommGroup
  have hHZ : IsZGroup H := by
    constructor
    intro q hq P
    letI : Fact q.Prime := ⟨hq⟩
    let PA : Subgroup G := (P : Subgroup H).map H.subtype
    have hPAp : IsPGroup q PA := P.isPGroup'.map H.subtype
    obtain ⟨Q, hPA_le_Q⟩ := hPAp.exists_le_sylow
    have hPAcyclic : IsCyclic PA := by
      by_cases hq2 : q = 2
      · subst q
        rcases htwo Q with hQcyclic | ⟨k, hk, hkP, ⟨eQ⟩⟩
        · exact Subgroup.isCyclic_of_le hPA_le_Q
        · haveI : NeZero k := ⟨by omega⟩
          let PAQ : Subgroup Q := PA.subgroupOf Q
          have huniqueQ :
              ∀ x y : Q, orderOf x = 2 → orderOf y = 2 → x = y := by
            intro x y hx hy
            apply eQ.injective
            have hx' : orderOf (eQ x) = 2 := by
              simpa using (orderOf_injective eQ.toMonoidHom eQ.injective x).trans hx
            have hy' : orderOf (eQ y) = 2 := by
              simpa using (orderOf_injective eQ.toMonoidHom eQ.injective y).trans hy
            exact
              (huppert_XI_2_4_quaternionGroup_eq_a_parameter_of_orderOf_eq_two k hx').trans
                (huppert_XI_2_4_quaternionGroup_eq_a_parameter_of_orderOf_eq_two k hy').symm
          have hPA_le_H : PA ≤ H := by
            intro g hg
            rcases hg with ⟨p, -, rfl⟩
            exact p.property
          have hPAQcomm : IsMulCommutative PAQ := by
            refine ⟨⟨fun a b => ?_⟩⟩
            apply Subtype.ext
            apply Subtype.ext
            let aH : H := ⟨((a : Q) : G), hPA_le_H a.property⟩
            let bH : H := ⟨((b : Q) : G), hPA_le_H b.property⟩
            change ((aH : G) * (bH : G)) = ((bH : G) * (aH : G))
            exact congrArg Subtype.val (mul_comm aH bH)
          have hPAQcyclic : IsCyclic PAQ :=
            huppert_XI_2_4_isCyclic_of_isMulCommutative_unique_order_two
              Q.isPGroup' huniqueQ PAQ hPAQcomm
          exact (Subgroup.subgroupOfEquivOfLe hPA_le_Q).isCyclic.mp hPAQcyclic
      · have hQcyclic : IsCyclic Q := hodd q hq2 Q
        letI : IsCyclic Q := hQcyclic
        exact Subgroup.isCyclic_of_le hPA_le_Q
    let eP : P ≃* PA :=
      Subgroup.equivMapOfInjective (P : Subgroup H) H.subtype H.subtype_injective
    exact eP.isCyclic.mpr hPAcyclic
  letI : IsZGroup H := hHZ
  exact ⟨hphi_inv_on_H, inferInstance⟩

private theorem huppert_XI_2_4_invariantNormal_cyclic
    {G : Type u} [Group G] [Finite G]
    (phi : G ≃* G) (hphi : Function.Involutive phi)
    (hfixed3 : ∀ x y z : G,
      phi x = x → phi y = y → phi z = z → x = y ∨ x = z ∨ y = z)
    (H : Subgroup G) [H.Normal]
    (hHphi : ∀ g : G, g ∈ H ↔ phi g ∈ H)
    (hindexEven : Even H.index)
    (hodd : ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 →
      ∀ Q : Sylow q G, IsCyclic Q)
    (htwo : ∀ Q : Sylow 2 G,
      IsCyclic Q ∨
        ∃ k : ℕ, 2 ≤ k ∧ IsPGroup 2 (QuaternionGroup k) ∧
          Nonempty (Q ≃* QuaternionGroup k)) :
    IsCyclic H :=
  (huppert_XI_2_4_invariantNormal_inversion_and_cyclic
    phi hphi hfixed3 H hHphi hindexEven hodd htwo).2


private def pgl2Map
    {K : Type u} {L : Type w} [Field K] [Field L]
    (e : K →+* L) :
    Matrix.ProjGenLinGroup (Fin 2) K →*
      Matrix.ProjGenLinGroup (Fin 2) L := by
  let f : GL (Fin 2) K →*
      Matrix.ProjGenLinGroup (Fin 2) L :=
    Matrix.ProjGenLinGroup.mk.comp
      (Matrix.GeneralLinearGroup.map e)
  apply Matrix.ProjGenLinGroup.lift f
  ext a
  change Matrix.ProjGenLinGroup.mk
      (Matrix.GeneralLinearGroup.map e
        (Matrix.GeneralLinearGroup.scalar (Fin 2) a)) = 1
  rw [← MonoidHom.mem_ker, Matrix.ProjGenLinGroup.ker_mk,
    Matrix.GeneralLinearGroup.center_eq_range_scalar]
  refine ⟨Units.map e a, ?_⟩
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.GeneralLinearGroup.map,
      Matrix.GeneralLinearGroup.scalar]

set_option backward.isDefEq.respectTransparency false in
private theorem pgl2Map_mk
    {K : Type u} {L : Type w} [Field K] [Field L]
    (e : K →+* L) (A : GL (Fin 2) K) :
    pgl2Map e (Matrix.ProjGenLinGroup.mk A) =
      Matrix.ProjGenLinGroup.mk
        (Matrix.GeneralLinearGroup.map e A) := by
  unfold pgl2Map
  exact Matrix.ProjGenLinGroup.lift_mk _ A

private def pgl2EquivOfRingEquiv
    {K : Type u} {L : Type w} [Field K] [Field L]
    (e : K ≃+* L) :
    Matrix.ProjGenLinGroup (Fin 2) K ≃*
      Matrix.ProjGenLinGroup (Fin 2) L := by
  let f := pgl2Map e.toRingHom
  let g := pgl2Map e.symm.toRingHom
  apply MonoidHom.toMulEquiv f g
  · apply MonoidHom.ext
    intro x
    rcases Matrix.ProjGenLinGroup.mk_surjective x with ⟨A, rfl⟩
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, f, g, pgl2Map_mk]
    apply congrArg Matrix.ProjGenLinGroup.mk
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    simp
  · apply MonoidHom.ext
    intro x
    rcases Matrix.ProjGenLinGroup.mk_surjective x with ⟨A, rfl⟩
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, f, g, pgl2Map_mk]
    apply congrArg Matrix.ProjGenLinGroup.mk
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    simp

private theorem frobeniusKernel_centralizer_singleton_eq_kernel
    {H : Type*} [Group H] [Finite H]
    (F D : Subgroup H)
    (hFrob : IsFrobeniusGroupWithKernelComplement F D)
    (z : F) (hzne : z ≠ 1) (hzcenter : z ∈ Subgroup.center F) :
    Subgroup.centralizer ({(z : H)} : Set H) = F := by
  apply le_antisymm
  · intro h hh
    obtain ⟨fd, hfd, _hfd_unique⟩ :=
      hFrob.isComplement'.existsUnique h
    let f : F := fd.1
    let d : D := fd.2
    have hdecomp : (f : H) * (d : H) = h := by
      simpa [f, d] using hfd
    have hcomm : h * (z : H) = (z : H) * h :=
      Subgroup.mem_centralizer_singleton_iff.mp hh
    have hzf : (z : H) * (f : H) = (f : H) * (z : H) := by
      exact congrArg Subtype.val
        ((Subgroup.mem_center_iff.mp hzcenter f).symm)
    have hdcomm : (d : H) * (z : H) = (z : H) * (d : H) := by
      apply mul_left_cancel (a := (f : H))
      calc
        (f : H) * ((d : H) * (z : H)) =
            h * (z : H) := by rw [← mul_assoc, hdecomp]
        _ = (z : H) * h := hcomm
        _ = (z : H) * ((f : H) * (d : H)) := by rw [hdecomp]
        _ = (f : H) * ((z : H) * (d : H)) := by
              rw [← mul_assoc, hzf, mul_assoc]
    by_cases hd : d = 1
    · have hhf : (h : H) = (f : H) := by
        rw [← hdecomp, hd, Subgroup.coe_one, mul_one]
      rw [hhf]
      exact f.property
    · have hzmem :
          (z : H) ∈ elementCentralizerIn F (d : H) := by
        exact ⟨z.property,
          Subgroup.mem_centralizer_singleton_iff.mpr hdcomm.symm⟩
      have hcent :=
        (lemma_3_1 F D hFrob.kernel_ne_bot hFrob.complement_ne_bot
          hFrob.normal hFrob.isComplement').mp hFrob d hd
      rw [hcent] at hzmem
      have hzone : z = 1 := by
        apply Subtype.ext
        simpa using hzmem
      exact (hzne hzone).elim
  · intro f hf
    rw [Subgroup.mem_centralizer_singleton_iff]
    let fF : F := ⟨f, hf⟩
    exact congrArg Subtype.val
      (Subgroup.mem_center_iff.mp hzcenter fF)

private theorem huppert_blackburn_XI_frobeniusKernel_uniqueFixedPoint
    {G Omega : Type*} [Group G] [MulAction G Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob :
      IsFrobeniusGroupWithKernelComplement F
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (z : F) (hzne : z ≠ 1) :
    ∀ c : Omega,
      ((((z : MulAction.stabilizer G a) : G) • c = c) ↔ c = a) := by
  intro c
  constructor
  · intro hzc
    by_contra hca
    let cSub : SubMulAction.ofStabilizer G a := ⟨c, hca⟩
    have hzcSub :
        (z : MulAction.stabilizer G a) • cSub = cSub := by
      exact Subtype.ext hzc
    letI : MulAction.IsMultiplyPretransitive G Omega 2 := htwo
    letI : MulAction.IsPretransitive G Omega :=
      MulAction.isPretransitive_of_is_two_pretransitive
    have hstab_multi :
        MulAction.IsMultiplyPretransitive
            (MulAction.stabilizer G a)
            (SubMulAction.ofStabilizer G a) 1 :=
      (SubMulAction.ofStabilizer.isMultiplyPretransitive
        (G := G) (a := a)).mp htwo
    have hpretrans :
        MulAction.IsPretransitive
          (MulAction.stabilizer G a)
          (SubMulAction.ofStabilizer G a) :=
      (MulAction.is_one_pretransitive_iff
        (G := MulAction.stabilizer G a)
        (α := SubMulAction.ofStabilizer G a)).mp hstab_multi
    have hregular :
        ∀ x y : SubMulAction.ofStabilizer G a,
          ∃! f : F, (f : MulAction.stabilizer G a) • x = y :=
      huppert_blackburn_XI_regular_of_isComplement_stabilizer
        hFrob.isComplement' hpretrans
    obtain ⟨k, _hk, hunique⟩ := hregular cSub cSub
    have hzk : z = k := hunique z hzcSub
    have honek : (1 : F) = k := hunique 1 (by simp)
    exact hzne (hzk.trans honek.symm)
  · intro hca
    rw [hca]
    exact (z : MulAction.stabilizer G a).property

private theorem huppert_blackburn_XI_frobeniusKernel_centralizer_eq_map
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob :
      IsFrobeniusGroupWithKernelComplement F
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (z : F) (hzne : z ≠ 1) (hzcenter : z ∈ Subgroup.center F) :
    Subgroup.centralizer
        ({((z : MulAction.stabilizer G a) : G)} : Set G) =
      F.map (MulAction.stabilizer G a).subtype := by
  apply le_antisymm
  · intro g hg
    have hcomm :
        g * (((z : MulAction.stabilizer G a) : G)) =
          (((z : MulAction.stabilizer G a) : G)) * g :=
      Subgroup.mem_centralizer_singleton_iff.mp hg
    have hzfix :
        (((z : MulAction.stabilizer G a) : G)) • (g • a) = g • a := by
      calc
        (((z : MulAction.stabilizer G a) : G)) • (g • a) =
            ((((z : MulAction.stabilizer G a) : G) * g) • a) := by
              rw [mul_smul]
        _ = ((g * (((z : MulAction.stabilizer G a) : G))) • a) := by
              rw [hcomm]
        _ = g • ((((z : MulAction.stabilizer G a) : G)) • a) := by
              rw [mul_smul]
        _ = g • a := by
              rw [(z : MulAction.stabilizer G a).property]
    have hga : g • a = a :=
      (huppert_blackburn_XI_frobeniusKernel_uniqueFixedPoint
        htwo a b hab F hFrob z hzne (g • a)).mp hzfix
    let gStab : MulAction.stabilizer G a :=
      ⟨g, MulAction.mem_stabilizer_iff.mpr hga⟩
    have hgStabCent :
        gStab ∈ Subgroup.centralizer
          ({(z : MulAction.stabilizer G a)} :
            Set (MulAction.stabilizer G a)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext hcomm
    have hgStabF : gStab ∈ F := by
      rw [← frobeniusKernel_centralizer_singleton_eq_kernel
        F _ hFrob z hzne hzcenter]
      exact hgStabCent
    exact Subgroup.mem_map.mpr ⟨gStab, hgStabF, rfl⟩
  · intro g hg
    rcases Subgroup.mem_map.mp hg with ⟨f, hf, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hfcent :
        (f : MulAction.stabilizer G a) ∈
          Subgroup.centralizer
            ({(z : MulAction.stabilizer G a)} :
              Set (MulAction.stabilizer G a)) := by
      rw [frobeniusKernel_centralizer_singleton_eq_kernel
        F _ hFrob z hzne hzcenter]
      exact hf
    exact congrArg Subtype.val
      (Subgroup.mem_centralizer_singleton_iff.mp hfcent)

@[implicit_reducible]
private noncomputable def rightNearFieldFieldOfComm
    (K : Type*) [PFAppendixII.RightNearField K]
    (hcomm : ∀ x y : K, x * y = y * x) : Field K := by
  letI : Ring K :=
    { (inferInstance : PFAppendixII.RightNearField K) with
      left_distrib := by
        intro a b c
        calc
          a * (b + c) = (b + c) * a := hcomm _ _
          _ = b * a + c * a :=
            PFAppendixII.RightNearField.right_distrib _ _ _
          _ = a * b + a * c := by rw [hcomm b a, hcomm c a] }
  exact
    ({ exists_pair_ne := ⟨0, 1, zero_ne_one⟩
       mul_comm := hcomm
       mul_inv_cancel := fun {a} ha =>
         ⟨a⁻¹, mul_inv_cancel₀ ha⟩ } : IsField K).toField

private theorem huppert_XI_2_1_units_cyclic_of_two_power_card
    {K : Type u} [PFAppendixII.RightNearField K] [Finite K]
    {f : ℕ} (hf : 0 < f) (hKcard : Nat.card K = 2 ^ f)
    (phi : MulAut Kˣ) (hphi : Function.Involutive phi)
    (hfixed3 : ∀ x y z : Kˣ,
      phi x = x → phi y = y → phi z = z →
        x = y ∨ x = z ∨ y = z) :
    IsCyclic Kˣ := by
  have hKcardEven : Even (Nat.card K) := by
    rw [hKcard]
    exact Nat.even_pow.mpr ⟨even_two, hf.ne'⟩
  have hUnitsOdd : Odd (Nat.card Kˣ) := by
    rw [Nat.card_units]
    exact Nat.Even.sub_odd Nat.card_pos hKcardEven odd_one
  have hfixedPointFree : MonoidHom.FixedPointFree phi :=
    huppert_XI_2_1_fixedPointFree_of_odd_card_fixed_triple phi hUnitsOdd hfixed3
  have hcommUnits : ∀ x y : Kˣ, x * y = y * x := by
    intro x y
    exact (hfixedPointFree.commute_all_of_involutive hphi x y).eq
  have hcomm : ∀ x y : K, x * y = y * x := by
    intro x y
    by_cases hx : x = 0
    · simp [hx]
    by_cases hy : y = 0
    · simp [hy]
    let ux : Kˣ := Units.mk0 x hx
    let uy : Kˣ := Units.mk0 y hy
    have hxy : ux * uy = uy * ux := hcommUnits ux uy
    simpa [ux, uy] using congrArg (fun z : Kˣ => (z : K)) hxy
  letI : Field K := rightNearFieldFieldOfComm K hcomm
  infer_instance

private theorem dicksonIndexTwoModel_odd_characteristic_even_degree
    {K : Type*} [PFAppendixII.RightNearField K] [Finite K]
    {p f r m : ℕ}
    (hp : Nat.Prime p)
    (hKcard : Nat.card K = p ^ f)
    (hchar : addOrderOf (1 : K) = p)
    (hmodel : PFAppendixII.IsDicksonIndexTwoModel K r m) :
    Odd p ∧ Even f := by
  rcases hmodel with ⟨hr, hrne, hmpos, hdata⟩
  dsimp only at hdata
  rcases hdata with ⟨hrFact, e, heone, _hsquare, _hnonsquare, _hcenter⟩
  letI : Fact (Nat.Prime r) := hrFact
  have hdegree_ne : 2 * m ≠ 0 := by omega
  have hGForder :
      addOrderOf (1 : GaloisField r (2 * m)) = r :=
    CharP.eq (GaloisField r (2 * m))
      (CharP.addOrderOf_one (GaloisField r (2 * m)))
      (inferInstance : CharP (GaloisField r (2 * m)) r)
  have hcharR : addOrderOf (1 : K) = r := by
    calc
      addOrderOf (1 : K) = addOrderOf (e 1) :=
        (e.addOrderOf_eq 1).symm
      _ = addOrderOf (1 : GaloisField r (2 * m)) := by rw [heone]
      _ = r := hGForder
  have hpr : p = r := hchar.symm.trans hcharR
  have hpne : p ≠ 2 := by
    intro hp2
    exact hrne (hpr.symm.trans hp2)
  have hKcardR : Nat.card K = r ^ (2 * m) := by
    calc
      Nat.card K = Nat.card (GaloisField r (2 * m)) :=
        Nat.card_congr e.toEquiv
      _ = r ^ (2 * m) := GaloisField.card r (2 * m) hdegree_ne
  have hpow : p ^ f = p ^ (2 * m) := by
    calc
      p ^ f = Nat.card K := hKcard.symm
      _ = r ^ (2 * m) := hKcardR
      _ = p ^ (2 * m) := by rw [hpr]
  have hf : f = 2 * m :=
    Nat.pow_right_injective hp.two_le hpow
  refine ⟨hp.odd_of_ne_two hpne, ?_⟩
  refine ⟨m, ?_⟩
  omega

private theorem sharpTriple_of_card_eq_descFactorial
    {G : Type u} {Omega : Type v}
    [Group G] [Finite G] [MulAction G Omega] [Fintype Omega]
    (hcard : Nat.card G = (Fintype.card Omega).descFactorial 3)
    (hat_most_two_fixed_points :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
          ¬ (g • a = a ∧ g • b = b ∧ g • c = c)) :
    ∀ a b c a' b' c' : Omega,
      a ≠ b → a ≠ c → b ≠ c →
      a' ≠ b' → a' ≠ c' → b' ≠ c' →
      ∃! g : G,
        g • a = a' ∧ g • b = b' ∧ g • c = c' := by
  classical
  intro a b c a' b' c' hab hac hbc ha'b' ha'c' hb'c'
  let source : Fin 3 ↪ Omega :=
    ⟨![a, b, c], by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all⟩
  let target : Fin 3 ↪ Omega :=
    ⟨![a', b', c'], by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all⟩
  let orbit : G → (Fin 3 ↪ Omega) := fun g =>
    source.trans (MulAction.toPermHom G Omega g).toEmbedding
  have horbit_inj : Function.Injective orbit := by
    intro g h hgh
    have hga : g • a = h • a := by
      have heq := congrArg (fun e : Fin 3 ↪ Omega => e 0) hgh
      change g • a = h • a at heq
      exact heq
    have hgb : g • b = h • b := by
      have heq := congrArg (fun e : Fin 3 ↪ Omega => e 1) hgh
      change g • b = h • b at heq
      exact heq
    have hgc : g • c = h • c := by
      have heq := congrArg (fun e : Fin 3 ↪ Omega => e 2) hgh
      change g • c = h • c at heq
      exact heq
    have hfix_a : (h⁻¹ * g) • a = a := by
      rw [mul_smul, hga, inv_smul_smul]
    have hfix_b : (h⁻¹ * g) • b = b := by
      rw [mul_smul, hgb, inv_smul_smul]
    have hfix_c : (h⁻¹ * g) • c = c := by
      rw [mul_smul, hgc, inv_smul_smul]
    have hone : h⁻¹ * g = 1 := by
      by_contra hne
      exact hat_most_two_fixed_points (h⁻¹ * g) hne a b c hab hac hbc
        ⟨hfix_a, hfix_b, hfix_c⟩
    exact (inv_mul_eq_one.mp hone).symm
  have horbit_card : Nat.card G = Nat.card (Fin 3 ↪ Omega) := by
    calc
      Nat.card G = (Fintype.card Omega).descFactorial 3 := hcard
      _ = Fintype.card (Fin 3 ↪ Omega) := by
        rw [Fintype.card_embedding_eq, Fintype.card_fin]
      _ = Nat.card (Fin 3 ↪ Omega) := Nat.card_eq_fintype_card.symm
  have horbit_surj : Function.Surjective orbit :=
    ((Nat.bijective_iff_injective_and_card orbit).2
      ⟨horbit_inj, horbit_card⟩).2
  obtain ⟨g, hg⟩ := horbit_surj target
  refine ⟨g, ?_, ?_⟩
  · have h0 := congrArg (fun e : Fin 3 ↪ Omega => e 0) hg
    have h1 := congrArg (fun e : Fin 3 ↪ Omega => e 1) hg
    have h2 := congrArg (fun e : Fin 3 ↪ Omega => e 2) hg
    change g • a = a' at h0
    change g • b = b' at h1
    change g • c = c' at h2
    exact And.intro h0 (And.intro h1 h2)
  · intro h hh
    apply horbit_inj
    rw [hg]
    ext i
    fin_cases i
    · change h • a = a'
      exact hh.1
    · change h • b = b'
      exact hh.2.1
    · change h • c = c'
      exact hh.2.2

private theorem finiteField_oddCharacteristic_psl_package
    {G : Type u} [Group G] {K : Type w} [Field K] [Finite K]
    {n : ℕ}
    (hKcard : Nat.card K = n)
    (hcharNe : ringChar K ≠ 2)
    (hmodel : Nonempty
      (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)) :
    ∃ p f : ℕ, Nat.Prime p ∧ 0 < f ∧ n = p ^ f ∧ Odd p ∧
      ∃ (L : Type w) (_ : Field L) (_ : Finite L),
        Nat.card L = n ∧
        Nonempty
          (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) L) := by
  letI : Fintype K := Fintype.ofFinite K
  rcases FiniteField.card' K with ⟨p, hpchar, f, hp, hKpow⟩
  letI : CharP K p := hpchar
  have hcharEq : ringChar K = p := ringChar.eq K p
  have hpne : p ≠ 2 := by
    intro hp2
    apply hcharNe
    rw [hcharEq, hp2]
  have hn : n = p ^ (f : ℕ) := by
    rw [← hKcard, Nat.card_eq_fintype_card, hKpow]
  exact ⟨p, f, hp, f.pos, hn, hp.odd_of_ne_two hpne,
    K, inferInstance, inferInstance, hKcard, hmodel⟩

private theorem suzukiMatrixGroup_card_formula
    (m : ℕ) (hm : 0 < m) :
    Nat.card (SuzukiMatrixGroup m) =
      ((2 ^ (2 * m + 1)) ^ 2 + 1) *
        (2 ^ (2 * m + 1)) ^ 2 *
          (2 ^ (2 * m + 1) - 1) := by
  let K := BinaryGaloisField (2 * m + 1)
  let pi : K ≃+* K := iterateFrobeniusEquiv K 2 (m + 1)
  have hpi : ∀ x : K, pi x = x ^ (2 ^ (m + 1)) := by
    intro x
    exact iterateFrobeniusEquiv_def K 2 (m + 1) x
  rcases huppert_blackburn_XI_3_3 m hm pi hpi with
    ⟨_, _, _, _, _, _, hcard, _⟩
  exact hcard

private theorem twoPower_eq_square_of_odd_order_factors
    (n d q f k : ℕ)
    (hf : 0 < f) (hk : 0 < k)
    (hn : n = 2 ^ f) (hq : q = 2 ^ k)
    (hdOdd : Odd d)
    (horder :
      (n + 1) * n * d = (q ^ 2 + 1) * q ^ 2 * (q - 1)) :
    n = q ^ 2 := by
  have hnEven : Even n := by
    rw [hn]
    exact Nat.even_pow.mpr ⟨even_two, hf.ne'⟩
  have hqEven : Even q := by
    rw [hq]
    exact Nat.even_pow.mpr ⟨even_two, hk.ne'⟩
  have hqPos : 0 < q := by
    rw [hq]
    exact pow_pos (by norm_num) k
  have hqSqEven : Even (q ^ 2) :=
    hqEven.pow_of_ne_zero (by norm_num)
  have hqSubOneOdd : Odd (q - 1) :=
    Nat.Even.sub_odd hqPos hqEven odd_one
  have hnOuterOdd : Odd ((n + 1) * d) :=
    hnEven.add_one.mul hdOdd
  have hqOuterOdd : Odd ((q ^ 2 + 1) * (q - 1)) :=
    hqSqEven.add_one.mul hqSubOneOdd
  have hproductEq :
      n * ((n + 1) * d) = q ^ 2 * ((q ^ 2 + 1) * (q - 1)) := by
    calc
      n * ((n + 1) * d) = (n + 1) * n * d := by ac_rfl
      _ = (q ^ 2 + 1) * q ^ 2 * (q - 1) := horder
      _ = q ^ 2 * ((q ^ 2 + 1) * (q - 1)) := by ac_rfl
  have hnCoprimeQOuter :
      Nat.Coprime n ((q ^ 2 + 1) * (q - 1)) := by
    rw [hn]
    exact Nat.Coprime.pow_left f hqOuterOdd.coprime_two_left
  have hnDvdQSqProduct :
      n ∣ q ^ 2 * ((q ^ 2 + 1) * (q - 1)) := by
    rw [← hproductEq]
    exact dvd_mul_right n ((n + 1) * d)
  have hnDvdQSq : n ∣ q ^ 2 :=
    hnCoprimeQOuter.dvd_of_dvd_mul_right hnDvdQSqProduct
  have hqSqCoprimeNOuter :
      Nat.Coprime (q ^ 2) ((n + 1) * d) := by
    rw [hq]
    exact Nat.Coprime.pow_left 2
      (Nat.Coprime.pow_left k hnOuterOdd.coprime_two_left)
  have hqSqDvdNProduct : q ^ 2 ∣ n * ((n + 1) * d) := by
    rw [hproductEq]
    exact dvd_mul_right (q ^ 2) ((q ^ 2 + 1) * (q - 1))
  have hqSqDvdN : q ^ 2 ∣ n :=
    hqSqCoprimeNOuter.dvd_of_dvd_mul_right hqSqDvdNProduct
  exact Nat.dvd_antisymm hnDvdQSq hqSqDvdN

set_option maxHeartbeats 400000 in
/-- Huppert-Blackburn XI.11.16, the classification of finite Zassenhaus groups. -/
public theorem huppert_blackburn_XI_11_16_zassenhaus_classification
    {G : Type u} {Omega : Type v}
    [Group G] [Finite G] [MulAction G Omega] [FaithfulSMul G Omega]
    [Fintype Omega]
    (n d : ℕ)
    (hdegree : Fintype.card Omega = n + 1)
    (horder : Nat.card G = (n + 1) * n * d)
    (htwo_transitive : MulAction.IsMultiplyPretransitive G Omega 2)
    (hat_most_two_fixed_points :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
          ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (hno_regular_normal :
      ¬ ∃ R : Subgroup G, R.Normal ∧ R ≠ ⊥ ∧
        ∀ a b : Omega, ∃! r : R, (r : G) • a = b) :
    ∃ p f : ℕ, Nat.Prime p ∧ 0 < f ∧ n = p ^ f ∧
      ((∃ (K : Type w) (_ : Field K) (_ : Finite K),
          Nat.card K = n ∧
          Nonempty (G ≃* Matrix.ProjGenLinGroup (Fin 2) K)) ∨
        (Odd p ∧
          ∃ (K : Type w) (_ : Field K) (_ : Finite K),
            Nat.card K = n ∧
            Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)) ∨
        (Odd p ∧ Even f ∧
          ∀ a b c a' b' c' : Omega,
            a ≠ b → a ≠ c → b ≠ c →
            a' ≠ b' → a' ≠ c' → b' ≠ c' →
            ∃! g : G,
              g • a = a' ∧ g • b = b' ∧ g • c = c') ∨
        (p = 2 ∧
          ∃ m : ℕ, 0 < m ∧
            n = (2 ^ (2 * m + 1)) ^ 2 ∧
            Nonempty (G ≃* SuzukiMatrixGroup m))) := by
  classical
  have hnpos : 0 < n := by
    have hprod : 0 < (n + 1) * n * d := by
      rw [← horder]
      exact Nat.card_pos
    exact pos_of_mul_pos_right
      (pos_of_mul_pos_left hprod (Nat.zero_le d)) (Nat.zero_le (n + 1))
  have hOmegaCard : 1 < Fintype.card Omega := by
    rw [hdegree]
    omega
  obtain ⟨a, b, hab⟩ := Fintype.one_lt_card_iff.mp hOmegaCard
  let b' : SubMulAction.ofStabilizer G a := ⟨b, hab.symm⟩
  obtain ⟨F, hFrob⟩ :=
    huppert_blackburn_XI_pointStabilizer_frobeniusKernel_exists
      htwo_transitive hat_most_two_fixed_points hno_regular_normal a b hab
  let SharpTriple : Prop :=
    ∀ a b c a' b' c' : Omega,
      a ≠ b → a ≠ c → b ≠ c →
      a' ≠ b' → a' ≠ c' → b' ≠ c' →
      ∃! g : G, g • a = a' ∧ g • b = b' ∧ g • c = c'
  have hFcard : Nat.card F = n :=
    huppert_blackburn_XI_pointStabilizer_frobeniusKernel_card
      n hdegree htwo_transitive a b hab F hFrob
  have hpointStabilizerCard :
      Nat.card (MulAction.stabilizer G a) = n * d := by
    letI : MulAction.IsMultiplyPretransitive G Omega 2 := htwo_transitive
    letI : MulAction.IsPretransitive G Omega :=
      MulAction.isPretransitive_of_is_two_pretransitive
    have hindex : (MulAction.stabilizer G a).index = n + 1 := by
      calc
        (MulAction.stabilizer G a).index = Nat.card Omega :=
          MulAction.index_stabilizer_of_transitive G a
        _ = Fintype.card Omega := Nat.card_eq_fintype_card
        _ = n + 1 := hdegree
    have hmul := (MulAction.stabilizer G a).card_mul_index
    rw [hindex] at hmul
    apply Nat.eq_of_mul_eq_mul_right (by omega : 0 < n + 1)
    calc
      Nat.card (MulAction.stabilizer G a) * (n + 1) = Nat.card G := hmul
      _ = (n + 1) * n * d := horder
      _ = (n * d) * (n + 1) := by ac_rfl
  have htwoPointStabilizerCard :
      Nat.card
          (MulAction.stabilizer (MulAction.stabilizer G a) b') = d := by
    have hmul := hFrob.isComplement'.card_mul
    rw [hFcard, hpointStabilizerCard] at hmul
    exact Nat.eq_of_mul_eq_mul_left hnpos hmul
  have hFnil : Group.IsNilpotent F :=
    huppert_blackburn_XI_frobeniusKernel_nilpotent F _ hFrob
  have hXI21 :
      SharpTriple →
        ∃ p f : ℕ, Nat.Prime p ∧ 0 < f ∧ n = p ^ f := by
    intro hsharp
    exact huppert_blackburn_XI_sharpTriple_degree_primePower
      n hdegree htwo_transitive hsharp a b hab F hFrob
  have hFcomm_of_sharp : SharpTriple → IsMulCommutative F := by
    intro hsharp
    rcases huppert_blackburn_XI_sharpTriple_kernel_elementaryAbelian
        n hdegree htwo_transitive hsharp a b hab F hFrob with
      ⟨p, f, hp, hf, hn, hFelem⟩
    exact hFelem.toIsMulCommutative
  have hXI26_core :
      ∀ p f : ℕ, Nat.Prime p → 0 < f → n = p ^ f →
        SharpTriple → IsElementaryAbelian p F →
        ∀ (K : Type u) (_ : PFAppendixII.RightNearField K)
          (eAdd : Additive F ≃+ K),
          ∀ eUnits :
              MulAction.stabilizer (MulAction.stabilizer G a) b' ≃* Kˣ,
            (∀ d : MulAction.stabilizer (MulAction.stabilizer G a) b',
              ∀ x : K,
                (((eAdd.symm (x * (eUnits d : K))).toMul : F) :
                    MulAction.stabilizer G a) =
                  (d : MulAction.stabilizer G a)⁻¹ *
                    (((eAdd.symm x).toMul : F) :
                      MulAction.stabilizer G a) *
                    (d : MulAction.stabilizer G a)) →
            ∀ ePoint : Omega ≃ Option K,
              ePoint a = none → ePoint b = some 0 →
              (∀ f : F, ∀ y : Option K,
                ePoint
                    ((((f : MulAction.stabilizer G a) : G) •
                      ePoint.symm y)) =
                  Option.map
                    (fun x => eAdd (Additive.ofMul f) + x) y) →
              (∀ d : MulAction.stabilizer
                    (MulAction.stabilizer G a) b',
                ∀ y : Option K,
                  ePoint
                      ((((d : MulAction.stabilizer G a) : G)⁻¹) •
                        ePoint.symm y) =
                    Option.map (fun x => x * (eUnits d : K)) y) →
              (∀ h : MulAction.stabilizer G a,
                ∃ f : F,
                  ∃ d : MulAction.stabilizer
                      (MulAction.stabilizer G a) b',
                    h = (f : MulAction.stabilizer G a) *
                        (d : MulAction.stabilizer G a)⁻¹ ∧
                      ∀ y : Option K,
                        ePoint ((h : G) • ePoint.symm y) =
                          Option.map
                            (fun x =>
                              eAdd (Additive.ofMul f) +
                                x * (eUnits d : K)) y) →
              ∀ t : G,
                t ^ 2 = 1 → t • a = b →
                  t • ePoint.symm (some 1) = ePoint.symm (some 1) →
                (∀ g : G,
                  g ∈ MulAction.stabilizer G a ∨
                    ∃ h1 h2 : MulAction.stabilizer G a,
                      g = (h1 : G) * t * (h2 : G)) →
                ∀ tau : Equiv.Perm (Option K),
                  (∀ x : Option K,
                    tau x = ePoint (t • ePoint.symm x)) →
                  (∀ x : Option K, tau (tau x) = x) →
                  ∀ tauUnits : Equiv.Perm Kˣ,
                    (∀ x : Kˣ,
                      some ((tauUnits x : Kˣ) : K) =
                        tau (some (x : K))) →
                  ∀ affinePerm : F →
                      MulAction.stabilizer
                        (MulAction.stabilizer G a) b' →
                        Equiv.Perm (Option K),
                    (∀ f0 : F,
                      ∀ d0 : MulAction.stabilizer
                          (MulAction.stabilizer G a) b',
                        ∀ y : Option K,
                          affinePerm f0 d0 y =
                            Option.map
                              (fun x =>
                                eAdd (Additive.ofMul f0) +
                                  x * (eUnits d0 : K)) y) →
                    ∀ rho : G →* Equiv.Perm (Option K),
                      (∀ g : G, ∀ y : Option K,
                        rho g y = ePoint (g • ePoint.symm y)) →
                      Function.Injective rho →
                      ∀ A : Subgroup (Equiv.Perm (Option K)),
                        (A : Set (Equiv.Perm (Option K))) =
                          {sigma | ∃ f0 : F,
                            ∃ d0 : MulAction.stabilizer
                                (MulAction.stabilizer G a) b',
                              sigma = affinePerm f0 d0} →
                        (∀ sigma : rho.range,
                          ((sigma : Equiv.Perm (Option K)) ∈ A ↔
                            (sigma : Equiv.Perm (Option K)) none = none)) →
                        ∀ B : Subgroup (Equiv.Perm (Option K)),
                          ∀ multiplierEquiv : (Kˣ)ᵐᵒᵖ ≃* B,
                            (∀ u : (Kˣ)ᵐᵒᵖ,
                              ((multiplierEquiv u : B) :
                                  Equiv.Perm (Option K)) =
                                affinePerm 1 (eUnits.symm u.unop)) →
                            B = A ⊓ A.conjBy tau →
                        (rho.range : Set (Equiv.Perm (Option K))) =
                          (A : Set (Equiv.Perm (Option K))) ∪
                            DoubleCoset.doubleCoset tau A A →
        (∃ C : Subgroup Kˣ, IsCyclic C ∧ C.index ≤ 2) ∧
          (∀ hcomm : ∀ x y : K, x * y = y * x,
            let fieldInst : Field K := rightNearFieldFieldOfComm K hcomm
            letI : Field K := fieldInst
            Nonempty
              (rho.range ≃* Matrix.ProjGenLinGroup (Fin 2) K)) := by
    intro p f hp hf hn hsharp hFelem K hNF eAdd eUnits hmul_coordinate
      ePoint hPointA hPointB hKernelAction hUnitsAction hStabilizerAffine
      t ht_sq hta ht_one hbruhat tau hTau_apply hTauSq
      tauUnits hTauUnits_apply affinePerm hAffinePerm_apply rho hRho_apply
      hRho_injective A hA_eq hA_mem B multiplierEquiv hMultiplier_apply hB_eq hRange
    have hXI25_data :
        ∃ theta : Kˣ ≃* Kˣ,
          Function.Involutive theta ∧
          (∀ x y z : Kˣ,
            theta x = x → theta y = y → theta z = z →
              x = y ∨ x = z ∨ y = z) ∧
          tau none = some 0 ∧ tau (some 0) = none ∧
          (∀ x : Kˣ,
            some ((theta x : Kˣ) : K) = tau (some (x : K))) ∧
          ∃ C : Subgroup Kˣ, IsCyclic C ∧ C.index ≤ 2 := by
      letI : Finite K := Finite.of_surjective eAdd eAdd.surjective
      have hXI25_sylowClassification :
          (∀ (q : ℕ) [Fact q.Prime], q ≠ 2 →
            ∀ Q : Sylow q Kˣ, IsCyclic Q) ∧
          (∀ Q : Sylow 2 Kˣ,
            IsCyclic Q ∨
              ∃ k : ℕ, 2 ≤ k ∧ IsPGroup 2 (QuaternionGroup k) ∧
                Nonempty (Q ≃* QuaternionGroup k)) := by
        let rightAdd : (Kˣ)ᵐᵒᵖ →* Multiplicative (K ≃+ K) :=
          PFAppendixII.rightNearFieldRightMulAction
        let rightAut : (Kˣ)ᵐᵒᵖ →* MulAut (Multiplicative K) :=
          { toFun := fun u => (Multiplicative.toAdd (rightAdd u)).toMultiplicative
            map_one' := by
              ext x
              change Multiplicative.ofAdd
                  (rightAdd 1 (Multiplicative.toAdd x)) = x
              rw [map_one]
              rfl
            map_mul' := by
              intro u v
              ext x
              change Multiplicative.ofAdd
                  (rightAdd (u * v) (Multiplicative.toAdd x)) =
                Multiplicative.ofAdd
                  (rightAdd u (rightAdd v (Multiplicative.toAdd x)))
              rw [map_mul]
              rfl }
        have hrightAut_injective : Function.Injective rightAut := by
          intro u v huv
          apply MulOpposite.unop_injective
          apply Units.ext
          have h := congrArg
            (fun phi : MulAut (Multiplicative K) =>
              Multiplicative.toAdd
                (phi (Multiplicative.ofAdd (1 : K)))) huv
          simpa [rightAut, rightAdd,
            PFAppendixII.rightNearFieldRightMulAction_apply] using h
        let automorphismSubgroup : Subgroup (MulAut (Multiplicative K)) :=
          rightAut.range
        have hfixed :
            ∀ phi : automorphismSubgroup, phi ≠ 1 →
              ∀ x : Multiplicative K,
                (phi : MulAut (Multiplicative K)) x = x → x = 1 := by
          intro phi hphi x hx
          rcases phi.property with ⟨u, hu_range⟩
          have hx' : rightAut u x = x := by
            rw [hu_range]
            exact hx
          change Multiplicative.toAdd x = 0
          by_contra hx0
          have hmul :
              Multiplicative.toAdd x * (u.unop : K) =
                Multiplicative.toAdd x := by
            simpa [rightAut, rightAdd,
              PFAppendixII.rightNearFieldRightMulAction_apply] using
                congrArg Multiplicative.toAdd hx'
          have hu_val : u.unop = 1 :=
            PFAppendixII.rightNearField_mul_right_fixed_of_ne_zero
              hx0 u.unop hmul
          have hu_one : u = 1 :=
            MulOpposite.unop_injective (by simpa using hu_val)
          apply hphi
          apply Subtype.ext
          change (phi : MulAut (Multiplicative K)) = 1
          rw [← hu_range, hu_one, map_one]
        have hclass :=
          huppert_V_8_15_fixedPointFree_automorphism_subgroup_classification
            automorphismSubgroup hfixed
        let eRange : (Kˣ)ᵐᵒᵖ ≃* automorphismSubgroup :=
          MonoidHom.ofInjective hrightAut_injective
        let eUnits : Kˣ ≃* automorphismSubgroup :=
          (MulEquiv.inv' Kˣ).trans eRange
        constructor
        · intro q hq qne Q
          let Qmap : Sylow q automorphismSubgroup :=
            Q.mapSurjective (f := eUnits.toMonoidHom) eUnits.surjective
          have hcyclic : IsCyclic Qmap := hclass.1 q qne Qmap
          let eQ : Q ≃* Qmap :=
            (Subgroup.equivMapOfInjective (Q : Subgroup Kˣ)
              eUnits.toMonoidHom eUnits.injective).trans
                (MulEquiv.subgroupCongr (by rfl))
          exact eQ.isCyclic.mpr hcyclic
        · intro Q
          let Qmap : Sylow 2 automorphismSubgroup :=
            Q.mapSurjective (f := eUnits.toMonoidHom) eUnits.surjective
          let eQ : Q ≃* Qmap :=
            (Subgroup.equivMapOfInjective (Q : Subgroup Kˣ)
              eUnits.toMonoidHom eUnits.injective).trans
                (MulEquiv.subgroupCongr (by rfl))
          rcases hclass.2.1 Qmap with hcyclic | ⟨k, hk, hkP, hQmodel⟩
          · exact Or.inl (eQ.isCyclic.mpr hcyclic)
          · exact Or.inr ⟨k, hk, hkP, hQmodel.map fun e => eQ.trans e⟩
      have ht_ne : t ≠ 1 := by
        intro ht
        apply hab
        calc
          a = (1 : G) • a := by simp
          _ = t • a := by rw [ht]
          _ = b := hta
      have hXI23_fixed_triple :
          ∀ x y z : Kˣ,
            tauUnits x = x → tauUnits y = y → tauUnits z = z →
              x = y ∨ x = z ∨ y = z := by
        have hfixedPoint :
            ∀ x : Kˣ, tauUnits x = x →
              t • ePoint.symm (some (x : K)) =
                ePoint.symm (some (x : K)) := by
          intro x hx
          apply ePoint.injective
          rw [ePoint.apply_symm_apply, ← hTau_apply,
            ← hTauUnits_apply, hx]
        intro x y z hx hy hz
        by_cases hxy : x = y
        · exact Or.inl hxy
        by_cases hxz : x = z
        · exact Or.inr (Or.inl hxz)
        by_cases hyz : y = z
        · exact Or.inr (Or.inr hyz)
        exfalso
        let px : Omega := ePoint.symm (some (x : K))
        let py : Omega := ePoint.symm (some (y : K))
        let pz : Omega := ePoint.symm (some (z : K))
        have hpxy : px ≠ py := by
          intro h
          apply hxy
          apply Units.ext
          exact Option.some.inj (by
            simpa [px, py] using congrArg ePoint h)
        have hpxz : px ≠ pz := by
          intro h
          apply hxz
          apply Units.ext
          exact Option.some.inj (by
            simpa [px, pz] using congrArg ePoint h)
        have hpyz : py ≠ pz := by
          intro h
          apply hyz
          apply Units.ext
          exact Option.some.inj (by
            simpa [py, pz] using congrArg ePoint h)
        exact hat_most_two_fixed_points t ht_ne px py pz
          hpxy hpxz hpyz
          ⟨hfixedPoint x hx, hfixedPoint y hy, hfixedPoint z hz⟩
      have hTau_none : tau none = some 0 := by
        rw [hTau_apply]
        have hPointA_symm : ePoint.symm none = a := by
          apply ePoint.injective
          rw [ePoint.apply_symm_apply, hPointA]
        rw [hPointA_symm, hta, hPointB]
      have hTau_zero : tau (some 0) = none := by
        have h := hTauSq none
        rw [hTau_none] at h
        exact h
      have hTau_one : tau (some 1) = some 1 := by
        rw [hTau_apply, ht_one, ePoint.apply_symm_apply]
      have hTauUnits_one : tauUnits 1 = 1 := by
        apply Units.ext
        have h := (hTauUnits_apply (1 : Kˣ)).trans hTau_one
        exact Option.some.inj (by simpa using h)
      have hTauUnits_involutive : Function.Involutive tauUnits := by
        intro x
        apply Units.ext
        exact Option.some.inj (by
          calc
            some ((tauUnits (tauUnits x) : Kˣ) : K) =
                tau (some ((tauUnits x : Kˣ) : K)) :=
              hTauUnits_apply (tauUnits x)
            _ = tau (tau (some (x : K))) := by
              rw [← hTauUnits_apply x]
            _ = some (x : K) := hTauSq (some (x : K)))
      let multiplierPerm (u : Kˣ) : Equiv.Perm (Option K) :=
        affinePerm 1 (eUnits.symm u)
      have hMultiplierPerm_apply (u : Kˣ) (y : Option K) :
          multiplierPerm u y = Option.map (fun x => x * (u : K)) y := by
        rw [show multiplierPerm u = affinePerm 1 (eUnits.symm u) by rfl,
          hAffinePerm_apply]
        simp
      have hMultiplierPerm_rho (u : Kˣ) :
          multiplierPerm u =
            rho (((eUnits.symm u :
              MulAction.stabilizer
                (MulAction.stabilizer G a) b') :
                  MulAction.stabilizer G a) : G)⁻¹ := by
        ext y
        rw [hRho_apply, hUnitsAction, hMultiplierPerm_apply]
        simp
      have hTau_mul_self : tau * tau = 1 := by
        apply Equiv.Perm.ext
        intro x
        exact hTauSq x
      have hTau_inv : tau⁻¹ = tau :=
        inv_eq_of_mul_eq_one_right hTau_mul_self
      have hMultiplierPerm_mem_B (u : Kˣ) : multiplierPerm u ∈ B := by
        have hu := (multiplierEquiv (MulOpposite.op u)).property
        have heq :
            (((multiplierEquiv (MulOpposite.op u) : B) :
                Equiv.Perm (Option K))) = multiplierPerm u := by
          simpa [multiplierPerm] using
            hMultiplier_apply (MulOpposite.op u)
        rw [← heq]
        exact hu
      have hTau_normalizes_B (sigma : B) :
          tau * (sigma : Equiv.Perm (Option K)) * tau ∈ B := by
        have hsigma :
            (sigma : Equiv.Perm (Option K)) ∈
              A ⊓ A.conjBy tau :=
          hB_eq ▸ sigma.property
        rcases hsigma with ⟨hsigmaA, hsigmaConj⟩
        have htarget :
            tau * (sigma : Equiv.Perm (Option K)) * tau ∈
              A ⊓ A.conjBy tau := by
          constructor
          · change (sigma : Equiv.Perm (Option K)) ∈ A.conjBy tau at hsigmaConj
            rw [Subgroup.conjBy, Subgroup.mem_map] at hsigmaConj
            rcases hsigmaConj with ⟨alpha, halphaA, halphaEq⟩
            simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at halphaEq
            rw [← halphaEq, hTau_inv]
            have hconjEq :
                tau * (tau * alpha * tau) * tau = alpha := by
              calc
                tau * (tau * alpha * tau) * tau =
                    (tau * tau) * alpha * (tau * tau) := by group
                _ = alpha := by rw [hTau_mul_self]; simp
            rw [hconjEq]
            exact halphaA
          · change tau * (sigma : Equiv.Perm (Option K)) * tau ∈ A.conjBy tau
            rw [Subgroup.conjBy, Subgroup.mem_map]
            refine ⟨(sigma : Equiv.Perm (Option K)), hsigmaA, ?_⟩
            simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hTau_inv]
        exact hB_eq.symm ▸ htarget
      have hTau_multiplier_conj (u : Kˣ) :
          tau * multiplierPerm u * tau =
            multiplierPerm (tauUnits u) := by
        let sigmaB : B :=
          ⟨tau * multiplierPerm u * tau,
            hTau_normalizes_B
              ⟨multiplierPerm u, hMultiplierPerm_mem_B u⟩⟩
        obtain ⟨v, hv⟩ := multiplierEquiv.surjective sigmaB
        have hvPerm :
            (((multiplierEquiv v : B) : Equiv.Perm (Option K))) =
              tau * multiplierPerm u * tau :=
          congrArg Subtype.val hv
        have hleft :
            (((multiplierEquiv v : B) : Equiv.Perm (Option K)))
                (some (1 : K)) = some (v.unop : K) := by
          rw [hMultiplier_apply, hAffinePerm_apply]
          simp
        have hright :
            (tau * multiplierPerm u * tau) (some (1 : K)) =
              some ((tauUnits u : Kˣ) : K) := by
          change tau (multiplierPerm u (tau (some (1 : K)))) = _
          rw [hTau_one, hMultiplierPerm_apply]
          simp only [Option.map_some, one_mul]
          exact (hTauUnits_apply u).symm
        have hvu : v.unop = tauUnits u := by
          apply Units.ext
          exact Option.some.inj
            (hleft.symm.trans
              ((congrArg (fun q : Equiv.Perm (Option K) =>
                q (some (1 : K))) hvPerm).trans hright))
        calc
          tau * multiplierPerm u * tau =
              (((multiplierEquiv v : B) : Equiv.Perm (Option K))) :=
            hvPerm.symm
          _ = multiplierPerm v.unop := by
            simpa [multiplierPerm] using hMultiplier_apply v
          _ = multiplierPerm (tauUnits u) := by rw [hvu]
      have hMultiplierPerm_mul (u v : Kˣ) :
          multiplierPerm u * multiplierPerm v =
            multiplierPerm (v * u) := by
        ext y
        cases y <;> simp [hMultiplierPerm_apply, mul_assoc]
      have hTauUnits_mul (u v : Kˣ) :
          tauUnits (u * v) = tauUnits u * tauUnits v := by
        have hperm :
            multiplierPerm (tauUnits (u * v)) =
              multiplierPerm (tauUnits u * tauUnits v) := by
          calc
            multiplierPerm (tauUnits (u * v)) =
                tau * multiplierPerm (u * v) * tau :=
              (hTau_multiplier_conj (u * v)).symm
            _ = tau * (multiplierPerm v * multiplierPerm u) * tau := by
              rw [hMultiplierPerm_mul]
            _ = (tau * multiplierPerm v * tau) *
                (tau * multiplierPerm u * tau) := by
              calc
                tau * (multiplierPerm v * multiplierPerm u) * tau =
                    tau * multiplierPerm v * (tau * tau) *
                      multiplierPerm u * tau := by
                    rw [hTau_mul_self]
                    simp
                    group
                _ = _ := by group
            _ = multiplierPerm (tauUnits v) *
                multiplierPerm (tauUnits u) := by
              rw [hTau_multiplier_conj, hTau_multiplier_conj]
            _ = multiplierPerm (tauUnits u * tauUnits v) := by
              rw [hMultiplierPerm_mul]
        apply Units.ext
        have happ := congrArg
          (fun q : Equiv.Perm (Option K) => q (some (1 : K))) hperm
        change
          multiplierPerm (tauUnits (u * v)) (some (1 : K)) =
            multiplierPerm (tauUnits u * tauUnits v) (some (1 : K)) at happ
        rw [hMultiplierPerm_apply, hMultiplierPerm_apply] at happ
        simpa using Option.some.inj happ
      let hXI24_tauUnits_mulEquiv : Kˣ ≃* Kˣ :=
        { tauUnits with map_mul' := hTauUnits_mul }
      have hXI24_tauUnits_mulEquiv_involutive :
          Function.Involutive hXI24_tauUnits_mulEquiv := by
        intro u
        change tauUnits (tauUnits u) = u
        exact hTauUnits_involutive u
      have hXI24_tauUnits_mulEquiv_fixed_triple :
          ∀ x y z : Kˣ,
            hXI24_tauUnits_mulEquiv x = x →
            hXI24_tauUnits_mulEquiv y = y →
            hXI24_tauUnits_mulEquiv z = z →
              x = y ∨ x = z ∨ y = z := by
        intro x y z hx hy hz
        apply hXI23_fixed_triple x y z
        · change tauUnits x = x at hx
          exact hx
        · change tauUnits y = y at hy
          exact hy
        · change tauUnits z = z at hz
          exact hz
      let twoPointInclusion :
          MulAction.stabilizer (MulAction.stabilizer G a) b' →* G :=
        (MulAction.stabilizer G a).subtype.comp
          (MulAction.stabilizer (MulAction.stabilizer G a) b').subtype
      let unitsInclusion : Kˣ →* G :=
        twoPointInclusion.comp eUnits.symm.toMonoidHom
      have hunitsInclusion_injective :
          Function.Injective unitsInclusion := by
        intro u v huv
        apply eUnits.symm.injective
        apply Subtype.ext
        apply Subtype.ext
        simpa [unitsInclusion, twoPointInclusion] using huv
      have hunits_fix_a (u : Kˣ) : unitsInclusion u • a = a := by
        change
          ((((eUnits.symm u :
              MulAction.stabilizer
                (MulAction.stabilizer G a) b') :
                  MulAction.stabilizer G a) : G) • a) = a
        exact (eUnits.symm u).1.property
      have hunits_fix_b (u : Kˣ) : unitsInclusion u • b = b := by
        change
          ((((eUnits.symm u :
              MulAction.stabilizer
                (MulAction.stabilizer G a) b') :
                  MulAction.stabilizer G a) : G) • b) = b
        have hfix := congrArg
          (fun x : SubMulAction.ofStabilizer G a => (x : Omega))
          (eUnits.symm u).property
        simpa only [b', SetLike.val_smul,
          MulAction.subgroup_smul_def] using hfix
      let x0 : Omega := ePoint.symm (some (1 : K))
      have hax0 : a ≠ x0 := by
        intro h
        have he := congrArg ePoint h
        simp [x0, hPointA] at he
      have hbx0 : b ≠ x0 := by
        intro h
        have he := congrArg ePoint h
        simp [x0, hPointB] at he
      have hXI22_uniqueOrderThree :
          ∀ U V : Subgroup Kˣ,
            Nat.card U = 3 → Nat.card V = 3 → U = V :=
        huppert_XI_2_2_subgroup_order_three_unique
          unitsInclusion hunitsInclusion_injective
          a b x0 hab hax0 hbx0 hunits_fix_a hunits_fix_b
          hsharp hat_most_two_fixed_points
      refine ⟨hXI24_tauUnits_mulEquiv,
        hXI24_tauUnits_mulEquiv_involutive,
        hXI24_tauUnits_mulEquiv_fixed_triple,
        hTau_none, hTau_zero, ?_, ?_⟩
      · intro x
        change some ((tauUnits x : Kˣ) : K) = tau (some (x : K))
        exact hTauUnits_apply x
      by_cases hp2 : p = 2
      · subst p
        have hKcard : Nat.card K = 2 ^ f := by
          calc
            Nat.card K = Nat.card (Additive F) :=
              Nat.card_congr eAdd.symm.toEquiv
            _ = Nat.card F := rfl
            _ = n := hFcard
            _ = 2 ^ f := hn
        have hUnitsCyclic : IsCyclic Kˣ :=
          huppert_XI_2_1_units_cyclic_of_two_power_card
            hf hKcard hXI24_tauUnits_mulEquiv
              hXI24_tauUnits_mulEquiv_involutive
                hXI24_tauUnits_mulEquiv_fixed_triple
        refine ⟨⊤, ?_, by simp⟩
        exact (Subgroup.topEquiv : (⊤ : Subgroup Kˣ) ≃* Kˣ).isCyclic.mpr
          hUnitsCyclic
      · have hXI25_invariantIndexTwo :
            ∃ C : Subgroup Kˣ,
              C.Normal ∧ C.index = 2 ∧
                ∀ u : Kˣ,
                  u ∈ C ↔ hXI24_tauUnits_mulEquiv u ∈ C := by
          by_cases hres : hktPResidual 2 Kˣ = ⊤
          · have hKcard : Nat.card K = p ^ f := by
              calc
                Nat.card K = Nat.card (Additive F) :=
                  Nat.card_congr eAdd.symm.toEquiv
                _ = Nat.card F := rfl
                _ = n := hFcard
                _ = p ^ f := hn
            have hNFchar : addOrderOf (1 : K) = p :=
              rightNearField_addOrderOf_one_eq_of_isElementaryAbelian hp eAdd
            have hKcardOdd : Odd (Nat.card K) := by
              rw [hKcard]
              exact (hp.odd_of_ne_two hp2).pow
            have hUnitsEven : 2 ∣ Nat.card Kˣ := by
              apply even_iff_two_dvd.mp
              rw [Nat.card_units]
              exact Nat.Odd.sub_odd hKcardOdd odd_one
            let P : Sylow 2 Kˣ := default
            rcases hXI25_sylowClassification.2 P with hPcyclic | hPquaternion
            · exact False.elim
                ((huppert_XI_2_5_pResidual_ne_top_of_cyclic_sylow_two
                  hUnitsEven P hPcyclic) hres)
            · have hsubrank :
                  ∀ U : Subgroup Kˣ, IsPGroup 2 U → generatorRank U ≤ 2 := by
                intro U hU2
                obtain ⟨Q, hUleQ⟩ := hU2.exists_le_sylow
                rcases hXI25_sylowClassification.2 Q with
                  hQcyclic | ⟨k, hk, _hkP, ⟨eQ⟩⟩
                · exact
                    (generatorRank_le_one_of_isCyclic
                      (Subgroup.isCyclic_of_le hUleQ)).trans (by omega)
                · haveI : NeZero k := ⟨by omega⟩
                  have huniqueQ :
                      ∀ x y : Q, orderOf x = 2 → orderOf y = 2 → x = y := by
                    intro x y hx hy
                    apply eQ.injective
                    have hx' : orderOf (eQ x) = 2 := by
                      simpa using
                        (orderOf_injective eQ.toMonoidHom eQ.injective x).trans hx
                    have hy' : orderOf (eQ y) = 2 := by
                      simpa using
                        (orderOf_injective eQ.toMonoidHom eQ.injective y).trans hy
                    exact
                      (huppert_XI_2_4_quaternionGroup_eq_a_parameter_of_orderOf_eq_two
                        k hx').trans
                        (huppert_XI_2_4_quaternionGroup_eq_a_parameter_of_orderOf_eq_two
                          k hy').symm
                  have huniqueU :
                      ∀ x y : U, orderOf x = 2 → orderOf y = 2 → x = y := by
                    intro x y hx hy
                    let xQ : Q := ⟨(x : Kˣ), hUleQ x.property⟩
                    let yQ : Q := ⟨(y : Kˣ), hUleQ y.property⟩
                    have hxQ : orderOf xQ = 2 := by
                      calc
                        orderOf xQ = orderOf (xQ : Kˣ) :=
                          (Subgroup.orderOf_coe xQ).symm
                        _ = orderOf (x : Kˣ) := rfl
                        _ = orderOf x := Subgroup.orderOf_coe x
                        _ = 2 := hx
                    have hyQ : orderOf yQ = 2 := by
                      calc
                        orderOf yQ = orderOf (yQ : Kˣ) :=
                          (Subgroup.orderOf_coe yQ).symm
                        _ = orderOf (y : Kˣ) := rfl
                        _ = orderOf y := Subgroup.orderOf_coe y
                        _ = 2 := hy
                    have hxyQ : xQ = yQ := huniqueQ xQ yQ hxQ hyQ
                    apply Subtype.ext
                    simpa [xQ, yQ] using congrArg Subtype.val hxyQ
                  exact
                    huppert_IV_5_10_generatorRank_le_two_of_unique_order_two
                      hU2 huniqueU
              have hthree : 3 ∣ Nat.card Kˣ := by
                by_contra hthree
                have hcomp : HasNormalPComplement 2 Kˣ :=
                  huppert_IV_5_11_hasNormalPComplement_of_rankTwo_twoSubgroups
                    hthree hsubrank
                exact
                  (hktPResidual_ne_top_of_hasNormalPComplement_of_dvd_card
                    hcomp hUnitsEven) hres
              have hSylowThreeCyclic :
                  ∀ Q : Sylow 3 Kˣ, IsCyclic Q := by
                letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
                exact hXI25_sylowClassification.1 3 (by omega)
              have hcompThree : HasNormalPComplement 3 Kˣ :=
                huppert_XI_2_5_hasNormalPComplement_three_of_top_twoResidual
                  hres hthree hXI22_uniqueOrderThree hSylowThreeCyclic
              letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
              letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
              let L : Subgroup Kˣ := pPrimeCore 3 Kˣ
              have hLchar : L.Characteristic := by
                simpa [L] using pPrimeCore_characteristic (p := 3) (G := Kˣ)
              letI : L.Characteristic := hLchar
              have hP_le_L : (P : Subgroup Kˣ) ≤ L := by
                simpa [L] using
                  sylow_two_le_pPrimeCore_three_of_hasNormalPComplement
                    hcompThree P
              let PL : Sylow 2 L := P.subtype hP_le_L
              have hPLquaternion :
                  ∃ k : ℕ, 2 ≤ k ∧ IsPGroup 2 (QuaternionGroup k) ∧
                    Nonempty (PL ≃* QuaternionGroup k) := by
                rcases hPquaternion with ⟨k, hk, hkP, ⟨eP⟩⟩
                let ePL : PL ≃* P := by
                  change (P : Subgroup Kˣ).subgroupOf L ≃* P
                  exact Subgroup.subgroupOfEquivOfLe hP_le_L
                exact ⟨k, hk, hkP, ⟨ePL.trans eP⟩⟩
              have hcompTwo : HasNormalPComplement 2 L := by
                simpa [L] using
                  huppert_XI_2_5_hasNormalPComplement_two_pPrimeCore_three
                    P hPquaternion hcompThree
              let O : Subgroup L := pPrimeCore 2 L
              have hOchar : O.Characteristic := by
                simpa [O] using pPrimeCore_characteristic (p := 2) (G := L)
              letI : O.Characteristic := hOchar
              let R := L ⧸ O
              let eR : R ≃* PL := by
                simpa [R, O] using
                  quotientPPrimeCoreEquivSylowOfHasNormalPComplement
                    hcompTwo PL
              have hRquaternion :
                  ∃ k : ℕ, 2 ≤ k ∧ IsPGroup 2 (QuaternionGroup k) ∧
                    Nonempty (R ≃* QuaternionGroup k) := by
                rcases hPLquaternion with ⟨k, hk, hkP, ⟨ePL⟩⟩
                exact ⟨k, hk, hkP, ⟨eR.trans ePL⟩⟩
              have hRfrattiniCard : Nat.card (R ⧸ frattini R) = 4 :=
                quaternionGroup_frattiniQuotient_card_eq_four hRquaternion
              let qO : L →* R := QuotientGroup.mk' O
              let M_L : Subgroup L := (frattini R).comap qO
              have hMLchar : M_L.Characteristic := by
                letI : (frattini R).Characteristic := frattini_characteristic
                simpa [M_L, qO, R] using
                  (Subgroup.Characteristic.comap_quotient_mk
                    (H := O) (K := frattini R)
                      (inferInstance : (frattini R).Characteristic))
              letI : M_L.Characteristic := hMLchar
              have hMLindex : M_L.index = (frattini R).index := by
                simpa [M_L, qO] using
                  (Subgroup.index_comap_of_surjective
                    (H := frattini R) (f := qO)
                      (QuotientGroup.mk'_surjective O))
              have hLquotCard : Nat.card (L ⧸ M_L) = 4 := by
                rw [← M_L.index_eq_card, hMLindex,
                  (frattini R).index_eq_card]
                exact hRfrattiniCard
              let M : Subgroup Kˣ := M_L.map L.subtype
              have hMchar : M.Characteristic := by
                simpa [M] using
                  characteristic_map_subtype_of_characteristic
                    (G := Kˣ) L M_L
              letI : M.Characteristic := hMchar
              obtain ⟨Z, hZchar, hZindex⟩ :=
                huppert_XI_2_5_exists_characteristic_index_twelve_of_top_two_residual
                  (G := Kˣ) hres hcompThree M_L (by
                    simpa [L] using hLquotCard)
              letI : Z.Characteristic := hZchar
              have hZinvariant :
                  ∀ u : Kˣ,
                    u ∈ Z ↔ hXI24_tauUnits_mulEquiv u ∈ Z := by
                intro u
                change u ∈ Z ↔
                  u ∈ Z.comap hXI24_tauUnits_mulEquiv.toMonoidHom
                rw [hZchar.fixed hXI24_tauUnits_mulEquiv]
              have hZcyclic : IsCyclic Z :=
                huppert_XI_2_4_invariantNormal_cyclic
                  hXI24_tauUnits_mulEquiv
                  hXI24_tauUnits_mulEquiv_involutive
                  hXI24_tauUnits_mulEquiv_fixed_triple
                  Z hZinvariant (by
                    rw [hZindex]
                    exact even_iff_two_dvd.mpr (by norm_num))
                  hXI25_sylowClassification.1
                  hXI25_sylowClassification.2
              exact False.elim
                (huppert_XI_2_5_topResidual_false
                  hp hp2 hf hKcard hNFchar hres
                  hXI25_sylowClassification.1
                  hXI25_sylowClassification.2
                  hXI22_uniqueOrderThree
                  Z hZchar hZindex hZcyclic)
          · exact huppert_XI_2_5_invariantIndexTwo_of_pResidual_ne_top
              hXI24_tauUnits_mulEquiv
              hXI24_tauUnits_mulEquiv_involutive hres
        rcases hXI25_invariantIndexTwo with
          ⟨C, hCnormal, hCindex, hCinvariant⟩
        letI : C.Normal := hCnormal
        refine ⟨C, ?_, by omega⟩
        exact huppert_XI_2_4_invariantNormal_cyclic
          hXI24_tauUnits_mulEquiv hXI24_tauUnits_mulEquiv_involutive hXI24_tauUnits_mulEquiv_fixed_triple
          C hCinvariant (by simp [hCindex])
          hXI25_sylowClassification.1 hXI25_sylowClassification.2
    rcases hXI25_data with
      ⟨hXI24_tauUnits_mulEquiv,
        hXI24_tauUnits_mulEquiv_involutive,
        hXI24_tauUnits_mulEquiv_fixed_triple,
        hTau_none, hTau_zero, hTauUnits_apply,
        hXI25_indexTwoCyclic⟩
    have hXI26_pglRange :
        ∀ hcomm : ∀ x y : K, x * y = y * x,
          let fieldInst : Field K := rightNearFieldFieldOfComm K hcomm
          letI : Field K := fieldInst
          Nonempty
            (rho.range ≃* Matrix.ProjGenLinGroup (Fin 2) K) := by
      intro hcomm
      let fieldInst : Field K := rightNearFieldFieldOfComm K hcomm
      letI : Field K := fieldInst
      letI : Finite K := Finite.of_surjective eAdd eAdd.surjective
      letI : Fintype K := Fintype.ofFinite K
      have hKcard : Nat.card K = n := by
        calc
          Nat.card K = Nat.card (Additive F) := Nat.card_congr eAdd.symm.toEquiv
          _ = Nat.card F := rfl
          _ = n := hFcard
      letI : IsCyclic Kˣ := inferInstance
      let fieldAffinePerm (b : K) (u : Kˣ) : Equiv.Perm (Option K) :=
        affinePerm ((eAdd.symm b).toMul : F) (eUnits.symm u)
      have hFieldAffinePerm (b : K) (u : Kˣ) (y : Option K) :
          fieldAffinePerm b u y =
            Option.map (fun x => b + x * (u : K)) y := by
        simpa [fieldAffinePerm] using
          hAffinePerm_apply ((eAdd.symm b).toMul : F) (eUnits.symm u) y
      have hAField : (A : Set (Equiv.Perm (Option K))) =
          {sigma | ∃ b : K, ∃ u : Kˣ, sigma = fieldAffinePerm b u} := by
        rw [hA_eq]
        ext sigma
        constructor
        · rintro ⟨f0, d0, rfl⟩
          refine ⟨eAdd (Additive.ofMul f0), eUnits d0, ?_⟩
          simp [fieldAffinePerm]
        · rintro ⟨b0, u0, rfl⟩
          refine ⟨((eAdd.symm b0).toMul : F), eUnits.symm u0, ?_⟩
          rfl
      have hd : d = n - 1 := by
        calc
          d = Nat.card
              (MulAction.stabilizer (MulAction.stabilizer G a) b') :=
            htwoPointStabilizerCard.symm
          _ = Nat.card Kˣ := Nat.card_congr eUnits.toEquiv
          _ = Nat.card K - 1 := Nat.card_units K
          _ = n - 1 := by rw [hKcard]
      have hfactor : n ^ 2 - 1 = (n - 1) * (n + 1) := by
        let r := n - 1
        have hneq : n = r + 1 := by
          dsimp [r]
          omega
        rw [hneq]
        simp only [Nat.add_sub_cancel]
        apply (tsub_eq_iff_eq_add_of_le (Nat.one_le_pow' 2 r)).2
        ring
      have hGcard : Nat.card G = Nat.card K * (Nat.card K ^ 2 - 1) := by
        calc
          Nat.card G = (n + 1) * n * d := horder
          _ = (n + 1) * n * (n - 1) := by rw [hd]
          _ = n * (n ^ 2 - 1) := by rw [hfactor]; ac_rfl
          _ = Nat.card K * (Nat.card K ^ 2 - 1) := by rw [hKcard]
      have hRangeCard : Nat.card rho.range =
          Nat.card K * (Nat.card K ^ 2 - 1) := by
        calc
          Nat.card rho.range = Nat.card G :=
            (Nat.card_congr (Equiv.ofInjective rho hRho_injective)).symm
          _ = Nat.card K * (Nat.card K ^ 2 - 1) := hGcard
      by_cases hp2 : p = 2
      · subst p
        have hKcardEven : Even (Nat.card K) := by
          rw [hKcard, hn]
          exact Nat.even_pow.mpr ⟨even_two, hf.ne'⟩
        have hUnitsOdd : Odd (Nat.card Kˣ) := by
          rw [Nat.card_units]
          exact Nat.Even.sub_odd Nat.card_pos hKcardEven odd_one
        have hfixedPointFree :
            MonoidHom.FixedPointFree hXI24_tauUnits_mulEquiv :=
          huppert_XI_2_1_fixedPointFree_of_odd_card_fixed_triple
            hXI24_tauUnits_mulEquiv hUnitsOdd
            hXI24_tauUnits_mulEquiv_fixed_triple
        have hthetaInv : ∀ x : Kˣ,
            hXI24_tauUnits_mulEquiv x = x⁻¹ := by
          simp [hfixedPointFree.coe_eq_inv_of_involutive
            hXI24_tauUnits_mulEquiv_involutive]
        have hTauInv : ∀ y : Option K,
            tau y = match y with
              | none => some 0
              | some x => if x = 0 then none else some x⁻¹ := by
          intro y
          cases y with
          | none => exact hTau_none
          | some x =>
              by_cases hx : x = 0
              · simpa [hx] using hTau_zero
              · let u : Kˣ := Units.mk0 x hx
                have h := (hTauUnits_apply u).symm
                rw [hthetaInv u] at h
                simpa [u, hx] using h
        exact xi26_pglRange_of_tau rho A tau fieldAffinePerm
          hFieldAffinePerm hAField hTauInv hRange hRangeCard
      · have hKcardOdd : Odd (Nat.card K) := by
          rw [hKcard, hn]
          exact (hp.odd_of_ne_two hp2).pow
        have hchar : ringChar K ≠ 2 := by
          intro hcharTwo
          apply (Nat.not_even_iff_odd.mpr hKcardOdd)
          apply Nat.even_iff.mpr
          simpa [Nat.card_eq_fintype_card] using
            FiniteField.even_card_of_char_two hcharTwo
        let squareSubgroup : Subgroup Kˣ :=
          (powMonoidHom 2 : Kˣ →* Kˣ).range
        have hsquareNormal : squareSubgroup.Normal := by infer_instance
        letI : squareSubgroup.Normal := hsquareNormal
        have hUnitsEven : Even (Nat.card Kˣ) := by
          rw [Nat.card_units]
          exact Nat.Odd.sub_odd hKcardOdd odd_one
        have hUnitsEvenFintype : 2 ∣ Fintype.card Kˣ := by
          simpa [Nat.card_eq_fintype_card] using
            (even_iff_two_dvd.mp hUnitsEven)
        have hsquareIndex : squareSubgroup.index = 2 := by
          calc
            squareSubgroup.index = (Fintype.card Kˣ).gcd 2 := by
              simpa [squareSubgroup] using
                IsCyclic.index_powMonoidHom_range Kˣ 2
            _ = 2 := Nat.gcd_eq_right hUnitsEvenFintype
        have hsquareInvariant : ∀ u : Kˣ,
            u ∈ squareSubgroup ↔
              hXI24_tauUnits_mulEquiv u ∈ squareSubgroup := by
          intro u
          constructor
          · rintro ⟨x, hx⟩
            refine ⟨hXI24_tauUnits_mulEquiv x, ?_⟩
            simpa [powMonoidHom_apply, map_pow] using
              congrArg hXI24_tauUnits_mulEquiv hx
          · rintro ⟨x, hx⟩
            refine ⟨hXI24_tauUnits_mulEquiv x, ?_⟩
            have hx' := congrArg hXI24_tauUnits_mulEquiv hx
            have : hXI24_tauUnits_mulEquiv (hXI24_tauUnits_mulEquiv u) = u := by
              simpa using hXI24_tauUnits_mulEquiv_involutive u
            simpa [powMonoidHom_apply, map_pow, this] using hx'
        have hthetaSquare : ∀ x : Kˣ,
            hXI24_tauUnits_mulEquiv (x ^ 2) = (x ^ 2)⁻¹ := by
          have hinverts :=
            (huppert_XI_2_4_invariantNormal_inversion_and_cyclic
              hXI24_tauUnits_mulEquiv
              hXI24_tauUnits_mulEquiv_involutive
              hXI24_tauUnits_mulEquiv_fixed_triple
              squareSubgroup hsquareInvariant (by simp [hsquareIndex])
              (fun _ _ _ _ => Subgroup.isCyclic _)
              (fun (Q : Sylow 2 Kˣ) =>
                Or.inl (by exact isCyclic_subgroup_units Q.1))).1
          intro x
          let xSq : squareSubgroup :=
            ⟨x ^ 2, ⟨x, by simp [powMonoidHom_apply]⟩⟩
          simpa [xSq] using hinverts xSq
        exact huppert_XI_2_6_pglRange hchar rho A tau fieldAffinePerm
          hFieldAffinePerm hAField hA_mem hTau_none hTau_zero hTauSq
          hXI24_tauUnits_mulEquiv (fun x => (hTauUnits_apply x).symm)
          hthetaSquare hRange hRangeCard
    exact ⟨hXI25_indexTwoCyclic, hXI26_pglRange⟩
  have hXI26 :
      ∀ p f : ℕ, Nat.Prime p → 0 < f → n = p ^ f →
        SharpTriple →
        ((∃ (K : Type w) (_ : Field K) (_ : Finite K),
            Nat.card K = n ∧
            Nonempty (G ≃* Matrix.ProjGenLinGroup (Fin 2) K)) ∨
          (Odd p ∧ Even f ∧ SharpTriple)) := by
    intro p f hp hf hn hsharp
    rcases huppert_blackburn_XI_sharpTriple_kernel_elementaryAbelian
        n hdegree htwo_transitive hsharp a b hab F hFrob with
      ⟨q, k, hq, _hk, hnq, hFelem_q⟩
    have hpq : p = q := by
      apply Nat.prime_eq_prime_of_dvd_pow hp hq
      rw [← hnq, hn]
      exact dvd_pow_self p (Nat.ne_of_gt hf)
    have hFelem : IsElementaryAbelian p F := by
      simpa [hpq] using hFelem_q
    have hFcard_additive : Nat.card (Additive F) = n := by
      exact (Nat.card_congr Additive.toMul).trans hFcard
    rcases huppert_blackburn_XI_sharpTriple_exists_rightNearField
        htwo_transitive hsharp a b hab F hFrob hFelem.toIsMulCommutative with
      ⟨K, hNF, hKfinite, eAdd, eUnits, hmul_coordinate⟩
    letI : PFAppendixII.RightNearField K := hNF
    letI : Finite K := hKfinite
    have hKcard : Nat.card K = n := by
      calc
        Nat.card K = Nat.card (Additive F) := Nat.card_congr eAdd.symm.toEquiv
        _ = n := hFcard_additive
    have hNFchar : addOrderOf (1 : K) = p :=
      rightNearField_addOrderOf_one_eq_of_isElementaryAbelian hp eAdd
    obtain ⟨ePoint, hPointA, hPointB, hPointF⟩ :=
      huppert_blackburn_XI_pointStabilizer_exists_projectivePointEquiv
        htwo_transitive a b hab F hFrob eAdd
    have hKernelAction :=
      huppert_blackburn_XI_projectivePointEquiv_kernel_action
        a b F eAdd ePoint hPointA hPointF
    have hUnitsAction :=
      huppert_blackburn_XI_projectivePointEquiv_twoPointStabilizer_action
        a b hab F eAdd eUnits hmul_coordinate ePoint hPointA hPointF
    have hXI26_stabilizerAffine (h : MulAction.stabilizer G a) :
        ∃ f : F,
          ∃ d : MulAction.stabilizer
              (MulAction.stabilizer G a) b',
            h = (f : MulAction.stabilizer G a) *
                (d : MulAction.stabilizer G a)⁻¹ ∧
              ∀ y : Option K,
                ePoint ((h : G) • ePoint.symm y) =
                  Option.map
                    (fun x =>
                      eAdd (Additive.ofMul f) + x * (eUnits d : K)) y := by
      obtain ⟨fd, hfd, _hfd_unique⟩ := hFrob.isComplement'.existsUnique h
      let f : F := fd.1
      let d : MulAction.stabilizer
          (MulAction.stabilizer G a) b' := fd.2⁻¹
      have hdecomp :
          h = (f : MulAction.stabilizer G a) *
            (d : MulAction.stabilizer G a)⁻¹ := by
        simpa [f, d] using hfd.symm
      refine ⟨f, d, hdecomp, ?_⟩
      intro y
      have hdActionPoint :
          (((d : MulAction.stabilizer G a) : G)⁻¹) •
              ePoint.symm y =
            ePoint.symm
              (Option.map (fun x => x * (eUnits d : K)) y) := by
        apply ePoint.injective
        rw [hUnitsAction d y, ePoint.apply_symm_apply]
      have hdecompG :
          (h : G) =
            ((f : MulAction.stabilizer G a) : G) *
              (((d : MulAction.stabilizer G a) : G)⁻¹) :=
        congrArg Subtype.val hdecomp
      calc
        ePoint ((h : G) • ePoint.symm y) =
            ePoint
              (((f : MulAction.stabilizer G a) : G) •
                ((((d : MulAction.stabilizer G a) : G)⁻¹) •
                  ePoint.symm y)) := by
          rw [hdecompG, mul_smul]
        _ = ePoint
              (((f : MulAction.stabilizer G a) : G) •
                ePoint.symm
                  (Option.map (fun x => x * (eUnits d : K)) y)) := by
          rw [hdActionPoint]
        _ = Option.map
              (fun x => eAdd (Additive.ofMul f) + x)
              (Option.map (fun x => x * (eUnits d : K)) y) :=
          hKernelAction f _
        _ = Option.map
              (fun x => eAdd (Additive.ofMul f) + x * (eUnits d : K)) y := by
          cases y <;> rfl
    obtain ⟨t, htne, ht_sq, hta, htb, ht_one⟩ :=
      huppert_blackburn_XI_projectivePointEquiv_exists_normalized_swap
        hsharp a b hab ePoint hPointA hPointB zero_ne_one
    have ht_moves : t • a ≠ a := by
      rw [hta]
      exact hab.symm
    have hDoubleCoset :=
      huppert_II_1_12_b_doubleCoset_decomposition
        htwo_transitive a t ht_moves
    have hXI26_bruhat (g : G) :
        g ∈ MulAction.stabilizer G a ∨
          ∃ h1 h2 : MulAction.stabilizer G a,
            g = (h1 : G) * t * (h2 : G) := by
      have hg :
          g ∈ (MulAction.stabilizer G a : Set G) ∪
            DoubleCoset.doubleCoset t (MulAction.stabilizer G a)
              (MulAction.stabilizer G a) := by
        rw [hDoubleCoset]
        exact Set.mem_univ g
      rcases hg with hg | hg
      · exact Or.inl hg
      · rcases DoubleCoset.mem_doubleCoset.mp hg with
          ⟨h1, hh1, h2, hh2, heq⟩
        exact Or.inr ⟨⟨h1, hh1⟩, ⟨h2, hh2⟩, heq⟩
    let tau : Equiv.Perm (Option K) :=
      ePoint.symm.trans ((MulAction.toPerm t).trans ePoint)
    have hTau_apply (x : Option K) :
        tau x = ePoint (t • ePoint.symm x) := rfl
    have hPointA_symm : ePoint.symm none = a := by
      apply ePoint.injective
      rw [ePoint.apply_symm_apply, hPointA]
    have hPointB_symm : ePoint.symm (some 0) = b := by
      apply ePoint.injective
      rw [ePoint.apply_symm_apply, hPointB]
    have hTauInf : tau none = some 0 := by
      rw [hTau_apply, hPointA_symm, hta, hPointB]
    have hTauZero : tau (some 0) = none := by
      rw [hTau_apply, hPointB_symm, htb, hPointA]
    have hTauOne : tau (some 1) = some 1 := by
      rw [hTau_apply, ht_one, ePoint.apply_symm_apply]
    have hTauSq (x : Option K) : tau (tau x) = x := by
      rw [hTau_apply, hTau_apply, ePoint.symm_apply_apply]
      rw [← mul_smul, ← pow_two, ht_sq, one_smul, ePoint.apply_symm_apply]
    have hXI26_tau_mul_self : tau * tau = 1 := by
      apply Equiv.Perm.ext
      intro x
      exact hTauSq x
    have hXI26_tau_inv : tau⁻¹ = tau := by
      exact inv_eq_of_mul_eq_one_right hXI26_tau_mul_self
    let hXI26_unitPoint : Option K → Prop :=
      fun y => y ≠ none ∧ y ≠ some 0
    have hXI26_tau_preserves_unitPoints (y : Option K) :
        hXI26_unitPoint (tau y) ↔ hXI26_unitPoint y := by
      constructor
      · intro hy
        constructor
        · intro hynone
          apply hy.2
          simpa [hynone] using hTauInf
        · intro hyzero
          apply hy.1
          simpa [hyzero] using hTauZero
      · intro hy
        constructor
        · intro htaunone
          apply hy.2
          exact tau.injective (htaunone.trans hTauZero.symm)
        · intro htauzero
          apply hy.1
          exact tau.injective (htauzero.trans hTauInf.symm)
    let hXI26_tauSubtype :
        Equiv.Perm {y : Option K // hXI26_unitPoint y} :=
      tau.subtypePerm hXI26_tau_preserves_unitPoints
    let hXI26_somePointEquiv : K ≃ {y : Option K // y ≠ none} :=
      Equiv.optionSubtype none ⟨Equiv.refl (Option K), rfl⟩
    let hXI26_nonzeroPointEquiv :
        {x : K // x ≠ 0} ≃
          {y : {y : Option K // y ≠ none} // y.1 ≠ some 0} :=
      hXI26_somePointEquiv.subtypeEquiv (fun x => by
        change x ≠ 0 ↔ some x ≠ some 0
        simp)
    let hXI26_flattenUnitPointEquiv :
        {y : {y : Option K // y ≠ none} // y.1 ≠ some 0} ≃
          {y : Option K // hXI26_unitPoint y} :=
      Equiv.subtypeSubtypeEquivSubtypeInter
        (fun y : Option K => y ≠ none)
        (fun y : Option K => y ≠ some 0)
    let hXI26_unitsOptionEquiv :
        Kˣ ≃ {y : Option K // hXI26_unitPoint y} :=
      unitsEquivNeZero.trans
        (hXI26_nonzeroPointEquiv.trans hXI26_flattenUnitPointEquiv)
    let hXI26_tauUnits : Equiv.Perm Kˣ :=
      hXI26_unitsOptionEquiv.symm.permCongrHom hXI26_tauSubtype
    have hXI26_tauUnits_conj (x : Kˣ) :
        hXI26_unitsOptionEquiv (hXI26_tauUnits x) =
          hXI26_tauSubtype (hXI26_unitsOptionEquiv x) := by
      change hXI26_unitsOptionEquiv
          (hXI26_unitsOptionEquiv.symm
            (hXI26_tauSubtype (hXI26_unitsOptionEquiv x))) = _
      rw [hXI26_unitsOptionEquiv.apply_symm_apply]
    have hXI26_tauUnits_apply (x : Kˣ) :
        some ((hXI26_tauUnits x : Kˣ) : K) =
          tau (some (x : K)) := by
      have h := congrArg Subtype.val (hXI26_tauUnits_conj x)
      simpa [hXI26_unitsOptionEquiv, hXI26_nonzeroPointEquiv,
        hXI26_flattenUnitPointEquiv, hXI26_somePointEquiv,
        hXI26_tauSubtype, hXI26_unitPoint] using h
    have hXI26_actionNormalForm (g : G) :
        (∃ f0 : F,
          ∃ d0 : MulAction.stabilizer
              (MulAction.stabilizer G a) b',
            ∀ y : Option K,
              ePoint (g • ePoint.symm y) =
                Option.map
                  (fun x =>
                    eAdd (Additive.ofMul f0) + x * (eUnits d0 : K)) y) ∨
        (∃ f1 : F,
          ∃ d1 : MulAction.stabilizer
              (MulAction.stabilizer G a) b',
            ∃ f2 : F,
              ∃ d2 : MulAction.stabilizer
                  (MulAction.stabilizer G a) b',
                ∀ y : Option K,
                  ePoint (g • ePoint.symm y) =
                    Option.map
                      (fun x =>
                        eAdd (Additive.ofMul f1) + x * (eUnits d1 : K))
                      (tau
                        (Option.map
                          (fun x =>
                            eAdd (Additive.ofMul f2) +
                              x * (eUnits d2 : K)) y))) := by
      rcases hXI26_bruhat g with hg | ⟨h1, h2, hg⟩
      · let h : MulAction.stabilizer G a := ⟨g, hg⟩
        rcases hXI26_stabilizerAffine h with
          ⟨f0, d0, _hdecomp, haction⟩
        left
        refine ⟨f0, d0, ?_⟩
        intro y
        simpa [h] using haction y
      · rcases hXI26_stabilizerAffine h1 with
          ⟨f1, d1, _hdecomp1, haction1⟩
        rcases hXI26_stabilizerAffine h2 with
          ⟨f2, d2, _hdecomp2, haction2⟩
        right
        refine ⟨f1, d1, f2, d2, ?_⟩
        intro y
        have hh2Point :
            ((h2 : G) • ePoint.symm y) =
              ePoint.symm
                (Option.map
                  (fun x =>
                    eAdd (Additive.ofMul f2) + x * (eUnits d2 : K)) y) := by
          apply ePoint.injective
          rw [haction2 y, ePoint.apply_symm_apply]
        have htPoint :
            t • ePoint.symm
                (Option.map
                  (fun x =>
                    eAdd (Additive.ofMul f2) + x * (eUnits d2 : K)) y) =
              ePoint.symm
                (tau
                  (Option.map
                    (fun x =>
                      eAdd (Additive.ofMul f2) + x * (eUnits d2 : K)) y)) := by
          apply ePoint.injective
          rw [← hTau_apply, ePoint.apply_symm_apply]
        calc
          ePoint (g • ePoint.symm y) =
              ePoint
                ((h1 : G) •
                  (t • ((h2 : G) • ePoint.symm y))) := by
            rw [hg, mul_smul, mul_smul]
          _ = ePoint
                ((h1 : G) •
                  (t • ePoint.symm
                    (Option.map
                      (fun x =>
                        eAdd (Additive.ofMul f2) +
                          x * (eUnits d2 : K)) y))) := by
            rw [hh2Point]
          _ = ePoint
                ((h1 : G) •
                  ePoint.symm
                    (tau
                      (Option.map
                        (fun x =>
                          eAdd (Additive.ofMul f2) +
                            x * (eUnits d2 : K)) y))) := by
            rw [htPoint]
          _ = Option.map
                (fun x =>
                  eAdd (Additive.ofMul f1) + x * (eUnits d1 : K))
                (tau
                  (Option.map
                    (fun x =>
                      eAdd (Additive.ofMul f2) +
                        x * (eUnits d2 : K)) y)) :=
            haction1 _
    let hXI26_affinePerm (f0 : F)
        (d0 : MulAction.stabilizer (MulAction.stabilizer G a) b') :
        Equiv.Perm (Option K) :=
      Equiv.optionCongr
        ((eUnits d0).mulRight.trans
          (Equiv.addLeft (eAdd (Additive.ofMul f0))))
    have hXI26_affinePerm_apply (f0 : F)
        (d0 : MulAction.stabilizer (MulAction.stabilizer G a) b')
        (y : Option K) :
        hXI26_affinePerm f0 d0 y =
          Option.map
            (fun x => eAdd (Additive.ofMul f0) + x * (eUnits d0 : K)) y :=
      rfl
    let hXI26_coordinatePermHom : G →* Equiv.Perm (Option K) :=
      ePoint.permCongrHom.toMonoidHom.comp (MulAction.toPermHom G Omega)
    have hXI26_coordinatePermHom_injective :
        Function.Injective hXI26_coordinatePermHom :=
      ePoint.permCongrHom.injective.comp MulAction.toPerm_injective
    have hXI26_coordinatePermHom_apply (g : G) (y : Option K) :
        hXI26_coordinatePermHom g y =
          ePoint (g • ePoint.symm y) :=
      rfl
    have hXI26_coordinatePermHom_t : hXI26_coordinatePermHom t = tau :=
      rfl
    have hXI26_permNormalForm (g : G) :
        (∃ f0 : F,
          ∃ d0 : MulAction.stabilizer
              (MulAction.stabilizer G a) b',
            hXI26_coordinatePermHom g = hXI26_affinePerm f0 d0) ∨
        (∃ f1 : F,
          ∃ d1 : MulAction.stabilizer
              (MulAction.stabilizer G a) b',
            ∃ f2 : F,
              ∃ d2 : MulAction.stabilizer
                  (MulAction.stabilizer G a) b',
                hXI26_coordinatePermHom g =
                  hXI26_affinePerm f1 d1 * tau *
                    hXI26_affinePerm f2 d2) := by
      rcases hXI26_actionNormalForm g with
        ⟨f0, d0, haction⟩ | ⟨f1, d1, f2, d2, haction⟩
      · left
        refine ⟨f0, d0, ?_⟩
        apply Equiv.Perm.ext
        intro y
        rw [hXI26_coordinatePermHom_apply, haction y,
          hXI26_affinePerm_apply]
      · right
        refine ⟨f1, d1, f2, d2, ?_⟩
        apply Equiv.Perm.ext
        intro y
        rw [hXI26_coordinatePermHom_apply, haction y,
          Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
          hXI26_affinePerm_apply, hXI26_affinePerm_apply]
    have hXI26_affineRealized (f0 : F)
        (d0 : MulAction.stabilizer (MulAction.stabilizer G a) b') :
        hXI26_coordinatePermHom
            (((f0 : MulAction.stabilizer G a) *
              (d0 : MulAction.stabilizer G a)⁻¹ :
                MulAction.stabilizer G a) : G) =
          hXI26_affinePerm f0 d0 := by
      apply Equiv.Perm.ext
      intro y
      have hdActionPoint :
          (((d0 : MulAction.stabilizer G a) : G)⁻¹) •
              ePoint.symm y =
            ePoint.symm
              (Option.map (fun x => x * (eUnits d0 : K)) y) := by
        apply ePoint.injective
        rw [hUnitsAction d0 y, ePoint.apply_symm_apply]
      calc
        hXI26_coordinatePermHom
              (((f0 : MulAction.stabilizer G a) *
                (d0 : MulAction.stabilizer G a)⁻¹ :
                  MulAction.stabilizer G a) : G) y =
            ePoint
              (((((f0 : MulAction.stabilizer G a) *
                (d0 : MulAction.stabilizer G a)⁻¹ :
                  MulAction.stabilizer G a) : G)) •
                ePoint.symm y) :=
          hXI26_coordinatePermHom_apply _ y
        _ = ePoint
              (((f0 : MulAction.stabilizer G a) : G) •
                ((((d0 : MulAction.stabilizer G a) : G)⁻¹) •
                  ePoint.symm y)) := by
          change ePoint
              (((((f0 : MulAction.stabilizer G a) : G) *
                (((d0 : MulAction.stabilizer G a) : G)⁻¹)) •
                  ePoint.symm y)) = _
          rw [mul_smul]
        _ = ePoint
              (((f0 : MulAction.stabilizer G a) : G) •
                ePoint.symm
                  (Option.map (fun x => x * (eUnits d0 : K)) y)) := by
          rw [hdActionPoint]
        _ = Option.map
              (fun x => eAdd (Additive.ofMul f0) + x)
              (Option.map (fun x => x * (eUnits d0 : K)) y) :=
          hKernelAction f0 _
        _ = Option.map
              (fun x =>
                eAdd (Additive.ofMul f0) + x * (eUnits d0 : K)) y := by
          cases y <;> rfl
        _ = hXI26_affinePerm f0 d0 y :=
          (hXI26_affinePerm_apply f0 d0 y).symm
    let hXI26_stabilizerPermHom :
        MulAction.stabilizer G a →* Equiv.Perm (Option K) :=
      hXI26_coordinatePermHom.comp
        (Subgroup.subtype (MulAction.stabilizer G a))
    let hXI26_affineSubgroup : Subgroup (Equiv.Perm (Option K)) :=
      hXI26_stabilizerPermHom.range
    have hXI26_affineSubgroup_eq :
        (hXI26_affineSubgroup : Set (Equiv.Perm (Option K))) =
          {sigma | ∃ f0 : F,
            ∃ d0 : MulAction.stabilizer
                (MulAction.stabilizer G a) b',
              sigma = hXI26_affinePerm f0 d0} := by
      ext sigma
      constructor
      · intro hsigma
        change sigma ∈ hXI26_stabilizerPermHom.range at hsigma
        rcases hsigma with ⟨h, rfl⟩
        rcases hXI26_stabilizerAffine h with
          ⟨f0, d0, _hdecomp, haction⟩
        refine ⟨f0, d0, ?_⟩
        apply Equiv.Perm.ext
        intro y
        change hXI26_coordinatePermHom (h : G) y =
          hXI26_affinePerm f0 d0 y
        rw [hXI26_coordinatePermHom_apply, haction y,
          hXI26_affinePerm_apply]
      · rintro ⟨f0, d0, rfl⟩
        change hXI26_affinePerm f0 d0 ∈
          hXI26_stabilizerPermHom.range
        refine ⟨(f0 : MulAction.stabilizer G a) *
          (d0 : MulAction.stabilizer G a)⁻¹, ?_⟩
        change hXI26_coordinatePermHom
            ((((f0 : MulAction.stabilizer G a) *
              (d0 : MulAction.stabilizer G a)⁻¹ :
                MulAction.stabilizer G a) : G)) =
          hXI26_affinePerm f0 d0
        exact hXI26_affineRealized f0 d0
    have hXI26_affineSubgroup_mem_iff_fix_inf
        (sigma : hXI26_coordinatePermHom.range) :
        ((sigma : Equiv.Perm (Option K)) ∈ hXI26_affineSubgroup ↔
          (sigma : Equiv.Perm (Option K)) none = none) := by
      constructor
      · intro hsigma
        have hsigma' :
            (sigma : Equiv.Perm (Option K)) ∈
              (hXI26_affineSubgroup : Set (Equiv.Perm (Option K))) :=
          hsigma
        rw [hXI26_affineSubgroup_eq] at hsigma'
        rcases hsigma' with ⟨f0, d0, hsigma_eq⟩
        calc
          (sigma : Equiv.Perm (Option K)) none =
              hXI26_affinePerm f0 d0 none :=
            congrArg (fun q : Equiv.Perm (Option K) => q none) hsigma_eq
          _ = none := hXI26_affinePerm_apply f0 d0 none
      · intro hsigma
        rcases sigma.property with ⟨g, hg⟩
        have hga : g • a = a := by
          apply ePoint.injective
          calc
            ePoint (g • a) = hXI26_coordinatePermHom g none := by
              rw [hXI26_coordinatePermHom_apply, hPointA_symm]
            _ = (sigma : Equiv.Perm (Option K)) none :=
              congrArg (fun q : Equiv.Perm (Option K) => q none) hg
            _ = none := hsigma
            _ = ePoint a := hPointA.symm
        change (sigma : Equiv.Perm (Option K)) ∈
          hXI26_stabilizerPermHom.range
        refine ⟨⟨g, hga⟩, ?_⟩
        change hXI26_coordinatePermHom g =
          (sigma : Equiv.Perm (Option K))
        exact hg
    let hXI26_twoPointPermHom :
        MulAction.stabilizer (MulAction.stabilizer G a) b' →*
          Equiv.Perm (Option K) :=
      hXI26_coordinatePermHom.comp
        ((Subgroup.subtype (MulAction.stabilizer G a)).comp
          (Subgroup.subtype
            (MulAction.stabilizer (MulAction.stabilizer G a) b')))
    let hXI26_multiplierSubgroup : Subgroup (Equiv.Perm (Option K)) :=
      hXI26_twoPointPermHom.range
    have hXI26_multiplierSubgroup_eq :
        (hXI26_multiplierSubgroup : Set (Equiv.Perm (Option K))) =
          {sigma | ∃ d0 : MulAction.stabilizer
              (MulAction.stabilizer G a) b',
            sigma = hXI26_affinePerm 1 d0} := by
      ext sigma
      constructor
      · intro hsigma
        change sigma ∈ hXI26_twoPointPermHom.range at hsigma
        rcases hsigma with ⟨d0, rfl⟩
        refine ⟨d0⁻¹, ?_⟩
        change hXI26_coordinatePermHom
            (((d0 : MulAction.stabilizer G a) : G)) =
          hXI26_affinePerm 1 d0⁻¹
        simpa using hXI26_affineRealized (1 : F) d0⁻¹
      · rintro ⟨d0, rfl⟩
        change hXI26_affinePerm 1 d0 ∈ hXI26_twoPointPermHom.range
        refine ⟨d0⁻¹, ?_⟩
        change hXI26_coordinatePermHom
            ((((d0⁻¹ : MulAction.stabilizer
              (MulAction.stabilizer G a) b') :
                MulAction.stabilizer G a) : G)) =
          hXI26_affinePerm 1 d0
        simpa using hXI26_affineRealized (1 : F) d0
    have hXI26_multiplierSubgroup_mem_iff_fix_zero
        (sigma : hXI26_coordinatePermHom.range) :
        ((sigma : Equiv.Perm (Option K)) ∈ hXI26_multiplierSubgroup ↔
          (sigma : Equiv.Perm (Option K)) ∈ hXI26_affineSubgroup ∧
            (sigma : Equiv.Perm (Option K)) (some 0) = some 0) := by
      constructor
      · intro hsigma
        have hsigma' :
            (sigma : Equiv.Perm (Option K)) ∈
              (hXI26_multiplierSubgroup : Set (Equiv.Perm (Option K))) :=
          hsigma
        rw [hXI26_multiplierSubgroup_eq] at hsigma'
        rcases hsigma' with ⟨d0, hsigma_eq⟩
        have hfixInf : (sigma : Equiv.Perm (Option K)) none = none := by
          calc
            (sigma : Equiv.Perm (Option K)) none =
                hXI26_affinePerm 1 d0 none :=
              congrArg (fun q : Equiv.Perm (Option K) => q none) hsigma_eq
            _ = none := hXI26_affinePerm_apply 1 d0 none
        refine ⟨hXI26_affineSubgroup_mem_iff_fix_inf sigma |>.mpr hfixInf, ?_⟩
        calc
          (sigma : Equiv.Perm (Option K)) (some 0) =
              hXI26_affinePerm 1 d0 (some 0) :=
            congrArg (fun q : Equiv.Perm (Option K) => q (some 0)) hsigma_eq
          _ = some 0 := by
            rw [hXI26_affinePerm_apply]
            simp
      · rintro ⟨hsigmaA, hsigmaZero⟩
        change (sigma : Equiv.Perm (Option K)) ∈
          hXI26_twoPointPermHom.range
        change (sigma : Equiv.Perm (Option K)) ∈
          hXI26_stabilizerPermHom.range at hsigmaA
        rcases hsigmaA with ⟨h, hh⟩
        have hhb : h • b' = b' := by
          apply Subtype.ext
          apply ePoint.injective
          calc
            ePoint (((h : MulAction.stabilizer G a) : G) • b) =
                hXI26_coordinatePermHom (h : G) (some 0) := by
              rw [hXI26_coordinatePermHom_apply, hPointB_symm]
            _ = (sigma : Equiv.Perm (Option K)) (some 0) :=
              congrArg (fun q : Equiv.Perm (Option K) => q (some 0)) hh
            _ = some 0 := hsigmaZero
            _ = ePoint b := hPointB.symm
        let d0 : MulAction.stabilizer (MulAction.stabilizer G a) b' :=
          ⟨h, MulAction.mem_stabilizer_iff.mpr hhb⟩
        refine ⟨d0, ?_⟩
        change hXI26_coordinatePermHom (h : G) =
          (sigma : Equiv.Perm (Option K))
        exact hh
    have hXI26_twoPointPermHom_injective :
        Function.Injective hXI26_twoPointPermHom := by
      intro d1 d2 hd
      apply Subtype.ext
      apply Subtype.ext
      apply hXI26_coordinatePermHom_injective
      exact hd
    let hXI26_twoPointRangeModel :
        MulAction.stabilizer (MulAction.stabilizer G a) b' ≃*
          hXI26_multiplierSubgroup :=
      MonoidHom.ofInjective hXI26_twoPointPermHom_injective
    let hXI26_multiplierOppositeEquiv :
        (Kˣ)ᵐᵒᵖ ≃* hXI26_multiplierSubgroup :=
      (MulEquiv.inv' Kˣ).symm.trans
        (eUnits.symm.trans hXI26_twoPointRangeModel)
    have hXI26_multiplierOppositeEquiv_apply (u : (Kˣ)ᵐᵒᵖ) :
        ((hXI26_multiplierOppositeEquiv u : hXI26_multiplierSubgroup) :
            Equiv.Perm (Option K)) =
          hXI26_affinePerm 1 (eUnits.symm u.unop) := by
      change hXI26_coordinatePermHom
          ((((eUnits.symm (u.unop⁻¹) :
            MulAction.stabilizer (MulAction.stabilizer G a) b') :
              MulAction.stabilizer G a) : G)) =
        hXI26_affinePerm 1 (eUnits.symm u.unop)
      simpa using hXI26_affineRealized (1 : F) (eUnits.symm u.unop)
    have hXI26_conjAffine_mem_iff_fix_zero
        (sigma : hXI26_coordinatePermHom.range) :
        ((sigma : Equiv.Perm (Option K)) ∈
              hXI26_affineSubgroup.conjBy tau ↔
          (sigma : Equiv.Perm (Option K)) (some 0) = some 0) := by
      constructor
      · intro hsigma
        rw [Subgroup.conjBy, Subgroup.mem_map] at hsigma
        rcases hsigma with ⟨alpha, halphaA, halphaSigma⟩
        have halphaRange : alpha ∈ hXI26_coordinatePermHom.range := by
          have halphaA' := halphaA
          change alpha ∈ hXI26_stabilizerPermHom.range at halphaA'
          rcases halphaA' with ⟨h, hh⟩
          exact ⟨(h : G), hh⟩
        have halphaInf : alpha none = none :=
          hXI26_affineSubgroup_mem_iff_fix_inf
            ⟨alpha, halphaRange⟩ |>.mp halphaA
        rw [← halphaSigma]
        change tau (alpha (tau⁻¹ (some 0))) = some 0
        rw [hXI26_tau_inv, hTauZero, halphaInf, hTauInf]
      · intro hsigmaZero
        let alpha : Equiv.Perm (Option K) :=
          tau * (sigma : Equiv.Perm (Option K)) * tau
        have htauRange : tau ∈ hXI26_coordinatePermHom.range :=
          ⟨t, hXI26_coordinatePermHom_t⟩
        have halphaRange : alpha ∈ hXI26_coordinatePermHom.range :=
          hXI26_coordinatePermHom.range.mul_mem
            (hXI26_coordinatePermHom.range.mul_mem htauRange sigma.property)
            htauRange
        have halphaInf : alpha none = none := by
          change tau ((sigma : Equiv.Perm (Option K)) (tau none)) = none
          rw [hTauInf, hsigmaZero, hTauZero]
        have halphaA : alpha ∈ hXI26_affineSubgroup :=
          hXI26_affineSubgroup_mem_iff_fix_inf
            ⟨alpha, halphaRange⟩ |>.mpr halphaInf
        rw [Subgroup.conjBy, Subgroup.mem_map]
        refine ⟨alpha, halphaA, ?_⟩
        change tau * alpha * tau⁻¹ =
          (sigma : Equiv.Perm (Option K))
        rw [hXI26_tau_inv]
        calc
          tau * alpha * tau =
              (tau * tau) * (sigma : Equiv.Perm (Option K)) *
                (tau * tau) := by
            simp only [alpha]
            group
          _ = (sigma : Equiv.Perm (Option K)) := by
            rw [hXI26_tau_mul_self]
            simp
    have hXI26_multiplierSubgroup_eq_inf_conj :
        hXI26_multiplierSubgroup =
          hXI26_affineSubgroup ⊓ hXI26_affineSubgroup.conjBy tau := by
      apply le_antisymm
      · intro sigma hsigmaB
        have hsigmaRange : sigma ∈ hXI26_coordinatePermHom.range := by
          have hsigmaB' := hsigmaB
          change sigma ∈ hXI26_twoPointPermHom.range at hsigmaB'
          rcases hsigmaB' with ⟨d0, hd0⟩
          exact ⟨(((d0 : MulAction.stabilizer G a) : G)), hd0⟩
        have hsigmaChar :=
          hXI26_multiplierSubgroup_mem_iff_fix_zero
            ⟨sigma, hsigmaRange⟩ |>.mp hsigmaB
        exact ⟨hsigmaChar.1,
          hXI26_conjAffine_mem_iff_fix_zero
            ⟨sigma, hsigmaRange⟩ |>.mpr hsigmaChar.2⟩
      · intro sigma hsigmaInf
        have hsigmaRange : sigma ∈ hXI26_coordinatePermHom.range := by
          have hsigmaA := hsigmaInf.1
          change sigma ∈ hXI26_stabilizerPermHom.range at hsigmaA
          rcases hsigmaA with ⟨h, hh⟩
          exact ⟨(h : G), hh⟩
        apply hXI26_multiplierSubgroup_mem_iff_fix_zero
          ⟨sigma, hsigmaRange⟩ |>.mpr
        exact ⟨hsigmaInf.1,
          hXI26_conjAffine_mem_iff_fix_zero
            ⟨sigma, hsigmaRange⟩ |>.mp hsigmaInf.2⟩
    have hXI26_coordinateRange_eq :
        (hXI26_coordinatePermHom.range :
            Set (Equiv.Perm (Option K))) =
          (hXI26_affineSubgroup : Set (Equiv.Perm (Option K))) ∪
            DoubleCoset.doubleCoset tau hXI26_affineSubgroup
              hXI26_affineSubgroup := by
      ext sigma
      constructor
      · intro hsigma
        change sigma ∈ hXI26_coordinatePermHom.range at hsigma
        rcases hsigma with ⟨g, rfl⟩
        rcases hXI26_bruhat g with hg | ⟨h1, h2, hg⟩
        · left
          change hXI26_coordinatePermHom g ∈
            hXI26_stabilizerPermHom.range
          exact ⟨⟨g, hg⟩, rfl⟩
        · right
          apply DoubleCoset.mem_doubleCoset.mpr
          refine ⟨hXI26_stabilizerPermHom h1, ⟨h1, rfl⟩,
            hXI26_stabilizerPermHom h2, ⟨h2, rfl⟩, ?_⟩
          change hXI26_coordinatePermHom g =
            hXI26_coordinatePermHom (h1 : G) * tau *
              hXI26_coordinatePermHom (h2 : G)
          rw [hg, map_mul, map_mul, hXI26_coordinatePermHom_t]
      · intro hsigma
        rcases hsigma with hsigma | hsigma
        · change sigma ∈ hXI26_stabilizerPermHom.range at hsigma
          rcases hsigma with ⟨h, rfl⟩
          change hXI26_coordinatePermHom (h : G) ∈
            hXI26_coordinatePermHom.range
          exact ⟨(h : G), rfl⟩
        · rcases DoubleCoset.mem_doubleCoset.mp hsigma with
            ⟨sigma1, hsigma1, sigma2, hsigma2, hsigma⟩
          change sigma1 ∈ hXI26_stabilizerPermHom.range at hsigma1
          change sigma2 ∈ hXI26_stabilizerPermHom.range at hsigma2
          rcases hsigma1 with ⟨h1, rfl⟩
          rcases hsigma2 with ⟨h2, rfl⟩
          change sigma ∈ hXI26_coordinatePermHom.range
          refine ⟨(h1 : G) * t * (h2 : G), ?_⟩
          rw [map_mul, map_mul, hXI26_coordinatePermHom_t]
          exact hsigma.symm
    let hXI26_rangeModel :
        G ≃* hXI26_coordinatePermHom.range :=
      MonoidHom.ofInjective hXI26_coordinatePermHom_injective
    rcases hXI26_core p f hp hf hn hsharp hFelem
        K hNF eAdd eUnits hmul_coordinate
        ePoint hPointA hPointB hKernelAction hUnitsAction
        hXI26_stabilizerAffine t ht_sq hta ht_one hXI26_bruhat
        tau hTau_apply hTauSq
        hXI26_tauUnits hXI26_tauUnits_apply
        hXI26_affinePerm hXI26_affinePerm_apply
        hXI26_coordinatePermHom hXI26_coordinatePermHom_apply
        hXI26_coordinatePermHom_injective
        hXI26_affineSubgroup
        hXI26_affineSubgroup_eq hXI26_affineSubgroup_mem_iff_fix_inf
        hXI26_multiplierSubgroup
        hXI26_multiplierOppositeEquiv
        hXI26_multiplierOppositeEquiv_apply
        hXI26_multiplierSubgroup_eq_inf_conj
        hXI26_coordinateRange_eq with
      ⟨⟨C, hCcyclic, hCindex⟩, hPGLRange⟩
    have hPGL :
        ∀ hcomm : ∀ x y : K, x * y = y * x,
          let fieldInst : Field K := rightNearFieldFieldOfComm K hcomm
          letI : Field K := fieldInst
          Nonempty (G ≃* Matrix.ProjGenLinGroup (Fin 2) K) := by
      intro hcomm
      let fieldInst : Field K := rightNearFieldFieldOfComm K hcomm
      letI : Field K := fieldInst
      exact (hPGLRange hcomm).map
        (fun eRange => hXI26_rangeModel.trans eRange)
    have hPGL_over_galoisField :
        ∀ hcomm : ∀ x y : K, x * y = y * x,
          let fieldInst : Field K := rightNearFieldFieldOfComm K hcomm
          letI : Field K := fieldInst
          ∃ (L : Type w) (_ : Field L) (_ : Finite L),
            Nat.card L = n ∧
            Nonempty (G ≃* Matrix.ProjGenLinGroup (Fin 2) L) := by
      intro hcomm
      let fieldInst : Field K := rightNearFieldFieldOfComm K hcomm
      letI : Field K := fieldInst
      letI : Fintype K := Fintype.ofFinite K
      letI : Fact (Nat.Prime p) := ⟨hp⟩
      let L : Type w := ULift.{w} (GaloisField p f)
      letI : Field L := inferInstance
      letI : Finite L := inferInstance
      letI : Fintype L := Fintype.ofFinite L
      have hLcard : Nat.card L = n := by
        calc
          Nat.card L = Nat.card (GaloisField p f) :=
            Nat.card_congr (Equiv.ulift : L ≃ GaloisField p f)
          _ = p ^ f := GaloisField.card p f (Nat.ne_of_gt hf)
          _ = n := hn.symm
      have hcard : Fintype.card K = Fintype.card L := by
        rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
          hKcard, hLcard]
      let eKL : K ≃+* L := FiniteField.ringEquivOfCardEq hcard
      refine ⟨L, inferInstance, inferInstance, hLcard, ?_⟩
      exact (hPGL hcomm).map
        (fun eG => eG.trans (pgl2EquivOfRingEquiv eKL))
    have hCindex_cases : C.index = 1 ∨ C.index = 2 := by
      have hCindex_ne : C.index ≠ 0 := Subgroup.index_ne_zero_of_finite
      omega
    rcases hCindex_cases with hCindex_one | hCindex_two
    · have hCtop : C = ⊤ := Subgroup.index_eq_one.mp hCindex_one
      have htopCyclic : IsCyclic (⊤ : Subgroup Kˣ) := hCtop ▸ hCcyclic
      have hUnitsCyclic : IsCyclic Kˣ :=
        (Subgroup.topEquiv : (⊤ : Subgroup Kˣ) ≃* Kˣ).isCyclic.mp htopCyclic
      letI : IsCyclic Kˣ := hUnitsCyclic
      have hcomm : ∀ x y : K, x * y = y * x := by
        intro x y
        by_cases hx : x = 0
        · simp [hx]
        by_cases hy : y = 0
        · simp [hy]
        let ux : Kˣ := Units.mk0 x hx
        let uy : Kˣ := Units.mk0 y hy
        have hxy : ux * uy = uy * ux := mul_comm' ux uy
        simpa [ux, uy] using congrArg (fun z : Kˣ => (z : K)) hxy
      exact Or.inl (hPGL_over_galoisField hcomm)
    · rcases PFAppendixII.proposition_2 C hCcyclic hCindex_two with
        hcomm | ⟨r, m, hmodel⟩
      · exact Or.inl (hPGL_over_galoisField hcomm)
      · have hoddEven :=
          dicksonIndexTwoModel_odd_characteristic_even_degree
            hp (hKcard.trans hn) hNFchar hmodel
        exact Or.inr ⟨hoddEven.1, hoddEven.2, hsharp⟩
  have hXI68_core :
      ¬ SharpTriple → IsMulCommutative F →
        ∃ (K : Type w) (_ : Field K),
          Nat.card K = Nat.card F ∧
            Nonempty (G ≃*
              Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) := by
    intro hsharp hFcomm
    exact
      huppert_XI_6_8_abelianKernel_psl
        htwo_transitive hat_most_two_fixed_points hno_regular_normal
        a b hab F hFrob hsharp hFcomm
  have hXI68 :
      ¬ SharpTriple → IsMulCommutative F →
        ∃ p f : ℕ, Nat.Prime p ∧ 0 < f ∧ n = p ^ f ∧ Odd p ∧
          ∃ (K : Type w) (_ : Field K) (_ : Finite K),
            Nat.card K = n ∧
            Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) := by
    intro hsharp hFcomm
    rcases hXI68_core hsharp hFcomm with
      ⟨K, fieldInst, hKcardF, hmodel⟩
    letI : Field K := fieldInst
    have hKcard : Nat.card K = n := hKcardF.trans hFcard
    letI : Finite K := Nat.finite_of_card_ne_zero (by
      rw [hKcard]
      exact hnpos.ne')
    have hcharNe : ringChar K ≠ 2 := by
      intro hchar
      have hneg : (-1 : K) = 1 := neg_one_eq_one_iff.mpr hchar
      have hcenterCard :
          Nat.card
              (Subgroup.center
                (Matrix.SpecialLinearGroup (Fin 2) K)) = 1 :=
        huppert614_card_center_of_neg_one_eq_one hneg
      have hPSLcard :
          Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) =
            n * (n ^ 2 - 1) := by
        have hmul := huppert614_card_psl_mul_center (K := K)
        rw [hcenterCard, mul_one, hKcard] at hmul
        exact hmul
      let e : G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
        Classical.choice hmodel
      have hfactor : n ^ 2 - 1 = (n - 1) * (n + 1) := by
        let r := n - 1
        have hneq : n = r + 1 := by
          dsimp [r]
          omega
        rw [hneq]
        simp only [Nat.add_sub_cancel]
        apply (tsub_eq_iff_eq_add_of_le (Nat.one_le_pow' 2 r)).2
        ring
      have hGcard :
          Nat.card G = (Fintype.card Omega).descFactorial 3 := by
        calc
          Nat.card G =
              Nat.card
                (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) :=
            Nat.card_congr e.toEquiv
          _ = n * (n ^ 2 - 1) := hPSLcard
          _ = (n + 1) * n * (n - 1) := by
            rw [hfactor]
            ac_rfl
          _ = (Fintype.card Omega).descFactorial 3 := by
            rw [hdegree]
            simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, mul_one]
            have hsub_one : n + 1 - 1 = n := by omega
            have hsub_two : n + 1 - 2 = n - 1 := by omega
            rw [hsub_one, hsub_two]
            simp only [Nat.sub_zero]
            ac_rfl
      exact hsharp
        (sharpTriple_of_card_eq_descFactorial hGcard
          hat_most_two_fixed_points)
    exact finiteField_oddCharacteristic_psl_package
      hKcard hcharNe hmodel
  have hXI61_noncommutativeSylow :
      ¬ IsMulCommutative F → Group.IsNilpotent F →
        ∃ p : ℕ, Nat.Prime p ∧
          ∃ P : Sylow p F, ¬ IsMulCommutative P := by
    intro hFcomm hFnil'
    by_contra h
    push Not at h
    obtain ⟨e⟩ :=
      ((Group.isNilpotent_of_finite_tfae (G := F)).out 1 5).mp hFnil'
    apply hFcomm
    refine ⟨⟨fun x y => ?_⟩⟩
    have hcoord : e.symm x * e.symm y = e.symm y * e.symm x := by
      funext p P
      exact
        (h p.val (Nat.prime_of_mem_primeFactors p.property) P).is_comm.comm
          (e.symm x p P) (e.symm y p P)
    calc
      x * y = e (e.symm x) * e (e.symm y) := by
        rw [e.apply_symm_apply, e.apply_symm_apply]
      _ = e (e.symm x * e.symm y) := (e.map_mul _ _).symm
      _ = e (e.symm y * e.symm x) := congrArg e hcoord
      _ = e (e.symm y) * e (e.symm x) := e.map_mul _ _
      _ = y * x := by rw [e.apply_symm_apply, e.apply_symm_apply]
  have hXI61_existsCentralPrimeElement :
      ∀ q : ℕ, Nat.Prime q → q ∣ Nat.card F → Group.IsNilpotent F →
        ∃ z : F, z ≠ 1 ∧ orderOf z = q ∧ z ∈ Subgroup.center F := by
    intro q hq hqdiv hFnil'
    letI : Fact (Nat.Prime q) := ⟨hq⟩
    letI : Group.IsNilpotent F := hFnil'
    let Q : Sylow q F := default
    have hQne : (Q : Subgroup F) ≠ ⊥ :=
      Sylow.ne_bot_of_dvd_card Q hqdiv
    letI : Nontrivial Q :=
      (Subgroup.nontrivial_iff_ne_bot (Q : Subgroup F)).mpr hQne
    have hcenterP : IsPGroup q (Subgroup.center Q) :=
      Q.isPGroup'.to_subgroup _
    have hcenter_ne : (Subgroup.center Q : Subgroup Q) ≠ ⊥ :=
      (Subgroup.nontrivial_iff_ne_bot (Subgroup.center Q)).mp
        (IsPGroup.center_nontrivial Q.isPGroup')
    have hqcenter : q ∣ Nat.card (Subgroup.center Q) := by
      rcases hcenterP.card_eq_or_dvd with hcard | hdiv
      · have hone : 1 < Nat.card (Subgroup.center Q) :=
          (Subgroup.one_lt_card_iff_ne_bot (Subgroup.center Q)).mpr hcenter_ne
        omega
      · exact hdiv
    obtain ⟨z, hzorder⟩ :=
      exists_prime_orderOf_dvd_card' (G := Subgroup.center Q) q hqcenter
    let zF : F := ((z : Subgroup.center Q) : Q)
    have hzorderF : orderOf zF = q := by
      calc
        orderOf zF = orderOf (((z : Subgroup.center Q) : Q) : F) := rfl
        _ = orderOf ((z : Subgroup.center Q) : Q) :=
          Subgroup.orderOf_coe ((z : Subgroup.center Q) : Q)
        _ = orderOf z := Subgroup.orderOf_coe z
        _ = q := hzorder
    have hzFne : zF ≠ 1 := by
      intro hz
      have horder_one : orderOf zF = 1 := by simp [hz]
      exact hq.ne_one (hzorderF.symm.trans horder_one)
    have hzmap :
        zF ∈ (Subgroup.center (Q : Subgroup F)).map
          (Q : Subgroup F).subtype := by
      exact Subgroup.mem_map.mpr ⟨(z : Subgroup.center Q), z.property, rfl⟩
    exact ⟨zF, hzFne, hzorderF,
      section8_center_sylow_map_le_center_of_nilpotent Q hzmap⟩
  have hXI61_centralPrime_eq_noncommutativeSylowPrime_core :
      ∀ p : ℕ, Nat.Prime p →
        ∀ P : Sylow p F, ¬ IsMulCommutative P →
          ∀ z : F, Nat.Prime (orderOf z) →
              Subgroup.centralizer
                  ({((z : MulAction.stabilizer G a) : G)} : Set G) =
                F.map (MulAction.stabilizer G a).subtype →
              orderOf z = p := by
    intro p hp P hPnoncomm z hzprime hcentralizer
    exact
      huppert_XI_6_1_centralPrime_eq_noncommutativeSylowPrime
        htwo_transitive hat_most_two_fixed_points hno_regular_normal
        a b hab F hFrob hFnil p hp P hPnoncomm z hzprime hcentralizer
  have hXI61_centralPrime_eq_noncommutativeSylowPrime :
      ∀ p : ℕ, Nat.Prime p →
        ∀ P : Sylow p F, ¬ IsMulCommutative P →
          ∀ q : ℕ, Nat.Prime q →
            ∀ z : F, z ≠ 1 → orderOf z = q →
              z ∈ Subgroup.center F → q = p := by
    intro p hp P hPcomm q hq z hzne hzorder hzcenter
    have hzprime : Nat.Prime (orderOf z) := by simpa [hzorder] using hq
    have hzp := hXI61_centralPrime_eq_noncommutativeSylowPrime_core
      p hp P hPcomm z hzprime
      (huppert_blackburn_XI_frobeniusKernel_centralizer_eq_map
        htwo_transitive a b hab F hFrob z hzne hzcenter)
    exact hzorder.symm.trans hzp
  have hXI61_uniquePrime_core :
      ∀ p : ℕ, Nat.Prime p →
        ∀ P : Sylow p F, ¬ IsMulCommutative P →
          Group.IsNilpotent F →
            ∀ q : ℕ, Nat.Prime q → q ∣ Nat.card F → q = p := by
    intro p hp P hPcomm hFnil' q hq hqdiv
    obtain ⟨z, hzne, hzorder, hzcenter⟩ :=
      hXI61_existsCentralPrimeElement q hq hqdiv hFnil'
    exact hXI61_centralPrime_eq_noncommutativeSylowPrime
      p hp P hPcomm q hq z hzne hzorder hzcenter
  have hXI61_core :
      ¬ IsMulCommutative F → Group.IsNilpotent F →
        ∃ p : ℕ, Nat.Prime p ∧ IsPGroup p F := by
    intro hFcomm hFnil'
    obtain ⟨p, hp, P, hPcomm⟩ :=
      hXI61_noncommutativeSylow hFcomm hFnil'
    have hcardPower :
        Nat.card F = p ^ (Nat.card F).primeFactorsList.length := by
      set_option backward.isDefEq.respectTransparency false in
        exact Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne'
          (fun {q} hq hqdiv =>
            hXI61_uniquePrime_core
              p hp P hPcomm hFnil' q hq hqdiv)
    letI : Fact (Nat.Prime p) := ⟨hp⟩
    exact ⟨p, hp, IsPGroup.iff_card.mpr
      ⟨(Nat.card F).primeFactorsList.length, hcardPower⟩⟩
  have hXI61 :
      ¬ IsMulCommutative F →
        ∃ p f : ℕ, Nat.Prime p ∧ 0 < f ∧ n = p ^ f := by
    intro hFcomm
    rcases hXI61_core hFcomm hFnil with ⟨p, hp, hFp⟩
    letI : Fact (Nat.Prime p) := ⟨hp⟩
    letI : Nontrivial F :=
      (Subgroup.nontrivial_iff_ne_bot F).mpr hFrob.kernel_ne_bot
    rcases (hFp.nontrivial_iff_card.mp inferInstance) with ⟨f, hf, hFpow⟩
    exact ⟨p, f, hp, hf, hFcard.symm.trans hFpow⟩
  have hXI91_noncommutativeKernel_not_zGroupComplement_core :
      ∀ p : ℕ, Nat.Prime p →
        ¬ IsMulCommutative F → IsPGroup p F →
        IsZGroup
          (MulAction.stabilizer (MulAction.stabilizer G a) b') → p = 2 := by
    intro p hp hFnoncomm hFp hDZ
    exact
      huppert_XI_9_1_noncommutativeKernel_zGroupComplement
        n hdegree htwo_transitive hat_most_two_fixed_points hno_regular_normal
        a b hab F hFrob p hp hFnoncomm hFp hDZ
  have hFcomm_of_even_twoPointStabilizerCard :
      Even (Nat.card
        (MulAction.stabilizer (MulAction.stabilizer G a) b')) →
      IsMulCommutative F := by
    intro hDcardEven
    have htwoD :
        2 ∣ Nat.card
          (MulAction.stabilizer (MulAction.stabilizer G a) b') :=
      even_iff_two_dvd.mp hDcardEven
    obtain ⟨t, htorder⟩ :=
      exists_prime_orderOf_dvd_card'
        (G := MulAction.stabilizer (MulAction.stabilizer G a) b') 2 htwoD
    have htne : t ≠ 1 := by
      intro ht
      subst t
      simp at htorder
    have htsq : t ^ 2 = 1 := by
      rw [← htorder]
      exact pow_orderOf_eq_one t
    have htsq_stabilizer :
        (t : MulAction.stabilizer G a) ^ 2 = 1 := by
      simpa using congrArg Subtype.val htsq
    letI : F.Normal := hFrob.normal
    let phi : MulAut F :=
      MulAut.conjNormal (H := F) (t : MulAction.stabilizer G a)
    have hphi_sq : phi ^ 2 = 1 := by
      change (MulAut.conjNormal (H := F)
        (t : MulAction.stabilizer G a)) ^ 2 = 1
      rw [← map_pow, htsq_stabilizer, map_one]
    have hphi_involutive : Function.Involutive phi := by
      intro x
      have hx := congrArg (fun psi : MulAut F => psi x) hphi_sq
      simpa [pow_two] using hx
    have hphi_fixedPointFree : MonoidHom.FixedPointFree phi := by
      intro x hx
      have hconj :
          (t : MulAction.stabilizer G a) *
                (x : MulAction.stabilizer G a) *
              (t : MulAction.stabilizer G a)⁻¹ =
            (x : MulAction.stabilizer G a) := by
        simpa [phi] using congrArg Subtype.val hx
      have hcomm :
          (t : MulAction.stabilizer G a) *
              (x : MulAction.stabilizer G a) =
            (x : MulAction.stabilizer G a) *
              (t : MulAction.stabilizer G a) := by
        calc
          (t : MulAction.stabilizer G a) *
                (x : MulAction.stabilizer G a) =
              ((t : MulAction.stabilizer G a) *
                  (x : MulAction.stabilizer G a) *
                (t : MulAction.stabilizer G a)⁻¹) *
                  (t : MulAction.stabilizer G a) := by
            simp [mul_assoc]
          _ = (x : MulAction.stabilizer G a) *
                (t : MulAction.stabilizer G a) := by rw [hconj]
      have hcent :=
        (lemma_3_1 F
          (MulAction.stabilizer (MulAction.stabilizer G a) b')
          hFrob.kernel_ne_bot hFrob.complement_ne_bot
          hFrob.normal hFrob.isComplement').mp hFrob t htne
      have hxcent :
          (x : MulAction.stabilizer G a) ∈
            elementCentralizerIn F (t : MulAction.stabilizer G a) :=
        ⟨x.property,
          Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm⟩
      rw [hcent] at hxcent
      exact Subtype.ext (Subgroup.mem_bot.mp hxcent)
    refine ⟨⟨fun x y => ?_⟩⟩
    exact (hphi_fixedPointFree.commute_all_of_involutive
      hphi_involutive x y).eq
  have hXI91_core :
      ∀ p : ℕ, Nat.Prime p →
        ¬ IsMulCommutative F → IsPGroup p F →
        p = 2 := by
    intro p hp hFcomm hFp
    by_contra hp2
    by_cases hdEven : Even d
    · have hDcardEven :
          Even (Nat.card
            (MulAction.stabilizer (MulAction.stabilizer G a) b')) := by
        rw [htwoPointStabilizerCard]
        exact hdEven
      exact hFcomm (hFcomm_of_even_twoPointStabilizerCard hDcardEven)
    · have hdOdd : Odd d := Nat.not_even_iff_odd.mp hdEven
      have hDcardOdd :
          Odd (Nat.card
            (MulAction.stabilizer (MulAction.stabilizer G a) b')) := by
        rw [htwoPointStabilizerCard]
        exact hdOdd
      have hDZ :
          IsZGroup
            (MulAction.stabilizer (MulAction.stabilizer G a) b') :=
        isZGroup_of_frobenius_complement_of_odd
          (K := F)
          (R := MulAction.stabilizer (MulAction.stabilizer G a) b')
          hFrob hDcardOdd
      exact hp2 (hXI91_noncommutativeKernel_not_zGroupComplement_core
        p hp hFcomm hFp hDZ)
  have hXI91 :
      ∀ p f : ℕ, Nat.Prime p → 0 < f → n = p ^ f →
        ¬ IsMulCommutative F → p = 2 := by
    intro p f hp hf hn hFcomm
    letI : Fact (Nat.Prime p) := ⟨hp⟩
    have hFp : IsPGroup p F := IsPGroup.iff_card.mpr ⟨f, hFcard.trans hn⟩
    exact hXI91_core p hp hFcomm hFp
  have hXI1115_core :
      ¬ IsMulCommutative F → IsPGroup 2 F →
        ∃ m : ℕ, 0 < m ∧ Nonempty (G ≃* SuzukiMatrixGroup m) := by
    intro hFnoncomm hF2
    exact
      huppert_XI_11_15_suzukiRecognition
        htwo_transitive hat_most_two_fixed_points hno_regular_normal
        a b hab F hFrob hFnoncomm hF2
  have hXI1115 :
      ∀ p f : ℕ, Nat.Prime p → 0 < f → n = p ^ f →
        ¬ IsMulCommutative F → p = 2 →
        ∃ m : ℕ, 0 < m ∧
          n = (2 ^ (2 * m + 1)) ^ 2 ∧
          Nonempty (G ≃* SuzukiMatrixGroup m) := by
    intro p f hp hf hn hFcomm hp2
    letI : Fact (Nat.Prime p) := ⟨hp⟩
    have hFp : IsPGroup p F := IsPGroup.iff_card.mpr ⟨f, hFcard.trans hn⟩
    have hF2 : IsPGroup 2 F := by simpa [hp2] using hFp
    rcases hXI1115_core hFcomm hF2 with ⟨m, hm, hmodel⟩
    have hdOdd : Odd d := by
      apply Nat.not_even_iff_odd.mp
      intro hdEven
      apply hFcomm
      apply hFcomm_of_even_twoPointStabilizerCard
      rwa [htwoPointStabilizerCard]
    have hmodelCard :
        Nat.card G = Nat.card (SuzukiMatrixGroup m) :=
      Nat.card_congr (Classical.choice hmodel).toEquiv
    have hcardEq :
        (n + 1) * n * d =
          ((2 ^ (2 * m + 1)) ^ 2 + 1) *
            (2 ^ (2 * m + 1)) ^ 2 *
              (2 ^ (2 * m + 1) - 1) := by
      calc
        (n + 1) * n * d = Nat.card G := horder.symm
        _ = Nat.card (SuzukiMatrixGroup m) := hmodelCard
        _ = _ := suzukiMatrixGroup_card_formula m hm
    have hnPower : n = 2 ^ f := by simpa [hp2] using hn
    have hnSuzuki : n = (2 ^ (2 * m + 1)) ^ 2 :=
      twoPower_eq_square_of_odd_order_factors
        n d (2 ^ (2 * m + 1)) f (2 * m + 1)
        hf (by omega) hnPower rfl hdOdd hcardEq
    exact ⟨m, hm, hnSuzuki, hmodel⟩
  by_cases hsharp : SharpTriple
  · rcases hXI21 hsharp with ⟨p, f, hp, hf, hn⟩
    rcases hXI26 p f hp hf hn hsharp with hpgl | hm
    · exact ⟨p, f, hp, hf, hn, Or.inl hpgl⟩
    · exact ⟨p, f, hp, hf, hn, Or.inr (Or.inr (Or.inl hm))⟩
  · by_cases hFab : IsMulCommutative F
    · rcases hXI68 hsharp hFab with ⟨p, f, hp, hf, hn, hpodd, hpsl⟩
      exact ⟨p, f, hp, hf, hn, Or.inr (Or.inl ⟨hpodd, hpsl⟩)⟩
    · rcases hXI61 hFab with ⟨p, f, hp, hf, hn⟩
      have hp2 : p = 2 := hXI91 p f hp hf hn hFab
      exact ⟨p, f, hp, hf, hn,
        Or.inr (Or.inr (Or.inr
          ⟨hp2, hXI1115 p f hp hf hn hFab hp2⟩))⟩

end External
end CFSG.BenderSuzuki
