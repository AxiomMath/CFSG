module

import Mathlib.GroupTheory.FixedPointFree
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.CoprimeAction
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.CoprimeHall
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.lemma_5

namespace CFSG
end CFSG
open CFSG

/-!
# Higman Lemma 6 and its Neumann input
-/

namespace CFSG.BenderSuzuki
namespace External
namespace Higman

open scoped TensorProduct
open scoped commutatorElement
open scoped IsMulCommutative

open PFAppendixIII

universe u v w

private def neumannKappa {Q : Type u} [Group Q] (x y : Q) : Q :=
  x⁻¹ * y⁻¹ * x * y

private theorem neumannKappa_mul_left
    {Q : Type u} [Group Q] (x y z : Q) :
    neumannKappa (x * y) z =
      y⁻¹ * neumannKappa x z * y * neumannKappa y z := by
  simp [neumannKappa]
  group

private theorem neumannKappa_balanced_of_commutes
    {Q : Type u} [Group Q] (phi : MulAut Q)
    (hcomm : ∀ q : Q, Commute q (phi q)) (x y : Q) :
    neumannKappa (phi x) y = neumannKappa x (phi y) := by
  have hp := (hcomm (x * y⁻¹)).eq
  simp only [map_mul, map_inv] at hp
  have hp' := congrArg
    (fun t : Q => (phi x)⁻¹ * x⁻¹ * t * y * phi y) hp
  group at hp'
  have hba_inv : Commute (phi x) x⁻¹ :=
    Commute.inv_right_iff.mpr (hcomm x).symm
  have hp'' :
      (phi x)⁻¹ * y⁻¹ * phi x * (phi y)⁻¹ * y =
        x⁻¹ * (phi y)⁻¹ * x := by
    simpa [hba_inv.inv_mul_cancel] using hp'
  calc
    neumannKappa (phi x) y =
        ((phi x)⁻¹ * y⁻¹ * phi x * (phi y)⁻¹ * y) * phi y := by
      simp [neumannKappa, mul_assoc, (hcomm y).symm.inv_mul_cancel]
    _ = (x⁻¹ * (phi y)⁻¹ * x) * phi y :=
      congrArg (fun t : Q => t * phi y) hp''
    _ = neumannKappa x (phi y) := by
      simp [neumannKappa, mul_assoc]

private theorem neumannKappa_conj_eq_of_balanced
    {Q : Type u} [Group Q] (phi : MulAut Q)
    (hbal : ∀ x y : Q,
      neumannKappa (phi x) y = neumannKappa x (phi y))
    (x z y : Q) :
    (phi y)⁻¹ * neumannKappa x (phi z) * phi y =
      y⁻¹ * neumannKappa x (phi z) * y := by
  have h := hbal (x * y) z
  simp only [map_mul, neumannKappa_mul_left] at h
  rw [hbal x z, hbal y z] at h
  exact mul_right_cancel h

private theorem neumannKappa_delta_commute_of_conj_eq
    {Q : Type u} [Group Q] (phi : MulAut Q)
    (hconj : ∀ x z y : Q,
      (phi y)⁻¹ * neumannKappa x (phi z) * phi y =
        y⁻¹ * neumannKappa x (phi z) * y)
    (x z y : Q) :
    Commute (neumannKappa x (phi z)) (phi y * y⁻¹) := by
  rw [commute_iff_eq]
  have h := congrArg (fun t : Q => phi y * t * y⁻¹) (hconj x z y)
  group at h
  simpa [mul_assoc] using h

/-- The irreducible Neumann order-three core, retaining the exact-order and
fixed-point-free hypotheses while exposing the derived period-three norm
identity used by the group-word argument. -/
private theorem neumann_order_three_product_identity_class_le_two_core
    {Q : Type u} [Group Q] [Finite Q]
    (phi : MulAut Q)
    (_hphi_order : orderOf phi = 3)
    (hphi_fixedPointFree : ∀ x : Q, phi x = x → x = 1)
    (hphi_period : (fun q : Q => phi q)^[3] = id)
    (hphi_product : ∀ q : Q, q * phi q * phi (phi q) = 1) :
    higmanLowerCentralSeries Q 2 = ⊥ := by
  have hthird (q : Q) : phi (phi (phi q)) = q := by
    have h := congrFun hphi_period q
    simpa [Function.iterate_succ_apply] using h
  have hcomm (q : Q) : Commute q (phi q) := by
    have hq := hphi_product q
    have hqq := hphi_product (q * phi q)
    simp only [map_mul] at hqq
    rw [hthird] at hqq
    have hc : phi (phi q) = (q * phi q)⁻¹ :=
      eq_inv_of_mul_eq_one_right hq
    rw [hc] at hqq
    group at hqq
    rw [commute_iff_eq]
    have hconj : q * phi q * q⁻¹ = phi q := by
      apply mul_inv_eq_one.mp
      simpa [mul_assoc] using hqq
    exact mul_inv_eq_iff_eq_mul.mp hconj
  have hbal : ∀ x y : Q,
      neumannKappa (phi x) y = neumannKappa x (phi y) :=
    neumannKappa_balanced_of_commutes phi hcomm
  have hconj : ∀ x z y : Q,
      (phi y)⁻¹ * neumannKappa x (phi z) * phi y =
        y⁻¹ * neumannKappa x (phi z) * y :=
    neumannKappa_conj_eq_of_balanced phi hbal
  have hdelta : ∀ x z y : Q,
      Commute (neumannKappa x (phi z)) (phi y * y⁻¹) :=
    neumannKappa_delta_commute_of_conj_eq phi hconj
  have hFPF : MonoidHom.FixedPointFree (fun q : Q => phi q) := by
    intro q hq
    exact hphi_fixedPointFree q hq
  have hsurj :
      Function.Surjective
        (MonoidHom.commutatorMap (fun q : Q => phi q)) :=
    MonoidHom.FixedPointFree.commutatorMap_surjective hFPF
  have hkappa_central (x w g : Q) :
      Commute (neumannKappa x w) g := by
    obtain ⟨y, hy⟩ := hsurj g⁻¹
    have hy' : phi y * y⁻¹ = g := by
      have hi := congrArg (fun t : Q => t⁻¹) hy
      simpa [MonoidHom.commutatorMap_apply, div_eq_mul_inv] using hi
    have h := hdelta x (phi.symm w) y
    simpa [hy'] using h
  have hcommutator_central (x y g : Q) : Commute ⁅x, y⁆ g := by
    have h := hkappa_central x⁻¹ y⁻¹ g
    simpa [neumannKappa, commutatorElement_def] using h
  change (⊤ : Subgroup Q).lowerCentralSeries (1 + 1) = ⊥
  rw [Subgroup.lowerCentralSeries_succ,
    Subgroup.top_lowerCentralSeries_one]
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  rw [commutator_eq_closure, Subgroup.closure_le]
  rintro c ⟨x, y, rfl⟩
  change ∀ g : Q, g ∈ (⊤ : Subgroup Q) →
    g * ⁅x, y⁆ = ⁅x, y⁆ * g
  intro g hg
  exact (hcommutator_central x y g).symm.eq
/-- The theorem of B. H. Neumann used in Higman Lemma 6: a finite group with
a fixed-point-free automorphism of order three has nilpotency class at most
two. -/
public theorem neumann_order_three_fixedPointFree_class_le_two
    {Q : Type u} [Group Q] [Finite Q]
    (phi : MulAut Q)
    (hphi_order : orderOf phi = 3)
    (hphi_fixedPointFree : ∀ x : Q, phi x = x → x = 1) :
    higmanLowerCentralSeries Q 2 = ⊥ := by
  classical
  have hFPF : MonoidHom.FixedPointFree (fun q : Q => phi q) := by
    intro q hq
    exact hphi_fixedPointFree q hq
  have hpow_apply : ∀ k q, (phi ^ k) q = (fun q : Q => phi q)^[k] q := by
    intro k
    induction k with
    | zero => intro q; simp
    | succ k ih =>
        intro q
        simp [pow_succ, Function.iterate_succ, ih]
  have hphi_period : (fun q : Q => phi q)^[3] = id := by
    ext q
    have hpow : (phi ^ 3 : MulAut Q) = 1 := by
      rw [← hphi_order]
      exact pow_orderOf_eq_one phi
    have hq := congrArg (fun g : MulAut Q => g q) hpow
    change (phi ^ 3) q = q at hq
    rw [hpow_apply] at hq
    simpa using hq
  have hphi_product (q : Q) : q * phi q * phi (phi q) = 1 := by
    have hnorm := MonoidHom.FixedPointFree.prod_pow_eq_one hFPF hphi_period q
    simpa [Function.iterate_succ_apply, mul_assoc] using hnorm
  exact neumann_order_three_product_identity_class_le_two_core
    phi hphi_order hphi_fixedPointFree hphi_period hphi_product

private theorem lemma6_commutator_one_one_le_three
    {H : Type u} [Group H] :
    ⁅higmanLowerCentralSeries H 1, higmanLowerCentralSeries H 1⁆ ≤
      higmanLowerCentralSeries H 3 := by
  let q : H →* H ⧸ higmanLowerCentralSeries H 3 :=
    QuotientGroup.mk' (higmanLowerCentralSeries H 3)
  have hmap3 : (higmanLowerCentralSeries H 3).map q = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    change higmanLowerCentralSeries H 3 ≤
      (QuotientGroup.mk' (higmanLowerCentralSeries H 3)).ker
    rw [QuotientGroup.ker_mk']
  have hrotate1 :
      ⁅⁅(higmanLowerCentralSeries H 0).map q,
          (higmanLowerCentralSeries H 1).map q⁆,
        (higmanLowerCentralSeries H 0).map q⁆ = ⊥ := by
    rw [← Subgroup.map_commutator, ← Subgroup.map_commutator]
    rw [Subgroup.commutator_comm (higmanLowerCentralSeries H 0)
      (higmanLowerCentralSeries H 1)]
    change (higmanLowerCentralSeries H 3).map q = ⊥
    exact hmap3
  have hrotate2 :
      ⁅⁅(higmanLowerCentralSeries H 1).map q,
          (higmanLowerCentralSeries H 0).map q⁆,
        (higmanLowerCentralSeries H 0).map q⁆ = ⊥ := by
    rw [← Subgroup.map_commutator, ← Subgroup.map_commutator]
    change (higmanLowerCentralSeries H 3).map q = ⊥
    exact hmap3
  have hthree := Subgroup.commutator_commutator_eq_bot_of_rotate
    (H₁ := (higmanLowerCentralSeries H 0).map q)
    (H₂ := (higmanLowerCentralSeries H 0).map q)
    (H₃ := (higmanLowerCentralSeries H 1).map q)
    hrotate1 hrotate2
  rw [← Subgroup.map_commutator, ← Subgroup.map_commutator] at hthree
  change (⁅higmanLowerCentralSeries H 1, higmanLowerCentralSeries H 1⁆).map q = ⊥ at hthree
  have hle := (Subgroup.map_eq_bot_iff
    ⁅higmanLowerCentralSeries H 1, higmanLowerCentralSeries H 1⁆).mp hthree
  change ⁅higmanLowerCentralSeries H 1, higmanLowerCentralSeries H 1⁆ ≤ q.ker at hle
  simpa only [q, QuotientGroup.ker_mk'] using hle

private theorem lemma6_commutator_sq_eq_one_of_square_commutes
    {G : Type*} [Group G] (x y : G)
    (hc : Commute ⁅x, y⁆ x)
    (hx2 : Commute (x ^ 2) y) :
    ⁅x, y⁆ ^ 2 = 1 := by
  let c : G := ⁅x, y⁆
  have hxy : x * y = c * y * x := by
    dsimp [c]
    simp only [commutatorElement_def]
    group
  have hcalc : x ^ 2 * y = c ^ 2 * (y * x ^ 2) := by
    calc
      x ^ 2 * y = x * (x * y) := by simp [pow_two, mul_assoc]
      _ = x * (c * y * x) := by rw [hxy]
      _ = (x * c) * (y * x) := by simp only [mul_assoc]
      _ = (c * x) * (y * x) := by rw [hc.symm.eq]
      _ = c * (x * y) * x := by simp only [mul_assoc]
      _ = c * (c * y * x) * x := by rw [hxy]
      _ = c ^ 2 * (y * x ^ 2) := by simp [pow_two, mul_assoc]
  have hcancel : (1 : G) * (y * x ^ 2) = c ^ 2 * (y * x ^ 2) := by
    calc
      (1 : G) * (y * x ^ 2) = y * x ^ 2 := one_mul _
      _ = x ^ 2 * y := hx2.eq.symm
      _ = c ^ 2 * (y * x ^ 2) := hcalc
  exact (mul_right_cancel hcancel).symm

public theorem lemma6_squares_lowerCentralSeries_succ
    {H : Type*} [Group H] (i : ℕ)
    (hsq : squaresSubgroup (higmanLowerCentralSeries H i) ≤
      (higmanLowerCentralSeries H (i + 1)).subgroupOf (higmanLowerCentralSeries H i)) :
    squaresSubgroup (higmanLowerCentralSeries H (i + 1)) ≤
      (higmanLowerCentralSeries H (i + 2)).subgroupOf
        (higmanLowerCentralSeries H (i + 1)) := by
  let q : H →* H ⧸ higmanLowerCentralSeries H (i + 2) :=
    QuotientGroup.mk' (higmanLowerCentralSeries H (i + 2))
  have hcentral (z : H) (hz : z ∈ higmanLowerCentralSeries H (i + 1))
      (x : H) : Commute (q z) (q x) := by
    rw [← commutatorElement_eq_one_iff_commute, ← map_commutatorElement]
    apply (QuotientGroup.eq_one_iff _).2
    change ⁅z, x⁆ ∈
      (⊤ : Subgroup H).lowerCentralSeries ((i + 1) + 1)
    rw [Subgroup.lowerCentralSeries_succ]
    exact Subgroup.subset_closure ⟨z, hz, x, trivial, rfl⟩
  rw [squaresSubgroup, Subgroup.closure_le]
  rintro _ ⟨c, rfl⟩
  change (c : H) ^ 2 ∈ higmanLowerCentralSeries H (i + 2)
  apply (QuotientGroup.eq_one_iff _).1
  have hc : (c : H) ∈ higmanLowerCentralSeries H (i + 1) := c.property
  change (c : H) ∈ Subgroup.closure
    {z | ∃ a ∈ higmanLowerCentralSeries H i, ∃ x ∈ (⊤ : Subgroup H),
      a * x * a⁻¹ * x⁻¹ = z} at hc
  have hcprop : q (c : H) ^ 2 = 1 := by
    refine Subgroup.closure_induction
      (p := fun z hz => q z ^ 2 = 1) ?_ ?_ ?_ ?_ hc
    · rintro z ⟨a, ha, x, _hx, rfl⟩
      let a' : higmanLowerCentralSeries H i := ⟨a, ha⟩
      have ha_sq_sub :
          a' ^ 2 ∈
            (higmanLowerCentralSeries H (i + 1)).subgroupOf
              (higmanLowerCentralSeries H i) :=
        hsq (Subgroup.subset_closure ⟨a', rfl⟩)
      have ha_sq : a ^ 2 ∈ higmanLowerCentralSeries H (i + 1) := ha_sq_sub
      have hcomm_mem :
          ⁅a, x⁆ ∈ higmanLowerCentralSeries H (i + 1) := by
        change ⁅a, x⁆ ∈ (⊤ : Subgroup H).lowerCentralSeries (i + 1)
        rw [Subgroup.lowerCentralSeries_succ]
        exact Subgroup.subset_closure ⟨a, ha, x, trivial, rfl⟩
      have hcommcentral : Commute ⁅q a, q x⁆ (q a) := by
        simpa only [map_commutatorElement] using
          hcentral ⁅a, x⁆ hcomm_mem a
      have ha2central : Commute ((q a) ^ 2) (q x) := by
        simpa only [map_pow] using hcentral (a ^ 2) ha_sq x
      simpa only [← commutatorElement_def, map_commutatorElement] using
        lemma6_commutator_sq_eq_one_of_square_commutes
          (q a) (q x) hcommcentral ha2central
    · simp only [map_one, one_pow]
    · intro a b ha hb iha ihb
      rw [map_mul, (hcentral a ha b).mul_pow, iha, ihb, one_mul]
    · intro a ha iha
      rw [map_inv, inv_pow, iha, inv_one]
  change q ((c : H) ^ 2) = 1
  simpa only [map_pow] using hcprop

private def lemma6_nextBracketLift
    {H : Type u} [Group H]
    (x : higmanLowerCentralSeries H 0) (c : higmanLowerCentralSeries H 1) :
    higmanLowerCentralSeries H 2 :=
  ⟨⁅(x : H), (c : H)⁆, by
    have hcx : ⁅(c : H), (x : H)⁆ ∈ higmanLowerCentralSeries H 2 := by
      change ⁅(c : H), (x : H)⁆ ∈
        (⊤ : Subgroup H).lowerCentralSeries (1 + 1)
      rw [Subgroup.lowerCentralSeries_succ]
      exact Subgroup.subset_closure
        ⟨(c : H), c.property, (x : H), trivial, rfl⟩
    have hinv := (higmanLowerCentralSeries H 2).inv_mem hcx
    simpa only [commutatorElement_inv] using hinv⟩

private def lemma6_deeperBracketLift
    {H : Type u} [Group H]
    (x : higmanLowerCentralSeries H 0) (d : higmanLowerCentralSeries H 2) :
    higmanLowerCentralSeries H 2 :=
  ⟨⁅(x : H), (d : H)⁆, by
    apply (⊤ : Subgroup H).lowerCentralSeries_antitone (by omega : 2 ≤ 3)
    have hdx : ⁅(d : H), (x : H)⁆ ∈ higmanLowerCentralSeries H 3 := by
      change ⁅(d : H), (x : H)⁆ ∈
        (⊤ : Subgroup H).lowerCentralSeries (2 + 1)
      rw [Subgroup.lowerCentralSeries_succ]
      exact Subgroup.subset_closure
        ⟨(d : H), d.property, (x : H), trivial, rfl⟩
    have hinv := (higmanLowerCentralSeries H 3).inv_mem hdx
    simpa only [commutatorElement_inv] using hinv⟩

private theorem lemma6_deeperBracketLift_mem_kernel
    {H : Type u} [Group H]
    (x : higmanLowerCentralSeries H 0) (d : higmanLowerCentralSeries H 2) :
    lemma6_deeperBracketLift x d ∈ lowerCentralFactorKernel H 2 := by
  apply (show
    (higmanLowerCentralSeries H 3).subgroupOf (higmanLowerCentralSeries H 2) ≤
      lowerCentralFactorKernel H 2 by
    rw [lowerCentralFactorKernel]
    exact le_sup_right)
  change ⁅(x : H), (d : H)⁆ ∈ higmanLowerCentralSeries H 3
  have hdx : ⁅(d : H), (x : H)⁆ ∈ higmanLowerCentralSeries H 3 := by
    change ⁅(d : H), (x : H)⁆ ∈
      (⊤ : Subgroup H).lowerCentralSeries (2 + 1)
    rw [Subgroup.lowerCentralSeries_succ]
    exact Subgroup.subset_closure
      ⟨(d : H), d.property, (x : H), trivial, rfl⟩
  have hinv := (higmanLowerCentralSeries H 3).inv_mem hdx
  simpa only [commutatorElement_inv] using hinv

private theorem lemma6_quotient_conj_eq
    {H : Type u} [Group H]
    (x : higmanLowerCentralSeries H 0) (d : higmanLowerCentralSeries H 2) :
    QuotientGroup.mk' (lowerCentralFactorKernel H 2)
        (⟨(x : H) * (d : H) * (x : H)⁻¹,
          (inferInstance : (higmanLowerCentralSeries H 2).Normal).conj_mem
            (d : H) d.property (x : H)⟩ : higmanLowerCentralSeries H 2) =
      QuotientGroup.mk' (lowerCentralFactorKernel H 2) d := by
  let q := QuotientGroup.mk' (lowerCentralFactorKernel H 2)
  have hfactor :
      (⟨(x : H) * (d : H) * (x : H)⁻¹,
        (inferInstance : (higmanLowerCentralSeries H 2).Normal).conj_mem
          (d : H) d.property (x : H)⟩ : higmanLowerCentralSeries H 2) =
        lemma6_deeperBracketLift x d * d := by
    apply Subtype.ext
    change (x : H) * (d : H) * (x : H)⁻¹ =
      ((x : H) * (d : H) * (x : H)⁻¹ * (d : H)⁻¹) * (d : H)
    group
  rw [hfactor, map_mul]
  have hkernel : q (lemma6_deeperBracketLift x d) = 1 := by
    apply (QuotientGroup.eq_one_iff _).2
    exact lemma6_deeperBracketLift_mem_kernel x d
  rw [hkernel, one_mul]

private def lemma6_bracketRightHom
    {H : Type u} [Group H] (x : higmanLowerCentralSeries H 0) :
    higmanLowerCentralSeries H 1 →* LowerCentralFactor H 2 where
  toFun c :=
    QuotientGroup.mk' (lowerCentralFactorKernel H 2)
      (lemma6_nextBracketLift x c)
  map_one' := by
    have hone : lemma6_nextBracketLift x 1 = 1 := by
      apply Subtype.ext
      simp [lemma6_nextBracketLift]
    rw [hone, map_one]
  map_mul' c d := by
    have hfactor :
        lemma6_nextBracketLift x (c * d) =
          lemma6_nextBracketLift x c *
            (⟨(c : H) * (lemma6_nextBracketLift x d : H) * (c : H)⁻¹,
              (inferInstance : (higmanLowerCentralSeries H 2).Normal).conj_mem
                (lemma6_nextBracketLift x d : H)
                (lemma6_nextBracketLift x d).property (c : H)⟩ :
              higmanLowerCentralSeries H 2) := by
      apply Subtype.ext
      change ⁅(x : H), (c : H) * (d : H)⁆ =
        ⁅(x : H), (c : H)⁆ *
          ((c : H) * ⁅(x : H), (d : H)⁆ * (c : H)⁻¹)
      simp only [commutatorElement_def]
      group
    change QuotientGroup.mk' (lowerCentralFactorKernel H 2)
        (lemma6_nextBracketLift x (c * d)) =
      QuotientGroup.mk' (lowerCentralFactorKernel H 2)
          (lemma6_nextBracketLift x c) *
        QuotientGroup.mk' (lowerCentralFactorKernel H 2)
          (lemma6_nextBracketLift x d)
    rw [hfactor, map_mul]
    let c0 : higmanLowerCentralSeries H 0 :=
      ⟨(c : H), (⊤ : Subgroup H).lowerCentralSeries_antitone (by omega : 0 ≤ 1) c.property⟩
    rw [lemma6_quotient_conj_eq c0 (lemma6_nextBracketLift x d)]

private theorem lemma6_bracketRightHom_kernel
    {H : Type u} [Group H] (x : higmanLowerCentralSeries H 0) :
    lowerCentralFactorKernel H 1 ≤ (lemma6_bracketRightHom x).ker := by
  rw [lowerCentralFactorKernel]
  apply sup_le
  · rw [squaresSubgroup, Subgroup.closure_le]
    rintro _ ⟨c, rfl⟩
    change lemma6_bracketRightHom x (c ^ 2) = 1
    rw [map_pow]
    exact lowerCentralFactor_sq_eq_one 2 _
  · intro d hd
    change QuotientGroup.mk' (lowerCentralFactorKernel H 2)
      (lemma6_nextBracketLift x d) = 1
    apply (QuotientGroup.eq_one_iff _).2
    let d' : higmanLowerCentralSeries H 2 := ⟨(d : H), hd⟩
    have heq : lemma6_nextBracketLift x d = lemma6_deeperBracketLift x d' := by
      apply Subtype.ext
      rfl
    rw [heq]
    exact lemma6_deeperBracketLift_mem_kernel x d'

private def lemma6_bracketRightFactorHom
    {H : Type u} [Group H] (x : higmanLowerCentralSeries H 0) :
    LowerCentralFactor H 1 →* LowerCentralFactor H 2 :=
  QuotientGroup.lift (lowerCentralFactorKernel H 1)
    (lemma6_bracketRightHom x) (lemma6_bracketRightHom_kernel x)


private def lemma6_bracketLeftHom
    {H : Type u} [Group H] :
    higmanLowerCentralSeries H 0 →*
      (LowerCentralFactor H 1 →* LowerCentralFactor H 2) where
  toFun x := lemma6_bracketRightFactorHom x
  map_one' := by
    apply MonoidHom.ext
    intro cq
    refine Quotient.inductionOn' cq ?_
    intro c
    change QuotientGroup.mk' (lowerCentralFactorKernel H 2)
      (lemma6_nextBracketLift 1 c) = 1
    have hone : lemma6_nextBracketLift 1 c = 1 := by
      apply Subtype.ext
      simp [lemma6_nextBracketLift]
    rw [hone, map_one]
  map_mul' x z := by
    apply MonoidHom.ext
    intro cq
    refine Quotient.inductionOn' cq ?_
    intro c
    have hfactor :
        lemma6_nextBracketLift (x * z) c =
          (⟨(x : H) * (lemma6_nextBracketLift z c : H) * (x : H)⁻¹,
            (inferInstance : (higmanLowerCentralSeries H 2).Normal).conj_mem
              (lemma6_nextBracketLift z c : H)
              (lemma6_nextBracketLift z c).property (x : H)⟩ :
            higmanLowerCentralSeries H 2) *
          lemma6_nextBracketLift x c := by
      apply Subtype.ext
      change ⁅(x : H) * (z : H), (c : H)⁆ =
        ((x : H) * ⁅(z : H), (c : H)⁆ * (x : H)⁻¹) *
          ⁅(x : H), (c : H)⁆
      simp only [commutatorElement_def]
      group
    change QuotientGroup.mk' (lowerCentralFactorKernel H 2)
        (lemma6_nextBracketLift (x * z) c) =
      QuotientGroup.mk' (lowerCentralFactorKernel H 2)
          (lemma6_nextBracketLift x c) *
        QuotientGroup.mk' (lowerCentralFactorKernel H 2)
          (lemma6_nextBracketLift z c)
    rw [hfactor, map_mul, lemma6_quotient_conj_eq]
    exact mul_comm _ _

private theorem lemma6_bracketLeftHom_kernel
    {H : Type u} [Group H] :
    lowerCentralFactorKernel H 0 ≤
      (lemma6_bracketLeftHom (H := H)).ker := by
  change
    (squaresSubgroup (higmanLowerCentralSeries H 0) ⊔
      (higmanLowerCentralSeries H 1).subgroupOf (higmanLowerCentralSeries H 0)) ≤ _
  apply sup_le
  · rw [squaresSubgroup, Subgroup.closure_le]
    rintro _ ⟨x, rfl⟩
    change lemma6_bracketLeftHom (H := H) (x ^ 2) = 1
    rw [map_pow]
    apply MonoidHom.ext
    intro c
    change (lemma6_bracketLeftHom (H := H) x c) ^ 2 = 1
    exact lowerCentralFactor_sq_eq_one 2 _
  · intro x hx
    change lemma6_bracketLeftHom (H := H) x = 1
    apply MonoidHom.ext
    intro cq
    refine Quotient.inductionOn' cq ?_
    intro c
    change QuotientGroup.mk' (lowerCentralFactorKernel H 2)
      (lemma6_nextBracketLift x c) = 1
    apply (QuotientGroup.eq_one_iff _).2
    apply (show
      (higmanLowerCentralSeries H 3).subgroupOf (higmanLowerCentralSeries H 2) ≤
        lowerCentralFactorKernel H 2 by
      rw [lowerCentralFactorKernel]
      exact le_sup_right)
    exact lemma6_commutator_one_one_le_three
      (Subgroup.commutator_mem_commutator hx c.property)

private def lemma6_bracketFactorHom
    {H : Type u} [Group H] :
    LowerCentralFactor H 0 →*
      (LowerCentralFactor H 1 →* LowerCentralFactor H 2) :=
  QuotientGroup.lift (lowerCentralFactorKernel H 0)
    (lemma6_bracketLeftHom (H := H))
    (lemma6_bracketLeftHom_kernel (H := H))


private noncomputable def lemma6_bracketFactorAddHom
    {H : Type u} [Group H] :
    Additive (LowerCentralFactor H 0) →+
      (Additive (LowerCentralFactor H 1) →ₗ[ZMod 2]
        Additive (LowerCentralFactor H 2)) where
  toFun x :=
    ((lemma6_bracketFactorHom x.toMul).toAdditive).toZModLinearMap 2
  map_zero' := by
    apply LinearMap.ext
    intro c
    apply Additive.toMul.injective
    exact MonoidHom.map_one₂ (lemma6_bracketFactorHom (H := H)) c.toMul
  map_add' x z := by
    apply LinearMap.ext
    intro c
    apply Additive.toMul.injective
    exact MonoidHom.map_mul₂ (lemma6_bracketFactorHom (H := H))
      x.toMul z.toMul c.toMul

private noncomputable def lemma6_lowerCentralIteratedBracket
    {H : Type u} [Group H] :
    Additive (LowerCentralFactor H 0) →ₗ[ZMod 2]
      Additive (LowerCentralFactor H 1) →ₗ[ZMod 2]
        Additive (LowerCentralFactor H 2) :=
  (lemma6_bracketFactorAddHom (H := H)).toZModLinearMap 2

private theorem lemma6_lowerCentralIteratedBracket_mk_mk
    {H : Type u} [Group H]
    (x : higmanLowerCentralSeries H 0) (c : higmanLowerCentralSeries H 1) :
    lemma6_lowerCentralIteratedBracket
        (Additive.ofMul
          (QuotientGroup.mk' (lowerCentralFactorKernel H 0) x))
        (Additive.ofMul
          (QuotientGroup.mk' (lowerCentralFactorKernel H 1) c)) =
      Additive.ofMul
        (QuotientGroup.mk' (lowerCentralFactorKernel H 2)
          (lemma6_nextBracketLift x c)) :=
  rfl

private theorem lemma6_nextBracketLift_equivariant
    {H : Type u} [Group H] (theta : MulAut H)
    (x : higmanLowerCentralSeries H 0) (c : higmanLowerCentralSeries H 1) :
    lowerCentralSeriesMulAut theta 2 (lemma6_nextBracketLift x c) =
      lemma6_nextBracketLift
        (lowerCentralSeriesMulAut theta 0 x)
        (lowerCentralSeriesMulAut theta 1 c) := by
  apply Subtype.ext
  rw [BenderSuzuki.External.Higman.lowerCentralSeriesMulAut_apply]
  change theta ⁅(x : H), (c : H)⁆ = ⁅theta (x : H), theta (c : H)⁆
  exact map_commutatorElement theta (x : H) (c : H)

private theorem lemma6_lowerCentralIteratedBracket_equivariant
    {H : Type u} [Group H] (theta : MulAut H)
    (v : Additive (LowerCentralFactor H 0))
    (w : Additive (LowerCentralFactor H 1)) :
    lemma6_lowerCentralIteratedBracket
        (lowerCentralFactorLinearAut theta 0 v)
        (lowerCentralFactorLinearAut theta 1 w) =
      lowerCentralFactorLinearAut theta 2
        (lemma6_lowerCentralIteratedBracket v w) := by
  obtain ⟨x, hx⟩ :=
    QuotientGroup.mk'_surjective (lowerCentralFactorKernel H 0) v.toMul
  obtain ⟨c, hc⟩ :=
    QuotientGroup.mk'_surjective (lowerCentralFactorKernel H 1) w.toMul
  have hv :
      v = Additive.ofMul
        (QuotientGroup.mk' (lowerCentralFactorKernel H 0) x) := by
    apply Additive.toMul.injective
    exact hx.symm
  have hw :
      w = Additive.ofMul
        (QuotientGroup.mk' (lowerCentralFactorKernel H 1) c) := by
    apply Additive.toMul.injective
    exact hc.symm
  rw [hv, hw, lowerCentralFactorLinearAut_ofMul_mk,
    lowerCentralFactorLinearAut_ofMul_mk,
    lemma6_lowerCentralIteratedBracket_mk_mk,
    lemma6_lowerCentralIteratedBracket_mk_mk,
    lowerCentralFactorLinearAut_ofMul_mk]
  apply Additive.ofMul.injective
  exact congrArg (QuotientGroup.mk' (lowerCentralFactorKernel H 2))
    (lemma6_nextBracketLift_equivariant theta x c).symm

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
private theorem lemma6_lowerCentralIteratedBracket_class_mem_span
    {H : Type u} [Group H] (d : higmanLowerCentralSeries H 2) :
    Additive.ofMul
        (QuotientGroup.mk' (lowerCentralFactorKernel H 2) d) ∈
      Submodule.span (ZMod 2)
        (Set.range fun p :
          Additive (LowerCentralFactor H 0) ×
            Additive (LowerCentralFactor H 1) =>
          lemma6_lowerCentralIteratedBracket p.1 p.2) := by
  let W := Submodule.span (ZMod 2)
    (Set.range fun p :
      Additive (LowerCentralFactor H 0) ×
        Additive (LowerCentralFactor H 1) =>
      lemma6_lowerCentralIteratedBracket p.1 p.2)
  let q := QuotientGroup.mk' (lowerCentralFactorKernel H 2)
  change Additive.ofMul (q d) ∈ W
  have hd : (d : H) ∈ higmanLowerCentralSeries H 2 := d.property
  change (d : H) ∈ Subgroup.closure
    {z | ∃ c ∈ higmanLowerCentralSeries H 1, ∃ x ∈ (⊤ : Subgroup H),
      c * x * c⁻¹ * x⁻¹ = z} at hd
  refine Subgroup.closure_induction (p := fun z hz =>
    Additive.ofMul (q (⟨z, hz⟩ : higmanLowerCentralSeries H 2)) ∈ W)
    ?_ ?_ ?_ ?_ hd
  · rintro z ⟨c, hc, x, _hx, rfl⟩
    let c' : higmanLowerCentralSeries H 1 := ⟨c, hc⟩
    let x' : higmanLowerCentralSeries H 0 := ⟨x, trivial⟩
    have hvalue :
        lemma6_lowerCentralIteratedBracket
            (Additive.ofMul
              (QuotientGroup.mk' (lowerCentralFactorKernel H 0) x'))
            (Additive.ofMul
              (QuotientGroup.mk' (lowerCentralFactorKernel H 1) c')) ∈ W := by
      apply Submodule.subset_span
      exact ⟨(Additive.ofMul
          (QuotientGroup.mk' (lowerCentralFactorKernel H 0) x'),
        Additive.ofMul
          (QuotientGroup.mk' (lowerCentralFactorKernel H 1) c')), rfl⟩
    rw [lemma6_lowerCentralIteratedBracket_mk_mk] at hvalue
    change Additive.ofMul (q (lemma6_nextBracketLift x' c')) ∈ W at hvalue
    convert hvalue using 1
    apply Additive.ofMul.injective
    calc
      q (⟨c * x * c⁻¹ * x⁻¹, by
          change c * x * c⁻¹ * x⁻¹ ∈
            (⊤ : Subgroup H).lowerCentralSeries (1 + 1)
          rw [Subgroup.lowerCentralSeries_succ]
          exact Subgroup.subset_closure ⟨c, hc, x, trivial, rfl⟩⟩ :
          higmanLowerCentralSeries H 2) =
          q ((lemma6_nextBracketLift x' c')⁻¹) := by
            apply congrArg q
            apply Subtype.ext
            exact (commutatorElement_inv (x : H) (c : H)).symm
      _ = (q (lemma6_nextBracketLift x' c'))⁻¹ := map_inv _ _
      _ = q (lemma6_nextBracketLift x' c') :=
        inv_eq_of_mul_eq_one_right (by
          simpa [pow_two] using lowerCentralFactor_sq_eq_one 2
            (q (lemma6_nextBracketLift x' c')))
  · change Additive.ofMul (q (1 : higmanLowerCentralSeries H 2)) ∈ W
    rw [map_one, ofMul_one]
    exact W.zero_mem
  · intro a b ha hb iha ihb
    change Additive.ofMul
      (q ((⟨a, ha⟩ : higmanLowerCentralSeries H 2) * ⟨b, hb⟩)) ∈ W
    rw [map_mul, ofMul_mul]
    exact W.add_mem iha ihb
  · intro a ha iha
    change Additive.ofMul
      (q (⟨a, ha⟩ : higmanLowerCentralSeries H 2)⁻¹) ∈ W
    rw [map_inv, ofMul_inv]
    exact W.neg_mem iha

private theorem lemma6_lowerCentralIteratedBracket_span
    {H : Type u} [Group H] :
    Submodule.span (ZMod 2)
        (Set.range fun p :
          Additive (LowerCentralFactor H 0) ×
            Additive (LowerCentralFactor H 1) =>
          lemma6_lowerCentralIteratedBracket p.1 p.2) = ⊤ := by
  apply top_unique
  intro z _hz
  obtain ⟨d, hd⟩ :=
    QuotientGroup.mk'_surjective (lowerCentralFactorKernel H 2) z.toMul
  have hz :
      z = Additive.ofMul
        (QuotientGroup.mk' (lowerCentralFactorKernel H 2) d) := by
    apply Additive.toMul.injective
    exact hd.symm
  rw [hz]
  exact lemma6_lowerCentralIteratedBracket_class_mem_span d


/-- The canonical iterated lower-central bracket needed in Higman Lemma 6.
Its values span L3 and it intertwines every automorphism induced from H. -/
private theorem lemma6_exists_lowerCentralIteratedBracket
    {H : Type u} [Group H] :
    ∃ bracket : Additive (LowerCentralFactor H 0) →ₗ[ZMod 2]
        Additive (LowerCentralFactor H 1) →ₗ[ZMod 2]
          Additive (LowerCentralFactor H 2),
      (∀ theta : MulAut H,
        ∀ x : Additive (LowerCentralFactor H 0),
        ∀ y : Additive (LowerCentralFactor H 1),
          bracket (lowerCentralFactorLinearAut theta 0 x)
              (lowerCentralFactorLinearAut theta 1 y) =
            lowerCentralFactorLinearAut theta 2 (bracket x y)) ∧
      Submodule.span (ZMod 2)
        (Set.range fun p : Additive (LowerCentralFactor H 0) ×
            Additive (LowerCentralFactor H 1) => bracket p.1 p.2) = ⊤ := by
  exact ⟨lemma6_lowerCentralIteratedBracket,
    lemma6_lowerCentralIteratedBracket_equivariant,
    lemma6_lowerCentralIteratedBracket_span⟩

/-- A faithful irreducible binary cyclic action of order 2^n - 1 has the
source dimension n. This is the finite-field step behind Higman's m = n. -/
private theorem lemma6_irreducible_card_of_order_core
    {V : Type u} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (T : V ≃ₗ[ZMod 2] V)
    (hV_irreducible :
      ∀ A : Submodule (ZMod 2) V,
        (∀ x : V, x ∈ A → T x ∈ A) → A = ⊥ ∨ A = ⊤)
    (n : ℕ) (hn : 2 ≤ n) (hT_order : orderOf T = 2 ^ n - 1) :
    Nat.card V = 2 ^ n := by
  exact BenderSuzuki.External.Higman.lemma5_irreducible_card_of_order
    T hV_irreducible n hn hT_order

/-- Abstract form of the first paragraph of Higman Lemma 6. The first bracket
shows that the action on L2 divides the action on L1. The iterated bracket and
irreducibility give the reverse divisibility once L2 and L3 are identified. -/
private theorem lemma6_action_order_sync_of_brackets
    {V : Type u} {W : Type v} {U : Type w}
    [AddCommGroup V] [AddCommGroup W] [AddCommGroup U]
    [Module (ZMod 2) V] [Module (ZMod 2) W] [Module (ZMod 2) U]
    [Finite V] [Finite W] [Finite U]
    (T : V ≃ₗ[ZMod 2] V) (S : W ≃ₗ[ZMod 2] W)
    (R : U ≃ₗ[ZMod 2] U)
    (hV_irreducible :
      ∀ A : Submodule (ZMod 2) V,
        (∀ x : V, x ∈ A → T x ∈ A) → A = ⊥ ∨ A = ⊤)
    (hW_transitive :
      ∀ x : W, x ≠ 0 → ∀ y : W, y ≠ 0 → ∃ k : ℕ, (S ^ k) x = y)
    (n : ℕ) (hn : 2 ≤ n) (hW_card : Nat.card W = 2 ^ n)
    (e : U ≃ₗ[ZMod 2] W) (he : ∀ x : U, e (R x) = S (e x))
    (B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] W)
    (hB_equivariant : ∀ x y : V, B (T x) (T y) = S (B x y))
    (hB_span : Submodule.span (ZMod 2)
      (Set.range fun p : V × V => B p.1 p.2) = ⊤)
    (C : V →ₗ[ZMod 2] W →ₗ[ZMod 2] U)
    (hC_equivariant : ∀ x : V, ∀ y : W, C (T x) (S y) = R (C x y))
    (hC_span : Submodule.span (ZMod 2)
      (Set.range fun p : V × W => C p.1 p.2) = ⊤) :
    orderOf T = 2 ^ n - 1 ∧
      orderOf S = 2 ^ n - 1 ∧
      orderOf R = 2 ^ n - 1 ∧
      Nat.card V = 2 ^ n ∧ Nat.card U = 2 ^ n := by
  have hS_order : orderOf S = 2 ^ n - 1 :=
    lemma4_transitive_linearAut_order S hW_transitive n hn hW_card
  have he_pow : ∀ k : ℕ, ∀ x : U, e ((R ^ k) x) = (S ^ k) (e x) := by
    intro k
    induction k with
    | zero =>
        intro x
        simp
    | succ k ih =>
        intro x
        simpa only [pow_succ, LinearEquiv.mul_apply] using
          (calc
            e ((R ^ k) (R x)) = (S ^ k) (e (R x)) := ih (R x)
            _ = (S ^ k) (S (e x)) := congrArg (fun y => (S ^ k) y) (he x))
  have hR_dvd_S : orderOf R ∣ orderOf S := by
    apply (orderOf_dvd_iff_pow_eq_one).2
    apply LinearEquiv.ext
    intro x
    apply e.injective
    rw [he_pow]
    simp
  have hS_dvd_R : orderOf S ∣ orderOf R := by
    apply (orderOf_dvd_iff_pow_eq_one).2
    apply LinearEquiv.ext
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← he_pow]
    simp
  have hR_order : orderOf R = orderOf S :=
    Nat.dvd_antisymm hR_dvd_S hS_dvd_R
  have hU_card : Nat.card U = 2 ^ n := by
    rw [Nat.card_congr e.toEquiv, hW_card]
  have hB_pow : ∀ k : ℕ, ∀ x y : V,
      B ((T ^ k) x) ((T ^ k) y) = (S ^ k) (B x y) := by
    intro k
    induction k with
    | zero =>
        intro x y
        simp
    | succ k ih =>
        intro x y
        simpa only [pow_succ, LinearEquiv.mul_apply] using
          (calc
            B ((T ^ k) (T x)) ((T ^ k) (T y)) =
                (S ^ k) (B (T x) (T y)) := ih (T x) (T y)
            _ = (S ^ k) (S (B x y)) :=
              congrArg (fun z => (S ^ k) z) (hB_equivariant x y))
  have hS_dvd_T : orderOf S ∣ orderOf T := by
    apply (orderOf_dvd_iff_pow_eq_one).2
    apply LinearEquiv.ext
    intro y
    have hfix : ∀ z : W,
        z ∈ Submodule.span (ZMod 2)
            (Set.range fun p : V × V => B p.1 p.2) →
          (S ^ orderOf T) z = z := by
      intro z hz
      refine Submodule.span_induction
        (p := fun z _ => (S ^ orderOf T) z = z) ?_ ?_ ?_ ?_ hz
      · intro z hz
        rcases hz with ⟨⟨x, y⟩, rfl⟩
        rw [← hB_pow]
        simp
      · simp
      · intro x y _ _ hx hy
        simp only [map_add, hx, hy]
      · intro a x _ hx
        simp only [map_smul, hx]
    simpa [hB_span] using hfix y (by rw [hB_span]; trivial)
  have hC_pow : ∀ k : ℕ, ∀ x : V, ∀ y : W,
      C ((T ^ k) x) ((S ^ k) y) = (R ^ k) (C x y) := by
    intro k
    induction k with
    | zero =>
        intro x y
        simp
    | succ k ih =>
        intro x y
        simpa only [pow_succ, LinearEquiv.mul_apply] using
          (calc
            C ((T ^ k) (T x)) ((S ^ k) (S y)) =
                (R ^ k) (C (T x) (S y)) := ih (T x) (S y)
            _ = (R ^ k) (R (C x y)) :=
              congrArg (fun z => (R ^ k) z) (hC_equivariant x y))
  let D : V →ₗ[ZMod 2] V :=
    (T ^ orderOf S).toLinearMap - LinearMap.id
  have hD_invariant : ∀ x : V, x ∈ D.range → T x ∈ D.range := by
    intro x hx
    obtain ⟨y, rfl⟩ := (LinearMap.mem_range).1 hx
    apply (LinearMap.mem_range).2
    refine ⟨T y, ?_⟩
    simp only [D, LinearMap.sub_apply, LinearMap.id_apply, map_sub]
    congr 1
    change ((T ^ orderOf S) * T) y = (T * (T ^ orderOf S)) y
    exact LinearEquiv.congr_fun (Commute.pow_self T (orderOf S)).eq y
  rcases hV_irreducible D.range hD_invariant with hD_bot | hD_top
  · have hD_zero : D = 0 := (LinearMap.range_eq_bot).mp hD_bot
    have hT_pow : T ^ orderOf S = 1 := by
      apply LinearEquiv.ext
      intro x
      have hx := LinearMap.congr_fun hD_zero x
      change (T ^ orderOf S) x - x = 0 at hx
      exact sub_eq_zero.mp hx
    have hT_dvd_S : orderOf T ∣ orderOf S :=
      (orderOf_dvd_iff_pow_eq_one).2 hT_pow
    have hT_order : orderOf T = orderOf S :=
      Nat.dvd_antisymm hT_dvd_S hS_dvd_T
    have hT_order_q : orderOf T = 2 ^ n - 1 := hT_order.trans hS_order
    have hV_card := lemma6_irreducible_card_of_order_core
      T hV_irreducible n hn hT_order_q
    exact ⟨hT_order_q, hS_order,
      hR_order.trans hS_order, hV_card, hU_card⟩
  · have hC_D_zero (x : V) (y : W) : C (D x) y = 0 := by
      have hpow := hC_pow (orderOf S) x y
      have hSpow : S ^ orderOf S = 1 := pow_orderOf_eq_one S
      have hRpow : R ^ orderOf S = 1 :=
        (orderOf_dvd_iff_pow_eq_one).mp hR_dvd_S
      simp [hSpow, hRpow] at hpow
      change C ((T ^ orderOf S) x - x) y = 0
      rw [map_sub, LinearMap.sub_apply, hpow, sub_self]
    have hC_zero (x : V) (y : W) : C x y = 0 := by
      obtain ⟨z, hz⟩ := (LinearMap.range_eq_top.mp hD_top) x
      rw [← hz]
      exact hC_D_zero z y
    have hspan_le_bot :
        Submodule.span (ZMod 2)
          (Set.range fun p : V × W => C p.1 p.2) ≤ ⊥ := by
      rw [Submodule.span_le]
      rintro z ⟨⟨x, y⟩, rfl⟩
      change C x y = 0
      exact hC_zero x y
    have htop_le_bot : (⊤ : Submodule (ZMod 2) U) ≤ ⊥ := by
      rw [← hC_span]
      exact hspan_le_bot
    have htop_eq_bot : (⊤ : Submodule (ZMod 2) U) = ⊥ :=
      le_antisymm htop_le_bot bot_le
    have hU_card_gt : 1 < Nat.card U := by
      rw [hU_card]
      exact one_lt_pow₀ (by norm_num : 1 < (2 : ℕ)) (by omega)
    let : Nontrivial U := Finite.one_lt_card_iff_nontrivial.mp hU_card_gt
    exact (top_ne_bot htop_eq_bot).elim

private theorem lemma6_lowerCentralFactorKernel_zero_le
    {H : Type u} [Group H]
    (hH_square : squaresSubgroup H ≤ higmanLowerCentralSeries H 1) :
    lowerCentralFactorKernel H 0 ≤
      (higmanLowerCentralSeries H 1).subgroupOf (higmanLowerCentralSeries H 0) := by
  rw [lowerCentralFactorKernel]
  apply sup_le
  · rw [squaresSubgroup, Subgroup.closure_le]
    rintro _ ⟨x, rfl⟩
    change (x : H) ^ 2 ∈ higmanLowerCentralSeries H 1
    exact hH_square (Subgroup.subset_closure ⟨(x : H), rfl⟩)
  · exact le_rfl

private theorem lemma6_odd_aut_eq_one
    {H : Type u} [Group H] [Finite H]
    (hH_two : IsPGroup 2 H)
    (hH_square : squaresSubgroup H ≤ higmanLowerCentralSeries H 1)
    (theta : MulAut H)
    (htheta_odd : Odd (orderOf theta))
    (hfactor : lowerCentralFactorLinearAut theta 0 = 1) :
    theta = 1 := by
  let : Fact (IsPGroup 2 H) := ⟨hH_two⟩
  have hPhi : frattini H = higmanLowerCentralSeries H 1 := by
    rw [frattini_eq_closure_commutator_union_powers (R := H) (p := 2)]
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro z hz
      rcases hz with hz | ⟨x, rfl⟩
      · change z ∈ (⊤ : Subgroup H).lowerCentralSeries 1
        rw [Subgroup.top_lowerCentralSeries_one]
        exact hz
      · exact hH_square (Subgroup.subset_closure ⟨x, rfl⟩)
    · intro z hz
      apply Subgroup.subset_closure
      apply Or.inl
      change z ∈ (⊤ : Subgroup H).lowerCentralSeries 1 at hz
      rw [Subgroup.top_lowerCentralSeries_one] at hz
      exact hz
  let A : Subgroup (MulAut H) := Subgroup.zpowers theta
  have hAodd : Odd (Nat.card A) := by
    rw [Nat.card_zpowers]
    exact htheta_odd
  obtain ⟨r, hHcard⟩ := hH_two.exists_card_eq
  have hcop : Nat.Coprime (Nat.card A) (Nat.card H) := by
    rw [hHcard]
    exact hAodd.coprime_two_right.pow_right r
  have hPhiInv : IsInvariant A H (frattini H) :=
    isInvariant_of_characteristic (A := A) (G := H) (frattini H)
  let : MulAction.QuotientAction A (frattini H) :=
    quotientAction_of_isInvariant
      (A := A) (G := H) (frattini H) hPhiInv
  let : MulDistribMulAction A (H ⧸ frattini H) :=
    quotientMulDistribMulAction
      (A := A) (G := H) (frattini H) hPhiInv
  let thetaGen : A := ⟨theta, Subgroup.mem_zpowers theta⟩
  have hthetaFix : ∀ q : H ⧸ frattini H, thetaGen • q = q := by
    intro q
    refine QuotientGroup.induction_on q ?_
    intro x
    apply QuotientGroup.eq_iff_div_mem.mpr
    change theta x / x ∈ frattini H
    let x0 : higmanLowerCentralSeries H 0 := ⟨x, trivial⟩
    let v : Additive (LowerCentralFactor H 0) :=
      Additive.ofMul
        (QuotientGroup.mk' (lowerCentralFactorKernel H 0) x0)
    have hvfix : lowerCentralFactorLinearAut theta 0 v = v := by
      rw [hfactor]
      rfl
    rw [lowerCentralFactorLinearAut_ofMul_mk] at hvfix
    have hqeq :
        QuotientGroup.mk' (lowerCentralFactorKernel H 0)
            (lowerCentralSeriesMulAut theta 0 x0) =
          QuotientGroup.mk' (lowerCentralFactorKernel H 0) x0 := by
      exact Additive.ofMul.injective hvfix
    have hdiv :
        (lowerCentralSeriesMulAut theta 0 x0) / x0 ∈
          lowerCentralFactorKernel H 0 :=
      QuotientGroup.eq_iff_div_mem.mp hqeq
    have hnext :=
      lemma6_lowerCentralFactorKernel_zero_le hH_square hdiv
    rw [hPhi]
    exact hnext
  have hquot : ActsTrivially (A := A) (G := H ⧸ frattini H) := by
    intro a q
    have ha_mem : a ∈ Subgroup.zpowers thetaGen := by
      rcases Subgroup.mem_zpowers_iff.mp a.2 with ⟨z, hz⟩
      exact Subgroup.mem_zpowers_iff.mpr ⟨z, by
        apply Subtype.ext
        simpa [thetaGen] using hz⟩
    exact smul_eq_self_of_mem_zpowers ha_mem (hthetaFix q)
  have hnil : Group.IsNilpotent H :=
    IsPGroup.isNilpotent (p := 2) (G := H) hH_two
  let : Group.IsNilpotent H := hnil
  have hsolv : Group.IsSolvable H := by infer_instance
  have hsup :
      fixedPointSubgroup A H ⊔
          commutatorAction (A := A) (G := H) = ⊤ :=
    fixedPointSubgroup_sup_commutatorAction_eq_top_of_solvable_coprime
      (G := H) (A := A) hsolv hcop
  have htriv : ActsTrivially (A := A) (G := H) :=
    actsTrivially_of_trivial_quotient_frattini_of_sup_eq_top
      (R := H) (A := A) (p := 2) hsup hquot
  apply MulEquiv.ext
  intro x
  have hx := htriv thetaGen x
  simpa [thetaGen] using hx

private theorem lemma6_irreducible_pow_fixedPointFree
    {V : Type u} [AddCommGroup V] [Module (ZMod 2) V]
    (T : V ≃ₗ[ZMod 2] V)
    (hV_irreducible :
      ∀ A : Submodule (ZMod 2) V,
        (∀ x : V, x ∈ A → T x ∈ A) → A = ⊥ ∨ A = ⊤)
    {k m : ℕ} (hT_order : orderOf T = m)
    (hk_pos : 0 < k) (hk_lt : k < m) :
    ∀ x : V, (T ^ k) x = x → x = 0 := by
  let D : V →ₗ[ZMod 2] V := (T ^ k).toLinearMap - LinearMap.id
  have hD_invariant : ∀ x : V, x ∈ D.ker → T x ∈ D.ker := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    change (T ^ k) x - x = 0 at hx
    change (T ^ k) (T x) - T x = 0
    have hcomm : (T ^ k) (T x) = T ((T ^ k) x) := by
      simpa only [← LinearEquiv.mul_apply] using
        LinearEquiv.congr_fun (Commute.pow_self T k).eq x
    rw [hcomm, ← map_sub, hx, map_zero]
  rcases hV_irreducible D.ker hD_invariant with hD_bot | hD_top
  · intro x hx
    have hxker : x ∈ D.ker := by
      rw [LinearMap.mem_ker]
      change (T ^ k) x - x = 0
      exact sub_eq_zero.mpr hx
    rw [hD_bot] at hxker
    simpa using hxker
  · have hD_zero : D = 0 := LinearMap.ker_eq_top.mp hD_top
    have hT_pow : T ^ k = 1 := by
      apply LinearEquiv.ext
      intro x
      have hx := LinearMap.congr_fun hD_zero x
      change (T ^ k) x - x = 0 at hx
      simpa using sub_eq_zero.mp hx
    have hm_dvd : m ∣ k := by
      rw [← hT_order]
      exact (orderOf_dvd_iff_pow_eq_one).2 hT_pow
    exact (Nat.not_le_of_gt hk_lt (Nat.le_of_dvd hk_pos hm_dvd)).elim

private theorem lemma6_transitive_pow_fixedPointFree
    {V : Type u} [AddCommGroup V] [Module (ZMod 2) V]
    (T : V ≃ₗ[ZMod 2] V)
    (hV_transitive :
      ∀ x : V, x ≠ 0 → ∀ y : V, y ≠ 0 → ∃ j : ℕ, (T ^ j) x = y)
    {k m : ℕ} (hT_order : orderOf T = m)
    (hk_pos : 0 < k) (hk_lt : k < m) :
    ∀ x : V, (T ^ k) x = x → x = 0 := by
  intro x hx
  by_contra hx_ne
  have hfix : ∀ y : V, (T ^ k) y = y := by
    intro y
    by_cases hy : y = 0
    · subst y
      simp
    · obtain ⟨j, hj⟩ := hV_transitive x hx_ne y hy
      rw [← hj]
      calc
        (T ^ k) ((T ^ j) x) = (T ^ j) ((T ^ k) x) := by
          rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply]
          exact LinearEquiv.congr_fun ((Commute.refl T).pow_pow k j).eq x
        _ = (T ^ j) x := by rw [hx]
  have hT_pow : T ^ k = 1 := by
    apply LinearEquiv.ext
    intro y
    simpa using hfix y
  have hm_dvd : m ∣ k := by
    rw [← hT_order]
    exact (orderOf_dvd_iff_pow_eq_one).2 hT_pow
  exact Nat.not_le_of_gt hk_lt (Nat.le_of_dvd hk_pos hm_dvd)

private theorem lemma6_pow_fixedPointFree_transfer
    {V : Type u} {W : Type v}
    [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    (T : V ≃ₗ[ZMod 2] V) (S : W ≃ₗ[ZMod 2] W)
    (e : W ≃ₗ[ZMod 2] V) (he : ∀ x : W, e (S x) = T (e x))
    (k : ℕ)
    (hT_fixedPointFree : ∀ x : V, (T ^ k) x = x → x = 0) :
    ∀ x : W, (S ^ k) x = x → x = 0 := by
  have he_pow : ∀ j : ℕ, ∀ x : W, e ((S ^ j) x) = (T ^ j) (e x) := by
    intro j
    induction j with
    | zero =>
        intro x
        simp
    | succ j ih =>
        intro x
        simpa only [pow_succ, LinearEquiv.mul_apply] using
          (calc
            e ((S ^ j) (S x)) = (T ^ j) (e (S x)) := ih (S x)
            _ = (T ^ j) (T (e x)) :=
              congrArg (fun y => (T ^ j) y) (he x))
  intro x hx
  apply e.injective
  simpa using hT_fixedPointFree (e x) (by rw [← he_pow, hx])

/-- The synchronized cardinality and action-order data used by both parity
branches of Higman Lemma 6. -/
private def lemma6ActionOrderSyncData
    {H : Type u} [Group H] (xi : MulAut H) (n : ℕ) : Prop :=
  orderOf (lowerCentralFactorLinearAut xi 0) = 2 ^ n - 1 ∧
    orderOf (lowerCentralFactorLinearAut xi 1) = 2 ^ n - 1 ∧
    orderOf (lowerCentralFactorLinearAut xi 2) = 2 ^ n - 1 ∧
    Nat.card (LowerCentralFactor H 0) = 2 ^ n ∧
    Nat.card (LowerCentralFactor H 2) = 2 ^ n

/-- First source step of Higman Lemma 6: an equivariant identification of
L₃ with L₂ synchronizes the Singer action and cardinalities of L₁, L₂, L₃. -/
private theorem lemma6_action_order_sync_core
    {H : Type u} [Group H] [Finite H]
    (xi : MulAut H)
    (hL1_irreducible :
      ∀ W : Submodule (ZMod 2) (Additive (LowerCentralFactor H 0)),
        (∀ v : Additive (LowerCentralFactor H 0), v ∈ W →
          lowerCentralFactorLinearAut xi 0 v ∈ W) →
        W = ⊥ ∨ W = ⊤)
    (hL2_transitive :
      ∀ x : Additive (LowerCentralFactor H 1), x ≠ 0 →
        ∀ y : Additive (LowerCentralFactor H 1), y ≠ 0 →
          ∃ k : ℕ, (lowerCentralFactorLinearAut xi 1 ^ k) x = y)
    (n : ℕ) (hn : 2 ≤ n)
    (hL2_card : Nat.card (LowerCentralFactor H 1) = 2 ^ n)
    (e : Additive (LowerCentralFactor H 2) ≃ₗ[ZMod 2]
      Additive (LowerCentralFactor H 1))
    (he : ∀ v : Additive (LowerCentralFactor H 2),
      e (lowerCentralFactorLinearAut xi 2 v) =
        lowerCentralFactorLinearAut xi 1 (e v)) :
    lemma6ActionOrderSyncData xi n := by
  obtain ⟨B, _hB_mk, hB_equivariant, _hB_self, hB_span⟩ :=
    lemma4_exists_lowerCentralBracket (H := H)
  obtain ⟨C, hC_equivariant, hC_span⟩ :=
    lemma6_exists_lowerCentralIteratedBracket (H := H)
  rcases lemma6_action_order_sync_of_brackets
      (lowerCentralFactorLinearAut xi 0)
      (lowerCentralFactorLinearAut xi 1)
      (lowerCentralFactorLinearAut xi 2)
      hL1_irreducible hL2_transitive n hn hL2_card e he
      B (hB_equivariant xi) hB_span C (hC_equivariant xi) hC_span with
    ⟨hL1_order, hL2_order, hL3_order, hL1_card_add, hL3_card_add⟩
  refine ⟨hL1_order, hL2_order, hL3_order, ?_, ?_⟩
  · exact (Nat.card_congr
      (Additive.toMul : Additive (LowerCentralFactor H 0) ≃
        LowerCentralFactor H 0)).symm.trans hL1_card_add
  · exact (Nat.card_congr
      (Additive.toMul : Additive (LowerCentralFactor H 2) ≃
        LowerCentralFactor H 2)).symm.trans hL3_card_add

private theorem lemma6_lowerCentralQuotient_fixedPointFree
    {H : Type u} [Group H]
    (theta : MulAut H) (k : ℕ)
    (hk0 : lowerCentralFactorKernel H 0 =
      (higmanLowerCentralSeries H 1).subgroupOf (higmanLowerCentralSeries H 0))
    (hk1 : lowerCentralFactorKernel H 1 =
      (higmanLowerCentralSeries H 2).subgroupOf (higmanLowerCentralSeries H 1))
    (hk2 : lowerCentralFactorKernel H 2 =
      (higmanLowerCentralSeries H 3).subgroupOf (higmanLowerCentralSeries H 2))
    (hfp0 : ∀ v : Additive (LowerCentralFactor H 0),
      (lowerCentralFactorLinearAut theta 0 ^ k) v = v → v = 0)
    (hfp1 : ∀ v : Additive (LowerCentralFactor H 1),
      (lowerCentralFactorLinearAut theta 1 ^ k) v = v → v = 0)
    (hfp2 : ∀ v : Additive (LowerCentralFactor H 2),
      (lowerCentralFactorLinearAut theta 2 ^ k) v = v → v = 0) :
    ∀ q : H ⧸ higmanLowerCentralSeries H 3,
      lowerCentralQuotientMulAut (theta ^ k) 3 q = q → q = 1 := by
  intro q
  refine QuotientGroup.induction_on q ?_
  intro x hx
  have hdiff3 : (theta ^ k) x / x ∈ higmanLowerCentralSeries H 3 := by
    apply QuotientGroup.eq_iff_div_mem.mp
    change lowerCentralQuotientMulAut (theta ^ k) 3
        (QuotientGroup.mk' (higmanLowerCentralSeries H 3) x) =
      QuotientGroup.mk' (higmanLowerCentralSeries H 3) x at hx
    rw [lowerCentralQuotientMulAut_mk] at hx
    exact hx
  let x0 : higmanLowerCentralSeries H 0 := ⟨x, trivial⟩
  let v0 : Additive (LowerCentralFactor H 0) :=
    Additive.ofMul (QuotientGroup.mk' (lowerCentralFactorKernel H 0) x0)
  have hv0fix : (lowerCentralFactorLinearAut theta 0 ^ k) v0 = v0 := by
    rw [← lowerCentralFactorLinearAut_pow]
    apply Additive.ofMul.injective
    rw [lowerCentralFactorLinearAut_ofMul_mk]
    apply QuotientGroup.eq_iff_div_mem.mpr
    rw [hk0]
    change (theta ^ k) x / x ∈ higmanLowerCentralSeries H 1
    exact (⊤ : Subgroup H).lowerCentralSeries_antitone (by omega : 1 ≤ 3) hdiff3
  have hv0zero := hfp0 v0 hv0fix
  change Additive.ofMul
    (QuotientGroup.mk' (lowerCentralFactorKernel H 0) x0) = 0 at hv0zero
  have hx0ker : x0 ∈ lowerCentralFactorKernel H 0 := by
    apply (QuotientGroup.eq_one_iff _).1
    exact Additive.ofMul.injective hv0zero
  have hx1 : x ∈ higmanLowerCentralSeries H 1 := by
    rw [hk0] at hx0ker
    exact hx0ker
  let x1 : higmanLowerCentralSeries H 1 := ⟨x, hx1⟩
  let v1 : Additive (LowerCentralFactor H 1) :=
    Additive.ofMul (QuotientGroup.mk' (lowerCentralFactorKernel H 1) x1)
  have hv1fix : (lowerCentralFactorLinearAut theta 1 ^ k) v1 = v1 := by
    rw [← lowerCentralFactorLinearAut_pow]
    apply Additive.ofMul.injective
    rw [lowerCentralFactorLinearAut_ofMul_mk]
    apply QuotientGroup.eq_iff_div_mem.mpr
    rw [hk1]
    change (theta ^ k) x / x ∈ higmanLowerCentralSeries H 2
    exact (⊤ : Subgroup H).lowerCentralSeries_antitone (by omega : 2 ≤ 3) hdiff3
  have hv1zero := hfp1 v1 hv1fix
  change Additive.ofMul
    (QuotientGroup.mk' (lowerCentralFactorKernel H 1) x1) = 0 at hv1zero
  have hx1ker : x1 ∈ lowerCentralFactorKernel H 1 := by
    apply (QuotientGroup.eq_one_iff _).1
    exact Additive.ofMul.injective hv1zero
  have hx2 : x ∈ higmanLowerCentralSeries H 2 := by
    rw [hk1] at hx1ker
    exact hx1ker
  let x2 : higmanLowerCentralSeries H 2 := ⟨x, hx2⟩
  let v2 : Additive (LowerCentralFactor H 2) :=
    Additive.ofMul (QuotientGroup.mk' (lowerCentralFactorKernel H 2) x2)
  have hv2fix : (lowerCentralFactorLinearAut theta 2 ^ k) v2 = v2 := by
    rw [← lowerCentralFactorLinearAut_pow]
    apply Additive.ofMul.injective
    rw [lowerCentralFactorLinearAut_ofMul_mk]
    apply QuotientGroup.eq_iff_div_mem.mpr
    rw [hk2]
    change (theta ^ k) x / x ∈ higmanLowerCentralSeries H 3
    exact hdiff3
  have hv2zero := hfp2 v2 hv2fix
  change Additive.ofMul
    (QuotientGroup.mk' (lowerCentralFactorKernel H 2) x2) = 0 at hv2zero
  have hx2ker : x2 ∈ lowerCentralFactorKernel H 2 := by
    apply (QuotientGroup.eq_one_iff _).1
    exact Additive.ofMul.injective hv2zero
  apply (QuotientGroup.eq_one_iff _).2
  rw [hk2] at hx2ker
  exact hx2ker

private theorem lemma6_lowerCentralQuotient_order_three
    {H : Type u} [Group H] [Finite H]
    (phi : MulAut (H ⧸ higmanLowerCentralSeries H 3))
    (hphi3 : phi ^ 3 = 1)
    (hphi_fpf : ∀ q, phi q = q → q = 1)
    (hk2 : lowerCentralFactorKernel H 2 =
      (higmanLowerCentralSeries H 3).subgroupOf (higmanLowerCentralSeries H 2))
    {n : ℕ} (hn : 2 ≤ n)
    (hL3_card : Nat.card (LowerCentralFactor H 2) = 2 ^ n) :
    orderOf phi = 3 := by
  have hL3_card_gt : 1 < Nat.card (LowerCentralFactor H 2) := by
    rw [hL3_card]
    exact one_lt_pow₀ (by norm_num : 1 < (2 : ℕ)) (by omega)
  let : Nontrivial (LowerCentralFactor H 2) :=
    Finite.one_lt_card_iff_nontrivial.mp hL3_card_gt
  obtain ⟨z, hz⟩ := exists_ne (1 : LowerCentralFactor H 2)
  obtain ⟨x, hx⟩ :=
    QuotientGroup.mk'_surjective (lowerCentralFactorKernel H 2) z
  let q : H ⧸ higmanLowerCentralSeries H 3 :=
    QuotientGroup.mk' (higmanLowerCentralSeries H 3) (x : H)
  have hq_ne : q ≠ 1 := by
    intro hq
    have hx3 : (x : H) ∈ higmanLowerCentralSeries H 3 :=
      (QuotientGroup.eq_one_iff _).1 hq
    have hxker : x ∈ lowerCentralFactorKernel H 2 := by
      rw [hk2]
      exact hx3
    have hzone :
        QuotientGroup.mk' (lowerCentralFactorKernel H 2) x = 1 :=
      (QuotientGroup.eq_one_iff _).2 hxker
    exact hz (hx.symm.trans hzone)
  have hphi_ne : phi ≠ 1 := by
    intro hphi
    apply hq_ne
    apply hphi_fpf q
    rw [hphi]
    rfl
  have hdvd : orderOf phi ∣ 3 :=
    orderOf_dvd_iff_pow_eq_one.mpr hphi3
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with horder | horder
  · exact (hphi_ne (orderOf_eq_one_iff.mp horder)).elim
  · exact horder

private theorem lemma6_lowerCentralQuotient_class_contradiction
    {H : Type u} [Group H] [Finite H]
    (hclass : higmanLowerCentralSeries (H ⧸ higmanLowerCentralSeries H 3) 2 = ⊥)
    (hk2 : lowerCentralFactorKernel H 2 =
      (higmanLowerCentralSeries H 3).subgroupOf (higmanLowerCentralSeries H 2))
    {n : ℕ} (hn : 2 ≤ n)
    (hL3_card : Nat.card (LowerCentralFactor H 2) = 2 ^ n) :
    False := by
  let q : H →* H ⧸ higmanLowerCentralSeries H 3 :=
    QuotientGroup.mk' (higmanLowerCentralSeries H 3)
  have hmap : (higmanLowerCentralSeries H 2).map q =
      higmanLowerCentralSeries (H ⧸ higmanLowerCentralSeries H 3) 2 :=
    lowerCentralSeries_map_eq_of_surjective q
      (QuotientGroup.mk'_surjective _) 2
  have hle23 : higmanLowerCentralSeries H 2 ≤ higmanLowerCentralSeries H 3 := by
    rw [← QuotientGroup.ker_mk' (higmanLowerCentralSeries H 3)]
    apply (Subgroup.map_eq_bot_iff (higmanLowerCentralSeries H 2)).mp
    rw [hmap, hclass]
  have hL3_card_gt : 1 < Nat.card (LowerCentralFactor H 2) := by
    rw [hL3_card]
    exact one_lt_pow₀ (by norm_num : 1 < (2 : ℕ)) (by omega)
  let : Nontrivial (LowerCentralFactor H 2) :=
    Finite.one_lt_card_iff_nontrivial.mp hL3_card_gt
  obtain ⟨z, hz⟩ := exists_ne (1 : LowerCentralFactor H 2)
  obtain ⟨x, hx⟩ :=
    QuotientGroup.mk'_surjective (lowerCentralFactorKernel H 2) z
  have hxker : x ∈ lowerCentralFactorKernel H 2 := by
    rw [hk2]
    exact hle23 x.property
  have hzone :
      QuotientGroup.mk' (lowerCentralFactorKernel H 2) x = 1 :=
    (QuotientGroup.eq_one_iff _).2 hxker
  exact hz (hx.symm.trans hzone)

/-- Second source step of Higman Lemma 6: even common dimension gives a
fixed-point-free automorphism of order three on H/H₄, contradicting Neumann. -/
private theorem lemma6_even_dimension_contradiction_core
    {H : Type u} [Group H] [Finite H]
    (hH_two : IsPGroup 2 H)
    (_hH_nonabelian : ¬ IsMulCommutative H)
    (xi : MulAut H)
    (hxi_odd : Odd (orderOf xi))
    (hL1_irreducible :
      ∀ W : Submodule (ZMod 2) (Additive (LowerCentralFactor H 0)),
        (∀ v : Additive (LowerCentralFactor H 0), v ∈ W →
          lowerCentralFactorLinearAut xi 0 v ∈ W) →
        W = ⊥ ∨ W = ⊤)
    (hL2_transitive :
      ∀ x : Additive (LowerCentralFactor H 1), x ≠ 0 →
        ∀ y : Additive (LowerCentralFactor H 1), y ≠ 0 →
          ∃ k : ℕ, (lowerCentralFactorLinearAut xi 1 ^ k) x = y)
    (n : ℕ) (hn : 2 ≤ n)
    (_hL2_card : Nat.card (LowerCentralFactor H 1) = 2 ^ n)
    (hH_square : squaresSubgroup H ≤ higmanLowerCentralSeries H 1)
    (e : Additive (LowerCentralFactor H 2) ≃ₗ[ZMod 2]
      Additive (LowerCentralFactor H 1))
    (he : ∀ v : Additive (LowerCentralFactor H 2),
      e (lowerCentralFactorLinearAut xi 2 v) =
        lowerCentralFactorLinearAut xi 1 (e v))
    (hsync : lemma6ActionOrderSyncData xi n)
    (hn_even : Even n) :
    False := by
  rcases hsync with
    ⟨hL1_order, hL2_order, hL3_order, hL1_card, hL3_card⟩
  let m := 2 ^ n - 1
  let k := m / 3
  have hthree_dvd : 3 ∣ m := by
    have h := Nat.pow_sub_one_dvd_pow_sub_one 2 hn_even.two_dvd
    norm_num at h
    simpa [m] using h
  have hpow : 4 ≤ 2 ^ n := by
    simpa using (Nat.pow_le_pow_right (n := 2) (by omega) hn)
  have hm_pos : 0 < m := by simp only [m]; omega
  have hthree_le : 3 ≤ m := by simp only [m]; omega
  have hthree_mul : 3 * k = m := Nat.mul_div_cancel' hthree_dvd
  have hk_pos : 0 < k := Nat.div_pos hthree_le (by norm_num)
  have hk_lt : k < m := Nat.div_lt_self hm_pos (by norm_num)
  have hfactor :
      lowerCentralFactorLinearAut (xi ^ m) 0 = 1 := by
    rw [lowerCentralFactorLinearAut_pow]
    change lowerCentralFactorLinearAut xi 0 ^ (2 ^ n - 1) = 1
    rw [← hL1_order]
    exact pow_orderOf_eq_one _
  have hodd_pow : Odd (orderOf (xi ^ m)) :=
    hxi_odd.of_dvd_nat (orderOf_pow_dvd m)
  have hxi_m : xi ^ m = 1 :=
    lemma6_odd_aut_eq_one
      hH_two hH_square (xi ^ m) hodd_pow hfactor
  have hsq0 :
      squaresSubgroup (higmanLowerCentralSeries H 0) ≤
        (higmanLowerCentralSeries H 1).subgroupOf (higmanLowerCentralSeries H 0) := by
    rw [squaresSubgroup, Subgroup.closure_le]
    rintro _ ⟨x, rfl⟩
    change (x : H) ^ 2 ∈ higmanLowerCentralSeries H 1
    exact hH_square (Subgroup.subset_closure ⟨(x : H), rfl⟩)
  have hsq1 :
      squaresSubgroup (higmanLowerCentralSeries H 1) ≤
        (higmanLowerCentralSeries H 2).subgroupOf (higmanLowerCentralSeries H 1) := by
    simpa using
      lemma6_squares_lowerCentralSeries_succ (H := H) 0 hsq0
  have hsq2 :
      squaresSubgroup (higmanLowerCentralSeries H 2) ≤
        (higmanLowerCentralSeries H 3).subgroupOf (higmanLowerCentralSeries H 2) := by
    simpa using
      lemma6_squares_lowerCentralSeries_succ (H := H) 1 hsq1
  have hk0 :
      lowerCentralFactorKernel H 0 =
        (higmanLowerCentralSeries H 1).subgroupOf (higmanLowerCentralSeries H 0) := by
    rw [lowerCentralFactorKernel]
    exact sup_eq_right.mpr hsq0
  have hk1 :
      lowerCentralFactorKernel H 1 =
        (higmanLowerCentralSeries H 2).subgroupOf (higmanLowerCentralSeries H 1) := by
    rw [lowerCentralFactorKernel]
    exact sup_eq_right.mpr hsq1
  have hk2 :
      lowerCentralFactorKernel H 2 =
        (higmanLowerCentralSeries H 3).subgroupOf (higmanLowerCentralSeries H 2) := by
    rw [lowerCentralFactorKernel]
    exact sup_eq_right.mpr hsq2
  have hL1_fpf := lemma6_irreducible_pow_fixedPointFree
    (lowerCentralFactorLinearAut xi 0) hL1_irreducible
    (by simpa [m] using hL1_order) hk_pos hk_lt
  have hL2_fpf := lemma6_transitive_pow_fixedPointFree
    (lowerCentralFactorLinearAut xi 1) hL2_transitive
    (by simpa [m] using hL2_order) hk_pos hk_lt
  have hL3_fpf := lemma6_pow_fixedPointFree_transfer
    (lowerCentralFactorLinearAut xi 1)
    (lowerCentralFactorLinearAut xi 2) e he k hL2_fpf
  let eta : MulAut H := xi ^ k
  let phi : MulAut (H ⧸ higmanLowerCentralSeries H 3) :=
    lowerCentralQuotientMulAut eta 3
  have heta3 : eta ^ 3 = 1 := by
    dsimp [eta]
    rw [← pow_mul, Nat.mul_comm k 3, hthree_mul, hxi_m]
  have hphi3 : phi ^ 3 = 1 := by
    dsimp [phi]
    calc
      lowerCentralQuotientMulAut eta 3 ^ 3 =
          lowerCentralQuotientMulAut (eta ^ 3) 3 :=
        (lowerCentralQuotientMulAut_pow eta 3 3).symm
      _ = lowerCentralQuotientMulAut (1 : MulAut H) 3 := by rw [heta3]
      _ = 1 := map_one (lowerCentralQuotientMulAutHom 3)
  have hphi_fpf : ∀ q, phi q = q → q = 1 := by
    simpa only [phi, eta] using
      lemma6_lowerCentralQuotient_fixedPointFree xi k hk0 hk1 hk2
        hL1_fpf hL2_fpf hL3_fpf
  have hphi_order : orderOf phi = 3 :=
    lemma6_lowerCentralQuotient_order_three
      phi hphi3 hphi_fpf hk2 hn hL3_card
  have hclass : higmanLowerCentralSeries (H ⧸ higmanLowerCentralSeries H 3) 2 = ⊥ :=
    neumann_order_three_fixedPointFree_class_le_two
      phi hphi_order hphi_fpf
  exact lemma6_lowerCentralQuotient_class_contradiction
    hclass hk2 hn hL3_card

private lemma lemma6_triple_two_pow_ne_pair_two_pow
    (i j k a b : ℕ) (hij : i < j) (hjk : j < k) (hab : a < b) :
    2 ^ i + 2 ^ j + 2 ^ k ≠ 2 ^ a + 2 ^ b := by
  intro h
  have hpi : 0 < 2 ^ i := Nat.two_pow_pos i
  have hpj : 0 < 2 ^ j := Nat.two_pow_pos j
  have hpk : 0 < 2 ^ k := Nat.two_pow_pos k
  have hpa : 0 < 2 ^ a := Nat.two_pow_pos a
  have hpb : 0 < 2 ^ b := Nat.two_pow_pos b
  have hijpow : 2 ^ i < 2 ^ j := Nat.pow_lt_pow_right (by omega) hij
  have hjkpow : 2 ^ j < 2 ^ k := Nat.pow_lt_pow_right (by omega) hjk
  have habpow : 2 ^ a < 2 ^ b := Nat.pow_lt_pow_right (by omega) hab
  have hleftLower : 2 ^ k < 2 ^ i + 2 ^ j + 2 ^ k := by omega
  have hrightLower : 2 ^ b < 2 ^ a + 2 ^ b := by omega
  have hijUpper : 2 ^ i + 2 ^ j < 2 ^ (j + 1) := by
    rw [pow_succ]
    omega
  have habUpper : 2 ^ a + 2 ^ b < 2 ^ (b + 1) := by
    rw [pow_succ]
    omega
  have hleftUpper : 2 ^ i + 2 ^ j + 2 ^ k < 2 ^ (k + 1) := by
    rw [pow_succ]
    have : 2 ^ i + 2 ^ j < 2 ^ k := by
      exact lt_of_lt_of_le hijUpper
        (Nat.pow_le_pow_right (by omega) (by omega))
    omega
  have hrightUpper : 2 ^ a + 2 ^ b < 2 ^ (b + 1) := habUpper
  have hbk : b = k := by
    rcases lt_trichotomy b k with hbk | hbk | hkb
    · have hp : 2 ^ (b + 1) ≤ 2 ^ k :=
        Nat.pow_le_pow_right (by omega) (by omega)
      omega
    · exact hbk
    · have hp : 2 ^ (k + 1) ≤ 2 ^ b :=
        Nat.pow_le_pow_right (by omega) (by omega)
      omega
  subst b
  have hs : 2 ^ i + 2 ^ j = 2 ^ a := by omega
  rcases le_or_gt a j with haj | hja
  · have hp : 2 ^ a ≤ 2 ^ j :=
      Nat.pow_le_pow_right (by omega) haj
    omega
  · have hp : 2 ^ (j + 1) ≤ 2 ^ a :=
      Nat.pow_le_pow_right (by omega) (by omega)
    omega

public lemma lemma6_triple_two_pow_not_modEq_pair_two_pow
    (n i j k a b : ℕ)
    (hij : i < j) (hjk : j < k) (hkn : k < n)
    (hab : a < b) (hbn : b < n) :
    ¬ Nat.ModEq (2 ^ n - 1)
      (2 ^ i + 2 ^ j + 2 ^ k) (2 ^ a + 2 ^ b) := by
  intro hmod
  have hn0 : n ≠ 0 := by omega
  have hpi : 0 < 2 ^ i := Nat.two_pow_pos i
  have hpj : 0 < 2 ^ j := Nat.two_pow_pos j
  have hpk : 0 < 2 ^ k := Nat.two_pow_pos k
  have hpa : 0 < 2 ^ a := Nat.two_pow_pos a
  have hpb : 0 < 2 ^ b := Nat.two_pow_pos b
  have hijpow : 2 ^ i < 2 ^ j := Nat.pow_lt_pow_right (by omega) hij
  have habpow : 2 ^ a < 2 ^ b := Nat.pow_lt_pow_right (by omega) hab
  have hijUpper : 2 ^ i + 2 ^ j < 2 ^ (j + 1) := by
    rw [pow_succ]
    omega
  have htriple_lt_pow : 2 ^ i + 2 ^ j + 2 ^ k < 2 ^ n := by
    have hlow : 2 ^ i + 2 ^ j < 2 ^ k := by
      exact lt_of_lt_of_le hijUpper
        (Nat.pow_le_pow_right (by omega) (by omega))
    have hknpow : 2 ^ (k + 1) ≤ 2 ^ n :=
      Nat.pow_le_pow_right (by omega) (by omega)
    rw [pow_succ] at hknpow
    omega
  have habUpper : 2 ^ a + 2 ^ b < 2 ^ (b + 1) := by
    rw [pow_succ]
    omega
  have hpair_lt_pow : 2 ^ a + 2 ^ b < 2 ^ n :=
    lt_of_lt_of_le habUpper
      (Nat.pow_le_pow_right (by omega) (by omega))
  have htriple_le :
      2 ^ i + 2 ^ j + 2 ^ k ≤ 2 ^ n - 1 := by omega
  have hpair_le : 2 ^ a + 2 ^ b ≤ 2 ^ n - 1 := by omega
  rcases htriple_le.eq_or_lt with htriple_eq | htriple_lt
  · rcases hpair_le.eq_or_lt with hpair_eq | hpair_lt
    · exact lemma6_triple_two_pow_ne_pair_two_pow i j k a b hij hjk hab
        (htriple_eq.trans hpair_eq.symm)
    · rw [htriple_eq] at hmod
      change (2 ^ n - 1) % (2 ^ n - 1) =
        (2 ^ a + 2 ^ b) % (2 ^ n - 1) at hmod
      rw [Nat.mod_self, Nat.mod_eq_of_lt hpair_lt] at hmod
      omega
  · rcases hpair_le.eq_or_lt with hpair_eq | hpair_lt
    · rw [hpair_eq] at hmod
      change (2 ^ i + 2 ^ j + 2 ^ k) % (2 ^ n - 1) =
        (2 ^ n - 1) % (2 ^ n - 1) at hmod
      rw [Nat.mod_self, Nat.mod_eq_of_lt htriple_lt] at hmod
      omega
    · exact lemma6_triple_two_pow_ne_pair_two_pow i j k a b hij hjk hab
        (hmod.eq_of_lt_of_lt htriple_lt hpair_lt)

private lemma lemma6_odd_not_both_cyclic_pair_differences
    (n d r : ℕ) (hn : Odd n) (hd : 1 < d) (hdn : d + 1 < n)
    (hminus : d - 1 = r ∨ d - 1 = n - r)
    (hplus : d + 1 = r ∨ d + 1 = n - r) :
    False := by
  rcases hn with ⟨q, rfl⟩
  rcases hminus with hminus | hminus <;>
    rcases hplus with hplus | hplus <;> omega

private lemma lemma6_modEq_eq_of_pos_of_le
    {m x y : ℕ} (hx : 0 < x) (hy : 0 < y) (hxle : x ≤ m) (hyle : y ≤ m)
    (hmod : Nat.ModEq m x y) :
    x = y := by
  rcases hxle.eq_or_lt with hxEq | hxlt
  · rcases hyle.eq_or_lt with hyEq | hylt
    · exact hxEq.trans hyEq.symm
    · rw [hxEq] at hmod
      change m % m = y % m at hmod
      rw [Nat.mod_self, Nat.mod_eq_of_lt hylt] at hmod
      omega
  · rcases hyle.eq_or_lt with hyEq | hylt
    · rw [hyEq] at hmod
      change x % m = m % m at hmod
      rw [Nat.mod_self, Nat.mod_eq_of_lt hxlt] at hmod
      omega
    · exact hmod.eq_of_lt_of_lt hxlt hylt

private lemma lemma6_pair_two_pow_eq_ordered
    (a b i j : ℕ) (hab : a < b) (hij : i < j)
    (hEq : 2 ^ a + 2 ^ b = 2 ^ i + 2 ^ j) :
    a = i ∧ b = j := by
  have hpa : 0 < 2 ^ a := Nat.two_pow_pos a
  have hpb : 0 < 2 ^ b := Nat.two_pow_pos b
  have hpi : 0 < 2 ^ i := Nat.two_pow_pos i
  have hpj : 0 < 2 ^ j := Nat.two_pow_pos j
  have habpow : 2 ^ a < 2 ^ b := Nat.pow_lt_pow_right (by omega) hab
  have hijpow : 2 ^ i < 2 ^ j := Nat.pow_lt_pow_right (by omega) hij
  have habUpper : 2 ^ a + 2 ^ b < 2 ^ (b + 1) := by
    rw [pow_succ]
    omega
  have hijUpper : 2 ^ i + 2 ^ j < 2 ^ (j + 1) := by
    rw [pow_succ]
    omega
  have hbj : b = j := by
    rcases lt_trichotomy b j with hbj | hbj | hjb
    · have hp : 2 ^ (b + 1) ≤ 2 ^ j :=
        Nat.pow_le_pow_right (by omega) (by omega)
      omega
    · exact hbj
    · have hp : 2 ^ (j + 1) ≤ 2 ^ b :=
        Nat.pow_le_pow_right (by omega) (by omega)
      omega
  subst j
  have hpai : 2 ^ a = 2 ^ i := by omega
  exact ⟨Nat.pow_right_injective (by omega) hpai, rfl⟩

private lemma lemma6_pair_two_pow_modEq_ordered
    (n a b i j : ℕ) (hab : a < b) (hbn : b < n)
    (hij : i < j) (hjn : j < n)
    (hmod : Nat.ModEq (2 ^ n - 1) (2 ^ a + 2 ^ b) (2 ^ i + 2 ^ j)) :
    a = i ∧ b = j := by
  have hpa : 0 < 2 ^ a := Nat.two_pow_pos a
  have hpb : 0 < 2 ^ b := Nat.two_pow_pos b
  have hpi : 0 < 2 ^ i := Nat.two_pow_pos i
  have hpj : 0 < 2 ^ j := Nat.two_pow_pos j
  have habpow : 2 ^ a < 2 ^ b := Nat.pow_lt_pow_right (by omega) hab
  have hijpow : 2 ^ i < 2 ^ j := Nat.pow_lt_pow_right (by omega) hij
  have habUpper : 2 ^ a + 2 ^ b < 2 ^ (b + 1) := by
    rw [pow_succ]
    omega
  have hijUpper : 2 ^ i + 2 ^ j < 2 ^ (j + 1) := by
    rw [pow_succ]
    omega
  have hleft_lt_pow : 2 ^ a + 2 ^ b < 2 ^ n :=
    lt_of_lt_of_le habUpper
      (Nat.pow_le_pow_right (by omega) (by omega))
  have hright_lt_pow : 2 ^ i + 2 ^ j < 2 ^ n :=
    lt_of_lt_of_le hijUpper
      (Nat.pow_le_pow_right (by omega) (by omega))
  have hEq : 2 ^ a + 2 ^ b = 2 ^ i + 2 ^ j :=
    lemma6_modEq_eq_of_pos_of_le (by omega) (by omega) (by omega) (by omega) hmod
  exact lemma6_pair_two_pow_eq_ordered a b i j hab hij hEq

public lemma lemma6_pair_two_pow_modEq_classify
    (n x y i j : ℕ) (hxn : x < n) (hyn : y < n) (hxy : x ≠ y)
    (hij : i < j) (hjn : j < n)
    (hmod : Nat.ModEq (2 ^ n - 1) (2 ^ x + 2 ^ y) (2 ^ i + 2 ^ j)) :
    (x = i ∧ y = j) ∨ (x = j ∧ y = i) := by
  rcases lt_or_gt_of_ne hxy with hxylt | hyxlt
  · exact Or.inl (lemma6_pair_two_pow_modEq_ordered n x y i j
      hxylt hyn hij hjn hmod)
  · have h := lemma6_pair_two_pow_modEq_ordered n y x i j
      hyxlt hxn hij hjn (by simpa [add_comm] using hmod)
    exact Or.inr ⟨h.2, h.1⟩

public lemma lemma6_two_pow_add_self_modEq_cyclic
    (n a : ℕ) (hn : 0 < n) (han : a < n) :
    Nat.ModEq (2 ^ n - 1) (2 ^ a + 2 ^ a) (2 ^ ((a + 1) % n)) := by
  by_cases hs : a + 1 < n
  · have hmod : (a + 1) % n = a + 1 := Nat.mod_eq_of_lt hs
    have heq : 2 ^ a + 2 ^ a = 2 ^ ((a + 1) % n) := by
      rw [hmod, pow_succ]
      omega
    exact heq ▸ Nat.ModEq.refl _
  · have hsucc : a + 1 = n := by omega
    subst n
    have hone : 1 ≤ 2 ^ (a + 1) := Nat.one_le_two_pow
    have hperiod : Nat.ModEq (2 ^ (a + 1) - 1) (2 ^ (a + 1)) 1 := by
      apply Nat.ModEq.symm
      exact (Nat.modEq_iff_dvd' hone).2 (dvd_refl (2 ^ (a + 1) - 1))
    rw [Nat.mod_self, pow_zero]
    rw [pow_succ] at hperiod
    simpa [pow_succ, mul_two] using hperiod

public lemma lemma6_single_two_pow_not_modEq_pair_two_pow
    (n c i j : ℕ) (hcn : c < n) (hij : i < j) (hjn : j < n) :
    ¬ Nat.ModEq (2 ^ n - 1) (2 ^ c) (2 ^ i + 2 ^ j) := by
  intro hmod
  have hpc : 0 < 2 ^ c := Nat.two_pow_pos c
  have hpi : 0 < 2 ^ i := Nat.two_pow_pos i
  have hpj : 0 < 2 ^ j := Nat.two_pow_pos j
  have hijpow : 2 ^ i < 2 ^ j := Nat.pow_lt_pow_right (by omega) hij
  have hc_lt_pow : 2 ^ c < 2 ^ n :=
    Nat.pow_lt_pow_right (by omega) hcn
  have hijUpper : 2 ^ i + 2 ^ j < 2 ^ (j + 1) := by
    rw [pow_succ]
    omega
  have hpair_lt_pow : 2 ^ i + 2 ^ j < 2 ^ n :=
    lt_of_lt_of_le hijUpper
      (Nat.pow_le_pow_right (by omega) (by omega))
  have hEq : 2 ^ c = 2 ^ i + 2 ^ j :=
    lemma6_modEq_eq_of_pos_of_le hpc (by omega) (by omega) (by omega) hmod
  rcases le_or_gt c j with hcj | hjc
  · have hp : 2 ^ c ≤ 2 ^ j :=
      Nat.pow_le_pow_right (by omega) hcj
    omega
  · have hp : 2 ^ (j + 1) ≤ 2 ^ c :=
      Nat.pow_le_pow_right (by omega) (by omega)
    omega

private lemma lemma6_repeated_two_pow_modEq_cyclic
    (n a b : ℕ) (hn : 0 < n) (hbn : b < n) :
    Nat.ModEq (2 ^ n - 1)
      (2 ^ a + 2 ^ b + 2 ^ b) (2 ^ a + 2 ^ ((b + 1) % n)) := by
  by_cases hs : b + 1 < n
  · have hmod : (b + 1) % n = b + 1 := Nat.mod_eq_of_lt hs
    have heq :
        2 ^ a + 2 ^ b + 2 ^ b = 2 ^ a + 2 ^ ((b + 1) % n) := by
      rw [hmod, pow_succ]
      omega
    exact heq ▸ Nat.ModEq.refl _
  · have hsucc : b + 1 = n := by omega
    subst n
    have hone : 1 ≤ 2 ^ (b + 1) := Nat.one_le_two_pow
    have hperiod : Nat.ModEq (2 ^ (b + 1) - 1) (2 ^ (b + 1)) 1 := by
      apply Nat.ModEq.symm
      exact (Nat.modEq_iff_dvd' hone).2 (dvd_refl (2 ^ (b + 1) - 1))
    have hadd := hperiod.add_left (2 ^ a)
    rw [Nat.mod_self, pow_zero]
    rw [pow_succ] at hadd
    simpa [pow_succ, mul_two, add_assoc] using hadd

public lemma lemma6_repeated_two_pow_collision_classify
    (n a b i j : ℕ) (hn : 0 < n) (han : a < n) (hbn : b < n)
    (hij : i < j) (hjn : j < n)
    (hmod : Nat.ModEq (2 ^ n - 1)
      (2 ^ a + 2 ^ b + 2 ^ b) (2 ^ i + 2 ^ j)) :
    (a = i ∧ (b + 1) % n = j) ∨ (a = j ∧ (b + 1) % n = i) := by
  have hcarry := lemma6_repeated_two_pow_modEq_cyclic n a b hn hbn
  have hpair : Nat.ModEq (2 ^ n - 1)
      (2 ^ a + 2 ^ ((b + 1) % n)) (2 ^ i + 2 ^ j) :=
    hcarry.symm.trans hmod
  have hcycn : (b + 1) % n < n := Nat.mod_lt _ hn
  by_cases heq : a = (b + 1) % n
  · rw [← heq] at hpair
    exact False.elim
      (lemma6_single_two_pow_not_modEq_pair_two_pow n ((a + 1) % n) i j
        (Nat.mod_lt _ hn) hij hjn
        ((lemma6_two_pow_add_self_modEq_cyclic n a hn han).symm.trans hpair))
  · exact lemma6_pair_two_pow_modEq_classify n a ((b + 1) % n) i j
      han hcycn heq hij hjn hpair

private def lemma6_finCyclicSucc {n : ℕ} (hn : 0 < n) (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩

private lemma lemma6_finCyclicSucc_injective {n : ℕ} (hn : 0 < n) :
    Function.Injective (lemma6_finCyclicSucc hn) := by
  intro i j h
  apply Fin.ext
  have hval : (i.val + 1) % n = (j.val + 1) % n :=
    congrArg Fin.val h
  by_cases hi : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt hi] at hval
    by_cases hj : j.val + 1 < n
    · rw [Nat.mod_eq_of_lt hj] at hval
      omega
    · have hjEq : j.val + 1 = n := by omega
      rw [hjEq, Nat.mod_self] at hval
      omega
  · have hiEq : i.val + 1 = n := by omega
    rw [hiEq, Nat.mod_self] at hval
    by_cases hj : j.val + 1 < n
    · rw [Nat.mod_eq_of_lt hj] at hval
      omega
    · omega

private lemma lemma6_repeated_two_pow_collision_fin_classify
    {n : ℕ} (hn : 0 < n) (a b x y : Fin n) (hab : a.val < b.val)
    (hmod : Nat.ModEq (2 ^ n - 1)
      (2 ^ x.val + 2 ^ y.val + 2 ^ y.val)
      (2 ^ a.val + 2 ^ b.val)) :
    (x = a ∧ lemma6_finCyclicSucc hn y = b) ∨
      (x = b ∧ lemma6_finCyclicSucc hn y = a) := by
  have h := lemma6_repeated_two_pow_collision_classify n x.val y.val a.val b.val
    hn x.isLt y.isLt hab b.isLt hmod
  rcases h with h | h
  · exact Or.inl ⟨Fin.ext h.1, Fin.ext h.2⟩
  · exact Or.inr ⟨Fin.ext h.1, Fin.ext h.2⟩

@[expose] public def lemma6_finPairGap {n : ℕ} (x y : Fin n) : ℕ :=
  (x.val - y.val) + (y.val - x.val)

@[expose] public def lemma6_finPairSupported
    {n : ℕ} (r : ℕ) (x y : Fin n) : Prop :=
  lemma6_finPairGap x y = r ∨ lemma6_finPairGap x y = n - r

private lemma lemma6_finCyclicSucc_eq_of_target_pos
    {n : ℕ} (hn : 0 < n) {y b : Fin n} (hb : 0 < b.val)
    (h : lemma6_finCyclicSucc hn y = b) :
    y.val + 1 = b.val := by
  have hval : (y.val + 1) % n = b.val := congrArg Fin.val h
  by_cases hy : y.val + 1 < n
  · simpa [Nat.mod_eq_of_lt hy] using hval
  · have hyEq : y.val + 1 = n := by omega
    rw [hyEq, Nat.mod_self] at hval
    omega

private lemma lemma6_finCyclicSucc_eq_zero_target
    {n : ℕ} (hn : 0 < n) {y a : Fin n} (ha : a.val = 0)
    (h : lemma6_finCyclicSucc hn y = a) :
    y.val + 1 = n := by
  have hval : (y.val + 1) % n = a.val := congrArg Fin.val h
  rw [ha] at hval
  by_cases hy : y.val + 1 < n
  · rw [Nat.mod_eq_of_lt hy] at hval
    omega
  · omega

private def lemma6_finRepeatedBucketCandidate {n : ℕ} (hn : 0 < n)
    (a b : Fin n) (p : Fin n × Fin n) : Prop :=
  (p.1 = a ∧ lemma6_finCyclicSucc hn p.2 = b) ∨
    (p.1 = b ∧ lemma6_finCyclicSucc hn p.2 = a)

private lemma lemma6_odd_repeated_bucket_cross_unsupported
    {n : ℕ} (hnodd : Odd n) (hn : 0 < n)
    (a b x y x' y' : Fin n) (r : ℕ)
    (hleft : a.val + 1 < b.val) (hright : b.val - a.val + 1 < n)
    (hfirst : x = a ∧ lemma6_finCyclicSucc hn y = b)
    (hsecond : x' = b ∧ lemma6_finCyclicSucc hn y' = a)
    (hsupport : lemma6_finPairSupported r x y)
    (hsupport' : lemma6_finPairSupported r x' y') :
    False := by
  rcases hfirst with ⟨hx, hy⟩
  rcases hsecond with ⟨hx', hy'⟩
  have hbpos : 0 < b.val := by omega
  have hyv : y.val + 1 = b.val :=
    lemma6_finCyclicSucc_eq_of_target_pos hn hbpos hy
  have hminus : b.val - a.val - 1 = r ∨
      b.val - a.val - 1 = n - r := by
    simp only [lemma6_finPairSupported, lemma6_finPairGap, hx] at hsupport
    rcases hsupport with hsupport | hsupport
    · left
      omega
    · right
      omega
  have hplus : b.val - a.val + 1 = r ∨
      b.val - a.val + 1 = n - r := by
    simp only [lemma6_finPairSupported, lemma6_finPairGap, hx'] at hsupport'
    by_cases ha0 : a.val = 0
    · have hy'v : y'.val + 1 = n :=
        lemma6_finCyclicSucc_eq_zero_target hn ha0 hy'
      rcases hsupport' with hsupport' | hsupport'
      · right
        omega
      · left
        omega
    · have hapos : 0 < a.val := Nat.pos_of_ne_zero ha0
      have hy'v : y'.val + 1 = a.val :=
        lemma6_finCyclicSucc_eq_of_target_pos hn hapos hy'
      rcases hsupport' with hsupport' | hsupport'
      · left
        omega
      · right
        omega
  exact lemma6_odd_not_both_cyclic_pair_differences n (b.val - a.val) r
    hnodd (by omega) (by omega) hminus hplus

private lemma lemma6_odd_supported_repeated_bucket_unique
    {n : ℕ} (hnodd : Odd n) (hn : 0 < n) (a b : Fin n) (r : ℕ)
    (hleft : a.val + 1 < b.val) (hright : b.val - a.val + 1 < n)
    {p q : Fin n × Fin n}
    (hpCandidate : lemma6_finRepeatedBucketCandidate hn a b p)
    (hqCandidate : lemma6_finRepeatedBucketCandidate hn a b q)
    (hpSupport : lemma6_finPairSupported r p.1 p.2)
    (hqSupport : lemma6_finPairSupported r q.1 q.2) :
    p = q := by
  rcases p with ⟨x, y⟩
  rcases q with ⟨x', y'⟩
  rcases hpCandidate with hpFirst | hpSecond
  · rcases hqCandidate with hqFirst | hqSecond
    · exact Prod.ext (hpFirst.1.trans hqFirst.1.symm)
        (lemma6_finCyclicSucc_injective hn (hpFirst.2.trans hqFirst.2.symm))
    · exact False.elim
        (lemma6_odd_repeated_bucket_cross_unsupported hnodd hn a b x y x' y' r
          hleft hright hpFirst hqSecond hpSupport hqSupport)
  · rcases hqCandidate with hqFirst | hqSecond
    · exact False.elim
        (lemma6_odd_repeated_bucket_cross_unsupported hnodd hn a b x' y' x y r
          hleft hright hqFirst hpSecond hqSupport hpSupport)
    · exact Prod.ext (hpSecond.1.trans hqSecond.1.symm)
        (lemma6_finCyclicSucc_injective hn (hpSecond.2.trans hqSecond.2.symm))

private noncomputable def lemma6_finSupportedRepeatedExponentCollisions
    {n : ℕ} (a b : Fin n) (r : ℕ) : Finset (Fin n × Fin n) := by
  classical
  exact Finset.univ.filter fun p =>
    Nat.ModEq (2 ^ n - 1)
      (2 ^ p.1.val + 2 ^ p.2.val + 2 ^ p.2.val)
      (2 ^ a.val + 2 ^ b.val) ∧
    lemma6_finPairSupported r p.1 p.2

private lemma lemma6_odd_finSupportedRepeatedExponentCollisions_card_le_one
    {n : ℕ} (hnodd : Odd n) (hn : 0 < n) (a b : Fin n) (r : ℕ)
    (hleft : a.val + 1 < b.val) (hright : b.val - a.val + 1 < n) :
    (lemma6_finSupportedRepeatedExponentCollisions a b r).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro p hp q hq
  simp only [lemma6_finSupportedRepeatedExponentCollisions, Finset.mem_filter,
    Finset.mem_univ, true_and] at hp hq
  have hpCandidate :=
    lemma6_repeated_two_pow_collision_fin_classify hn a b p.1 p.2 (by omega) hp.1
  have hqCandidate :=
    lemma6_repeated_two_pow_collision_fin_classify hn a b q.1 q.2 (by omega) hq.1
  exact lemma6_odd_supported_repeated_bucket_unique hnodd hn a b r hleft hright
    hpCandidate hqCandidate hp.2 hq.2


private lemma lemma6_finPairSupported_of_sub_eq
    {n : ℕ} (a b x y : Fin n)
    (hab : a ≠ b) (hxy : x ≠ y) (hsub : b - a = y - x) :
    lemma6_finPairSupported (lemma6_finPairGap a b) x y := by
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with hablt | hbalt <;>
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hxy) with hxylt | hyxlt
  · left
    simp only [lemma6_finPairGap]
    have hv := congrArg Fin.val hsub
    rw [Fin.sub_val_of_le (by omega), Fin.sub_val_of_le (by omega)] at hv
    omega
  · right
    simp only [lemma6_finPairGap]
    have hv := congrArg Fin.val hsub
    rw [Fin.sub_val_of_le (by omega), Fin.val_sub] at hv
    rw [Nat.mod_eq_of_lt (by omega)] at hv
    omega
  · right
    simp only [lemma6_finPairGap]
    have hv := congrArg Fin.val hsub
    rw [Fin.val_sub, Fin.sub_val_of_le (by omega)] at hv
    rw [Nat.mod_eq_of_lt (by omega)] at hv
    omega
  · left
    simp only [lemma6_finPairGap]
    have hv := congrArg Fin.val hsub
    rw [Fin.val_sub, Fin.val_sub] at hv
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hv
    omega

private lemma lemma6_finPairSupported_symm
    {n r : ℕ} {x y : Fin n} (h : lemma6_finPairSupported r x y) :
    lemma6_finPairSupported r y x := by
  simpa only [lemma6_finPairSupported, lemma6_finPairGap, add_comm] using h


private def lemma6_finCyclicAdd {n : ℕ} (hn : 0 < n) (k : ℕ) (i : Fin n) : Fin n :=
  ⟨(i.val + k) % n, Nat.mod_lt _ hn⟩

private lemma lemma6_finCyclicAdd_injective {n : ℕ} (hn : 0 < n) (k : ℕ) :
    Function.Injective (lemma6_finCyclicAdd hn k) := by
  intro i j h
  apply Fin.ext
  have hmod : Nat.ModEq n (i.val + k) (j.val + k) := by
    change (i.val + k) % n = (j.val + k) % n
    exact congrArg Fin.val h
  have hij : Nat.ModEq n i.val j.val :=
    Nat.ModEq.add_right_cancel (Nat.ModEq.refl k) hmod
  exact hij.eq_of_lt_of_lt i.isLt j.isLt

public lemma lemma6_two_pow_modEq_cyclic
    (n k : ℕ) :
    Nat.ModEq (2 ^ n - 1) (2 ^ k) (2 ^ (k % n)) := by
  have hone : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hperiod : Nat.ModEq (2 ^ n - 1) (2 ^ n) 1 := by
    apply Nat.ModEq.symm
    exact (Nat.modEq_iff_dvd' hone).2 (dvd_refl (2 ^ n - 1))
  have hpow := hperiod.pow (k / n)
  have hmul := hpow.mul (Nat.ModEq.refl (2 ^ (k % n)))
  have hk : k % n + n * (k / n) = k := Nat.mod_add_div k n
  convert hmul using 1
  · rw [← pow_mul, ← pow_add]
    congr 1
    omega
  · simp

private lemma lemma6_pair_two_pow_mul_modEq_cyclic
    (n a b k : ℕ) :
    Nat.ModEq (2 ^ n - 1)
      ((2 ^ a + 2 ^ b) * 2 ^ k)
      (2 ^ ((a + k) % n) + 2 ^ ((b + k) % n)) := by
  have ha := lemma6_two_pow_modEq_cyclic n (a + k)
  have hb := lemma6_two_pow_modEq_cyclic n (b + k)
  have hadd := ha.add hb
  convert hadd using 1
  · simp [pow_add, add_mul]


private lemma lemma6_finCyclicAdd_eq_add
    {n : ℕ} (hn : 0 < n) (k : ℕ) (i : Fin n) :
    lemma6_finCyclicAdd hn k i = i + lemma6_finCyclicAdd hn k ⟨0, hn⟩ := by
  apply Fin.ext
  simp only [lemma6_finCyclicAdd, Fin.val_add]
  simpa only [Nat.zero_add] using (Nat.add_mod_mod i.val k n).symm

private lemma lemma6_fin_sub_eq_of_cyclicAdd_eq
    {n : ℕ} (hn : 0 < n) (a b x y : Fin n) (s t : ℕ)
    (hx : lemma6_finCyclicAdd hn t x = lemma6_finCyclicAdd hn s a)
    (hy : lemma6_finCyclicAdd hn t y = lemma6_finCyclicAdd hn s b) :
    b - a = y - x := by
  let : NeZero n := ⟨hn.ne'⟩
  have hx' : x + lemma6_finCyclicAdd hn t ⟨0, hn⟩ =
      a + lemma6_finCyclicAdd hn s ⟨0, hn⟩ := by
    simpa only [← lemma6_finCyclicAdd_eq_add hn] using hx
  have hy' : y + lemma6_finCyclicAdd hn t ⟨0, hn⟩ =
      b + lemma6_finCyclicAdd hn s ⟨0, hn⟩ := by
    simpa only [← lemma6_finCyclicAdd_eq_add hn] using hy
  have h := congrArg₂ (fun p q : Fin n => p - q) hy'.symm hx'.symm
  simpa only [add_sub_add_right_eq_sub] using h


public theorem lemma6_finPairSupported_of_scaled_pair_modEq
    {n : ℕ} (hn : 0 < n) (a b x y : Fin n)
    (hab : a ≠ b) (hxy : x ≠ y) (s t : ℕ)
    (hmod : Nat.ModEq (2 ^ n - 1)
      ((2 ^ a.val + 2 ^ b.val) * 2 ^ s)
      ((2 ^ x.val + 2 ^ y.val) * 2 ^ t)) :
    lemma6_finPairSupported (lemma6_finPairGap a b) x y := by
  let as : Fin n := lemma6_finCyclicAdd hn s a
  let bs : Fin n := lemma6_finCyclicAdd hn s b
  let xt : Fin n := lemma6_finCyclicAdd hn t x
  let yt : Fin n := lemma6_finCyclicAdd hn t y
  have habs : as ≠ bs := fun h => hab (lemma6_finCyclicAdd_injective hn s h)
  have hxyt : xt ≠ yt := fun h => hxy (lemma6_finCyclicAdd_injective hn t h)
  have hseed := lemma6_pair_two_pow_mul_modEq_cyclic n a.val b.val s
  have htarget := lemma6_pair_two_pow_mul_modEq_cyclic n x.val y.val t
  change Nat.ModEq (2 ^ n - 1)
      ((2 ^ a.val + 2 ^ b.val) * 2 ^ s)
      (2 ^ as.val + 2 ^ bs.val) at hseed
  change Nat.ModEq (2 ^ n - 1)
      ((2 ^ x.val + 2 ^ y.val) * 2 ^ t)
      (2 ^ xt.val + 2 ^ yt.val) at htarget
  have hshift : Nat.ModEq (2 ^ n - 1)
      (2 ^ xt.val + 2 ^ yt.val) (2 ^ as.val + 2 ^ bs.val) :=
    htarget.symm.trans (hmod.symm.trans hseed)
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne habs) with hasb | hbsa
  · have hc := lemma6_pair_two_pow_modEq_classify n xt.val yt.val as.val bs.val
      xt.isLt yt.isLt (Fin.val_ne_of_ne hxyt) hasb bs.isLt hshift
    rcases hc with hc | hc
    · have hxEq : xt = as := Fin.ext hc.1
      have hyEq : yt = bs := Fin.ext hc.2
      exact lemma6_finPairSupported_of_sub_eq a b x y hab hxy
        (lemma6_fin_sub_eq_of_cyclicAdd_eq hn a b x y s t hxEq hyEq)
    · have hxEq : xt = bs := Fin.ext hc.1
      have hyEq : yt = as := Fin.ext hc.2
      exact lemma6_finPairSupported_symm
        (lemma6_finPairSupported_of_sub_eq a b y x hab hxy.symm
          (lemma6_fin_sub_eq_of_cyclicAdd_eq hn a b y x s t hyEq hxEq))
  · have hshift' : Nat.ModEq (2 ^ n - 1)
        (2 ^ xt.val + 2 ^ yt.val) (2 ^ bs.val + 2 ^ as.val) := by
      simpa only [add_comm] using hshift
    have hc := lemma6_pair_two_pow_modEq_classify n xt.val yt.val bs.val as.val
      xt.isLt yt.isLt (Fin.val_ne_of_ne hxyt) hbsa as.isLt hshift'
    rcases hc with hc | hc
    · have hxEq : xt = bs := Fin.ext hc.1
      have hyEq : yt = as := Fin.ext hc.2
      exact lemma6_finPairSupported_symm
        (lemma6_finPairSupported_of_sub_eq a b y x hab hxy.symm
          (lemma6_fin_sub_eq_of_cyclicAdd_eq hn a b y x s t hyEq hxEq))
    · have hxEq : xt = as := Fin.ext hc.1
      have hyEq : yt = bs := Fin.ext hc.2
      exact lemma6_finPairSupported_of_sub_eq a b x y hab hxy
        (lemma6_fin_sub_eq_of_cyclicAdd_eq hn a b x y s t hxEq hyEq)


public lemma lemma6_finPairGap_pos_of_ne
    {n : ℕ} {a b : Fin n} (hab : a ≠ b) :
    0 < lemma6_finPairGap a b := by
  simp only [lemma6_finPairGap]
  have hv : a.val ≠ b.val := Fin.val_ne_of_ne hab
  omega

public lemma lemma6_finPairGap_lt
    {n : ℕ} (a b : Fin n) :
    lemma6_finPairGap a b < n := by
  simp only [lemma6_finPairGap]
  omega

private theorem lemma6_finPairSupported_of_primitive_pair_power_eq
    {K : Type*} [Field K] {n : ℕ} (hn : 0 < n)
    (lambda mu : K) (hlambda : lambda ≠ 0) (hmu : mu ≠ 0)
    (hlambda_order : orderOf (Units.mk0 lambda hlambda) = 2 ^ n - 1)
    (a b x y : Fin n) (hab : a ≠ b) (hxy : x ≠ y) (p q : Fin n)
    (hseed : lambda ^ (2 ^ a.val + 2 ^ b.val) = mu ^ (2 ^ p.val))
    (hpair : lambda ^ (2 ^ x.val + 2 ^ y.val) = mu ^ (2 ^ q.val)) :
    lemma6_finPairSupported (lemma6_finPairGap a b) x y := by
  let lambdaUnit : Kˣ := Units.mk0 lambda hlambda
  let muUnit : Kˣ := Units.mk0 mu hmu
  have hseedUnit :
      lambdaUnit ^ (2 ^ a.val + 2 ^ b.val) = muUnit ^ (2 ^ p.val) := by
    apply Units.ext
    simpa only [lambdaUnit, muUnit, Units.val_pow_eq_pow_val,
      Units.val_mk0] using hseed
  have hpairUnit :
      lambdaUnit ^ (2 ^ x.val + 2 ^ y.val) = muUnit ^ (2 ^ q.val) := by
    apply Units.ext
    simpa only [lambdaUnit, muUnit, Units.val_pow_eq_pow_val,
      Units.val_mk0] using hpair
  have hlambdaEq :
      lambdaUnit ^ ((2 ^ a.val + 2 ^ b.val) * 2 ^ q.val) =
        lambdaUnit ^ ((2 ^ x.val + 2 ^ y.val) * 2 ^ p.val) := by
    calc
      lambdaUnit ^ ((2 ^ a.val + 2 ^ b.val) * 2 ^ q.val) =
          (lambdaUnit ^ (2 ^ a.val + 2 ^ b.val)) ^ (2 ^ q.val) := by
            rw [pow_mul]
      _ = (muUnit ^ (2 ^ p.val)) ^ (2 ^ q.val) := by rw [hseedUnit]
      _ = (muUnit ^ (2 ^ q.val)) ^ (2 ^ p.val) := by
        calc
          (muUnit ^ (2 ^ p.val)) ^ (2 ^ q.val) =
              muUnit ^ (2 ^ p.val * 2 ^ q.val) :=
                (pow_mul muUnit (2 ^ p.val) (2 ^ q.val)).symm
          _ = muUnit ^ (2 ^ q.val * 2 ^ p.val) := by rw [mul_comm]
          _ = (muUnit ^ (2 ^ q.val)) ^ (2 ^ p.val) :=
                pow_mul muUnit (2 ^ q.val) (2 ^ p.val)
      _ = (lambdaUnit ^ (2 ^ x.val + 2 ^ y.val)) ^ (2 ^ p.val) := by
        rw [hpairUnit]
      _ = lambdaUnit ^ ((2 ^ x.val + 2 ^ y.val) * 2 ^ p.val) := by
        rw [pow_mul]
  have hmod : Nat.ModEq (2 ^ n - 1)
      ((2 ^ a.val + 2 ^ b.val) * 2 ^ q.val)
      ((2 ^ x.val + 2 ^ y.val) * 2 ^ p.val) := by
    have h := pow_eq_pow_iff_modEq.mp hlambdaEq
    simpa only [lambdaUnit, hlambda_order] using h
  exact lemma6_finPairSupported_of_scaled_pair_modEq hn a b x y hab hxy q.val p.val hmod

public theorem lemma6_finPairSupported_of_primitive_pair_eigenvalue_eq
    {K : Type*} [Field K] {n : ℕ} (hn : 0 < n)
    (lambda mu : K) (hlambda : lambda ≠ 0) (hmu : mu ≠ 0)
    (hlambda_order : orderOf (Units.mk0 lambda hlambda) = 2 ^ n - 1)
    (a b x y : Fin n) (hab : a ≠ b) (hxy : x ≠ y) (p q : Fin n)
    (hseed : lambda ^ (2 ^ a.val) * lambda ^ (2 ^ b.val) =
      mu ^ (2 ^ p.val))
    (hpair : lambda ^ (2 ^ x.val) * lambda ^ (2 ^ y.val) =
      mu ^ (2 ^ q.val)) :
    lemma6_finPairSupported (lemma6_finPairGap a b) x y := by
  apply lemma6_finPairSupported_of_primitive_pair_power_eq hn lambda mu hlambda hmu
    hlambda_order a b x y hab hxy p q
  · simpa only [pow_add] using hseed
  · simpa only [pow_add] using hpair


public theorem lemma6_scalarExtendedBilinear_span
    {K V W : Type*} [Field K] [Algebra (ZMod 2) K]
    [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    (B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] W)
    (BK : (K ⊗[ZMod 2] V) →ₗ[K]
      (K ⊗[ZMod 2] V) →ₗ[K] (K ⊗[ZMod 2] W))
    (hBK_tmul : ∀ v w : V,
      BK ((1 : K) ⊗ₜ[ZMod 2] v) ((1 : K) ⊗ₜ[ZMod 2] w) =
        (1 : K) ⊗ₜ[ZMod 2] B v w)
    (hspan : Submodule.span (ZMod 2)
      (Set.range fun p : V × V => B p.1 p.2) = ⊤) :
    Submodule.span K
      (Set.range fun p : (K ⊗[ZMod 2] V) × (K ⊗[ZMod 2] V) =>
        BK p.1 p.2) = ⊤ := by
  let S : Submodule K (K ⊗[ZMod 2] W) :=
    Submodule.span K
      (Set.range fun p : (K ⊗[ZMod 2] V) × (K ⊗[ZMod 2] V) =>
        BK p.1 p.2)
  change S = ⊤
  have hall : ∀ z : K ⊗[ZMod 2] W, z ∈ S := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact S.zero_mem
    | add x y hx hy => exact S.add_mem hx hy
    | tmul a w =>
        have hw : w ∈ Submodule.span (ZMod 2)
            (Set.range fun p : V × V => B p.1 p.2) := by
          rw [hspan]
          trivial
        refine Submodule.span_induction
          (p := fun z _ => a ⊗ₜ[ZMod 2] z ∈ S) ?_ ?_ ?_ ?_ hw
        · rintro _ ⟨⟨x, y⟩, rfl⟩
          apply Submodule.subset_span
          refine ⟨⟨a ⊗ₜ[ZMod 2] x, (1 : K) ⊗ₜ[ZMod 2] y⟩, ?_⟩
          have ha : a ⊗ₜ[ZMod 2] x =
              a • ((1 : K) ⊗ₜ[ZMod 2] x) := by
            rw [TensorProduct.smul_tmul']
            simp
          rw [ha]
          change BK (a • ((1 : K) ⊗ₜ[ZMod 2] x))
            ((1 : K) ⊗ₜ[ZMod 2] y) = a ⊗ₜ[ZMod 2] B x y
          rw [map_smul, LinearMap.smul_apply, hBK_tmul]
          rw [TensorProduct.smul_tmul']
          simp
        · simpa only [TensorProduct.tmul_zero] using S.zero_mem
        · intro x y _ _ hx hy
          simpa only [TensorProduct.tmul_add] using S.add_mem hx hy
        · intro c x _ hx
          have h := S.smul_mem (algebraMap (ZMod 2) K c) hx
          simpa only [TensorProduct.tmul_smul, Algebra.smul_def,
            TensorProduct.smul_tmul', Algebra.algebraMap_self_apply] using h
  apply top_unique
  intro z _
  exact hall z

public theorem lemma6_scalarExtendedBilinear_span₂
    {K E F W : Type*} [Field K] [Algebra (ZMod 2) K]
    [AddCommGroup E] [Module (ZMod 2) E]
    [AddCommGroup F] [Module (ZMod 2) F]
    [AddCommGroup W] [Module (ZMod 2) W]
    (B : E →ₗ[ZMod 2] F →ₗ[ZMod 2] W)
    (BK : (K ⊗[ZMod 2] E) →ₗ[K]
      (K ⊗[ZMod 2] F) →ₗ[K] (K ⊗[ZMod 2] W))
    (hBK_tmul : ∀ e : E, ∀ f : F,
      BK ((1 : K) ⊗ₜ[ZMod 2] e) ((1 : K) ⊗ₜ[ZMod 2] f) =
        (1 : K) ⊗ₜ[ZMod 2] B e f)
    (hspan : Submodule.span (ZMod 2)
      (Set.range fun p : E × F => B p.1 p.2) = ⊤) :
    Submodule.span K
      (Set.range fun p : (K ⊗[ZMod 2] E) × (K ⊗[ZMod 2] F) =>
        BK p.1 p.2) = ⊤ := by
  let S : Submodule K (K ⊗[ZMod 2] W) :=
    Submodule.span K
      (Set.range fun p : (K ⊗[ZMod 2] E) × (K ⊗[ZMod 2] F) =>
        BK p.1 p.2)
  change S = ⊤
  have hall : ∀ z : K ⊗[ZMod 2] W, z ∈ S := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact S.zero_mem
    | add x y hx hy => exact S.add_mem hx hy
    | tmul a w =>
        have hw : w ∈ Submodule.span (ZMod 2)
            (Set.range fun p : E × F => B p.1 p.2) := by
          rw [hspan]
          trivial
        refine Submodule.span_induction
          (p := fun z _ => a ⊗ₜ[ZMod 2] z ∈ S) ?_ ?_ ?_ ?_ hw
        · rintro _ ⟨⟨e, f⟩, rfl⟩
          apply Submodule.subset_span
          refine ⟨⟨a ⊗ₜ[ZMod 2] e, (1 : K) ⊗ₜ[ZMod 2] f⟩, ?_⟩
          have ha : a ⊗ₜ[ZMod 2] e =
              a • ((1 : K) ⊗ₜ[ZMod 2] e) := by
            rw [TensorProduct.smul_tmul']
            simp
          rw [ha]
          change BK (a • ((1 : K) ⊗ₜ[ZMod 2] e))
            ((1 : K) ⊗ₜ[ZMod 2] f) = a ⊗ₜ[ZMod 2] B e f
          rw [map_smul, LinearMap.smul_apply, hBK_tmul]
          rw [TensorProduct.smul_tmul']
          simp
        · simpa only [TensorProduct.tmul_zero] using S.zero_mem
        · intro x y _ _ hx hy
          simpa only [TensorProduct.tmul_add] using S.add_mem hx hy
        · intro c x _ hx
          have h := S.smul_mem (algebraMap (ZMod 2) K c) hx
          simpa only [TensorProduct.tmul_smul, Algebra.smul_def,
            TensorProduct.smul_tmul', Algebra.algebraMap_self_apply] using h
  apply top_unique
  intro z _
  exact hall z

public theorem lemma6_exists_basis_pair_ne_zero_of_span_eq_top
    {K E F ι : Type*} [Field K]
    [AddCommGroup E] [Module K E]
    [AddCommGroup F] [Module K F] [Nontrivial F]
    [Fintype ι] [DecidableEq ι]
    (B : E →ₗ[K] E →ₗ[K] F) (u : Module.Basis ι K E)
    (hspan : Submodule.span K
      (Set.range fun p : E × E => B p.1 p.2) = ⊤) :
    ∃ i j : ι, B (u i) (u j) ≠ 0 := by
  classical
  by_contra h
  push Not at h
  have hBzero (x y : E) : B x y = 0 := by
    let xs := ∑ i : ι, (u.repr x i) • u i
    let ys := ∑ j : ι, (u.repr y j) • u j
    have hx : xs = x := by simp [xs]
    have hy : ys = y := by simp [ys]
    rw [← hx, ← hy]
    simp only [xs, ys, map_sum, LinearMap.sum_apply, map_smul,
      LinearMap.smul_apply]
    simp [h]
  have hspanbot : Submodule.span K
      (Set.range fun p : E × E => B p.1 p.2) = ⊥ := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro z ⟨p, rfl⟩
      simp [hBzero]
    · exact bot_le
  have htopbot : (⊤ : Submodule K F) = ⊥ := hspan.symm.trans hspanbot
  exact (top_ne_bot : (⊤ : Submodule K F) ≠ ⊥) htopbot

public theorem lemma6_exists_basis_pair_ne_zero_of_span_eq_top₂
    {K E F W ι κ : Type*} [Field K]
    [AddCommGroup E] [Module K E]
    [AddCommGroup F] [Module K F]
    [AddCommGroup W] [Module K W] [Nontrivial W]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (B : E →ₗ[K] F →ₗ[K] W)
    (u : Module.Basis ι K E) (v : Module.Basis κ K F)
    (hspan : Submodule.span K
      (Set.range fun p : E × F => B p.1 p.2) = ⊤) :
    ∃ i : ι, ∃ j : κ, B (u i) (v j) ≠ 0 := by
  classical
  by_contra h
  push Not at h
  have hBzero (x : E) (y : F) : B x y = 0 := by
    let xs := ∑ i : ι, (u.repr x i) • u i
    let ys := ∑ j : κ, (v.repr y j) • v j
    have hx : xs = x := by simp [xs]
    have hy : ys = y := by simp [ys]
    rw [← hx, ← hy]
    simp only [xs, ys, map_sum, LinearMap.sum_apply, map_smul,
      LinearMap.smul_apply]
    simp [h]
  have hspanbot : Submodule.span K
      (Set.range fun p : E × F => B p.1 p.2) = ⊥ := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro z ⟨p, rfl⟩
      simp [hBzero]
    · exact bot_le
  have htopbot : (⊤ : Submodule K W) = ⊥ := hspan.symm.trans hspanbot
  exact (top_ne_bot : (⊤ : Submodule K W) ≠ ⊥) htopbot

public theorem lemma6_irreducible_of_transitive
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (T : V ≃ₗ[F] V)
    (htrans : ∀ x : V, x ≠ 0 → ∀ y : V, y ≠ 0 →
      ∃ k : ℕ, (T ^ k) x = y) :
    ∀ W : Submodule F V,
      (∀ v : V, v ∈ W → T v ∈ W) → W = ⊥ ∨ W = ⊤ := by
  intro W hW
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  · right
    obtain ⟨x, hxW, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    apply top_unique
    intro y _hy
    by_cases hy0 : y = 0
    · simp [hy0]
    obtain ⟨k, hk⟩ := htrans x hx0 y hy0
    have hxpow : ∀ j : ℕ, (T ^ j) x ∈ W := by
      intro j
      induction j with
      | zero => simpa using hxW
      | succ j ih =>
          simpa only [pow_succ', LinearEquiv.mul_apply] using hW _ ih
    rw [← hk]
    exact hxpow k
set_option backward.isDefEq.respectTransparency false in
public theorem lemma6_diagonal_eigenvalue_eq_basis_eigenvalue
    {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Fintype ι] [DecidableEq ι]
    (T : V →ₗ[K] V) (b : Module.Basis ι K V) (mu : ι → K)
    (hb : ∀ i, T (b i) = mu i • b i)
    (z : V) (nu : K) (hz : T z = nu • z) (hz0 : z ≠ 0) :
    ∃ i, nu = mu i := by
  have hrepr_ne : b.repr z ≠ 0 := by
    intro hzero
    apply hz0
    apply b.repr.injective
    simpa using hzero
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hrepr_ne
  refine ⟨i, ?_⟩
  have hT_expand :
      T z = ∑ j : ι, (b.repr z j * mu j) • b j := by
    conv_lhs => rw [← b.sum_repr z]
    simp only [map_sum, map_smul, hb, smul_smul]
  have hnu_expand :
      nu • z = ∑ j : ι, (nu * b.repr z j) • b j := by
    conv_lhs => rw [← b.sum_repr z]
    simp only [Finset.smul_sum, smul_smul]
  have hsum :
      (∑ j : ι, (b.repr z j * mu j) • b j) =
        ∑ j : ι, (nu * b.repr z j) • b j := by
    rw [← hT_expand, ← hnu_expand]
    exact hz
  have hcoord_sum (a : ι → K) :
      b.coord i (∑ j : ι, a j • b j) = a i := by
    rw [map_sum]
    simp only [map_smul, Module.Basis.coord_apply,
      Module.Basis.repr_self]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _hj hji
      rw [Finsupp.single_apply]
      simp [hji]
    · simp
  have hcoord := congrArg (b.coord i) hsum
  rw [hcoord_sum, hcoord_sum] at hcoord
  apply (mul_left_cancel₀ hi)
  simpa [mul_comm] using hcoord.symm


set_option backward.isDefEq.respectTransparency false in
public theorem lemma6_nonzero_equivariant_bilinear_basis_value_spectrum
    {K E F ι κ : Type*} [Field K]
    [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]
    [Fintype κ] [DecidableEq κ]
    (T : E ≃ₗ[K] E) (S : F ≃ₗ[K] F)
    (B : E →ₗ[K] E →ₗ[K] F)
    (hB : ∀ x y : E, B (T x) (T y) = S (B x y))
    (u : Module.Basis ι K E) (mu : ι → K)
    (hu : ∀ i, T (u i) = mu i • u i)
    (b : Module.Basis κ K F) (nu : κ → K)
    (hb : ∀ s, S (b s) = nu s • b s)
    (i j : ι) (hij : B (u i) (u j) ≠ 0) :
    ∃ s, mu i * mu j = nu s := by
  apply lemma6_diagonal_eigenvalue_eq_basis_eigenvalue
    S.toLinearMap b nu hb (B (u i) (u j)) (mu i * mu j)
  · calc
      S (B (u i) (u j)) = B (T (u i)) (T (u j)) := (hB (u i) (u j)).symm
      _ = B (mu i • u i) (mu j • u j) := by rw [hu, hu]
      _ = (mu i * mu j) • B (u i) (u j) := by
        simp [map_smul, smul_smul, mul_comm]
  · exact hij

/-- A nonzero value of an equivariant bilinear map with two different source
actions has eigenvalue equal to one of the target diagonal eigenvalues. -/
public theorem lemma6_nonzero_equivariant_bilinear_basis_value_spectrum₂
    {K E F W ι κ τ : Type*} [Field K]
    [AddCommGroup E] [Module K E]
    [AddCommGroup F] [Module K F]
    [AddCommGroup W] [Module K W]
    [Fintype τ] [DecidableEq τ]
    (T : E ≃ₗ[K] E) (S : F ≃ₗ[K] F) (R : W ≃ₗ[K] W)
    (B : E →ₗ[K] F →ₗ[K] W)
    (hB : ∀ x y, B (T x) (S y) = R (B x y))
    (u : Module.Basis ι K E) (mu : ι → K)
    (hu : ∀ i, T (u i) = mu i • u i)
    (v : Module.Basis κ K F) (nu : κ → K)
    (hv : ∀ j, S (v j) = nu j • v j)
    (b : Module.Basis τ K W) (rho : τ → K)
    (hb : ∀ t, R (b t) = rho t • b t)
    (i : ι) (j : κ) (hij : B (u i) (v j) ≠ 0) :
    ∃ t, mu i * nu j = rho t := by
  apply lemma6_diagonal_eigenvalue_eq_basis_eigenvalue
    R.toLinearMap b rho hb (B (u i) (v j)) (mu i * nu j)
  · calc
      R (B (u i) (v j)) = B (T (u i)) (S (v j)) :=
        (hB (u i) (v j)).symm
      _ = B (mu i • u i) (nu j • v j) := by rw [hu, hv]
      _ = (mu i * nu j) • B (u i) (v j) := by
        simp [map_smul, smul_smul, mul_comm]
  · exact hij


public theorem lemma6_coordinate_unit_order
    {R K V : Type*} [Field R] [Field K] [Finite K] [Algebra R K]
    [AddCommGroup V] [Module R V] [Finite V]
    (T : V ≃ₗ[R] V) (coordinates : K ≃ₗ[R] V)
    (lambda : K) (hlambda : lambda ≠ 0)
    (hcoordinates : ∀ alpha : K,
      T (coordinates alpha) = coordinates (lambda * alpha)) :
    orderOf T = orderOf (Units.mk0 lambda hlambda) := by
  let lambdaUnit : Kˣ := Units.mk0 lambda hlambda
  have hpow (k : ℕ) (alpha : K) :
      (T ^ k) (coordinates alpha) =
        coordinates ((lambdaUnit ^ k : Kˣ) * alpha) := by
    induction k generalizing alpha with
    | zero => simp
    | succ k ih =>
        rw [pow_succ, LinearEquiv.mul_apply, hcoordinates, ih]
        simp [lambdaUnit, pow_succ, mul_assoc]
  have hiff (k : ℕ) : T ^ k = 1 ↔ lambdaUnit ^ k = 1 := by
    constructor
    · intro hk
      apply Units.ext
      have h := congrArg (fun f : V ≃ₗ[R] V => f (coordinates 1)) hk
      change (T ^ k) (coordinates 1) = coordinates 1 at h
      rw [hpow] at h
      simpa using coordinates.injective h
    · intro hk
      apply LinearEquiv.ext
      intro v
      obtain ⟨alpha, rfl⟩ := coordinates.surjective v
      rw [hpow, hk]
      simp
  apply Nat.dvd_antisymm
  · apply orderOf_dvd_of_pow_eq_one
    exact (hiff (orderOf lambdaUnit)).2 (pow_orderOf_eq_one lambdaUnit)
  · apply orderOf_dvd_of_pow_eq_one
    exact (hiff (orderOf T)).1 (pow_orderOf_eq_one T)

public noncomputable def lemma6_scalarExtendBilinear
    {K V W U : Type*} [Field K]
    [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    [AddCommGroup U] [Module (ZMod 2) U]
    [Algebra (ZMod 2) K]
    (C : V →ₗ[ZMod 2] W →ₗ[ZMod 2] U) :
    (K ⊗[ZMod 2] V) →ₗ[K]
      (K ⊗[ZMod 2] W) →ₗ[K] (K ⊗[ZMod 2] U) :=
  (LinearMap.tensorProduct (ZMod 2) K W U).comp (C.baseChange K)

set_option maxHeartbeats 800000 in
public theorem lemma6_scalarExtendBilinear_tmul
    {K V W U : Type*} [Field K]
    [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    [AddCommGroup U] [Module (ZMod 2) U]
    [Algebra (ZMod 2) K]
    (C : V →ₗ[ZMod 2] W →ₗ[ZMod 2] U)
    (v : V) (w : W) :
    lemma6_scalarExtendBilinear C
        ((1 : K) ⊗ₜ[ZMod 2] v) ((1 : K) ⊗ₜ[ZMod 2] w) =
      (1 : K) ⊗ₜ[ZMod 2] C v w := by
  simp [lemma6_scalarExtendBilinear, LinearMap.tensorProduct,
    LinearMap.baseChange_tmul]

set_option maxHeartbeats 800000 in
/-- Scalar extension preserves alternation of a binary bilinear map. -/
public theorem lemma6_scalarExtendBilinear_self
    {K V W : Type*} [Field K]
    [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    [Algebra (ZMod 2) K]
    (B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] W)
    (hB_self : ∀ v : V, B v v = 0) :
    ∀ x : K ⊗[ZMod 2] V, lemma6_scalarExtendBilinear B x x = 0 := by
  have hadd_self (z : W) : z + z = 0 := by
    nth_rw 2 [← ZModModule.neg_eq_self z]
    exact add_neg_cancel z
  have hB_symm (v w : V) : B v w = B w v := by
    have hsum : B v w + B w v = 0 := by
      have h := hB_self (v + w)
      simp only [map_add, LinearMap.add_apply] at h
      rw [hB_self, hB_self] at h
      simpa only [zero_add, add_zero, add_assoc, add_comm] using h
    calc
      B v w = B v w + (B w v + B w v) := by
        rw [hadd_self, add_zero]
      _ = (B v w + B w v) + B w v := by abel
      _ = B w v := by rw [hsum, zero_add]
  have hBK_symm (x y : K ⊗[ZMod 2] V) :
      lemma6_scalarExtendBilinear B x y =
        lemma6_scalarExtendBilinear B y x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a v =>
        induction y using TensorProduct.induction_on with
        | zero => simp
        | tmul b w =>
            have ha : a ⊗ₜ[ZMod 2] v =
                a • ((1 : K) ⊗ₜ[ZMod 2] v) := by
              rw [TensorProduct.smul_tmul']
              simp
            have hb : b ⊗ₜ[ZMod 2] w =
                b • ((1 : K) ⊗ₜ[ZMod 2] w) := by
              rw [TensorProduct.smul_tmul']
              simp
            rw [ha, hb, map_smul, LinearMap.map_smul₂,
              map_smul, LinearMap.map_smul₂,
              lemma6_scalarExtendBilinear_tmul,
              lemma6_scalarExtendBilinear_tmul, hB_symm]
            simp [smul_smul, mul_comm]
        | add y z hy hz =>
            simp only [map_add, LinearMap.add_apply]
            rw [hy, hz]
    | add x y hx hy =>
        simp only [map_add, LinearMap.add_apply]
        rw [hx, hy]
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a v =>
      have ha : a ⊗ₜ[ZMod 2] v =
          a • ((1 : K) ⊗ₜ[ZMod 2] v) := by
        rw [TensorProduct.smul_tmul']
        simp
      rw [ha, map_smul, LinearMap.map_smul₂,
        lemma6_scalarExtendBilinear_tmul, hB_self]
      simp
  | add x y hx hy =>
      simp only [map_add, LinearMap.add_apply]
      rw [hx, hy, hBK_symm y x]
      nth_rw 2 [← ZModModule.neg_eq_self
        (lemma6_scalarExtendBilinear B x y)]
      simpa only [zero_add, add_zero] using
        add_neg_cancel (lemma6_scalarExtendBilinear B x y)

public theorem lemma6_scalarExtendBilinear_equivariant
    {K V W U : Type*} [Field K]
    [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    [AddCommGroup U] [Module (ZMod 2) U]
    [Algebra (ZMod 2) K]
    (T : V ≃ₗ[ZMod 2] V) (S : W ≃ₗ[ZMod 2] W)
    (R : U ≃ₗ[ZMod 2] U)
    (C : V →ₗ[ZMod 2] W →ₗ[ZMod 2] U)
    (hC : ∀ v w, C (T v) (S w) = R (C v w)) :
    ∀ x : K ⊗[ZMod 2] V, ∀ y : K ⊗[ZMod 2] W,
      lemma6_scalarExtendBilinear C
          (T.baseChange (ZMod 2) K V V x)
          (S.baseChange (ZMod 2) K W W y) =
        R.baseChange (ZMod 2) K U U
          (lemma6_scalarExtendBilinear C x y) := by
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a v =>
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul b w =>
          have ha : a ⊗ₜ[ZMod 2] v =
              a • ((1 : K) ⊗ₜ[ZMod 2] v) := by
            rw [TensorProduct.smul_tmul']
            simp
          have hb : b ⊗ₜ[ZMod 2] w =
              b • ((1 : K) ⊗ₜ[ZMod 2] w) := by
            rw [TensorProduct.smul_tmul']
            simp
          rw [ha, hb]
          simp only [map_smul, LinearMap.smul_apply, smul_smul]
          rw [LinearEquiv.baseChange_tmul, LinearEquiv.baseChange_tmul,
            lemma6_scalarExtendBilinear_tmul,
            lemma6_scalarExtendBilinear_tmul, hC,
            LinearEquiv.baseChange_tmul]
      | add y z hy hz =>
          simp only [map_add]
          rw [hy, hz]
  | add x y hx hy =>
      intro z
      simp only [map_add, LinearMap.add_apply]
      rw [hx z, hy z]

private theorem lemma6_scalarExtendBilinear_eigen
    {K V W U : Type*} [Field K]
    [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    [AddCommGroup U] [Module (ZMod 2) U]
    [Algebra (ZMod 2) K]
    (T : V ≃ₗ[ZMod 2] V) (S : W ≃ₗ[ZMod 2] W)
    (R : U ≃ₗ[ZMod 2] U)
    (C : V →ₗ[ZMod 2] W →ₗ[ZMod 2] U)
    (hC : ∀ v w, C (T v) (S w) = R (C v w))
    (e : U ≃ₗ[ZMod 2] W)
    (he : ∀ z, e (R z) = S (e z))
    (x : TensorProduct (ZMod 2) K V)
    (y : TensorProduct (ZMod 2) K W)
    (alpha beta : K)
    (hx : T.baseChange (ZMod 2) K V V x = alpha • x)
    (hy : S.baseChange (ZMod 2) K W W y = beta • y) :
    S.baseChange (ZMod 2) K W W
        (e.baseChange (ZMod 2) K U W
          (lemma6_scalarExtendBilinear (K := K) C x y)) =
      (alpha * beta) •
        e.baseChange (ZMod 2) K U W
          (lemma6_scalarExtendBilinear (K := K) C x y) := by
  let TK := T.baseChange (ZMod 2) K V V
  let SK := S.baseChange (ZMod 2) K W W
  let RK := R.baseChange (ZMod 2) K U U
  let eK := e.baseChange (ZMod 2) K U W
  let CK := lemma6_scalarExtendBilinear (K := K) C
  have hCK : ∀ v w, CK (TK v) (SK w) = RK (CK v w) :=
    lemma6_scalarExtendBilinear_equivariant (K := K) T S R C hC
  have heK :
      ∀ z : TensorProduct (ZMod 2) K U, eK (RK z) = SK (eK z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp [eK, RK, SK]
    | tmul a z =>
        simp [eK, RK, SK, LinearEquiv.baseChange_tmul, he]
    | add z t hz ht =>
        simp only [map_add]
        rw [hz, ht]
  change SK (eK (CK x y)) =
    (alpha * beta) • eK (CK x y)
  calc
    SK (eK (CK x y)) = eK (RK (CK x y)) := (heK (CK x y)).symm
    _ = eK (CK (TK x) (SK y)) := congrArg eK (hCK x y).symm
    _ = (alpha * beta) • eK (CK x y) := by
      change eK (CK (T.baseChange (ZMod 2) K V V x)
        (S.baseChange (ZMod 2) K W W y)) = _
      rw [hx, hy]
      simp [smul_smul, mul_comm]

private theorem lemma6_scalarExtend_tripleBasis_eigen
    {K V W U : Type*} [Field K]
    [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    [AddCommGroup U] [Module (ZMod 2) U]
    [Algebra (ZMod 2) K]
    (T : V ≃ₗ[ZMod 2] V) (S : W ≃ₗ[ZMod 2] W)
    (R : U ≃ₗ[ZMod 2] U)
    (C : V →ₗ[ZMod 2] W →ₗ[ZMod 2] U)
    (hC : ∀ v w, C (T v) (S w) = R (C v w))
    (e : U ≃ₗ[ZMod 2] W)
    (he : ∀ z, e (R z) = S (e z))
    (lambda : K) (x : TensorProduct (ZMod 2) K V)
    (y : TensorProduct (ZMod 2) K W)
    (i j k : ℕ)
    (hx : T.baseChange (ZMod 2) K V V x =
      lambda ^ (2 ^ k) • x)
    (hy : S.baseChange (ZMod 2) K W W y =
      lambda ^ (2 ^ i + 2 ^ j) • y) :
    S.baseChange (ZMod 2) K W W
        (e.baseChange (ZMod 2) K U W
          (lemma6_scalarExtendBilinear (K := K) C x y)) =
      lambda ^ (2 ^ k + 2 ^ i + 2 ^ j) •
        e.baseChange (ZMod 2) K U W
          (lemma6_scalarExtendBilinear (K := K) C x y) := by
  have h := lemma6_scalarExtendBilinear_eigen
    T S R C hC e he x y
      (lambda ^ (2 ^ k)) (lambda ^ (2 ^ i + 2 ^ j)) hx hy
  simpa [← pow_add, add_assoc] using h

private theorem lemma6_eigenvalueBucket_eq_zero
    {K W ι : Type*} [Field K] [AddCommGroup W] [Module K W]
    [DecidableEq ι] [DecidableEq K]
    (T : Module.End K W) (s : Finset ι)
    (mu : ι → K) (v : ι → W)
    (hv : ∀ i ∈ s, T (v i) = mu i • v i)
    (hsum : ∑ i ∈ s, v i = 0)
    (a : K) :
    ∑ i ∈ s.filter (fun i => mu i = a), v i = 0 := by
  classical
  let va : W := ∑ i ∈ s.filter (fun i => mu i = a), v i
  let vb : W := ∑ i ∈ s.filter (fun i => mu i ≠ a), v i
  have hva : va ∈ T.eigenspace a := by
    rw [Module.End.mem_eigenspace_iff]
    simp only [va, map_sum]
    calc
      (∑ i ∈ s.filter (fun i => mu i = a), T (v i)) =
          ∑ i ∈ s.filter (fun i => mu i = a), a • v i := by
            apply Finset.sum_congr rfl
            intro i hi
            have his : i ∈ s := Finset.filter_subset _ _ hi
            have hia : mu i = a := (Finset.mem_filter.mp hi).2
            rw [hv i his, hia]
      _ = a • (∑ i ∈ s.filter (fun i => mu i = a), v i) :=
        Finset.smul_sum.symm
  have hvb : vb ∈ ⨆ (b : K) (_ : b ≠ a), T.eigenspace b := by
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.mem_iSup_of_mem (mu i)
    have hne : mu i ≠ a := (Finset.mem_filter.mp hi).2
    apply Submodule.mem_iSup_of_mem hne
    rw [Module.End.mem_eigenspace_iff]
    exact hv i (Finset.filter_subset _ _ hi)
  have hab : va + vb = 0 := by
    rw [show va + vb = ∑ i ∈ s, v i by
      simpa only [va, vb] using
        (Finset.sum_filter_add_sum_filter_not
          (s := s) (p := fun i => mu i = a) (f := v))]
    exact hsum
  have hva_eq_neg : va = -vb := eq_neg_of_add_eq_zero_left hab
  have hva_other : va ∈ ⨆ (b : K) (_ : b ≠ a), T.eigenspace b := by
    rw [hva_eq_neg]
    exact Submodule.neg_mem _ hvb
  have hdisj :
      Disjoint (T.eigenspace a)
        (⨆ (b : K) (_ : b ≠ a), T.eigenspace b) :=
    T.eigenspaces_iSupIndep a
  have hva_zero : va = 0 :=
    Submodule.disjoint_def.mp hdisj va hva hva_other
  simpa only [va] using hva_zero

private lemma lemma6_finset_bucket_target_eq_zero
    {α W K : Type*} [DecidableEq α] [DecidableEq K]
    [AddCommMonoid W]
    (s : Finset α) (mu : α → K) (v : α → W)
    (a : α) (ha : a ∈ s)
    (hbucket : ∑ i ∈ s.filter (fun i => mu i = mu a), v i = 0)
    (hunique : ∀ i ∈ s, mu i = mu a → i = a ∨ v i = 0) :
    v a = 0 := by
  classical
  have ha_filter : a ∈ s.filter (fun i => mu i = mu a) := by
    simp only [Finset.mem_filter, ha, true_and]
  have hsum : ∑ i ∈ s.filter (fun i => mu i = mu a), v i = v a := by
    apply Finset.sum_eq_single a
    · intro i hi hia
      have his : i ∈ s := Finset.filter_subset _ _ hi
      have hmu : mu i = mu a := (Finset.mem_filter.mp hi).2
      exact (hunique i his hmu).resolve_left hia
    · exact fun hnot => (hnot ha_filter).elim
  rw [hsum] at hbucket
  exact hbucket


private theorem lemma6_lowerCentralIteratedBracket_square_self
    {H : Type u} [Group H]
    (hH_square : squaresSubgroup H ≤ higmanLowerCentralSeries H 1)
    (squareMap : Additive (LowerCentralFactor H 0) →
      Additive (LowerCentralFactor H 1))
    (hsquare_mk :
      ∀ x : higmanLowerCentralSeries H 0,
        ∀ hsquare : (x : H) ^ 2 ∈ higmanLowerCentralSeries H 1,
          squareMap
              (Additive.ofMul
                (QuotientGroup.mk' (lowerCentralFactorKernel H 0) x)) =
            Additive.ofMul
              (QuotientGroup.mk' (lowerCentralFactorKernel H 1)
                ⟨(x : H) ^ 2, hsquare⟩))
    (v : Additive (LowerCentralFactor H 0)) :
    lemma6_lowerCentralIteratedBracket v (squareMap v) = 0 := by
  obtain ⟨x, hx⟩ :=
    QuotientGroup.mk'_surjective (lowerCentralFactorKernel H 0) v.toMul
  have hv :
      v = Additive.ofMul
        (QuotientGroup.mk' (lowerCentralFactorKernel H 0) x) := by
    apply Additive.toMul.injective
    exact hx.symm
  have hsquare : (x : H) ^ 2 ∈ higmanLowerCentralSeries H 1 := by
    exact hH_square (Subgroup.subset_closure ⟨(x : H), rfl⟩)
  rw [hv, hsquare_mk x hsquare,
    lemma6_lowerCentralIteratedBracket_mk_mk]
  have hone :
      lemma6_nextBracketLift x
          (⟨(x : H) ^ 2, hsquare⟩ : higmanLowerCentralSeries H 1) = 1 := by
    apply Subtype.ext
    change (x : H) * (x : H) ^ 2 * (x : H)⁻¹ *
      ((x : H) ^ 2)⁻¹ = 1
    group
  rw [hone, map_one, ofMul_one]
private theorem lemma6_scalarExtended_normalForm_tripleSum_eq_zero
    {K V W U : Type*} [Field K]
    [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    [AddCommGroup U] [Module (ZMod 2) U]
    [Algebra (ZMod 2) K]
    (C : V →ₗ[ZMod 2] W →ₗ[ZMod 2] U)
    (e : U ≃ₗ[ZMod 2] W)
    (m : ℕ)
    (coordinates : K ≃ₗ[ZMod 2] V)
    (u : Fin m → K ⊗[ZMod 2] V)
    (bracketK :
      (K ⊗[ZMod 2] V) →ₗ[K]
        (K ⊗[ZMod 2] V) →ₗ[K] (K ⊗[ZMod 2] W))
    (squareMap : V → W)
    (hu_expansion : ∀ alpha : K,
      (1 : K) ⊗ₜ[ZMod 2] coordinates alpha =
        ∑ i : Fin m, alpha ^ (2 ^ (i : ℕ)) • u i)
    (hsquare_formula : ∀ alpha : K,
      (1 : K) ⊗ₜ[ZMod 2] squareMap (coordinates alpha) =
        ∑ i : Fin m, ∑ j ∈ Finset.Ioi i,
          alpha ^ (2 ^ (i : ℕ) + 2 ^ (j : ℕ)) •
            bracketK (u i) (u j))
    (hsquare_self : ∀ v : V, C v (squareMap v) = 0) :
    ∑ i : Fin m, ∑ j ∈ Finset.Ioi i, ∑ k : Fin m,
      e.baseChange (ZMod 2) K U W
        (lemma6_scalarExtendBilinear C (u k) (bracketK (u i) (u j))) = 0 := by
  have hzeroK :
      lemma6_scalarExtendBilinear C
          ((1 : K) ⊗ₜ[ZMod 2] coordinates 1)
          ((1 : K) ⊗ₜ[ZMod 2] squareMap (coordinates 1)) = 0 := by
    rw [lemma6_scalarExtendBilinear_tmul,
      hsquare_self (coordinates 1)]
    simp
  rw [hu_expansion 1, hsquare_formula 1] at hzeroK
  have hezero := congrArg (e.baseChange (ZMod 2) K U W) hzeroK
  simpa only [one_pow, one_smul, map_sum, LinearMap.sum_apply, map_zero]
    using hezero
private theorem lemma6_lowerCentral_normalForm_tripleSum_eq_zero
    {H : Type u} [Group H]
    {K : Type*} [Field K] [Algebra (ZMod 2) K]
    (e : Additive (LowerCentralFactor H 2) ≃ₗ[ZMod 2]
      Additive (LowerCentralFactor H 1))
    (m : ℕ)
    (coordinates : K ≃ₗ[ZMod 2]
      Additive (LowerCentralFactor H 0))
    (u : Fin m → K ⊗[ZMod 2]
      Additive (LowerCentralFactor H 0))
    (bracketK :
      (K ⊗[ZMod 2] Additive (LowerCentralFactor H 0)) →ₗ[K]
        (K ⊗[ZMod 2] Additive (LowerCentralFactor H 0)) →ₗ[K]
          (K ⊗[ZMod 2] Additive (LowerCentralFactor H 1)))
    (squareMap : Additive (LowerCentralFactor H 0) →
      Additive (LowerCentralFactor H 1))
    (hu_expansion : ∀ alpha : K,
      (1 : K) ⊗ₜ[ZMod 2] coordinates alpha =
        ∑ i : Fin m, alpha ^ (2 ^ (i : ℕ)) • u i)
    (hsquare_formula : ∀ alpha : K,
      (1 : K) ⊗ₜ[ZMod 2] squareMap (coordinates alpha) =
        ∑ i : Fin m, ∑ j ∈ Finset.Ioi i,
          alpha ^ (2 ^ (i : ℕ) + 2 ^ (j : ℕ)) •
            bracketK (u i) (u j))
    (hH_square : squaresSubgroup H ≤ higmanLowerCentralSeries H 1)
    (hsquare_mk :
      ∀ x : higmanLowerCentralSeries H 0,
        ∀ hsquare : (x : H) ^ 2 ∈ higmanLowerCentralSeries H 1,
          squareMap
              (Additive.ofMul
                (QuotientGroup.mk' (lowerCentralFactorKernel H 0) x)) =
            Additive.ofMul
              (QuotientGroup.mk' (lowerCentralFactorKernel H 1)
                ⟨(x : H) ^ 2, hsquare⟩)) :
    ∑ i : Fin m, ∑ j ∈ Finset.Ioi i, ∑ k : Fin m,
      e.baseChange (ZMod 2) K
          (Additive (LowerCentralFactor H 2))
          (Additive (LowerCentralFactor H 1))
        (lemma6_scalarExtendBilinear lemma6_lowerCentralIteratedBracket
          (u k) (bracketK (u i) (u j))) = 0 := by
  exact lemma6_scalarExtended_normalForm_tripleSum_eq_zero
    lemma6_lowerCentralIteratedBracket e m coordinates u bracketK squareMap
    hu_expansion hsquare_formula
    (lemma6_lowerCentralIteratedBracket_square_self
      hH_square squareMap hsquare_mk)
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- Spectral-combinatorial heart of the odd-dimensional branch. This is the
literal scalar-extended form of Higman's eigenvalue argument: distinct-index
triple brackets have unsupported multipliers; the repeated-index buckets have
at most one supported term when `n` is odd; and `[u^(2),u]=0` kills that term. -/
private theorem lemma6_odd_basis_triples_vanish_core
    {H : Type u} [Group H] [Finite H]
    (xi : MulAut H)
    (hL2_transitive :
      ∀ x : Additive (LowerCentralFactor H 1), x ≠ 0 →
        ∀ y : Additive (LowerCentralFactor H 1), y ≠ 0 →
          ∃ k : ℕ, (lowerCentralFactorLinearAut xi 1 ^ k) x = y)
    (n : ℕ) (hn : 2 ≤ n) (hn_odd : Odd n)
    (hL2_card : Nat.card (LowerCentralFactor H 1) = 2 ^ n)
    (hH_square : squaresSubgroup H ≤ higmanLowerCentralSeries H 1)
    (e : Additive (LowerCentralFactor H 2) ≃ₗ[ZMod 2]
      Additive (LowerCentralFactor H 1))
    (he : ∀ v : Additive (LowerCentralFactor H 2),
      e (lowerCentralFactorLinearAut xi 2 v) =
        lowerCentralFactorLinearAut xi 1 (e v))
    (lambda : BinaryGaloisField n) (hlambda : lambda ≠ 0)
    (hlambda_order : orderOf (Units.mk0 lambda hlambda) = 2 ^ n - 1)
    (coordinates : BinaryGaloisField n ≃ₗ[ZMod 2]
      Additive (LowerCentralFactor H 0))
    (u : Module.Basis (Fin n) (BinaryGaloisField n)
      (BinaryGaloisField n ⊗[ZMod 2]
        Additive (LowerCentralFactor H 0)))
    (xiK : (BinaryGaloisField n ⊗[ZMod 2]
      Additive (LowerCentralFactor H 0)) ≃ₗ[BinaryGaloisField n]
        (BinaryGaloisField n ⊗[ZMod 2]
          Additive (LowerCentralFactor H 0)))
    (bracket : Additive (LowerCentralFactor H 0) →ₗ[ZMod 2]
      Additive (LowerCentralFactor H 0) →ₗ[ZMod 2]
        Additive (LowerCentralFactor H 1))
    (bracketK : (BinaryGaloisField n ⊗[ZMod 2]
      Additive (LowerCentralFactor H 0)) →ₗ[BinaryGaloisField n]
        (BinaryGaloisField n ⊗[ZMod 2]
          Additive (LowerCentralFactor H 0)) →ₗ[BinaryGaloisField n]
            (BinaryGaloisField n ⊗[ZMod 2]
              Additive (LowerCentralFactor H 1)))
    (squareMap : Additive (LowerCentralFactor H 0) →
      Additive (LowerCentralFactor H 1))
    (hxiK_tmul : ∀ v : Additive (LowerCentralFactor H 0),
      xiK (1 ⊗ₜ[ZMod 2] v) =
        1 ⊗ₜ[ZMod 2] lowerCentralFactorLinearAut xi 0 v)
    (hu_eigen : ∀ i : Fin n,
      xiK (u i) = lambda ^ (2 ^ (i : ℕ)) • u i)
    (hu_expansion : ∀ alpha : BinaryGaloisField n,
      1 ⊗ₜ[ZMod 2] coordinates alpha =
        ∑ i : Fin n, alpha ^ (2 ^ (i : ℕ)) • u i)
    (hbracketK_tmul :
      ∀ v w : Additive (LowerCentralFactor H 0),
        bracketK (1 ⊗ₜ[ZMod 2] v) (1 ⊗ₜ[ZMod 2] w) =
          1 ⊗ₜ[ZMod 2] bracket v w)
    (hbracket_mk :
      ∀ x y : higmanLowerCentralSeries H 0,
        ∀ hcomm : ⁅(x : H), (y : H)⁆ ∈ higmanLowerCentralSeries H 1,
          bracket
              (Additive.ofMul
                (QuotientGroup.mk' (lowerCentralFactorKernel H 0) x))
              (Additive.ofMul
                (QuotientGroup.mk' (lowerCentralFactorKernel H 0) y)) =
            Additive.ofMul
              (QuotientGroup.mk' (lowerCentralFactorKernel H 1)
                ⟨⁅(x : H), (y : H)⁆, hcomm⟩))
    (hsquare_mk :
      ∀ x : higmanLowerCentralSeries H 0,
        ∀ hsquare : (x : H) ^ 2 ∈ higmanLowerCentralSeries H 1,
          squareMap
              (Additive.ofMul
                (QuotientGroup.mk' (lowerCentralFactorKernel H 0) x)) =
            Additive.ofMul
              (QuotientGroup.mk' (lowerCentralFactorKernel H 1)
                ⟨(x : H) ^ 2, hsquare⟩))
    (hsquare_formula : ∀ alpha : BinaryGaloisField n,
      1 ⊗ₜ[ZMod 2] squareMap (coordinates alpha) =
        ∑ i : Fin n, ∑ j ∈ Finset.Ioi i,
          alpha ^ (2 ^ (i : ℕ) + 2 ^ (j : ℕ)) •
            bracketK (u i) (u j)) :
    ∀ i j k : Fin n,
      lemma6_scalarExtendBilinear lemma6_lowerCentralIteratedBracket
          (u k) (bracketK (u i) (u j)) = 0 := by
  classical
  have hnpos : 0 < n := by omega
  have hL2_add_card :
      Nat.card (Additive (LowerCentralFactor H 1)) = 2 ^ n :=
    (Nat.card_congr
      (Additive.toMul : Additive (LowerCentralFactor H 1) ≃
        LowerCentralFactor H 1)).trans hL2_card
  have hL2_card_gt :
      1 < Nat.card (Additive (LowerCentralFactor H 1)) := by
    rw [hL2_add_card]
    exact one_lt_pow₀ (by norm_num : 1 < (2 : ℕ)) (by omega)
  let : Nontrivial (Additive (LowerCentralFactor H 1)) :=
    Finite.one_lt_card_iff_nontrivial.mp hL2_card_gt
  have hL2_irreducible := lemma6_irreducible_of_transitive
    (lowerCentralFactorLinearAut xi 1) hL2_transitive
  obtain ⟨m2, _hm2, mu, _coordinates2, b, hL2_card2, hmu,
      _hcoordinates2, hb_eigen, _hb_expansion⟩ :=
    lemma5_irreducible_conjugate_eigenbasis
      (lowerCentralFactorLinearAut xi 1) hL2_irreducible
  have hm2n : m2 = n :=
    Nat.pow_right_injective (by omega : 1 < 2)
      (hL2_card2.symm.trans hL2_add_card)
  subst m2
  obtain ⟨_hbracket_equivariant, hbracketK_equivariant,
      _hbracket_self, hbracketK_self, hbracket_span⟩ :=
    lemma5_lowerCentralBracket_interfaces xi n xiK bracket bracketK
      hxiK_tmul hbracketK_tmul hbracket_mk
  have hbracketK_span := lemma6_scalarExtendedBilinear_span
    bracket bracketK hbracketK_tmul hbracket_span
  obtain ⟨a0, b0, habracket0⟩ :=
    lemma6_exists_basis_pair_ne_zero_of_span_eq_top
      bracketK u hbracketK_span
  have hab0 : a0 ≠ b0 := by
    intro hab
    subst b0
    exact habracket0 (hbracketK_self (u a0))
  obtain ⟨p0, hseed⟩ :=
    lemma6_nonzero_equivariant_bilinear_basis_value_spectrum
      xiK
      ((lowerCentralFactorLinearAut xi 1).baseChange (ZMod 2)
        (BinaryGaloisField n)
        (Additive (LowerCentralFactor H 1))
        (Additive (LowerCentralFactor H 1)))
      bracketK hbracketK_equivariant u
      (fun i : Fin n => lambda ^ (2 ^ i.val)) hu_eigen b
      (fun q : Fin n => mu ^ (2 ^ q.val)) hb_eigen
      a0 b0 habracket0
  have hsupport (x y : Fin n)
      (hxy : bracketK (u x) (u y) ≠ 0) :
      lemma6_finPairSupported (lemma6_finPairGap a0 b0) x y := by
    have hxy_ne : x ≠ y := by
      intro h
      subst y
      exact hxy (hbracketK_self (u x))
    obtain ⟨q, hpair⟩ :=
      lemma6_nonzero_equivariant_bilinear_basis_value_spectrum
        xiK
        ((lowerCentralFactorLinearAut xi 1).baseChange (ZMod 2)
          (BinaryGaloisField n)
          (Additive (LowerCentralFactor H 1))
          (Additive (LowerCentralFactor H 1)))
        bracketK hbracketK_equivariant u
        (fun i : Fin n => lambda ^ (2 ^ i.val)) hu_eigen b
        (fun q : Fin n => mu ^ (2 ^ q.val)) hb_eigen
        x y hxy
    exact lemma6_finPairSupported_of_primitive_pair_eigenvalue_eq
      hnpos lambda mu hlambda hmu hlambda_order
      a0 b0 x y hab0 hxy_ne p0 q hseed hpair
  have hxiK_baseChange :
      xiK =
        (lowerCentralFactorLinearAut xi 0).baseChange (ZMod 2)
          (BinaryGaloisField n)
          (Additive (LowerCentralFactor H 0))
          (Additive (LowerCentralFactor H 0)) := by
    apply LinearEquiv.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a v =>
        have ha :
            a ⊗ₜ[ZMod 2] v =
              a • ((1 : BinaryGaloisField n) ⊗ₜ[ZMod 2] v) := by
          rw [TensorProduct.smul_tmul']
          simp
        rw [ha, map_smul, map_smul, hxiK_tmul,
          LinearEquiv.baseChange_tmul]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hu_base_eigen (k : Fin n) :
      (lowerCentralFactorLinearAut xi 0).baseChange (ZMod 2)
          (BinaryGaloisField n)
          (Additive (LowerCentralFactor H 0))
          (Additive (LowerCentralFactor H 0)) (u k) =
        lambda ^ (2 ^ k.val) • u k := by
    rw [← hxiK_baseChange]
    exact hu_eigen k
  have hinner_eigen (i j : Fin n) :
      (lowerCentralFactorLinearAut xi 1).baseChange (ZMod 2)
          (BinaryGaloisField n)
          (Additive (LowerCentralFactor H 1))
          (Additive (LowerCentralFactor H 1))
          (bracketK (u i) (u j)) =
        lambda ^ (2 ^ i.val + 2 ^ j.val) • bracketK (u i) (u j) := by
    calc
      _ = bracketK (xiK (u i)) (xiK (u j)) :=
        (hbracketK_equivariant (u i) (u j)).symm
      _ = bracketK
          (lambda ^ (2 ^ i.val) • u i)
          (lambda ^ (2 ^ j.val) • u j) := by rw [hu_eigen, hu_eigen]
      _ = lambda ^ (2 ^ i.val + 2 ^ j.val) •
          bracketK (u i) (u j) := by
        rw [map_smul, LinearMap.map_smul₂, smul_smul, ← pow_add]
        simp [add_comm]
  have hterm_eigen (i j k : Fin n) :=
    lemma6_scalarExtend_tripleBasis_eigen
      (lowerCentralFactorLinearAut xi 0)
      (lowerCentralFactorLinearAut xi 1)
      (lowerCentralFactorLinearAut xi 2)
      lemma6_lowerCentralIteratedBracket
      (lemma6_lowerCentralIteratedBracket_equivariant xi)
      e he lambda (u k) (bracketK (u i) (u j))
      i.val j.val k.val (hu_base_eigen k) (hinner_eigen i j)
  have htriple_sum := lemma6_lowerCentral_normalForm_tripleSum_eq_zero
    e n coordinates u bracketK squareMap hu_expansion hsquare_formula
    hH_square hsquare_mk
  have hdistinct (i j k : Fin n) (hij : i ≠ j)
      (hki : k ≠ i) (hkj : k ≠ j) :
      lemma6_scalarExtendBilinear lemma6_lowerCentralIteratedBracket
        (u k) (bracketK (u i) (u j)) = 0 := by
    let z := e.baseChange (ZMod 2) (BinaryGaloisField n)
      (Additive (LowerCentralFactor H 2))
      (Additive (LowerCentralFactor H 1))
      (lemma6_scalarExtendBilinear lemma6_lowerCentralIteratedBracket
        (u k) (bracketK (u i) (u j)))
    by_contra hterm
    have hz0 : z ≠ 0 := by
      dsimp only [z]
      exact (LinearEquiv.map_ne_zero_iff _).2 hterm
    obtain ⟨q, htriple⟩ :=
      lemma6_diagonal_eigenvalue_eq_basis_eigenvalue
        ((lowerCentralFactorLinearAut xi 1).baseChange (ZMod 2)
          (BinaryGaloisField n)
          (Additive (LowerCentralFactor H 1))
          (Additive (LowerCentralFactor H 1))).toLinearMap
        b (fun q : Fin n => mu ^ (2 ^ q.val)) hb_eigen z
        (lambda ^ (2 ^ k.val + 2 ^ i.val + 2 ^ j.val))
        (by simpa only [z, LinearEquiv.coe_toLinearMap] using
          hterm_eigen i j k) hz0
    let lambdaUnit : (BinaryGaloisField n)ˣ := Units.mk0 lambda hlambda
    let muUnit : (BinaryGaloisField n)ˣ := Units.mk0 mu hmu
    have hseedUnit :
        lambdaUnit ^ (2 ^ a0.val + 2 ^ b0.val) =
          muUnit ^ (2 ^ p0.val) := by
      apply Units.ext
      simpa only [lambdaUnit, muUnit, Units.val_mul,
        Units.val_pow_eq_pow_val, Units.val_mk0, pow_add] using hseed
    have htripleUnit :
        lambdaUnit ^ (2 ^ k.val + 2 ^ i.val + 2 ^ j.val) =
          muUnit ^ (2 ^ q.val) := by
      apply Units.ext
      simpa only [lambdaUnit, muUnit, Units.val_pow_eq_pow_val,
        Units.val_mk0] using htriple
    have hlambdaEq :
        lambdaUnit ^ ((2 ^ a0.val + 2 ^ b0.val) * 2 ^ q.val) =
          lambdaUnit ^
            ((2 ^ k.val + 2 ^ i.val + 2 ^ j.val) * 2 ^ p0.val) := by
      calc
        lambdaUnit ^ ((2 ^ a0.val + 2 ^ b0.val) * 2 ^ q.val) =
            (lambdaUnit ^ (2 ^ a0.val + 2 ^ b0.val)) ^
              (2 ^ q.val) := by rw [pow_mul]
        _ = (muUnit ^ (2 ^ p0.val)) ^ (2 ^ q.val) := by
          rw [hseedUnit]
        _ = (muUnit ^ (2 ^ q.val)) ^ (2 ^ p0.val) := by
          calc
            (muUnit ^ (2 ^ p0.val)) ^ (2 ^ q.val) =
                muUnit ^ (2 ^ p0.val * 2 ^ q.val) :=
              (pow_mul muUnit (2 ^ p0.val) (2 ^ q.val)).symm
            _ = muUnit ^ (2 ^ q.val * 2 ^ p0.val) := by rw [mul_comm]
            _ = (muUnit ^ (2 ^ q.val)) ^ (2 ^ p0.val) :=
              pow_mul muUnit (2 ^ q.val) (2 ^ p0.val)
        _ = (lambdaUnit ^
              (2 ^ k.val + 2 ^ i.val + 2 ^ j.val)) ^
              (2 ^ p0.val) := by rw [htripleUnit]
        _ = lambdaUnit ^
              ((2 ^ k.val + 2 ^ i.val + 2 ^ j.val) * 2 ^ p0.val) := by
          rw [pow_mul]
    have hmod : Nat.ModEq (2 ^ n - 1)
        ((2 ^ a0.val + 2 ^ b0.val) * 2 ^ q.val)
        ((2 ^ k.val + 2 ^ i.val + 2 ^ j.val) * 2 ^ p0.val) := by
      have h := pow_eq_pow_iff_modEq.mp hlambdaEq
      simpa only [lambdaUnit, hlambda_order] using h
    let aq := lemma6_finCyclicAdd hnpos q.val a0
    let bq := lemma6_finCyclicAdd hnpos q.val b0
    let kp := lemma6_finCyclicAdd hnpos p0.val k
    let ip := lemma6_finCyclicAdd hnpos p0.val i
    let jp := lemma6_finCyclicAdd hnpos p0.val j
    have hpairShift : Nat.ModEq (2 ^ n - 1)
        ((2 ^ a0.val + 2 ^ b0.val) * 2 ^ q.val)
        (2 ^ aq.val + 2 ^ bq.val) := by
      simpa only [aq, bq, lemma6_finCyclicAdd] using
        lemma6_pair_two_pow_mul_modEq_cyclic n a0.val b0.val q.val
    have htripleShift : Nat.ModEq (2 ^ n - 1)
        ((2 ^ k.val + 2 ^ i.val + 2 ^ j.val) * 2 ^ p0.val)
        (2 ^ kp.val + 2 ^ ip.val + 2 ^ jp.val) := by
      have h := ((lemma6_two_pow_modEq_cyclic n (k.val + p0.val)).add
        (lemma6_two_pow_modEq_cyclic n (i.val + p0.val))).add
        (lemma6_two_pow_modEq_cyclic n (j.val + p0.val))
      simpa only [kp, ip, jp, lemma6_finCyclicAdd, pow_add,
        add_mul] using h
    have hcyclic : Nat.ModEq (2 ^ n - 1)
        (2 ^ kp.val + 2 ^ ip.val + 2 ^ jp.val)
        (2 ^ aq.val + 2 ^ bq.val) :=
      htripleShift.symm.trans (hmod.symm.trans hpairShift)
    have hkpi : kp ≠ ip := fun h =>
      hki (lemma6_finCyclicAdd_injective hnpos p0.val h)
    have hkpj : kp ≠ jp := fun h =>
      hkj (lemma6_finCyclicAdd_injective hnpos p0.val h)
    have hipj : ip ≠ jp := fun h =>
      hij (lemma6_finCyclicAdd_injective hnpos p0.val h)
    have haqbq : aq ≠ bq := fun h =>
      hab0 (lemma6_finCyclicAdd_injective hnpos q.val h)
    have hordered (x y z' : Fin n)
        (hxy : x.val < y.val) (hyz : y.val < z'.val) :
        ¬ Nat.ModEq (2 ^ n - 1)
          (2 ^ x.val + 2 ^ y.val + 2 ^ z'.val)
          (2 ^ aq.val + 2 ^ bq.val) := by
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne haqbq) with habq | hbaq
      · exact lemma6_triple_two_pow_not_modEq_pair_two_pow
          n x.val y.val z'.val aq.val bq.val hxy hyz z'.isLt
          habq bq.isLt
      · intro hbad
        apply lemma6_triple_two_pow_not_modEq_pair_two_pow
          n x.val y.val z'.val bq.val aq.val hxy hyz z'.isLt
          hbaq aq.isLt
        simpa only [add_comm] using hbad
    have hnot : ¬ Nat.ModEq (2 ^ n - 1)
        (2 ^ kp.val + 2 ^ ip.val + 2 ^ jp.val)
        (2 ^ aq.val + 2 ^ bq.val) := by
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hkpi) with hkpi' | hipk'
      · rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hipj) with hipj' | hjpi'
        · exact hordered kp ip jp hkpi' hipj'
        · rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hkpj) with hkpj' | hjpk'
          · simpa only [add_assoc, add_comm, add_left_comm] using
              hordered kp jp ip hkpj' hjpi'
          · simpa only [add_assoc, add_comm, add_left_comm] using
              hordered jp kp ip hjpk' hkpi'
      · rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hkpj) with hkpj' | hjpk'
        · simpa only [add_assoc, add_comm, add_left_comm] using
            hordered ip kp jp hipk' hkpj'
        · rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hipj) with hipj' | hjpi'
          · simpa only [add_assoc, add_comm, add_left_comm] using
              hordered ip jp kp hipj' hjpk'
          · simpa only [add_assoc, add_comm, add_left_comm] using
              hordered jp ip kp hjpi' hipk'
    exact hnot hcyclic
  have hadd_self_L2K
      (z : BinaryGaloisField n ⊗[ZMod 2]
        Additive (LowerCentralFactor H 1)) : z + z = 0 := by
    rw [← two_smul (BinaryGaloisField n) z]
    simp only [CharTwo.two_eq_zero, zero_smul]
  have hbracketK_symm
      (x y : BinaryGaloisField n ⊗[ZMod 2]
        Additive (LowerCentralFactor H 0)) :
      bracketK x y = bracketK y x := by
    have hsum : bracketK x y + bracketK y x = 0 := by
      have h := hbracketK_self (x + y)
      simp only [map_add, LinearMap.add_apply] at h
      rw [hbracketK_self x, hbracketK_self y] at h
      simpa only [zero_add, add_zero, add_assoc, add_comm] using h
    calc
      bracketK x y = bracketK x y + (bracketK y x + bracketK y x) := by
        rw [hadd_self_L2K, add_zero]
      _ = (bracketK x y + bracketK y x) + bracketK y x := by ac_rfl
      _ = bracketK y x := by rw [hsum, zero_add]
  have hrepeat_ordered (x y r : Fin n) (hxy : x.val < y.val)
      (hr : r = x ∨ r = y) :
      lemma6_scalarExtendBilinear lemma6_lowerCentralIteratedBracket
        (u r) (bracketK (u x) (u y)) = 0 := by
    let triples : Finset (Fin n × (Fin n × Fin n)) :=
      Finset.univ.filter fun p => p.2.1 ∈ Finset.Ioi p.1
    let value (p : Fin n × (Fin n × Fin n)) :=
      e.baseChange (ZMod 2) (BinaryGaloisField n)
        (Additive (LowerCentralFactor H 2))
        (Additive (LowerCentralFactor H 1))
        (lemma6_scalarExtendBilinear lemma6_lowerCentralIteratedBracket
          (u p.2.2) (bracketK (u p.1) (u p.2.1)))
    let multiplier (p : Fin n × (Fin n × Fin n)) :=
      lambda ^ (2 ^ p.2.2.val + 2 ^ p.1.val + 2 ^ p.2.1.val)
    have hvalue_eigen (p : Fin n × (Fin n × Fin n))
        (_hp : p ∈ triples) :
        (lowerCentralFactorLinearAut xi 1).baseChange (ZMod 2)
            (BinaryGaloisField n)
            (Additive (LowerCentralFactor H 1))
            (Additive (LowerCentralFactor H 1)) (value p) =
          multiplier p • value p := by
      exact hterm_eigen p.1 p.2.1 p.2.2
    have hflat_sum : ∑ p ∈ triples, value p = 0 := by
      rw [show (∑ p ∈ triples, value p) =
          ∑ i : Fin n, ∑ j ∈ Finset.Ioi i, ∑ k : Fin n,
            e.baseChange (ZMod 2) (BinaryGaloisField n)
              (Additive (LowerCentralFactor H 2))
              (Additive (LowerCentralFactor H 1))
              (lemma6_scalarExtendBilinear lemma6_lowerCentralIteratedBracket
                (u k) (bracketK (u i) (u j))) by
        simp only [triples, value, Finset.sum_filter, Finset.mem_Ioi]
        rw [← Finset.univ_product_univ, Finset.sum_product]
        apply Finset.sum_congr rfl
        intro i _hi
        rw [← Finset.univ_product_univ, Finset.sum_product]
        rw [show Finset.Ioi i = Finset.univ.filter (fun j => i < j) by
          ext j
          simp only [Finset.mem_Ioi, Finset.mem_filter, Finset.mem_univ,
            true_and]]
        rw [Finset.sum_filter]
        simp only [Finset.sum_ite_irrel,
          Finset.sum_const_zero]]
      exact htriple_sum
    have hfinish :
        lemma6_scalarExtendBilinear lemma6_lowerCentralIteratedBracket
          (u r) (bracketK (u x) (u y)) = 0 := by
      let target : Fin n × (Fin n × Fin n) := (x, y, r)
      have htarget_mem : target ∈ triples := by
        simp only [target, triples, Finset.mem_filter, Finset.mem_univ,
          Finset.mem_Ioi, true_and]
        exact hxy
      by_contra htarget_raw
      have htarget_value : value target ≠ 0 := by
        simp only [value, target]
        exact (LinearEquiv.map_ne_zero_iff _).2 htarget_raw
      obtain ⟨q, htarget_spectrum⟩ :=
        lemma6_diagonal_eigenvalue_eq_basis_eigenvalue
          ((lowerCentralFactorLinearAut xi 1).baseChange (ZMod 2)
            (BinaryGaloisField n)
            (Additive (LowerCentralFactor H 1))
            (Additive (LowerCentralFactor H 1))).toLinearMap
          b (fun q : Fin n => mu ^ (2 ^ q.val)) hb_eigen (value target)
          (multiplier target) (hvalue_eigen target htarget_mem) htarget_value
      let lambdaUnit : (BinaryGaloisField n)ˣ := Units.mk0 lambda hlambda
      let muUnit : (BinaryGaloisField n)ˣ := Units.mk0 mu hmu
      have hseedUnit :
          lambdaUnit ^ (2 ^ a0.val + 2 ^ b0.val) =
            muUnit ^ (2 ^ p0.val) := by
        apply Units.ext
        simpa only [lambdaUnit, muUnit, Units.val_mul,
          Units.val_pow_eq_pow_val, Units.val_mk0, pow_add] using hseed
      have htargetUnit :
          lambdaUnit ^ (2 ^ r.val + 2 ^ x.val + 2 ^ y.val) =
            muUnit ^ (2 ^ q.val) := by
        apply Units.ext
        simpa only [lambdaUnit, muUnit, multiplier, target,
          Units.val_pow_eq_pow_val, Units.val_mk0] using htarget_spectrum
      have hlambdaEq :
          lambdaUnit ^ ((2 ^ a0.val + 2 ^ b0.val) * 2 ^ q.val) =
            lambdaUnit ^
              ((2 ^ r.val + 2 ^ x.val + 2 ^ y.val) * 2 ^ p0.val) := by
        calc
          lambdaUnit ^ ((2 ^ a0.val + 2 ^ b0.val) * 2 ^ q.val) =
              (lambdaUnit ^ (2 ^ a0.val + 2 ^ b0.val)) ^
                (2 ^ q.val) := by rw [pow_mul]
          _ = (muUnit ^ (2 ^ p0.val)) ^ (2 ^ q.val) := by
            rw [hseedUnit]
          _ = (muUnit ^ (2 ^ q.val)) ^ (2 ^ p0.val) := by
            calc
              (muUnit ^ (2 ^ p0.val)) ^ (2 ^ q.val) =
                  muUnit ^ (2 ^ p0.val * 2 ^ q.val) :=
                (pow_mul muUnit (2 ^ p0.val) (2 ^ q.val)).symm
              _ = muUnit ^ (2 ^ q.val * 2 ^ p0.val) := by rw [mul_comm]
              _ = (muUnit ^ (2 ^ q.val)) ^ (2 ^ p0.val) :=
                pow_mul muUnit (2 ^ q.val) (2 ^ p0.val)
          _ = (lambdaUnit ^
                (2 ^ r.val + 2 ^ x.val + 2 ^ y.val)) ^
                (2 ^ p0.val) := by rw [htargetUnit]
          _ = lambdaUnit ^
                ((2 ^ r.val + 2 ^ x.val + 2 ^ y.val) * 2 ^ p0.val) := by
            rw [pow_mul]
      have hmod : Nat.ModEq (2 ^ n - 1)
          ((2 ^ a0.val + 2 ^ b0.val) * 2 ^ q.val)
          ((2 ^ r.val + 2 ^ x.val + 2 ^ y.val) * 2 ^ p0.val) := by
        have h := pow_eq_pow_iff_modEq.mp hlambdaEq
        simpa only [lambdaUnit, hlambda_order] using h
      let shift : ℕ := q.val + (n - p0.val)
      let aq := lemma6_finCyclicAdd hnpos shift a0
      let bq := lemma6_finCyclicAdd hnpos shift b0
      have hp0add : p0.val + (n - p0.val) = n := by omega
      have hpowfactor : 2 ^ p0.val * 2 ^ (n - p0.val) = 2 ^ n := by
        rw [← pow_add, hp0add]
      have hscaled : Nat.ModEq (2 ^ n - 1)
          ((2 ^ a0.val + 2 ^ b0.val) * 2 ^ shift)
          ((2 ^ r.val + 2 ^ x.val + 2 ^ y.val) * 2 ^ n) := by
        have hmul := hmod.mul
          (Nat.ModEq.refl (2 ^ (n - p0.val)))
        convert hmul using 1
        · simp only [shift, pow_add]
          ring
        · rw [mul_assoc, hpowfactor]
      have hpairShift : Nat.ModEq (2 ^ n - 1)
          ((2 ^ a0.val + 2 ^ b0.val) * 2 ^ shift)
          (2 ^ aq.val + 2 ^ bq.val) := by
        simpa only [aq, bq, lemma6_finCyclicAdd] using
          lemma6_pair_two_pow_mul_modEq_cyclic n a0.val b0.val shift
      have hperiod : Nat.ModEq (2 ^ n - 1) (2 ^ n) 1 := by
        apply Nat.ModEq.symm
        exact (Nat.modEq_iff_dvd' Nat.one_le_two_pow).2
          (dvd_refl (2 ^ n - 1))
      have htargetReduce : Nat.ModEq (2 ^ n - 1)
          ((2 ^ r.val + 2 ^ x.val + 2 ^ y.val) * 2 ^ n)
          (2 ^ r.val + 2 ^ x.val + 2 ^ y.val) := by
        simpa only [mul_one] using
          (Nat.ModEq.refl (2 ^ r.val + 2 ^ x.val + 2 ^ y.val)).mul hperiod
      have htargetPair : Nat.ModEq (2 ^ n - 1)
          (2 ^ r.val + 2 ^ x.val + 2 ^ y.val)
          (2 ^ aq.val + 2 ^ bq.val) :=
        htargetReduce.symm.trans (hscaled.symm.trans hpairShift)
      have haqbq : aq ≠ bq := fun h =>
        hab0 (lemma6_finCyclicAdd_injective hnpos shift h)
      have hordered_bucket (a b' : Fin n) (hab : a.val < b'.val)
          (htargetPair' : Nat.ModEq (2 ^ n - 1)
            (2 ^ r.val + 2 ^ x.val + 2 ^ y.val)
            (2 ^ a.val + 2 ^ b'.val)) : False := by
        let gap := lemma6_finPairGap a0 b0
        let collisions := lemma6_finSupportedRepeatedExponentCollisions a b' gap
        have hgap_pos : 0 < gap := lemma6_finPairGap_pos_of_ne hab0
        have hgap_lt : gap < n := lemma6_finPairGap_lt a0 b0
        have hself_unsupported (z : Fin n) :
            ¬ lemma6_finPairSupported gap z z := by
          simp only [lemma6_finPairSupported, lemma6_finPairGap,
            Nat.sub_self, zero_add]
          omega
        have hcollision_card : collisions.card ≤ 1 := by
          by_cases hleft : a.val + 1 < b'.val
          · by_cases hright : b'.val - a.val + 1 < n
            · exact lemma6_odd_finSupportedRepeatedExponentCollisions_card_le_one
                hn_odd hnpos a b' gap hleft hright
            · have ha0 : a.val = 0 := by omega
              have hbtop : b'.val + 1 = n := by omega
              have hsucc : lemma6_finCyclicSucc hnpos b' = a := by
                apply Fin.ext
                simp only [lemma6_finCyclicSucc]
                rw [hbtop, Nat.mod_self, ha0]
              rw [Finset.card_le_one]
              intro p hp q' hq'
              simp only [collisions,
                lemma6_finSupportedRepeatedExponentCollisions,
                Finset.mem_filter, Finset.mem_univ, true_and] at hp hq'
              have hpClass := lemma6_repeated_two_pow_collision_fin_classify
                hnpos a b' p.1 p.2 hab hp.1
              have hqClass := lemma6_repeated_two_pow_collision_fin_classify
                hnpos a b' q'.1 q'.2 hab hq'.1
              have hpFirst :
                  p.1 = a ∧ lemma6_finCyclicSucc hnpos p.2 = b' := by
                rcases hpClass with hpFirst | hpSecond
                · exact hpFirst
                · exfalso
                  apply hself_unsupported p.1
                  have hp2 : p.2 = b' :=
                    lemma6_finCyclicSucc_injective hnpos
                      (hpSecond.2.trans hsucc.symm)
                  have hp12 : p.1 = p.2 := hpSecond.1.trans hp2.symm
                  simpa only [hp12] using hp.2
              have hqFirst :
                  q'.1 = a ∧ lemma6_finCyclicSucc hnpos q'.2 = b' := by
                rcases hqClass with hqFirst | hqSecond
                · exact hqFirst
                · exfalso
                  apply hself_unsupported q'.1
                  have hq2 : q'.2 = b' :=
                    lemma6_finCyclicSucc_injective hnpos
                      (hqSecond.2.trans hsucc.symm)
                  have hq12 : q'.1 = q'.2 := hqSecond.1.trans hq2.symm
                  simpa only [hq12] using hq'.2
              exact Prod.ext (hpFirst.1.trans hqFirst.1.symm)
                (lemma6_finCyclicSucc_injective hnpos
                  (hpFirst.2.trans hqFirst.2.symm))
          · have habSucc : a.val + 1 = b'.val := by omega
            have hsucc : lemma6_finCyclicSucc hnpos a = b' := by
              apply Fin.ext
              simp only [lemma6_finCyclicSucc]
              rw [Nat.mod_eq_of_lt (by omega)]
              exact habSucc
            rw [Finset.card_le_one]
            intro p hp q' hq'
            simp only [collisions,
              lemma6_finSupportedRepeatedExponentCollisions,
              Finset.mem_filter, Finset.mem_univ, true_and] at hp hq'
            have hpClass := lemma6_repeated_two_pow_collision_fin_classify
              hnpos a b' p.1 p.2 hab hp.1
            have hqClass := lemma6_repeated_two_pow_collision_fin_classify
              hnpos a b' q'.1 q'.2 hab hq'.1
            have hpSecond :
                p.1 = b' ∧ lemma6_finCyclicSucc hnpos p.2 = a := by
              rcases hpClass with hpFirst | hpSecond
              · exfalso
                apply hself_unsupported p.1
                have hp2 : p.2 = a :=
                  lemma6_finCyclicSucc_injective hnpos
                    (hpFirst.2.trans hsucc.symm)
                have hp12 : p.1 = p.2 := hpFirst.1.trans hp2.symm
                simpa only [hp12] using hp.2
              · exact hpSecond
            have hqSecond :
                q'.1 = b' ∧ lemma6_finCyclicSucc hnpos q'.2 = a := by
              rcases hqClass with hqFirst | hqSecond
              · exfalso
                apply hself_unsupported q'.1
                have hq2 : q'.2 = a :=
                  lemma6_finCyclicSucc_injective hnpos
                    (hqFirst.2.trans hsucc.symm)
                have hq12 : q'.1 = q'.2 := hqFirst.1.trans hq2.symm
                simpa only [hq12] using hq'.2
              · exact hqSecond
            exact Prod.ext (hpSecond.1.trans hqSecond.1.symm)
              (lemma6_finCyclicSucc_injective hnpos
                (hpSecond.2.trans hqSecond.2.symm))
        have hbucket_finish : False := by
          have hinner_ne : bracketK (u x) (u y) ≠ 0 := by
            intro hzero
            apply htarget_raw
            rw [hzero, map_zero]
          let pt : Fin n × Fin n := if r = x then (y, x) else (x, y)
          have hpt_exponent :
              2 ^ pt.1.val + 2 ^ pt.2.val + 2 ^ pt.2.val =
                2 ^ r.val + 2 ^ x.val + 2 ^ y.val := by
            by_cases hrx : r = x
            · subst r
              simp only [pt, if_pos rfl]
              omega
            · have hry : r = y := hr.resolve_left hrx
              subst r
              simp only [pt, if_neg hrx]
              omega
          have hpt_support : lemma6_finPairSupported gap pt.1 pt.2 := by
            by_cases hrx : r = x
            · subst r
              simpa only [pt, if_pos rfl] using
                lemma6_finPairSupported_symm (hsupport x y hinner_ne)
            · have hry : r = y := hr.resolve_left hrx
              subst r
              simpa only [pt, if_neg hrx] using hsupport x y hinner_ne
          have hpt_mem : pt ∈ collisions := by
            simp only [collisions,
              lemma6_finSupportedRepeatedExponentCollisions,
              Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · rw [hpt_exponent]
              exact htargetPair'
            · exact hpt_support
          have hbucket := lemma6_eigenvalueBucket_eq_zero
            ((lowerCentralFactorLinearAut xi 1).baseChange (ZMod 2)
              (BinaryGaloisField n)
              (Additive (LowerCentralFactor H 1))
              (Additive (LowerCentralFactor H 1))).toLinearMap
            triples multiplier value hvalue_eigen hflat_sum (multiplier target)
          have hunique (p : Fin n × (Fin n × Fin n)) (hp : p ∈ triples)
              (hpmultiplier : multiplier p = multiplier target) :
              p = target ∨ value p = 0 := by
            rcases p with ⟨i, j, k⟩
            have hij : i.val < j.val := by
              have hij' : i < j := by
                simpa only [triples, Finset.mem_filter, Finset.mem_univ,
                  Finset.mem_Ioi, true_and] using hp
              exact Fin.lt_def.mp hij'
            have hij_ne : i ≠ j := by omega
            have hunitMultiplier :
                lambdaUnit ^ (2 ^ k.val + 2 ^ i.val + 2 ^ j.val) =
                  lambdaUnit ^ (2 ^ r.val + 2 ^ x.val + 2 ^ y.val) := by
              apply Units.ext
              simpa only [lambdaUnit, multiplier, target,
                Units.val_pow_eq_pow_val, Units.val_mk0] using hpmultiplier
            have hmodMultiplier : Nat.ModEq (2 ^ n - 1)
                (2 ^ k.val + 2 ^ i.val + 2 ^ j.val)
                (2 ^ r.val + 2 ^ x.val + 2 ^ y.val) := by
              have h := pow_eq_pow_iff_modEq.mp hunitMultiplier
              simpa only [lambdaUnit, hlambda_order] using h
            by_cases hki : k = i
            · subst k
              by_cases hinner : bracketK (u i) (u j) = 0
              · right
                simp only [value, hinner, map_zero]
              · let pc : Fin n × Fin n := (j, i)
                have hpc_support :
                    lemma6_finPairSupported gap pc.1 pc.2 := by
                  simpa only [pc] using
                    lemma6_finPairSupported_symm (hsupport i j hinner)
                have hpc_mod : Nat.ModEq (2 ^ n - 1)
                    (2 ^ pc.1.val + 2 ^ pc.2.val + 2 ^ pc.2.val)
                    (2 ^ a.val + 2 ^ b'.val) := by
                  have h := hmodMultiplier.trans htargetPair'
                  simpa only [pc, add_assoc, add_comm, add_left_comm] using h
                have hpc_mem : pc ∈ collisions := by
                  simp only [collisions,
                    lemma6_finSupportedRepeatedExponentCollisions,
                    Finset.mem_filter, Finset.mem_univ, true_and]
                  exact ⟨hpc_mod, hpc_support⟩
                have hpceq : pc = pt :=
                  (Finset.card_le_one.mp hcollision_card) pc hpc_mem pt hpt_mem
                left
                by_cases hrx : r = x
                · subst r
                  simp only [pc, pt, if_pos rfl, Prod.mk.injEq] at hpceq
                  rcases hpceq with ⟨hjy, hix⟩
                  subst j
                  subst i
                  rfl
                · have hry : r = y := hr.resolve_left hrx
                  subst r
                  simp only [pc, pt, if_neg hrx, Prod.mk.injEq] at hpceq
                  rcases hpceq with ⟨hjx, hiy⟩
                  exfalso
                  omega
            · by_cases hkj : k = j
              · subst k
                by_cases hinner : bracketK (u i) (u j) = 0
                · right
                  simp only [value, hinner, map_zero]
                · let pc : Fin n × Fin n := (i, j)
                  have hpc_support :
                      lemma6_finPairSupported gap pc.1 pc.2 := by
                    simpa only [pc] using hsupport i j hinner
                  have hpc_mod : Nat.ModEq (2 ^ n - 1)
                      (2 ^ pc.1.val + 2 ^ pc.2.val + 2 ^ pc.2.val)
                      (2 ^ a.val + 2 ^ b'.val) := by
                    have h := hmodMultiplier.trans htargetPair'
                    simpa only [pc, add_assoc, add_comm, add_left_comm] using h
                  have hpc_mem : pc ∈ collisions := by
                    simp only [collisions,
                      lemma6_finSupportedRepeatedExponentCollisions,
                      Finset.mem_filter, Finset.mem_univ, true_and]
                    exact ⟨hpc_mod, hpc_support⟩
                  have hpceq : pc = pt :=
                    (Finset.card_le_one.mp hcollision_card) pc hpc_mem pt hpt_mem
                  left
                  by_cases hrx : r = x
                  · subst r
                    simp only [pc, pt, if_pos rfl, Prod.mk.injEq] at hpceq
                    rcases hpceq with ⟨hiy, hjx⟩
                    exfalso
                    omega
                  · have hry : r = y := hr.resolve_left hrx
                    subst r
                    simp only [pc, pt, if_neg hrx, Prod.mk.injEq] at hpceq
                    rcases hpceq with ⟨hix, hjy⟩
                    subst i
                    subst j
                    rfl
              · right
                simp only [value, hdistinct i j k hij_ne hki hkj, map_zero]
          have htarget_zero := lemma6_finset_bucket_target_eq_zero
            triples multiplier value target htarget_mem hbucket hunique
          exact htarget_value htarget_zero
        exact hbucket_finish
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne haqbq) with hab | hba
      · exact hordered_bucket aq bq hab htargetPair
      · apply hordered_bucket bq aq hba
        simpa only [add_comm] using htargetPair
    exact hfinish
  have hrepeat_left (i j : Fin n) :
      lemma6_scalarExtendBilinear lemma6_lowerCentralIteratedBracket
        (u i) (bracketK (u i) (u j)) = 0 := by
    by_cases hij : i = j
    · subst j
      rw [hbracketK_self, map_zero]
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hij' | hji'
    · exact hrepeat_ordered i j i hij' (Or.inl rfl)
    · rw [hbracketK_symm]
      exact hrepeat_ordered j i i hji' (Or.inr rfl)
  have hrepeat_right (i j : Fin n) :
      lemma6_scalarExtendBilinear lemma6_lowerCentralIteratedBracket
        (u j) (bracketK (u i) (u j)) = 0 := by
    by_cases hij : i = j
    · subst j
      rw [hbracketK_self, map_zero]
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hij' | hji'
    · exact hrepeat_ordered i j j hij' (Or.inr rfl)
    · rw [hbracketK_symm]
      exact hrepeat_ordered j i j hji' (Or.inl rfl)
  intro i j k
  by_cases hij : i = j
  · subst j
    rw [hbracketK_self, map_zero]
  by_cases hki : k = i
  · subst k
    exact hrepeat_left i j
  by_cases hkj : k = j
  · subst k
    exact hrepeat_right i j
  exact hdistinct i j k hij hki hkj
/-- Final source step of Higman Lemma 6: in odd common dimension, Lemma 5's
conjugate eigenbasis and square formula force every spanning triple bracket to
vanish. -/
private theorem lemma6_odd_triple_bracket_core
    {H : Type u} [Group H] [Finite H]
    (hH_two : IsPGroup 2 H)
    (hH_nonabelian : ¬ IsMulCommutative H)
    (xi : MulAut H)
    (hxi_odd : Odd (orderOf xi))
    (hL1_irreducible :
      ∀ W : Submodule (ZMod 2) (Additive (LowerCentralFactor H 0)),
        (∀ v : Additive (LowerCentralFactor H 0), v ∈ W →
          lowerCentralFactorLinearAut xi 0 v ∈ W) →
        W = ⊥ ∨ W = ⊤)
    (hL2_transitive :
      ∀ x : Additive (LowerCentralFactor H 1), x ≠ 0 →
        ∀ y : Additive (LowerCentralFactor H 1), y ≠ 0 →
          ∃ k : ℕ, (lowerCentralFactorLinearAut xi 1 ^ k) x = y)
    (n : ℕ) (hn : 2 ≤ n)
    (hL2_card : Nat.card (LowerCentralFactor H 1) = 2 ^ n)
    (hH_square : squaresSubgroup H ≤ higmanLowerCentralSeries H 1)
    (e : Additive (LowerCentralFactor H 2) ≃ₗ[ZMod 2]
      Additive (LowerCentralFactor H 1))
    (he : ∀ v : Additive (LowerCentralFactor H 2),
      e (lowerCentralFactorLinearAut xi 2 v) =
        lowerCentralFactorLinearAut xi 1 (e v))
    (hsync : lemma6ActionOrderSyncData xi n)
    (hn_odd : Odd n) :
    False := by
  classical
  obtain ⟨m, hm, lambda, coordinates, u, xiK, bracket, bracketK,
      squareMap, hL1_card, hlambda, hcoordinates, hxiK_tmul,
      hu_eigen, hu_expansion, hbracketK_tmul, hbracket_mk,
      hsquare_mk, _hsquare_equivariant, _hsquare_add,
      hsquare_formula⟩ :=
    lemma5_square_map_normal_form hH_two hH_nonabelian xi hxi_odd
      hL1_irreducible hL2_transitive n hn hL2_card hH_square
  have hmn : m = n := by
    apply Nat.pow_right_injective (by omega : 1 < 2)
    exact hL1_card.symm.trans hsync.2.2.2.1
  subst m
  have hlambda_order :
      orderOf (Units.mk0 lambda hlambda) = 2 ^ n - 1 := by
    calc
      orderOf (Units.mk0 lambda hlambda) =
          orderOf (lowerCentralFactorLinearAut xi 0) :=
        (lemma6_coordinate_unit_order
          (lowerCentralFactorLinearAut xi 0) coordinates lambda hlambda
          hcoordinates).symm
      _ = 2 ^ n - 1 := hsync.1
  obtain ⟨_hbracket_equivariant, _hbracketK_equivariant,
      _hbracket_self, _hbracketK_self, hbracket_span⟩ :=
    lemma5_lowerCentralBracket_interfaces xi n xiK bracket bracketK
      hxiK_tmul hbracketK_tmul hbracket_mk
  have htriples : ∀ i j k : Fin n,
      lemma6_scalarExtendBilinear lemma6_lowerCentralIteratedBracket
          (u k) (bracketK (u i) (u j)) = 0 :=
    lemma6_odd_basis_triples_vanish_core xi hL2_transitive n hn hn_odd
      hL2_card hH_square e he lambda hlambda hlambda_order coordinates u xiK
      bracket bracketK squareMap hxiK_tmul hu_eigen hu_expansion
      hbracketK_tmul hbracket_mk hsquare_mk hsquare_formula
  have htensor_expansion
      (v : Additive (LowerCentralFactor H 0)) :
      (1 : BinaryGaloisField n) ⊗ₜ[ZMod 2] v =
        ∑ i : Fin n,
          (coordinates.symm v) ^ (2 ^ (i : ℕ)) • u i := by
    simpa using hu_expansion (coordinates.symm v)
  have hC_on_bracket
      (z v w : Additive (LowerCentralFactor H 0)) :
      lemma6_lowerCentralIteratedBracket z (bracket v w) = 0 := by
    have htensor_zero :
        (1 : BinaryGaloisField n) ⊗ₜ[ZMod 2]
            lemma6_lowerCentralIteratedBracket z (bracket v w) = 0 := by
      calc
        (1 : BinaryGaloisField n) ⊗ₜ[ZMod 2]
              lemma6_lowerCentralIteratedBracket z (bracket v w) =
            lemma6_scalarExtendBilinear lemma6_lowerCentralIteratedBracket
              ((1 : BinaryGaloisField n) ⊗ₜ[ZMod 2] z)
              ((1 : BinaryGaloisField n) ⊗ₜ[ZMod 2] bracket v w) :=
          (lemma6_scalarExtendBilinear_tmul
            lemma6_lowerCentralIteratedBracket z (bracket v w)).symm
        _ = lemma6_scalarExtendBilinear lemma6_lowerCentralIteratedBracket
              ((1 : BinaryGaloisField n) ⊗ₜ[ZMod 2] z)
              (bracketK
                ((1 : BinaryGaloisField n) ⊗ₜ[ZMod 2] v)
                ((1 : BinaryGaloisField n) ⊗ₜ[ZMod 2] w)) := by
          rw [hbracketK_tmul]
        _ = lemma6_scalarExtendBilinear lemma6_lowerCentralIteratedBracket
              (∑ k : Fin n,
                (coordinates.symm z) ^ (2 ^ (k : ℕ)) • u k)
              (bracketK
                (∑ i : Fin n,
                  (coordinates.symm v) ^ (2 ^ (i : ℕ)) • u i)
                (∑ j : Fin n,
                  (coordinates.symm w) ^ (2 ^ (j : ℕ)) • u j)) := by
          rw [htensor_expansion z, htensor_expansion v,
            htensor_expansion w]
        _ = 0 := by
          simp only [map_sum, map_smul, LinearMap.sum_apply,
            LinearMap.smul_apply, htriples, smul_zero,
            Finset.sum_const_zero]
    exact (Module.FaithfullyFlat.one_tmul_eq_zero_iff
      (ZMod 2) (Additive (LowerCentralFactor H 2))
      (A := BinaryGaloisField n)
      (lemma6_lowerCentralIteratedBracket z (bracket v w))).mp htensor_zero
  have hC_point
      (z : Additive (LowerCentralFactor H 0)) :
      lemma6_lowerCentralIteratedBracket z = 0 := by
    rw [Submodule.linearMap_eq_zero_iff_of_span_eq_top
      (lemma6_lowerCentralIteratedBracket z) hbracket_span]
    rintro ⟨_y, ⟨p, rfl⟩⟩
    exact hC_on_bracket z p.1 p.2
  have hC_zero : lemma6_lowerCentralIteratedBracket (H := H) = 0 := by
    apply LinearMap.ext
    intro z
    exact hC_point z
  have hL2_add_card :
      Nat.card (Additive (LowerCentralFactor H 1)) = 2 ^ n :=
    (Nat.card_congr
      (Additive.toMul : Additive (LowerCentralFactor H 1) ≃
        LowerCentralFactor H 1)).trans hL2_card
  let : Nontrivial (Additive (LowerCentralFactor H 1)) := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    have hcard_one : Nat.card (Additive (LowerCentralFactor H 1)) = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨hsub, inferInstance⟩
    rw [hL2_add_card] at hcard_one
    have hpow_gt : 1 < 2 ^ n := by
      have : 2 ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    omega
  let : Nontrivial (Additive (LowerCentralFactor H 2)) :=
    e.toEquiv.nontrivial
  have hspan_zero :
      Submodule.span (ZMod 2)
        (Set.range fun p : Additive (LowerCentralFactor H 0) ×
            Additive (LowerCentralFactor H 1) =>
          lemma6_lowerCentralIteratedBracket p.1 p.2) = ⊥ := by
    rw [hC_zero]
    simp
  have hbot_top :
      (⊥ : Submodule (ZMod 2) (Additive (LowerCentralFactor H 2))) = ⊤ :=
    hspan_zero.symm.trans lemma6_lowerCentralIteratedBracket_span
  exact bot_ne_top hbot_top
/-- Higman Lemma 6. Under the source hypothesis H² = H₂, the source factors
L₃ and L₂ are not xi-isomorphic as F₂[xi]-modules. -/
public theorem lemma6_third_factor_nonisomorphic
    {H : Type u} [Group H] [Finite H]
    (hH_two : IsPGroup 2 H)
    (hH_nonabelian : ¬ IsMulCommutative H)
    (xi : MulAut H)
    (hxi_odd : Odd (orderOf xi))
    (hL1_irreducible :
      ∀ W : Submodule (ZMod 2) (Additive (LowerCentralFactor H 0)),
        (∀ v : Additive (LowerCentralFactor H 0), v ∈ W →
          lowerCentralFactorLinearAut xi 0 v ∈ W) →
        W = ⊥ ∨ W = ⊤)
    (hL2_transitive :
      ∀ x : Additive (LowerCentralFactor H 1), x ≠ 0 →
        ∀ y : Additive (LowerCentralFactor H 1), y ≠ 0 →
          ∃ k : ℕ, (lowerCentralFactorLinearAut xi 1 ^ k) x = y)
    (n : ℕ) (hn : 2 ≤ n)
    (hL2_card : Nat.card (LowerCentralFactor H 1) = 2 ^ n)
    (hH_square : squaresSubgroup H ≤ higmanLowerCentralSeries H 1) :
    ¬ ∃ e : Additive (LowerCentralFactor H 2) ≃ₗ[ZMod 2]
        Additive (LowerCentralFactor H 1),
      ∀ v : Additive (LowerCentralFactor H 2),
        e (lowerCentralFactorLinearAut xi 2 v) =
          lowerCentralFactorLinearAut xi 1 (e v) := by
  rintro ⟨e, he⟩
  have hsync := lemma6_action_order_sync_core
    xi hL1_irreducible hL2_transitive n hn hL2_card e he
  rcases Nat.even_or_odd n with hn_even | hn_odd
  · exact lemma6_even_dimension_contradiction_core
      hH_two hH_nonabelian xi hxi_odd hL1_irreducible hL2_transitive
        n hn hL2_card hH_square e he hsync hn_even
  · exact lemma6_odd_triple_bracket_core
      hH_two hH_nonabelian xi hxi_odd hL1_irreducible hL2_transitive
        n hn hL2_card hH_square e he hsync hn_odd

end Higman
end External
end CFSG.BenderSuzuki
