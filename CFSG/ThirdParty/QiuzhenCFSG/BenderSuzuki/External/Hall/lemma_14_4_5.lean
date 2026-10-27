module

import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.Module.ZMod
import Mathlib.Data.Nat.Choose.Dvd
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Hall.lemma_14_4_4

namespace CFSG
end CFSG
open CFSG

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

/-!
# Hall Lemma 14.4.5

Source interface for the double-coset cycle factors `d_j(u)` and their Engel
commutator congruence.
-/

namespace CFSG.BenderSuzuki
namespace External

open PFchapter1section1
open scoped Pointwise

universe u v

set_option maxRecDepth 2000 in
/-- Source-faithful cycle-factor data surrounding Hall Lemma 14.4.5.  The
list records the active `p`-cycles for each `u`, while `Zs` records the
finitely many fixed choices `z_i` coming from the nontrivial double-coset
permutation representations. -/
@[expose] public noncomputable def hallCycleFactorDataIn
    {G : Type u} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (P₁ : Sylow p G) (N₁ H₁ G₀ H P H₀ K : Subgroup G)
    (hN₁ : N₁ = Subgroup.normalizer ((P₁ : Subgroup G) : Set G))
    (hN₁_le_H₁ : N₁ ≤ H₁)
    (hG₀ : G₀ = hallPResidual p G)
    (hH : H = G₀ ⊓ H₁)
    (hP : P = G₀ ⊓ (P₁ : Subgroup G))
    (hH₀ : H₀ = hallTransferModulus p H H₁) : Prop := by
  have hH_le_G₀ : H ≤ G₀ := by
    rw [hH]
    exact inf_le_left
  have hH_le_H₁ : H ≤ H₁ := by
    rw [hH]
    exact inf_le_right
  have hP₁_le_H₁ : (P₁ : Subgroup G) ≤ H₁ :=
    Subgroup.le_normalizer.trans (hN₁ ▸ hN₁_le_H₁)
  have hP_le_H : P ≤ H := by
    rw [hP, hH]
    exact inf_le_inf le_rfl hP₁_le_H₁
  have hH₀_le_H : H₀ ≤ H := by
    rw [hH₀]
    exact hallTransferModulus_le_of_inf p H₁ G₀ H hG₀ hH
  have hH₀_normal : (H₀.subgroupOf H).Normal := by
    subst H₀
    exact hallTransferModulus_subgroupOf_normal p H H₁ hH_le_H₁
      (hallTransferModulus_le_of_inf p H₁ G₀ H hG₀ hH)
  have hcomm : commutator H ≤ H₀.subgroupOf H := by
    intro x hx
    have hxmap : H.subtype x ∈ (commutator H).map H.subtype :=
      Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    rw [Subgroup.map_subtype_commutator] at hxmap
    have hC : ⁅H, H₁⁆ ≤ H₀ := by
      rw [hH₀]
      exact le_sup_right.trans le_sup_left
    exact hC ((Subgroup.commutator_mono le_rfl hH_le_H₁) hxmap)
  letI : IsMulCommutative (H ⧸ H₀.subgroupOf H) :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le).2 hcomm
  letI : CommGroup (H ⧸ H₀.subgroupOf H) := IsMulCommutative.instCommGroup
  let HG₀ : Subgroup G₀ := H.subgroupOf G₀
  let eH : HG₀ ≃* H := Subgroup.subgroupOfEquivOfLe hH_le_G₀
  let π : H →* H ⧸ H₀.subgroupOf H := QuotientGroup.mk' (H₀.subgroupOf H)
  let φ : HG₀ →* H ⧸ H₀.subgroupOf H := π.comp eH.toMonoidHom
  exact ∃ Zs : Finset G, ∃ cycleFactors : H → List H,
    (∀ z : G, z ∈ Zs → z ∈ K) ∧
    (∀ u : H, (u : G) ∈ P →
      hallDiagonalDefect (G := G₀) (H := HG₀) φ (eH.symm u) =
        ((cycleFactors u).map π).prod) ∧
    (∀ u : H, (u : G) ∈ P → ∀ d : H, d ∈ cycleFactors u →
      ∃ z : G, z ∈ Zs ∧ ∃ w : G, w ∈ G₀ ∧
        w * engelSymbol p (u : G) z * w⁻¹ ∈ H ∧
        (d : G) / (w * engelSymbol p (u : G) z * w⁻¹) ∈ H₀) ∧
    H ≤ H₀ ⊔ Subgroup.closure
      {x : G | ∃ u : H, (u : G) ∈ P ∧
        ∃ d : H, d ∈ cycleFactors u ∧ x = (d : G)}


private noncomputable def hallResidualCosetEquiv
    {G : Type u} [Group G] (G₀ H₁ H : Subgroup G) [G₀.Normal]
    (hH : H = G₀ ⊓ H₁) (hSup : G₀ ⊔ H₁ = ⊤) :
    G₀ ⧸ H.subgroupOf G₀ ≃ G ⧸ H₁ := by
  let f : G₀ ⧸ H.subgroupOf G₀ → G ⧸ H₁ :=
    Quotient.map' G₀.subtype (by
      intro a b hab
      rw [QuotientGroup.leftRel_eq] at hab ⊢
      have habH : (a : G)⁻¹ * (b : G) ∈ H := hab
      rw [hH] at habH
      exact habH.2)
  apply Equiv.ofBijective f
  constructor
  · refine Quotient.ind₂' ?_
    intro a b hab
    apply QuotientGroup.eq.mpr
    change a⁻¹ * b ∈ H.subgroupOf G₀
    change (a : G)⁻¹ * (b : G) ∈ H
    rw [hH]
    exact ⟨G₀.mul_mem (G₀.inv_mem a.property) b.property,
      QuotientGroup.eq.mp hab⟩
  · refine Quotient.ind' ?_
    intro g
    have hg : g ∈ G₀ ⊔ H₁ := by
      rw [hSup]
      simp
    rw [← SetLike.mem_coe, Subgroup.normal_mul] at hg
    rcases hg with ⟨n, hn, h, hh, rfl⟩
    refine ⟨QuotientGroup.mk ⟨n, hn⟩, ?_⟩
    apply QuotientGroup.eq.mpr
    change (n : G)⁻¹ * (n * h) ∈ H₁
    simpa [mul_assoc] using hh


private def hallResidualCosetLeftMul
    {G : Type u} [Group G] (G₀ H : Subgroup G) (u : G₀) :
    G₀ ⧸ H.subgroupOf G₀ → G₀ ⧸ H.subgroupOf G₀ :=
  Quotient.map' (fun x : G₀ => u * x) (by
    intro a b hab
    rw [QuotientGroup.leftRel_eq] at hab ⊢
    simpa [mul_assoc] using hab)

private theorem hallResidualCosetEquiv_leftMul
    {G : Type u} [Group G] (G₀ H₁ H : Subgroup G) [G₀.Normal]
    (hH : H = G₀ ⊓ H₁) (hSup : G₀ ⊔ H₁ = ⊤)
    (u : G₀) (q : G₀ ⧸ H.subgroupOf G₀) :
    hallResidualCosetEquiv G₀ H₁ H hH hSup
        (hallResidualCosetLeftMul G₀ H u q) =
      ((u : G) • hallResidualCosetEquiv G₀ H₁ H hH hSup q : G ⧸ H₁) := by
  refine Quotient.inductionOn' q ?_
  intro x
  rfl

private noncomputable def hallFixedPointRestriction
    {X : Type u} [Finite X] (u z : Equiv.Perm X) (hcomm : Commute z u) :
    Equiv.Perm (Function.fixedPoints u) := by
  have hzcent : z ∈ Subgroup.centralizer ({u} : Set (Equiv.Perm X)) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcomm.eq
  exact z.subtypePerm fun x =>
    Equiv.Perm.apply_mem_fixedPoints_iff_mem_of_mem_centralizer hzcent

private theorem hallFixedPointRestriction_apply
    {X : Type u} [Finite X] (u z : Equiv.Perm X) (hcomm : Commute z u)
    (x : Function.fixedPoints u) :
    (hallFixedPointRestriction u z hcomm x : X) = z x := by
  rfl

private theorem hallFixedPointRestriction_free
    {X : Type u} [Finite X] (u z : Equiv.Perm X) (hcomm : Commute z u)
    (hzfree : ∀ x : X, z x ≠ x) :
    ∀ x : Function.fixedPoints u, hallFixedPointRestriction u z hcomm x ≠ x := by
  intro x hx
  apply hzfree x
  exact congrArg Subtype.val hx

private theorem hallFixedPointRestriction_pow
    {X : Type u} [Finite X] (p : ℕ) (u z : Equiv.Perm X)
    (hcomm : Commute z u) (hzpow : z ^ p = 1) :
    hallFixedPointRestriction u z hcomm ^ p = 1 := by
  unfold hallFixedPointRestriction
  rw [Equiv.Perm.subtypePerm_pow]
  apply Equiv.Perm.ext
  intro x
  apply Subtype.ext
  change (z ^ p) x = x
  rw [hzpow]
  rfl


private theorem hall_prime_action_minimalPeriod
    {X : Type u} [Finite X] (p : ℕ) [Fact p.Prime]
    (z : Equiv.Perm X) (hzorder : orderOf z = p)
    (hzfree : ∀ x : X, z x ≠ x) (x : X) :
    Function.minimalPeriod (z • ·) x = p := by
  apply Function.minimalPeriod_eq_prime
  · change (z ^ p) x = x
    rw [← hzorder, pow_orderOf_eq_one]
    rfl
  · exact hzfree x

private theorem hall_zmod_cycle_cast
    (m p : ℕ) [NeZero p] (h : m = p) (k : Fin p) :
    ZMod.ringEquivCongr h.symm ((ZMod.finEquiv p) k) = (k.val : ZMod m) := by
  subst m
  rw [ZMod.ringEquivCongr_refl_apply]
  cases p with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ p =>
      calc
        (ZMod.finEquiv (p + 1)) k =
            (((ZMod.finEquiv (p + 1) k).val : ℕ) : ZMod (p + 1)) :=
          (ZMod.natCast_zmod_val ((ZMod.finEquiv (p + 1)) k)).symm
        _ = (k.val : ZMod (p + 1)) := by rfl
private noncomputable def hallPrimeCycleEquiv
    {X : Type u} [Finite X] (p : ℕ) [Fact p.Prime]
    (z : Equiv.Perm X) (hzorder : orderOf z = p)
    (hzfree : ∀ x : X, z x ≠ x) :
    (Σ _q : Quotient (MulAction.orbitRel (Subgroup.zpowers z) X), Fin p) ≃ X :=
  (Equiv.sigmaCongrRight fun q =>
    (ZMod.finEquiv p).toEquiv |>.trans
      (ZMod.ringEquivCongr
        (hall_prime_action_minimalPeriod p z hzorder hzfree q.out).symm).toEquiv |>.trans
      (MulAction.orbitZPowersEquiv z q.out).symm).trans
    (MulAction.selfEquivSigmaOrbits (Subgroup.zpowers z) X).symm

private theorem hallPrimeCycleEquiv_apply
    {X : Type u} [Finite X] (p : ℕ) [Fact p.Prime]
    (z : Equiv.Perm X) (hzorder : orderOf z = p)
    (hzfree : ∀ x : X, z x ≠ x)
    (q : Quotient (MulAction.orbitRel (Subgroup.zpowers z) X)) (k : Fin p) :
    hallPrimeCycleEquiv p z hzorder hzfree ⟨q, k⟩ = (z ^ (k : ℕ)) q.out := by
  let hm := hall_prime_action_minimalPeriod p z hzorder hzfree q.out
  change (((MulAction.orbitZPowersEquiv z q.out).symm
    (ZMod.ringEquivCongr hm.symm ((ZMod.finEquiv p) k)) :
      MulAction.orbit (Subgroup.zpowers z) q.out) : X) = _
  rw [hall_zmod_cycle_cast _ _ hm k, MulAction.orbitZPowersEquiv_symm_apply]
  change (z ^ (ZMod.cast (k.val : ZMod (Function.minimalPeriod (z • ·) q.out)) : ℤ))
    q.out = (z ^ (k : ℕ)) q.out
  rw [ZMod.cast_eq_val]
  have hkm : k.val < Function.minimalPeriod (z • ·) q.out := by
    rw [hm]
    exact k.isLt
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hkm, zpow_natCast]

private noncomputable def hallPrimeCycleEquivOfPowFree
    {X : Type u} [Finite X] (p : ℕ) [Fact p.Prime]
    (z : Equiv.Perm X) (hzpow : z ^ p = 1)
    (hzfree : ∀ x : X, z x ≠ x) :
    (Σ _q : Quotient (MulAction.orbitRel (Subgroup.zpowers z) X), Fin p) ≃ X := by
  classical
  by_cases hX : Nonempty X
  · letI : Nonempty X := hX
    apply hallPrimeCycleEquiv p z
    · apply orderOf_eq_prime hzpow
      intro hzone
      let x : X := Classical.choice hX
      apply hzfree x
      have hx := congrArg (fun σ : Equiv.Perm X => σ x) hzone
      simpa using hx
    · exact hzfree
  · haveI : IsEmpty X := not_nonempty_iff.mp hX
    exact Equiv.equivOfIsEmpty _ _

private theorem hallPrimeCycleEquivOfPowFree_apply
    {X : Type u} [Finite X] (p : ℕ) [Fact p.Prime]
    (z : Equiv.Perm X) (hzpow : z ^ p = 1)
    (hzfree : ∀ x : X, z x ≠ x)
    (q : Quotient (MulAction.orbitRel (Subgroup.zpowers z) X)) (k : Fin p) :
    hallPrimeCycleEquivOfPowFree p z hzpow hzfree ⟨q, k⟩ =
      (z ^ (k : ℕ)) q.out := by
  classical
  have hX : Nonempty X := ⟨q.out⟩
  rw [hallPrimeCycleEquivOfPowFree]
  split
  · rename_i hnonempty
    letI : Nonempty X := hnonempty
    apply hallPrimeCycleEquiv_apply
  · rename_i hempty
    exact (hempty hX).elim
private theorem hall_zmod_prime_cycle_succ
    {X : Type*} (p : ℕ) [NeZero p] (z : Equiv.Perm X)
    (hzorder : orderOf z = p) (j : ZMod p) (x : X) :
    z ((z ^ j.val) x) = (z ^ (j + 1).val) x := by
  change (z * z ^ j.val) x = (z ^ (j + 1).val) x
  rw [← pow_succ']
  congr 1
  apply (pow_eq_pow_iff_modEq).2
  rw [hzorder]
  apply (ZMod.natCast_eq_natCast_iff _ _ p).mp
  rw [ZMod.natCast_zmod_val]
  simp
private theorem hall_prime_cast_choose_pred
    (p : ℕ) [Fact p.Prime] {k : ℕ} (hk : k < p) :
    ((Nat.choose (p - 1) k : ℕ) : ZMod p) = (-1 : ZMod p) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hk' : k < p := (Nat.lt_succ_self k).trans hk
      have hdiv : p ∣ p.choose (k + 1) :=
        (Fact.out : p.Prime).dvd_choose_self (Nat.succ_ne_zero k) hk
      have hcast : ((p.choose (k + 1) : ℕ) : ZMod p) = 0 :=
        (ZMod.natCast_eq_zero_iff _ _).2 hdiv
      have hp_eq : p = (p - 1) + 1 := by
        omega
      have hchoose : p.choose (k + 1) =
          (p - 1).choose k + (p - 1).choose (k + 1) := by
        conv_lhs => rw [hp_eq]
        exact Nat.choose_succ_succ' (p - 1) k
      rw [hchoose, Nat.cast_add, ih hk'] at hcast
      calc
        ((Nat.choose (p - 1) (k + 1) : ℕ) : ZMod p) =
            -((-1 : ZMod p) ^ k) := eq_neg_of_add_eq_zero_left (by simpa [add_comm] using hcast)
        _ = (-1 : ZMod p) ^ (k + 1) := by rw [pow_succ]; ring


private theorem hall_fwdDiff_prime_pred_eq_sum
    {A : Type*} [AddCommGroup A] (p : ℕ) [Fact p.Prime]
    (hpA : ∀ a : A, p • a = 0) (f : ZMod p → A) (y : ZMod p) :
    (fwdDiff (-1 : ZMod p))^[p - 1] f y =
      ∑ k ∈ Finset.range p, f (y - (k : ZMod p)) := by
  letI : Module (ZMod p) A := AddCommGroup.zmodModule hpA
  have hpred_succ : p - 1 + 1 = p := by
    exact Nat.sub_add_cancel (Fact.out : p.Prime).one_le
  have hneg : (-1 : ZMod p) ^ (p - 1) = 1 := by
    rcases (Fact.out : p.Prime).eq_two_or_odd with hp2 | hpodd
    · subst p
      simp
    · exact (Nat.Odd.sub_odd ((Nat.odd_iff).2 hpodd) odd_one).neg_one_pow
  have hcoeff : ∀ k < p,
      (((-1 : ℤ) ^ (p - 1 - k) * (Nat.choose (p - 1) k : ℤ) : ℤ) :
          ZMod p) = 1 := by
    intro k hk
    push_cast
    rw [hall_prime_cast_choose_pred p hk, ← pow_add,
      Nat.sub_add_cancel (Nat.le_sub_one_of_lt hk), hneg]
  rw [fwdDiff_iter_eq_sum_shift, hpred_succ]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k < p := Finset.mem_range.mp hk
  rw [← Int.cast_smul_eq_zsmul (ZMod p), hcoeff k hk', one_smul]
  congr 1
  simp [sub_eq_add_neg]

private theorem hall_cyclic_recurrence_prime_pred_eq_prod
    {A : Type*} [CommGroup A] (p : ℕ) [Fact p.Prime]
    (hpA : ∀ a : A, a ^ p = 1)
    (a : ℕ → ZMod p → A)
    (hrec : ∀ r : ℕ, ∀ y : ZMod p,
      a (r + 1) y = (a r y)⁻¹ * a r (y - 1))
    (y : ZMod p) :
    a (p - 1) y = ∏ k ∈ Finset.range p, a 0 (y - (k : ZMod p)) := by
  let f : ZMod p → Additive A := fun k => Additive.ofMul (a 0 k)
  have hpAdd : ∀ b : Additive A, p • b = 0 := by
    intro b
    change b.toMul ^ p = 1
    exact hpA b.toMul
  have hiter : ∀ r : ℕ, ∀ k : ZMod p,
      Additive.ofMul (a r k) = (fwdDiff (-1 : ZMod p))^[r] f k := by
    intro r
    induction r with
    | zero =>
        intro k
        rfl
    | succ r ih =>
        intro k
        rw [Function.iterate_succ_apply']
        change Additive.ofMul (a (r + 1) k) =
          (fwdDiff (-1 : ZMod p)) ((fwdDiff (-1 : ZMod p))^[r] f) k
        rw [hrec r k]
        simp [fwdDiff, ih, sub_eq_add_neg, add_comm]
  change Additive.ofMul (a (p - 1) y) =
    Additive.ofMul (∏ k ∈ Finset.range p, a 0 (y - (k : ZMod p)))
  rw [hiter]
  rw [hall_fwdDiff_prime_pred_eq_sum p hpAdd f y]
  simp [f]

private theorem hall_cycle_conjugate_step
    {G : Type*} [Group G] {p : ℕ}
    (u z : G) (w y : ZMod p → G)
    (hstep : ∀ k, w k * z = y k * w (k + 1))
    (r : ℕ) (k : ZMod p) :
    let ur := iteratedInverseFirstCommutator r u z
    w k * inverseFirstCommutator ur z * (w k)⁻¹ =
      (w k * ur * (w k)⁻¹)⁻¹ *
        (w (k - 1) * ur * (w (k - 1))⁻¹) *
        inverseFirstCommutator
          (w (k - 1) * ur * (w (k - 1))⁻¹) (y (k - 1)) := by
  let v := k - 1
  have hwz : w v * z = y v * w k := by
    simpa [v, sub_eq_add_neg, add_assoc] using hstep v
  have hleft : (w k)⁻¹ * (y v)⁻¹ = z⁻¹ * (w v)⁻¹ := by
    calc
      (w k)⁻¹ * (y v)⁻¹ = (y v * w k)⁻¹ := by simp
      _ = (w v * z)⁻¹ := by rw [← hwz]
      _ = z⁻¹ * (w v)⁻¹ := by simp
  have hright : (w v)⁻¹ * y v = z * (w k)⁻¹ := by
    calc
      (w v)⁻¹ * y v = (w v)⁻¹ * y v * w k * (w k)⁻¹ := by group
      _ = (w v)⁻¹ * (y v * w k) * (w k)⁻¹ := by group
      _ = (w v)⁻¹ * (w v * z) * (w k)⁻¹ := by rw [← hwz]
      _ = z * (w k)⁻¹ := by group
  let ur := iteratedInverseFirstCommutator r u z
  change w k * inverseFirstCommutator ur z * (w k)⁻¹ = _
  change _ = (w k * ur * (w k)⁻¹)⁻¹ *
    (w v * ur * (w v)⁻¹) *
      inverseFirstCommutator (w v * ur * (w v)⁻¹) (y v)
  calc
    w k * inverseFirstCommutator ur z * (w k)⁻¹ =
        w k * ur⁻¹ * z⁻¹ * ur * z * (w k)⁻¹ := by
          simp only [inverseFirstCommutator]
          group
    _ = w k * ur⁻¹ * (z⁻¹ * (w v)⁻¹) * w v * ur *
        (z * (w k)⁻¹) := by group
    _ = w k * ur⁻¹ * ((w k)⁻¹ * (y v)⁻¹) * w v * ur *
        ((w v)⁻¹ * y v) := by rw [← hleft, ← hright]
    _ = (w k * ur * (w k)⁻¹)⁻¹ * (w v * ur * (w v)⁻¹) *
        inverseFirstCommutator (w v * ur * (w v)⁻¹) (y v) := by
          simp only [inverseFirstCommutator]
          group

private theorem hall_cycle_conjugate_recurrence_mod
    {G : Type u} [Group G] {p : ℕ}
    (H H₀ H₁ : Subgroup G) (hH₀_le_H : H₀ ≤ H)
    [(H₀.subgroupOf H).Normal]
    (hcomm : ⁅H, H₁⁆ ≤ H₀)
    (u z : G) (w y : ZMod p → G)
    (a : ℕ → ZMod p → H)
    (ha : ∀ r k, (a r k : G) =
      w k * iteratedInverseFirstCommutator r u z * (w k)⁻¹)
    (hy : ∀ k, y k ∈ H₁)
    (hstep : ∀ k, w k * z = y k * w (k + 1))
    (r : ℕ) (k : ZMod p) :
    QuotientGroup.mk' (H₀.subgroupOf H) (a (r + 1) k) =
      (QuotientGroup.mk' (H₀.subgroupOf H) (a r k))⁻¹ *
        QuotientGroup.mk' (H₀.subgroupOf H) (a r (k - 1)) := by
  let v := k - 1
  have hwz : w v * z = y v * w k := by
    simpa [v, sub_eq_add_neg, add_assoc] using hstep v
  have hleft : (w k)⁻¹ * (y v)⁻¹ = z⁻¹ * (w v)⁻¹ := by
    calc
      (w k)⁻¹ * (y v)⁻¹ = (y v * w k)⁻¹ := by simp
      _ = (w v * z)⁻¹ := by rw [← hwz]
      _ = z⁻¹ * (w v)⁻¹ := by simp
  have hright : (w v)⁻¹ * y v = z * (w k)⁻¹ := by
    calc
      (w v)⁻¹ * y v = (w v)⁻¹ * y v * w k * (w k)⁻¹ := by group
      _ = (w v)⁻¹ * (y v * w k) * (w k)⁻¹ := by group
      _ = (w v)⁻¹ * (w v * z) * (w k)⁻¹ := by rw [← hwz]
      _ = z * (w k)⁻¹ := by group
  let ur := iteratedInverseFirstCommutator r u z
  have hcalc :
      w k * inverseFirstCommutator ur z * (w k)⁻¹ =
        (a r k : G)⁻¹ * (a r v : G) *
          inverseFirstCommutator (a r v : G) (y v) := by
    rw [ha r k, ha r v]
    calc
      w k * inverseFirstCommutator ur z * (w k)⁻¹ =
          w k * ur⁻¹ * z⁻¹ * ur * z * (w k)⁻¹ := by
            simp only [inverseFirstCommutator]
            group
      _ = w k * ur⁻¹ * (z⁻¹ * (w v)⁻¹) * w v * ur *
          (z * (w k)⁻¹) := by group
      _ = w k * ur⁻¹ * ((w k)⁻¹ * (y v)⁻¹) * w v * ur *
          ((w v)⁻¹ * y v) := by rw [← hleft, ← hright]
      _ = (w k * ur * (w k)⁻¹)⁻¹ * (w v * ur * (w v)⁻¹) *
          inverseFirstCommutator (w v * ur * (w v)⁻¹) (y v) := by
            simp only [inverseFirstCommutator]
            group
  have hcG : inverseFirstCommutator (a r v : G) (y v) ∈ H₀ := by
    apply hcomm
    simpa [inverseFirstCommutator, commutatorElement_def] using
      Subgroup.commutator_mem_commutator
        (H.inv_mem (a r v).property) (H₁.inv_mem (hy v))
  let c : H :=
    ⟨inverseFirstCommutator (a r v : G) (y v), hH₀_le_H hcG⟩
  have haeq : a (r + 1) k = (a r k)⁻¹ * a r v * c := by
    apply Subtype.ext
    rw [ha (r + 1) k]
    change w k * inverseFirstCommutator ur z * (w k)⁻¹ = _
    simpa [c, v] using hcalc
  rw [haeq]
  simp only [map_mul, map_inv]
  have hc1 : QuotientGroup.mk' (H₀.subgroupOf H) c = 1 :=
    (QuotientGroup.eq_one_iff c).2 hcG
  simp [hc1, v]

private theorem hall_lemma_14_4_5_generation_of_factorization
    {G : Type u} [Group G] (H H₀ P : Subgroup G)
    [(H₀.subgroupOf H).Normal]
    (hH₀_le_H : H₀ ≤ H)
    (dstar : H → H) (cycleFactors : H → List H)
    (hdstar_factor : ∀ u : H, (u : G) ∈ P →
      QuotientGroup.mk' (H₀.subgroupOf H) (dstar u) =
        ((cycleFactors u).map (QuotientGroup.mk' (H₀.subgroupOf H))).prod)
    (hgenerated : H ≤ H₀ ⊔ Subgroup.closure
      {x : G | ∃ u : H, (u : G) ∈ P ∧ x = (dstar u : G)}) :
    H ≤ H₀ ⊔ Subgroup.closure
      {x : G | ∃ u : H, (u : G) ∈ P ∧
        ∃ d : H, d ∈ cycleFactors u ∧ x = (d : G)} := by
  let π : H →* H ⧸ H₀.subgroupOf H := QuotientGroup.mk' (H₀.subgroupOf H)
  let factorSet : Set G :=
    {x : G | ∃ u : H, (u : G) ∈ P ∧
      ∃ d : H, d ∈ cycleFactors u ∧ x = (d : G)}
  let K : Subgroup G := H₀ ⊔ Subgroup.closure factorSet
  have hK_le_H : K ≤ H := by
    refine sup_le hH₀_le_H ((Subgroup.closure_le H).2 ?_)
    rintro x ⟨u, _hu, d, _hd, rfl⟩
    exact d.property
  let KH : Subgroup H := K.subgroupOf H
  let L : Subgroup (H ⧸ H₀.subgroupOf H) := KH.map π
  refine le_trans hgenerated ?_
  refine sup_le le_sup_left ((Subgroup.closure_le K).2 ?_)
  rintro _ ⟨u, hu, rfl⟩
  have hfactor_mem : ∀ d : H, d ∈ cycleFactors u → π d ∈ L := by
    intro d hd
    refine Subgroup.mem_map.mpr ⟨d, ?_, rfl⟩
    change (d : G) ∈ K
    exact (show Subgroup.closure factorSet ≤ K from le_sup_right)
      (Subgroup.subset_closure ⟨u, hu, d, hd, rfl⟩)
  have hprod_mem_aux : ∀ M : List H,
      (∀ d : H, d ∈ M → π d ∈ L) → (M.map π).prod ∈ L := by
    intro M
    induction M with
    | nil =>
        intro _
        exact L.one_mem
    | cons d M ih =>
        intro hM
        rw [List.map_cons, List.prod_cons]
        exact L.mul_mem (hM d (by simp))
          (ih (fun e he => hM e (by simp [he])))
  have hprod_mem : ((cycleFactors u).map π).prod ∈ L :=
    hprod_mem_aux (cycleFactors u) hfactor_mem
  have hdstar_mem : π (dstar u) ∈ L := by
    rw [hdstar_factor u hu]
    exact hprod_mem
  rcases Subgroup.mem_map.mp hdstar_mem with ⟨k, hkKH, hkπ⟩
  have hkK : (k : G) ∈ K := hkKH
  have hdiv : dstar u / k ∈ H₀.subgroupOf H :=
    QuotientGroup.eq_iff_div_mem.mp hkπ.symm
  have hdivK : ((dstar u / k : H) : G) ∈ K :=
    (show H₀ ≤ K from le_sup_left) hdiv
  have hmulK := K.mul_mem hdivK hkK
  simpa [K] using hmulK

private theorem hall_exists_central_prime_order_action_in_normal
    {P : Type*} {X : Type*} [Group P] [Finite P] [Finite X]
    [MulAction P X] (p : ℕ) [Fact p.Prime] (hP : IsPGroup p P)
    (Q : Subgroup P) [Q.Normal]
    (x : X) (hmoved : ∃ g : P, g ∈ Q ∧ g • x ≠ x) :
    ∃ z : P, z ∈ Q ∧
      orderOf ((MulAction.toPermHom P (MulAction.orbit P x)) z) = p ∧
      (∀ g : P, Commute
        ((MulAction.toPermHom P (MulAction.orbit P x)) z)
        ((MulAction.toPermHom P (MulAction.orbit P x)) g)) ∧
      ∀ y : MulAction.orbit P x,
        ((MulAction.toPermHom P (MulAction.orbit P x)) z) y ≠ y := by
  classical
  let ρ := MulAction.toPermHom P (MulAction.orbit P x)
  let S := ρ.range
  have hS : IsPGroup p S :=
    hP.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  let B : Subgroup S := Q.map ρ.rangeRestrict
  letI : B.Normal :=
    (inferInstance : Q.Normal).map ρ.rangeRestrict
      ρ.rangeRestrict_surjective
  have hB_ne_bot : B ≠ ⊥ := by
    rcases hmoved with ⟨g, hgQ, hg⟩
    intro hbot
    have hmem : ρ.rangeRestrict g ∈ B :=
      Subgroup.mem_map.mpr ⟨g, hgQ, rfl⟩
    rw [hbot] at hmem
    have hrho_one : ρ g = 1 :=
      congrArg Subtype.val (by simpa using hmem)
    have hfix := congrArg
      (fun σ : Equiv.Perm (MulAction.orbit P x) =>
        σ ⟨x, MulAction.mem_orbit_self x⟩) hrho_one
    exact hg (by simpa [ρ] using congrArg Subtype.val hfix)
  have hpB : p ∣ Nat.card B := by
    exact (hS.to_subgroup B).card_eq_or_dvd.resolve_left
      (ne_of_gt ((Subgroup.one_lt_card_iff_ne_bot B).2 hB_ne_bot))
  have hSconj : IsPGroup p (ConjAct S) :=
    hS.of_equiv ConjAct.toConjAct
  obtain ⟨b, hbfix, hbne⟩ :=
    hSconj.exists_fixed_point_of_prime_dvd_card_of_fixed_point
      (α := B) hpB (a := (1 : B)) (by
        rw [MulAction.mem_fixedPoints]
        intro s
        apply Subtype.ext
        simp)
  have hbcenter : (b : S) ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro s
    have hfix := (MulAction.mem_fixedPoints.mp hbfix) (ConjAct.toConjAct s)
    have hval := congrArg Subtype.val hfix
    exact mul_inv_eq_iff_eq_mul.mp hval
  let D : Subgroup S := B ⊓ Subgroup.center S
  have hD_ne_bot : D ≠ ⊥ := by
    intro hbot
    have hbD : (b : S) ∈ D := ⟨b.2, hbcenter⟩
    rw [hbot] at hbD
    exact hbne (Subtype.ext (by simpa using hbD.symm))
  have hD : IsPGroup p D := hS.to_subgroup D
  have hpdvd : p ∣ Nat.card D :=
    hD.card_eq_or_dvd.resolve_left
      (ne_of_gt ((Subgroup.one_lt_card_iff_ne_bot D).2 hD_ne_bot))
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' p hpdvd
  rcases Subgroup.mem_map.mp c.property.1 with ⟨z, hzQ, hzc⟩
  have hzcval :
      ρ z = ((c : D) : S) :=
    congrArg Subtype.val hzc
  have hcS : orderOf ((c : D) : S) = p := by
    simpa [Subgroup.orderOf_coe] using hc
  refine ⟨z, hzQ, ?_, ?_, ?_⟩
  · simpa [ρ, hzcval, Subgroup.orderOf_coe] using hcS
  · intro g
    let sg : S := ⟨ρ g, ⟨g, rfl⟩⟩
    have hcommS : Commute c.1 sg := by
      exact (Subgroup.mem_center_iff.mp c.property.2 sg).symm
    change Commute (ρ z) (ρ g)
    rw [hzcval]
    exact hcommS.map S.subtype
  · intro y hy
    have hfix : ∀ q : MulAction.orbit P x, ρ z q = q := by
      intro q
      obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq P y q
      calc
        ρ z (g • y) = ρ z (ρ g y) := rfl
        _ = ρ g (ρ z y) := by
          have hcomm : Commute (ρ z) (ρ g) := by
            rw [hzcval]
            let sg : S := ⟨ρ g, ⟨g, rfl⟩⟩
            have hcommS : Commute c.1 sg :=
              (Subgroup.mem_center_iff.mp c.property.2 sg).symm
            exact hcommS.map S.subtype
          have happ := congrArg
            (fun σ : Equiv.Perm (MulAction.orbit P x) => σ y) hcomm.eq
          simpa using happ
        _ = ρ g y := by rw [hy]
        _ = g • y := rfl
    have hone : ρ z = 1 := Equiv.Perm.ext (by intro q; simpa using hfix q)
    have horder_one : orderOf (ρ z) = 1 := by rw [hone, orderOf_one]
    have horder_p : orderOf (ρ z) = p := by
      simpa [ρ, hzcval, Subgroup.orderOf_coe] using hcS
    exact (Fact.out : p.Prime).ne_one (horder_p.symm.trans horder_one)

private theorem hall_nonprincipal_weakly_closed_orbit_moved
    {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (P : Sylow p G) (Q H : Subgroup G)
    (hH : H = Subgroup.normalizer (Q : Set G))
    (hweak : WeaklyClosedIn (P : Subgroup G) Q)
    (q0 : G ⧸ H) (hq0 : q0 ≠ QuotientGroup.mk (1 : G)) :
    ∃ z : P, (z : G) ∈ Q ∧ ((z : G) • q0 : G ⧸ H) ≠ q0 := by
  classical
  by_contra hmove
  push Not at hmove
  let t : G := q0.out
  have htq : (t : G ⧸ H) = q0 := Quotient.out_eq q0
  let f : Q →* G :=
    (MulAut.conj t⁻¹).toMonoidHom.comp Q.subtype
  have hA_le_H : f.range ≤ H := by
    rintro x ⟨z, rfl⟩
    let zP : P := ⟨(z : G), hweak.1 z.2⟩
    have hzfix := hmove zP z.2
    have hzfix' :
        ((zP : G) • (t : G ⧸ H) : G ⧸ H) = (t : G ⧸ H) := by
      simpa [htq] using hzfix
    have hrel := QuotientGroup.eq.mp hzfix'
    have hxinv : (f z)⁻¹ ∈ H := by
      simpa [f, zP, t, mul_assoc] using hrel
    simpa using H.inv_mem hxinv
  have hQp : IsPGroup p Q := by
    have hQsub : IsPGroup p (Q.subgroupOf (P : Subgroup G)) :=
      P.isPGroup'.to_subgroup _
    exact hQsub.of_equiv (Subgroup.subgroupOfEquivOfLe hweak.1)
  have hAp : IsPGroup p f.range :=
    hQp.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  let A : Subgroup H := f.range.subgroupOf H
  have hAsubp : IsPGroup p A := by
    exact hAp.of_equiv
      (Subgroup.subgroupOfEquivOfLe hA_le_H).symm
  obtain ⟨T, hAT⟩ := hAsubp.exists_le_sylow
  have hP_le_H : (P : Subgroup G) ≤ H := by
    rw [hH]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hweak.1).mp
      (weaklyClosedIn_subgroupOf_normal hweak)
  let S₁ : Sylow p H := P.subtype hP_le_H
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq H T S₁
  have hyT :
      MulAut.conj y • (T : Subgroup H) = (S₁ : Subgroup H) := by
    simpa only [Sylow.coe_subgroup_smul] using
      congrArg (fun R : Sylow p H => (R : Subgroup H)) hy
  have hyA_le :
      MulAut.conj y • A ≤ (S₁ : Subgroup H) := by
    rw [← hyT, Subgroup.pointwise_smul_def,
      Subgroup.pointwise_smul_def]
    exact Subgroup.map_mono hAT
  let g : G := t * (y : G)⁻¹
  have hright_le_P : rightConjugate Q g ≤ (P : Subgroup G) := by
    intro x hx
    change x ∈ Q.conjBy g⁻¹ at hx
    rcases Subgroup.mem_map.mp hx with ⟨z, hzQ, rfl⟩
    let aH : H := ⟨f ⟨z, hzQ⟩,
      hA_le_H ⟨⟨z, hzQ⟩, rfl⟩⟩
    let a : A := ⟨aH, ⟨⟨z, hzQ⟩, rfl⟩⟩
    have hay : (MulAut.conj y) aH ∈ (S₁ : Subgroup H) :=
      hyA_le (show (MulAut.conj y) aH ∈ MulAut.conj y • A by
        rw [Subgroup.pointwise_smul_def]
        exact Subgroup.mem_map.mpr ⟨a, a.2, rfl⟩)
    have hayG :
        (((MulAut.conj y) aH : H) : G) ∈ (P : Subgroup G) := hay
    simpa [g, f, aH, a, MulAut.conj_apply, mul_assoc] using hayG
  have hright_eq : rightConjugate Q g = Q :=
    hweak.2 g hright_le_P
  have hginv_normalizes : g⁻¹ ∈ Subgroup.normalizer (Q : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [← hright_eq]
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    · intro hx
      have hmem : g⁻¹ * x * g ∈ rightConjugate Q g := by
        simpa [hright_eq] using hx
      change g⁻¹ * x * g ∈ Q.conjBy g⁻¹ at hmem
      rcases Subgroup.mem_map.mp hmem with ⟨z, hz, hzx⟩
      have hzx' : z = x := by
        apply (MulAut.conj g⁻¹).injective
        simpa using hzx
      simpa [hzx'] using hz
  have hg_normalizes : g ∈ Subgroup.normalizer (Q : Set G) := by
    simpa using (Subgroup.normalizer (Q : Set G)).inv_mem hginv_normalizes
  have hgH : g ∈ H := by
    rw [hH]
    exact hg_normalizes
  have htH : t ∈ H := by
    have := H.mul_mem hgH y.2
    simpa [g, mul_assoc] using this
  apply hq0
  calc
    q0 = (t : G ⧸ H) := htq.symm
    _ = QuotientGroup.mk (1 : G) := by
      apply QuotientGroup.eq.mpr
      simpa using H.inv_mem htH

private theorem hall_nonprincipal_weakly_closed_orbit_central_prime_order_action
    {G : Type u} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (P₁ : Sylow p G) (Q H₁ : Subgroup G)
    (hH₁ : H₁ = Subgroup.normalizer (Q : Set G))
    (hweak : WeaklyClosedIn (P₁ : Subgroup G) Q)
    (q : G ⧸ H₁) (hq : q ≠ QuotientGroup.mk (1 : G)) :
    ∃ z : P₁, (z : G) ∈ Q ∧
      orderOf ((MulAction.toPermHom P₁ (MulAction.orbit P₁ q)) z) = p ∧
      (∀ g : P₁, Commute
        ((MulAction.toPermHom P₁ (MulAction.orbit P₁ q)) z)
        ((MulAction.toPermHom P₁ (MulAction.orbit P₁ q)) g)) ∧
      ∀ y : MulAction.orbit P₁ q,
        ((MulAction.toPermHom P₁ (MulAction.orbit P₁ q)) z) y ≠ y := by
  let QP : Subgroup P₁ := Q.subgroupOf (P₁ : Subgroup G)
  letI : QP.Normal := weaklyClosedIn_subgroupOf_normal hweak
  apply hall_exists_central_prime_order_action_in_normal
    p P₁.isPGroup' QP q
  rcases hall_nonprincipal_weakly_closed_orbit_moved
    p P₁ Q H₁ hH₁ hweak q hq with ⟨z, hzQ, hzmoved⟩
  exact ⟨z, hzQ, hzmoved⟩


private theorem hall_nonprincipal_orbit_out_ne_principal
    {G : Type u} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (P₁ : Sylow p G) (H₁ : Subgroup G)
    (o : Quotient (MulAction.orbitRel P₁ (G ⧸ H₁)))
    (ho : o ≠ Quotient.mk'' (QuotientGroup.mk (1 : G) : G ⧸ H₁)) :
    o.out ≠ (QuotientGroup.mk (1 : G) : G ⧸ H₁) := by
  intro hout
  apply ho
  calc
    o = Quotient.mk'' o.out := (Quotient.out_eq' o).symm
    _ = Quotient.mk'' (QuotientGroup.mk (1 : G) : G ⧸ H₁) := congrArg _ hout


private abbrev hallNonprincipalOrbitIndex
    {G : Type u} [Group G] (p : ℕ) (P₁ : Sylow p G) (H₁ : Subgroup G) :=
  {o : Quotient (MulAction.orbitRel P₁ (G ⧸ H₁)) //
    o ≠ Quotient.mk'' (QuotientGroup.mk (1 : G) : G ⧸ H₁)}


private structure HallActiveCycle
    {G : Type u} [Group G] (p : ℕ) (P₁ : Sylow p G)
    (G₀ H₁ H : Subgroup G) (Zs : Finset G) (u : H) where
  z : P₁
  w : ZMod p → G₀
  y : ZMod p → H₁
  h : ZMod p → H
  hz : (z : G) ∈ Zs
  step : ∀ k, (w k : G) * (z : G) = (y k : G) * (w (k + 1) : G)
  conj : ∀ k, (w k : G) * (u : G) * (w k : G)⁻¹ = (h k : G)

private abbrev hallFixedCoset
    {G : Type u} [Group G] (H : Subgroup G) (u : H) :=
  {q : G ⧸ H // Function.minimalPeriod ((u : G) • ·) q = 1}

private noncomputable def hallActiveCycleOfResidualCycle
    {G : Type u} [Group G] {p : ℕ} (P₁ : Sylow p G)
    (G₀ H₁ H : Subgroup G) (Zs : Finset G)
    (u : H) (uH : H.subgroupOf G₀)
    (hu : (((uH : G₀) : G)) = (u : G))
    (z : P₁) (hz : (z : G) ∈ Zs)
    (r : ZMod p → hallFixedCoset (H.subgroupOf G₀) uH)
    (hrSucc : ∀ k : ZMod p,
      ((z : G) • (((r k).1.out : G₀) : G) : G ⧸ H₁) =
        ((((r (k + 1)).1.out : G₀) : G) : G ⧸ H₁)) :
    HallActiveCycle p P₁ G₀ H₁ H Zs u := by
  let t : ZMod p → G₀ := fun k => (r k).1.out
  let w : ZMod p → G₀ := fun j => (t (0 - j))⁻¹
  let h : ZMod p → H := fun j => ⟨
    (w j : G) * (u : G) * (w j : G)⁻¹, by
      have hmem := QuotientGroup.out_conj_pow_minimalPeriod_mem
        (H := H.subgroupOf G₀) (uH : G₀) (r (0 - j)).1
      rw [(r (0 - j)).2, pow_one] at hmem
      change (((r (0 - j)).1.out⁻¹ * (uH : G₀) *
        (r (0 - j)).1.out : G₀) : G) ∈ H at hmem
      simpa [w, t, hu] using hmem⟩
  let y : ZMod p → H₁ := fun j => ⟨
    (w j : G) * (z : G) * (w (j + 1) : G)⁻¹, by
      let k := 0 - (j + 1)
      have hq :
          ((z : G) • ((t k : G) : G ⧸ H₁)) =
            ((t (0 - j) : G) : G ⧸ H₁) := by
        simpa [t, k, sub_eq_add_neg, add_assoc] using hrSucc k
      have hrel := QuotientGroup.eq.mp hq
      have hinv := H₁.inv_mem hrel
      simpa [w, k, t, mul_assoc] using hinv⟩
  refine
    { z := z
      w := w
      y := y
      h := h
      hz := hz
      step := ?_
      conj := ?_ }
  · intro j
    simp only [w, y]
    group
  · intro j
    rfl
private def hallActiveCycleFactor
    {G : Type u} [Group G] {p : ℕ} {P₁ : Sylow p G}
    {G₀ H₁ H : Subgroup G} {Zs : Finset G} {u : H}
    (c : HallActiveCycle p P₁ G₀ H₁ H Zs u) : H :=
  (List.ofFn fun k : Fin p => c.h (0 - (k.val : ZMod p))).prod

private theorem hallActiveCycle_conjugated_mem
    {G : Type u} [Group G] {p : ℕ} {P₁ : Sylow p G}
    {G₀ H₁ H H₀ : Subgroup G} {Zs : Finset G} {u : H}
    (c : HallActiveCycle p P₁ G₀ H₁ H Zs u)
    (hH₀_le_H : H₀ ≤ H) (hcomm : ⁅H, H₁⁆ ≤ H₀) :
    ∀ r : ℕ, ∀ k : ZMod p,
      (c.w k : G) * iteratedInverseFirstCommutator r (u : G) (c.z : G) *
        (c.w k : G)⁻¹ ∈ H := by
  intro r
  induction r with
  | zero =>
      intro k
      rw [show iteratedInverseFirstCommutator 0 (u : G) (c.z : G) = (u : G) by rfl,
        c.conj k]
      exact (c.h k).property
  | succ r ih =>
      intro k
      let v := k - 1
      let ur := iteratedInverseFirstCommutator r (u : G) (c.z : G)
      have hstep := hall_cycle_conjugate_step (u : G) (c.z : G)
        (fun j => (c.w j : G)) (fun j => (c.y j : G)) c.step r k
      change (c.w k : G) * inverseFirstCommutator ur (c.z : G) *
        (c.w k : G)⁻¹ ∈ H
      rw [hstep]
      have hcomm_mem : inverseFirstCommutator
          ((c.w v : G) * ur * (c.w v : G)⁻¹) (c.y v : G) ∈ H₀ := by
        apply hcomm
        simpa [inverseFirstCommutator, commutatorElement_def] using
          Subgroup.commutator_mem_commutator
            (H.inv_mem (ih v)) (H₁.inv_mem (c.y v).property)
      exact H.mul_mem (H.mul_mem (H.inv_mem (ih k)) (ih v))
        (hH₀_le_H hcomm_mem)

private theorem hallActiveCycle_factor_engel_congruence
    {G : Type u} [Group G] {p : ℕ} [Fact p.Prime] {P₁ : Sylow p G}
    {G₀ H₁ H H₀ : Subgroup G} {Zs : Finset G} {u : H}
    (c : HallActiveCycle p P₁ G₀ H₁ H Zs u)
    (hH₀_le_H : H₀ ≤ H) [(H₀.subgroupOf H).Normal]
    (hcomm : ⁅H, H₁⁆ ≤ H₀)
    (hcommH : commutator H ≤ H₀.subgroupOf H)
    (hpow : hallPPowerSubgroup p H ≤ H₀) :
    (c.w 0 : G) * engelSymbol p (u : G) (c.z : G) * (c.w 0 : G)⁻¹ ∈ H ∧
      (hallActiveCycleFactor c : G) /
        ((c.w 0 : G) * engelSymbol p (u : G) (c.z : G) *
          (c.w 0 : G)⁻¹) ∈ H₀ := by
  letI : IsMulCommutative (H ⧸ H₀.subgroupOf H) :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le).2 hcommH
  letI : CommGroup (H ⧸ H₀.subgroupOf H) := IsMulCommutative.instCommGroup
  let π : H →* H ⧸ H₀.subgroupOf H := QuotientGroup.mk' (H₀.subgroupOf H)
  let a : ℕ → ZMod p → H := fun r k =>
    ⟨(c.w k : G) * iteratedInverseFirstCommutator r (u : G) (c.z : G) *
      (c.w k : G)⁻¹, hallActiveCycle_conjugated_mem c hH₀_le_H hcomm r k⟩
  have ha : ∀ r k, (a r k : G) =
      (c.w k : G) * iteratedInverseFirstCommutator r (u : G) (c.z : G) *
        (c.w k : G)⁻¹ := by
    intro r k
    rfl
  have hrec : ∀ r : ℕ, ∀ k : ZMod p,
      π (a (r + 1) k) = (π (a r k))⁻¹ * π (a r (k - 1)) := by
    intro r k
    exact hall_cycle_conjugate_recurrence_mod H H₀ H₁ hH₀_le_H hcomm
      (u : G) (c.z : G) (fun j => (c.w j : G)) (fun j => (c.y j : G))
        a ha (fun j => (c.y j).property) c.step r k
  have hpQuot : ∀ q : H ⧸ H₀.subgroupOf H, q ^ p = 1 := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (H₀.subgroupOf H) q
    rw [← map_pow]
    apply (QuotientGroup.eq_one_iff (x ^ p)).2
    exact hpow (Subgroup.subset_closure ⟨x, rfl⟩)
  have ha_zero (k : ZMod p) : a 0 k = c.h k := by
    apply Subtype.ext
    rw [ha 0 k]
    rw [show iteratedInverseFirstCommutator 0 (u : G) (c.z : G) = (u : G) by rfl]
    exact c.conj k
  have hcyc :
      π (a (p - 1) 0) =
        ∏ k ∈ Finset.range p, π (a 0 (0 - (k : ZMod p))) :=
    hall_cyclic_recurrence_prime_pred_eq_prod p hpQuot
      (fun r k => π (a r k)) hrec 0
  have hfactor :
      π (hallActiveCycleFactor c) =
        ∏ k ∈ Finset.range p, π (a 0 (0 - (k : ZMod p))) := by
    calc
      π (hallActiveCycleFactor c) =
          (List.ofFn fun k : Fin p =>
            π (c.h (0 - (k.val : ZMod p)))).prod := by
              rw [hallActiveCycleFactor, map_list_prod, ← List.ofFn_comp']
      _ = ∏ k : Fin p, π (c.h (0 - (k.val : ZMod p))) :=
        List.prod_ofFn
      _ = ∏ k ∈ Finset.range p, π (c.h (0 - (k : ZMod p))) :=
        Fin.prod_univ_eq_prod_range
          (fun k : ℕ => π (c.h (0 - (k : ZMod p)))) p
      _ = ∏ k ∈ Finset.range p, π (a 0 (0 - (k : ZMod p))) := by
        apply Finset.prod_congr rfl
        intro k hk
        rw [ha_zero]
  have hquot :
      π (hallActiveCycleFactor c) =
        π ⟨(c.w 0 : G) * engelSymbol p (u : G) (c.z : G) *
          (c.w 0 : G)⁻¹,
          hallActiveCycle_conjugated_mem c hH₀_le_H hcomm (p - 1) 0⟩ := by
    rw [hfactor, ← hcyc]
    rfl
  constructor
  · simpa [engelSymbol] using
      hallActiveCycle_conjugated_mem c hH₀_le_H hcomm (p - 1) 0
  · have hmem :=
      (QuotientGroup.eq_iff_div_mem (N := H₀.subgroupOf H)).mp hquot
    exact hmem
private theorem hall_sylow_principal_coset_fixed
    {G : Type u} [Group G] {p : ℕ} (P₁ : Sylow p G) (H₁ : Subgroup G)
    (hP₁_le_H₁ : (P₁ : Subgroup G) ≤ H₁) (g : P₁) :
    ((g : G) • (QuotientGroup.mk (1 : G) : G ⧸ H₁)) =
      QuotientGroup.mk (1 : G) := by
  apply QuotientGroup.eq.mpr
  simpa using H₁.inv_mem (hP₁_le_H₁ g.property)

private theorem hall_orbit_quotient_eq_principal_iff
    {G : Type u} [Group G] {p : ℕ} (P₁ : Sylow p G) (H₁ : Subgroup G)
    (hP₁_le_H₁ : (P₁ : Subgroup G) ≤ H₁) (q : G ⧸ H₁) :
    (Quotient.mk'' q :
        Quotient (MulAction.orbitRel P₁ (G ⧸ H₁))) =
        Quotient.mk'' (QuotientGroup.mk (1 : G) : G ⧸ H₁) ↔
      q = QuotientGroup.mk (1 : G) := by
  constructor
  · intro hq
    have horbit : q ∈ MulAction.orbit P₁
        (QuotientGroup.mk (1 : G) : G ⧸ H₁) :=
      Quotient.eq''.mp hq
    rcases MulAction.mem_orbit_iff.mp horbit with ⟨g, hg⟩
    calc
      q = g • (QuotientGroup.mk (1 : G) : G ⧸ H₁) := hg.symm
      _ = QuotientGroup.mk (1 : G) :=
        hall_sylow_principal_coset_fixed P₁ H₁ hP₁_le_H₁ g
  · intro hq
    rw [hq]
private abbrev hallAmbientFixedCoset
    {G : Type u} [Group G] {p : ℕ} (P₁ : Sylow p G)
    (H₁ : Subgroup G) (u : P₁) :=
  Function.fixedPoints ((MulAction.toPermHom P₁ (G ⧸ H₁)) u)

private abbrev hallOrbitFixedCoset
    {G : Type u} [Group G] {p : ℕ} (P₁ : Sylow p G)
    (H₁ : Subgroup G) (u : P₁)
    (i : hallNonprincipalOrbitIndex p P₁ H₁) :=
  Function.fixedPoints
    ((MulAction.toPermHom P₁ (MulAction.orbit P₁ i.1.out)) u)

private noncomputable def hallNonprincipalFixedOrbitEquiv
    {G : Type u} [Group G] [Finite G] (p : ℕ) (P₁ : Sylow p G)
    (H₁ : Subgroup G) (hP₁_le_H₁ : (P₁ : Subgroup G) ≤ H₁)
    (u : P₁) :
    {q : hallAmbientFixedCoset P₁ H₁ u //
      (q.1 : G ⧸ H₁) ≠ QuotientGroup.mk (1 : G)} ≃
      Σ i : hallNonprincipalOrbitIndex p P₁ H₁,
        hallOrbitFixedCoset P₁ H₁ u i := by
  let principal : G ⧸ H₁ := QuotientGroup.mk (1 : G)
  let principalOrbit : Quotient (MulAction.orbitRel P₁ (G ⧸ H₁)) :=
    Quotient.mk'' principal
  let f : (Σ i : hallNonprincipalOrbitIndex p P₁ H₁,
      hallOrbitFixedCoset P₁ H₁ u i) →
      {q : hallAmbientFixedCoset P₁ H₁ u // (q.1 : G ⧸ H₁) ≠ principal} :=
    fun s => ⟨⟨s.2.1, congrArg Subtype.val s.2.2⟩, by
        intro hs
        apply s.1.2
        have hmem : (s.2.1 : G ⧸ H₁) ∈
            MulAction.orbitRel.Quotient.orbit s.1.1 := by
          rw [MulAction.orbitRel.Quotient.orbit_eq_orbit_out
            s.1.1 Quotient.out_eq']
          exact s.2.1.property
        have hquot :
            (Quotient.mk'' (s.2.1 : G ⧸ H₁) :
              Quotient (MulAction.orbitRel P₁ (G ⧸ H₁))) = s.1.1 :=
          MulAction.orbitRel.Quotient.mem_orbit.mp hmem
        calc
          s.1.1 = Quotient.mk'' (s.2.1 : G ⧸ H₁) := hquot.symm
          _ = principalOrbit := congrArg
            (fun x : G ⧸ H₁ =>
              (Quotient.mk'' x :
                Quotient (MulAction.orbitRel P₁ (G ⧸ H₁)))) hs⟩
  refine (Equiv.ofBijective f ?_).symm
  constructor
  · rintro ⟨i, x⟩ ⟨j, y⟩ hxy
    have hval : (x.1 : G ⧸ H₁) = (y.1 : G ⧸ H₁) :=
      congrArg (fun q => (q.1.1 : G ⧸ H₁)) hxy
    have hxi : (x.1 : G ⧸ H₁) ∈
        MulAction.orbitRel.Quotient.orbit i.1 := by
      rw [MulAction.orbitRel.Quotient.orbit_eq_orbit_out
        i.1 Quotient.out_eq']
      exact x.1.property
    have hyj : (y.1 : G ⧸ H₁) ∈
        MulAction.orbitRel.Quotient.orbit j.1 := by
      rw [MulAction.orbitRel.Quotient.orbit_eq_orbit_out
        j.1 Quotient.out_eq']
      exact y.1.property
    have hqi :
        (Quotient.mk'' (x.1 : G ⧸ H₁) :
          Quotient (MulAction.orbitRel P₁ (G ⧸ H₁))) = i.1 :=
      MulAction.orbitRel.Quotient.mem_orbit.mp hxi
    have hqj :
        (Quotient.mk'' (y.1 : G ⧸ H₁) :
          Quotient (MulAction.orbitRel P₁ (G ⧸ H₁))) = j.1 :=
      MulAction.orbitRel.Quotient.mem_orbit.mp hyj
    have hij : i = j := by
      apply Subtype.ext
      exact hqi.symm.trans ((congrArg
        (fun z : G ⧸ H₁ =>
          (Quotient.mk'' z :
            Quotient (MulAction.orbitRel P₁ (G ⧸ H₁)))) hval).trans hqj)
    subst j
    have hxy' : x = y := by
      apply Subtype.ext
      apply Subtype.ext
      exact hval
    exact congrArg (fun z => Sigma.mk i z) hxy'
  · intro q
    let o : Quotient (MulAction.orbitRel P₁ (G ⧸ H₁)) :=
      Quotient.mk'' (q.1.1 : G ⧸ H₁)
    have ho : o ≠ principalOrbit := by
      intro ho
      apply q.2
      exact (hall_orbit_quotient_eq_principal_iff
        P₁ H₁ hP₁_le_H₁ (q.1.1 : G ⧸ H₁)).mp ho
    let i : hallNonprincipalOrbitIndex p P₁ H₁ := ⟨o, ho⟩
    have hmem : (q.1.1 : G ⧸ H₁) ∈ MulAction.orbit P₁ i.1.out := by
      rw [← MulAction.orbitRel.Quotient.orbit_eq_orbit_out
        i.1 Quotient.out_eq']
      exact MulAction.orbitRel.Quotient.mem_orbit.mpr rfl
    let x : MulAction.orbit P₁ i.1.out := ⟨q.1.1, hmem⟩
    have hxfix : x ∈ hallOrbitFixedCoset P₁ H₁ u i := by
      apply Subtype.ext
      exact q.1.2
    refine ⟨⟨i, ⟨x, hxfix⟩⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    rfl
private noncomputable def hallResidualFixedCosetEquiv
    {G : Type u} [Group G] (G₀ H₁ H : Subgroup G) [G₀.Normal]
    (hH : H = G₀ ⊓ H₁) (hSup : G₀ ⊔ H₁ = ⊤)
    (uH : H.subgroupOf G₀) (u : G) (hu : ((uH : G₀) : G) = u) :
    hallFixedCoset (H.subgroupOf G₀) uH ≃
      Function.fixedPoints ((u : G) • · : G ⧸ H₁ → G ⧸ H₁) := by
  let e := hallResidualCosetEquiv G₀ H₁ H hH hSup
  refine
    { toFun := fun q => ⟨e q.1, ?_⟩
      invFun := fun q => ⟨e.symm q.1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hq :
        hallResidualCosetLeftMul G₀ H (uH : G₀) q.1 = q.1 := by
      exact Function.minimalPeriod_eq_one_iff_isFixedPt.mp q.2
    change (u : G) • e q.1 = e q.1
    calc
      (u : G) • e q.1 = ((uH : G₀) : G) • e q.1 := by rw [hu]
      _ = e (hallResidualCosetLeftMul G₀ H (uH : G₀) q.1) :=
        (hallResidualCosetEquiv_leftMul G₀ H₁ H hH hSup (uH : G₀) q.1).symm
      _ = e q.1 := congrArg e hq
  · rw [Function.minimalPeriod_eq_one_iff_isFixedPt]
    have hq : (u : G) • q.1 = q.1 := q.2
    apply e.injective
    change e (hallResidualCosetLeftMul G₀ H (uH : G₀) (e.symm q.1)) =
      e (e.symm q.1)
    rw [hallResidualCosetEquiv_leftMul, e.apply_symm_apply]
    simpa [hu] using hq
  · intro q
    apply Subtype.ext
    exact e.symm_apply_apply q.1
  · intro q
    apply Subtype.ext
    exact e.apply_symm_apply q.1
private def hallPrincipalFixedCoset
    {G : Type u} [Group G] {H : Subgroup G} (u : H) :
    hallFixedCoset H u :=
  ⟨QuotientGroup.mk (1 : G), by
    rw [Function.minimalPeriod_eq_one_iff_isFixedPt]
    apply QuotientGroup.eq.mpr
    simpa only [smul_eq_mul, mul_one] using H.inv_mem u.property⟩

private theorem hallResidualFixedCosetEquiv_principal
    {G : Type u} [Group G] (G₀ H₁ H : Subgroup G) [G₀.Normal]
    (hH : H = G₀ ⊓ H₁) (hSup : G₀ ⊔ H₁ = ⊤)
    (hH_le_H₁ : H ≤ H₁) (uH : H.subgroupOf G₀) :
    hallResidualFixedCosetEquiv G₀ H₁ H hH hSup uH
        (((uH : G₀) : G)) rfl (hallPrincipalFixedCoset uH) =
      (⟨QuotientGroup.mk (1 : G), by
        change (((uH : G₀) : G) •
          (QuotientGroup.mk (1 : G) : G ⧸ H₁)) = QuotientGroup.mk (1 : G)
        apply QuotientGroup.eq.mpr
        simpa using H₁.inv_mem (hH_le_H₁ uH.property)⟩ :
          Function.fixedPoints
            (((uH : G₀) : G) • · : G ⧸ H₁ → G ⧸ H₁)) := by
  apply Subtype.ext
  rfl
private noncomputable def hallResidualNonprincipalFixedOrbitEquiv
    {G : Type u} [Group G] [Finite G] (p : ℕ) (P₁ : Sylow p G)
    (G₀ H₁ H : Subgroup G) [G₀.Normal]
    (hH : H = G₀ ⊓ H₁) (hSup : G₀ ⊔ H₁ = ⊤)
    (hH_le_H₁ : H ≤ H₁) (hP₁_le_H₁ : (P₁ : Subgroup G) ≤ H₁)
    (uH : H.subgroupOf G₀)
    (huP : (((uH : G₀) : G)) ∈ (P₁ : Subgroup G)) :
    let uP : P₁ := ⟨((uH : G₀) : G), huP⟩
    {q : hallFixedCoset (H.subgroupOf G₀) uH //
      q ≠ hallPrincipalFixedCoset uH} ≃
      Σ i : hallNonprincipalOrbitIndex p P₁ H₁,
        hallOrbitFixedCoset P₁ H₁ uP i := by
  dsimp only
  let uP : P₁ := ⟨((uH : G₀) : G), huP⟩
  let e := hallResidualFixedCosetEquiv G₀ H₁ H hH hSup uH
    (((uH : G₀) : G)) rfl
  have hprincipal :
      e (hallPrincipalFixedCoset uH) =
        (⟨QuotientGroup.mk (1 : G), by
          exact hall_sylow_principal_coset_fixed P₁ H₁ hP₁_le_H₁ uP⟩ :
          hallAmbientFixedCoset P₁ H₁ uP) := by
    exact hallResidualFixedCosetEquiv_principal G₀ H₁ H hH hSup
      hH_le_H₁ uH
  let eNonprincipal :
      {q : hallFixedCoset (H.subgroupOf G₀) uH //
        q ≠ hallPrincipalFixedCoset uH} ≃
      {q : hallAmbientFixedCoset P₁ H₁ uP //
        (q.1 : G ⧸ H₁) ≠ QuotientGroup.mk (1 : G)} :=
    e.subtypeEquiv fun q => by
    constructor
    · intro hq hval
      apply hq
      apply e.injective
      apply Subtype.ext
      calc
        (e q).1 = QuotientGroup.mk (1 : G) := hval
        _ = (e (hallPrincipalFixedCoset uH)).1 :=
          (congrArg Subtype.val hprincipal).symm
    · intro hq hres
      subst q
      apply hq
      exact congrArg Subtype.val hprincipal
  exact eNonprincipal.trans
    (hallNonprincipalFixedOrbitEquiv p P₁ H₁ hP₁_le_H₁ uP)
private theorem hallResidualNonprincipalFixedOrbitEquiv_symm_apply_coe
    {G : Type u} [Group G] [Finite G] (p : ℕ) (P₁ : Sylow p G)
    (G₀ H₁ H : Subgroup G) [G₀.Normal]
    (hH : H = G₀ ⊓ H₁) (hSup : G₀ ⊔ H₁ = ⊤)
    (hH_le_H₁ : H ≤ H₁) (hP₁_le_H₁ : (P₁ : Subgroup G) ≤ H₁)
    (uH : H.subgroupOf G₀)
    (huP : (((uH : G₀) : G)) ∈ (P₁ : Subgroup G))
    (s : Σ i : hallNonprincipalOrbitIndex p P₁ H₁,
      hallOrbitFixedCoset P₁ H₁
        (⟨((uH : G₀) : G), huP⟩ : P₁) i) :
    let e := hallResidualFixedCosetEquiv G₀ H₁ H hH hSup uH
      (((uH : G₀) : G)) rfl
    let e' := hallResidualNonprincipalFixedOrbitEquiv p P₁ G₀ H₁ H
      hH hSup hH_le_H₁ hP₁_le_H₁ uH huP
    (e (e'.symm s).1).1 = (s.2.1.1 : G ⧸ H₁) := by
  classical
  dsimp only
  unfold hallResidualNonprincipalFixedOrbitEquiv
  dsimp only
  unfold hallNonprincipalFixedOrbitEquiv
  dsimp only
  let e := hallResidualFixedCosetEquiv G₀ H₁ H hH hSup uH
    (((uH : G₀) : G)) rfl
  let q : Function.fixedPoints
      ((((uH : G₀) : G)) • · : G ⧸ H₁ → G ⧸ H₁) :=
    ⟨s.2.1.1, congrArg Subtype.val s.2.2⟩
  change (e (e.symm q)).1 = q.1
  exact congrArg Subtype.val (e.apply_symm_apply q)
private theorem hallDiagonalDefect_eq_prod_ne_principal
    {G A : Type u} [Group G] [Finite G] [CommGroup A]
    {H : Subgroup G} [H.FiniteIndex] (φ : H →* A) (u : H) :
    letI : Fintype (G ⧸ H) := Fintype.ofFinite _
    letI : DecidablePred (fun q : G ⧸ H =>
      Function.minimalPeriod ((u : G) • ·) q = 1) := fun q =>
      instDecidableEqNat (Function.minimalPeriod ((u : G) • ·) q) 1
    letI : DecidableEq (G ⧸ H) := Classical.decEq _
    hallDiagonalDefect (H := H) φ u =
      ∏ q : {q : hallFixedCoset H u // q ≠ hallPrincipalFixedCoset u},
        φ ⟨q.1.1.out⁻¹ * (u : G) * q.1.1.out, by
          have hmem :=
            QuotientGroup.out_conj_pow_minimalPeriod_mem
              (H := H) (u : G) q.1.1
          simpa [q.1.2] using hmem⟩ := by
  classical
  letI : Fintype (G ⧸ H) := Fintype.ofFinite _
  letI : DecidableEq (G ⧸ H) := Classical.decEq _
  letI : DecidablePred (fun q : G ⧸ H =>
    Function.minimalPeriod ((u : G) • ·) q = 1) := fun q =>
      instDecidableEqNat (Function.minimalPeriod ((u : G) • ·) q) 1
  let q0 := hallPrincipalFixedCoset u
  let term : hallFixedCoset H u → A := fun q =>
    φ ⟨q.1.out⁻¹ * (u : G) * q.1.out, by
      have hmem :=
        QuotientGroup.out_conj_pow_minimalPeriod_mem
          (H := H) (u : G) q.1
      simpa [q.2] using hmem⟩
  have hout_inv : q0.1.out⁻¹ ∈ H := by
    have heq :
        (q0.1.out : G ⧸ H) = QuotientGroup.mk (1 : G) := by
      calc
        (q0.1.out : G ⧸ H) = q0.1 := Quotient.out_eq q0.1
        _ = QuotientGroup.mk (1 : G) := rfl
    have hrel := QuotientGroup.eq.mp heq
    simpa using hrel
  have hout : q0.1.out ∈ H := by
    simpa using H.inv_mem hout_inv
  let x : H := ⟨q0.1.out, hout⟩
  have hterm0 : term q0 = φ u := by
    change φ (x⁻¹ * u * x) = φ u
    rw [map_mul, map_mul, map_inv]
    calc
      (φ x)⁻¹ * φ u * φ x = φ u * ((φ x)⁻¹ * φ x) := by
        ac_rfl
      _ = φ u := by simp
  simp only [hallDiagonalDefect, hallDiagonalContribution]
  change (φ u)⁻¹ * ∏ q, term q = ∏ q : {_q // _q ≠ q0}, term q.1
  rw [Fintype.prod_eq_mul_prod_subtype_ne term q0, hterm0]
  group
private theorem hall_lemma_14_4_5_double_coset_cycle_data
    {G : Type u} [Group G] [Finite G] {A : Type u} [CommGroup A]
    (p : ℕ) [Fact p.Prime]
    (P₁ : Sylow p G) (N₁ H₁ G₀ H P _H₀ : Subgroup G)
    (_hN₁ : N₁ = Subgroup.normalizer ((P₁ : Subgroup G) : Set G))
    (_hN₁_le_H₁ : N₁ ≤ H₁)
    (hG₀ : G₀ = hallPResidual p G)
    (hH : H = G₀ ⊓ H₁)
    (hP : P = G₀ ⊓ (P₁ : Subgroup G))
    (hP₁_le_H₁ : (P₁ : Subgroup G) ≤ H₁)
    (hH_le_G₀ : H ≤ G₀) (hSup : G₀ ⊔ H₁ = ⊤)
    (HG₀ : Subgroup G₀) (eH : HG₀ ≃* H)
    (hHG₀ : HG₀ = H.subgroupOf G₀)
    (heH : HEq eH (Subgroup.subgroupOfEquivOfLe hH_le_G₀))
    (π : H →* A) (φ : HG₀ →* A)
    (hφ : φ = π.comp eH.toMonoidHom)
    (Zs : Finset G)
    (z : hallNonprincipalOrbitIndex p P₁ H₁ → P₁)
    (hzZs : ∀ i : hallNonprincipalOrbitIndex p P₁ H₁, (z i : G) ∈ Zs)
    (hzspec : ∀ i : hallNonprincipalOrbitIndex p P₁ H₁,
      orderOf ((MulAction.toPermHom P₁ (MulAction.orbit P₁ i.1.out)) (z i)) = p ∧
        (∀ g : P₁, Commute
          ((MulAction.toPermHom P₁ (MulAction.orbit P₁ i.1.out)) (z i))
          ((MulAction.toPermHom P₁ (MulAction.orbit P₁ i.1.out)) g)) ∧
        ∀ x : MulAction.orbit P₁ i.1.out,
          (MulAction.toPermHom P₁ (MulAction.orbit P₁ i.1.out)) (z i) x ≠ x) :
    ∃ activeCycles : (u : H) → List
        (HallActiveCycle p P₁ G₀ H₁ H Zs u),
      ∀ u : H, (u : G) ∈ P →
        hallDiagonalDefect (G := G₀) (H := HG₀) φ (eH.symm u) =
          (((activeCycles u).map hallActiveCycleFactor).map π).prod := by
  subst HG₀
  cases heH
  subst φ
  classical
  have hH_le_H₁ : H ≤ H₁ := by
    rw [hH]
    exact inf_le_right
  have hG₀_normal : G₀.Normal := by
    subst G₀
    exact hallPResidual_normal p G
  letI : G₀.Normal := hG₀_normal

  let cycleDataFor : ∀ (u : H), (hu : (u : G) ∈ P) →
      {cs : List (HallActiveCycle p P₁ G₀ H₁ H Zs u) //
        hallDiagonalDefect (G := G₀) (H := H.subgroupOf G₀)
            (π.comp (Subgroup.subgroupOfEquivOfLe hH_le_G₀).toMonoidHom)
            ((Subgroup.subgroupOfEquivOfLe hH_le_G₀).symm u) =
          (((cs.map hallActiveCycleFactor).map π).prod)} := fun u hu => by
    let uH : H.subgroupOf G₀ :=
      (Subgroup.subgroupOfEquivOfLe hH_le_G₀).symm u
    have huP : (u : G) ∈ (P₁ : Subgroup G) := by
      rw [hP] at hu
      exact hu.2
    let uP : P₁ := ⟨(u : G), huP⟩

    let ρ : ∀ i : hallNonprincipalOrbitIndex p P₁ H₁,
        P₁ →* Equiv.Perm (MulAction.orbit P₁ i.1.out) := fun i =>
      MulAction.toPermHom P₁ (MulAction.orbit P₁ i.1.out)
    let uPerm := fun i : hallNonprincipalOrbitIndex p P₁ H₁ => ρ i uP
    let zPerm := fun i : hallNonprincipalOrbitIndex p P₁ H₁ => ρ i (z i)
    have hspec : ∀ i : hallNonprincipalOrbitIndex p P₁ H₁,
        orderOf (zPerm i) = p ∧
          (∀ g : P₁, Commute (zPerm i) (ρ i g)) ∧
          ∀ x : MulAction.orbit P₁ i.1.out, zPerm i x ≠ x := by
      intro i
      simpa [zPerm, ρ] using hzspec i
    let hcomm : ∀ i : hallNonprincipalOrbitIndex p P₁ H₁,
        Commute (zPerm i) (uPerm i) := fun i => (hspec i).2.1 uP
    let zFix := fun i : hallNonprincipalOrbitIndex p P₁ H₁ =>
      hallFixedPointRestriction (uPerm i) (zPerm i) (hcomm i)
    have hzpow : ∀ i : hallNonprincipalOrbitIndex p P₁ H₁,
        zFix i ^ p = 1 := by
      intro i
      apply hallFixedPointRestriction_pow p (uPerm i) (zPerm i) (hcomm i)
      calc
        zPerm i ^ p = zPerm i ^ orderOf (zPerm i) :=
          congrArg (fun n => zPerm i ^ n) (hspec i).1.symm
        _ = 1 := pow_orderOf_eq_one (zPerm i)
    have hzfree : ∀ i : hallNonprincipalOrbitIndex p P₁ H₁,
        ∀ x : hallOrbitFixedCoset P₁ H₁ uP i, zFix i x ≠ x := by
      intro i
      exact hallFixedPointRestriction_free (uPerm i) (zPerm i)
        (hcomm i) (hspec i).2.2
    let CycleIndex := Σ i : hallNonprincipalOrbitIndex p P₁ H₁,
      Quotient (MulAction.orbitRel (Subgroup.zpowers (zFix i))
        (hallOrbitFixedCoset P₁ H₁ uP i))
    let eRes := hallResidualNonprincipalFixedOrbitEquiv p P₁ G₀ H₁ H
      hH hSup hH_le_H₁ hP₁_le_H₁ uH huP
    let point : CycleIndex → ZMod p →
        Σ i : hallNonprincipalOrbitIndex p P₁ H₁,
          hallOrbitFixedCoset P₁ H₁ uP i := fun c j =>
      ⟨c.1, (zFix c.1 ^ j.val) c.2.out⟩
    have hzorder : ∀ c : CycleIndex, orderOf (zFix c.1) = p := by
      intro c
      apply orderOf_eq_prime (hzpow c.1)
      intro hone
      apply hzfree c.1 c.2.out
      have hx := congrArg
        (fun σ : Equiv.Perm (hallOrbitFixedCoset P₁ H₁ uP c.1) => σ c.2.out) hone
      simpa using hx
    have hpointSucc : ∀ c : CycleIndex, ∀ j : ZMod p,
        zFix c.1 (point c j).2 = (point c (j + 1)).2 := by
      intro c j
      exact hall_zmod_prime_cycle_succ p (zFix c.1) (hzorder c) j c.2.out
    let r : CycleIndex → ZMod p → hallFixedCoset (H.subgroupOf G₀) uH :=
      fun c j => (eRes.symm (point c j)).1
    have hrOut : ∀ c : CycleIndex, ∀ j : ZMod p,
        ((((r c j).1.out : G₀) : G) : G ⧸ H₁) =
          ((point c j).2.1.1 : G ⧸ H₁) := by
      intro c j
      calc
        ((((r c j).1.out : G₀) : G) : G ⧸ H₁) =
            (hallResidualFixedCosetEquiv G₀ H₁ H hH hSup uH
              (((uH : G₀) : G)) rfl (r c j)).1 := by
                change hallResidualCosetEquiv G₀ H₁ H hH hSup
                    (((r c j).1.out : G₀) : G₀ ⧸ H.subgroupOf G₀) =
                  hallResidualCosetEquiv G₀ H₁ H hH hSup (r c j).1
                exact congrArg (hallResidualCosetEquiv G₀ H₁ H hH hSup)
                  (Quotient.out_eq (r c j).1)
        _ = ((point c j).2.1.1 : G ⧸ H₁) := by
          exact hallResidualNonprincipalFixedOrbitEquiv_symm_apply_coe
            p P₁ G₀ H₁ H hH hSup hH_le_H₁ hP₁_le_H₁ uH huP (point c j)
    have hpointAmbientSucc : ∀ c : CycleIndex, ∀ j : ZMod p,
        ((z c.1 : G) • ((point c j).2.1.1 : G ⧸ H₁)) =
          ((point c (j + 1)).2.1.1 : G ⧸ H₁) := by
      intro c j
      have hs := congrArg
        (fun x : hallOrbitFixedCoset P₁ H₁ uP c.1 => (x.1.1 : G ⧸ H₁))
        (hpointSucc c j)
      rw [hallFixedPointRestriction_apply] at hs
      change ((z c.1 : G) • ((point c j).2.1.1 : G ⧸ H₁)) =
        ((point c (j + 1)).2.1.1 : G ⧸ H₁) at hs
      exact hs
    have hrSucc : ∀ c : CycleIndex, ∀ j : ZMod p,
        ((z c.1 : G) • ((((r c j).1.out : G₀) : G)) : G ⧸ H₁) =
          (((((r c (j + 1)).1.out : G₀) : G)) : G ⧸ H₁) := by
      intro c j
      calc
        ((z c.1 : G) • ((((r c j).1.out : G₀) : G)) : G ⧸ H₁) =
            (z c.1 : G) • ((point c j).2.1.1 : G ⧸ H₁) :=
          congrArg ((z c.1 : G) • ·) (hrOut c j)
        _ = ((point c (j + 1)).2.1.1 : G ⧸ H₁) := hpointAmbientSucc c j
        _ = (((((r c (j + 1)).1.out : G₀) : G)) : G ⧸ H₁) :=
          (hrOut c (j + 1)).symm

    let makeCycle : CycleIndex → HallActiveCycle p P₁ G₀ H₁ H Zs u := fun c =>
      hallActiveCycleOfResidualCycle P₁ G₀ H₁ H Zs u uH rfl
        (z c.1) (hzZs c.1) (r c) (hrSucc c)
    letI : Fintype CycleIndex := Fintype.ofFinite _
    refine ⟨(Finset.univ : Finset CycleIndex).toList.map makeCycle, ?_⟩
    let eCycle : (Σ c : CycleIndex, Fin p) ≃
        Σ i : hallNonprincipalOrbitIndex p P₁ H₁,
          hallOrbitFixedCoset P₁ H₁ uP i :=
      (Equiv.sigmaAssoc (fun (_i : hallNonprincipalOrbitIndex p P₁ H₁)
        (_c : Quotient (MulAction.orbitRel
          (Subgroup.zpowers (zFix _i))
          (hallOrbitFixedCoset P₁ H₁ uP _i))) => Fin p)).trans
        (Equiv.sigmaCongrRight fun i =>
          hallPrimeCycleEquivOfPowFree p (zFix i) (hzpow i) (hzfree i))
    have heCycle : ∀ c : CycleIndex, ∀ k : Fin p,
        eCycle ⟨c, k⟩ = point c (k.val : ZMod p) := by
      intro c k
      have hk := hallPrimeCycleEquivOfPowFree_apply p (zFix c.1)
        (hzpow c.1) (hzfree c.1) c.2 k
      have hk' :
          hallPrimeCycleEquivOfPowFree p (zFix c.1)
              (hzpow c.1) (hzfree c.1) ⟨c.2, k⟩ =
            (point c (k.val : ZMod p)).2 := by
        simpa [point, ZMod.val_natCast, Nat.mod_eq_of_lt k.isLt] using hk
      exact congrArg (Sigma.mk c.1) hk'
    let eIndex :
        {q : hallFixedCoset (H.subgroupOf G₀) uH //
          q ≠ hallPrincipalFixedCoset uH} ≃ (Σ c : CycleIndex, Fin p) :=
      eRes.trans eCycle.symm
    letI : Fintype {q : hallFixedCoset (H.subgroupOf G₀) uH //
        q ≠ hallPrincipalFixedCoset uH} := Fintype.ofFinite _
    let residualTerm : hallFixedCoset (H.subgroupOf G₀) uH → H := fun q => ⟨
      ((((q.1.out : G₀)⁻¹ * (uH : G₀) * q.1.out : G₀) : G)), by
        have hmem := QuotientGroup.out_conj_pow_minimalPeriod_mem
          (H := H.subgroupOf G₀) (uH : G₀) q.1
        rw [q.2, pow_one] at hmem
        exact hmem⟩
    have hmake : ∀ c : CycleIndex, ∀ k : Fin p,
        (makeCycle c).h (0 - (k.val : ZMod p)) =
          residualTerm (r c (k.val : ZMod p)) := by
      intro c k
      apply Subtype.ext
      simp [makeCycle, hallActiveCycleOfResidualCycle, residualTerm, uH,
        sub_eq_add_neg]
    let termR : {q : hallFixedCoset (H.subgroupOf G₀) uH //
        q ≠ hallPrincipalFixedCoset uH} → A := fun q => π (residualTerm q.1)
    let termCK : (Σ c : CycleIndex, Fin p) → A := fun ck =>
      π ((makeCycle ck.1).h (0 - (ck.2.val : ZMod p)))
    have hreindex : (∏ q, termR q) = ∏ ck, termCK ck := by
      symm
      apply Fintype.prod_equiv eIndex.symm termCK termR
      rintro ⟨c, k⟩
      have hindex : (eIndex.symm ⟨c, k⟩).1 =
          r c (k.val : ZMod p) := by
        dsimp [eIndex, r]
        apply congrArg (fun x => (eRes.symm x).1)
        exact (Equiv.symm_symm_apply eCycle ⟨c, k⟩).trans (heCycle c k)
      simp only [termCK, termR]
      rw [hindex, ← hmake]
    calc
      hallDiagonalDefect
          (π.comp (Subgroup.subgroupOfEquivOfLe hH_le_G₀).toMonoidHom) uH =
          ∏ q, termR q := by
        rw [hallDiagonalDefect_eq_prod_ne_principal]
        simp only [termR, residualTerm, MonoidHom.coe_comp,
          Function.comp_apply]
        congr 1
        ext q
        simp
      _ = ∏ ck, termCK ck := hreindex
      _ = ∏ c : CycleIndex, ∏ k : Fin p,
          π ((makeCycle c).h (0 - (k.val : ZMod p))) := by
        exact Fintype.prod_sigma termCK
      _ = ∏ c : CycleIndex, π (hallActiveCycleFactor (makeCycle c)) := by
        apply Fintype.prod_congr
        intro c
        rw [hallActiveCycleFactor, map_list_prod, ← List.ofFn_comp',
          List.prod_ofFn]
      _ = (((((Finset.univ : Finset CycleIndex).toList.map makeCycle).map
          hallActiveCycleFactor).map π).prod) := by
        simp [List.map_map]
  let activeCycles : (u : H) → List (HallActiveCycle p P₁ G₀ H₁ H Zs u) :=
    fun u => if hu : (u : G) ∈ P then (cycleDataFor u hu).1 else []
  refine ⟨activeCycles, ?_⟩
  intro u hu
  simpa only [activeCycles, dif_pos hu] using (cycleDataFor u hu).2
private theorem hall_lemma_14_4_5_cycle_factor_data_core_of_choice
    {G : Type u} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (P₁ : Sylow p G) (N₁ H₁ G₀ H P H₀ K : Subgroup G)
    (hN₁ : N₁ = Subgroup.normalizer ((P₁ : Subgroup G) : Set G))
    (hN₁_le_H₁ : N₁ ≤ H₁)
    (hG₀ : G₀ = hallPResidual p G)
    (hH : H = G₀ ⊓ H₁)
    (hP : P = G₀ ⊓ (P₁ : Subgroup G))
    (hH₀ : H₀ = hallTransferModulus p H H₁)
    (Zs : Finset G)
    (z : hallNonprincipalOrbitIndex p P₁ H₁ → P₁)
    (hzZs : ∀ i : hallNonprincipalOrbitIndex p P₁ H₁, (z i : G) ∈ Zs)
    (hzspec : ∀ i : hallNonprincipalOrbitIndex p P₁ H₁,
      orderOf ((MulAction.toPermHom P₁ (MulAction.orbit P₁ i.1.out)) (z i)) = p ∧
        (∀ g : P₁, Commute
          ((MulAction.toPermHom P₁ (MulAction.orbit P₁ i.1.out)) (z i))
          ((MulAction.toPermHom P₁ (MulAction.orbit P₁ i.1.out)) g)) ∧
        ∀ x : MulAction.orbit P₁ i.1.out,
          (MulAction.toPermHom P₁ (MulAction.orbit P₁ i.1.out)) (z i) x ≠ x)
    (hZsK : ∀ x : G, x ∈ Zs → x ∈ K) :
    hallCycleFactorDataIn p P₁ N₁ H₁ G₀ H P H₀ K
      hN₁ hN₁_le_H₁ hG₀ hH hP hH₀ := by
  classical
  have hH_le_G₀ : H ≤ G₀ := by
    rw [hH]
    exact inf_le_left
  have hH_le_H₁ : H ≤ H₁ := by
    rw [hH]
    exact inf_le_right
  have hP₁_le_H₁ : (P₁ : Subgroup G) ≤ H₁ :=
    Subgroup.le_normalizer.trans (hN₁ ▸ hN₁_le_H₁)
  have hH₀_le_H : H₀ ≤ H := by
    rw [hH₀]
    exact hallTransferModulus_le_of_inf p H₁ G₀ H hG₀ hH
  have hH₀_normal : (H₀.subgroupOf H).Normal := by
    subst H₀
    exact hallTransferModulus_subgroupOf_normal p H H₁ hH_le_H₁
      (hallTransferModulus_le_of_inf p H₁ G₀ H hG₀ hH)
  letI : (H₀.subgroupOf H).Normal := hH₀_normal
  have hcomm : ⁅H, H₁⁆ ≤ H₀ := by
    rw [hH₀]
    exact le_sup_right.trans le_sup_left
  have hcommH : commutator H ≤ H₀.subgroupOf H := by
    intro x hx
    have hxmap : H.subtype x ∈ (commutator H).map H.subtype :=
      Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    rw [Subgroup.map_subtype_commutator] at hxmap
    exact hcomm ((Subgroup.commutator_mono le_rfl hH_le_H₁) hxmap)
  letI : IsMulCommutative (H ⧸ H₀.subgroupOf H) :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le).2 hcommH
  letI : CommGroup (H ⧸ H₀.subgroupOf H) := IsMulCommutative.instCommGroup
  have hG₀_normal : G₀.Normal := by
    subst G₀
    exact hallPResidual_normal p G
  letI : G₀.Normal := hG₀_normal
  have hSup : G₀ ⊔ H₁ = ⊤ := by
    rw [hG₀, sup_comm]
    exact hall_sup_hallPResidual_eq_top_of_sylow_le p P₁ H₁ hP₁_le_H₁
  let HG₀ : Subgroup G₀ := H.subgroupOf G₀
  let eH : HG₀ ≃* H := Subgroup.subgroupOfEquivOfLe hH_le_G₀
  let π : H →* H ⧸ H₀.subgroupOf H := QuotientGroup.mk' (H₀.subgroupOf H)
  let φ : HG₀ →* H ⧸ H₀.subgroupOf H := π.comp eH.toMonoidHom

  obtain ⟨activeCycles, hactive_factor⟩ :=
    hall_lemma_14_4_5_double_coset_cycle_data p P₁ N₁ H₁ G₀ H P H₀
      hN₁ hN₁_le_H₁ hG₀ hH hP hP₁_le_H₁ hH_le_G₀ hSup HG₀ eH
        (by rfl) (by rfl) π φ rfl Zs z hzZs hzspec
  let cycleFactors : H → List H := fun u =>
    (activeCycles u).map hallActiveCycleFactor
  have hz : ∀ x : G, x ∈ Zs → x ∈ K := hZsK
  have hfactor : ∀ u : H, (u : G) ∈ P →
      hallDiagonalDefect (G := G₀) (H := HG₀) φ (eH.symm u) =
        ((cycleFactors u).map π).prod := by
    intro u hu
    simpa [cycleFactors] using hactive_factor u hu
  have hpow : hallPPowerSubgroup p H ≤ H₀ := by
    rw [hH₀]
    exact le_sup_left.trans le_sup_left
  have hengel : ∀ u : H, (u : G) ∈ P → ∀ d : H, d ∈ cycleFactors u →
      ∃ z : G, z ∈ Zs ∧ ∃ w : G, w ∈ G₀ ∧
        w * engelSymbol p (u : G) z * w⁻¹ ∈ H ∧
        (d : G) / (w * engelSymbol p (u : G) z * w⁻¹) ∈ H₀ := by
    intro u hu d hd
    change d ∈ (activeCycles u).map hallActiveCycleFactor at hd
    rw [List.mem_map] at hd
    rcases hd with ⟨c, hc, rfl⟩
    have hend := hallActiveCycle_factor_engel_congruence
      c hH₀_le_H hcomm hcommH hpow
    exact ⟨(c.z : G), c.hz, (c.w 0 : G), (c.w 0).property, hend.1, hend.2⟩
  have hdiag :=
    hall_lemma_14_4_4_generated_by_diagonal_defects
      p P₁ N₁ H₁ G₀ H P H₀ hN₁ hN₁_le_H₁ hG₀ hH hP hH₀
  simp only [hallDiagonalDefectGeneration] at hdiag
  rcases hdiag with ⟨dstar, hdstar, hgenerated⟩
  have hgenerated_cycles :=
    hall_lemma_14_4_5_generation_of_factorization H H₀ P hH₀_le_H
      dstar cycleFactors
      (fun u hu => (hdstar u).trans (hfactor u hu)) hgenerated
  exact ⟨Zs, cycleFactors, hz, hfactor, hengel, hgenerated_cycles⟩


set_option maxRecDepth 2000 in
/-- Hall Lemma 14.4.5 with Hall-Wielandt's weak-closure choice: every fixed
nonprincipal-orbit representative can be chosen inside Q. -/
public theorem hall_lemma_14_4_5_cycle_factor_engel_congruence_of_weakly_closed
    {G : Type u} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (P₁ : Sylow p G) (Q N₁ H₁ G₀ H P H₀ : Subgroup G)
    (hN₁ : N₁ = Subgroup.normalizer ((P₁ : Subgroup G) : Set G))
    (hN₁_le_H₁ : N₁ ≤ H₁)
    (hH₁ : H₁ = Subgroup.normalizer (Q : Set G))
    (hweak : WeaklyClosedIn (P₁ : Subgroup G) Q)
    (hG₀ : G₀ = hallPResidual p G)
    (hH : H = G₀ ⊓ H₁)
    (hP : P = G₀ ⊓ (P₁ : Subgroup G))
    (hH₀ : H₀ = hallTransferModulus p H H₁) :
    hallCycleFactorDataIn p P₁ N₁ H₁ G₀ H P H₀ Q
      hN₁ hN₁_le_H₁ hG₀ hH hP hH₀ := by
  classical
  let z : hallNonprincipalOrbitIndex p P₁ H₁ → P₁ := fun i =>
    Classical.choose
      (hall_nonprincipal_weakly_closed_orbit_central_prime_order_action
        p P₁ Q H₁ hH₁ hweak i.1.out
          (hall_nonprincipal_orbit_out_ne_principal p P₁ H₁ i.1 i.2))
  letI : Fintype (hallNonprincipalOrbitIndex p P₁ H₁) := Fintype.ofFinite _
  let Zs : Finset G :=
    (Finset.univ : Finset (hallNonprincipalOrbitIndex p P₁ H₁)).image
      fun i => (z i : G)
  have hzZs : ∀ i : hallNonprincipalOrbitIndex p P₁ H₁,
      (z i : G) ∈ Zs := by
    intro i
    simp [Zs]
  have hzspec : ∀ i : hallNonprincipalOrbitIndex p P₁ H₁,
      orderOf ((MulAction.toPermHom P₁ (MulAction.orbit P₁ i.1.out)) (z i)) = p ∧
        (∀ g : P₁, Commute
          ((MulAction.toPermHom P₁ (MulAction.orbit P₁ i.1.out)) (z i))
          ((MulAction.toPermHom P₁ (MulAction.orbit P₁ i.1.out)) g)) ∧
        ∀ x : MulAction.orbit P₁ i.1.out,
          (MulAction.toPermHom P₁ (MulAction.orbit P₁ i.1.out)) (z i) x ≠ x := by
    intro i
    simpa [z] using
      (Classical.choose_spec
        (hall_nonprincipal_weakly_closed_orbit_central_prime_order_action
          p P₁ Q H₁ hH₁ hweak i.1.out
            (hall_nonprincipal_orbit_out_ne_principal p P₁ H₁ i.1 i.2))).2
  have hZsQ : ∀ x : G, x ∈ Zs → x ∈ Q := by
    intro x hx
    simp only [Zs, Finset.mem_image] at hx
    rcases hx with ⟨i, _hi, rfl⟩
    exact (Classical.choose_spec
      (hall_nonprincipal_weakly_closed_orbit_central_prime_order_action
        p P₁ Q H₁ hH₁ hweak i.1.out
          (hall_nonprincipal_orbit_out_ne_principal p P₁ H₁ i.1 i.2))).1
  exact hall_lemma_14_4_5_cycle_factor_data_core_of_choice
    p P₁ N₁ H₁ G₀ H P H₀ Q
      hN₁ hN₁_le_H₁ hG₀ hH hP hH₀ Zs z hzZs hzspec hZsQ


end External
end CFSG.BenderSuzuki


