module

public import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalIndecSplitData
public import Mathlib.GroupTheory.PGroup

import CFSG.GroupTheory.OddOrderPGroup
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.Quasithin.F112R.St84

open Matrix
open scoped MatrixGroups commutatorElement

variable {G : Type*} [Group G] {F : Type} [Field F]

namespace G2qSplitData

variable {L Q Z W : Subgroup G} {α : ↥L →* SL(2, F)} {nv zv : G → Fin 2 → F} {k : G}

private theorem commutator_torus_mem (hkQ : k ∈ Subgroup.normalizer (Q : Set G)) {a : G}
    (ha : a ∈ Q) : ⁅a, k⁆ ∈ Q := by
  rw [show ⁅a, k⁆ = a * (k * a⁻¹ * k⁻¹) by rw [commutatorElement_def]; group]
  exact mul_mem ha ((Subgroup.mem_normalizer_iff.mp hkQ _).mp (inv_mem ha))

private theorem xSub_mul (hd : G2qSplitData L Q Z W α nv zv)
    (hkQ : k ∈ Subgroup.normalizer (Q : Set G)) {a₁ a₂ z₁ z₂ : G} (ha₁ : a₁ ∈ Q) (hz₁ : z₁ ∈ Z)
    (ha₂ : a₂ ∈ Q) (hz₂ : z₂ ∈ Z) :
    ∃ a ∈ Q, ∃ z ∈ Z, ⁅a₁, k⁆ * z₁ * (⁅a₂, k⁆ * z₂) = ⁅a, k⁆ * z := by
  obtain ⟨p, hp⟩ : ∃ p, p = ⁅a₁, k⁆ := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, r = ⁅a₂, k⁆ := ⟨_, rfl⟩
  have hpQ : p ∈ Q := hp ▸ commutator_torus_mem hkQ ha₁
  have hrQ : r ∈ Q := hr ▸ commutator_torus_mem hkQ ha₂
  have hc : ⁅a₂, p⁻¹⁆ * z₁ ∈ Z := mul_mem (hd.commutator_mem a₂ ha₂ _ (inv_mem hpQ)) hz₁
  refine ⟨a₂ * a₁, mul_mem ha₂ ha₁, ⁅a₂, p⁻¹⁆ * z₁ * z₂, mul_mem hc hz₂, ?_⟩
  have key1 : ⁅a₂ * a₁, k⁆ = a₂ * p * a₂⁻¹ * r := by
    rw [hp, hr]
    group
  have key2 : a₂ * p * a₂⁻¹ * (⁅a₂, p⁻¹⁆ * z₁) = p * z₁ := by group
  rw [← hp, ← hr, key1]
  calc p * z₁ * (r * z₂) = a₂ * p * a₂⁻¹ * (⁅a₂, p⁻¹⁆ * z₁) * r * z₂ := by rw [key2]; group
    _ = a₂ * p * a₂⁻¹ * (r * (⁅a₂, p⁻¹⁆ * z₁)) * z₂ := by rw [hd.comm _ hc r hrQ]; group
    _ = a₂ * p * a₂⁻¹ * r * (⁅a₂, p⁻¹⁆ * z₁ * z₂) := by group

private theorem xSub_inv (hd : G2qSplitData L Q Z W α nv zv)
    (hkQ : k ∈ Subgroup.normalizer (Q : Set G)) {a z : G} (ha : a ∈ Q) (hz : z ∈ Z) :
    ∃ a' ∈ Q, ∃ z' ∈ Z, (⁅a, k⁆ * z)⁻¹ = ⁅a', k⁆ * z' := by
  obtain ⟨p, hp⟩ : ∃ p, p = ⁅a, k⁆ := ⟨_, rfl⟩
  have hpQ : p ∈ Q := hp ▸ commutator_torus_mem hkQ ha
  refine ⟨a⁻¹, inv_mem ha, ⁅a⁻¹, p⁆ * z⁻¹,
    mul_mem (hd.commutator_mem _ (inv_mem ha) p hpQ) (inv_mem hz), ?_⟩
  have key : ⁅a⁻¹, k⁆ * ⁅a⁻¹, p⁆ = p⁻¹ := by
    rw [hp]
    group
  rw [← hp, mul_inv_rev, ← hd.comm _ (inv_mem hz) _ (inv_mem hpQ), ← key, mul_assoc]

private def xSub (hd : G2qSplitData L Q Z W α nv zv)
    (hkQ : k ∈ Subgroup.normalizer (Q : Set G)) : Subgroup G where
  carrier := {y | ∃ a ∈ Q, ∃ z ∈ Z, y = ⁅a, k⁆ * z}
  one_mem' := ⟨1, one_mem _, 1, one_mem _, by group⟩
  mul_mem' := by
    rintro _ _ ⟨a₁, ha₁, z₁, hz₁, rfl⟩ ⟨a₂, ha₂, z₂, hz₂, rfl⟩
    exact xSub_mul hd hkQ ha₁ hz₁ ha₂ hz₂
  inv_mem' := by
    rintro _ ⟨a, ha, z, hz, rfl⟩
    exact xSub_inv hd hkQ ha hz

private theorem mem_xSub {hd : G2qSplitData L Q Z W α nv zv}
    {hkQ : k ∈ Subgroup.normalizer (Q : Set G)} {y : G} :
    y ∈ xSub hd hkQ ↔ ∃ a ∈ Q, ∃ z ∈ Z, y = ⁅a, k⁆ * z :=
  Iff.rfl

private theorem xSub_conj_mem (hd : G2qSplitData L Q Z W α nv zv)
    (hkQ : k ∈ Subgroup.normalizer (Q : Set G)) (hkt : ∀ ℓ ∈ L, k * ℓ * k⁻¹ * ℓ⁻¹ ∈ Q)
    {ℓ y : G} (hℓ : ℓ ∈ L) (hy : y ∈ xSub hd hkQ) : ℓ * y * ℓ⁻¹ ∈ xSub hd hkQ := by
  obtain ⟨a, ha, z, hz, rfl⟩ := mem_xSub.mp hy
  have hb : ℓ * (k * a * k⁻¹) * ℓ⁻¹ ∈ Q :=
    hd.conj_mem_Q hℓ ((Subgroup.mem_normalizer_iff.mp hkQ a).mp ha)
  have hC := hd.commutator_mem _ hb _ (hkt ℓ hℓ)
  refine mem_xSub.mpr ⟨ℓ * a * ℓ⁻¹, hd.conj_mem_Q hℓ ha,
    ⁅ℓ * (k * a * k⁻¹) * ℓ⁻¹, k * ℓ * k⁻¹ * ℓ⁻¹⁆⁻¹ * (ℓ * z * ℓ⁻¹),
    mul_mem (inv_mem hC) (hd.nat.conj_mem ⟨ℓ, hℓ⟩ z hz), ?_⟩
  group

theorem commutator_inf_le_of_torus (hd : G2qSplitData L Q Z W α nv zv)
    (hkQ : k ∈ Subgroup.normalizer (Q : Set G)) (hkt : ∀ ℓ ∈ L, k * ℓ * k⁻¹ * ℓ⁻¹ ∈ Q)
    {t : F} (ht : t ≠ 1) (hμ : ∀ a ∈ Q, nv (k * a * k⁻¹) = t • nv a)
    (hkW : ∀ w ∈ W, ⁅k, w⁆ ∈ Z) : ⁅Q, L⁆ ⊓ W ≤ Z := by
  have hkQ' : ∀ a ∈ Q, k * a * k⁻¹ ∈ Q := fun a ha => (Subgroup.mem_normalizer_iff.mp hkQ a).mp ha
  have ht' : (1 : F) - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
  have hcoord : ∀ a ∈ Q, nv ⁅a, k⁆ = (1 - t) • nv a := by
    intro a ha
    rw [show ⁅a, k⁆ = a * (k * a⁻¹ * k⁻¹) by rw [commutatorElement_def]; group,
      hd.natW.map_mul _ ha _ (hkQ' _ (inv_mem ha)), hμ _ (inv_mem ha), hd.natW.map_inv ha,
      smul_neg, sub_smul, one_smul, sub_eq_add_neg]
  have hZX : Z ≤ xSub hd hkQ := fun z hz => mem_xSub.mpr ⟨1, one_mem _, z, hz, by group⟩
  have hXL : ∀ ℓ ∈ L, ∀ y ∈ xSub hd hkQ, ℓ * y * ℓ⁻¹ ∈ xSub hd hkQ :=
    fun ℓ hℓ y hy => xSub_conj_mem hd hkQ hkt hℓ hy
  have hQWX : ∀ a ∈ Q, ∃ w ∈ W, ∃ x ∈ xSub hd hkQ, a = w * x := by
    intro a ha
    obtain ⟨b, hb, hbv⟩ := hd.natW.surj ((1 - t)⁻¹ • nv a)
    have hxQ : ⁅b, k⁆ ∈ Q := commutator_torus_mem hkQ hb
    refine ⟨a * ⁅b, k⁆⁻¹, ?_, ⁅b, k⁆, mem_xSub.mpr ⟨b, hb, 1, one_mem _, (mul_one _).symm⟩,
      (inv_mul_cancel_right _ _).symm⟩
    refine (hd.natW.eq_zero_iff _ (mul_mem ha (inv_mem hxQ))).mp ?_
    rw [hd.natW.map_mul _ ha _ (inv_mem hxQ), hd.natW.map_inv hxQ, hcoord b hb, hbv, smul_smul,
      mul_inv_cancel₀ ht', one_smul, add_neg_cancel]
  have hRX : ⁅Q, L⁆ ≤ xSub hd hkQ := by
    rw [Subgroup.commutator_le]
    intro a ha ℓ hℓ
    obtain ⟨w, hw, x, hx, rfl⟩ := hQWX a ha
    rw [show ⁅w * x, ℓ⁆ = w * (x * (ℓ * x⁻¹ * ℓ⁻¹)) * w⁻¹ * ⁅w, ℓ⁆ by group]
    exact mul_mem (hXL w (hd.le (hd.le_Q hw)) _ (mul_mem hx (hXL ℓ hℓ _ (inv_mem hx))))
      (hZX (hd.commutator_W w hw ℓ hℓ))
  intro y hy
  obtain ⟨hyR, hyW⟩ := Subgroup.mem_inf.mp hy
  obtain ⟨a, ha, z, hz, rfl⟩ := mem_xSub.mp (hRX hyR)
  have hcQ := commutator_torus_mem hkQ ha
  have hcW : ⁅a, k⁆ ∈ W := by
    have h := mul_mem hyW (inv_mem (hd.center_le hz))
    rwa [mul_inv_cancel_right] at h
  have haW : a ∈ W := by
    refine (hd.natW.eq_zero_iff _ ha).mp ?_
    have h0 := (hd.natW.eq_zero_iff _ hcQ).mpr hcW
    rw [hcoord a ha] at h0
    exact (smul_eq_zero.mp h0).resolve_left ht'
  have hcZ : ⁅a, k⁆ ∈ Z := by
    rw [← commutatorElement_inv]
    exact inv_mem (hkW a haW)
  exact mul_mem hcZ hz

private theorem conj_eq_of_trivial (hd : G2qSplitData L Q Z W α nv zv) (hQ2 : IsPGroup 2 Q)
    {m : ℕ} (hm : Odd m) (hkm : k ^ m = 1) (hkQ : k ∈ Subgroup.normalizer (Q : Set G))
    (hZ : ∀ z ∈ Z, zv (k * z * k⁻¹) = zv z) (hN : ∀ a ∈ Q, nv (k * a * k⁻¹) = nv a)
    (hkW : ∀ w ∈ W, ⁅k, w⁆ ∈ Z) : ∀ a ∈ Q, k * a * k⁻¹ = a := by
  have hZfix : k ∈ Subgroup.centralizer (Z : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have h := hd.nat.eq_of_eq (hd.torus_conj_mem_Z hkQ hz) hz (hZ z hz)
    calc z * k = k * z * k⁻¹ * k := by rw [h]
      _ = k * z := by group
  have hWfix := CFSG.mem_centralizer_of_odd_pow_eq_one (hQ2.to_le hd.Z_le_Q) hm hkm hZfix hkW
  have hQW : ∀ a ∈ Q, ⁅k, a⁆ ∈ W := by
    intro a ha
    have hc := hd.natW.inv_mul_mem ha ((Subgroup.mem_normalizer_iff.mp hkQ a).mp ha) (hN a ha).symm
    rw [show ⁅k, a⁆ = a * (a⁻¹ * (k * a * k⁻¹)) * a⁻¹ by rw [commutatorElement_def]; group]
    exact hd.conj_mem_W (hd.le ha) hc
  have hQfix := CFSG.mem_centralizer_of_odd_pow_eq_one (hQ2.to_le hd.le_Q) hm hkm hWfix hQW
  intro a ha
  rw [← Subgroup.mem_centralizer_iff.mp hQfix a ha, mul_inv_cancel_right]

variable {H₀ : Subgroup G}

private theorem torusN_mul (hd : G2qSplitData L Q Z W α nv zv)
    (hL : ∀ k ∈ H₀, k ∈ Subgroup.normalizer (L : Set G))
    (hQ : ∀ k ∈ H₀, k ∈ Subgroup.normalizer (Q : Set G))
    (ht : ∀ k ∈ H₀, ∀ ℓ ∈ L, k * ℓ * k⁻¹ * ℓ⁻¹ ∈ Q) {k k' : G} (hk : k ∈ H₀) (hk' : k' ∈ H₀) :
    natSecConjScalar Q nv (k * k') = natSecConjScalar Q nv k * natSecConjScalar Q nv k' :=
  hd.natW.natSecConjScalar_mul (fun x hx => (Subgroup.mem_normalizer_iff.mp (hQ k' hk') x).mp hx)
    (hd.exists_torus_natW (hL k hk) (hQ k hk) (ht k hk))
    (hd.exists_torus_natW (hL k' hk') (hQ k' hk') (ht k' hk'))
    (hd.exists_torus_natW (hL _ (mul_mem hk hk')) (hQ _ (mul_mem hk hk'))
      (ht _ (mul_mem hk hk')))

private theorem torusZ_mul (hd : G2qSplitData L Q Z W α nv zv)
    (hQ : ∀ k ∈ H₀, k ∈ Subgroup.normalizer (Q : Set G))
    (ht : ∀ k ∈ H₀, ∀ ℓ ∈ L, k * ℓ * k⁻¹ * ℓ⁻¹ ∈ Q) {k k' : G} (hk : k ∈ H₀) (hk' : k' ∈ H₀) :
    natSecConjScalar Z zv (k * k') = natSecConjScalar Z zv k * natSecConjScalar Z zv k' :=
  hd.nat.natSecConjScalar_mul (fun _ hx => hd.torus_conj_mem_Z (hQ k' hk') hx)
    (hd.exists_torus_nat (hQ k hk) (ht k hk)) (hd.exists_torus_nat (hQ k' hk') (ht k' hk'))
    (hd.exists_torus_nat (hQ _ (mul_mem hk hk')) (ht _ (mul_mem hk hk')))

private theorem torusN_inv (hd : G2qSplitData L Q Z W α nv zv)
    (hL : ∀ k ∈ H₀, k ∈ Subgroup.normalizer (L : Set G))
    (hQ : ∀ k ∈ H₀, k ∈ Subgroup.normalizer (Q : Set G))
    (ht : ∀ k ∈ H₀, ∀ ℓ ∈ L, k * ℓ * k⁻¹ * ℓ⁻¹ ∈ Q) {k : G} (hk : k ∈ H₀) :
    natSecConjScalar Q nv k * natSecConjScalar Q nv k⁻¹ = 1 := by
  rw [← torusN_mul hd hL hQ ht hk (inv_mem hk), mul_inv_cancel, hd.natW.natSecConjScalar_one]

private theorem torusZ_inv (hd : G2qSplitData L Q Z W α nv zv)
    (hQ : ∀ k ∈ H₀, k ∈ Subgroup.normalizer (Q : Set G))
    (ht : ∀ k ∈ H₀, ∀ ℓ ∈ L, k * ℓ * k⁻¹ * ℓ⁻¹ ∈ Q) {k : G} (hk : k ∈ H₀) :
    natSecConjScalar Z zv k * natSecConjScalar Z zv k⁻¹ = 1 := by
  rw [← torusZ_mul hd hQ ht hk (inv_mem hk), mul_inv_cancel, hd.nat.natSecConjScalar_one]

private theorem case_one (hd : G2qSplitData L Q Z W α nv zv) (hQ2 : IsPGroup 2 Q)
    (hodd : Odd (Nat.card H₀)) (hL : ∀ k ∈ H₀, k ∈ Subgroup.normalizer (L : Set G))
    (hQ : ∀ k ∈ H₀, k ∈ Subgroup.normalizer (Q : Set G))
    (ht : ∀ k ∈ H₀, ∀ ℓ ∈ L, k * ℓ * k⁻¹ * ℓ⁻¹ ∈ Q)
    (hfaith : ∀ k ∈ H₀, (∀ a ∈ Q, k * a * k⁻¹ = a) → k = 1) (hk : k ∈ H₀) (hk1 : k ≠ 1)
    (hkμν : natSecConjScalar Q nv k = natSecConjScalar Z zv k) : ⁅Q, L⁆ ⊓ W ≤ Z := by
  have hμ0 : natSecConjScalar Q nv k ≠ 0 :=
    left_ne_zero_of_mul_eq_one (torusN_inv hd hL hQ ht hk)
  have hμk := natSecConjScalar_spec (hd.exists_torus_natW (hL k hk) (hQ k hk) (ht k hk))
  have hνk := natSecConjScalar_spec (hd.exists_torus_nat (hQ k hk) (ht k hk))
  rw [← hkμν] at hνk
  have hkW : ∀ w ∈ W, ⁅k, w⁆ ∈ Z := by
    intro w hw
    obtain ⟨s, hs⟩ := hd.exists_pair hw
    have hw' := hd.torus_conj_mem_W (hL k hk) (hQ k hk) hw
    obtain ⟨s', hs'⟩ := hd.exists_pair hw'
    have hss : s' = s :=
      mul_right_cancel₀ hμ0 ((hd.torus_pair (hQ k hk) hμk hνk hw hs hs').trans (mul_comm _ _))
    rw [hss] at hs'
    have hc := hd.inv_mul_mem_of_pair_eq hw hw' hs hs'
    rw [show ⁅k, w⁆ = w * (w⁻¹ * (k * w * k⁻¹)) * w⁻¹ by rw [commutatorElement_def]; group,
      hd.conj_eq_of_mem (hd.le_Q hw) hc]
    exact hc
  have hμ1 : natSecConjScalar Q nv k ≠ 1 := by
    intro h1
    have hkm : k ^ Nat.card H₀ = 1 := by
      have h := congrArg Subtype.val (pow_card_eq_one' (x := (⟨k, hk⟩ : ↥H₀)))
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at h
    refine hk1 (hfaith k hk (hd.conj_eq_of_trivial hQ2 hodd hkm (hQ k hk) (fun z hz => ?_)
      (fun a ha => ?_) hkW))
    · rw [hνk z hz, h1, one_smul]
    · rw [hμk a ha, h1, one_smul]
  exact hd.commutator_inf_le_of_torus (hQ k hk) (ht k hk) hμ1 hμk hkW

private theorem exists_torus_eq [Finite F] (hd : G2qSplitData L Q Z W α nv zv)
    (hcard : Nat.card H₀ = Nat.card F - 1) (hL : ∀ k ∈ H₀, k ∈ Subgroup.normalizer (L : Set G))
    (hQ : ∀ k ∈ H₀, k ∈ Subgroup.normalizer (Q : Set G))
    (ht : ∀ k ∈ H₀, ∀ ℓ ∈ L, k * ℓ * k⁻¹ * ℓ⁻¹ ∈ Q)
    (hinj : ∀ k ∈ H₀, natSecConjScalar Q nv k = natSecConjScalar Z zv k → k = 1) {u : F}
    (hu : u ≠ 0) : ∃ k ∈ H₀, natSecConjScalar Z zv k = u * natSecConjScalar Q nv k := by
  have hμ0 : ∀ k ∈ H₀, natSecConjScalar Q nv k ≠ 0 :=
    fun k hk => left_ne_zero_of_mul_eq_one (torusN_inv hd hL hQ ht hk)
  have hν0 : ∀ k ∈ H₀, natSecConjScalar Z zv k ≠ 0 :=
    fun k hk => left_ne_zero_of_mul_eq_one (torusZ_inv hd hQ ht hk)
  let χ : ↥H₀ → Fˣ := fun k => Units.mk0 (natSecConjScalar Z zv k / natSecConjScalar Q nv k)
    (div_ne_zero (hν0 k k.2) (hμ0 k k.2))
  have hχ : Function.Injective χ := by
    rintro ⟨k, hk⟩ ⟨k', hk'⟩ h
    have h' := congrArg Units.val h
    simp only [χ, Units.val_mk0] at h'
    rw [div_eq_div_iff (hμ0 k hk) (hμ0 k' hk')] at h'
    have hm : k⁻¹ * k' = 1 := by
      refine hinj _ (mul_mem (inv_mem hk) hk') ?_
      rw [torusN_mul hd hL hQ ht (inv_mem hk) hk', torusZ_mul hd hQ ht (inv_mem hk) hk',
        eq_inv_of_mul_eq_one_right (torusN_inv hd hL hQ ht hk),
        eq_inv_of_mul_eq_one_right (torusZ_inv hd hQ ht hk), inv_mul_eq_div, inv_mul_eq_div,
        div_eq_div_iff (hμ0 k hk) (hν0 k hk)]
      linear_combination h'
    exact Subtype.ext (inv_mul_eq_one.mp hm)
  have hbij := hχ.bijective_of_nat_card_le (by rw [Nat.card_units, hcard])
  obtain ⟨⟨k, hk⟩, hk'⟩ := hbij.2 (Units.mk0 u hu)
  refine ⟨k, hk, ?_⟩
  have h := congrArg Units.val hk'
  simp only [χ, Units.val_mk0] at h
  rw [← h, div_mul_cancel₀ _ (hμ0 k hk)]

private theorem W_le_commutator_of_inj [Finite F] (hd : G2qSplitData L Q Z W α nv zv)
    (hcard : Nat.card H₀ = Nat.card F - 1) (hL : ∀ k ∈ H₀, k ∈ Subgroup.normalizer (L : Set G))
    (hQ : ∀ k ∈ H₀, k ∈ Subgroup.normalizer (Q : Set G))
    (ht : ∀ k ∈ H₀, ∀ ℓ ∈ L, k * ℓ * k⁻¹ * ℓ⁻¹ ∈ Q)
    (hinj : ∀ k ∈ H₀, natSecConjScalar Q nv k = natSecConjScalar Z zv k → k = 1) {y : G}
    (hyR : y ∈ ⁅Q, L⁆) (hyW : y ∈ W) (hyZ : y ∉ Z) : W ≤ ⁅Q, L⁆ := by
  intro w hw
  by_cases hwZ : w ∈ Z
  · exact hd.center_le_commutator hwZ
  obtain ⟨sy, hsy⟩ := hd.exists_pair hyW
  obtain ⟨sw, hsw⟩ := hd.exists_pair hw
  have hsy0 : sy ≠ 0 := fun h => hyZ ((hd.pair_eq_zero_iff hyW hsy).mp h)
  have hsw0 : sw ≠ 0 := fun h => hwZ ((hd.pair_eq_zero_iff hw hsw).mp h)
  obtain ⟨k, hk, hkν⟩ := exists_torus_eq hd hcard hL hQ ht hinj (div_ne_zero hsw0 hsy0)
  have hμ0 : natSecConjScalar Q nv k ≠ 0 :=
    left_ne_zero_of_mul_eq_one (torusN_inv hd hL hQ ht hk)
  have hy' := hd.torus_conj_mem_W (hL k hk) (hQ k hk) hyW
  obtain ⟨s', hs'⟩ := hd.exists_pair hy'
  have hrel := hd.torus_pair (hQ k hk)
    (natSecConjScalar_spec (hd.exists_torus_natW (hL k hk) (hQ k hk) (ht k hk)))
    (natSecConjScalar_spec (hd.exists_torus_nat (hQ k hk) (ht k hk))) hyW hsy hs'
  rw [hkν, mul_right_comm, div_mul_cancel₀ _ hsy0] at hrel
  rw [mul_right_cancel₀ hμ0 hrel] at hs'
  have hc := hd.inv_mul_mem_of_pair_eq hy' hw hs' hsw
  have hy'R : k * y * k⁻¹ ∈ ⁅Q, L⁆ := conj_mem_commutator_of_conj_mem
    (fun a ha => (Subgroup.mem_normalizer_iff.mp (hQ k hk) a).mp ha)
    (fun ℓ hℓ => (Subgroup.mem_normalizer_iff.mp (hL k hk) ℓ).mp hℓ) hyR
  rw [show w = k * y * k⁻¹ * ((k * y * k⁻¹)⁻¹ * w) by group]
  exact mul_mem hy'R (hd.center_le_commutator hc)

theorem commutator_inf_eq_or [Finite F] (hd : G2qSplitData L Q Z W α nv zv)
    (hQ2 : IsPGroup 2 Q) (hcard : Nat.card H₀ = Nat.card F - 1) (hodd : Odd (Nat.card H₀))
    (hL : ∀ k ∈ H₀, k ∈ Subgroup.normalizer (L : Set G))
    (hQ : ∀ k ∈ H₀, k ∈ Subgroup.normalizer (Q : Set G))
    (ht : ∀ k ∈ H₀, ∀ ℓ ∈ L, k * ℓ * k⁻¹ * ℓ⁻¹ ∈ Q)
    (hfaith : ∀ k ∈ H₀, (∀ a ∈ Q, k * a * k⁻¹ = a) → k = 1) :
    ⁅Q, L⁆ ⊓ W = Z ∨ W ≤ ⁅Q, L⁆ := by
  have hZRW : Z ≤ ⁅Q, L⁆ ⊓ W := le_inf hd.center_le_commutator hd.center_le
  by_cases hcase : ∃ k ∈ H₀, k ≠ 1 ∧ natSecConjScalar Q nv k = natSecConjScalar Z zv k
  · obtain ⟨k, hk, hk1, hkμν⟩ := hcase
    exact Or.inl (le_antisymm (case_one hd hQ2 hodd hL hQ ht hfaith hk hk1 hkμν) hZRW)
  · have hinj : ∀ k ∈ H₀, natSecConjScalar Q nv k = natSecConjScalar Z zv k → k = 1 :=
      fun k hk h => by_contra fun hk1 => hcase ⟨k, hk, hk1, h⟩
    by_cases hRW : ⁅Q, L⁆ ⊓ W ≤ Z
    · exact Or.inl (le_antisymm hRW hZRW)
    · obtain ⟨y, hy, hyZ⟩ := SetLike.not_le_iff_exists.mp hRW
      exact Or.inr (W_le_commutator_of_inj hd hcard hL hQ ht hinj (Subgroup.mem_inf.mp hy).1
        (Subgroup.mem_inf.mp hy).2 hyZ)

end G2qSplitData

end CFSG.Quasithin.F112R.St84

end
