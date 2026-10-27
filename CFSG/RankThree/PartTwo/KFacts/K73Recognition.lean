module

public import CFSG.RankThree.PartTwo.KFacts.K73Wreath

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.RankThree.PartTwo.Sec11
open scoped commutatorElement

variable {P : Type*} [Group P]

theorem pow_mod_three {x : P} (hx : x ^ 3 = 1) (m : ℕ) : x ^ (m % 3) = x ^ m := by
  conv_rhs => rw [← Nat.mod_add_div m 3, pow_add, pow_mul, hx, one_pow, mul_one]

theorem pow_val_add {x : P} (hx : x ^ 3 = 1) (a b : ZMod 3) :
    x ^ (a + b).val = x ^ a.val * x ^ b.val := by
  rw [ZMod.val_add, pow_mod_three hx, pow_add]

section Recognition

variable {e t : P}

@[expose] def eConj (e t : P) (i : ℕ) : P := t ^ i * e * (t ^ i)⁻¹

theorem eConj_zero : eConj e t 0 = e := by simp [eConj]

theorem eConj_pow_three (he : e ^ 3 = 1) (i : ℕ) : eConj e t i ^ 3 = 1 := by
  rw [eConj, conj_pow, he, mul_one, mul_inv_cancel]

theorem conj_eConj (i : ℕ) : t * eConj e t i * t⁻¹ = eConj e t (i + 1) := by
  simp only [eConj, pow_succ', mul_inv_rev]
  group

theorem eConj_add_three (ht : t ^ 3 = 1) (i : ℕ) : eConj e t (i + 3) = eConj e t i := by
  simp only [eConj, pow_add, ht, mul_one]

theorem commute_eConj (hc : e * eConj e t 1 = eConj e t 1 * e) (i : ℕ) :
    Commute (eConj e t i) (eConj e t (i + 1)) := by
  induction i with
  | zero =>
    rw [eConj_zero]
    exact hc
  | succ i ih =>
    have h := congrArg (fun z => t * z * t⁻¹) ih.eq
    have e1 : ∀ a b : P, t * (a * b) * t⁻¹ = (t * a * t⁻¹) * (t * b * t⁻¹) := fun a b => by
      group
    simp only [e1, conj_eConj] at h
    exact h

theorem commute_eConj_two (ht : t ^ 3 = 1) (hc : e * eConj e t 1 = eConj e t 1 * e) :
    Commute (eConj e t 0) (eConj e t 1) ∧ Commute (eConj e t 1) (eConj e t 2) ∧
      Commute (eConj e t 0) (eConj e t 2) := by
  refine ⟨commute_eConj hc 0, commute_eConj hc 1, ?_⟩
  have h := commute_eConj hc 2
  rw [show (2 + 1 : ℕ) = 0 + 3 from rfl, eConj_add_three ht] at h
  exact h.symm

@[expose] def eVec (e t : P) (v : ZMod 3 → ZMod 3) : P :=
  eConj e t 0 ^ (v 0).val * eConj e t 1 ^ (v 1).val * eConj e t 2 ^ (v 2).val

theorem eVec_zero : eVec e t 0 = 1 := by
  simp [eVec]

theorem eVec_add (he : e ^ 3 = 1) (ht : t ^ 3 = 1) (hc : e * eConj e t 1 = eConj e t 1 * e)
    (v w : ZMod 3 → ZMod 3) : eVec e t (v + w) = eVec e t v * eVec e t w := by
  obtain ⟨h01, h12, h02⟩ := commute_eConj_two ht hc
  simp only [eVec, Pi.add_apply]
  rw [pow_val_add (eConj_pow_three he 0), pow_val_add (eConj_pow_three he 1),
    pow_val_add (eConj_pow_three he 2)]
  set a₀ := eConj e t 0 ^ (v 0).val
  set b₀ := eConj e t 0 ^ (w 0).val
  set a₁ := eConj e t 1 ^ (v 1).val
  set b₁ := eConj e t 1 ^ (w 1).val
  set a₂ := eConj e t 2 ^ (v 2).val
  set b₂ := eConj e t 2 ^ (w 2).val
  have c1 : b₀ * a₁ = a₁ * b₀ := (h01.pow_pow _ _).eq
  have c2 : b₀ * a₂ = a₂ * b₀ := (h02.pow_pow _ _).eq
  have c3 : b₁ * a₂ = a₂ * b₁ := (h12.pow_pow _ _).eq
  calc a₀ * b₀ * (a₁ * b₁) * (a₂ * b₂) = a₀ * (b₀ * a₁) * b₁ * a₂ * b₂ := by group
    _ = a₀ * a₁ * b₀ * (b₁ * a₂) * b₂ := by rw [c1]; group
    _ = a₀ * a₁ * (b₀ * a₂) * b₁ * b₂ := by rw [c3]; group
    _ = a₀ * a₁ * a₂ * (b₀ * b₁ * b₂) := by rw [c2]; group

theorem conj_eVec (ht : t ^ 3 = 1) (hc : e * eConj e t 1 = eConj e t 1 * e)
    (v : ZMod 3 → ZMod 3) : t * eVec e t v * t⁻¹ = eVec e t (fun i => v (i - 1)) := by
  obtain ⟨h01, h12, h02⟩ := commute_eConj_two ht hc
  have e3 : eConj e t 3 = eConj e t 0 := eConj_add_three ht 0
  have hconj : ∀ (i n : ℕ), t * eConj e t i ^ n * t⁻¹ = eConj e t (i + 1) ^ n := by
    intro i n
    rw [← conj_pow, conj_eConj]
  have e1 : t * eVec e t v * t⁻¹ = (t * eConj e t 0 ^ (v 0).val * t⁻¹) *
      (t * eConj e t 1 ^ (v 1).val * t⁻¹) * (t * eConj e t 2 ^ (v 2).val * t⁻¹) := by
    simp only [eVec]
    group
  rw [e1, hconj, hconj, hconj, show (2 + 1 : ℕ) = 3 from rfl, e3]
  simp only [eVec, show ((0 : ZMod 3) - 1) = 2 from rfl, show ((1 : ZMod 3) - 1) = 0 from rfl,
    show ((2 : ZMod 3) - 1) = 1 from rfl, show (0 + 1 : ℕ) = 1 from rfl,
    show (1 + 1 : ℕ) = 2 from rfl]
  have c1 : eConj e t 1 ^ (v 0).val * eConj e t 0 ^ (v 2).val =
      eConj e t 0 ^ (v 2).val * eConj e t 1 ^ (v 0).val := (h01.pow_pow _ _).eq.symm
  have c2 : eConj e t 2 ^ (v 1).val * eConj e t 0 ^ (v 2).val =
      eConj e t 0 ^ (v 2).val * eConj e t 2 ^ (v 1).val := (h02.pow_pow _ _).eq.symm
  calc eConj e t 1 ^ (v 0).val * eConj e t 2 ^ (v 1).val * eConj e t 0 ^ (v 2).val
      = eConj e t 1 ^ (v 0).val * (eConj e t 2 ^ (v 1).val * eConj e t 0 ^ (v 2).val) := by group
    _ = eConj e t 1 ^ (v 0).val * eConj e t 0 ^ (v 2).val * eConj e t 2 ^ (v 1).val := by
      rw [c2]; group
    _ = eConj e t 0 ^ (v 2).val * eConj e t 1 ^ (v 0).val * eConj e t 2 ^ (v 1).val := by
      rw [c1]

theorem conj_pow_eVec (ht : t ^ 3 = 1) (hc : e * eConj e t 1 = eConj e t 1 * e)
    (v : ZMod 3 → ZMod 3) (n : ℕ) :
    t ^ n * eVec e t v * (t ^ n)⁻¹ = eVec e t (fun i => v (i - n)) := by
  induction n generalizing v with
  | zero =>
    rw [pow_zero, inv_one, one_mul, mul_one]
    congr 1
    funext i
    congr 1
    push_cast
    ring
  | succ n ih =>
    have e1 : t ^ (n + 1) * eVec e t v * (t ^ (n + 1))⁻¹ =
        t * (t ^ n * eVec e t v * (t ^ n)⁻¹) * t⁻¹ := by
      rw [pow_succ', mul_inv_rev]
      group
    rw [e1, ih, conj_eVec ht hc]
    congr 1
    funext i
    congr 1
    push_cast
    ring

@[expose] def wVec (w : W33) : ZMod 3 → ZMod 3 :=
  fun i => Multiplicative.toAdd (w.left (Multiplicative.ofAdd i))

theorem wVec_mul (w w' : W33) :
    wVec (w * w') = wVec w + fun i => wVec w' (i - Multiplicative.toAdd w.right) := by
  funext i
  simp only [wVec, RegularWreathProduct.mul_left, Pi.mul_apply, toAdd_mul, Pi.add_apply]
  congr 3
  change Multiplicative.ofAdd (-Multiplicative.toAdd w.right + i) = _
  exact congrArg Multiplicative.ofAdd
    ((by decide : ∀ x j : ZMod 3, -x + j = j - x) (Multiplicative.toAdd w.right) i)

theorem wVec_one : wVec (1 : W33) = 0 := by
  funext i
  rfl

@[expose] def wreathHom (he : e ^ 3 = 1) (ht : t ^ 3 = 1)
    (hc : e * eConj e t 1 = eConj e t 1 * e) : W33 →* P where
  toFun w := eVec e t (wVec w) * t ^ (Multiplicative.toAdd w.right).val
  map_one' := by
    rw [wVec_one, eVec_zero, one_mul]
    exact pow_zero t
  map_mul' w w' := by
    rw [wVec_mul, eVec_add he ht hc, RegularWreathProduct.mul_right, toAdd_mul,
      pow_val_add ht]
    have h := conj_pow_eVec ht hc (wVec w') (Multiplicative.toAdd w.right).val
    rw [ZMod.natCast_zmod_val] at h
    rw [← h]
    group

theorem wreathHom_apply (he : e ^ 3 = 1) (ht : t ^ 3 = 1)
    (hc : e * eConj e t 1 = eConj e t 1 * e) (w : W33) :
    wreathHom he ht hc w = eVec e t (wVec w) * t ^ (Multiplicative.toAdd w.right).val := rfl

@[expose] def eBase (e t : P) : Subgroup P :=
  Subgroup.closure {eConj e t 0, eConj e t 1, eConj e t 2}

theorem eConj_mem_eBase {i : ℕ} (hi : i = 0 ∨ i = 1 ∨ i = 2) : eConj e t i ∈ eBase e t := by
  apply Subgroup.subset_closure
  rcases hi with rfl | rfl | rfl <;> simp

theorem eVec_mem_eBase (v : ZMod 3 → ZMod 3) : eVec e t v ∈ eBase e t :=
  Subgroup.mul_mem _ (Subgroup.mul_mem _
    (Subgroup.pow_mem _ (eConj_mem_eBase (Or.inl rfl)) _)
    (Subgroup.pow_mem _ (eConj_mem_eBase (Or.inr (Or.inl rfl))) _))
    (Subgroup.pow_mem _ (eConj_mem_eBase (Or.inr (Or.inr rfl))) _)

theorem zpow_eq_pow_val {x : P} (hx : x ^ 3 = 1) (i : ℤ) : x ^ i = x ^ ((i : ZMod 3).val) := by
  have hx' : x ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, hx]
  rw [zpow_eq_zpow_emod i hx', ← zpow_natCast, ZMod.val_intCast]
  norm_num

theorem exists_eVec_eq (he : e ^ 3 = 1) (ht : t ^ 3 = 1) (hc : e * eConj e t 1 = eConj e t 1 * e)
    {z : P} (hz : z ∈ eBase e t) : ∃ v, eVec e t v = z := by
  obtain ⟨h01, h12, h02⟩ := commute_eConj_two ht hc
  obtain ⟨i, j, k, rfl⟩ := exists_zpow_triple_of_mem_closure h01.eq h02.eq h12.eq hz
  refine ⟨![(i : ZMod 3), (j : ZMod 3), (k : ZMod 3)], ?_⟩
  simp only [eVec]
  rw [zpow_eq_pow_val (eConj_pow_three he 0) i, zpow_eq_pow_val (eConj_pow_three he 1) j,
    zpow_eq_pow_val (eConj_pow_three he 2) k]
  rfl

theorem eVec_injective (he : e ^ 3 = 1) (ht : t ^ 3 = 1) (hc : e * eConj e t 1 = eConj e t 1 * e)
    (h27 : Nat.card (eBase e t) = 27) : Function.Injective (eVec e t) := by
  let F : (ZMod 3 → ZMod 3) → eBase e t := fun v => ⟨eVec e t v, eVec_mem_eBase v⟩
  have hF : Function.Surjective F := by
    rintro ⟨z, hz⟩
    obtain ⟨v, hv⟩ := exists_eVec_eq he ht hc hz
    exact ⟨v, Subtype.ext hv⟩
  have hbij : Function.Bijective F := hF.bijective_of_nat_card_le (by
    rw [h27, Nat.card_fun]
    simp)
  intro v w h
  exact hbij.1 (Subtype.ext h)

theorem wreathHom_injective (he : e ^ 3 = 1) (ht : t ^ 3 = 1)
    (hc : e * eConj e t 1 = eConj e t 1 * e) (h27 : Nat.card (eBase e t) = 27)
    (htE : t ∉ eBase e t) : Function.Injective (wreathHom he ht hc) := by
  rw [injective_iff_map_eq_one]
  intro w hw
  rw [wreathHom_apply] at hw
  set q := Multiplicative.toAdd w.right with hq
  have htq : t ^ q.val ∈ eBase e t := by
    have : t ^ q.val = (eVec e t (wVec w))⁻¹ := eq_inv_of_mul_eq_one_right hw
    rw [this]
    exact Subgroup.inv_mem _ (eVec_mem_eBase _)
  have hq0 : q = 0 := by
    by_contra hq0
    have hval : q.val = 1 ∨ q.val = 2 := by
      have h3 := ZMod.val_lt q
      have h0 : q.val ≠ 0 := fun h => hq0 ((ZMod.val_eq_zero q).mp h)
      omega
    rcases hval with h | h
    · rw [h, pow_one] at htq
      exact htE htq
    · rw [h] at htq
      apply htE
      have h4 : (t ^ 2) ^ 2 ∈ eBase e t := Subgroup.pow_mem _ htq 2
      rwa [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_add, ht, one_mul, pow_one] at h4
  rw [hq0, ZMod.val_zero, pow_zero, mul_one] at hw
  have hv : wVec w = 0 := eVec_injective he ht hc h27 (hw.trans eVec_zero.symm)
  apply RegularWreathProduct.ext
  · funext x
    have := congrFun hv (Multiplicative.toAdd x)
    exact this
  · exact hq0

theorem wVec_delta :
    wVec (⟨fun x => if x = 1 then wreathT else 1, 1⟩ : W33) 0 = 1 ∧
      wVec (⟨fun x => if x = 1 then wreathT else 1, 1⟩ : W33) 1 = 0 ∧
      wVec (⟨fun x => if x = 1 then wreathT else 1, 1⟩ : W33) 2 = 0 := by
  decide

theorem wVec_wreathZ : wVec wreathZ 0 = 1 ∧ wVec wreathZ 1 = 1 ∧ wVec wreathZ 2 = 1 := by
  decide

theorem wreathHom_delta (he : e ^ 3 = 1) (ht : t ^ 3 = 1)
    (hc : e * eConj e t 1 = eConj e t 1 * e) :
    wreathHom he ht hc ⟨fun x => if x = 1 then wreathT else 1, 1⟩ = e := by
  obtain ⟨h0, h1, h2⟩ := wVec_delta
  rw [wreathHom_apply, eVec, h0, h1, h2]
  show eConj e t 0 ^ 1 * eConj e t 1 ^ 0 * eConj e t 2 ^ 0 * t ^ 0 = e
  rw [pow_one, pow_zero, pow_zero, pow_zero, mul_one, mul_one, mul_one, eConj_zero]

theorem wreathHom_top (he : e ^ 3 = 1) (ht : t ^ 3 = 1)
    (hc : e * eConj e t 1 = eConj e t 1 * e) : wreathHom he ht hc ⟨1, wreathT⟩ = t := by
  rw [wreathHom_apply, show wVec ⟨1, wreathT⟩ = 0 from rfl, eVec_zero, one_mul]
  exact pow_one t

theorem wreathHom_wreathZ (he : e ^ 3 = 1) (ht : t ^ 3 = 1)
    (hc : e * eConj e t 1 = eConj e t 1 * e) :
    wreathHom he ht hc wreathZ = eConj e t 0 * eConj e t 1 * eConj e t 2 := by
  obtain ⟨h0, h1, h2⟩ := wVec_wreathZ
  rw [wreathHom_apply, eVec, h0, h1, h2, wreathZ_right]
  show eConj e t 0 ^ 1 * eConj e t 1 ^ 1 * eConj e t 2 ^ 1 * t ^ 0 = _
  rw [pow_one, pow_one, pow_one, pow_zero, mul_one]

theorem range_wreathHom (he : e ^ 3 = 1) (ht : t ^ 3 = 1)
    (hc : e * eConj e t 1 = eConj e t 1 * e) :
    (wreathHom he ht hc).range = Subgroup.closure {e, t} := by
  apply le_antisymm
  · rintro _ ⟨w, rfl⟩
    rw [wreathHom_apply]
    refine Subgroup.mul_mem _ ?_ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
    have hE : eBase e t ≤ Subgroup.closure {e, t} := by
      rw [eBase, Subgroup.closure_le]
      have hmem : ∀ i : ℕ, eConj e t i ∈ Subgroup.closure ({e, t} : Set P) := fun i =>
        Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _
          (Subgroup.subset_closure (by simp)) _) (Subgroup.subset_closure (by simp)))
          (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _))
      rintro _ (rfl | rfl | rfl) <;> exact hmem _
    exact hE (eVec_mem_eBase _)
  · rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨_, wreathHom_delta he ht hc⟩
    · exact ⟨_, wreathHom_top he ht hc⟩

theorem map_wreathBase (he : e ^ 3 = 1) (ht : t ^ 3 = 1)
    (hc : e * eConj e t 1 = eConj e t 1 * e) :
    wreathBase.map (wreathHom he ht hc) = eBase e t := by
  apply le_antisymm
  · rintro _ ⟨w, hw, rfl⟩
    have hw' : w.right = 1 := mem_wreathBase.mp hw
    rw [wreathHom_apply, hw']
    show eVec e t (wVec w) * t ^ 0 ∈ eBase e t
    rw [pow_zero, mul_one]
    exact eVec_mem_eBase _
  · intro z hz
    obtain ⟨v, rfl⟩ := exists_eVec_eq he ht hc hz
    refine ⟨⟨fun x => Multiplicative.ofAdd (v (Multiplicative.toAdd x)), 1⟩,
      mem_wreathBase.mpr rfl, ?_⟩
    rw [wreathHom_apply]
    have hv : wVec ⟨fun x => Multiplicative.ofAdd (v (Multiplicative.toAdd x)), 1⟩ = v := rfl
    rw [hv]
    show eVec e t v * t ^ 0 = eVec e t v
    rw [pow_zero, mul_one]

structure WreathData (e t : P) : Prop where
  pow_e : e ^ 3 = 1
  pow_t : t ^ 3 = 1
  comm : e * eConj e t 1 = eConj e t 1 * e
  card_eBase : Nat.card (eBase e t) = 27
  not_mem : t ∉ eBase e t

namespace WreathData

variable {e t : P} (h : WreathData e t)
include h

@[expose] def hom : W33 →* P := wreathHom h.pow_e h.pow_t h.comm

theorem hom_injective : Function.Injective h.hom :=
  wreathHom_injective h.pow_e h.pow_t h.comm h.card_eBase h.not_mem

theorem range_hom : h.hom.range = Subgroup.closure {e, t} := range_wreathHom _ _ _

@[expose] noncomputable def mulEquiv : W33 ≃* Subgroup.closure ({e, t} : Set P) :=
  (MonoidHom.ofInjective h.hom_injective).trans (MulEquiv.subgroupCongr h.range_hom)

theorem card_closure : Nat.card (Subgroup.closure ({e, t} : Set P)) = 81 := by
  rw [← Nat.card_congr h.mulEquiv.toEquiv, card_wreath]

theorem map_top : (⊤ : Subgroup W33).map h.hom = Subgroup.closure {e, t} := by
  rw [← MonoidHom.range_eq_map, h.range_hom]

theorem commutator_eq :
    ⁅Subgroup.closure ({e, t} : Set P), Subgroup.closure ({e, t} : Set P)⁆ =
      (⁅(⊤ : Subgroup W33), (⊤ : Subgroup W33)⁆ : Subgroup W33).map h.hom := by
  rw [Subgroup.map_commutator, h.map_top]

theorem commutator_commutator :
    ⁅⁅Subgroup.closure ({e, t} : Set P), Subgroup.closure ({e, t} : Set P)⁆,
        Subgroup.closure ({e, t} : Set P)⁆ =
      Subgroup.zpowers (eConj e t 0 * eConj e t 1 * eConj e t 2) := by
  rw [h.commutator_eq, ← h.map_top, ← Subgroup.map_commutator, commutator_commutator_wreath,
    center_eq_zpowers_wreathZ, MonoidHom.map_zpowers]
  exact congrArg _ (wreathHom_wreathZ h.pow_e h.pow_t h.comm)

theorem map_base : wreathBase.map h.hom = eBase e t := map_wreathBase _ _ _

theorem hom_wreathZ : h.hom wreathZ = eConj e t 0 * eConj e t 1 * eConj e t 2 :=
  wreathHom_wreathZ _ _ _

theorem eBase_le : eBase e t ≤ Subgroup.closure {e, t} := by
  rw [← h.map_base, ← h.map_top]
  exact Subgroup.map_mono le_top

theorem inf_centralizer_eq :
    Subgroup.closure ({e, t} : Set P) ⊓ Subgroup.centralizer (Subgroup.closure ({e, t} : Set P)) =
      Subgroup.zpowers (eConj e t 0 * eConj e t 1 * eConj e t 2) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxT, hxc⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨w, rfl⟩ := h.range_hom ▸ hxT
    have hw : w ∈ Subgroup.center W33 := by
      rw [Subgroup.mem_center_iff]
      intro z
      apply h.hom_injective
      have := Subgroup.mem_centralizer_iff.mp hxc (h.hom z) (h.range_hom ▸ ⟨z, rfl⟩)
      rw [map_mul, map_mul]
      exact this
    rw [center_eq_zpowers_wreathZ] at hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    rw [map_zpow, h.hom_wreathZ]
    exact Subgroup.zpow_mem_zpowers _ k
  · rw [Subgroup.zpowers_le, ← h.hom_wreathZ]
    refine Subgroup.mem_inf.mpr ⟨h.range_hom ▸ ⟨wreathZ, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨z, rfl⟩ := h.range_hom ▸ hy
    rw [← map_mul, ← map_mul]
    exact congrArg h.hom ((Subgroup.mem_center_iff.mp wreathZ_mem_center z))

theorem eBase_inf_centralizer {y : P} (hyT : y ∈ Subgroup.closure {e, t})
    (hyE : y ∉ eBase e t) :
    eBase e t ⊓ Subgroup.centralizer {y} =
      Subgroup.zpowers (eConj e t 0 * eConj e t 1 * eConj e t 2) := by
  obtain ⟨w, rfl⟩ := h.range_hom ▸ hyT
  have hw : w.right ≠ 1 := by
    intro hw1
    apply hyE
    rw [← h.map_base]
    exact Subgroup.mem_map_of_mem _ (mem_wreathBase.mpr hw1)
  have key := inf_centralizer_eq_center hw
  rw [center_eq_zpowers_wreathZ] at key
  apply le_antisymm
  · intro x hx
    obtain ⟨hxE, hxc⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨z, rfl⟩ := h.range_hom ▸ (h.eBase_le hxE)
    have hz : z ∈ wreathBase ⊓ Subgroup.centralizer {w} := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [← h.map_base] at hxE
        obtain ⟨z', hz', hzz'⟩ := hxE
        rw [h.hom_injective hzz'] at hz'
        exact hz'
      · rw [Subgroup.mem_centralizer_singleton_iff] at hxc ⊢
        apply h.hom_injective
        rw [map_mul, map_mul]
        exact hxc
    rw [key] at hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [map_zpow, h.hom_wreathZ]
    exact Subgroup.zpow_mem_zpowers _ k
  · rw [Subgroup.zpowers_le, ← h.hom_wreathZ]
    have hZ : wreathZ ∈ wreathBase ⊓ Subgroup.centralizer {w} := by
      rw [key]
      exact Subgroup.mem_zpowers _
    obtain ⟨hZB, hZc⟩ := Subgroup.mem_inf.mp hZ
    refine Subgroup.mem_inf.mpr ⟨h.map_base ▸ Subgroup.mem_map_of_mem _ hZB, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hZc ⊢
    rw [← map_mul, ← map_mul, hZc]

end WreathData

end Recognition

end CFSG.RankThree.PartTwo.KFacts
