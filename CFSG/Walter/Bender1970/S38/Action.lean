module

public import CFSG.Walter.Bender1970.S1.FixedPointFree
public import CFSG.Walter.Bender1970.S38.RegularNilpotent
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.Algebra.Module.ZMod

public section

namespace CFSG.Walter

section Fix

variable {A Y : Type*} [Group A] [Group Y]

@[expose] def fixOf (ρ : Y →* MulAut A) (S : Subgroup Y) : Subgroup A where
  carrier := {a | ∀ s ∈ S, ρ s a = a}
  mul_mem' {a b} ha hb s hs := by rw [map_mul, ha s hs, hb s hs]
  one_mem' s _ := map_one _
  inv_mem' {a} ha s hs := by rw [map_inv, ha s hs]

theorem mem_fixOf {ρ : Y →* MulAut A} {S : Subgroup Y} {a : A} :
    a ∈ fixOf ρ S ↔ ∀ s ∈ S, ρ s a = a := Iff.rfl

@[expose] def stabOf (ρ : Y →* MulAut A) (a : A) : Subgroup Y where
  carrier := {y | ρ y a = a}
  mul_mem' {x y} hx hy := by
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    rw [map_mul, MulAut.mul_apply, hy, hx]
  one_mem' := by simp
  inv_mem' {x} hx := by
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [map_inv]
    conv_lhs => rw [← hx]
    exact MulAut.inv_apply_self A (ρ x) a

theorem mem_stabOf {ρ : Y →* MulAut A} {a : A} {y : Y} : y ∈ stabOf ρ a ↔ ρ y a = a := Iff.rfl

theorem mem_fixOf_iff_le_stabOf {ρ : Y →* MulAut A} {S : Subgroup Y} {a : A} :
    a ∈ fixOf ρ S ↔ S ≤ stabOf ρ a := Iff.rfl

theorem map_mem_fixOf_conj {ρ : Y →* MulAut A} {S : Subgroup Y} {a : A} (ha : a ∈ fixOf ρ S)
    (y : Y) {s : Y} (hs : y⁻¹ * s * y ∈ S) : ρ s (ρ y a) = ρ y a := by
  have h := ha _ hs
  rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply] at h
  calc ρ s (ρ y a) = ρ y ((ρ y⁻¹) (ρ s (ρ y a))) := by
        rw [map_inv, MulAut.apply_inv_self]
    _ = ρ y a := by rw [h]

end Fix

section OnePointFive

variable {A Y : Type*} [CommGroup A] [Finite A] [Group Y] [Finite Y]

theorem card_eq_card_fixOf_pow (h2 : ∀ a : A, a ^ 2 = 1) (ρ : Y →* MulAut A)
    {N R : Subgroup Y} (hN : IsMulCommutative N) (hRN : R ≤ Subgroup.normalizer (N : Set Y))
    (hfpf : ∀ x ∈ R, x ≠ 1 → ∀ n ∈ N, x * n * x⁻¹ = n → n = 1) (hNodd : Odd (Nat.card N))
    (hCN : ∀ a : A, (∀ n ∈ N, ρ n a = a) → a = 1) :
    Nat.card A = Nat.card (fixOf ρ R) ^ Nat.card R := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Module (ZMod 2) (Additive A) :=
    AddCommMonoid.zmodModule (n := 2) fun x => by
      change Additive.ofMul ((Additive.toMul x) ^ 2) = 0
      rw [h2]
      rfl
  let ρ' : Representation (ZMod 2) Y (Additive A) :=
    { toFun := fun y => (MulEquiv.toAdditive (ρ y)).toAddMonoidHom.toZModLinearMap 2
      map_one' := by
        ext x
        simp
      map_mul' := fun y z => by
        ext x
        simp }
  have hρ' : ∀ (y : Y) (x : Additive A), ρ' y x = Additive.ofMul (ρ y (Additive.toMul x)) :=
    fun _ _ => rfl
  have hNchar : ((Nat.card N : ℕ) : ZMod 2) ≠ 0 := by
    rw [ne_eq, ZMod.natCast_eq_zero_iff_even, Nat.not_even_iff_odd]
    exact hNodd
  have hCN' : ∀ v : Additive A, (∀ n ∈ N, ρ' n v = v) → v = 0 := by
    intro v hv
    have h1 := hCN (Additive.toMul v) fun n hn => by
      have := hv n hn
      rw [hρ'] at this
      exact congrArg Additive.toMul this
    exact congrArg Additive.ofMul h1
  have key := bender1970_1_5_finrank_eq ρ' N R hN hRN hfpf hNchar hCN'
  set I := Representation.invariants (ρ'.comp R.subtype) with hI
  have hIcard : Nat.card I = Nat.card (fixOf ρ R) := by
    refine Nat.card_congr
      { toFun := fun v => ⟨Additive.toMul (v : Additive A), fun r hr => ?_⟩
        invFun := fun a => ⟨Additive.ofMul (a : A), fun r => ?_⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    · have h := v.2 ⟨r, hr⟩
      exact congrArg Additive.toMul h
    · exact congrArg Additive.ofMul (a.2 r r.2)
  have hA : 2 ^ Module.finrank (ZMod 2) (Additive A) = Nat.card A :=
    FiniteField.pow_finrank_eq_natCard 2 (Additive A)
  have hIc : 2 ^ Module.finrank (ZMod 2) I = Nat.card I := FiniteField.pow_finrank_eq_natCard 2 I
  rw [← hA, key, ← hIcard, ← hIc, ← pow_mul, mul_comm]

end OnePointFive

variable {A Y : Type*} [CommGroup A] [Group Y]

structure Bender38Action (ρ : Y →* MulAut A) (W Q : Subgroup A) (X R : Subgroup Y) : Prop where
  sq_eq_one : ∀ a : A, a ^ 2 = 1
  injective : Function.Injective ρ
  odd_card : Odd (Nat.card Y)
  inf_eq_bot : W ⊓ Q = ⊥
  sup_eq_top : W ⊔ Q = ⊤
  ne_bot : W ≠ ⊥
  four_le_card : 4 ≤ Nat.card Q
  map_mem_W : ∀ x ∈ X, ∀ w ∈ W, ρ x w ∈ W
  mem_X : ∀ y : Y, ∀ w ∈ W, w ≠ 1 → ρ y w ∈ W → y ∈ X
  map_mem_Q : ∀ x ∈ X, ∀ v ∈ Q, ρ x v ∈ Q
  le_X : R ≤ X
  conj_mem : ∀ x ∈ X, ∀ r ∈ R, x * r * x⁻¹ ∈ R
  isCyclic : IsCyclic R
  fix_W : ∀ r ∈ R, ∀ w ∈ W, ρ r w = w
  free : ∀ r ∈ R, ∀ v ∈ Q, ρ r v = v → v ≠ 1 → r = 1
  trans : ∀ u ∈ Q, u ≠ 1 → ∀ v ∈ Q, v ≠ 1 → ∃ r ∈ R, ρ r u = v

namespace Bender38Action

variable {ρ : Y →* MulAut A} {W Q : Subgroup A} {X R : Subgroup Y}
  (hD : Bender38Action ρ W Q X R)
include hD

theorem exists_mul (a : A) : ∃ w ∈ W, ∃ v ∈ Q, w * v = a := by
  have ha : a ∈ W ⊔ Q := hD.sup_eq_top ▸ Subgroup.mem_top a
  exact Subgroup.mem_sup.mp ha

theorem eq_of_mul_eq {w w' v v' : A} (hw : w ∈ W) (hw' : w' ∈ W) (hv : v ∈ Q) (hv' : v' ∈ Q)
    (h : w * v = w' * v') : w = w' ∧ v = v' := by
  have h1 : w'⁻¹ * w = v' * v⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h, mul_inv_cancel_right]
  have h2 : w'⁻¹ * w ∈ W ⊓ Q :=
    ⟨W.mul_mem (W.inv_mem hw') hw, h1 ▸ Q.mul_mem hv' (Q.inv_mem hv)⟩
  rw [hD.inf_eq_bot, Subgroup.mem_bot, inv_mul_eq_one] at h2
  subst h2
  refine ⟨rfl, ?_⟩
  exact mul_left_cancel h

theorem map_mul_of_mem_R {r : Y} (hr : r ∈ R) {w v : A} (hw : w ∈ W) :
    ρ r (w * v) = w * ρ r v := by
  rw [map_mul, hD.fix_W r hr w hw]

theorem fix_iff {r : Y} (hr : r ∈ R) (hr1 : r ≠ 1) (a : A) : ρ r a = a ↔ a ∈ W := by
  obtain ⟨w, hw, v, hv, rfl⟩ := hD.exists_mul a
  rw [hD.map_mul_of_mem_R hr hw]
  constructor
  · intro h
    have h1 : ρ r v = v := mul_left_cancel h
    by_cases hv1 : v = 1
    · rw [hv1, mul_one]
      exact hw
    · exact absurd (hD.free r hr v hv h1 hv1) hr1
  · intro h
    have hvW : v ∈ W := by simpa using W.mul_mem (W.inv_mem hw) h
    have hv1 : v = 1 := by
      have : v ∈ W ⊓ Q := ⟨hvW, hv⟩
      rwa [hD.inf_eq_bot, Subgroup.mem_bot] at this
    rw [hv1, map_one]

theorem mem_X_of_conj_mem {y r : Y} (hr : r ∈ R) (hr1 : r ≠ 1) (h : y * r * y⁻¹ ∈ R) :
    y ∈ X := by
  obtain ⟨⟨w, hw⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hD.ne_bot
  have hr1' : y * r * y⁻¹ ≠ 1 := by
    intro h1
    apply hr1
    calc r = y⁻¹ * (y * r * y⁻¹) * y := by group
      _ = 1 := by rw [h1]; group
  have hfix : ρ (y * r * y⁻¹) (ρ y w) = ρ y w := by
    rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, map_inv, MulAut.inv_apply_self,
      hD.fix_W r hr w hw]
  have hmem := (hD.fix_iff h hr1' _).mp hfix
  exact hD.mem_X y w hw (fun h => hw1 (Subtype.ext h)) hmem

theorem mem_X_of_fix {y : Y} {w : A} (hw : w ∈ W) (hw1 : w ≠ 1) (h : ρ y w = w) : y ∈ X :=
  hD.mem_X y w hw hw1 (by rw [h]; exact hw)

theorem eq_one_of_not_mem {y : Y} (hy : y ∉ X) {w : A} (hw : w ∈ W) (h : ρ y w ∈ W) :
    w = 1 := by
  by_contra hw1
  exact hy (hD.mem_X y w hw hw1 h)

theorem eq_one_of_mem_R_of_fix_Q {r : Y} (hr : r ∈ R) (h : ∀ v ∈ Q, ρ r v = v) : r = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨v, hv, hv1⟩ : ∃ v ∈ Q, v ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : Q = ⊥ := (Subgroup.eq_bot_iff_forall Q).mpr hcon
    have h4 := hD.four_le_card
    rw [this, Subgroup.card_bot] at h4
    omega
  exact hD.free r hr v hv (h v hv) hv1

theorem isPGroup_two (S : Subgroup A) : IsPGroup 2 S := fun a =>
  ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow, hD.sq_eq_one, Subgroup.coe_one])⟩

theorem card_eq_mul : Nat.card A = Nat.card W * Nat.card Q := by
  classical
  refine (Nat.card_congr (Equiv.ofBijective (fun x : W × Q => (x.1 : A) * x.2)
    ⟨fun x y h => ?_, fun a => ?_⟩)).symm.trans (Nat.card_prod _ _)
  · obtain ⟨h1, h2⟩ := hD.eq_of_mul_eq x.1.2 y.1.2 x.2.2 y.2.2 h
    exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
  · obtain ⟨w, hw, v, hv, rfl⟩ := hD.exists_mul a
    exact ⟨(⟨w, hw⟩, ⟨v, hv⟩), rfl⟩

section Finite

variable [Finite A]

theorem card_R_add_one : Nat.card R + 1 = Nat.card Q := by
  classical
  obtain ⟨v₀, hv₀, hv₀1⟩ : ∃ v ∈ Q, v ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : Q = ⊥ := (Subgroup.eq_bot_iff_forall Q).mpr hcon
    have h4 := hD.four_le_card
    rw [this, Subgroup.card_bot] at h4
    omega
  rw [← card_ne_one_add_one Q]
  congr 1
  refine Nat.card_congr (Equiv.ofBijective (fun r : R =>
    (⟨⟨ρ r v₀, hD.map_mem_Q r (hD.le_X r.2) v₀ hv₀⟩, fun h => hv₀1 ?_⟩ : {v : Q // v ≠ 1}))
    ⟨fun r₁ r₂ h => ?_, fun v => ?_⟩)
  · have h' := congrArg Subtype.val h
    exact (MulEquiv.map_eq_one_iff _).mp h'
  · have h1 : ρ r₁ v₀ = ρ r₂ v₀ := congrArg (fun x => ((x : {v : Q // v ≠ 1}) : A)) h
    have h2 : ρ ((r₁ : Y)⁻¹ * r₂) v₀ = v₀ := by
      rw [map_mul, MulAut.mul_apply, ← h1, map_inv, MulAut.inv_apply_self]
    have h3 := hD.free _ (R.mul_mem (R.inv_mem r₁.2) r₂.2) v₀ hv₀ h2 hv₀1
    rw [inv_mul_eq_one] at h3
    exact Subtype.ext h3
  · obtain ⟨r, hr, hrv⟩ := hD.trans v₀ hv₀ hv₀1 v v.1.2 (fun h => v.2 (Subtype.ext h))
    exact ⟨⟨r, hr⟩, Subtype.ext (Subtype.ext hrv)⟩

theorem exists_ne_one : ∃ r ∈ R, r ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have : R = ⊥ := (Subgroup.eq_bot_iff_forall R).mpr hcon
  have h := hD.card_R_add_one
  rw [this, Subgroup.card_bot] at h
  have h4 := hD.four_le_card
  omega

end Finite

@[expose] noncomputable def restrictQ : X →* MulAut Q where
  toFun x :=
    { toFun := fun v => ⟨ρ x v, hD.map_mem_Q x x.2 v v.2⟩
      invFun := fun v => ⟨ρ (x⁻¹ : X) v, hD.map_mem_Q _ (x⁻¹).2 v v.2⟩
      left_inv := fun v => Subtype.ext (by
        simp only [Subgroup.coe_inv, map_inv, MulAut.inv_apply_self])
      right_inv := fun v => Subtype.ext (by
        simp only [Subgroup.coe_inv, map_inv, MulAut.apply_inv_self])
      map_mul' := fun v w => Subtype.ext (map_mul _ _ _) }
  map_one' := by
    ext v
    simp
  map_mul' x y := by
    ext v
    simp [MulAut.mul_apply]

theorem restrictQ_apply (x : X) (v : Q) : ((hD.restrictQ x v : Q) : A) = ρ x v := rfl

theorem exists_eq_on_Q [Finite A] {F : Subgroup Y} (hFX : F ≤ X) (hRF : R ≤ F)
    (hF : Group.IsNilpotent F) {x : Y} (hx : x ∈ F) : ∃ r ∈ R, ∀ v ∈ Q, ρ x v = ρ r v := by
  set σ := hD.restrictQ with hσ
  set F' : Subgroup (MulAut Q) := (F.subgroupOf X).map σ with hF'
  set R' : Subgroup (MulAut Q) := (R.subgroupOf X).map σ with hR'
  have hR'F' : R' ≤ F' := Subgroup.map_mono fun y hy => hRF hy
  have hF'nil : Group.IsNilpotent F' := by
    have : Group.IsNilpotent (F.subgroupOf X) :=
      Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hFX).symm
    exact Group.nilpotent_of_surjective (σ.subgroupMap _) (σ.subgroupMap_surjective _)
  have hF'R' : F' ≤ Subgroup.normalizer (R' : Set (MulAut Q)) := by
    refine le_trans (Subgroup.map_mono fun f hf => ?_) (Subgroup.le_normalizer_map σ)
    rw [Subgroup.mem_normalizer_iff]
    intro r
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    constructor
    · exact hD.conj_mem f f.2 r
    · intro h
      have h1 := hD.conj_mem _ (X.inv_mem f.2) _ h
      simpa [mul_assoc] using h1
  have hR'cyc : IsCyclic R' := by
    have : IsCyclic R := hD.isCyclic
    have : IsCyclic (R.subgroupOf X) :=
      isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hD.le_X).symm.toMonoidHom
        (Subgroup.subgroupOfEquivOfLe hD.le_X).symm.surjective
    exact isCyclic_of_surjective (σ.subgroupMap _) (σ.subgroupMap_surjective _)
  have hfree' : ∀ r ∈ R', ∀ v : Q, r v = v → v ≠ 1 → r = 1 := by
    rintro _ ⟨r, hr, rfl⟩ v hv hv1
    have h1 : ρ r v = v := congrArg Subtype.val hv
    have h2 := hD.free r hr v v.2 h1 (fun h => hv1 (Subtype.ext h))
    have h3 : r = 1 := Subtype.ext h2
    rw [h3, map_one]
  have htrans' : ∀ u v : Q, u ≠ 1 → v ≠ 1 → ∃ r ∈ R', r u = v := by
    intro u v hu hv
    obtain ⟨r, hr, hrv⟩ := hD.trans u u.2 (fun h => hu (Subtype.ext h)) v v.2
      (fun h => hv (Subtype.ext h))
    exact ⟨σ ⟨r, hD.le_X hr⟩, ⟨⟨r, hD.le_X hr⟩, hr, rfl⟩, Subtype.ext hrv⟩
  have heq := eq_of_isNilpotent_of_regular (hD.isPGroup_two Q) hR'F' hF'nil hF'R' hR'cyc
    hfree' htrans'
  have hxF' : σ ⟨x, hFX hx⟩ ∈ F' := ⟨⟨x, hFX hx⟩, hx, rfl⟩
  rw [heq] at hxF'
  obtain ⟨r, hr, hreq⟩ := hxF'
  refine ⟨r, hr, fun v hv => ?_⟩
  have h1 := congrArg (fun φ : MulAut Q => ((φ ⟨v, hv⟩ : Q) : A)) hreq
  exact h1.symm

theorem commute_of_mem [Finite A] {F : Subgroup Y} (hFX : F ≤ X) (hRF : R ≤ F)
    (hF : Group.IsNilpotent F) {x r : Y} (hx : x ∈ F) (hr : r ∈ R) : x * r = r * x := by
  obtain ⟨r₀, hr₀, hxr₀⟩ := hD.exists_eq_on_Q hFX hRF hF hx
  have hRcomm : r₀ * r = r * r₀ := by
    have : IsCyclic R := hD.isCyclic
    have hc : IsMulCommutative R := IsCyclic.isMulCommutative
    exact congrArg Subtype.val (hc.is_comm.comm ⟨r₀, hr₀⟩ ⟨r, hr⟩)
  apply hD.injective
  ext a
  obtain ⟨w, hw, v, hv, rfl⟩ := hD.exists_mul a
  have hxw : ρ x w ∈ W := hD.map_mem_W x (hFX hx) w hw
  have hrv : ρ r v ∈ Q := hD.map_mem_Q r (hD.le_X hr) v hv
  calc ρ (x * r) (w * v) = ρ x w * ρ (r₀ * r) v := by
        rw [map_mul ρ x r, MulAut.mul_apply, hD.map_mul_of_mem_R hr hw, map_mul (ρ x) w,
          hxr₀ _ hrv, map_mul ρ r₀ r, MulAut.mul_apply]
    _ = ρ x w * ρ (r * r₀) v := by rw [hRcomm]
    _ = ρ (r * x) (w * v) := by
        rw [map_mul ρ r x, MulAut.mul_apply, map_mul (ρ x) w v, hD.map_mul_of_mem_R hr hxw,
          hxr₀ v hv, map_mul ρ r r₀, MulAut.mul_apply]

theorem exists_mem_centralizerQ [Finite A] {F : Subgroup Y} (hFX : F ≤ X) (hRF : R ≤ F)
    (hF : Group.IsNilpotent F) {x : Y} (hx : x ∈ F) :
    ∃ r ∈ R, ∀ v ∈ Q, ρ (r⁻¹ * x) v = v := by
  obtain ⟨r, hr, hxr⟩ := hD.exists_eq_on_Q hFX hRF hF hx
  refine ⟨r, hr, fun v hv => ?_⟩
  rw [map_mul, MulAut.mul_apply, hxr v hv, map_inv, MulAut.inv_apply_self]

end Bender38Action

end CFSG.Walter
