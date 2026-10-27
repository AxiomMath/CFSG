module

public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.Quasithin.E6.Bar

open Subgroup

variable {Y : Type} [Group Y] (L : Subgroup Y)

abbrev Qbar : Type := ↥L ⧸ Subgroup.center ↥L

@[expose] def conjL (r : ↥(normalizer (L : Set Y))) : MulAut ↥L where
  toFun x := ⟨(r : Y) * x * (r : Y)⁻¹, (mem_normalizer_iff.1 r.2 x).1 x.2⟩
  invFun x := ⟨(r : Y)⁻¹ * x * (r : Y), by
    simpa using (mem_normalizer_iff.1 (inv_mem r.2) x).1 x.2⟩
  left_inv x := by ext; simp [mul_assoc]
  right_inv x := by ext; simp [mul_assoc]
  map_mul' a b := by ext; simp [mul_assoc]

variable {L}

theorem conjL_apply (r : ↥(normalizer (L : Set Y))) (x : ↥L) :
    ((conjL L r x : ↥L) : Y) = (r : Y) * x * (r : Y)⁻¹ := rfl

theorem conjL_one : conjL L (1 : ↥(normalizer (L : Set Y))) = 1 := by
  ext x
  simp [conjL_apply]

theorem conjL_mul (r s : ↥(normalizer (L : Set Y))) :
    conjL L (r * s) = conjL L r * conjL L s := by
  ext x
  simp [conjL_apply, mul_assoc]

@[expose] def conjHom (L : Subgroup Y) : ↥(normalizer (L : Set Y)) →* MulAut ↥L where
  toFun := conjL L
  map_one' := conjL_one
  map_mul' := conjL_mul

theorem conjL_map_center (r : ↥(normalizer (L : Set Y))) :
    (Subgroup.center ↥L).map (conjL L r).toMonoidHom = Subgroup.center ↥L :=
  Subgroup.map_center_eq (conjL L r)

@[expose] noncomputable def barAut (r : ↥(normalizer (L : Set Y))) : MulAut (Qbar L) :=
  QuotientGroup.congr (Subgroup.center ↥L) (Subgroup.center ↥L) (conjL L r) (conjL_map_center r)

theorem barAut_mk (r : ↥(normalizer (L : Set Y))) (x : ↥L) :
    barAut r (QuotientGroup.mk x : Qbar L) = QuotientGroup.mk (conjL L r x) :=
  QuotientGroup.congr_mk _ _ _ _ x

theorem barAut_mul (r s : ↥(normalizer (L : Set Y))) : barAut (r * s) = barAut r * barAut s := by
  refine MulEquiv.ext fun q => ?_
  induction q using QuotientGroup.induction_on with
  | H x =>
    change barAut (r * s) (QuotientGroup.mk x) = barAut r (barAut s (QuotientGroup.mk x))
    rw [barAut_mk, barAut_mk, barAut_mk, conjL_mul]
    rfl

theorem barAut_one : barAut (1 : ↥(normalizer (L : Set Y))) = 1 := by
  refine MulEquiv.ext fun q => ?_
  induction q using QuotientGroup.induction_on with
  | H x =>
    change barAut 1 (QuotientGroup.mk x) = QuotientGroup.mk x
    rw [barAut_mk, conjL_one]
    rfl

@[expose] noncomputable def barHom (L : Subgroup Y) :
    ↥(normalizer (L : Set Y)) →* MulAut (Qbar L) where
  toFun := barAut
  map_one' := barAut_one
  map_mul' := barAut_mul

theorem barHom_mk (r : ↥(normalizer (L : Set Y))) (x y : ↥L)
    (h : (y : Y) = (r : Y) * x * (r : Y)⁻¹) :
    barHom L r (QuotientGroup.mk x : Qbar L) = QuotientGroup.mk y := by
  have : conjL L r x = y := Subtype.ext h.symm
  change barAut r (QuotientGroup.mk x) = _
  rw [barAut_mk, this]

theorem barHom_of_mem (x : ↥L) :
    barHom L ⟨(x : Y), Subgroup.le_normalizer x.2⟩ = MulAut.conj (QuotientGroup.mk x : Qbar L) := by
  refine MulEquiv.ext fun q => ?_
  induction q using QuotientGroup.induction_on with
  | H y =>
    rw [MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact barHom_mk _ y (x * y * x⁻¹) (by simp)

theorem barHom_mk_of_comm (r : ↥(normalizer (L : Set Y))) (x : ↥L)
    (h : (r : Y) * x = x * r) : barHom L r (QuotientGroup.mk x : Qbar L) = QuotientGroup.mk x :=
  barHom_mk r x x (by rw [h]; group)

theorem barHom_eq_one_iff (hperf : Group.IsPerfect ↥L) (r : ↥(normalizer (L : Set Y))) :
    barHom L r = 1 ↔ ∀ x : ↥L, (r : Y) * x = x * r := by
  constructor
  · intro h x
    have hc : ∀ x : ↥L, x⁻¹ * conjL L r x ∈ Subgroup.center ↥L := by
      intro x
      have := congrArg (fun φ : MulAut (Qbar L) => φ (QuotientGroup.mk x)) h
      have h2 : barAut r (QuotientGroup.mk x : Qbar L) = QuotientGroup.mk x := this
      rw [barAut_mk] at h2
      exact QuotientGroup.eq.1 h2.symm
    let f : ↥L →* ↥(Subgroup.center ↥L) :=
      { toFun := fun x => ⟨x⁻¹ * conjL L r x, hc x⟩
        map_one' := by ext; simp
        map_mul' := fun a b => by
          have hz := Subgroup.mem_center_iff.1 (hc a) (b⁻¹)
          apply Subtype.ext
          change (a * b)⁻¹ * conjL L r (a * b) = (a⁻¹ * conjL L r a) * (b⁻¹ * conjL L r b)
          rw [map_mul]
          calc (a * b)⁻¹ * (conjL L r a * conjL L r b)
              = b⁻¹ * (a⁻¹ * conjL L r a) * conjL L r b := by group
            _ = (a⁻¹ * conjL L r a) * b⁻¹ * conjL L r b := by rw [hz]
            _ = (a⁻¹ * conjL L r a) * (b⁻¹ * conjL L r b) := by group }
    have hker : commutator ↥L ≤ f.ker := Abelianization.commutator_subset_ker f
    rw [Group.isPerfect_def.1 hperf] at hker
    have h1 : f x = 1 := MonoidHom.mem_ker.1 (hker (Subgroup.mem_top x))
    have h2 : x⁻¹ * conjL L r x = 1 := congrArg Subtype.val h1
    have h3 : conjL L r x = x := (inv_mul_eq_one.1 h2).symm
    have h4 := congrArg Subtype.val h3
    rw [conjL_apply] at h4
    exact mul_inv_eq_iff_eq_mul.1 h4
  · intro h
    refine MulEquiv.ext fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H x => exact barHom_mk_of_comm r x (h x)

theorem exists_fixed_of_involutive {α : Type} [Finite α] (hodd : Odd (Nat.card α)) (t : α → α)
    (ht : Function.Involutive t) : ∃ a, t a = a := by
  classical
  have := Fintype.ofFinite α
  let f : Function.End α := t
  have hsq : f ^ 2 ^ 1 = 1 := by
    funext a
    change t (t a) = a
    exact ht a
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 2) (n := 1) hsq
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at hmod
  by_contra hno
  push Not at hno
  have : Nat.card ↑(Function.fixedPoints f) = 0 := by
    rw [Nat.card_eq_zero]
    left
    exact ⟨fun ⟨a, ha⟩ => hno a ha⟩
  rw [this] at hmod
  obtain ⟨k, hk⟩ := hodd
  unfold Nat.ModEq at hmod
  omega

theorem exists_fixed_lift [Finite Y] (hodd : Odd (Nat.card ↥(Subgroup.center ↥L)))
    (a : ↥(normalizer (L : Set Y))) (ha : (a : Y) ^ 2 = 1) (q : Qbar L)
    (hq : barHom L a q = q) :
    ∃ x : ↥L, conjL L a x = x ∧ (QuotientGroup.mk x : Qbar L) = q := by
  obtain ⟨x₀, rfl⟩ := QuotientGroup.mk_surjective q
  have hmk : (QuotientGroup.mk (conjL L a x₀) : Qbar L) = QuotientGroup.mk x₀ := by
    have h : barAut a (QuotientGroup.mk x₀ : Qbar L) = QuotientGroup.mk x₀ := hq
    rwa [barAut_mk] at h
  have hz₀ : x₀⁻¹ * conjL L a x₀ ∈ Subgroup.center ↥L := QuotientGroup.eq.1 hmk.symm
  have hc2 : ∀ x : ↥L, conjL L a (conjL L a x) = x := by
    intro x
    have haa : a * a = 1 := Subtype.ext (by simpa [pow_two] using ha)
    have : conjL L a * conjL L a = 1 := by rw [← conjL_mul, haa, conjL_one]
    exact congrArg (fun φ : MulAut ↥L => φ x) this
  have hcZ : ∀ z : ↥(Subgroup.center ↥L), conjL L a z ∈ Subgroup.center ↥L := fun z => by
    have h := Subgroup.mem_map_of_mem (conjL L a).toMonoidHom z.2
    rw [conjL_map_center] at h
    exact h
  set z₀ : ↥L := x₀⁻¹ * conjL L a x₀ with hz₀def
  have hcx : conjL L a x₀ = x₀ * z₀ := by rw [hz₀def, mul_inv_cancel_left]
  have hz₀c : z₀ * conjL L a z₀ = 1 := by
    have h1 : conjL L a (conjL L a x₀) = x₀ := hc2 x₀
    rw [hcx, map_mul, hcx] at h1
    have h2 : x₀ * (z₀ * conjL L a z₀) = x₀ * 1 := by rw [mul_one, ← mul_assoc]; exact h1
    exact mul_left_cancel h2
  have hz₀ct : z₀ * conjL L a z₀ ∈ Subgroup.center ↥L := hz₀c ▸ one_mem _
  let t : ↥(Subgroup.center ↥L) → ↥(Subgroup.center ↥L) := fun z =>
    ⟨z₀ * conjL L a z, mul_mem hz₀ (hcZ z)⟩
  have ht : Function.Involutive t := by
    intro z
    apply Subtype.ext
    change z₀ * conjL L a (z₀ * conjL L a z) = z
    rw [map_mul, hc2 z, ← mul_assoc, hz₀c, one_mul]
  obtain ⟨z, hz⟩ := exists_fixed_of_involutive hodd t ht
  have hzt : z₀ * conjL L a z = z := congrArg Subtype.val hz
  refine ⟨x₀ * z, ?_, ?_⟩
  · rw [map_mul, hcx, mul_assoc, hzt]
  · rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff (z : ↥L)).2 z.2, mul_one]

theorem map_mk_card [Finite Y] (hodd : Odd (Nat.card ↥(Subgroup.center ↥L))) (P : Subgroup ↥L)
    (hP : IsPGroup 2 P) :
    Nat.card ↥(P.map (QuotientGroup.mk' (Subgroup.center ↥L))) = Nat.card P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinj : Function.Injective ((QuotientGroup.mk' (Subgroup.center ↥L)).domRestrict P) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxZ : (x : ↥L) ∈ Subgroup.center ↥L := (QuotientGroup.eq_one_iff _).1 hx
    obtain ⟨k, hk⟩ := hP x
    have hdvd : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    have hord : orderOf (x : ↥L) ∣ Nat.card ↥(Subgroup.center ↥L) :=
      Subgroup.orderOf_dvd_natCard (Subgroup.center ↥L) hxZ
    have hxo : orderOf (x : ↥L) = orderOf x := Subgroup.orderOf_coe x
    rw [hxo] at hord
    have hcop : Nat.Coprime (2 ^ k) (Nat.card ↥(Subgroup.center ↥L)) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd)
    have h1 : orderOf x = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hdvd hcop) hord
    exact orderOf_eq_one_iff.1 h1
  have hrange : P.map (QuotientGroup.mk' (Subgroup.center ↥L)) =
      ((QuotientGroup.mk' (Subgroup.center ↥L)).domRestrict P).range := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨⟨x, hx⟩, rfl⟩
      exact ⟨x, hx, rfl⟩
  rw [hrange]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

@[expose] def fixedSub {Q : Type} [Group Q] (α : MulAut Q) : Subgroup Q where
  carrier := {q | α q = q}
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_ofPred_eq] at *
    rw [map_mul, ha, hb]
  one_mem' := map_one α
  inv_mem' := fun {a} ha => by
    simp only [Set.mem_ofPred_eq] at *
    rw [map_inv, ha]

theorem mem_fixedSub {Q : Type} [Group Q] (α : MulAut Q) (q : Q) :
    q ∈ fixedSub α ↔ α q = q := Iff.rfl

end CFSG.Quasithin.E6.Bar
