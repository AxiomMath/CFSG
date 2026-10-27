module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.Walter.Huppert

variable {p : ℕ} [hp : Fact p.Prime] {V : Type*} [Group V] [Finite V]

structure Plane (p : ℕ) (V : Type*) [Group V] : Prop where
  comm : ∀ a b : V, a * b = b * a
  pow : ∀ v : V, v ^ p = 1
  card : Nat.card V = p ^ 2

omit hp in
theorem isPGroup_zpowers {G : Type*} [Group G] {σ : G} {k : ℕ} (hσ : σ ^ p ^ k = 1) :
    IsPGroup p (Subgroup.zpowers σ) := by
  rintro ⟨g, z, rfl⟩
  refine ⟨k, Subtype.ext ?_⟩
  change (σ ^ z) ^ p ^ k = 1
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hσ, one_zpow]

omit [Finite V] in
@[expose] def fixedSubgroup (σ : MulAut V) : Subgroup V where
  carrier := {v | σ v = v}
  one_mem' := map_one σ
  mul_mem' := fun {a b} ha hb => by
    change σ (a * b) = a * b
    rw [map_mul, show σ a = a from ha, show σ b = b from hb]
  inv_mem' := fun {a} ha => by
    change σ a⁻¹ = a⁻¹
    rw [map_inv, show σ a = a from ha]

omit [Finite V] in
theorem mem_fixedSubgroup {σ : MulAut V} {v : V} : v ∈ fixedSubgroup σ ↔ σ v = v := Iff.rfl

theorem card_fixedSubgroup_modEq {σ : MulAut V} {k : ℕ} (hσ : σ ^ p ^ k = 1) :
    Nat.card V ≡ Nat.card (fixedSubgroup σ) [MOD p] := by
  have h := (isPGroup_zpowers (p := p) hσ).card_modEq_card_fixedPoints V
  have hset : MulAction.fixedPoints (Subgroup.zpowers σ) V = (fixedSubgroup σ : Set V) := by
    ext v
    rw [MulAction.mem_fixedPoints, SetLike.mem_coe, mem_fixedSubgroup]
    constructor
    · intro hv
      exact hv ⟨σ, Subgroup.mem_zpowers σ⟩
    · rintro hv ⟨g, z, rfl⟩
      change (σ ^ z) • v = v
      have : ∀ n : ℕ, (σ ^ n) v = v := by
        intro n
        induction n with
        | zero => rfl
        | succ n ih => rw [pow_succ, MulAut.mul_apply, hv, ih]
      rcases Int.eq_nat_or_neg z with ⟨n, rfl | rfl⟩
      · rw [zpow_natCast]; exact this n
      · rw [zpow_neg, zpow_natCast, MulAut.smul_def, MulAut.inv_def, MulEquiv.symm_apply_eq]
        exact (this n).symm
  rw [hset] at h
  exact h

theorem eq_one_of_card_dvd {σ : MulAut V} {k : ℕ} (hσ : σ ^ p ^ k = 1)
    (hV : Nat.card V ∣ p) : σ = 1 := by
  have h := card_fixedSubgroup_modEq hσ
  have hle := Subgroup.card_le_of_le (le_top : fixedSubgroup σ ≤ ⊤)
  rw [Subgroup.card_top] at hle
  have htop : fixedSubgroup σ = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rcases (Nat.dvd_prime hp.out).mp hV with h1 | h1
    · have : Nat.card (fixedSubgroup σ) ≠ 0 := Nat.card_pos.ne'
      omega
    · rw [h1] at h hle ⊢
      have h0 : Nat.card (fixedSubgroup σ) % p = 0 := by
        have := h.symm
        rw [Nat.ModEq, Nat.mod_self] at this
        exact this
      have hpos : 0 < Nat.card (fixedSubgroup σ) := Nat.card_pos
      obtain ⟨c, hc⟩ := Nat.dvd_of_mod_eq_zero h0
      rcases c with _ | _ | c
      · omega
      · omega
      · nlinarith [hp.out.two_le]
  ext v
  exact (mem_fixedSubgroup.mp (htop ▸ Subgroup.mem_top v))

namespace Plane

variable (hV : Plane p V)
include hV

omit [Finite V] in
theorem orderOf_eq {v : V} (hv : v ≠ 1) : orderOf v = p := orderOf_eq_prime (hV.pow v) hv

omit [Finite V] in
theorem card_zpowers {v : V} (hv : v ≠ 1) : Nat.card (Subgroup.zpowers v) = p := by
  rw [Nat.card_zpowers, hV.orderOf_eq hv]

omit hp [Finite V] in
theorem pow_mod (v : V) (n : ℕ) : v ^ n = v ^ (n % p) := pow_eq_pow_mod n (hV.pow v)

omit hp [Finite V] in
theorem mul_pow' (a b : V) (n : ℕ) : (a * b) ^ n = a ^ n * b ^ n :=
  (Commute.mul_pow (hV.comm a b) n)

omit [Finite V] in
theorem pow_val_add (e : V) (x y : ZMod p) : e ^ (x + y).val = e ^ x.val * e ^ y.val := by
  rw [ZMod.val_add, ← hV.pow_mod, pow_add]

omit [Finite V] in
theorem pow_val_mul (e : V) (x y : ZMod p) : e ^ (x * y).val = e ^ (x.val * y.val) := by
  rw [ZMod.val_mul, ← hV.pow_mod]

omit [Finite V] in
theorem pow_val_natCast (e : V) (n : ℕ) : e ^ ((n : ZMod p)).val = e ^ n := by
  rw [ZMod.val_natCast, ← hV.pow_mod]

omit [Finite V] hV in
theorem pow_val_one (e : V) : e ^ (1 : ZMod p).val = e := by
  rw [ZMod.val_one, pow_one]

omit [Finite V] in
theorem pow_val_neg (e : V) (x : ZMod p) : e ^ (-x).val = (e ^ x.val)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← hV.pow_val_add, neg_add_cancel, ZMod.val_zero, pow_zero]

omit hp hV in
theorem exists_pow_eq_of_mem_zpowers {e v : V} (h : v ∈ Subgroup.zpowers e) :
    ∃ n : ℕ, e ^ n = v :=
  (Submonoid.mem_powers_iff v e).mp (mem_powers_iff_mem_zpowers.mpr h)

omit [Finite V] in
theorem pow_not_mem_zpowers {e f : V} (hf : f ∉ Subgroup.zpowers e) {j : ℕ} (hj : ¬ p ∣ j) :
    f ^ j ∉ Subgroup.zpowers e := by
  intro hmem
  apply hf
  have hcop : Nat.Coprime j p :=
    Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hj)
  obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.out.one_lt
  have : f = (f ^ j) ^ u := by
    rw [← pow_mul, hV.pow_mod f (j * u), hu, pow_one]
  rw [this]
  exact Subgroup.pow_mem _ hmem u

omit [Finite V] in
theorem dvd_of_mul_eq_one {e f : V} (he : e ≠ 1) (hf : f ∉ Subgroup.zpowers e) {i j : ℕ}
    (h : e ^ i * f ^ j = 1) : p ∣ i ∧ p ∣ j := by
  have hj : p ∣ j := by
    by_contra hj
    apply hV.pow_not_mem_zpowers hf hj
    have : f ^ j = (e ^ i)⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers e) i)
  refine ⟨?_, hj⟩
  obtain ⟨c, rfl⟩ := hj
  rw [pow_mul, hV.pow f, one_pow, mul_one] at h
  rw [← hV.orderOf_eq he]
  exact orderOf_dvd_of_pow_eq_one h

theorem exists_coords {e f : V} (he : e ≠ 1) (hf : f ∉ Subgroup.zpowers e) (v : V) :
    ∃ x y : ZMod p, v = e ^ x.val * f ^ y.val := by
  let φ : ZMod p × ZMod p → V := fun x => e ^ x.1.val * f ^ x.2.val
  have hinj : Function.Injective φ := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ hij
    simp only [φ] at hij
    have h1 : e ^ (i - i').val * f ^ (j - j').val = 1 := by
      rw [sub_eq_add_neg, sub_eq_add_neg, hV.pow_val_add, hV.pow_val_add, hV.pow_val_neg,
        hV.pow_val_neg]
      calc e ^ i.val * (e ^ i'.val)⁻¹ * (f ^ j.val * (f ^ j'.val)⁻¹)
          = (e ^ i.val * f ^ j.val) * (e ^ i'.val * f ^ j'.val)⁻¹ := by
            rw [mul_inv_rev, hV.comm (f ^ j'.val)⁻¹]
            simp only [mul_assoc]
            congr 1
            rw [← mul_assoc, ← mul_assoc, hV.comm (e ^ i'.val)⁻¹]
        _ = 1 := by rw [hij, mul_inv_cancel]
    obtain ⟨hi, hj⟩ := hV.dvd_of_mul_eq_one he hf h1
    have key : ∀ a b : ZMod p, p ∣ (a - b).val → a = b := by
      intro a b hab
      have : (a - b).val = 0 := by
        have hlt := ZMod.val_lt (a - b)
        obtain ⟨c, hc⟩ := hab
        rcases c with _ | c
        · simpa using hc
        · nlinarith
      rw [ZMod.val_eq_zero, sub_eq_zero] at this
      exact this
    rw [key i i' hi, key j j' hj]
  have hbij : Function.Bijective φ := by
    refine hinj.bijective_of_nat_card_le ?_
    rw [hV.card, Nat.card_prod, Nat.card_zmod, sq]
  obtain ⟨⟨i, j⟩, hx⟩ := hbij.2 v
  exact ⟨i, j, hx.symm⟩

theorem mulAut_ext {e f : V} (he : e ≠ 1) (hf : f ∉ Subgroup.zpowers e) {σ τ : MulAut V}
    (h1 : σ e = τ e) (h2 : σ f = τ f) : σ = τ := by
  ext v
  obtain ⟨i, j, rfl⟩ := hV.exists_coords he hf v
  rw [map_mul, map_mul, map_pow, map_pow, map_pow, map_pow, h1, h2]

omit [Finite V] in
theorem exists_not_mem_zpowers (e : V) : ∃ f : V, f ∉ Subgroup.zpowers e := by
  by_contra h
  push Not at h
  have htop : Subgroup.zpowers e = ⊤ := eq_top_iff.mpr fun v _ => h v
  have hcard := congrArg (fun H : Subgroup V => Nat.card H) htop
  simp only [Subgroup.card_top] at hcard
  have hle : Nat.card (Subgroup.zpowers e) ≤ p := by
    by_cases he : e = 1
    · rw [he, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot]; exact hp.out.one_lt.le
    · rw [hV.card_zpowers he]
  rw [hcard, hV.card] at hle
  nlinarith [hp.out.two_le]

omit hp [Finite V] hV in
theorem map_coords (σ : MulAut V) (e f : V) (x y : ZMod p) :
    σ (e ^ x.val * f ^ y.val) = (σ e) ^ x.val * (σ f) ^ y.val := by
  rw [map_mul, map_pow, map_pow]

omit [Finite V] in
theorem coords_of_transvection {e f : V} {σ : MulAut V} {a : ZMod p} (he : σ e = e)
    (hf : σ f = e ^ a.val * f) (x y : ZMod p) :
    σ (e ^ x.val * f ^ y.val) = e ^ (x + a * y).val * f ^ y.val := by
  rw [Plane.map_coords, he, hf, hV.mul_pow', ← pow_mul, hV.pow_val_add, hV.pow_val_mul,
    mul_assoc]

omit [Finite V] in
theorem coords_of_transvection' {e f : V} {σ : MulAut V} {b : ZMod p} (hf : σ f = f)
    (he : σ e = e * f ^ b.val) (x y : ZMod p) :
    σ (e ^ x.val * f ^ y.val) = e ^ x.val * f ^ (y + b * x).val := by
  rw [Plane.map_coords, he, hf, hV.mul_pow', ← pow_mul, hV.pow_val_add, hV.pow_val_mul,
    mul_assoc, hV.comm (f ^ (b.val * x.val)), mul_comm b.val x.val]

theorem exists_axis {σ : MulAut V} {k : ℕ} (hσ : σ ^ p ^ k = 1) (hσ1 : σ ≠ 1) :
    ∃ e : V, e ≠ 1 ∧ σ e = e ∧ ∀ v, ∃ n : ℕ, v⁻¹ * σ v = e ^ n := by
  have hF : Nat.card (fixedSubgroup σ) = p := by
    have hmod := card_fixedSubgroup_modEq hσ
    rw [hV.card] at hmod
    have hdvd : Nat.card (fixedSubgroup σ) ∣ p ^ 2 := hV.card ▸ Subgroup.card_subgroup_dvd_card _
    obtain ⟨m, hm, hmeq⟩ := (Nat.dvd_prime_pow hp.out).mp hdvd
    have hne : Nat.card (fixedSubgroup σ) ≠ p ^ 2 := by
      intro hc
      apply hσ1
      have htop := Subgroup.eq_top_of_card_eq _ (hc.trans hV.card.symm)
      ext v
      exact mem_fixedSubgroup.mp (htop ▸ Subgroup.mem_top v)
    interval_cases m
    · exfalso
      rw [hmeq, pow_zero] at hmod
      have := Nat.ModEq.symm hmod
      rw [Nat.ModEq, Nat.one_mod_eq_one.mpr hp.out.one_lt.ne', sq, Nat.mul_mod_left] at this
      exact absurd this (by norm_num)
    · rw [hmeq, pow_one]
    · exact absurd hmeq hne
  have : Nontrivial (fixedSubgroup σ) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hF]; exact hp.out.one_lt
  obtain ⟨⟨e, heF⟩, he1⟩ := exists_ne (1 : fixedSubgroup σ)
  have he : e ≠ 1 := fun h => he1 (Subtype.ext h)
  have hσe : σ e = e := heF
  obtain ⟨f, hf⟩ := hV.exists_not_mem_zpowers e
  obtain ⟨i, j, hfij⟩ := hV.exists_coords he hf (σ f)
  have hiter : ∀ n : ℕ, ∃ c : ZMod p, (σ ^ n) f = e ^ c.val * f ^ (j ^ n).val := by
    intro n
    induction n with
    | zero =>
      refine ⟨0, ?_⟩
      simp only [pow_zero, ZMod.val_zero, one_mul, MulAut.one_apply, ZMod.val_one, pow_one]
    | succ n ih =>
      obtain ⟨c, hc⟩ := ih
      refine ⟨c + i * j ^ n, ?_⟩
      rw [pow_succ', MulAut.mul_apply, hc, Plane.map_coords, hσe, hfij, hV.mul_pow', ← pow_mul,
        ← pow_mul, ← hV.pow_val_mul, ← hV.pow_val_mul, ← mul_assoc, hV.pow_val_add, pow_succ',
        mul_comm i]
  obtain ⟨c, hc⟩ := hiter (p ^ k)
  rw [hσ, MulAut.one_apply, ZMod.pow_card_pow] at hc
  have hj1 : j = 1 := by
    have h1 : e ^ c.val * f ^ (j - 1).val = 1 := by
      rw [sub_eq_add_neg, hV.pow_val_add, hV.pow_val_neg, Plane.pow_val_one, ← mul_assoc, ← hc,
        mul_inv_cancel]
    obtain ⟨-, hdvd⟩ := hV.dvd_of_mul_eq_one he hf h1
    have hlt := ZMod.val_lt (j - 1)
    obtain ⟨d, hd⟩ := hdvd
    have h0 : (j - 1).val = 0 := by
      rcases d with _ | d
      · simpa using hd
      · nlinarith
    rw [ZMod.val_eq_zero, sub_eq_zero] at h0
    exact h0
  rw [hj1, Plane.pow_val_one] at hfij
  refine ⟨e, he, hσe, fun v => ?_⟩
  obtain ⟨a, b, rfl⟩ := hV.exists_coords he hf v
  refine ⟨(i * b).val, ?_⟩
  rw [hV.coords_of_transvection hσe hfij, hV.pow_val_add, mul_inv_rev]
  calc (f ^ b.val)⁻¹ * (e ^ a.val)⁻¹ * (e ^ a.val * e ^ (i * b).val * f ^ b.val)
      = (f ^ b.val)⁻¹ * (e ^ (i * b).val * f ^ b.val) := by group
    _ = e ^ (i * b).val := by rw [hV.comm (e ^ (i * b).val), inv_mul_cancel_left]

theorem mem_zpowers_of_axis {e : V} (he : e ≠ 1) {σ₁ σ₂ : MulAut V} (hσ₁ : σ₁ ≠ 1)
    (h₁e : σ₁ e = e) (h₁ : ∀ v, ∃ n : ℕ, v⁻¹ * σ₁ v = e ^ n)
    (h₂e : σ₂ e = e) (h₂ : ∀ v, ∃ n : ℕ, v⁻¹ * σ₂ v = e ^ n) :
    σ₂ ∈ Subgroup.zpowers σ₁ := by
  obtain ⟨f, hf⟩ := hV.exists_not_mem_zpowers e
  obtain ⟨a, ha⟩ := h₁ f
  obtain ⟨b, hb⟩ := h₂ f
  set α : ZMod p := (a : ZMod p)
  set β : ZMod p := (b : ZMod p)
  have ha' : σ₁ f = e ^ α.val * f := by
    rw [hV.pow_val_natCast, ← ha, hV.comm, mul_inv_cancel_left]
  have hb' : σ₂ f = e ^ β.val * f := by
    rw [hV.pow_val_natCast, ← hb, hV.comm, mul_inv_cancel_left]
  have hα : α ≠ 0 := by
    intro h0
    apply hσ₁
    refine hV.mulAut_ext he hf (h₁e.trans rfl) ?_
    rw [ha', h0, ZMod.val_zero, pow_zero, one_mul]; rfl
  have hiter : ∀ n : ℕ, ∀ x y : ZMod p,
      (σ₁ ^ n) (e ^ x.val * f ^ y.val) = e ^ (x + n * α * y).val * f ^ y.val := by
    intro n
    induction n with
    | zero => intro x y; simp
    | succ n ih =>
      intro x y
      rw [pow_succ', MulAut.mul_apply, ih, hV.coords_of_transvection h₁e ha']
      congr 3
      push_cast
      ring
  refine ⟨((β * α⁻¹).val : ℤ), ?_⟩
  change σ₁ ^ (((β * α⁻¹).val : ℕ) : ℤ) = σ₂
  rw [zpow_natCast]
  ext v
  obtain ⟨x, y, rfl⟩ := hV.exists_coords he hf v
  rw [hiter, hV.coords_of_transvection h₂e hb', ZMod.natCast_zmod_val, mul_assoc β,
    inv_mul_cancel₀ hα, mul_one]

theorem exists_inv_of_axes {e₁ e₂ : V} (he₁ : e₁ ≠ 1) (he₂ : e₂ ∉ Subgroup.zpowers e₁)
    {σ₁ σ₂ : MulAut V} (hσ₁ : σ₁ ≠ 1) (hσ₂ : σ₂ ≠ 1)
    (h₁e : σ₁ e₁ = e₁) (h₁ : ∀ v, ∃ n : ℕ, v⁻¹ * σ₁ v = e₁ ^ n)
    (h₂e : σ₂ e₂ = e₂) (h₂ : ∀ v, ∃ n : ℕ, v⁻¹ * σ₂ v = e₂ ^ n) :
    ∃ k : ℕ, ∀ v, ((σ₁ * σ₂ ^ k * σ₁) ^ 2) v = v⁻¹ := by
  have he₂1 : e₂ ≠ 1 := fun h => he₂ (h ▸ Subgroup.one_mem _)
  obtain ⟨a, ha⟩ := h₁ e₂
  obtain ⟨b, hb⟩ := h₂ e₁
  set α : ZMod p := (a : ZMod p)
  set β : ZMod p := (b : ZMod p)
  have ha' : σ₁ e₂ = e₁ ^ α.val * e₂ := by
    rw [hV.pow_val_natCast, ← ha, hV.comm, mul_inv_cancel_left]
  have hb' : σ₂ e₁ = e₁ * e₂ ^ β.val := by
    rw [hV.pow_val_natCast, ← hb, mul_inv_cancel_left]
  have h₂e' : σ₂ (e₂ ^ (1 : ZMod p).val) = e₂ ^ (1 : ZMod p).val := by
    rw [Plane.pow_val_one, h₂e]
  have hα : α ≠ 0 := by
    intro h0
    apply hσ₁
    refine hV.mulAut_ext he₁ he₂ (h₁e.trans rfl) ?_
    rw [ha', h0, ZMod.val_zero, pow_zero, one_mul]; rfl
  have hβ : β ≠ 0 := by
    intro h0
    apply hσ₂
    have hσ₂e₁ : σ₂ e₁ = e₁ := by rw [hb', h0, ZMod.val_zero, pow_zero, mul_one]
    exact hV.mulAut_ext he₁ he₂ (hσ₂e₁.trans rfl) (h₂e.trans rfl)
  have hiter : ∀ n : ℕ, ∀ x y : ZMod p,
      (σ₂ ^ n) (e₁ ^ x.val * e₂ ^ y.val) = e₁ ^ x.val * e₂ ^ (y + n * β * x).val := by
    intro n
    induction n with
    | zero => intro x y; simp
    | succ n ih =>
      intro x y
      rw [pow_succ', MulAut.mul_apply, ih, hV.coords_of_transvection' h₂e hb']
      congr 3
      push_cast
      ring
  set k : ℕ := (-(α * β)⁻¹).val with hkdef
  have hk : (k : ZMod p) * α * β = -1 := by
    rw [hkdef, ZMod.natCast_val, ZMod.cast_id', id, mul_assoc, neg_mul,
      inv_mul_cancel₀ (mul_ne_zero hα hβ)]
  have hω : ∀ x y : ZMod p, (σ₁ * σ₂ ^ k * σ₁) (e₁ ^ x.val * e₂ ^ y.val) =
      e₁ ^ (α * y).val * e₂ ^ (k * β * x).val := by
    intro x y
    rw [MulAut.mul_apply, MulAut.mul_apply, hV.coords_of_transvection h₁e ha', hiter,
      hV.coords_of_transvection h₁e ha']
    congr 3
    · linear_combination (x + α * y) * hk
    · linear_combination y * hk
  refine ⟨k, fun v => ?_⟩
  obtain ⟨x, y, rfl⟩ := hV.exists_coords he₁ he₂ v
  rw [pow_two, MulAut.mul_apply, hω, hω, mul_inv_rev, hV.comm (e₂ ^ y.val)⁻¹, ← hV.pow_val_neg,
    ← hV.pow_val_neg]
  congr 3
  · linear_combination x * hk
  · linear_combination y * hk

theorem exists_inv_of_not_mem_zpowers {u₁ u₂ : MulAut V} {k₁ k₂ : ℕ} (h₁ : u₁ ^ p ^ k₁ = 1)
    (h₂ : u₂ ^ p ^ k₂ = 1) (hu₁ : u₁ ≠ 1) (hu₂ : u₂ ∉ Subgroup.zpowers u₁) :
    ∃ k : ℕ, ∀ v, ((u₁ * u₂ ^ k * u₁) ^ 2) v = v⁻¹ := by
  have hu₂1 : u₂ ≠ 1 := fun h => hu₂ (h ▸ Subgroup.one_mem _)
  obtain ⟨e₁, he₁, h₁e, h₁a⟩ := hV.exists_axis h₁ hu₁
  obtain ⟨e₂, he₂, h₂e, h₂a⟩ := hV.exists_axis h₂ hu₂1
  by_cases hmem : e₂ ∈ Subgroup.zpowers e₁
  · exfalso
    apply hu₂
    obtain ⟨n, hn⟩ := Plane.exists_pow_eq_of_mem_zpowers hmem
    have hpn : ¬ p ∣ n := by
      rintro ⟨c, rfl⟩
      rw [pow_mul, hV.pow, one_pow] at hn
      exact he₂ hn.symm
    have hcop : Nat.Coprime n p :=
      Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hpn)
    obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.out.one_lt
    have he₁e₂ : e₁ = e₂ ^ u := by
      rw [← hn, ← pow_mul, hV.pow_mod e₁ (n * u), hu, pow_one]
    refine hV.mem_zpowers_of_axis he₁ hu₁ h₁e h₁a ?_ ?_
    · rw [he₁e₂, map_pow, h₂e]
    · intro v
      obtain ⟨m, hm⟩ := h₂a v
      exact ⟨n * m, by rw [hm, pow_mul, hn]⟩
  · exact hV.exists_inv_of_axes he₁ hmem hu₁ hu₂1 h₁e h₁a h₂e h₂a

end Plane

end CFSG.Walter.Huppert
