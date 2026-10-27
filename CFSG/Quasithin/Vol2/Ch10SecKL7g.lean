module

public import CFSG.Quasithin.Vol2.Ch10SecKL7d

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.KL7

open CFSG.Quasithin CFSG.Assembly.LowTwoRank

section TwoResidual

variable {G : Type*} [Group G]

theorem mem_zpowers_pow_of_coprime (x : G) {n : ℕ} (h : n.Coprime (orderOf x)) :
    x ∈ Subgroup.zpowers (x ^ n) := by
  have hb := Nat.gcd_eq_gcd_ab n (orderOf x)
  rw [Nat.Coprime.gcd_eq_one h, Nat.cast_one] at hb
  refine ⟨Nat.gcdA n (orderOf x), ?_⟩
  calc (x ^ n) ^ Nat.gcdA n (orderOf x) = x ^ ((n : ℤ) * Nat.gcdA n (orderOf x)) := by
        rw [← zpow_natCast, ← zpow_mul]
    _ = x ^ ((n : ℤ) * Nat.gcdA n (orderOf x) + (orderOf x : ℤ) * Nat.gcdB n (orderOf x)) := by
        rw [zpow_add, zpow_mul x (orderOf x), zpow_natCast, pow_orderOf_eq_one, one_zpow, mul_one]
    _ = x := by rw [← hb, zpow_one]

theorem twoResidual_le (H : Subgroup G) : twoResidual H ≤ H :=
  iInf₂_le H ⟨le_rfl, Subgroup.le_normalizer, fun x hx => ⟨0, by simpa using hx⟩⟩

theorem mem_twoResidual_of_odd {H : Subgroup G} {x : G} (hx : x ∈ H) (hodd : Odd (orderOf x)) :
    x ∈ twoResidual H := by
  rw [twoResidual, Subgroup.mem_iInf]
  intro N
  rw [Subgroup.mem_iInf]
  rintro ⟨-, -, hN⟩
  obtain ⟨k, hk⟩ := hN x hx
  have hcop : (2 ^ k).Coprime (orderOf x) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd)
  exact (Subgroup.zpowers_le.2 hk) (mem_zpowers_pow_of_coprime x hcop)

theorem mem_map_conj_iff' {g y : G} {N : Subgroup G} :
    y ∈ N.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * y * g ∈ N := by
  constructor
  · rintro ⟨l, hl, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hl
  · intro hy
    refine ⟨g⁻¹ * y * g, hy, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

theorem conj_mem_twoResidual {H : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (H : Set G))
    {r : G} (hr : r ∈ twoResidual H) : g * r * g⁻¹ ∈ twoResidual H := by
  have hg' : g⁻¹ ∈ Subgroup.normalizer (H : Set G) := inv_mem hg
  rw [twoResidual, Subgroup.mem_iInf] at hr ⊢
  intro N
  rw [Subgroup.mem_iInf]
  rintro ⟨hNH, hHN, hN⟩
  have hmem := hr (N.map (MulAut.conj g⁻¹).toMonoidHom)
  rw [Subgroup.mem_iInf] at hmem
  have hr' := hmem ⟨?_, ?_, ?_⟩
  · rw [mem_map_conj_iff', inv_inv] at hr'
    exact hr'
  · intro y hy
    rw [mem_map_conj_iff', inv_inv] at hy
    have := (Subgroup.mem_normalizer_iff.1 hg' _).1 (hNH hy)
    simpa [mul_assoc] using this
  · intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [mem_map_conj_iff', mem_map_conj_iff', inv_inv]
    have hgh : g * h * g⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.1 hg h).1 hh
    rw [Subgroup.mem_normalizer_iff.1 (hHN hgh) (g * y * g⁻¹)]
    constructor <;> intro hm <;> simpa [mul_assoc] using hm
  · intro x hx
    have hgx : g * x * g⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.1 hg x).1 hx
    obtain ⟨k, hk⟩ := hN _ hgx
    refine ⟨k, ?_⟩
    rw [mem_map_conj_iff', inv_inv]
    rw [conj_pow] at hk
    exact hk

end TwoResidual

variable {W : Type} [CommGroup W]

theorem card_modEq_fixV {p k : ℕ} [hp : Fact p.Prime] (y : MulAut W) (hy : y ^ p ^ k = 1)
    (V : Subgroup W) [Finite V] (hV : ∀ v ∈ V, y v ∈ V) :
    Nat.card V ≡ Nat.card ↥(V ⊓ fixV (Subgroup.zpowers y)) [MOD p] := by
  have hpow : ∀ n : ℕ, ∀ v ∈ V, (y ^ n) v ∈ V := by
    intro n
    induction n with
    | zero => intro v hv; simpa using hv
    | succ n ih => intro v hv; rw [pow_succ, MulAut.mul_apply]; exact ih _ (hV v hv)
  let S : Subgroup (MulAut W) :=
    { carrier := {g | ∀ v, g v ∈ V ↔ v ∈ V}
      one_mem' := fun v => Iff.rfl
      mul_mem' := fun {a b} ha hb v => by rw [MulAut.mul_apply, ha, hb]
      inv_mem' := fun {a} ha v => by rw [← ha, MulAut.apply_inv_self] }
  have hyS : y ∈ S := fun v => ⟨fun h => by
    have hinv : y⁻¹ = y ^ (p ^ k - 1) := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, Nat.sub_add_cancel
        (Nat.one_le_pow _ _ hp.out.pos), hy]
    have := hpow (p ^ k - 1) _ h
    rwa [← hinv, MulAut.inv_apply_self] at this, hV v⟩
  have hZS : Subgroup.zpowers y ≤ S := Subgroup.zpowers_le.2 hyS
  let act : MulAction ↥(Subgroup.zpowers y) ↥V :=
    { smul := fun g v => ⟨(g : MulAut W) v, (hZS g.2 v).2 v.2⟩
      one_smul := fun v => Subtype.ext rfl
      mul_smul := fun g h v => Subtype.ext rfl }
  have hP : IsPGroup p ↥(Subgroup.zpowers y) := fun g => ⟨k, by
    obtain ⟨z, hz⟩ := g.2
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hz, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy,
      one_zpow]
    rfl⟩
  have h1 := hP.card_modEq_card_fixedPoints (α := ↥V)
  have h2 : Nat.card ↥(MulAction.fixedPoints ↥(Subgroup.zpowers y) ↥V) =
      Nat.card ↥(V ⊓ fixV (Subgroup.zpowers y)) := Nat.card_congr
    { toFun := fun v => ⟨(v : ↥V), (v : ↥V).2, mem_fixV_zp.2 (congrArg Subtype.val
        ((MulAction.mem_fixedPoints.1 v.2) ⟨y, Subgroup.mem_zpowers y⟩))⟩
      invFun := fun v => ⟨⟨v, v.2.1⟩, MulAction.mem_fixedPoints.2 fun g => Subtype.ext
        (v.2.2 g g.2)⟩
      left_inv := fun v => rfl
      right_inv := fun v => rfl }
  rwa [h2] at h1

theorem fixV_conj (g x : MulAut W) :
    fixV (Subgroup.zpowers (g * x * g⁻¹)) = (fixV (Subgroup.zpowers x)).map g.toMonoidHom :=
  CFSG.Quasithin.fixV_zpowers_conj g x

theorem rkIdx_fixV_inv (x : MulAut W) :
    rkIdx (fixV (Subgroup.zpowers x⁻¹)) = rkIdx (fixV (Subgroup.zpowers x)) := by
  rw [Subgroup.zpowers_inv]

theorem rkIdx_fixV_conj (g x : MulAut W) :
    rkIdx (fixV (Subgroup.zpowers (g * x * g⁻¹))) = rkIdx (fixV (Subgroup.zpowers x)) := by
  rw [fixV_conj, rkIdx, rkIdx, MulEquiv.toMonoidHom_eq_coe, Subgroup.index_map_equiv]

section Card24

variable (hW : Nat.card W = 2 ^ 24)
include hW

theorem index_eq_two_pow (X : Subgroup W) : X.index = 2 ^ rkIdx X := by
  have hd : X.index ∣ 2 ^ 24 := hW ▸ X.index_dvd_card
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
  rw [rkIdx, hm, padicValNat.prime_pow]

theorem card_mul_two_pow (X : Subgroup W) : Nat.card X * 2 ^ rkIdx X = 2 ^ 24 := by
  rw [← index_eq_two_pow hW, Subgroup.card_mul_index, hW]

theorem rkIdx_anti {X Y : Subgroup W} (h : X ≤ Y) : rkIdx Y ≤ rkIdx X := by
  have hd := Subgroup.index_dvd_of_le h
  rw [index_eq_two_pow hW, index_eq_two_pow hW] at hd
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 hd

theorem rkIdx_inf_le (X Y : Subgroup W) : rkIdx (X ⊓ Y) ≤ rkIdx X + rkIdx Y := by
  have h := Subgroup.index_inf_le (H := X) (K := Y)
  rw [index_eq_two_pow hW, index_eq_two_pow hW, index_eq_two_pow hW, ← pow_add] at h
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h

theorem rkIdx_fixV_mul_le (a b : MulAut W) :
    rkIdx (fixV (Subgroup.zpowers (a * b))) ≤
      rkIdx (fixV (Subgroup.zpowers a)) + rkIdx (fixV (Subgroup.zpowers b)) := by
  refine (rkIdx_anti hW ?_).trans (rkIdx_inf_le hW _ _)
  intro w hw
  obtain ⟨ha, hb⟩ := Subgroup.mem_inf.1 hw
  rw [mem_fixV_zp] at ha hb
  rw [mem_fixV_zp, MulAut.mul_apply, hb, ha]

theorem rkIdx_fixV_pow_le (x : MulAut W) (n : ℕ) :
    rkIdx (fixV (Subgroup.zpowers (x ^ n))) ≤ rkIdx (fixV (Subgroup.zpowers x)) := by
  refine rkIdx_anti hW fun w hw => ?_
  rw [mem_fixV_zp] at hw ⊢
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, MulAut.mul_apply, hw, ih]

end Card24

namespace Hyp

variable {Mb L₁ L₂ : Subgroup (MulAut W)} {W₁ W₂ : Subgroup W} {τ : MulAut W}
variable (h : Hyp Mb L₁ L₂ W₁ W₂ τ)
include h

theorem le_rkIdx_of_inf {X : Subgroup W} (hX : X ⊓ W₁ = ⊥) : 12 ≤ rkIdx X := by
  have : Finite W := h.finite_W
  have hinj : Function.Injective ((QuotientGroup.mk' W₁).comp X.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx1 : (x : W) ∈ W₁ := (QuotientGroup.eq_one_iff _).1 hx
    have hx2 : (x : W) ∈ X ⊓ W₁ := ⟨x.2, hx1⟩
    rw [hX, Subgroup.mem_bot] at hx2
    exact Subtype.ext hx2
  have hle := Nat.card_le_card_of_injective _ hinj
  rw [← Subgroup.index_eq_card] at hle
  have hidx : W₁.index = 2 ^ 12 := by
    have := Subgroup.card_mul_index W₁
    rw [h.card_W₁, h.card_W] at this
    have h12 : 2 ^ 12 * W₁.index = 2 ^ 12 * 2 ^ 12 := by rw [this]; norm_num
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h12
  have h2 := card_mul_two_pow h.card_W X
  rw [hidx] at hle
  have h3 : 2 ^ 24 ≤ 2 ^ 12 * 2 ^ rkIdx X := by
    rw [← h2]
    exact Nat.mul_le_mul_right _ hle
  rw [← pow_add] at h3
  have := (Nat.pow_le_pow_iff_right (by norm_num)).1 h3
  omega

theorem card_fixV_eq_mul {x : MulAut W} (h₁ : ∀ w ∈ W₁, x w ∈ W₁) (h₂ : ∀ w ∈ W₂, x w ∈ W₂) :
    Nat.card (fixV (Subgroup.zpowers x)) =
      Nat.card ↥(fixV (Subgroup.zpowers x) ⊓ W₁) * Nat.card ↥(fixV (Subgroup.zpowers x) ⊓ W₂) := by
  set X := fixV (Subgroup.zpowers x)
  rw [← Nat.card_prod]
  let f : ↥(X ⊓ W₁) × ↥(X ⊓ W₂) → ↥X := fun p => ⟨p.1 * p.2, mul_mem p.1.2.1 p.2.2.1⟩
  have hbij := h.bijective_prodMul
  refine (Nat.card_congr (Equiv.ofBijective f ⟨fun p q hpq => ?_, fun w => ?_⟩)).symm
  · have : (W₁.subtype.coprod W₂.subtype) (⟨p.1, p.1.2.2⟩, ⟨p.2, p.2.2.2⟩) =
        (W₁.subtype.coprod W₂.subtype) (⟨q.1, q.1.2.2⟩, ⟨q.2, q.2.2.2⟩) :=
      congrArg Subtype.val hpq
    have h' := hbij.1 this
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at h'
    exact Prod.ext (Subtype.ext h'.1) (Subtype.ext h'.2)
  · obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.1 (h.sup ▸ Subgroup.mem_top (w : W))
    have hw := mem_fixV_zp.1 w.2
    have hxab : (W₁.subtype.coprod W₂.subtype) (⟨x a, h₁ a ha⟩, ⟨x b, h₂ b hb⟩) =
        (W₁.subtype.coprod W₂.subtype) (⟨a, ha⟩, ⟨b, hb⟩) := by
      show x a * x b = a * b
      rw [← map_mul, hab, hw]
    have h' := hbij.1 hxab
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at h'
    exact ⟨(⟨a, mem_fixV_zp.2 h'.1, ha⟩, ⟨b, mem_fixV_zp.2 h'.2, hb⟩), Subtype.ext hab⟩

theorem rkIdx_eq_add {x : MulAut W} (h₁ : ∀ w ∈ W₁, x w ∈ W₁) (h₂ : ∀ w ∈ W₂, x w ∈ W₂) :
    rkIdx (fixV (Subgroup.zpowers x)) =
      E3.mQuot W₁ (fixV (Subgroup.zpowers x)) + E3.mQuot W₂ (fixV (Subgroup.zpowers x)) := by
  have : Finite W := h.finite_W
  have hc := h.card_fixV_eq_mul h₁ h₂
  set X := fixV (Subgroup.zpowers x) with hX
  have h0 := card_mul_two_pow h.card_W X
  have hr₁ := Subgroup.relIndex_mul_card X W₁
  have hr₂ := Subgroup.relIndex_mul_card X W₂
  have hp₁ : IsPGroup 2 W₁ := IsPGroup.of_card h.card_W₁
  have hp₂ : IsPGroup 2 W₂ := IsPGroup.of_card h.card_W₂
  rw [E3.relIndex_eq_two_pow hp₁, h.card_W₁] at hr₁
  rw [E3.relIndex_eq_two_pow hp₂, h.card_W₂] at hr₂
  have hpos : 0 < Nat.card ↥(X ⊓ W₁) * Nat.card ↥(X ⊓ W₂) := Nat.mul_pos Nat.card_pos Nat.card_pos
  have key : 2 ^ rkIdx X * (Nat.card ↥(X ⊓ W₁) * Nat.card ↥(X ⊓ W₂)) =
      2 ^ (E3.mQuot W₁ X + E3.mQuot W₂ X) * (Nat.card ↥(X ⊓ W₁) * Nat.card ↥(X ⊓ W₂)) := by
    rw [← hc, mul_comm, h0, pow_add]
    calc (2 : ℕ) ^ 24 = 2 ^ 12 * 2 ^ 12 := by norm_num
      _ = 2 ^ E3.mQuot W₁ X * Nat.card ↥(X ⊓ W₁) * (2 ^ E3.mQuot W₂ X * Nat.card ↥(X ⊓ W₂)) := by
          rw [hr₁, hr₂]
      _ = _ := by rw [hc]; ring
  exact Nat.pow_right_injective le_rfl (Nat.eq_of_mul_eq_mul_right hpos key)

end Hyp

end CFSG.Quasithin.Vol2.Ch10.SecB.KL7
