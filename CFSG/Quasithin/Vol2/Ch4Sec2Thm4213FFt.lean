module

public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213FFw

public section

namespace CFSG.Quasithin.H13.Ch4.FFt

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

section Klein

variable {M : Type*} [Group M]

theorem pow_val_add {a : M} (ha : a ^ 2 = 1) (x y : ZMod 2) :
    a ^ (x + y).val = a ^ x.val * a ^ y.val := by
  rw [ZMod.val_add, ← pow_add]
  conv_rhs => rw [← Nat.mod_add_div (x.val + y.val) 2, pow_add, pow_mul, ha, one_pow, mul_one]

@[expose] def klein {a b : M} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hab : a * b = b * a) :
    Multiplicative (Fin 2 → ZMod 2) →* M where
  toFun v := a ^ (Multiplicative.toAdd v 0).val * b ^ (Multiplicative.toAdd v 1).val
  map_one' := by simp
  map_mul' v w := by
    simp only [toAdd_mul, Pi.add_apply]
    rw [pow_val_add ha, pow_val_add hb]
    set p := (Multiplicative.toAdd v 0).val
    set q := (Multiplicative.toAdd w 0).val
    set r := (Multiplicative.toAdd v 1).val
    set t := (Multiplicative.toAdd w 1).val
    have hc : b ^ r * a ^ q = a ^ q * b ^ r := ((show Commute a b from hab).symm.pow_pow r q).eq
    calc a ^ p * a ^ q * (b ^ r * b ^ t) = a ^ p * (a ^ q * b ^ r) * b ^ t := by group
      _ = a ^ p * (b ^ r * a ^ q) * b ^ t := by rw [hc]
      _ = a ^ p * b ^ r * (a ^ q * b ^ t) := by group

theorem klein_apply {a b : M} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hab : a * b = b * a)
    (v : Multiplicative (Fin 2 → ZMod 2)) :
    klein ha hb hab v = a ^ (Multiplicative.toAdd v 0).val * b ^ (Multiplicative.toAdd v 1).val :=
  rfl

theorem klein_injective {a b : M} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hab : a * b = b * a)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) : Function.Injective (klein ha hb hab) := by
  rw [injective_iff_map_eq_one]
  intro v hv
  rw [klein_apply] at hv
  have hab' : a * b ≠ 1 := fun h => hne (by
    rw [mul_eq_one_iff_eq_inv] at h
    rw [h, inv_eq_of_mul_eq_one_right (by rw [← sq, hb])])
  have key : ∀ x y : ZMod 2, a ^ x.val * b ^ y.val = 1 → x = 0 ∧ y = 0 := by
    intro x y h
    fin_cases x <;> fin_cases y
    · exact ⟨rfl, rfl⟩
    · have h' : a ^ 0 * b ^ 1 = 1 := h
      rw [pow_zero, pow_one, one_mul] at h'
      exact absurd h' hb1
    · have h' : a ^ 1 * b ^ 0 = 1 := h
      rw [pow_zero, pow_one, mul_one] at h'
      exact absurd h' ha1
    · have h' : a ^ 1 * b ^ 1 = 1 := h
      rw [pow_one, pow_one] at h'
      exact absurd h' hab'
  obtain ⟨h0, h1⟩ := key _ _ hv
  apply Multiplicative.toAdd.injective
  funext i
  fin_cases i
  · exact h0
  · exact h1

theorem card_klein_range {a b : M} [Finite M] (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
    (hab : a * b = b * a) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) :
    Nat.card (klein ha hb hab).range = 4 := by
  rw [MonoidHom.range_eq_map,
    Subgroup.card_map_of_injective (klein_injective ha hb hab ha1 hb1 hne), Subgroup.card_top]
  show Nat.card (Fin 2 → ZMod 2) = 4
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin]
  rfl

theorem isElemAbelian2_klein_range {U : Type*} [CommGroup U] {a b : MulAut U} (ha : a ^ 2 = 1)
    (hb : b ^ 2 = 1) (hab : a * b = b * a) : IsElemAbelian2 (klein ha hb hab).range := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨v, rfl⟩ _ ⟨w, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]
  · rintro _ ⟨v, rfl⟩
    rw [← map_pow]
    have : v ^ 2 = 1 := by
      apply Multiplicative.toAdd.injective
      funext j
      simp only [toAdd_pow, toAdd_one, Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul,
        Nat.cast_ofNat]
      exact (show ∀ x : ZMod 2, 2 * x = 0 by decide) _
    rw [this, map_one]

end Klein

section Transv

variable {U : Type*} [CommGroup U]

@[expose] def dHom (x : MulAut U) : U →* U where
  toFun u := x u * u⁻¹
  map_one' := by simp
  map_mul' u v := by
    rw [map_mul, mul_inv]
    exact mul_mul_mul_comm _ _ _ _

@[expose] def commU (x : MulAut U) : Subgroup U := (dHom x).range

@[expose] def fixU (x : MulAut U) : Subgroup U := (dHom x).ker

theorem dHom_apply (x : MulAut U) (u : U) : dHom x u = x u * u⁻¹ := rfl

theorem mem_fixU {x : MulAut U} {u : U} : u ∈ fixU x ↔ x u = u := by
  rw [fixU, MonoidHom.mem_ker, dHom_apply, mul_inv_eq_one]

theorem card_commU_mul_card_fixU [Finite U] (x : MulAut U) :
    Nat.card (commU x) * Nat.card (fixU x) = Nat.card U := by
  have h := Subgroup.card_mul_index (fixU x)
  rw [fixU, Subgroup.index_ker] at h
  rw [commU, mul_comm]
  exact h

theorem apply_mem_commU {σ y : MulAut U} (h : y * σ = σ * y) {u : U} (hu : u ∈ commU y) :
    σ u ∈ commU y := by
  obtain ⟨v, rfl⟩ := hu
  refine ⟨σ v, ?_⟩
  have h1 := congrArg (fun g : MulAut U => g v) h
  simp only [MulAut.mul_apply] at h1
  rw [dHom_apply, dHom_apply, map_mul, map_inv, h1]

theorem apply_mem_fixU {σ y : MulAut U} (h : y * σ = σ * y) {u : U} (hu : u ∈ fixU y) :
    σ u ∈ fixU y := by
  rw [mem_fixU] at hu ⊢
  have h1 := congrArg (fun g : MulAut U => g u) h
  simp only [MulAut.mul_apply] at h1
  rw [h1, hu]

theorem commU_le_fixU (hU2 : ∀ u : U, u ^ 2 = 1) {x : MulAut U} (hx2 : x ^ 2 = 1) :
    commU x ≤ fixU x := by
  rintro _ ⟨u, rfl⟩
  rw [mem_fixU, dHom_apply, map_mul, map_inv]
  have h1 : x (x u) = u := by
    have := congrArg (fun g : MulAut U => g u) hx2
    simpa [sq, MulAut.mul_apply] using this
  have hinv : ∀ v : U, v⁻¹ = v := fun v => by rw [inv_eq_iff_mul_eq_one, ← sq, hU2]
  rw [h1, hinv, hinv, mul_comm]

theorem card_eq_four_pow [Finite U] (hU2 : ∀ u : U, u ^ 2 = 1) {σ : MulAut U}
    (hσ3 : σ ^ 3 = 1) (hfree : ∀ u, σ u = u → u = 1) {W : Subgroup U}
    (hW : ∀ w ∈ W, σ w ∈ W) : ∃ k, Nat.card W = 4 ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hW2 : IsPGroup 2 ↥W := fun w => ⟨1, Subtype.ext (by simpa using hU2 w)⟩
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hW2
  have hpow : ∀ n : ℕ, σ ^ n = σ ^ (n % 3) := fun n => by
    conv_lhs => rw [← Nat.mod_add_div n 3, pow_add, pow_mul, hσ3, one_pow, mul_one]
  have hWn : ∀ n : ℕ, ∀ w ∈ W, (σ ^ n) w ∈ W := by
    intro n
    induction n with
    | zero => intro w hw; simpa using hw
    | succ n ih =>
      intro w hw
      rw [pow_succ', MulAut.mul_apply]
      exact hW _ (ih w hw)
  let _ : MulAction (Multiplicative (ZMod 3)) ↥W :=
    { smul := fun m w => ⟨(σ ^ (Multiplicative.toAdd m).val) w, hWn _ w w.2⟩
      one_smul := fun w => Subtype.ext (by
        show (σ ^ (Multiplicative.toAdd (1 : Multiplicative (ZMod 3))).val) w = w
        rw [toAdd_one, ZMod.val_zero, pow_zero, MulAut.one_apply])
      mul_smul := fun m n w => Subtype.ext (by
        show (σ ^ (Multiplicative.toAdd (m * n)).val) w =
          (σ ^ (Multiplicative.toAdd m).val) ((σ ^ (Multiplicative.toAdd n).val) w)
        rw [toAdd_mul, ZMod.val_add, ← hpow, pow_add, MulAut.mul_apply]) }
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : IsPGroup 3 (Multiplicative (ZMod 3)) := IsPGroup.of_card (n := 1) (by
    show Nat.card (ZMod 3) = 3 ^ 1
    rw [Nat.card_zmod, pow_one])
  have hmod := h3.card_modEq_card_fixedPoints ↥W
  have hfix1 : Nat.card (MulAction.fixedPoints (Multiplicative (ZMod 3)) ↥W) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    have h1 : ∀ x : ↥(MulAction.fixedPoints (Multiplicative (ZMod 3)) ↥W),
        ((x : ↥W) : U) = 1 := by
      intro x
      have hx := x.2 (Multiplicative.ofAdd 1)
      have h2 : (σ ^ (1 : ZMod 3).val) ((x : ↥W) : U) = ((x : ↥W) : U) :=
        congrArg Subtype.val hx
      rw [show (1 : ZMod 3).val = 1 from rfl, pow_one] at h2
      exact hfree _ h2
    refine ⟨⟨fun x y => Subtype.ext (Subtype.ext ((h1 x).trans (h1 y).symm))⟩,
      ⟨⟨1, fun m => Subtype.ext (map_one _)⟩⟩⟩
  rw [hj, hfix1] at hmod
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' j
  · exact ⟨m, by rw [hj, pow_mul]; norm_num⟩
  · exfalso
    have h4 : 4 ^ m % 3 = 1 := by
      rw [Nat.pow_mod]
      norm_num
    have h5 : 2 ^ (2 * m + 1) % 3 = 2 := by
      rw [pow_succ, pow_mul, Nat.mul_mod, show (2 : ℕ) ^ 2 = 4 from rfl, h4]
    have h6 : 2 ^ (2 * m + 1) % 3 = 1 % 3 := hmod
    omega

theorem card_commU_fixU [Finite U] (hU2 : ∀ u : U, u ^ 2 = 1) (hU64 : Nat.card U = 64)
    {σ : MulAut U} (hσ3 : σ ^ 3 = 1) (hfree : ∀ u, σ u = u → u = 1) {x : MulAut U}
    (hx2 : x ^ 2 = 1) (hx1 : x ≠ 1) (hxσ : x * σ = σ * x) :
    Nat.card (commU x) = 4 ∧ Nat.card (fixU x) = 16 := by
  obtain ⟨a, ha⟩ := card_eq_four_pow hU2 hσ3 hfree fun _ hu => apply_mem_commU hxσ hu
  obtain ⟨b, hb⟩ := card_eq_four_pow hU2 hσ3 hfree fun _ hu => apply_mem_fixU hxσ hu
  have hprod := card_commU_mul_card_fixU x
  rw [ha, hb, hU64, ← pow_add, show (64 : ℕ) = 4 ^ 3 from rfl] at hprod
  have hab3 : a + b = 3 := Nat.pow_right_injective (by norm_num : 2 ≤ 4) hprod
  have hle : 4 ^ a ≤ 4 ^ b := ha ▸ hb ▸ Subgroup.card_le_of_le (commU_le_fixU hU2 hx2)
  have hab : a ≤ b := (Nat.pow_le_pow_iff_right (by norm_num)).mp hle
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at ha
    apply hx1
    ext u
    have h1 : dHom x u ∈ commU x := ⟨u, rfl⟩
    rw [Subgroup.card_eq_one.mp ha, Subgroup.mem_bot, dHom_apply, mul_inv_eq_one] at h1
    exact h1
  have ha1 : a = 1 := by omega
  have hb2 : b = 2 := by omega
  rw [ha, hb, ha1, hb2]
  norm_num

end Transv

section Dihedral

variable {U : Type*} [CommGroup U]

theorem pow_apply_eq {g : MulAut U} {u : U} (h : g u = u) (n : ℕ) : (g ^ n) u = u := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, MulAut.mul_apply, h, ih]

theorem fixU_eq_or_commU_eq [Finite U] (hU2 : ∀ u : U, u ^ 2 = 1) (hU64 : Nat.card U = 64)
    {σ : MulAut U} (hσ3 : σ ^ 3 = 1) (hfree : ∀ u, σ u = u → u = 1) {a b : MulAut U}
    (ha2 : a ^ 2 = 1) (hb2 : b ^ 2 = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b)
    (hab : a * b = b * a) (haσ : a * σ = σ * a) (hbσ : b * σ = σ * b) :
    fixU a = fixU b ∨ commU a = commU b := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hfix, hcomm⟩ := hcon
  have hab2 : (a * b) ^ 2 = 1 := by
    have : (a * b) ^ 2 = a ^ 2 * b ^ 2 := (Commute.mul_pow hab 2)
    rw [this, ha2, hb2, one_mul]
  have hab1 : a * b ≠ 1 := fun h => hne (by
    rw [mul_eq_one_iff_eq_inv] at h
    rw [h, inv_eq_of_mul_eq_one_right (by rw [← sq, hb2])])
  have habσ : a * b * σ = σ * (a * b) := by
    rw [mul_assoc, hbσ, ← mul_assoc, haσ, mul_assoc]
  obtain ⟨hcab, -⟩ := card_commU_fixU hU2 hU64 hσ3 hfree hab2 hab1 habσ
  have key : ∀ x y : MulAut U, x ^ 2 = 1 → y ^ 2 = 1 → x ≠ 1 → y ≠ 1 → x * σ = σ * x →
      y * σ = σ * y → fixU x ≠ fixU y → Nat.card (commU (x * y)) = 4 →
      commU x = commU (x * y) := by
    intro x y hx2 hy2 hx1 hy1 hxσ hyσ hxy hcxy
    obtain ⟨hcx, hfx⟩ := card_commU_fixU hU2 hU64 hσ3 hfree hx2 hx1 hxσ
    obtain ⟨-, hfy⟩ := card_commU_fixU hU2 hU64 hσ3 hfree hy2 hy1 hyσ
    set φ : ↥(fixU y) →* U := (dHom x).comp (fixU y).subtype with hφ
    have hrx : φ.range ≤ commU x := by
      rintro _ ⟨u, rfl⟩
      exact ⟨u, rfl⟩
    have hrxy : φ.range ≤ commU (x * y) := by
      rintro _ ⟨u, rfl⟩
      refine ⟨u, ?_⟩
      show (x * y) (u : U) * (u : U)⁻¹ = x u * (u : U)⁻¹
      rw [MulAut.mul_apply, mem_fixU.mp u.2]
    have hker : Nat.card φ.ker = Nat.card ↥(fixU x ⊓ fixU y) := by
      refine Nat.card_congr
        { toFun := fun k => ⟨((k : ↥(fixU y)) : U), ?_, (k : ↥(fixU y)).2⟩
          invFun := fun w => ⟨⟨w, w.2.2⟩, ?_⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      · have hk : x ((k : ↥(fixU y)) : U) * ((k : ↥(fixU y)) : U)⁻¹ = 1 := k.2
        exact mem_fixU.mpr (mul_inv_eq_one.mp hk)
      · show x (w : U) * (w : U)⁻¹ = 1
        rw [mul_inv_eq_one]
        exact mem_fixU.mp w.2.1
    have hprod : Nat.card φ.ker * Nat.card φ.range = 16 := by
      have h := Subgroup.card_mul_index φ.ker
      rw [Subgroup.index_ker] at h
      rw [h, hfy]
    rw [hker] at hprod
    have hI : ∀ w ∈ fixU x ⊓ fixU y, σ w ∈ fixU x ⊓ fixU y := fun w hw =>
      ⟨apply_mem_fixU hxσ hw.1, apply_mem_fixU hyσ hw.2⟩
    obtain ⟨k, hk⟩ := card_eq_four_pow hU2 hσ3 hfree hI
    have hle16 : Nat.card ↥(fixU x ⊓ fixU y) ≠ 16 := by
      intro h16
      apply hxy
      have h1 : fixU x ⊓ fixU y = fixU y :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h16, hfy])
      have h2 : fixU y ≤ fixU x := h1 ▸ inf_le_left
      exact (Subgroup.eq_of_le_of_card_ge h2 (by rw [hfx, hfy])).symm
    have hrange4 : Nat.card φ.range ≤ 4 := hcx ▸ Subgroup.card_le_of_le hrx
    have hrange : Nat.card φ.range = 4 := by
      have hpos : 1 ≤ Nat.card φ.range := Nat.card_pos
      rw [hk] at hprod hle16
      have hk3 : k < 3 := by
        by_contra hk3
        push Not at hk3
        have h64 : 4 ^ 3 ≤ 4 ^ k := Nat.pow_le_pow_right (by norm_num) hk3
        have h4k : 4 ^ k ≤ 4 ^ k * Nat.card φ.range := Nat.le_mul_of_pos_right _ hpos
        omega
      interval_cases k
      · rw [pow_zero, one_mul] at hprod
        omega
      · rw [pow_one] at hprod
        omega
      · exact absurd (by norm_num) hle16
    have h1 : φ.range = commU x :=
      Subgroup.eq_of_le_of_card_ge hrx (by rw [hcx, hrange])
    exact Subgroup.eq_of_le_of_card_ge (h1 ▸ hrxy) (by rw [hcxy, hcx])
  have h1 := key a b ha2 hb2 ha1 hb1 haσ hbσ hfix hcab
  have h2 := key b a hb2 ha2 hb1 ha1 hbσ haσ (Ne.symm hfix) (by rw [← hab]; exact hcab)
  rw [← hab] at h2
  exact hcomm (h1.trans h2.symm)

theorem comm_of_commU_eq {x y : MulAut U} (hxy : commU x = commU y) (hx : commU x ≤ fixU x)
    (hy : commU y ≤ fixU y) : x * y = y * x := by
  ext u
  simp only [MulAut.mul_apply]
  have hp : dHom y u ∈ fixU x := hx (by rw [hxy]; exact ⟨u, rfl⟩)
  have hq : dHom x u ∈ fixU y := hy (by rw [← hxy]; exact ⟨u, rfl⟩)
  calc x (y u) = x (dHom y u * u) := by rw [dHom_apply, inv_mul_cancel_right]
    _ = dHom y u * x u := by rw [map_mul, mem_fixU.mp hp]
    _ = dHom y u * (dHom x u * u) := by rw [dHom_apply x, inv_mul_cancel_right]
    _ = dHom x u * (dHom y u * u) := by rw [mul_left_comm]
    _ = dHom x u * y u := by rw [dHom_apply y, inv_mul_cancel_right]
    _ = y (dHom x u) * y u := by rw [mem_fixU.mp hq]
    _ = y (dHom x u * u) := by rw [map_mul]
    _ = y (x u) := by rw [dHom_apply, inv_mul_cancel_right]

theorem isFFModule_of_dihedral [Finite U] (hU2 : ∀ u : U, u ^ 2 = 1) (hU64 : Nat.card U = 64)
    {σ r s : MulAut U} (hσ3 : σ ^ 3 = 1) (hfree : ∀ u, σ u = u → u = 1)
    (hrσ : r * σ = σ * r) (hsσ : s * σ = σ * s) (hr4 : r ^ 4 = 1) (hr2 : r ^ 2 ≠ 1)
    (hs2 : s ^ 2 = 1) (hsr : s * r * s⁻¹ = r⁻¹) {X : Subgroup (MulAut U)} (hrX : r ∈ X)
    (hsX : s ∈ X) : IsFFModule X := by
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right (by rw [← sq, hs2])
  have hz2 : (r ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact hr4
  have hzinv : (r ^ 2)⁻¹ = r ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← sq, hz2])
  have hrr : r = r⁻¹ → False := fun h => hr2 (by
    rw [sq]
    nth_rewrite 2 [h]
    exact mul_inv_cancel r)
  have hs1 : s ≠ 1 := fun h => hrr (by
    have := hsr
    rw [h, one_mul, inv_one, mul_one] at this
    exact this)
  have ht2 : (s * r) ^ 2 = 1 := by
    rw [sq, show s * r * (s * r) = (s * r * s⁻¹) * r by rw [hsinv]; group, hsr, inv_mul_cancel]
  have ht1 : s * r ≠ 1 := by
    intro h
    have hs : s = r⁻¹ := eq_inv_of_mul_eq_one_left h
    apply hr2
    have : s ^ 2 = (r ^ 2)⁻¹ := by rw [hs, inv_pow]
    rw [hs2] at this
    exact inv_eq_one.mp this.symm
  have hrz : r * r ^ 2 = r ^ 2 * r := by rw [← pow_succ', ← pow_succ]
  have hzs : r ^ 2 * s = s * r ^ 2 := by
    have h1 : s * r ^ 2 * s⁻¹ = r ^ 2 := by
      have h2 : s * r ^ 2 * s⁻¹ = (s * r * s⁻¹) ^ 2 := by
        rw [sq, sq]
        group
      rw [h2, hsr, inv_pow, hzinv]
    calc r ^ 2 * s = s * r ^ 2 * s⁻¹ * s := by rw [h1]
      _ = s * r ^ 2 := by group
  have hzt : r ^ 2 * (s * r) = s * r * r ^ 2 := by
    rw [← mul_assoc, hzs, mul_assoc, ← hrz, mul_assoc]
  have hzs' : r ^ 2 ≠ s := by
    intro h
    apply hrr
    rw [← hsr, ← h, ← hrz, mul_inv_cancel_right]
  have hzt' : r ^ 2 ≠ s * r := by
    intro h
    have hsr' : s = r := by
      have h1 : s = r ^ 2 * r⁻¹ := by rw [h, mul_inv_cancel_right]
      rw [h1, sq, mul_inv_cancel_right]
    apply hrr
    rw [← hsr, hsr', mul_inv_cancel_right]
  have hzσ : r ^ 2 * σ = σ * r ^ 2 := by
    rw [sq, mul_assoc, hrσ, ← mul_assoc, hrσ, mul_assoc]
  have htσ : s * r * σ = σ * (s * r) := by
    rw [mul_assoc, hrσ, ← mul_assoc, hsσ, mul_assoc]
  have hz1 : r ^ 2 ≠ 1 := hr2
  have hzX : r ^ 2 ∈ X := X.pow_mem hrX 2
  have htX : s * r ∈ X := X.mul_mem hsX hrX
  have hoff : ∀ b : MulAut U, b ∈ X → (hb2 : b ^ 2 = 1) → b ≠ 1 → r ^ 2 ≠ b →
      (hzb : r ^ 2 * b = b * r ^ 2) → fixU (r ^ 2) = fixU b → IsFFModule X := by
    intro b hbX hb2 hb1 hzb hzbc hfix
    obtain ⟨-, hfz⟩ := card_commU_fixU hU2 hU64 hσ3 hfree hz2 hz1 hzσ
    have h4 := card_klein_range hz2 hb2 hzbc hz1 hb1 hzb
    refine ⟨(klein hz2 hb2 hzbc).range, ?_, ?_, isElemAbelian2_klein_range hz2 hb2 hzbc, ?_⟩
    · rintro _ ⟨v, rfl⟩
      rw [klein_apply]
      exact X.mul_mem (X.pow_mem hzX _) (X.pow_mem hbX _)
    · intro hbot
      rw [hbot, Subgroup.card_bot] at h4
      exact absurd h4 (by norm_num)
    · have hle : fixU (r ^ 2) ≤ fixV (klein hz2 hb2 hzbc).range := by
        intro u hu
        rw [mem_fixV]
        rintro _ ⟨v, rfl⟩
        have hzu : (r ^ 2) u = u := mem_fixU.mp hu
        have hbu : b u = u := mem_fixU.mp (hfix ▸ hu)
        rw [klein_apply, MulAut.mul_apply, pow_apply_eq hbu, pow_apply_eq hzu]
      rw [hU64, h4]
      have := Subgroup.card_le_of_le hle
      omega
  rcases fixU_eq_or_commU_eq hU2 hU64 hσ3 hfree hz2 hs2 hz1 hs1 hzs' hzs hzσ hsσ with h1 | h1
  · exact hoff s hsX hs2 hs1 hzs' hzs h1
  rcases fixU_eq_or_commU_eq hU2 hU64 hσ3 hfree hz2 ht2 hz1 ht1 hzt' hzt hzσ htσ with h2 | h2
  · exact hoff (s * r) htX ht2 ht1 hzt' hzt h2
  exfalso
  have hst := comm_of_commU_eq (h1.symm.trans h2) (commU_le_fixU hU2 hs2)
    (commU_le_fixU hU2 ht2)
  apply hrr
  calc r = s * (s * r) := by rw [← mul_assoc, ← sq, hs2, one_mul]
    _ = s * r * s := hst
    _ = s * r * s⁻¹ := by rw [hsinv]
    _ = r⁻¹ := hsr

end Dihedral

theorem exists_dihedral_lift {X : Type*} [Group X] [Finite X]
    (hZ : Nat.card (Subgroup.center X) = 3) {S : Type*} [Group S]
    (e : X ⧸ Subgroup.center X ≃* S) {r₀ s₀ : S} (hr4 : r₀ ^ 4 = 1) (hr2 : r₀ ^ 2 ≠ 1)
    (hs2 : s₀ ^ 2 = 1) (hsr : s₀ * r₀ * s₀⁻¹ = r₀⁻¹) :
    ∃ r s : X, r ^ 4 = 1 ∧ r ^ 2 ≠ 1 ∧ s ^ 2 = 1 ∧ s * r * s⁻¹ = r⁻¹ := by
  set π : X →* S := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X)) with hπ
  have hπs : Function.Surjective π :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ∀ x : X, π x = 1 → x ∈ Subgroup.center X := by
    intro x hx
    have h1 : (QuotientGroup.mk' (Subgroup.center X) x) = 1 := by
      apply e.injective
      rw [map_one]
      exact hx
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  have hz3 : ∀ x ∈ Subgroup.center X, x ^ 3 = 1 := by
    intro x hx
    have h1 : (⟨x, hx⟩ : ↥(Subgroup.center X)) ^ Nat.card (Subgroup.center X) = 1 :=
      pow_card_eq_one'
    rw [hZ] at h1
    simpa using congrArg Subtype.val h1
  obtain ⟨qr, hqr⟩ := hπs r₀
  obtain ⟨qs, hqs⟩ := hπs s₀
  have hr8 : r₀ ^ 8 = 1 := by rw [show 8 = 4 * 2 from rfl, pow_mul, hr4, one_pow]
  have hqr4 : qr ^ 4 ∈ Subgroup.center X := hker _ (by rw [map_pow, hqr, hr4])
  have hqs2 : qs ^ 2 ∈ Subgroup.center X := hker _ (by rw [map_pow, hqs, hs2])
  set r := qr ^ 9 with hr
  set s := qs ^ 3 with hs
  have hπr : π r = r₀ := by
    rw [hr, map_pow, hqr, show 9 = 8 + 1 from rfl, pow_succ, hr8, one_mul]
  have hπs' : π s = s₀ := by
    rw [hs, map_pow, hqs, show 3 = 2 + 1 from rfl, pow_succ, hs2, one_mul]
  have hr4' : r ^ 4 = 1 := by
    rw [hr, ← pow_mul, show 9 * 4 = 4 * 9 from rfl, pow_mul,
      show 9 = 3 * 3 from rfl, pow_mul, hz3 _ hqr4, one_pow]
  have hs2' : s ^ 2 = 1 := by
    rw [hs, ← pow_mul, show 3 * 2 = 2 * 3 from rfl, pow_mul, hz3 _ hqs2]
  refine ⟨r, s, hr4', fun h => hr2 ?_, hs2', ?_⟩
  · rw [← hπr, ← map_pow, h, map_one]
  · set x := s * r * s⁻¹ * r with hx
    have hxZ : x ∈ Subgroup.center X := hker _ (by
      rw [hx, map_mul, map_mul, map_mul, map_inv, hπr, hπs', hsr, inv_mul_cancel])
    have hxc : ∀ y : X, x * y = y * x := fun y =>
      (Subgroup.mem_center_iff.mp hxZ y).symm
    have h1 : s * r * s⁻¹ = x * r⁻¹ := by rw [hx]; group
    have h2 : (s * r * s⁻¹) ^ 4 = 1 := by
      rw [conj_pow, hr4', mul_one, mul_inv_cancel]
    have h3 : (x * r⁻¹) ^ 4 = x ^ 4 * r⁻¹ ^ 4 := (Commute.mul_pow (hxc r⁻¹) 4)
    rw [h1, h3, inv_pow, hr4', inv_one, mul_one, show 4 = 3 + 1 from rfl, pow_succ,
      hz3 x hxZ, one_mul] at h2
    rw [h1, h2, one_mul]

@[expose] def r6 : ↥(alternatingGroup (Fin 6)) :=
  ⟨Equiv.swap 0 3 * Equiv.swap 0 2 * Equiv.swap 0 1 * Equiv.swap 4 5, by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_mul,
      Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide),
      Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide)]
    decide⟩

@[expose] def s6 : ↥(alternatingGroup (Fin 6)) :=
  ⟨Equiv.swap 0 2 * Equiv.swap 4 5, by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
      Equiv.Perm.sign_swap (by decide)]
    decide⟩

theorem r6_pow_four : r6 ^ 4 = 1 := by decide

theorem r6_sq_ne_one : r6 ^ 2 ≠ 1 := by decide

theorem s6_sq : s6 ^ 2 = 1 := by decide

theorem s6_r6 : s6 * r6 * s6⁻¹ = r6⁻¹ := by decide

end CFSG.Quasithin.H13.Ch4.FFt

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Quasithin.A4 CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G]

namespace Conf4212

variable {T M L I H K : Subgroup G} (c : Conf4212 G T M L I H K)
include c

open scoped IsMulCommutative in
theorem ff_of_case5 (h5 : CFSG.Quasithin.IsHatA6Block (perfectCore (L ⊓ H))) :
    ∃ _ : IsMulCommutative ↥⁅reducedAggregate (L ⊔ T), L⁆,
      IsFFModule (V := ↥⁅reducedAggregate (L ⊔ T), L⁆)
        (autOn (L ⊔ T) ⁅reducedAggregate (L ⊔ T), L⁆) := by
  have hV := c.isMulCommutative_V
  have hVU := c.V_eq_blockU_of_isHatA6Block h5
  set LH := perfectCore (L ⊓ H) with hLHdef
  set V := ⁅reducedAggregate (L ⊔ T), L⁆ with hVdef
  have h5' := h5
  obtain ⟨-, hhat, hcard, hcent⟩ := h5'
  have hLHV : LH ≤ Subgroup.normalizer (V : Set G) := c.LH_le_normalizer_V
  set ρ := Setup.rho V LH hLHV with hρ
  have hmemQ : ∀ x : ↥LH, (x : G) ∈ pCoreOf 2 LH ↔ (QuotientGroup.mk x : ModO2 LH) = 1 := by
    intro x
    rw [QuotientGroup.eq_one_iff]
    exact Subgroup.mem_map_iff_mem LH.subtype_injective
  have hρ1 : ∀ ℓ : ↥LH, ρ ℓ = 1 ↔ (ℓ : G) ∈ pCoreOf 2 LH := by
    intro ℓ
    rw [Setup.rho_eq_one_iff, ← hcent, hVU]
    exact ⟨fun h => ⟨ℓ.2, h⟩, fun h => h.2⟩
  have hle : CFSG.pCore 2 ↥LH ≤ ρ.ker := by
    intro ℓ hℓ
    rw [MonoidHom.mem_ker, hρ1, hmemQ, QuotientGroup.eq_one_iff]
    exact hℓ
  set π : ModO2 LH →* MulAut ↥V := QuotientGroup.lift (CFSG.pCore 2 ↥LH) ρ hle with hπ
  have hπmk : ∀ ℓ : ↥LH, π (QuotientGroup.mk ℓ) = ρ ℓ := fun ℓ => QuotientGroup.lift_mk _ _ _
  have hπinj : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    intro q hq
    obtain ⟨ℓ, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hπmk, hρ1, hmemQ] at hq
    exact hq
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ↥(Subgroup.center (ModO2 LH)), c₀ ≠ 1 := by
    by_contra hne
    push Not at hne
    have h1 : Nat.card (Subgroup.center (ModO2 LH)) = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => (hne a).trans (hne b).symm⟩, ⟨1⟩⟩
    have h2 : Nat.card (Subgroup.center (ModO2 LH)) = 3 := hhat.2.1
    omega
  have hc3 : (c₀ : ModO2 LH) ^ 3 = 1 := by
    have h1 : c₀ ^ Nat.card (Subgroup.center (ModO2 LH)) = 1 := pow_card_eq_one'
    rw [hhat.2.1] at h1
    simpa using congrArg Subtype.val h1
  have hσ3 : π c₀ ^ 3 = 1 := by rw [← map_pow, hc3, map_one]
  have hσ1 : π c₀ ≠ 1 := fun h => hc₀ (Subtype.ext (hπinj (h.trans (map_one π).symm)))
  have hσc : ∀ q : ModO2 LH, π q * π c₀ = π c₀ * π q := fun q => by
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp c₀.2 q]
  have hU2 : ∀ v : ↥V, v ^ 2 = 1 := fun v => Subtype.ext (c.hypC28.V_elem.2 _ v.2)
  have hU64 : Nat.card ↥V = 64 := by
    rw [hVU, hcard]
    norm_num
  have hfree : ∀ u : ↥V, π c₀ u = u → u = 1 := by
    set W : Subgroup G := (FFt.fixU (π c₀)).map V.subtype with hW
    have hWU : W ≤ blockU LH := hVU ▸ Subgroup.map_subtype_le _
    have hLHW : LH ≤ Subgroup.normalizer (W : Set G) := by
      intro ℓ hℓ
      refine A4.mem_normalizer_of_conj_mem fun w hw => ?_
      obtain ⟨u, hu, rfl⟩ := hw
      refine ⟨ρ ⟨ℓ, hℓ⟩ u, ?_, Setup.rho_apply_coe hLHV _ _⟩
      rw [SetLike.mem_coe, FFt.mem_fixU] at hu ⊢
      have h1 := congrArg (fun g : MulAut ↥V => g u) (hσc (QuotientGroup.mk ⟨ℓ, hℓ⟩))
      simp only [MulAut.mul_apply, hπmk] at h1
      rw [← h1, hu]
    rcases T4213N.eq_bot_or_eq_blockU_of_isHatA6Block h5 hWU hLHW with hbot | htop
    · intro u hu
      have hmem : (u : G) ∈ W := ⟨u, FFt.mem_fixU.mpr hu, rfl⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact Subtype.ext hmem
    · exfalso
      apply hσ1
      ext u
      have hmem : (u : G) ∈ W := by rw [htop, ← hVU]; exact u.2
      obtain ⟨u', hu', hu'u⟩ := hmem
      have : u' = u := Subtype.ext hu'u
      rw [← this, MulAut.one_apply, FFt.mem_fixU.mp hu']
  obtain ⟨e⟩ := hhat.2.2
  obtain ⟨r, s, hr4, hr2, hs2, hsr⟩ :=
    FFt.exists_dihedral_lift hhat.2.1 e FFt.r6_pow_four FFt.r6_sq_ne_one FFt.s6_sq FFt.s6_r6
  have hmemA : ∀ q : ModO2 LH, π q ∈ autOn LH V := by
    intro q
    obtain ⟨ℓ, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← Setup.range_rho hLHV, hπmk]
    exact ⟨ℓ, rfl⟩
  have hFF : IsFFModule (autOn LH V) :=
    FFt.isFFModule_of_dihedral hU2 hU64 hσ3 hfree (hσc r) (hσc s)
      (by rw [← map_pow, hr4, map_one])
      (fun h => hr2 (hπinj (by rw [map_pow, h, map_one])))
      (by rw [← map_pow, hs2, map_one])
      (by rw [← map_inv, ← map_mul, ← map_mul, hsr, map_inv]) (hmemA r) (hmemA s)
  refine ⟨hV, B1Red.isFFModule_mono ?_ hFF⟩
  exact T4213N.autOn_le_of_acts c.sup_le_normalizer_V fun a ha =>
    ⟨a, (((perfectCore_le _).trans inf_le_left).trans le_sup_left) ha, fun _ _ => rfl⟩

end Conf4212

end CFSG.Quasithin.H13.Ch4
