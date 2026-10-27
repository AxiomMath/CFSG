module

public import CFSG.Quasithin.Background.CommVBasics
public import CFSG.Quasithin.Background.D2Coprime
public import CFSG.Quasithin.Background.D2Params
public import Mathlib.Data.Rat.Star

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Quasithin

section Coord

variable {H : Type*} [Group H]

structure IsE9 (P : Subgroup H) : Prop where
  comm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a
  pow : ∀ a ∈ P, a ^ 3 = 1
  card : Nat.card P = 9

@[expose] def cd3 (x y : H) (i j : ZMod 3) : H := x ^ i.val * y ^ j.val

theorem pow_mod_three {x : H} (hx : x ^ 3 = 1) (n : ℕ) : x ^ (n % 3) = x ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, hx, one_pow, one_mul]

theorem pow_val_add {x : H} (hx : x ^ 3 = 1) (i i' : ZMod 3) :
    x ^ (i + i').val = x ^ i.val * x ^ i'.val := by
  rw [ZMod.val_add, pow_mod_three hx, pow_add]

variable {x y : H}

theorem cd3_zero : cd3 x y 0 0 = 1 := by simp [cd3]

theorem cd3_one_zero : cd3 x y 1 0 = x := by simp [cd3, ZMod.val_one]

theorem cd3_zero_one : cd3 x y 0 1 = y := by simp [cd3, ZMod.val_one]

theorem cd3_mul (hxy : x * y = y * x) (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (i j i' j' : ZMod 3) :
    cd3 x y i j * cd3 x y i' j' = cd3 x y (i + i') (j + j') := by
  unfold cd3
  rw [pow_val_add hx, pow_val_add hy]
  have h : y ^ j.val * x ^ i'.val = x ^ i'.val * y ^ j.val :=
    ((Commute.pow_pow (show Commute x y from hxy) i'.val j.val).eq).symm
  calc x ^ i.val * y ^ j.val * (x ^ i'.val * y ^ j'.val)
      = x ^ i.val * (y ^ j.val * x ^ i'.val) * y ^ j'.val := by simp only [mul_assoc]
    _ = x ^ i.val * (x ^ i'.val * y ^ j.val) * y ^ j'.val := by rw [h]
    _ = x ^ i.val * x ^ i'.val * (y ^ j.val * y ^ j'.val) := by simp only [mul_assoc]

theorem cd3_pow (hxy : x * y = y * x) (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (i j : ZMod 3)
    (n : ℕ) : cd3 x y i j ^ n = cd3 x y (n * i) (n * j) := by
  induction n with
  | zero => simp [cd3]
  | succ n ih =>
    rw [pow_succ, ih, cd3_mul hxy hx hy]
    congr 1 <;> push_cast <;> ring

theorem cd3_pow_three (hxy : x * y = y * x) (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (i j : ZMod 3) :
    cd3 x y i j ^ 3 = 1 := by
  rw [cd3_pow hxy hx hy]
  have h3 : ((3 : ℕ) : ZMod 3) = 0 := by decide
  rw [h3, zero_mul, zero_mul, cd3_zero]

theorem cd3_inv (hxy : x * y = y * x) (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (i j : ZMod 3) :
    (cd3 x y i j)⁻¹ = cd3 x y (2 * i) (2 * j) := by
  have h : ∀ a : ZMod 3, a + 2 * a = 0 := by decide
  rw [inv_eq_iff_mul_eq_one, cd3_mul hxy hx hy, h, h, cd3_zero]

theorem exists_pow_eq_zpow {g : H} (hg : g ^ 3 = 1) (k : ℤ) : ∃ n : ℕ, n < 3 ∧ g ^ k = g ^ n := by
  set r := k % 3 with hr
  have h2 : 0 ≤ r := Int.emod_nonneg k (by norm_num)
  have h3 : r < 3 := Int.emod_lt_of_pos k (by norm_num)
  have h1 : k = 3 * (k / 3) + r := (Int.mul_ediv_add_emod k 3).symm
  refine ⟨r.toNat, by omega, ?_⟩
  have hg' : g ^ (3 : ℤ) = 1 := by rw [zpow_ofNat]; exact hg
  rw [h1, zpow_add, zpow_mul, hg', one_zpow, one_mul, ← zpow_natCast, Int.toNat_of_nonneg h2]

theorem cd3_eq_one (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hx1 : x ≠ 1)
    (hyx : y ∉ Subgroup.zpowers x) {a b : ZMod 3} (h : cd3 x y a b = 1) : a = 0 ∧ b = 0 := by
  have hy1 : y ≠ 1 := fun h1 => hyx (h1 ▸ Subgroup.one_mem _)
  have hxx : x ^ 2 ≠ 1 := fun h2 => hx1 (by
    calc x = x ^ 3 * (x ^ 2)⁻¹ := by group
      _ = 1 := by rw [hx, h2]; group)
  have hyy : y ^ 2 ≠ 1 := fun h2 => hy1 (by
    calc y = y ^ 3 * (y ^ 2)⁻¹ := by group
      _ = 1 := by rw [hy, h2]; group)
  have hmem : ∀ n : ℤ, x ^ n ∈ Subgroup.zpowers x := fun n => Subgroup.zpow_mem_zpowers x n
  unfold cd3 at h
  fin_cases a <;> fin_cases b <;> simp [ZMod.val] at h ⊢
  · rfl
  all_goals exfalso
  · exact hy1 h
  · exact hyy h
  · exact hx1 h
  · exact hyx (by
      have : y = x⁻¹ := eq_inv_of_mul_eq_one_right h
      rw [this]; exact Subgroup.inv_mem _ (Subgroup.mem_zpowers x))
  · exact hyx (by
      have h1 : y ^ 2 = x⁻¹ := eq_inv_of_mul_eq_one_right h
      have h2 : y = (y ^ 2) ^ 2 := by
        calc y = y ^ 3 * y := by rw [hy, one_mul]
          _ = (y ^ 2) ^ 2 := by group
      rw [h2, h1]
      exact Subgroup.pow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers x)) 2)
  · exact hxx h
  · exact hyx (by
      have : y = (x ^ 2)⁻¹ := eq_inv_of_mul_eq_one_right h
      rw [this]
      exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) 2))
  · exact hyx (by
      have h1 : y ^ 2 = (x ^ 2)⁻¹ := eq_inv_of_mul_eq_one_right h
      have h2 : y = (y ^ 2) ^ 2 := by
        calc y = y ^ 3 * y := by rw [hy, one_mul]
          _ = (y ^ 2) ^ 2 := by group
      rw [h2, h1]
      exact Subgroup.pow_mem _ (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) 2))
        2)

theorem cd3_injective (hxy : x * y = y * x) (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hx1 : x ≠ 1)
    (hyx : y ∉ Subgroup.zpowers x) {i j i' j' : ZMod 3} (h : cd3 x y i j = cd3 x y i' j') :
    i = i' ∧ j = j' := by
  have h2 : ∀ a : ZMod 3, a + 2 * a = 0 := by decide
  have h1 : cd3 x y (i + 2 * i') (j + 2 * j') = 1 := by
    rw [← cd3_mul hxy hx hy, h, cd3_mul hxy hx hy, h2, h2, cd3_zero]
  obtain ⟨ha, hb⟩ := cd3_eq_one hx hy hx1 hyx h1
  have h3 : ∀ a b : ZMod 3, a + 2 * b = 0 → a = b := by decide
  exact ⟨h3 _ _ ha, h3 _ _ hb⟩

theorem IsE9.exists_cd3 {P : Subgroup H} (hP : IsE9 P) (hx : x ∈ P) (hy : y ∈ P) (hx1 : x ≠ 1)
    (hyx : y ∉ Subgroup.zpowers x) : ∀ g ∈ P, ∃ i j : ZMod 3, g = cd3 x y i j := by
  have hxy := hP.comm x hx y hy
  have hx3 := hP.pow x hx
  have hy3 := hP.pow y hy
  have : Finite P := Nat.finite_of_card_ne_zero (by rw [hP.card]; norm_num)
  have hmem : ∀ i j : ZMod 3, cd3 x y i j ∈ P := fun i j =>
    P.mul_mem (P.pow_mem hx _) (P.pow_mem hy _)
  let f : ZMod 3 × ZMod 3 → P := fun ij => ⟨cd3 x y ij.1 ij.2, hmem ij.1 ij.2⟩
  have hf : Function.Injective f := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    obtain ⟨h1, h2⟩ := cd3_injective hxy hx3 hy3 hx1 hyx (congrArg Subtype.val h)
    exact Prod.ext h1 h2
  have hcard : Nat.card P ≤ Nat.card (ZMod 3 × ZMod 3) := by
    rw [hP.card, Nat.card_prod, Nat.card_zmod]
  have hbij := hf.bijective_of_nat_card_le hcard
  intro g hg
  obtain ⟨⟨i, j⟩, hij⟩ := hbij.2 ⟨g, hg⟩
  exact ⟨i, j, (congrArg Subtype.val hij).symm⟩

theorem mem_zpowers_cd3 (hxy : x * y = y * x) (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hx1 : x ≠ 1)
    (hyx : y ∉ Subgroup.zpowers x) {i j a b : ZMod 3} :
    cd3 x y i j ∈ Subgroup.zpowers (cd3 x y a b) ↔ ∃ k : ZMod 3, i = k * a ∧ j = k * b := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    obtain ⟨n, -, hn⟩ := exists_pow_eq_zpow (cd3_pow_three hxy hx hy a b) k
    rw [hn, cd3_pow hxy hx hy] at hk
    obtain ⟨h1, h2⟩ := cd3_injective hxy hx hy hx1 hyx hk
    exact ⟨n, h1.symm, h2.symm⟩
  · rintro ⟨k, rfl, rfl⟩
    have : cd3 x y (k * a) (k * b) = cd3 x y a b ^ k.val := by
      rw [cd3_pow hxy hx hy, ZMod.natCast_zmod_val]
    rw [this]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _

theorem cd3_one_one : cd3 x y 1 1 = x * y := by simp [cd3, ZMod.val_one]

theorem cd3_one_two : cd3 x y 1 2 = x * y * y := by
  have h1 : (1 : ZMod 3).val = 1 := rfl
  have h2 : (2 : ZMod 3).val = 2 := rfl
  rw [cd3, h1, h2, pow_one, pow_two, mul_assoc]

structure IsBasis (P : Subgroup H) (x y : H) : Prop where
  mem_left : x ∈ P
  mem_right : y ∈ P
  ne_one : x ≠ 1
  not_mem : y ∉ Subgroup.zpowers x

theorem zpowers_eq_of_mem_of_mem {g h : H} (hg : g ∈ Subgroup.zpowers h)
    (hh : h ∈ Subgroup.zpowers g) : Subgroup.zpowers g = Subgroup.zpowers h :=
  le_antisymm (Subgroup.zpowers_le.mpr hg) (Subgroup.zpowers_le.mpr hh)

theorem conj_eq_of_mem_zpowers {g d : H} (hg : g ^ 3 = 1) (hd : d ^ 3 = 1) (hd1 : d ≠ 1)
    (h : g * d * g⁻¹ ∈ Subgroup.zpowers d) : g * d * g⁻¹ = d := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
  obtain ⟨n, hn3, hn⟩ := exists_pow_eq_zpow hd k
  rw [hn] at hk
  interval_cases n
  · exfalso
    apply hd1
    rw [pow_zero] at hk
    calc d = g⁻¹ * (g * d * g⁻¹) * g := by group
      _ = 1 := by rw [← hk]; group
  · rw [← hk, pow_one]
  · exfalso
    have h1 : g * d ^ 2 * g⁻¹ = d := by
      rw [← conj_pow, ← hk, ← pow_mul]
      calc d ^ (2 * 2) = d ^ 3 * d := by group
        _ = d := by rw [hd, one_mul]
    have h2 : g ^ 3 * d * (g ^ 3)⁻¹ = d ^ 2 := by
      calc g ^ 3 * d * (g ^ 3)⁻¹ = g * (g * (g * d * g⁻¹) * g⁻¹) * g⁻¹ := by
            rw [pow_three']; group
        _ = d ^ 2 := by rw [← hk, h1, hk]
    rw [hg, one_mul, inv_one, mul_one] at h2
    apply hd1
    calc d = d⁻¹ * d ^ 2 := by group
      _ = 1 := by rw [← h2]; group

theorem conj_cd3 (hxy : x * y = y * x) (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (g : H)
    {s₁ t₁ s₂ t₂ : ZMod 3} (h₁ : g * x * g⁻¹ = cd3 x y s₁ t₁) (h₂ : g * y * g⁻¹ = cd3 x y s₂ t₂)
    (u v : ZMod 3) :
    g * cd3 x y u v * g⁻¹ = cd3 x y (u * s₁ + v * s₂) (u * t₁ + v * t₂) := by
  have hconj : g * cd3 x y u v * g⁻¹ = (g * x * g⁻¹) ^ u.val * (g * y * g⁻¹) ^ v.val := by
    rw [conj_pow, conj_pow, cd3]
    group
  rw [hconj, h₁, h₂, cd3_pow hxy hx hy, cd3_pow hxy hx hy, cd3_mul hxy hx hy,
    ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]

end Coord

section Norm

variable {V : Type*} [CommGroup V]

@[expose] def nrm3 (d : MulAut V) : V →* V where
  toFun v := v * d v * d (d v)
  map_one' := by simp
  map_mul' a b := by simp only [map_mul]; ac_rfl

theorem nrm3_apply (d : MulAut V) (v : V) : nrm3 d v = v * d v * d (d v) := rfl

theorem apply_apply_apply_of_pow_three {d : MulAut V} (hd : d ^ 3 = 1) (v : V) :
    d (d (d v)) = v := by
  have h : (d * d * d) v = v := by rw [← pow_three', hd]; rfl
  rwa [MulAut.mul_apply, MulAut.mul_apply] at h

theorem apply_nrm3 {d : MulAut V} (hd : d ^ 3 = 1) (v : V) : d (nrm3 d v) = nrm3 d v := by
  rw [nrm3_apply, map_mul, map_mul, apply_apply_apply_of_pow_three hd]
  ac_rfl

theorem mul_self_eq_one_of_sq (hV : ∀ v : V, v ^ 2 = 1) (v : V) : v * v = 1 := by
  rw [← pow_two]
  exact hV v

theorem nrm3_of_apply_eq (hV : ∀ v : V, v ^ 2 = 1) {d : MulAut V} {v : V} (h : d v = v) :
    nrm3 d v = v := by
  rw [nrm3_apply, h, h, mul_self_eq_one_of_sq hV v, one_mul]

theorem apply_comm_of_mul_comm {d e : MulAut V} (h : e * d = d * e) (w : V) :
    d (e w) = e (d w) := by
  rw [← MulAut.mul_apply, ← h, MulAut.mul_apply]

theorem nrm3_apply_comm {d e : MulAut V} (h : e * d = d * e) (v : V) :
    nrm3 d (e v) = e (nrm3 d v) := by
  rw [nrm3_apply, nrm3_apply, map_mul, map_mul, apply_comm_of_mul_comm h,
    apply_comm_of_mul_comm h]

private theorem prod_four_triples (v a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ : V) (hv : v * v = 1) :
    v * a₁ * a₂ * (v * a₃ * a₄) * (v * a₅ * a₆) * (v * a₇ * a₈) =
      v * (v * a₁ * a₂ * (a₃ * a₅ * a₈) * (a₄ * a₇ * a₆)) := by
  calc v * a₁ * a₂ * (v * a₃ * a₄) * (v * a₅ * a₆) * (v * a₇ * a₈)
      = (v * v) * (v * v) * (a₁ * a₂ * a₃ * a₄ * a₅ * a₆ * a₇ * a₈) := by ac_rfl
    _ = (v * v) * (a₁ * a₂ * a₃ * a₄ * a₅ * a₆ * a₇ * a₈) := by rw [hv, one_mul, one_mul]
    _ = v * (v * a₁ * a₂ * (a₃ * a₅ * a₈) * (a₄ * a₇ * a₆)) := by ac_rfl

theorem nrm3_identity (hV : ∀ v : V, v ^ 2 = 1) {x y : MulAut V} (hxy : x * y = y * x)
    (hy : y ^ 3 = 1) (v : V) :
    nrm3 x v * nrm3 y v * nrm3 (x * y) v * nrm3 (x * y * y) v = v * nrm3 x (nrm3 y v) := by
  have hc : ∀ w, y (x w) = x (y w) := apply_comm_of_mul_comm hxy
  have hy3 := apply_apply_apply_of_pow_three hy
  simp only [nrm3_apply, MulAut.mul_apply, map_mul, hc, hy3]
  exact prod_four_triples _ _ _ _ _ _ _ _ _ (mul_self_eq_one_of_sq hV v)

end Norm


section Pieces

variable {V : Type*} [CommGroup V] {P : Subgroup (MulAut V)}

@[expose] def piece (P : Subgroup (MulAut V)) (d : MulAut V) : Subgroup V :=
  fixV (Subgroup.zpowers d) ⊓ commV P

theorem mem_piece {d : MulAut V} {v : V} : v ∈ piece P d ↔ d v = v ∧ v ∈ commV P := by
  rw [piece, Subgroup.mem_inf, mem_fixV_zpowers_iff]

theorem pow_apply_eq_self {g : MulAut V} {v : V} (h : g v = v) (n : ℕ) : (g ^ n) v = v := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, MulAut.mul_apply, h, ih]

theorem apply_mem_commV {g : MulAut V} (hg : ∀ h ∈ P, g * h * g⁻¹ ∈ P) {c : V}
    (hc : c ∈ commV P) : g c ∈ commV P :=
  CFSG.Quasithin.commV_apply_mem_of_normalizes hg hc

theorem IsE9.normalizes (_hP : IsE9 P) {g : MulAut V} (hg : g ∈ P) :
    ∀ h ∈ P, g * h * g⁻¹ ∈ P :=
  fun _ hh => P.mul_mem (P.mul_mem hg hh) (P.inv_mem hg)

theorem IsE9.odd_card (hP : IsE9 P) : Odd (Nat.card P) := by rw [hP.card]; decide

theorem IsE9.commV_inf_fixV [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (hP : IsE9 P) :
    commV P ⊓ fixV P = ⊥ := by
  have := (coprime_decomp hP.odd_card hV (W := ⊤) fun _ _ _ _ => Subgroup.mem_top _).2
  rwa [← commV_eq_commSub, top_inf_eq] at this

theorem IsE9.commV_sup_fixV [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (hP : IsE9 P) :
    commV P ⊔ fixV P = ⊤ := by
  have := (coprime_decomp hP.odd_card hV (W := ⊤) fun _ _ _ _ => Subgroup.mem_top _).1
  rwa [← commV_eq_commSub, top_inf_eq] at this

theorem IsE9.mem_fixV_of_isBasis (hP : IsE9 P) {x y : MulAut V} (hb : IsBasis P x y) {v : V}
    (hx : x v = v) (hy : y v = v) : v ∈ fixV P := by
  intro g hg
  obtain ⟨i, j, rfl⟩ := hP.exists_cd3 hb.1 hb.2 hb.3 hb.4 g hg
  rw [cd3, MulAut.mul_apply, pow_apply_eq_self hy, pow_apply_eq_self hx]

theorem IsE9.eq_one_of_isBasis [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (hP : IsE9 P) {x y : MulAut V}
    (hb : IsBasis P x y) {v : V} (hvc : v ∈ commV P) (hx : x v = v) (hy : y v = v) : v = 1 := by
  have h : v ∈ commV P ⊓ fixV P := ⟨hvc, hP.mem_fixV_of_isBasis hb hx hy⟩
  rw [hP.commV_inf_fixV hV] at h
  exact h

theorem nrm3_mem_commV (hP : IsE9 P) {d : MulAut V} (hd : d ∈ P) {u : V} (hu : u ∈ commV P) :
    nrm3 d u ∈ commV P := by
  have h1 := apply_mem_commV (hP.normalizes hd) hu
  have h2 := apply_mem_commV (hP.normalizes hd) h1
  rw [nrm3_apply]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hu h1) h2

theorem nrm3_mem_piece (hP : IsE9 P) {d : MulAut V} (hd : d ∈ P) {u : V} (hu : u ∈ commV P) :
    nrm3 d u ∈ piece P d :=
  mem_piece.mpr ⟨apply_nrm3 (hP.pow d hd) u, nrm3_mem_commV hP hd hu⟩

theorem nrm3_eq_self_of_mem_piece (hV : ∀ v : V, v ^ 2 = 1) {d : MulAut V} {w : V}
    (hw : w ∈ piece P d) : nrm3 d w = w :=
  nrm3_of_apply_eq hV (mem_piece.mp hw).1

theorem nrm3_eq_one_of_mem_piece [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (hP : IsE9 P) {d e : MulAut V}
    (hb : IsBasis P d e) {w : V} (hw : w ∈ piece P e) : nrm3 d w = 1 := by
  obtain ⟨hew, hwc⟩ := mem_piece.mp hw
  refine hP.eq_one_of_isBasis hV hb (nrm3_mem_commV hP hb.1 hwc)
    (apply_nrm3 (hP.pow d hb.1) w) ?_
  rw [← nrm3_apply_comm (hP.comm e hb.2 d hb.1), hew]

theorem piece_inf_piece [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (hP : IsE9 P) {d e : MulAut V}
    (hb : IsBasis P d e) : piece P d ⊓ piece P e = ⊥ := by
  rw [eq_bot_iff]
  rintro w ⟨hw1, hw2⟩
  exact hP.eq_one_of_isBasis hV hb (mem_piece.mp hw1).2 (mem_piece.mp hw1).1 (mem_piece.mp hw2).1

theorem eq_prod_nrm3 [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (hP : IsE9 P) {x y : MulAut V}
    (hb : IsBasis P x y) {u : V} (hu : u ∈ commV P) :
    u = nrm3 x u * nrm3 y u * nrm3 (x * y) u * nrm3 (x * y * y) u := by
  rw [nrm3_identity hV (hP.comm x hb.1 y hb.2) (hP.pow y hb.2)]
  have h1 : nrm3 x (nrm3 y u) = 1 := by
    refine hP.eq_one_of_isBasis hV hb (nrm3_mem_commV hP hb.1 (nrm3_mem_commV hP hb.2 hu))
      (apply_nrm3 (hP.pow x hb.1) _) ?_
    rw [← nrm3_apply_comm (hP.comm y hb.2 x hb.1), apply_nrm3 (hP.pow y hb.2)]
  rw [h1, mul_one]

theorem apply_mem_piece {g : MulAut V} (hg : ∀ h ∈ P, g * h * g⁻¹ ∈ P) {d : MulAut V} {v : V}
    (hv : v ∈ piece P d) : g v ∈ piece P (g * d * g⁻¹) := by
  obtain ⟨h1, h2⟩ := mem_piece.mp hv
  refine mem_piece.mpr ⟨?_, apply_mem_commV hg h2⟩
  simp [MulAut.mul_apply, h1]

theorem piece_eq_of_zpowers_eq {d d' : MulAut V}
    (h : Subgroup.zpowers d = Subgroup.zpowers d') : piece P d = piece P d' := by
  rw [piece, piece, h]

end Pieces

section Lines

variable {H : Type*} [Group H] {P : Subgroup H} {x y : H}

@[expose] def lineGen (x y : H) : Fin 4 → H := ![x, y, x * y, x * y * y]

@[expose] def lineCoord : Fin 4 → ZMod 3 × ZMod 3 := ![(1, 0), (0, 1), (1, 1), (1, 2)]

theorem lineGen_eq_cd3 (x y : H) (i : Fin 4) :
    lineGen x y i = cd3 x y (lineCoord i).1 (lineCoord i).2 := by
  fin_cases i
  · exact cd3_one_zero.symm
  · exact cd3_zero_one.symm
  · exact cd3_one_one.symm
  · exact cd3_one_two.symm

theorem lineGen_mem (hx : x ∈ P) (hy : y ∈ P) (i : Fin 4) : lineGen x y i ∈ P := by
  fin_cases i
  · exact hx
  · exact hy
  · exact P.mul_mem hx hy
  · exact P.mul_mem (P.mul_mem hx hy) hy

theorem IsBasis.lineGen_ne_one (hP : IsE9 P) (hb : IsBasis P x y) (i : Fin 4) :
    lineGen x y i ≠ 1 := by
  intro h
  rw [lineGen_eq_cd3] at h
  have key : ∀ i : Fin 4, ¬ ((lineCoord i).1 = 0 ∧ (lineCoord i).2 = 0) := by decide
  exact key i (cd3_eq_one (hP.pow x hb.1) (hP.pow y hb.2) hb.3 hb.4 h)

theorem IsBasis.lineGen (hP : IsE9 P) (hb : IsBasis P x y) {i j : Fin 4} (hij : i ≠ j) :
    IsBasis P (lineGen x y i) (lineGen x y j) := by
  refine ⟨lineGen_mem hb.1 hb.2 i, lineGen_mem hb.1 hb.2 j, hb.lineGen_ne_one hP i, ?_⟩
  rw [lineGen_eq_cd3, lineGen_eq_cd3, mem_zpowers_cd3 (hP.comm x hb.1 y hb.2) (hP.pow x hb.1)
    (hP.pow y hb.2) hb.3 hb.4]
  have key : ∀ i j : Fin 4, i ≠ j → ¬ ∃ k : ZMod 3,
      (lineCoord j).1 = k * (lineCoord i).1 ∧ (lineCoord j).2 = k * (lineCoord i).2 := by
    decide
  exact key i j hij

theorem IsE9.exists_isBasis (hP : IsE9 P) {d : H} (hd : d ∈ P) (hd1 : d ≠ 1) :
    ∃ e, IsBasis P d e := by
  by_contra hcon
  push Not at hcon
  have hle : P ≤ Subgroup.zpowers d := fun e he => by
    by_contra hne
    exact hcon e ⟨hd, he, hd1, hne⟩
  have heq : P = Subgroup.zpowers d := le_antisymm hle (Subgroup.zpowers_le.mpr hd)
  have h1 := hP.card
  rw [heq, Nat.card_zpowers] at h1
  have h2 : orderOf d ≤ 3 := orderOf_le_of_pow_eq_one (by norm_num) (hP.pow d hd)
  omega

theorem mem_zpowers_symm {a b : H} (hb : b ^ 3 = 1) (ha1 : a ≠ 1)
    (h : a ∈ Subgroup.zpowers b) : b ∈ Subgroup.zpowers a := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
  obtain ⟨n, hn3, hn⟩ := exists_pow_eq_zpow hb k
  rw [hn] at hk
  interval_cases n
  · exact absurd (by rw [← hk, pow_zero]) ha1
  · rw [← hk, pow_one]; exact Subgroup.mem_zpowers b
  · have : b = a ^ 2 := by
      rw [← hk, ← pow_mul]
      calc b = b ^ 3 * b := by rw [hb, one_mul]
        _ = b ^ (2 * 2) := by group
    rw [this]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers a) 2

theorem centralizes_of_normalizes_two (hP : IsE9 P) {g d e : H} (hb : IsBasis P d e)
    (hg : g ^ 3 = 1) (hgd : g * d * g⁻¹ ∈ Subgroup.zpowers d)
    (hge : g * e * g⁻¹ ∈ Subgroup.zpowers e) : ∀ h ∈ P, g * h * g⁻¹ = h := by
  have he1 : e ≠ 1 := fun h1 => hb.4 (h1 ▸ Subgroup.one_mem _)
  have h1 := conj_eq_of_mem_zpowers hg (hP.pow d hb.1) hb.3 hgd
  have h2 := conj_eq_of_mem_zpowers hg (hP.pow e hb.2) he1 hge
  intro h hh
  obtain ⟨i, j, rfl⟩ := hP.exists_cd3 hb.1 hb.2 hb.3 hb.4 h hh
  have : g * cd3 d e i j * g⁻¹ = (g * d * g⁻¹) ^ i.val * (g * e * g⁻¹) ^ j.val := by
    rw [conj_pow, conj_pow, cd3]
    group
  rw [this, h1, h2, cd3]

end Lines

section Involutions

variable {H : Type*} [Group H] {P : Subgroup H}

theorem exists_inverted {a : H} (ha2 : a ^ 2 = 1) (haP : ∀ h ∈ P, a * h * a⁻¹ ∈ P)
    (hact : ∃ h ∈ P, a * h ≠ h * a) : ∃ i ∈ P, i ≠ 1 ∧ a * i * a⁻¹ = i⁻¹ := by
  obtain ⟨h, hh, hne⟩ := hact
  have haa : a * a = 1 := by rw [← pow_two]; exact ha2
  refine ⟨h⁻¹ * (a * h * a⁻¹), P.mul_mem (P.inv_mem hh) (haP h hh), fun h1 => hne ?_, ?_⟩
  · calc a * h = h * (h⁻¹ * (a * h * a⁻¹)) * a := by group
      _ = h * a := by rw [h1, mul_one]
  · calc a * (h⁻¹ * (a * h * a⁻¹)) * a⁻¹ = (a * h * a⁻¹)⁻¹ * ((a * a) * h * (a * a)⁻¹) := by
          group
      _ = (a * h * a⁻¹)⁻¹ * h := by rw [haa]; group
      _ = (h⁻¹ * (a * h * a⁻¹))⁻¹ := by group

theorem exists_fixed (hP : IsE9 P) {a : H} (ha2 : a ^ 2 = 1) (haP : ∀ h ∈ P, a * h * a⁻¹ ∈ P)
    (hninv : ∃ h ∈ P, a * h * a⁻¹ ≠ h⁻¹) : ∃ c ∈ P, c ≠ 1 ∧ a * c * a⁻¹ = c := by
  obtain ⟨h, hh, hne⟩ := hninv
  have haa : a * a = 1 := by rw [← pow_two]; exact ha2
  refine ⟨h * (a * h * a⁻¹), P.mul_mem hh (haP h hh), fun h1 => hne ?_, ?_⟩
  · exact eq_inv_of_mul_eq_one_right h1
  · calc a * (h * (a * h * a⁻¹)) * a⁻¹ = (a * h * a⁻¹) * ((a * a) * h * (a * a)⁻¹) := by group
      _ = (a * h * a⁻¹) * h := by rw [haa]; group
      _ = h * (a * h * a⁻¹) := (hP.comm h hh _ (haP h hh)).symm

theorem isBasis_of_fixed_inverted (hP : IsE9 P) {a c i : H} (hc : c ∈ P) (hi : i ∈ P)
    (hc1 : c ≠ 1) (hi1 : i ≠ 1) (hac : a * c * a⁻¹ = c) (hai : a * i * a⁻¹ = i⁻¹) :
    IsBasis P c i := by
  refine ⟨hc, hi, hc1, fun hmem => hi1 ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hfix : a * i * a⁻¹ = i := by rw [← hk, ← conj_zpow, hac]
  have h2 : i ^ 2 = 1 := by
    rw [pow_two]
    calc i * i = i * (a * i * a⁻¹) := by rw [hfix]
      _ = 1 := by rw [hai, mul_inv_cancel]
  calc i = i ^ 3 * (i ^ 2)⁻¹ := by group
    _ = 1 := by rw [hP.pow i hi, h2]; group

theorem exists_moved (hP : IsE9 P) {b : H} (hb2 : b ^ 2 = 1) (hbP : ∀ h ∈ P, b * h * b⁻¹ ∈ P)
    (hact : ∃ h ∈ P, b * h ≠ h * b) (hninv : ∃ h ∈ P, b * h * b⁻¹ ≠ h⁻¹) :
    ∃ d ∈ P, d ≠ 1 ∧ b * d * b⁻¹ ∉ Subgroup.zpowers d := by
  obtain ⟨i, hi, hi1, hbi⟩ := exists_inverted hb2 hbP hact
  obtain ⟨c, hc, hc1, hbc⟩ := exists_fixed hP hb2 hbP hninv
  have hB := isBasis_of_fixed_inverted hP hc hi hc1 hi1 hbc hbi
  have hci := hP.comm c hc i hi
  have hc3 := hP.pow c hc
  have hi3 := hP.pow i hi
  refine ⟨c * i, P.mul_mem hc hi, ?_, ?_⟩
  · rw [← cd3_one_one (x := c) (y := i)]
    intro h1
    have := (cd3_eq_one hc3 hi3 hc1 hB.4 h1).1
    exact absurd this (by decide)
  · have h1 : b * (c * i) * b⁻¹ = cd3 c i 1 2 := by
      rw [cd3_one_two]
      have hinv : i⁻¹ = i * i := by
        rw [inv_eq_iff_mul_eq_one, ← pow_three]
        exact hi3
      calc b * (c * i) * b⁻¹ = (b * c * b⁻¹) * (b * i * b⁻¹) := by group
        _ = c * i * i := by rw [hbc, hbi, hinv, mul_assoc]
    rw [h1, ← cd3_one_one (x := c) (y := i), mem_zpowers_cd3 hci hc3 hi3 hc1 hB.4]
    decide

theorem inverts_of_commuting_involutions (hP : IsE9 P) {a b : H} (ha2 : a ^ 2 = 1)
    (hab : a * b = b * a) (haP : ∀ h ∈ P, a * h * a⁻¹ ∈ P)
    (hbP : ∀ h ∈ P, b * h * b⁻¹ ∈ P) (hb : ∃ h ∈ P, b * h ≠ h * b)
    (ha : ∃ h ∈ P, a * h ≠ h * a) (habP : ∃ h ∈ P, a * b * h ≠ h * (a * b)) :
    (∀ h ∈ P, a * h * a⁻¹ = h⁻¹) ∨ (∀ h ∈ P, b * h * b⁻¹ = h⁻¹) ∨
      (∀ h ∈ P, a * b * h * (a * b)⁻¹ = h⁻¹) := by
  by_cases hainv : ∀ h ∈ P, a * h * a⁻¹ = h⁻¹
  · exact Or.inl hainv
  push Not at hainv
  obtain ⟨i, hi, hi1, hai⟩ := exists_inverted ha2 haP ha
  obtain ⟨c, hc, hc1, hac⟩ := exists_fixed hP ha2 haP hainv
  have hB := isBasis_of_fixed_inverted hP hc hi hc1 hi1 hac hai
  have hci := hP.comm c hc i hi
  have hc3 := hP.pow c hc
  have hi3 := hP.pow i hi
  have hinvi : i⁻¹ = cd3 c i 0 2 := by
    have := cd3_inv hci hc3 hi3 0 1
    rw [cd3_zero_one] at this
    rw [this, mul_zero, mul_one]
  have hacd : ∀ u v : ZMod 3, a * cd3 c i u v * a⁻¹ = cd3 c i u (2 * v) := by
    intro u v
    have h1 : a * c * a⁻¹ = cd3 c i 1 0 := by rw [hac, cd3_one_zero]
    have h2 : a * i * a⁻¹ = cd3 c i 0 2 := by rw [hai, hinvi]
    rw [conj_cd3 hci hc3 hi3 a h1 h2]
    congr 1 <;> ring
  have hconj : ∀ g : H, a * (b * g * b⁻¹) * a⁻¹ = b * (a * g * a⁻¹) * b⁻¹ := by
    intro g
    calc a * (b * g * b⁻¹) * a⁻¹ = (a * b) * g * (a * b)⁻¹ := by group
      _ = (b * a) * g * (b * a)⁻¹ := by rw [hab]
      _ = b * (a * g * a⁻¹) * b⁻¹ := by group
  obtain ⟨s₁, t₁, hs₁⟩ := hP.exists_cd3 hc hi hc1 hB.4 _ (hbP c hc)
  obtain ⟨s₂, t₂, hs₂⟩ := hP.exists_cd3 hc hi hc1 hB.4 _ (hbP i hi)
  have ht₁ : t₁ = 0 := by
    have h1 : a * (b * c * b⁻¹) * a⁻¹ = b * c * b⁻¹ := by rw [hconj, hac]
    rw [hs₁, hacd] at h1
    have := (cd3_injective hci hc3 hi3 hc1 hB.4 h1).2
    have key : ∀ t : ZMod 3, 2 * t = t → t = 0 := by decide
    exact key t₁ this
  have hs₂0 : s₂ = 0 := by
    have h1 : a * (b * i * b⁻¹) * a⁻¹ = (b * i * b⁻¹)⁻¹ := by
      rw [hconj, hai]; group
    rw [hs₂, hacd, cd3_inv hci hc3 hi3] at h1
    have := (cd3_injective hci hc3 hi3 hc1 hB.4 h1).1
    have key : ∀ s : ZMod 3, s = 2 * s → s = 0 := by decide
    exact key s₂ this
  subst ht₁ hs₂0
  have hs₁0 : s₁ ≠ 0 := by
    rintro rfl
    apply hc1
    have h1 : b * c * b⁻¹ = 1 := by rw [hs₁, cd3_zero]
    calc c = b⁻¹ * (b * c * b⁻¹) * b := by group
      _ = 1 := by rw [h1]; group
  have ht₂0 : t₂ ≠ 0 := by
    rintro rfl
    apply hi1
    have h1 : b * i * b⁻¹ = 1 := by rw [hs₂, cd3_zero]
    calc i = b⁻¹ * (b * i * b⁻¹) * b := by group
      _ = 1 := by rw [h1]; group
  have hbcd : ∀ u v : ZMod 3, b * cd3 c i u v * b⁻¹ = cd3 c i (u * s₁) (v * t₂) := by
    intro u v
    rw [conj_cd3 hci hc3 hi3 b hs₁ hs₂]
    congr 1 <;> ring
  have key : ∀ s t : ZMod 3, s ≠ 0 → t ≠ 0 →
      (s = 1 ∧ t = 1) ∨ (s = 1 ∧ t = 2) ∨ (s = 2 ∧ t = 2) ∨ (s = 2 ∧ t = 1) := by decide
  rcases key s₁ t₂ hs₁0 ht₂0 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  ·
    exfalso
    obtain ⟨h, hh, hne⟩ := hb
    obtain ⟨u, v, rfl⟩ := hP.exists_cd3 hc hi hc1 hB.4 h hh
    apply hne
    have := hbcd u v
    rw [mul_one, mul_one] at this
    calc b * cd3 c i u v = (b * cd3 c i u v * b⁻¹) * b := by group
      _ = cd3 c i u v * b := by rw [this]
  ·
    exfalso
    obtain ⟨h, hh, hne⟩ := habP
    obtain ⟨u, v, rfl⟩ := hP.exists_cd3 hc hi hc1 hB.4 h hh
    apply hne
    have : a * b * cd3 c i u v * (a * b)⁻¹ = cd3 c i u v := by
      calc a * b * cd3 c i u v * (a * b)⁻¹ = a * (b * cd3 c i u v * b⁻¹) * a⁻¹ := by group
        _ = cd3 c i u v := by
          rw [hbcd, hacd]
          congr 1 <;> ring_nf
          · have key : ∀ v : ZMod 3, v * 4 = v := by decide
            exact key v
    calc a * b * cd3 c i u v = (a * b * cd3 c i u v * (a * b)⁻¹) * (a * b) := by group
      _ = cd3 c i u v * (a * b) := by rw [this]
  ·
    refine Or.inr (Or.inl fun h hh => ?_)
    obtain ⟨u, v, rfl⟩ := hP.exists_cd3 hc hi hc1 hB.4 h hh
    rw [hbcd, cd3_inv hci hc3 hi3]
    congr 1 <;> ring
  ·
    refine Or.inr (Or.inr fun h hh => ?_)
    obtain ⟨u, v, rfl⟩ := hP.exists_cd3 hc hi hc1 hB.4 h hh
    calc a * b * cd3 c i u v * (a * b)⁻¹ = a * (b * cd3 c i u v * b⁻¹) * a⁻¹ := by group
      _ = (cd3 c i u v)⁻¹ := by
        rw [hbcd, hacd, cd3_inv hci hc3 hi3]
        congr 1 <;> ring

end Involutions

section Pieces2

variable {V : Type*} [CommGroup V] [Finite V] {P : Subgroup (MulAut V)}

theorem iSupIndep_piece (hV : ∀ v : V, v ^ 2 = 1) (hP : IsE9 P) {x y : MulAut V}
    (hb : IsBasis P x y) : iSupIndep (fun i : Fin 4 => piece P (lineGen x y i)) := by
  rw [iSupIndep_def]
  intro i
  rw [disjoint_iff, eq_bot_iff]
  rintro w ⟨hw1, hw2⟩
  have hle : (⨆ j, ⨆ (_ : j ≠ i), piece P (lineGen x y j)) ≤ (nrm3 (lineGen x y i)).ker :=
    iSup₂_le fun j hj w hw => nrm3_eq_one_of_mem_piece hV hP (hb.lineGen hP (Ne.symm hj)) hw
  rw [Subgroup.mem_bot, ← nrm3_eq_self_of_mem_piece hV hw1]
  exact hle hw2

theorem eq_prod_nrm3_lineGen (hV : ∀ v : V, v ^ 2 = 1) (hP : IsE9 P) {x y : MulAut V}
    (hb : IsBasis P x y) {u : V} (hu : u ∈ commV P) :
    u = nrm3 (lineGen x y 0) u * nrm3 (lineGen x y 1) u * nrm3 (lineGen x y 2) u *
      nrm3 (lineGen x y 3) u := by
  simpa [lineGen] using eq_prod_nrm3 hV hP hb hu

theorem false_of_three_pieces_bot (hV : ∀ v : V, v ^ 2 = 1) (hP : IsE9 P) {x y : MulAut V}
    (hb : IsBasis P x y) (i : Fin 4) (h : ∀ j, j ≠ i → piece P (lineGen x y j) = ⊥) : False := by
  set d := lineGen x y i with hd
  have hdP : d ∈ P := lineGen_mem hb.1 hb.2 i
  have hfac : ∀ u ∈ commV P, ∀ j, j ≠ i → nrm3 (lineGen x y j) u = 1 := fun u hu j hj => by
    have := nrm3_mem_piece hP (lineGen_mem hb.1 hb.2 j) hu
    rw [h j hj] at this
    exact this
  have hcomm : ∀ u ∈ commV P, d u = u := by
    intro u hu
    have hu' : u = nrm3 d u := by
      have e := eq_prod_nrm3_lineGen hV hP hb hu
      fin_cases i
      · rwa [hfac u hu 1 (by decide), hfac u hu 2 (by decide), hfac u hu 3 (by decide),
          mul_one, mul_one, mul_one] at e
      · rwa [hfac u hu 0 (by decide), hfac u hu 2 (by decide), hfac u hu 3 (by decide),
          one_mul, mul_one, mul_one] at e
      · rwa [hfac u hu 0 (by decide), hfac u hu 1 (by decide), hfac u hu 3 (by decide),
          one_mul, one_mul, mul_one] at e
      · rwa [hfac u hu 0 (by decide), hfac u hu 1 (by decide), hfac u hu 2 (by decide),
          one_mul, one_mul, one_mul] at e
    rw [hu']
    exact apply_nrm3 (hP.pow d hdP) u
  apply hb.lineGen_ne_one hP i
  ext v
  have hv : v ∈ commV P ⊔ fixV P := by rw [hP.commV_sup_fixV hV]; exact Subgroup.mem_top v
  obtain ⟨a, ha, b, hb', rfl⟩ := Subgroup.mem_sup.mp hv
  rw [MulAut.one_apply, map_mul, hcomm a ha, hb' d hdP]

theorem two_le_rk_piece (hV : ∀ v : V, v ^ 2 = 1) (hP : IsE9 P) {d : MulAut V} (hd : d ∈ P)
    (hd1 : d ≠ 1) (hne : piece P d ≠ ⊥) : 2 ≤ rk (piece P d) := by
  obtain ⟨e, hb⟩ := hP.exists_isBasis hd hd1
  obtain ⟨⟨w, hw⟩, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have hw1' : w ≠ 1 := fun h => hw1 (Subtype.ext h)
  obtain ⟨hdw, hwc⟩ := mem_piece.mp hw
  have hew : e w ∈ piece P d := by
    refine mem_piece.mpr ⟨?_, apply_mem_commV (hP.normalizes hb.2) hwc⟩
    rw [apply_comm_of_mul_comm (hP.comm e hb.2 d hb.1), hdw]
  have hne' : e w ≠ w := fun h => hw1' (hP.eq_one_of_isBasis hV hb hwc hdw h)
  have hw2 : w ^ 2 = 1 := hV w
  have hord : orderOf w = 2 := orderOf_eq_prime hw2 hw1'
  have hlt : Subgroup.zpowers w < piece P d := by
    refine lt_of_le_of_ne (Subgroup.zpowers_le.mpr hw) fun heq => ?_
    have hmem : e w ∈ Subgroup.zpowers w := heq ▸ hew
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · have : e w = 1 := by
        rw [← hk, ← two_mul, zpow_mul, show ((2 : ℤ)) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast,
          hw2, one_zpow]
      exact hw1' (e.injective (this.trans (map_one e).symm))
    · have : e w = w := by
        rw [← hk, zpow_add, zpow_mul, show ((2 : ℤ)) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast,
          hw2, one_zpow, one_mul, zpow_one]
      exact hne' this
  have hrk1 : rk (Subgroup.zpowers w) = 1 := by
    rw [rk, Nat.card_zpowers, hord]
    simp
  by_contra hlt2
  have hle : rk (piece P d) ≤ rk (Subgroup.zpowers w) := by omega
  exact hlt.ne (eq_of_le_of_rk_le hV hlt.le hle)

omit [Finite V] in
theorem piece_conj_eq_bot {K : Subgroup (MulAut V)} (hKP : ∀ k ∈ K, ∀ h ∈ P, k * h * k⁻¹ ∈ P)
    {k : MulAut V} (hk : k ∈ K) {d : MulAut V} (h : piece P d = ⊥) :
    piece P (k * d * k⁻¹) = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  have h1 := apply_mem_piece (hKP k⁻¹ (K.inv_mem hk)) hv
  have h2 : k⁻¹ * (k * d * k⁻¹) * k⁻¹⁻¹ = d := by group
  rw [h2, h] at h1
  have h3 : k⁻¹ v = 1 := h1
  rw [Subgroup.mem_bot]
  calc v = k (k⁻¹ v) := by simp
    _ = 1 := by rw [h3, map_one]

theorem piece_ne_bot (hV : ∀ v : V, v ^ 2 = 1) (hP : IsE9 P) {K : Subgroup (MulAut V)}
    (hKP : ∀ k ∈ K, ∀ h ∈ P, k * h * k⁻¹ ∈ P) {x₀ : MulAut V} (hx₀K : x₀ ∈ K)
    (hx₀3 : x₀ ^ 3 = 1) (hx₀P : ∃ h ∈ P, x₀ * h ≠ h * x₀)
    (hirr : ∀ d ∈ P, d ≠ 1 → ∃ k ∈ K, k * d * k⁻¹ ∉ Subgroup.zpowers d)
    {d : MulAut V} (hd : d ∈ P) (hd1 : d ≠ 1) : piece P d ≠ ⊥ := by
  intro h0
  have hx₀n := hKP x₀ hx₀K
  have hcent : ∀ {d e : MulAut V}, IsBasis P d e → x₀ * d * x₀⁻¹ ∈ Subgroup.zpowers d →
      x₀ * e * x₀⁻¹ ∈ Subgroup.zpowers e → False := by
    intro d e hb h1 h2
    obtain ⟨g, hg, hne⟩ := hx₀P
    have := centralizes_of_normalizes_two hP hb hx₀3 h1 h2 g hg
    exact hne (by
      calc x₀ * g = (x₀ * g * x₀⁻¹) * x₀ := by group
        _ = g * x₀ := by rw [this])
  have hconj1 : ∀ g ∈ P, g ≠ 1 → ∀ k : MulAut V, k * g * k⁻¹ ≠ 1 := by
    intro g _ hg1 k h
    apply hg1
    calc g = k⁻¹ * (k * g * k⁻¹) * k := by group
      _ = 1 := by rw [h]; group
  obtain ⟨d₀, hd₀, hd₀1, h₀, hx⟩ : ∃ d₀ ∈ P, d₀ ≠ 1 ∧ piece P d₀ = ⊥ ∧
      x₀ * d₀ * x₀⁻¹ ∉ Subgroup.zpowers d₀ := by
    by_cases hx : x₀ * d * x₀⁻¹ ∈ Subgroup.zpowers d
    · obtain ⟨k, hk, hkd⟩ := hirr d hd hd1
      refine ⟨k * d * k⁻¹, hKP k hk d hd, hconj1 d hd hd1 k, piece_conj_eq_bot hKP hk h0,
        fun hx' => ?_⟩
      exact hcent ⟨hd, hKP k hk d hd, hd1, hkd⟩ hx hx'
    · exact ⟨d, hd, hd1, h0, hx⟩
  set d₁ := x₀ * d₀ * x₀⁻¹ with hd₁def
  set d₂ := x₀ * d₁ * x₀⁻¹ with hd₂def
  have hd₁ : d₁ ∈ P := hx₀n d₀ hd₀
  have hd₂ : d₂ ∈ P := hx₀n d₁ hd₁
  have h₁ : piece P d₁ = ⊥ := piece_conj_eq_bot hKP hx₀K h₀
  have h₂ : piece P d₂ = ⊥ := piece_conj_eq_bot hKP hx₀K h₁
  have hb : IsBasis P d₀ d₁ := ⟨hd₀, hd₁, hd₀1, hx⟩
  have hd₁1 : d₁ ≠ 1 := hconj1 d₀ hd₀ hd₀1 x₀
  have hd₂1 : d₂ ∉ Subgroup.zpowers d₁ := by
    intro hmem
    apply hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have : x₀ * (d₀ ^ k) * x₀⁻¹ = x₀ * d₁ * x₀⁻¹ := by
      rw [hd₂def] at hk
      rw [← hk, hd₁def, ← conj_zpow]
    have h' := mul_left_cancel (mul_right_cancel this)
    rw [h']
  have hd₂0 : d₂ ∉ Subgroup.zpowers d₀ := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hx3 : x₀ * d₂ * x₀⁻¹ = d₀ := by
      rw [hd₂def, hd₁def]
      calc x₀ * (x₀ * (x₀ * d₀ * x₀⁻¹) * x₀⁻¹) * x₀⁻¹ = x₀ ^ 3 * d₀ * (x₀ ^ 3)⁻¹ := by
            rw [pow_three']; group
        _ = d₀ := by rw [hx₀3]; group
    have : d₀ = d₁ ^ k := by
      rw [← hx3, ← hk, hd₁def, conj_zpow]
    have hmem' : d₀ ∈ Subgroup.zpowers d₁ := Subgroup.mem_zpowers_iff.mpr ⟨k, this.symm⟩
    exact hx (mem_zpowers_symm (hP.pow d₁ hd₁) hd₀1 hmem')
  have hxy := hP.comm d₀ hd₀ d₁ hd₁
  have hx3 := hP.pow d₀ hd₀
  have hy3 := hP.pow d₁ hd₁
  obtain ⟨i, j, hij⟩ := hP.exists_cd3 hd₀ hd₁ hd₀1 hx d₂ hd₂
  have hzp : ∀ {a b : ZMod 3}, (∃ k : ZMod 3, i = k * a ∧ j = k * b) →
      (∃ k : ZMod 3, a = k * i ∧ b = k * j) → piece P (cd3 d₀ d₁ a b) = ⊥ := by
    intro a b h1 h2
    rw [← h₂, piece_eq_of_zpowers_eq (zpowers_eq_of_mem_of_mem _ _)]
    · rw [hij]; exact (mem_zpowers_cd3 hxy hx3 hy3 hd₀1 hx).mpr h2
    · rw [hij]; exact (mem_zpowers_cd3 hxy hx3 hy3 hd₀1 hx).mpr h1
  have hi0 : i ≠ 0 := by
    rintro rfl
    apply hd₂1
    rw [hij, ← cd3_zero_one (x := d₀) (y := d₁)]
    exact (mem_zpowers_cd3 hxy hx3 hy3 hd₀1 hx).mpr ⟨j, by ring, by ring⟩
  have hj0 : j ≠ 0 := by
    rintro rfl
    apply hd₂0
    rw [hij, ← cd3_one_zero (x := d₀) (y := d₁)]
    exact (mem_zpowers_cd3 hxy hx3 hy3 hd₀1 hx).mpr ⟨i, by ring, by ring⟩
  have key : ∀ i j : ZMod 3, i ≠ 0 → j ≠ 0 →
      ((∃ k : ZMod 3, i = k * 1 ∧ j = k * 1) ∧ (∃ k : ZMod 3, (1 : ZMod 3) = k * i ∧
        (1 : ZMod 3) = k * j)) ∨
      ((∃ k : ZMod 3, i = k * 1 ∧ j = k * 2) ∧ (∃ k : ZMod 3, (1 : ZMod 3) = k * i ∧
        (2 : ZMod 3) = k * j)) := by decide
  have hpieces : ∀ m : Fin 4, m ≠ 2 → m ≠ 3 → piece P (lineGen d₀ d₁ m) = ⊥ := by
    intro m h2 h3
    fin_cases m
    · exact h₀
    · exact h₁
    · exact absurd rfl h2
    · exact absurd rfl h3
  rcases key i j hi0 hj0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have h3 : piece P (lineGen d₀ d₁ 2) = ⊥ := by
      rw [lineGen_eq_cd3]; exact hzp h1 h2
    refine false_of_three_pieces_bot hV hP hb 3 fun m hm => ?_
    by_cases hm2 : m = 2
    · rw [hm2]; exact h3
    · exact hpieces m hm2 hm
  · have h3 : piece P (lineGen d₀ d₁ 3) = ⊥ := by
      rw [lineGen_eq_cd3]; exact hzp h1 h2
    refine false_of_three_pieces_bot hV hP hb 2 fun m hm => ?_
    by_cases hm3 : m = 3
    · rw [hm3]; exact h3
    · exact hpieces m hm hm3


theorem zpow_eq_one_or_self {H : Type*} [Group H] {a : H} (ha2 : a ^ 2 = 1) (k : ℤ) :
    a ^ k = 1 ∨ a ^ k = a := by
  rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · left
    rw [← two_mul, zpow_mul, show ((2 : ℤ)) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, ha2, one_zpow]
  · right
    rw [zpow_add, zpow_mul, show ((2 : ℤ)) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, ha2,
      one_zpow, one_mul, zpow_one]

theorem three_le_rkIdx_of_involution (hV : ∀ v : V, v ^ 2 = 1) (hP : IsE9 P)
    (hne : ∀ d ∈ P, d ≠ 1 → piece P d ≠ ⊥) {a : MulAut V} (ha2 : a ^ 2 = 1)
    (haP : ∀ h ∈ P, a * h * a⁻¹ ∈ P) (hact : ∃ h ∈ P, a * h ≠ h * a) :
    3 ≤ rkIdx (fixV (Subgroup.zpowers a)) := by
  obtain ⟨d, hd, hd1, had⟩ := exists_inverted ha2 haP hact
  obtain ⟨e, hb⟩ := hP.exists_isBasis hd hd1
  have hd3 := hP.pow d hd
  set s : Finset (Fin 4) := {1, 2, 3} with hs
  set U : Subgroup V := ⨆ i ∈ s, piece P (lineGen d e i) with hU
  have hrk6 : 6 ≤ rk U := by
    rw [hU, rk_iSup_biSup_eq_sum _ (iSupIndep_piece hV hP hb) s, hs,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    have h : ∀ i, 2 ≤ rk (piece P (lineGen d e i)) := fun i =>
      two_le_rk_piece hV hP (lineGen_mem hb.1 hb.2 i) (hb.lineGen_ne_one hP i)
        (hne _ (lineGen_mem hb.1 hb.2 i) (hb.lineGen_ne_one hP i))
    have := h 1
    have := h 2
    have := h 3
    omega
  have hgen0 : lineGen d e 0 = d := rfl
  have hUker : U ≤ (nrm3 d).ker := by
    refine iSup₂_le fun i hi w hw => ?_
    have hi0 : (0 : Fin 4) ≠ i := by
      rw [hs] at hi
      fin_cases i <;> simp_all
    have := nrm3_eq_one_of_mem_piece hV hP (hb.lineGen hP hi0) hw
    rwa [hgen0] at this
  have hUd : ∀ u ∈ U, d u ∈ U := by
    have hle : U ≤ U.comap (d : MulAut V).toMonoidHom := by
      refine iSup₂_le fun i hi w hw => ?_
      have h1 := apply_mem_piece (hP.normalizes hd) hw
      have h2 : d * lineGen d e i * d⁻¹ = lineGen d e i := by
        rw [hP.comm d hd _ (lineGen_mem hb.1 hb.2 i)]
        group
      rw [h2] at h1
      exact (le_iSup₂ (f := fun i (_ : i ∈ s) => piece P (lineGen d e i)) i hi) h1
    exact fun u hu => hle hu
  have hUfix : ∀ u ∈ U, d u = u → u = 1 := fun u hu hdu => by
    rw [← nrm3_of_apply_eq hV hdu]
    exact hUker hu
  set C : Subgroup V := U ⊓ fixV (Subgroup.zpowers a) with hC
  let f : C × C → U := fun p => ⟨(p.1 : V) * d p.2, U.mul_mem p.1.2.1 (hUd _ p.2.2.1)⟩
  have hinj : Function.Injective f := by
    rintro ⟨⟨u₁, hu₁⟩, ⟨u₁', hu₁'⟩⟩ ⟨⟨u₂, hu₂⟩, ⟨u₂', hu₂'⟩⟩ h
    simp only [f, Subtype.mk.injEq] at h
    set t := u₂' * u₁'⁻¹ with ht
    have htC : t ∈ C := C.mul_mem hu₂' (C.inv_mem hu₁')
    have hs' : u₁ * u₂⁻¹ = d t := by
      rw [ht, map_mul, map_inv]
      calc u₁ * u₂⁻¹ = (u₁ * d u₁') * (d u₁')⁻¹ * u₂⁻¹ := by group
        _ = (u₂ * d u₂') * (d u₁')⁻¹ * u₂⁻¹ := by rw [h]
        _ = d u₂' * (d u₁')⁻¹ := by
          calc (u₂ * d u₂') * (d u₁')⁻¹ * u₂⁻¹ = d u₂' * (d u₁')⁻¹ * (u₂ * u₂⁻¹) := by ac_rfl
            _ = d u₂' * (d u₁')⁻¹ := by rw [mul_inv_cancel, mul_one]
    have hsC : u₁ * u₂⁻¹ ∈ C := C.mul_mem hu₁ (C.inv_mem hu₂)
    have hat : a t = t := (mem_fixV_zpowers_iff).mp htC.2
    have has : a (u₁ * u₂⁻¹) = u₁ * u₂⁻¹ := (mem_fixV_zpowers_iff).mp hsC.2
    have hdt : d t = d⁻¹ t := by
      have h1 : a (d t) = d⁻¹ (a t) := by
        rw [← MulAut.mul_apply, ← MulAut.mul_apply]
        congr 1
        calc a * d = (a * d * a⁻¹) * a := by group
          _ = d⁻¹ * a := by rw [had]
      rw [hat, ← hs', has] at h1
      rw [← hs', h1]
    have hdt' : d t = t := by
      have h1 : d (d t) = t := by rw [hdt]; simp
      calc d t = d (d (d t)) := by rw [h1]
        _ = t := apply_apply_apply_of_pow_three hd3 t
    have ht1 : t = 1 := hUfix t htC.1 hdt'
    have hs1 : u₁ * u₂⁻¹ = 1 := by rw [hs', ht1, map_one]
    have e1 : u₁ = u₂ := mul_inv_eq_one.mp hs1
    have e2 : u₂' = u₁' := mul_inv_eq_one.mp ht1
    subst e1 e2
    rfl
  have hcard := Nat.card_le_card_of_injective f hinj
  rw [Nat.card_prod, card_eq_two_pow hV C, card_eq_two_pow hV U, ← pow_add] at hcard
  have h2C : rk C + rk C ≤ rk U := (Nat.pow_le_pow_iff_right (by norm_num)).mp hcard
  have h1 := rk_add_rkIdx (fixV (Subgroup.zpowers a))
  have h2 := rk_sup_add_rk_inf U (fixV (Subgroup.zpowers a))
  have h3 : rk ↥(U ⊔ fixV (Subgroup.zpowers a)) ≤ rk V :=
    (rk_mono le_top).trans (rk_top (G := V)).le
  rw [← hC] at h2
  omega


theorem IsE9.exists_ne_one {H : Type*} [Group H] {Q : Subgroup H} (hQ : IsE9 Q) :
    ∃ x ∈ Q, x ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hQ1 : Q = ⊥ := (Subgroup.eq_bot_iff_forall Q).mpr hcon
  have := hQ.card
  rw [hQ1, Subgroup.card_bot] at this
  omega

theorem four_le_rkIdx_of_inverting (hV : ∀ v : V, v ^ 2 = 1) (hP : IsE9 P)
    (hne : ∀ d ∈ P, d ≠ 1 → piece P d ≠ ⊥) {c : MulAut V} (hc2 : c ^ 2 = 1)
    (hcinv : ∀ h ∈ P, c * h * c⁻¹ = h⁻¹) : 4 ≤ rkIdx (fixV (Subgroup.zpowers c)) := by
  obtain ⟨x, hx, hx1⟩ := hP.exists_ne_one
  obtain ⟨y, hb⟩ := hP.exists_isBasis hx hx1
  have hcP : ∀ h ∈ P, c * h * c⁻¹ ∈ P := fun h hh => by rw [hcinv h hh]; exact P.inv_mem hh
  have hcpiece : ∀ g ∈ P, ∀ w ∈ piece P g, c w ∈ piece P g := by
    intro g hg w hw
    have := apply_mem_piece hcP hw
    rwa [hcinv g hg, piece_eq_of_zpowers_eq (Subgroup.zpowers_inv (g := g))] at this
  have hinv_piece : ∀ g ∈ P, ∀ k ∈ Subgroup.zpowers c, ∀ w ∈ piece P g, k w ∈ piece P g := by
    intro g hg k hk w hw
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
    rcases zpow_eq_one_or_self hc2 n with h | h
    · rw [h]; exact hw
    · rw [h]; exact hcpiece g hg w hw
  set T : Fin 4 → Subgroup V := fun i => commSub (piece P (lineGen x y i)) (Subgroup.zpowers c)
    with hT
  have hTle : ∀ i, T i ≤ piece P (lineGen x y i) := fun i =>
    commSub_le_of_invariant (hinv_piece _ (lineGen_mem hb.1 hb.2 i))
  have hTne : ∀ i, T i ≠ ⊥ := by
    intro i hTi
    set g := lineGen x y i
    have hg := lineGen_mem hb.1 hb.2 i
    have hg1 : g ≠ 1 := hb.lineGen_ne_one hP i
    apply hne g hg hg1
    have hfix : piece P g ≤ fixV (Subgroup.zpowers c) := commSub_eq_bot_iff.mp hTi
    obtain ⟨e, hge⟩ := hP.exists_isBasis hg hg1
    rw [eq_bot_iff]
    intro w hw
    have hew : e w ∈ piece P g := by
      have := apply_mem_piece (hP.normalizes hge.2) hw
      have h2 : e * g * e⁻¹ = g := by rw [hP.comm e hge.2 g hg]; group
      rwa [h2] at this
    have h1 : c (e w) = e w := mem_fixV_zpowers_iff.mp (hfix hew)
    have h2 : c w = w := mem_fixV_zpowers_iff.mp (hfix hw)
    have hce : c * e = e⁻¹ * c := by
      calc c * e = (c * e * c⁻¹) * c := by group
        _ = e⁻¹ * c := by rw [hcinv e hge.2]
    have h3 : c (e w) = e⁻¹ w := by
      calc c (e w) = (c * e) w := rfl
        _ = (e⁻¹ * c) w := by rw [hce]
        _ = e⁻¹ (c w) := rfl
        _ = e⁻¹ w := by rw [h2]
    have h4 : e w = w := by
      have h5 : e (e w) = w := by rw [← h1, h3]; simp
      calc e w = e (e (e w)) := by rw [h5]
        _ = w := apply_apply_apply_of_pow_three (hP.pow e hge.2) w
    exact hP.eq_one_of_isBasis hV hge (mem_piece.mp hw).2 (mem_piece.mp hw).1 h4
  have hindep : iSupIndep T := (iSupIndep_piece hV hP hb).mono hTle
  have hsum := rk_iSup_biSup_eq_sum T hindep Finset.univ
  have hge1 : ∀ i, 1 ≤ rk (T i) := fun i => by
    by_contra h
    exact hTne i ((rk_eq_zero_iff hV).mp (by omega))
  have hle : (⨆ i ∈ (Finset.univ : Finset (Fin 4)), T i) ≤ commV (Subgroup.zpowers c) := by
    rw [commV_eq_commSub]
    exact iSup₂_le fun i _ => commSub_mono le_top le_rfl
  have h4 : 4 ≤ ∑ i : Fin 4, rk (T i) := by
    rw [Fin.sum_univ_four]
    have := hge1 0
    have := hge1 1
    have := hge1 2
    have := hge1 3
    omega
  rw [rkIdx_fixV_zpowers]
  exact h4.trans (hsum ▸ rk_mono hle)

theorem five_le_rkIdx_of_pair (hV : ∀ v : V, v ^ 2 = 1) (hP : IsE9 P)
    (hne : ∀ d ∈ P, d ≠ 1 → piece P d ≠ ⊥) {A : Subgroup (MulAut V)} {c b : MulAut V}
    (hcA : c ∈ A) (hbA : b ∈ A) (hc2 : c ^ 2 = 1) (hb2 : b ^ 2 = 1)
    (hcinv : ∀ h ∈ P, c * h * c⁻¹ = h⁻¹) (hbP : ∀ h ∈ P, b * h * b⁻¹ ∈ P)
    (hbact : ∃ h ∈ P, b * h ≠ h * b) (hbinv : ∃ h ∈ P, b * h * b⁻¹ ≠ h⁻¹) :
    5 ≤ rkIdx (fixV A) := by
  have h4 := four_le_rkIdx_of_inverting hV hP hne hc2 hcinv
  obtain ⟨d, hd, hd1, hbd⟩ := exists_moved hP hb2 hbP hbact hbinv
  have hcP : ∀ h ∈ P, c * h * c⁻¹ ∈ P := fun h hh => by rw [hcinv h hh]; exact P.inv_mem hh
  obtain ⟨⟨w₀, hw₀⟩, hw₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp (hne d hd hd1)
  have hw₀1' : w₀ ≠ 1 := fun h => hw₀1 (Subtype.ext h)
  have hcw₀ : c w₀ ∈ piece P d := by
    have := apply_mem_piece hcP hw₀
    rwa [hcinv d hd, piece_eq_of_zpowers_eq (Subgroup.zpowers_inv (g := d))] at this
  obtain ⟨w, hw, hw1, hcw⟩ : ∃ w ∈ piece P d, w ≠ 1 ∧ c w = w := by
    by_cases h : c w₀ = w₀
    · exact ⟨w₀, hw₀, hw₀1', h⟩
    · refine ⟨w₀ * c w₀, (piece P d).mul_mem hw₀ hcw₀, fun h1 => h ?_, ?_⟩
      · have := eq_inv_of_mul_eq_one_right h1
        rw [this]
        exact (eq_inv_of_mul_eq_one_left (mul_self_eq_one_of_sq hV w₀)).symm
      · have hcc : c (c w₀) = w₀ := by
          rw [← MulAut.mul_apply, ← pow_two, hc2]
          rfl
        rw [map_mul, hcc, mul_comm]
  have hBasis : IsBasis P d (b * d * b⁻¹) := ⟨hd, hbP d hd, hd1, hbd⟩
  have hbw : b w ≠ w := by
    intro h
    have h1 := apply_mem_piece hbP hw
    rw [h] at h1
    have h2 : w ∈ piece P d ⊓ piece P (b * d * b⁻¹) := ⟨hw, h1⟩
    rw [piece_inf_piece hV hP hBasis] at h2
    exact hw1 h2
  have hle : fixV A ≤ fixV (Subgroup.zpowers c) := fun v hv g hg =>
    hv g (Subgroup.zpowers_le.mpr hcA hg)
  have hlt : rk (fixV A) < rk (fixV (Subgroup.zpowers c)) := by
    by_contra hge
    have heq := eq_of_le_of_rk_le hV hle (by omega)
    have hwA : w ∈ fixV A := by
      rw [heq]
      exact mem_fixV_zpowers_iff.mpr hcw
    exact hbw (hwA b hbA)
  have h1 := rk_add_rkIdx (fixV A)
  have h2 := rk_add_rkIdx (fixV (Subgroup.zpowers c))
  omega


theorem exists_mem_notMem_finset {G : Type*} [Group G] {A : Subgroup G} [Finite A]
    (S : Finset G) (h : S.card < Nat.card A) : ∃ g ∈ A, g ∉ S := by
  by_contra hcon
  push Not at hcon
  have hsub : (A : Set G) ⊆ (S : Set G) := fun g hg => hcon g hg
  have h1 := Nat.card_mono S.finite_toSet hsub
  simp only [Nat.card_coe_set_eq, Set.ncard_coe_finset] at h1
  have h2 : Nat.card A = (A : Set G).ncard := Nat.card_coe_set_eq _
  omega

theorem rk_le_two_of_isA2 (hP : IsE9 P) {K : Subgroup (MulAut V)}
    (hKP : ∀ k ∈ K, ∀ h ∈ P, k * h * k⁻¹ ∈ P)
    (hinv : ∀ a ∈ K, a ^ 2 = 1 → a ≠ 1 → ∃ h ∈ P, a * h ≠ h * a)
    {A : Subgroup (MulAut V)} (hA : IsA2 K A) : rk A ≤ 2 := by
  classical
  by_contra hrk
  push Not at hrk
  have hAel := hA.isElemAbelian2
  have hcard : 8 ≤ Nat.card A := by
    rw [card_eq_two_pow_of_isPGroup hAel.isPGroup]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ rk A := Nat.pow_le_pow_right (by norm_num) hrk
  have hsq : ∀ g ∈ A, g ^ 2 = 1 := hAel.2
  have hinvself : ∀ g ∈ A, g⁻¹ = g := fun g hg =>
    inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hsq g hg)
  have hcomm : ∀ g ∈ A, ∀ g' ∈ A, g * g' = g' * g := hAel.1
  have hAK : A ≤ K := hA.le
  have hact : ∀ g ∈ A, g ≠ 1 → ∃ h ∈ P, g * h ≠ h * g := fun g hg hg1 =>
    hinv g (hAK hg) (hsq g hg) hg1
  have hprod1 : ∀ g ∈ A, ∀ g' ∈ A, g ≠ g' → g * g' ≠ 1 := fun g hg g' hg' hne h =>
    hne (by rw [← hinvself g hg]; exact (eq_inv_of_mul_eq_one_right h).symm)
  have huniq : ∀ g ∈ A, ∀ g' ∈ A, (∀ h ∈ P, g * h * g⁻¹ = h⁻¹) →
      (∀ h ∈ P, g' * h * g'⁻¹ = h⁻¹) → g = g' := by
    intro g hg g' hg' h1 h2
    by_contra hne
    obtain ⟨h, hh, hne'⟩ := hact (g * g') (A.mul_mem hg hg') (hprod1 g hg g' hg' hne)
    apply hne'
    have : g * g' * h * (g * g')⁻¹ = h := by
      calc g * g' * h * (g * g')⁻¹ = g * (g' * h * g'⁻¹) * g⁻¹ := by group
        _ = (g * h * g⁻¹)⁻¹ := by rw [h2 h hh]; group
        _ = h := by rw [h1 h hh, inv_inv]
    calc g * g' * h = (g * g' * h * (g * g')⁻¹) * (g * g') := by group
      _ = h * (g * g') := by rw [this]
  have hFin : Finite A := inferInstance
  by_cases hex : ∃ c₀ ∈ A, ∀ h ∈ P, c₀ * h * c₀⁻¹ = h⁻¹
  · obtain ⟨c₀, hc₀, hc₀inv⟩ := hex
    obtain ⟨a, ha, haS⟩ := exists_mem_notMem_finset (A := A) ({1, c₀} : Finset (MulAut V))
      ((Finset.card_le_two).trans_lt (by omega))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at haS
    obtain ⟨b, hb, hbS⟩ :=
      exists_mem_notMem_finset (A := A) ({1, a, c₀, a * c₀} : Finset (MulAut V))
      ((Finset.card_le_four).trans_lt (by omega))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hbS
    have hninv : ∀ g ∈ A, g ≠ c₀ → ¬ ∀ h ∈ P, g * h * g⁻¹ = h⁻¹ := fun g hg hgc hgi =>
      hgc (huniq g hg c₀ hc₀ hgi hc₀inv)
    have habc : a * b ≠ c₀ := fun h => hbS.2.2.2 (by
      rw [← h, ← mul_assoc, ← pow_two, hsq a ha, one_mul])
    rcases inverts_of_commuting_involutions hP (hsq a ha) (hcomm a ha b hb) (hKP a (hAK ha))
        (hKP b (hAK hb)) (hact b hb hbS.1) (hact a ha haS.1)
        (hact (a * b) (A.mul_mem ha hb) (hprod1 a ha b hb (Ne.symm hbS.2.1))) with h | h | h
    · exact hninv a ha haS.2 h
    · exact hninv b hb hbS.2.2.1 h
    · exact hninv (a * b) (A.mul_mem ha hb) habc h
  · push Not at hex
    obtain ⟨a, ha, haS⟩ := exists_mem_notMem_finset (A := A) ({1} : Finset (MulAut V))
      (by rw [Finset.card_singleton]; omega)
    simp only [Finset.mem_singleton] at haS
    obtain ⟨b, hb, hbS⟩ := exists_mem_notMem_finset (A := A) ({1, a} : Finset (MulAut V))
      ((Finset.card_le_two).trans_lt (by omega))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hbS
    rcases inverts_of_commuting_involutions hP (hsq a ha) (hcomm a ha b hb) (hKP a (hAK ha))
        (hKP b (hAK hb)) (hact b hb hbS.1) (hact a ha haS)
        (hact (a * b) (A.mul_mem ha hb) (hprod1 a ha b hb (Ne.symm hbS.2))) with h | h | h
    · obtain ⟨h', hh', hne⟩ := hex a ha
      exact hne (h h' hh')
    · obtain ⟨h', hh', hne⟩ := hex b hb
      exact hne (h h' hh')
    · obtain ⟨h', hh', hne⟩ := hex (a * b) (A.mul_mem ha hb)
      exact hne (h h' hh')

end Pieces2

section Qhat

variable {V : Type*} [CommGroup V] [Finite V] {P : Subgroup (MulAut V)}

theorem two_lt_rAV_of_isE9 (hV : ∀ v : V, v ^ 2 = 1) (hP : IsE9 P) {K : Subgroup (MulAut V)}
    (hKP : ∀ k ∈ K, ∀ h ∈ P, k * h * k⁻¹ ∈ P)
    (hinv : ∀ a ∈ K, a ^ 2 = 1 → a ≠ 1 → ∃ h ∈ P, a * h ≠ h * a)
    {x₀ : MulAut V} (hx₀K : x₀ ∈ K) (hx₀3 : x₀ ^ 3 = 1) (hx₀P : ∃ h ∈ P, x₀ * h ≠ h * x₀)
    (hirr : ∀ d ∈ P, d ≠ 1 → ∃ k ∈ K, k * d * k⁻¹ ∉ Subgroup.zpowers d) :
    ∀ A, IsA2 K A → 2 < rAV A := by
  have hne := fun d hd hd1 => piece_ne_bot hV hP hKP hx₀K hx₀3 hx₀P hirr (d := d) hd hd1
  intro A hA
  have hrk2 := rk_le_two_of_isA2 hP hKP hinv hA
  have hpos := hA.rk_pos
  have hAel := hA.isElemAbelian2
  have hAK : A ≤ K := hA.le
  have hsq : ∀ g ∈ A, g ^ 2 = 1 := hAel.2
  have hcardA : Nat.card A = 2 ^ rk A := card_eq_two_pow_of_isPGroup hAel.isPGroup
  have hact : ∀ g ∈ A, g ≠ 1 → ∃ h ∈ P, g * h ≠ h * g := fun g hg hg1 =>
    hinv g (hAK hg) (hsq g hg) hg1
  rcases (by omega : rk A = 1 ∨ rk A = 2) with h1 | h2
  ·
    obtain ⟨⟨a, haA⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hA.ne_bot
    have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
    have hAa : Subgroup.zpowers a = A := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr haA) ?_
      rw [hcardA, h1, Nat.card_zpowers, orderOf_eq_prime (hsq a haA) ha1']
      norm_num
    have h3 := three_le_rkIdx_of_involution hV hP hne (hsq a haA) (hKP a (hAK haA))
      (hact a haA ha1')
    rw [hAa] at h3
    rw [rAV, h1]
    have : (3 : ℚ) ≤ (rkIdx (fixV A) : ℚ) := by exact_mod_cast h3
    push_cast
    linarith
  ·
    obtain ⟨⟨a, haA⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hA.ne_bot
    have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
    have hFin : Finite A := inferInstance
    classical
    obtain ⟨b, hbA, hbS⟩ := exists_mem_notMem_finset (A := A) ({1, a} : Finset (MulAut V))
      ((Finset.card_le_two).trans_lt (by rw [hcardA, h2]; norm_num))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hbS
    have hinvself : ∀ g ∈ A, g⁻¹ = g := fun g hg =>
      inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hsq g hg)
    have hab1 : a * b ≠ 1 := fun h => hbS.2 (by
      rw [← hinvself a haA]; exact eq_inv_of_mul_eq_one_right h)
    have habA := A.mul_mem haA hbA
    have key : ∀ c ∈ A, ∀ b' ∈ A, c ≠ b' → b' ≠ 1 → (∀ h ∈ P, c * h * c⁻¹ = h⁻¹) →
        5 ≤ rkIdx (fixV A) := by
      intro c hc b' hb' hcb' hb'1 hcinv
      refine five_le_rkIdx_of_pair hV hP hne hc hb' (hsq c hc) (hsq b' hb') hcinv
        (hKP b' (hAK hb')) (hact b' hb' hb'1) ?_
      by_contra hcon
      push Not at hcon
      have hcb'1 : c * b' ≠ 1 := fun h => hcb' (by
        rw [← hinvself c hc]; exact (eq_inv_of_mul_eq_one_right h).symm)
      obtain ⟨h, hh, hne'⟩ := hact (c * b') (A.mul_mem hc hb') hcb'1
      apply hne'
      have : c * b' * h * (c * b')⁻¹ = h := by
        calc c * b' * h * (c * b')⁻¹ = c * (b' * h * b'⁻¹) * c⁻¹ := by group
          _ = (c * h * c⁻¹)⁻¹ := by rw [hcon h hh]; group
          _ = h := by rw [hcinv h hh, inv_inv]
      calc c * b' * h = (c * b' * h * (c * b')⁻¹) * (c * b') := by group
        _ = h * (c * b') := by rw [this]
    have h5 : 5 ≤ rkIdx (fixV A) := by
      rcases inverts_of_commuting_involutions hP (hsq a haA) (hAel.1 a haA b hbA)
          (hKP a (hAK haA)) (hKP b (hAK hbA)) (hact b hbA hbS.1) (hact a haA ha1')
          (hact (a * b) habA hab1) with h | h | h
      · exact key a haA b hbA (Ne.symm hbS.2) hbS.1 h
      · exact key b hbA a haA hbS.2 ha1' h
      · refine key (a * b) habA a haA (fun h' => hbS.1 ?_) ha1' h
        calc b = a⁻¹ * (a * b) := by group
          _ = 1 := by rw [h', hinvself a haA, ← pow_two, hsq a haA]
    rw [rAV, h2]
    have : (5 : ℚ) ≤ (rkIdx (fixV A) : ℚ) := by exact_mod_cast h5
    push_cast
    rw [lt_div_iff₀ (by norm_num)]
    linarith

theorem two_lt_qhatOf_of_isE9 (hV : ∀ v : V, v ^ 2 = 1) (hP : IsE9 P) {K : Subgroup (MulAut V)}
    (hKP : ∀ k ∈ K, ∀ h ∈ P, k * h * k⁻¹ ∈ P)
    (hinv : ∀ a ∈ K, a ^ 2 = 1 → a ≠ 1 → ∃ h ∈ P, a * h ≠ h * a)
    {x₀ : MulAut V} (hx₀K : x₀ ∈ K) (hx₀3 : x₀ ^ 3 = 1) (hx₀P : ∃ h ∈ P, x₀ * h ≠ h * x₀)
    (hirr : ∀ d ∈ P, d ≠ 1 → ∃ k ∈ K, k * d * k⁻¹ ∉ Subgroup.zpowers d) :
    ((2 : ℚ) : WithTop ℚ) < qhatOf K :=
  lt_kq_iff.mpr fun A hA _ =>
    two_lt_rAV_of_isE9 hV hP hKP hinv hx₀K hx₀3 hx₀P hirr A hA

end Qhat

end CFSG.Quasithin.EmptyFaithfulMultiple
