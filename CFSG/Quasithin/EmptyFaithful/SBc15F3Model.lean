module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

public section

namespace CFSG.Quasithin

namespace SBc15

namespace L3

structure N3 where
  a : Nat
  b : Nat
  c : Nat
  d : Nat
  e : Nat
  f : Nat
  g : Nat
  h : Nat
  i : Nat
  deriving DecidableEq

namespace N3

def dot (x₀ y₀ x₁ y₁ x₂ y₂ : Nat) : Nat :=
  Nat.xor (Nat.xor (Nat.mul x₀ y₀) (Nat.mul x₁ y₁)) (Nat.mul x₂ y₂)

def mul (x y : N3) : N3 :=
  ⟨dot x.a y.a x.b y.d x.c y.g, dot x.a y.b x.b y.e x.c y.h, dot x.a y.c x.b y.f x.c y.i,
   dot x.d y.a x.e y.d x.f y.g, dot x.d y.b x.e y.e x.f y.h, dot x.d y.c x.e y.f x.f y.i,
   dot x.g y.a x.h y.d x.i y.g, dot x.g y.b x.h y.e x.i y.h, dot x.g y.c x.h y.f x.i y.i⟩

def one : N3 := ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩

def inv (x : N3) : N3 :=
  ⟨Nat.xor (Nat.mul x.e x.i) (Nat.mul x.f x.h), Nat.xor (Nat.mul x.b x.i) (Nat.mul x.c x.h),
   Nat.xor (Nat.mul x.b x.f) (Nat.mul x.c x.e),
   Nat.xor (Nat.mul x.d x.i) (Nat.mul x.f x.g), Nat.xor (Nat.mul x.a x.i) (Nat.mul x.c x.g),
   Nat.xor (Nat.mul x.a x.f) (Nat.mul x.c x.d),
   Nat.xor (Nat.mul x.d x.h) (Nat.mul x.e x.g), Nat.xor (Nat.mul x.a x.h) (Nat.mul x.b x.g),
   Nat.xor (Nat.mul x.a x.e) (Nat.mul x.b x.d)⟩

def det (x : N3) : Nat :=
  Nat.xor (Nat.xor
    (Nat.mul x.a (Nat.xor (Nat.mul x.e x.i) (Nat.mul x.f x.h)))
    (Nat.mul x.b (Nat.xor (Nat.mul x.d x.i) (Nat.mul x.f x.g))))
    (Nat.mul x.c (Nat.xor (Nat.mul x.d x.h) (Nat.mul x.e x.g)))

def pow (x : N3) : Nat → N3
  | 0 => one
  | n + 1 => mul (pow x n) x

def conj (r a : N3) : N3 := mul (mul r a) (inv r)

def bits : List Nat := [0, 1]

def allN3 : List N3 :=
  bits.flatMap fun a => bits.flatMap fun b => bits.flatMap fun c => bits.flatMap fun d =>
  bits.flatMap fun e => bits.flatMap fun f => bits.flatMap fun g => bits.flatMap fun h =>
  bits.map fun i => ⟨a, b, c, d, e, f, g, h, i⟩

def elems : List N3 := allN3.filter fun m => Nat.beq m.det 1

def Ord7 (z : N3) : Prop := pow z 7 = one ∧ z ≠ one

instance (z : N3) : Decidable (Ord7 z) := inferInstanceAs (Decidable (pow z 7 = one ∧ z ≠ one))

def rl : List N3 :=
  [⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 1, 1, 0, 0, 1⟩, ⟨1, 0, 1, 0, 1, 0, 0, 0, 1⟩,
   ⟨1, 0, 1, 0, 1, 1, 0, 0, 1⟩, ⟨1, 1, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 1, 1, 0, 1, 0, 0, 0, 1⟩,
   ⟨1, 1, 0, 0, 1, 1, 0, 0, 1⟩, ⟨1, 1, 1, 0, 1, 1, 0, 0, 1⟩]

def al : List N3 :=
  [⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 1, 1, 0, 0, 1⟩, ⟨1, 0, 1, 0, 1, 0, 0, 0, 1⟩,
   ⟨1, 0, 1, 0, 1, 1, 0, 0, 1⟩, ⟨0, 1, 0, 1, 1, 0, 0, 0, 1⟩, ⟨0, 1, 0, 1, 1, 1, 0, 0, 1⟩,
   ⟨0, 1, 1, 1, 1, 0, 0, 0, 1⟩, ⟨0, 1, 1, 1, 1, 1, 0, 0, 1⟩, ⟨1, 1, 0, 1, 0, 0, 0, 0, 1⟩,
   ⟨1, 1, 0, 1, 0, 1, 0, 0, 1⟩, ⟨1, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨1, 1, 1, 1, 0, 1, 0, 0, 1⟩]

def al' : List N3 :=
  [⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 1, 0, 1, 0, 0, 0, 1⟩, ⟨1, 1, 0, 0, 1, 0, 0, 0, 1⟩,
   ⟨1, 1, 1, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 0, 1, 0, 1, 1⟩, ⟨1, 0, 0, 0, 1, 1, 0, 1, 0⟩,
   ⟨1, 0, 1, 0, 0, 1, 0, 1, 1⟩, ⟨1, 0, 1, 0, 1, 1, 0, 1, 0⟩, ⟨1, 1, 0, 0, 0, 1, 0, 1, 1⟩,
   ⟨1, 1, 0, 0, 1, 1, 0, 1, 0⟩, ⟨1, 1, 1, 0, 0, 1, 0, 1, 1⟩, ⟨1, 1, 1, 0, 1, 1, 0, 1, 0⟩]

def vl : List N3 :=
  [⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 1, 1, 0, 0, 1⟩, ⟨1, 0, 1, 0, 1, 0, 0, 0, 1⟩,
   ⟨1, 0, 1, 0, 1, 1, 0, 0, 1⟩]

def vl' : List N3 :=
  [⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 1, 0, 1, 0, 0, 0, 1⟩, ⟨1, 1, 0, 0, 1, 0, 0, 0, 1⟩,
   ⟨1, 1, 1, 0, 1, 0, 0, 0, 1⟩]

def Closed (l : List N3) : Prop :=
  one ∈ l ∧ (∀ x ∈ l, ∀ y ∈ l, mul x y ∈ l) ∧ ∀ x ∈ l, inv x ∈ l

instance (l : List N3) : Decidable (Closed l) :=
  inferInstanceAs (Decidable (one ∈ l ∧ (∀ x ∈ l, ∀ y ∈ l, mul x y ∈ l) ∧ ∀ x ∈ l, inv x ∈ l))

set_option maxRecDepth 100000 in
theorem closed_lists : Closed rl ∧ Closed al ∧ Closed al' ∧ Closed vl ∧ Closed vl' := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem pe_orders :
    ∀ x ∈ elems, pow x 2 = one ∨ pow x 3 = one ∨ pow x 4 = one ∨ pow x 7 = one := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem pe_e1 : ∀ x ∈ elems, pow x 3 = one → x ≠ one → x ∈ al ∨ x ∈ al' ∨
    ∃ r₂ ∈ rl, ∃ r₃ ∈ rl, Ord7 (mul (mul x (conj r₂ x)) (conj r₃ x)) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem pe_e2a : ∀ a ∈ al, pow a 3 = one → a ≠ one → ∀ x ∈ al,
    ∃ r₁ ∈ rl, ∃ r₂ ∈ rl, x = mul (conj r₁ a) (conj r₂ a) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem pe_e2b : ∀ a ∈ al', pow a 3 = one → a ≠ one → ∀ x ∈ al',
    ∃ r₁ ∈ rl, ∃ r₂ ∈ rl, x = mul (conj r₁ a) (conj r₂ a) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem pe_e3ab : ∃ a ∈ al, ∃ b ∈ al', Ord7 (mul a b) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem pe_e3ba : ∃ a ∈ al', ∃ b ∈ al, Ord7 (mul a b) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem pe_sub : (∀ v ∈ vl, v ∈ rl) ∧ ∀ v ∈ vl', v ∈ rl := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem pe_norm : (∀ k ∈ rl, ∀ v ∈ vl, conj k v ∈ vl) ∧ (∀ k ∈ al, ∀ v ∈ vl, conj k v ∈ vl) ∧
    (∀ k ∈ rl, ∀ v ∈ vl', conj k v ∈ vl') ∧ ∀ k ∈ al', ∀ v ∈ vl', conj k v ∈ vl' := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem pe_weaka : ∀ k ∈ elems, (∀ v ∈ vl, conj k v ∈ rl) → ∃ y ∈ al, ∃ r ∈ rl, k = mul y r := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem pe_weakb : ∀ k ∈ elems, (∀ v ∈ vl', conj k v ∈ rl) → ∃ y ∈ al', ∃ r ∈ rl, k = mul y r := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem pe_comma : ∀ y ∈ al, y ≠ one → pow y 3 = one → ∀ w ∈ vl,
    ∃ v ∈ vl, w = mul (mul v y) (mul (inv v) (inv y)) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem pe_commb : ∀ y ∈ al', y ≠ one → pow y 3 = one → ∀ w ∈ vl',
    ∃ v ∈ vl', w = mul (mul v y) (mul (inv v) (inv y)) := by
  decide +kernel

end N3

abbrev SL32 : Type := Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)

def toN3 (x : SL32) : N3 :=
  ⟨(x.1 0 0).val, (x.1 0 1).val, (x.1 0 2).val, (x.1 1 0).val, (x.1 1 1).val, (x.1 1 2).val,
   (x.1 2 0).val, (x.1 2 1).val, (x.1 2 2).val⟩

set_option maxRecDepth 100000 in
theorem val_dot (a b c d e f : ZMod 2) :
    (a * b + c * d + e * f).val = N3.dot a.val b.val c.val d.val e.val f.val := by
  revert a b c d e f
  decide +kernel

set_option maxRecDepth 100000 in
theorem val_sub (a b c d : ZMod 2) :
    (a * b - c * d).val = Nat.xor (Nat.mul a.val b.val) (Nat.mul c.val d.val) := by
  revert a b c d
  decide +kernel

set_option maxRecDepth 100000 in
theorem val_add_two (a b c d : ZMod 2) :
    (a * b + c * d).val = Nat.xor (Nat.mul a.val b.val) (Nat.mul c.val d.val) := by
  revert a b c d
  decide +kernel

set_option maxRecDepth 100000 in
theorem val_det (a b c d e f g h i : ZMod 2) :
    (a * e * i - a * f * h - b * d * i + b * f * g + c * d * h - c * e * g).val =
      N3.det ⟨a.val, b.val, c.val, d.val, e.val, f.val, g.val, h.val, i.val⟩ := by
  revert a b c d e f g h i
  decide +kernel

theorem toN3_mul (x y : SL32) : toN3 (x * y) = N3.mul (toN3 x) (toN3 y) := by
  simp only [toN3, N3.mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three,
    val_dot]

set_option maxRecDepth 100000 in
theorem toN3_one : toN3 1 = N3.one := by
  decide +kernel

theorem toN3_inv (x : SL32) : toN3 x⁻¹ = N3.inv (toN3 x) := by
  simp [toN3, N3.inv, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_three, val_sub,
    val_add_two]

theorem toN3_pow (x : SL32) (n : ℕ) : toN3 (x ^ n) = N3.pow (toN3 x) n := by
  induction n with
  | zero => exact toN3_one
  | succ n ih => rw [pow_succ, toN3_mul, ih]; rfl

theorem det_toN3 (x : SL32) : (toN3 x).det = 1 := by
  have h := x.2
  rw [Matrix.det_fin_three] at h
  have h2 := congrArg ZMod.val h
  rw [val_det] at h2
  have h1 : (1 : ZMod 2).val = 1 := by decide
  rw [h1] at h2
  exact h2

theorem toN3_injective : Function.Injective toN3 := by
  intro x y h
  have key : ∀ i j : Fin 3, x.1 i j = y.1 i j := by
    intro i j
    apply ZMod.val_injective
    fin_cases i <;> fin_cases j <;> simpa [toN3] using
      (by first
        | exact congrArg N3.a h | exact congrArg N3.b h | exact congrArg N3.c h
        | exact congrArg N3.d h | exact congrArg N3.e h | exact congrArg N3.f h
        | exact congrArg N3.g h | exact congrArg N3.h h | exact congrArg N3.i h)
  exact Subtype.ext (Matrix.ext key)

theorem toN3_mem_allN3 (x : SL32) : toN3 x ∈ N3.allN3 := by
  have hb : ∀ z : ZMod 2, z.val ∈ N3.bits := by
    intro z
    have := ZMod.val_lt z
    simp only [N3.bits, List.mem_cons, List.not_mem_nil, or_false]
    omega
  simp only [N3.allN3, List.mem_flatMap, List.mem_map]
  exact ⟨_, hb _, _, hb _, _, hb _, _, hb _, _, hb _, _, hb _, _, hb _, _, hb _, _, hb _, rfl⟩

theorem toN3_mem_elems (x : SL32) : toN3 x ∈ N3.elems := by
  simp only [N3.elems, List.mem_filter]
  exact ⟨toN3_mem_allN3 x, by simp [det_toN3]⟩

set_option maxRecDepth 100000 in
theorem card_SL32 : Nat.card SL32 = 168 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

set_option maxRecDepth 100000 in
theorem elems_length_nodup : N3.elems.length = 168 ∧ N3.elems.Nodup := by
  decide +kernel

theorem exists_toN3_eq {m : N3} (hm : m ∈ N3.elems) : ∃ x : SL32, toN3 x = m := by
  let F : SL32 → {m // m ∈ N3.elems.toFinset} := fun x =>
    ⟨toN3 x, List.mem_toFinset.mpr (toN3_mem_elems x)⟩
  have hF : Function.Injective F := fun x y h => toN3_injective (congrArg Subtype.val h)
  have hcard : Nat.card {m // m ∈ N3.elems.toFinset} = 168 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup elems_length_nodup.2,
      elems_length_nodup.1]
  have hbij := hF.bijective_of_nat_card_le (by rw [hcard, card_SL32])
  obtain ⟨x, hx⟩ := hbij.2 ⟨m, List.mem_toFinset.mpr hm⟩
  exact ⟨x, congrArg Subtype.val hx⟩

theorem toN3_conj (r a : SL32) : toN3 (r * a * r⁻¹) = N3.conj (toN3 r) (toN3 a) := by
  rw [toN3_mul, toN3_mul, toN3_inv]
  rfl

theorem pow_eq_one_iff {x : SL32} {n : ℕ} : x ^ n = 1 ↔ N3.pow (toN3 x) n = N3.one :=
  ⟨fun h => by rw [← toN3_pow, h, toN3_one],
    fun h => toN3_injective (by rw [toN3_pow, toN3_one]; exact h)⟩

theorem ne_one_iff {x : SL32} : x ≠ 1 ↔ toN3 x ≠ N3.one :=
  ⟨fun h hx => h (toN3_injective (hx.trans toN3_one.symm)),
    fun h hx => h (by rw [hx, toN3_one])⟩

@[expose] def Ord7 (z : SL32) : Prop := z ^ 7 = 1 ∧ z ≠ 1

theorem ord7_of {z : SL32} (h : N3.Ord7 (toN3 z)) : Ord7 z :=
  ⟨pow_eq_one_iff.mpr h.1, ne_one_iff.mpr h.2⟩

def listSub (l : List N3) (h : N3.Closed l) : Subgroup SL32 where
  carrier := {x | toN3 x ∈ l}
  one_mem' := by
    show toN3 1 ∈ l
    rw [toN3_one]
    exact h.1
  mul_mem' := by
    intro x y hx hy
    change toN3 x ∈ l at hx
    change toN3 y ∈ l at hy
    show toN3 (x * y) ∈ l
    rw [toN3_mul]
    exact h.2.1 _ hx _ hy
  inv_mem' := by
    intro x hx
    change toN3 x ∈ l at hx
    show toN3 x⁻¹ ∈ l
    rw [toN3_inv]
    exact h.2.2 _ hx

theorem mem_listSub {l : List N3} {h : N3.Closed l} {x : SL32} :
    x ∈ listSub l h ↔ toN3 x ∈ l :=
  Iff.rfl

def R0 : Subgroup SL32 := listSub N3.rl N3.closed_lists.1

def A4a : Subgroup SL32 := listSub N3.al N3.closed_lists.2.1

def A4b : Subgroup SL32 := listSub N3.al' N3.closed_lists.2.2.1

def V4a : Subgroup SL32 := listSub N3.vl N3.closed_lists.2.2.2.1

def V4b : Subgroup SL32 := listSub N3.vl' N3.closed_lists.2.2.2.2

theorem mem_R0 {x : SL32} : x ∈ R0 ↔ toN3 x ∈ N3.rl := Iff.rfl

theorem mem_A4a {x : SL32} : x ∈ A4a ↔ toN3 x ∈ N3.al := Iff.rfl

theorem mem_A4b {x : SL32} : x ∈ A4b ↔ toN3 x ∈ N3.al' := Iff.rfl

theorem mem_V4a {x : SL32} : x ∈ V4a ↔ toN3 x ∈ N3.vl := Iff.rfl

theorem mem_V4b {x : SL32} : x ∈ V4b ↔ toN3 x ∈ N3.vl' := Iff.rfl

set_option maxRecDepth 100000 in
theorem lists_sub_elems : (∀ m ∈ N3.rl, m ∈ N3.elems) ∧ (∀ m ∈ N3.al, m ∈ N3.elems) ∧
    (∀ m ∈ N3.al', m ∈ N3.elems) ∧ (∀ m ∈ N3.vl, m ∈ N3.elems) ∧ ∀ m ∈ N3.vl', m ∈ N3.elems := by
  decide +kernel

theorem exists_R0 {m : N3} (hm : m ∈ N3.rl) : ∃ x : SL32, x ∈ R0 ∧ toN3 x = m := by
  obtain ⟨x, hx⟩ := exists_toN3_eq (lists_sub_elems.1 m hm)
  exact ⟨x, mem_R0.mpr (hx ▸ hm), hx⟩

theorem exists_A4a {m : N3} (hm : m ∈ N3.al) : ∃ x : SL32, x ∈ A4a ∧ toN3 x = m := by
  obtain ⟨x, hx⟩ := exists_toN3_eq (lists_sub_elems.2.1 m hm)
  exact ⟨x, mem_A4a.mpr (hx ▸ hm), hx⟩

theorem exists_A4b {m : N3} (hm : m ∈ N3.al') : ∃ x : SL32, x ∈ A4b ∧ toN3 x = m := by
  obtain ⟨x, hx⟩ := exists_toN3_eq (lists_sub_elems.2.2.1 m hm)
  exact ⟨x, mem_A4b.mpr (hx ▸ hm), hx⟩

theorem exists_V4a {m : N3} (hm : m ∈ N3.vl) : ∃ x : SL32, x ∈ V4a ∧ toN3 x = m := by
  obtain ⟨x, hx⟩ := exists_toN3_eq (lists_sub_elems.2.2.2.1 m hm)
  exact ⟨x, mem_V4a.mpr (hx ▸ hm), hx⟩

theorem exists_V4b {m : N3} (hm : m ∈ N3.vl') : ∃ x : SL32, x ∈ V4b ∧ toN3 x = m := by
  obtain ⟨x, hx⟩ := exists_toN3_eq (lists_sub_elems.2.2.2.2 m hm)
  exact ⟨x, mem_V4b.mpr (hx ▸ hm), hx⟩

theorem exp_cases (x : SL32) : x ^ 2 = 1 ∨ x ^ 3 = 1 ∨ x ^ 4 = 1 ∨ x ^ 7 = 1 := by
  simpa only [pow_eq_one_iff] using N3.pe_orders _ (toN3_mem_elems x)

theorem e1_L (x : SL32) (h3 : x ^ 3 = 1) (h1 : x ≠ 1) :
    x ∈ A4a ∨ x ∈ A4b ∨ ∃ r₂ ∈ R0, ∃ r₃ ∈ R0,
      Ord7 (x * (r₂ * x * r₂⁻¹) * (r₃ * x * r₃⁻¹)) := by
  rcases N3.pe_e1 _ (toN3_mem_elems x) (pow_eq_one_iff.mp h3) (ne_one_iff.mp h1) with
    h | h | ⟨m₂, hm₂, m₃, hm₃, h7⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · obtain ⟨r₂, hr₂, rfl⟩ := exists_R0 hm₂
    obtain ⟨r₃, hr₃, rfl⟩ := exists_R0 hm₃
    refine Or.inr (Or.inr ⟨r₂, hr₂, r₃, hr₃, ord7_of ?_⟩)
    rw [toN3_mul, toN3_mul, toN3_conj, toN3_conj]
    exact h7

theorem e2a_L {a : SL32} (ha : a ∈ A4a) (h3 : a ^ 3 = 1) (h1 : a ≠ 1) {x : SL32} (hx : x ∈ A4a) :
    ∃ r₁ ∈ R0, ∃ r₂ ∈ R0, x = (r₁ * a * r₁⁻¹) * (r₂ * a * r₂⁻¹) := by
  obtain ⟨m₁, hm₁, m₂, hm₂, hmx⟩ := N3.pe_e2a _ ha (pow_eq_one_iff.mp h3) (ne_one_iff.mp h1) _ hx
  obtain ⟨r₁, hr₁, rfl⟩ := exists_R0 hm₁
  obtain ⟨r₂, hr₂, rfl⟩ := exists_R0 hm₂
  refine ⟨r₁, hr₁, r₂, hr₂, toN3_injective ?_⟩
  rw [toN3_mul, toN3_conj, toN3_conj]
  exact hmx

theorem e2b_L {a : SL32} (ha : a ∈ A4b) (h3 : a ^ 3 = 1) (h1 : a ≠ 1) {x : SL32} (hx : x ∈ A4b) :
    ∃ r₁ ∈ R0, ∃ r₂ ∈ R0, x = (r₁ * a * r₁⁻¹) * (r₂ * a * r₂⁻¹) := by
  obtain ⟨m₁, hm₁, m₂, hm₂, hmx⟩ := N3.pe_e2b _ ha (pow_eq_one_iff.mp h3) (ne_one_iff.mp h1) _ hx
  obtain ⟨r₁, hr₁, rfl⟩ := exists_R0 hm₁
  obtain ⟨r₂, hr₂, rfl⟩ := exists_R0 hm₂
  refine ⟨r₁, hr₁, r₂, hr₂, toN3_injective ?_⟩
  rw [toN3_mul, toN3_conj, toN3_conj]
  exact hmx

theorem e3ab_L : ∃ a ∈ A4a, ∃ b ∈ A4b, Ord7 (a * b) := by
  obtain ⟨m₁, hm₁, m₂, hm₂, h7⟩ := N3.pe_e3ab
  obtain ⟨a, ha, rfl⟩ := exists_A4a hm₁
  obtain ⟨b, hb, rfl⟩ := exists_A4b hm₂
  exact ⟨a, ha, b, hb, ord7_of (by rw [toN3_mul]; exact h7)⟩

theorem e3ba_L : ∃ a ∈ A4b, ∃ b ∈ A4a, Ord7 (a * b) := by
  obtain ⟨m₁, hm₁, m₂, hm₂, h7⟩ := N3.pe_e3ba
  obtain ⟨a, ha, rfl⟩ := exists_A4b hm₁
  obtain ⟨b, hb, rfl⟩ := exists_A4a hm₂
  exact ⟨a, ha, b, hb, ord7_of (by rw [toN3_mul]; exact h7)⟩

theorem V4a_le_R0 : V4a ≤ R0 := fun _ hx => N3.pe_sub.1 _ hx

theorem V4b_le_R0 : V4b ≤ R0 := fun _ hx => N3.pe_sub.2 _ hx

theorem R0_conj_V4a {k v : SL32} (hk : k ∈ R0) (hv : v ∈ V4a) : k * v * k⁻¹ ∈ V4a := by
  rw [mem_V4a, toN3_conj]
  exact N3.pe_norm.1 _ hk _ hv

theorem A4a_conj_V4a {k v : SL32} (hk : k ∈ A4a) (hv : v ∈ V4a) : k * v * k⁻¹ ∈ V4a := by
  rw [mem_V4a, toN3_conj]
  exact N3.pe_norm.2.1 _ hk _ hv

theorem R0_conj_V4b {k v : SL32} (hk : k ∈ R0) (hv : v ∈ V4b) : k * v * k⁻¹ ∈ V4b := by
  rw [mem_V4b, toN3_conj]
  exact N3.pe_norm.2.2.1 _ hk _ hv

theorem A4b_conj_V4b {k v : SL32} (hk : k ∈ A4b) (hv : v ∈ V4b) : k * v * k⁻¹ ∈ V4b := by
  rw [mem_V4b, toN3_conj]
  exact N3.pe_norm.2.2.2 _ hk _ hv

theorem weaka_L (k : SL32) (hk : ∀ v ∈ V4a, k * v * k⁻¹ ∈ R0) :
    ∃ y ∈ A4a, ∃ r ∈ R0, k = y * r := by
  obtain ⟨m₁, hm₁, m₂, hm₂, hkm⟩ := N3.pe_weaka _ (toN3_mem_elems k) (fun v hv => by
    obtain ⟨x, hx, rfl⟩ := exists_V4a hv
    have := hk x hx
    rwa [mem_R0, toN3_conj] at this)
  obtain ⟨y, hy, rfl⟩ := exists_A4a hm₁
  obtain ⟨r, hr, rfl⟩ := exists_R0 hm₂
  exact ⟨y, hy, r, hr, toN3_injective (by rw [toN3_mul]; exact hkm)⟩

theorem weakb_L (k : SL32) (hk : ∀ v ∈ V4b, k * v * k⁻¹ ∈ R0) :
    ∃ y ∈ A4b, ∃ r ∈ R0, k = y * r := by
  obtain ⟨m₁, hm₁, m₂, hm₂, hkm⟩ := N3.pe_weakb _ (toN3_mem_elems k) (fun v hv => by
    obtain ⟨x, hx, rfl⟩ := exists_V4b hv
    have := hk x hx
    rwa [mem_R0, toN3_conj] at this)
  obtain ⟨y, hy, rfl⟩ := exists_A4b hm₁
  obtain ⟨r, hr, rfl⟩ := exists_R0 hm₂
  exact ⟨y, hy, r, hr, toN3_injective (by rw [toN3_mul]; exact hkm)⟩

theorem comma_L {y : SL32} (hy : y ∈ A4a) (h1 : y ≠ 1) (h3 : y ^ 3 = 1) {w : SL32} (hw : w ∈ V4a) :
    ∃ v ∈ V4a, w = v * y * v⁻¹ * y⁻¹ := by
  obtain ⟨m, hm, hwm⟩ := N3.pe_comma _ hy (ne_one_iff.mp h1) (pow_eq_one_iff.mp h3) _ hw
  obtain ⟨v, hv, rfl⟩ := exists_V4a hm
  refine ⟨v, hv, toN3_injective ?_⟩
  rw [mul_assoc (v * y) v⁻¹ y⁻¹, toN3_mul, toN3_mul, toN3_mul, toN3_inv, toN3_inv]
  exact hwm

theorem commb_L {y : SL32} (hy : y ∈ A4b) (h1 : y ≠ 1) (h3 : y ^ 3 = 1) {w : SL32} (hw : w ∈ V4b) :
    ∃ v ∈ V4b, w = v * y * v⁻¹ * y⁻¹ := by
  obtain ⟨m, hm, hwm⟩ := N3.pe_commb _ hy (ne_one_iff.mp h1) (pow_eq_one_iff.mp h3) _ hw
  obtain ⟨v, hv, rfl⟩ := exists_V4b hm
  refine ⟨v, hv, toN3_injective ?_⟩
  rw [mul_assoc (v * y) v⁻¹ y⁻¹, toN3_mul, toN3_mul, toN3_mul, toN3_inv, toN3_inv]
  exact hwm

set_option maxRecDepth 100000 in
theorem cards_std : Nat.card R0 = 8 ∧ Nat.card A4a = 12 ∧ Nat.card A4b = 12 ∧ Nat.card V4a = 4 ∧
    Nat.card V4b = 4 := by
  have key : ∀ l : List N3, Nat.card {x : SL32 // toN3 x ∈ l} =
      (Finset.univ.filter fun x : SL32 => toN3 x ∈ l).card := by
    intro l
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine (key N3.rl).trans ?_
    decide +kernel
  · refine (key N3.al).trans ?_
    decide +kernel
  · refine (key N3.al').trans ?_
    decide +kernel
  · refine (key N3.vl).trans ?_
    decide +kernel
  · refine (key N3.vl').trans ?_
    decide +kernel

end L3

end SBc15

end CFSG.Quasithin
