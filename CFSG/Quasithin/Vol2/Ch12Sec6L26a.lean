module

public import CFSG.Quasithin.Vol2.Ch12Sec6KG26Data
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal

public section

namespace CFSG.Quasithin.H13.S126Crd

open scoped Pointwise

variable {G : Type*} [Group G]

theorem exists_coord {A Z : Subgroup G} [Finite A] (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hA2 : ∀ a ∈ A, a * a = 1) (hZA : Z ≤ A) (hcard : Nat.card A = 16 * Nat.card Z) :
    ∃ φ : ↥A →* Multiplicative (Fin 4 → ZMod 2), Function.Surjective φ ∧
      ∀ a, φ a = 1 ↔ (a : G) ∈ Z := by
  classical
  let _ : CommGroup ↥A :=
    { (inferInstance : Group ↥A) with
      mul_comm := fun a b => Subtype.ext (hA a a.2 b b.2) }
  let _ : Module (ZMod 2) (Additive ↥A) := AddCommGroup.zmodModule fun x => by
    rw [two_nsmul]
    apply Additive.toMul.injective
    rw [toMul_add, toMul_zero]
    exact Subtype.ext (hA2 _ (Additive.toMul x).2)
  let N : Submodule (ZMod 2) (Additive ↥A) :=
    AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup (Z.subgroupOf A))
  have hmemN : ∀ a : ↥A, Additive.ofMul a ∈ N ↔ (a : G) ∈ Z := fun a => Iff.rfl
  let Q := Additive ↥A ⧸ N
  have : Finite (Additive ↥A) := Finite.of_equiv ↥A Additive.ofMul
  have : Finite Q := Finite.of_surjective N.mkQ N.mkQ_surjective
  let _ : Fintype Q := Fintype.ofFinite Q
  have hcardQ : Nat.card Q = 16 := by
    have h1 := Submodule.card_eq_card_quotient_mul_card N
    have h2 : Nat.card (Additive ↥A) = Nat.card ↥A := Nat.card_congr Additive.ofMul.symm
    have h3 : Nat.card N = Nat.card Z := by
      have : Nat.card N = Nat.card ↥(Z.subgroupOf A) := Nat.card_congr
        { toFun := fun x => ⟨Additive.toMul x.1, x.2⟩
          invFun := fun y => ⟨Additive.ofMul y.1, y.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      rw [this]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZA).toEquiv
    rw [h2, h3, hcard, mul_comm 16] at h1
    have : Finite ↥Z := Finite.of_injective _ (Subgroup.inclusion_injective hZA)
    have hpos : 0 < Nat.card Z := Nat.card_pos
    exact (Nat.eq_of_mul_eq_mul_left hpos h1).symm
  have h4 : Module.finrank (ZMod 2) Q = 4 := by
    have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := Q)
    rw [← Nat.card_eq_fintype_card, hcardQ, ZMod.card] at h
    have : (16 : ℕ) = 2 ^ 4 := by norm_num
    rw [this] at h
    exact (Nat.pow_right_injective (le_refl 2) h).symm
  let b := Module.finBasisOfFinrankEq (ZMod 2) Q h4
  let φ : ↥A →* Multiplicative (Fin 4 → ZMod 2) :=
    { toFun := fun a => Multiplicative.ofAdd (b.equivFun (N.mkQ (Additive.ofMul a)))
      map_one' := by simp
      map_mul' := fun a a' => by
        rw [← ofAdd_add, ← map_add, ← map_add]
        rfl }
  refine ⟨φ, fun e => ?_, fun a => ?_⟩
  · obtain ⟨q, hq⟩ := b.equivFun.surjective (Multiplicative.toAdd e)
    obtain ⟨m, rfl⟩ := N.mkQ_surjective q
    refine ⟨Additive.toMul m, ?_⟩
    show Multiplicative.ofAdd (b.equivFun (N.mkQ (Additive.ofMul (Additive.toMul m)))) = e
    rw [ofMul_toMul, hq]
    rfl
  · change Multiplicative.ofAdd (b.equivFun (N.mkQ (Additive.ofMul a))) = 1 ↔ _
    rw [← hmemN a, ← Submodule.Quotient.mk_eq_zero, ← ofAdd_zero,
      Multiplicative.ofAdd.injective.eq_iff]
    exact LinearEquiv.map_eq_zero_iff _

open S126KG Matrix

variable {G : Type*} [Group G]

structure Setup (Z A B : Subgroup G) (v i : G) : Prop where
  card_Z : Nat.card Z = 2
  Z_le_A : Z ≤ A
  Z_le_B : Z ≤ B
  comm_A : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a
  comm_B : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b
  sq_A : ∀ a ∈ A, a * a = 1
  sq_B : ∀ b ∈ B, b * b = 1
  card_A : Nat.card A = 32
  card_B : Nat.card B = 32
  comm_AB : ∀ a ∈ A, ∀ b ∈ B, a * b * a⁻¹ * b⁻¹ ∈ Z
  nondeg : ∀ b ∈ B, (∀ a ∈ A, a * b = b * a) → b ∈ Z
  v_A : ∀ a ∈ A, v * a = a * v
  v_B : ∀ b ∈ B, v * b * v⁻¹ * b⁻¹ ∈ A
  v_inj : ∀ b ∈ B, v * b * v⁻¹ * b⁻¹ ∈ Z → b ∈ Z
  i_B : ∀ b ∈ B, i * b = b * i
  i_A : ∀ a ∈ A, i * a * i⁻¹ * a⁻¹ ∈ B
  i_inj : ∀ a ∈ A, i * a * i⁻¹ * a⁻¹ ∈ Z → a ∈ Z

namespace Setup

variable {Z A B : Subgroup G} {v i : G} (h : Setup Z A B v i)
include h

@[expose] noncomputable def eps (c : G) : ZMod 2 := by
  classical
  exact if c = 1 then 0 else 1

omit h in
theorem eps_eq_zero {c : G} : eps c = 0 ↔ c = 1 := by
  classical
  unfold eps
  split_ifs with hc
  · exact ⟨fun _ => hc, fun _ => rfl⟩
  · exact ⟨fun h0 => absurd h0 (by decide), fun h1 => absurd h1 hc⟩

theorem mem_Z_eq {c d : G} (hc : c ∈ Z) (hd : d ∈ Z) (hc1 : c ≠ 1) (hd1 : d ≠ 1) : c = d := by
  by_contra hne
  have : Finite ↥Z := Nat.finite_of_card_ne_zero (by rw [h.card_Z]; norm_num)
  have h3 : ({1, c, d} : Set G) ⊆ (Z : Set G) := by
    rintro x (rfl | rfl | rfl)
    exacts [Z.one_mem, hc, hd]
  have hcard := Set.ncard_le_ncard h3 (Set.toFinite _)
  rw [Set.ncard_insert_of_notMem (by simp [Ne.symm hc1, Ne.symm hd1]), Set.ncard_pair hne,
    ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, h.card_Z] at hcard
  omega

theorem eps_mul {c d : G} (hc : c ∈ Z) (hd : d ∈ Z) : eps (c * d) = eps c + eps d := by
  classical
  by_cases hc1 : c = 1
  · rw [hc1, one_mul, eps_eq_zero.2 rfl, zero_add]
  by_cases hd1 : d = 1
  · rw [hd1, mul_one, eps_eq_zero.2 rfl, add_zero]
  have hcd := h.mem_Z_eq hc hd hc1 hd1
  subst hcd
  have hcc : c * c = 1 := h.sq_A c (h.Z_le_A hc)
  rw [hcc, eps_eq_zero.2 rfl]
  have : eps c = 1 := by
    unfold eps
    simp [hc1]
  rw [this]
  decide

theorem comm_mem {a b : G} (ha : a ∈ A) (hb : b ∈ B) : a * b * a⁻¹ * b⁻¹ ∈ Z :=
  h.comm_AB a ha b hb

theorem Z_comm_A {c a : G} (hc : c ∈ Z) (ha : a ∈ A) : c * a = a * c :=
  h.comm_A c (h.Z_le_A hc) a ha

theorem Z_comm_B {c b : G} (hc : c ∈ Z) (hb : b ∈ B) : c * b = b * c :=
  h.comm_B c (h.Z_le_B hc) b hb

theorem comm_mul_left {a a' b : G} (ha : a ∈ A) (ha' : a' ∈ A) (hb : b ∈ B) :
    a * a' * b * (a * a')⁻¹ * b⁻¹ = (a * b * a⁻¹ * b⁻¹) * (a' * b * a'⁻¹ * b⁻¹) := by
  have hc := h.comm_mem ha' hb
  have e : a * (a' * b * a'⁻¹ * b⁻¹) = (a' * b * a'⁻¹ * b⁻¹) * a := h.Z_comm_A hc ha |>.symm
  calc a * a' * b * (a * a')⁻¹ * b⁻¹ = a * (a' * b * a'⁻¹ * b⁻¹) * b * a⁻¹ * b⁻¹ := by group
    _ = (a' * b * a'⁻¹ * b⁻¹) * a * b * a⁻¹ * b⁻¹ := by rw [e]
    _ = (a' * b * a'⁻¹ * b⁻¹) * (a * b * a⁻¹ * b⁻¹) := by group
    _ = (a * b * a⁻¹ * b⁻¹) * (a' * b * a'⁻¹ * b⁻¹) := (h.comm_A _ (h.Z_le_A hc) _
        (h.Z_le_A (h.comm_mem ha hb)))

theorem comm_mul_right {a b b' : G} (ha : a ∈ A) (hb : b ∈ B) (hb' : b' ∈ B) :
    a * (b * b') * a⁻¹ * (b * b')⁻¹ = (a * b * a⁻¹ * b⁻¹) * (a * b' * a⁻¹ * b'⁻¹) := by
  have hc := h.comm_mem ha hb'
  have e : Commute (a * b' * a⁻¹ * b'⁻¹) b⁻¹ :=
    Commute.inv_right (show Commute (a * b' * a⁻¹ * b'⁻¹) b from h.Z_comm_B hc hb)
  calc a * (b * b') * a⁻¹ * (b * b')⁻¹ = a * b * a⁻¹ * ((a * b' * a⁻¹ * b'⁻¹) * b⁻¹) := by group
    _ = a * b * a⁻¹ * (b⁻¹ * (a * b' * a⁻¹ * b'⁻¹)) := by rw [e.eq]
    _ = (a * b * a⁻¹ * b⁻¹) * (a * b' * a⁻¹ * b'⁻¹) := by group

@[expose] noncomputable def pair (a b : G) : ZMod 2 := eps (a * b * a⁻¹ * b⁻¹)

theorem pair_mul_left {a a' b : G} (ha : a ∈ A) (ha' : a' ∈ A) (hb : b ∈ B) :
    pair (a * a') b = pair a b + pair a' b := by
  unfold pair
  rw [h.comm_mul_left ha ha' hb, h.eps_mul (h.comm_mem ha hb) (h.comm_mem ha' hb)]

theorem pair_mul_right {a b b' : G} (ha : a ∈ A) (hb : b ∈ B) (hb' : b' ∈ B) :
    pair a (b * b') = pair a b + pair a b' := by
  unfold pair
  rw [h.comm_mul_right ha hb hb', h.eps_mul (h.comm_mem ha hb) (h.comm_mem ha hb')]

theorem pair_Z_left {c b : G} (hc : c ∈ Z) (hb : b ∈ B) : pair c b = 0 := by
  unfold pair
  rw [h.Z_comm_B hc hb, mul_inv_cancel_right, mul_inv_cancel]
  exact eps_eq_zero.2 rfl

theorem pair_Z_right {a c : G} (ha : a ∈ A) (hc : c ∈ Z) : pair a c = 0 := by
  unfold pair
  rw [← h.Z_comm_A hc ha, mul_inv_cancel_right, mul_inv_cancel]
  exact eps_eq_zero.2 rfl

omit h in
theorem pair_eq_zero_iff {a b : G} : pair a b = 0 ↔ a * b = b * a := by
  unfold pair
  rw [eps_eq_zero]
  constructor
  · intro e
    calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
      _ = b * a := by rw [e, one_mul]
  · intro e
    rw [e]
    group

end Setup

structure Coords (Z A : Subgroup G) where
  φ : ↥A →* Multiplicative (Fin 4 → ZMod 2)
  surj : Function.Surjective φ
  ker : ∀ a, φ a = 1 ↔ (a : G) ∈ Z
  e : Fin 4 → ↥A
  he : ∀ j, φ (e j) = Multiplicative.ofAdd (Pi.single j 1)

namespace Coords

variable {Z A : Subgroup G} (c : Coords Z A)

@[expose] def vec (a : ↥A) : Fin 4 → ZMod 2 := Multiplicative.toAdd (c.φ a)

theorem vec_mul (a a' : ↥A) : c.vec (a * a') = c.vec a + c.vec a' := by
  simp [vec]

theorem vec_e (j : Fin 4) : c.vec (c.e j) = Pi.single j 1 := by
  simp [vec, c.he]

theorem vec_eq_zero (a : ↥A) : c.vec a = 0 ↔ (a : G) ∈ Z := by
  rw [← c.ker, vec, ← toAdd_one, Multiplicative.toAdd.injective.eq_iff]

theorem vec_pow (a : ↥A) (n : ℕ) : c.vec (a ^ n) = n • c.vec a := by
  simp [vec]

theorem natCast_val (x : ZMod 2) : ((x.val : ℕ) : ZMod 2) = x := ZMod.natCast_zmod_val x

theorem sel_sum : ∀ w : Fin 4 → ZMod 2,
    ((if w 0 = 1 then Pi.single 0 1 else 0) + (if w 1 = 1 then Pi.single 1 1 else 0) +
      (if w 2 = 1 then Pi.single 2 1 else 0) + (if w 3 = 1 then Pi.single 3 1 else 0) :
        Fin 4 → ZMod 2) = w := by
  decide +kernel

theorem ite_mul_eq : ∀ t y : ZMod 2, (if t = 1 then y else 0) = t * y := by decide

theorem sum_formula (f : ↥A → ZMod 2) (hf : ∀ a a', f (a * a') = f a + f a')
    (hfZ : ∀ a : ↥A, (a : G) ∈ Z → f a = 0) (a : ↥A) : f a = ∑ j, c.vec a j * f (c.e j) := by
  classical
  have hf1 : f 1 = 0 := by
    have h1 := hf 1 1
    rw [mul_one] at h1
    have h2 : ∀ t : ZMod 2, t = t + t → t = 0 := by decide
    exact h2 _ h1
  set w := c.vec a with hw
  let sel : Fin 4 → ↥A := fun j => if w j = 1 then c.e j else 1
  have hsel : ∀ j, c.vec (sel j) = if w j = 1 then Pi.single j 1 else 0 := by
    intro j
    by_cases hj : w j = 1
    · simp only [sel, hj, ite_true, vec_e]
    · simp only [sel, hj, ite_false]
      simp [vec]
  have hfsel : ∀ j, f (sel j) = w j * f (c.e j) := by
    intro j
    rw [← ite_mul_eq]
    by_cases hj : w j = 1
    · simp only [sel, hj, ite_true]
    · simp only [sel, hj, ite_false, hf1]
  let p : ↥A := sel 0 * sel 1 * sel 2 * sel 3
  have hvp : c.vec p = w := by
    simp only [p, vec_mul, hsel]
    exact sel_sum w
  have hq : f (a * p⁻¹) = 0 := by
    apply hfZ
    rw [← c.vec_eq_zero, vec_mul]
    have : c.vec p⁻¹ = -c.vec p := by rw [vec, vec, map_inv, toAdd_inv]
    rw [this, hvp, hw]
    exact add_neg_cancel _
  have hap : a = a * p⁻¹ * p := by group
  rw [hap, hf, hq, zero_add]
  simp only [p, hf, hfsel, Fin.sum_univ_four]

end Coords

theorem exists_coords {Z A : Subgroup G} [Finite A] (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hA2 : ∀ a ∈ A, a * a = 1) (hZA : Z ≤ A) (hcard : Nat.card A = 16 * Nat.card Z) :
    Nonempty (Coords Z A) := by
  obtain ⟨φ, hs, hk⟩ := exists_coord hA hA2 hZA hcard
  exact ⟨⟨φ, hs, hk, fun j => (hs (Multiplicative.ofAdd (Pi.single j 1))).choose,
    fun j => (hs _).choose_spec⟩⟩

namespace Setup

variable {Z A B : Subgroup G} {v i : G} (h : Setup Z A B v i)
include h

omit h in
theorem pair_one_right (a : G) : pair a 1 = 0 := by
  unfold pair
  rw [mul_one, mul_inv_cancel, one_mul, inv_one]
  exact eps_eq_zero.2 rfl

@[expose] noncomputable def psi (cA : Coords Z A) : ↥B →* Multiplicative (Fin 4 → ZMod 2) where
  toFun b := Multiplicative.ofAdd fun j => pair (cA.e j : G) b
  map_one' := by
    apply Multiplicative.toAdd.injective
    funext j
    exact pair_one_right _
  map_mul' b b' := by
    apply Multiplicative.toAdd.injective
    funext j
    exact h.pair_mul_right (cA.e j).2 b.2 b'.2

theorem toAdd_psi (cA : Coords Z A) (b : ↥B) (j : Fin 4) :
    Multiplicative.toAdd (h.psi cA b) j = pair (cA.e j : G) b := rfl

theorem pair_eq_sum (cA : Coords Z A) (a : ↥A) {b : G} (hb : b ∈ B) :
    pair (a : G) b = ∑ j, cA.vec a j * pair (cA.e j : G) b :=
  cA.sum_formula (fun a => pair (a : G) b) (fun a a' => h.pair_mul_left a.2 a'.2 hb)
    (fun _ ha => h.pair_Z_left ha hb) a

theorem psi_eq_one_iff (cA : Coords Z A) (b : ↥B) : h.psi cA b = 1 ↔ (b : G) ∈ Z := by
  constructor
  · intro hb
    have h0 : ∀ j, pair (cA.e j : G) b = 0 := fun j => by
      have := congrFun (congrArg Multiplicative.toAdd hb) j
      rwa [toAdd_psi, toAdd_one] at this
    apply h.nondeg b b.2
    intro a ha
    rw [← pair_eq_zero_iff, h.pair_eq_sum cA ⟨a, ha⟩ b.2]
    simp [h0]
  · intro hb
    apply Multiplicative.toAdd.injective
    funext j
    rw [toAdd_psi, toAdd_one]
    exact h.pair_Z_right (cA.e j).2 hb

theorem psi_surj [Finite G] (cA : Coords Z A) : Function.Surjective (h.psi cA) := by
  rw [← MonoidHom.range_eq_top]
  have hker : (h.psi cA).ker = Z.subgroupOf B := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, h.psi_eq_one_iff]
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (h.psi cA).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (h.psi cA)).toEquiv, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.Z_le_B).toEquiv, h.card_B, h.card_Z] at h1
  have h16 : Nat.card (h.psi cA).range = 16 := by omega
  rw [← Subgroup.card_eq_iff_eq_top, h16, Nat.card_eq_fintype_card]
  rfl

@[expose] noncomputable def coordsB [Finite G] (cA : Coords Z A) : Coords Z B where
  φ := h.psi cA
  surj := h.psi_surj cA
  ker := h.psi_eq_one_iff cA
  e := fun j => (h.psi_surj cA (Multiplicative.ofAdd (Pi.single j 1))).choose
  he := fun _ => (h.psi_surj cA _).choose_spec

theorem vec_coordsB [Finite G] (cA : Coords Z A) (b : ↥B) (j : Fin 4) :
    (h.coordsB cA).vec b j = pair (cA.e j : G) b := rfl

theorem pair_eq_dot [Finite G] (cA : Coords Z A) (a : ↥A) (b : ↥B) :
    pair (a : G) b = ∑ j, cA.vec a j * (h.coordsB cA).vec b j := by
  rw [h.pair_eq_sum cA a b.2]
  rfl

theorem vec_eq_pair [Finite G] (cA : Coords Z A) (a : ↥A) (j : Fin 4) :
    cA.vec a j = pair (a : G) ((h.coordsB cA).e j) := by
  rw [h.pair_eq_dot cA a, (h.coordsB cA).vec_e j, Fin.sum_univ_four]
  fin_cases j <;> simp

@[expose] def xb (b : ↥B) : ↥A := ⟨v * b * v⁻¹ * (b : G)⁻¹, h.v_B b b.2⟩

@[expose] def ya (a : ↥A) : ↥B := ⟨i * a * i⁻¹ * (a : G)⁻¹, h.i_A a a.2⟩

theorem v_Z {c : G} (hc : c ∈ Z) : v * c * v⁻¹ = c := by
  rw [h.v_A c (h.Z_le_A hc), mul_inv_cancel_right]

theorem i_Z {c : G} (hc : c ∈ Z) : i * c * i⁻¹ = c := by
  rw [h.i_B c (h.Z_le_B hc), mul_inv_cancel_right]

theorem xb_mul (b b' : ↥B) :
    ((h.xb b * h.xb b' : ↥A) : G)⁻¹ * (h.xb (b * b') : G) ∈ Z := by
  have hx'A : (h.xb b' : G) ∈ A := (h.xb b').2
  have e : (h.xb (b * b') : G) = (h.xb b : G) * (h.xb b' : G) *
      ((h.xb b' : G)⁻¹ * b * (h.xb b' : G) * (b : G)⁻¹) := by
    simp only [xb, Subgroup.coe_mul]
    group
  rw [e, Subgroup.coe_mul]
  have hc : (h.xb b' : G)⁻¹ * b * (h.xb b' : G) * (b : G)⁻¹ ∈ Z := by
    have := h.comm_mem (A.inv_mem hx'A) b.2
    rwa [inv_inv] at this
  convert hc using 1
  group

theorem vecA_xb_mul (cA : Coords Z A) (b b' : ↥B) :
    cA.vec (h.xb (b * b')) = cA.vec (h.xb b) + cA.vec (h.xb b') := by
  have := h.xb_mul b b'
  rw [← cA.vec_mul]
  have hz : cA.vec ((h.xb b * h.xb b')⁻¹ * h.xb (b * b')) = 0 := (cA.vec_eq_zero _).2 this
  rw [cA.vec_mul] at hz
  have hi : cA.vec (h.xb b * h.xb b')⁻¹ = -cA.vec (h.xb b * h.xb b') := by
    rw [Coords.vec, Coords.vec, map_inv, toAdd_inv]
  rw [hi] at hz
  exact (neg_add_eq_zero.1 hz).symm

theorem xb_Z {c : ↥B} (hc : (c : G) ∈ Z) : (h.xb c : G) = 1 := by
  simp only [xb]
  rw [h.v_Z hc, mul_inv_cancel]

theorem ya_mul (a a' : ↥A) :
    ((h.ya a * h.ya a' : ↥B) : G)⁻¹ * (h.ya (a * a') : G) ∈ Z := by
  have hy'B : (h.ya a' : G) ∈ B := (h.ya a').2
  have e : (h.ya (a * a') : G) = (h.ya a : G) * (h.ya a' : G) *
      ((h.ya a' : G)⁻¹ * a * (h.ya a' : G) * (a : G)⁻¹) := by
    simp only [ya, Subgroup.coe_mul]
    group
  rw [e, Subgroup.coe_mul]
  have hc : (h.ya a' : G)⁻¹ * a * (h.ya a' : G) * (a : G)⁻¹ ∈ Z := by
    have := h.comm_mem a.2 (B.inv_mem hy'B)
    have h2 := Z.inv_mem this
    convert h2 using 1
    group
  convert hc using 1
  group

theorem vecB_ya_mul (cB : Coords Z B) (a a' : ↥A) :
    cB.vec (h.ya (a * a')) = cB.vec (h.ya a) + cB.vec (h.ya a') := by
  have := h.ya_mul a a'
  have hz : cB.vec ((h.ya a * h.ya a')⁻¹ * h.ya (a * a')) = 0 := (cB.vec_eq_zero _).2 this
  rw [cB.vec_mul] at hz
  have hi : cB.vec (h.ya a * h.ya a')⁻¹ = -cB.vec (h.ya a * h.ya a') := by
    rw [Coords.vec, Coords.vec, map_inv, toAdd_inv]
  rw [hi, cB.vec_mul] at hz
  exact (neg_add_eq_zero.1 hz).symm

theorem ya_Z {c : ↥A} (hc : (c : G) ∈ Z) : (h.ya c : G) = 1 := by
  simp only [ya]
  rw [h.i_Z hc, mul_inv_cancel]

theorem pair_xb_self (b : ↥B) : pair (h.xb b : G) b = 0 := by
  have hx : (h.xb b : G) * h.xb b = 1 := h.sq_A _ (h.xb b).2
  have hb : (b : G) * b = 1 := h.sq_B _ b.2
  have hvb : (v * b * v⁻¹) * (v * b * v⁻¹) = 1 := by
    calc (v * b * v⁻¹) * (v * b * v⁻¹) = v * ((b : G) * b) * v⁻¹ := by group
      _ = 1 := by rw [hb, mul_one, mul_inv_cancel]
  have e : v * b * v⁻¹ = (h.xb b : G) * b := by simp only [xb]; group
  rw [e] at hvb
  unfold pair
  rw [eps_eq_zero, inv_eq_of_mul_eq_one_right hx, inv_eq_of_mul_eq_one_right hb]
  calc (h.xb b : G) * b * (h.xb b) * b = (h.xb b : G) * b * ((h.xb b : G) * b) := by group
    _ = 1 := hvb

theorem pair_Z_mem {c : ↥A} (hc : (c : G) ∈ Z) {b : G} (hb : b ∈ B) : pair (c : G) b = 0 :=
  h.pair_Z_left hc hb

theorem pair_xb_symm (b b' : ↥B) : pair (h.xb b : G) b' = pair (h.xb b' : G) b := by
  obtain ⟨c, hc, hce⟩ : ∃ c ∈ Z, (h.xb (b * b') : G) = (h.xb b : G) * h.xb b' * c :=
    ⟨_, h.xb_mul b b', by simp only [Subgroup.coe_mul]; group⟩
  have h0 := h.pair_xb_self (b * b')
  rw [hce, h.pair_mul_left (A.mul_mem (h.xb b).2 (h.xb b').2) (h.Z_le_A hc) (b * b').2,
    h.pair_mul_left (h.xb b).2 (h.xb b').2 (b * b').2, h.pair_Z_left hc (b * b').2, add_zero,
    Subgroup.coe_mul, h.pair_mul_right (h.xb b).2 b.2 b'.2,
    h.pair_mul_right (h.xb b').2 b.2 b'.2, h.pair_xb_self b, h.pair_xb_self b', zero_add,
    add_zero] at h0
  have h2 : ∀ s t : ZMod 2, s + t = 0 → s = t := by decide
  exact h2 _ _ h0

theorem pair_self_ya (a : ↥A) : pair (a : G) (h.ya a) = 0 := by
  have hy : (h.ya a : G) * h.ya a = 1 := h.sq_B _ (h.ya a).2
  have ha : (a : G) * a = 1 := h.sq_A _ a.2
  have hia : (i * a * i⁻¹) * (i * a * i⁻¹) = 1 := by
    calc (i * a * i⁻¹) * (i * a * i⁻¹) = i * ((a : G) * a) * i⁻¹ := by group
      _ = 1 := by rw [ha, mul_one, mul_inv_cancel]
  have e : i * a * i⁻¹ = (h.ya a : G) * a := by simp only [ya]; group
  rw [e] at hia
  unfold pair
  rw [eps_eq_zero, inv_eq_of_mul_eq_one_right hy, inv_eq_of_mul_eq_one_right ha]
  calc (a : G) * (h.ya a) * a * (h.ya a) = (h.ya a : G)⁻¹ * ((h.ya a : G) * a * ((h.ya a) * a)) *
        (h.ya a) := by group
    _ = 1 := by rw [hia, mul_one, inv_mul_cancel]

theorem pair_ya_symm (a a' : ↥A) : pair (a' : G) (h.ya a) = pair (a : G) (h.ya a') := by
  obtain ⟨c, hc, hce⟩ : ∃ c ∈ Z, (h.ya (a * a') : G) = (h.ya a : G) * h.ya a' * c :=
    ⟨_, h.ya_mul a a', by simp only [Subgroup.coe_mul]; group⟩
  have h0 := h.pair_self_ya (a * a')
  rw [hce, h.pair_mul_right (a * a').2 (B.mul_mem (h.ya a).2 (h.ya a').2) (h.Z_le_B hc),
    h.pair_mul_right (a * a').2 (h.ya a).2 (h.ya a').2, h.pair_Z_right (a * a').2 hc, add_zero,
    Subgroup.coe_mul, h.pair_mul_left a.2 a'.2 (h.ya a).2,
    h.pair_mul_left a.2 a'.2 (h.ya a').2, h.pair_self_ya a, h.pair_self_ya a', zero_add,
    add_zero] at h0
  have h2 : ∀ s t : ZMod 2, s + t = 0 → s = t := by decide
  exact h2 _ _ h0

section Mat

variable [Finite G] (cA : Coords Z A)

@[expose] noncomputable def Xm : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  Matrix.of fun j k => cA.vec (h.xb ((h.coordsB cA).e k)) j

@[expose] noncomputable def Ym : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  Matrix.of fun j k => (h.coordsB cA).vec (h.ya (cA.e k)) j

theorem vec_xb (b : ↥B) : cA.vec (h.xb b) = h.Xm cA *ᵥ (h.coordsB cA).vec b := by
  funext j
  have := (h.coordsB cA).sum_formula (fun b => cA.vec (h.xb b) j)
    (fun b b' => by simp only [h.vecA_xb_mul cA, Pi.add_apply])
    (fun b hb => by
      rw [show h.xb b = 1 from Subtype.ext (h.xb_Z hb)]
      simp [Coords.vec]) b
  rw [this, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm]
  rfl

theorem vec_ya (a : ↥A) : (h.coordsB cA).vec (h.ya a) = h.Ym cA *ᵥ cA.vec a := by
  funext j
  have := cA.sum_formula (fun a => (h.coordsB cA).vec (h.ya a) j)
    (fun a a' => by simp only [h.vecB_ya_mul (h.coordsB cA), Pi.add_apply])
    (fun a ha => by
      rw [show h.ya a = 1 from Subtype.ext (h.ya_Z ha)]
      simp [Coords.vec]) a
  rw [this, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm]
  rfl

theorem Xm_apply (j k : Fin 4) :
    h.Xm cA j k = pair (h.xb ((h.coordsB cA).e k) : G) ((h.coordsB cA).e j) :=
  h.vec_eq_pair cA _ j

theorem Ym_apply (j k : Fin 4) : h.Ym cA j k = pair (cA.e j : G) (h.ya (cA.e k)) :=
  h.vec_coordsB cA _ j

@[expose] noncomputable def xs : Fin 6 → ZMod 2 :=
  ![h.Xm cA 0 1, h.Xm cA 0 2, h.Xm cA 0 3, h.Xm cA 1 2, h.Xm cA 1 3, h.Xm cA 2 3]

@[expose] noncomputable def ys : Fin 6 → ZMod 2 :=
  ![h.Ym cA 0 1, h.Ym cA 0 2, h.Ym cA 0 3, h.Ym cA 1 2, h.Ym cA 1 3, h.Ym cA 2 3]

theorem Xm_diag (j : Fin 4) : h.Xm cA j j = 0 := by
  rw [Xm_apply]
  exact h.pair_xb_self _

theorem Xm_symm (j k : Fin 4) : h.Xm cA j k = h.Xm cA k j := by
  rw [Xm_apply, Xm_apply, h.pair_xb_symm]

theorem Ym_diag (j : Fin 4) : h.Ym cA j j = 0 := by
  rw [Ym_apply]
  exact h.pair_self_ya _

theorem Ym_symm (j k : Fin 4) : h.Ym cA j k = h.Ym cA k j := by
  rw [Ym_apply, Ym_apply, h.pair_ya_symm]

theorem Xm_eq : h.Xm cA = alt4 (h.xs cA) := by
  ext j k
  fin_cases j <;> fin_cases k <;>
    simp [alt4, xs, Xm_diag, Xm_symm h cA _ (0 : Fin 4)] <;> rw [Xm_symm]

theorem Ym_eq : h.Ym cA = alt4 (h.ys cA) := by
  ext j k
  fin_cases j <;> fin_cases k <;>
    simp [alt4, ys, Ym_diag, Ym_symm h cA _ (0 : Fin 4)] <;> rw [Ym_symm]

theorem pf_xs : pf (h.xs cA) = 1 := by
  apply pf_eq_one_of_injective
  intro β hβ
  obtain ⟨b, hb⟩ := (h.coordsB cA).surj (Multiplicative.ofAdd β)
  have hvb : (h.coordsB cA).vec b = β := by rw [Coords.vec, hb]; rfl
  rw [← h.Xm_eq, ← hvb, ← h.vec_xb] at hβ
  have hbZ : (b : G) ∈ Z := h.v_inj b b.2 ((cA.vec_eq_zero _).1 hβ)
  rw [← hvb]
  exact ((h.coordsB cA).vec_eq_zero b).2 hbZ

theorem pf_ys : pf (h.ys cA) = 1 := by
  apply pf_eq_one_of_injective
  intro α hα
  obtain ⟨a, ha⟩ := cA.surj (Multiplicative.ofAdd α)
  have hva : cA.vec a = α := by rw [Coords.vec, ha]; rfl
  rw [← h.Ym_eq, ← hva, ← h.vec_ya] at hα
  have haZ : (a : G) ∈ Z := h.i_inj a a.2 (((h.coordsB cA).vec_eq_zero _).1 hα)
  rw [← hva]
  exact (cA.vec_eq_zero a).2 haZ

@[expose] def Rel (u : G) (γ : Fin 4 ⊕ Fin 4 → ZMod 2) : Prop :=
  ∃ a : ↥A, ∃ b : ↥B, cA.vec a = γ ∘ Sum.inl ∧ (h.coordsB cA).vec b = γ ∘ Sum.inr ∧
    u⁻¹ * (a * b) ∈ Z

theorem rel_v {u : G} {γ : Fin 4 ⊕ Fin 4 → ZMod 2} (hu : h.Rel cA u γ) :
    h.Rel cA (v * u * v⁻¹) (vBlk (h.xs cA) *ᵥ γ) := by
  obtain ⟨a, b, ha, hb, hc⟩ := hu
  refine ⟨a * h.xb b, b, ?_, ?_, ?_⟩
  · rw [vBlk, fromBlocks_mulVec, Sum.elim_comp_inl, cA.vec_mul, h.vec_xb, ha, hb, ← h.Xm_eq,
      Matrix.one_mulVec]
  · rw [vBlk, fromBlocks_mulVec, Sum.elim_comp_inr, hb, Matrix.zero_mulVec, zero_add,
      Matrix.one_mulVec]
  · have hva : v⁻¹ * a * v = a := by
      rw [mul_assoc, ← h.v_A a a.2, inv_mul_cancel_left]
    have e : (v * u * v⁻¹)⁻¹ * ((a * h.xb b : ↥A) * b : G) = v * (u⁻¹ * (a * b)) * v⁻¹ := by
      simp only [xb, Subgroup.coe_mul]
      calc (v * u * v⁻¹)⁻¹ * ((a : G) * (v * b * v⁻¹ * (b : G)⁻¹) * b) =
            v * u⁻¹ * (v⁻¹ * a * v) * b * v⁻¹ := by group
        _ = v * (u⁻¹ * (a * b)) * v⁻¹ := by rw [hva]; group
    rw [e, h.v_Z hc]
    exact hc

theorem rel_i {u : G} {γ : Fin 4 ⊕ Fin 4 → ZMod 2} (hu : h.Rel cA u γ) :
    h.Rel cA (i * u * i⁻¹) (iBlk (h.ys cA) *ᵥ γ) := by
  obtain ⟨a, b, ha, hb, hc⟩ := hu
  refine ⟨a, h.ya a * b, ?_, ?_, ?_⟩
  · rw [iBlk, fromBlocks_mulVec, Sum.elim_comp_inl, ha, Matrix.one_mulVec, Matrix.zero_mulVec,
      add_zero]
  · rw [iBlk, fromBlocks_mulVec, Sum.elim_comp_inr, (h.coordsB cA).vec_mul, h.vec_ya, ha, hb,
      ← h.Ym_eq, Matrix.one_mulVec]
  · have hdZ : (h.ya a : G)⁻¹ * (a : G)⁻¹ * (h.ya a) * a ∈ Z := by
      have := Z.inv_mem (h.comm_mem (A.inv_mem a.2) (B.inv_mem (h.ya a).2))
      convert this using 1
      group
    have hdb : ((h.ya a : G)⁻¹ * (a : G)⁻¹ * (h.ya a) * a) * b =
        b * ((h.ya a : G)⁻¹ * (a : G)⁻¹ * (h.ya a) * a) := h.Z_comm_B hdZ b.2
    have hib : i * b * i⁻¹ = b := by rw [h.i_B b b.2, mul_inv_cancel_right]
    have hic : i * (u⁻¹ * (a * b))⁻¹ * i⁻¹ = (u⁻¹ * (a * b))⁻¹ := h.i_Z (Z.inv_mem hc)
    have hia : i * a * i⁻¹ =
        (a : G) * (h.ya a) * ((h.ya a : G)⁻¹ * (a : G)⁻¹ * (h.ya a) * a) := by
      simp only [ya]
      group
    have e : i * u * i⁻¹ = (a : G) * (h.ya a) * b *
        (((h.ya a : G)⁻¹ * (a : G)⁻¹ * (h.ya a) * a) * (u⁻¹ * (a * b))⁻¹) := by
      calc i * u * i⁻¹ = (i * a * i⁻¹) * (i * b * i⁻¹) * (i * (u⁻¹ * (a * b))⁻¹ * i⁻¹) := by
            group
        _ = (a : G) * (h.ya a) * (((h.ya a : G)⁻¹ * (a : G)⁻¹ * (h.ya a) * a) * b) *
            (u⁻¹ * (a * b))⁻¹ := by rw [hia, hib, hic]; group
        _ = _ := by rw [hdb]; group
    have e2 : (i * u * i⁻¹)⁻¹ * ((a : G) * ((h.ya a * b : ↥B) : G)) =
        (((h.ya a : G)⁻¹ * (a : G)⁻¹ * (h.ya a) * a) * (u⁻¹ * (a * b))⁻¹)⁻¹ := by
      rw [e, Subgroup.coe_mul]
      group
    rw [e2]
    exact Z.inv_mem (Z.mul_mem hdZ (Z.inv_mem hc))

theorem rel_g {u : G} {γ : Fin 4 ⊕ Fin 4 → ZMod 2} (hu : h.Rel cA u γ) :
    h.Rel cA ((v * i) * u * (v * i)⁻¹) (gBlk (h.xs cA) (h.ys cA) *ᵥ γ) := by
  have e : (v * i) * u * (v * i)⁻¹ = v * (i * u * i⁻¹) * v⁻¹ := by group
  rw [e, ← vBlk_mul_iBlk, ← Matrix.mulVec_mulVec]
  exact h.rel_v cA (h.rel_i cA hu)

theorem rel_pow {u : G} {γ : Fin 4 ⊕ Fin 4 → ZMod 2} (hu : h.Rel cA u γ) (k : ℕ) :
    h.Rel cA ((v * i) ^ k * u * ((v * i) ^ k)⁻¹) (gBlk (h.xs cA) (h.ys cA) ^ k *ᵥ γ) := by
  induction k with
  | zero => simpa using hu
  | succ k ih =>
    have e : (v * i) ^ (k + 1) * u * ((v * i) ^ (k + 1))⁻¹ =
        (v * i) * ((v * i) ^ k * u * ((v * i) ^ k)⁻¹) * (v * i)⁻¹ := by
      generalize v * i = w
      rw [pow_succ']
      group
    rw [e, pow_succ', ← Matrix.mulVec_mulVec]
    exact h.rel_g cA ih

theorem rel_unique {u u' : G} {γ : Fin 4 ⊕ Fin 4 → ZMod 2} (hu : h.Rel cA u γ)
    (hu' : h.Rel cA u' γ) : u⁻¹ * u' ∈ Z := by
  obtain ⟨a, b, ha, hb, hc⟩ := hu
  obtain ⟨a', b', ha', hb', hc'⟩ := hu'
  have h1 : (a : G)⁻¹ * a' ∈ Z := by
    have : cA.vec (a⁻¹ * a') = 0 := by
      rw [cA.vec_mul, ha', ← ha, Coords.vec, Coords.vec, map_inv, toAdd_inv]
      exact neg_add_cancel _
    exact (cA.vec_eq_zero _).1 this
  have h2 : (b : G)⁻¹ * b' ∈ Z := by
    have : (h.coordsB cA).vec (b⁻¹ * b') = 0 := by
      rw [(h.coordsB cA).vec_mul, hb', ← hb, Coords.vec, Coords.vec, map_inv, toAdd_inv]
      exact neg_add_cancel _
    exact ((h.coordsB cA).vec_eq_zero _).1 this
  have hz1 : ((a : G)⁻¹ * a') * b = b * ((a : G)⁻¹ * a') := h.Z_comm_B h1 b.2
  have e : u⁻¹ * u' = (u⁻¹ * (a * b)) * ((a : G)⁻¹ * a') * ((b : G)⁻¹ * b') *
      (u'⁻¹ * (a' * b'))⁻¹ := by
    calc u⁻¹ * u' = u⁻¹ * (a * b) * ((b : G)⁻¹ * ((a : G)⁻¹ * a') * b) * ((b : G)⁻¹ * b') *
          (u'⁻¹ * (a' * b'))⁻¹ := by group
      _ = _ := by rw [mul_assoc (b : G)⁻¹, hz1]; group
  rw [e]
  exact Z.mul_mem (Z.mul_mem (Z.mul_mem hc h1) h2) (Z.inv_mem hc')

omit [Finite G] in
theorem conj_mem_Z {x c : G} (hx : x ∈ A) (hc : c ∈ Z) : x * c * x⁻¹ ∈ Z := by
  rw [← h.Z_comm_A hc hx, mul_inv_cancel_right]
  exact hc

theorem trivMod_of_pow_eq_one (cA : Coords Z A) {k : ℕ}
    (hk : gBlk (h.xs cA) (h.ys cA) ^ k = 1) :
    (∀ a ∈ A, (v * i) ^ k * a * ((v * i) ^ k)⁻¹ * a⁻¹ ∈ Z) ∧
      ∀ b ∈ B, (v * i) ^ k * b * ((v * i) ^ k)⁻¹ * b⁻¹ ∈ Z := by
  constructor
  · intro a₀ ha₀
    have hrel : h.Rel cA a₀ (Sum.elim (cA.vec ⟨a₀, ha₀⟩) 0) := by
      refine ⟨⟨a₀, ha₀⟩, 1, by rw [Sum.elim_comp_inl], ?_, ?_⟩
      · rw [Sum.elim_comp_inr]
        simp [Coords.vec]
      · simp
    have h2 := h.rel_pow cA hrel k
    rw [hk, Matrix.one_mulVec] at h2
    have h3 := h.rel_unique cA hrel h2
    have := h.conj_mem_Z ha₀ h3
    convert this using 1
    group
  · intro b₀ hb₀
    have hrel : h.Rel cA b₀ (Sum.elim 0 ((h.coordsB cA).vec ⟨b₀, hb₀⟩)) := by
      refine ⟨1, ⟨b₀, hb₀⟩, ?_, by rw [Sum.elim_comp_inr], ?_⟩
      · rw [Sum.elim_comp_inl]
        simp [Coords.vec]
      · simp
    have h2 := h.rel_pow cA hrel k
    rw [hk, Matrix.one_mulVec] at h2
    have h3 := h.rel_unique cA hrel h2
    have h4 : b₀ * (b₀⁻¹ * ((v * i) ^ k * b₀ * ((v * i) ^ k)⁻¹)) * b₀⁻¹ ∈ Z := by
      rw [← h.Z_comm_B h3 hb₀, mul_inv_cancel_right]
      exact h3
    convert h4 using 1
    group

theorem pow_five_or_six :
    ((∀ a ∈ A, (v * i) ^ 5 * a * ((v * i) ^ 5)⁻¹ * a⁻¹ ∈ Z) ∧
        ∀ b ∈ B, (v * i) ^ 5 * b * ((v * i) ^ 5)⁻¹ * b⁻¹ ∈ Z) ∨
      ((∀ a ∈ A, (v * i) ^ 6 * a * ((v * i) ^ 6)⁻¹ * a⁻¹ ∈ Z) ∧
        ∀ b ∈ B, (v * i) ^ 6 * b * ((v * i) ^ 6)⁻¹ * b⁻¹ ∈ Z) := by
  obtain ⟨cA⟩ := exists_coords h.comm_A h.sq_A h.Z_le_A (by rw [h.card_A, h.card_Z])
  rcases gBlk_pow _ _ (h.pf_xs cA) (h.pf_ys cA) with h5 | h6
  · exact Or.inl (h.trivMod_of_pow_eq_one cA h5)
  · exact Or.inr (h.trivMod_of_pow_eq_one cA h6)

end Mat

end Setup

end CFSG.Quasithin.H13.S126Crd
