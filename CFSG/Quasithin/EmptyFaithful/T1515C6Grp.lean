module

public import CFSG.Quasithin.Background.CommVBasics
public import CFSG.Quasithin.EmptyFaithful.T1515C6Mod
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin

open scoped Pointwise

section Fixing

variable {V : Type*} [Group V]

@[expose] def fixingV (S : Set V) : Subgroup (MulAut V) where
  carrier := {φ | ∀ z ∈ S, φ z = z}
  one_mem' := fun z _ => rfl
  mul_mem' := fun {a b} ha hb z hz => by
    show a (b z) = z
    rw [hb z hz, ha z hz]
  inv_mem' := fun {a} ha z hz => by
    show a⁻¹ z = z
    have := ha z hz
    calc a⁻¹ z = a⁻¹ (a z) := by rw [this]
      _ = z := by simp

theorem mem_fixingV {S : Set V} {φ : MulAut V} : φ ∈ fixingV S ↔ ∀ z ∈ S, φ z = z := Iff.rfl

end Fixing

variable {V : Type*} [CommGroup V]

structure SixCtx (A₁ A₂ M T : Subgroup (MulAut V)) (τ : MulAut V) : Prop where
  sq : ∀ v : V, v * v = 1
  card_V : Nat.card V = 256
  e₁ : Nonempty (A₁ ≃* DihedralGroup 3)
  e₂ : Nonempty (A₂ ≃* DihedralGroup 3)
  comm : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a
  disj : A₁ ⊓ A₂ = ⊥
  le_M : A₁ ⊔ A₂ ≤ M
  card_M : Nat.card M = 72
  le_T : T ≤ M
  card_T : Nat.card T = 8
  tau_mem : τ ∈ T
  tau_conj : A₁.map (MulAut.conj τ).toMonoidHom = A₂
  dsum_inf : commV A₁ ⊓ commV A₂ = ⊥
  dsum_sup : commV A₁ ⊔ commV A₂ = ⊤


theorem card_le_two_of_sq_one {X : Type*} [Group X] {A P : Subgroup X} (hA : Nat.card A = 6)
    (hPA : P ≤ A) (hsq : ∀ x ∈ P, x * x = 1) : Nat.card P ≤ 2 := by
  have hdvd : Nat.card P ∣ 6 := hA ▸ Subgroup.card_dvd_of_le hPA
  have hfin : Finite P := Nat.finite_of_card_ne_zero (fun h0 => by rw [h0] at hdvd; simp at hdvd)
  have h3 : ¬ 3 ∣ Nat.card P := by
    intro h3
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := P) 3 h3
    have h1 : (x : X) * x = 1 := hsq x x.2
    have h2 : orderOf (x : X) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h1)
    have h4 : orderOf (x : X) = 3 := by
      rw [← hx]
      exact (Subgroup.orderOf_coe x)
    rw [h4] at h2
    omega
  generalize Nat.card P = n at hdvd h3
  have hle : n ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases n <;> simp_all

def projSub (A B K : Subgroup (MulAut V)) (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    Subgroup (MulAut V) where
  carrier := {a | a ∈ A ∧ ∃ b ∈ B, a * b ∈ K}
  one_mem' := ⟨A.one_mem, 1, B.one_mem, by simp⟩
  mul_mem' := by
    rintro a a' ⟨ha, b, hb, hab⟩ ⟨ha', b', hb', hab'⟩
    refine ⟨A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
    have : a * a' * (b * b') = (a * b) * (a' * b') := by
      calc a * a' * (b * b') = a * (a' * b) * b' := by group
        _ = a * (b * a') * b' := by rw [hc a' ha' b hb]
        _ = (a * b) * (a' * b') := by group
    rw [this]
    exact K.mul_mem hab hab'
  inv_mem' := by
    rintro a ⟨ha, b, hb, hab⟩
    refine ⟨A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
    have : a⁻¹ * b⁻¹ = (a * b)⁻¹ := by
      calc a⁻¹ * b⁻¹ = (b * a)⁻¹ := by group
        _ = (a * b)⁻¹ := by rw [← hc a ha b hb]
    rw [this]
    exact K.inv_mem hab

theorem mem_projSub {A B K : Subgroup (MulAut V)} {hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a}
    {a : MulAut V} : a ∈ projSub A B K hc ↔ a ∈ A ∧ ∃ b ∈ B, a * b ∈ K := Iff.rfl


theorem card_two_subgroup {X : Type*} [Group X] {P : Subgroup X} (hP : Nat.card P = 2) {s : X}
    (hs : s ∈ P) (hs1 : s ≠ 1) : ∀ a ∈ P, a = 1 ∨ a = s := by
  obtain ⟨x, y, hxy, hset⟩ := Nat.card_eq_two_iff.mp hP
  have hx : ∀ e : P, e = x ∨ e = y := fun e => by
    have : e ∈ ({x, y} : Set P) := hset ▸ Set.mem_univ e
    simpa using this
  intro a ha
  have hs1' : (⟨s, hs⟩ : P) ≠ 1 := fun h => hs1 (congrArg Subtype.val h)
  by_contra hcon
  push Not at hcon
  have ha1 : (⟨a, ha⟩ : P) ≠ 1 := fun h => hcon.1 (congrArg Subtype.val h)
  have has : (⟨a, ha⟩ : P) ≠ ⟨s, hs⟩ := fun h => hcon.2 (congrArg Subtype.val h)
  rcases hx 1 with h1 | h1 <;> rcases hx ⟨s, hs⟩ with h2 | h2 <;> rcases hx ⟨a, ha⟩ with h3 | h3 <;>
    simp_all

theorem sq_one_of_projSub {A B K : Subgroup (MulAut V)} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hd : A ⊓ B = ⊥) (hA : Nat.card A = 6) (hK : Nat.card K = 4) {a : MulAut V}
    (ha : a ∈ projSub A B K hc) : a * a = 1 := by
  obtain ⟨haA, b, hb, hab⟩ := ha
  have h4 : (a * b) ^ 4 = 1 := by
    have := pow_card_eq_one' (x := (⟨a * b, hab⟩ : K))
    rw [hK] at this
    exact congrArg Subtype.val this
  have h6 : a ^ 6 = 1 := by
    have := pow_card_eq_one' (x := (⟨a, haA⟩ : A))
    rw [hA] at this
    exact congrArg Subtype.val this
  have hcomm : Commute a b := hc a haA b hb
  rw [hcomm.mul_pow] at h4
  have ha4 : a ^ 4 = 1 := by
    have h5 : a ^ 4 = (b ^ 4)⁻¹ := eq_inv_of_mul_eq_one_left h4
    have h7 : a ^ 4 ∈ A ⊓ B := ⟨A.pow_mem haA 4, by rw [h5]; exact B.inv_mem (B.pow_mem hb 4)⟩
    rw [hd, Subgroup.mem_bot] at h7
    exact h7
  have : a ^ 6 = a ^ 4 * a ^ 2 := by rw [← pow_add]
  rw [h6, ha4, one_mul] at this
  rw [← pow_two]
  exact this.symm


@[expose] def sixT0 (A₁ A₂ T : Subgroup (MulAut V)) : Subgroup (MulAut V) := T ⊓ (A₁ ⊔ A₂)

@[expose] def sixZ₁ (A₁ A₂ T : Subgroup (MulAut V)) : Subgroup V :=
  commV A₁ ⊓ fixV (sixT0 A₁ A₂ T)

@[expose] def sixZ₂ (A₁ A₂ T : Subgroup (MulAut V)) : Subgroup V :=
  commV A₂ ⊓ fixV (sixT0 A₁ A₂ T)

@[expose] def sixCbar (M : Subgroup (MulAut V)) (Z : Subgroup V) : Subgroup (MulAut V) :=
  M ⊓ fixingV (Z : Set V)

@[expose] def sixD₁ (A₁ : Subgroup (MulAut V)) (Z : Subgroup V) : Subgroup (MulAut V) :=
  A₁ ⊓ fixingV (Z : Set V)

structure SixGens (A₁ A₂ T : Subgroup (MulAut V)) (s u : MulAut V) : Prop where
  sA : s ∈ A₁
  s1 : s ≠ 1
  ss : s * s = 1
  sT : s ∈ T ⊓ (A₁ ⊔ A₂)
  uA : u ∈ A₂
  u1 : u ≠ 1
  uu : u * u = 1
  uT : u ∈ T ⊓ (A₁ ⊔ A₂)
  all : ∀ x ∈ T ⊓ (A₁ ⊔ A₂), x = 1 ∨ x = s ∨ x = u ∨ x = s * u


theorem commV_mono_c6 {X Y : Subgroup (MulAut V)} (hXY : X ≤ Y) : commV X ≤ commV Y :=
  Subgroup.closure_mono fun _ ⟨a, ha, v, hv⟩ => ⟨a, hXY ha, v, hv⟩

theorem exists_comm_rep [Finite V] {c : MulAut V} {W : Subgroup V} (hcW : ∀ w ∈ W, c w ∈ W)
    (hfix : ∀ w ∈ W, c w = w → w = 1) : ∀ v ∈ W, ∃ w ∈ W, c w * w⁻¹ = v := by
  let f : W → W := fun w => ⟨c w * (w : V)⁻¹, W.mul_mem (hcW w w.2) (W.inv_mem w.2)⟩
  have hinj : Function.Injective f := by
    intro w₁ w₂ hw
    have h1 : c w₁ * (w₁ : V)⁻¹ = c w₂ * (w₂ : V)⁻¹ := congrArg Subtype.val hw
    have h2 : c ((w₁ : V) * (w₂ : V)⁻¹) = (w₁ : V) * (w₂ : V)⁻¹ := by
      rw [map_mul, map_inv]
      have h1' : c w₁ / (w₁ : V) = c w₂ / (w₂ : V) := by simpa [div_eq_mul_inv] using h1
      have h2' := div_eq_div_iff_mul_eq_mul.mp h1'
      have h3' : c w₁ / c w₂ = (w₁ : V) / (w₂ : V) :=
        div_eq_div_iff_mul_eq_mul.mpr (by rw [h2', mul_comm])
      simpa [div_eq_mul_inv] using h3'
    have h3 := hfix _ (W.mul_mem w₁.2 (W.inv_mem w₂.2)) h2
    exact Subtype.ext (mul_inv_eq_one.mp h3)
  have hsurj : Function.Surjective f := Finite.injective_iff_surjective.mp hinj
  intro v hv
  obtain ⟨w, hw⟩ := hsurj ⟨v, hv⟩
  exact ⟨w, w.2, congrArg Subtype.val hw⟩

theorem le_commV_zpowers [Finite V] {c : MulAut V} {W : Subgroup V} (hcW : ∀ w ∈ W, c w ∈ W)
    (hfix : ∀ w ∈ W, c w = w → w = 1) : W ≤ commV (Subgroup.zpowers c) := by
  intro v hv
  obtain ⟨w, hw, rfl⟩ := exists_comm_rep hcW hfix v hv
  exact Subgroup.subset_closure ⟨c, Subgroup.mem_zpowers c, w, rfl⟩

namespace SixCtx

variable {A₁ A₂ M T : Subgroup (MulAut V)} {τ : MulAut V} (h : SixCtx A₁ A₂ M T τ)
include h

theorem card_A₁ : Nat.card A₁ = 6 := by
  obtain ⟨e⟩ := h.e₁
  rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]

theorem card_A₂ : Nat.card A₂ = 6 := by
  obtain ⟨e⟩ := h.e₂
  rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]

theorem card_A₀ [Finite V] : Nat.card (A₁ ⊔ A₂ : Subgroup (MulAut V)) = 36 := by
  have := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A₁ A₂ h.comm).1
  rw [h.disj, Subgroup.card_bot, mul_one, h.card_A₁, h.card_A₂] at this
  exact this

theorem mem_A₀ [Finite V] {x : MulAut V} (hx : x ∈ A₁ ⊔ A₂) : ∃ a ∈ A₁, ∃ b ∈ A₂, x = a * b := by
  have hset := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A₁ A₂ h.comm).2
  have : x ∈ ((A₁ ⊔ A₂ : Subgroup (MulAut V)) : Set (MulAut V)) := hx
  rw [hset] at this
  obtain ⟨a, ha, b, hb, rfl⟩ := this
  exact ⟨a, ha, b, hb, rfl⟩


theorem mul_inj {a a' b b' : MulAut V} (ha : a ∈ A₁) (ha' : a' ∈ A₁) (hb : b ∈ A₂)
    (hb' : b' ∈ A₂) (hab : a * b = a' * b') : a = a' ∧ b = b' := by
  have h1 : a'⁻¹ * a = b' * b⁻¹ := by
    have : a' ⁻¹ * (a * b) * b⁻¹ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [hab]
    simpa [mul_assoc] using this
  have hmem1 : a'⁻¹ * a ∈ A₁ := A₁.mul_mem (A₁.inv_mem ha') ha
  have hmem2 : a'⁻¹ * a ∈ A₂ := by
    rw [h1]
    exact A₂.mul_mem hb' (A₂.inv_mem hb)
  have hbot : a'⁻¹ * a ∈ A₁ ⊓ A₂ := ⟨hmem1, hmem2⟩
  rw [h.disj, Subgroup.mem_bot] at hbot
  have haa : a = a' := by
    have := congrArg (a' * ·) hbot
    simpa using this
  refine ⟨haa, ?_⟩
  rw [haa] at hab
  exact mul_left_cancel hab

end SixCtx

section VStruct

theorem mem_commV_gen {A : Subgroup (MulAut V)} {a : MulAut V} (ha : a ∈ A) (v : V) :
    a v * v⁻¹ ∈ commV A :=
  Subgroup.subset_closure ⟨a, ha, v, rfl⟩

theorem commV_invariant_c6 {A : Subgroup (MulAut V)} {a : MulAut V} (ha : a ∈ A) {v : V}
    (hv : v ∈ commV A) : a v ∈ commV A :=
  CFSG.Quasithin.commV_apply_mem_of_mem ha hv


theorem conj_commV {A B : Subgroup (MulAut V)} {g : MulAut V} (hg : ∀ a ∈ A, g * a * g⁻¹ ∈ B)
    {v : V} (hv : v ∈ commV A) : g v ∈ commV B := by
  induction hv using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a', ha', w, rfl⟩ := hx
    have h : g (a' w * w⁻¹) = (g * a' * g⁻¹) (g w) * (g w)⁻¹ := by
      simp only [map_mul, map_inv, MulAut.mul_apply, MulAut.inv_apply]
      simp
    rw [h]
    exact mem_commV_gen (hg a' ha') (g w)
  | one => rw [map_one]; exact (commV B).one_mem
  | mul x y _ _ hx hy => rw [map_mul]; exact (commV B).mul_mem hx hy
  | inv x _ hx => rw [map_inv]; exact (commV B).inv_mem hx

theorem trivial_on_commV {A B : Subgroup (MulAut V)} (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hinf : commV A ⊓ commV B = ⊥) {b : MulAut V} (hb : b ∈ B) {v : V} (hv : v ∈ commV A) :
    b v = v := by
  have hinv : ∀ x ∈ commV A, b x ∈ commV A := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨a', ha', w, rfl⟩ := hx
      have hba : b * a' = a' * b := (hcomm a' ha' b hb).symm
      have h : b (a' w * w⁻¹) = a' (b w) * (b w)⁻¹ := by
        simp only [map_mul, map_inv]
        have := congrArg (fun φ : MulAut V => φ w) hba
        simp only [MulAut.mul_apply] at this
        rw [this]
      rw [h]
      exact mem_commV_gen ha' (b w)
    | one => rw [map_one]; exact (commV A).one_mem
    | mul x y _ _ hx hy => rw [map_mul]; exact (commV A).mul_mem hx hy
    | inv x _ hx => rw [map_inv]; exact (commV A).inv_mem hx
  have h1 : b v * v⁻¹ ∈ commV B := mem_commV_gen hb v
  have h2 : b v * v⁻¹ ∈ commV A := (commV A).mul_mem (hinv v hv) ((commV A).inv_mem hv)
  have h3 : b v * v⁻¹ ∈ commV A ⊓ commV B := ⟨h2, h1⟩
  rw [hinf, Subgroup.mem_bot] at h3
  exact mul_inv_eq_one.mp h3

end VStruct

namespace SixCtx

variable {A₁ A₂ M T : Subgroup (MulAut V)} {τ : MulAut V} (h : SixCtx A₁ A₂ M T τ)
include h

theorem A₂_fix_V₁ {b : MulAut V} (hb : b ∈ A₂) {v : V} (hv : v ∈ commV A₁) : b v = v :=
  trivial_on_commV h.comm h.dsum_inf hb hv

theorem A₁_fix_V₂ {a : MulAut V} (ha : a ∈ A₁) {v : V} (hv : v ∈ commV A₂) : a v = v :=
  trivial_on_commV (fun x hx y hy => (h.comm y hy x hx).symm) (by rw [inf_comm]; exact h.dsum_inf)
    ha hv

theorem A₀_inv_V₁ [Finite V] {x : MulAut V} (hx : x ∈ A₁ ⊔ A₂) {v : V} (hv : v ∈ commV A₁) :
    x v ∈ commV A₁ := by
  obtain ⟨a, ha, b, hb, rfl⟩ := h.mem_A₀ hx
  show a (b v) ∈ commV A₁
  rw [h.A₂_fix_V₁ hb hv]
  exact commV_invariant_c6 ha hv

theorem A₀_inv_V₂ [Finite V] {x : MulAut V} (hx : x ∈ A₁ ⊔ A₂) {v : V} (hv : v ∈ commV A₂) :
    x v ∈ commV A₂ := by
  obtain ⟨a, ha, b, hb, rfl⟩ := h.mem_A₀ hx
  show a (b v) ∈ commV A₂
  rw [h.A₁_fix_V₂ ha (commV_invariant_c6 hb hv)]
  exact commV_invariant_c6 hb hv

theorem V₁_gen : commV A₁ ≤ Subgroup.closure {x : V | ∃ a ∈ A₁, ∃ w ∈ commV A₁, x = a w * w⁻¹} := by
  rw [commV, Subgroup.closure_le]
  rintro x ⟨a, ha, v, rfl⟩
  have hv : v ∈ commV A₁ ⊔ commV A₂ := by rw [h.dsum_sup]; exact Subgroup.mem_top v
  obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := Subgroup.mem_sup.mp hv
  refine Subgroup.subset_closure ⟨a, ha, v₁, hv₁, ?_⟩
  rw [map_mul, h.A₁_fix_V₂ ha hv₂, mul_inv_rev]
  calc a v₁ * v₂ * (v₂⁻¹ * v₁⁻¹) = (a v₁ * v₁⁻¹) * (v₂ * v₂⁻¹) := by ac_rfl
    _ = a v₁ * v₁⁻¹ := by rw [mul_inv_cancel, mul_one]

theorem V₂_gen : commV A₂ ≤ Subgroup.closure {x : V | ∃ a ∈ A₂, ∃ w ∈ commV A₂, x = a w * w⁻¹} := by
  rw [commV, Subgroup.closure_le]
  rintro x ⟨a, ha, v, rfl⟩
  have hv : v ∈ commV A₁ ⊔ commV A₂ := by rw [h.dsum_sup]; exact Subgroup.mem_top v
  obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := Subgroup.mem_sup.mp hv
  refine Subgroup.subset_closure ⟨a, ha, v₂, hv₂, ?_⟩
  rw [map_mul, h.A₂_fix_V₁ ha hv₁, mul_inv_rev]
  calc v₁ * a v₂ * (v₂⁻¹ * v₁⁻¹) = (a v₂ * v₂⁻¹) * (v₁ * v₁⁻¹) := by ac_rfl
    _ = a v₂ * v₂⁻¹ := by rw [mul_inv_cancel, mul_one]

theorem index_A₀ [Finite V] : ((A₁ ⊔ A₂).subgroupOf M).index = 2 := by
  have h1 := Subgroup.card_mul_index ((A₁ ⊔ A₂).subgroupOf M)
  have h2 : Nat.card ((A₁ ⊔ A₂).subgroupOf M) = Nat.card (A₁ ⊔ A₂ : Subgroup (MulAut V)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.le_M).toEquiv
  rw [h2, h.card_A₀, h.card_M] at h1
  omega

theorem mul_mem_iff_A₀ [Finite V] {x y : MulAut V} (hx : x ∈ M) (hy : y ∈ M) :
    x * y ∈ A₁ ⊔ A₂ ↔ (x ∈ A₁ ⊔ A₂ ↔ y ∈ A₁ ⊔ A₂) := by
  have := Subgroup.mul_mem_iff_of_index_two h.index_A₀ (a := (⟨x, hx⟩ : M)) (b := ⟨y, hy⟩)
  simpa [Subgroup.mem_subgroupOf] using this

theorem tau_mem_M : τ ∈ M := h.le_T h.tau_mem

theorem tau_not_mem [Finite V] : τ ∉ A₁ ⊔ A₂ := by
  intro hτ
  obtain ⟨a, ha, b, hb, hab⟩ := h.mem_A₀ hτ
  obtain ⟨x, hx, hx1⟩ : ∃ x ∈ A₁, x ≠ 1 := by
    have hbot : A₁ ≠ ⊥ := fun hbot => by
      have := h.card_A₁
      rw [hbot, Subgroup.card_bot] at this
      omega
    obtain ⟨y, hy⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hbot
    exact ⟨y, y.2, fun h' => hy (Subtype.ext h')⟩
  have hmem : (MulAut.conj τ) x ∈ A₂ := by
    rw [← h.tau_conj]
    exact ⟨x, hx, rfl⟩
  have hconj : (MulAut.conj τ) x = a * x * a⁻¹ := by
    rw [MulAut.conj_apply, hab]
    have hbx : b * x = x * b := (h.comm x hx b hb).symm
    calc a * b * x * (a * b)⁻¹ = a * (b * x) * b⁻¹ * a⁻¹ := by group
      _ = a * (x * b) * b⁻¹ * a⁻¹ := by rw [hbx]
      _ = a * x * a⁻¹ := by group
  have h1 : a * x * a⁻¹ ∈ A₁ := A₁.mul_mem (A₁.mul_mem ha hx) (A₁.inv_mem ha)
  rw [hconj] at hmem
  have : a * x * a⁻¹ ∈ A₁ ⊓ A₂ := ⟨h1, hmem⟩
  rw [h.disj, Subgroup.mem_bot] at this
  apply hx1
  have := congrArg (fun y => a⁻¹ * y * a) this
  simpa [mul_assoc] using this

theorem tau_sq_mem [Finite V] : τ * τ ∈ A₁ ⊔ A₂ := by
  have := (h.mul_mem_iff_A₀ h.tau_mem_M h.tau_mem_M).mpr Iff.rfl
  exact this

theorem index_T₀ [Finite V] : ((T ⊓ (A₁ ⊔ A₂)).subgroupOf T).index = 2 := by
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨τ, h.tau_mem⟩, fun b => ?_⟩
  have hb : (b : MulAut V) ∈ M := h.le_T b.2
  have hbτ := h.mul_mem_iff_A₀ hb h.tau_mem_M
  have hnot := h.tau_not_mem
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.mem_inf]
  have hbT : (b : MulAut V) ∈ T := b.2
  have hbτT : (b : MulAut V) * τ ∈ T := T.mul_mem b.2 h.tau_mem
  by_cases hq : (b : MulAut V) ∈ A₁ ⊔ A₂
  · have : ¬ (b : MulAut V) * τ ∈ A₁ ⊔ A₂ := by
      rw [hbτ]
      exact fun hh => hnot (hh.mp hq)
    exact Or.inr ⟨⟨hbT, hq⟩, fun hh => this hh.2⟩
  · have : (b : MulAut V) * τ ∈ A₁ ⊔ A₂ := by
      rw [hbτ]
      exact ⟨fun hh => absurd hh hq, fun hh => absurd hh hnot⟩
    exact Or.inl ⟨⟨hbτT, this⟩, fun hh => hq hh.2⟩

theorem card_T₀ [Finite V] : Nat.card (T ⊓ (A₁ ⊔ A₂) : Subgroup (MulAut V)) = 4 := by
  have h1 := Subgroup.card_mul_index ((T ⊓ (A₁ ⊔ A₂)).subgroupOf T)
  have h2 : Nat.card ((T ⊓ (A₁ ⊔ A₂)).subgroupOf T) =
      Nat.card (T ⊓ (A₁ ⊔ A₂) : Subgroup (MulAut V)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [h2, h.index_T₀, h.card_T] at h1
  omega

theorem T₀_conj_mem [Finite V] {x y : MulAut V} (hx : x ∈ T) (hy : y ∈ T ⊓ (A₁ ⊔ A₂)) :
    x * y * x⁻¹ ∈ T ⊓ (A₁ ⊔ A₂) := by
  have := Subgroup.normal_of_index_eq_two h.index_T₀
  have := (inferInstance : ((T ⊓ (A₁ ⊔ A₂)).subgroupOf T).Normal).conj_mem ⟨y, hy.1⟩
    (Subgroup.mem_subgroupOf.mpr hy) ⟨x, hx⟩
  exact Subgroup.mem_subgroupOf.mp this


theorem T₀_struct [Finite V] : ∃ s ∈ A₁, s ≠ 1 ∧ s * s = 1 ∧ s ∈ T ⊓ (A₁ ⊔ A₂) ∧
    ∃ u ∈ A₂, u ≠ 1 ∧ u * u = 1 ∧ u ∈ T ⊓ (A₁ ⊔ A₂) ∧
      ∀ x ∈ T ⊓ (A₁ ⊔ A₂), x = 1 ∨ x = s ∨ x = u ∨ x = s * u := by
  have hc' : ∀ b ∈ A₂, ∀ a ∈ A₁, b * a = a * b := fun b hb a ha => (h.comm a ha b hb).symm
  have hd' : A₂ ⊓ A₁ = ⊥ := by rw [inf_comm]; exact h.disj
  set K : Subgroup (MulAut V) := T ⊓ (A₁ ⊔ A₂) with hKdef
  have hK : Nat.card K = 4 := h.card_T₀
  set P₁ := projSub A₁ A₂ K h.comm with hP₁
  set P₂ := projSub A₂ A₁ K hc' with hP₂
  have hP₁A : P₁ ≤ A₁ := fun a ha => ha.1
  have hP₂A : P₂ ≤ A₂ := fun a ha => ha.1
  have hc12 : ∀ a ∈ P₁, ∀ b ∈ P₂, a * b = b * a := fun a ha b hb => h.comm a (hP₁A ha) b (hP₂A hb)
  have hP₁sq : ∀ x ∈ P₁, x * x = 1 := fun x hx => sq_one_of_projSub h.comm h.disj h.card_A₁ hK hx
  have hP₂sq : ∀ x ∈ P₂, x * x = 1 := fun x hx => sq_one_of_projSub hc' hd' h.card_A₂ hK hx
  have hP₁c : Nat.card P₁ ≤ 2 := card_le_two_of_sq_one h.card_A₁ hP₁A hP₁sq
  have hP₂c : Nat.card P₂ ≤ 2 := card_le_two_of_sq_one h.card_A₂ hP₂A hP₂sq
  have hinf : P₁ ⊓ P₂ = ⊥ := by
    rw [eq_bot_iff, ← h.disj]
    exact inf_le_inf hP₁A hP₂A
  obtain ⟨hcardsup, hsupset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute P₁ P₂ hc12
  rw [hinf, Subgroup.card_bot, mul_one] at hcardsup
  have hKle : K ≤ P₁ ⊔ P₂ := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := h.mem_A₀ hx.2
    have haP : a ∈ P₁ := ⟨ha, b, hb, hx⟩
    have hbP : b ∈ P₂ := ⟨hb, a, ha, by rw [← h.comm a ha b hb]; exact hx⟩
    exact Subgroup.mul_mem_sup haP hbP
  have hfin : Finite (MulAut V) := inferInstance
  have hle4 : Nat.card (P₁ ⊔ P₂ : Subgroup (MulAut V)) ≤ 4 := by
    rw [hcardsup]
    calc Nat.card P₁ * Nat.card P₂ ≤ 2 * 2 := Nat.mul_le_mul hP₁c hP₂c
      _ = 4 := by norm_num
  have hge4 : 4 ≤ Nat.card (P₁ ⊔ P₂ : Subgroup (MulAut V)) := hK ▸ Subgroup.card_le_of_le hKle
  have hKeq : K = P₁ ⊔ P₂ := Subgroup.eq_of_le_of_card_ge hKle (by omega)
  have hprod : Nat.card P₁ * Nat.card P₂ = 4 := by omega
  have hc1 : Nat.card P₁ = 2 := by
    have h0 : 0 < Nat.card P₁ := Nat.card_pos
    have h0' : 0 < Nat.card P₂ := Nat.card_pos
    interval_cases hp : Nat.card P₁ <;> interval_cases hq : Nat.card P₂ <;> omega
  have hc2 : Nat.card P₂ = 2 := by
    rw [hc1] at hprod
    omega
  obtain ⟨s, hsP, hs1⟩ : ∃ s ∈ P₁, s ≠ 1 := by
    have hbot : P₁ ≠ ⊥ := fun hbot => by
      rw [hbot, Subgroup.card_bot] at hc1
      omega
    obtain ⟨y, hy⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hbot
    exact ⟨y, y.2, fun h' => hy (Subtype.ext h')⟩
  obtain ⟨u, huP, hu1⟩ : ∃ u ∈ P₂, u ≠ 1 := by
    have hbot : P₂ ≠ ⊥ := fun hbot => by
      rw [hbot, Subgroup.card_bot] at hc2
      omega
    obtain ⟨y, hy⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hbot
    exact ⟨y, y.2, fun h' => hy (Subtype.ext h')⟩
  refine ⟨s, hP₁A hsP, hs1, hP₁sq s hsP, hKeq ▸ Subgroup.mem_sup_left hsP, u, hP₂A huP, hu1,
    hP₂sq u huP, hKeq ▸ Subgroup.mem_sup_right huP, ?_⟩
  intro x hx
  rw [hKeq] at hx
  have hx' : x ∈ (P₁ : Set (MulAut V)) * (P₂ : Set (MulAut V)) := by
    rw [← hsupset]
    exact hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx'
  rcases card_two_subgroup hc1 hsP hs1 a ha with rfl | rfl <;>
    rcases card_two_subgroup hc2 huP hu1 b hb with rfl | rfl <;> simp


theorem tau_conj_mem {a : MulAut V} (ha : a ∈ A₁) : τ * a * τ⁻¹ ∈ A₂ := by
  have : (MulAut.conj τ) a ∈ A₁.map (MulAut.conj τ).toMonoidHom := ⟨a, ha, rfl⟩
  rw [h.tau_conj] at this
  simpa [MulAut.conj_apply] using this

theorem tau_conj_inv_mem {b : MulAut V} (hb : b ∈ A₂) : τ⁻¹ * b * τ ∈ A₁ := by
  rw [← h.tau_conj] at hb
  obtain ⟨a, ha, rfl⟩ := hb
  simpa [MulAut.conj_apply, mul_assoc] using ha

theorem tau_conj_mem' [Finite V] {b : MulAut V} (hb : b ∈ A₂) : τ * b * τ⁻¹ ∈ A₁ := by
  obtain ⟨x, hx, y, hy, hxy⟩ := h.mem_A₀ h.tau_sq_mem
  have h1 : τ⁻¹ * b * τ ∈ A₁ := h.tau_conj_inv_mem hb
  have h2 : τ * b * τ⁻¹ = (τ * τ) * (τ⁻¹ * b * τ) * (τ * τ)⁻¹ := by group
  rw [h2, hxy]
  have h3 : x * y * (τ⁻¹ * b * τ) * (x * y)⁻¹ = x * (τ⁻¹ * b * τ) * x⁻¹ := by
    have hc : y * (τ⁻¹ * b * τ) = (τ⁻¹ * b * τ) * y := (h.comm _ h1 y hy).symm
    calc x * y * (τ⁻¹ * b * τ) * (x * y)⁻¹ = x * (y * (τ⁻¹ * b * τ)) * y⁻¹ * x⁻¹ := by group
      _ = x * ((τ⁻¹ * b * τ) * y) * y⁻¹ * x⁻¹ := by rw [hc]
      _ = x * (τ⁻¹ * b * τ) * x⁻¹ := by group
  rw [h3]
  exact A₁.mul_mem (A₁.mul_mem hx h1) (A₁.inv_mem hx)

theorem card_V₁_eq_card_V₂ [Finite V] : Nat.card (commV A₁) = Nat.card (commV A₂) := by
  refine Nat.card_congr
    { toFun := fun v => ⟨τ v, conj_commV (fun a ha => h.tau_conj_mem ha) v.2⟩
      invFun := fun v => ⟨τ⁻¹ v, conj_commV (fun a ha => ?_) v.2⟩
      left_inv := fun v => ?_
      right_inv := fun v => ?_ }
  · have := h.tau_conj_inv_mem ha
    simpa using this
  · apply Subtype.ext; show τ⁻¹ (τ v.1) = v.1; simp
  · apply Subtype.ext; show τ (τ⁻¹ v.1) = v.1; simp

theorem card_V₁ [Finite V] : Nat.card (commV A₁) = 16 := by
  have hc : ∀ x ∈ commV A₁, ∀ y ∈ commV A₂, x * y = y * x := fun x _ y _ => mul_comm x y
  have h1 := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (commV A₁) (commV A₂) hc).1
  rw [h.dsum_sup, h.dsum_inf, Subgroup.card_bot, mul_one, Subgroup.card_top, h.card_V,
    ← h.card_V₁_eq_card_V₂] at h1
  have : Nat.card (commV A₁) * Nat.card (commV A₁) = 16 * 16 := by omega
  exact Nat.mul_self_inj.mp this

theorem card_V₂ [Finite V] : Nat.card (commV A₂) = 16 := by
  rw [← h.card_V₁_eq_card_V₂]
  exact h.card_V₁



omit h in
theorem mem_fixV_T₀ {s u : MulAut V}
    (hall : ∀ x ∈ T ⊓ (A₁ ⊔ A₂), x = 1 ∨ x = s ∨ x = u ∨ x = s * u)
    (hs : s ∈ T ⊓ (A₁ ⊔ A₂)) (hu : u ∈ T ⊓ (A₁ ⊔ A₂)) {v : V} :
    v ∈ fixV (T ⊓ (A₁ ⊔ A₂)) ↔ s v = v ∧ u v = v := by
  constructor
  · intro hv
    exact ⟨hv s hs, hv u hu⟩
  · rintro ⟨hsv, huv⟩ x hx
    rcases hall x hx with rfl | rfl | rfl | rfl
    · rfl
    · exact hsv
    · exact huv
    · show s (u v) = v
      rw [huv, hsv]

theorem card_Z₁ [Finite V] {s u : MulAut V} (hsA : s ∈ A₁) (hs1 : s ≠ 1) (hs2 : s * s = 1)
    (hu : u ∈ A₂)
    (hfix : ∀ v : V, v ∈ fixV (T ⊓ (A₁ ⊔ A₂)) ↔ s v = v ∧ u v = v) :
    Nat.card (commV A₁ ⊓ fixV (T ⊓ (A₁ ⊔ A₂)) : Subgroup V) = 4 := by
  obtain ⟨e⟩ := h.e₁
  obtain ⟨c, t, hcA, htA, hc3, hc1, ht2, ht1, htc, hnf⟩ := dihedral3_gens e
  have h4 := card_fix_involution_of_dihedral3 h.sq hc3 ht2 htc hnf
    (W := commV A₁) (fun a ha w hw => commV_invariant_c6 ha hw) hcA htA h.V₁_gen h.card_V₁ hsA hs2 hs1
  have heq : commV A₁ ⊓ fixV (T ⊓ (A₁ ⊔ A₂)) =
      commV A₁ ⊓ MonoidHom.eqLocus s.toMonoidHom (MonoidHom.id V) := by
    ext v
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hv, hf⟩
      exact ⟨hv, ((hfix v).mp hf).1⟩
    · rintro ⟨hv, hf⟩
      refine ⟨hv, (hfix v).mpr ⟨hf, h.A₂_fix_V₁ hu hv⟩⟩
  rw [heq]
  exact h4

theorem card_Z₂ [Finite V] {s u : MulAut V} (hsA : s ∈ A₁) (hu : u ∈ A₂) (hu1 : u ≠ 1)
    (hu2 : u * u = 1)
    (hfix : ∀ v : V, v ∈ fixV (T ⊓ (A₁ ⊔ A₂)) ↔ s v = v ∧ u v = v) :
    Nat.card (commV A₂ ⊓ fixV (T ⊓ (A₁ ⊔ A₂)) : Subgroup V) = 4 := by
  obtain ⟨e⟩ := h.e₂
  obtain ⟨c, t, hcA, htA, hc3, hc1, ht2, ht1, htc, hnf⟩ := dihedral3_gens e
  have h4 := card_fix_involution_of_dihedral3 h.sq hc3 ht2 htc hnf
    (W := commV A₂) (fun a ha w hw => commV_invariant_c6 ha hw) hcA htA h.V₂_gen h.card_V₂ hu hu2 hu1
  have heq : commV A₂ ⊓ fixV (T ⊓ (A₁ ⊔ A₂)) =
      commV A₂ ⊓ MonoidHom.eqLocus u.toMonoidHom (MonoidHom.id V) := by
    ext v
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hv, hf⟩
      exact ⟨hv, ((hfix v).mp hf).2⟩
    · rintro ⟨hv, hf⟩
      refine ⟨hv, (hfix v).mpr ⟨h.A₁_fix_V₂ hsA hv, hf⟩⟩
  rw [heq]
  exact h4

theorem fixV_T₀_decomp [Finite V] {s u : MulAut V} (hsA : s ∈ A₁) (hu : u ∈ A₂)
    (hfix : ∀ v : V, v ∈ fixV (T ⊓ (A₁ ⊔ A₂)) ↔ s v = v ∧ u v = v) :
    fixV (T ⊓ (A₁ ⊔ A₂)) =
      (commV A₁ ⊓ fixV (T ⊓ (A₁ ⊔ A₂))) ⊔ (commV A₂ ⊓ fixV (T ⊓ (A₁ ⊔ A₂))) := by
  apply le_antisymm
  · intro v hv
    have hvt : v ∈ commV A₁ ⊔ commV A₂ := by rw [h.dsum_sup]; exact Subgroup.mem_top v
    obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := Subgroup.mem_sup.mp hvt
    have hsv := ((hfix _).mp hv).1
    have huv := ((hfix _).mp hv).2
    have hsv₂ : s v₂ = v₂ := h.A₁_fix_V₂ hsA hv₂
    have huv₁ : u v₁ = v₁ := h.A₂_fix_V₁ hu hv₁
    have hs1' : s v₁ = v₁ := by
      have h1 : s v₁ * s v₂ = v₁ * v₂ := by rw [← map_mul]; exact hsv
      rw [hsv₂] at h1
      exact mul_right_cancel h1
    have hu2' : u v₂ = v₂ := by
      have h1 : u v₁ * u v₂ = v₁ * v₂ := by rw [← map_mul]; exact huv
      rw [huv₁] at h1
      exact mul_left_cancel h1
    refine Subgroup.mul_mem_sup ⟨hv₁, (hfix _).mpr ⟨hs1', huv₁⟩⟩ ⟨hv₂, (hfix _).mpr ⟨hsv₂, hu2'⟩⟩
  · exact sup_le inf_le_right inf_le_right

theorem Z₁_inf_Z₂ [Finite V] :
    (commV A₁ ⊓ fixV (T ⊓ (A₁ ⊔ A₂))) ⊓ (commV A₂ ⊓ fixV (T ⊓ (A₁ ⊔ A₂))) = ⊥ := by
  rw [eq_bot_iff, ← h.dsum_inf]
  exact inf_le_inf inf_le_left inf_le_left



theorem exists_gens [Finite V] : ∃ s u : MulAut V, SixGens A₁ A₂ T s u := by
  obtain ⟨s, hsA, hs1, hss, hsT, u, huA, hu1, huu, huT, hall⟩ := h.T₀_struct
  exact ⟨s, u, ⟨hsA, hs1, hss, hsT, huA, hu1, huu, huT, hall⟩⟩

end SixCtx

namespace SixGens

variable {A₁ A₂ M T : Subgroup (MulAut V)} {τ : MulAut V} {s u : MulAut V}

theorem fixV_iff [Finite V] (g : SixGens A₁ A₂ T s u) (v : V) :
    v ∈ fixV (sixT0 A₁ A₂ T) ↔ s v = v ∧ u v = v :=
  SixCtx.mem_fixV_T₀ g.all g.sT g.uT

theorem mem_Z₁ [Finite V] (h : SixCtx A₁ A₂ M T τ) (g : SixGens A₁ A₂ T s u) (v : V) :
    v ∈ sixZ₁ A₁ A₂ T ↔ v ∈ commV A₁ ∧ s v = v := by
  unfold sixZ₁
  rw [Subgroup.mem_inf, g.fixV_iff]
  constructor
  · rintro ⟨hv, hs, -⟩
    exact ⟨hv, hs⟩
  · rintro ⟨hv, hs⟩
    exact ⟨hv, hs, h.A₂_fix_V₁ g.uA hv⟩

theorem mem_Z₂ [Finite V] (h : SixCtx A₁ A₂ M T τ) (g : SixGens A₁ A₂ T s u) (v : V) :
    v ∈ sixZ₂ A₁ A₂ T ↔ v ∈ commV A₂ ∧ u v = v := by
  unfold sixZ₂
  rw [Subgroup.mem_inf, g.fixV_iff]
  constructor
  · rintro ⟨hv, -, hu⟩
    exact ⟨hv, hu⟩
  · rintro ⟨hv, hu⟩
    exact ⟨hv, h.A₁_fix_V₂ g.sA hv, hu⟩

theorem card_Z₁ [Finite V] (h : SixCtx A₁ A₂ M T τ) (g : SixGens A₁ A₂ T s u) :
    Nat.card (sixZ₁ A₁ A₂ T) = 4 :=
  SixCtx.card_Z₁ h g.sA g.s1 g.ss g.uA g.fixV_iff

theorem card_Z₂ [Finite V] (h : SixCtx A₁ A₂ M T τ) (g : SixGens A₁ A₂ T s u) :
    Nat.card (sixZ₂ A₁ A₂ T) = 4 :=
  SixCtx.card_Z₂ h g.sA g.uA g.u1 g.uu g.fixV_iff

theorem Z₁_ne_bot [Finite V] (h : SixCtx A₁ A₂ M T τ) (g : SixGens A₁ A₂ T s u) :
    sixZ₁ A₁ A₂ T ≠ ⊥ := fun hb => by
  have := card_Z₁ h g
  rw [hb, Subgroup.card_bot] at this
  omega

theorem Z₂_ne_bot [Finite V] (h : SixCtx A₁ A₂ M T τ) (g : SixGens A₁ A₂ T s u) :
    sixZ₂ A₁ A₂ T ≠ ⊥ := fun hb => by
  have := card_Z₂ h g
  rw [hb, Subgroup.card_bot] at this
  omega

theorem Z₁_le_V₁ : sixZ₁ A₁ A₂ T ≤ commV A₁ := inf_le_left

theorem Z₂_le_V₂ : sixZ₂ A₁ A₂ T ≤ commV A₂ := inf_le_left

theorem fixV_decomp [Finite V] (h : SixCtx A₁ A₂ M T τ) (g : SixGens A₁ A₂ T s u) :
    fixV (sixT0 A₁ A₂ T) = sixZ₁ A₁ A₂ T ⊔ sixZ₂ A₁ A₂ T :=
  SixCtx.fixV_T₀_decomp h g.sA g.uA g.fixV_iff

theorem Z₁_inf_Z₂ [Finite V] (h : SixCtx A₁ A₂ M T τ) : sixZ₁ A₁ A₂ T ⊓ sixZ₂ A₁ A₂ T = ⊥ :=
  SixCtx.Z₁_inf_Z₂ h


theorem Cbar_le_A₀ [Finite V] (h : SixCtx A₁ A₂ M T τ) (g : SixGens A₁ A₂ T s u) :
    sixCbar M (sixZ₁ A₁ A₂ T) ≤ A₁ ⊔ A₂ := by
  intro x hx
  by_contra hxA
  have hxM : x ∈ M := hx.1
  have hτinv : τ⁻¹ ∈ M := M.inv_mem h.tau_mem_M
  have hτinvA : τ⁻¹ ∉ A₁ ⊔ A₂ := fun hh => h.tau_not_mem (by simpa using (A₁ ⊔ A₂).inv_mem hh)
  have hy : τ⁻¹ * x ∈ A₁ ⊔ A₂ :=
    (h.mul_mem_iff_A₀ hτinv hxM).mpr ⟨fun hh => absurd hh hτinvA, fun hh => absurd hh hxA⟩
  obtain ⟨z, hz, hz1⟩ : ∃ z ∈ sixZ₁ A₁ A₂ T, z ≠ 1 := by
    obtain ⟨y, hy⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp (SixGens.Z₁_ne_bot h g)
    exact ⟨y, y.2, fun h' => hy (Subtype.ext h')⟩
  have hxz : x z = z := hx.2 z hz
  have h1 : (τ⁻¹ * x) z ∈ commV A₁ := h.A₀_inv_V₁ hy (SixGens.Z₁_le_V₁ hz)
  have h2 : τ ((τ⁻¹ * x) z) ∈ commV A₂ := conj_commV (fun a ha => h.tau_conj_mem ha) h1
  have h3 : τ ((τ⁻¹ * x) z) = z := by
    show τ (τ⁻¹ (x z)) = z
    rw [hxz]
    simp
  rw [h3] at h2
  have : z ∈ commV A₁ ⊓ commV A₂ := ⟨SixGens.Z₁_le_V₁ hz, h2⟩
  rw [h.dsum_inf, Subgroup.mem_bot] at this
  exact hz1 this

theorem s_mem_D₁ [Finite V] (h : SixCtx A₁ A₂ M T τ) (g : SixGens A₁ A₂ T s u) :
    s ∈ sixD₁ A₁ (sixZ₁ A₁ A₂ T) :=
  ⟨g.sA, fun z hz => ((SixGens.mem_Z₁ h g z).mp hz).2⟩

theorem card_D₁ [Finite V] (h : SixCtx A₁ A₂ M T τ) (g : SixGens A₁ A₂ T s u) :
    Nat.card (sixD₁ A₁ (sixZ₁ A₁ A₂ T)) = 2 := by
  have hD1A : sixD₁ A₁ (sixZ₁ A₁ A₂ T) ≤ A₁ := inf_le_left
  have hdvd : Nat.card (sixD₁ A₁ (sixZ₁ A₁ A₂ T)) ∣ 6 := h.card_A₁ ▸ Subgroup.card_dvd_of_le hD1A
  have hfin : Finite (sixD₁ A₁ (sixZ₁ A₁ A₂ T)) :=
    Nat.finite_of_card_ne_zero (fun h0 => by rw [h0] at hdvd; simp at hdvd)
  have h2dvd : 2 ∣ Nat.card (sixD₁ A₁ (sixZ₁ A₁ A₂ T)) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hord : orderOf (⟨s, s_mem_D₁ h g⟩ : sixD₁ A₁ (sixZ₁ A₁ A₂ T)) = 2 := by
      refine orderOf_eq_prime ?_ ?_
      · apply Subtype.ext
        show s ^ 2 = 1
        rw [pow_two]; exact g.ss
      · intro h'
        exact g.s1 (congrArg Subtype.val h')
    rw [← hord]
    exact orderOf_dvd_natCard _
  have hne6 : Nat.card (sixD₁ A₁ (sixZ₁ A₁ A₂ T)) ≠ 6 := by
    intro h6
    have hD : sixD₁ A₁ (sixZ₁ A₁ A₂ T) = A₁ :=
      Subgroup.eq_of_le_of_card_ge hD1A (by rw [h6, h.card_A₁])
    obtain ⟨e⟩ := h.e₁
    obtain ⟨c, t, hcA, htA, hc3, hc1, ht2, ht1, htc, hnf⟩ := dihedral3_gens e
    have hcD : c ∈ sixD₁ A₁ (sixZ₁ A₁ A₂ T) := by rw [hD]; exact hcA
    have hfix := fix_eq_one_of_dihedral3 h.sq hc3 ht2 htc hnf
      (W := commV A₁) (fun a ha w hw => commV_invariant_c6 ha hw) hcA h.V₁_gen
    obtain ⟨z, hz, hz1⟩ : ∃ z ∈ sixZ₁ A₁ A₂ T, z ≠ 1 := by
      obtain ⟨y, hy⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp (SixGens.Z₁_ne_bot h g)
      exact ⟨y, y.2, fun h' => hy (Subtype.ext h')⟩
    exact hz1 (hfix z (SixGens.Z₁_le_V₁ hz) (hcD.2 z hz))
  generalize Nat.card (sixD₁ A₁ (sixZ₁ A₁ A₂ T)) = n at hdvd h2dvd hne6
  have hle : n ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases n <;> simp_all

theorem Cbar_eq [Finite V] (h : SixCtx A₁ A₂ M T τ) (g : SixGens A₁ A₂ T s u) :
    sixCbar M (sixZ₁ A₁ A₂ T) = sixD₁ A₁ (sixZ₁ A₁ A₂ T) ⊔ A₂ := by
  apply le_antisymm
  · intro x hx
    have hxA := Cbar_le_A₀ h g hx
    obtain ⟨a, ha, b, hb, rfl⟩ := h.mem_A₀ hxA
    have haD : a ∈ sixD₁ A₁ (sixZ₁ A₁ A₂ T) := by
      refine ⟨ha, fun z hz => ?_⟩
      have h1 : (a * b) z = z := hx.2 z hz
      have h2 : b z = z := h.A₂_fix_V₁ hb (SixGens.Z₁_le_V₁ hz)
      have h3 : (a * b) z = a (b z) := rfl
      rw [h3, h2] at h1
      exact h1
    exact Subgroup.mul_mem_sup haD hb
  · refine sup_le ?_ ?_
    · intro a ha
      exact ⟨h.le_M (Subgroup.mem_sup_left ha.1), ha.2⟩
    · intro b hb
      exact ⟨h.le_M (Subgroup.mem_sup_right hb), fun z hz => h.A₂_fix_V₁ hb (SixGens.Z₁_le_V₁ hz)⟩

theorem card_Cbar [Finite V] (h : SixCtx A₁ A₂ M T τ) (g : SixGens A₁ A₂ T s u) :
    Nat.card (sixCbar M (sixZ₁ A₁ A₂ T)) = 12 := by
  rw [Cbar_eq h g]
  have hc : ∀ x ∈ sixD₁ A₁ (sixZ₁ A₁ A₂ T), ∀ y ∈ A₂, x * y = y * x :=
    fun x hx y hy => h.comm x hx.1 y hy
  have h1 := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hc).1
  have hinf : sixD₁ A₁ (sixZ₁ A₁ A₂ T) ⊓ A₂ = ⊥ := by
    rw [eq_bot_iff, ← h.disj]
    exact inf_le_inf inf_le_left le_rfl
  rw [hinf, Subgroup.card_bot, mul_one, card_D₁ h g, h.card_A₂] at h1
  omega

theorem T_inf_Cbar [Finite V] (h : SixCtx A₁ A₂ M T τ) (g : SixGens A₁ A₂ T s u) :
    T ⊓ sixCbar M (sixZ₁ A₁ A₂ T) = sixT0 A₁ A₂ T := by
  apply le_antisymm
  · intro x hx
    exact ⟨hx.1, Cbar_le_A₀ h g hx.2⟩
  · intro x hx
    exact ⟨hx.1, h.le_T hx.1, fun z hz => hz.2 x hx⟩


theorem Cbar_mem [Finite V] (h : SixCtx A₁ A₂ M T τ) (g : SixGens A₁ A₂ T s u) {x : MulAut V}
    (hx : x ∈ sixCbar M (sixZ₁ A₁ A₂ T)) :
    ∃ a ∈ sixD₁ A₁ (sixZ₁ A₁ A₂ T), ∃ b ∈ A₂, x = a * b := by
  have hxA := Cbar_le_A₀ h g hx
  obtain ⟨a, ha, b, hb, rfl⟩ := h.mem_A₀ hxA
  refine ⟨a, ⟨ha, fun z hz => ?_⟩, b, hb, rfl⟩
  have h1 : (a * b) z = z := hx.2 z hz
  have h2 : b z = z := h.A₂_fix_V₁ hb (SixGens.Z₁_le_V₁ hz)
  have h3 : (a * b) z = a (b z) := rfl
  rw [h3, h2] at h1
  exact h1

end SixGens

namespace SixCtx

variable {A₁ A₂ M T : Subgroup (MulAut V)} {τ : MulAut V}

theorem rot₂ [Finite V] (h : SixCtx A₁ A₂ M T τ) :
    ∃ c t : MulAut V, c ∈ A₂ ∧ t ∈ A₂ ∧ orderOf c = 3 ∧ c ^ 3 = 1 ∧ t * t = 1 ∧ t * c * t = c⁻¹ ∧
      (∀ b : MulAut V, b ∈ A₂ → ∃ i j : ℕ, b = c ^ i * t ^ j) ∧
      (∀ b : MulAut V, b ∈ A₂ → Odd (orderOf b) → b ∈ Subgroup.zpowers c) ∧
      (∀ w : V, w ∈ commV A₂ → c w = w → w = 1) := by
  obtain ⟨e⟩ := h.e₂
  obtain ⟨c, t, hcA, htA, hc3, hc1, ht2, ht1, htc, hnf⟩ := dihedral3_gens e
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨c, t, hcA, htA, orderOf_eq_prime hc3 hc1, hc3, ht2, htc, hnf, ?_, ?_⟩
  · intro b hb hodd
    obtain ⟨i, j, rfl⟩ := hnf b hb
    have hpowt : t ^ j = 1 ∨ t ^ j = t := by
      clear hb hodd
      induction j with
      | zero => left; simp
      | succ n ih =>
        rcases ih with h' | h'
        · right; rw [pow_succ, h', one_mul]
        · left; rw [pow_succ, h', ht2]
    rcases hpowt with hj | hj
    · rw [hj, mul_one]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers c) i
    · rw [hj] at hodd ⊢
      have hsq := dihedral_refl_sq ht2 htc i
      have h2 : orderOf (c ^ i * t) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
      have h1 : orderOf (c ^ i * t) = 1 := by
        rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h' | h'
        · exact h'
        · rw [h'] at hodd
          exact absurd hodd (by decide)
      rw [orderOf_eq_one_iff.mp h1]
      exact (Subgroup.zpowers c).one_mem
  · exact fix_eq_one_of_dihedral3 h.sq hc3 ht2 htc hnf
      (W := commV A₂) (fun a ha w hw => commV_invariant_c6 ha hw) hcA h.V₂_gen

end SixCtx

namespace SixGens

variable {A₁ A₂ M T : Subgroup (MulAut V)} {τ : MulAut V} {s u : MulAut V}

theorem odd_mem [Finite V] (h : SixCtx A₁ A₂ M T τ) (g : SixGens A₁ A₂ T s u) {c : MulAut V}
    (hodd : ∀ b ∈ A₂, Odd (orderOf b) → b ∈ Subgroup.zpowers c) {x : MulAut V}
    (hx : x ∈ sixCbar M (sixZ₁ A₁ A₂ T)) (hxo : Odd (orderOf x)) : x ∈ Subgroup.zpowers c := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Cbar_mem h g hx
  rcases card_two_subgroup (card_D₁ h g) (s_mem_D₁ h g) g.s1 a ha with rfl | rfl
  · rw [one_mul] at hxo ⊢
    exact hodd b hb hxo
  · exfalso
    have hcomm : Commute a b := h.comm a g.sA b hb
    have hk : (a * b) ^ orderOf (a * b) = 1 := pow_orderOf_eq_one _
    rw [hcomm.mul_pow, pow_odd_of_sq_eq_one g.ss hxo] at hk
    have hmem : a ∈ A₁ ⊓ A₂ := by
      refine ⟨g.sA, ?_⟩
      have : a = (b ^ orderOf (a * b))⁻¹ := eq_inv_of_mul_eq_one_left hk
      rw [this]
      exact A₂.inv_mem (A₂.pow_mem hb _)
    rw [h.disj, Subgroup.mem_bot] at hmem
    exact g.s1 hmem

theorem oTwoUpper_Cbar [Finite V] (h : SixCtx A₁ A₂ M T τ) (g : SixGens A₁ A₂ T s u) {c : MulAut V}
    (hcA : c ∈ A₂) (hc3 : orderOf c = 3)
    (hodd : ∀ b ∈ A₂, Odd (orderOf b) → b ∈ Subgroup.zpowers c) :
    oTwoUpper (sixCbar M (sixZ₁ A₁ A₂ T)) = Subgroup.zpowers c := by
  apply le_antisymm
  · rw [oTwoUpper, Subgroup.closure_le]
    rintro x ⟨hx, hxo⟩
    exact odd_mem h g hodd hx hxo
  · rw [Subgroup.zpowers_le]
    refine mem_oTwoUpper_of_odd ?_ ?_
    · exact ⟨h.le_M (Subgroup.mem_sup_right hcA), fun z hz => h.A₂_fix_V₁ hcA (SixGens.Z₁_le_V₁ hz)⟩
    · rw [hc3]; exact ⟨1, rfl⟩

end SixGens

theorem commV_zpowers_eq [Finite V] {A₂ : Subgroup (MulAut V)} {c : MulAut V} (hcA : c ∈ A₂)
    (hfix : ∀ w : V, w ∈ commV A₂ → c w = w → w = 1) :
    commV (Subgroup.zpowers c) = commV A₂ :=
  le_antisymm (commV_mono_c6 (Subgroup.zpowers_le.mpr hcA))
    (le_commV_zpowers (fun _ hw => commV_invariant_c6 hcA hw) hfix)


namespace SixCtx

variable {A₁ A₂ M T : Subgroup (MulAut V)} {τ : MulAut V}

theorem swap_mem [Finite V] (h : SixCtx A₁ A₂ M T τ) {x : MulAut V} (hx : x ∈ M)
    (hxA : x ∉ A₁ ⊔ A₂) :
    (∀ v : V, v ∈ commV A₁ → x v ∈ commV A₂) ∧ (∀ v : V, v ∈ commV A₂ → x v ∈ commV A₁) := by
  have hτinv : τ⁻¹ ∈ M := M.inv_mem h.tau_mem_M
  have hτinvA : τ⁻¹ ∉ A₁ ⊔ A₂ := fun hh => h.tau_not_mem (by simpa using (A₁ ⊔ A₂).inv_mem hh)
  have hy : τ⁻¹ * x ∈ A₁ ⊔ A₂ :=
    (h.mul_mem_iff_A₀ hτinv hx).mpr ⟨fun hh => absurd hh hτinvA, fun hh => absurd hh hxA⟩
  have hxτ : x = τ * (τ⁻¹ * x) := by group
  constructor
  · intro v hv
    have h1 : (τ⁻¹ * x) v ∈ commV A₁ := h.A₀_inv_V₁ hy hv
    have h2 := conj_commV (fun a ha => h.tau_conj_mem ha) h1
    rw [hxτ]
    exact h2
  · intro v hv
    have h1 : (τ⁻¹ * x) v ∈ commV A₂ := h.A₀_inv_V₂ hy hv
    have h2 := conj_commV (fun a ha => h.tau_conj_mem' ha) h1
    rw [hxτ]
    exact h2

end SixCtx

namespace SixGens

variable {A₁ A₂ M T : Subgroup (MulAut V)} {τ : MulAut V} {s u : MulAut V}

theorem s_moves_V₁ [Finite V] (h : SixCtx A₁ A₂ M T τ) (g : SixGens A₁ A₂ T s u) :
    ∃ v ∈ commV A₁, s v ≠ v := by
  by_contra hcon
  push Not at hcon
  have hle : commV A₁ ≤ sixZ₁ A₁ A₂ T := fun v hv => (mem_Z₁ h g v).mpr ⟨hv, hcon v hv⟩
  have := Subgroup.card_le_of_le hle
  rw [h.card_V₁, card_Z₁ h g] at this
  omega

theorem T₀_fix_V₁ [Finite V] (h : SixCtx A₁ A₂ M T τ) (g : SixGens A₁ A₂ T s u) {x : MulAut V}
    (hx : x ∈ T ⊓ (A₁ ⊔ A₂)) : (∀ v ∈ commV A₁, x v = v) ↔ (x = 1 ∨ x = u) := by
  constructor
  · intro hv
    obtain ⟨v, hv1, hsv⟩ := s_moves_V₁ h g
    rcases g.all x hx with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact absurd (hv v hv1) hsv
    · exact Or.inr rfl
    · exfalso
      apply hsv
      have := hv v hv1
      have h3 : (s * u) v = s (u v) := rfl
      rw [h3, h.A₂_fix_V₁ g.uA hv1] at this
      exact this
  · rintro (rfl | rfl) v hv
    · rfl
    · exact h.A₂_fix_V₁ g.uA hv

theorem tau_Z₁ [Finite V] (h : SixCtx A₁ A₂ M T τ) {z : V}
    (hz : z ∈ sixZ₁ A₁ A₂ T) : τ z ∈ sixZ₂ A₁ A₂ T := by
  refine ⟨conj_commV (fun a ha => h.tau_conj_mem ha) (Z₁_le_V₁ hz), fun x hx => ?_⟩
  have hτinvT : τ⁻¹ ∈ T := T.inv_mem h.tau_mem
  have hconj : τ⁻¹ * x * τ ∈ T ⊓ (A₁ ⊔ A₂) := by
    have := h.T₀_conj_mem hτinvT hx
    simpa [mul_assoc] using this
  have h1 : (τ⁻¹ * x * τ) z = z := hz.2 _ hconj
  have h2 : x (τ z) = τ z := by
    have h3 : τ ((τ⁻¹ * x * τ) z) = x (τ z) := by
      show τ (τ⁻¹ (x (τ z))) = x (τ z)
      simp
    rw [← h3, h1]
  exact h2

theorem tau_Z₂ [Finite V] (h : SixCtx A₁ A₂ M T τ) {z : V}
    (hz : z ∈ sixZ₂ A₁ A₂ T) : τ z ∈ sixZ₁ A₁ A₂ T := by
  refine ⟨conj_commV (fun a ha => h.tau_conj_mem' ha) (Z₂_le_V₂ hz), fun x hx => ?_⟩
  have hτinvT : τ⁻¹ ∈ T := T.inv_mem h.tau_mem
  have hconj : τ⁻¹ * x * τ ∈ T ⊓ (A₁ ⊔ A₂) := by
    have := h.T₀_conj_mem hτinvT hx
    simpa [mul_assoc] using this
  have h1 : (τ⁻¹ * x * τ) z = z := hz.2 _ hconj
  have h3 : τ ((τ⁻¹ * x * τ) z) = x (τ z) := by
    show τ (τ⁻¹ (x (τ z))) = x (τ z)
    simp
  rw [← h3, h1]

end SixGens


namespace SixCtx

variable {A₁ A₂ M T : Subgroup (MulAut V)} {τ : MulAut V}

theorem inv_tau_mul_mem [Finite V] (h : SixCtx A₁ A₂ M T τ) {x : MulAut V} (hx : x ∈ M)
    (hxA : x ∉ A₁ ⊔ A₂) : τ⁻¹ * x ∈ A₁ ⊔ A₂ := by
  have hτinv : τ⁻¹ ∈ M := M.inv_mem h.tau_mem_M
  have hτinvA : τ⁻¹ ∉ A₁ ⊔ A₂ := fun hh => h.tau_not_mem (by simpa using (A₁ ⊔ A₂).inv_mem hh)
  exact (h.mul_mem_iff_A₀ hτinv hx).mpr ⟨fun hh => absurd hh hτinvA, fun hh => absurd hh hxA⟩

end SixCtx

namespace SixGens

variable {A₁ A₂ M T : Subgroup (MulAut V)} {τ : MulAut V} {s u : MulAut V}

theorem fixV_T_le_Z [Finite V] (h : SixCtx A₁ A₂ M T τ) (g : SixGens A₁ A₂ T s u) {z : V}
    (hz : z ∈ fixV T) : z ∈ sixZ₁ A₁ A₂ T ⊔ sixZ₂ A₁ A₂ T := by
  rw [← fixV_decomp h g]
  exact fun x hx => hz x hx.1

theorem diag_fix [Finite V] (h : SixCtx A₁ A₂ M T τ) {z : V}
    (hz : z ∈ sixZ₂ A₁ A₂ T) : τ z * z ∈ fixV T := by
  intro x hx
  have hτz : τ z ∈ sixZ₁ A₁ A₂ T := tau_Z₂ h hz
  by_cases hxA : x ∈ A₁ ⊔ A₂
  · have hx0 : x ∈ T ⊓ (A₁ ⊔ A₂) := ⟨hx, hxA⟩
    rw [map_mul, hτz.2 x hx0, hz.2 x hx0]
  · have hy : τ⁻¹ * x ∈ T ⊓ (A₁ ⊔ A₂) :=
      ⟨T.mul_mem (T.inv_mem h.tau_mem) hx, h.inv_tau_mul_mem (h.le_T hx) hxA⟩
    have hττ : τ * τ ∈ T ⊓ (A₁ ⊔ A₂) := ⟨T.mul_mem h.tau_mem h.tau_mem, h.tau_sq_mem⟩
    have hxτ : x = τ * (τ⁻¹ * x) := by group
    have h1 : (τ⁻¹ * x) (τ z) = τ z := hτz.2 _ hy
    have h2 : (τ⁻¹ * x) z = z := hz.2 _ hy
    have h3 : τ (τ z) = z := hz.2 (τ * τ) hττ
    calc x (τ z * z) = τ ((τ⁻¹ * x) (τ z * z)) := by
          conv_lhs => rw [hxτ]
          rfl
      _ = τ (τ z * z) := by rw [map_mul, h1, h2]
      _ = τ z * z := by rw [map_mul, h3, mul_comm]

end SixGens


namespace SixGens

variable {A₁ A₂ M T : Subgroup (MulAut V)} {τ : MulAut V} {s u : MulAut V}

theorem A₂_le_Cbar [Finite V] (h : SixCtx A₁ A₂ M T τ) :
    A₂ ≤ sixCbar M (sixZ₁ A₁ A₂ T) := fun _ hb =>
  ⟨h.le_M (Subgroup.mem_sup_right hb), fun _ hz => h.A₂_fix_V₁ hb (Z₁_le_V₁ hz)⟩

theorem Cbar_sup_T [Finite V] (h : SixCtx A₁ A₂ M T τ) :
    sixCbar M (sixZ₁ A₁ A₂ T) ⊔ T = M := by
  apply le_antisymm
  · exact sup_le inf_le_left h.le_T
  · have hA₂ : A₂ ≤ sixCbar M (sixZ₁ A₁ A₂ T) ⊔ T := (A₂_le_Cbar h).trans le_sup_left
    have hτ : τ ∈ sixCbar M (sixZ₁ A₁ A₂ T) ⊔ T := Subgroup.mem_sup_right h.tau_mem
    have hA₁ : A₁ ≤ sixCbar M (sixZ₁ A₁ A₂ T) ⊔ T := by
      intro a ha
      have h1 : τ * a * τ⁻¹ ∈ sixCbar M (sixZ₁ A₁ A₂ T) ⊔ T := hA₂ (h.tau_conj_mem ha)
      have h2 : a = τ⁻¹ * (τ * a * τ⁻¹) * τ := by group
      rw [h2]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hτ) h1) hτ
    intro x hx
    by_cases hxA : x ∈ A₁ ⊔ A₂
    · exact (sup_le hA₁ hA₂) hxA
    · have hy := h.inv_tau_mul_mem hx hxA
      have hy' : τ⁻¹ * x ∈ sixCbar M (sixZ₁ A₁ A₂ T) ⊔ T := (sup_le hA₁ hA₂) hy
      have : x = τ * (τ⁻¹ * x) := by group
      rw [this]
      exact Subgroup.mul_mem _ hτ hy'

end SixGens


namespace SixGens

variable {A₁ A₂ M T : Subgroup (MulAut V)} {τ : MulAut V} {s u : MulAut V}

theorem A₂_le_sup {c t : MulAut V} (hc3 : c ^ 3 = 1) (ht2 : t * t = 1)
    (hnf : ∀ b : MulAut V, b ∈ A₂ → ∃ i j : ℕ, b = c ^ i * t ^ j) (hu : u ∈ A₂) (hu1 : u ≠ 1)
    (huu : u * u = 1) : A₂ ≤ Subgroup.zpowers c ⊔ Subgroup.zpowers u := by
  obtain ⟨i, j, hij⟩ := hnf u hu
  have hu_eq : u = c ^ i * t := by
    rcases pow_eq_one_or_self ht2 j with hj | hj
    · exfalso
      rw [hj, mul_one] at hij
      apply hu1
      have h3 : u ^ 3 = 1 := by rw [hij, ← pow_mul, mul_comm, pow_mul, hc3, one_pow]
      have h2 : u ^ 2 = 1 := by rw [pow_two]; exact huu
      have : u ^ 3 = u ^ 2 * u := by rw [pow_succ]
      rw [h2, one_mul] at this
      rw [← this]
      exact h3
    · rw [hj] at hij
      exact hij
  have hcmem : c ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers u :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers c)
  have ht : t ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers u := by
    have : t = (c ^ i)⁻¹ * u := by rw [hu_eq]; group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.pow_mem _ hcmem i))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers u))
  intro b hb
  obtain ⟨k, l, rfl⟩ := hnf b hb
  exact Subgroup.mul_mem _ (Subgroup.pow_mem _ hcmem k) (Subgroup.pow_mem _ ht l)

theorem Cbar_le_sup [Finite V] (h : SixCtx A₁ A₂ M T τ) (g : SixGens A₁ A₂ T s u) {c t : MulAut V}
    (hc3 : c ^ 3 = 1) (ht2 : t * t = 1)
    (hnf : ∀ b : MulAut V, b ∈ A₂ → ∃ i j : ℕ, b = c ^ i * t ^ j) :
    sixCbar M (sixZ₁ A₁ A₂ T) ≤ sixT0 A₁ A₂ T ⊔ Subgroup.zpowers c := by
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Cbar_mem h g hx
  have haT : a ∈ sixT0 A₁ A₂ T := by
    rcases card_two_subgroup (card_D₁ h g) (s_mem_D₁ h g) g.s1 a ha with rfl | rfl
    · exact (sixT0 A₁ A₂ T).one_mem
    · exact g.sT
  have hbS : b ∈ sixT0 A₁ A₂ T ⊔ Subgroup.zpowers c := by
    have h1 := A₂_le_sup hc3 ht2 hnf g.uA g.u1 g.uu
    refine (h1.trans (sup_le ?_ ?_)) hb
    · exact le_sup_right
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_sup_left g.uT
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left haT) hbS

end SixGens

end CFSG.Quasithin
