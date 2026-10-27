module

public import CFSG.Quasithin.Background.Module
public import Mathlib.GroupTheory.FiniteAbelian.Duality
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.Quasithin.MS93.S38E

open CFSG.Quasithin

structure Pairing (Y Q : Type*) [CommGroup Y] [CommGroup Q] where
  f : Y → Y → Q
  map_mul_left : ∀ a b c, f (a * b) c = f a c * f b c
  map_mul_right : ∀ a b c, f a (b * c) = f a b * f a c
  self : ∀ a, f a a = 1
  nondeg : ∀ a, (∀ b, f a b = 1) → a = 1

namespace Pairing

variable {Y Q : Type*} [CommGroup Y] [CommGroup Q] (p : Pairing Y Q)

theorem one_left (b : Y) : p.f 1 b = 1 := by
  have h := p.map_mul_left 1 1 b
  rw [one_mul] at h
  exact left_eq_mul.mp h

theorem one_right (a : Y) : p.f a 1 = 1 := by
  have h := p.map_mul_right a 1 1
  rw [one_mul] at h
  exact left_eq_mul.mp h

theorem inv_left (a b : Y) : p.f a⁻¹ b = (p.f a b)⁻¹ := by
  have h := p.map_mul_left a a⁻¹ b
  rw [mul_inv_cancel, one_left] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem inv_right (a b : Y) : p.f a b⁻¹ = (p.f a b)⁻¹ := by
  have h := p.map_mul_right a b b⁻¹
  rw [mul_inv_cancel, one_right] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem swap (a b : Y) : p.f b a = (p.f a b)⁻¹ := by
  have h := p.self (a * b)
  rw [p.map_mul_left, p.map_mul_right, p.map_mul_right, p.self, p.self, one_mul, mul_one] at h
  exact eq_inv_of_mul_eq_one_right h

theorem div_left (a b c : Y) : p.f (a * b⁻¹) c = p.f a c * (p.f b c)⁻¹ := by
  rw [p.map_mul_left, p.inv_left]

theorem div_right (a b c : Y) : p.f a (b * c⁻¹) = p.f a b * (p.f a c)⁻¹ := by
  rw [p.map_mul_right, p.inv_right]

theorem nondeg_right (b : Y) (h : ∀ a, p.f a b = 1) : b = 1 :=
  p.nondeg b fun a => by rw [p.swap, h a, inv_one]

@[expose] def perp (S : Subgroup Y) : Subgroup Y where
  carrier := {a | ∀ s ∈ S, p.f a s = 1}
  one_mem' := fun s _ => p.one_left s
  mul_mem' := fun ha hb s hs => by rw [p.map_mul_left, ha s hs, hb s hs, one_mul]
  inv_mem' := fun ha s hs => by rw [p.inv_left, ha s hs, inv_one]

theorem mem_perp {S : Subgroup Y} {a : Y} : a ∈ p.perp S ↔ ∀ s ∈ S, p.f a s = 1 := Iff.rfl

@[expose] def IsInv (I : Subgroup (MulAut Y)) : Prop :=
  ∀ g ∈ I, ∀ a b : Y, p.f (g a) (g b) = p.f a b

variable {p} in
theorem IsInv.mono {I J : Subgroup (MulAut Y)} (hJ : p.IsInv J) (h : I ≤ J) : p.IsInv I :=
  fun g hg => hJ g (h hg)

theorem f_apply_left {I : Subgroup (MulAut Y)} (hI : p.IsInv I) {g : MulAut Y} (hg : g ∈ I)
    (a b : Y) : p.f (g a) b = p.f a (g⁻¹ b) := by
  conv_lhs => rw [show b = g (g⁻¹ b) by simp]
  exact hI g hg a _

theorem mem_perp_commV {P : Subgroup (MulAut Y)} (hP : p.IsInv P) {x : Y}
    (hx : ∀ g ∈ P, g x = x) : x ∈ p.perp (commV P) := by
  rw [mem_perp]
  intro s hs
  induction hs using Subgroup.closure_induction with
  | mem s hs =>
    obtain ⟨g, hg, y, rfl⟩ := hs
    have h1 : p.f x (g y) = p.f x y := by
      conv_lhs => rw [← hx g hg]
      exact hP g hg x y
    rw [p.div_right, h1, mul_inv_cancel]
  | one => exact p.one_right x
  | mul a b _ _ ha hb => rw [p.map_mul_right, ha, hb, one_mul]
  | inv a _ ha => rw [p.inv_right, ha, inv_one]

theorem fixV_le_perp_commV {K : Subgroup (MulAut Y)} (hK : p.IsInv K) :
    fixV K ≤ p.perp (commV K) :=
  fun _ hx => p.mem_perp_commV hK fun g hg => hx g hg

theorem perp_commV_le_fixV {K : Subgroup (MulAut Y)} (hK : p.IsInv K) :
    p.perp (commV K) ≤ fixV K := by
  intro a ha k hk
  have key : ∀ b, p.f (k a * a⁻¹) b = 1 := by
    intro b
    rw [p.div_left, p.f_apply_left hK hk]
    have h1 : p.f a (k⁻¹ b * b⁻¹) = 1 :=
      ha _ (Subgroup.subset_closure ⟨k⁻¹, K.inv_mem hk, b, rfl⟩)
    rw [p.div_right] at h1
    exact mul_inv_eq_one.mpr (mul_inv_eq_one.mp h1)
  exact mul_inv_eq_one.mp (p.nondeg _ key)

theorem perp_commV_eq_fixV {K : Subgroup (MulAut Y)} (hK : p.IsInv K) :
    p.perp (commV K) = fixV K :=
  le_antisymm (p.perp_commV_le_fixV hK) (p.fixV_le_perp_commV hK)

end Pairing

namespace Pairing

variable {Y : Type*} [CommGroup Y] (p : Pairing Y ℂˣ)

theorem card_hom_units (S : Type*) [CommGroup S] [Finite S] : Nat.card (S →* ℂˣ) = Nat.card S := by
  have : NeZero (Monoid.exponent S) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  have : NeZero ((Monoid.exponent S : ℕ) : ℂ) := ⟨by exact_mod_cast (NeZero.ne _)⟩
  exact CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity S ℂ

@[expose] def toHomRight (S : Subgroup Y) : Y →* (↥S →* ℂˣ) where
  toFun a :=
    { toFun := fun s => p.f a s
      map_one' := p.one_right a
      map_mul' := fun s t => p.map_mul_right a s t }
  map_one' := by
    ext s
    exact congrArg Units.val (p.one_left s)
  map_mul' a b := by
    ext s
    exact congrArg Units.val (p.map_mul_left a b s)

theorem ker_toHomRight (S : Subgroup Y) : (p.toHomRight S).ker = p.perp S := by
  ext a
  simp only [MonoidHom.mem_ker, mem_perp]
  constructor
  · intro h s hs
    have := congrArg (fun φ : ↥S →* ℂˣ => φ ⟨s, hs⟩) h
    exact this
  · intro h
    ext s
    exact congrArg Units.val (h s s.2)

variable [Finite Y]

theorem index_perp_le (S : Subgroup Y) : (p.perp S).index ≤ Nat.card S := by
  rw [← p.ker_toHomRight, Subgroup.index_ker, ← card_hom_units ↥S]
  exact Nat.card_mono (Set.toFinite _) (Set.subset_univ _) |>.trans_eq (Nat.card_univ)

theorem card_le_index_perp (S : Subgroup Y) : Nat.card S ≤ (p.perp S).index := by
  rw [Subgroup.index, ← card_hom_units (Y ⧸ p.perp S)]
  let φ : ↥S →* ((Y ⧸ p.perp S) →* ℂˣ) :=
    { toFun := fun s => QuotientGroup.lift (p.perp S)
        { toFun := fun a => p.f a s
          map_one' := p.one_left s
          map_mul' := fun a b => p.map_mul_left a b s }
        (fun a ha => ha s s.2)
      map_one' := by
        ext a
        exact congrArg Units.val (p.one_right a)
      map_mul' := fun s t => by
        ext a
        exact congrArg Units.val (p.map_mul_right a s t) }
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro s hs
    rw [MonoidHom.mem_ker] at hs
    have key : ∀ a, p.f a s = 1 := fun a =>
      Units.ext (congrArg (fun ψ : (Y ⧸ p.perp S) →* ℂˣ => (ψ (QuotientGroup.mk a) : ℂ)) hs)
    have := p.nondeg_right (s : Y) key
    exact (Subgroup.mem_bot).mpr (Subtype.ext this)
  exact Nat.card_le_card_of_injective φ hinj

theorem card_mul_card_perp (S : Subgroup Y) : Nat.card S * Nat.card (p.perp S) = Nat.card Y := by
  rw [← (p.perp S).index_mul_card, le_antisymm (p.index_perp_le S) (p.card_le_index_perp S)]

theorem card_commV_mul_card_fixV {E : Subgroup (MulAut Y)} (hE : p.IsInv E) :
    Nat.card (commV E) * Nat.card (fixV E) = Nat.card Y := by
  rw [← p.perp_commV_eq_fixV hE]
  exact p.card_mul_card_perp _

end Pairing

end CFSG.Quasithin.MS93.S38E
