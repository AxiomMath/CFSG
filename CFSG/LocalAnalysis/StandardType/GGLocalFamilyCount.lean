module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.StandardType

@[expose] def LocalFamilies {ι : Type*} {F : ι → Type*} [∀ i, Field (F i)] (R : ι → ι → Prop)
    (T : ∀ i j : ι, R i j → (F j ≃+* F i)) (A : Type*) (key : A → ι) : Type _ :=
  {z : (a : A) → F (key a) //
    ∀ (a b : A) (h : R (key a) (key b)), T (key a) (key b) h (z b) * z a = 1}

private def localFamiliesPiTwo {β : Type*} [DecidableEq β] (F : β → Type*) (a b : β)
    (hab : ∀ e : β, e = a ∨ e = b) (hne : a ≠ b) :
    ((e : β) → F e) ≃ F a × F b where
  toFun z := (z a, z b)
  invFun p := fun e =>
    if h : e = a then h ▸ p.1 else (hab e).resolve_left h ▸ p.2
  left_inv z := by
    funext e
    rcases hab e with rfl | rfl
    · simp
    · simp [hne.symm]
  right_inv p := by
    simp [hne, hne.symm]

theorem card_localFamilies_split {ι : Type*} {F : ι → Type*} [∀ i, Field (F i)]
    (R : ι → ι → Prop) (T : ∀ i j : ι, R i j → (F j ≃+* F i)) (A : Type*) (key : A → ι)
    (p : A → Prop) [DecidablePred p]
    (hp : ∀ a b : A, R (key a) (key b) → (p a ↔ p b)) :
    Nat.card (LocalFamilies R T A key) =
      Nat.card (LocalFamilies R T {a // p a} (fun a => key a.1)) *
        Nat.card (LocalFamilies R T {a // ¬ p a} (fun a => key a.1)) := by
  classical
  have hh : ∀ z : (a : A) → F (key a),
      (∀ (a b : A) (h : R (key a) (key b)), T (key a) (key b) h (z b) * z a = 1) ↔
      (∀ (a b : {a // p a}) (h : R (key a.1) (key b.1)),
        T (key a.1) (key b.1) h (z b.1) * z a.1 = 1) ∧
      (∀ (a b : {a // ¬ p a}) (h : R (key a.1) (key b.1)),
        T (key a.1) (key b.1) h (z b.1) * z a.1 = 1) := by
    intro z
    constructor
    · intro hz
      exact ⟨fun a b h => hz a.1 b.1 h, fun a b h => hz a.1 b.1 h⟩
    · rintro ⟨h1, h2⟩ a b h
      by_cases hpa : p a
      · exact h1 ⟨a, hpa⟩ ⟨b, (hp a b h).mp hpa⟩ h
      · exact h2 ⟨a, hpa⟩ ⟨b, fun hb => hpa ((hp a b h).mpr hb)⟩ h
  exact (Nat.card_congr ((Equiv.subtypeEquiv
    (Equiv.piEquivPiSubtypeProd p (fun a => F (key a))) hh).trans
    Equiv.subtypeProdEquivProd)).trans (Nat.card_prod _ _)

theorem card_localFamilies_prod {ι : Type*} {F : ι → Type*} [∀ i, Field (F i)]
    (R : ι → ι → Prop) (T : ∀ i j : ι, R i j → (F j ≃+* F i)) (A : Type*) (key : A → ι)
    {C : Type*} [Fintype C] (cls : A → C)
    (hcls : ∀ a b : A, R (key a) (key b) → cls a = cls b) :
    Nat.card (LocalFamilies R T A key) =
      ∏ c : C, Nat.card (LocalFamilies R T {a // cls a = c} (fun a => key a.1)) := by
  classical
  let e0 : ((a : A) → F (key a)) ≃ ((c : C) → (a : {a // cls a = c}) → F (key a.1)) :=
    { toFun := fun y c a => y a.1
      invFun := fun z a => z (cls a) ⟨a, rfl⟩
      left_inv := fun y => rfl
      right_inv := fun z => by
        funext c a
        obtain ⟨a, rfl⟩ := a
        rfl }
  have hpred : ∀ y : (a : A) → F (key a),
      (∀ (a b : A) (h : R (key a) (key b)), T (key a) (key b) h (y b) * y a = 1) ↔
      ∀ c : C, ∀ (a b : {a // cls a = c}) (h : R (key a.1) (key b.1)),
        T (key a.1) (key b.1) h (e0 y c b) * e0 y c a = 1 := by
    intro y
    constructor
    · intro hy c a b h
      exact hy a.1 b.1 h
    · intro hz a b h
      have hb : cls b = cls a := (hcls a b h).symm
      exact hz (cls a) ⟨a, rfl⟩ ⟨b, hb⟩ h
  have e1 : LocalFamilies R T A key ≃
      ((c : C) → {z : (a : {a // cls a = c}) → F (key a.1) //
        ∀ (a b : {a // cls a = c}) (h : R (key a.1) (key b.1)),
          T (key a.1) (key b.1) h (z b) * z a = 1}) :=
    (Equiv.subtypeEquiv e0 hpred).trans
      (Equiv.subtypePiEquivPi (α := C) (β := fun c => (a : {a // cls a = c}) → F (key a.1))
        (p := fun c z => ∀ (a b : {a // cls a = c}) (h : R (key a.1) (key b.1)),
          T (key a.1) (key b.1) h (z b) * z a = 1))
  rw [Nat.card_congr e1]
  exact Nat.card_pi

theorem card_localFamilies_unique {ι : Type*} {F : ι → Type*} [∀ i, Field (F i)]
    (R : ι → ι → Prop) (T : ∀ i j : ι, R i j → (F j ≃+* F i)) (A : Type*) [Unique A]
    (key : A → ι) (h : R (key default) (key default)) :
    Nat.card (LocalFamilies R T A key) =
      Nat.card {u : F (key default) // T (key default) (key default) h u * u = 1} := by
  classical
  refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.piUnique (fun a => F (key a))) ?_)
  intro z
  constructor
  · intro hz
    exact hz default default h
  · intro hz a b h'
    obtain rfl : a = default := Subsingleton.elim a default
    obtain rfl : b = default := Subsingleton.elim b default
    rw [Subsingleton.elim h' h]
    exact hz

theorem card_localFamilies_pair {ι : Type*} {F : ι → Type*} [∀ i, Field (F i)]
    (R : ι → ι → Prop) (T : ∀ i j : ι, R i j → (F j ≃+* F i))
    (A : Type*) (key : A → ι) (a b : A) (hne : a ≠ b) (hcover : ∀ x : A, x = a ∨ x = b)
    (hab : R (key a) (key b)) (hba : R (key b) (key a))
    (hinv : ∀ (x y : A) (hxy : R (key x) (key y)) (hyx : R (key y) (key x)),
      T (key y) (key x) hyx = (T (key x) (key y) hxy).symm)
    (hfix : ∀ x : A, ¬ R (key x) (key x)) :
    Nat.card (LocalFamilies R T A key) = Nat.card (F (key a)) - 1 := by
  classical
  let f : F (key b) ≃+* F (key a) := T (key a) (key b) hab
  let Q : F (key a) × F (key b) → Prop := fun p =>
    f p.2 * p.1 = 1 ∧ T (key b) (key a) hba p.1 * p.2 = 1
  have hstep1 : Nat.card (LocalFamilies R T A key) =
      Nat.card {p : F (key a) × F (key b) // Q p} := by
    apply Nat.card_congr
    refine Equiv.subtypeEquiv (localFamiliesPiTwo (fun x => F (key x)) a b hcover hne) ?_
    intro z
    constructor
    · intro hz
      exact ⟨hz a b hab, hz b a hba⟩
    · rintro ⟨h1, h2⟩ x y h'
      rcases hcover x with hx | hx <;> rcases hcover y with hy | hy
      · subst x; subst y
        exact absurd h' (hfix a)
      · subst x; subst y
        rw [Subsingleton.elim h' hab]
        exact h1
      · subst x; subst y
        rw [Subsingleton.elim h' hba]
        exact h2
      · subst x; subst y
        exact absurd h' (hfix b)
  rw [hstep1]
  have hstep2 : Nat.card {p : F (key a) × F (key b) // Q p} = Nat.card (F (key a))ˣ := by
    apply Nat.card_congr
    refine
      { toFun := fun p => Units.mk0 p.1.1 (fun h0 => ?_)
        invFun := fun u => ⟨(u, f.symm ((u : F (key a))⁻¹)), ?_⟩
        left_inv := fun p => ?_
        right_inv := fun u => ?_ }
    · have h := p.2.1
      rw [h0, mul_zero] at h
      exact zero_ne_one h
    · refine ⟨?_, ?_⟩
      · show f (f.symm ((u : F (key a))⁻¹)) * (u : F (key a)) = 1
        rw [RingEquiv.apply_symm_apply, inv_mul_cancel₀ (Units.ne_zero u)]
      · show T (key b) (key a) hba (u : F (key a)) * f.symm ((u : F (key a))⁻¹) = 1
        rw [hinv a b hab hba, ← map_mul, mul_inv_cancel₀ (Units.ne_zero u), map_one]
    · apply Subtype.ext
      apply Prod.ext
      · rfl
      · show f.symm ((p.1.1)⁻¹) = p.1.2
        rw [show (p.1.1)⁻¹ = f p.1.2 from (eq_inv_of_mul_eq_one_left p.2.1).symm]
        exact RingEquiv.symm_apply_apply f p.1.2
    · exact Units.ext rfl
  rw [hstep2, Nat.card_units]

end CFSG.StandardType
