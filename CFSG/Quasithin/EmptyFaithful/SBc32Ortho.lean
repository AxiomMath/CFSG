module

public import CFSG.Quasithin.EmptyFaithful.Vocabulary

public section

namespace CFSG.Quasithin

namespace SBc

section Ortho

variable {V : Type*} [Group V] {q : V → ZMod 2}

private theorem zmod_cases2 (a : ZMod 2) : a = 0 ∨ a = 1 := by revert a; decide

private theorem q_mul' (x y : V) : q (x * y) = q x + q y + quadPolar q x y := by
  unfold quadPolar
  generalize q (x * y) = a
  generalize q x = b
  generalize q y = c
  revert a b c
  decide

private theorem polar_symm (hcomm : ∀ x y : V, x * y = y * x) (x y : V) :
    quadPolar q x y = quadPolar q y x := by
  unfold quadPolar
  rw [hcomm x y]
  ring

private theorem polar_one_right (hq : IsQuadraticFormOn q) (x : V) : quadPolar q x 1 = 0 := by
  have h := hq.2.2 x 1 1
  rw [mul_one] at h
  generalize quadPolar q x 1 = a at h
  revert a
  decide

private theorem polar_self (hq : IsQuadraticFormOn q) (hsq : ∀ v : V, v * v = 1) (x : V) :
    quadPolar q x x = 0 := by
  unfold quadPolar
  rw [hsq x, hq.1]
  generalize q x = a
  revert a
  decide

private def transvFun (q : V → ZMod 2) (a : V) (x : V) : V :=
  if quadPolar q x a = 1 then x * a else x

private theorem transvFun_mul (hq : IsQuadraticFormOn q) (hcomm : ∀ x y : V, x * y = y * x)
    (hsq : ∀ v : V, v * v = 1) (a x y : V) :
    transvFun q a (x * y) = transvFun q a x * transvFun q a y := by
  have hB : quadPolar q (x * y) a = quadPolar q x a + quadPolar q y a := hq.2.1 x y a
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  have h01 : (0 : ZMod 2) + 1 = 1 := by decide
  have h10 : (1 : ZMod 2) + 0 = 1 := by decide
  have h00 : (0 : ZMod 2) + 0 = 0 := by decide
  have hne : (0 : ZMod 2) ≠ 1 := by decide
  rcases zmod_cases2 (quadPolar q x a) with hx | hx <;>
    rcases zmod_cases2 (quadPolar q y a) with hy | hy
  · simp [transvFun, hB, hx, hy, h00]
  · simp [transvFun, hB, hx, hy, h01, mul_assoc]
  · simp [transvFun, hB, hx, hy, h10]
    calc x * y * a = x * (y * a) := by group
      _ = x * (a * y) := by rw [hcomm y a]
      _ = x * a * y := by group
  · simp [transvFun, hB, hx, hy, h11, hne]
    calc x * y = x * (y * (a * a)) := by rw [hsq a, mul_one]
      _ = x * a * (y * a) := by
        calc x * (y * (a * a)) = x * (y * a * a) := by group
          _ = x * (a * y * a) := by rw [hcomm y a]
          _ = x * a * (y * a) := by group

private theorem transvFun_invol (hq : IsQuadraticFormOn q) (hsq : ∀ v : V, v * v = 1) (a x : V) :
    transvFun q a (transvFun q a x) = x := by
  unfold transvFun
  by_cases hx : quadPolar q x a = 1
  · have hB : quadPolar q (x * a) a = quadPolar q x a + quadPolar q a a := hq.2.1 x a a
    have hB1 : quadPolar q (x * a) a = 1 := by rw [hB, hx, polar_self hq hsq]; decide
    simp only [hx, hB1, ite_true]
    calc x * a * a = x * (a * a) := by group
      _ = x := by rw [hsq a, mul_one]
  · simp [hx]

private def transv (hq : IsQuadraticFormOn q) (hcomm : ∀ x y : V, x * y = y * x)
    (hsq : ∀ v : V, v * v = 1) (a : V) : MulAut V where
  toFun := transvFun q a
  invFun := transvFun q a
  left_inv := transvFun_invol hq hsq a
  right_inv := transvFun_invol hq hsq a
  map_mul' := transvFun_mul hq hcomm hsq a

private theorem transv_mem (hq : IsQuadraticFormOn q) (hcomm : ∀ x y : V, x * y = y * x)
    (hsq : ∀ v : V, v * v = 1) {a : V} (ha : q a = 1) :
    transv hq hcomm hsq a ∈ orthogonalGroupOf q := by
  intro x
  show q (transvFun q a x) = q x
  unfold transvFun
  split_ifs with hx
  · rw [q_mul' (q := q) x a, hx, ha]
    generalize q x = c
    revert c
    decide
  · rfl

private theorem exists_nonsingular_perp [Finite V] (hq : IsQuadraticFormOn q)
    (hnd : IsNondegQuadratic q) (hcomm : ∀ x y : V, x * y = y * x) (hcard : 4 < Nat.card V)
    {x : V} (hx1 : x ≠ 1) : ∃ y : V, q y = 1 ∧ quadPolar q x y = 0 := by
  by_contra hcon
  push Not at hcon
  have hq0 : ∀ y, quadPolar q x y = 0 → q y = 0 := fun y hy =>
    (zmod_cases2 (q y)).resolve_right (fun h => hcon y h hy)
  obtain ⟨a, ha⟩ : ∃ a, quadPolar q x a = 1 := by
    by_contra hno
    push Not at hno
    exact hx1 (hnd x (fun y => (zmod_cases2 _).resolve_right (hno y)))
  let Φ : V →* Multiplicative (ZMod 2 × ZMod 2) :=
    MonoidHom.mk' (fun y => Multiplicative.ofAdd (quadPolar q x y, quadPolar q a y)) (fun y z => by
      rw [← ofAdd_add]
      congr 1
      exact Prod.ext (hq.2.2 x y z) (hq.2.2 a y z))
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have hy' : (quadPolar q x y, quadPolar q a y) = 0 := by
      have := congrArg Multiplicative.toAdd hy
      simpa [Φ] using this
    have h1 : quadPolar q x y = 0 := congrArg Prod.fst hy'
    have h2 : quadPolar q a y = 0 := congrArg Prod.snd hy'
    apply hnd y
    have hperp : ∀ v, quadPolar q x v = 0 → quadPolar q y v = 0 := by
      intro v hv
      have hyv : quadPolar q x (y * v) = 0 := by rw [hq.2.2, h1, hv]; decide
      have e1 := hq0 (y * v) hyv
      have e2 := hq0 y h1
      have e3 := hq0 v hv
      unfold quadPolar
      rw [e1, e2, e3]
      decide
    intro v
    rcases zmod_cases2 (quadPolar q x v) with hv | hv
    · exact hperp v hv
    · have hva : quadPolar q x (v * a) = 0 := by rw [hq.2.2, hv, ha]; decide
      have h3 := hperp (v * a) hva
      rw [hq.2.2] at h3
      have h4 : quadPolar q y a = 0 := by rw [polar_symm hcomm]; exact h2
      rw [h4] at h3
      simpa using h3
  have := Nat.card_le_card_of_injective Φ hinj
  have h4 : Nat.card (Multiplicative (ZMod 2 × ZMod 2)) = 4 := by
    simp [Nat.card_eq_fintype_card]
  omega

theorem eq_one_of_fixed_by_isometries [Finite V] (hq : IsQuadraticFormOn q)
    (hnd : IsNondegQuadratic q) (hcomm : ∀ x y : V, x * y = y * x) (hsq : ∀ v : V, v * v = 1)
    (hcard : 4 < Nat.card V) {f : V} (hfix : ∀ g ∈ orthogonalGroupOf q, g f = f) : f = 1 := by
  have hperp : ∀ a, q a = 1 → quadPolar q f a = 0 := by
    intro a ha
    have h := hfix (transv hq hcomm hsq a) (transv_mem hq hcomm hsq ha)
    change transvFun q a f = f at h
    unfold transvFun at h
    by_contra hne
    have hB1 : quadPolar q f a = 1 := (zmod_cases2 _).resolve_left hne
    simp only [hB1, ite_true] at h
    have : a = 1 := by simpa using h
    rw [this, hq.1] at ha
    exact absurd ha (by decide)
  apply hnd f
  intro v
  by_cases hv : q v = 1
  · exact hperp v hv
  · have hv0 : q v = 0 := (zmod_cases2 _).resolve_right hv
    by_cases hv1 : v = 1
    · rw [hv1]
      exact polar_one_right hq f
    · obtain ⟨y, hy1, hy0⟩ := exists_nonsingular_perp hq hnd hcomm hcard hv1
      have hvy : q (v * y) = 1 := by
        rw [q_mul' (q := q) v y, hv0, hy1, hy0]
        decide
      have h1 := hperp (v * y) hvy
      have h2 := hperp y hy1
      rw [hq.2.2] at h1
      rw [h2] at h1
      simpa using h1

end Ortho

end SBc

end CFSG.Quasithin
