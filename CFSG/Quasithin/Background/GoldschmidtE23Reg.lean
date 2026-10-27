module

public import CFSG.Quasithin.Background.B1Basic

public section

namespace CFSG.Quasithin

namespace GE23

section Reg

variable {V : Type} [CommGroup V]

theorem commutes_trivial {x a : MulAut V} (hxa : x * a = a * x)
    (hfix : ∀ v : V, x (a v * v⁻¹) = a v * v⁻¹) (v : V) : a (x v * v⁻¹) = x v * v⁻¹ := by
  have h1 : x (a v) = a (x v) := by
    have := congrArg (fun y : MulAut V => y v) hxa
    exact this
  have h2 : x (a v) = (a v * v⁻¹) * x v := by
    have e : a v = (a v * v⁻¹) * v := by group
    calc x (a v) = x ((a v * v⁻¹) * v) := by rw [← e]
      _ = x (a v * v⁻¹) * x v := map_mul x _ _
      _ = (a v * v⁻¹) * x v := by rw [hfix v]
  rw [map_mul, map_inv, ← h1, h2]
  calc a v * v⁻¹ * x v * (a v)⁻¹ = (a v * (a v)⁻¹) * (v⁻¹ * x v) := by ac_rfl
    _ = x v * v⁻¹ := by rw [mul_inv_cancel, one_mul, mul_comm]

theorem trivial_of_commuting {Z : Subgroup V} {x : MulAut V} (hxZ : ∀ z ∈ Z, x z = z) {ι : Type*}
    (a : ι → MulAut V) (hcomm : ∀ i, x * a i = a i * x) (himg : ∀ i v, a i v * v⁻¹ ∈ Z)
    (hreg : ∀ v : V, (∀ i, a i v = v) → v ∈ Z) (v : V) : x v * v⁻¹ ∈ Z :=
  hreg _ fun i => commutes_trivial (hcomm i) (fun w => hxZ _ (himg i w)) v

theorem isElemAbelian2_of_trivial (hV : ∀ v : V, v ^ 2 = 1) {Z : Subgroup V}
    {Q : Subgroup (MulAut V)}
    (hQZ : ∀ x ∈ Q, ∀ z ∈ Z, x z = z) (htriv : ∀ x ∈ Q, ∀ v : V, x v * v⁻¹ ∈ Z) :
    IsElemAbelian2 Q := by
  have key : ∀ x ∈ Q, ∀ y ∈ Q, ∀ v : V, x (y v) = (y v * v⁻¹) * x v := by
    intro x hx y hy v
    have e : y v = (y v * v⁻¹) * v := by group
    calc x (y v) = x ((y v * v⁻¹) * v) := by rw [← e]
      _ = x (y v * v⁻¹) * x v := map_mul x _ _
      _ = (y v * v⁻¹) * x v := by rw [hQZ x hx _ (htriv y hy v)]
  refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
  · ext v
    show x (y v) = y (x v)
    rw [key x hx y hy v, key y hy x hx v]
    ac_rfl
  · rw [pow_two]
    ext v
    show x (x v) = v
    rw [key x hx x hx v]
    have h2 : (x v) * (x v) = 1 := by rw [← sq]; exact hV _
    calc x v * v⁻¹ * x v = (x v * x v) * v⁻¹ := by ac_rfl
      _ = v := by
        rw [h2, one_mul]
        exact inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hV v)

end Reg

section Count

variable {V : Type} [CommGroup V] [Finite V]

theorem eq_of_trivial_action (hV : ∀ v : V, v ^ 2 = 1) {X P Q : Subgroup (MulAut V)}
    (hns : ¬ IsStrongFFModule X) (hQX : Q ≤ X) (hPQ : P ≤ Q) (hP : P ≠ ⊥)
    (hoff : Nat.card V ≤ Nat.card P * Nat.card (fixV P))
    (hQZ : ∀ x ∈ Q, ∀ z ∈ fixV P, x z = z)
    (htriv : ∀ x ∈ Q, ∀ v : V, x v * v⁻¹ ∈ fixV P) : Q = P := by
  have hel : IsElemAbelian2 Q := isElemAbelian2_of_trivial hV hQZ htriv
  have hQ : Q ≠ ⊥ := fun h => hP (le_bot_iff.1 (h ▸ hPQ))
  have hfix : fixV Q = fixV P :=
    le_antisymm (B1.fixV_le_fixV hPQ) (fun z hz x hx => hQZ x hx z hz)
  by_contra hne
  have hlt : Nat.card P < Nat.card Q := by
    by_contra hle
    exact hne (Subgroup.eq_of_le_of_card_ge hPQ (not_lt.1 hle)).symm
  apply hns
  refine ⟨Q, hQX, hQ, hel, ?_⟩
  rw [hfix]
  calc Nat.card V ≤ Nat.card P * Nat.card (fixV P) := hoff
    _ < Nat.card Q * Nat.card (fixV P) := Nat.mul_lt_mul_of_pos_right hlt Nat.card_pos

end Count

end GE23

end CFSG.Quasithin
