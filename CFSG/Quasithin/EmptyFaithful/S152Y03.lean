module

public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin

open DihedralGroup

section Dihedral

variable {n : ℕ} [NeZero n]

@[expose] def rotSub (n : ℕ) : Subgroup (DihedralGroup n) where
  carrier := {x | ∃ i, x = r i}
  one_mem' := ⟨0, rfl⟩
  mul_mem' := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    exact ⟨i + j, by simp⟩
  inv_mem' := by
    rintro _ ⟨i, rfl⟩
    exact ⟨-i, by simp⟩

omit [NeZero n] in
theorem mem_rotSub_iff (x : DihedralGroup n) : x ∈ rotSub n ↔ ∃ i, x = r i := Iff.rfl

theorem mem_rotSub_iff_odd (hn : Odd n) (x : DihedralGroup n) :
    x ∈ rotSub n ↔ Odd (orderOf x) := by
  cases x with
  | r i =>
    refine ⟨fun _ => ?_, fun _ => ⟨i, rfl⟩⟩
    rw [orderOf_r]
    exact Odd.of_dvd_nat hn (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left n i.val))
  | sr j =>
    rw [orderOf_sr]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨i, hi⟩ := h
      cases hi
    · exact absurd h (by decide)

omit [NeZero n] in
theorem card_rotSub : Nat.card (rotSub n) = n := by
  have e : ZMod n ≃ rotSub n :=
    Equiv.ofBijective (fun i => ⟨r i, i, rfl⟩) ⟨fun a b h => by
      have := congrArg Subtype.val h
      simpa using this, fun ⟨x, i, hx⟩ => ⟨i, Subtype.ext hx.symm⟩⟩
  rw [← Nat.card_congr e, Nat.card_zmod]

omit [NeZero n] in
theorem sr_conj_r (j i : ZMod n) : sr j * r i * (sr j)⁻¹ = (r i)⁻¹ := by
  simp only [inv_sr, sr_mul_r, sr_mul_sr, inv_r]
  congr 1
  ring

theorem dihedral_shape {A : Type*} [Group A] {X : Subgroup A} (hn : Odd n)
    (e : ↥X ≃* DihedralGroup n) :
    Nat.card (oTwoUpper X) = n ∧ Nat.card X = 2 * n ∧
      ∀ t ∈ X, orderOf t = 2 → ∀ a ∈ oTwoUpper X, t * a * t⁻¹ = a⁻¹ := by
  set φ : DihedralGroup n →* A := X.subtype.comp e.symm.toMonoidHom with hφ
  have hφinj : Function.Injective φ := X.subtype_injective.comp e.symm.injective
  set N : Subgroup A := (rotSub n).map φ with hN
  have hmemN : ∀ x : A, x ∈ N ↔ ∃ d ∈ rotSub n, φ d = x := fun x => Subgroup.mem_map
  have hodd : ∀ (x : A) (hx : x ∈ X), Odd (orderOf x) ↔ e ⟨x, hx⟩ ∈ rotSub n := by
    intro x hx
    rw [mem_rotSub_iff_odd hn, MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
  have hXN : oTwoUpper X = N := by
    apply le_antisymm
    · refine (Subgroup.closure_le N).mpr fun x hx => ?_
      obtain ⟨hxX, hxo⟩ := hx
      refine (hmemN x).mpr ⟨e ⟨x, hxX⟩, (hodd x hxX).mp hxo, ?_⟩
      simp [hφ]
    · intro x hx
      obtain ⟨d, hd, rfl⟩ := (hmemN x).mp hx
      have hxX : φ d ∈ X := (e.symm d).2
      refine mem_oTwoUpper_of_odd hxX ((hodd _ hxX).mpr ?_)
      have : e ⟨φ d, hxX⟩ = d := by
        apply e.symm.injective
        apply Subtype.ext
        simp [hφ]
      rw [this]
      exact hd
  refine ⟨?_, ?_, ?_⟩
  · rw [hXN, hN, Subgroup.card_map_of_injective hφinj, card_rotSub]
  · rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  · intro t ht hto a ha
    rw [hXN] at ha
    obtain ⟨d, hd, rfl⟩ := (hmemN a).mp ha
    obtain ⟨i, rfl⟩ := hd
    have hte : e ⟨t, ht⟩ ∉ rotSub n := by
      intro hm
      have := (mem_rotSub_iff_odd hn _).mp hm
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hto] at this
      exact absurd this (by decide)
    obtain ⟨j, hj⟩ : ∃ j, e ⟨t, ht⟩ = sr j := by
      generalize e ⟨t, ht⟩ = d at hte ⊢
      cases d with
      | r i => exact absurd (⟨i, rfl⟩ : r i ∈ rotSub n) hte
      | sr j => exact ⟨j, rfl⟩
    have h1 : t = φ (sr j) := by
      have : ⟨t, ht⟩ = e.symm (sr j) := by rw [← hj]; simp
      simpa [hφ] using congrArg Subtype.val this
    rw [h1]
    rw [← map_inv, ← map_mul, ← map_mul, sr_conj_r]
    exact map_inv φ _

end Dihedral

end CFSG.Quasithin
