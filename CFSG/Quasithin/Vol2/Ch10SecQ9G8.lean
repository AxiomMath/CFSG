module

public import CFSG.Quasithin.Vol2.Ch10SecQ9G7
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open Equiv

abbrev SL4 : Type := Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)

noncomputable abbrev ρ4 : SL4 →* Perm (Fin 4 → ZMod 2) := MulAction.toPermHom _ _

@[expose] def fixAdd (k : SL4) : AddSubgroup (Fin 4 → ZMod 2) where
  carrier := {v | k • v = v}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [smul_add, ha, hb]
  zero_mem' := by simp
  neg_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rw [smul_neg, ha]

theorem card_vec4 : Nat.card (Fin 4 → ZMod 2) = 16 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  norm_num

theorem ρ4_injective : Function.Injective ρ4 := by
  rw [injective_iff_map_eq_one]
  intro k hk
  ext i j
  have h1 := congrArg (fun f : Perm (Fin 4 → ZMod 2) => f (Pi.single j 1) i) hk
  simp only [MulAction.toPermHom_apply, MulAction.toPerm_apply, Perm.coe_one, id_eq] at h1
  rw [Matrix.SpecialLinearGroup.smul_def] at h1
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.one_apply, eq_comm] using h1

theorem card_fix_dvd (k : SL4) : Nat.card {v // ρ4 k v = v} ∣ 16 := by
  rw [← card_vec4]
  exact AddSubgroup.card_addSubgroup_dvd_card (fixAdd k)

theorem card_fix_cases (k : SL4) : Nat.card {v // ρ4 k v = v} = 1 ∨
    Nat.card {v // ρ4 k v = v} = 2 ∨ Nat.card {v // ρ4 k v = v} = 4 ∨
    Nat.card {v // ρ4 k v = v} = 8 ∨ Nat.card {v // ρ4 k v = v} = 16 := by
  obtain ⟨i, hi, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (show Nat.card {v // ρ4 k v = v} ∣ 2 ^ 4 from card_fix_dvd k)
  interval_cases i <;> rw [he] <;> norm_num

theorem card_fix_seven {k : SL4} (hk : orderOf k = 7) : Nat.card {v // ρ4 k v = v} = 2 := by
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hk7 : ρ4 k ^ 7 = 1 := by
    rw [← map_pow]
    have := pow_orderOf_eq_one k
    rw [hk] at this
    rw [this, map_one]
  have hk1 : ρ4 k ≠ 1 := fun h => by
    rw [← map_one ρ4] at h
    rw [ρ4_injective h, orderOf_one] at hk
    omega
  have h1 := card_modEq_card_fix (ρ4 k) hk7
  have h2 := card_fix_lt hk1
  rw [card_vec4] at h1 h2
  unfold Nat.ModEq at h1
  rcases card_fix_cases k with h | h | h | h | h <;> rw [h] at h1 h2 ⊢ <;> omega

theorem card_fix_three {h : SL4} (hh : orderOf h = 3) :
    Nat.card {v // ρ4 h v = v} = 1 ∨ Nat.card {v // ρ4 h v = v} = 4 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hh3 : ρ4 h ^ 3 = 1 := by
    rw [← map_pow]
    have := pow_orderOf_eq_one h
    rw [hh] at this
    rw [this, map_one]
  have hh1 : ρ4 h ≠ 1 := fun h' => by
    rw [← map_one ρ4] at h'
    rw [ρ4_injective h', orderOf_one] at hh
    omega
  have h1 := card_modEq_card_fix (ρ4 h) hh3
  have h2 := card_fix_lt hh1
  rw [card_vec4] at h1 h2
  unfold Nat.ModEq at h1
  rcases card_fix_cases h with h' | h' | h' | h' | h' <;> rw [h'] at h1 h2 ⊢ <;> omega

theorem sl4_false {k h : SL4} (hk : orderOf k = 7) (hh : orderOf h = 3) (hc : Commute k h) :
    False := by
  classical
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  set K := ρ4 k with hKdef
  set H := ρ4 h with hHdef
  have hcK : Commute K H := hc.map ρ4
  have hK7 : K ^ 7 = 1 := by
    have h1 := pow_orderOf_eq_one k
    rw [hk] at h1
    rw [hKdef, ← map_pow, h1, map_one]
  have h2 := card_fix_seven hk
  have h0K : K 0 = 0 := smul_zero k
  have h0H : H 0 = 0 := smul_zero h
  obtain ⟨e, he0, heK⟩ : ∃ e, e ≠ 0 ∧ K e = e := by
    have : Nontrivial {v // K v = v} :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [h2]; norm_num)
    obtain ⟨⟨e, he⟩, hne⟩ := exists_ne (⟨0, h0K⟩ : {v // K v = v})
    exact ⟨e, fun h => hne (Subtype.ext h), he⟩
  have hfixK : ∀ x, K x = x → x = 0 ∨ x = e := by
    intro x hx
    by_contra hcon
    rw [not_or] at hcon
    have := Fintype.ofFinite {v // K v = v}
    have h3 : ({⟨0, h0K⟩, ⟨e, heK⟩, ⟨x, hx⟩} : Finset {v // K v = v}).card = 3 :=
      Finset.card_eq_three.mpr ⟨_, _, _, fun h => he0 (congrArg Subtype.val h).symm,
        fun h => hcon.1 (congrArg Subtype.val h).symm,
        fun h => hcon.2 (congrArg Subtype.val h).symm, rfl⟩
    have h4 := Finset.card_le_univ ({⟨0, h0K⟩, ⟨e, heK⟩, ⟨x, hx⟩} : Finset {v // K v = v})
    rw [h3, ← Nat.card_eq_fintype_card, h2] at h4
    omega
  have hHe : H e = e := by
    have hKHe : K (H e) = H e := by
      have := congrArg (fun f : Perm (Fin 4 → ZMod 2) => f e) hcK.eq
      simp only [Perm.mul_apply] at this
      rw [this, heK]
    rcases hfixK _ hKHe with h' | h'
    · exact absurd (H.injective (h'.trans h0H.symm)) he0
    · exact h'
  have hFh : Nat.card {v // H v = v} = 4 := by
    rcases card_fix_three hh with h' | h'
    · exfalso
      have : Nat.card {v // H v = v} ≤ 1 := h'.le
      rw [Finite.card_le_one_iff_subsingleton] at this
      exact he0 (congrArg Subtype.val (Subsingleton.elim (⟨e, hHe⟩ : {v // H v = v}) ⟨0, h0H⟩))
    · exact h'
  set K' := K.subtypePerm (p := fun x => H x = x) (apply_fix_iff hcK) with hK'
  have h5 := card_modEq_card_fix K' (subtypePerm_pow_eq_one hcK hK7)
  have h6 : Nat.card {y // K' y = y} ≤ 4 :=
    calc Nat.card {y // K' y = y} ≤ Nat.card {v // H v = v} := Finite.card_subtype_le _
      _ = 4 := hFh
  rw [hFh] at h5
  unfold Nat.ModEq at h5
  have h7 : Nat.card {y // K' y = y} = 4 := by omega
  have h8 := Nat.card_le_card_of_injective (α := {y // K' y = y}) (β := {v // K v = v})
    (fun y => ⟨y.1.1, by simpa [hK'] using congrArg Subtype.val y.2⟩)
    (fun a b hab => Subtype.ext (Subtype.ext (by
      have := congrArg Subtype.val hab
      simpa using this)))
  rw [h7, h2] at h8
  omega

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
