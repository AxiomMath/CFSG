module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13F4D2Aux1
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13F4D
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13Hyp

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour
open CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations (hyperplanes)
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

noncomputable instance f4d2_fintypeHyperplanes (p : ℕ) (E : Subgroup (MulAut W)) :
    Fintype (hyperplanes p E) :=
  (finite_hyperplanes p E).fintype

@[expose] def f4d2_E (x x' : MulAut W) : Subgroup (MulAut W) :=
  Subgroup.zpowers x ⊔ Subgroup.zpowers x'

@[expose] def f4d2_H (x x' : MulAut W) (i : Fin 7) : Subgroup (MulAut W) :=
  Subgroup.zpowers (x' * x ^ (i : ℕ))

section Basic

variable {x x' u : MulAut W}

omit [Finite W] in
theorem f4d2_hyperplanes_eq (hx7 : orderOf x = 7) (hx'7 : orderOf x' = 7)
    (hcomm : x * x' = x' * x) (hne : x' ∉ Subgroup.zpowers x) :
    hyperplanes 7 (f4d2_E x x') = {Subgroup.zpowers x} ∪ Set.range (f4d2_H x x') := by
  exact w16g_hyperplanes_sup_zpowers (G := MulAut W) Nat.prime_seven hx7 hx'7 hcomm hne

omit [Finite W] in
theorem f4d2_H_mem (hx7 : orderOf x = 7) (hx'7 : orderOf x' = 7)
    (hcomm : x * x' = x' * x) (hne : x' ∉ Subgroup.zpowers x) (i : Fin 7) :
    f4d2_H x x' i ∈ hyperplanes 7 (f4d2_E x x') := by
  rw [f4d2_hyperplanes_eq hx7 hx'7 hcomm hne]
  exact Set.mem_union_right _ ⟨i, rfl⟩

omit [Finite W] in
theorem f4d2_H_injective (hx7 : orderOf x = 7) (hx'7 : orderOf x' = 7)
    (hcomm : x * x' = x' * x) (hne : x' ∉ Subgroup.zpowers x) :
    Function.Injective (f4d2_H x x') := by
  exact (w16g_zpowers_mul_pow_injective (G := MulAut W) Nat.prime_seven hx7 hx'7 hcomm hne).1

omit [Finite W] in
theorem f4d2_H_ne_zpowers (hx7 : orderOf x = 7) (hx'7 : orderOf x' = 7)
    (hcomm : x * x' = x' * x) (hne : x' ∉ Subgroup.zpowers x) (i : Fin 7) :
    f4d2_H x x' i ≠ Subgroup.zpowers x := by
  exact (w16g_zpowers_mul_pow_injective (G := MulAut W) Nat.prime_seven hx7 hx'7 hcomm hne).2 i

omit [Finite W] in
theorem f4d2_H_zero (x x' : MulAut W) : f4d2_H x x' 0 = Subgroup.zpowers x' := by
  simp [f4d2_H]

omit [Finite W] in
theorem f4d2_H_six (hx7 : orderOf x = 7) (hcomm : x * x' = x' * x) :
    f4d2_H x x' 6 = Subgroup.zpowers (x * x'⁻¹) := by
  exact (s134b_zpowers_mul_inv (x := x) (x' := x') hx7 hcomm).symm

omit [Finite W] in
theorem f4d2_H_ne_six (hx7 : orderOf x = 7) (hx'7 : orderOf x' = 7)
    (hcomm : x * x' = x' * x) (hne : x' ∉ Subgroup.zpowers x) {i : Fin 7} (hi : i ≠ 6) :
    f4d2_H x x' i ≠ Subgroup.zpowers (x * x'⁻¹) := by
  rw [← f4d2_H_six hx7 hcomm]
  exact fun h => hi (f4d2_H_injective hx7 hx'7 hcomm hne h)

omit [Finite W] in
theorem f4d2_H_ne_X' (hx7 : orderOf x = 7) (hx'7 : orderOf x' = 7)
    (hcomm : x * x' = x' * x) (hne : x' ∉ Subgroup.zpowers x) {i : Fin 7} (hi : i ≠ 0) :
    f4d2_H x x' i ≠ Subgroup.zpowers x' := by
  rw [← f4d2_H_zero x x']
  exact fun h => hi (f4d2_H_injective hx7 hx'7 hcomm hne h)

omit [Finite W] in
theorem f4d2_pow_add_seven (hx7 : orderOf x = 7) (a : ℕ) : x ^ (a + 7) = x ^ a := by
  rw [pow_add, show x ^ 7 = 1 by rw [← hx7]; exact pow_orderOf_eq_one x, mul_one]

omit [Finite W] in
theorem f4d2_pow_ten (hx7 : orderOf x = 7) : x ^ 10 = x ^ 3 := by
  simpa using f4d2_pow_add_seven hx7 3

omit [Finite W] in
theorem f4d2_pow_twelve (hx7 : orderOf x = 7) : x ^ 12 = x ^ 5 := by
  simpa using f4d2_pow_add_seven hx7 5

theorem f4d2_rk_H2_eq_H1 (_hx7 : orderOf x = 7) (_hx'7 : orderOf x' = 7)
    (_hcomm : x * x' = x' * x) (_hne : x' ∉ Subgroup.zpowers x)
    (hux : u * x * u⁻¹ = x ^ 2) (hux' : u * x' * u⁻¹ = x') :
    rk ↥(hypPart (f4d2_E x x') (f4d2_H x x' 2)) =
      rk ↥(hypPart (f4d2_E x x') (f4d2_H x x' 1)) := by
  exact s134b_rk_hypPart_double (x := x) (x' := x') (u := u) hux hux' 1

theorem f4d2_rk_H4_eq_H2 (_hx7 : orderOf x = 7) (_hx'7 : orderOf x' = 7)
    (_hcomm : x * x' = x' * x) (_hne : x' ∉ Subgroup.zpowers x)
    (hux : u * x * u⁻¹ = x ^ 2) (hux' : u * x' * u⁻¹ = x') :
    rk ↥(hypPart (f4d2_E x x') (f4d2_H x x' 4)) =
      rk ↥(hypPart (f4d2_E x x') (f4d2_H x x' 2)) := by
  exact s134b_rk_hypPart_double (x := x) (x' := x') (u := u) hux hux' 2

theorem f4d2_rk_H6_eq_H3 (_hx7 : orderOf x = 7) (_hx'7 : orderOf x' = 7)
    (_hcomm : x * x' = x' * x) (_hne : x' ∉ Subgroup.zpowers x)
    (hux : u * x * u⁻¹ = x ^ 2) (hux' : u * x' * u⁻¹ = x') :
    rk ↥(hypPart (f4d2_E x x') (f4d2_H x x' 6)) =
      rk ↥(hypPart (f4d2_E x x') (f4d2_H x x' 3)) := by
  exact s134b_rk_hypPart_double (x := x) (x' := x') (u := u) hux hux' 3

theorem f4d2_rk_H5_eq_H3 (hx7 : orderOf x = 7) (_hx'7 : orderOf x' = 7)
    (_hcomm : x * x' = x' * x) (_hne : x' ∉ Subgroup.zpowers x)
    (hux : u * x * u⁻¹ = x ^ 2) (hux' : u * x' * u⁻¹ = x') :
    rk ↥(hypPart (f4d2_E x x') (f4d2_H x x' 5)) =
      rk ↥(hypPart (f4d2_E x x') (f4d2_H x x' 3)) := by
  have h := s134b_rk_hypPart_double (x := x) (x' := x') (u := u) hux hux' 5
  rw [f4d2_pow_ten hx7] at h
  exact h.symm

omit [Finite W] in
theorem f4d2_z_ord (hx7 : orderOf x = 7) (hx'7 : orderOf x' = 7)
    (hcomm : x * x' = x' * x) (hne : x' ∉ Subgroup.zpowers x) :
    orderOf (x * x'⁻¹) = 7 := by
  have hz7 : (x * x'⁻¹) ^ 7 = 1 := by
    have hx7' : x ^ 7 = 1 := by rw [← hx7]; exact pow_orderOf_eq_one x
    have hx'7' : x' ^ 7 = 1 := by rw [← hx'7]; exact pow_orderOf_eq_one x'
    rw [(show Commute x x' from hcomm).inv_right.mul_pow 7, hx7', inv_pow, hx'7', inv_one, mul_one]
  have hz1 : x * x'⁻¹ ≠ 1 := by
    intro h
    apply hne
    have hxeq : x = x' := by
      calc x = (x * x'⁻¹) * x' := by group
        _ = 1 * x' := by rw [h]
        _ = x' := one_mul x'
    rw [← hxeq]
    exact Subgroup.mem_zpowers x
  have hdvd : orderOf (x * x'⁻¹) ∣ 7 := orderOf_dvd_iff_pow_eq_one.mpr hz7
  rcases (Nat.dvd_prime Nat.prime_seven).mp hdvd with h1 | h7
  · exact absurd (orderOf_eq_one_iff.mp h1) hz1
  · exact h7

omit [Finite W] in
theorem f4d2_z_mem (x x' : MulAut W) : x * x'⁻¹ ∈ f4d2_E x x' := by
  rw [f4d2_E]
  exact Subgroup.mul_mem _
    (Subgroup.mem_sup_left (Subgroup.mem_zpowers x))
    (Subgroup.mem_sup_right (Subgroup.inv_mem _ (Subgroup.mem_zpowers x')))

omit [Finite W] in
theorem f4d2_z_hyp (hx7 : orderOf x = 7) (hx'7 : orderOf x' = 7)
    (hcomm : x * x' = x' * x) (hne : x' ∉ Subgroup.zpowers x) :
    Subgroup.zpowers (x * x'⁻¹) ∈ hyperplanes 7 (f4d2_E x x') := by
  rw [← f4d2_H_six hx7 hcomm]
  exact f4d2_H_mem hx7 hx'7 hcomm hne 6

theorem f4d2_sum_seven_le (hW : ∀ w : W, w * w = 1) (hx7 : orderOf x = 7)
    (hx'7 : orderOf x' = 7) (hcomm : x * x' = x' * x) (hne : x' ∉ Subgroup.zpowers x)
    (hdec : iSupIndep (fun D : hyperplanes 7 (f4d2_E x x') => hypPart (f4d2_E x x') D))
    (hMstab : StableUnder (f4d2_E x x') (commSub ⊤ (f4d2_E x x')))
    (hMfix : commSub ⊤ (f4d2_E x x') ⊓ fixV (f4d2_E x x') = ⊥)
    (hEcomm : ∀ a ∈ f4d2_E x x', ∀ b ∈ f4d2_E x x', a * b = b * a)
    (hz_le : rk ↥(commSub ⊤ (Subgroup.zpowers (x * x'⁻¹))) ≤ 6) :
    rk ↥(hypPart (f4d2_E x x') (Subgroup.zpowers x)) +
      (∑ i ∈ (Finset.univ : Finset (Fin 7)).filter (fun i : Fin 7 => i ≠ 6),
        rk ↥(hypPart (f4d2_E x x') (f4d2_H x x' i))) ≤ 6 := by
  classical
  let g : Fin 7 → Subgroup (MulAut W) := f4d2_H x x'
  have hg_inj : Function.Injective g := f4d2_H_injective hx7 hx'7 hcomm hne
  let s : Finset (Fin 7) := Finset.univ.filter (fun i : Fin 7 => i ≠ 6)
  have hnot : Subgroup.zpowers x ∉ s.image g := by
    intro h
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp h
    exact (f4d2_H_ne_zpowers hx7 hx'7 hcomm hne i) hi
  let T : Finset (Subgroup (MulAut W)) := insert (Subgroup.zpowers x) (s.image g)
  have hT : ∀ D ∈ T, D ∈ hyperplanes 7 (f4d2_E x x') := by
    intro D hD
    change D ∈ insert (Subgroup.zpowers x) (s.image g) at hD
    rcases Finset.mem_insert.mp hD with rfl | hD
    · show Subgroup.zpowers x ∈ hyperplanes 7 (f4d2_E x x')
      rw [f4d2_hyperplanes_eq hx7 hx'7 hcomm hne]
      exact Or.inl rfl
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hD
      exact f4d2_H_mem hx7 hx'7 hcomm hne i
  have hTz : ∀ D ∈ T, D ≠ Subgroup.zpowers (x * x'⁻¹) := by
    intro D hD
    change D ∈ insert (Subgroup.zpowers x) (s.image g) at hD
    rcases Finset.mem_insert.mp hD with rfl | hD
    · intro h
      have h6 := f4d2_H_ne_zpowers hx7 hx'7 hcomm hne 6
      rw [f4d2_H_six hx7 hcomm] at h6
      exact h6 h.symm
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hD
      change i ∈ Finset.univ.filter (fun i : Fin 7 => i ≠ 6) at hi
      exact f4d2_H_ne_six hx7 hx'7 hcomm hne (by simpa using (Finset.mem_filter.mp hi).2)
  have hbound := f4d2_sum_rk_le_commSub_ne hW hdec hMstab hMfix hEcomm
    (f4d2_z_ord hx7 hx'7 hcomm hne) (f4d2_z_mem x x') (f4d2_z_hyp hx7 hx'7 hcomm hne)
    T hT hTz
  have hsumT_eq : ∑ D ∈ T, rk ↥(hypPart (f4d2_E x x') D) =
      rk ↥(hypPart (f4d2_E x x') (Subgroup.zpowers x)) +
        ∑ i ∈ s, rk ↥(hypPart (f4d2_E x x') (f4d2_H x x' i)) := by
    change (∑ D ∈ insert (Subgroup.zpowers x) (s.image g),
        rk ↥(hypPart (f4d2_E x x') D)) = _
    rw [Finset.sum_insert hnot, Finset.sum_image (fun a _ b _ h => hg_inj h)]
  rw [hsumT_eq] at hbound
  exact hbound.trans hz_le

theorem f4d2_orbit_bound (hx7 : orderOf x = 7) (hx'7 : orderOf x' = 7)
    (hcomm : x * x' = x' * x) (hne : x' ∉ Subgroup.zpowers x)
    (hux : u * x * u⁻¹ = x ^ 2) (hux' : u * x' * u⁻¹ = x')
    (hUx' : hypPart (f4d2_E x x') (Subgroup.zpowers x') = ⊥)
    (hbound : rk ↥(hypPart (f4d2_E x x') (Subgroup.zpowers x)) +
      (∑ i ∈ (Finset.univ : Finset (Fin 7)).filter (fun i : Fin 7 => i ≠ 6),
        rk ↥(hypPart (f4d2_E x x') (f4d2_H x x' i))) ≤ 6) :
    3 * rk ↥(hypPart (f4d2_E x x') (f4d2_H x x' 1)) +
      2 * rk ↥(hypPart (f4d2_E x x') (f4d2_H x x' 3)) ≤ 6 := by
  rw [Finset.sum_filter, Fin.sum_univ_seven] at hbound
  norm_num at hbound
  have hf0 : rk ↥(hypPart (f4d2_E x x') (f4d2_H x x' 0)) = 0 := by
    rw [f4d2_H_zero, hUx']
    exact rk_bot
  rw [hf0] at hbound
  rw [f4d2_rk_H4_eq_H2 hx7 hx'7 hcomm hne hux hux',
    f4d2_rk_H5_eq_H3 hx7 hx'7 hcomm hne hux hux',
    f4d2_rk_H2_eq_H1 hx7 hx'7 hcomm hne hux hux'] at hbound
  omega

omit [Finite W] in
theorem f4d2_X_mem (hx7 : orderOf x = 7) (hx'7 : orderOf x' = 7)
    (hcomm : x * x' = x' * x) (hne : x' ∉ Subgroup.zpowers x) :
    Subgroup.zpowers x ∈ hyperplanes 7 (f4d2_E x x') := by
  rw [f4d2_hyperplanes_eq hx7 hx'7 hcomm hne]
  exact Or.inl rfl

noncomputable def f4d2_hyperplaneEquiv (hx7 : orderOf x = 7) (hx'7 : orderOf x' = 7)
    (hcomm : x * x' = x' * x) (hne : x' ∉ Subgroup.zpowers x) :
    Option (Fin 7) ≃ hyperplanes 7 (f4d2_E x x') :=
  Equiv.ofBijective
    (fun o => Option.elim o ⟨Subgroup.zpowers x, f4d2_X_mem hx7 hx'7 hcomm hne⟩
      (fun i => ⟨f4d2_H x x' i, f4d2_H_mem hx7 hx'7 hcomm hne i⟩))
    (by
      constructor
      · intro a b hab
        cases a with
        | none =>
          cases b with
          | none => rfl
          | some j =>
            exact absurd (congrArg Subtype.val hab).symm
              (f4d2_H_ne_zpowers hx7 hx'7 hcomm hne j)
        | some i =>
          cases b with
          | none =>
            exact absurd (congrArg Subtype.val hab)
              (f4d2_H_ne_zpowers hx7 hx'7 hcomm hne i)
          | some j =>
            have h : f4d2_H x x' i = f4d2_H x x' j := congrArg Subtype.val hab
            exact congrArg some (f4d2_H_injective hx7 hx'7 hcomm hne h)
      · intro D
        have hmem : (D : Subgroup (MulAut W)) ∈ {Subgroup.zpowers x} ∪
            Set.range (f4d2_H x x') :=
          (f4d2_hyperplanes_eq hx7 hx'7 hcomm hne) ▸ D.2
        rcases hmem with hX | ⟨i, hi⟩
        · exact ⟨none, Subtype.ext hX.symm⟩
        · exact ⟨some i, Subtype.ext hi⟩)

theorem f4d2_sum_hyperplanes (hx7 : orderOf x = 7) (hx'7 : orderOf x' = 7)
    (hcomm : x * x' = x' * x) (hne : x' ∉ Subgroup.zpowers x)
    (f : hyperplanes 7 (f4d2_E x x') → ℕ) :
    (∑ D : hyperplanes 7 (f4d2_E x x'), f D) =
      f ⟨Subgroup.zpowers x, f4d2_X_mem hx7 hx'7 hcomm hne⟩ +
        ∑ i : Fin 7, f ⟨f4d2_H x x' i, f4d2_H_mem hx7 hx'7 hcomm hne i⟩ := by
  rw [← (f4d2_hyperplaneEquiv hx7 hx'7 hcomm hne).sum_comp f, Fintype.sum_option]
  rfl

theorem f4d2_rk_eq_sum_all
    (hdec : iSupIndep (fun D : hyperplanes 7 (f4d2_E x x') => hypPart (f4d2_E x x') D))
    (hsup : (⨆ D : hyperplanes 7 (f4d2_E x x'), hypPart (f4d2_E x x') D) =
      commSub ⊤ (f4d2_E x x')) :
    rk ↥(commSub ⊤ (f4d2_E x x')) =
      ∑ D : hyperplanes 7 (f4d2_E x x'), rk ↥(hypPart (f4d2_E x x') D) := by
  have hsupeq : (⨆ D ∈ (Finset.univ : Finset (hyperplanes 7 (f4d2_E x x'))),
        hypPart (f4d2_E x x') D) =
      ⨆ D : hyperplanes 7 (f4d2_E x x'), hypPart (f4d2_E x x') D := by
    apply le_antisymm
    · refine iSup_le fun D => iSup_le fun _ => ?_
      exact le_iSup (fun D : hyperplanes 7 (f4d2_E x x') => hypPart (f4d2_E x x') D) D
    · refine iSup_le fun D => ?_
      exact le_iSup₂
        (f := fun D (_ : D ∈ (Finset.univ : Finset (hyperplanes 7 (f4d2_E x x')))) =>
          hypPart (f4d2_E x x') D) D (Finset.mem_univ D)
  rw [← hsup, ← hsupeq]
  exact rk_iSup_biSup_eq_sum
    (S := fun D : hyperplanes 7 (f4d2_E x x') => hypPart (f4d2_E x x') D) hdec Finset.univ

theorem f4d2_rk_commSub_eq (hx7 : orderOf x = 7) (hx'7 : orderOf x' = 7)
    (hcomm : x * x' = x' * x) (hne : x' ∉ Subgroup.zpowers x)
    (hux : u * x * u⁻¹ = x ^ 2) (hux' : u * x' * u⁻¹ = x')
    (hUx : hypPart (f4d2_E x x') (Subgroup.zpowers x) = ⊥)
    (hUx' : hypPart (f4d2_E x x') (Subgroup.zpowers x') = ⊥)
    (hdec : iSupIndep (fun D : hyperplanes 7 (f4d2_E x x') => hypPart (f4d2_E x x') D))
    (hsup : (⨆ D : hyperplanes 7 (f4d2_E x x'), hypPart (f4d2_E x x') D) =
      commSub ⊤ (f4d2_E x x'))
    (hr1 : rk ↥(hypPart (f4d2_E x x') (f4d2_H x x' 1)) = 0) :
    rk ↥(commSub ⊤ (f4d2_E x x')) =
      3 * rk ↥(hypPart (f4d2_E x x') (f4d2_H x x' 3)) := by
  rw [f4d2_rk_eq_sum_all hdec hsup, f4d2_sum_hyperplanes hx7 hx'7 hcomm hne]
  have h0 : rk ↥(hypPart (f4d2_E x x') (f4d2_H x x' 0)) = 0 := by
    rw [f4d2_H_zero, hUx']
    exact rk_bot
  rw [hUx, rk_bot, zero_add, Fin.sum_univ_seven, h0,
    f4d2_rk_H4_eq_H2 hx7 hx'7 hcomm hne hux hux',
    f4d2_rk_H2_eq_H1 hx7 hx'7 hcomm hne hux hux',
    f4d2_rk_H5_eq_H3 hx7 hx'7 hcomm hne hux hux',
    f4d2_rk_H6_eq_H3 hx7 hx'7 hcomm hne hux hux',
    hr1]
  ring

theorem f4d2_rk_nine (hW2 : ∀ w : W, w ^ 2 = 1) (hx7 : orderOf x = 7)
    (hx'7 : orderOf x' = 7) (hcomm : x * x' = x' * x) (hne : x' ∉ Subgroup.zpowers x)
    (hthree : ∀ D ∈ hyperplanes 7 (f4d2_E x x'), 3 ∣ rk ↥(hypPart (f4d2_E x x') D))
    (hbound : 3 * rk ↥(hypPart (f4d2_E x x') (f4d2_H x x' 1)) +
      2 * rk ↥(hypPart (f4d2_E x x') (f4d2_H x x' 3)) ≤ 6)
    (hrkM : rk ↥(commSub ⊤ (f4d2_E x x')) =
      3 * rk ↥(hypPart (f4d2_E x x') (f4d2_H x x' 3)))
    (hMne : commSub ⊤ (f4d2_E x x') ≠ ⊥) :
    rk ↥(commSub ⊤ (f4d2_E x x')) = 9 := by
  obtain ⟨a, ha⟩ := hthree (f4d2_H x x' 1) (f4d2_H_mem hx7 hx'7 hcomm hne 1)
  obtain ⟨b, hb⟩ := hthree (f4d2_H x x' 3) (f4d2_H_mem hx7 hx'7 hcomm hne 3)
  rw [ha] at hbound
  rw [hb] at hbound hrkM
  have hb1 : b = 1 := by
    have hbpos : b ≠ 0 := by
      intro h0
      apply hMne
      apply (rk_eq_zero_iff hW2).mp
      rw [hrkM, h0]
    omega
  rw [hrkM, hb1]

theorem f4d2_supp_rk (hW2 : ∀ w : W, w ^ 2 = 1) (hx7 : orderOf x = 7)
    (hx'7 : orderOf x' = 7) (hcomm : x * x' = x' * x) (hne : x' ∉ Subgroup.zpowers x)
    (hux : u * x * u⁻¹ = x ^ 2) (hux' : u * x' * u⁻¹ = x')
    (hUx : hypPart (f4d2_E x x') (Subgroup.zpowers x) = ⊥)
    (hUx' : hypPart (f4d2_E x x') (Subgroup.zpowers x') = ⊥)
    (hr1 : rk ↥(hypPart (f4d2_E x x') (f4d2_H x x' 1)) = 0)
    (hr3 : rk ↥(hypPart (f4d2_E x x') (f4d2_H x x' 3)) = 3) :
    ∀ D ∈ hypSupp 7 (f4d2_E x x'), rk ↥(hypPart (f4d2_E x x') D) = 3 := by
  intro D hD
  have hH0 : hypPart (f4d2_E x x') (f4d2_H x x' 0) = ⊥ := by
    rw [f4d2_H_zero]; exact hUx'
  have hH1 : hypPart (f4d2_E x x') (f4d2_H x x' 1) = ⊥ :=
    (rk_eq_zero_iff hW2).mp hr1
  have hH2 : hypPart (f4d2_E x x') (f4d2_H x x' 2) = ⊥ := by
    apply (rk_eq_zero_iff hW2).mp
    rw [f4d2_rk_H2_eq_H1 hx7 hx'7 hcomm hne hux hux']
    exact hr1
  have hH4 : hypPart (f4d2_E x x') (f4d2_H x x' 4) = ⊥ := by
    apply (rk_eq_zero_iff hW2).mp
    rw [f4d2_rk_H4_eq_H2 hx7 hx'7 hcomm hne hux hux',
      f4d2_rk_H2_eq_H1 hx7 hx'7 hcomm hne hux hux']
    exact hr1
  have hH5 : rk ↥(hypPart (f4d2_E x x') (f4d2_H x x' 5)) = 3 := by
    rw [f4d2_rk_H5_eq_H3 hx7 hx'7 hcomm hne hux hux']; exact hr3
  have hH6 : rk ↥(hypPart (f4d2_E x x') (f4d2_H x x' 6)) = 3 := by
    rw [f4d2_rk_H6_eq_H3 hx7 hx'7 hcomm hne hux hux']; exact hr3
  have hhyp : D ∈ hyperplanes 7 (f4d2_E x x') := hD.1
  have hne_bot : hypPart (f4d2_E x x') D ≠ ⊥ := hD.2
  rw [f4d2_hyperplanes_eq hx7 hx'7 hcomm hne] at hhyp
  rcases hhyp with hDX | ⟨i, hi⟩
  · rw [hDX] at hne_bot ⊢
    exact absurd hUx hne_bot
  · rw [← hi] at hne_bot ⊢
    fin_cases i
    · exact absurd hH0 hne_bot
    · exact absurd hH1 hne_bot
    · exact absurd hH2 hne_bot
    · exact hr3
    · exact absurd hH4 hne_bot
    · exact hH5
    · exact hH6

theorem f4d2_hypPart_z_eq_bot (hW2 : ∀ w : W, w ^ 2 = 1) (hx7 : orderOf x = 7)
    (hx'7 : orderOf x' = 7) (hcomm : x * x' = x' * x) (hne : x' ∉ Subgroup.zpowers x)
    (hux : u * x * u⁻¹ = x ^ 2) (hux' : u * x' * u⁻¹ = x')
    (hother : ∀ D ∈ hyperplanes 7 (f4d2_E x x'), D ≠ Subgroup.zpowers x →
      D ≠ Subgroup.zpowers x' → D ≠ Subgroup.zpowers (x * x'⁻¹) →
      hypPart (f4d2_E x x') D = ⊥) :
    hypPart (f4d2_E x x') (Subgroup.zpowers (x * x'⁻¹)) = ⊥ := by
  rw [← f4d2_H_six hx7 hcomm]
  have h3 : hypPart (f4d2_E x x') (f4d2_H x x' 3) = ⊥ :=
    hother (f4d2_H x x' 3) (f4d2_H_mem hx7 hx'7 hcomm hne 3)
      (f4d2_H_ne_zpowers hx7 hx'7 hcomm hne 3)
      (f4d2_H_ne_X' hx7 hx'7 hcomm hne (by decide : (3 : Fin 7) ≠ 0))
      (f4d2_H_ne_six hx7 hx'7 hcomm hne (by decide : (3 : Fin 7) ≠ 6))
  apply (rk_eq_zero_iff hW2).mp
  rw [f4d2_rk_H6_eq_H3 hx7 hx'7 hcomm hne hux hux', h3, rk_bot]

omit [Finite W] in
theorem f4d2_map_conj_zero (u : MulAut W) (K : Subgroup (MulAut W)) :
    K.map (MulAut.conj (u ^ 0)).toMonoidHom = K := by
  rw [pow_zero, map_one]
  exact Subgroup.map_id K

omit [Finite W] in
theorem f4d2_supp_trans (hx7 : orderOf x = 7) (_hx'7 : orderOf x' = 7)
    (_hcomm : x * x' = x' * x) (_hne : x' ∉ Subgroup.zpowers x)
    (hux : u * x * u⁻¹ = x ^ 2) (hux' : u * x' * u⁻¹ = x')
    (hclass : ∀ D ∈ hypSupp 7 (f4d2_E x x'), D = f4d2_H x x' 3 ∨ D = f4d2_H x x' 5 ∨
      D = f4d2_H x x' 6) :
    ∀ D ∈ hypSupp 7 (f4d2_E x x'), ∀ D' ∈ hypSupp 7 (f4d2_E x x'),
      ∃ m : ℕ, D' = D.map (MulAut.conj (u ^ m)).toMonoidHom := by
  have h36 : (f4d2_H x x' 3).map (MulAut.conj u).toMonoidHom = f4d2_H x x' 6 := by
    have h := s134b_map_conj_hyperplane (x := x) (x' := x') (u := u) hux hux' 3
    simpa [f4d2_H] using h
  have h65 : (f4d2_H x x' 6).map (MulAut.conj u).toMonoidHom = f4d2_H x x' 5 := by
    have h := s134b_map_conj_hyperplane (x := x) (x' := x') (u := u) hux hux' 6
    rw [f4d2_pow_twelve hx7] at h
    simpa [f4d2_H] using h
  have h53 : (f4d2_H x x' 5).map (MulAut.conj u).toMonoidHom = f4d2_H x x' 3 := by
    have h := s134b_map_conj_hyperplane (x := x) (x' := x') (u := u) hux hux' 5
    rw [f4d2_pow_ten hx7] at h
    simpa [f4d2_H] using h
  have hff : (MulAut.conj u * MulAut.conj u).toMonoidHom =
      (MulAut.conj u).toMonoidHom.comp (MulAut.conj u).toMonoidHom := rfl
  have h35 : (f4d2_H x x' 3).map (MulAut.conj (u ^ 2)).toMonoidHom = f4d2_H x x' 5 := by
    rw [pow_two, map_mul, hff, ← Subgroup.map_map, h36, h65]
  have h63 : (f4d2_H x x' 6).map (MulAut.conj (u ^ 2)).toMonoidHom = f4d2_H x x' 3 := by
    rw [pow_two, map_mul, hff, ← Subgroup.map_map, h65, h53]
  have h56 : (f4d2_H x x' 5).map (MulAut.conj (u ^ 2)).toMonoidHom = f4d2_H x x' 6 := by
    rw [pow_two, map_mul, hff, ← Subgroup.map_map, h53, h36]
  intro D hD D' hD'
  rcases hclass D hD with rfl | rfl | rfl <;>
    rcases hclass D' hD' with rfl | rfl | rfl
  · exact ⟨0, (f4d2_map_conj_zero u (f4d2_H x x' 3)).symm⟩
  · exact ⟨2, h35.symm⟩
  · exact ⟨1, h36.symm⟩
  · exact ⟨1, h53.symm⟩
  · exact ⟨0, (f4d2_map_conj_zero u (f4d2_H x x' 5)).symm⟩
  · exact ⟨2, h56.symm⟩
  · exact ⟨2, h63.symm⟩
  · exact ⟨1, h65.symm⟩
  · exact ⟨0, (f4d2_map_conj_zero u (f4d2_H x x' 6)).symm⟩

omit [Finite W] in
theorem f4d2_r1_eq_zero (hx7 : orderOf x = 7) (hx'7 : orderOf x' = 7)
    (hcomm : x * x' = x' * x) (hne : x' ∉ Subgroup.zpowers x)
    (hthree : ∀ D ∈ hyperplanes 7 (f4d2_E x x'), 3 ∣ rk ↥(hypPart (f4d2_E x x') D))
    (hbound : 3 * rk ↥(hypPart (f4d2_E x x') (f4d2_H x x' 1)) +
      2 * rk ↥(hypPart (f4d2_E x x') (f4d2_H x x' 3)) ≤ 6) :
    rk ↥(hypPart (f4d2_E x x') (f4d2_H x x' 1)) = 0 := by
  obtain ⟨a, ha⟩ := hthree (f4d2_H x x' 1) (f4d2_H_mem hx7 hx'7 hcomm hne 1)
  rw [ha] at hbound
  have ha0 : a = 0 := by omega
  rw [ha, ha0, mul_zero]

theorem f4d2_hypSupp_class (hW2 : ∀ w : W, w ^ 2 = 1) (hx7 : orderOf x = 7)
    (hx'7 : orderOf x' = 7) (hcomm : x * x' = x' * x) (hne : x' ∉ Subgroup.zpowers x)
    (hux : u * x * u⁻¹ = x ^ 2) (hux' : u * x' * u⁻¹ = x')
    (hUx : hypPart (f4d2_E x x') (Subgroup.zpowers x) = ⊥)
    (hUx' : hypPart (f4d2_E x x') (Subgroup.zpowers x') = ⊥)
    (hr1 : rk ↥(hypPart (f4d2_E x x') (f4d2_H x x' 1)) = 0)
    (hr3 : rk ↥(hypPart (f4d2_E x x') (f4d2_H x x' 3)) = 3) :
    ∀ D ∈ hypSupp 7 (f4d2_E x x'), D = f4d2_H x x' 3 ∨ D = f4d2_H x x' 5 ∨
      D = f4d2_H x x' 6 := by
  intro D hD
  have hhyp : D ∈ hyperplanes 7 (f4d2_E x x') := hD.1
  have hval := f4d2_supp_rk hW2 hx7 hx'7 hcomm hne hux hux' hUx hUx' hr1 hr3 D hD
  have hH0 : rk ↥(hypPart (f4d2_E x x') (f4d2_H x x' 0)) = 0 := by
    rw [f4d2_H_zero, hUx']; exact rk_bot
  have hH2 : rk ↥(hypPart (f4d2_E x x') (f4d2_H x x' 2)) = 0 := by
    rw [f4d2_rk_H2_eq_H1 hx7 hx'7 hcomm hne hux hux']; exact hr1
  have hH4 : rk ↥(hypPart (f4d2_E x x') (f4d2_H x x' 4)) = 0 := by
    rw [f4d2_rk_H4_eq_H2 hx7 hx'7 hcomm hne hux hux',
      f4d2_rk_H2_eq_H1 hx7 hx'7 hcomm hne hux hux']; exact hr1
  rw [f4d2_hyperplanes_eq hx7 hx'7 hcomm hne] at hhyp
  rcases hhyp with hDX | ⟨i, hi⟩
  · exfalso
    rw [hDX, hUx, rk_bot] at hval
    norm_num at hval
  · rw [← hi] at hval ⊢
    fin_cases i
    · exact absurd hval (by
        show ¬(rk ↥(hypPart (f4d2_E x x') (f4d2_H x x' 0)) = 3)
        rw [hH0]; norm_num)
    · exact absurd hval (by
        show ¬(rk ↥(hypPart (f4d2_E x x') (f4d2_H x x' 1)) = 3)
        rw [hr1]; norm_num)
    · exact absurd hval (by
        show ¬(rk ↥(hypPart (f4d2_E x x') (f4d2_H x x' 2)) = 3)
        rw [hH2]; norm_num)
    · exact Or.inl rfl
    · exact absurd hval (by
        show ¬(rk ↥(hypPart (f4d2_E x x') (f4d2_H x x' 4)) = 3)
        rw [hH4]; norm_num)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

end Basic

end CFSG.LocalAnalysis.WeakClosure81
