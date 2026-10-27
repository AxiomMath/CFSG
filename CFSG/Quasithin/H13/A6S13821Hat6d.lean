module

public import CFSG.Quasithin.H13.L32AC47e

public section

namespace CFSG.Quasithin.H13.A6.Hat6

open Equiv Equiv.Perm CFSG.Quasithin.H13.L32A.C.Alt6

theorem conj_injective : Function.Injective (MulAut.conj : A6 →* MulAut A6) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro a ha
  have hc : a ∈ Subgroup.center A6 := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 := congrArg (fun f : MulAut A6 => f g) (MonoidHom.mem_ker.mp ha)
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc g * a = a * g * a⁻¹ * a := by rw [h1]
      _ = a * g := by group
  rwa [alternatingGroup.center_eq_bot (by simp)] at hc

theorem conj_apply_aut {Q : Type*} [Group Q] (f : MulAut Q) (a : Q) :
    MulAut.conj (f a) = f * MulAut.conj a * f⁻¹ := by
  refine MulEquiv.ext fun x => ?_
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul,
    map_inv, MulAut.apply_inv_self]

theorem no_three_normalizes_d0 : ∀ g : Perm (Fin 6), g ^ 3 = 1 → g ≠ 1 →
    ¬ ∀ d ∈ d0List, g * d * g⁻¹ ∈ d0List := by
  decide +kernel

theorem klein_span : ∀ u ∈ invList, ∀ v ∈ invList, u ≠ v → u * v = v * u →
    (∀ e ∈ e1List, e = 1 ∨ e = u ∨ e = v ∨ e = u * v) ∨
      ∀ e ∈ e2List, e = 1 ∨ e = u ∨ e = v ∨ e = u * v := by
  decide +kernel

theorem le_D0_of_normalizes {E : Subgroup A6} (hE : IsPGroup 2 E)
    (hD : D0 ≤ Subgroup.normalizer (E : Set A6)) : E ≤ D0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 D0 := IsPGroup.of_card (n := 3) (by rw [card_D0]; rfl)
  have hP := hE.to_sup_of_normal_left' h2 hD
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
  have hdvd : 2 ^ k ∣ 360 := hk ▸ card_A6 ▸ Subgroup.card_subgroup_dvd_card (E ⊔ D0)
  have hk3 : k ≤ 3 := by
    by_contra h
    have h4 : 2 ^ 4 ∣ 360 := (Nat.pow_dvd_pow 2 (by omega)).trans hdvd
    norm_num at h4
  have hle : Nat.card ↥(E ⊔ D0) ≤ Nat.card D0 := by
    rw [hk, card_D0]
    calc 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hk3
      _ = 8 := by norm_num
  have heq := Subgroup.eq_of_le_of_card_ge (le_sup_right : D0 ≤ E ⊔ D0) hle
  rw [heq]
  exact le_sup_left

theorem ne_D0_of_normalizes {E : Subgroup A6} {x : A6} (hx : orderOf x = 3)
    (hxE : x ∈ Subgroup.normalizer (E : Set A6)) : E ≠ D0 := by
  rintro rfl
  have h3 : x ^ 3 = 1 := by rw [← hx, pow_orderOf_eq_one]
  apply no_three_normalizes_d0 (x : Perm (Fin 6)) (by
    have := congrArg Subtype.val h3
    simpa using this) (fun h => by
      have h1 : x = 1 := Subtype.ext h
      rw [h1, orderOf_one] at hx
      omega)
  intro d hd
  exact (Subgroup.mem_normalizer_iff.mp hxE (toA6 d (d0_sign _ hd))).mp hd

theorem eq_E1_or_E2 {E : Subgroup A6} (hE : E ≤ D0) (h4 : Nat.card E = 4)
    (hinv : ∀ e ∈ E, e * e = 1) : E = E1 ∨ E = E2 := by
  have hne : E ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at h4
    norm_num at h4
  obtain ⟨u, huE, hu1⟩ := (Subgroup.bot_or_exists_ne_one E).resolve_left hne
  obtain ⟨v, hvE, hvz⟩ : ∃ v ∈ E, v ∉ Subgroup.zpowers u := by
    by_contra hcon
    push Not at hcon
    have h2 : Nat.card (Subgroup.zpowers u) = 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (by rw [sq]; exact hinv u huE) hu1
    have h3 : Subgroup.zpowers u = E :=
      le_antisymm (Subgroup.zpowers_le.mpr huE) fun x hx => hcon x hx
    rw [h3, h4] at h2
    norm_num at h2
  have hv1 : v ≠ 1 := fun h => hvz (h ▸ Subgroup.one_mem _)
  have huv : u ≠ v := fun h => hvz (h ▸ Subgroup.mem_zpowers u)
  have hcomm : u * v = v * u := by
    have h1 := hinv _ (E.mul_mem huE hvE)
    rw [mul_eq_one_iff_eq_inv, mul_inv_rev, inv_eq_of_mul_eq_one_right (hinv v hvE),
      inv_eq_of_mul_eq_one_right (hinv u huE)] at h1
    exact h1
  have hu := inv_D0 _ (hE huE) (fun h => hu1 (Subtype.ext h)) (congrArg Subtype.val (hinv u huE))
  have hv := inv_D0 _ (hE hvE) (fun h => hv1 (Subtype.ext h)) (congrArg Subtype.val (hinv v hvE))
  have hcomm' : (u : Perm (Fin 6)) * v = v * u := congrArg Subtype.val hcomm
  have key : ∀ e : A6, (e : Perm (Fin 6)) = 1 ∨ (e : Perm (Fin 6)) = u ∨
      (e : Perm (Fin 6)) = v ∨ (e : Perm (Fin 6)) = u * v → e ∈ E := by
    intro e he
    rcases he with h | h | h | h
    · rw [show e = 1 from Subtype.ext h]
      exact E.one_mem
    · rw [show e = u from Subtype.ext h]
      exact huE
    · rw [show e = v from Subtype.ext h]
      exact hvE
    · rw [show e = u * v from Subtype.ext h]
      exact E.mul_mem huE hvE
  rcases klein_span _ hu _ hv (fun h => huv (Subtype.ext h)) hcomm' with h | h
  · left
    have hle : E1 ≤ E := fun e he => key e (h _ he)
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h4, card_E1])).symm
  · right
    have hle : E2 ≤ E := fun e he => key e (h _ he)
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h4, card_E2])).symm

end CFSG.Quasithin.H13.A6.Hat6
