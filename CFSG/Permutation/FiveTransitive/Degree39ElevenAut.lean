module

public import CFSG.Permutation.FiveTransitive.FreeComplementCard
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG

namespace FiveTransitive.Degree39ElevenAut

open MulAction

theorem action_trivial_of_fixed
    {A H : Type*} [Group A] [Group H] [Finite H] [MulDistribMulAction A H]
    (hA : IsPGroup 3 A) (hH : IsPGroup 11 H) (hcard : Nat.card H ≤ 121)
    (h : H) (hh : h ≠ 1) (hfix : ∀ a : A, a • h = h) (a : A) (x : H) : a • x = x := by
  classical
  let _ : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let _ : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  let C := FixedPoints.subgroup A H
  have hmod : Nat.card H % 3 = Nat.card C % 3 := hA.card_modEq_card_fixedPoints H
  have hle : Nat.card C ≤ Nat.card H := Nat.card_le_card_of_injective (fun c : C => c.val) Subtype.val_injective
  have hne : Nat.card C ≠ 1 := by
    intro he
    have hbot := Subgroup.card_eq_one.mp he
    have hm : h ∈ C := hfix
    rw [hbot,Subgroup.mem_bot] at hm
    exact hh hm
  obtain ⟨e,he⟩ := IsPGroup.iff_card.mp hH
  obtain ⟨d,hd⟩ := IsPGroup.iff_card.mp (hH.to_subgroup C)
  have hbound (k : ℕ) (hk : 11 ^ k ≤ 121) : k ≤ 2 := by
    by_contra hn
    have hp := Nat.pow_le_pow_right (by norm_num : 0 < 11) (by omega : 3 ≤ k)
    norm_num at hp
    omega
  have he2 := hbound e (he ▸ hcard)
  have hd2 := hbound d (hd ▸ hle.trans hcard)
  have hsame : Nat.card C = Nat.card H := by
    rw [he,hd] at hmod hle ⊢
    rw [hd] at hne
    interval_cases e <;> interval_cases d <;> norm_num at *
  have htop : C = ⊤ := Subgroup.eq_top_of_card_eq C hsame
  have hx : x ∈ C := htop ▸ Subgroup.mem_top x
  exact hx a

theorem nine_not_dvd
    (H : Type*) [Group H] [Finite H]
    (hH : IsPGroup 11 H) (hcard : Nat.card H ≤ 121) : ¬ 9 ∣ Nat.card (MulAut H) := by
  classical
  let _ : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let _ : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  by_cases hHone : Nat.card H = 1
  · let _ : Subsingleton H := (Nat.card_eq_one_iff_unique.mp hHone).1
    let _ : Subsingleton (MulAut H) := ⟨fun f g => MulEquiv.ext (fun x => Subsingleton.elim _ _)⟩
    rw [Nat.card_of_subsingleton (1 : MulAut H)]
    norm_num
  let T : Sylow 3 (MulAut H) := default
  have hfree : ∀ t : T, ∀ h : H, h ∉ ({1} : Set H) → t • h = h → t = 1 := by
    intro t h hh hth
    have hh' : h ≠ 1 := by simpa only [Set.mem_singleton_iff] using hh
    let A := stabilizer T h
    apply Subtype.ext
    apply MulEquiv.ext
    intro x
    exact action_trivial_of_fixed (T.isPGroup'.to_subgroup A) hH hcard h hh'
      (fun a => a.property) (⟨t,hth⟩ : A) x
  have hd := FreeComplementCard.card_dvd_complement T H ({1} : Set H)
    (by intro t h hh; rw [Set.mem_singleton_iff] at hh ⊢; rw [hh,smul_one]) hfree
  rw [Set.ncard_singleton] at hd
  intro h9
  have h9T : 9 ∣ Nat.card T := T.pow_dvd_card_of_pow_dvd_card (n := 2) h9
  have hn := h9T.trans hd
  obtain ⟨e,he⟩ := IsPGroup.iff_card.mp hH
  have he2 : e ≤ 2 := by
    by_contra h
    have hp := Nat.pow_le_pow_right (by norm_num : 0 < 11) (by omega : 3 ≤ e)
    rw [← he] at hp
    norm_num at hp
    omega
  rw [he] at hn hHone
  interval_cases e <;> norm_num at *

end FiveTransitive.Degree39ElevenAut

end CFSG
