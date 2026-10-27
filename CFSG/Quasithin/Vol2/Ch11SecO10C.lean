module

public import CFSG.Quasithin.Vol2.Ch11SecAFactsFlag
public import CFSG.Quasithin.Vol2.Ch11SecAFacts

public section

namespace CFSG.Quasithin.Vol2.Ch11.O10

open CFSG.Open CFSG.Quasithin
open Ch11.SecA (EndStableW stabW IsFlagW)

variable {W : Type*} [CommGroup W]

@[expose] def fixW (Q : Subgroup (MulAut W)) : Subgroup W where
  carrier := {w | ∀ x ∈ Q, x w = w}
  mul_mem' := fun {a b} ha hb x hx => by rw [map_mul, ha x hx, hb x hx]
  one_mem' := fun x _ => map_one x
  inv_mem' := fun {a} ha x hx => by rw [map_inv, ha x hx]

theorem fixW_ne_top {Q : Subgroup (MulAut W)} (hQ : Q ≠ ⊥) : fixW Q ≠ ⊤ := by
  intro h
  apply hQ
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  ext w
  have hw : w ∈ fixW Q := h ▸ Subgroup.mem_top w
  exact hw x hx

theorem endStableW_fixW {H Q : Subgroup (MulAut W)} (hQH : Q ≤ H) : EndStableW H ⊥ (fixW Q) := by
  intro φ _ hc u hu x hx
  have h := hc x (hQH hx) u
  rw [Subgroup.mem_bot, mul_inv_eq_one, hu x hx] at h
  exact h.symm

theorem mem_stabW_fixW {Q : Subgroup (MulAut W)} {x : MulAut W}
    (hx : x ∈ Subgroup.normalizer (Q : Set (MulAut W))) : x ∈ stabW (fixW Q) := by
  rw [Ch11.SecA.mem_stabW]
  intro w
  constructor
  · intro hw y hy
    have hy' : x⁻¹ * y * x⁻¹⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx) y).mp hy
    have h1 := hw _ hy'
    rw [inv_inv, MulAut.mul_apply, MulAut.mul_apply] at h1
    calc y (x w) = x (x⁻¹ (y (x w))) := (MulAut.apply_inv_self W x _).symm
      _ = x w := by rw [h1]
  · intro hw y hy
    have hy' : x * y * x⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hx y).mp hy
    have h1 := hw _ hy'
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self] at h1
    exact x.injective h1

variable [Finite W]

theorem fixW_ne_bot (hW : ∀ w : W, w ^ 2 = 1) (hW1 : Nontrivial W) {Q : Subgroup (MulAut W)}
    (hQ : IsPGroup 2 Q) : fixW Q ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hW2 : IsPGroup 2 W := fun w => ⟨1, by rw [pow_one]; exact hW w⟩
  have hmod := hQ.card_modEq_card_fixedPoints W
  obtain ⟨k, hk⟩ := hW2.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, Nat.card_eq_one_iff_unique] at hk
    exact (not_subsingleton W) hk.1
  have h0 : Nat.card W % 2 = 0 := by
    obtain ⟨c, hc⟩ : 2 ∣ Nat.card W := hk ▸ dvd_pow_self 2 hk0
    omega
  have hfix : Nat.card (MulAction.fixedPoints Q W) % 2 = 0 := by
    unfold Nat.ModEq at hmod
    omega
  intro hbot
  have hsub : ∀ w ∈ MulAction.fixedPoints Q W, w = 1 := by
    intro w hw
    have : w ∈ fixW Q := fun x hx => hw ⟨x, hx⟩
    rw [hbot] at this
    exact Subgroup.mem_bot.mp this
  have h1 : Nat.card (MulAction.fixedPoints Q W) = 1 := by
    rw [Nat.card_eq_one_iff_exists]
    refine ⟨⟨1, fun x => map_one (x : MulAut W)⟩, fun ⟨w, hw⟩ => ?_⟩
    exact Subtype.ext (hsub w hw)
  omega

theorem exists_isFlagW_fixW (hW : ∀ w : W, w ^ 2 = 1) (hW1 : Nontrivial W)
    {H P Q : Subgroup (MulAut W)} {q : ℕ} (hq : 2 ≤ q)
    (hpow : ∀ U : Subgroup W, EndStableW H ⊥ U → ∃ d : ℕ, Nat.card U = q ^ d)
    (hcard : Nat.card W ≤ q ^ 4) (hQ : IsPGroup 2 Q) (hQ1 : Q ≠ ⊥) (hQH : Q ≤ H)
    (hPQ : P ≤ Subgroup.normalizer (Q : Set (MulAut W))) :
    ∃ d : ℕ, (d = 1 ∨ d = 2 ∨ d = 3) ∧ IsFlagW H P ⊥ q d (fixW Q) := by
  obtain ⟨d, hd⟩ := hpow _ (endStableW_fixW hQH)
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hd
    exact fixW_ne_bot hW hW1 hQ (Subgroup.eq_bot_of_card_eq _ hd)
  have hd3 : d ≤ 3 := by
    by_contra h
    apply fixW_ne_top hQ1
    apply Subgroup.eq_top_of_card_eq
    apply le_antisymm (Subgroup.card_le_card_group _)
    calc Nat.card W ≤ q ^ 4 := hcard
      _ ≤ q ^ d := Nat.pow_le_pow_right (by omega) (by omega)
      _ = Nat.card (fixW Q) := hd.symm
  refine ⟨d, by omega, bot_le, endStableW_fixW hQH, ?_, fun x hx => mem_stabW_fixW (hPQ hx)⟩
  rw [Subgroup.relIndex_bot_left, hd]

end CFSG.Quasithin.Vol2.Ch11.O10
