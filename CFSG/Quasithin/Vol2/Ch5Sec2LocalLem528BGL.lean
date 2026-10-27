module

public import CFSG.Sporadic.J4
public import CFSG.Quasithin.Vol2.Ch11SecA11Cases1

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.Vol2.Ch11.SecA CFSG.Blueprint

theorem card_mulAut_of_sq_eq_one {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {d : ℕ} (hd : Nat.card V = 2 ^ d) :
    Nat.card (MulAut V) = Nat.card (GL (Fin d) (ZMod 2)) := by
  let _ : Module (ZMod 2) (Additive V) := AddCommGroup.zmodModule (n := 2) fun x => by
    rw [two_nsmul]
    change Additive.ofMul (Additive.toMul x * Additive.toMul x) = 0
    rw [← sq, hV]
    rfl
  have : Module.Finite (ZMod 2) (Additive V) := Module.Finite.of_finite
  have hrank : Module.finrank (ZMod 2) (Additive V) = d := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
    rw [Nat.card_zmod, show Nat.card (Additive V) = Nat.card V from rfl, hd] at h
    exact (Nat.pow_right_injective le_rfl h).symm
  let b := Module.finBasisOfFinrankEq (ZMod 2) (Additive V) hrank
  have e1 : MulAut V ≃ (Additive V ≃+ Additive V) := MulEquiv.toAdditive
  have e2 : (Additive V ≃+ Additive V) ≃ (Additive V ≃ₗ[ZMod 2] Additive V) :=
    { toFun := fun e => e.toLinearEquiv (fun c x => ZMod.map_smul e c x)
      invFun := fun l => l.toAddEquiv
      left_inv := fun e => by ext; rfl
      right_inv := fun l => by ext; rfl }
  rw [Nat.card_congr (e1.trans e2), ← Nat.card_congr
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Additive V)).toEquiv]
  exact Nat.card_congr (Matrix.GeneralLinearGroup.toLin' b).toEquiv.symm

theorem card_GL4_two : Nat.card (GL (Fin 4) (ZMod 2)) = 20160 := by
  rw [Matrix.card_GL_field, ZMod.card]
  decide

theorem card_GL6_two : Nat.card (GL (Fin 6) (ZMod 2)) = 20158709760 := by
  rw [Matrix.card_GL_field, ZMod.card]
  decide

theorem prime_dvd_card_GL_six {p : ℕ} (hp : p.Prime) (h : p ∣ 20158709760) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 31 := by
  have e : (20158709760 : ℕ) = 2 ^ 15 * 3 ^ 4 * 5 * 7 ^ 2 * 31 := by norm_num
  rw [e] at h
  have hq : ∀ q : ℕ, q.Prime → p ∣ q → p = q := fun q hq h =>
    (Nat.prime_dvd_prime_iff_eq hp hq).mp h
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
      · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
        · exact Or.inl (hq 2 Nat.prime_two (hp.dvd_of_dvd_pow h))
        · exact Or.inr (Or.inl (hq 3 Nat.prime_three (hp.dvd_of_dvd_pow h)))
      · exact Or.inr (Or.inr (Or.inl (hq 5 Nat.prime_five h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (hq 7 (by norm_num) (hp.dvd_of_dvd_pow h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (hq 31 (by norm_num) h))))

variable {X : Type} [Group X]

theorem false_of_dvd_gl6
    (h : Nat.card X ∣ 20158709760)
    (hX : IsPSL 2 5 2 X ∨
      (∃ p : ℕ, p.Prime ∧ p ^ 2 % 5 = 1 ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧ IsPSL 2 p 1 X) ∨
      IsSporadic .J1 X ∨ IsSporadic .J4 X) : False := by
  have hsp : ∀ {s : TauCeti.SporadicName} {N : ℕ}, Nat.card (NativeSporadic.Carrier s) = N →
      IsSporadic s X → Nat.card X = N := fun hN ⟨e⟩ => (Nat.card_congr e.toEquiv).trans hN
  rcases hX with hX | ⟨p, hp, hp5, hp8, hX⟩ | hX | hX
  · rw [card_of_isPSL (by norm_num) hX] at h
    exact absurd h (by decide)
  · have h2 := two_mul_card_of_isPSL_two hp (by omega) hX
    have hpX : p ∣ Nat.card X := by
      have : p ∣ 2 * Nat.card X := h2 ▸ dvd_mul_right p _
      exact ((Nat.coprime_primes hp Nat.prime_two).mpr (by omega)).dvd_of_dvd_mul_left this
    rcases prime_dvd_card_GL_six hp (hpX.trans h) with rfl | rfl | rfl | rfl | rfl <;>
      simp_all
  · rw [hsp (s := .J1) (N := 175560) CFSG.Sporadic.J1.card_J1 hX] at h
    exact absurd h (by decide)
  · rw [hsp (s := .J4) (N := 86775571046077562880) CFSG.Sporadic.J4.card_J4 hX] at h
    exact absurd h (by decide)

theorem false_of_hat7_dvd_gl4 (h : Nat.card X ∣ 20160)
    (hX : IsHat X (alternatingGroup (Fin 7))) : False := by
  rw [card_of_isHat hX] at h
  have : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    decide
  rw [this] at h
  exact absurd h (by decide)

end CFSG.Quasithin.H13
