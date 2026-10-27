module

public import CFSG.Quasithin.Background.F918Z3Cb
public import CFSG.Quasithin.Background.F918Z6Symm
public import CFSG.Quasithin.Background.F918Z3Ca
public import CFSG.Quasithin.Background.F918Z3D

public section

namespace CFSG.Quasithin

open scoped Matrix

namespace Z3Cg2

theorem exists_card_eq_two_pow (F : Type) [Field F] [Finite F] [CharP F 2] :
    ∃ e : ℕ, Nat.card F = 2 ^ e := by
  have := Fintype.ofFinite F
  obtain ⟨n, -, hn⟩ := FiniteField.card F 2
  exact ⟨n, by rw [Nat.card_eq_fintype_card]; exact hn⟩

section Params

variable {V : Type} [CommGroup V] {D X : Subgroup (MulAut V)} {F : Type} [Field F] [Finite F]
  {d : ℕ} {β : V ≃* Multiplicative (Matrix (Fin d) (Fin d) F)}
  {ρ : ↥D →* Matrix.GeneralLinearGroup (Fin d) F}
  {σ : ↥X →* Matrix.GeneralLinearGroup (Fin d) F}

theorem params_of_orth [CharP F 2] (hd : 3 ≤ d) (hM : IsMatModel D X β ρ σ) {I : Subgroup V}
    (hI0 : I ≠ ⊥) (hIinv : ∀ y ∈ D, ∀ v ∈ I, y v ∈ I)
    (hImin : ∀ U ≤ I, (∀ y ∈ D, ∀ v ∈ U, y v ∈ U) → U = ⊥ ∨ U = I) {a : ℕ}
    (hO : OrthMinusData D I a) : d = 4 ∧ Nat.card F = 2 ^ a := by
  obtain ⟨e, he⟩ := exists_card_eq_two_pow F
  obtain ⟨F₀, _, _, _, hcard, hcomm⟩ := hO.scalars
  have hae : a ∣ e := Z3D.dvd_of_smul_comm hM hI0 hIinv hImin hcomm hcard he
  obtain ⟨k, rfl⟩ := hae
  have h1 : Nat.card ↥I = Nat.card F ^ d := Z3D.card_eq_pow hM hI0 hIinv hImin
  rw [hO.card, he, ← pow_mul] at h1
  have h2 : 4 * a = a * k * d := Nat.pow_right_injective (le_refl 2) h1
  have ha : 1 ≤ a := hO.one_le
  have h3 : 4 = k * d := by
    have h4 : a * 4 = a * (k * d) := by rw [← mul_assoc]; omega
    exact Nat.eq_of_mul_eq_mul_left (by omega) h4
  have hk : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · omega
    · exact hk
  have hd4 : d ≤ 4 := by nlinarith
  have hd' : d = 4 := by
    interval_cases d
    · omega
    · rfl
  subst hd'
  have hk1 : k = 1 := by omega
  subst hk1
  exact ⟨rfl, by rw [he, mul_one]⟩

theorem card_V_eq (β : V ≃* Multiplicative (Matrix (Fin d) (Fin d) F)) :
    Nat.card V = Nat.card F ^ (d * d) := by
  rw [Nat.card_congr β.toEquiv, Nat.card_congr Multiplicative.toAdd]
  exact InvolMat.card_matrix F d

theorem card_V_orth (β : V ≃* Multiplicative (Matrix (Fin d) (Fin d) F)) {a : ℕ} (hd : d = 4)
    (hF : Nat.card F = 2 ^ a) : Nat.card V = 2 ^ (16 * a) := by
  rw [card_V_eq β, hF, hd, ← pow_mul]
  congr 1
  ring

end Params

theorem isPSL_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {n p f : ℕ}
    (h : IsPSL n p f Y) : IsPSL n p f X := by
  obtain ⟨hadm, K, _, _, hK, ⟨e'⟩⟩ := h
  exact ⟨hadm, K, inferInstance, inferInstance, hK, ⟨e.trans e'⟩⟩

theorem isPSL_X {V : Type} [CommGroup V] {D X : Subgroup (MulAut V)} {s : MulAut V}
    (hDX : X = D.map (MulAut.conj s).toMonoidHom) {n p f : ℕ} (h : IsPSL n p f ↥D) :
    IsPSL n p f ↥X :=
  isPSL_of_mulEquiv (conjEquivOfEq hDX).symm h

end Z3Cg2

end CFSG.Quasithin
