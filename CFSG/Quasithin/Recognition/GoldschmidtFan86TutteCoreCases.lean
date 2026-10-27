module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteCoreSupport
public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteCoreRel

public section

namespace CFSG.Quasithin.Fan86.Tutte

variable {H : Type*} [Group H] {s : ℕ} {r l ξ : H} {Hs : ℕ → Subgroup H}

theorem shift_r_conj (r l : H) (i : ℕ) (K : List ℤ) (hK : Even K.length) :
    (MulAut.conj (r ^ (i : ℤ))).toMonoidHom (nfw r l (-1) K) =
      nfw r l (-1) (K.map (· - (i : ℤ))) := by
  have := nfw_shift_r r l (-(i : ℤ)) K hK
  rw [neg_neg] at this
  show r ^ (i : ℤ) * nfw r l (-1) K * (r ^ (i : ℤ))⁻¹ = _
  rw [← zpow_neg, this]
  simp [sub_eq_add_neg]

theorem support7 (h : IsTutteSys s r l ξ Hs) (h7 : ξ * r * ξ = r⁻¹ ∧ ξ * l * ξ = l⁻¹) {i : ℕ}
    (hi : 1 ≤ i) (his : 2 * i ≤ s) (hab : Abel Hs (s - i)) (L : List ℤ)
    (hL : L.Pairwise (· > ·)) (hL1 : ∀ t ∈ L, 1 ≤ t ∧ t < (s : ℤ)) (hodd : Odd L.length)
    (hLh : nfw r l (-1) L = rho r ξ s * tx r l s) :
    ∀ b : ℤ, (i : ℤ) < b → b < s →
      (Xor (b ∈ L) ((s : ℤ) - b ∈ L) ↔ (2 * i < s ∧ b = (s : ℤ) - i)) :=
  core_support h hi his hab (-1) (Or.inr rfl) (MulAut.conj (r ^ (i : ℤ))).toMonoidHom
    (shift_r_conj r l i) (fun e' he' N => ⟨e', he', xi_nfw7 h h7 e' N⟩) L hL hL1
    (rel7 h h7 hi his hab L hodd hLh)

theorem no_two_cores7 (h : IsTutteSys s r l ξ Hs) (h7 : ξ * r * ξ = r⁻¹ ∧ ξ * l * ξ = l⁻¹)
    (i₁ i₂ : ℕ) (h1 : 1 ≤ i₁) (h12 : i₁ < i₂) (h2 : 2 * i₂ ≤ s) (hab : Abel Hs (s - i₁)) :
    False := by
  obtain ⟨L, hL, hL1, hodd, hLh⟩ := parity_h7 h h7
  have hab2 : Abel Hs (s - i₂) := fun a ha b hb =>
    hab a (Hs_mono h (by omega) (by omega) ha) b (Hs_mono h (by omega) (by omega) hb)
  have hb1 := support7 h h7 (i := i₁) h1 (by omega) hab L hL hL1 hodd hLh ((s : ℤ) - i₁)
    (by omega) (by omega)
  have hb2 := support7 h h7 (i := i₂) (by omega) h2 hab2 L hL hL1 hodd hLh ((s : ℤ) - i₁)
    (by omega) (by omega)
  have e1 : Xor (((s : ℤ) - i₁) ∈ L) ((s : ℤ) - ((s : ℤ) - i₁) ∈ L) :=
    hb1.mpr ⟨by omega, rfl⟩
  have := (hb2.mp e1).2
  omega

end CFSG.Quasithin.Fan86.Tutte
