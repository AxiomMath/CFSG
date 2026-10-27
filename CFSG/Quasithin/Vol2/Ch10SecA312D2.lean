module

public import CFSG.Quasithin.Vol2.Ch10SecA312D1
public import CFSG.Quasithin.Vol2.Ch10SecA312C6

public section

namespace CFSG.Quasithin.Vol2.Ch10.A312D

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Ch10.A312C

theorem card_of_isZ4StarExtra2 {V : Type} [Group V] (h : IsZ4StarExtra2 V) :
    Nat.card V = 2 ^ 6 := by
  obtain ⟨Z, E, hZ, -, ⟨-, hE⟩, hZc, hZE, hI⟩ := h
  have hN : Z ≤ Subgroup.normalizer (E : Set V) := fun z hz =>
    Subgroup.mem_normalizer_iff.mpr fun x => by
      rw [← Subgroup.mem_center_iff.mp (hZc hz) x, mul_inv_cancel_right]
  have h := A312C.card_sup_mul_card_inf hN
  rw [hZE, Subgroup.card_top, inf_comm, hI, hE, hZ] at h
  norm_num at h ⊢
  omega

variable {X : Type} [Group X] [Finite X] {B₁ B₂ : Subgroup X}

theorem dvd_card_of_alt5 (hB₁ : ⁅B₁, B₁⁆ = B₁) (hc : ⁅B₁, B₂⁆ ≤ pCoreOf 2 B₁ ⊓ pCoreOf 2 B₂)
    (e : ModO2 B₁ ≃* ModO2 B₂) (h : IsAlt 5 ↥B₁) : 3600 ∣ Nat.card X := by
  obtain ⟨φ⟩ := h
  have hk : IsPGroup 2 φ.toMonoidHom.ker := by
    rw [(MonoidHom.ker_eq_bot_iff _).mpr φ.injective]
    exact IsPGroup.of_bot
  have h1 := card_mul_dvd_of_hom hB₁ hc e φ.toMonoidHom φ.surjective hk
  rw [card_alt5 ⟨φ⟩, card_alt5 ⟨MulEquiv.refl _⟩] at h1
  exact h1

theorem dvd_card_of_ext (hB₁ : ⁅B₁, B₁⁆ = B₁) (hc : ⁅B₁, B₂⁆ ≤ pCoreOf 2 B₁ ⊓ pCoreOf 2 B₂)
    (e : ModO2 B₁ ≃* ModO2 B₂) {V : Subgroup ↥B₁} [V.Normal] {n : ℕ} (hV : Nat.card V = 2 ^ n)
    [IsSimpleGroup (↥B₁ ⧸ V)] :
    Nat.card (↥B₁ ⧸ V) * 2 ^ n * Nat.card (↥B₁ ⧸ V) ∣ Nat.card X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hk : IsPGroup 2 (QuotientGroup.mk' V).ker := by
    rw [QuotientGroup.ker_mk']
    exact IsPGroup.of_card hV
  have h1 := card_mul_dvd_of_hom hB₁ hc e (QuotientGroup.mk' V) (QuotientGroup.mk'_surjective V) hk
  rwa [V.card_eq_card_quotient_mul_card_subgroup, hV] at h1

theorem sq_dvd_of_sl2 (hB₁ : ⁅B₁, B₁⁆ = B₁) (hc : ⁅B₁, B₂⁆ ≤ pCoreOf 2 B₁ ⊓ pCoreOf 2 B₂)
    (e : ModO2 B₁ ≃* ModO2 B₂) {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) (h : IsSL2 p ↥B₁) :
    p * (p ^ 2 - 1) * (p * (p ^ 2 - 1)) ∣ 2 * Nat.card X := by
  have hBc := card_of_isSL2 h
  obtain ⟨φ⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [Nat.card_zmod]; omega)
  have hZ : Nat.card Z = 1 ∨ Nat.card Z = 2 := by
    have h1 : Nat.card Z ≤ 2 := by
      rw [Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (0 : Fin 2)).toEquiv,
        Fintype.card_fin]
      exact card_rootsOfUnity (R := ZMod p) (k := 2)
    have h2 := Nat.card_pos (α := Z)
    omega
  have hZ2 : Nat.card Z ∣ 2 := by
    rcases hZ with h1 | h1
    · rw [h1]; exact one_dvd 2
    · rw [h1]
  have hZp : IsPGroup 2 Z := by
    rcases hZ with h1 | h1
    · exact IsPGroup.of_card (n := 0) (by rw [h1]; rfl)
    · exact IsPGroup.of_card (n := 1) (by rw [h1]; rfl)
  have hk : IsPGroup 2 ((QuotientGroup.mk' Z).comp φ.toMonoidHom).ker := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact hZp.comap_of_injective _ φ.injective
  have h1 := card_mul_dvd_of_hom hB₁ hc e ((QuotientGroup.mk' Z).comp φ.toMonoidHom)
    ((QuotientGroup.mk'_surjective Z).comp φ.surjective) hk
  have h2 : Nat.card B₁ =
      Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) * Nat.card Z := by
    rw [Nat.card_congr φ.toEquiv]
    exact Z.card_eq_card_quotient_mul_card_subgroup
  have h3 : Nat.card ↥B₁ * Nat.card ↥B₁ ∣ Nat.card X * 2 := by
    calc Nat.card ↥B₁ * Nat.card ↥B₁ = Nat.card ↥B₁ *
          Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) * Nat.card Z := by
          rw [mul_assoc, ← h2]
      _ ∣ Nat.card X * 2 := mul_dvd_mul h1 hZ2
  rw [← hBc, mul_comm 2]
  exact h3

end CFSG.Quasithin.Vol2.Ch10.A312D
