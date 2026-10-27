module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3SevenNorm
public import CFSG.Quasithin.Background.D2Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin

theorem s16c167_card_ge_of_seven_inverted {U : Type} [CommGroup U] [Finite U]
    (hsq : ∀ u : U, u * u = 1) (hne : Nat.card U ≠ 1) {τ z : MulAut U} (hτ : τ ^ 7 = 1)
    (hfix : ∀ u : U, τ u = u → u = 1) (hz : z * z = 1) (hinv : z * τ * z⁻¹ = τ⁻¹) :
    2 ^ 6 ≤ Nat.card U := by
  classical
  have hord : orderOf (2 : ZMod 7) = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact orderOf_eq_prime (p := 3) (by decide) (by decide)
  haveI : Fintype U := Fintype.ofFinite U
  have hτne : τ ≠ 1 := by
    intro h
    have hall : ∀ u : U, u = 1 := fun u => hfix u (by rw [h]; rfl)
    haveI : Subsingleton U := ⟨fun a b => by rw [hall a, hall b]⟩
    exact hne (Nat.card_of_subsingleton (1 : U))
  have hdvd : 7 ∣ Nat.card U - 1 := by
    haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    have hσ : (MulAut.toPerm U τ) ^ 7 ^ 1 = 1 := by
      rw [pow_one, ← map_pow, hτ, map_one]
    have h := Equiv.Perm.card_compl_support_modEq hσ
    have hcompl : (MulAut.toPerm U τ).supportᶜ = {1} := by
      ext v
      simp only [Finset.mem_compl, Equiv.Perm.mem_support, not_not, Finset.mem_singleton]
      exact ⟨fun hv => hfix v hv, fun hv => by rw [hv]; exact map_one τ⟩
    rw [hcompl, Finset.card_singleton] at h
    have hd : 7 ∣ Fintype.card U - 1 := (Nat.modEq_iff_dvd' Fintype.card_pos).1 h
    rwa [← Nat.card_eq_fintype_card] at hd
  have hp : IsPGroup 2 U := isPGroup_two_of_sq_eq_one (fun u => by rw [pow_two]; exact hsq u)
  have hcard : Nat.card U = 2 ^ rk U := card_eq_two_pow_of_isPGroup hp
  rw [hcard] at hdvd hne ⊢
  have hr0 : rk U ≠ 0 := fun h0 => hne (by rw [h0]; rfl)
  have h1 : (1 : ℕ) ≡ 2 ^ rk U [MOD 7] :=
    (Nat.modEq_iff_dvd' Nat.one_le_two_pow).2 hdvd
  have hz7 : (2 : ZMod 7) ^ rk U = 1 := by
    have h2 := (ZMod.natCast_eq_natCast_iff _ _ _).2 h1.symm
    simpa using h2
  have h3 : 3 ∣ rk U := hord ▸ orderOf_dvd_of_pow_eq_one hz7
  have hr3 : rk U ≠ 3 := by
    intro h3'
    have hY : Nat.card U = 8 := by rw [hcard, h3']; norm_num
    have hxl : ∃ a : ℕ, z * τ * z⁻¹ = τ ^ a :=
      ⟨6, by
        rw [hinv]
        exact inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hτ)⟩
    have hz1 : z = 1 := s16c167_seven_normalizer_trivial hY hsq hτ hτne hz hxl
    rw [hz1] at hinv
    have hττ : τ * τ = 1 := by
      have h4 : τ = τ⁻¹ := by simpa using hinv
      exact mul_eq_one_iff_eq_inv.2 h4
    apply hτne
    calc τ = τ ^ 7 * ((τ ^ 2) ^ 3)⁻¹ := by group
      _ = 1 := by rw [hτ, pow_two, hττ]; simp
  have hr6 : 6 ≤ rk U := by omega
  exact Nat.pow_le_pow_right (by norm_num) hr6

theorem s16c167_card_ge_of_seven_inverted_sub {W : Type} [CommGroup W] [Finite W]
    (hsq : ∀ w : W, w * w = 1) {U : Subgroup W} (hU : U ≠ ⊥) {τ z : MulAut W}
    (hτU : τ ∈ stabSub U) (hzU : z ∈ stabSub U) (hτ : τ ^ 7 = 1)
    (hfix : ∀ u ∈ U, τ u = u → u = 1) (hz : z * z = 1) (hinv : z * τ * z⁻¹ = τ⁻¹) :
    2 ^ 6 ≤ Nat.card U := by
  have hτ' : resHom U ⟨τ, hτU⟩ ^ 7 = 1 := by
    rw [← map_pow]
    have : (⟨τ, hτU⟩ : stabSub U) ^ 7 = 1 := Subtype.ext (by simpa using hτ)
    rw [this, map_one]
  have hz' : resHom U ⟨z, hzU⟩ * resHom U ⟨z, hzU⟩ = 1 := by
    rw [← map_mul]
    have : (⟨z, hzU⟩ : stabSub U) * ⟨z, hzU⟩ = 1 := Subtype.ext (by simpa using hz)
    rw [this, map_one]
  have hinv' : resHom U ⟨z, hzU⟩ * resHom U ⟨τ, hτU⟩ * (resHom U ⟨z, hzU⟩)⁻¹ =
      (resHom U ⟨τ, hτU⟩)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul, ← map_inv]
    congr 1
    exact Subtype.ext (by simpa using hinv)
  refine s16c167_card_ge_of_seven_inverted (U := ↥U) (fun u => Subtype.ext (hsq u))
    (fun h => hU (Subgroup.card_eq_one.1 h)) hτ' (fun u hu => ?_) hz' hinv'
  exact Subtype.ext (hfix u u.2 (congrArg Subtype.val hu))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
