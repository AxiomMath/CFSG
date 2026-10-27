module

import CFSG.LinearAlgebra.IrreducibleBinaryCentralizerField
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeSecHom
public import CFSG.Quasithin.Background.F918Z8Sz6Eb
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

section Aut

theorem exists_card_mulAut_pi {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) (d : ℕ) :
    ∃ u : ℕ, Odd u ∧
      Nat.card (MulAut (Multiplicative (Fin d → K))) = 2 ^ (d * (d - 1) / 2) * u := by
  have h01 : ∀ c : K, c = 0 ∨ c = 1 := by
    obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (0 : K)).mp hK
    intro c
    by_cases hc : c = 0
    · exact Or.inl hc
    · exact Or.inr ((hy c hc).trans (hy 1 one_ne_zero).symm)
  have hlin : ∀ (e : (Fin d → K) ≃+ (Fin d → K)) (c : K) (w : Fin d → K),
      e (c • w) = c • e w := by
    intro e c w
    rcases h01 c with rfl | rfl <;> simp
  let e₁ : MulAut (Multiplicative (Fin d → K)) ≃ ((Fin d → K) ≃ₗ[K] (Fin d → K)) :=
    { toFun := fun f => { (AddEquiv.toMultiplicative.symm f) with map_smul' := hlin _ }
      invFun := fun g => AddEquiv.toMultiplicative g.toAddEquiv
      left_inv := fun f => by ext; rfl
      right_inv := fun g => by ext; rfl }
  let e₂ : Matrix.GeneralLinearGroup (Fin d) K ≃* ((Fin d → K) ≃ₗ[K] (Fin d → K)) :=
    Matrix.GeneralLinearGroup.toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv K _)
  have := Fintype.ofFinite K
  have hq : Fintype.card K = 2 := by rw [Fintype.card_eq_nat_card]; exact hK
  have hcard : Nat.card (MulAut (Multiplicative (Fin d → K))) =
      ∏ i : Fin d, (2 ^ d - 2 ^ (i : ℕ)) := by
    rw [Nat.card_congr (e₁.trans e₂.symm.toEquiv), Matrix.card_GL_field, hq]
  obtain ⟨u, hu, hprod⟩ :=
    CFSG.LinearAlgebra.prod_pow_sub_pow_eq_two_pow_mul_odd (d := 1) one_pos d
  refine ⟨u, hu, ?_⟩
  rw [hcard]
  simpa using hprod

theorem exists_card_mulAut_of_mulEquiv {G : Type*} [Group G] {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) {d : ℕ} (e : G ≃* Multiplicative (Fin d → K)) :
    ∃ u : ℕ, Odd u ∧ Nat.card (MulAut G) = 2 ^ (d * (d - 1) / 2) * u := by
  obtain ⟨u, hu, h⟩ := exists_card_mulAut_pi hK d
  exact ⟨u, hu, by rw [Nat.card_congr (MulAut.congr e).toEquiv, h]⟩

end Aut

section

variable {Y : Type} [CommGroup Y] [Finite Y]

theorem sxi_rank_natural {X A : Subgroup (MulAut Y)} {I J : Subgroup Y} {d : ℕ}
    (hnat : BinaryNaturalSL (autSec X I J) ⊤ ⊥ d 1) (hAel : IsElemAbelian2 A)
    (hAI : A ≤ stabSub I) (hAJ : A ≤ stabSub J) :
    rk (Sec I J) = d ∧ rk (autSec A I J) ≤ d * (d - 1) / 2 := by
  obtain ⟨K, hKf, hKfin, hKcard, e, -⟩ := hnat.exists_natEquiv
  rw [pow_one] at hKcard
  have hcard : Nat.card (Sec I J) = 2 ^ d := by
    rw [Nat.card_congr e.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun, hKcard,
      Nat.card_fin]
  refine ⟨by rw [rk, hcard, padicValNat.prime_pow], ?_⟩
  obtain ⟨u, hu, hGL⟩ := exists_card_mulAut_of_mulEquiv hKcard e
  have hp : IsPGroup 2 (autSec A I J) :=
    (Bridge.isElemAbelian2_autSec hAel (le_inf hAI hAJ)).isPGroup
  have hdvd : 2 ^ rk (autSec A I J) ∣ 2 ^ (d * (d - 1) / 2) * u := by
    rw [← hGL, ← card_eq_two_pow_of_isPGroup hp]
    exact Subgroup.card_subgroup_dvd_card _
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp
    (((Nat.coprime_two_left.2 hu).pow_left _).dvd_of_dvd_mul_right hdvd)

end

end CFSG.Quasithin
