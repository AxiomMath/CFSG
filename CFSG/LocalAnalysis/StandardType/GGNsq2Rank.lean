module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut

public section

namespace CFSG.StandardType

theorem card_linearEquiv_zmod_three {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    [FiniteDimensional (ZMod 3) V] {n : ℕ} (hn : Module.finrank (ZMod 3) V = n) :
    Nat.card (V ≃ₗ[ZMod 3] V) = ∏ i : Fin n, (3 ^ n - 3 ^ (i : ℕ)) := by
  classical
  let b : Module.Basis (Fin n) (ZMod 3) V := Module.finBasisOfFinrankEq (ZMod 3) V hn
  let e : Matrix.GeneralLinearGroup (Fin n) (ZMod 3) ≃* (V ≃ₗ[ZMod 3] V) :=
    (Matrix.GeneralLinearGroup.toLin' b).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 3) V)
  rw [← Nat.card_congr e.toEquiv, Matrix.card_GL_field, ZMod.card]

theorem not_seven_dvd_prod_of_le_five {n : ℕ} (hn : n ≤ 5) :
    ¬ 7 ∣ ∏ i : Fin n, (3 ^ n - 3 ^ (i : ℕ)) := by
  interval_cases n <;> first | decide | (simp [Fin.prod_univ_succ]; omega)

theorem three_pow_six_le_card_of_seven_dvd {G : Type} [Group G] [Finite G] {Bs : Subgroup G}
    (hBs : CFSG.Open.IsElemAbelian 3 Bs) {A : Subgroup (MulAut ↥Bs)} (h7 : 7 ∣ Nat.card A) :
    3 ^ 6 ≤ Nat.card Bs := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨V, _, _, ⟨ι⟩⟩ := exists_ggLinData (p := 3) hBs
  haveI : Finite V := Finite.of_equiv ↥Bs (Additive.ofMul.trans ι.toEquiv)
  haveI : Module.Finite (ZMod 3) V := inferInstance
  have hdvd : Nat.card A ∣ Nat.card (V ≃ₗ[ZMod 3] V) := by
    refine Subgroup.card_dvd_of_injective ((ggLin (p := 3) ι).comp A.subtype) ?_
    exact (ggLin_injective (p := 3) ι).comp A.subtype_injective
  have h7' : 7 ∣ ∏ i : Fin (Module.finrank (ZMod 3) V),
      (3 ^ Module.finrank (ZMod 3) V - 3 ^ (i : ℕ)) := by
    rw [← card_linearEquiv_zmod_three (V := V) rfl]
    exact h7.trans hdvd
  have hd : 6 ≤ Module.finrank (ZMod 3) V := by
    by_contra hlt
    exact not_seven_dvd_prod_of_le_five (by omega) h7'
  have hcard : Nat.card Bs = 3 ^ Module.finrank (ZMod 3) V := by
    rw [card_eq_of_ggLin ι, Module.natCard_eq_pow_finrank (K := ZMod 3), Nat.card_zmod]
  rw [hcard]
  exact Nat.pow_le_pow_right (by norm_num) hd

end CFSG.StandardType

end
