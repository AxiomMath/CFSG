module

public import CFSG.Quasithin.Background.F918Z5ATensor
import CFSG.Open.StatedZModTwo
import CFSG.Adapters.StatedClassicalSmallOrders

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank
open scoped Matrix

section Orders

theorem subsingleton_units_of_card_two {F : Type} [Field F] (hF : Nat.card F = 2) :
    Subsingleton Fˣ := by
  have h : Nat.card Fˣ = 1 := by rw [Nat.card_units, hF]
  exact (Nat.card_eq_one_iff_unique.mp h).1

theorem statedSL_eq_top_of_card_two {F : Type} [Field F] (hF : Nat.card F = 2) (n : ℕ) :
    StatedSL n F = ⊤ :=
  CFSG.Open.StatedAPI.statedSL_eq_top_of_card_two hF n

theorem card_gl_three_of_card_two {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2) :
    Nat.card (Matrix.GeneralLinearGroup (Fin 3) F) = 168 := by
  have : Fintype F := Fintype.ofFinite F
  have hq : Fintype.card F = 2 := by rw [← Nat.card_eq_fintype_card]; exact hF
  rw [Matrix.card_GL_field, hq]
  simp [Fin.prod_univ_three]

theorem card_eq_of_isPSL_three_two {G : Type} [Group G] (h : IsPSL 3 2 1 G) :
    Nat.card G = 168 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_two h

end Orders

theorem tensorNatL32_of_sqModel_three {V : Type} [CommGroup V] [Finite V]
    {D X : Subgroup (MulAut V)} (hcomm : ∀ g ∈ D, ∀ x ∈ X, g * x = x * g)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2)
    (β : V ≃* Multiplicative (Matrix (Fin 3) (Fin 3) F))
    (ρ : ↥D →* Matrix.GeneralLinearGroup (Fin 3) F)
    (σ : ↥X →* Matrix.GeneralLinearGroup (Fin 3) F)
    (hM : IsMatModel D X β ρ σ) (hD : IsPSL 3 2 1 ↥D) (hX : IsPSL 3 2 1 ↥X) :
    TensorNatL32 (D ⊔ X) := by
  have hGL := card_gl_three_of_card_two hF
  have hρb : Function.Bijective ρ :=
    hM.rho_injective.bijective_of_nat_card_le (by rw [hGL, card_eq_of_isPSL_three_two hD])
  have hσb : Function.Bijective σ :=
    hM.sigma_injective.bijective_of_nat_card_le (by rw [hGL, card_eq_of_isPSL_three_two hX])
  have hSL := statedSL_eq_top_of_card_two hF 3
  exact tensorNatL32_of_matModel_of_card_two hF hcomm hM
    (by rw [hSL]; exact MonoidHom.range_eq_top.mpr hρb.2)
    (by rw [hSL]; exact MonoidHom.range_eq_top.mpr hσb.2)

end CFSG.Quasithin
