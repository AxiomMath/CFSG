module

public import CFSG.Quasithin.Background.F918Z5B1

public section

namespace CFSG.Quasithin

theorem omega4Plus_of_sqModel_two {V : Type} [CommGroup V] [Finite V]
    {D X : Subgroup (MulAut V)} (hcomm : ∀ g ∈ D, ∀ x ∈ X, g * x = x * g)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (β : V ≃* Multiplicative (Matrix (Fin 2) (Fin 2) F))
    (ρ : ↥D →* Matrix.GeneralLinearGroup (Fin 2) F)
    (σ : ↥X →* Matrix.GeneralLinearGroup (Fin 2) F)
    (hM : IsMatModel D X β ρ σ) (hperfD : Group.IsPerfect ↥D) (hperfX : Group.IsPerfect ↥X)
    {n₀ : ℕ} (hD : IsPSL 2 2 n₀ ↥D) (hXD : Nonempty (↥D ≃* ↥X)) :
    ∃ n, IsPSL 2 2 n ↥D ∧ Omega4PlusModule (D ⊔ X) n := by
  obtain ⟨hcard, hρ, hσ⟩ := SqModel.matModel_two_equiv hM hperfD hperfX hD hXD
  exact ⟨n₀, hD, omega4PlusModule_of_matModel hcard hcomm hM hρ hσ⟩

end CFSG.Quasithin
