module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.Quasithin.Background.E3Defs

public section

namespace CFSG.Quasithin.H13.GM22

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G}

omit [Finite G] in
theorem relIndex_eq_two_of_lt {A B C : Subgroup G} (hAB : A ≤ B) (hBC : B ≤ C)
    (h2 : A.relIndex C = 2) (hne : ¬ C ≤ B) : B.relIndex C = 2 := by
  have h1 := Subgroup.relIndex_mul_relIndex A B C hAB hBC
  have hdvd : B.relIndex C ∣ 2 := h2 ▸ Dvd.intro_left _ h1
  have hne1 : B.relIndex C ≠ 1 := fun h => hne (Subgroup.relIndex_eq_one.mp h)
  exact ((Nat.dvd_prime Nat.prime_two).1 hdvd).resolve_left hne1

omit [Finite G] in
theorem commute_conj_iff {P : Type*} [Group P] (σ u v : P) :
    Commute (σ * u * σ⁻¹) (σ * v * σ⁻¹) ↔ Commute u v := by
  constructor
  · intro h
    have := h.map (MulAut.conj σ⁻¹)
    simpa [MulAut.conj_apply, mul_assoc] using this
  · intro h
    simpa [MulAut.conj_apply] using h.map (MulAut.conj σ)

theorem oTwoUpper_conjSubgroup (A : Subgroup G) (g : G) :
    oTwoUpper (conjSubgroup A g) = conjSubgroup (oTwoUpper A) g :=
  oTwoUpper_map (MulAut.conj g⁻¹).toMonoidHom A

end CFSG.Quasithin.H13.GM22
