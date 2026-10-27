module

public import CFSG.Quasithin.EmptyFaithful.S151S8C1
public import CFSG.Quasithin.EmptyFaithful.S151S9TCoreP
public import CFSG.Quasithin.EmptyFaithful.S151S9TCoreS

public section

namespace CFSG.Quasithin.S151S9T

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
open scoped commutatorElement

theorem idx3_core {G : Type} [Group G] [Finite G] {L S P : Subgroup G}
    (hS2 : IsPGroup 2 ↥S)
    (hPL : P ≤ L) (hBP : S ⊓ L ≤ P) (hSP : S ≤ Subgroup.normalizer (P : Set G))
    (hcard : Nat.card ↥P = 3 * Nat.card ↥(S ⊓ L))
    (hnN : ¬ P ≤ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G))
    {x₀ : G} (hx₀ : x₀ ∈ P) (hx₀3 : orderOf x₀ = 3)
    {r : Fin 5 → G} (hr0 : ∀ i, r i ∈ S ⊓ L) (hr1 : ∀ i, x₀⁻¹ * r i * x₀ ∈ S ⊓ L)
    (hr2 : ∀ i, x₀ * r i * x₀⁻¹ ∈ S ⊓ L)
    (hinj : Function.Injective fun i => ⁅⁅r i, x₀⁆, x₀⁆) :
    CharTwo P ∧ IsMinParabolicOf (P ⊔ S) (P ⊔ S) ∧ NumC126 (P ⊔ S) ∧
      oPrimeResidualOf 3 P ⊔ (S ⊓ L) = P := by
  have hB2 : IsPGroup 2 ↥(S ⊓ L) := hS2.to_le inf_le_left
  obtain ⟨hchar, h3, hnum, hsup⟩ := idx3_P hB2 hBP hcard hnN hx₀ hx₀3 hr0 hr1 hr2 hinj
  obtain ⟨a, ha⟩ := hB2.exists_card_eq
  have hP : ∀ x ∈ P, ∃ i j : ℕ, orderOf x = 2 ^ i * 3 ^ j :=
    CoreS.exists_orderOf_eq_two_pow_mul_three_pow (a := a) (by rw [hcard, ha])
  have hres : twoResidual (P ⊔ S) = oPrimeResidualOf 3 P := twoResidual_sup_eq hS2 hSP hP
  have hSinf : S ⊓ P = S ⊓ L := le_antisymm (inf_le_inf_left S hPL) (le_inf inf_le_left hBP)
  have hnS : ¬ P ≤ Subgroup.normalizer (S : Set G) := fun h =>
    hnN fun x hx =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨h hx, Subgroup.le_normalizer (hPL hx)⟩
  refine ⟨hchar, isMinParabolic_sup hS2 hSP (hSinf ▸ hcard) hnS, ?_, hsup⟩
  unfold NumC126
  rw [hres]
  exact ⟨fun x hx => ⟨1, by simpa using h3 x hx⟩, hnum⟩

end CFSG.Quasithin.S151S9T
