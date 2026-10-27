module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K332Wreath

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route.Wreath

open CFSG.RankThree.PartTwo.Sec4.RonanK432

variable {C S : Type} [CommGroup C] [Group S]

theorem hasTwist_of_pair {φ : (Fin 3 → C) →* S} {μ : ℤ}
    (htw : ∀ i j : Fin 3, i ≠ j → ∃ g : S, ∀ c,
      g * φ c * g⁻¹ = φ (Function.update (Function.update c i (c i ^ μ)) j (c j ^ μ)))
    {i j : Fin 3} (hij : i ≠ j) : HasTwist φ μ i j := by
  have hk : ∀ i j : Fin 3, i ≠ j → ∃ k : Fin 3, k ≠ i ∧ k ≠ j := by decide
  obtain ⟨k, hki, hkj⟩ := hk i j hij
  obtain ⟨g, hg⟩ := htw i k hki.symm
  refine ⟨g, fun c => Function.update (Function.update c i (c i ^ μ)) k (c k ^ μ), hg,
    fun c => ⟨?_, ?_⟩⟩
  · simp only [Function.update_of_ne hki.symm, Function.update_self]
  · simp only [Function.update_of_ne hkj.symm, Function.update_of_ne hij.symm]

theorem listRow_of_wreath_pair [Finite C] [Finite S] {a : ℕ} (ha : 1 ≤ a)
    (hC : Nat.card C = 3 ^ a) {φ : (Fin 3 → C) →* S} (hφ : Function.Injective φ) {μ : ℤ}
    (hμ : ¬ (3 : ℤ) ∣ μ - 1)
    (htw : ∀ i j : Fin 3, i ≠ j → ∃ g : S, ∀ c,
      g * φ c * g⁻¹ = φ (Function.update (Function.update c i (c i ^ μ)) j (c j ^ μ)))
    {s : S} (hs3 : s ^ 3 = 1) (hs : ∀ x : Fin 3 → C, s * φ x * s⁻¹ = φ (sh x))
    (hS : ¬ 3 ^ (3 * a + 2) ∣ Nat.card S) : ListRow S :=
  listRow_of_wreath_twists ha hC hφ hμ (fun _ _ hij => hasTwist_of_pair htw hij) hs3 hs hS

end CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route.Wreath
