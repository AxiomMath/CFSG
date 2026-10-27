module

public import CFSG.LieType.Chevalley.E6GraphLeviIntersections
public import CFSG.RankThree.PartOne.KE6.Phi6Decomp

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.RankThree.Classical2
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {Ω : Type} [Field Ω]

theorem epsilon_data {ε : ℕ} (hε : ε < 2) :
    ∃ πε : Equiv.Perm (Fin Tag.E6.rank),
      (∀ i j, Tag.E6.cartan (πε i) (πε j) = Tag.E6.cartan i j) ∧
      (∀ c : Fin Tag.E6.rank → Ωˣ, (diagQ Ω) ^ ε * rootDiagUnit Tag.E6 c * ((diagQ Ω) ^ ε)⁻¹ =
        rootDiagUnit Tag.E6 (fun i => c (πε.symm i))) ∧
      (∀ g ∈ adjointGroup Tag.E6 Ω, (diagQ Ω) ^ ε * g * ((diagQ Ω) ^ ε)⁻¹ ∈
        adjointGroup Tag.E6 Ω) ∧
      (∀ (w : WeylGroup Tag.E6) {t₀ : ModGL Tag.E6 Ω}, t₀ ∈ torusGroup Tag.E6 Ω →
        ∀ β : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 β → ∃ μ : Ωˣ, ∀ c : Ω,
          (t₀ * canonicalRep (coxeterSystem Tag.E6) Ω w * (diagQ Ω) ^ ε) *
            pinnedX Tag.E6 Ω β c *
            (t₀ * canonicalRep (coxeterSystem Tag.E6) Ω w * (diagQ Ω) ^ ε)⁻¹ =
              pinnedX Tag.E6 Ω (w • permLattice πε β) ((μ : Ω) * c)) ∧
      (ε = 0 → πε = 1) ∧ (ε = 1 → πε = e6Rho) := by
  have : ε = 0 ∨ ε = 1 := by omega
  rcases this with rfl | rfl
  · refine ⟨1, fun i j => rfl, fun c => ?_, fun g hg => ?_, fun w t₀ ht₀ β hβ => ?_,
      fun _ => rfl, fun h => absurd h (by decide)⟩
    · simp only [pow_zero, inv_one, one_mul, mul_one]
      rfl
    · simpa using hg
    · simpa using rootAction_one hβ w ht₀
  · refine ⟨e6Rho, TwistTag.E6.cartan_perm, fun c => ?_, fun g hg => ?_, fun w t₀ ht₀ β hβ => ?_,
      fun h => absurd h (by decide), fun _ => rfl⟩
    · rw [pow_one]
      exact diagQ_conj_rootDiagUnit c
    · rw [pow_one]
      exact CFSG.LieType.Chevalley.E6GraphLevi.diagramMap_conj_mem_adjointGroup' hg
    · rw [pow_one]
      exact rootAction_Q hβ w ht₀

theorem entrywise_iterateFrobenius_zero {ℓ : ℕ} [Fact ℓ.Prime] [CharP Ω ℓ]
    (g : ModGL Tag.E6 Ω) :
    Units.map (entrywiseHom (iterateFrobenius Ω ℓ 0)) g = g := by
  have : iterateFrobenius Ω ℓ 0 = RingHom.id Ω :=
    RingHom.ext fun c => by rw [iterateFrobenius_def]; simp
  rw [this]
  exact Units.ext (entrywise_id _)

theorem units_map_iterateFrobenius_zero {ℓ : ℕ} [Fact ℓ.Prime] [CharP Ω ℓ] (u : Ωˣ) :
    Units.map (iterateFrobenius Ω ℓ 0).toMonoidHom u = u := by
  apply Units.ext
  change iterateFrobenius Ω ℓ 0 (u : Ω) = u
  rw [iterateFrobenius_def]
  simp

end CFSG.RankThree.PartOne.KE6
