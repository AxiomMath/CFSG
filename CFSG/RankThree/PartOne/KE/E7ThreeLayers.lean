module

public import CFSG.RankThree.PartOne.KE.A2Family
public import CFSG.RankThree.PartOne.KE.E7ThreeLatticeInputs

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice
open scoped Matrix MatrixGroups

@[expose] def E7Layer {L : Type} [Field L] (n : ModGL Tag.E7 L) (Fr : L →+* L)
    (S : Set (Fin Tag.E7.rank → ℤ)) (k : Type) [Field k] [Algebra k L] : Prop :=
  ∃ (ι' : Type) (P : ι' → Subgroup (ModGL Tag.E7 L)), IsSigmaFamily n Fr S P ∧
    ((Pi.single (⟨0, by decide⟩ : Fin Tag.E7.rank) 1 : Fin Tag.E7.rank → ℤ) ∈ S →
      ∃ (i₀ : ι') (m : Fin Tag.E7.rank) (h₀ : ModGL Tag.E7 L), ∀ Y : SL(2, k),
        h₀ * simpleRootSL2 Tag.E7 L m (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) * h₀⁻¹ ∈
          P i₀)

@[expose] def E7ThreeLayers : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] (ℓ f : ℕ) [Fact ℓ.Prime] [CharP L ℓ], 1 ≤ f →
    ∀ (k : Type) [Field k] [Algebra k L] [IsAlgClosure k L], Nat.card k = ℓ ^ f →
    ∀ ε : ℤ, (ε = 1 ∨ ε = -1) → (ε = -1 → 2 < ℓ ^ f) →
    ∀ (n : ModGL Tag.E7 L) (hnm : n ∈ monomialSubgroup Tag.E7 L), n ∈ adjointGroup Tag.E7 L →
      (∀ u : Fin Tag.E7.rank → ℤ, weylQuotientHom Tag.E7 L ⟨n, hnm⟩ • u = (ε • e7T3W) *ᵥ u) →
      ∀ c ∈ e7T3Certs, c.Good →
        E7Layer n (iterateFrobenius L ℓ f) {α | ∃ l ∈ c.rootList, α = toVec Tag.E7.rank l} k

variable {L : Type} [Field L]

theorem e7Layer_empty (n : ModGL Tag.E7 L) (Fr : L →+* L) (k : Type) [Field k] [Algebra k L] :
    E7Layer n Fr ∅ k := by
  classical
  have hspan : rootSpan Tag.E7 L (∅ : Set (Fin Tag.E7.rank → ℤ)) = ⊥ := by simp [rootSpan]
  refine ⟨Empty, fun e => e.elim, ⟨fun e => e.elim, fun e => e.elim, fun e => e.elim,
    fun e => e.elim, fun e => e.elim, fun e => e.elim, fun y hy hyR _ => ?_⟩, fun h => ?_⟩
  · rw [hspan, sup_bot_eq] at hy
    refine Subgroup.mem_inf.2 ⟨mem_twistedTorusOf.2 ⟨hy, hyR⟩, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [hspan] at hg
    have : g = 1 := hg
    rw [this, one_mul, mul_one]
  · exact absurd h (by simp)

end CFSG.RankThree.PartOne.KE
