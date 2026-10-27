module

public import CFSG.Quasithin.Background.G64Realize
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin

variable {V : Type} [CommGroup V] [Finite V]

theorem binaryNaturalSU3_realization {H : Subgroup (MulAut V)} {k : ℕ}
    (h : BinaryNaturalSU3 H ⊤ ⊥ k) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = (2 ^ k) ^ 2 ∧
      ∃ (π : ↥(StatedSU 3 (2 ^ k) K) →* ↥H),
        Function.Surjective π ∧
        ∃ Φ : V ≃* Multiplicative (Fin 3 → K),
          ∀ (γ : ↥(StatedSU 3 (2 ^ k) K)) (v : V),
            Φ (((π γ : ↥H) : MulAut V) v) =
              natAct (StatedSU 3 (2 ^ k) K) γ (Φ v) := by
  obtain ⟨K, hK, hFin, hcard, hR⟩ := h
  obtain ⟨π, hπ⟩ := hR
  let D : FFModel := FFModel.nat (StatedSU 3 (2 ^ k) K)
  have hDker : D.ker = ⊥ := rfl
  obtain ⟨E, hE⟩ := CFSG.Quasithin.G64.RealizesVia.exists_secEquiv (D := D) hDker hπ
  refine ⟨K, hK, hFin, hcard, π, hπ.1, E.trans Subgroup.topEquiv, ?_⟩
  intro γ v
  have h1 := hE γ v
  change ((E (((π γ : ↥H) : MulAut V) v) : ↥D.sec) : D.Amb) =
    natAct (StatedSU 3 (2 ^ k) K) γ ((E v : ↥D.sec) : D.Amb)
  exact h1

end CFSG.Quasithin.Stroth
