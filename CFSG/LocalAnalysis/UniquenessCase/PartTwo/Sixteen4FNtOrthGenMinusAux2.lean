module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtOrthGenMinusAux1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LieType.BorelTits CFSG.Open
open scoped CFSG.Decide.Bounded

theorem w183MinusNormOneVec {m : ℕ} {K : Type} [Field K] (b c : K) :
    StatedQuadMinus (m + 2) K b c (Pi.single (Sum.inr (Sum.inr 0)) (1 : K)) = 1 := by
  simp [StatedQuadMinus, CFSG.MatrixModel.minusQuadCore, Pi.single_apply]

theorem w183MapStatedQuadMinus {K L : Type} [Field K] [Field L] (e : K ≃+* L)
    (n : ℕ) (b c : K) (v : Fin (n - 1) ⊕ (Fin (n - 1) ⊕ Fin 2) → K) :
    e (StatedQuadMinus n K b c v) =
      StatedQuadMinus n L (e b) (e c)
        (w183PiEquiv e (Fin (n - 1) ⊕ (Fin (n - 1) ⊕ Fin 2)) v) := by
  simp only [StatedQuadMinus, CFSG.MatrixModel.minusQuadCore, map_sum, map_add, map_mul,
    map_pow, map_ofNat, w183PiEquiv_apply]

theorem w183MapQuadMinusPolar {K L : Type} [Field K] [Field L] (e : K ≃+* L)
    (n : ℕ) (b c : K) (u v : Fin (n - 1) ⊕ (Fin (n - 1) ⊕ Fin 2) → K) :
    e (quadMinusPolar n K b c u v) =
      quadMinusPolar n L (e b) (e c)
        (w183PiEquiv e (Fin (n - 1) ⊕ (Fin (n - 1) ⊕ Fin 2)) u)
        (w183PiEquiv e (Fin (n - 1) ⊕ (Fin (n - 1) ⊕ Fin 2)) v) := by
  simp only [quadMinusPolar, map_sum, map_add, map_mul, map_ofNat, w183PiEquiv_apply]

theorem w183ConnMapRingEquiv {K L : Type} [Field K] [Field L] (e : K ≃+* L) {ι : Type}
    {Q : (ι → K) → K} {Q' : (ι → L) → L} {P : (ι → K) → (ι → K) → K}
    {P' : (ι → L) → (ι → L) → L}
    (hQ : ∀ v, e (Q v) = Q' (w183PiEquiv e ι v))
    (hP : ∀ v w, e (P v w) = P' (w183PiEquiv e ι v) (w183PiEquiv e ι w))
    (h : ∀ u v, Q' u = 1 → Q' v = 1 → u ≠ v →
      P' u v = 1 ∨ ∃ w, Q' w = 1 ∧ P' u w = 1 ∧ P' v w = 1) :
    ∀ u v, Q u = 1 → Q v = 1 → u ≠ v →
      P u v = 1 ∨ ∃ w, Q w = 1 ∧ P u w = 1 ∧ P v w = 1 := by
  intro u v hu hv huv
  let φ := w183PiEquiv e ι
  have h1 : Q' (φ u) = 1 := by rw [← hQ u, hu, map_one]
  have h2 : Q' (φ v) = 1 := by rw [← hQ v, hv, map_one]
  have hne : φ u ≠ φ v := fun hh => huv (φ.injective hh)
  rcases h (φ u) (φ v) h1 h2 hne with hp | ⟨w', hw'q, hw'u, hw'v⟩
  · left
    exact e.injective (by rw [hP u v, hp, map_one])
  · refine Or.inr ⟨φ.symm w', ?_, ?_, ?_⟩
    · exact e.injective (by rw [hQ, φ.apply_symm_apply, hw'q, map_one])
    · exact e.injective (by rw [hP, φ.apply_symm_apply, hw'u, map_one])
    · exact e.injective (by rw [hP, φ.apply_symm_apply, hw'v, map_one])

theorem w183MinusConnFourZMod :
    ∀ u ∈ (Finset.univ : Finset (Fin 1 ⊕ (Fin 1 ⊕ Fin 2) → ZMod 2)),
      ∀ v ∈ (Finset.univ : Finset (Fin 1 ⊕ (Fin 1 ⊕ Fin 2) → ZMod 2)),
      StatedQuadMinus 2 (ZMod 2) 1 1 u = 1 → StatedQuadMinus 2 (ZMod 2) 1 1 v = 1 →
      u ≠ v → quadMinusPolar 2 (ZMod 2) 1 1 u v = 1 ∨
        ∃ w ∈ (Finset.univ : Finset (Fin 1 ⊕ (Fin 1 ⊕ Fin 2) → ZMod 2)),
          StatedQuadMinus 2 (ZMod 2) 1 1 w = 1 ∧
            quadMinusPolar 2 (ZMod 2) 1 1 u w = 1 ∧
            quadMinusPolar 2 (ZMod 2) 1 1 v w = 1 := by
  decide +kernel

theorem w183MinusConnFourZMod' :
    ∀ u v : Fin 1 ⊕ (Fin 1 ⊕ Fin 2) → ZMod 2,
      StatedQuadMinus 2 (ZMod 2) 1 1 u = 1 → StatedQuadMinus 2 (ZMod 2) 1 1 v = 1 →
      u ≠ v → quadMinusPolar 2 (ZMod 2) 1 1 u v = 1 ∨
        ∃ w, StatedQuadMinus 2 (ZMod 2) 1 1 w = 1 ∧
          quadMinusPolar 2 (ZMod 2) 1 1 u w = 1 ∧
          quadMinusPolar 2 (ZMod 2) 1 1 v w = 1 := by
  intro u v hu hv huv
  rcases w183MinusConnFourZMod u (Finset.mem_univ u) v (Finset.mem_univ v) hu hv huv with
    h | ⟨w, -, hw⟩
  · exact Or.inl h
  · exact Or.inr ⟨w, hw⟩

theorem w183MinusConnFour {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    ∀ u v : Fin 1 ⊕ (Fin 1 ⊕ Fin 2) → K,
      StatedQuadMinus 2 K 1 1 u = 1 → StatedQuadMinus 2 K 1 1 v = 1 →
      u ≠ v → quadMinusPolar 2 K 1 1 u v = 1 ∨
        ∃ w, StatedQuadMinus 2 K 1 1 w = 1 ∧
          quadMinusPolar 2 K 1 1 u w = 1 ∧
          quadMinusPolar 2 K 1 1 v w = 1 := by
  let e := CFSG.Quasithin.G64.ringEquivZModTwo K hK
  exact w183ConnMapRingEquiv e
    (fun v => by simpa using w183MapStatedQuadMinus e 2 (1 : K) (1 : K) v)
    (fun u v => by simpa using w183MapQuadMinusPolar e 2 (1 : K) (1 : K) u v)
    w183MinusConnFourZMod'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
