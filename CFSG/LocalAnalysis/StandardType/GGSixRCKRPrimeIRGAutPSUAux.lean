module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2OverlapValField
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGDefs
public import CFSG.LieType.Universal.Catalog
public import CFSG.LieType.BorelTits.UnitaryForm
public import CFSG.LieType.Universal.Unitary.Basic
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryDiagonalOuterOrder

public section

namespace CFSG.StandardType.RCKRP

open CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

abbrev irgU_F (g : ℕ) : Type := GaloisField 2 (2 * g)

noncomputable abbrev irgU_sigma (g : ℕ) : irgU_F g ≃+* irgU_F g :=
  CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * g)) 2 g

theorem irgU_one_le_g {n g : ℕ} (hadm : CFSG.Open.StatedLieAdmissible .PSU n 2 g) :
    1 ≤ g := hadm.2.1

theorem irgU_ringEquiv_commute_unitaryInvolution {F : Type} [Field F] [Finite F]
    (p f : ℕ) [Fact p.Prime] [CharP F p] (φ : F ≃+* F) (c : F) :
    φ (CFSG.LieType.BorelTits.unitaryInvolution F p f c) =
      CFSG.LieType.BorelTits.unitaryInvolution F p f (φ c) := by
  simp [CFSG.LieType.BorelTits.unitaryInvolution_apply, iterateFrobenius_def, map_pow]

theorem irgU_map_longRootMatrix {F : Type} [Field F] {n : ℕ} (φ : F ≃+* F) (i : Fin n) (c : F) :
    (longRootMatrix i c).map φ = longRootMatrix i (φ c) := by
  simp [longRootMatrix, Matrix.map_add, Matrix.map_one]

theorem irgU_traceZero_preserved {F : Type} [Field F] (σ : F ≃+* F) (φ : F ≃+* F)
    (hφ : ∀ c, φ (σ c) = σ (φ c)) {c : F} (hc : c ∈ traceZero σ) : φ c ∈ traceZero σ := by
  rw [mem_traceZero] at hc ⊢
  rw [← hφ c, ← map_add, hc, map_zero]

theorem irgU_sigma_involutive (g : ℕ) (hK : Nat.card (irgU_F g) = (2 ^ g) ^ 2) :
    ∀ c, irgU_sigma g (irgU_sigma g c) = c :=
  CFSG.LieType.BorelTits.unitaryInvolution_involutive (p := 2) (f := g) hK

lemma irgU_exists_coord {n : ℕ} (hn : 3 ≤ n) {i : Fin n} (hi : i ≠ Fin.rev i) :
    ∃ k : Fin n, k ≠ i ∧ k ≠ Fin.rev i := by
  by_contra h
  push Not at h
  have huniv : ({i, Fin.rev i} : Finset (Fin n)) = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro j
    by_cases hj : j = i
    · simp [hj]
    · have hji : j = Fin.rev i := h j hj
      simp [hji]
  have hcard := Finset.card_univ (α := Fin n)
  rw [← huniv] at hcard
  have h2 : ({i, Fin.rev i} : Finset (Fin n)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using hi), Finset.card_singleton]
  rw [h2, Fintype.card_fin] at hcard
  omega

end CFSG.StandardType.RCKRP

end
