module

public import CFSG.RankThree.PartOne.SEITZ2.SU3Rat

public section

namespace CFSG.RankThree.PartOne.SEITZ2

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary

section PhiN

variable {K : Type} [Field K] {k : Subfield K} {σ : K ≃+* K} {σ₀ : k ≃+* k} {n : ℕ}

@[expose] noncomputable def phiN (hσk : ∀ c : k, σ (c : K) = ((σ₀ c : k) : K)) :
    SUid σ₀ n →* SUid σ n where
  toFun g := ⟨Units.map (RingHom.mapMatrix k.subtype).toMonoidHom g.1, by
    obtain ⟨hdet, hu⟩ := g.2
    refine ⟨?_, ?_⟩
    · change (k.subtype.mapMatrix (g.1 : Matrix (Fin n) (Fin n) k)).det = 1
      rw [← RingHom.map_det, hdet, map_one]
    · change conjTr σ ((g.1 : Matrix (Fin n) (Fin n) k).map k.subtype) *
        ((g.1 : Matrix (Fin n) (Fin n) k).map k.subtype) = 1
      rw [conjTr_map_subtype hσk, ← Matrix.map_mul, hu, Matrix.map_one _ (map_zero _) (map_one _)]⟩
  map_one' := Subtype.ext (by simp)
  map_mul' g g' := Subtype.ext (by simp)

theorem coe_phiN (hσk : ∀ c : k, σ (c : K) = ((σ₀ c : k) : K)) (g : SUid σ₀ n) :
    (((phiN hσk g : SUid σ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).map k.subtype := rfl

theorem phiN_smul (hσk : ∀ c : k, σ (c : K) = ((σ₀ c : k) : K)) (g : SUid σ₀ n)
    (v : Fin n → k) : phiN hσk g • incl v = incl (g • v) := by
  rw [smul_def, smul_def, coe_phiN]
  funext i
  simp [incl, Matrix.mulVec, dotProduct]

theorem isTv_phiN (hσk : ∀ c : k, σ (c : K) = ((σ₀ c : k) : K)) {t : SUid σ₀ n} {a : Fin n → k}
    {c : k} (h : IsTv σ₀ t a c) : IsTv σ (phiN hσk t) (incl a) (c : K) := by
  have hincl : ∀ j : Fin n, incl (Pi.single j (1 : k)) = (Pi.single j (1 : K) : Fin n → K) := by
    intro j
    funext i
    by_cases hij : i = j
    · subst hij
      simp [incl]
    · simp [incl, hij]
  have hM : ((phiN hσk t : SUid σ n) : GL (Fin n) K).val = tvMat σ (incl a) (c : K) := by
    apply Matrix.ext_of_mulVec_single
    intro j
    have h1 : phiN hσk t • incl (Pi.single j (1 : k)) =
        incl (Pi.single j (1 : k)) + ((c : K) * herm σ (incl a) (incl (Pi.single j (1 : k)))) •
          incl a := by
      rw [phiN_smul hσk, h]
      funext i
      simp [incl, herm_incl hσk]
    rw [hincl j] at h1
    rw [tvMat_mulVec]
    exact h1
  intro w
  rw [smul_def, hM, tvMat_mulVec]


end PhiN

end CFSG.RankThree.PartOne.SEITZ2
