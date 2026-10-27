module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bSU4

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.ClassicalGroups.UnitaryFlag CFSG.Open CFSG.LocalAnalysis.ComponentInitial
open scoped Matrix

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

variable (h : UnitaryFieldData p f K) in
noncomputable def moduleMulEquiv {R : Matrix (Fin (2 * r + ε)) (HypIndex r ε) K}
    (hR : IsHypTransport h R) :
    CFSG.Quasithin.H.StdMod (HypIndex r ε) K ≃*
      CFSG.Quasithin.H.StdMod (Fin (2 * r + ε)) K :=
  (transportEquiv h hR).toAddEquiv.toMultiplicative

theorem transportEquiv_smul {h : UnitaryFieldData p f K}
    {R : Matrix (Fin (2 * r + ε)) (HypIndex r ε) K} (hR : IsHypTransport h R)
    (g : hypSU h r ε) (v : HypIndex r ε → K) :
    transportEquiv h hR (g • v) =
      (hypTransport h hR g : unitarySU p f K (2 * r + ε)) • (transportEquiv h hR v) := by
  simp only [transportEquiv, LinearEquiv.coe_ofLinearMap, Matrix.mulVecLin_apply,
    Subgroup.smul_def, Units.smul_def, Matrix.smul_eq_mulVec, coe_hypTransport,
    Matrix.mulVec_mulVec, Matrix.mul_assoc, transportInv_mul hR, Matrix.mul_one]

theorem moduleMulEquiv_smul {h : UnitaryFieldData p f K}
    {R : Matrix (Fin (2 * r + ε)) (HypIndex r ε) K} (hR : IsHypTransport h R)
    (g : hypSU h r ε) (v : HypIndex r ε → K) :
    moduleMulEquiv h hR (Multiplicative.ofAdd (g • v)) =
      CFSG.Quasithin.H.matHom (ι := Fin (2 * r + ε)) (K := K)
        ((hypTransport h hR g : unitarySU p f K (2 * r + ε)) : GL (Fin (2 * r + ε)) K)
        (moduleMulEquiv h hR (Multiplicative.ofAdd v)) := by
  rw [show moduleMulEquiv h hR (Multiplicative.ofAdd (g • v)) =
      Multiplicative.ofAdd (transportEquiv h hR (g • v)) from rfl,
    show moduleMulEquiv h hR (Multiplicative.ofAdd v) =
      Multiplicative.ofAdd (transportEquiv h hR v) from rfl,
    transportEquiv_smul hR g v]
  rfl

theorem congrHom_symm_matHom_hypTransport {h : UnitaryFieldData p f K}
    {R : Matrix (Fin (2 * r + ε)) (HypIndex r ε) K} (hR : IsHypTransport h R)
    (g : hypSU h r ε) :
    CFSG.Quasithin.H.congrHom (moduleMulEquiv h hR).symm
        (CFSG.Quasithin.H.matHom (ι := Fin (2 * r + ε)) (K := K)
          ((hypTransport h hR g : unitarySU p f K (2 * r + ε)) :
            GL (Fin (2 * r + ε)) K)) =
      CFSG.Quasithin.H.matHom (ι := HypIndex r ε) (K := K)
        ((g : hypSU h r ε) : GL (HypIndex r ε) K) := by
  ext v
  rw [CFSG.Quasithin.H.congrHom_apply, MulEquiv.symm_symm]
  have hv : moduleMulEquiv h hR v =
      moduleMulEquiv h hR (Multiplicative.ofAdd (Multiplicative.toAdd v)) := by
    rw [ofAdd_toAdd]
  rw [hv, ← moduleMulEquiv_smul hR g (Multiplicative.toAdd v),
    MulEquiv.symm_apply_apply]
  rfl

theorem map_matHom_eq_natImage_map_congrHom_symm {h : UnitaryFieldData p f K}
    {R : Matrix (Fin (2 * r + ε)) (HypIndex r ε) K} (hR : IsHypTransport h R) :
    (hypSU h r ε).map CFSG.Quasithin.H.matHom =
      (CFSG.Quasithin.H.natImage (unitarySU p f K (2 * r + ε))).map
        (CFSG.Quasithin.H.congrHom (moduleMulEquiv h hR).symm) := by
  rw [CFSG.Quasithin.H.natImage_eq_map, Subgroup.map_map]
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨(hypTransport h hR ⟨g, hg⟩ : unitarySU p f K (2 * r + ε)),
      (hypTransport h hR ⟨g, hg⟩).2, ?_⟩
    exact congrHom_symm_matHom_hypTransport hR ⟨g, hg⟩
  · rintro ⟨γ, hγ, rfl⟩
    obtain ⟨g, hg⟩ := (hypTransport h hR).surjective ⟨γ, hγ⟩
    refine ⟨g, g.2, ?_⟩
    have hcoe : ((hypTransport h hR g : unitarySU p f K (2 * r + ε)) :
        GL (Fin (2 * r + ε)) K) = γ :=
      congrArg Subtype.val hg
    rw [← hcoe]
    exact (congrHom_symm_matHom_hypTransport hR g).symm

theorem su4NaturalLine_of_hyp
    (hHyp : ∀ (K : Type) [Field K] [Finite K] (a : ℕ) (h : UnitaryFieldData 2 a K),
      Nat.card K = (2 ^ a) ^ 2 →
      SU4Line (CFSG.Quasithin.H.StdMod (HypIndex 2 0) K)
        ((hypSU h 2 0).map CFSG.Quasithin.H.matHom) (2 * a)) :
    SU4NaturalLine := by
  intro K hKfield hKfinite a hK
  let h : UnitaryFieldData 2 a K :=
    { prime := Nat.prime_two
      one_le := by
        rcases Nat.eq_zero_or_pos a with rfl | ha
        · exfalso
          haveI : Fintype K := Fintype.ofFinite K
          have h2 : 1 < Fintype.card K := Fintype.one_lt_card
          rw [← Nat.card_eq_fintype_card, hK] at h2
          simpa using h2
        · exact ha
      card := by rw [hK, ← pow_mul, Nat.mul_comm a 2] }
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := 2) (ε := 0) h
  have hmap : (hypSU h 2 0).map CFSG.Quasithin.H.matHom =
      (CFSG.Quasithin.H.natImage (StatedSU 4 (2 ^ a) K)).map
        (CFSG.Quasithin.H.congrHom (moduleMulEquiv h hR).symm) :=
    map_matHom_eq_natImage_map_congrHom_symm hR
  exact su4Line_of_map_congr _ _ (2 * a) (moduleMulEquiv h hR).symm hmap
    (hHyp K a h hK)

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
