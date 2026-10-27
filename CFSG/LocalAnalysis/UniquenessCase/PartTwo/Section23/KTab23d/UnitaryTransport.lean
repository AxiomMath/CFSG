module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Defs
public import CFSG.ClassicalGroups.UnitaryFlag.ModelTransport
public import CFSG.Quasithin.H13.U4ParPoint
public import CFSG.Open.StatedDefs

import CFSG.ClassicalGroups.UnitaryFlag.WittBasis
import CFSG.LinearAlgebra.LinearGroups.UnitaryBasics
import CFSG.LinearAlgebra.LinearGroups.UnitaryFourOrder
public import CFSG.LieType.BorelTits.CompleteFlag

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD

open Matrix CFSG.Open CFSG.LinearGroups CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.Quasithin.H13.U4Par

theorem exists_isHypTransport_first {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    {r ε : ℕ} (hr : 0 < r) {a : Fin (2 * r + ε) → K} (ha0 : a ≠ 0)
    (ha : stdHermForm h (2 * r + ε) a a = 0) :
    ∃ R : Matrix (Fin (2 * r + ε)) (HypIndex r ε) K, IsHypTransport h R ∧
      R *ᵥ (Pi.single (Sum.inl ⟨0, hr⟩) 1 : HypIndex r ε → K) = a := by
  obtain ⟨b, hab, hb⟩ := (hermitian_hyperbolic_splitting h (stdHermForm_isSymm h (2 * r + ε))
    (stdHermForm_separatingLeft h (2 * r + ε)) ha0 ha).1
  obtain ⟨w, hw, hwa, -⟩ := exists_hypBasis_of_pair h (stdHermForm_isSymm h (2 * r + ε))
    (stdHermForm_separatingLeft h (2 * r + ε)) (Module.finrank_fin_fun K) hr ha hb hab
  refine ⟨Matrix.of fun k x => w x k, ?_, ?_⟩
  · ext x y
    rw [← hw x y, stdHermForm_apply, mul_apply]
    rfl
  · rw [mulVec_single_one]
    exact hwa

theorem exists_isHypTransport_four {a : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 a K) :
    ∃ R : Matrix (Fin (2 * 2 + 0)) (HypIndex 2 0) K, IsHypTransport h R ∧
      R *ᵥ (Pi.single ie1 1 : HypIndex 2 0 → K) =
        (Pi.single 0 1 + Pi.single 1 1 : Fin 4 → K) := by
  have ha0 : (Pi.single 0 1 + Pi.single 1 1 : Fin 4 → K) ≠ 0 := by
    intro h0
    have h1 : (1 : K) = 0 := by
      simpa [Pi.single_apply] using congrFun h0 0
    exact one_ne_zero h1
  have ha : stdHermForm h (2 * 2 + 0) (Pi.single 0 1 + Pi.single 1 1 : Fin 4 → K)
      (Pi.single 0 1 + Pi.single 1 1 : Fin 4 → K) = 0 := by
    haveI := h.charP
    have hsplit : stdHermForm h (2 * 2 + 0) (Pi.single 0 1 + Pi.single 1 1 : Fin 4 → K) =
        stdHermForm h (2 * 2 + 0) (Pi.single 0 1 : Fin 4 → K) +
          stdHermForm h (2 * 2 + 0) (Pi.single 1 1 : Fin 4 → K) :=
      map_add _ _ _
    rw [hsplit, LinearMap.add_apply, stdHermForm_single, stdHermForm_single]
    simpa using CharTwo.add_self_eq_zero (1 : K)
  exact exists_isHypTransport_first h (r := 2) (ε := 0) (by norm_num) ha0 ha

private lemma transportInv_mulVec_mulVec_Q05 {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) {r ε : ℕ}
    {R : Matrix (Fin (2 * r + ε)) (HypIndex r ε) K} (hR : IsHypTransport h R)
    (v : HypIndex r ε → K) : transportInv h R *ᵥ (R *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, transportInv_mul hR, Matrix.one_mulVec]

private lemma mulVec_injective_of_isHypTransport_Q05 {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) {r ε : ℕ}
    {R : Matrix (Fin (2 * r + ε)) (HypIndex r ε) K} (hR : IsHypTransport h R) :
    Function.Injective fun v : HypIndex r ε → K => R *ᵥ v := by
  intro u v huv
  have huv' := congrArg (fun w => transportInv h R *ᵥ w) huv
  rwa [transportInv_mulVec_mulVec_Q05 h hR u, transportInv_mulVec_mulVec_Q05 h hR v] at huv'

private lemma hypTransport_mulVec_Q05 {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) {r ε : ℕ}
    {R : Matrix (Fin (2 * r + ε)) (HypIndex r ε) K} (hR : IsHypTransport h R)
    (g : hypSU h r ε) {e₀ : Fin (2 * r + ε) → K} {e₁ : HypIndex r ε → K}
    (he : R *ᵥ e₁ = e₀) :
    (((hypTransport h hR g : unitarySU p f K (2 * r + ε)) : GL (Fin (2 * r + ε)) K) :
      Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) *ᵥ e₀ =
      R *ᵥ (((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ e₁) := by
  rw [coe_hypTransport, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← he,
    transportInv_mulVec_mulVec_Q05 h hR e₁]

private lemma mulVec_single_eq_smul_Q05 {K : Type} [Field K] (G : Matrix Ix Ix K)
    (h : ∀ a, a ≠ ie1 → G a ie1 = 0) :
    G *ᵥ (Pi.single ie1 1 : Ix → K) = G ie1 ie1 • (Pi.single ie1 1 : Ix → K) := by
  rw [mulVec_single_one]
  funext a
  rw [Matrix.col_apply, Pi.smul_apply]
  by_cases ha : a = ie1
  · subst ha
    simp
  · simp [h a ha, ha]

private lemma eq_zero_of_mulVec_single_eq_smul_Q05 {K : Type} [Field K] (G : Matrix Ix Ix K)
    {c : K} (hc : G *ᵥ (Pi.single ie1 1 : Ix → K) = c • (Pi.single ie1 1 : Ix → K)) :
    ∀ a, a ≠ ie1 → G a ie1 = 0 := by
  intro a ha
  have h := congrFun hc a
  rw [mulVec_single_one, Matrix.col_apply, Pi.smul_apply] at h
  simpa [ha] using h

theorem map_parP_hypTransport_eq_lineStab {a : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 a K) {R : Matrix (Fin (2 * 2 + 0)) (HypIndex 2 0) K}
    (hR : IsHypTransport h R) {e₀ : Fin 4 → K}
    (he : R *ᵥ (Pi.single ie1 1 : HypIndex 2 0 → K) = e₀) :
    (parP h).map (hypTransport h hR).toMonoidHom = lineStab (StatedSU 4 (2 ^ a) K) e₀ := by
  ext x
  rw [Subgroup.mem_map_equiv, mem_lineStab, mem_parP_iff h]
  set g : hypSU h 2 0 := (hypTransport h hR).symm x with hg
  have hxg : hypTransport h hR g = x := MulEquiv.apply_symm_apply (hypTransport h hR) x
  constructor
  · intro hcol
    refine ⟨(((g : GL Ix K) : Matrix Ix Ix K)) ie1 ie1, ?_⟩
    rw [← hxg, hypTransport_mulVec_Q05 h hR g he, mulVec_single_eq_smul_Q05 _ hcol,
      Matrix.mulVec_smul, he]
  · rintro ⟨c, hc⟩
    rw [← hxg] at hc
    rw [hypTransport_mulVec_Q05 h hR g he, ← he, ← Matrix.mulVec_smul] at hc
    exact eq_zero_of_mulVec_single_eq_smul_Q05 _ (mulVec_injective_of_isHypTransport_Q05 h hR hc)

end CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD
