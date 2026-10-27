module

public import CFSG.Timmesfeld.Transvection.ModelSUTransitive

public section

namespace CFSG.Timmesfeld.Transvection

namespace ModelRank

open Matrix CFSG.LieType.Universal.Unitary CFSG.Timmesfeld.LieEmbed CFSG.Timmesfeld.ARS
open scoped commutatorElement

variable {F : Type} [Field F] {m : ℕ}

@[expose] def SUTorusStmt (σ : F ≃+* F) (m : ℕ) : Prop :=
  ∀ {a d v v' : Fin m → F}, uForm σ a a = 0 → uForm σ d d = 0 → uForm σ a d = 1 →
    uForm σ v v = 0 → uForm σ v' v' = 0 → uForm σ v v' = 1 → uForm σ a v = 0 →
    uForm σ a v' = 0 → uForm σ d v = 0 → uForm σ d v' = 0 → ∀ {μ : F}, μ ≠ 0 →
    ∃ g : SU σ m, suMat σ m g *ᵥ a = μ • a ∧ suMat σ m g *ᵥ d = (σ μ)⁻¹ • d ∧
      suMat σ m g *ᵥ v = σ μ • v ∧ suMat σ m g *ᵥ v' = μ⁻¹ • v'

end ModelRank

end CFSG.Timmesfeld.Transvection

namespace CFSG.Timmesfeld.Transvection

namespace ModelRank

open Matrix CFSG.LieType.Universal.Unitary CFSG.Timmesfeld.LieEmbed

variable {F : Type} [Field F] {σ : F ≃+* F} {m : ℕ}

theorem vecMulVec_uRow_mulVec (p q x : Fin m → F) :
    vecMulVec p (uRow σ q) *ᵥ x = uForm σ q x • p := by
  funext i
  simp only [mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
    ← uRow_dotProduct, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem one_add_smul_vecMulVec_uRow_mulVec (p q x : Fin m → F) (c : F) :
    (1 + (c - 1) • vecMulVec p (uRow σ q)) *ᵥ x = x + ((c - 1) * uForm σ q x) • p := by
  rw [add_mulVec, one_mulVec, smul_mulVec, vecMulVec_uRow_mulVec, smul_smul]

theorem det_one_add_smul_vecMulVec_uRow (p q : Fin m → F) (c : F) :
    (1 + (c - 1) • vecMulVec p (uRow σ q)).det = 1 + (c - 1) * uForm σ q p := by
  rw [← smul_vecMulVec, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow,
    dotProduct_smul, uRow_dotProduct, smul_eq_mul]

theorem suTorusStmt_holds (hσ : ∀ c, σ (σ c) = c) : SUTorusStmt σ m := by
  intro a d v v' haa hdd had hvv hv'v' hvv' hav hav' hdv hdv' μ hμ
  have hda : uForm σ d a = 1 := by rw [← uForm_conj σ hσ, had, map_one]
  have hv'v : uForm σ v' v = 1 := by rw [← uForm_conj σ hσ, hvv', map_one]
  have hva : uForm σ v a = 0 := uForm_eq_zero_comm hσ hav
  have hv'a : uForm σ v' a = 0 := uForm_eq_zero_comm hσ hav'
  have hvd : uForm σ v d = 0 := uForm_eq_zero_comm hσ hdv
  have hv'd : uForm σ v' d = 0 := uForm_eq_zero_comm hσ hdv'
  have hsμ : σ μ ≠ 0 := (map_ne_zero σ).2 hμ
  set M : Matrix (Fin m) (Fin m) F :=
    (1 + (μ - 1) • vecMulVec a (uRow σ d)) * (1 + ((σ μ)⁻¹ - 1) • vecMulVec d (uRow σ a)) *
      (1 + (σ μ - 1) • vecMulVec v (uRow σ v')) * (1 + (μ⁻¹ - 1) • vecMulVec v' (uRow σ v))
    with hMdef
  have hM : ∀ x, M *ᵥ x = x + ((μ - 1) * uForm σ d x) • a +
      (((σ μ)⁻¹ - 1) * uForm σ a x) • d + ((σ μ - 1) * uForm σ v' x) • v +
      ((μ⁻¹ - 1) * uForm σ v x) • v' := by
    intro x
    simp only [hMdef, ← mulVec_mulVec, one_add_smul_vecMulVec_uRow_mulVec, uForm_add_right,
      uForm_smul_right, haa, hdd, hvv, hv'v', hav, hav', hdv, hdv', hva, hv'a, hvd, hv'd,
      mul_zero, add_zero]
    abel
  have hdet : M.det = 1 := by
    rw [hMdef, det_mul, det_mul, det_mul, det_one_add_smul_vecMulVec_uRow,
      det_one_add_smul_vecMulVec_uRow, det_one_add_smul_vecMulVec_uRow,
      det_one_add_smul_vecMulVec_uRow, hda, had, hv'v, hvv']
    field_simp
    ring
  have hiso : ∀ x y, uForm σ (M *ᵥ x) (M *ᵥ y) = uForm σ x y := by
    intro x y
    rw [hM, hM]
    simp only [uForm_add_left, uForm_add_right, uForm_smul_left, uForm_smul_right, haa, hdd,
      had, hda, hvv, hv'v', hvv', hv'v, hav, hav', hdv, hdv', hva, hv'a, hvd, hv'd, map_mul,
      map_sub, map_one, map_inv₀, hσ, mul_zero, zero_mul, add_zero, zero_add, mul_one]
    rw [← uForm_conj σ hσ a x, ← uForm_conj σ hσ d x, ← uForm_conj σ hσ v x,
      ← uForm_conj σ hσ v' x]
    have h1 : μ * μ⁻¹ = 1 := mul_inv_cancel₀ hμ
    have h2 : σ μ * (σ μ)⁻¹ = 1 := mul_inv_cancel₀ hsμ
    linear_combination (σ (uForm σ a x) * uForm σ d y + σ (uForm σ v' x) * uForm σ v y) * h1 +
      (σ (uForm σ d x) * uForm σ a y + σ (uForm σ v x) * uForm σ v' y) * h2
  obtain ⟨g, hg⟩ := CFSG.StandardType.GGOppRadSpU.exists_SU_of_isometry σ hσ (Matrix.toLin' M)
    (fun x y => by
      rw [suForm_β_eq_uForm, suForm_β_eq_uForm, Matrix.toLin'_apply, Matrix.toLin'_apply, hiso])
    (by rw [LinearMap.toMatrix'_toLin', hdet])
  have hgx : ∀ x, suMat σ m g *ᵥ x = M *ᵥ x := by
    intro x
    have h := hg x
    rw [CFSG.LieType.BorelTits.natRep_apply, Matrix.toLin'_apply] at h
    rw [suMat_apply]
    exact h
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · rw [hgx, hM, hda, haa, hv'a, hva]
    simp only [mul_one, mul_zero, zero_smul, add_zero]
    module
  · rw [hgx, hM, hdd, had, hv'd, hvd]
    simp only [mul_one, mul_zero, zero_smul, add_zero]
    module
  · rw [hgx, hM, hdv, hav, hv'v, hvv]
    simp only [mul_one, mul_zero, zero_smul, add_zero]
    module
  · rw [hgx, hM, hdv', hav', hv'v', hvv']
    simp only [mul_one, mul_zero, zero_smul, add_zero]
    module

end ModelRank

end CFSG.Timmesfeld.Transvection
