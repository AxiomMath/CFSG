module

public import CFSG.Timmesfeld.Transvection.ModelSURadical
public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalSpUSUStd
public import CFSG.Timmesfeld.LieEmbed.UnitaryWittN

public section

namespace CFSG.Timmesfeld.Transvection

open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.Timmesfeld.LieEmbed

namespace ModelRank

variable {F : Type} [Field F] {σ : F ≃+* F} {m : ℕ}

theorem suForm_β_eq_uForm (hσ : ∀ c, σ (σ c) = c) (x y : Fin m → F) :
    (CFSG.StandardType.GGOppRadSpU.suForm σ hσ m).β x y = uForm σ x y := by
  rw [CFSG.StandardType.GGOppRadSpU.suForm_β, uForm_eq]

theorem exists_suMat_mulVec_eichler [CharP F 2] (hσ : ∀ c, σ (σ c) = c) {a w : Fin m → F}
    (haa : uForm σ a a = 0) (haw : uForm σ a w = 0) {c : F} (hc : c + σ c = uForm σ w w) :
    ∃ x : SU σ m, ∀ u, suMat σ m x *ᵥ u = u + uForm σ a u • (w + c • a) + uForm σ w u • a := by
  obtain ⟨g, hg⟩ := CFSG.StandardType.GGOppRadSpU.exists_SU_eichler σ hσ
    (by rw [suForm_β_eq_uForm]; exact haa) (by rw [suForm_β_eq_uForm]; exact haw) (c := c)
    (by rw [suForm_β_eq_uForm]; exact hc)
  refine ⟨g, fun u => ?_⟩
  have h := hg u
  rw [CFSG.LieType.BorelTits.natRep_apply, suForm_β_eq_uForm, suForm_β_eq_uForm] at h
  rw [suMat_apply]
  exact h

theorem exists_mem_uRad_mulVec_eq [CharP F 2] (hσ : ∀ c, σ (σ c) = c) {a v v' : Fin m → F}
    (haa : uForm σ a a = 0) (hv : uForm σ v v = 0) (hv' : uForm σ v' v' = 0)
    (h1 : uForm σ a v = 1) (h1' : uForm σ a v' = 1) :
    ∃ x ∈ uRad σ a, suMat σ m x *ᵥ v = v' := by
  have haw : uForm σ a (v + v') = 0 := by
    rw [uForm_add_right, h1, h1', CharTwo.add_self_eq_zero]
  have hwa : uForm σ (v + v') a = 0 := uForm_eq_zero_comm hσ haw
  have hc : uForm σ (v + v') v + σ (uForm σ (v + v') v) = uForm σ (v + v') (v + v') := by
    rw [uForm_conj σ hσ]
    simp only [uForm_add_left, uForm_add_right, hv, hv']
    ring
  obtain ⟨x, hx⟩ := exists_suMat_mulVec_eichler hσ haa haw hc
  refine ⟨x, ⟨?_, fun u hu => ⟨uForm σ (v + v') u, ?_⟩⟩, ?_⟩
  · rw [hx, haa, hwa, zero_smul, zero_smul, add_zero, add_zero]
  · rw [hx, hu, zero_smul, add_zero]
  · rw [hx, h1, one_smul]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (v i + uForm σ (v + v') v * a i) * (CharTwo.two_eq_zero : (2 : F) = 0)

end ModelRank

end CFSG.Timmesfeld.Transvection
