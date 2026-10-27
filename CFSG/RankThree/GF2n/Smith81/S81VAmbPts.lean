module

public import CFSG.RankThree.GF2n.Smith81.S81VWitt
public import CFSG.RankThree.GF2n.Smith81.S81VAmbMap
public import CFSG.RankThree.GF2n.Smith81.S81VBlock

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.RankThree.GF2n.Smith81.U6Cube Module Matrix

variable {F : Type} [Field F] [Finite F] [CharP F 2] {σ : F ≃+* F}

@[expose] def PtU (σ : F ≃+* F) : Type := {W : Submodule F (Fin 6 → F) // IsPt σ W}

theorem isPt_W₀ : IsPt σ (W₀ F) := isTotIso_W₀

@[expose] noncomputable def ptU (g : SUid σ 6) : PtU σ := ⟨(W₀ F).map (gLin g), isPt_map g isPt_W₀⟩

@[expose] def ColU (x y z : PtU σ) : Prop := finrank F ↥(x.1 ⊓ y.1) = 2 ∧ x.1 ⊓ y.1 ≤ z.1

theorem ptU_val (g : SUid σ 6) : (ptU g).1 = (W₀ F).map (gLin g) := rfl

theorem ptU_mul_of_mem_Pstab (g : SUid σ 6) {p : SUid σ 6} (hp : p ∈ Pstab σ (W₀ F)) :
    ptU (g * p) = ptU g := by
  have hp' : (W₀ F).map (gLin p) = W₀ F := hp
  apply Subtype.ext
  rw [ptU_val, ptU_val, ← map_map_gLin g p (W₀ F), hp']

theorem ptU_eq_iff (g g' : SUid σ 6) : ptU g = ptU g' ↔ g'⁻¹ * g ∈ Pstab σ (W₀ F) := by
  have e1 : gLin (1 : SUid σ 6) = LinearMap.id := LinearMap.ext gLin_one
  constructor
  · intro h
    have h' : (ptU g).1 = (ptU g').1 := by rw [h]
    rw [ptU_val, ptU_val] at h'
    show (W₀ F).map (gLin (g'⁻¹ * g)) = W₀ F
    rw [← map_map_gLin g'⁻¹ g (W₀ F), h', map_map_gLin g'⁻¹ g' (W₀ F), inv_mul_cancel, e1,
      Submodule.map_id]
  · intro h
    have hp : (W₀ F).map (gLin (g'⁻¹ * g)) = W₀ F := h
    have h2 : ((W₀ F).map (gLin (g'⁻¹ * g))).map (gLin g') = (W₀ F).map (gLin g') := by
      rw [hp]
    rw [map_map_gLin, mul_inv_cancel_left] at h2
    apply Subtype.ext
    rw [ptU_val, ptU_val]
    exact h2

theorem ptU_surjective (hσ : IsUnitaryInvolution σ) : Function.Surjective (ptU : SUid σ 6 → PtU σ) := by
  rintro ⟨W, hW⟩
  obtain ⟨g, hg⟩ := exists_su_smul_W₀ hσ hW.1 hW.2
  refine ⟨g, Subtype.ext ?_⟩
  show (W₀ F).map (gLin g) = W
  ext v
  rw [hg v, Submodule.mem_map]
  exact Iff.rfl

end CFSG.RankThree.GF2n.Smith81.S81V
