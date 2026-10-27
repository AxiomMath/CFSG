module

public import CFSG.RankThree.GF2n.Smith81.S81VFrameMat

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.RankThree.GF2n.Smith81.U6Cube Module Matrix

variable {F : Type} [Field F] {σ : F ≃+* F} {a b : Fin 3 → Fin 6 → F}

@[expose] def Wa (a : Fin 3 → Fin 6 → F) : Submodule F (Fin 6 → F) :=
  Submodule.span F (Set.range a)

@[expose] def Pstab (σ : F ≃+* F) (W : Submodule F (Fin 6 → F)) : Subgroup (SUid σ 6) where
  carrier := {g | W.map (gLin g) = W}
  mul_mem' {g h} hg hh := by
    show W.map (gLin (g * h)) = W
    have e : gLin (g * h) = (gLin g).comp (gLin h) := LinearMap.ext (gLin_mul g h)
    rw [e, Submodule.map_comp]
    have hh' : W.map (gLin h) = W := hh
    have hg' : W.map (gLin g) = W := hg
    rw [hh', hg']
  one_mem' := by
    show W.map (gLin (1 : SUid σ 6)) = W
    have e : gLin (1 : SUid σ 6) = LinearMap.id := LinearMap.ext (gLin_one)
    rw [e, Submodule.map_id]
  inv_mem' {g} hg := by
    show W.map (gLin g⁻¹) = W
    have hg' : W.map (gLin g) = W := hg
    have e : gLin (g⁻¹ * g) = (gLin g⁻¹).comp (gLin g) := LinearMap.ext (gLin_mul g⁻¹ g)
    have e1 : gLin (g⁻¹ * g) = LinearMap.id := by
      rw [inv_mul_cancel]
      exact LinearMap.ext (gLin_one)
    calc W.map (gLin g⁻¹) = (W.map (gLin g)).map (gLin g⁻¹) := by rw [hg']
      _ = W.map ((gLin g⁻¹).comp (gLin g)) := (Submodule.map_comp _ _ _).symm
      _ = W := by rw [← e, e1, Submodule.map_id]

private theorem blk1_a_mem_Wa (j : Fin 3) : a j ∈ Wa a :=
  Submodule.subset_span (Set.mem_range_self j)

private theorem blk1_cT_zero : cT σ (0 : Matrix (Fin 3) (Fin 3) F) = 0 := by
  ext i j
  simp [cT_apply]

variable (hσ : ∀ c, σ (σ c) = c) (hf : Frame σ a b)

include hσ hf

theorem mem_Wa_iff (x : Fin 6 → F) :
    x ∈ Wa a ↔ ∀ i, herm σ (a i) x = 0 := by
  constructor
  · intro hx
    have hx' : x ∈ Submodule.span F (Set.range a) := hx
    clear hx
    induction hx' using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨j, rfl⟩ := hv
      intro i
      exact hf.aa i j
    | zero => intro i; simp
    | add u v _ _ hu hv =>
      intro i
      rw [herm_add_right, hu i, hv i, add_zero]
    | smul c u _ hu =>
      intro i
      rw [herm_smul_right, hu i, mul_zero]
  · intro hx
    have hA : ∀ i, fb hσ hf (Sum.inl i) ∈ Wa a := fun i => by
      rw [fb_apply hσ hf]
      exact blk1_a_mem_Wa i
    rw [← (fb hσ hf).sum_repr x]
    refine Submodule.sum_mem _ fun p _ => ?_
    rcases p with i | i
    · exact Submodule.smul_mem _ _ (hA i)
    · have h0 : (fb hσ hf).repr x (Sum.inr i) = 0 := by
        rw [repr_inr hσ hf]
        exact hx i
      show (fb hσ hf).repr x (Sum.inr i) • fb hσ hf (Sum.inr i) ∈ Wa a
      rw [h0, zero_smul]
      exact Submodule.zero_mem _

private theorem blk1_gm_inr_inl (g : SUid σ 6) (i j : Fin 3) :
    gm hσ hf g (Sum.inr i) (Sum.inl j) = herm σ (a i) (g • a j) := by
  have hrep : (fb hσ hf).repr (fam a b (Sum.inl j)) = Finsupp.single (Sum.inl j) 1 := by
    rw [← fb_apply hσ hf (Sum.inl j), Module.Basis.repr_self]
  have h1 := gm_repr hσ hf g (fam a b (Sum.inl j))
  rw [hrep] at h1
  have h2 := congrFun h1 (Sum.inr i)
  have h4 := (repr_inr hσ hf (g • fam a b (Sum.inl j)) i).symm.trans h2
  have h3 : (gm hσ hf g *ᵥ ⇑(Finsupp.single (Sum.inl j) (1 : F))) (Sum.inr i)
      = gm hσ hf g (Sum.inr i) (Sum.inl j) := by
    simp [Matrix.mulVec, dotProduct, Finsupp.single_apply]
  exact (h4.trans h3).symm

theorem mem_Pstab_iff (g : SUid σ 6) :
    g ∈ Pstab σ (Wa a) ↔ ∀ i j, gm hσ hf g (Sum.inr i) (Sum.inl j) = 0 := by
  have hmem : g ∈ Pstab σ (Wa a) ↔ (Wa a).map (gLin g) = Wa a := Iff.rfl
  rw [hmem]
  constructor
  · intro h i j
    rw [blk1_gm_inr_inl hσ hf g i j]
    have hj : gLin g (a j) ∈ Wa a := by
      rw [← h]
      exact Submodule.mem_map_of_mem (blk1_a_mem_Wa j)
    exact (mem_Wa_iff hσ hf (gLin g (a j))).1 hj i
  · intro h
    have hsub : ∀ j, gLin g (a j) ∈ Wa a := fun j =>
      (mem_Wa_iff hσ hf (gLin g (a j))).2 fun i =>
        (blk1_gm_inr_inl hσ hf g i j).symm.trans (h i j)
    have hle : (Wa a).map (gLin g) ≤ Wa a := by
      rw [Submodule.map_le_iff_le_comap]
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨j, rfl⟩
      exact hsub j
    have hrank : Module.finrank F ((Wa a).map (gLin g)) = Module.finrank F (Wa a) :=
      (LinearEquiv.finrank_eq
        (Submodule.equivMapOfInjective (gLin g) (gLin_injective g) (Wa a))).symm
    exact Submodule.eq_of_le_of_finrank_eq hle hrank

theorem Pstab_blocks (g : SUid σ 6) (hg : g ∈ Pstab σ (Wa a)) :
    ∃ A B D : Matrix (Fin 3) (Fin 3) F, gm hσ hf g = Matrix.fromBlocks A B 0 D ∧ cT σ A * D = 1 ∧
      cT σ D * A = 1 ∧ cT σ B * D + cT σ D * B = 0 := by
  have hlow := (mem_Pstab_iff hσ hf g).1 hg
  obtain ⟨A, B, D, hABD⟩ : ∃ A B D : Matrix (Fin 3) (Fin 3) F,
      gm hσ hf g = Matrix.fromBlocks A B 0 D := by
    have hC : (gm hσ hf g).toBlocks₂₁ = 0 := by
      ext i j
      exact hlow i j
    have h := Matrix.fromBlocks_toBlocks (gm hσ hf g)
    rw [hC] at h
    exact ⟨_, _, _, h.symm⟩
  refine ⟨A, B, D, hABD, ?_⟩
  have hU := gm_unitary hσ hf g
  rw [hABD] at hU
  have key : cT σ (Matrix.fromBlocks A B 0 D) * Jm F * Matrix.fromBlocks A B 0 D
      = Matrix.fromBlocks 0 (cT σ A * D) (cT σ D * A) (cT σ D * B + cT σ B * D) := by
    rw [cT_fromBlocks, blk1_cT_zero]
    simp only [Jm, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one,
      Matrix.one_mul, add_zero, zero_add]
  have hJ := key.symm.trans hU
  rw [Jm] at hJ
  obtain ⟨-, h12, h21, h22⟩ := Matrix.fromBlocks_inj.mp hJ
  exact ⟨h12, h21, (add_comm _ _).trans h22⟩

end CFSG.RankThree.GF2n.Smith81.S81V
