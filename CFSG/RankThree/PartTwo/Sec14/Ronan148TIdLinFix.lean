module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148TEvenL3

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148T

open Matrix

variable {F : Type*} [Field F]

@[expose] def fixSpace (D : Subgroup (GL (Fin 3) F)) : Submodule F (Fin 3 → F) where
  carrier := {v | ∀ d ∈ D, (d : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v}
  add_mem' := by
    intro a b ha hb d hd
    rw [Matrix.mulVec_add, ha d hd, hb d hd]
  zero_mem' := by
    intro d _
    exact Matrix.mulVec_zero _
  smul_mem' := by
    intro c a ha d hd
    rw [Matrix.mulVec_smul, ha d hd]

@[expose] noncomputable def comSpace (D : Subgroup (GL (Fin 3) F)) : Submodule F (Fin 3 → F) :=
  Submodule.span F {u | ∃ d ∈ D, ∃ v : Fin 3 → F, u = (d : Matrix (Fin 3) (Fin 3) F) *ᵥ v - v}

theorem mem_fixSpace_iff {D : Subgroup (GL (Fin 3) F)} {v : Fin 3 → F} :
    v ∈ fixSpace D ↔ ∀ d ∈ D, (d : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v :=
  Iff.rfl

theorem sub_mem_comSpace {D : Subgroup (GL (Fin 3) F)} {d : GL (Fin 3) F} (hd : d ∈ D)
    (w : Fin 3 → F) : (d : Matrix (Fin 3) (Fin 3) F) *ᵥ w - w ∈ comSpace D := by
  unfold comSpace
  exact Submodule.subset_span ⟨d, hd, w, rfl⟩

theorem conj_mulVec (g d : GL (Fin 3) F) (w : Fin 3 → F) :
    ((g * d * g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
        ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ w) =
      (g : Matrix (Fin 3) (Fin 3) F) *ᵥ ((d : Matrix (Fin 3) (Fin 3) F) *ᵥ w) := by
  have hig : ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      (g : Matrix (Fin 3) (Fin 3) F) = 1 := Units.inv_mul g
  rw [Units.val_mul, Units.val_mul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, mul_assoc, hig,
    mul_one]

theorem mulVec_mem_fixSpace {D : Subgroup (GL (Fin 3) F)} {g : GL (Fin 3) F}
    (hg : ∀ d ∈ D, g⁻¹ * d * g ∈ D) {v : Fin 3 → F} (hv : v ∈ fixSpace D) :
    (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ fixSpace D := by
  rw [mem_fixSpace_iff] at hv ⊢
  intro d hd
  have h1 : ((g⁻¹ * d * g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v :=
    hv _ (hg d hd)
  rw [Units.val_mul, Units.val_mul] at h1
  have hM : (g : Matrix (Fin 3) (Fin 3) F) *
      (((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (d : Matrix (Fin 3) (Fin 3) F) *
        (g : Matrix (Fin 3) (Fin 3) F)) =
      (d : Matrix (Fin 3) (Fin 3) F) * (g : Matrix (Fin 3) (Fin 3) F) := by
    rw [← mul_assoc, ← mul_assoc, Units.mul_inv g, one_mul]
  calc (d : Matrix (Fin 3) (Fin 3) F) *ᵥ ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ v)
      = ((d : Matrix (Fin 3) (Fin 3) F) * (g : Matrix (Fin 3) (Fin 3) F)) *ᵥ v :=
        Matrix.mulVec_mulVec v _ _
    _ = ((g : Matrix (Fin 3) (Fin 3) F) *
          (((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (d : Matrix (Fin 3) (Fin 3) F) *
            (g : Matrix (Fin 3) (Fin 3) F))) *ᵥ v := by rw [hM]
    _ = (g : Matrix (Fin 3) (Fin 3) F) *ᵥ
          ((((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (d : Matrix (Fin 3) (Fin 3) F) *
            (g : Matrix (Fin 3) (Fin 3) F)) *ᵥ v) := (Matrix.mulVec_mulVec v _ _).symm
    _ = (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v := by rw [h1]

theorem mulVec_mem_comSpace {D : Subgroup (GL (Fin 3) F)} {g : GL (Fin 3) F}
    (hg : ∀ d ∈ D, g * d * g⁻¹ ∈ D) {v : Fin 3 → F} (hv : v ∈ comSpace D) :
    (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ comSpace D := by
  have hle : (comSpace D).map (Matrix.toLin' (g : Matrix (Fin 3) (Fin 3) F)) ≤ comSpace D := by
    unfold comSpace
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨d, hd, w, rfl⟩, rfl⟩
    have key : (g : Matrix (Fin 3) (Fin 3) F) *ᵥ ((d : Matrix (Fin 3) (Fin 3) F) *ᵥ w - w) =
        ((g * d * g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
          ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ w) - (g : Matrix (Fin 3) (Fin 3) F) *ᵥ w := by
      rw [Matrix.mulVec_sub, conj_mulVec]
    rw [Matrix.toLin'_apply, key]
    exact sub_mem_comSpace (hg d hd) _
  have hmem := hle (Submodule.mem_map_of_mem hv)
  rwa [Matrix.toLin'_apply] at hmem

theorem eq_bot_of_forall_mulVec_eq {D : Subgroup (GL (Fin 3) F)}
    (h : ∀ d ∈ D, ∀ v : Fin 3 → F, (d : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v) : D = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro d hd
  apply Units.ext
  rw [Units.val_one]
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  simp only [Matrix.toLin'_apply, Matrix.one_mulVec]
  exact h d hd v

theorem fixSpace_ne_top {D : Subgroup (GL (Fin 3) F)} (hD : D ≠ ⊥) : fixSpace D ≠ ⊤ := by
  intro h
  apply hD
  apply eq_bot_of_forall_mulVec_eq
  intro d hd v
  have hv : v ∈ fixSpace D := by
    rw [h]
    exact Submodule.mem_top
  exact (mem_fixSpace_iff.mp hv) d hd

theorem comSpace_ne_bot {D : Subgroup (GL (Fin 3) F)} (hD : D ≠ ⊥) : comSpace D ≠ ⊥ := by
  intro h
  apply hD
  apply eq_bot_of_forall_mulVec_eq
  intro d hd v
  have hv := sub_mem_comSpace hd v
  rw [h, Submodule.mem_bot, sub_eq_zero] at hv
  exact hv

theorem fixSpace_or_comSpace {D : Subgroup (GL (Fin 3) F)} [Group.IsPerfect D] (hD : D ≠ ⊥)
    {W : Submodule F (Fin 3 → F)}
    (hW : ∀ g ∈ D, ∀ v ∈ W, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ W) (hW0 : W ≠ ⊥)
    (hWt : W ≠ ⊤) :
    (fixSpace D ≠ ⊥ ∧ fixSpace D ≠ ⊤) ∨ (comSpace D ≠ ⊥ ∧ comSpace D ≠ ⊤) := by
  have hinv : ∀ g ∈ D, ∀ v ∈ W, Matrix.toLin' (g : Matrix (Fin 3) (Fin 3) F) v ∈ W :=
    fun g hg v hv => by rw [Matrix.toLin'_apply]; exact hW g hg v hv
  let baseW : D →* Module.End F W :=
    { toFun := fun g => (Matrix.toLin' ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)).restrict
        (hinv g g.2)
      map_one' := by
        ext v
        simp
      map_mul' := fun a b => by
        ext v
        simp [Matrix.mulVec_mulVec] }
  let baseQ : D →* Module.End F ((Fin 3 → F) ⧸ W) :=
    { toFun := fun g => W.mapQ W (Matrix.toLin' ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))
        (fun v hv => hinv g g.2 v hv)
      map_one' := by
        ext v
        simp
      map_mul' := fun a b => by
        ext v
        simp }
  have hdim := Submodule.finrank_quotient_add_finrank W
  rw [Module.finrank_fin_fun] at hdim
  have hW1 : Module.finrank F W ≠ 0 := fun h => hW0 (Submodule.finrank_eq_zero.mp h)
  have hW3 : Module.finrank F W < 3 := by
    have := Submodule.finrank_lt hWt
    rwa [Module.finrank_fin_fun] at this
  have hfixtop : fixSpace D ≠ ⊤ := fixSpace_ne_top hD
  have hcombot : comSpace D ≠ ⊥ := comSpace_ne_bot hD
  rcases (by omega : Module.finrank F W = 1 ∨ Module.finrank F W = 2) with h1 | h2
  ·
    have hWtriv : ∀ g : D, baseW.toHomUnits g = 1 := eq_one_of_finrank_eq_one h1 _
    have hWfix : ∀ g ∈ D, ∀ v ∈ W, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v := by
      intro g hg v hv
      have h3 := congrArg
        (fun u : (Module.End F W)ˣ => ((u : Module.End F W) ⟨v, hv⟩ : Fin 3 → F))
        (hWtriv ⟨g, hg⟩)
      simpa [baseW] using h3
    have hWle : W ≤ fixSpace D := by
      intro v hv
      exact mem_fixSpace_iff.mpr fun g hg => hWfix g hg v hv
    left
    refine ⟨?_, hfixtop⟩
    intro h
    apply hW0
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hx' : x ∈ fixSpace D := hWle hx
    rw [h, Submodule.mem_bot] at hx'
    exact hx'
  ·
    have hQtriv : ∀ g : D, baseQ.toHomUnits g = 1 := eq_one_of_finrank_eq_one (by omega) _
    have hcomle : ∀ g ∈ D, ∀ v : Fin 3 → F, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v - v ∈ W := by
      intro g hg v
      have h3 := congrArg
        (fun u : (Module.End F ((Fin 3 → F) ⧸ W))ˣ =>
          ((u : Module.End F ((Fin 3 → F) ⧸ W)) (W.mkQ v)))
        (hQtriv ⟨g, hg⟩)
      simp only [MonoidHom.toHomUnits, baseQ, Units.val_one, Module.End.one_apply] at h3
      change W.mkQ (Matrix.toLin' (g : Matrix (Fin 3) (Fin 3) F) v) = W.mkQ v at h3
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq,
        Matrix.toLin'_apply] at h3
      exact h3
    have hcomle' : comSpace D ≤ W := by
      unfold comSpace
      rw [Submodule.span_le]
      rintro _ ⟨d, hd, w, rfl⟩
      exact hcomle d hd w
    have hcomtop : comSpace D ≠ ⊤ := by
      intro h
      apply hWt
      apply top_le_iff.mp
      rw [← h]
      exact hcomle'
    right
    exact ⟨hcombot, hcomtop⟩

end CFSG.RankThree.PartTwo.Sec14.Ronan148T
