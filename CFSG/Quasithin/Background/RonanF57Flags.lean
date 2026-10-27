module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.CentralizerScalars
public import CFSG.Quasithin.Background.RonanF57Mat
public import CFSG.Quasithin.Background.RonanF57Unitary

public section

namespace CFSG.Quasithin.RonanF57

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag Matrix
  CFSG.HardMathSupport.Curtis.UnitaryLevi

variable {E : Type} [Group E] {Gp : Subgroup E} {K : Type} [Field K]

section Spans

@[expose] def wPoint (W : Matrix (Fin 4) (Fin 4) K) : Submodule K (Fin 4 → K) :=
  Submodule.span K {fun i => W i 0}

@[expose] def wPlane (W : Matrix (Fin 4) (Fin 4) K) : Submodule K (Fin 4 → K) :=
  Submodule.span K {fun i => W i 0, fun i => W i 1}

theorem mulVec_two (W : Matrix (Fin 4) (Fin 4) K) (v : Fin 4 → K) (h2 : v 2 = 0) (h3 : v 3 = 0) :
    W *ᵥ v = v 0 • (fun i => W i 0) + v 1 • (fun i => W i 1) := by
  funext i
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, h2, h3]
  ring

theorem mulVec_one (W : Matrix (Fin 4) (Fin 4) K) (v : Fin 4 → K) (h1 : v 1 = 0) (h2 : v 2 = 0)
    (h3 : v 3 = 0) : W *ᵥ v = v 0 • (fun i => W i 0) := by
  funext i
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, h1, h2, h3]
  ring

theorem wPoint_coe (W : Matrix (Fin 4) (Fin 4) K) :
    (wPoint W : Set (Fin 4 → K)) = (fun v => W *ᵥ v) ''
      {v : Fin 4 → K | ∀ pos : Fin 4, pos ∉ ({0} : Set (Fin 4)) → v pos = 0} := by
  ext w
  constructor
  · intro hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    refine ⟨Pi.single 0 c, ?_, ?_⟩
    · intro pos hpos
      have : pos ≠ 0 := fun h => hpos (by simp [h])
      simp [Pi.single_eq_of_ne this]
    · funext i
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, Pi.single_apply, mul_comm]
  · rintro ⟨v, hv, rfl⟩
    have h1 : v 1 = 0 := hv 1 (by simp)
    have h2 : v 2 = 0 := hv 2 (by simp)
    have h3 : v 3 = 0 := hv 3 (by simp)
    show W *ᵥ v ∈ wPoint W
    rw [mulVec_one W v h1 h2 h3]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem wPlane_coe (W : Matrix (Fin 4) (Fin 4) K) :
    (wPlane W : Set (Fin 4 → K)) = (fun v => W *ᵥ v) ''
      {v : Fin 4 → K | ∀ pos : Fin 4, pos ∉ ({0, 1} : Set (Fin 4)) → v pos = 0} := by
  ext w
  constructor
  · intro hw
    obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.mp hw
    refine ⟨Pi.single 0 c + Pi.single 1 d, ?_, ?_⟩
    · intro pos hpos
      have h0 : pos ≠ 0 := fun h => hpos (by simp [h])
      have h1 : pos ≠ 1 := fun h => hpos (by simp [h])
      simp [Pi.single_eq_of_ne h0, Pi.single_eq_of_ne h1]
    · funext i
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, Pi.single_apply, mul_comm]
  · rintro ⟨v, hv, rfl⟩
    have h2 : v 2 = 0 := hv 2 (by simp)
    have h3 : v 3 = 0 := hv 3 (by simp)
    show W *ᵥ v ∈ wPlane W
    rw [mulVec_two W v h2 h3]
    exact Submodule.mem_span_pair.mpr ⟨v 0, v 1, rfl⟩

theorem wPoint_le_wPlane (W : Matrix (Fin 4) (Fin 4) K) : wPoint W ≤ wPlane W :=
  Submodule.span_mono (by simp)

theorem eq_zero_of_mulVec_eq_zero (W : GL (Fin 4) K) {x : Fin 4 → K}
    (hx : (W : Matrix (Fin 4) (Fin 4) K) *ᵥ x = 0) : x = 0 := by
  have := congrArg (fun y => ((W⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ y) hx
  simpa [Matrix.mulVec_mulVec, ← Units.val_mul] using this

theorem finrank_wPoint (W : GL (Fin 4) K) :
    Module.finrank K (wPoint (W : Matrix (Fin 4) (Fin 4) K)) = 1 := by
  apply finrank_span_singleton
  intro h0
  have : (W : Matrix (Fin 4) (Fin 4) K) *ᵥ (Pi.single 0 1) = 0 := by
    funext i
    simpa [Matrix.mulVec_single_one] using congrFun h0 i
  have := congrFun (eq_zero_of_mulVec_eq_zero W this) 0
  simp at this

theorem finrank_wPlane (W : GL (Fin 4) K) :
    Module.finrank K (wPlane (W : Matrix (Fin 4) (Fin 4) K)) = 2 := by
  have hli : LinearIndependent K ![fun i => (W : Matrix (Fin 4) (Fin 4) K) i 0,
      fun i => (W : Matrix (Fin 4) (Fin 4) K) i 1] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 : (W : Matrix (Fin 4) (Fin 4) K) *ᵥ (Pi.single 0 s + Pi.single 1 t) = 0 := by
      funext i
      have := congrFun hst i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, Pi.single_apply]
      linear_combination this
    have h2 := eq_zero_of_mulVec_eq_zero W h1
    constructor
    · simpa using congrFun h2 0
    · simpa using congrFun h2 1
  have hrange : Set.range ![fun i => (W : Matrix (Fin 4) (Fin 4) K) i 0,
      fun i => (W : Matrix (Fin 4) (Fin 4) K) i 1] =
      ({fun i => (W : Matrix (Fin 4) (Fin 4) K) i 0, fun i => (W : Matrix (Fin 4) (Fin 4) K) i 1} :
        Set (Fin 4 → K)) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · intro hx
      rcases hx with h | h
      · exact ⟨0, h.symm⟩
      · exact ⟨1, (Set.mem_singleton_iff.mp h).symm⟩
  have := finrank_span_eq_card hli
  rw [hrange] at this
  rw [Fintype.card_fin] at this
  exact this

theorem wPlane_isotropic (h : UnitaryFieldData 2 1 K) {W : Matrix (Fin 4) (Fin 4) K}
    (hW : (W.map h.bar)ᵀ * W = antiDiag4 K) :
    ∀ v ∈ wPlane W, ∀ w ∈ wPlane W, ∑ i, v i ^ 2 * w i = 0 := by
  have hS : ∀ k l : Fin 4, ∑ i, h.bar (W i k) * W i l = antiDiag4 K k l := by
    intro k l
    have := congrFun (congrFun hW k) l
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply] using this
  have h00 := hS 0 0
  have h01 := hS 0 1
  have h10 := hS 1 0
  have h11 := hS 1 1
  simp only [antiDiag4, Fin.sum_univ_four] at h00 h01 h10 h11
  simp at h00 h01 h10 h11
  intro v hv w hw
  obtain ⟨c0, d0, rfl⟩ := Submodule.mem_span_pair.mp hv
  obtain ⟨c1, d1, rfl⟩ := Submodule.mem_span_pair.mp hw
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_four]
  simp only [← bar_eq_sq h, map_add, map_mul]
  linear_combination (h.bar c0 * c1) * h00 + (h.bar c0 * d1) * h01 + (h.bar d0 * c1) * h10 +
    (h.bar d0 * d1) * h11

end Spans

end CFSG.Quasithin.RonanF57
