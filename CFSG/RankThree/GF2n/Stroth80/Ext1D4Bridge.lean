module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import CFSG.LinearAlgebra.IndexAverageProjection
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Matrix.ToLin

public section

namespace CFSG.RankThree.GF2n.Stroth80.Ext1D4

open Matrix

variable {K : Type*} [Field K] {E : Type*} [AddCommGroup E] [Module K E]
  {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

noncomputable def basisOfLifts {A : Submodule K E} (bA : Module.Basis ι K A)
    (bQ : Module.Basis κ K (E ⧸ A)) (f : κ → E) (hf : ∀ j, A.mkQ (f j) = bQ j) :
    Module.Basis (ι ⊕ κ) K E := by
  let b : ι ⊕ κ → E := Sum.elim (fun i ↦ bA i) f
  have br : A.mkQ ∘ b ∘ Sum.inr = bQ := funext hf
  apply Module.Basis.mk (v := b)
  · apply LinearIndependent.sumElim_of_quotient
    · exact bA.linearIndependent
    · convert! bQ.linearIndependent
  · unfold b
    rw [Set.Sum.elim_range, Submodule.span_union,
      show Set.range (fun i ↦ (bA i : E)) = A.subtype '' (Set.range (fun i ↦ bA i)) by aesop,
      ← Submodule.map_span, bA.span_eq, Submodule.map_top, Submodule.range_subtype, top_le_iff,
      ← Submodule.map_mkQ_eq_top, Submodule.map_span, ← Set.range_comp]
    rw [show A.mkQ ∘ f = bQ from funext hf, bQ.span_eq]

section Lifts

variable {A : Submodule K E} (bA : Module.Basis ι K A) (bQ : Module.Basis κ K (E ⧸ A))
  (f : κ → E) (hf : ∀ j, A.mkQ (f j) = bQ j)

theorem basisOfLifts_inl (i : ι) : basisOfLifts bA bQ f hf (Sum.inl i) = bA i := by
  simp [basisOfLifts]

theorem basisOfLifts_inr (j : κ) : basisOfLifts bA bQ f hf (Sum.inr j) = f j := by
  simp [basisOfLifts]

theorem basisOfLifts_repr_inr (v : E) (j : κ) :
    (basisOfLifts bA bQ f hf).repr v (Sum.inr j) = bQ.repr (A.mkQ v) j := by
  classical
  have key : (basisOfLifts bA bQ f hf).coord (Sum.inr j) = (bQ.coord j).comp A.mkQ := by
    refine (basisOfLifts bA bQ f hf).ext fun k => ?_
    rcases k with i | j'
    · rw [Module.Basis.coord_apply, Module.Basis.repr_self, LinearMap.comp_apply,
        basisOfLifts_inl, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero A).2 (bA i).2,
        map_zero]
      simp
    · rw [Module.Basis.coord_apply, Module.Basis.repr_self, LinearMap.comp_apply,
        basisOfLifts_inr, hf, Module.Basis.coord_apply, Module.Basis.repr_self]
      by_cases h : j' = j
      · subst h; simp
      · simp [Finsupp.single_apply, h]
  exact LinearMap.congr_fun key v

theorem basisOfLifts_repr_inl_of_mem (v : E) (hv : v ∈ A) (i : ι) :
    (basisOfLifts bA bQ f hf).repr v (Sum.inl i) = bA.repr ⟨v, hv⟩ i := by
  classical
  have key : ((basisOfLifts bA bQ f hf).coord (Sum.inl i)).comp A.subtype = bA.coord i := by
    refine bA.ext fun i' => ?_
    rw [LinearMap.comp_apply, Module.Basis.coord_apply, Submodule.subtype_apply,
      ← basisOfLifts_inl bA bQ f hf i', Module.Basis.repr_self, Module.Basis.coord_apply,
      Module.Basis.repr_self]
    by_cases h : i' = i
    · subst h; simp
    · simp [Finsupp.single_apply, h]
  exact LinearMap.congr_fun key ⟨v, hv⟩

theorem mem_iff_basisOfLifts_repr_inr (v : E) :
    v ∈ A ↔ ∀ j, (basisOfLifts bA bQ f hf).repr v (Sum.inr j) = 0 := by
  simp only [basisOfLifts_repr_inr]
  constructor
  · intro hv j
    rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero A).2 hv, map_zero,
      Finsupp.zero_apply]
  · intro h
    have h0 : bQ.repr (A.mkQ v) = 0 := Finsupp.ext h
    rw [LinearEquiv.map_eq_zero_iff, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
    exact h0

theorem toMatrix_basisOfLifts (g : Module.End K E) (hgA : ∀ a ∈ A, g a ∈ A)
    (P₁ : Matrix ι ι K) (hP₁ : ∀ j, g (bA j) = ∑ i, P₁ i j • (bA i : E))
    (P₂ : Matrix κ κ K) (hP₂ : ∀ j, A.mkQ (g (f j)) = ∑ i, P₂ i j • bQ i) :
    LinearMap.toMatrix (basisOfLifts bA bQ f hf) (basisOfLifts bA bQ f hf) g =
      fromBlocks P₁ (LinearMap.toMatrix (basisOfLifts bA bQ f hf)
        (basisOfLifts bA bQ f hf) g).toBlocks₁₂ 0 P₂ := by
  set b := basisOfLifts bA bQ f hf
  rw [← fromBlocks_toBlocks (LinearMap.toMatrix b b g)]
  congr 1
  · ext i j
    rw [toBlocks₁₁, of_apply, LinearMap.toMatrix_apply, basisOfLifts_inl,
      basisOfLifts_repr_inl_of_mem bA bQ f hf _ (hgA _ (bA j).2)]
    have : (⟨g (bA j), hgA _ (bA j).2⟩ : A) = ∑ i', P₁ i' j • bA i' :=
      Subtype.ext (by rw [Submodule.coe_sum]; simp only [Submodule.coe_smul]; exact hP₁ j)
    rw [this, Module.Basis.repr_sum_self]
  · ext i j
    rw [toBlocks₂₁, of_apply, LinearMap.toMatrix_apply, basisOfLifts_inl,
      basisOfLifts_repr_inr, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero A).2
        (hgA _ (bA j).2), map_zero, Finsupp.zero_apply, zero_apply]
  · ext i j
    rw [toBlocks₂₂, of_apply, LinearMap.toMatrix_apply, basisOfLifts_inr, basisOfLifts_repr_inr,
      hP₂, Module.Basis.repr_sum_self]

theorem toBlocks₁₂_basisOfLifts_eq_zero (g : Module.End K E) (d : κ → K)
    (hg : ∀ j, g (f j) = d j • f j) :
    (LinearMap.toMatrix (basisOfLifts bA bQ f hf) (basisOfLifts bA bQ f hf) g).toBlocks₁₂ = 0 := by
  ext i j
  rw [toBlocks₁₂, of_apply, LinearMap.toMatrix_apply, basisOfLifts_inr, hg, map_smul,
    ← basisOfLifts_inr bA bQ f hf j, Module.Basis.repr_self, Finsupp.smul_apply, zero_apply]
  simp

end Lifts

theorem exists_weight_lifts {Z : Type*} [Group Z] [Finite Z] (hZ : (Nat.card Z : K) ≠ 0)
    (σ : Z →* Module.End K E) (A : Submodule K E) (hA : ∀ z, ∀ a ∈ A, σ z a ∈ A)
    (bQ : Module.Basis κ K (E ⧸ A)) (d : Z → κ → K)
    (hd : ∀ z j (e : E), A.mkQ e = bQ j → A.mkQ (σ z e) = d z j • bQ j) :
    ∃ f : κ → E, (∀ j, A.mkQ (f j) = bQ j) ∧ ∀ z j, σ z (f j) = d z j • f j := by
  classical
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl A
  set p := Submodule.projection A C hC
  have hpA : ∀ v, p v ∈ A := fun v => Submodule.projection_apply_mem hC v
  have hpid : ∀ a ∈ A, p a = a := fun a ha => Submodule.projection_apply_of_mem_left hC ha
  obtain ⟨p', hp'A, hp'id, hp'G⟩ :=
    CFSG.LinearAlgebra.IndexAverage.exists_equivariant_projection_of_index σ ⊥
      (by rw [Subgroup.index_bot]; exact hZ) A hA p hpA hpid
      (fun h hh v => by rw [Subgroup.mem_bot.1 hh, map_one]; rfl)
  choose e he using fun j => Submodule.mkQ_surjective A (bQ j)
  have hmk : ∀ j, A.mkQ (e j - p' (e j)) = bQ j := fun j => by
    rw [map_sub, he, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero A).2 (hp'A _), sub_zero]
  have hp'f : ∀ j, p' (e j - p' (e j)) = 0 := fun j => by
    rw [map_sub, hp'id _ (hp'A _), sub_self]
  refine ⟨fun j => e j - p' (e j), hmk, fun z j => ?_⟩
  set w := σ z (e j - p' (e j)) - d z j • (e j - p' (e j)) with hw_def
  have hw : w ∈ A := by
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, hw_def, map_sub, map_smul,
      hd z j _ (hmk j), hmk j, sub_self]
  have hpw : p' w = 0 := by
    rw [hw_def, map_sub, map_smul, hp'G, hp'f, map_zero, smul_zero, sub_zero]
  have h0 := hp'id w hw
  rw [hpw] at h0
  exact sub_eq_zero.1 h0.symm

end CFSG.RankThree.GF2n.Stroth80.Ext1D4
