module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829LN0
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.Quasithin.H13.L829N

open Matrix Module
open scoped MatrixGroups

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

private lemma s9r_sq {R : Type*} [Ring R] (h2 : ∀ y : R, y + y = 0) {x : R}
    (hx : x * x = 1) : (x - 1) * (x - 1) = 0 := by
  have e : (x - 1) * (x - 1) = x * x - (x + x) + 1 := by noncomm_ring
  rw [e, hx, h2 x, sub_zero]
  exact h2 1

private lemma s9r_add_self (A : Subalgebra (ZMod 2) (Module.End (ZMod 2) W))
    (f : Module.End A W) : f + f = 0 := by
  have h2 : ∀ v : W, v + v = 0 := fun v => by
    have h : ((1 : ZMod 2) + 1) • v = 0 := by
      rw [show ((1 : ZMod 2) + 1) = 0 from by decide, zero_smul]
    rwa [add_smul, one_smul] at h
  refine LinearMap.ext fun w => ?_
  rw [LinearMap.add_apply, LinearMap.zero_apply]
  exact h2 (f w)

@[expose] noncomputable def s9rPsi {A : Subalgebra (ZMod 2) (Module.End (ZMod 2) W)}
    {X : Submodule A W} {E : Type} [Field E] {d : ℕ}
    (σ : Module.End A X ≃+* E) (ε : W ≃ₗ[A] (Fin d → ↥X)) :
    Module.End A W ≃+* Matrix (Fin d) (Fin d) E :=
  (ε.conjRingEquiv.trans (endVecRingEquivMatrixEnd (Fin d) (↥A) (↥X))).trans
    (RingEquiv.mapMatrix σ)

private lemma s9rPsi_apply {A : Subalgebra (ZMod 2) (Module.End (ZMod 2) W)}
    {X : Submodule A W} {E : Type} [Field E] {d : ℕ}
    (σ : Module.End A X ≃+* E) (ε : W ≃ₗ[A] (Fin d → ↥X)) (F : Module.End A W) (i j : Fin d) :
    s9rPsi σ ε F i j = σ ((LinearMap.proj i : (Fin d → ↥X) →ₗ[A] ↥X) ∘ₗ ε.toLinearMap ∘ₗ F ∘ₗ
      ε.symm.toLinearMap ∘ₗ LinearMap.single A (fun _ : Fin d => ↥X) j) := rfl

private lemma s9r_factor {A : Subalgebra (ZMod 2) (Module.End (ZMod 2) W)}
    {X : Submodule A W} {E : Type} [Field E] {d : ℕ}
    (σ : Module.End A X ≃+* E) (ε : W ≃ₗ[A] (Fin d → ↥X))
    (F : Module.End A W) (Θ : Submodule A W) (hF : ∀ v, F v ∈ Θ) (θ : ↥Θ ≃ₗ[A] ↥X) :
    ∃ u μ : Fin d → E, s9rPsi σ ε F = Matrix.vecMulVec u μ := by
  obtain ⟨iota, hiota⟩ : ∃ iota : ↥X →ₗ[A] W, ∀ z : ↥Θ, iota (θ z) = (z : W) :=
    ⟨Θ.subtype ∘ₗ θ.symm.toLinearMap, fun z => by simp⟩
  obtain ⟨nu, hnu⟩ : ∃ nu : Fin d → (↥X →ₗ[A] ↥Θ), ∀ j x,
      (nu j x : W) = F (ε.symm (Pi.single j x)) :=
    ⟨fun j => LinearMap.codRestrict Θ (F ∘ₗ ε.symm.toLinearMap ∘ₗ
      LinearMap.single A (fun _ : Fin d => ↥X) j) (fun x => hF _), fun j x => rfl⟩
  refine ⟨fun i => σ ((LinearMap.proj i : (Fin d → ↥X) →ₗ[A] ↥X) ∘ₗ ε.toLinearMap ∘ₗ iota),
    fun j => σ (θ.toLinearMap ∘ₗ nu j), ?_⟩
  ext i j
  simp only [Matrix.vecMulVec_apply]
  rw [← map_mul σ, s9rPsi_apply]
  congr 1
  refine LinearMap.ext fun x => ?_
  have h1 : iota ((θ.toLinearMap ∘ₗ nu j) x) = F (ε.symm (Pi.single j x)) := by
    show iota (θ (nu j x)) = _
    rw [hiota]
    exact hnu j x
  show ε (F (ε.symm (Pi.single j x))) i = ε (iota ((θ.toLinearMap ∘ₗ nu j) x)) i
  rw [h1]

private lemma s9r_rank_one {d : ℕ} {E : Type} [Field E] (N : Matrix (Fin d) (Fin d) E)
    (u μ : Fin d → E) (hN : N = Matrix.vecMulVec u μ) (hne : N ≠ 0) : N.rank = 1 := by
  refine le_antisymm ?_ ?_
  · rw [hN]
    exact Matrix.rank_vecMulVec_le u μ
  obtain ⟨i, j, hij⟩ : ∃ i j, N i j ≠ 0 := by
    by_contra h
    exact hne (Matrix.ext fun i j => by
      by_contra hc
      exact h ⟨i, j, hc⟩)
  have hpos : 0 < N.rank := by
    unfold Matrix.rank
    rw [Module.finrank_pos_iff_exists_ne_zero]
    refine ⟨⟨N.mulVec (Pi.single j 1), LinearMap.mem_range_self N.mulVecLin (Pi.single j 1)⟩,
      fun h0 => hij ?_⟩
    have h1 : N.mulVec (Pi.single j 1) = 0 := congrArg Subtype.val h0
    have h2 := congrFun h1 i
    simpa [Matrix.mulVec_single_one] using h2
  omega

@[expose] noncomputable def s9rActA (A : Subalgebra (ZMod 2) (Module.End (ZMod 2) W))
    (g : W ≃ₗ[ZMod 2] W)
    (hg : ∀ a ∈ A, (g : Module.End (ZMod 2) W) * a = a * (g : Module.End (ZMod 2) W)) :
    W ≃ₗ[A] W where
  toFun := g
  invFun := g.symm
  map_add' := map_add g
  map_smul' := fun a x => congrArg (fun F : Module.End (ZMod 2) W => F x)
    (hg (a : Module.End (ZMod 2) W) a.2)
  left_inv := fun x => g.symm_apply_apply x
  right_inv := fun x => g.apply_symm_apply x

@[expose] noncomputable def s9rHom (A : Subalgebra (ZMod 2) (Module.End (ZMod 2) W))
    (G' : Subgroup (W ≃ₗ[ZMod 2] W))
    (hG' : ∀ g ∈ G', ∀ a ∈ A, (g : Module.End (ZMod 2) W) * a = a * (g : Module.End (ZMod 2) W)) :
    G' →* (W ≃ₗ[A] W) where
  toFun g := s9rActA A g.1 (hG' g.1 g.2)
  map_one' := LinearEquiv.ext fun _ => rfl
  map_mul' _ _ := LinearEquiv.ext fun _ => rfl

@[expose] noncomputable def s9rPhi (A : Subalgebra (ZMod 2) (Module.End (ZMod 2) W))
    {X : Submodule A W} {E : Type} [Field E] {d : ℕ}
    (σ : Module.End A X ≃+* E) (ε : W ≃ₗ[A] (Fin d → ↥X))
    (G' : Subgroup (W ≃ₗ[ZMod 2] W))
    (hG' : ∀ g ∈ G', ∀ a ∈ A, (g : Module.End (ZMod 2) W) * a = a * (g : Module.End (ZMod 2) W)) :
    G' →* GL (Fin d) E :=
  (Units.map (s9rPsi σ ε).toMonoidHom).comp
    (((LinearMap.GeneralLinearGroup.generalLinearEquiv (↥A) W).symm.toMonoidHom).comp
      (s9rHom A G' hG'))

theorem s9rPhi_val (A : Subalgebra (ZMod 2) (Module.End (ZMod 2) W))
    {X : Submodule A W} {E : Type} [Field E] {d : ℕ}
    (σ : Module.End A X ≃+* E) (ε : W ≃ₗ[A] (Fin d → ↥X))
    (G' : Subgroup (W ≃ₗ[ZMod 2] W))
    (hG' : ∀ g ∈ G', ∀ a ∈ A, (g : Module.End (ZMod 2) W) * a = a * (g : Module.End (ZMod 2) W))
    (g : ↥G') :
    ((s9rPhi A σ ε G' hG' g : GL (Fin d) E) : Matrix (Fin d) (Fin d) E) =
      s9rPsi σ ε ((s9rHom A G' hG' g : W ≃ₗ[A] W) : Module.End A W) := rfl

theorem s9r_inj_phi (A : Subalgebra (ZMod 2) (Module.End (ZMod 2) W))
    {X : Submodule A W} {E : Type} [Field E] {d : ℕ} (σ : Module.End A X ≃+* E)
    (ε : W ≃ₗ[A] (Fin d → ↥X)) (G' : Subgroup (W ≃ₗ[ZMod 2] W))
    (hG' : ∀ g ∈ G', ∀ a ∈ A, (g : Module.End (ZMod 2) W) * a = a * (g : Module.End (ZMod 2) W)) :
    Function.Injective (s9rPhi A σ ε G' hG') := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have h1 := congrArg Units.val hg
  rw [Units.val_one, s9rPhi_val] at h1
  have hx : ((s9rHom A G' hG' g : W ≃ₗ[A] W) : Module.End A W) = 1 :=
    (s9rPsi σ ε).injective (h1.trans (map_one (s9rPsi σ ε)).symm)
  refine Subtype.ext (LinearEquiv.ext fun w => ?_)
  have hw := congrArg (fun F : Module.End A W => F w) hx
  exact hw

theorem s9r_transv_phi (A : Subalgebra (ZMod 2) (Module.End (ZMod 2) W))
    {X : Submodule A W} {E : Type} [Field E] {d : ℕ} (σ : Module.End A X ≃+* E)
    (ε : W ≃ₗ[A] (Fin d → ↥X)) (G' : Subgroup (W ≃ₗ[ZMod 2] W))
    (hG' : ∀ g ∈ G', ∀ a ∈ A, (g : Module.End (ZMod 2) W) * a = a * (g : Module.End (ZMod 2) W))
    (g : ↥G') (hg1 : g ≠ 1) (hg2 : (g : W ≃ₗ[ZMod 2] W) * g = 1)
    (hΘex : ∃ Θ : Submodule A W, (∀ w, w ∈ Θ ↔ ∃ u, (g : W ≃ₗ[ZMod 2] W) u - u = w) ∧
      Nonempty (↥Θ ≃ₗ[A] ↥X)) :
    IsTransvectionK (s9rPhi A σ ε G' hG' g : GL (Fin d) E) := by
  obtain ⟨Θ, hΘ, ⟨θ⟩⟩ := hΘex
  obtain ⟨x, hxdef⟩ : ∃ x : Module.End A W,
      x = ((s9rHom A G' hG' g : W ≃ₗ[A] W) : Module.End A W) := ⟨_, rfl⟩
  have hxw : ∀ w : W, x w = (g : W ≃ₗ[ZMod 2] W) w := fun w => by
    rw [hxdef] <;> rfl
  have hval : ((s9rPhi A σ ε G' hG' g : GL (Fin d) E) : Matrix (Fin d) (Fin d) E) =
      s9rPsi σ ε x := by
    rw [s9rPhi_val, hxdef]
  have hgg : ∀ w : W, (g : W ≃ₗ[ZMod 2] W) ((g : W ≃ₗ[ZMod 2] W) w) = w := fun w => by
    have hw := congrArg (fun h : W ≃ₗ[ZMod 2] W => h w) hg2
    exact hw
  have hxx : x * x = 1 := by
    refine LinearMap.ext fun w => ?_
    show x (x w) = w
    rw [hxw, hxw]
    exact hgg w
  have hgne : (g : W ≃ₗ[ZMod 2] W) ≠ 1 := fun h => hg1 (Subtype.ext h)
  have hxne : x ≠ 1 := by
    intro h
    apply hgne
    refine LinearEquiv.ext fun w => ?_
    have hw : x w = w := by rw [h] <;> rfl
    exact (hxw w).symm.trans hw
  have hF : ∀ v : W, (x - 1 : Module.End A W) v ∈ Θ := fun v => by
    refine (hΘ _).mpr ⟨v, ?_⟩
    rw [LinearMap.sub_apply, Module.End.one_apply, hxw]
  have hF0 : x - 1 ≠ 0 := fun h => hxne (sub_eq_zero.mp h)
  have hsq : (x - 1) * (x - 1) = 0 := s9r_sq (s9r_add_self A) hxx
  have hΨsq : s9rPsi σ ε (x - 1) * s9rPsi σ ε (x - 1) = 0 := by
    rw [← map_mul, hsq, map_zero]
  have hΨne : s9rPsi σ ε (x - 1) ≠ 0 := fun h =>
    hF0 ((s9rPsi σ ε).injective (h.trans (map_zero (s9rPsi σ ε)).symm))
  obtain ⟨u, μ, hfac⟩ := s9r_factor σ ε (x - 1) Θ hF θ
  have hrank : (s9rPsi σ ε (x - 1)).rank = 1 := s9r_rank_one _ u μ hfac hΨne
  have hT : ((s9rPhi A σ ε G' hG' g : GL (Fin d) E) : Matrix (Fin d) (Fin d) E) - 1 =
      s9rPsi σ ε (x - 1) := by
    rw [hval, map_sub, map_one]
  unfold IsTransvectionK
  refine ⟨?_, ?_, ?_⟩
  · have hne := (s9r_inj_phi A σ ε G' hG').ne hg1
    rwa [map_one] at hne
  · rw [hT]
    exact hΨsq
  · rw [hT]
    exact hrank

end CFSG.Quasithin.H13.L829N
