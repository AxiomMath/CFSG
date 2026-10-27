module

public import CFSG.LocalAnalysis.StandardType.GGTBJOmDefs
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.Algebra.Module.Submodule.Equiv

public section

open Module Multiplicative QuadraticMap Polynomial

namespace CFSG.StandardType

namespace OrthTorus

open SpCoord
open CFSG.RankThree.Classical2 (orthDerived)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p r : ℕ} {A : Subgroup (V ≃ₗ[K] V)}

theorem TBJOmData.tau_mulSingle_apply_iff [Fact p.Prime]
    (Δ : TBJOmData Q p A r) (i : Fin r) (v : V) :
    Δ.τ (Pi.mulSingle i (ofAdd (1 : ZMod p))) v = v ↔
      ∀ u ∈ Δ.F.U i, polar Q u v = 0 := by
  rw [Δ.τ_eq, Δ.F.fix]
  constructor
  · intro h u hu
    refine h i ?_ u hu
    simp [piMul_apply, toAdd_ofAdd]
  · intro h j hj u hu
    by_cases hji : j = i
    · subst hji
      exact h u hu
    · rw [piMul_apply, toAdd_ofAdd, Pi.mulSingle_eq_of_ne hji, toAdd_one] at hj
      exact (hj rfl).elim

private theorem TBJOmData.mapsTo_orthogonal_inv_of_conj_tau_mulSingle [Fact p.Prime]
    (Δ : TBJOmData Q p A r) {i k : Fin r} {w : V ≃ₗ[K] V}
    (hwconj : w * Δ.τ (Pi.mulSingle i (ofAdd (1 : ZMod p))) * w⁻¹ =
      Δ.τ (Pi.mulSingle k (ofAdd (1 : ZMod p)))) :
    ∀ v, (∀ u ∈ Δ.F.U k, polar Q u v = 0) →
      ∀ u ∈ Δ.F.U i, polar Q u (w.symm v) = 0 := by
  intro v hv u hu
  have hvek : Δ.τ (Pi.mulSingle k (ofAdd (1 : ZMod p))) v = v :=
    (Δ.tau_mulSingle_apply_iff k v).mpr hv
  have hconj : w⁻¹ * Δ.τ (Pi.mulSingle k (ofAdd (1 : ZMod p))) * w =
      Δ.τ (Pi.mulSingle i (ofAdd (1 : ZMod p))) := by
    rw [← hwconj]
    group
  have hvei : Δ.τ (Pi.mulSingle i (ofAdd (1 : ZMod p))) (w.symm v) = w.symm v := by
    have h := congrArg (fun g : V ≃ₗ[K] V => g (w.symm v)) hconj
    have h' : w.symm v = Δ.τ (Pi.mulSingle i (ofAdd (1 : ZMod p))) (w.symm v) := by
      simpa [LinearEquiv.mul_apply, hvek] using h
    exact h'.symm
  exact (Δ.tau_mulSingle_apply_iff i (w.symm v)).mp hvei u hu

theorem TBJOmData.mapsTo_piece_of_conj_tau_mulSingle [Fact p.Prime]
    (Δ : TBJOmData Q p A r) (hQ : (polarBilin Q).Nondegenerate) {i k : Fin r}
    {w : V ≃ₗ[K] V} (hwO : w ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hwconj : w * Δ.τ (Pi.mulSingle i (ofAdd (1 : ZMod p))) * w⁻¹ =
      Δ.τ (Pi.mulSingle k (ofAdd (1 : ZMod p)))) :
    ∀ u ∈ Δ.F.U i, w u ∈ Δ.F.U k := by
  intro u hu
  have hmem : w u ∈ LinearMap.BilinForm.orthogonal (polarBilin Q)
      (LinearMap.BilinForm.orthogonal (polarBilin Q) (Δ.F.U k)) := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro x hx
    rw [polarBilin_apply_apply, QuadraticMap.polar_comm Q x (w u)]
    have hxorth : ∀ y ∈ Δ.F.U k, polar Q y x = 0 := by
      simpa [polarBilin_apply_apply] using hx
    have hv : ∀ y ∈ Δ.F.U i, polar Q y (w.symm x) = 0 :=
      Δ.mapsTo_orthogonal_inv_of_conj_tau_mulSingle hwconj x hxorth
    calc polar Q (w u) x = polar Q (w u) (w (w.symm x)) := by rw [w.apply_symm_apply]
      _ = polar Q u (w.symm x) :=
        TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hwO u (w.symm x)
      _ = 0 := hv u hu
  rwa [LinearMap.BilinForm.orthogonal_orthogonal hQ
    (QuadraticMap.isSymm_polarBilin Q).isRefl (Δ.F.U k)] at hmem

theorem TBJOmData.map_piece_eq_of_conj_tau_mulSingle [Fact p.Prime]
    (Δ : TBJOmData Q p A r) (hQ : (polarBilin Q).Nondegenerate) {i k : Fin r}
    {w : V ≃ₗ[K] V} (hwO : w ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hwconj : w * Δ.τ (Pi.mulSingle i (ofAdd (1 : ZMod p))) * w⁻¹ =
      Δ.τ (Pi.mulSingle k (ofAdd (1 : ZMod p)))) :
    Submodule.map w.toLinearMap (Δ.F.U i) = Δ.F.U k := by
  refine le_antisymm ?_ ?_
  · rintro v ⟨u, hu, rfl⟩
    exact Δ.mapsTo_piece_of_conj_tau_mulSingle hQ hwO hwconj u hu
  · intro v hv
    have hconj : w⁻¹ * Δ.τ (Pi.mulSingle k (ofAdd (1 : ZMod p))) * w =
        Δ.τ (Pi.mulSingle i (ofAdd (1 : ZMod p))) := by
      rw [← hwconj]
      group
    refine ⟨w.symm v, ?_, w.apply_symm_apply v⟩
    exact Δ.mapsTo_piece_of_conj_tau_mulSingle hQ
      ((TauCeti.QuadraticMap.orthogonalGroup Q).inv_mem hwO) hconj v hv

@[expose] def TBJOmData.pieceAction (Δ : TBJOmData Q p A r)
    (f : Fin r → Multiplicative (ZMod p)) (i : Fin r) (u : Δ.F.U i) : Δ.F.U i :=
  ⟨Δ.τ f (u : V), by
    rw [Δ.τ_eq]
    exact Δ.F.mapsTo (piMul r p f) i (u : V) u.2⟩

@[simp]
theorem TBJOmData.pieceAction_coe (Δ : TBJOmData Q p A r)
    (f : Fin r → Multiplicative (ZMod p)) (i : Fin r) (u : Δ.F.U i) :
    ((Δ.pieceAction f i u : Δ.F.U i) : V) = Δ.τ f (u : V) :=
  rfl

structure PlaneMoveData (Δ : TBJOmData Q p A r) (o i : Fin r) where
  w : V ≃ₗ[K] V
  mem_orthogonal : w ∈ TauCeti.QuadraticMap.orthogonalGroup Q
  map_piece : Submodule.map w.toLinearMap (Δ.F.U o) = Δ.F.U i
  conj : ∀ f : Fin r → Multiplicative (ZMod p),
    w * Δ.τ f * w⁻¹ = Δ.τ (SpCoord.permAut (Equiv.swap o i) f)
  fix_orthogonal : ∀ v : V, (∀ u ∈ Δ.F.U o, polar Q u v = 0) →
    (∀ u ∈ Δ.F.U i, polar Q u v = 0) → w v = v
  eq_one_of_eq : i = o → w = 1

theorem exists_planeMoveData [Fact p.Prime]
    (Δ : TBJOmData Q p A r) (hQ : (polarBilin Q).Nondegenerate) (o i : Fin r) :
    Nonempty (PlaneMoveData Δ o i) := by
  by_cases hio : i = o
  · subst hio
    refine ⟨⟨1, ?_, ?_, ?_, ?_, ?_⟩⟩
    · simp
    · simp
    · intro f
      simp [Equiv.swap_self, SpCoord.permAut_apply]
    · intro v _ _
      rfl
    · intro _
      rfl
  · obtain ⟨w, hwΩ, hfix, hwconj⟩ := Δ.swapMove o i (Ne.symm hio)
    have hwO : w ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
      Subgroup.commutator_le_self (TauCeti.QuadraticMap.orthogonalGroup Q) hwΩ
    have hgen : w * Δ.τ (Pi.mulSingle o (ofAdd (1 : ZMod p))) * w⁻¹ =
        Δ.τ (Pi.mulSingle i (ofAdd (1 : ZMod p))) := by
      rw [hwconj, SpCoord.permAut_mulSingle, Equiv.swap_apply_left]
    refine ⟨⟨w, hwO, Δ.map_piece_eq_of_conj_tau_mulSingle hQ hwO hgen, hwconj, hfix,
      fun h => absurd h hio⟩⟩

@[expose] noncomputable def TBJOmData.planeMove [Fact p.Prime] (Δ : TBJOmData Q p A r)
    (hQ : (polarBilin Q).Nondegenerate) (o i : Fin r) : V ≃ₗ[K] V :=
  (Classical.choice (exists_planeMoveData Δ hQ o i)).w

theorem TBJOmData.planeMove_mem_orthogonal [Fact p.Prime] (Δ : TBJOmData Q p A r)
    (hQ : (polarBilin Q).Nondegenerate) (o i : Fin r) :
    Δ.planeMove hQ o i ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  (Classical.choice (exists_planeMoveData Δ hQ o i)).mem_orthogonal

theorem TBJOmData.planeMove_map_piece [Fact p.Prime] (Δ : TBJOmData Q p A r)
    (hQ : (polarBilin Q).Nondegenerate) (o i : Fin r) :
    Submodule.map (Δ.planeMove hQ o i).toLinearMap (Δ.F.U o) = Δ.F.U i :=
  (Classical.choice (exists_planeMoveData Δ hQ o i)).map_piece

@[expose] noncomputable def TBJOmData.planeIsometry [Fact p.Prime] (Δ : TBJOmData Q p A r)
    (hQ : (polarBilin Q).Nondegenerate) (o i : Fin r) :
    (Q.comp (Δ.F.U o).subtype).IsometryEquiv (Q.comp (Δ.F.U i).subtype) where
  toLinearEquiv :=
    (Δ.planeMove hQ o i).ofSubmodules (Δ.F.U o) (Δ.F.U i) (Δ.planeMove_map_piece hQ o i)
  map_app' := fun u => by
    change Q ((((Δ.planeMove hQ o i).ofSubmodules (Δ.F.U o) (Δ.F.U i)
      (Δ.planeMove_map_piece hQ o i)) u : Δ.F.U i) : V) = Q (u : V)
    rw [LinearEquiv.ofSubmodules_apply]
    exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
      (Δ.planeMove_mem_orthogonal hQ o i) (u : V)

@[simp]
theorem TBJOmData.planeIsometry_coe [Fact p.Prime] (Δ : TBJOmData Q p A r)
    (hQ : (polarBilin Q).Nondegenerate) (o i : Fin r) (u : Δ.F.U o) :
    ((Δ.planeIsometry hQ o i u : Δ.F.U i) : V) =
      Δ.planeMove hQ o i (u : V) :=
  rfl

end OrthTorus

end CFSG.StandardType

end
