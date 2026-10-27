module

public import CFSG.LocalAnalysis.StandardType.GGOrthRk1Pieces
public import CFSG.LocalAnalysis.StandardType.GGOrthRk1Model
import Mathlib.LinearAlgebra.FixedSubmodule

public section

open Module Multiplicative

namespace CFSG.StandardType

namespace OrthTorus

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}

omit [Finite K] in
theorem TBJOmData.exists_rk1_theta (Δ : TBJOmData Q p A r)
    (hfix : ∀ v : V, (∀ a ∈ A, a v = v) → v = 0) (i j : Fin r) (hij : i ≠ j)
    (φ : (Δ.D × Δ.D) →ₗ[K] V) (hφ : Function.Injective φ)
    (hφr : LinearMap.range φ = Δ.F.U i ⊔ Δ.F.U j)
    (hφQ : ∀ v : Δ.D × Δ.D, Q (φ v) = rk1Omega Δ.finrank_D v.1 v.2)
    (hφτ : ∀ f ∈ reflFixedCoord p r i j, ∀ v : Δ.D × Δ.D,
      Δ.τ f (φ v) = φ ((Δ.c ^ (toAdd (f i)).val) v.1, (Δ.c ^ (toAdd (f i)).val) v.2)) :
    ∃ θ : Matrix.SpecialLinearGroup (Fin 2) K →* (V ≃ₗ[K] V),
      (∀ g v, θ g (φ v) = φ (rk1ModelAct g v)) ∧
      (∀ g, ∀ k : Fin r, k ≠ i → k ≠ j → ∀ u ∈ Δ.F.U k, θ g u = u) ∧
      Function.Injective θ ∧
      (∀ g, θ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) ∧
      (∀ g, θ g ∈ Subgroup.centralizer (Δ.reflFixed i j : Set (V ≃ₗ[K] V))) ∧
      ∀ (y : V ≃ₗ[K] V) (g : Matrix.SpecialLinearGroup (Fin 2) K),
        (∀ k : Fin r, k ≠ i → k ≠ j → ∀ u ∈ Δ.F.U k, y u = u) →
        (∀ v, y (φ v) = φ (rk1ModelAct g v)) → y = θ g := by
  classical
  let S : Set (Fin r) := {k | k ≠ i ∧ k ≠ j}
  let W : Submodule K V := Δ.F.U i ⊔ Δ.F.U j
  let W' : Submodule K V := ⨆ k ∈ S, Δ.F.U k
  have hdisjmem : ∀ x ∈ W, x ∈ W' → x = 0 := by
    intro x hx hx'
    change x ∈ Δ.F.U i ⊔ Δ.F.U j at hx
    change x ∈ (⨆ k ∈ S, Δ.F.U k) at hx'
    have hst : Disjoint ({i, j} : Set (Fin r)) S := by
      rw [Set.disjoint_left]
      intro y hy hyS
      rcases hy with rfl | rfl
      · exact hyS.1 rfl
      · exact hyS.2 rfl
    have h := Δ.iSupIndep_U.disjoint_biSup_biSup' (s := ({i, j} : Set (Fin r))) (t := S)
      hst (Set.toFinite _)
    rw [iSup_pair] at h
    exact Submodule.disjoint_def.mp h x hx hx'
  have hsup : W ⊔ W' = ⊤ := by
    rw [← Δ.iSup_U_eq_top hfix]
    refine le_antisymm ?_ ?_
    · apply sup_le
      · change Δ.F.U i ⊔ Δ.F.U j ≤ ⨆ k, Δ.F.U k
        exact sup_le (le_iSup _ i) (le_iSup _ j)
      · change (⨆ k ∈ S, Δ.F.U k) ≤ ⨆ k, Δ.F.U k
        apply iSup_le; intro k
        apply iSup_le; intro _
        exact le_iSup _ k
    · apply iSup_le; intro k
      by_cases hki : k = i
      · subst hki
        exact le_sup_of_le_left le_sup_left
      · by_cases hkj : k = j
        · subst hkj
          exact le_sup_of_le_left le_sup_right
        · exact le_trans (le_iSup_of_le k (le_iSup (fun _ : k ∈ S => Δ.F.U k)
              (show k ∈ S from ⟨hki, hkj⟩))) le_sup_right
  have hφmem : ∀ y : Δ.D × Δ.D, φ y ∈ W := by
    intro y
    change φ y ∈ Δ.F.U i ⊔ Δ.F.U j
    rw [← hφr]
    exact LinearMap.mem_range_self φ y
  have hsurj : Function.Surjective (W.subtype.coprod W'.subtype : W × W' →ₗ[K] V) := by
    intro v
    have hv : v ∈ W ⊔ W' := by rw [hsup]; trivial
    obtain ⟨w, hw, w', hw', hsum⟩ := Submodule.mem_sup.mp hv
    exact ⟨(⟨w, hw⟩, ⟨w', hw'⟩), by rw [LinearMap.coprod_apply]; exact hsum⟩
  have hinj : Function.Injective (W.subtype.coprod W'.subtype : W × W' →ₗ[K] V) := by
    intro p q hpq
    change (p.1 : V) + (p.2 : V) = (q.1 : V) + (q.2 : V) at hpq
    have hmemW : ((p.1 : V) - q.1) ∈ W := W.sub_mem p.1.2 q.1.2
    have hmemW' : ((p.1 : V) - q.1) ∈ W' := by
      have heq : (p.1 : V) - q.1 = (q.2 : V) - p.2 := by
        rw [sub_eq_sub_iff_add_eq_add, hpq, add_comm]
      rw [heq]
      exact W'.sub_mem q.2.2 p.2.2
    have h0 : (p.1 : V) - q.1 = 0 := hdisjmem _ hmemW hmemW'
    have hpq1 : p.1 = q.1 := Subtype.ext (sub_eq_zero.mp h0)
    have hpq2 : p.2 = q.2 := by
      rw [show (p.1 : V) = (q.1 : V) from congrArg Subtype.val hpq1] at hpq
      exact Subtype.ext (add_left_cancel hpq)
    exact Prod.ext hpq1 hpq2
  let P : (W × W') ≃ₗ[K] V :=
    LinearEquiv.ofBijective (W.subtype.coprod W'.subtype) ⟨hinj, hsurj⟩
  have P_apply : ∀ (x : W) (y : W'), P (x, y) = (x : V) + (y : V) := by
    intro x y
    exact LinearMap.coprod_apply W.subtype W'.subtype (x, y)
  let eW : (Δ.D × Δ.D) ≃ₗ[K] W :=
    (LinearEquiv.ofInjective φ hφ).trans (LinearEquiv.ofEq (LinearMap.range φ) W hφr)
  have eW_apply : ∀ v : Δ.D × Δ.D, (eW v : V) = φ v := by
    intro v
    simp only [eW, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply,
      LinearEquiv.ofInjective_apply]
  let L := (eW.prodCongr (LinearEquiv.refl K W')).trans P
  have L_apply : ∀ (x : Δ.D × Δ.D) (y : W'), L (x, y) = φ x + (y : V) := by
    intro x y
    simp only [L, LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
      LinearEquiv.refl_apply, P_apply, eW_apply]
  have L_symm_phi : ∀ v : Δ.D × Δ.D, L.symm (φ v) = (v, 0) := by
    intro v
    apply L.injective
    rw [L.apply_symm_apply, L_apply]
    simp
  have L_symm_right : ∀ (u : V) (hu : u ∈ W'), L.symm u = ((0 : Δ.D × Δ.D), ⟨u, hu⟩) := by
    intro u hu
    apply L.injective
    rw [L.apply_symm_apply, L_apply]
    simp
  let θ : Matrix.SpecialLinearGroup (Fin 2) K →* (V ≃ₗ[K] V) :=
    MonoidHom.mk'
      (fun g => L.symm.trans (((rk1ModelAct g).prodCongr (LinearEquiv.refl K W')).trans L))
      (by
        intro g h
        ext v
        simp only [LinearEquiv.trans_apply, LinearEquiv.mul_apply, map_mul,
          LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply,
          LinearEquiv.symm_apply_apply])
  have θ_apply : ∀ (g : Matrix.SpecialLinearGroup (Fin 2) K) (v : V),
      θ g v = φ (rk1ModelAct g (L.symm v).1) + ((L.symm v).2 : V) := by
    intro g v
    change (L.symm.trans (((rk1ModelAct g).prodCongr (LinearEquiv.refl K W')).trans L)) v = _
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
      LinearEquiv.refl_apply, L_apply]
  have θ_apply_phi : ∀ (g : Matrix.SpecialLinearGroup (Fin 2) K) (v : Δ.D × Δ.D),
      θ g (φ v) = φ (rk1ModelAct g v) := by
    intro g v
    rw [θ_apply, L_symm_phi]
    simp
  have θ_apply_right : ∀ (g : Matrix.SpecialLinearGroup (Fin 2) K) (u : V), u ∈ W' → θ g u = u := by
    intro g u hu
    rw [θ_apply, L_symm_right u hu]
    simp
  have θ_apply_Uk : ∀ (g : Matrix.SpecialLinearGroup (Fin 2) K) (k : Fin r), k ≠ i → k ≠ j →
      ∀ u ∈ Δ.F.U k, θ g u = u := by
    intro g k hki hkj u hu
    have hUk : Δ.F.U k ≤ W' :=
      le_iSup_of_le k (le_iSup (fun _ : k ∈ S => Δ.F.U k) (show k ∈ S from ⟨hki, hkj⟩))
    exact θ_apply_right g u (hUk hu)
  have hW_W'_polar : ∀ u ∈ W, ∀ v ∈ W', QuadraticMap.polar Q u v = 0 := by
    intro u hu v hv
    change u ∈ Δ.F.U i ⊔ Δ.F.U j at hu
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Submodule.mem_sup.mp hu
    have hker₁ : v ∈ LinearMap.ker (QuadraticMap.polarBilin Q u₁) := by
      have hle : W' ≤ LinearMap.ker (QuadraticMap.polarBilin Q u₁) := by
        change (⨆ k ∈ S, Δ.F.U k) ≤ LinearMap.ker (QuadraticMap.polarBilin Q u₁)
        apply iSup_le; intro k
        apply iSup_le; intro hk z hz
        rw [LinearMap.mem_ker, QuadraticMap.polarBilin_apply_apply]
        exact Δ.F.orth i k hk.1.symm u₁ hu₁ z hz
      exact hle hv
    have hker₂ : v ∈ LinearMap.ker (QuadraticMap.polarBilin Q u₂) := by
      have hle : W' ≤ LinearMap.ker (QuadraticMap.polarBilin Q u₂) := by
        change (⨆ k ∈ S, Δ.F.U k) ≤ LinearMap.ker (QuadraticMap.polarBilin Q u₂)
        apply iSup_le; intro k
        apply iSup_le; intro hk z hz
        rw [LinearMap.mem_ker, QuadraticMap.polarBilin_apply_apply]
        exact Δ.F.orth j k hk.2.symm u₂ hu₂ z hz
      exact hle hv
    rw [QuadraticMap.polar_add_left]
    rw [LinearMap.mem_ker, QuadraticMap.polarBilin_apply_apply] at hker₁ hker₂
    rw [hker₁, hker₂, add_zero]
  have θ_injective : Function.Injective θ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    let _ : Nontrivial Δ.D :=
      Module.nontrivial_of_finrank_pos (R := K) (M := Δ.D) (by rw [Δ.finrank_D]; norm_num)
    have hM : rk1ModelAct (K := K) (D := Δ.D) g = 1 := by
      refine LinearEquiv.ext fun u => ?_
      have h : φ (rk1ModelAct g u) = φ u := by
        have := congrArg (fun e : V ≃ₗ[K] V => e (φ u)) hg
        simpa [θ_apply_phi] using this
      exact hφ h
    exact rk1ModelAct_injective (by rw [hM, map_one])
  have θ_orthogonal : ∀ g, θ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    intro g
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    let x : Δ.D × Δ.D := (L.symm v).1
    let y : W' := (L.symm v).2
    have hyx : L.symm v = (x, y) := rfl
    have hv : v = φ x + (y : V) := by
      rw [← L.apply_symm_apply v, L_apply]
    have hθv : θ g v = φ (rk1ModelAct g x) + (y : V) := by
      rw [θ_apply, hyx]
    have hpolar : QuadraticMap.polar Q (φ (rk1ModelAct g x)) (y : V) = 0 :=
      hW_W'_polar _ (hφmem (rk1ModelAct g x)) y y.2
    have hpolarx : QuadraticMap.polar Q (φ x) (y : V) = 0 :=
      hW_W'_polar _ (hφmem x) y y.2
    calc Q (θ g v) = Q (φ (rk1ModelAct g x) + (y : V)) := by rw [hθv]
      _ = Q (φ (rk1ModelAct g x)) + Q (y : V) +
            QuadraticMap.polar Q (φ (rk1ModelAct g x)) (y : V) :=
            QuadraticMap.map_add Q _ _
      _ = Q (φ (rk1ModelAct g x)) + Q (y : V) := by rw [hpolar, add_zero]
      _ = Q (φ x) + Q (y : V) := by
            rw [hφQ (rk1ModelAct g x), rk1ModelAct_omega Δ.finrank_D g x, ← hφQ x]
      _ = Q (φ x) + Q (y : V) + QuadraticMap.polar Q (φ x) (y : V) := by rw [hpolarx, add_zero]
      _ = Q (φ x + (y : V)) := (QuadraticMap.map_add Q _ _).symm
      _ = Q v := by rw [hv]
  have θ_centralizer : ∀ g, θ g ∈ Subgroup.centralizer (Δ.reflFixed i j : Set (V ≃ₗ[K] V)) := by
    intro g
    rw [Subgroup.mem_centralizer_iff]
    intro yy hyy
    have hyy' : yy ∈ (reflFixedCoord p r i j).map Δ.τ := hyy
    obtain ⟨f, hf, rfl⟩ := (Subgroup.mem_map).mp hyy'
    have hτW' : ∀ u ∈ W', Δ.τ f u ∈ W' := by
      have hle : W' ≤ Submodule.comap (Δ.τ f : V →ₗ[K] V) W' := by
        change (⨆ k ∈ S, Δ.F.U k) ≤ Submodule.comap (Δ.τ f : V →ₗ[K] V) W'
        apply iSup_le; intro k
        apply iSup_le; intro hk z hz
        rw [Submodule.mem_comap, Δ.τ_eq f]
        have hUk : Δ.F.U k ≤ W' :=
          le_iSup_of_le k (le_iSup (fun _ : k ∈ S => Δ.F.U k) hk)
        exact hUk (Δ.F.mapsTo (piMul r p f) k z hz)
      intro u hu
      exact hle hu
    ext v
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    let x : Δ.D × Δ.D := (L.symm v).1
    let y : W' := (L.symm v).2
    have hyx : L.symm v = (x, y) := rfl
    have hv : v = φ x + (y : V) := by
      rw [← L.apply_symm_apply v, L_apply]
    have hθv : θ g v = φ (rk1ModelAct g x) + (y : V) := by
      rw [θ_apply, hyx]
    calc Δ.τ f (θ g v)
        = Δ.τ f (φ (rk1ModelAct g x) + (y : V)) := by rw [hθv]
      _ = Δ.τ f (φ (rk1ModelAct g x)) + Δ.τ f (y : V) := by rw [map_add]
      _ = φ ((Δ.c ^ (toAdd (f i)).val) (rk1ModelAct g x).1,
              (Δ.c ^ (toAdd (f i)).val) (rk1ModelAct g x).2) + Δ.τ f (y : V) := by
            rw [hφτ f hf (rk1ModelAct g x)]
      _ = φ (rk1ModelAct g ((Δ.c ^ (toAdd (f i)).val) x.1,
              (Δ.c ^ (toAdd (f i)).val) x.2)) + Δ.τ f (y : V) := by
            have hmap : ((Δ.c ^ (toAdd (f i)).val) (rk1ModelAct g x).1,
                (Δ.c ^ (toAdd (f i)).val) (rk1ModelAct g x).2) =
                rk1ModelAct g ((Δ.c ^ (toAdd (f i)).val) x.1,
                  (Δ.c ^ (toAdd (f i)).val) x.2) :=
              (rk1ModelAct_map g (show Δ.D →ₗ[K] Δ.D from
                (Δ.c ^ (toAdd (f i)).val : Δ.D ≃ₗ[K] Δ.D)) x).symm
            rw [hmap]
      _ = θ g (φ ((Δ.c ^ (toAdd (f i)).val) x.1,
              (Δ.c ^ (toAdd (f i)).val) x.2)) + Δ.τ f (y : V) := by rw [θ_apply_phi]
      _ = θ g (Δ.τ f (φ x)) + Δ.τ f (y : V) := by rw [← hφτ f hf x]
      _ = θ g (Δ.τ f (φ x)) + θ g (Δ.τ f (y : V)) := by
            rw [θ_apply_right g (Δ.τ f (y : V)) (hτW' (y : V) y.2)]
      _ = θ g (Δ.τ f (φ x) + Δ.τ f (y : V)) := by
            exact (map_add (θ g) (Δ.τ f (φ x)) (Δ.τ f (y : V))).symm
      _ = θ g (Δ.τ f (φ x + (y : V))) := by
            congr 1
            exact (map_add (Δ.τ f) (φ x) (y : V)).symm
      _ = θ g (Δ.τ f v) := by rw [hv]
  refine ⟨θ, θ_apply_phi, θ_apply_Uk, θ_injective, θ_orthogonal, θ_centralizer, ?_⟩
  intro y g hyUk hyφ
  ext v
  let x : Δ.D × Δ.D := (L.symm v).1
  let yy : W' := (L.symm v).2
  have hyx : L.symm v = (x, yy) := rfl
  have hv : v = φ x + (yy : V) := by
    rw [← L.apply_symm_apply v, L_apply]
  have hθv : θ g v = φ (rk1ModelAct g x) + (yy : V) := by
    rw [θ_apply, hyx]
  have hyfixW' : ∀ u ∈ W', y u = u := by
    have hle : W' ≤ LinearMap.fixedSubmodule (y : V →ₗ[K] V) := by
      change (⨆ k ∈ S, Δ.F.U k) ≤ LinearMap.fixedSubmodule (y : V →ₗ[K] V)
      apply iSup_le; intro k
      apply iSup_le; intro hk z hz
      rw [LinearMap.mem_fixedSubmodule_iff]
      exact hyUk k hk.1 hk.2 z hz
    intro u hu
    exact LinearMap.mem_fixedSubmodule_iff.mp (hle hu)
  calc y v = y (φ x + (yy : V)) := by rw [hv]
    _ = y (φ x) + y (yy : V) := by rw [map_add]
    _ = φ (rk1ModelAct g x) + y (yy : V) := by rw [hyφ x]
    _ = φ (rk1ModelAct g x) + (yy : V) := by rw [hyfixW' yy yy.2]
    _ = θ g v := by rw [hθv]

end OrthTorus

end CFSG.StandardType

end
