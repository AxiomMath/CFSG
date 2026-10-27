module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829NKRepAT
public import CFSG.Quasithin.Vol2.Ch8Sec2L829NKDefs
public import CFSG.Quasithin.Background.RonanF918Five

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.L829NK

open CFSG.ProperTwoGeneratedCore.BinaryThreeSpace CFSG.Quasithin.H.SL3Rep CFSG.Open
open Matrix

@[expose] noncomputable def psiGL {K : Type} [Field K] {n : ℕ} :
    GL (Fin n) K ≃* ((Fin n → K) ≃ₗ[K] (Fin n → K)) :=
  (Matrix.GeneralLinearGroup.toLin).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin n → K))

theorem nk_leafSL3Rep : NKLeafSL3Rep := by
  intro K _ _ _ hK n N hirr htv hex
  classical
  obtain ⟨L, _, hL, ⟨e₁⟩⟩ := hex
  letI : Algebra (ZMod 2) K := ZMod.algebra (R := K) 2
  have halg : ∀ a : ZMod 2, algebraMap (ZMod 2) K a = ((a.val : ℕ) : K) := by
    intro a
    conv_lhs => rw [← ZMod.natCast_zmod_val a]
    exact map_natCast (algebraMap (ZMod 2) K) a.val
  obtain ⟨e₂⟩ := CFSG.Quasithin.RonanF918.isPSL_three_equiv_statedSL_zmod_two hL
  let e₃ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) ≃* ↥(StatedSL 3 (ZMod 2)) :=
    (MonoidHom.ofInjective Matrix.SpecialLinearGroup.toGL_injective).trans
      (MulEquiv.subgroupCongr (StatedAPI.statedSL_eq_range_toGL 3 (ZMod 2)).symm)
  let e : GS ≃* ↥N := (iota.symm.trans e₃).trans (e₂.symm.trans e₁.symm)
  let φ : GS →* GL (Fin n) K := N.subtype.comp e.toMonoidHom
  have hφinj : Function.Injective φ := Subtype.val_injective.comp e.injective
  have hφN : ∀ h, φ h ∈ N := fun h => (e h).2
  have hNφ : ∀ g ∈ N, ∃ h, φ h = g := fun g hg => ⟨e.symm ⟨g, hg⟩, by simp [φ]⟩
  let θ : GS →* ((Fin n → K) ≃ₗ[K] (Fin n → K)) := psiGL.toMonoidHom.comp φ
  have hθ : ∀ h v, θ h v = ((φ h : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v :=
    fun h v => rfl
  have hθinj : Function.Injective θ := psiGL.injective.comp hφinj
  have hirr' : ∀ W' : Submodule K (Fin n → K), (∀ g, ∀ w ∈ W', θ g w ∈ W') → W' = ⊥ ∨ W' = ⊤ := by
    intro W' hW'
    refine hirr W' fun g hg w hw => ?_
    obtain ⟨h, rfl⟩ := hNφ g hg
    rw [← hθ]
    exact hW' h w hw
  have htv' : ∀ g : GS, orderOf g = 2 →
      Module.finrank K (LinearMap.range ((θ g : (Fin n → K) →ₗ[K] (Fin n → K)) - LinearMap.id)) ≤ 1 := by
    intro g hg
    have hord : orderOf (φ g) = 2 := by rw [orderOf_injective φ hφinj g]; exact hg
    obtain ⟨-, -, hrk⟩ := htv (φ g) (hφN g) hord
    have : (θ g : (Fin n → K) →ₗ[K] (Fin n → K)) - LinearMap.id =
        Matrix.mulVecLin (((φ g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1) := by
      refine LinearMap.ext fun v => ?_
      simp [hθ, Matrix.sub_mulVec]
    rw [this]
    exact hrk.le
  obtain ⟨b, hb1, hb2⟩ := nk_sl3_transvection_rep hK θ hθinj hirr' htv'
  have hn : n = 3 := by
    have h1 : Module.finrank K (Fin n → K) = Fintype.card (Fin 3) := Module.finrank_eq_card_basis b
    simpa using h1
  refine ⟨hn, ?_⟩
  let s : Module.Basis (Fin n) K (Fin n → K) := Pi.basisFun K (Fin n)
  let b' : Module.Basis (Fin n) K (Fin n → K) := b.reindex (finCongr hn.symm)
  have hQQ' : b'.toMatrix s * s.toMatrix b' = 1 := b'.toMatrix_mul_toMatrix_flip s
  have hQ'Q : s.toMatrix b' * b'.toMatrix s = 1 := s.toMatrix_mul_toMatrix_flip b'
  let P : GL (Fin n) K := ⟨b'.toMatrix s, s.toMatrix b', hQQ', hQ'Q⟩
  have hP : ∀ g : GL (Fin n) K, ((P * g * P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      b'.toMatrix s * (g : Matrix (Fin n) (Fin n) K) * s.toMatrix b' := fun g => rfl
  have hbc : ∀ h, LinearMap.toMatrix b' b' (θ h : (Fin n → K) →ₗ[K] (Fin n → K)) =
      ((P * φ h * P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    intro h
    rw [hP]
    have h1 := basis_toMatrix_mul_linearMap_toMatrix s b' s (θ h : (Fin n → K) →ₗ[K] (Fin n → K))
    have h2 := linearMap_toMatrix_mul_basis_toMatrix b' s b' (θ h : (Fin n → K) →ₗ[K] (Fin n → K))
    have h3 : LinearMap.toMatrix s s (θ h : (Fin n → K) →ₗ[K] (Fin n → K)) =
        ((φ h : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      have : (θ h : (Fin n → K) →ₗ[K] (Fin n → K)) =
          Matrix.toLin' ((φ h : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
        LinearMap.ext fun v => by rw [LinearEquiv.coe_coe, hθ, Matrix.toLin'_apply]
      rw [this, LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
    rw [← h2, ← h1, h3]
  have hre : ∀ (f : (Fin n → K) →ₗ[K] (Fin n → K)),
      LinearMap.toMatrix b' b' f = (LinearMap.toMatrix b b f).submatrix (Fin.cast hn) (Fin.cast hn) := by
    intro f
    ext i j
    simp [LinearMap.toMatrix_apply, b', Module.Basis.reindex_apply, Module.Basis.repr_reindex_apply]
  have hcast : (algebraMap (ZMod 2) K) = (fun a : ZMod 2 => ((a.val : ℕ) : K)) := funext halg
  refine ⟨P, fun g => ⟨fun hg => ?_, fun ⟨M, hdet, hM⟩ => ?_⟩⟩
  · obtain ⟨h, rfl⟩ := hNφ g hg
    obtain ⟨M, hM⟩ := hb1 h
    refine ⟨(M : Matrix (Fin 3) (Fin 3) (ZMod 2)), M.2, ?_⟩
    rw [← hbc h, hre, hM, hcast]
  · obtain ⟨h, hh⟩ := hb2 ⟨M, hdet⟩
    have h1 : ((P * φ h * P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ((P * g * P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      rw [← hbc h, hre, hh, hM, hcast]
    have h2 : P * φ h * P⁻¹ = P * g * P⁻¹ := Units.ext h1
    have h3 : φ h = g := mul_left_cancel (mul_right_cancel h2)
    rw [← h3]
    exact hφN h

end CFSG.Quasithin.H13.L829NK
