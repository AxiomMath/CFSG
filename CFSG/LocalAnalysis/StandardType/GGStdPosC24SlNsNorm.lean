module

public import CFSG.LocalAnalysis.StandardType.GGSlNsRootGenDefs
import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameTorus

public section

namespace CFSG.StandardType

open Matrix Polynomial CoordSL Multiplicative CFSG.LocalAnalysis.ComponentInitial

theorem SlNsRootGen.exists_signedPerm_of_conj {K : Type} [Field K] [Finite K] [CharP K 2]
    {g : K[X]} [Fact (Irreducible g)] {n s r p : ℕ} [Fact p.Prime]
    (hpK : p ∣ Nat.card K + 1) (hgd : g ∣ cyclotomic p K)
    (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r) (hC : (rootMat g).det = 1)
    (hCp : rootMat g ^ p = 1) (x : SpecialLinearGroup (Fin n) K)
    (hx : ∀ t, ∃ t', x * SlNsRootGen.torusSL ε hC hCp (ofAdd t) * x⁻¹ =
      SlNsRootGen.torusSL ε hC hCp (ofAdd t')) :
    ∃ (π : Equiv.Perm (Fin s)) (σ : Fin s → ZMod p), (∀ i, σ i = 1 ∨ σ i = -1) ∧
      ∀ t t', x * SlNsRootGen.torusSL ε hC hCp (ofAdd t) * x⁻¹ =
          SlNsRootGen.torusSL ε hC hCp (ofAdd t') →
        ∀ i, t' (π i) = σ i * t i := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := SpNS.ne_two_of_dvd_card_add_one hpK
  have hpK' : (p : K) ≠ 0 := TableBSymp.natCast_ne_zero_of_charTwo hp hp2
  have : Module.Finite K (AdjoinRoot g) := (rootPB g).finite
  have : Finite (AdjoinRoot g) := Module.finite_of_finite K
  have hζo := root_isPrimitiveRoot hp hpK' hgd
  have hζp : AdjoinRoot.root g ^ p = 1 := hζo.pow_eq_one
  set Φ := frameCoords g ε
  have hdec : ∀ (d d' : Fin s → AdjoinRoot g) (w w' : Fin r → K),
      (0 : LinearMap.BilinForm K (Fin n → K)) (Φ (d, w)) (Φ (d', w')) =
        ∑ i, (0 : LinearMap.BilinForm K (AdjoinRoot g)) (d i) (d' i) +
          (0 : LinearMap.BilinForm K (Fin n → K)) (Φ (0, w)) (Φ (0, w')) := by
    intro d d' w w'
    simp
  have hζβ : ∀ u v : AdjoinRoot g,
      (0 : LinearMap.BilinForm K (AdjoinRoot g)) (AdjoinRoot.root g * u)
        (AdjoinRoot.root g * v) = (0 : LinearMap.BilinForm K (AdjoinRoot g)) u v :=
    fun _ _ => rfl
  set τ := SpNS.torHom (K := K) hζp hdec hζβ with hτ
  let Ψ : SpecialLinearGroup (Fin n) K →*
      ↥(sesqUnitaryGroup (0 : LinearMap.BilinForm K (Fin n → K))) :=
    (GeneralLinearGroup.toLin.toMonoidHom.comp SpecialLinearGroup.toGL).codRestrict _
      fun _ _ _ => rfl
  have hΨ : ∀ t : Fin s → ZMod p,
      Ψ (SlNsRootGen.torusSL ε hC hCp (ofAdd t)) = τ fun i => ofAdd (t i) := by
    intro t
    refine Subtype.ext (Units.ext (LinearMap.ext fun v => ?_))
    obtain ⟨⟨d, w⟩, rfl⟩ := Φ.surjective v
    rw [hτ, SpNS.coe_torHom, SpNS.frameUnit_apply, SpNS.torEquiv_apply,
      SlNsRootGen.torusSL_apply]
    change SLNS.nsMat ε (rootMat g) _ *ᵥ frameCoords g ε (d, w) = _
    rw [nsMat_mulVec_frameCoords]
    rfl
  have hh : ∀ f, ∃ f', Ψ x * τ f * (Ψ x)⁻¹ = τ f' := by
    intro f
    obtain ⟨t', ht'⟩ := hx fun i => toAdd (f i)
    refine ⟨fun i => ofAdd (t' i), ?_⟩
    rw [← hΨ, ← ht', map_mul, map_mul, map_inv, hΨ]
    rfl
  obtain ⟨π, σ, hσ, hrel⟩ := SpNS.torHom_normalizer hζp hp hdec hζβ hζo
    (fun a θ hθ hθζ => SpNS.eq_one_or_eq_neg_one_of_intertwine hp hp2 hpK' hgd hpK a θ hθ hθζ)
    (Ψ x) hh
  refine ⟨π, σ, hσ, fun t t' htt' i => ?_⟩
  exact hrel (fun i => ofAdd (t i)) (fun i => ofAdd (t' i))
    (by rw [← hΨ, ← hΨ, ← htt', map_mul, map_mul, map_inv]) i

end CFSG.StandardType

end
