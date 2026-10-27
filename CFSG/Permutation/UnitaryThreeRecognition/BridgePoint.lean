module

public import CFSG.Permutation.UnitaryThreeRecognition.BridgeDefs

public section

namespace CFSG.UnitaryThreeRecognition

open MulAction CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.UnitaryThreeRecognition.Model CFSG.UnitaryThreeRecognition.WeylAlg

namespace CoordHyp

variable {G Ω : Type*} [Group G] [MulAction G Ω] {Q : Subgroup G} {a b : Ω} {j s : G}
  {p f d : ℕ} {K : Type*} [Field K] {J : HermitianForm 3 K} {φ : Q ≃* Coord J}
  (C : CoordHyp Q a b j J φ) (S : StdHyp G Q a b j s p f d)
include C S

theorem exists_point_weyl (k₀ : Kˣ)
    (hk₀ : ∀ c : Coord J, c ≠ 1 →
      hermitianTorusAction J k₀ (S.sMapCoord φ (hermitianTorusAction J k₀⁻¹ c)) = weylCoord J c) :
    ∃ s' : G, s' * s' = 1 ∧ s' • a = b ∧ ∀ u (hu : u ∈ Q), u ≠ 1 →
      s' • (u • b) = ((φ.symm (weylCoord J (φ ⟨u, hu⟩)) : Q) : G) • b := by
  obtain ⟨t₀, ht₀, htk⟩ := C.torus_surj k₀
  refine ⟨t₀ * s * t₀⁻¹, ?_, ?_, ?_⟩
  · calc t₀ * s * t₀⁻¹ * (t₀ * s * t₀⁻¹) = t₀ * (s * s) * t₀⁻¹ := by group
      _ = 1 := by rw [S.hs2]; group
  · have h1 : t₀⁻¹ • a = a := by rw [inv_smul_eq_iff, ht₀.1]
    rw [mul_smul, mul_smul, h1, S.hsa, ht₀.2]
  · intro u hu hu1
    have ht₀i : t₀⁻¹ ∈ pairStab G a b := (pairStab G a b).inv_mem ht₀
    set v : Q := ⟨t₀⁻¹ * u * t₀⁻¹⁻¹, S.root.normal t₀⁻¹ ht₀i.1 u hu⟩ with hvdef
    have hv1 : (v : G) ≠ 1 := by
      intro e
      apply hu1
      have e' : t₀⁻¹ * u * t₀⁻¹⁻¹ = 1 := e
      calc u = t₀ * (t₀⁻¹ * u * t₀⁻¹⁻¹) * t₀⁻¹ := by group
        _ = 1 := by rw [e']; group
    have hφv : φ v = hermitianTorusAction J k₀⁻¹ (φ ⟨u, hu⟩) := by
      have h1 := htk v (S.root.normal t₀ ht₀.1 v v.2)
      have h2 : (⟨t₀ * v * t₀⁻¹, S.root.normal t₀ ht₀.1 v v.2⟩ : Q) = ⟨u, hu⟩ :=
        Subtype.ext (by change t₀ * (t₀⁻¹ * u * t₀⁻¹⁻¹) * t₀⁻¹ = u; group)
      rw [h2] at h1
      rw [h1, ← torus_mul_apply, inv_mul_cancel, torus_one_apply]
    set y : Q := ⟨t₀ * sLeft Q a b s v * t₀⁻¹, S.root.normal t₀ ht₀.1 _
      (S.root.sLeft_mem S.hb S.hsa S.hs2 v.2 hv1)⟩ with hydef
    have hφy : φ y = weylCoord J (φ ⟨u, hu⟩) := by
      have h1 := htk ⟨sLeft Q a b s v, S.root.sLeft_mem S.hb S.hsa S.hs2 v.2 hv1⟩
        (S.root.normal t₀ ht₀.1 _ (S.root.sLeft_mem S.hb S.hsa S.hs2 v.2 hv1))
      rw [hydef, h1, ← S.sMapCoord_apply φ v hv1, hφv]
      apply hk₀
      intro e
      apply hu1
      have := φ.injective (e.trans (map_one φ).symm)
      exact congrArg Subtype.val this
    have hsym : φ.symm (weylCoord J (φ ⟨u, hu⟩)) = y := by rw [← hφy, MulEquiv.symm_apply_apply]
    rw [hsym]
    have hb0 : t₀⁻¹ • b = b := by rw [inv_smul_eq_iff, ht₀.2]
    have hvb : (v : G) • b = t₀⁻¹ • (u • b) := by
      change (t₀⁻¹ * u * t₀⁻¹⁻¹) • b = _
      rw [inv_inv, mul_smul, mul_smul, ht₀.2]
    have hL := S.root.smul_sLeft S.hb S.hsa S.hs2 v.2 hv1
    rw [hvb] at hL
    calc (t₀ * s * t₀⁻¹) • (u • b) = t₀ • (s • (t₀⁻¹ • (u • b))) := by simp only [mul_smul]
      _ = t₀ • (sLeft Q a b s v • b) := by rw [hL]
      _ = (t₀ * sLeft Q a b s v * t₀⁻¹) • b := by rw [mul_smul, mul_smul, hb0]

end CoordHyp

end CFSG.UnitaryThreeRecognition
