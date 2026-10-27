module

public import CFSG.Permutation.UnitaryThreeRecognition.BridgeSetup

public section

namespace CFSG.UnitaryThreeRecognition

open MulAction CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.UnitaryThreeRecognition.Model CFSG.UnitaryThreeRecognition.WeylAlg

namespace StdHyp

variable {G Ω : Type*} [Group G] [MulAction G Ω] {Q : Subgroup G} {a b : Ω} {j s : G}
  {p f d : ℕ} (S : StdHyp G Q a b j s p f d)
include S

theorem conjS_mem {t : G} (ht : t ∈ pairStab G a b) : s * t * s ∈ pairStab G a b := by
  have hs : s⁻¹ = s := by rw [inv_eq_iff_mul_eq_one, S.hs2]
  have := IsRootSubgroup.conj_mem_pairStab S.hsa S.hsb ht
  rwa [hs] at this

@[expose] def conjS : pairStab G a b →* pairStab G a b where
  toFun t := ⟨s * t * s, S.conjS_mem t.2⟩
  map_one' := Subtype.ext (by simp [S.hs2])
  map_mul' t₁ t₂ := Subtype.ext (by
    change s * ((t₁ : G) * t₂) * s = s * t₁ * s * (s * t₂ * s)
    calc s * ((t₁ : G) * t₂) * s = s * t₁ * (s * s) * t₂ * s := by rw [S.hs2]; group
      _ = s * t₁ * s * (s * t₂ * s) := by group)

theorem conjS_val (t : pairStab G a b) : (S.conjS t : G) = s * t * s := rfl

omit [MulAction G Ω] S in
theorem symm_ne_one' {K : Type*} [Field K] {J : HermitianForm 3 K} (φ : Q ≃* Coord J)
    {c : Coord J} (hc : c ≠ 1) : ((φ.symm c : Q) : G) ≠ 1 := by
  intro e
  apply hc
  have : φ.symm c = 1 := Subtype.ext e
  rw [← φ.apply_symm_apply c, this, map_one]

@[expose] noncomputable def sMapCoord {K : Type*} [Field K] {J : HermitianForm 3 K}
    (φ : Q ≃* Coord J) (c : Coord J) : Coord J := by
  classical
  exact if hc : c = 1 then 1 else
    φ ⟨sLeft Q a b s (φ.symm c), S.root.sLeft_mem S.hb S.hsa S.hs2 (φ.symm c).2
      (symm_ne_one' φ hc)⟩

theorem sMapCoord_apply {K : Type*} [Field K] {J : HermitianForm 3 K} (φ : Q ≃* Coord J)
    (u : Q) (hu : (u : G) ≠ 1) :
    S.sMapCoord φ (φ u) = φ ⟨sLeft Q a b s u, S.root.sLeft_mem S.hb S.hsa S.hs2 u.2 hu⟩ := by
  classical
  have hc : φ u ≠ 1 := by
    intro e; apply hu
    have := φ.injective (e.trans (map_one φ).symm)
    exact congrArg Subtype.val this
  rw [sMapCoord, dite_eq_right hc]
  simp only [MulEquiv.symm_apply_apply]

end StdHyp

namespace CoordHyp

variable {G Ω : Type*} [Group G] [MulAction G Ω] {Q : Subgroup G} {a b : Ω} {j s : G}
  {p f d : ℕ} {K : Type*} [Field K] {J : HermitianForm 3 K} {φ : Q ≃* Coord J}
  (C : CoordHyp Q a b j J φ) (S : StdHyp G Q a b j s p f d)
  [Finite G] [Finite Ω] {q : ℕ} (hconj : ∀ x : K, J.conj x = x ^ q)
  (hcop : Nat.Coprime 3 (q + 1))

@[expose] noncomputable def sigmaK : Kˣ →* Kˣ :=
  (C.torusEquiv S hconj hcop).toMonoidHom.comp
    (S.conjS.comp (C.torusEquiv S hconj hcop).symm.toMonoidHom)

theorem sigmaK_apply (k : Kˣ) :
    C.sigmaK S hconj hcop k = C.kOf (S.conjS ((C.torusEquiv S hconj hcop).symm k)) := rfl

@[expose] noncomputable def hmap (c : Coord J) : Kˣ := by
  classical
  exact if hc : c = 1 then 1 else
    C.torusEquiv S hconj hcop
      ⟨sTor Q a b s (φ.symm c), S.root.sTor_mem S.hb S.hsa S.hs2 (φ.symm c).2
        (StdHyp.symm_ne_one' φ hc)⟩

theorem hmap_apply (u : Q) (hu : (u : G) ≠ 1) :
    C.hmap S hconj hcop (φ u) =
      C.kOf ⟨sTor Q a b s u, S.root.sTor_mem S.hb S.hsa S.hs2 u.2 hu⟩ := by
  classical
  have hc : φ u ≠ 1 := by
    intro e; apply hu
    have := φ.injective (e.trans (map_one φ).symm)
    exact congrArg Subtype.val this
  rw [hmap, dite_eq_right hc]
  simp only [MulEquiv.symm_apply_apply]
  rfl

end CoordHyp

end CFSG.UnitaryThreeRecognition
