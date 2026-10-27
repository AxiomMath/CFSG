module

public import CFSG.RankThree.GF2n.Stroth80.Sec7NoInvFrame

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.ClassicalGroups.F2Fixed CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.Open QuadraticMap
open scoped Matrix MatrixGroups

theorem noInvariantForm_frame_hom {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K) {R : Type} [Group R] (φ : R →* GL (Fin 3 ⊕ Fin 3) K)
    (hφ : φ.range = StatedOmega (StatedQuadPlus 3 K)) {u u' : Fin 3 ⊕ Fin 3 → K}
    (hu : quadPlus 3 K u = 0) (hu' : quadPlus 3 K u' = 0) (hu0 : u ≠ 0)
    (huu' : polar (quadPlus 3 K) u u' ≠ 0) (Y : Type) [AddCommGroup Y] [Finite Y]
    [DistribMulAction R Y] (h2 : ∀ a : Y, a + a = 0) (hker : ∀ r ∈ φ.ker, ∀ a : Y, r • a = a)
    (L₁ L₂ : Subgroup R)
    (hL₁ : L₁.map φ = (ElemMatrixIso.plus (K := K) (m := 3) le_rfl).LomGL u)
    (hL₂ : L₂.map φ = (ElemMatrixIso.plus (K := K) (m := 3) le_rfl).LomGL u')
    (hdec : IsCompl (fixedSub Y (L₁ : Set R)) (fixedSub Y (L₂ : Set R)))
    (hcard : Nat.card Y = Nat.card K ^ 4) :
    ¬ ∃ β : Y →+ Y →+ ZMod 2, (∀ (r : R) (a b : Y), β (r • a) (r • b) = β a b) ∧
        ∀ a : Y, (∀ b : Y, β a b = 0) → a = 0 := by
  rintro ⟨β, hinv, hnd⟩
  classical
  let E := ElemMatrixIso.plus (K := K) (m := 3) le_rfl
  have hΦ := viaMatrix_surjective (e := E.equiv) φ hφ
  have hk : ∀ y ∈ (viaMatrix (StatedOmega (StatedQuadPlus 3 K)) E.equiv φ hφ).ker,
      ∀ a : Y, y • a = a := by
    intro y hy a
    rw [ker_viaMatrix] at hy
    exact hker y hy a
  letI : DistribMulAction (Gom (quadPlus 3 K)) Y := descendAction _ hΦ hk
  have hsm : ∀ (z : R) (a : Y),
      viaMatrix (StatedOmega (StatedQuadPlus 3 K)) E.equiv φ hφ z • a = z • a := fun z a =>
    descendAction_smul _ hΦ hk z a
  refine noInvariantForm_frame hK hu hu' hu0 huu' Y h2 ?_ hcard β ?_ hnd
  · rw [fixedSub_descend_Lom E φ hφ hker hL₁, fixedSub_descend_Lom E φ hφ hker hL₂]
    exact hdec
  · intro g a b
    obtain ⟨r, rfl⟩ := hΦ g
    rw [hsm, hsm]
    exact hinv r a b

end CFSG.RankThree.GF2n.Stroth80
