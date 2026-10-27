module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtCover
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtOmegaBigAbstract
import CFSG.ClassicalGroups.Orthogonal.StatedOmegaElementary
public import CFSG.ClassicalGroups.Orthogonal.Simple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

theorem w183_h1_elemAct_quadPlus {K : Type} [Field K] [Finite K] [Algebra (ZMod 2) K] {r a : ℕ}
    (hr : 3 ≤ r) (ha : 2 ≤ a) (hK : Nat.card K = 2 ^ a) :
    JonesParshall.Z1A (w183ElemAct (CFSG.LieType.Universal.Spin.quadPlus r K)) =
      JonesParshall.B1A (w183ElemAct (CFSG.LieType.Universal.Spin.quadPlus r K)) :=
  w183_h1_abstract (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus r K)
    (CFSG.ClassicalGroups.Orthogonal.plusPair K ⟨0, by omega⟩)
    (CFSG.ClassicalGroups.Orthogonal.plusPair K ⟨1, by omega⟩)
    (CFSG.ClassicalGroups.Orthogonal.plusPair_orth (by simp [Fin.ext_iff])) hK ha

theorem w183_h1_elemAct_quadMinus {K : Type} [Field K] [Finite K] [Algebra (ZMod 2) K] {r a : ℕ}
    (hr : 3 ≤ r) (ha : 2 ≤ a) (hK : Nat.card K = 2 ^ a) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    JonesParshall.Z1A (w183ElemAct (CFSG.LieType.Universal.Spin.quadMinus r K b c)) =
      JonesParshall.B1A (w183ElemAct (CFSG.LieType.Universal.Spin.quadMinus r K b c)) :=
  w183_h1_abstract
    (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite r K hirr)
    (CFSG.ClassicalGroups.Orthogonal.minusPair K b c ⟨0, by omega⟩)
    (CFSG.ClassicalGroups.Orthogonal.minusPair K b c ⟨1, by omega⟩)
    (CFSG.ClassicalGroups.Orthogonal.minusPair_orth (by simp [Fin.ext_iff])) hK ha

theorem s16nt_omega_h1_plus_big {K : Type} [Field K] [Finite K] [Algebra (ZMod 2) K] {r a : ℕ}
    (hr : 3 ≤ r) (ha : 2 ≤ a) (hK : Nat.card K = 2 ^ a) :
    Module.finrank (ZMod 2) (CFSG.Quasithin.JonesParshall.H1
      (s16ntNatRep (StatedOmega (StatedQuadPlus r K)))) = 0 := by
  let Q := CFSG.LieType.Universal.Spin.quadPlus r K
  let EG := CFSG.ClassicalGroups.Orthogonal.elementaryGroup Q
  let SO := StatedOmega (StatedQuadPlus r K)
  have hbridge : SO =
      EG.map (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin r ⊕ Fin r) K).symm.toMonoidHom :=
    CFSG.ClassicalGroups.Orthogonal.statedOmega_quadPlus_eq_map (n := r) (K := K) hr
  let θ : ↥EG ≃* ↥SO :=
    (MulEquiv.subgroupMap
      (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin r ⊕ Fin r) K).symm EG).trans
      (MulEquiv.subgroupCongr hbridge.symm)
  have hθval : ∀ g : ↥EG,
      ((θ g : ↥SO) : GL (Fin r ⊕ Fin r) K) =
        (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin r ⊕ Fin r) K).symm
          ((g : ↥EG) : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) := by
    intro g
    rfl
  have hβ : ∀ (γ : ↥SO) (w : Fin r ⊕ Fin r → K),
      (AddEquiv.refl (Fin r ⊕ Fin r → K)) (s16ntNatRep SO γ w) =
        w183ElemAct Q (θ.symm γ) ((AddEquiv.refl (Fin r ⊕ Fin r → K)) w) := by
    intro γ w
    have h1 : ((θ (θ.symm γ) : ↥SO) : GL (Fin r ⊕ Fin r) K) =
        (γ : GL (Fin r ⊕ Fin r) K) := by
      rw [MulEquiv.apply_symm_apply]
    have h2 := hθval (θ.symm γ)
    rw [h1] at h2
    have h3 : ((θ.symm γ : ↥EG) : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) =
        CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin r ⊕ Fin r) K
          (γ : GL (Fin r ⊕ Fin r) K) := by
      have := congrArg (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin r ⊕ Fin r) K) h2
      rw [MulEquiv.apply_symm_apply] at this
      exact this
    show ((γ : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).mulVec w =
      ((θ.symm γ : ↥EG) : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) w
    rw [h3, CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply]
  have hcore := w183_h1_elemAct_quadPlus (K := K) hr ha hK
  have hcard := JonesParshall.card_H1_eq_of_card (s16ntNatRep SO) (μ := w183ElemAct Q)
    (θ := θ.symm) (β := AddEquiv.refl (Fin r ⊕ Fin r → K)) hβ (k := 1)
    (by rw [hcore, one_mul])
  exact JonesParshall.finrank_H1_of_card (s16ntNatRep SO) (d := 0) (by rw [hcard, pow_zero])

theorem s16nt_omega_h1_minus_big {K : Type} [Field K] [Finite K] [Algebra (ZMod 2) K] {r a : ℕ}
    (hr : 3 ≤ r) (ha : 2 ≤ a) (hK : Nat.card K = 2 ^ a) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Module.finrank (ZMod 2) (CFSG.Quasithin.JonesParshall.H1
      (s16ntNatRep (StatedOmega (StatedQuadMinus r K b c)))) = 0 := by
  have : Fintype K := Fintype.ofFinite K
  have hF : Fintype.card K = 2 ^ a := by rw [← Nat.card_eq_fintype_card]; exact hK
  have : CharP K 2 := charP_of_card_eq_prime_pow hF
  let Q := CFSG.LieType.Universal.Spin.quadMinus r K b c
  let EG := CFSG.ClassicalGroups.Orthogonal.elementaryGroup Q
  let SO := StatedOmega (StatedQuadMinus r K b c)
  let ι := Fin (r - 1) ⊕ Fin (r - 1) ⊕ Fin 2
  have hbridge : SO = EG.map
      (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).symm.toMonoidHom :=
    CFSG.ClassicalGroups.Orthogonal.statedOmega_quadMinus_eq_map_of_two_le
      (n := r) (K := K) (b := b) (c := c) (by omega) hirr
  let θ : ↥EG ≃* ↥SO :=
    (MulEquiv.subgroupMap
      (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).symm EG).trans
      (MulEquiv.subgroupCongr hbridge.symm)
  have hθval : ∀ g : ↥EG,
      ((θ g : ↥SO) : GL ι K) =
        (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).symm
          ((g : ↥EG) : (ι → K) ≃ₗ[K] (ι → K)) := by
    intro g
    rfl
  have hβ : ∀ (γ : ↥SO) (w : ι → K),
      (AddEquiv.refl (ι → K)) (s16ntNatRep SO γ w) =
        w183ElemAct Q (θ.symm γ) ((AddEquiv.refl (ι → K)) w) := by
    intro γ w
    have h1 : ((θ (θ.symm γ) : ↥SO) : GL ι K) = (γ : GL ι K) := by
      rw [MulEquiv.apply_symm_apply]
    have h2 := hθval (θ.symm γ)
    rw [h1] at h2
    have h3 : ((θ.symm γ : ↥EG) : (ι → K) ≃ₗ[K] (ι → K)) =
        CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K (γ : GL ι K) := by
      have := congrArg (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K) h2
      rw [MulEquiv.apply_symm_apply] at this
      exact this
    show ((γ : GL ι K) : Matrix ι ι K).mulVec w =
      ((θ.symm γ : ↥EG) : (ι → K) ≃ₗ[K] (ι → K)) w
    rw [h3, CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply]
  have hcore := w183_h1_elemAct_quadMinus (K := K) hr ha hK hirr
  have hcard := JonesParshall.card_H1_eq_of_card (s16ntNatRep SO) (μ := w183ElemAct Q)
    (θ := θ.symm) (β := AddEquiv.refl (ι → K)) hβ (k := 1)
    (by rw [hcore, one_mul])
  exact JonesParshall.finrank_H1_of_card (s16ntNatRep SO) (d := 0) (by rw [hcard, pow_zero])

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
