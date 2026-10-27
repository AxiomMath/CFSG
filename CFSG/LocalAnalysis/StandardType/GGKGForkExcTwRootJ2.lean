module

public import CFSG.LocalAnalysis.StandardType.GGKGForkExcTwRootJ1

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.KE
  CFSG.LieType.AlgebraicGroups

theorem ggKGTj_mapF_injective {K : Type} [Field K] {n : ℕ}
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ (2 ^ n)) :
    Function.Injective
      (Matrix.SpecialLinearGroup.map (n := Fin 2) (Subfield.subtype (ggKGTj_F Fr hFr))) := by
  intro X Y h
  apply Subtype.ext
  apply Matrix.map_injective (Subfield.subtype (ggKGTj_F Fr hFr)).injective
  exact congrArg Subtype.val h

noncomputable def ggKGTj_phi1 {K : Type} [Field K] {n : ℕ}
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ (2 ^ n))
    (P : SL2 (AlgebraicClosure K)) :
    SL2 ↥(ggKGTj_F Fr hFr) →* SL2 (AlgebraicClosure K) :=
  (MulAut.conj P).toMonoidHom.comp
    (Matrix.SpecialLinearGroup.map (Subfield.subtype (ggKGTj_F Fr hFr)))

theorem ggKGTj_phi1_apply {K : Type} [Field K] {n : ℕ}
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ (2 ^ n))
    (P : SL2 (AlgebraicClosure K)) (N : SL2 ↥(ggKGTj_F Fr hFr)) :
    ggKGTj_phi1 Fr hFr P N =
      P * Matrix.SpecialLinearGroup.map (Subfield.subtype (ggKGTj_F Fr hFr)) N * P⁻¹ := by
  show (MulAut.conj P).toMonoidHom (Matrix.SpecialLinearGroup.map _ N) = _
  change P * Matrix.SpecialLinearGroup.map _ N * P⁻¹ = _
  rfl

theorem ggKGTj_phi1_injective {K : Type} [Field K] {n : ℕ}
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ (2 ^ n))
    (P : SL2 (AlgebraicClosure K)) :
    Function.Injective (ggKGTj_phi1 Fr hFr P) :=
  (MulAut.conj P).injective.comp (ggKGTj_mapF_injective Fr hFr)

theorem ggKGTj_phi1_fixed {K : Type} [Field K] {n : ℕ}
    [CharP (AlgebraicClosure K) 2] (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
    (hFr : ∀ c, Fr c = c ^ (2 ^ n)) {P : SL2 (AlgebraicClosure K)}
    (hPq : Matrix.SpecialLinearGroup.map Fr P = WSL * P) (N : SL2 ↥(ggKGTj_F Fr hFr)) :
    WSL * Matrix.SpecialLinearGroup.map Fr (ggKGTj_phi1 Fr hFr P N) * WSL =
      ggKGTj_phi1 Fr hFr P N := by
  have hgf : Matrix.SpecialLinearGroup.map Fr
      (Matrix.SpecialLinearGroup.map (Subfield.subtype (ggKGTj_F Fr hFr)) N) =
      Matrix.SpecialLinearGroup.map (Subfield.subtype (ggKGTj_F Fr hFr)) N := by
    ext i j
    exact ggKGTj_subtype_fix Fr hFr (N.1 i j)
  rw [ggKGTj_phi1_apply, map_mul, map_mul, map_inv, hPq, hgf]
  rw [show (WSL * P)⁻¹ = P⁻¹ * WSL by rw [mul_inv_rev, ggKGTj_WSL_inv_eq]]
  rw [show WSL * (WSL * P * Matrix.SpecialLinearGroup.map (Subfield.subtype (ggKGTj_F Fr hFr)) N *
        (P⁻¹ * WSL)) * WSL =
      (WSL * WSL) * P * Matrix.SpecialLinearGroup.map (Subfield.subtype (ggKGTj_F Fr hFr)) N *
        P⁻¹ * (WSL * WSL) from by group, ggKGTj_WSL_sq_one]
  group

end CFSG.StandardType

end
