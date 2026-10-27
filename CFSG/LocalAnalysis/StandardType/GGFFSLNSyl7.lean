module

public import CFSG.LocalAnalysis.StandardType.GGFFModelNDefs
public import CFSG.LocalAnalysis.StandardType.GGFFSLNDefs
import CFSG.LocalAnalysis.StandardType.GGHalfFiveCommutant
import CFSG.RankThree.PartTwo.Sec4.RonanK429RowFBlock

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.GGFF

open scoped MatrixGroups
open Matrix
open CFSG.RankThree.PartTwo.Sec4.RonanK429F

private theorem negOneF2 : (-1 : GGHalf.F2) = 1 := by
  rw [neg_eq_iff_add_eq_zero, one_add_one_eq_two, GGHalf.gf2_two]

private noncomputable def theta (n : ℕ) : SL(n, ZMod 2) →* SL(n, GGHalf.F2) :=
  SpecialLinearGroup.map
    ((GaloisField.equivZmodP (p := 2)).toRingEquiv.symm : ZMod 2 →+* GGHalf.F2)

private theorem theta_injective (n : ℕ) : Function.Injective (theta n) := by
  intro A B h
  apply Subtype.ext
  have h1 : ((theta n A : SL(n, GGHalf.F2)) : Matrix (Fin n) (Fin n) GGHalf.F2) =
      ((theta n B : SL(n, GGHalf.F2)) : Matrix (Fin n) (Fin n) GGHalf.F2) :=
    congrArg Subtype.val h
  change (A : Matrix (Fin n) (Fin n) (ZMod 2)).map
      ((GaloisField.equivZmodP (p := 2)).toRingEquiv.symm : ZMod 2 →+* GGHalf.F2) =
    (B : Matrix (Fin n) (Fin n) (ZMod 2)).map
      ((GaloisField.equivZmodP (p := 2)).toRingEquiv.symm : ZMod 2 →+* GGHalf.F2) at h1
  exact Matrix.map_injective
    ((GaloisField.equivZmodP (p := 2)).toRingEquiv.symm).injective h1

private noncomputable def omegaZ (n : ℕ) (k : Fin n) : SL(n + 1, ZMod 2) :=
  CFSG.LieType.Universal.SpecialLinear.weylRep n (ZMod 2) k *
    SpecialLinearGroup.transvection
      (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne (1 : ZMod 2)

private theorem theta_omegaZ (n : ℕ) (k : Fin n) :
    theta (n + 1) (omegaZ n k) = GGHalf.omegaBlock n k := by
  simp only [omegaZ, GGHalf.omegaBlock, CFSG.LieType.Universal.SpecialLinear.weylRep, theta,
    map_mul, SpecialLinearGroup.map_transvection, map_neg, map_one, negOneF2]

private theorem zeta6_eq : zetaOf W6.T = omegaZ 5 0 * omegaZ 5 2 * omegaZ 5 4 := by
  decide +kernel

private theorem theta_zeta6 : theta 6 (zetaOf W6.T) = GGHalf.zeta5 := by
  rw [zeta6_eq, map_mul, map_mul, theta_omegaZ, theta_omegaZ, theta_omegaZ]
  rfl

private noncomputable instance f4Fintype : Fintype GGHalf.F4 := Fintype.ofFinite GGHalf.F4

private theorem card_centralizer_zeta5 :
    Nat.card (Subgroup.centralizer ({GGHalf.zeta5} : Set (SL(6, GGHalf.F2)))) = 181440 := by
  rw [GGHalf.centralizer_zeta5]
  rw [← Nat.card_congr (MonoidHom.ofInjective (GGHalf.resGL_injective 3)).toEquiv]
  rw [Matrix.card_GL_field (𝔽 := GGHalf.F4) (n := 3)]
  have hF4 : Fintype.card GGHalf.F4 = 4 := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 2 (by norm_num)
  rw [hF4]
  norm_num [Fin.prod_univ_three]

theorem syl7_SL6 : ∀ P : Subgroup SL(6, ZMod 2), IsPGroup 7 P →
    (∀ p ∈ P, p * zetaOf W6.T = zetaOf W6.T * p) → Nat.card P ≤ 7 := by
  intro P hP hC
  have hle : P.map (theta 6) ≤
      Subgroup.centralizer ({GGHalf.zeta5} : Set (SL(6, GGHalf.F2))) := by
    intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := congrArg (theta 6) (hC p hp)
    simpa only [map_mul, theta_zeta6] using h
  have hdvd : Nat.card P ∣ 181440 := by
    have h1 : Nat.card P ∣
        Nat.card (Subgroup.centralizer ({GGHalf.zeta5} : Set (SL(6, GGHalf.F2)))) := by
      rw [← Subgroup.card_map_of_injective (f := theta 6) (K := P) (theta_injective 6)]
      exact Subgroup.card_dvd_of_le hle
    rwa [card_centralizer_zeta5] at h1
  obtain ⟨n, hn⟩ := hP.exists_card_dvd_pow
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 7)).1 hn
  have hk1 : k ≤ 1 := by
    by_contra h
    have h2 : 2 ≤ k := by omega
    have h49 : (7 : ℕ) ^ 2 ∣ 181440 := (pow_dvd_pow 7 h2).trans (hk ▸ hdvd)
    norm_num at h49
  calc Nat.card P = 7 ^ k := hk
    _ ≤ 7 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
    _ = 7 := by norm_num

private noncomputable def e61 : Fin 7 ≃ Fin 6 ⊕ Fin 1 :=
  (finSumFinEquiv : Fin 6 ⊕ Fin 1 ≃ Fin 7).symm

private theorem slUpperBlockMat_eq (A : Matrix (Fin 6) (Fin 6) (ZMod 2)) :
    slUpperBlockMat 6 (ZMod 2) A =
      (fromBlocks A 0 0 (1 : Matrix (Fin 1) (Fin 1) (ZMod 2))).submatrix e61 e61 := by
  rw [slUpperBlockMat, Matrix.coe_reindexAlgEquiv]
  rfl

private theorem bl_slUpperBlockMat (A : Matrix (Fin 6) (Fin 6) (ZMod 2)) :
    bl e61 (slUpperBlockMat 6 (ZMod 2) A) =
      fromBlocks A 0 0 (1 : Matrix (Fin 1) (Fin 1) (ZMod 2)) := by
  rw [slUpperBlockMat_eq, bl_submatrix]

private theorem zeta7_eq : zetaOf W7.T = slUpperBlockHom 6 (ZMod 2) (zetaOf W6.T) := by
  decide +kernel

private theorem zeta7_add_sq :
    ((zetaOf W7.T : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)) +
      (((zetaOf W7.T : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)) ^ 2) =
      1 + slUpperBlockMat 6 (ZMod 2) 0 := by
  decide +kernel

private theorem mem_range_iota6_of_commute (X : SL(7, ZMod 2))
    (hX : X * zetaOf W7.T = zetaOf W7.T * X) :
    X ∈ (slUpperBlockHom 6 (ZMod 2)).range := by
  have hXm : (X : Matrix (Fin 7) (Fin 7) (ZMod 2)) *
      ((zetaOf W7.T : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)) =
      ((zetaOf W7.T : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)) *
        (X : Matrix (Fin 7) (Fin 7) (ZMod 2)) := by
    simpa using congrArg (fun g : SL(7, ZMod 2) =>
      (g : Matrix (Fin 7) (Fin 7) (ZMod 2))) hX
  have h2m : (X : Matrix (Fin 7) (Fin 7) (ZMod 2)) *
      ((zetaOf W7.T : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)) ^ 2 =
      ((zetaOf W7.T : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)) ^ 2 *
        (X : Matrix (Fin 7) (Fin 7) (ZMod 2)) := by
    have h2g : X * zetaOf W7.T ^ 2 = zetaOf W7.T ^ 2 * X :=
      (show Commute X (zetaOf W7.T) from hX).pow_right 2
    simpa only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_pow] using
      congrArg (fun g : SL(7, ZMod 2) => (g : Matrix (Fin 7) (Fin 7) (ZMod 2))) h2g
  have hcomm : (X : Matrix (Fin 7) (Fin 7) (ZMod 2)) * (1 + slUpperBlockMat 6 (ZMod 2) 0) =
      (1 + slUpperBlockMat 6 (ZMod 2) 0) * (X : Matrix (Fin 7) (Fin 7) (ZMod 2)) := by
    rw [← zeta7_add_sq, Matrix.mul_add, Matrix.add_mul, hXm, h2m]
  have hbl := congrArg (bl e61) hcomm
  rw [bl_mul, bl_mul, bl_add, bl_one, bl_slUpperBlockMat] at hbl
  have hF : bl e61 (X : Matrix (Fin 7) (Fin 7) (ZMod 2)) *
      fromBlocks 0 0 0 (1 : Matrix (Fin 1) (Fin 1) (ZMod 2)) =
      fromBlocks 0 0 0 (1 : Matrix (Fin 1) (Fin 1) (ZMod 2)) *
        bl e61 (X : Matrix (Fin 7) (Fin 7) (ZMod 2)) := by
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul] at hbl
    exact add_left_cancel hbl
  have hblX : bl e61 (X : Matrix (Fin 7) (Fin 7) (ZMod 2)) =
      fromBlocks (bl e61 (X : Matrix (Fin 7) (Fin 7) (ZMod 2))).toBlocks₁₁ 0 0
        (bl e61 (X : Matrix (Fin 7) (Fin 7) (ZMod 2))).toBlocks₂₂ :=
    eq_fromBlocks_of_isBlockDiag (isBlockDiag_of_commute hF)
  set A : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
    (bl e61 (X : Matrix (Fin 7) (Fin 7) (ZMod 2))).toBlocks₁₁
  set B : Matrix (Fin 1) (Fin 1) (ZMod 2) :=
    (bl e61 (X : Matrix (Fin 7) (Fin 7) (ZMod 2))).toBlocks₂₂
  have hsub : X = (fromBlocks A 0 0 B).submatrix e61 e61 := by
    conv_lhs => rw [← submatrix_bl e61 (X : Matrix (Fin 7) (Fin 7) (ZMod 2))]
    rw [hblX]
  have hdet : A.det * B.det = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe X
    rw [hsub, Matrix.det_submatrix_equiv_self e61,
      Matrix.det_fromBlocks_zero₂₁] at h
    exact h
  have hkey : ∀ x y : ZMod 2, x * y = 1 → x = 1 ∧ y = 1 := by decide
  obtain ⟨hAdet, hBdet⟩ := hkey A.det B.det hdet
  have hB1 : B = 1 := by
    ext i j
    fin_cases i
    fin_cases j
    simpa [Matrix.det_fin_one] using hBdet
  refine ⟨⟨A, hAdet⟩, ?_⟩
  apply Subtype.ext
  change slUpperBlockMat 6 (ZMod 2) A = (X : Matrix (Fin 7) (Fin 7) (ZMod 2))
  rw [hsub, hB1, slUpperBlockMat_eq]

theorem syl7_SL7 : ∀ P : Subgroup SL(7, ZMod 2), IsPGroup 7 P →
    (∀ p ∈ P, p * zetaOf W7.T = zetaOf W7.T * p) → Nat.card P ≤ 7 := by
  intro P hP hC
  let Q : Subgroup SL(6, ZMod 2) := P.comap (slUpperBlockHom 6 (ZMod 2))
  have hmem : P ≤ (slUpperBlockHom 6 (ZMod 2)).range :=
    fun p hp => mem_range_iota6_of_commute p (hC p hp)
  have hQmap : Subgroup.map (slUpperBlockHom 6 (ZMod 2)) Q = P :=
    Subgroup.map_comap_eq_self hmem
  have hQ7 : IsPGroup 7 Q :=
    hP.comap_of_injective (slUpperBlockHom 6 (ZMod 2))
      (slUpperBlockHom_injective (n := 6) (F := ZMod 2))
  have hQc : ∀ q ∈ Q, q * zetaOf W6.T = zetaOf W6.T * q := by
    intro q hq
    have h := hC (slUpperBlockHom 6 (ZMod 2) q) hq
    rw [zeta7_eq] at h
    apply slUpperBlockHom_injective (n := 6) (F := ZMod 2)
    simpa only [map_mul] using h
  have hbound := syl7_SL6 Q hQ7 hQc
  have hcard : Nat.card P = Nat.card Q := by
    rw [← hQmap, Subgroup.card_map_of_injective (slUpperBlockHom_injective (n := 6)
      (F := ZMod 2))]
  rw [hcard]
  exact hbound

end CFSG.StandardType.GGFF

end
