module

public import CFSG.RankThree.PartTwo.Sec4.Item413Cases
public import CFSG.LocalAnalysis.ComponentInitial.LinearModelOuterTwoPart

public section

namespace CFSG.RankThree.PartTwo.Sec21

namespace Item223CensusResProof

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Descent

variable {K K' : Type} [Field K] [Field K'] {n : ℕ}

@[expose] noncomputable def psOfSL
    (φ : SpecialLinearGroup (Fin n) K' ≃* SpecialLinearGroup (Fin n) K) :
    projectiveSL n K' ≃* projectiveSL n K :=
  QuotientGroup.congr (scalars n K') (scalars n K) φ (by
    rw [scalars_eq_center, scalars_eq_center]
    exact Sec4.map_center_mulEquiv φ)

theorem psOfSL_proj (φ : SpecialLinearGroup (Fin n) K' ≃* SpecialLinearGroup (Fin n) K)
    (g : SpecialLinearGroup (Fin n) K') : psOfSL φ (proj n K' g) = proj n K (φ g) :=
  QuotientGroup.congr_mk' _ _ _ _ g

theorem psOfSL_symm_proj (φ : SpecialLinearGroup (Fin n) K' ≃* SpecialLinearGroup (Fin n) K)
    (g : SpecialLinearGroup (Fin n) K) : (psOfSL φ).symm (proj n K g) = proj n K' (φ.symm g) := by
  apply (psOfSL φ).injective
  rw [MulEquiv.apply_symm_apply, psOfSL_proj, MulEquiv.apply_symm_apply]

theorem descendAut_congr (φ : SpecialLinearGroup (Fin n) K' ≃* SpecialLinearGroup (Fin n) K)
    (σ : MulAut (SpecialLinearGroup (Fin n) K')) :
    descendAut n K (MulAut.congr φ σ) = MulAut.congr (psOfSL φ) (descendAut n K' σ) := by
  ext x
  obtain ⟨g, rfl⟩ := proj_surjective n K x
  simp only [MulAut.congr_apply, MulEquiv.trans_apply]
  rw [descendAut_proj, psOfSL_symm_proj, descendAut_proj, psOfSL_proj]
  rfl

end Descent

section Field

variable {K K' : Type} [Field K] [Field K'] (ψ : K' ≃+* K) (n : ℕ)

@[expose] noncomputable def slEquiv :
    SpecialLinearGroup (Fin n) K' ≃* SpecialLinearGroup (Fin n) K where
  toFun := SpecialLinearGroup.map ψ.toRingHom
  invFun := SpecialLinearGroup.map ψ.symm.toRingHom
  left_inv g := by
    ext i j
    simp
  right_inv g := by
    ext i j
    simp
  map_mul' := map_mul _

theorem congr_conjAut_slEquiv (A : GL (Fin n) K') :
    MulAut.congr (psOfSL (slEquiv ψ n)) (conjAut n K' A) =
      conjAut n K (GeneralLinearGroup.map ψ.toRingHom A) := by
  ext x
  obtain ⟨g, rfl⟩ := proj_surjective n K x
  simp only [MulAut.congr_apply, MulEquiv.trans_apply]
  rw [psOfSL_symm_proj, conjAut_proj, psOfSL_proj, conjAut_proj]
  congr 1
  ext i j
  change (ψ.toRingHom.mapMatrix
      (((CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation
      n K' A ((slEquiv ψ n).symm g)) : SpecialLinearGroup (Fin n) K') :
      Matrix (Fin n) (Fin n) K')) i j = _
  rw [coe_slConjugation, coe_slConjugation, map_mul, map_mul]
  have h1 : ψ.toRingHom.mapMatrix ((((slEquiv ψ n).symm g : SpecialLinearGroup (Fin n) K')) :
      Matrix (Fin n) (Fin n) K') = (g : Matrix (Fin n) (Fin n) K) := by
    ext a b
    simp [slEquiv]
  have h2 : ψ.toRingHom.mapMatrix ((A⁻¹ : GL (Fin n) K') : Matrix (Fin n) (Fin n) K') =
      ((GeneralLinearGroup.map ψ.toRingHom A)⁻¹ : GL (Fin n) K) := by
    rw [← map_inv]
    rfl
  rw [h1, h2]
  rfl

theorem congr_mem_linearAutGroup_slEquiv {τ : MulAut (projectiveSL n K')}
    (hτ : τ ∈ linearAutGroup n K') :
    MulAut.congr (psOfSL (slEquiv ψ n)) τ ∈ linearAutGroup n K := by
  induction hτ using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨A, rfl⟩ := hx
    rw [congr_conjAut_slEquiv]
    exact conjAut_mem_linearAutGroup _
  | one => rw [map_one]; exact Subgroup.one_mem _
  | mul x y _ _ hx hy => rw [map_mul]; exact Subgroup.mul_mem _ hx hy
  | inv x _ hx => rw [map_inv]; exact Subgroup.inv_mem _ hx

end Field

section Orders

variable {K : Type} [Field K] [Finite K]

theorem card_SL_three : Nat.card (SpecialLinearGroup (Fin 3) K) =
    Nat.card K ^ 3 * (Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1) := by
  have : Fintype K := Fintype.ofFinite K
  rw [Matrix.card_SL_field, Nat.card_eq_fintype_card, Fin.prod_univ_three]
  set q := Fintype.card K
  have hq : 1 ≤ q := Fintype.card_pos
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one]
  have h1 : q ^ 3 - 1 = (q - 1) * (q ^ 2 + q + 1) := by
    zify [Nat.one_le_pow 3 q hq, hq]
    ring
  have h2 : q ^ 3 - q = q * (q ^ 2 - 1) := by
    zify [Nat.one_le_pow 2 q hq, show q ≤ q ^ 3 from Nat.le_self_pow (by norm_num) q]
    ring
  have h3 : q ^ 3 - q ^ 2 = q ^ 2 * (q - 1) := by
    zify [hq, Nat.pow_le_pow_right hq (show 2 ≤ 3 by norm_num)]
    ring
  rw [h1, h2, h3]
  rcases Nat.lt_or_ge q 2 with hq1 | hq2
  · have hq1' : q = 1 := by omega
    rw [hq1']
    simp
  · have hpos : 0 < q - 1 := by omega
    rw [show (q - 1) * (q ^ 2 + q + 1) * (q * (q ^ 2 - 1)) * (q ^ 2 * (q - 1)) =
      (q ^ 3 * (q ^ 2 - 1) * ((q - 1) * (q ^ 2 + q + 1))) * (q - 1) by ring,
      Nat.mul_div_cancel _ hpos]

theorem card_projectiveSL_three_mul :
    Nat.card (projectiveSL 3 K) * Nat.gcd 3 (Nat.card K - 1) =
      Nat.card (SpecialLinearGroup (Fin 3) K) := by
  rw [← CFSG.LocalAnalysis.ComponentInitial.card_scalars_eq_gcd K (by norm_num)]
  exact (Subgroup.card_eq_card_quotient_mul_card_subgroup (scalars 3 K)).symm

theorem sl3Poly_lt {q q' : ℕ} (hq : 2 ≤ q) (hqq : q < q') :
    q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1) < q' ^ 3 * (q' ^ 2 - 1) * (q' ^ 3 - 1) := by
  have h1 : q ^ 3 < q' ^ 3 := Nat.pow_lt_pow_left hqq (by norm_num)
  have h2 : q ^ 2 - 1 ≤ q' ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hqq.le 2) 1
  have h3 : q ^ 3 - 1 ≤ q' ^ 3 - 1 := Nat.sub_le_sub_right h1.le 1
  have h4 : 0 < q ^ 2 - 1 := by
    have : 2 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
    omega
  have h5 : 0 < q ^ 3 - 1 := by
    have : 2 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
    omega
  calc q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1) < q' ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1) := by
        apply Nat.mul_lt_mul_of_pos_right _ h5
        exact Nat.mul_lt_mul_of_pos_right h1 h4
    _ ≤ q' ^ 3 * (q' ^ 2 - 1) * (q' ^ 3 - 1) := by gcongr

theorem sl3Poly_inj {q q' : ℕ} (hq : 2 ≤ q) (hq' : 2 ≤ q')
    (h : q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1) = q' ^ 3 * (q' ^ 2 - 1) * (q' ^ 3 - 1)) : q = q' := by
  rcases lt_trichotomy q q' with hlt | heq | hgt
  · exact absurd h (sl3Poly_lt hq hlt).ne
  · exact heq
  · exact absurd h (sl3Poly_lt hq' hgt).ne'

theorem two_le_card_field (K : Type*) [Field K] [Finite K] : 2 ≤ Nat.card K := by
  have : Fintype K := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card]
  exact Fintype.one_lt_card

theorem card_eq_of_projectiveSL_three {K' : Type} [Field K'] [Finite K']
    (hK : 3 ∣ Nat.card K - 1) (hK' : 3 ∣ Nat.card K' - 1)
    (e : projectiveSL 3 K' ≃* projectiveSL 3 K) : Nat.card K' = Nat.card K := by
  have h := Nat.card_congr e.toEquiv
  have h1 := card_projectiveSL_three_mul (K := K)
  have h2 := card_projectiveSL_three_mul (K := K')
  rw [Nat.gcd_eq_left hK, card_SL_three] at h1
  rw [Nat.gcd_eq_left hK', card_SL_three] at h2
  exact sl3Poly_inj (two_le_card_field K') (two_le_card_field K) (by rw [← h1, ← h2, h])

end Orders

section Inndiag

variable {K K' : Type} [Field K] [Field K'] [Finite K] [Finite K']

theorem congr_mem_linearAutGroup (hK : 3 ∣ Nat.card K - 1) (hK' : 3 ∣ Nat.card K' - 1)
    (φ : projectiveSL 3 K' ≃* projectiveSL 3 K) {τ : MulAut (projectiveSL 3 K')}
    (hτ : τ ∈ linearAutGroup 3 K') : MulAut.congr φ τ ∈ linearAutGroup 3 K := by
  have hc := card_eq_of_projectiveSL_three hK hK' φ
  have : Fintype K := Fintype.ofFinite K
  have : Fintype K' := Fintype.ofFinite K'
  let ψ : K' ≃+* K := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hc])
  set Ψ := psOfSL (slEquiv ψ 3)
  set α : MulAut (projectiveSL 3 K') := φ.trans Ψ.symm
  have hφ : MulAut.congr φ τ = MulAut.congr Ψ (α * τ * α⁻¹) := by
    ext x
    simp [α, MulAut.congr_apply, MulAut.mul_apply, MulAut.inv_def]
  rw [hφ]
  apply congr_mem_linearAutGroup_slEquiv
  exact (KFacts.stdPinnedPSL_stable (n := 3) (K := K') (by norm_num)).normal.conj_mem τ hτ α

theorem descendAut_congr_mem_linearAutGroup (hK : 3 ∣ Nat.card K - 1)
    (hK' : 3 ∣ Nat.card K' - 1)
    (φ : SpecialLinearGroup (Fin 3) K' ≃* SpecialLinearGroup (Fin 3) K)
    {σ : MulAut (SpecialLinearGroup (Fin 3) K')} (hσ : descendAut 3 K' σ ∈ linearAutGroup 3 K') :
    descendAut 3 K (MulAut.congr φ σ) ∈ linearAutGroup 3 K := by
  rw [descendAut_congr]
  exact congr_mem_linearAutGroup hK hK' (psOfSL φ) hσ

end Inndiag

end Item223CensusResProof

end CFSG.RankThree.PartTwo.Sec21
