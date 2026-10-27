module

public import CFSG.RankThree.PartOne.KE6.E8T3Arith
public import CFSG.RankThree.PartOne.KE.A1Weyl
public import CFSG.RankThree.Classical2.TwistedE6Phi3Torus
public import CFSG.RankThree.PartOne.KE6.E8T3Data

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 CFSG.RankThree.Lattice
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KE CFSG.RankThree.Chevalley
open scoped Matrix

variable {L : Type} [Field L]

theorem mem_ker_monomialHom_iff_forall_E8 (N : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ)
    (b : Fin Tag.E8.rank → Lˣ) :
    b ∈ (monomialHom (G := Lˣ) Nᵀ).ker ↔ ∀ μ, rootChar b (N *ᵥ μ) = 1 := by
  have hcol : ∀ j, rootChar b (N *ᵥ Pi.single j 1) =
      (monomialHom (G := Lˣ) Nᵀ b) j := fun j => by
    rw [monomialHom_apply, rootChar]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [Matrix.mulVec_single, Matrix.transpose_apply]
  rw [MonoidHom.mem_ker]
  constructor
  · intro h μ
    have hμ : μ = ∑ j, μ j • (Pi.single j 1 : Fin Tag.E8.rank → ℤ) := by
      ext i
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hμ, Matrix.mulVec_sum, rootChar_sum]
    refine Finset.prod_eq_one fun j _ => ?_
    rw [Matrix.mulVec_smul, rootChar_zsmul, hcol, h, Pi.one_apply, one_zpow]
  · intro h
    funext j
    rw [← hcol, h, Pi.one_apply]

theorem rootChar_scalar_sub {q : ℕ}
    (M : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ) (b : Fin Tag.E8.rank → Lˣ)
    (μ : Fin Tag.E8.rank → ℤ) :
    rootChar b ((Matrix.scalar (Fin Tag.E8.rank) (q : ℤ) - M) *ᵥ μ) =
      rootChar b μ ^ q * (rootChar b (M *ᵥ μ))⁻¹ := by
  rw [Matrix.sub_mulVec, rootChar_sub]
  have : (Matrix.scalar (Fin Tag.E8.rank) (q : ℤ)) *ᵥ μ = (q : ℤ) • μ := by
    ext i
    rw [Matrix.scalar_apply, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  rw [this, rootChar_zsmul, zpow_natCast]

theorem e8T3_mem_fixed_iff_ker {Fr : L →+* L} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q)
    (M : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ) (a : Fin Tag.E8.rank → Lˣ) :
    a ∈ fixedCharTuples M Fr ↔
      a ∈ (monomialHom (G := Lˣ) (Matrix.scalar (Fin Tag.E8.rank) (q : ℤ) - M)ᵀ).ker := by
  rw [mem_ker_monomialHom_iff_forall_E8, mem_fixedCharTuples_iff]
  refine forall_congr' fun μ => ?_
  rw [rootChar_scalar_sub, CTTorus.map_units_eq_pow hFr]
  constructor
  · intro h
    rw [h, mul_inv_cancel]
  · intro h
    exact (mul_inv_eq_one.1 h).symm

theorem det_scalar_sub_We {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (q : ℕ) :
    (Matrix.scalar (Fin Tag.E8.rank) (q : ℤ) - weylMatrix (e8T3We ε)).det =
      ((e8T3D ε q : ℕ) : ℤ) ^ 4 := by
  rw [weylMatrix_e8T3We hε, e8T3D_cast hε]
  have hee : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hrank : ε ^ Tag.E8.rank = 1 := by
    rcases hε with rfl | rfl
    · exact one_pow _
    · exact Even.neg_one_pow (by decide)
  have h1 : Matrix.scalar (Fin Tag.E8.rank) (q : ℤ) - ε • toMat Tag.E8.rank e8T3MList =
      ε • (Matrix.scalar (Fin Tag.E8.rank) (ε * (q : ℤ)) - toMat Tag.E8.rank e8T3MList) := by
    rw [smul_sub]
    congr 1
    ext i j
    simp only [Matrix.scalar_apply, Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]
    split_ifs
    · rw [← mul_assoc, hee, one_mul]
    · simp
  rw [h1, Matrix.det_smul, Fintype.card_fin, hrank, one_mul, det_sub_e8T3]
  have : (ε * (q : ℤ)) ^ 2 = (q : ℤ) ^ 2 := by rw [mul_pow, sq ε, hee, one_mul]
  rw [this]

theorem natCard_e8T3Fixed [IsAlgClosed L] {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {ℓ : ℕ}
    [Fact ℓ.Prime] [CharP L ℓ] {Fr : L →+* L} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q) (hq : ℓ ∣ q) :
    Nat.card (fixedCharTuples (weylMatrix (e8T3We ε)) Fr) = (e8T3D ε q) ^ 4 := by
  have hq0 : (q : L) = 0 := (CharP.cast_eq_zero_iff L ℓ q).2 hq
  have hdet := det_scalar_sub_We hε q
  have hne : (((Matrix.scalar (Fin Tag.E8.rank) (q : ℤ) - weylMatrix (e8T3We ε))ᵀ).det : L) ≠ 0 := by
    rw [Matrix.det_transpose, hdet]
    have h1 : (((e8T3D ε q : ℕ) : ℤ) : L) = 1 := by
      rw [e8T3D_cast hε]
      push_cast
      rw [hq0]
      ring
    push_cast at h1 ⊢
    rw [h1]
    norm_num
  have h := natCard_ker_monomialHom (Ω := L)
    (Matrix.scalar (Fin Tag.E8.rank) (q : ℤ) - weylMatrix (e8T3We ε))ᵀ hne
  have hker : fixedCharTuples (weylMatrix (e8T3We ε)) Fr =
      (monomialHom (G := Lˣ) (Matrix.scalar (Fin Tag.E8.rank) (q : ℤ) -
        weylMatrix (e8T3We ε))ᵀ).ker := Subgroup.ext fun a => e8T3_mem_fixed_iff_ker hFr _ a
  rw [hker, h, Matrix.det_transpose, hdet]
  simp

theorem e8T3_twistedTorus [IsAlgClosed L] {ε : ℤ}
    (n : ModGL Tag.E8 L) (hnm : n ∈ monomialSubgroup Tag.E8 L)
    (hnW : weylQuotientHom Tag.E8 L ⟨n, hnm⟩ = e8T3We ε) (Fr : L →+* L) :
    twistedTorusOf n (Units.map (entrywiseHom Fr)) =
      (fixedCharTuples (weylMatrix (e8T3We ε)) Fr).map (rootDiagUnitHom Tag.E8 L) := by
  have hnWv : ∀ u : Fin Tag.E8.rank → ℤ, weylQuotientHom Tag.E8 L ⟨n, hnm⟩ • u =
      (weylMatrix (e8T3We ε)) *ᵥ u := fun u => by rw [hnW, weylMatrix_mulVec]
  rw [← twistedFixedTuples_eq_fixedCharTuples hnWv Fr]
  exact twistedTorus_eq_map_twistedFixedTuples_of_weylImage hnm _ rfl Fr

theorem natCard_e8T3Torus [IsAlgClosed L] {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {ℓ : ℕ}
    [Fact ℓ.Prime] [CharP L ℓ] (n : ModGL Tag.E8 L) (hnm : n ∈ monomialSubgroup Tag.E8 L)
    (hnW : weylQuotientHom Tag.E8 L ⟨n, hnm⟩ = e8T3We ε) {Fr : L →+* L} {q : ℕ}
    (hFr : ∀ c, Fr c = c ^ q) (hq : ℓ ∣ q) :
    Nat.card (twistedTorusOf n (Units.map (entrywiseHom Fr))) = (e8T3D ε q) ^ 4 := by
  rw [e8T3_twistedTorus n hnm hnW Fr, Subgroup.card_map_of_injective rootDiagUnit_injective]
  exact natCard_e8T3Fixed hε hFr hq

end CFSG.RankThree.PartOne.KE6
