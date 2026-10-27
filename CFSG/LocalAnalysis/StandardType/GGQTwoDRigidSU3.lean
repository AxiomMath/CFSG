module

public import CFSG.ClassicalInvolution.Balance.StrongPowSuBlocks
import CFSG.LocalAnalysis.StandardType.GGQTwoDRigidSU3Diag
import CFSG.ClassicalInvolution.Balance.StrongPowSuDiag
import CFSG.LocalAnalysis.StandardType.GGQTwoDRigidGen
import CFSG.LocalAnalysis.StandardType.GGQTwoSixLem62
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.ClassicalInvolution.Balance.PassTwoFinal
public import CFSG.ClassicalInvolution.Models.LinearFrames
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieClassical
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieE6E7Triality
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwo
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank
import CFSG.ClassicalInvolution.Models.UnitaryPairs
import CFSG.ClassicalInvolution.Models.UnitaryPairs.Pairs

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open CFSG.ClassicalInvolution.RouteD.Gaps (diagGL coe_diagGL coe_diagGL_inv
  exists_diagGL_of_offdiag_zero)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (unitLambdaDiag unitLambdaDiag_mem
  unitSignedSwapMatrix unitSignedSwapMatrix_mem)

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
private theorem cube_eq_zero_or_one (hK : Nat.card K = 4) (x : K) :
    x ^ 3 = 0 ∨ x ^ 3 = 1 := by
  by_cases hx : x = 0
  · left; simp [hx]
  · exact Or.inr (cube_eq_one_of_ne_zero hK hx)

omit [Finite K] [CharP K 2] in
private theorem conj_eq_self_of_ne_zero (x y : K) (hy : y ≠ 0) : y * x * y⁻¹ = x := by
  rw [mul_comm y x, mul_inv_cancel_right₀ hy]

private theorem centralizer_diagSub_le (hK : Nat.card K = 4) :
    ∀ y : Su K 2 1 3, (∀ a ∈ diagSub, y * a = a * y) → y ∈ diagSub := by
  intro y hy
  have hdata : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 K :=
    ⟨Nat.prime_two, by norm_num, by rw [hK]; norm_num⟩
  have hK' : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  have hun : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK]
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf g = 3 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hun]
  have hg1 : g ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hord
    omega
  have hg2 : g ^ 2 ≠ 1 := by
    intro h
    have hdvd : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one h
    rw [hord] at hdvd
    omega
  have hg2g : g ^ 2 ≠ g := by
    intro h
    have h' : g * g = g * 1 := by simpa [pow_two] using h
    exact hg1 (mul_left_cancel h')
  have hg3 : g ^ 3 = 1 := by
    have h := pow_orderOf_eq_one g
    rwa [hord] at h
  have hg3K : ((g : Kˣ) : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hg3, Units.val_one]
  have hg1K : ((g : Kˣ) : K) ≠ 1 := fun h => hg1 (Units.ext h)
  have hg2K : ((g : Kˣ) : K) ^ 2 ≠ 1 := fun h =>
    hg2 (Units.ext (by simpa [Units.val_pow_eq_pow_val] using h))
  have hg2gK : ((g : Kˣ) : K) ^ 2 ≠ ((g : Kˣ) : K) := fun h =>
    hg2g (Units.ext (by simpa [Units.val_pow_eq_pow_val] using h))
  have hneg : (-1 : K) = 1 := neg_one_eq_one_iff.mpr (ringChar.eq K 2)
  have hneg1 : ((g : Kˣ) : K) ≠ -1 := by rw [hneg]; exact hg1K
  have hg2gK' : ((g : Kˣ) : K) ≠ ((g : Kˣ) : K) ^ 2 := fun h => hg2gK h.symm
  have hg1K' : (1 : K) ≠ ((g : Kˣ) : K) := fun h => hg1K h.symm
  have hg2K' : (1 : K) ≠ ((g : Kˣ) : K) ^ 2 := fun h => hg2K h.symm
  have hginv : ((g : Kˣ) : K)⁻¹ = ((g : Kˣ) : K) ^ 2 := by
    apply inv_eq_of_mul_eq_one_left
    rw [← pow_succ, hg3K]
  have hbar : hdata.bar ((g : Kˣ) : K) = ((g : Kˣ) : K) ^ 2 := by
    rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_apply]
    norm_num
  have hc : hdata.bar ((g : Kˣ) : K) * ((g : Kˣ) : K) = 1 := by
    rw [hbar, ← pow_succ, hg3K]
  obtain ⟨M, hM, hMmem⟩ := unitLambdaDiag_mem (h := hdata) (c := ((g : Kˣ) : K))
    (m := 3) (i := 0) (j := 1) hc (by decide)
  let t : Su K 2 1 3 := ⟨M, mem_SUid_of_mem_gramSU hK' hdata hMmem⟩
  have htmat : ((t : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal (unitLambdaDiag ((g : Kˣ) : K) 0 1) := hM
  have htA : t ∈ diagSub := by
    intro i j hij
    rw [htmat, Matrix.diagonal_apply, if_neg hij]
  have hcomm := hy t htA
  have hmat := congrArg (fun z : Su K 2 1 3 =>
    ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) hcomm
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, htmat] at hmat
  have hne : ∀ p q : Fin 3, p ≠ q →
      unitLambdaDiag ((g : Kˣ) : K) 0 1 p ≠
        unitLambdaDiag ((g : Kˣ) : K) 0 1 q := by
    intro p q hpq
    fin_cases p <;> fin_cases q <;> simp_all [unitLambdaDiag]
  intro p q hpq
  have h := congrFun (congrFun hmat p) q
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h
  have hzero : (((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) p q *
      (unitLambdaDiag ((g : Kˣ) : K) 0 1 q - unitLambdaDiag ((g : Kˣ) : K) 0 1 p) = 0 := by
    rw [mul_sub, h]
    ring
  exact (mul_eq_zero.mp hzero).resolve_right (sub_ne_zero.mpr (Ne.symm (hne p q hpq)))

omit [Finite K] in
private theorem cube_pair_cases (hK : Nat.card K = 4) {a b : K} (h : a ^ 3 + b ^ 3 = 1) :
    (a ≠ 0 ∧ b = 0) ∨ (a = 0 ∧ b ≠ 0) := by
  have ha := cube_eq_zero_or_one hK a
  have hb := cube_eq_zero_or_one hK b
  have hone : (1 : K) + 1 = 0 := by
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    simpa [one_add_one_eq_two] using h2
  rcases ha with ha0 | ha1
  · rcases hb with hb0 | hb1
    · exfalso
      rw [ha0, hb0] at h
      norm_num at h
    · refine Or.inr ⟨?_, ?_⟩
      · exact (pow_eq_zero_iff (by norm_num : 3 ≠ 0)).mp ha0
      · rintro rfl
        norm_num at hb1
  · rcases hb with hb0 | hb1
    · refine Or.inl ⟨?_, ?_⟩
      · rintro rfl
        norm_num at ha1
      · exact (pow_eq_zero_iff (by norm_num : 3 ≠ 0)).mp hb0
    · exfalso
      rw [ha1, hb1, hone] at h
      exact zero_ne_one h

private theorem sum_cube_col (g : Su K 2 1 3) (l : Fin 3) :
    ∑ k : Fin 3, (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) k l) ^ 3 = 1 := by
  have h := congrFun (congrFun g.2.2 l) l
  simp only [conjTr, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Matrix.one_apply, unitaryInvolution_apply, pow_one, if_true] at h
  simpa only [pow_succ] using h

private theorem coordBlockSU_entry_unique (hK : Nat.card K = 4) {J : Finset (Fin 3)}
    (hJ : J.card = 2) {g : Su K 2 1 3} (hg : g ∈ coordBlockSU K 2 1 J) (l : Fin 3) :
    ∃! p : Fin 3, (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) p l ≠ 0 := by
  by_cases hl : l ∈ J
  · obtain ⟨i, j, hij, hJeq⟩ := Finset.card_eq_two.mp hJ
    have hsum := sum_cube_col g l
    have hzero : ∀ k : Fin 3, k ∉ J →
        (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) k l = 0 := by
      intro k hk
      have h := (mem_coordBlockSU_iff.mp hg) k l (Or.inl hk)
      have hkl : k ≠ l := fun h' => hk (h' ▸ hl)
      simpa [hkl] using h
    have hsumJ : Finset.sum J (fun k =>
        (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) k l ^ 3) = 1 := by
      rw [← hsum]
      exact Finset.sum_subset (Finset.subset_univ J)
        (fun k _ hk => by rw [hzero k hk]; simp)
    rw [hJeq, Finset.sum_pair hij] at hsumJ
    rcases cube_pair_cases hK hsumJ with ⟨hai, hbj⟩ | ⟨hai, hbj⟩
    · refine ⟨i, hai, ?_⟩
      intro p hp
      have hpJ : p ∈ J := by
        by_contra hpJ
        exact hp (hzero p hpJ)
      rw [hJeq] at hpJ
      simp only [Finset.mem_insert, Finset.mem_singleton] at hpJ
      rcases hpJ with rfl | rfl
      · rfl
      · exfalso; exact hp hbj
    · refine ⟨j, hbj, ?_⟩
      intro p hp
      have hpJ : p ∈ J := by
        by_contra hpJ
        exact hp (hzero p hpJ)
      rw [hJeq] at hpJ
      simp only [Finset.mem_insert, Finset.mem_singleton] at hpJ
      rcases hpJ with rfl | rfl
      · exfalso; exact hp hai
      · rfl
  · refine ⟨l, ?_, ?_⟩
    · have h := (mem_coordBlockSU_iff.mp hg) l l (Or.inr hl)
      change (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) l l ≠ 0
      have h1 : (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) l l = 1 := by
        simpa using h
      rw [h1]
      exact fun h2 => zero_ne_one h2.symm
    · intro p hp
      have h := (mem_coordBlockSU_iff.mp hg) p l (Or.inr hl)
      by_contra hpl
      have hp0 : (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) p l = 0 := by
        simpa [hpl] using h
      exact hp hp0

private theorem entry_mul_conj_diag (g a : Su K 2 1 3) (ha : a ∈ diagSub) (p q : Fin 3) :
    (((g * a * g⁻¹ : Su K 2 1 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) p q =
      ∑ l : Fin 3, (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) p l *
        (((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) l l *
        unitaryInvolution K 2 1 ((((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) q l) := by
  have hinv : (((g⁻¹ : Su K 2 1 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      conjTr (unitaryInvolution K 2 1)
        (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
    have hmul : (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) *
        (((g⁻¹ : Su K 2 1 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
      have h : (g : GL (Fin 3) K) * ((g⁻¹ : Su K 2 1 3) : GL (Fin 3) K) = 1 := by
        simp
      simp
    have hconj : conjTr (unitaryInvolution K 2 1)
          (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) =
        (((g⁻¹ : Su K 2 1 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      calc conjTr (unitaryInvolution K 2 1)
            (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) =
          conjTr (unitaryInvolution K 2 1)
            (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) * 1 := (mul_one _).symm
        _ = conjTr (unitaryInvolution K 2 1)
              (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) *
            ((((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) *
              (((g⁻¹ : Su K 2 1 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
              rw [hmul]
        _ = (conjTr (unitaryInvolution K 2 1)
              (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) *
            (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))) *
              (((g⁻¹ : Su K 2 1 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
              rw [Matrix.mul_assoc]
        _ = (((g⁻¹ : Su K 2 1 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
              rw [g.2.2, Matrix.one_mul]
    exact hconj.symm
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hinv]
  simp only [conjTr, Matrix.transpose_apply, Matrix.map_apply, Matrix.mul_apply]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_eq_single l]
  · intro k _ hkl
    rw [ha l k (Ne.symm hkl)]
    simp
  · intro hl
    simp at hl

private theorem coordBlockSU_le_normalizer_diagSub (hK : Nat.card K = 4) {J : Finset (Fin 3)}
    (hJ : J.card = 2) :
    coordBlockSU K 2 1 J ≤ Subgroup.normalizer (diagSub (K := K) : Set (Su K 2 1 3)) := by
  have hconj : ∀ x ∈ coordBlockSU K 2 1 J, ∀ a ∈ diagSub,
      x * a * x⁻¹ ∈ diagSub := by
    intro x hx a ha p q hpq
    rw [entry_mul_conj_diag x a ha p q]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hxl : (((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) p l = 0
    · simp [hxl]
    · obtain ⟨r, -, huniq⟩ := coordBlockSU_entry_unique hK hJ hx l
      have hql : (((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) q l = 0 := by
        by_contra hqne
        exact hpq ((huniq p hxl).trans (huniq q hqne).symm)
      simp [hql]
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro a
  refine ⟨fun ha => hconj g hg a ha, fun ha => ?_⟩
  have h := hconj (g⁻¹) (Subgroup.inv_mem _ hg) (g * a * g⁻¹) ha
  rwa [show g⁻¹ * (g * a * g⁻¹) * (g⁻¹)⁻¹ = a by group] at h

private theorem diagSub_eq_mul_coordBlocks (hK : Nat.card K = 4) {g : Su K 2 1 3}
    (hg : g ∈ diagSub) :
    ∃ g1 g2 : Su K 2 1 3,
      g1 ∈ coordBlockSU K 2 1 ({0, 1} : Finset (Fin 3)) ∧
      g2 ∈ coordBlockSU K 2 1 ({1, 2} : Finset (Fin 3)) ∧
      g1 ^ 3 = 1 ∧ g2 ^ 3 = 1 ∧ g = g1 * g2 := by
  obtain ⟨u, hu⟩ := exists_diagGL_of_offdiag_zero (g : GL (Fin 3) K) hg
  have hdet : (((diagGL u : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rw [← hu]; exact g.2.1
  have hprodK : (∏ i, (u i : K)) = 1 := by
    rw [← Matrix.det_diagonal, ← coe_diagGL]
    exact hdet
  have hprodU : u 0 * u 1 * u 2 = 1 := by
    apply Units.ext
    simpa [Fin.prod_univ_three, Units.val_mul, mul_assoc] using hprodK
  let d1 : Fin 3 → Kˣ := ![u 0, (u 0)⁻¹, 1]
  let d2 : Fin 3 → Kˣ := ![1, u 0 * u 1, u 2]
  have hdet1 : (∏ i, (d1 i : K)) = 1 := by
    rw [Fin.prod_univ_three]
    simp [d1]
  have hdet2 : (∏ i, (d2 i : K)) = 1 := by
    rw [Fin.prod_univ_three]
    simpa [Fin.prod_univ_three, d2, Units.val_mul, mul_assoc] using hprodK
  let g1 : Su K 2 1 3 := ⟨diagGL d1, diagGL_mem_SUid hK hdet1⟩
  let g2 : Su K 2 1 3 := ⟨diagGL d2, diagGL_mem_SUid hK hdet2⟩
  have hg1b : g1 ∈ coordBlockSU K 2 1 ({0, 1} : Finset (Fin 3)) := by
    apply diagGL_mem_coordBlockSU hK hdet1
    intro i hi
    fin_cases i <;> simp_all [d1]
  have hg2b : g2 ∈ coordBlockSU K 2 1 ({1, 2} : Finset (Fin 3)) := by
    apply diagGL_mem_coordBlockSU hK hdet2
    intro i hi
    fin_cases i <;> simp_all [d2]
  have hg1A : g1 ∈ diagSub := by
    intro i j hij
    change ((diagGL d1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j = 0
    rw [coe_diagGL, Matrix.diagonal_apply, if_neg hij]
  have hg2A : g2 ∈ diagSub := by
    intro i j hij
    change ((diagGL d2 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j = 0
    rw [coe_diagGL, Matrix.diagonal_apply, if_neg hij]
  have hd12 : d1 * d2 = u := by
    funext i
    fin_cases i <;> simp [d1, d2]
  have hdiagmul : (diagGL d1 * diagGL d2 : GL (Fin 3) K) = diagGL u := by
    rw [← hd12]
    refine Units.ext (Matrix.ext fun i j => ?_)
    rw [Units.val_mul, coe_diagGL, coe_diagGL, coe_diagGL, Matrix.diagonal_mul_diagonal]
    rfl
  refine ⟨g1, g2, hg1b, hg2b, diagSub_pow_three hK hg1A, diagSub_pow_three hK hg2A, ?_⟩
  apply Subtype.ext
  apply Units.ext
  rw [hu, Subgroup.coe_mul, Units.val_mul]
  change (((diagGL u : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) =
    (((g1 : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) *
      (((g2 : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K)
  rw [show ((g1 : GL (Fin 3) K)) = diagGL d1 from rfl,
    show ((g2 : GL (Fin 3) K)) = diagGL d2 from rfl, ← hdiagmul]
  rfl

omit [Finite K] [CharP K 2] in
private theorem conj_scalar_diagonal (d : Fin 3 → Kˣ) (hd : ∀ i, d i = d 0)
    (M : Matrix (Fin 3) (Fin 3) K) :
    Matrix.diagonal (fun i => (d i : K)) * M *
      Matrix.diagonal (fun i => ((d i : K))⁻¹) = M := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, hd i, hd j]
  field_simp [(d 0).ne_zero]

theorem mulAut_su3_eq_one (hK : Nat.card K = 4) (α : MulAut (Su K 2 1 3)) {k : ℕ}
    (hk : α ^ 2 ^ k = 1)
    (h01 : ∀ g ∈ coordBlockSU K 2 1 ({0, 1} : Finset (Fin 3)), g ^ 3 = 1 → α g = g)
    (h12 : ∀ g ∈ coordBlockSU K 2 1 ({1, 2} : Finset (Fin 3)), g ^ 3 = 1 → α g = g) :
    α = 1 := by
  have hαA : ∀ a ∈ diagSub (K := K), α a = a := by
    intro a ha
    obtain ⟨g1, g2, h1b, h2b, h13, h23, hge⟩ := diagSub_eq_mul_coordBlocks hK ha
    rw [hge, map_mul, h01 g1 h1b h13, h12 g2 h2b h23]
  have hC : ∀ y : Su K 2 1 3, (∀ a ∈ diagSub (K := K), y * a = a * y) →
      y ∈ diagSub (K := K) := centralizer_diagSub_le hK
  have hodd : ∀ a ∈ diagSub (K := K), ∃ n : ℕ, Odd n ∧ a ^ n = 1 := by
    intro a ha
    exact ⟨3, by decide, diagSub_pow_three hK ha⟩
  have hfix01 : ∀ g ∈ coordBlockSU K 2 1 ({0, 1} : Finset (Fin 3)), α g = g :=
    fun g hg => mulAut_apply_eq_self_of_mem_normalizer_of_odd α hαA hC hodd hk
      (coordBlockSU_le_normalizer_diagSub hK (by decide) hg)
  have hfix12 : ∀ g ∈ coordBlockSU K 2 1 ({1, 2} : Finset (Fin 3)), α g = g :=
    fun g hg => mulAut_apply_eq_self_of_mem_normalizer_of_odd α hαA hC hodd hk
      (coordBlockSU_le_normalizer_diagSub hK (by decide) hg)
  have hmap01 : (coordBlockSU K 2 1 ({0, 1} : Finset (Fin 3))).map α.toMonoidHom =
      coordBlockSU K 2 1 ({0, 1} : Finset (Fin 3)) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change α y ∈ coordBlockSU K 2 1 ({0, 1} : Finset (Fin 3))
      rw [hfix01 y hy]
      exact hy
    · intro hx
      exact ⟨x, hx, hfix01 x hx⟩
  have hmap12 : (coordBlockSU K 2 1 ({1, 2} : Finset (Fin 3))).map α.toMonoidHom =
      coordBlockSU K 2 1 ({1, 2} : Finset (Fin 3)) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change α y ∈ coordBlockSU K 2 1 ({1, 2} : Finset (Fin 3))
      rw [hfix12 y hy]
      exact hy
    · intro hx
      exact ⟨x, hx, hfix12 x hx⟩
  obtain ⟨d, σ, hd⟩ := SixPoint.qTwoSix_lem62 hK α hmap01 hmap12
  have hdata : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 K :=
    ⟨Nat.prime_two, by norm_num, by rw [hK]; norm_num⟩
  have hK' : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  have hσfix : ∀ a : K, a ≠ 0 → σ a = a := by
    intro a ha
    let u : Kˣ := Units.mk0 a ha
    have hc : hdata.bar (a : K) * (a : K) = 1 := by
      have hbar : hdata.bar (a : K) = (a : K) ^ 2 := by
        rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_apply]
        norm_num
      rw [hbar, ← pow_succ, cube_eq_one_of_ne_zero hK ha]
    obtain ⟨M, hM, hMmem⟩ := unitLambdaDiag_mem (h := hdata) (c := (a : K))
      (m := 3) (i := 0) (j := 1) hc (by decide)
    let t : Su K 2 1 3 := ⟨M, mem_SUid_of_mem_gramSU hK' hdata hMmem⟩
    have htmat : ((t : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        Matrix.diagonal (unitLambdaDiag (a : K) 0 1) := hM
    have htblock : t ∈ coordBlockSU K 2 1 ({0, 1} : Finset (Fin 3)) :=
      torEl_mem (hi := by decide) (hj := by decide) htmat
    have hft : α t = t := hfix01 t htblock
    have h := hd t
    rw [hft, htmat, Matrix.diagonal_map (f := σ) (map_zero σ)] at h
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal] at h
    have h00 := congrFun (congrFun h 0) 0
    simp only [Matrix.diagonal_apply, unitLambdaDiag, if_true] at h00
    have hσu : σ (a : K) = (a : K) := by
      calc σ (a : K) = (d 0 : K) * σ (a : K) * ((d 0 : K)⁻¹) :=
            (conj_eq_self_of_ne_zero _ _ (d 0).ne_zero).symm
        _ = (a : K) := by simpa using h00.symm
    simpa [u] using hσu
  have hσ : σ = RingEquiv.refl K := by
    refine RingEquiv.ext fun a => ?_
    by_cases ha : a = 0
    · simp [ha]
    · exact hσfix a ha
  have hswap : ∀ {J : Finset (Fin 3)} {i j : Fin 3}, i ∈ J → j ∈ J → i ≠ j →
      (∀ w ∈ coordBlockSU K 2 1 J, α w = w) → d i = d j := by
    intro J i j hi hj hij hfix
    obtain ⟨M, hM, hMmem⟩ := unitSignedSwapMatrix_mem (h := hdata) (m := 3) (i := i) (j := j) hij
    let w : Su K 2 1 3 := ⟨M, mem_SUid_of_mem_gramSU hK' hdata hMmem⟩
    have hwmat : ((w : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        unitSignedSwapMatrix i j := hM
    have hwblock : w ∈ coordBlockSU K 2 1 J := swapEl_mem hi hj hwmat
    have hft : α w = w := hfix w hwblock
    have h := hd w
    rw [hσ, hft, hwmat] at h
    have hmap : (unitSignedSwapMatrix i j).map ⇑(RingEquiv.refl K) =
        unitSignedSwapMatrix i j := by
      ext a b
      rfl
    rw [hmap] at h
    have hinv : Matrix.diagonal (fun l => (((d l)⁻¹ : Kˣ) : K)) =
        Matrix.diagonal (fun l => ((d l : K))⁻¹) := by
      congr 1
      funext l
      exact Units.val_inv_eq_inv_val (d l)
    rw [hinv] at h
    have hDinvD : Matrix.diagonal (fun l => ((d l : K))⁻¹) *
        Matrix.diagonal (fun l => (d l : K)) = 1 := by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext l
      exact inv_mul_cancel₀ (d l).ne_zero
    have hW : unitSignedSwapMatrix i j * Matrix.diagonal (fun l => (d l : K)) =
        Matrix.diagonal (fun l => (d l : K)) * unitSignedSwapMatrix i j := by
      calc unitSignedSwapMatrix i j * Matrix.diagonal (fun l => (d l : K)) =
          (Matrix.diagonal (fun l => (d l : K)) * unitSignedSwapMatrix i j *
            Matrix.diagonal (fun l => ((d l : K))⁻¹)) *
            Matrix.diagonal (fun l => (d l : K)) := by
            conv_lhs => rw [h]
        _ = Matrix.diagonal (fun l => (d l : K)) * unitSignedSwapMatrix i j *
            (Matrix.diagonal (fun l => ((d l)⁻¹ : K)) *
              Matrix.diagonal (fun l => (d l : K))) := by noncomm_ring
        _ = Matrix.diagonal (fun l => (d l : K)) * unitSignedSwapMatrix i j := by
            rw [hDinvD, Matrix.mul_one]
    have hcomm' : Matrix.diagonal (fun l => (d l : K)) * unitSignedSwapMatrix i j =
        unitSignedSwapMatrix i j * Matrix.diagonal (fun l => (d l : K)) := hW.symm
    have hdiag := diag_eq_of_comm_swap (g := Matrix.diagonal (fun l => (d l : K))) hcomm'
    exact Units.ext (by simpa [Matrix.diagonal_apply] using hdiag)
  have hd01 : d 0 = d 1 :=
    hswap (J := ({0, 1} : Finset (Fin 3))) (i := 0) (j := 1) (by decide) (by decide)
      (by decide) hfix01
  have hd12 : d 1 = d 2 :=
    hswap (J := ({1, 2} : Finset (Fin 3))) (i := 1) (j := 2) (by decide) (by decide)
      (by decide) hfix12
  have hdall : ∀ i, d i = d 0 := by
    intro i
    fin_cases i
    · rfl
    · exact hd01.symm
    · exact hd12.symm.trans hd01.symm
  refine MulEquiv.ext fun u => ?_
  have h := hd u
  rw [hσ] at h
  have hmap : (((u : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)).map
      ⇑(RingEquiv.refl K) = ((u : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    ext i j
    rfl
  rw [hmap] at h
  have hinv : Matrix.diagonal (fun i => (((d i)⁻¹ : Kˣ) : K)) =
      Matrix.diagonal (fun i => ((d i : K))⁻¹) := by
    congr 1
    funext i
    exact Units.val_inv_eq_inv_val (d i)
  rw [hinv] at h
  rw [conj_scalar_diagonal d hdall ((u : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)] at h
  exact Subtype.ext (Units.ext h)

end CFSG.StandardType.QTwo

end
