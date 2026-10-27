module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148APGLConjRank
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24PSU3Classes
import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd.FullUni
import CFSG.HardMathSupport.Foote.ModuleExclusions.PSUAlg
import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryNorm
import CFSG.Open.PGLModelStated
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Foundations
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.RankThree.PartTwo.Sec8.Pairs
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
import CFSG.RankThree.PartTwo.Sec6.Item612Core
import CFSG.RankThree.PartTwo.Sec6.Statements
import Certificates.Certificate43

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148A

open Matrix
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
  (twExists_pow_three_eq_of_nine_dvd twExists_unitary_mul_eq_diagonal
    twPow_three_eq_of_mul_eq_diagonal twDet_eq_of_mul_eq_diagonal)
open CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd (adjU_mul)

theorem exists_e9_of_commute {X : Type} [Group X] [Finite X] {y z : X} (hy3 : y ^ 3 = 1)
    (hy1 : y ≠ 1) (hz3 : z ^ 3 = 1) (hzy : z * y = y * z) (hz : z ∉ Subgroup.zpowers y) :
    ∃ E : Subgroup X, y ∈ E ∧ CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcomm : ∀ s ∈ Subgroup.zpowers y, ∀ t ∈ Subgroup.zpowers z, s * t = t * s := by
    rintro s ⟨i, rfl⟩ t ⟨j, rfl⟩
    exact (Commute.zpow_zpow (Commute.symm hzy) i j).eq
  refine ⟨Subgroup.zpowers y ⊔ Subgroup.zpowers z,
    Subgroup.mem_sup_left (Subgroup.mem_zpowers y),
    Ronan148W.isElemAbelian_sup_of_commute (Ronan148W.isElemAbelian_zpowers hy3)
      (Ronan148W.isElemAbelian_zpowers hz3) hcomm, ?_⟩
  have hz1 : z ≠ 1 := fun h => hz (h ▸ Subgroup.one_mem _)
  have hoy : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hoz : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  have hinf : Subgroup.zpowers y ⊓ Subgroup.zpowers z = ⊥ := by
    have hdvd : Nat.card ↥(Subgroup.zpowers y ⊓ Subgroup.zpowers z) ∣ 3 := by
      rw [← hoz, ← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact Subgroup.card_eq_one.mp h
    · exfalso
      have heq : Subgroup.zpowers y ⊓ Subgroup.zpowers z = Subgroup.zpowers z :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [Nat.card_zpowers, hoz, h])
      have hzI : z ∈ Subgroup.zpowers y ⊓ Subgroup.zpowers z := by
        rw [heq]
        exact Subgroup.mem_zpowers z
      exact hz hzI.1
  have hcard := Sec6.card_sup_mul_card_inf (Ronan148W.le_normalizer_of_commute hcomm)
  rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, hoy, hoz] at hcard
  exact hcard

section Mat

variable {p f : ℕ} {K : Type} [Field K]

theorem exists_isPrimitiveRoot_nine_bar (hU : UnitaryFieldData p f K) (h9 : 9 ∣ p ^ f + 1) :
    ∃ ζ : K, IsPrimitiveRoot ζ 9 ∧ hU.bar ζ * ζ = 1 := by
  have := hU.finite
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  have hq := hU.one_lt_pow
  have hm : 9 ∣ orderOf g := by
    rw [hg, Nat.card_units, hU.card_eq_sq]
    have hsq : (p ^ f) ^ 2 - 1 = (p ^ f + 1) * (p ^ f - 1) := by
      zify [hq.le, Nat.one_le_pow 2 (p ^ f) (by omega)]
      ring
    rw [hsq]
    exact Dvd.dvd.mul_right h9 _
  have hg0 : orderOf g ≠ 0 := by rw [hg]; exact Nat.card_pos.ne'
  obtain ⟨ζ, hζ⟩ : ∃ ζ : K, IsPrimitiveRoot ζ 9 := by
    refine ⟨((g ^ (orderOf g / 9) : Kˣ) : K), IsPrimitiveRoot.coe_units_iff.mpr ?_⟩
    have := IsPrimitiveRoot.orderOf (g ^ (orderOf g / 9))
    rwa [orderOf_pow_orderOf_div hg0 hm] at this
  refine ⟨ζ, hζ, ?_⟩
  obtain ⟨k, hk⟩ := h9
  rw [mul_comm, ← UnitaryFieldData.norm, hU.norm_eq_pow, hk]
  calc ζ ^ (9 * k) = (ζ ^ 9) ^ k := by ring
    _ = 1 := by rw [hζ.pow_eq_one, one_pow]

theorem exists_isometry_commute_of_cube_scalar (hU : UnitaryFieldData p f K) (h9 : 9 ∣ p ^ f + 1)
    {A : Matrix (Fin 3) (Fin 3) K} (hAu : (A.map hU.bar)ᵀ * A = 1) (hAdet : A.det = 1) {α : K}
    (hA3 : A ^ 3 = α • 1) :
    ∃ Z : Matrix (Fin 3) (Fin 3) K, (Z.map hU.bar)ᵀ * Z = 1 ∧ Z.det = 1 ∧
      (∃ c : K, Z ^ 3 = c • 1) ∧ Z * A = A * Z ∧
      ∀ k < 3, ∀ c : K, c ≠ 0 → c • Z ≠ A ^ k := by
  classical
  have h3 : 3 ∣ p ^ f + 1 := Nat.dvd_trans (by norm_num) h9
  have hα3 : α ^ 3 = 1 := by
    have h := congrArg Matrix.det hA3
    rw [Matrix.det_pow, hAdet, one_pow, Matrix.det_smul, Matrix.det_one, mul_one,
      Fintype.card_fin] at h
    exact h.symm
  have hα0 : α ≠ 0 := by
    rintro rfl
    norm_num at hα3
  obtain ⟨s, hs, hsu⟩ := twExists_pow_three_eq_of_nine_dvd hU h9 hα3
  obtain ⟨P, e, hPu, hAP⟩ := twExists_unitary_mul_eq_diagonal hU h3 hAu hA3 hs hsu
  have he3 := twPow_three_eq_of_mul_eq_diagonal hPu hA3 hAP
  obtain ⟨Q, hQ⟩ : ∃ Q : Matrix (Fin 3) (Fin 3) K, Q = (P.map hU.bar)ᵀ := ⟨_, rfl⟩
  have hQP : Q * P = 1 := by rw [hQ]; exact hPu
  have hPQ : P * Q = 1 := mul_eq_one_comm.mp hQP
  have hQ' : (Q.map hU.bar)ᵀ = P := by
    rw [hQ]
    ext i j
    simp [UnitaryFieldData.bar_bar]
  have hAeq : A = P * diagonal e * Q := by
    rw [← hAP, Matrix.mul_assoc, hPQ, Matrix.mul_one]
  have hpow : ∀ (M : Matrix (Fin 3) (Fin 3) K) (k : ℕ), (P * M * Q) ^ k = P * M ^ k * Q := by
    intro M k
    induction k with
    | zero => rw [pow_zero, pow_zero, Matrix.mul_one, hPQ]
    | succ k ih =>
      rw [pow_succ, ih, pow_succ]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Q P, hQP, Matrix.one_mul]
  have hAk : ∀ k : ℕ, A ^ k = P * diagonal e ^ k * Q := fun k => by rw [hAeq]; exact hpow _ k
  have key : ∀ w : Fin 3 → K, (∀ i, hU.bar (w i) * w i = 1) → w 0 * w 1 * w 2 = 1 →
      (∀ i, w i ^ 3 = w 0 ^ 3) →
      (∀ k < 3, ∀ c : K, c ≠ 0 → ∃ i, c * w i ≠ e i ^ k) →
      ∃ Z : Matrix (Fin 3) (Fin 3) K, (Z.map hU.bar)ᵀ * Z = 1 ∧ Z.det = 1 ∧
        (∃ c : K, Z ^ 3 = c • 1) ∧ Z * A = A * Z ∧
        ∀ k < 3, ∀ c : K, c ≠ 0 → c • Z ≠ A ^ k := by
    intro w hwu hwd hw3 hwk
    have hD : ((diagonal w).map hU.bar)ᵀ * diagonal w = 1 := by
      rw [Matrix.diagonal_map (map_zero hU.bar), Matrix.diagonal_transpose,
        Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      exact hwu i
    refine ⟨P * diagonal w * Q, ?_, ?_, ⟨w 0 ^ 3, ?_⟩, ?_, ?_⟩
    · rw [adjU_mul, adjU_mul, hQ', ← hQ]
      calc P * (((diagonal w).map hU.bar)ᵀ * Q) * (P * diagonal w * Q)
          = P * (((diagonal w).map hU.bar)ᵀ * (Q * P) * diagonal w) * Q := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hQP, Matrix.mul_one, hD, Matrix.mul_one, hPQ]
    · rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Fin.prod_univ_three, hwd,
        mul_one, ← Matrix.det_mul, hPQ, Matrix.det_one]
    · have hw3' : (w ^ 3) = fun _ => w 0 ^ 3 := funext fun i => by rw [Pi.pow_apply, hw3 i]
      rw [hpow, Matrix.diagonal_pow, hw3', ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul,
        Matrix.mul_one, Matrix.smul_mul, hPQ]
    · rw [hAeq]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Q P, hQP, Matrix.one_mul, ← Matrix.mul_assoc Q P, hQP,
        Matrix.one_mul, ← Matrix.mul_assoc (diagonal w), ← Matrix.mul_assoc (diagonal e),
        Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      congr 3
      funext i
      exact mul_comm _ _
    · intro k hk c hc hZ
      rw [hAk k] at hZ
      have hDk : c • diagonal w = diagonal e ^ k := by
        calc c • diagonal w = Q * (c • (P * diagonal w * Q)) * P := by
              rw [Matrix.mul_smul, Matrix.smul_mul]
              congr 1
              simp only [← Matrix.mul_assoc]
              rw [hQP, Matrix.one_mul, Matrix.mul_assoc, hQP, Matrix.mul_one]
          _ = Q * (P * diagonal e ^ k * Q) * P := by rw [hZ]
          _ = diagonal e ^ k := by
              simp only [← Matrix.mul_assoc]
              rw [hQP, Matrix.one_mul, Matrix.mul_assoc, hQP, Matrix.mul_one]
      obtain ⟨i, hi⟩ := hwk k hk c hc
      apply hi
      have h := congrFun (congrFun hDk i) i
      rw [Matrix.smul_apply, Matrix.diagonal_apply_eq, Matrix.diagonal_pow,
        Matrix.diagonal_apply_eq, Pi.pow_apply, smul_eq_mul] at h
      exact h
  obtain ⟨ζ, hζ, hζu⟩ := exists_isPrimitiveRoot_nine_bar hU h9
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by norm_num)
  have hζ9 : ζ ^ 9 = 1 := hζ.pow_eq_one
  have hζ3 : ζ ^ 3 ≠ 1 := hζ.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have hζ6 : ζ ^ 6 ≠ 1 := hζ.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have hbarpow : ∀ m : ℕ, hU.bar (ζ ^ m) * ζ ^ m = 1 := fun m => by
    rw [map_pow, ← mul_pow, hζu, one_pow]
  by_cases hdist : e 0 ≠ e 1 ∧ e 0 ≠ e 2 ∧ e 1 ≠ e 2
  ·
    obtain ⟨h01, h02, h12⟩ := hdist
    refine key ![ζ, ζ, (ζ ^ 2)⁻¹] ?_ ?_ ?_ ?_
    · intro i
      fin_cases i
      · exact hζu
      · exact hζu
      · change hU.bar (ζ ^ 2)⁻¹ * (ζ ^ 2)⁻¹ = 1
        rw [map_inv₀, ← mul_inv, hbarpow, inv_one]
    · change ζ * ζ * (ζ ^ 2)⁻¹ = 1
      rw [← sq, mul_inv_cancel₀ (pow_ne_zero 2 hζ0)]
    · intro i
      fin_cases i
      · rfl
      · rfl
      · change ((ζ ^ 2)⁻¹) ^ 3 = ζ ^ 3
        rw [inv_pow, ← pow_mul]
        exact inv_eq_of_mul_eq_one_right (by rw [← pow_add]; exact hζ9)
    · intro k hk c hc
      by_contra hall
      push Not at hall
      have h0 : c * ζ = e 0 ^ k := hall 0
      have h1 : c * ζ = e 1 ^ k := hall 1
      have h2 : c * (ζ ^ 2)⁻¹ = e 2 ^ k := hall 2
      interval_cases k
      · apply hζ3
        have h02' : c * ζ = c * (ζ ^ 2)⁻¹ := by rw [h0, h2, pow_zero, pow_zero]
        have hζζ : ζ = (ζ ^ 2)⁻¹ := mul_left_cancel₀ hc h02'
        calc ζ ^ 3 = ζ * ζ ^ 2 := by ring
          _ = (ζ ^ 2)⁻¹ * ζ ^ 2 := congrArg (· * ζ ^ 2) hζζ
          _ = 1 := inv_mul_cancel₀ (pow_ne_zero 2 hζ0)
      · exact h01 (by rw [← pow_one (e 0), ← pow_one (e 1), ← h0, h1])
      · apply h01
        have hsq : e 0 ^ 2 = e 1 ^ 2 := h0.symm.trans h1
        have he1 : e 1 ≠ 0 := by
          intro h
          have := he3 1
          rw [h, zero_pow (by norm_num)] at this
          exact hα0 this.symm
        have hcube : e 0 * e 1 ^ 2 = e 1 * e 1 ^ 2 := by
          calc e 0 * e 1 ^ 2 = e 0 * e 0 ^ 2 := by rw [hsq]
            _ = e 0 ^ 3 := by ring
            _ = e 1 ^ 3 := by rw [he3 0, he3 1]
            _ = e 1 * e 1 ^ 2 := by ring
        exact mul_right_cancel₀ (pow_ne_zero 2 he1) hcube
  ·
    refine key ![1, ζ ^ 3, ζ ^ 6] ?_ ?_ ?_ ?_
    · intro i
      fin_cases i
      · change hU.bar 1 * 1 = 1
        rw [map_one, one_mul]
      · exact hbarpow 3
      · exact hbarpow 6
    · change 1 * ζ ^ 3 * ζ ^ 6 = 1
      rw [one_mul, ← pow_add]
      exact hζ9
    · intro i
      fin_cases i
      · rfl
      · change (ζ ^ 3) ^ 3 = 1 ^ 3
        rw [← pow_mul, one_pow]
        exact hζ9
      · change (ζ ^ 6) ^ 3 = 1 ^ 3
        rw [← pow_mul, one_pow, show 6 * 3 = 9 * 2 by norm_num, pow_mul, hζ9, one_pow]
    · intro k _ c hc
      by_contra hall
      push Not at hall
      have h0 : c * 1 = e 0 ^ k := hall 0
      have h1 : c * ζ ^ 3 = e 1 ^ k := hall 1
      have h2 : c * ζ ^ 6 = e 2 ^ k := hall 2
      by_cases h01 : e 0 = e 1
      · apply hζ3
        have : c * ζ ^ 3 = c * 1 := by rw [h0, h1, h01]
        exact mul_left_cancel₀ hc this
      by_cases h02 : e 0 = e 2
      · apply hζ6
        have : c * ζ ^ 6 = c * 1 := by rw [h0, h2, h02]
        exact mul_left_cancel₀ hc this
      have h12 : e 1 = e 2 := by
        by_contra h12
        exact hdist ⟨h01, h02, h12⟩
      apply hζ3
      have h36 : ζ ^ 3 = ζ ^ 6 := mul_left_cancel₀ hc (by rw [h1, h2, h12])
      have h33 : ζ ^ 3 * ζ ^ 3 = ζ ^ 3 * 1 := by
        rw [← pow_add, mul_one]
        exact h36.symm
      exact mul_left_cancel₀ (pow_ne_zero 3 hζ0) h33

end Mat

theorem exists_commute_not_mem_zpowers_projSU {f : ℕ} (hf : 1 ≤ f) (h9 : 9 ∣ 2 ^ f + 1)
    (y : ↥(CFSG.PGLModel.projSU 3 2 f)) (hy3 : y ^ 3 = 1) :
    ∃ z : ↥(CFSG.PGLModel.projSU 3 2 f), z ^ 3 = 1 ∧ z * y = y * z ∧
      z ∉ Subgroup.zpowers y := by
  classical
  have hU : UnitaryFieldData 2 f (GaloisField 2 (2 * f)) :=
    ⟨Nat.prime_two, hf, GaloisField.card 2 (2 * f) (by omega)⟩
  have hy' : (y : ProjGenLinGroup (Fin 3) (GaloisField 2 (2 * f))) ∈
      (CFSG.Open.StatedSU 3 (2 ^ f) (GaloisField 2 (2 * f))).map ProjGenLinGroup.mk := by
    exact (SetLike.ext_iff.mp (CFSG.PGLModel.projImage_statedSU 3 2 f) _).mpr y.2
  obtain ⟨A, hAS, hAy⟩ := Subgroup.mem_map.mp hy'
  obtain ⟨hAu, hAdet⟩ := CFSG.HardMathSupport.Foote.ModuleExclusions.unitary_of_mem_statedSU
    hU.bar (fun _ => rfl) hAS
  have hA3c : A ^ 3 ∈ Subgroup.center (GL (Fin 3) (GaloisField 2 (2 * f))) := by
    rw [← ProjGenLinGroup.mk_eq_one, map_pow, hAy]
    exact congrArg Subtype.val hy3
  obtain ⟨α, hα⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp hA3c
  have hA3 : (A : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * f))) ^ 3 = α • 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hα, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  obtain ⟨Z, hZu, hZdet, ⟨c, hZ3⟩, hZA, hZk⟩ :=
    exists_isometry_commute_of_cube_scalar hU h9 hAu hAdet hA3
  let Zg : GL (Fin 3) (GaloisField 2 (2 * f)) :=
    ⟨Z, (Z.map hU.bar)ᵀ, mul_eq_one_comm.mp hZu, hZu⟩
  have hZS : Zg ∈ CFSG.Open.StatedSU 3 (2 ^ f) (GaloisField 2 (2 * f)) := by
    rw [CFSG.PGLModel.statedSU_eq_closure_det]
    refine Subgroup.subset_closure ⟨Units.ext ?_, hZu⟩
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    exact hZdet
  have hzmem : ProjGenLinGroup.mk Zg ∈ CFSG.PGLModel.projSU 3 2 f :=
    (SetLike.ext_iff.mp (CFSG.PGLModel.projImage_statedSU 3 2 f) _).mp
      (Subgroup.mem_map_of_mem _ hZS)
  refine ⟨⟨_, hzmem⟩, ?_, ?_, ?_⟩
  · apply Subtype.ext
    change ProjGenLinGroup.mk Zg ^ 3 = 1
    rw [← map_pow, ProjGenLinGroup.mk_eq_one,
      Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
    exact ⟨c, by
      rw [Units.val_pow_eq_pow_val, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]
      exact hZ3.symm⟩
  · apply Subtype.ext
    change ProjGenLinGroup.mk Zg * (y : ProjGenLinGroup (Fin 3) (GaloisField 2 (2 * f))) =
      (y : ProjGenLinGroup (Fin 3) (GaloisField 2 (2 * f))) * ProjGenLinGroup.mk Zg
    rw [← hAy, ← map_mul, ← map_mul]
    congr 1
    exact Units.ext hZA
  · intro hz
    have hyfin : IsOfFinOrder y := isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, hy3⟩
    obtain ⟨k, hk, hzk⟩ := Finset.mem_image.mp (hyfin.mem_zpowers_iff_mem_range_orderOf.mp hz)
    have hk3 : k < 3 :=
      lt_of_lt_of_le (Finset.mem_range.mp hk) (orderOf_le_of_pow_eq_one (by norm_num) hy3)
    have h := congrArg Subtype.val hzk
    change (y : ProjGenLinGroup (Fin 3) (GaloisField 2 (2 * f))) ^ k = ProjGenLinGroup.mk Zg at h
    rw [← hAy, ← map_pow, ProjGenLinGroup.mk_eq_mk_iff] at h
    obtain ⟨u, hu⟩ := h
    apply hZk k hk3 (u⁻¹ : (GaloisField 2 (2 * f))ˣ) (Units.ne_zero _)
    have h' := congrArg Units.val hu
    rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Units.val_pow_eq_pow_val,
      Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one] at h'
    change _ = Z at h'
    rw [← h', smul_smul, Units.inv_mul, one_smul]

theorem kF148U3NineE9_holds : KF148U3NineE9 := by
  intro X _ _ f hf hiso h8 x hx
  have h9 : 9 ∣ 2 ^ f + 1 := by omega
  rcases hiso with ⟨h1, -⟩ | ⟨-, ⟨φ⟩⟩
  · omega
  have hz : ∀ x' : X, x' ^ 3 = 1 → ∃ z : X, z ^ 3 = 1 ∧ z * x' = x' * z ∧
      z ∉ Subgroup.zpowers x' := by
    intro x' hx'
    obtain ⟨z, hz3, hzc, hzn⟩ := exists_commute_not_mem_zpowers_projSU hf h9 (φ x')
      (by rw [← map_pow, hx', map_one])
    refine ⟨φ.symm z, by rw [← map_pow, hz3, map_one], ?_, fun hmem => hzn ?_⟩
    · apply φ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hzc]
    · have h := Subgroup.mem_map_of_mem φ.toMonoidHom hmem
      rw [MonoidHom.map_zpowers] at h
      simpa using h
  by_cases hx1 : x = 1
  · obtain ⟨z₁, hz₁3, -, hz₁⟩ := hz x hx
    have hz₁1 : z₁ ≠ 1 := fun h => hz₁ (by rw [h, hx1]; exact Subgroup.one_mem _)
    obtain ⟨z₂, hz₂3, hz₂c, hz₂⟩ := hz z₁ hz₁3
    obtain ⟨E, -, hE, hE9⟩ := exists_e9_of_commute hz₁3 hz₁1 hz₂3 hz₂c hz₂
    exact ⟨E, hx1 ▸ Subgroup.one_mem E, hE, hE9⟩
  · obtain ⟨z, hz3, hzc, hzn⟩ := hz x hx
    exact exists_e9_of_commute hx hx1 hz3 hzc hzn

section Certificates


theorem step148PGLConjOmega2_of_rank' (hR : Ronan148W.Step148OmegaRankThree) :
    Step148PGLConjOmega2 :=
  step148PGLConjOmega2_of_rank hR kF148U3NineE9_holds

end Certificates

end CFSG.RankThree.PartTwo.Sec14.Ronan148A
