module

public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockDefs
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockOmegaDict
public import CFSG.Blueprint.SourceClassicalTransportOrthogonal
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CBlockOrthA
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256q
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockDecomp
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.LocalAnalysis.StandardType.GGE0Frame
public import CFSG.LocalAnalysis.StandardType.GGOuterInvFieldTags
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaPlusFourShape
public import CFSG.RankThree.PartOne.KC.OrthogonalCommutatorBridge
public import CFSG.RankThree.PartOne.S11d.OrthCaseN
public import CFSG.RankThree.PartOne.S11d.OrthModels
public import CFSG.RankThree.PartOne.S11d.OrthSplitAbs
public import CFSG.HardMathSupport.Dickson.Bal207.OrthD4Semilin
public import CFSG.HardMathSupport.Dickson.Bal207.OrthD4Loc
public import CFSG.HardMathSupport.Dickson.Bal207.Restate
public import CFSG.RankThree.PartOne.S15K.FixedWitt
public import CFSG.RankThree.PartOne.S15K.LayerModel

public section

namespace CFSG.StandardType.ClassicalBlocks

open CFSG CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.StandardType.ClassicalPosition Matrix
open Polynomial
open CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
open CFSG.RankThree.PartOne.KCOrthogonal CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.OrthogonalInvolutions CFSG.RankThree.Classical2
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256q
open scoped commutatorElement

noncomputable abbrev ggJSo2_ML {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] :
    GL ι K ≃* ((ι → K) ≃ₗ[K] (ι → K)) :=
  (Matrix.GeneralLinearGroup.toLin (R := K)).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K (ι → K))

private lemma ggJSo2_ML_apply {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (A : GL ι K) (v : ι → K) :
    ggJSo2_ML A v = (A : Matrix ι ι K) *ᵥ v := by
  simp only [ggJSo2_ML, MulEquiv.trans_apply,
    LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv, Matrix.GeneralLinearGroup.coe_toLin,
    Matrix.mulVecLin_apply]

private lemma ggJSo2_matrixOrthogonal_eq {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Φ : QuadraticForm K (ι → K)) :
    CFSG.Blueprint.EvenSource.matrixOrthogonal ⇑Φ =
      (TauCeti.QuadraticMap.orthogonalGroup Φ).comap
        (ggJSo2_ML (ι := ι) (K := K)).toMonoidHom := by
  ext A
  simp only [CFSG.Blueprint.EvenSource.matrixOrthogonal, Set.mem_setOf_eq, Subgroup.mem_comap,
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  change (∀ v, Φ ((A : Matrix ι ι K) *ᵥ v) = Φ v) ↔ ∀ v, Φ (ggJSo2_ML A v) = Φ v
  simp only [ggJSo2_ML_apply]

private lemma ggJSo2_map_statedOmega {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Φ : QuadraticForm K (ι → K)) :
    (StatedOmega ⇑Φ).map (ggJSo2_ML (ι := ι) (K := K)).toMonoidHom = orthDerived Φ := by
  rw [CFSG.Blueprint.EvenSource.statedOmega_eq_commutator, ggJSo2_matrixOrthogonal_eq,
    Subgroup.map_commutator]
  rw [Subgroup.map_comap_eq_self_of_surjective (ggJSo2_ML (ι := ι) (K := K)).surjective]

lemma ggJSo2_oddOrderIsometry {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (b : GL ι K) (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b)) :
    CFSG.RankThree.PartOne.KCOrthogonal.OddOrderIsometry Φ (orderOf b)
      (ggJSo2_ML b) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact orthDerived_le_orthogonalGroup
      (ggJSo2_map_statedOmega Φ ▸ Subgroup.mem_map.mpr ⟨b, hb, rfl⟩)
  · rw [← map_pow, pow_orderOf_eq_one, map_one]
  · intro h
    exact hodd.not_two_dvd_nat ((CharP.cast_eq_zero_iff K 2 (orderOf b)).mp h)
  · exact hΦ.1

private noncomputable abbrev ggJSo2r_geomSum {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (B : Matrix ι ι K) (m : ℕ) : Matrix ι ι K :=
  ∑ k ∈ Finset.range m, B ^ k

private noncomputable abbrev ggJSo2r_avg {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (B : Matrix ι ι K) (m : ℕ) : Matrix ι ι K :=
  (m : K)⁻¹ • ggJSo2r_geomSum B m

private lemma ggJSo2r_geomSum_mul_self {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {B : Matrix ι ι K} {m : ℕ} (hBm : B ^ m = 1) :
    B * ggJSo2r_geomSum B m = ggJSo2r_geomSum B m := by
  apply sub_eq_zero.mp
  have h : B * ggJSo2r_geomSum B m - 1 * ggJSo2r_geomSum B m = 0 := by
    rw [← sub_mul, mul_geom_sum, hBm, sub_self]
  simpa using h

private lemma ggJSo2r_geomSum_mul' {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {B : Matrix ι ι K} {m : ℕ} (hBm : B ^ m = 1) :
    ggJSo2r_geomSum B m * B = ggJSo2r_geomSum B m := by
  apply sub_eq_zero.mp
  have h : ggJSo2r_geomSum B m * B - ggJSo2r_geomSum B m * 1 = 0 := by
    rw [← mul_sub, geom_sum_mul, hBm, sub_self]
  simpa using h

private lemma ggJSo2r_avg_mul {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {B : Matrix ι ι K} {m : ℕ} (hBm : B ^ m = 1) :
    B * ggJSo2r_avg B m = ggJSo2r_avg B m := by
  calc B * ggJSo2r_avg B m
      = B * ((m : K)⁻¹ • ggJSo2r_geomSum B m) := rfl
    _ = (m : K)⁻¹ • (B * ggJSo2r_geomSum B m) :=
        Matrix.mul_smul B (m : K)⁻¹ (ggJSo2r_geomSum B m)
    _ = (m : K)⁻¹ • ggJSo2r_geomSum B m := by rw [ggJSo2r_geomSum_mul_self hBm]
    _ = ggJSo2r_avg B m := rfl

private lemma ggJSo2r_avg_mul' {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {B : Matrix ι ι K} {m : ℕ} (hBm : B ^ m = 1) :
    ggJSo2r_avg B m * B = ggJSo2r_avg B m := by
  calc ggJSo2r_avg B m * B
      = ((m : K)⁻¹ • ggJSo2r_geomSum B m) * B := rfl
    _ = (m : K)⁻¹ • (ggJSo2r_geomSum B m * B) :=
        Matrix.smul_mul (m : K)⁻¹ (ggJSo2r_geomSum B m) B
    _ = (m : K)⁻¹ • ggJSo2r_geomSum B m := by rw [ggJSo2r_geomSum_mul' hBm]
    _ = ggJSo2r_avg B m := rfl

private lemma ggJSo2r_avg_mul_eq_of_mul_eq {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {B X : Matrix ι ι K} {m : ℕ} (hm : (m : K) ≠ 0) (hX : B * X = X) :
    ggJSo2r_avg B m * X = X := by
  have hpow : ∀ k : ℕ, B ^ k * X = X := by
    intro k
    induction k with
    | zero => rw [pow_zero, one_mul]
    | succ k ih => rw [pow_succ, mul_assoc, hX, ih]
  have hSX : ggJSo2r_geomSum B m * X = m • X := by
    calc ggJSo2r_geomSum B m * X
        = (∑ k ∈ Finset.range m, B ^ k) * X := rfl
      _ = ∑ k ∈ Finset.range m, B ^ k * X :=
          Finset.sum_mul (Finset.range m) (fun k => B ^ k) X
      _ = ∑ k ∈ Finset.range m, X := Finset.sum_congr rfl (fun k _ => hpow k)
      _ = m • X := by rw [Finset.sum_const, Finset.card_range]
  calc ggJSo2r_avg B m * X
      = ((m : K)⁻¹ • ggJSo2r_geomSum B m) * X := rfl
    _ = (m : K)⁻¹ • (ggJSo2r_geomSum B m * X) :=
        Matrix.smul_mul (m : K)⁻¹ (ggJSo2r_geomSum B m) X
    _ = (m : K)⁻¹ • (m • X) := by rw [hSX]
    _ = (m : K)⁻¹ • ((m : K) • X) := by
        rw [← Nat.cast_smul_eq_nsmul (R := K) m X]
    _ = X := by rw [smul_smul, inv_mul_cancel₀ hm, one_smul]

private lemma ggJSo2r_avg_mul_self {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {B : Matrix ι ι K} {m : ℕ} (hBm : B ^ m = 1) (hm : (m : K) ≠ 0) :
    ggJSo2r_avg B m * ggJSo2r_avg B m = ggJSo2r_avg B m :=
  ggJSo2r_avg_mul_eq_of_mul_eq hm (ggJSo2r_avg_mul hBm)

private lemma ggJSo2r_avg_mulVec_eq_of_fixed {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {B : Matrix ι ι K} {m : ℕ} (hm : (m : K) ≠ 0) {w : ι → K} (hw : B *ᵥ w = w) :
    ggJSo2r_avg B m *ᵥ w = w := by
  have hpow : ∀ k : ℕ, B ^ k *ᵥ w = w := by
    intro k
    induction k with
    | zero => rw [pow_zero, Matrix.one_mulVec]
    | succ k ih => rw [pow_succ, ← Matrix.mulVec_mulVec, hw, ih]
  have hSw : ggJSo2r_geomSum B m *ᵥ w = m • w := by
    calc ggJSo2r_geomSum B m *ᵥ w
        = (∑ k ∈ Finset.range m, B ^ k) *ᵥ w := rfl
      _ = ∑ k ∈ Finset.range m, B ^ k *ᵥ w :=
          Matrix.sum_mulVec (Finset.range m) (fun k => B ^ k) w
      _ = ∑ k ∈ Finset.range m, w := Finset.sum_congr rfl (fun k _ => hpow k)
      _ = m • w := by rw [Finset.sum_const, Finset.card_range]
  calc ggJSo2r_avg B m *ᵥ w
      = ((m : K)⁻¹ • ggJSo2r_geomSum B m) *ᵥ w := rfl
    _ = (m : K)⁻¹ • (ggJSo2r_geomSum B m *ᵥ w) :=
        Matrix.smul_mulVec (m : K)⁻¹ (ggJSo2r_geomSum B m) w
    _ = (m : K)⁻¹ • (m • w) := by rw [hSw]
    _ = (m : K)⁻¹ • ((m : K) • w) := by
        rw [← Nat.cast_smul_eq_nsmul (R := K) m w]
    _ = w := by rw [smul_smul, inv_mul_cancel₀ hm, one_smul]

private lemma ggJSo2r_adjoin_mul_avg {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (B g : Matrix ι ι K) (hg : B * g = g) :
    ∀ x ∈ Algebra.adjoin K ({B} : Set (Matrix ι ι K)), ∃ c : K, x * g = c • g := by
  intro x hx
  refine Algebra.adjoin_induction (p := fun x _ => ∃ c : K, x * g = c • g)
    ?_ ?_ ?_ ?_ hx
  · intro y hy
    rw [Set.mem_singleton_iff] at hy
    exact ⟨1, by rw [hy, hg, one_smul]⟩
  · intro r
    exact ⟨r, by rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.one_mul]⟩
  · intro y z hy hz ⟨c₁, h₁⟩ ⟨c₂, h₂⟩
    exact ⟨c₁ + c₂, by rw [add_mul, h₁, h₂, add_smul]⟩
  · intro y z hy hz ⟨c₁, h₁⟩ ⟨c₂, h₂⟩
    refine ⟨c₁ * c₂, ?_⟩
    calc (y * z) * g = y * (z * g) := mul_assoc y z g
      _ = y * (c₂ • g) := by rw [h₂]
      _ = c₂ • (y * g) := Matrix.mul_smul y c₂ g
      _ = c₂ • (c₁ • g) := by rw [h₁]
      _ = (c₂ * c₁) • g := smul_smul c₂ c₁ g
      _ = (c₁ * c₂) • g := by rw [mul_comm]

private lemma ggJSo2r_adjoin_comm_avg {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (B g : Matrix ι ι K) (hg : B * g = g * B) :
    ∀ x ∈ Algebra.adjoin K ({B} : Set (Matrix ι ι K)), x * g = g * x := by
  intro x hx
  refine Algebra.adjoin_induction (p := fun x _ => x * g = g * x) ?_ ?_ ?_ ?_ hx
  · intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact hg
  · intro r
    rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
      Matrix.mul_one]
  · intro y z hy hz ihy ihz
    rw [add_mul, mul_add, ihy, ihz]
  · intro y z hy hz ihy ihz
    rw [mul_assoc, ihz, ← mul_assoc, ihy, mul_assoc]

private lemma ggJSo2r_range_avg {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [CharP K 2] (b : GL ι K) (hodd : Odd (orderOf b)) :
    (Matrix.toLin' (ggJSo2r_avg (b : Matrix ι ι K) (orderOf b))).range =
      CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b) := by
  have hm : ((orderOf b : ℕ) : K) ≠ 0 := fun h =>
    hodd.not_two_dvd_nat ((CharP.cast_eq_zero_iff K 2 (orderOf b)).mp h)
  have hBm : (b : Matrix ι ι K) ^ orderOf b = 1 := by
    rw [← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one]
  have hBg : (b : Matrix ι ι K) * ggJSo2r_avg (b : Matrix ι ι K) (orderOf b) =
      ggJSo2r_avg (b : Matrix ι ι K) (orderOf b) := ggJSo2r_avg_mul hBm
  apply le_antisymm
  · intro w hw
    rw [LinearMap.mem_range] at hw
    obtain ⟨v, rfl⟩ := hw
    rw [CFSG.RankThree.PartOne.KCOrthogonal.mem_fixedSpace, ggJSo2_ML_apply,
      Matrix.toLin'_apply, Matrix.mulVec_mulVec, hBg]
  · intro w hw
    rw [LinearMap.mem_range]
    refine ⟨w, ?_⟩
    rw [Matrix.toLin'_apply]
    rw [CFSG.RankThree.PartOne.KCOrthogonal.mem_fixedSpace, ggJSo2_ML_apply] at hw
    exact ggJSo2r_avg_mulVec_eq_of_fixed hm hw

private lemma ggJSo2_range_eq_fixedSpace {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (b : GL ι K) (hodd : Odd (orderOf b))
    {ε : Matrix ι ι K}
    (hε : IsPrimAdjIdemIn (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε)
    (h1 : (b : Matrix ι ι K) * ε = ε) :
    (Matrix.toLin' ε).range = CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b) := by
  classical
  have hm : ((orderOf b : ℕ) : K) ≠ 0 := fun h =>
    hodd.not_two_dvd_nat ((CharP.cast_eq_zero_iff K 2 (orderOf b)).mp h)
  have hBm : (b : Matrix ι ι K) ^ orderOf b = 1 := by
    rw [← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one]
  let g : Matrix ι ι K := ggJSo2r_avg (b : Matrix ι ι K) (orderOf b)
  have hBg : (b : Matrix ι ι K) * g = g := ggJSo2r_avg_mul hBm
  have hgB : g * (b : Matrix ι ι K) = g := ggJSo2r_avg_mul' hBm
  have hgg : g * g = g := ggJSo2r_avg_mul_self hBm hm
  have hge : g * ε = ε := ggJSo2r_avg_mul_eq_of_mul_eq hm h1
  have hεA : ε ∈ Algebra.adjoin K ({(b : Matrix ι ι K)} : Set (Matrix ι ι K)) := by
    simpa only [Set.image_singleton] using hε.1
  obtain ⟨c, hc⟩ := ggJSo2r_adjoin_mul_avg (b : Matrix ι ι K) g hBg ε hεA
  have hcomm : ε * g = g * ε :=
    ggJSo2r_adjoin_comm_avg (b : Matrix ι ι K) g (hBg.trans hgB.symm) ε hεA
  have hεcg : ε = c • g := by
    calc ε = g * ε := hge.symm
      _ = ε * g := hcomm.symm
      _ = c • g := hc
  have hg_ne : g ≠ 0 := by
    intro hg0
    exact hε.2.2.1 (by rw [hεcg, hg0, smul_zero])
  have hc_ne : c ≠ 0 := by
    intro hc0
    exact hε.2.2.1 (by rw [hεcg, hc0, zero_smul])
  have hcc : c ^ 2 • g = c • g := by
    have h2 : ε * ε = c ^ 2 • g := by
      calc ε * ε = (c • g) * (c • g) := by rw [hεcg]
        _ = c ^ 2 • (g * g) := by
              rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, pow_two]
        _ = c ^ 2 • g := by rw [hgg]
    rw [hε.2.1.eq] at h2
    rw [← h2, hεcg]
  have hzero : (c ^ 2 - c) • g = 0 := by
    rw [sub_smul, hcc, sub_self]
  have hc_eq : c = 1 := by
    have hcs : c ^ 2 - c = 0 := (smul_eq_zero_iff_left hg_ne).mp hzero
    have hmul : c * (c - 1) = 0 := by
      have hcc' : c * c = c := by
        rw [pow_two] at hcs
        exact sub_eq_zero.mp hcs
      rw [mul_sub, mul_one, hcc', sub_self]
    rcases mul_eq_zero.mp hmul with h | h
    · exact absurd h hc_ne
    · exact sub_eq_zero.mp h
  have hεg : ε = g := by rw [hεcg, hc_eq, one_smul]
  rw [hεg]
  have hgoal : g = ggJSo2r_avg (b : Matrix ι ι K) (orderOf b) := rfl
  rw [hgoal]
  exact ggJSo2r_range_avg b hodd

private lemma ggJSo2g_ML_apply' {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (A : GL ι K) (v : ι → K) :
    ggJSo2_ML A v = Matrix.toLin' (A : Matrix ι ι K) v := by
  rw [ggJSo2_ML_apply, Matrix.toLin'_apply]

private lemma ggJSo2g_apply_eq_self_of_mem_range {ι K : Type} [Fintype ι] [DecidableEq ι]
    [Field K] {ε : Matrix ι ι K} (hidem : IsIdempotentElem ε) {w : ι → K}
    (hw : w ∈ LinearMap.range (Matrix.toLin' ε)) : (Matrix.toLin' ε) w = w := by
  obtain ⟨w', hw'⟩ := hw
  rw [← hw', ← Matrix.toLin'_mul_apply, hidem.eq]

private lemma ggJSo2g_ker_eq_othersSpace {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (b : GL ι K) (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b))
    {ε : Matrix ι ι K}
    (hε : IsPrimAdjIdemIn (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε)
    (h1 : (b : Matrix ι ι K) * ε = ε) :
    LinearMap.ker (Matrix.toLin' ε) =
      othersSpace ((ggJSo2_ML (ι := ι) (K := K) b).toLinearMap) (X - 1) := by
  classical
  have hx := ggJSo2_oddOrderIsometry Φ hΦ b hb hodd
  have hrange := ggJSo2_range_eq_fixedSpace Φ b hodd hε h1
  have hG := ggOmegaBlk_G_isUnit_det Φ hΦ
  have hadj := hε.2.2.2.1
  have hidem : IsIdempotentElem ε := hε.2.1
  have hQW := hx.polarBilin_fixed_nondegenerate
  have horth := hx.fixed_others.2
  apply le_antisymm
  · intro z hz
    obtain ⟨w, hw, r, hr, hwr⟩ := exists_add_of_isCompl hx.fixed_others.1 z
    have hwperp : ∀ w' : fixedSpace (ggJSo2_ML b),
        QuadraticMap.polarBilin (Φ.comp (fixedSpace (ggJSo2_ML b)).subtype)
          ⟨w, hw⟩ w' = 0 := by
      intro w'
      rw [QuadraticMap.polarBilin_apply_apply, polar_comp_subtype]
      change QuadraticMap.polar Φ w (w' : ι → K) = 0
      have hzperp : QuadraticMap.polar Φ z (w' : ι → K) = 0 := by
        have hw'range : (w' : ι → K) ∈ LinearMap.range (Matrix.toLin' ε) := by
          rw [hrange]; exact w'.2
        obtain ⟨u, hu⟩ := hw'range
        have hz0 : (Matrix.toLin' ε) z = 0 := LinearMap.mem_ker.mp hz
        rw [← hu, Matrix.toLin'_apply, QuadraticMap.polar_comm,
          ggOmegaBlk_polar_selfAdjoint Φ hG hadj u z, ← Matrix.toLin'_apply, hz0,
          QuadraticMap.polar_zero_right]
      have hrperp : QuadraticMap.polar Φ r (w' : ι → K) = 0 := by
        rw [QuadraticMap.polar_comm]
        exact horth w' w'.2 r hr
      have hwz : (w : ι → K) = z - (r : ι → K) := by rw [← hwr]; abel
      rw [hwz, QuadraticMap.polar_sub_left, hzperp, hrperp, sub_zero]
    have hw0 : (⟨w, hw⟩ : fixedSpace (ggJSo2_ML b)) = 0 := hQW.1 _ hwperp
    have hwz0 : (w : ι → K) = 0 := congrArg Subtype.val hw0
    rw [← hwr, hwz0, zero_add]
    exact hr
  · intro z hz
    rw [LinearMap.mem_ker]
    have hfixed : Matrix.toLin' ε z ∈ fixedSpace (ggJSo2_ML b) := by
      rw [← hrange]; exact LinearMap.mem_range_self _ z
    have horthz : ∀ w : fixedSpace (ggJSo2_ML b),
        QuadraticMap.polarBilin (Φ.comp (fixedSpace (ggJSo2_ML b)).subtype)
          ⟨Matrix.toLin' ε z, hfixed⟩ w = 0 := by
      intro w
      rw [QuadraticMap.polarBilin_apply_apply, polar_comp_subtype]
      change QuadraticMap.polar Φ (Matrix.toLin' ε z) (w : ι → K) = 0
      rw [Matrix.toLin'_apply, ggOmegaBlk_polar_selfAdjoint Φ hG hadj z (w : ι → K)]
      have hwrange : (w : ι → K) ∈ LinearMap.range (Matrix.toLin' ε) := by
        rw [hrange]; exact w.2
      rw [← Matrix.toLin'_apply, ggJSo2g_apply_eq_self_of_mem_range hidem hwrange,
        QuadraticMap.polar_comm]
      exact horth w w.2 z hz
    have hz0 : (⟨Matrix.toLin' ε z, hfixed⟩ : fixedSpace (ggJSo2_ML b)) = 0 :=
      hQW.1 _ horthz
    exact congrArg Subtype.val hz0

private lemma ggJSo2g_range_one_sub {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (b : GL ι K) (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b))
    {ε : Matrix ι ι K}
    (hε : IsPrimAdjIdemIn (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε)
    (h1 : (b : Matrix ι ι K) * ε = ε) :
    LinearMap.range (Matrix.toLin' (1 - ε : Matrix ι ι K)) =
      othersSpace ((ggJSo2_ML (ι := ι) (K := K) b).toLinearMap) (X - 1) := by
  have hidem : IsIdempotentElem ε := hε.2.1
  have hp : IsIdempotentElem (Matrix.toLin' ε) := by
    rw [isIdempotentElem_iff]
    apply LinearMap.ext
    intro v
    rw [Module.End.mul_apply, ← Matrix.toLin'_mul_apply, hidem.eq]
  rw [ggOmegaBlk_toLin_one_sub, ← LinearMap.IsIdempotentElem.ker_eq_range_one_sub hp,
    ggJSo2g_ker_eq_othersSpace Φ hΦ b hb hodd hε h1]

private lemma ggJSo2_map_G_eq {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (b : GL ι K) (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b))
    {ε : Matrix ι ι K}
    (hε : IsPrimAdjIdemIn (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε)
    (h1 : (b : Matrix ι ι K) * ε = ε) :
    (glBlockCentralizer (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε).map
        ((ggJSo2_ML (ι := ι) (K := K)).toMonoidHom.comp (StatedOmega ⇑Φ).subtype) =
      CFSG.RankThree.PartOne.KCOrthogonal.supportedBlock Φ (ggJSo2_ML b) (X - 1) ⊓
        orthDerived Φ := by
  have hrange := ggJSo2g_range_one_sub Φ hΦ b hb hodd hε h1
  ext g
  constructor
  · intro hg
    rw [Subgroup.mem_map] at hg
    obtain ⟨u, hu, hgu⟩ := hg
    have hu' : ((u : ↥(StatedOmega ⇑Φ)) : GL ι K) ∈
        Subgroup.centralizer ({b} : Set (GL ι K)) ⊓ glFixing (1 - ε) :=
      Subgroup.mem_comap.mp hu
    have hcent : ((u : ↥(StatedOmega ⇑Φ)) : GL ι K) ∈
        Subgroup.centralizer ({b} : Set (GL ι K)) := (Subgroup.mem_inf.mp hu').1
    have hfix : ((u : ↥(StatedOmega ⇑Φ)) : GL ι K) ∈ glFixing (1 - ε) :=
      (Subgroup.mem_inf.mp hu').2
    have hbb : ((u : ↥(StatedOmega ⇑Φ)) : GL ι K) * b =
        b * ((u : ↥(StatedOmega ⇑Φ)) : GL ι K) :=
      (Subgroup.mem_centralizer_singleton_iff).mp hcent
    have horth : ggJSo2_ML ((u : ↥(StatedOmega ⇑Φ)) : GL ι K) ∈ orthDerived Φ := by
      have hmem : ggJSo2_ML ((u : ↥(StatedOmega ⇑Φ)) : GL ι K) ∈
          (StatedOmega ⇑Φ).map (ggJSo2_ML (ι := ι) (K := K)).toMonoidHom :=
        ⟨(u : ↥(StatedOmega ⇑Φ)), (u : ↥(StatedOmega ⇑Φ)).2, rfl⟩
      rwa [ggJSo2_map_statedOmega Φ] at hmem
    rw [Subgroup.mem_inf]
    constructor
    · rw [mem_supportedBlock]
      constructor
      · rw [mem_isometryCentralizer]
        constructor
        · intro v
          have hO := orthDerived_le_orthogonalGroup (Q := Φ) horth
          have hv := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hO v
          rw [← hgu]
          exact hv
        · intro v
          have hcomm2 : ggJSo2_ML ((u : ↥(StatedOmega ⇑Φ)) : GL ι K) * ggJSo2_ML b =
              ggJSo2_ML b * ggJSo2_ML ((u : ↥(StatedOmega ⇑Φ)) : GL ι K) := by
            rw [← map_mul, ← map_mul, hbb]
          have hv := congrArg (fun e : (ι → K) ≃ₗ[K] (ι → K) => e v) hcomm2
          rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply] at hv
          rw [← hgu]
          exact hv
      · intro v hv
        have hfix' : ∀ w, Matrix.toLin' (((u : ↥(StatedOmega ⇑Φ)) : GL ι K) : Matrix ι ι K)
            (Matrix.toLin' (1 - ε) w) = Matrix.toLin' (1 - ε) w :=
          (ggOmegaBlk_mem_glFixing_iff (((u : ↥(StatedOmega ⇑Φ)) : GL ι K)) (1 - ε)).mp hfix
        rw [← hrange] at hv
        obtain ⟨w, rfl⟩ := hv
        rw [← hgu]
        change ggJSo2_ML ((u : ↥(StatedOmega ⇑Φ)) : GL ι K) (Matrix.toLin' (1 - ε) w) =
          Matrix.toLin' (1 - ε) w
        rw [ggJSo2g_ML_apply']
        exact hfix' w
    · have hmem : g ∈ (StatedOmega ⇑Φ).map
          (ggJSo2_ML (ι := ι) (K := K)).toMonoidHom :=
        ⟨(u : ↥(StatedOmega ⇑Φ)), (u : ↥(StatedOmega ⇑Φ)).2, hgu⟩
      rwa [ggJSo2_map_statedOmega Φ] at hmem
  · intro hg
    rw [Subgroup.mem_inf] at hg
    obtain ⟨hgS, hgΩ⟩ := hg
    rw [Subgroup.mem_map]
    rw [mem_supportedBlock] at hgS
    obtain ⟨hcent, hfixx⟩ := hgS
    have hcommv : ∀ v, g (ggJSo2_ML b v) = ggJSo2_ML b (g v) :=
      (mem_isometryCentralizer.mp hcent).2
    let w : GL ι K := (ggJSo2_ML (ι := ι) (K := K)).symm g
    have hwg : ggJSo2_ML (ι := ι) (K := K) w = g := MulEquiv.apply_symm_apply _ _
    have hwStated : w ∈ StatedOmega ⇑Φ := by
      have hmem : ggJSo2_ML (ι := ι) (K := K) w ∈
          (StatedOmega ⇑Φ).map (ggJSo2_ML (ι := ι) (K := K)).toMonoidHom := by
        rw [ggJSo2_map_statedOmega Φ, hwg]
        exact hgΩ
      rw [Subgroup.mem_map_equiv] at hmem
      simpa using hmem
    refine ⟨⟨w, hwStated⟩, ?_, ?_⟩
    · rw [glBlockCentralizer, Subgroup.mem_comap, Subgroup.mem_inf]
      constructor
      · rw [Subgroup.mem_centralizer_singleton_iff]
        apply (ggJSo2_ML (ι := ι) (K := K)).injective
        rw [map_mul, map_mul]
        change ggJSo2_ML w * ggJSo2_ML b = ggJSo2_ML b * ggJSo2_ML w
        rw [hwg]
        apply LinearEquiv.ext
        intro v
        rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
        exact hcommv v
      · rw [ggOmegaBlk_mem_glFixing_iff]
        intro z
        have hzmem : Matrix.toLin' (1 - ε) z ∈ LinearMap.range (Matrix.toLin' (1 - ε)) :=
          ⟨z, rfl⟩
        have hgz : g (Matrix.toLin' (1 - ε) z) = Matrix.toLin' (1 - ε) z :=
          hfixx _ (by rwa [hrange] at hzmem)
        change Matrix.toLin' (w : Matrix ι ι K) (Matrix.toLin' (1 - ε) z) =
          Matrix.toLin' (1 - ε) z
        rw [← ggJSo2g_ML_apply' w (Matrix.toLin' (1 - ε) z), hwg]
        exact hgz
    · exact hwg

private lemma ggJSo2_inf_orthDerived_eq_supportedFixedDerived {ι K : Type} [Fintype ι]
    [DecidableEq ι] [Field K] [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (b : GL ι K) (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b))
    (hD : CFSG.RankThree.PartOne.DicksonDerived
      (Φ.comp (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b)).subtype)
      (ggJSo2_oddOrderIsometry Φ hΦ b hb hodd).polarBilin_fixed_nondegenerate) :
    CFSG.RankThree.PartOne.KCOrthogonal.supportedBlock Φ (ggJSo2_ML b) (X - 1) ⊓
        orthDerived Φ =
      CFSG.RankThree.PartOne.KCOrthogonal.supportedFixedDerived Φ (ggJSo2_ML b) := by
  classical
  refine le_antisymm ?_ ?_
  · intro g hg
    obtain ⟨hgF, hgO⟩ := Subgroup.mem_inf.mp hg
    refine CFSG.RankThree.PartOne.KCOrthogonal.mem_supportedFixedDerived.mpr ⟨hgF, ?_⟩
    by_cases hmem : (X - 1 : K[X]) ∈ primaryFactors (ggJSo2_ML b).toLinearMap
    · have hO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Φ :=
        (Subgroup.mem_inf.mp
          (CFSG.RankThree.PartOne.KCOrthogonal.supportedBlock_le_isometryCentralizer
            (X - 1) hgF)).1
      have hL : CFSG.RankThree.OrthogonalInvolutions.dicksonHom Φ hΦ
          (⟨g, hO⟩ : ↥(TauCeti.QuadraticMap.orthogonalGroup Φ)) = 1 := by
        rw [show (⟨g, hO⟩ : ↥(TauCeti.QuadraticMap.orthogonalGroup Φ)) =
            ⟨g, CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup_of_commutator
              Φ hgO⟩ from Subtype.ext rfl]
        exact CFSG.RankThree.PartOne.KCOrthogonal.dicksonHom_apply_orthDerived_eq_one hΦ hgO
      refine hD ⟨CFSG.RankThree.PartOne.KCOrthogonal.isometryRestrictFixed Φ (ggJSo2_ML b)
          ⟨g, CFSG.RankThree.PartOne.KCOrthogonal.supportedBlock_le_isometryCentralizer
            (X - 1) hgF⟩,
        CFSG.RankThree.PartOne.KCOrthogonal.isometryRestrictFixed_mem_orthogonalGroup _⟩ ?_
      rw [← (ggJSo2_oddOrderIsometry Φ hΦ b hb hodd).dicksonHom_eq_restrict_of_mem_supportedBlock
        hodd hΦ hmem hgF]
      exact hL
    · have hbot : CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b) = ⊥ :=
        CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace_eq_bot_of_not_mem
          (x := ggJSo2_ML b) hmem
      haveI : Subsingleton (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b)) := by
        rw [hbot]
        exact Submodule.subsingleton_iff_eq_bot.mpr rfl
      haveI : Subsingleton
          (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b) ≃ₗ[K]
            CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b)) :=
        ⟨fun _ _ => LinearEquiv.ext fun _ => Subsingleton.elim _ _⟩
      rw [Subsingleton.elim (CFSG.RankThree.PartOne.KCOrthogonal.restrictFixed Φ (ggJSo2_ML b)
        ⟨g, hgF⟩) 1]
      exact Subgroup.one_mem _
  · intro g hg
    exact ⟨CFSG.RankThree.PartOne.KCOrthogonal.supportedFixedDerived_le_supportedBlock hg,
      (ggJSo2_oddOrderIsometry Φ hΦ b hb hodd).supportedFixedDerived_le_orthDerived hg⟩

@[expose] noncomputable def glBlockCentralizerEquivSupportedFixedDerived
    {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Fintype K] [CharP K 2]
    (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (b : GL ι K) (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b))
    {ε : Matrix ι ι K}
    (hε : IsPrimAdjIdemIn (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε)
    (h1 : (b : Matrix ι ι K) * ε = ε)
    (hD : CFSG.RankThree.PartOne.DicksonDerived
      (Φ.comp (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b)).subtype)
      (ggJSo2_oddOrderIsometry Φ hΦ b hb hodd).polarBilin_fixed_nondegenerate) :
    ↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε) ≃*
      ↥(CFSG.RankThree.PartOne.KCOrthogonal.supportedFixedDerived Φ (ggJSo2_ML b)) := by
  classical
  let f : ↥(StatedOmega ⇑Φ) →* ((ι → K) ≃ₗ[K] (ι → K)) :=
    (ggJSo2_ML (ι := ι) (K := K)).toMonoidHom.comp (StatedOmega ⇑Φ).subtype
  have hf : Function.Injective f := fun a c hac =>
    Subtype.ext ((ggJSo2_ML (ι := ι) (K := K)).injective hac)
  exact (Subgroup.equivMapOfInjective _ f hf).trans
    (MulEquiv.subgroupCongr (by
      rw [ggJSo2_map_G_eq Φ hΦ b hb hodd hε h1,
        ggJSo2_inf_orthDerived_eq_supportedFixedDerived Φ hΦ b hb hodd hD]))

@[simp] theorem glBlockCentralizerEquivSupportedFixedDerived_apply
    {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Fintype K] [CharP K 2]
    (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (b : GL ι K) (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b))
    {ε : Matrix ι ι K}
    (hε : IsPrimAdjIdemIn (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε)
    (h1 : (b : Matrix ι ι K) * ε = ε)
    (hD : CFSG.RankThree.PartOne.DicksonDerived
      (Φ.comp (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b)).subtype)
      (ggJSo2_oddOrderIsometry Φ hΦ b hb hodd).polarBilin_fixed_nondegenerate)
    (u : ↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε)) :
    ((glBlockCentralizerEquivSupportedFixedDerived Φ hΦ b hb hodd hε h1 hD u :
        ↥(CFSG.RankThree.PartOne.KCOrthogonal.supportedFixedDerived Φ (ggJSo2_ML b))) :
        (ι → K) ≃ₗ[K] (ι → K)) =
      ggJSo2_ML (((u : ↥(glBlockCentralizer
        (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε)) : ↥(StatedOmega ⇑Φ)) : GL ι K) := by
  rfl

@[expose] noncomputable def glBlockCentralizerEquivFixedDerived
    {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Fintype K] [CharP K 2]
    (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (b : GL ι K) (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b))
    {ε : Matrix ι ι K}
    (hε : IsPrimAdjIdemIn (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε)
    (h1 : (b : Matrix ι ι K) * ε = ε)
    (hD : CFSG.RankThree.PartOne.DicksonDerived
      (Φ.comp (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b)).subtype)
      (ggJSo2_oddOrderIsometry Φ hΦ b hb hodd).polarBilin_fixed_nondegenerate) :
    ↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε) ≃*
      ↥(CFSG.RankThree.Classical2.orthDerived
        (Φ.comp (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b)).subtype)) :=
  (glBlockCentralizerEquivSupportedFixedDerived Φ hΦ b hb hodd hε h1 hD).trans
    (CFSG.HardMathSupport.Dickson.Bal207.OrthFix.fixRestr
      (ggJSo2_oddOrderIsometry Φ hΦ b hb hodd))

@[simp] theorem glBlockCentralizerEquivFixedDerived_apply_coe
    {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Fintype K] [CharP K 2]
    (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (b : GL ι K) (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b))
    {ε : Matrix ι ι K}
    (hε : IsPrimAdjIdemIn (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε)
    (h1 : (b : Matrix ι ι K) * ε = ε)
    (hD : CFSG.RankThree.PartOne.DicksonDerived
      (Φ.comp (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b)).subtype)
      (ggJSo2_oddOrderIsometry Φ hΦ b hb hodd).polarBilin_fixed_nondegenerate)
    (u : ↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε))
    (w : CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b)) :
    (((glBlockCentralizerEquivFixedDerived Φ hΦ b hb hodd hε h1 hD u :
        ↥(CFSG.RankThree.Classical2.orthDerived
          (Φ.comp (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b)).subtype))) :
        CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b) ≃ₗ[K]
          CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b)) w : (ι → K)) =
      ggJSo2_ML (((u : ↥(glBlockCentralizer
        (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε)) : ↥(StatedOmega ⇑Φ)) : GL ι K)
        (w : ι → K) := by
  show ((((CFSG.HardMathSupport.Dickson.Bal207.OrthFix.fixRestr
      (ggJSo2_oddOrderIsometry Φ hΦ b hb hodd))
      (glBlockCentralizerEquivSupportedFixedDerived Φ hΦ b hb hodd hε h1 hD u) :
      ↥(CFSG.RankThree.Classical2.orthDerived
        (Φ.comp (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b)).subtype))) :
      CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b) ≃ₗ[K]
        CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b)) w : (ι → K)) =
    ggJSo2_ML (((u : ↥(glBlockCentralizer
      (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε)) : ↥(StatedOmega ⇑Φ)) : GL ι K)
      (w : ι → K)
  rw [CFSG.HardMathSupport.Dickson.Bal207.OrthFix.coe_fixRestr_apply,
    glBlockCentralizerEquivSupportedFixedDerived_apply]

noncomputable abbrev fixedSemilinRestrict {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {x : V ≃ₗ[K] V} {S : V ≃+ V} (hSx : ∀ v, S (x v) = x (S v)) :
    CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace x ≃+
      CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace x :=
  CFSG.RankThree.PartOne.KCOrthComm.restrictAdd S hSx

theorem fixedSemilinRestrict_smul {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {x : V ≃ₗ[K] V} {σ : K ≃+* K} {S : V ≃+ V}
    (hS : ∀ (c : K) (v : V), S (c • v) = σ c • S v)
    (hSx : ∀ v, S (x v) = x (S v)) (c : K)
    (w : CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace x) :
    fixedSemilinRestrict hSx (c • w) = σ c • fixedSemilinRestrict hSx w := by
  apply Subtype.ext
  exact hS c (w : V)

theorem fixedSemilinRestrict_preserves_quadraticForm {K V : Type} [Field K]
    [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}
    {σ : K ≃+* K} {S : V ≃+ V}
    (hSx : ∀ v, S (x v) = x (S v)) (hSQ : ∀ v, Q (S v) = σ (Q v))
    (w : CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace x) :
    (Q.comp (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace x).subtype)
        (fixedSemilinRestrict hSx w) =
      σ ((Q.comp (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace x).subtype) w) :=
  hSQ w

theorem glBlockCentralizerEquivFixedDerived_semilin_square
    {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Fintype K] [CharP K 2]
    (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (b : GL ι K) (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b))
    {ε : Matrix ι ι K}
    (hε : IsPrimAdjIdemIn (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε)
    (h1 : (b : Matrix ι ι K) * ε = ε)
    (hD : CFSG.RankThree.PartOne.DicksonDerived
      (Φ.comp (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b)).subtype)
      (ggJSo2_oddOrderIsometry Φ hΦ b hb hodd).polarBilin_fixed_nondegenerate)
    {S : (ι → K) ≃+ (ι → K)}
    (hSx : ∀ v, S (ggJSo2_ML b v) = ggJSo2_ML b (S v))
    {g g' : ↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε)}
    (hgg' : ∀ v, ggJSo2_ML (((g' : ↥(glBlockCentralizer
        (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε)) : ↥(StatedOmega ⇑Φ)) : GL ι K) v =
      S (ggJSo2_ML (((g : ↥(glBlockCentralizer
        (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε)) : ↥(StatedOmega ⇑Φ)) : GL ι K)
        (S.symm v)))
    (w : CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b)) :
    (((glBlockCentralizerEquivFixedDerived Φ hΦ b hb hodd hε h1 hD g' :
        ↥(CFSG.RankThree.Classical2.orthDerived
          (Φ.comp (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b)).subtype))) :
        CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b) ≃ₗ[K]
          CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b)) w) =
      fixedSemilinRestrict hSx
        (((glBlockCentralizerEquivFixedDerived Φ hΦ b hb hodd hε h1 hD g :
          ↥(CFSG.RankThree.Classical2.orthDerived
            (Φ.comp (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b)).subtype))) :
          CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b) ≃ₗ[K]
            CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b))
          ((fixedSemilinRestrict hSx).symm w)) := by
  apply Subtype.ext
  rw [CFSG.RankThree.PartOne.KCOrthComm.coe_restrictAdd,
    glBlockCentralizerEquivFixedDerived_apply_coe,
    glBlockCentralizerEquivFixedDerived_apply_coe,
    CFSG.RankThree.PartOne.KCOrthComm.coe_restrictAdd_symm]
  exact hgg' (w : ι → K)

@[expose] noncomputable def fixedBasisSemilin {K W W' : Type} [Field K]
    [AddCommGroup W] [Module K W] [AddCommGroup W'] [Module K W']
    (e : W ≃ₗ[K] W') (T : W ≃+ W) : W' ≃+ W' where
  toFun v := e (T (e.symm v))
  invFun v := e (T.symm (e.symm v))
  left_inv v := by simp
  right_inv v := by simp
  map_add' v w := by simp only [map_add]

@[simp] theorem fixedBasisSemilin_apply {K W W' : Type} [Field K]
    [AddCommGroup W] [Module K W] [AddCommGroup W'] [Module K W']
    (e : W ≃ₗ[K] W') (T : W ≃+ W) (v : W') :
    fixedBasisSemilin e T v = e (T (e.symm v)) := rfl

@[simp] theorem fixedBasisSemilin_symm_apply {K W W' : Type} [Field K]
    [AddCommGroup W] [Module K W] [AddCommGroup W'] [Module K W']
    (e : W ≃ₗ[K] W') (T : W ≃+ W) (v : W') :
    (fixedBasisSemilin e T).symm v = e (T.symm (e.symm v)) := rfl

theorem fixedBasisSemilin_smul {K W W' : Type} [Field K]
    [AddCommGroup W] [Module K W] [AddCommGroup W'] [Module K W']
    (e : W ≃ₗ[K] W') (T : W ≃+ W) {σ : K ≃+* K}
    (hT : ∀ (c : K) (w : W), T (c • w) = σ c • T w) (c : K) (v : W') :
    fixedBasisSemilin e T (c • v) = σ c • fixedBasisSemilin e T v := by
  simp only [fixedBasisSemilin_apply, map_smul, hT]

theorem fixedBasisSemilin_preserves_quadraticForm {K W W' : Type} [Field K]
    [AddCommGroup W] [Module K W] [AddCommGroup W'] [Module K W']
    {Q : QuadraticForm K W} {Q' : QuadraticForm K W'}
    (e : Q.IsometryEquiv Q') (T : W ≃+ W) {σ : K ≃+* K}
    (hT : ∀ w : W, Q (T w) = σ (Q w)) (v : W') :
    Q' (fixedBasisSemilin e.toLinearEquiv T v) = σ (Q' v) := by
  rw [fixedBasisSemilin_apply]
  calc
    Q' (e.toLinearEquiv (T (e.symm v)))
        = Q (T (e.symm v)) := e.map_app' _
    _ = σ (Q (e.symm v)) := hT _
    _ = σ (Q' v) := by
      congr 1
      have h2 : Q' (e.toLinearEquiv (e.toLinearEquiv.symm v)) =
          Q (e.toLinearEquiv.symm v) := e.map_app' _
      rw [e.toLinearEquiv.apply_symm_apply] at h2
      exact h2.symm

@[expose] noncomputable def glBlockCentralizerEquivFixedDerivedBasis
    {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Fintype K] [CharP K 2]
    (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (b : GL ι K) (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b))
    {ε : Matrix ι ι K}
    (hε : IsPrimAdjIdemIn (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε)
    (h1 : (b : Matrix ι ι K) * ε = ε)
    (hD : CFSG.RankThree.PartOne.DicksonDerived
      (Φ.comp (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b)).subtype)
      (ggJSo2_oddOrderIsometry Φ hΦ b hb hodd).polarBilin_fixed_nondegenerate)
    {d : ℕ} {Φ₁ : QuadraticForm K (Fin d → K)}
    (eIso : (Φ.comp
      (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b)).subtype).IsometryEquiv Φ₁) :
    ↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε) ≃*
      ↥(CFSG.RankThree.Classical2.orthDerived Φ₁) :=
  (glBlockCentralizerEquivFixedDerived Φ hΦ b hb hodd hε h1 hD).trans
    (CFSG.RankThree.PartOne.orthDerivedEquiv eIso)

theorem glBlockCentralizerEquivFixedDerivedBasis_apply
    {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Fintype K] [CharP K 2]
    (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (b : GL ι K) (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b))
    {ε : Matrix ι ι K}
    (hε : IsPrimAdjIdemIn (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε)
    (h1 : (b : Matrix ι ι K) * ε = ε)
    (hD : CFSG.RankThree.PartOne.DicksonDerived
      (Φ.comp (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b)).subtype)
      (ggJSo2_oddOrderIsometry Φ hΦ b hb hodd).polarBilin_fixed_nondegenerate)
    {d : ℕ} {Φ₁ : QuadraticForm K (Fin d → K)}
    (eIso : (Φ.comp
      (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b)).subtype).IsometryEquiv Φ₁)
    (u : ↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε))
    (v : Fin d → K) :
    ((glBlockCentralizerEquivFixedDerivedBasis Φ hΦ b hb hodd hε h1 hD eIso u :
        ↥(CFSG.RankThree.Classical2.orthDerived Φ₁)) :
        (Fin d → K) ≃ₗ[K] (Fin d → K)) v =
      eIso.toLinearEquiv
        (((glBlockCentralizerEquivFixedDerived Φ hΦ b hb hodd hε h1 hD u :
          ↥(CFSG.RankThree.Classical2.orthDerived
            (Φ.comp (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b)).subtype))) :
          CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b) ≃ₗ[K]
            CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b))
          (eIso.toLinearEquiv.symm v)) := by
  rfl

theorem glBlockCentralizerEquivFixedDerivedBasis_square
    {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Fintype K] [CharP K 2]
    (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (b : GL ι K) (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b))
    {ε : Matrix ι ι K}
    (hε : IsPrimAdjIdemIn (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε)
    (h1 : (b : Matrix ι ι K) * ε = ε)
    (hD : CFSG.RankThree.PartOne.DicksonDerived
      (Φ.comp (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b)).subtype)
      (ggJSo2_oddOrderIsometry Φ hΦ b hb hodd).polarBilin_fixed_nondegenerate)
    {d : ℕ} {Φ₁ : QuadraticForm K (Fin d → K)}
    (eIso : (Φ.comp
      (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b)).subtype).IsometryEquiv Φ₁)
    {S : (ι → K) ≃+ (ι → K)}
    (hSx : ∀ v, S (ggJSo2_ML b v) = ggJSo2_ML b (S v))
    {g g' : ↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε)}
    (hgg' : ∀ v, ggJSo2_ML (((g' : ↥(glBlockCentralizer
        (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε)) : ↥(StatedOmega ⇑Φ)) : GL ι K) v =
      S (ggJSo2_ML (((g : ↥(glBlockCentralizer
        (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε)) : ↥(StatedOmega ⇑Φ)) : GL ι K)
        (S.symm v)))
    (v : Fin d → K) :
    ((glBlockCentralizerEquivFixedDerivedBasis Φ hΦ b hb hodd hε h1 hD eIso g' :
        ↥(CFSG.RankThree.Classical2.orthDerived Φ₁)) :
        (Fin d → K) ≃ₗ[K] (Fin d → K)) v =
      fixedBasisSemilin eIso.toLinearEquiv (fixedSemilinRestrict hSx)
        (((glBlockCentralizerEquivFixedDerivedBasis Φ hΦ b hb hodd hε h1 hD eIso g :
          ↥(CFSG.RankThree.Classical2.orthDerived Φ₁)) :
          (Fin d → K) ≃ₗ[K] (Fin d → K))
          ((fixedBasisSemilin eIso.toLinearEquiv (fixedSemilinRestrict hSx)).symm v)) := by
  let e : CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b) ≃ₗ[K]
      (Fin d → K) := eIso.toLinearEquiv
  let T : CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b) ≃+
      CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b) :=
    fixedSemilinRestrict (S := S) hSx
  rw [glBlockCentralizerEquivFixedDerivedBasis_apply,
    glBlockCentralizerEquivFixedDerivedBasis_apply, fixedBasisSemilin_symm_apply]
  have hsquare := glBlockCentralizerEquivFixedDerived_semilin_square Φ hΦ b hb hodd hε h1 hD
    (S := S) hSx (g := g) (g' := g') hgg' (w := e.symm v)
  have h2 := congrArg e hsquare
  rw [fixedBasisSemilin_apply]
  simp only [LinearEquiv.symm_apply_apply]
  exact h2

private lemma ggJSo2_dim_two_conj {K W : Type} [Field K]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W] (R : QuadraticForm K W)
    (hR : (QuadraticMap.polarBilin R).Nondegenerate) (h2 : Module.finrank K W = 2)
    {a : W} (ha : R a ≠ 0) :
    ∃ s ∈ TauCeti.QuadraticMap.orthogonalGroup R, ∀ u : W ≃ₗ[K] W,
      (hu : u ∈ TauCeti.QuadraticMap.orthogonalGroup R) →
      CFSG.RankThree.OrthogonalInvolutions.dicksonHom R hR ⟨u, hu⟩ = 1 → s * u * s = u⁻¹ := by
  have : Nontrivial W := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  let _ : Invertible (R a) := invertibleOfNonzero ha
  set s : W ≃ₗ[K] W := TauCeti.QuadraticMap.reflection R a with hs
  have hsO : s ∈ TauCeti.QuadraticMap.orthogonalGroup R :=
    TauCeti.QuadraticMap.reflection_mem_orthogonalGroup R a
  have hs1 : Module.finrank K (CFSG.RankThree.OrthogonalInvolutions.commSpace s) = 1 :=
    CFSG.RankThree.OrthogonalInvolutions.finrank_commSpace_reflection hR a
  have hδs : CFSG.RankThree.OrthogonalInvolutions.dicksonHom R hR ⟨s, hsO⟩ =
      Multiplicative.ofAdd (1 : ZMod 2) := by
    rw [CFSG.RankThree.OrthogonalInvolutions.dicksonHom_apply]
    simp only [hs1, Nat.cast_one]
  refine ⟨s, hsO, fun u hu hδu => ?_⟩
  have hus : u * s ∈ TauCeti.QuadraticMap.orthogonalGroup R := mul_mem hu hsO
  have hδus : CFSG.RankThree.OrthogonalInvolutions.dicksonHom R hR ⟨u * s, hus⟩ =
      Multiplicative.ofAdd (1 : ZMod 2) := by
    have h1 : (⟨u * s, hus⟩ : ↥(TauCeti.QuadraticMap.orthogonalGroup R)) =
        ⟨u, hu⟩ * ⟨s, hsO⟩ := rfl
    rw [h1, map_mul, hδu, hδs, one_mul]
  have hodd : (Module.finrank K (CFSG.RankThree.OrthogonalInvolutions.commSpace (u * s)) :
      ZMod 2) = 1 := by
    rw [CFSG.RankThree.OrthogonalInvolutions.dicksonHom_apply] at hδus
    exact Multiplicative.ofAdd.injective hδus
  have hle : Module.finrank K (CFSG.RankThree.OrthogonalInvolutions.commSpace (u * s)) ≤ 2 :=
    (Submodule.finrank_le _).trans h2.le
  have h1' : Module.finrank K (CFSG.RankThree.OrthogonalInvolutions.commSpace (u * s)) = 1 := by
    generalize Module.finrank K (CFSG.RankThree.OrthogonalInvolutions.commSpace (u * s)) = n
      at hodd hle
    interval_cases n
    · exact absurd hodd (by decide)
    · rfl
    · exact absurd hodd (by decide)
  have hsq := CFSG.RankThree.PartOne.KCOrthogonal.mul_self_eq_one_of_finrank_commSpace_eq_one
    hR hus h1'
  apply eq_inv_of_mul_eq_one_right
  calc u * (s * u * s) = u * s * (u * s) := by simp only [mul_assoc]
    _ = 1 := hsq

private lemma ggJSo2_finite_linearEquiv {K W : Type} [Field K] [Finite K] [AddCommGroup W]
    [Module K W] [FiniteDimensional K W] : Finite (W ≃ₗ[K] W) := by
  have : Finite W := Module.finite_of_finite K
  exact Finite.of_injective (fun e : W ≃ₗ[K] W => (e : W → W))
    fun _ _ h => LinearEquiv.ext (congrFun h)

private lemma ggJSo2_odd_orderOf_of_dicksonHom_eq_one {K W : Type} [Field K] [Finite K]
    [CharP K 2] [AddCommGroup W] [Module K W] [FiniteDimensional K W] (R : QuadraticForm K W)
    (hR : (QuadraticMap.polarBilin R).Nondegenerate) (hle : Module.finrank K W ≤ 2)
    {g : ↥(TauCeti.QuadraticMap.orthogonalGroup R)}
    (hδ : dicksonHom R hR g = 1) : Odd (orderOf g) := by
  by_contra h
  have heven : Even (orderOf g) := Nat.not_odd_iff_even.mp h
  obtain ⟨k, hk⟩ := heven
  have hk2 : orderOf g = 2 * k := by omega
  haveI : Finite (W ≃ₗ[K] W) := ggJSo2_finite_linearEquiv
  haveI : Finite ↥(TauCeti.QuadraticMap.orthogonalGroup R) :=
    Finite.of_injective (fun x => (x : W ≃ₗ[K] W)) fun _ _ h => Subtype.ext h
  have hpos : 0 < orderOf g := orderOf_pos_iff.mpr (isOfFinOrder_of_finite g)
  have hkne : k ≠ 0 := by omega
  have hlt : k < orderOf g := by omega
  have hgn : g ^ k ≠ 1 := pow_ne_one_of_lt_orderOf hkne hlt
  have hδk : dicksonHom R hR (g ^ k) = 1 := by rw [map_pow, hδ, one_pow]
  have hg2 : (g ^ k) ^ 2 = 1 := by
    rw [← pow_mul, show k * 2 = 2 * k by omega, ← hk2]
    exact pow_orderOf_eq_one g
  have h1 : g ^ k = 1 :=
    twoElt_eq_one_of_dickson_of_finrank_le_two hR hle hδk 1 (by simpa using hg2)
  exact hgn h1

private lemma ggJSo2_dicksonDerived_dim_two {K W : Type} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W] (R : QuadraticForm K W)
    (hR : (QuadraticMap.polarBilin R).Nondegenerate) (h2 : Module.finrank K W = 2) :
    CFSG.RankThree.PartOne.DicksonDerived R hR := by
  intro g hδ
  haveI : Nontrivial W := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  obtain ⟨a, ha⟩ := exists_map_ne_zero (Q := R) hR
  obtain ⟨s, hsO, hconj⟩ := ggJSo2_dim_two_conj R hR h2 ha
  have hodd : Odd (orderOf g) :=
    ggJSo2_odd_orderOf_of_dicksonHom_eq_one R hR (by omega) hδ
  obtain ⟨k, hk⟩ := exists_pow_eq_pow_two_mul (pow_orderOf_eq_one g) hodd 1
  have hg_eq : g = (g ^ k) ^ 2 := by
    have h : g ^ (2 * k) = g := by simpa using hk.symm
    conv_lhs => rw [← h]
    rw [← pow_mul g k 2, Nat.mul_comm k 2]
  have hgsq : (g : W ≃ₗ[K] W) =
      (((g ^ k : ↥(TauCeti.QuadraticMap.orthogonalGroup R)) : W ≃ₗ[K] W)) ^ 2 := by
    conv_lhs => rw [hg_eq]
    rw [Subgroup.coe_pow]
  have hval2_mem : (((g ^ k : ↥(TauCeti.QuadraticMap.orthogonalGroup R)) :
      W ≃ₗ[K] W)) ^ 2 ∈ orthDerived R := by
    set hval : W ≃ₗ[K] W :=
      ((g ^ k : ↥(TauCeti.QuadraticMap.orthogonalGroup R)) : W ≃ₗ[K] W) with hval_def
    have hval_mem : hval ∈ TauCeti.QuadraticMap.orthogonalGroup R := by
      rw [hval_def]
      exact (g ^ k).2
    have hs2 : s * s = 1 := by
      have h := hconj 1 (TauCeti.QuadraticMap.orthogonalGroup R).one_mem (by
        rw [show (⟨1, (TauCeti.QuadraticMap.orthogonalGroup R).one_mem⟩ :
          ↥(TauCeti.QuadraticMap.orthogonalGroup R)) = 1 from rfl]
        exact map_one _)
      simpa using h
    have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
    have hch : s * hval * s = hval⁻¹ := by
      refine hconj hval hval_mem ?_
      have hone : (⟨hval, hval_mem⟩ : ↥(TauCeti.QuadraticMap.orthogonalGroup R)) = g ^ k :=
        Subtype.ext hval_def
      rw [hone, map_pow, hδ, one_pow]
    have hcomm : ⁅s, hval⁆ = hval⁻¹ * hval⁻¹ := by
      rw [commutatorElement_def, hsinv, hch]
    have hcmem : ⁅s, hval⁆ ∈ orthDerived R :=
      Subgroup.commutator_mem_commutator hsO hval_mem
    have h2' : hval ^ 2 = (⁅s, hval⁆)⁻¹ := by
      rw [hcomm]; group
    rw [h2']
    exact Subgroup.inv_mem _ hcmem
  rw [hgsq]
  exact hval2_mem

private lemma ggJSo2_dicksonDerived_of_finrank_le_two {K W : Type} [Field K] [Finite K]
    [CharP K 2] [AddCommGroup W] [Module K W] [FiniteDimensional K W] (R : QuadraticForm K W)
    (hR : (QuadraticMap.polarBilin R).Nondegenerate) (hle : Module.finrank K W ≤ 2) :
    CFSG.RankThree.PartOne.DicksonDerived R hR := by
  have heven : Even (Module.finrank K W) := by
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    refine LinearMap.BilinForm.IsAlt.even_finrank
      (B := QuadraticMap.polarBilin R) (fun a => ?_) hR
    rw [QuadraticMap.polarBilin_apply_apply, polar_self_eq_two_mul, h2, zero_mul]
  obtain ⟨n, hn⟩ := heven
  rcases (show Module.finrank K W = 0 ∨ Module.finrank K W = 2 by omega) with h0 | h2
  · intro g _
    haveI : Subsingleton W := Module.finrank_zero_iff.mp h0
    have hg1 : (g : W ≃ₗ[K] W) = 1 := LinearEquiv.ext fun w => Subsingleton.elim _ _
    rw [hg1]
    exact (orthDerived R).one_mem
  · exact ggJSo2_dicksonDerived_dim_two R hR h2

lemma ggJSo2_dicksonDerived_generic {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (b : GL ι K) (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b))
    (hnot : ¬ (Nat.card K = 2 ∧
      Module.finrank K (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b)) = 4)) :
    CFSG.RankThree.PartOne.DicksonDerived
      (Φ.comp (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b)).subtype)
      (ggJSo2_oddOrderIsometry Φ hΦ b hb hodd).polarBilin_fixed_nondegenerate := by
  let x : (ι → K) ≃ₗ[K] (ι → K) := ggJSo2_ML b
  have hx : CFSG.RankThree.PartOne.KCOrthogonal.OddOrderIsometry Φ (orderOf b) x :=
    ggJSo2_oddOrderIsometry Φ hΦ b hb hodd
  by_cases hK : 4 ≤ Nat.card K
  · by_cases h3 : 3 ≤ Module.finrank K (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace x)
    · exact dicksonDerived_fixedSpace_of_four_le_card hK hx h3
    · exact ggJSo2_dicksonDerived_of_finrank_le_two _
        hx.polarBilin_fixed_nondegenerate (by omega)
  · have hcard2 : Nat.card K = 2 := by
      obtain ⟨n, -, hq⟩ := FiniteField.card K 2
      have hnpos1 : 1 ≤ (n : ℕ) := n.2
      have hlt : 2 ^ (n : ℕ) < 4 := by
        rw [← hq, ← Nat.card_eq_fintype_card]
        omega
      have hn1 : (n : ℕ) = 1 := by
        by_contra hn
        have hn2 : 2 ≤ (n : ℕ) := by omega
        have h4 : 4 ≤ 2 ^ (n : ℕ) := by
          calc (4 : ℕ) = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ (n : ℕ) := Nat.pow_le_pow_right (by norm_num) hn2
        omega
      rw [Nat.card_eq_fintype_card, hq, hn1, pow_one]
    by_cases h4 : 4 ≤ Module.finrank K (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace x)
    · obtain ⟨m, hm⟩ := hx.even_finrank_fixed
      have hne4 : Module.finrank K (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace x) ≠ 4 :=
        fun h => hnot ⟨hcard2, h⟩
      have hmne2 : m ≠ 2 := by
        intro h
        exact hne4 (by omega)
      rcases (by omega : m = 3 ∨ 4 ≤ m) with hm3 | hm4
      · have hd6 : Module.finrank K
            (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace x) = 6 := by omega
        by_cases hT : ∃ U : Submodule K
            (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace x),
            Module.finrank K U = 3 ∧ ∀ u ∈ U,
              (Φ.comp (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace x).subtype) u = 0
        · exact CFSG.RankThree.PartOne.dicksonDerived_of_threeSingular _
            hx.polarBilin_fixed_nondegenerate hT
        · refine (CFSG.RankThree.PartOne.nonsplit_quasisimple_dicksonDerived _
            hx.polarBilin_fixed_nondegenerate (Or.inr hd6) ?_).2
          intro U hU
          have hU3 : Module.finrank K U = 3 := by rw [hd6] at hU; omega
          by_contra hall
          push Not at hall
          exact hT ⟨U, hU3, hall⟩
      · exact CFSG.RankThree.PartOne.dicksonDerived_of_threeSingular _
          hx.polarBilin_fixed_nondegenerate
          (CFSG.RankThree.PartOne.exists_threeSingular_of_dim _
            hx.polarBilin_fixed_nondegenerate hm4 (by omega))
    · obtain ⟨m, hm⟩ := hx.even_finrank_fixed
      exact ggJSo2_dicksonDerived_of_finrank_le_two _
        hx.polarBilin_fixed_nondegenerate (by omega)

noncomputable def glBlockCentralizerEquivFixedDerived_of_generic
    {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Fintype K] [CharP K 2]
    (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (b : GL ι K) (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b))
    {ε : Matrix ι ι K}
    (hε : IsPrimAdjIdemIn (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε)
    (h1 : (b : Matrix ι ι K) * ε = ε)
    (hnot : ¬ (Nat.card K = 2 ∧
      Module.finrank K (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b)) = 4)) :
    ↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε) ≃*
      ↥(CFSG.RankThree.Classical2.orthDerived
        (Φ.comp (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b)).subtype)) :=
  glBlockCentralizerEquivFixedDerived Φ hΦ b hb hodd hε h1
    (ggJSo2_dicksonDerived_generic Φ hΦ b hb hodd hnot)

private lemma ggJSo2e_plus_four_case {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι)
    (b : GL ι K) (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b))
    {ε : Matrix ι ι K}
    (hε : IsPrimAdjIdemIn (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε)
    (h1 : (b : Matrix ι ι K) * ε = ε) (hK : Fintype.card K = 2)
    (h4 : Module.finrank K (LinearMap.range (Matrix.toLin' ε)) = 4)
    (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType
      (Φ.comp (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b)).subtype)) :
    IsSolvable ↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε) ∧
      padicValNat 2 (Nat.card ↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε)) = 2 := by
  classical
  let x : (ι → K) ≃ₗ[K] (ι → K) := ggJSo2_ML b
  let W : Submodule K (ι → K) := CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace x
  let R : QuadraticForm K W := Φ.comp W.subtype
  have hx : CFSG.RankThree.PartOne.KCOrthogonal.OddOrderIsometry Φ (orderOf b) x :=
    ggJSo2_oddOrderIsometry Φ hΦ b hb hodd
  have hR : (QuadraticMap.polarBilin R).Nondegenerate := hx.polarBilin_fixed_nondegenerate
  have hrange : LinearMap.range (Matrix.toLin' ε) = W := by
    simpa only [x, W] using ggJSo2_range_eq_fixedSpace Φ b hodd hε h1
  have hW4 : Module.finrank K W = 4 := by rw [← hrange]; exact h4
  haveI : Nontrivial ↥W := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have hX : (X - 1 : K[X]) ∈ primaryFactors x.toLinearMap := by
    by_contra hmem
    have hbot : W = ⊥ := by
      simpa only [W] using fixedSpace_eq_bot_of_not_mem (x := x) hmem
    rw [hbot, finrank_bot] at hW4
    omega
  have hDΦ : CFSG.RankThree.PartOne.DicksonDerived Φ hΦ :=
    CFSG.RankThree.PartOne.dicksonDerived_of_threeSingular Φ hΦ
      (ggOmegaBlk_threeSingular Φ hΦ h8)
  have horthOmega : orthDerived Φ = omegaGroup Φ hΦ := by
    apply le_antisymm
    · exact CFSG.RankThree.PartOne.FieldFix.orthDerived_le_omegaGroup hΦ
    · intro g hg
      refine hDΦ ⟨g, omegaGroup_le Φ hΦ hg⟩ ?_
      have h1' : (⟨g, omegaGroup_le Φ hΦ hg⟩ : ↥(TauCeti.QuadraticMap.orthogonalGroup Φ)) ∈
          (dicksonHom Φ hΦ).ker := by
        rw [dicksonHom_ker]
        exact Subgroup.mem_subgroupOf.mpr hg
      exact MonoidHom.mem_ker.mp h1'
  let Ksub : Subgroup ((ι → K) ≃ₗ[K] (ι → K)) :=
    CFSG.RankThree.PartOne.KCOrthogonal.supportedBlock Φ x (X - 1) ⊓ orthDerived Φ
  let Ksub' : Subgroup ↥(CFSG.RankThree.PartOne.KCOrthogonal.supportedBlock Φ x (X - 1)) :=
    Ksub.subgroupOf (CFSG.RankThree.PartOne.KCOrthogonal.supportedBlock Φ x (X - 1))
  have himage : Ksub'.map (restrictFixed Φ x) = omegaGroup R hR := by
    ext h
    constructor
    · rintro ⟨g, hg, rfl⟩
      have hg1 : (g : (ι → K) ≃ₗ[K] (ι → K)) ∈ orthDerived Φ :=
        (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hg)).2
      have hω : (g : (ι → K) ≃ₗ[K] (ι → K)) ∈ omegaGroup Φ hΦ := horthOmega ▸ hg1
      have heven : Even (Module.finrank K (commSpace (g : (ι → K) ≃ₗ[K] (ι → K)))) :=
        (mem_omegaGroup.mp hω).2
      rw [mem_omegaGroup]
      exact ⟨restrictFixed_mem_orthogonalGroup g,
        by rwa [← hx.finrank_commSpace_eq_restrictFixed g.2]⟩
    · intro hh
      have hhO : h ∈ TauCeti.QuadraticMap.orthogonalGroup R := (mem_omegaGroup.mp hh).1
      let g : ↥(CFSG.RankThree.PartOne.KCOrthogonal.supportedBlock Φ x (X - 1)) :=
        (fixedBlockEquiv hx).symm ⟨h, hhO⟩
      have hcoe : restrictFixed Φ x g = h :=
        congrArg Subtype.val ((fixedBlockEquiv hx).apply_symm_apply ⟨h, hhO⟩)
      refine ⟨g, ?_, ?_⟩
      · refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨g.2, ?_⟩)
        rw [horthOmega, mem_omegaGroup]
        refine ⟨(Subgroup.mem_inf.mp (mem_supportedBlock.mp g.2).1).1, ?_⟩
        rw [hx.finrank_commSpace_eq_restrictFixed g.2, hcoe]
        exact (mem_omegaGroup.mp hh).2
      · exact hcoe
  have hmap := ggJSo2_map_G_eq Φ hΦ b hb hodd hε h1
  let f : ↥(StatedOmega ⇑Φ) →* ((ι → K) ≃ₗ[K] (ι → K)) :=
    (ggJSo2_ML (ι := ι) (K := K)).toMonoidHom.comp (StatedOmega ⇑Φ).subtype
  have hf : Function.Injective f := fun a c hac =>
    Subtype.ext ((ggJSo2_ML (ι := ι) (K := K)).injective hac)
  let eMap : ↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε) ≃* ↥Ksub :=
    (Subgroup.equivMapOfInjective
      (glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε) f hf).trans
      (MulEquiv.subgroupCongr (by simpa only [Ksub, x] using hmap))
  let eOmega : ↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε) ≃* ↥(omegaGroup R hR) :=
    eMap.trans ((Subgroup.subgroupOfEquivOfLe inf_le_left).symm.trans
      ((Subgroup.equivMapOfInjective Ksub' (restrictFixed Φ x)
        (restrictFixed_injective hx)).trans (MulEquiv.subgroupCongr himage)))
  have hK' : Nat.card K = 2 := by rwa [Nat.card_eq_fintype_card]
  have hOsolv : Group.IsSolvable ↥(TauCeti.QuadraticMap.orthogonalGroup R) :=
    CFSG.LocalAnalysis.GLTheoremA.T123CB.isSolvable_orthogonalGroup_of_card_two_of_plus
      R hR hK' hW4 hplus
  have hOmegasolv : Group.IsSolvable ↥(omegaGroup R hR) :=
    Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion (omegaGroup_le R hR))
      (Subgroup.inclusion_injective (omegaGroup_le R hR))
  have hGsolv : Group.IsSolvable ↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε) :=
    Group.isSolvable_of_isSolvable_injective (f := eOmega.toMonoidHom) eOmega.injective
  have hc := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type hR (m := 1)
    (by rw [hW4]) (ε := 1) (Or.inl ⟨rfl, hplus⟩)
  rw [hK'] at hc
  have h72 : Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup R) = 72 := by
    have h1' : (Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup R) : ℤ) = 72 := by
      rw [hc]; decide
    exact_mod_cast h1'
  have hcardΩ : Nat.card ↥(omegaGroup R hR) = 36 := by
    have hmul := Subgroup.relIndex_mul_card (H := omegaGroup R hR)
      (K := TauCeti.QuadraticMap.orthogonalGroup R)
    rw [inf_of_le_left (omegaGroup_le R hR),
      CFSG.RankThree.OrthogonalInvolutions.relIndex_omegaGroup R hR, h72] at hmul
    omega
  have hcardG : Nat.card ↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε) = 36 := by
    rw [Nat.card_congr eOmega.toEquiv, hcardΩ]
  refine ⟨hGsolv, ?_⟩
  rw [hcardG, show (36 : ℕ) = 2 ^ 2 * 9 by norm_num,
    padicValNat.mul (p := 2) (by norm_num) (by norm_num),
    padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 9)]

theorem blockGroup_iso_Omega_one {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι)
    (b : GL ι K) (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b))
    {ε : Matrix ι ι K}
    (hε : IsPrimAdjIdemIn (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε)
    (h1 : (b : Matrix ι ι K) * ε = ε) :
    ∃ (ι₁ : Type) (_ : Fintype ι₁) (_ : DecidableEq ι₁) (Q₁ : (ι₁ → K) → K),
      Fintype.card ι₁ = Module.finrank K (LinearMap.range (Matrix.toLin' ε)) ∧
      (∃ Φ₁ : QuadraticForm K (ι₁ → K), ⇑Φ₁ = Q₁ ∧ (QuadraticMap.polarBilin Φ₁).Nondegenerate) ∧
      ((Nonempty (↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε) ≃* ↥(StatedOmega Q₁)) ∧
          ¬ (Fintype.card K = 2 ∧ Fintype.card ι₁ = 4 ∧
              ∃ S : Submodule K (ι₁ → K), Module.finrank K S = 2 ∧ ∀ x ∈ S, Q₁ x = 0)) ∨
        (Fintype.card K = 2 ∧ Fintype.card ι₁ = 4 ∧
          IsSolvable ↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε) ∧
          padicValNat 2 (Nat.card ↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε)) = 2)) := by
  classical
  have hx : CFSG.RankThree.PartOne.KCOrthogonal.OddOrderIsometry Φ (orderOf b)
      (ggJSo2_ML b) := ggJSo2_oddOrderIsometry Φ hΦ b hb hodd
  have hrange : LinearMap.range (Matrix.toLin' ε) =
      CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b) :=
    ggJSo2_range_eq_fixedSpace Φ b hodd hε h1
  let W := CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b)
  have hW : LinearMap.range (Matrix.toLin' ε) = W := hrange
  let d := Module.finrank K W
  let bW : Module.Basis (Fin d) K W := Module.finBasisOfFinrankEq K W rfl
  let R : QuadraticForm K W := Φ.comp W.subtype
  have hR : (QuadraticMap.polarBilin R).Nondegenerate := hx.polarBilin_fixed_nondegenerate
  let Φ₁ : QuadraticForm K (Fin d → K) := R.comp bW.equivFun.symm.toLinearMap
  have hnd1 : (QuadraticMap.polarBilin Φ₁).Nondegenerate := by
    rw [QuadraticMap.polarBilin_comp]
    constructor
    · intro x hx0
      apply bW.equivFun.symm.injective
      rw [map_zero]
      refine hR.1 (bW.equivFun.symm x) fun y => ?_
      have h := hx0 (bW.equivFun y)
      change (QuadraticMap.polarBilin R) (bW.equivFun.symm x)
        (bW.equivFun.symm (bW.equivFun y)) = 0 at h
      rwa [LinearEquiv.symm_apply_apply] at h
    · intro y hy0
      apply bW.equivFun.symm.injective
      rw [map_zero]
      refine hR.2 (bW.equivFun.symm y) fun x => ?_
      have h := hy0 (bW.equivFun x)
      change (QuadraticMap.polarBilin R) (bW.equivFun.symm (bW.equivFun x))
        (bW.equivFun.symm y) = 0 at h
      rwa [LinearEquiv.symm_apply_apply] at h
  have hcardfin : Fintype.card (Fin d) =
      Module.finrank K (LinearMap.range (Matrix.toLin' ε)) := by
    rw [hW]
    simp [d]
  refine ⟨Fin d, inferInstance, inferInstance, ⇑Φ₁, hcardfin, ⟨Φ₁, rfl, hnd1⟩, ?_⟩
  have build : CFSG.RankThree.PartOne.DicksonDerived
      (Φ.comp (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b)).subtype)
      (ggJSo2_oddOrderIsometry Φ hΦ b hb hodd).polarBilin_fixed_nondegenerate →
      Nonempty (↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε) ≃* ↥(StatedOmega ⇑Φ₁)) := by
    intro hD
    let eIso : R.IsometryEquiv Φ₁ :=
      { toLinearEquiv := bW.equivFun
        map_app' := fun w => by
          show Φ₁ (bW.equivFun w) = R w
          show R (bW.equivFun.symm (bW.equivFun w)) = R w
          rw [LinearEquiv.symm_apply_apply] }
    let eFixed : ↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε) ≃*
        ↥(orthDerived R) :=
      glBlockCentralizerEquivFixedDerived Φ hΦ b hb hodd hε h1 hD
    let e3 : ↥(orthDerived R) ≃* ↥(orthDerived Φ₁) :=
      CFSG.RankThree.PartOne.orthDerivedEquiv eIso
    let e4 : ↥(StatedOmega ⇑Φ₁) ≃* ↥(orthDerived Φ₁) :=
      (Subgroup.equivMapOfInjective (StatedOmega ⇑Φ₁)
        (ggJSo2_ML (ι := Fin d) (K := K)).toMonoidHom
        (ggJSo2_ML (ι := Fin d) (K := K)).injective).trans
        (MulEquiv.subgroupCongr (ggJSo2_map_statedOmega Φ₁))
    exact ⟨eFixed.trans (e3.trans e4.symm)⟩
  by_cases hspecial : Fintype.card K = 2 ∧
      Module.finrank K (LinearMap.range (Matrix.toLin' ε)) = 4
  · have hdimW : Module.finrank K W = 4 := by rw [← hW]; exact hspecial.2
    by_cases hminus : ∀ U : Submodule K W, Module.finrank K U = Module.finrank K W / 2 →
        ∃ u ∈ U, R u ≠ 0
    · left
      refine ⟨build (CFSG.RankThree.PartOne.nonsplit_quasisimple_dicksonDerived R hR
        (Or.inl hdimW) hminus).2, ?_⟩
      rintro ⟨-, -, S, hS2, hS0⟩
      let S' : Submodule K W := S.map bW.equivFun.symm.toLinearMap
      have hS' : Module.finrank K S' = 2 := by
        change Module.finrank K (S.map bW.equivFun.symm.toLinearMap) = 2
        rw [LinearEquiv.finrank_map_eq bW.equivFun.symm S]
        exact hS2
      have hS0' : ∀ u ∈ S', R u = 0 := by
        rintro u hu
        obtain ⟨x, hxS, rfl⟩ := Submodule.mem_map.mp hu
        have h := hS0 x hxS
        simpa only [Φ₁, QuadraticMap.comp_apply] using h
      obtain ⟨u, hu, hne⟩ := hminus S' (by rw [hS', hdimW])
      exact hne (hS0' u hu)
    · right
      have hplus : CFSG.GroupTheory.WeirSylow.IsPlusType R := by
        push Not at hminus
        obtain ⟨U, hU, hU0⟩ := hminus
        exact ⟨U, by simp [hU, hdimW], hU0⟩
      exact ⟨hspecial.1, by rw [hcardfin, hspecial.2],
        ggJSo2e_plus_four_case Φ hΦ h8 b hb hodd hε h1 hspecial.1 hspecial.2 hplus⟩
  · left
    refine ⟨build (ggJSo2_dicksonDerived_generic Φ hΦ b hb hodd (by
      rintro ⟨hK2, hdim4⟩
      exact hspecial ⟨by rwa [Nat.card_eq_fintype_card] at hK2, by rw [hW]; exact hdim4⟩)), ?_⟩
    rintro ⟨hK2, hcard4, -⟩
    exact hspecial ⟨hK2, by rw [← hcardfin]; exact hcard4⟩

theorem paired_prim_idem_primary_reciprocal
    {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (Φ : QuadraticForm K (ι → K)) (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (b : GL ι K) {p : ℕ} {x : (ι → K) ≃ₗ[K] (ι → K)}
    (hx : OddOrderIsometry Φ p x)
    {ε e e' : Matrix ι ι K} {a a' : K[X]}
    (ha : a ∈ primaryFactors x.toLinearMap) (ha' : a' ∈ primaryFactors x.toLinearMap)
    (hae : Matrix.toLinAlgEquiv' e = primaryProjection x.toLinearMap a)
    (ha'e : Matrix.toLinAlgEquiv' e' = primaryProjection x.toLinearMap a')
    (hεe : ε = e + e') (hne : e ≠ e')
    (hε : IsPrimAdjIdemIn (RingHom.id K)
      (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε)
    (he : IsPrimIdemIn (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) e)
    (he' : IsPrimIdemIn (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) e') :
    a' = reciprocalPolynomial a ∧ a ≠ reciprocalPolynomial a := by
  have hG : IsUnit (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)).det :=
    ggOmegaBlk_G_isUnit_det Φ hΦ
  have ha_ne : a ≠ a' := by
    intro h
    exact hne (Matrix.toLinAlgEquiv'.injective (by rw [hae, ha'e, h]))
  have hεself : ∀ z w, QuadraticMap.polar Φ (ε.mulVec z) w =
      QuadraticMap.polar Φ z (ε.mulVec w) :=
    ggOmegaBlk_polar_selfAdjoint Φ hG hε.2.2.2.1
  have hεlin : Matrix.toLinAlgEquiv' ε = primaryProjection x.toLinearMap a +
      primaryProjection x.toLinearMap a' := by
    rw [hεe, map_add, hae, ha'e]
  have hsum : Matrix.toLinAlgEquiv' ε =
      primaryProjection x.toLinearMap (reciprocalPolynomial a) +
        primaryProjection x.toLinearMap (reciprocalPolynomial a') := by
    apply LinearMap.ext
    intro w
    rw [← sub_eq_zero]
    apply hΦ.1
    intro u
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_sub_left, sub_eq_zero]
    rw [QuadraticMap.polar_comm Φ _ u, QuadraticMap.polar_comm Φ _ u]
    rw [Matrix.toLinAlgEquiv'_apply, ← hεself u w, LinearMap.add_apply,
      QuadraticMap.polar_add_right,
      ← ggOmegaBlk_polar_adjoint_primaryProjection hx ha u w,
      ← ggOmegaBlk_polar_adjoint_primaryProjection hx ha' u w,
      ← QuadraticMap.polar_add_left, ← LinearMap.add_apply, ← hεlin,
      Matrix.toLinAlgEquiv'_apply]
  have hcases : a = reciprocalPolynomial a ∨ a' = reciprocalPolynomial a := by
    have h4 : primaryProjection x.toLinearMap a + primaryProjection x.toLinearMap a' =
        primaryProjection x.toLinearMap (reciprocalPolynomial a) +
          primaryProjection x.toLinearMap (reciprocalPolynomial a') :=
      hεlin.symm.trans hsum
    have h := congrArg (fun T => primaryProjection x.toLinearMap a * T) h4
    have hL : primaryProjection x.toLinearMap a *
        (primaryProjection x.toLinearMap a + primaryProjection x.toLinearMap a') =
        primaryProjection x.toLinearMap a := by
      rw [mul_add, primaryProjection_mul_self hx.squarefree_minpoly ha,
        ggOmegaBlk_primaryProjection_mul_eq_zero hx.squarefree_minpoly ha ha' ha_ne, add_zero]
    rw [hL] at h
    by_contra hcon
    push Not at hcon
    have hcon2 : a ≠ reciprocalPolynomial a' := by
      intro h
      have h' : reciprocalPolynomial a = a' := by
        rw [h, hx.reciprocal_reciprocal_eq ha']
      exact hcon.2 h'.symm
    rw [mul_add,
      ggOmegaBlk_primaryProjection_mul_eq_zero hx.squarefree_minpoly ha
        (hx.reciprocalPolynomial_mem ha) hcon.1,
      ggOmegaBlk_primaryProjection_mul_eq_zero hx.squarefree_minpoly ha
        (hx.reciprocalPolynomial_mem ha') hcon2, add_zero] at h
    exact (fun h0 => primaryProjectionR_ne_zero hx.squarefree_minpoly ha
      (Subtype.ext h0)) h
  have ha_ne_self : a ≠ reciprocalPolynomial a := by
    intro haself
    have hadj : formAdj (RingHom.id K)
        (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)) e = e := by
      apply Matrix.toLinAlgEquiv'.injective
      rw [ggOmegaBlk_matrix_adjoint_primaryProjection Φ hΦ hx ha hae, ← haself, hae]
    have h_ee' : e * e' = 0 := by
      apply Matrix.toLinAlgEquiv'.injective
      rw [map_mul, hae, ha'e, map_zero]
      exact ggOmegaBlk_primaryProjection_mul_eq_zero hx.squarefree_minpoly ha ha' ha_ne
    have hee : e * ε = e := by
      rw [hεe, mul_add, he.2.1.eq, h_ee', add_zero]
    rcases hε.2.2.2.2 e he.1 he.2.1 hadj hee with h0 | hεeq
    · exact he.2.2.1 h0
    · have h' : e' = 0 := by
        rw [hεe] at hεeq
        have h2 : e + 0 = e + e' := by rw [add_zero]; exact hεeq
        exact (add_left_cancel h2).symm
      exact he'.2.2.1 h'
  refine ⟨?_, ha_ne_self⟩
  rcases hcases with h | h
  · exact absurd h ha_ne_self
  · exact h

private lemma ggJSo2b_proj_orbit
    {K : Type} [Field K] {ι : Type} [Fintype ι]
    (Φ : QuadraticForm K (ι → K))
    {p : ℕ} {x : (ι → K) ≃ₗ[K] (ι → K)} (hx : OddOrderIsometry Φ p x)
    {a : K[X]} (ha : a ∈ primaryFactors x.toLinearMap)
    (hne : a ≠ reciprocalPolynomial a) :
    ∀ u ∈ orbitSpace x.toLinearMap a,
      (primaryProjection x.toLinearMap a +
        primaryProjection x.toLinearMap (reciprocalPolynomial a)) u = u := by
  intro u hu
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Submodule.mem_sup.mp hu
  rw [LinearMap.add_apply, map_add, map_add,
    primaryProjection_of_mem hx.squarefree_minpoly ha hu₁,
    primaryProjection_of_mem_ne hx.squarefree_minpoly ha (hx.reciprocalPolynomial_mem ha)
      (Ne.symm hne) hu₂,
    primaryProjection_of_mem_ne hx.squarefree_minpoly (hx.reciprocalPolynomial_mem ha) ha hne hu₁,
    primaryProjection_of_mem hx.squarefree_minpoly (hx.reciprocalPolynomial_mem ha) hu₂,
    add_zero, zero_add]

private lemma ggJSo2b_proj_others
    {K : Type} [Field K] {ι : Type} [Fintype ι]
    (Φ : QuadraticForm K (ι → K))
    {p : ℕ} {x : (ι → K) ≃ₗ[K] (ι → K)} (hx : OddOrderIsometry Φ p x)
    {a : K[X]} (ha : a ∈ primaryFactors x.toLinearMap) :
    ∀ v ∈ othersSpace x.toLinearMap a,
      (primaryProjection x.toLinearMap a +
        primaryProjection x.toLinearMap (reciprocalPolynomial a)) v = 0 := by
  intro v hv
  unfold othersSpace at hv
  refine Submodule.iSup_induction _ (motive := fun v => (primaryProjection x.toLinearMap a +
      primaryProjection x.toLinearMap (reciprocalPolynomial a)) v = 0) hv
    (fun k w hw => ?_) (by simp)
    (fun x y hx hy => by rw [map_add, hx, hy, add_zero])
  refine Submodule.iSup_induction _ (motive := fun w => (primaryProjection x.toLinearMap a +
      primaryProjection x.toLinearMap (reciprocalPolynomial a)) w = 0) hw
    (fun hk w hw => ?_) (by simp)
    (fun x y hx hy => by rw [map_add, hx, hy, add_zero])
  rw [LinearMap.add_apply,
    primaryProjection_of_mem_ne hx.squarefree_minpoly ha hk.1 hk.2.1 hw,
    primaryProjection_of_mem_ne hx.squarefree_minpoly (hx.reciprocalPolynomial_mem ha) hk.1
      hk.2.2 hw, add_zero]

private lemma ggJSo2b_ker
    {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (Φ : QuadraticForm K (ι → K))
    {p : ℕ} {x : (ι → K) ≃ₗ[K] (ι → K)} (hx : OddOrderIsometry Φ p x)
    {a : K[X]} (ha : a ∈ primaryFactors x.toLinearMap)
    (hne : a ≠ reciprocalPolynomial a) {ε : Matrix ι ι K}
    (ht : Matrix.toLinAlgEquiv' ε = primaryProjection x.toLinearMap a +
      primaryProjection x.toLinearMap (reciprocalPolynomial a)) :
    LinearMap.ker (Matrix.toLin' ε) = othersSpace x.toLinearMap a := by
  rw [← ggOmegaBlk_toLinAlgEquiv'_eq_toLin' ε, ht]
  apply le_antisymm
  · intro v hv
    rw [LinearMap.mem_ker] at hv
    obtain ⟨u, hu, r, hr, rfl⟩ := exists_add_of_isCompl (hx.isCompl_orbit_others ha) v
    have hpu : (primaryProjection x.toLinearMap a +
        primaryProjection x.toLinearMap (reciprocalPolynomial a)) u = u :=
      ggJSo2b_proj_orbit Φ hx ha hne u hu
    have hpr : (primaryProjection x.toLinearMap a +
        primaryProjection x.toLinearMap (reciprocalPolynomial a)) r = 0 :=
      ggJSo2b_proj_others Φ hx ha r hr
    rw [map_add, hpu, hpr, add_zero] at hv
    rw [hv, zero_add]
    exact hr
  · intro v hv
    exact ggJSo2b_proj_others Φ hx ha v hv

private lemma ggJSo2b_range_one_sub
    {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (Φ : QuadraticForm K (ι → K))
    {p : ℕ} {x : (ι → K) ≃ₗ[K] (ι → K)} (hx : OddOrderIsometry Φ p x)
    {a : K[X]} (ha : a ∈ primaryFactors x.toLinearMap)
    (hne : a ≠ reciprocalPolynomial a) {ε : Matrix ι ι K}
    (ht : Matrix.toLinAlgEquiv' ε = primaryProjection x.toLinearMap a +
      primaryProjection x.toLinearMap (reciprocalPolynomial a)) :
    LinearMap.range (Matrix.toLin' (1 - ε)) = othersSpace x.toLinearMap a := by
  have hker := ggJSo2b_ker Φ hx ha hne ht
  have hp : IsIdempotentElem (Matrix.toLin' ε) := by
    rw [← ggOmegaBlk_toLinAlgEquiv'_eq_toLin' ε, ht]
    show (primaryProjection x.toLinearMap a +
      primaryProjection x.toLinearMap (reciprocalPolynomial a)) *
      (primaryProjection x.toLinearMap a +
        primaryProjection x.toLinearMap (reciprocalPolynomial a)) =
      primaryProjection x.toLinearMap a +
        primaryProjection x.toLinearMap (reciprocalPolynomial a)
    rw [add_mul, mul_add, mul_add,
      primaryProjection_mul_self hx.squarefree_minpoly ha,
      ggOmegaBlk_primaryProjection_mul_eq_zero hx.squarefree_minpoly ha
        (hx.reciprocalPolynomial_mem ha) hne,
      ggOmegaBlk_primaryProjection_mul_eq_zero hx.squarefree_minpoly
        (hx.reciprocalPolynomial_mem ha) ha (Ne.symm hne),
      primaryProjection_mul_self hx.squarefree_minpoly (hx.reciprocalPolynomial_mem ha)]
    abel
  rw [ggOmegaBlk_toLin_one_sub, ← LinearMap.IsIdempotentElem.ker_eq_range_one_sub hp, hker]

private lemma ggJSo2b_range
    {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (Φ : QuadraticForm K (ι → K))
    {p : ℕ} {x : (ι → K) ≃ₗ[K] (ι → K)} (hx : OddOrderIsometry Φ p x)
    {a : K[X]} (ha : a ∈ primaryFactors x.toLinearMap)
    (hne : a ≠ reciprocalPolynomial a) {ε : Matrix ι ι K}
    (ht : Matrix.toLinAlgEquiv' ε = primaryProjection x.toLinearMap a +
      primaryProjection x.toLinearMap (reciprocalPolynomial a)) :
    LinearMap.range (Matrix.toLin' ε) = orbitSpace x.toLinearMap a := by
  rw [← ggOmegaBlk_toLinAlgEquiv'_eq_toLin' ε, ht]
  apply le_antisymm
  · rintro y ⟨v, rfl⟩
    rw [LinearMap.add_apply]
    exact Submodule.add_mem_sup (primaryProjection_mem hx.squarefree_minpoly ha v)
      (primaryProjection_mem hx.squarefree_minpoly (hx.reciprocalPolynomial_mem ha) v)
  · intro y hy
    exact ⟨y, ggJSo2b_proj_orbit Φ hx ha hne y hy⟩

private lemma ggJSo2b_finrank_reciprocal
    {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x)
    {a : K[X]} (ha : a ∈ primaryFactors x.toLinearMap) :
    Module.finrank K (primaryComponent x.toLinearMap a) =
      Module.finrank K (primaryComponent x.toLinearMap (reciprocalPolynomial a)) := by
  have hinj : Function.Injective (pairingHom Q x a) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    refine Subtype.ext (hx.eq_zero_of_polar_paired_left ha u.2 fun w hw => ?_)
    simpa [pairingHom_apply] using LinearMap.congr_fun hu ⟨w, hw⟩
  have hinj2 : Function.Injective (pairingHom Q x a).flip := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    refine Subtype.ext (hx.eq_zero_of_polar_paired_right ha w.2 fun u hu => ?_)
    simpa [pairingHom_apply] using LinearMap.congr_fun hw ⟨u, hu⟩
  refine le_antisymm ?_ ?_
  · have h := LinearMap.finrank_le_finrank_of_injective hinj
    rwa [Subspace.dual_finrank_eq] at h
  · have h := LinearMap.finrank_le_finrank_of_injective hinj2
    rwa [Subspace.dual_finrank_eq] at h

theorem map_glBlockCentralizer_eq_supportedBlock_linear
    {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Fintype K] [CharP K 2]
    (Φ : QuadraticForm K (ι → K)) (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (h8 : 8 ≤ Fintype.card ι) (b : GL ι K)
    {ε e e' : Matrix ι ι K} {a : K[X]}
    (hx : OddOrderIsometry Φ (orderOf b) (toLinEquiv ι K b))
    (hp2 : Odd (orderOf b))
    (ha : a ∈ primaryFactors (toLinEquiv ι K b).toLinearMap)
    (hae : Matrix.toLinAlgEquiv' e = primaryProjection (toLinEquiv ι K b).toLinearMap a)
    (ha'e : Matrix.toLinAlgEquiv' e' =
      primaryProjection (toLinEquiv ι K b).toLinearMap (reciprocalPolynomial a))
    (hne : a ≠ reciprocalPolynomial a)
    (hεe : ε = e + e') :
    (glBlockCentralizer (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε).map
      ((toLinEquiv ι K).toMonoidHom.comp (StatedOmega ⇑Φ).subtype) =
      supportedBlock Φ (toLinEquiv ι K b) a := by
  have hne1 : a ≠ X - 1 := fun h => hne (by rw [h, reciprocalPolynomial_X_sub_one])
  have hsub : supportedBlock Φ (toLinEquiv ι K b) a ≤ orthDerived Φ :=
    ggOmegaBlk_supportedBlock_le_orthDerived Φ hΦ h8 hx hp2 ha hne1
  have htoLinε : Matrix.toLinAlgEquiv' ε = primaryProjection (toLinEquiv ι K b).toLinearMap a +
      primaryProjection (toLinEquiv ι K b).toLinearMap (reciprocalPolynomial a) := by
    rw [hεe, map_add, hae, ha'e]
  ext g
  constructor
  · intro hg
    rw [Subgroup.mem_map] at hg
    obtain ⟨u, hu, hgu⟩ := hg
    have hu' : ((u : ↥(StatedOmega ⇑Φ)) : GL ι K) ∈
        Subgroup.centralizer ({b} : Set (GL ι K)) ⊓ glFixing (1 - ε) :=
      Subgroup.mem_comap.mp hu
    have hcent : ((u : ↥(StatedOmega ⇑Φ)) : GL ι K) ∈
        Subgroup.centralizer ({b} : Set (GL ι K)) := (Subgroup.mem_inf.mp hu').1
    have hfix : ((u : ↥(StatedOmega ⇑Φ)) : GL ι K) ∈ glFixing (1 - ε) :=
      (Subgroup.mem_inf.mp hu').2
    have hbb : ((u : ↥(StatedOmega ⇑Φ)) : GL ι K) * b =
        b * ((u : ↥(StatedOmega ⇑Φ)) : GL ι K) :=
      (Subgroup.mem_centralizer_singleton_iff).mp hcent
    rw [mem_supportedBlock]
    constructor
    · rw [mem_isometryCentralizer]
      constructor
      · intro v
        have hom : toLinEquiv ι K ((u : ↥(StatedOmega ⇑Φ)) : GL ι K) ∈ orthDerived Φ := by
          have h : ((u : ↥(StatedOmega ⇑Φ)) : GL ι K) ∈
              (orthDerived Φ).comap (toLinEquiv ι K).toMonoidHom := by
            rw [← statedOmega_eq_comap (Q := Φ) (Q₀ := ⇑Φ) rfl]
            exact u.2
          exact Subgroup.mem_comap.mp h
        have hO := CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup
          (Q := Φ) hom
        have hv := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hO v
        rw [← hgu]
        exact hv
      · intro v
        have hcomm2 : toLinEquiv ι K ((u : ↥(StatedOmega ⇑Φ)) : GL ι K) *
            toLinEquiv ι K b = toLinEquiv ι K b *
              toLinEquiv ι K ((u : ↥(StatedOmega ⇑Φ)) : GL ι K) := by
          rw [← map_mul, ← map_mul, hbb]
        have hv := congrArg (fun e : (ι → K) ≃ₗ[K] (ι → K) => e v) hcomm2
        rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply] at hv
        rw [← hgu]
        exact hv
    · intro v hv
      have hfix' : ∀ w, Matrix.toLin' (((u : ↥(StatedOmega ⇑Φ)) : GL ι K) : Matrix ι ι K)
          (Matrix.toLin' (1 - ε) w) = Matrix.toLin' (1 - ε) w :=
        (ggOmegaBlk_mem_glFixing_iff (((u : ↥(StatedOmega ⇑Φ)) : GL ι K)) (1 - ε)).mp hfix
      rw [← ggJSo2b_range_one_sub Φ hx ha hne htoLinε] at hv
      obtain ⟨w, rfl⟩ := hv
      rw [← hgu]
      change Matrix.toLin' (((u : ↥(StatedOmega ⇑Φ)) : GL ι K) : Matrix ι ι K)
        (Matrix.toLin' (1 - ε) w) = Matrix.toLin' (1 - ε) w
      exact hfix' w
  · intro hg
    rw [Subgroup.mem_map]
    have hg' := hg
    rw [mem_supportedBlock] at hg'
    obtain ⟨hcent, hfixx⟩ := hg'
    have hcommv : ∀ v, g (toLinEquiv ι K b v) = toLinEquiv ι K b (g v) :=
      (mem_isometryCentralizer.mp hcent).2
    have hgΩ : g ∈ orthDerived Φ := hsub hg
    let w : GL ι K := (toLinEquiv ι K).symm g
    have hwg : toLinEquiv ι K w = g := MulEquiv.apply_symm_apply _ _
    have hwStated : w ∈ StatedOmega ⇑Φ := by
      rw [statedOmega_eq_comap (Q := Φ) (Q₀ := ⇑Φ) rfl, Subgroup.mem_comap]
      change toLinEquiv ι K w ∈ orthDerived Φ
      rwa [hwg]
    refine ⟨⟨w, hwStated⟩, ?_, ?_⟩
    · rw [glBlockCentralizer, Subgroup.mem_comap, Subgroup.mem_inf]
      constructor
      · rw [Subgroup.mem_centralizer_singleton_iff]
        apply (toLinEquiv ι K).injective
        rw [map_mul, map_mul]
        change toLinEquiv ι K w * toLinEquiv ι K b =
          toLinEquiv ι K b * toLinEquiv ι K w
        rw [hwg]
        apply LinearEquiv.ext
        intro v
        rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
        exact hcommv v
      · rw [ggOmegaBlk_mem_glFixing_iff]
        intro z
        have hzmem : Matrix.toLin' (1 - ε) z ∈ LinearMap.range (Matrix.toLin' (1 - ε)) :=
          ⟨z, rfl⟩
        have hgz : g (Matrix.toLin' (1 - ε) z) = Matrix.toLin' (1 - ε) z :=
          hfixx _ (by rwa [ggJSo2b_range_one_sub Φ hx ha hne htoLinε] at hzmem)
        change Matrix.toLin' w (Matrix.toLin' (1 - ε) z) = Matrix.toLin' (1 - ε) z
        rw [← ggOmegaBlk_toLinEquiv_toLinearMap w, hwg]
        exact hgz
    · exact hwg

@[expose] noncomputable def glBlockCentralizerEquivSupportedBlock_linear
    {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Fintype K] [CharP K 2]
    (Φ : QuadraticForm K (ι → K)) (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (h8 : 8 ≤ Fintype.card ι) (b : GL ι K)
    {ε e e' : Matrix ι ι K} {a : K[X]}
    (hx : OddOrderIsometry Φ (orderOf b) (toLinEquiv ι K b))
    (hp2 : Odd (orderOf b))
    (ha : a ∈ primaryFactors (toLinEquiv ι K b).toLinearMap)
    (hae : Matrix.toLinAlgEquiv' e = primaryProjection (toLinEquiv ι K b).toLinearMap a)
    (ha'e : Matrix.toLinAlgEquiv' e' =
      primaryProjection (toLinEquiv ι K b).toLinearMap (reciprocalPolynomial a))
    (hne : a ≠ reciprocalPolynomial a)
    (hεe : ε = e + e') :
    ↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε) ≃*
      ↥(supportedBlock Φ (toLinEquiv ι K b) a) :=
  (Subgroup.equivMapOfInjective _
    ((toLinEquiv ι K).toMonoidHom.comp (StatedOmega ⇑Φ).subtype)
    (fun x y hxy => Subtype.ext ((toLinEquiv ι K).injective hxy))).trans
    (MulEquiv.subgroupCongr
      (map_glBlockCentralizer_eq_supportedBlock_linear Φ hΦ h8 b hx hp2 ha hae ha'e hne hεe))

@[simp] theorem glBlockCentralizerEquivSupportedBlock_linear_apply
    {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Fintype K] [CharP K 2]
    (Φ : QuadraticForm K (ι → K)) (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (h8 : 8 ≤ Fintype.card ι) (b : GL ι K)
    {ε e e' : Matrix ι ι K} {a : K[X]}
    (hx : OddOrderIsometry Φ (orderOf b) (toLinEquiv ι K b))
    (hp2 : Odd (orderOf b))
    (ha : a ∈ primaryFactors (toLinEquiv ι K b).toLinearMap)
    (hae : Matrix.toLinAlgEquiv' e = primaryProjection (toLinEquiv ι K b).toLinearMap a)
    (ha'e : Matrix.toLinAlgEquiv' e' =
      primaryProjection (toLinEquiv ι K b).toLinearMap (reciprocalPolynomial a))
    (hne : a ≠ reciprocalPolynomial a)
    (hεe : ε = e + e')
    (u : ↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε)) :
    ((glBlockCentralizerEquivSupportedBlock_linear Φ hΦ h8 b hx hp2 ha hae ha'e hne hεe u :
        ↥(supportedBlock Φ (toLinEquiv ι K b) a)) : (ι → K) ≃ₗ[K] (ι → K)) =
      toLinEquiv ι K (((u : ↥(glBlockCentralizer
        (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε)) : ↥(StatedOmega ⇑Φ)) : GL ι K) := by
  rfl

theorem blockDegree_eq_natDegree_of_primaryProjection
    {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : GL ι K) (hsq : Squarefree (minpoly K (Matrix.toLin' (b : Matrix ι ι K))))
    {a : K[X]} (ha : a ∈ primaryFactors (Matrix.toLin' (b : Matrix ι ι K)))
    {e : Matrix ι ι K}
    (hae : Matrix.toLinAlgEquiv' e = primaryProjection (Matrix.toLin' (b : Matrix ι ι K)) a) :
    blockDegree (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) e = a.natDegree := by
  classical
  haveI : Fact (Irreducible a) := ⟨irreducible_of_mem_primaryFactors ha⟩
  let bm : Matrix ι ι K := (b : Matrix ι ι K)
  let A : Subalgebra K (Matrix ι ι K) :=
    Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))
  let x : Module.End K (ι → K) := Matrix.toLin' (b : Matrix ι ι K)
  let P : Module.End K (ι → K) := primaryProjection x a
  let εa : K[X] := primaryIdempotent x a
  let T : K[X] →ₗ[K] Matrix ι ι K :=
    (LinearMap.mulRight K e).comp (aeval bm).toLinearMap
  have hT : ∀ f : K[X], T f = aeval bm f * e := by
    intro f
    change (LinearMap.mulRight K e) (aeval bm f) = aeval bm f * e
    exact LinearMap.mulRight_apply K e (aeval bm f)
  have hA : A = Algebra.adjoin K ({bm} : Set (Matrix ι ι K)) := by
    change Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K))) = _
    rw [Set.image_singleton]
  have hφβ : Matrix.toLinAlgEquiv' bm = x := by
    rw [ggOmegaBlk_toLinAlgEquiv'_eq_toLin']
  have hTφ : ∀ f : K[X], Matrix.toLinAlgEquiv' (T f) = aeval x f * P := by
    intro f
    rw [hT f, map_mul, hae, ← aeval_algHom_apply, hφβ]
  have hmul_iff : ∀ f : K[X], minpoly K x ∣ f * εa ↔ a ∣ f := by
    intro f
    constructor
    · intro h
      have h1 : a ∣ f * εa := dvd_trans (mem_primaryFactors.mp ha).2.2 h
      have h2 : a ∣ f * (1 - εa) := by
        convert dvd_mul_of_dvd_right (dvd_neg.mpr (primaryIdempotent_spec hsq ha).1) f
          using 1
        ring
      have h3 : a ∣ f * εa + f * (1 - εa) := dvd_add h1 h2
      convert h3 using 1
      ring
    · intro h
      obtain ⟨g, rfl⟩ := h
      rw [show a * g * εa = g * (a * εa) by ring]
      exact dvd_mul_of_dvd_right (primaryIdempotent_spec hsq ha).2.2 g
  have habs : ∀ f : K[X], T f = 0 ↔ a ∣ f := by
    intro f
    constructor
    · intro hf
      have hφ : aeval x f * P = 0 := by
        have h := hTφ f
        rw [hf, map_zero] at h
        exact h.symm
      have hmem : aeval x (f * εa) = 0 := by
        rw [aeval_mul]
        change aeval x f * primaryProjection x a = 0
        exact hφ
      exact (hmul_iff f).1 (minpoly.dvd K x hmem)
    · intro hf
      obtain ⟨g, rfl⟩ := hf
      have hdvd : minpoly K x ∣ (a * g) * εa := by
        rw [show (a * g) * εa = g * (a * εa) by ring]
        exact dvd_mul_of_dvd_right (primaryIdempotent_spec hsq ha).2.2 g
      have hzero : aeval x ((a * g) * εa) = 0 := by
        obtain ⟨q, hq⟩ := hdvd
        rw [hq, map_mul, minpoly.aeval, zero_mul]
      have hφ : aeval x (a * g) * P = 0 := by
        rw [show P = aeval x εa from rfl, ← aeval_mul]
        exact hzero
      apply Matrix.toLinAlgEquiv'.injective
      rw [hTφ (a * g), hφ, map_zero]
  have hker : LinearMap.ker T = (Ideal.span {a}).restrictScalars K := by
    ext f
    rw [LinearMap.mem_ker]
    change T f = 0 ↔ f ∈ Ideal.span {a}
    rw [Ideal.mem_span_singleton]
    exact habs f
  have hrange : LinearMap.range T =
      (Subalgebra.toSubmodule A).map (LinearMap.mulRight K e) := by
    ext y
    constructor
    · rintro ⟨f, rfl⟩
      refine ⟨aeval bm f, ?_, ?_⟩
      · rw [hA]
        change aeval bm f ∈ Algebra.adjoin K ({bm} : Set (Matrix ι ι K))
        rw [Algebra.adjoin_singleton_eq_range_aeval]
        exact ⟨f, rfl⟩
      · rw [hT f]
        exact LinearMap.mulRight_apply K e (aeval bm f)
    · rintro ⟨z, hz, rfl⟩
      rw [hA, Algebra.adjoin_singleton_eq_range_aeval] at hz
      obtain ⟨f, rfl⟩ := hz
      refine ⟨f, ?_⟩
      rw [hT f]
      exact (LinearMap.mulRight_apply K e (aeval bm f)).symm
  have hdeg : blockDegree A e = a.natDegree := by
    show Module.finrank K ((Subalgebra.toSubmodule A).map (LinearMap.mulRight K e)) =
      a.natDegree
    rw [← hrange, ← (LinearMap.quotKerEquivRange T).finrank_eq, hker]
    show Module.finrank K (AdjoinRoot a) = a.natDegree
    exact finrank_adjoinRoot
  exact hdeg

theorem blockGroup_iso_Omega_linear {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι)
    (b : GL ι K) (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b))
    {ε : Matrix ι ι K}
    (hε : IsPrimAdjIdemIn (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε)
    {e e' : Matrix ι ι K}
    (he : IsPrimIdemIn (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) e)
    (he' : IsPrimIdemIn (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) e')
    (hne : e ≠ e') (hεe : ε = e + e') :
    ∃ (d m : ℕ) (E : Type) (_ : Field E) (_ : Fintype E), 1 ≤ d ∧
      Fintype.card E = Fintype.card K ^ d ∧
      2 * d * m = Module.finrank K (LinearMap.range (Matrix.toLin' ε)) ∧
      blockDegree (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) e = d ∧
      Nonempty (↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype {b} ε) ≃* GL (Fin m) E) := by
  classical
  let xE : (ι → K) ≃ₗ[K] (ι → K) := toLinEquiv ι K b
  have horder : orderOf xE = orderOf b := MulEquiv.orderOf_eq (toLinEquiv ι K) b
  have hx : OddOrderIsometry Φ (orderOf b) xE := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · have hmem : xE ∈ orthDerived Φ := by
        have h := hb
        rw [statedOmega_eq_comap (Q := Φ) (Q₀ := ⇑Φ) rfl, Subgroup.mem_comap] at h
        exact h
      exact CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup
        (Q := Φ) hmem
    · show xE ^ orderOf b = 1
      rw [← horder]
      exact pow_orderOf_eq_one xE
    · intro h0
      have h2 : 2 ∣ orderOf b := (CharP.cast_eq_zero_iff K 2 (orderOf b)).mp h0
      exact hodd.not_two_dvd_nat h2
    · intro v hv
      exact hΦ.1 v hv
  have hsq_mat : Squarefree (minpoly K (Matrix.toLin' (b : Matrix ι ι K))) := by
    rw [← ggOmegaBlk_toLinEquiv_toLinearMap b]
    exact hx.squarefree_minpoly
  obtain ⟨a, ha_mat, hae_mat⟩ := ggOmegaBlk_prim_idem_eq_primaryProjection b hsq_mat he
  obtain ⟨a', ha'_mat, ha'e_mat⟩ := ggOmegaBlk_prim_idem_eq_primaryProjection b hsq_mat he'
  have ha : a ∈ primaryFactors xE.toLinearMap := by
    rw [← ggOmegaBlk_toLinEquiv_toLinearMap b] at ha_mat
    exact ha_mat
  have ha' : a' ∈ primaryFactors xE.toLinearMap := by
    rw [← ggOmegaBlk_toLinEquiv_toLinearMap b] at ha'_mat
    exact ha'_mat
  have hae : Matrix.toLinAlgEquiv' e = primaryProjection xE.toLinearMap a := by
    rw [← ggOmegaBlk_toLinEquiv_toLinearMap b] at hae_mat
    exact hae_mat
  have ha'e : Matrix.toLinAlgEquiv' e' = primaryProjection xE.toLinearMap a' := by
    rw [← ggOmegaBlk_toLinEquiv_toLinearMap b] at ha'e_mat
    exact ha'e_mat
  obtain ⟨hrec, hane⟩ := paired_prim_idem_primary_reciprocal Φ hΦ b hx ha ha' hae ha'e hεe hne
    hε he he'
  have ha'e' : Matrix.toLinAlgEquiv' e' =
      primaryProjection xE.toLinearMap (reciprocalPolynomial a) := by
    rw [hrec] at ha'e
    exact ha'e
  have htoLinε : Matrix.toLinAlgEquiv' ε =
      primaryProjection xE.toLinearMap a +
        primaryProjection xE.toLinearMap (reciprocalPolynomial a) := by
    rw [hεe, map_add, hae, ha'e']
  let d : ℕ := a.natDegree
  let E : Type := AdjoinRoot a
  haveI : Fact (Irreducible a) := ⟨irreducible_of_mem_primaryFactors ha⟩
  haveI : Finite E := Module.finite_of_finite K
  haveI : Fintype E := Fintype.ofFinite E
  let m : ℕ := primaryMultiplicity xE.toLinearMap a
  have hcard : Fintype.card E = Fintype.card K ^ d := by
    rw [Fintype.card_eq_nat_card, Module.natCard_eq_pow_finrank (K := K),
      CFSG.RankThree.PartOne.KCUnitary.finrank_adjoinRoot, Nat.card_eq_fintype_card]
  have hd : 1 ≤ d := by
    show 1 ≤ a.natDegree
    have hpos : 0 < a.natDegree := Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors ha)
    omega
  have hfa : Module.finrank K (primaryComponent xE.toLinearMap a) = d * m := by
    rw [finrank_primaryComponent]
  have hfr : Module.finrank K (primaryComponent xE.toLinearMap (reciprocalPolynomial a)) =
      d * m := by
    rw [(ggJSo2b_finrank_reciprocal hx ha).symm, hfa]
  have hinf : primaryComponent xE.toLinearMap a ⊓
      primaryComponent xE.toLinearMap (reciprocalPolynomial a) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    obtain ⟨hv1, hv2⟩ := Submodule.mem_inf.mp hv
    rw [← primaryProjection_of_mem hx.squarefree_minpoly ha hv1,
      primaryProjection_of_mem_ne hx.squarefree_minpoly ha
        (hx.reciprocalPolynomial_mem ha) (Ne.symm hane) hv2]
  have hfin : Module.finrank K (LinearMap.range (Matrix.toLin' ε)) =
      Module.finrank K (primaryComponent xE.toLinearMap a) +
      Module.finrank K (primaryComponent xE.toLinearMap (reciprocalPolynomial a)) := by
    rw [ggJSo2b_range Φ hx ha hane htoLinε, orbitSpace,
      ← Submodule.finrank_sup_add_finrank_inf_eq, hinf, finrank_bot, add_zero]
  have hdim : 2 * d * m = Module.finrank K (LinearMap.range (Matrix.toLin' ε)) := by
    rw [hfin, hfa, hfr]
    ring
  have hblockdeg : blockDegree (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) e = d := by
    show blockDegree (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) e = a.natDegree
    exact blockDegree_eq_natDegree_of_primaryProjection b hsq_mat ha_mat hae_mat
  refine ⟨d, m, E, inferInstance, inferInstance, hd, hcard, hdim, hblockdeg, ?_⟩
  let eMap : ↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε) ≃*
      ↥(supportedBlock Φ xE a) :=
    glBlockCentralizerEquivSupportedBlock_linear Φ hΦ h8 b hx hodd ha hae ha'e' hane hεe
  let eG : ↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε) ≃*
      GL (Fin m) E :=
    (eMap.trans (pairedBlockEquiv hx ha hane)).trans
      (Units.mapEquiv (LinearMap.toMatrixAlgEquiv
        (Module.finBasis E (primaryComponent xE.toLinearMap a))).toMulEquiv)
  exact ⟨eG⟩

noncomputable def glBlockCentralizerAmbient
    {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Fintype K] [CharP K 2]
    (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (b : GL ι K) (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b))
    {ε : Matrix ι ι K}
    (hε : IsPrimAdjIdemIn (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε)
    (h1 : (b : Matrix ι ι K) * ε = ε)
    (hD : CFSG.RankThree.PartOne.DicksonDerived
      (Φ.comp (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b)).subtype)
      (ggJSo2_oddOrderIsometry Φ hΦ b hb hodd).polarBilin_fixed_nondegenerate)
    (u : ↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε)) :
    CFSG.RankThree.Classical2.orthDerived Φ :=
  ⟨ggJSo2_ML (((u : ↥(glBlockCentralizer
      (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε)) : ↥(StatedOmega ⇑Φ)) : GL ι K),
    by
      rw [← glBlockCentralizerEquivSupportedFixedDerived_apply Φ hΦ b hb hodd hε h1 hD u]
      exact (ggJSo2_oddOrderIsometry Φ hΦ b hb hodd).supportedFixedDerived_le_orthDerived
        (SetLike.coe_mem _)⟩

@[expose] noncomputable def glBlockCentralizerEquivFixedComponentImage
    {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Fintype K] [CharP K 2]
    (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (b : GL ι K) (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b))
    {ε : Matrix ι ι K}
    (hε : IsPrimAdjIdemIn (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε)
    (h1 : (b : Matrix ι ι K) * ε = ε)
    (hD : CFSG.RankThree.PartOne.DicksonDerived
      (Φ.comp (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b)).subtype)
      (ggJSo2_oddOrderIsometry Φ hΦ b hb hodd).polarBilin_fixed_nondegenerate) :
    ↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε) ≃*
      ↥(fixedComponentImage Φ (ggJSo2_ML b)) := by
  haveI : Nonempty ι := by
    by_contra h
    haveI : IsEmpty ι := not_nonempty_iff.mp h
    exact hε.2.2.1 (Subsingleton.elim _ _)
  haveI : Inhabited ι := Classical.inhabited_of_nonempty ‹Nonempty ι›
  haveI : Nontrivial (ι → K) := Pi.nontrivial
  exact (glBlockCentralizerEquivSupportedFixedDerived Φ hΦ b hb hodd hε h1 hD).trans
    (CFSG.HardMathSupport.Dickson.Bal207.OrthFix.fixRho (Q := Φ) (x := ggJSo2_ML b)
      (p := orderOf b) hΦ (ggJSo2_oddOrderIsometry Φ hΦ b hb hodd))

@[simp] theorem glBlockCentralizerEquivFixedComponentImage_apply_coe
    {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Fintype K] [CharP K 2]
    (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (b : GL ι K) (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b))
    {ε : Matrix ι ι K}
    (hε : IsPrimAdjIdemIn (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε)
    (h1 : (b : Matrix ι ι K) * ε = ε)
    (hD : CFSG.RankThree.PartOne.DicksonDerived
      (Φ.comp (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b)).subtype)
      (ggJSo2_oddOrderIsometry Φ hΦ b hb hodd).polarBilin_fixed_nondegenerate)
    (u : ↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι K)) ε)) :
    ((glBlockCentralizerEquivFixedComponentImage Φ hΦ b hb hodd hε h1 hD u :
        ↥(fixedComponentImage Φ (ggJSo2_ML b))) : ProjOrthDerived Φ) =
      CFSG.RankThree.PartOne.piOrth Φ
        (glBlockCentralizerAmbient Φ hΦ b hb hodd hε h1 hD u) := by
  haveI : Nonempty ι := by
    by_contra h
    haveI : IsEmpty ι := not_nonempty_iff.mp h
    exact hε.2.2.1 (Subsingleton.elim _ _)
  haveI : Inhabited ι := Classical.inhabited_of_nonempty ‹Nonempty ι›
  haveI : Nontrivial (ι → K) := Pi.nontrivial
  change ((CFSG.HardMathSupport.Dickson.Bal207.OrthFix.fixRho (Q := Φ) (x := ggJSo2_ML b)
      (p := orderOf b) hΦ (ggJSo2_oddOrderIsometry Φ hΦ b hb hodd)
      (glBlockCentralizerEquivSupportedFixedDerived Φ hΦ b hb hodd hε h1 hD u) :
      ProjOrthDerived Φ)) =
    CFSG.RankThree.PartOne.piOrth Φ
      (glBlockCentralizerAmbient Φ hΦ b hb hodd hε h1 hD u)
  rw [CFSG.HardMathSupport.Dickson.Bal207.OrthFix.coe_fixRho]
  exact congrArg (CFSG.RankThree.PartOne.piOrth Φ) (Subtype.ext rfl)

end CFSG.StandardType.ClassicalBlocks
namespace CFSG.RankThree.PartOne

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.RankThree.PartOne.KCOrthogonal

theorem actsBySemilinear_kappa {K : Type} [Field K] {d : ℕ}
    (Q : QuadraticForm K (Fin d → K)) (g : similarityPairs Q) :
    ActsBySemilinear Q (coordinateSemilinearMap g.val) (KCOrthComm.kappa Q g) := by
  intro ω
  obtain ⟨A, rfl⟩ := (KCOrthComm.matrixDerivedEquiv Q).surjective ω
  refine ⟨KCOrthComm.matrixDerivedEquiv Q (matrixDerivedConjugation Q g A), ?_, ?_⟩
  · intro v
    rw [KCOrthComm.coe_matrixDerivedEquiv, KCOrthComm.coe_matrixDerivedEquiv]
    change matrixLinearEquiv (matrixConjugation g.val A.val) v =
      coordinateSemilinearMap g.val
        (matrixLinearEquiv A.val ((coordinateSemilinearMap g.val).symm v))
    rw [matrixConjugation_vector]
  · change KCOrthComm.kappa Q g
        (QuotientGroup.mk ((KCOrthComm.matrixDerivedEquiv Q) A)) =
      QuotientGroup.mk ((KCOrthComm.matrixDerivedEquiv Q)
        (matrixDerivedConjugation Q g A))
    rw [KCOrthComm.kappa_mk]

end CFSG.RankThree.PartOne

