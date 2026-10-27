module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK329Data
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ZUniData
public import CFSG.RankThree.SubgroupLists.UnitaryThreeFamily
import CFSG.Adapters.StatedClassicalUnitaryOrders

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Blueprint (LieModel)
open CFSG.Open CFSG.LocalAnalysis.GLTheoremA.S267Z.Uni
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg
open CFSG.LocalAnalysis.GLTheoremA.S267Z.SL3 (blk mem_blk)
open CFSG.RankThree.SubgroupLists
open Matrix
open scoped Matrix commutatorElement

private lemma k329lz_lieModel_congr {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (z : X)
    (h : LieModel ↥⁅Subgroup.centralizer ({e z} : Set Y), Subgroup.centralizer ({e z} : Set Y)⁆
      .PSL 2 2 3) :
    LieModel ↥⁅Subgroup.centralizer ({z} : Set X), Subgroup.centralizer ({z} : Set X)⁆
      .PSL 2 2 3 := by
  have hC : Subgroup.centralizer ({e z} : Set Y) =
      (Subgroup.centralizer ({z} : Set X)).map e.toMonoidHom := by
    apply le_antisymm
    · intro y hy
      refine Subgroup.mem_map.mpr ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
      apply e.injective
      rw [map_mul, map_mul, e.apply_symm_apply]
      exact hy
    · simpa using Subgroup.map_centralizer_le_centralizer_image ({z} : Set X) e.toMonoidHom
  have hder : ⁅Subgroup.centralizer ({e z} : Set Y), Subgroup.centralizer ({e z} : Set Y)⁆ =
      (⁅Subgroup.centralizer ({z} : Set X),
        Subgroup.centralizer ({z} : Set X)⁆).map e.toMonoidHom := by
    rw [hC, Subgroup.map_commutator]
  let iso0 : ↥⁅Subgroup.centralizer ({z} : Set X), Subgroup.centralizer ({z} : Set X)⁆ ≃*
      ↥((⁅Subgroup.centralizer ({z} : Set X),
        Subgroup.centralizer ({z} : Set X)⁆).map e.toMonoidHom) :=
    Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective
  exact LieModel.of_mulEquiv (iso0.trans (MulEquiv.subgroupCongr hder.symm)).symm h

private lemma k329lz_hlamn {K : Type} [Field K] [Finite K] (h : UnitaryFieldData 2 3 K)
    (a : Kˣ) (ha : orderOf a = 9) : h.bar (a : K) * (a : K) = 1 := by
  rw [UnitaryFieldData.bar_apply]; norm_num
  rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, ← pow_succ,
    show (8:ℕ)+1 = 9 by norm_num, show a ^ 9 = 1 by rw [← ha, pow_orderOf_eq_one], Units.val_one]

private lemma k329lz_tOne_order {K : Type} [Field K] [Finite K] (h : UnitaryFieldData 2 3 K)
    (a : Kˣ) (ha : orderOf a = 9) : orderOf (projU h (tOne h (k329lz_hlamn h a ha))) = 3 := by
  have hchar : CharP K 2 := h.charP
  have hlamn := k329lz_hlamn h a ha
  have ha9 : (a : K) ^ 9 = 1 := by
    rw [← Units.val_pow_eq_pow_val, show a ^ 9 = 1 by rw [← ha, pow_orderOf_eq_one], Units.val_one]
  have hlam3 : (a : K) ^ 3 ≠ 1 := by
    intro h3
    have h3u : a ^ 3 = 1 := by
      apply Units.ext; rw [Units.val_pow_eq_pow_val, Units.val_one]; exact h3
    have hdvd : orderOf a ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr h3u
    rw [ha] at hdvd; norm_num at hdvd
  apply orderOf_eq_prime
  · have hp := projU_tOne_pow (h := h) (p := 3) (lam := (a : K)) (hlamn := hlamn)
      (by rw [show (3*3:ℕ) = 9 by norm_num]; exact ha9)
    simpa using hp
  · exact projU_tOne_ne_one (h := h) (lam := (a : K)) (hlamn := hlamn) hlam3

private lemma k329lz_tOne_commutator {K : Type} [Field K] [Finite K] (h : UnitaryFieldData 2 3 K)
    (a : Kˣ) (ha : orderOf a = 9) :
    ⁅Subgroup.centralizer ({tOne h (k329lz_hlamn h a ha)} : Set ↥(SG h)),
      Subgroup.centralizer ({tOne h (k329lz_hlamn h a ha)} : Set ↥(SG h))⁆ = blockU h blk := by
  have hchar : CharP K 2 := h.charP
  have hlamn := k329lz_hlamn h a ha
  have hlam0 : (a : K) ≠ 0 := Units.ne_zero a
  have hlam3 : (a : K) ^ 3 ≠ 1 := by
    intro h3
    have h3u : a ^ 3 = 1 := by
      apply Units.ext; rw [Units.val_pow_eq_pow_val, Units.val_one]; exact h3
    have hdvd : orderOf a ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr h3u
    rw [ha] at hdvd; norm_num at hdvd
  have hd0 : ∀ j, j ≠ 0 → dOne (a : K) 0 ≠ dOne (a : K) j := by
    intro j hj
    fin_cases j
    · exact absurd rfl hj
    · exact dOne_zero_ne_one hlam0 hlam3
    · show dOne (a : K) 0 ≠ dOne (a : K) 2
      rw [← dOne_one_eq_two]
      exact dOne_zero_ne_one hlam0 hlam3
  have hzhat : tOne h hlamn = diagU h (dOne (a : K)) (norm_dOne hlamn) (prod_dOne hlam0) := rfl
  apply le_antisymm
  · rw [hzhat]
    exact commutator_centralizer_le_blockU (d := dOne (a:K)) (hn := norm_dOne hlamn)
      (hd := prod_dOne hlam0) hd0
  · have hK8 : Nat.card K = (2^3)^2 := by rw [h.card]; norm_num
    have hq5 : 5 ≤ 2^3 := by norm_num
    have hblk2 : 2 ≤ blk.card := by decide
    have hcommblock : ⁅blockU h blk, blockU h blk⁆ = blockU h blk := by
      have hperf :=
        (isQuasisimple_blockU (h := h) (ℓ := 2) (f := 3) hK8 hq5 (I := blk) hblk2).1
      exact Subgroup.isPerfect_iff.mp (Group.isPerfect_def.2 hperf)
    calc blockU h blk = ⁅blockU h blk, blockU h blk⁆ := hcommblock.symm
      _ ≤ ⁅Subgroup.centralizer ({tOne h hlamn} : Set ↥(SG h)),
            Subgroup.centralizer ({tOne h hlamn} : Set ↥(SG h))⁆ :=
          Subgroup.commutator_mono (by rw [hzhat]; exact blockU_le_centralizer_tOne hlamn)
            (by rw [hzhat]; exact blockU_le_centralizer_tOne hlamn)

private lemma k329lz_blockU_map_lie {K : Type} [Field K] [Finite K] (h : UnitaryFieldData 2 3 K) :
    LieModel ↥((blockU h blk).map (projU h)) .PSL 2 2 3 := by
  have hchar : CharP K 2 := h.charP
  have hK : Nat.card K = (2^3)^2 := by rw [h.card]; norm_num
  have hF8 : Nat.card (fixedSubfield K 2 3) = 2^3 := card_fixedSubfield hK
  let e1 : ↥((blockU h blk).map (projU h)) ≃* ↥(blockU h blk) :=
    (mapProjUEquiv zero_not_mem_blk (blockU h blk) le_rfl).symm
  let e2 : ↥(blockU h blk) ≃* StatedSU 2 8 K :=
    (MulEquiv.subgroupCongr (blockU_eq_map (h := h) blk)).trans
      ((Subgroup.equivMapOfInjective (coordBlockSU K 2 3 blk) (suEquiv h).toMonoidHom
          (suEquiv h).injective).symm.trans
        ((MonoidHom.ofInjective (f := blockSUOn K 2 3 blk)
            (blockSUOn_injective (K := K) (p := 2) (f := 3) blk)).symm.trans
          (MulEquiv.subgroupCongr (SUid_eq_statedSU hK 2))))
  let e3 : StatedSU 2 8 K ≃* StatedProj (StatedSL 2 (fixedSubfield K 2 3)) :=
    ((nonempty_sl2_mulEquiv_statedSU_two (r := 2) (f := 3) (K := K) hK).some.symm.trans
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 (fixedSubfield K 2 3))).trans
      ((QuotientGroup.quotientMulEquivOfEq
          (CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSL_two_eq_bot
            (K := fixedSubfield K 2 3))).trans
        QuotientGroup.quotientBot).symm
  have hmodel : StatedClassicalModel ↥((blockU h blk).map (projU h)) .PSL 2 2 3 :=
    ⟨⟨Nat.prime_two, by norm_num, by norm_num, by decide, by decide⟩,
      fixedSubfield K 2 3, inferInstance, inferInstance, by rw [hF8], ⟨(e1.trans e2).trans e3⟩⟩
  exact Or.inl ⟨by decide, hmodel⟩

private theorem k329lz_PU_main {K : Type} [Field K] [Finite K]
    (h : UnitaryFieldData 2 3 K) (a : Kˣ) (ha : orderOf a = 9) :
    ∃ z : PU h, orderOf z = 3 ∧
      LieModel ↥⁅Subgroup.centralizer ({z} : Set (PU h)), Subgroup.centralizer ({z} : Set (PU h))⁆
        .PSL 2 2 3 := by
  have hlamn := k329lz_hlamn h a ha
  have hlam0 : (a : K) ≠ 0 := Units.ne_zero a
  refine ⟨projU h (tOne h hlamn), k329lz_tOne_order h a ha, ?_⟩
  have hC : Subgroup.centralizer ({projU h (tOne h hlamn)} : Set (PU h)) =
      (Subgroup.centralizer ({tOne h hlamn} : Set ↥(SG h))).map (projU h) := by
    have hzhat : tOne h hlamn = diagU h (dOne (a : K)) (norm_dOne hlamn) (prod_dOne hlam0) := rfl
    rw [hzhat]
    exact centralizer_projU_diagU (h := h) (d := dOne (a:K)) (hn := norm_dOne hlamn)
      (hd := prod_dOne hlam0) (dOne_one_eq_two (a:K))
  have hder : ⁅Subgroup.centralizer ({projU h (tOne h hlamn)} : Set (PU h)),
      Subgroup.centralizer ({projU h (tOne h hlamn)} : Set (PU h))⁆ =
      (blockU h blk).map (projU h) := by
    rw [hC, ← Subgroup.map_commutator, k329lz_tOne_commutator h a ha]
  rw [hder]
  exact k329lz_blockU_map_lie h

private lemma k329lu_bar_mul {K : Type} [Field K] (h : UnitaryFieldData 2 3 K) {x : K}
    (hx : x ^ 9 = 1) : h.bar x * x = 1 := by
  rw [UnitaryFieldData.bar_apply, ← pow_succ]
  exact hx

private lemma k329lu_unit_pow {K : Type} [Field K] {x : Kˣ} (hx : x ^ 9 = 1) : (x : K) ^ 9 = 1 := by
  rw [← Units.val_pow_eq_pow_val, hx, Units.val_one]

private lemma k329lu_norm_diag {K : Type} [Field K] (h : UnitaryFieldData 2 3 K) {x y z : Kˣ}
    (hx : x ^ 9 = 1) (hy : y ^ 9 = 1) (hz : z ^ 9 = 1) :
    ∀ i, h.bar ((![(x : K), (y : K), (z : K)] : Fin 3 → K) i) *
      (![(x : K), (y : K), (z : K)] : Fin 3 → K) i = 1 := by
  intro i
  fin_cases i
  · exact k329lu_bar_mul h (k329lu_unit_pow hx)
  · exact k329lu_bar_mul h (k329lu_unit_pow hy)
  · exact k329lu_bar_mul h (k329lu_unit_pow hz)

private noncomputable def k329lu_dg {K : Type} [Field K] (h : UnitaryFieldData 2 3 K) (x y : Kˣ)
    (hx : x ^ 9 = 1) (hy : y ^ 9 = 1) : ↥(SG h) :=
  diagU h ![(x : K), (y : K), (((x * y)⁻¹ : Kˣ) : K)]
    (k329lu_norm_diag h hx hy (by rw [inv_pow, mul_pow, hx, hy, one_mul, inv_one]))
    (by
      rw [Fin.prod_univ_three]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons]
      rw [← Units.val_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one])

private lemma k329lu_coe_dg {K : Type} [Field K] (h : UnitaryFieldData 2 3 K) {x y : Kˣ}
    (hx : x ^ 9 = 1) (hy : y ^ 9 = 1) :
    (((k329lu_dg h x y hx hy : ↥(SG h)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal ![(x : K), (y : K), (((x * y)⁻¹ : Kˣ) : K)] :=
  rfl

private lemma k329lu_dg_comm {K : Type} [Field K] (h : UnitaryFieldData 2 3 K) {x y x' y' : Kˣ}
    (hx : x ^ 9 = 1) (hy : y ^ 9 = 1) (hx' : x' ^ 9 = 1) (hy' : y' ^ 9 = 1) :
    k329lu_dg h x y hx hy * k329lu_dg h x' y' hx' hy' =
      k329lu_dg h x' y' hx' hy' * k329lu_dg h x y hx hy :=
  diagU_mul_comm

private lemma k329lu_dg_injective {K : Type} [Field K] (h : UnitaryFieldData 2 3 K) {x y x' y' : Kˣ}
    (hx : x ^ 9 = 1) (hy : y ^ 9 = 1) (hx' : x' ^ 9 = 1) (hy' : y' ^ 9 = 1)
    (he : k329lu_dg h x y hx hy = k329lu_dg h x' y' hx' hy') : x = x' ∧ y = y' := by
  have h' := congrArg (fun g : ↥(SG h) => ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) he
  simp only [k329lu_coe_dg] at h'
  have h0 := congrFun (congrFun h' 0) 0
  have h1 := congrFun (congrFun h' 1) 1
  simp only [diagonal_apply_eq, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  exact ⟨Units.ext h0, Units.ext h1⟩

private lemma k329lu_ker_central {K : Type} [Field K] (h : UnitaryFieldData 2 3 K)
    {k : ↥(SG h)} (hk : projU h k = 1) : k ∈ Subgroup.center ↥(SG h) ∧ k ^ 3 = 1 := by
  have hk' : k ∈ normOneScalars h (SG h) 3 := (ker_projU (h := h)).le (MonoidHom.mem_ker.2 hk)
  refine ⟨normOneScalars_le_center h _ 3 hk', ?_⟩
  obtain ⟨c, -, hc3, hc⟩ := mem_normOneScalars.1 hk'
  apply Subtype.ext
  rw [Subgroup.coe_pow, hc, ← map_pow, hc3, map_one]
  rfl

private lemma k329lu_ker_card_le {K : Type} [Field K] (h : UnitaryFieldData 2 3 K) :
    Nat.card (projU h).ker ≤ 3 := by
  have hex : ∀ k : (projU h).ker, ∃ c : rootsOfUnity 3 K,
      ((k : ↥(SG h)) : GL (Fin 3) K) = Matrix.GeneralLinearGroup.scalar (Fin 3) (c : Kˣ) := by
    intro k
    have hk' : (k : ↥(SG h)) ∈ normOneScalars h (SG h) 3 := (ker_projU (h := h)).le k.2
    obtain ⟨c, -, hc3, hc⟩ := mem_normOneScalars.1 hk'
    exact ⟨⟨c, (mem_rootsOfUnity 3 c).2 hc3⟩, hc⟩
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro k k' hkk'
    apply Subtype.ext
    apply Subtype.ext
    rw [hf k, hf k', hkk']
  exact (Nat.card_le_card_of_injective f hinj).trans (card_rootsOfUnity K 3)

private lemma k329lu_cube_comm {K : Type} [Field K] (h : UnitaryFieldData 2 3 K)
    {g u : ↥(SG h)} (hg : projU h g * projU h u = projU h u * projU h g) :
    u * g ^ 3 = g ^ 3 * u := by
  have hk : projU h ⁅g, u⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hg
  obtain ⟨hcen, hk3⟩ := k329lu_ker_central h hk
  have hcomm : Commute g ⁅g, u⁆ := Subgroup.mem_center_iff.1 hcen g
  have h1 := hcomm.commutatorElement_pow_left 3
  rw [hk3] at h1
  exact (commutatorElement_eq_one_iff_mul_comm.1 h1.symm).symm

private lemma k329lu_pow_nine_of_bar {K : Type} [Field K] (h : UnitaryFieldData 2 3 K) {x : K}
    (hx : h.bar x * x = 1) : x ^ 9 = 1 := by
  rw [UnitaryFieldData.bar_apply, ← pow_succ] at hx
  exact hx

private lemma k329lu_norm_eq {K : Type} [Field K] (h : UnitaryFieldData 2 3 K) {x : Kˣ}
    (hx : x ^ 9 = 1) : h.norm (x : K) = 1 := by
  rw [UnitaryFieldData.norm, mul_comm]
  exact k329lu_bar_mul h (k329lu_unit_pow hx)

private lemma k329lu_inv_eq {K : Type} [Field K] {ω : Kˣ} (hω3 : ω ^ 3 = 1) :
    (((1 * ω)⁻¹ : Kˣ) : K) = (ω : K) * (ω : K) := by
  rw [← Units.val_mul]
  congr 1
  rw [one_mul]
  apply inv_eq_of_mul_eq_one_right
  rw [← hω3, pow_three]

private lemma k329lu_distinct {K : Type} [Field K] {ω : Kˣ} (hω3 : ω ^ 3 = 1)
    (hω1 : (ω : K) ≠ 1) :
    ∀ i j : Fin 3, i ≠ j →
      (![((1 : Kˣ) : K), (ω : K), (((1 * ω)⁻¹ : Kˣ) : K)] : Fin 3 → K) i ≠
        (![((1 : Kˣ) : K), (ω : K), (((1 * ω)⁻¹ : Kˣ) : K)] : Fin 3 → K) j := by
  have hinv := k329lu_inv_eq hω3
  have hω3K : (ω : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hω3, Units.val_one]
  have hω0 : (ω : K) ≠ 0 := ω.ne_zero
  have hωω : (ω : K) * ω ≠ 1 := by
    intro h2
    apply hω1
    linear_combination (-(ω : K)) * h2 + hω3K
  have hne : (ω : K) ≠ (ω : K) * ω := by
    intro h2
    apply hω1
    apply mul_left_cancel₀ hω0
    linear_combination -h2
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    first
      | exact absurd rfl hij
      | (simp only [Units.val_one, hinv]
         first
           | exact Ne.symm hω1
           | exact hω1
           | exact Ne.symm hωω
           | exact hωω
           | exact hne
           | exact Ne.symm hne)

private def k329lu_sigmaMat (K : Type) [Field K] : Matrix (Fin 3) (Fin 3) K :=
  !![0, 1, 0; 0, 0, 1; 1, 0, 0]

private lemma k329lu_det_sigmaMat {K : Type} [Field K] : (k329lu_sigmaMat K).det = 1 := by
  simp [k329lu_sigmaMat, Matrix.det_fin_three]

private noncomputable def k329lu_sigma {K : Type} [Field K] (h : UnitaryFieldData 2 3 K) :
    ↥(SG h) :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (k329lu_sigmaMat K)
      (by rw [k329lu_det_sigmaMat]; exact one_ne_zero),
    mem_gramSU.2 ⟨by
      change ((k329lu_sigmaMat K).map h.bar)ᵀ * ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        k329lu_sigmaMat K = ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
      have hmap : (k329lu_sigmaMat K).map h.bar = k329lu_sigmaMat K := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [k329lu_sigmaMat]
      rw [hmap, Units.val_one, Matrix.mul_one]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [k329lu_sigmaMat, Matrix.mul_apply, Fin.sum_univ_three],
      k329lu_det_sigmaMat⟩⟩

private lemma k329lu_coe_sigma {K : Type} [Field K] (h : UnitaryFieldData 2 3 K) :
    (((k329lu_sigma h : ↥(SG h)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      k329lu_sigmaMat K :=
  rfl

private lemma k329lu_sigmaMat_mul {K : Type} [Field K] (d : Fin 3 → K) (w : K)
    (h1 : d 1 = w * d 0) (h2 : d 2 = w * d 1) (h0 : d 0 = w * d 2) :
    k329lu_sigmaMat K * diagonal d = diagonal (fun _ => w) * (diagonal d * k329lu_sigmaMat K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [k329lu_sigmaMat, Matrix.mul_apply, Matrix.diagonal_apply] <;>
    first
      | linear_combination h1
      | linear_combination h2
      | linear_combination h0

private lemma k329lu_sigma_dg {K : Type} [Field K] (h : UnitaryFieldData 2 3 K) {ω : Kˣ}
    (hω9 : ω ^ 9 = 1) (hω3 : ω ^ 3 = 1) :
    k329lu_sigma h * k329lu_dg h 1 ω (one_pow 9) hω9 =
      scalarU h ω (k329lu_norm_eq h hω9) hω3 *
        (k329lu_dg h 1 ω (one_pow 9) hω9 * k329lu_sigma h) := by
  have hinv : (ω : K)⁻¹ = (ω : K) * (ω : K) := by
    rw [← k329lu_inv_eq hω3]
    simp
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, coe_scalarU, k329lu_coe_dg, k329lu_coe_sigma]
  apply k329lu_sigmaMat_mul
  · simp
  · simp [hinv]
  · simp

private lemma k329lu_scalarU_ne_one {K : Type} [Field K] (h : UnitaryFieldData 2 3 K) {ω : Kˣ}
    (hn : h.norm (ω : K) = 1) (hω3 : ω ^ 3 = 1) (hω1 : (ω : K) ≠ 1) :
    scalarU h ω hn hω3 ≠ 1 := by
  intro h1
  have h2 := congrArg (fun g : ↥(SG h) => ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0) h1
  simp only [coe_scalarU, diagonal_apply_eq, Subgroup.coe_one, Units.val_one,
    Matrix.one_apply_eq] at h2
  exact hω1 h2

private lemma k329lu_pow_nine_of_comm {K : Type} [Field K] (h : UnitaryFieldData 2 3 K) {ω : Kˣ}
    (hω9 : ω ^ 9 = 1) (hω3 : ω ^ 3 = 1) (hω1 : (ω : K) ≠ 1) {E : ↥(SG h)}
    (hE : k329lu_dg h 1 ω (one_pow 9) hω9 * E = E * k329lu_dg h 1 ω (one_pow 9) hω9) :
    E ^ 9 = 1 := by
  have hcen : E ∈ Subgroup.centralizer ({k329lu_dg h 1 ω (one_pow 9) hω9} : Set ↥(SG h)) :=
    Subgroup.mem_centralizer_singleton_iff.2 hE.symm
  have hoff : ∀ i j : Fin 3, i ≠ j →
      ((E : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j = 0 := fun i j hij =>
    (mem_centralizer_diagU_iff.1 hcen) i j (k329lu_distinct hω3 hω1 i j hij)
  obtain ⟨e, he⟩ : ∃ e : Fin 3 → K,
      ((E : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal e :=
    ⟨fun i => ((E : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i i, by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp
      · rw [diagonal_apply_ne _ hij, hoff i j hij]⟩
  have hunit := (mem_gramSU.1 E.2).1
  rw [he, Units.val_one, Matrix.mul_one, diagonal_map (map_zero _), diagonal_transpose,
    diagonal_mul_diagonal] at hunit
  have he9 : ∀ i, e i ^ 9 = 1 := by
    intro i
    have h1 := congrFun (congrFun hunit i) i
    rw [diagonal_apply_eq, Matrix.one_apply_eq] at h1
    exact k329lu_pow_nine_of_bar h h1
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, he, diagonal_pow]
  have h9 : e ^ 9 = fun _ => 1 := funext fun i => by rw [Pi.pow_apply]; exact he9 i
  rw [h9]
  simp

private lemma k329lu_pow_27 {K : Type} [Field K] (h : UnitaryFieldData 2 3 K) {ω : Kˣ}
    (hω9 : ω ^ 9 = 1) (hω3 : ω ^ 3 = 1) (hω1 : (ω : K) ≠ 1) {x : PU h}
    (hx : x ∈ Subgroup.centralizer
      ({projU h (k329lu_dg h 1 ω (one_pow 9) hω9)} : Set (PU h))) : x ^ 27 = 1 := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ x
  have hg := Subgroup.mem_centralizer_singleton_iff.1 hx
  have h3 := k329lu_cube_comm h hg
  have h9 := k329lu_pow_nine_of_comm h hω9 hω3 hω1 h3
  change projU h g ^ 27 = 1
  rw [← map_pow, show (27 : ℕ) = 3 * 9 by norm_num, pow_mul, h9, map_one]

private lemma k329lu_isPGroup {G : Type} [Group G] (C : Subgroup G) (hC : ∀ x ∈ C, x ^ 27 = 1) :
    IsPGroup 3 C := fun x =>
  ⟨3, Subtype.ext (by rw [Subgroup.coe_pow]; exact hC x x.2)⟩

private lemma k329lu_card_eq_81 {G : Type} [Group G] [Finite G] (hG : Nat.card G = 5515776)
    {C : Subgroup G} (hp : IsPGroup 3 C) (hbig : 27 < Nat.card C) : Nat.card C = 81 := by
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 3)).1 hp
  have hdvd : 3 ^ n ∣ 5515776 := by
    rw [← hn, ← hG]
    exact Subgroup.card_subgroup_dvd_card C
  have hn4 : n ≤ 4 := by
    by_contra hlt
    push Not at hlt
    have h5 : 3 ^ 5 ∣ 5515776 := (pow_dvd_pow 3 hlt).trans hdvd
    norm_num at h5
  have hn4' : 4 ≤ n := by
    by_contra hlt
    push Not at hlt
    have h3 : 3 ^ n ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rw [hn, show n = 4 by omega]
  norm_num

private lemma k329lu_sigma_mem {K : Type} [Field K] (h : UnitaryFieldData 2 3 K) {ω : Kˣ}
    (hω9 : ω ^ 9 = 1) (hω3 : ω ^ 3 = 1) :
    projU h (k329lu_sigma h) ∈ Subgroup.centralizer
      ({projU h (k329lu_dg h 1 ω (one_pow 9) hω9)} : Set (PU h)) := by
  rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, k329lu_sigma_dg h hω9 hω3,
    map_mul, projU_scalarU, one_mul]

private lemma k329lu_dg_mem {K : Type} [Field K] (h : UnitaryFieldData 2 3 K) {ω x y : Kˣ}
    (hω9 : ω ^ 9 = 1) (hx : x ^ 9 = 1) (hy : y ^ 9 = 1) :
    projU h (k329lu_dg h x y hx hy) ∈ Subgroup.centralizer
      ({projU h (k329lu_dg h 1 ω (one_pow 9) hω9)} : Set (PU h)) := by
  rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
    k329lu_dg_comm h hx hy (one_pow 9) hω9]

private lemma k329lu_card_cent_ge {K : Type} [Field K] [Finite K] (h : UnitaryFieldData 2 3 K)
    {a : Kˣ} (ha : orderOf a = 9) {ω : Kˣ} (hω9 : ω ^ 9 = 1) :
    81 ≤ Nat.card (Subgroup.centralizer
      ({k329lu_dg h 1 ω (one_pow 9) hω9} : Set ↥(SG h))) := by
  have ha9 : a ^ 9 = 1 := by rw [← ha, pow_orderOf_eq_one]
  have hpow : ∀ n : ℕ, (a ^ n) ^ 9 = 1 := fun n => by
    rw [← pow_mul, mul_comm, pow_mul, ha9, one_pow]
  let f : Fin 9 × Fin 9 → Subgroup.centralizer
      ({k329lu_dg h 1 ω (one_pow 9) hω9} : Set ↥(SG h)) := fun p =>
    ⟨k329lu_dg h (a ^ (p.1 : ℕ)) (a ^ (p.2 : ℕ)) (hpow _) (hpow _),
      Subgroup.mem_centralizer_singleton_iff.2
        (k329lu_dg_comm h (hpow _) (hpow _) (one_pow 9) hω9)⟩
  have hinj : Function.Injective f := by
    intro p q hpq
    have h1 : a ^ (p.1 : ℕ) = a ^ (q.1 : ℕ) ∧ a ^ (p.2 : ℕ) = a ^ (q.2 : ℕ) :=
      k329lu_dg_injective h (hpow _) (hpow _) (hpow _) (hpow _) (congrArg Subtype.val hpq)
    have e1 : (p.1 : ℕ) = q.1 :=
      pow_injOn_Iio_orderOf (x := a) (by rw [Set.mem_Iio, ha]; exact p.1.2)
        (by rw [Set.mem_Iio, ha]; exact q.1.2) h1.1
    have e2 : (p.2 : ℕ) = q.2 :=
      pow_injOn_Iio_orderOf (x := a) (by rw [Set.mem_Iio, ha]; exact p.2.2)
        (by rw [Set.mem_Iio, ha]; exact q.2.2) h1.2
    exact Prod.ext (Fin.ext e1) (Fin.ext e2)
  calc 81 = Nat.card (Fin 9 × Fin 9) := by simp
    _ ≤ _ := Nat.card_le_card_of_injective f hinj

private lemma k329lu_card_range_ge {K : Type} [Field K] [Finite K] (h : UnitaryFieldData 2 3 K)
    (S : Subgroup ↥(SG h)) (hS : 81 ≤ Nat.card S) :
    27 ≤ Nat.card ((projU h).comp S.subtype).range := by
  have h1 := Subgroup.card_ker_mul_card_range ((projU h).comp S.subtype)
  have h3 : Nat.card ((projU h).comp S.subtype).ker ∣ Nat.card (projU h).ker := by
    rw [← MonoidHom.comap_ker]
    exact Subgroup.card_comap_dvd_of_injective _ S.subtype S.subtype_injective
  have h2 : Nat.card ((projU h).comp S.subtype).ker ≤ 3 :=
    (Nat.le_of_dvd Nat.card_pos h3).trans (k329lu_ker_card_le h)
  by_contra hlt
  push Not at hlt
  have h4 := Nat.mul_le_mul h2 (Nat.le_of_lt_succ hlt)
  omega

private lemma k329lu_sigma_not_range {K : Type} [Field K] (h : UnitaryFieldData 2 3 K) {ω : Kˣ}
    (hω9 : ω ^ 9 = 1) (hω3 : ω ^ 3 = 1) (hω1 : (ω : K) ≠ 1) :
    projU h (k329lu_sigma h) ∉ ((projU h).comp (Subgroup.centralizer
      ({k329lu_dg h 1 ω (one_pow 9) hω9} : Set ↥(SG h))).subtype).range := by
  rintro ⟨⟨s, hs⟩, hsσ⟩
  have hs' := Subgroup.mem_centralizer_singleton_iff.1 hs
  have hk : projU h ((k329lu_sigma h)⁻¹ * s) = 1 := by
    have hsσ' : projU h s = projU h (k329lu_sigma h) := hsσ
    rw [map_mul, map_inv, hsσ', inv_mul_cancel]
  obtain ⟨hcen, -⟩ := k329lu_ker_central h hk
  have hkc := Subgroup.mem_center_iff.1 hcen
  have hsk : s = k329lu_sigma h * ((k329lu_sigma h)⁻¹ * s) := by group
  have hcomm : k329lu_dg h 1 ω (one_pow 9) hω9 * k329lu_sigma h =
      k329lu_sigma h * k329lu_dg h 1 ω (one_pow 9) hω9 := by
    apply mul_right_cancel (b := (k329lu_sigma h)⁻¹ * s)
    calc k329lu_dg h 1 ω (one_pow 9) hω9 * k329lu_sigma h * ((k329lu_sigma h)⁻¹ * s)
        = k329lu_dg h 1 ω (one_pow 9) hω9 * (k329lu_sigma h * ((k329lu_sigma h)⁻¹ * s)) := by
          rw [mul_assoc]
      _ = k329lu_dg h 1 ω (one_pow 9) hω9 * s := by rw [← hsk]
      _ = s * k329lu_dg h 1 ω (one_pow 9) hω9 := hs'.symm
      _ = k329lu_sigma h * ((k329lu_sigma h)⁻¹ * s) * k329lu_dg h 1 ω (one_pow 9) hω9 := by
          rw [← hsk]
      _ = k329lu_sigma h * (((k329lu_sigma h)⁻¹ * s) * k329lu_dg h 1 ω (one_pow 9) hω9) := by
          rw [mul_assoc]
      _ = k329lu_sigma h * (k329lu_dg h 1 ω (one_pow 9) hω9 * ((k329lu_sigma h)⁻¹ * s)) := by
          rw [← hkc (k329lu_dg h 1 ω (one_pow 9) hω9)]
      _ = k329lu_sigma h * k329lu_dg h 1 ω (one_pow 9) hω9 * ((k329lu_sigma h)⁻¹ * s) := by
          rw [mul_assoc]
  have hz := k329lu_sigma_dg h hω9 hω3
  rw [hcomm] at hz
  exact k329lu_scalarU_ne_one h (k329lu_norm_eq h hω9) hω3 hω1 (by simpa using hz.symm)

private lemma k329lu_big {K : Type} [Field K] [Finite K] (h : UnitaryFieldData 2 3 K) {a : Kˣ}
    (ha : orderOf a = 9) {ω : Kˣ} (hω9 : ω ^ 9 = 1) (hω3 : ω ^ 3 = 1) (hω1 : (ω : K) ≠ 1) :
    27 < Nat.card (Subgroup.centralizer
      ({projU h (k329lu_dg h 1 ω (one_pow 9) hω9)} : Set (PU h))) := by
  have h1 := k329lu_card_range_ge h _ (k329lu_card_cent_ge h ha hω9)
  have hle : ((projU h).comp (Subgroup.centralizer
      ({k329lu_dg h 1 ω (one_pow 9) hω9} : Set ↥(SG h))).subtype).range ≤
      Subgroup.centralizer ({projU h (k329lu_dg h 1 ω (one_pow 9) hω9)} : Set (PU h)) := by
    rintro _ ⟨⟨s, hs⟩, rfl⟩
    have hs' := Subgroup.mem_centralizer_singleton_iff.1 hs
    rw [Subgroup.mem_centralizer_singleton_iff]
    change projU h s * projU h _ = projU h _ * projU h s
    rw [← map_mul, ← map_mul, hs']
  have hlt : ((projU h).comp (Subgroup.centralizer
      ({k329lu_dg h 1 ω (one_pow 9) hω9} : Set ↥(SG h))).subtype).range <
      Subgroup.centralizer ({projU h (k329lu_dg h 1 ω (one_pow 9) hω9)} : Set (PU h)) :=
    lt_of_le_of_ne hle (fun heq => k329lu_sigma_not_range h hω9 hω3 hω1
      (by rw [heq]; exact k329lu_sigma_mem h hω9 hω3))
  exact lt_of_le_of_lt h1 (Subgroup.card_lt_of_lt hlt)

private lemma k329lu_order_u {K : Type} [Field K] (h : UnitaryFieldData 2 3 K) {ω : Kˣ}
    (hω9 : ω ^ 9 = 1) (hω3 : ω ^ 3 = 1) (hω1 : (ω : K) ≠ 1) :
    orderOf (projU h (k329lu_dg h 1 ω (one_pow 9) hω9)) = 3 := by
  have hω3K : (ω : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hω3, Units.val_one]
  apply orderOf_eq_prime
  · rw [← map_pow]
    have hu3 : k329lu_dg h 1 ω (one_pow 9) hω9 ^ 3 = 1 := by
      apply Subtype.ext
      apply Units.ext
      rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, k329lu_coe_dg, diagonal_pow]
      simp only [Subgroup.coe_one, Units.val_one]
      rw [← diagonal_one]
      congr 1
      funext i
      fin_cases i <;> simp [hω3K]
    rw [hu3, map_one]
  · intro hone
    obtain ⟨c, -, -, hc⟩ := projU_eq_one_iff.1 hone
    have hc' := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hc
    have e0 := congrFun (congrFun hc' 0) 0
    have e1 := congrFun (congrFun hc' 1) 1
    simp only [k329lu_coe_dg, Matrix.GeneralLinearGroup.coe_scalar, scalar_apply,
      diagonal_apply_eq, Matrix.cons_val_zero, Matrix.cons_val_one, Units.val_one] at e0 e1
    exact hω1 (e1.trans e0.symm)

private lemma k329lu_noncomm {K : Type} [Field K] (h : UnitaryFieldData 2 3 K) {a : Kˣ}
    (ha9 : a ^ 9 = 1) (hai : a⁻¹ ^ 9 = 1) (ha3 : (a : K) ^ 3 ≠ 1) :
    projU h (k329lu_dg h a a⁻¹ ha9 hai) * projU h (k329lu_sigma h) ≠
      projU h (k329lu_sigma h) * projU h (k329lu_dg h a a⁻¹ ha9 hai) := by
  intro hcomm
  rw [← map_mul, ← map_mul] at hcomm
  obtain ⟨c, hc⟩ := exists_scalar_of_projU_eq hcomm
  have hc' := congrArg (fun g : Matrix (Fin 3) (Fin 3) K => g) hc
  have e01 := congrFun (congrFun hc' 0) 1
  have e20 := congrFun (congrFun hc' 2) 0
  simp [Subgroup.coe_mul, Units.val_mul, k329lu_coe_dg, k329lu_coe_sigma, k329lu_sigmaMat,
    Matrix.mul_apply, Matrix.diagonal_apply] at e01 e20
  have ha0 : (a : K) ≠ 0 := a.ne_zero
  apply ha3
  field_simp at e01 e20
  linear_combination ((a : K) ^ 2) * e20 - e01

private lemma k329lu_centralizer_map {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (z : X) :
    Subgroup.centralizer ({e z} : Set Y) =
      (Subgroup.centralizer ({z} : Set X)).map e.toMonoidHom := by
  apply le_antisymm
  · intro y hy
    refine Subgroup.mem_map.mpr ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply]
    exact hy
  · simpa using Subgroup.map_centralizer_le_centralizer_image ({z} : Set X) e.toMonoidHom

private lemma k329lu_transport {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {y : Y}
    (h3 : orderOf y = 3) (hC : Nat.card (Subgroup.centralizer ({y} : Set Y)) = 81)
    (hnc : ∃ a ∈ Subgroup.centralizer ({y} : Set Y), ∃ b ∈ Subgroup.centralizer ({y} : Set Y),
      a * b ≠ b * a) :
    ∃ x : X, orderOf x = 3 ∧ Nat.card (Subgroup.centralizer ({x} : Set X)) = 81 ∧
      ∃ a ∈ Subgroup.centralizer ({x} : Set X), ∃ b ∈ Subgroup.centralizer ({x} : Set X),
        a * b ≠ b * a := by
  have hy : e (e.symm y) = y := e.apply_symm_apply y
  have hcent := k329lu_centralizer_map e (e.symm y)
  rw [hy] at hcent
  refine ⟨e.symm y, ?_, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq]
    exact h3
  · rw [hcent, Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective] at hC
    exact hC
  · obtain ⟨a, ha, b, hb, hab⟩ := hnc
    rw [hcent] at ha hb
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.1 ha
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.1 hb
    refine ⟨a', ha', b', hb', fun hab' => hab ?_⟩
    change e a' * e b' = e b' * e a'
    rw [← map_mul, ← map_mul, hab']

private lemma k329lu_finish {G : Type} [Group G] [Finite G] (hG : Nat.card G = 5515776) {u₀ : G}
    (h3 : orderOf u₀ = 3) (hC : Nat.card (Subgroup.centralizer ({u₀} : Set G)) = 81)
    (hnc : ∃ a ∈ Subgroup.centralizer ({u₀} : Set G), ∃ b ∈ Subgroup.centralizer ({u₀} : Set G),
      a * b ≠ b * a)
    (Q : Sylow 3 G) :
    ∃ u ∈ (Q : Subgroup G), orderOf u = 3 ∧ Subgroup.centralizer ({u} : Set G) = Q ∧
      ∃ a ∈ (Q : Subgroup G), ∃ b ∈ (Q : Subgroup G), a * b ≠ b * a := by
  have hfac : (Nat.card G).factorization 3 = 4 := by
    rw [hG]
    have h1 : 3 ^ 4 ∣ 5515776 := by norm_num
    have h2 : ¬ 3 ^ 5 ∣ 5515776 := by norm_num
    have h3' := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three (by norm_num)).1 h1
    have h4 := mt (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three (by norm_num)).2 h2
    omega
  let Q₀ : Sylow 3 G := Sylow.ofCard (Subgroup.centralizer ({u₀} : Set G))
    (by rw [hC, hfac]; norm_num)
  have hQ₀ : (Q₀ : Subgroup G) = Subgroup.centralizer ({u₀} : Set G) := Sylow.coe_ofCard _ _
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q₀ Q
  have hQ : (Q : Subgroup G) =
      (Subgroup.centralizer ({u₀} : Set G)).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul, hQ₀]
    rfl
  refine ⟨MulAut.conj g u₀, ?_, ?_, ?_, ?_⟩
  · rw [hQ]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_centralizer_singleton_iff.2 rfl)
  · exact (orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective u₀).trans h3
  · rw [k329lu_centralizer_map (MulAut.conj g) u₀, hQ]
  · obtain ⟨a, ha, b, hb, hab⟩ := hnc
    refine ⟨MulAut.conj g a, ?_, MulAut.conj g b, ?_, fun hab' => hab ?_⟩
    · rw [hQ]
      exact Subgroup.mem_map_of_mem _ ha
    · rw [hQ]
      exact Subgroup.mem_map_of_mem _ hb
    · apply (MulAut.conj g).injective
      rw [map_mul, map_mul]
      exact hab'

private theorem k329lu_PU_main {K : Type} [Field K] [Finite K] (h : UnitaryFieldData 2 3 K)
    (a : Kˣ) (ha : orderOf a = 9) (hG : Nat.card (PU h) = 5515776) :
    ∃ u : PU h, orderOf u = 3 ∧ Nat.card (Subgroup.centralizer ({u} : Set (PU h))) = 81 ∧
      ∃ x ∈ Subgroup.centralizer ({u} : Set (PU h)), ∃ y ∈ Subgroup.centralizer ({u} : Set (PU h)),
        x * y ≠ y * x := by
  have ha9 : a ^ 9 = 1 := by rw [← ha, pow_orderOf_eq_one]
  have hai : a⁻¹ ^ 9 = 1 := by rw [inv_pow, ha9, inv_one]
  have ha3 : (a : K) ^ 3 ≠ 1 := by
    intro h3
    have h3u : a ^ 3 = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      exact h3
    have hdvd : orderOf a ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr h3u
    rw [ha] at hdvd
    norm_num at hdvd
  have hω9 : (a ^ 3) ^ 9 = 1 := by
    rw [← pow_mul, show 3 * 9 = 9 * 3 by norm_num, pow_mul, ha9, one_pow]
  have hω3 : (a ^ 3) ^ 3 = 1 := by
    rw [← pow_mul]
    exact ha9
  have hω1 : ((a ^ 3 : Kˣ) : K) ≠ 1 := by
    rw [Units.val_pow_eq_pow_val]
    exact ha3
  refine ⟨projU h (k329lu_dg h 1 (a ^ 3) (one_pow 9) hω9), k329lu_order_u h hω9 hω3 hω1, ?_, ?_⟩
  · exact k329lu_card_eq_81 hG
      (k329lu_isPGroup _ fun x hx => k329lu_pow_27 h hω9 hω3 hω1 hx)
      (k329lu_big h ha hω9 hω3 hω1)
  · exact ⟨_, k329lu_dg_mem h hω9 ha9 hai, _, k329lu_sigma_mem h hω9 hω3,
      k329lu_noncomm h ha9 hai ha3⟩

theorem k329_u38_centralizer_u (X : Type) [Group X] [Finite X] (hX : LieModel X .PSU 3 2 3)
    (Q : Sylow 3 X) :
    ∃ u ∈ (Q : Subgroup X), orderOf u = 3 ∧ Subgroup.centralizer ({u} : Set X) = Q ∧
      ∃ a ∈ (Q : Subgroup X), ∃ b ∈ (Q : Subgroup X), a * b ≠ b * a := by
  have hXcard : Nat.card X = 5515776 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_eight
      (hX.statedClassicalModel (by decide))
  obtain ⟨-, K, hKf, hKfin, hKcard, ⟨φ⟩⟩ := hX.statedClassicalModel (by decide)
  have h : UnitaryFieldData 2 3 K :=
    ⟨Nat.prime_two, by norm_num, by rw [hKcard]; norm_num⟩
  have hK64 : Nat.card K = 64 := by rw [hKcard]; norm_num
  obtain ⟨a, ha⟩ : ∃ a : Kˣ, orderOf a = 9 := by
    have hcard : Nat.card Kˣ = 63 := by rw [Nat.card_units, hK64]
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
    rw [hcard] at hg
    exact ⟨g ^ 7, by rw [orderOf_pow, hg]; norm_num⟩
  let Ψ : X ≃* PU h := φ.trans (PUEquivStated h).symm
  have hG : Nat.card (PU h) = 5515776 := by
    rw [← hXcard]
    exact (Nat.card_congr Ψ.toEquiv).symm
  obtain ⟨u₀, h3, hC, hnc⟩ := k329lu_PU_main h a ha hG
  obtain ⟨u₁, h3', hC', hnc'⟩ := k329lu_transport Ψ h3 hC hnc
  exact k329lu_finish hXcard h3' hC' hnc' Q

theorem k329_u38_centralizer_z (X : Type) [Group X] [Finite X] (hX : LieModel X .PSU 3 2 3)
    (Q : Sylow 3 X) :
    ∃ z ∈ (Q : Subgroup X), orderOf z = 3 ∧
      LieModel ↥⁅Subgroup.centralizer ({z} : Set X), Subgroup.centralizer ({z} : Set X)⁆
        .PSL 2 2 3 := by
  obtain ⟨-, K, hKf, hKfin, hKcard, ⟨φ⟩⟩ := hX.statedClassicalModel (by decide)
  have h : UnitaryFieldData 2 3 K :=
    ⟨Nat.prime_two, by norm_num, by rw [hKcard]; norm_num⟩
  have hK64 : Nat.card K = 64 := by rw [hKcard]; norm_num
  obtain ⟨a, ha⟩ : ∃ a : Kˣ, orderOf a = 9 := by
    have hcard : Nat.card Kˣ = 63 := by rw [Nat.card_units, hK64]
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
    rw [hcard] at hg
    exact ⟨g ^ 7, by rw [orderOf_pow, hg]; norm_num⟩
  obtain ⟨z₀, hz₀order, hz₀lie⟩ := k329lz_PU_main h a ha
  let Ψ : X ≃* PU h := φ.trans (PUEquivStated h).symm
  let z₁ : X := Ψ.symm z₀
  have hΨz₁ : Ψ z₁ = z₀ := MulEquiv.apply_symm_apply Ψ z₀
  have hz₁order : orderOf z₁ = 3 := by
    have h := orderOf_injective Ψ.toMonoidHom Ψ.injective z₁
    rw [show Ψ.toMonoidHom z₁ = z₀ from hΨz₁, hz₀order] at h
    exact h.symm
  have hz₁lie : LieModel ↥⁅Subgroup.centralizer ({z₁} : Set X),
      Subgroup.centralizer ({z₁} : Set X)⁆ .PSL 2 2 3 :=
    k329lz_lieModel_congr Ψ z₁ (by rw [hΨz₁]; exact hz₀lie)
  have hz₁3 : IsPGroup 3 (Subgroup.zpowers z₁) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz₁order]; norm_num)
  obtain ⟨P₁, hP₁⟩ := hz₁3.exists_le_sylow
  have hz₁P₁ : z₁ ∈ P₁ := hP₁ (Subgroup.mem_zpowers z₁)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X P₁ Q
  refine ⟨MulAut.conj g z₁, ?_, ?_, ?_⟩
  · rw [← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hz₁P₁
  · exact (orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective z₁).trans hz₁order
  · refine k329lz_lieModel_congr (MulAut.conj g).symm ((MulAut.conj g) z₁) ?_
    rw [show (MulAut.conj g).symm ((MulAut.conj g) z₁) = z₁ from MulEquiv.symm_apply_apply _ _]
    exact hz₁lie

theorem k329U38LocalFacts_of_parts : k329U38LocalFactsStatement :=
  fun X _ _ hX Q => ⟨k329_u38_centralizer_u X hX Q, k329_u38_centralizer_z X hX Q⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
