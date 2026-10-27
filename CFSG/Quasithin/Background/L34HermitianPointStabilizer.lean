module

public import CFSG.Quasithin.Background.HL3NineComm
public import CFSG.Quasithin.Recognition.Kleidman.F204.CaseIIT2Sec
public import CFSG.RankThree.PartTwo.KFacts.L34Sylow
public import CFSG.LinearAlgebra.HermitianDiagonalization

public section

namespace CFSG.Quasithin

open Matrix CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.H.L3Nine
open CFSG.RankThree.PartTwo.KFacts.L34
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private theorem tw_hM_diagonal (hK : Nat.card K = (2 ^ 1) ^ 2) {u : Kˣ} {d : Fin 3 → K} :
    tw 1 (LinearFieldFour.hM (u : K)) (Matrix.diagonal d) = Matrix.diagonal d := by
  have h3u : (u : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, LinearThreeFourOuter.units_pow_three hK u, Units.val_one]
  have hbu : H.SU3.bar 1 (u : K) = (u : K) * u := by
    rw [H.SU3.bar_apply, pow_one, pow_two]
  have hbu2 : H.SU3.bar 1 ((u : K) * u) = (u : K) := by
    rw [H.SU3.bar_apply, pow_one, mul_pow]
    rw [show (u : K) ^ 2 * (u : K) ^ 2 = (u : K) ^ 3 * (u : K) by ring, h3u, one_mul]
  have hhM : LinearFieldFour.hM (u : K) = Matrix.diagonal ![(u : K), (1 : K), (u : K) * u] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [LinearFieldFour.hM]
  have hconj : H.SU3.conjM 1 (LinearFieldFour.hM (u : K)) =
      Matrix.diagonal ![H.SU3.bar 1 (u : K), (1 : K), H.SU3.bar 1 ((u : K) * u)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [H.SU3.conjM, LinearFieldFour.hM]
  have hnorm : (u : K) * H.SU3.bar 1 (u : K) = 1 := by
    rw [hbu, ← pow_three, h3u]
  have hnorm2 : ((u : K) * u) * H.SU3.bar 1 ((u : K) * u) = 1 := by
    rw [hbu2, show (u : K) * u * u = (u : K) ^ 3 by ring, h3u]
  rw [tw, hconj, hhM, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i
  · calc ((u : K) * d 0) * H.SU3.bar 1 (u : K) =
        ((u : K) * H.SU3.bar 1 (u : K)) * d 0 := by ring
      _ = d 0 := by rw [hnorm, one_mul]
  · simp
  · calc (((u : K) * u) * d 2) * H.SU3.bar 1 ((u : K) * u) =
        (((u : K) * u) * H.SU3.bar 1 ((u : K) * u)) * d 2 := by ring
      _ = d 2 := by rw [hnorm2, one_mul]

open CFSG.LieType.Universal.Unitary CFSG.ComponentClassification.CatalogueBHermitian

private theorem exists_order_three_fix_hermitian_of_congr
    (hK : Nat.card K = (2 ^ 1) ^ 2) (X : HMod 1 K)
    (hdiag : ∃ (P : GL (Fin 3) K) (d : Fin 3 → K),
      (∀ i, d i = 0 ∨ d i = 1) ∧
      conjTr (H.SU3.bar 1) P.val * mat X * P.val = Matrix.diagonal d) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 3) K,
      g ^ 3 = 1 ∧ rho hK g ≠ 1 ∧ rho hK g X = X := by
  obtain ⟨u, hu⟩ := exists_units_ne_one hK
  obtain ⟨P, d, hd01, hPX⟩ := hdiag
  have hsigma : (H.SU3.bar 1 : K ≃+* K) ^ 2 = 1 := by
    ext x
    exact H.SU3.bar_bar hK x
  let Q : GL (Fin 3) K := conjugateTransposeGL (H.SU3.bar 1) P
  have hQval : (Q : Matrix (Fin 3) (Fin 3) K) = conjTr (H.SU3.bar 1) P.val := rfl
  have hQstar : conjTr (H.SU3.bar 1) (Q : Matrix (Fin 3) (Fin 3) K) = P.val := by
    rw [hQval]
    exact conjugateTranspose_involutive (H.SU3.bar 1) hsigma P.val
  have hd : ∀ i, H.SU3.bar 1 (d i) = d i := by
    intro i
    rcases hd01 i with h | h <;> rw [h] <;> simp
  have hherm : (H.SU3.conjM 1 (Matrix.diagonal d))ᵀ = Matrix.diagonal d := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [H.SU3.conjM, hd]
  let h : Matrix.SpecialLinearGroup (Fin 3) K := hSL u
  have hpair : (u, (1 : Kˣ)) ^ 3 = 1 := by
    ext <;> simp [LinearThreeFourOuter.units_pow_three hK u]
  have hh3 : h ^ 3 = 1 := by
    change (hSL u) ^ 3 = 1
    rw [hSL, ← map_pow, hpair, map_one]
  let gGL : GL (Fin 3) K := (Q : GL (Fin 3) K)⁻¹ * SpecialLinearGroup.toGL h * Q
  have hgdet : (gGL : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    have hdet : Matrix.GeneralLinearGroup.det gGL = 1 := by
      change Matrix.GeneralLinearGroup.det ((Q : GL (Fin 3) K)⁻¹ *
        SpecialLinearGroup.toGL h * Q) = 1
      rw [map_mul, map_mul, map_inv]
      have hh : Matrix.GeneralLinearGroup.det (SpecialLinearGroup.toGL h) = 1 := by
        apply Units.ext
        rw [Matrix.GeneralLinearGroup.val_det_apply]
        exact h.2
      rw [hh, mul_one, inv_mul_cancel]
    rw [← Matrix.GeneralLinearGroup.val_det_apply, hdet, Units.val_one]
  let g : Matrix.SpecialLinearGroup (Fin 3) K := ⟨gGL, hgdet⟩
  have hgcoe : SpecialLinearGroup.toGL g = gGL := Units.ext rfl
  have hg3 : g ^ 3 = 1 := by
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [map_pow, map_one, hgcoe]
    change ((Q : GL (Fin 3) K)⁻¹ * SpecialLinearGroup.toGL h * Q) ^ 3 = 1
    rw [show (Q : GL (Fin 3) K)⁻¹ * SpecialLinearGroup.toGL h * Q =
        (Q : GL (Fin 3) K)⁻¹ * SpecialLinearGroup.toGL h * ((Q : GL (Fin 3) K)⁻¹)⁻¹ by
      rw [inv_inv]]
    rw [conj_pow]
    rw [show (SpecialLinearGroup.toGL h) ^ 3 = 1 by
      rw [← map_pow, hh3, map_one]]
    simp
  have hQX : rhoT hK Q X = mkH (Matrix.diagonal d) hherm := by
    apply mat_injective
    rw [mat_rhoT, tw, mat_mkH]
    change (Q : Matrix (Fin 3) (Fin 3) K) * mat X *
      conjTr (H.SU3.bar 1) (Q : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal d
    rw [hQstar, hQval]
    exact hPX
  have hfixD : rhoT hK (SpecialLinearGroup.toGL h)
      (mkH (Matrix.diagonal d) hherm) = mkH (Matrix.diagonal d) hherm := by
    apply mat_injective
    rw [mat_rhoT, tw, mat_mkH]
    have hcoeh : (SpecialLinearGroup.toGL h : Matrix (Fin 3) (Fin 3) K) =
        LinearFieldFour.hM (u : K) := by
      change (h : Matrix (Fin 3) (Fin 3) K) = LinearFieldFour.hM (u : K)
      rw [show h = hSL u from rfl]
      exact CFSG.RankThree.PartTwo.KFacts.L34.coe_hSL (k := K) (u := u) hK
    rw [hcoeh]
    exact tw_hM_diagonal hK
  have hgX : rho hK g X = X := by
    change rhoT hK (SpecialLinearGroup.toGL g) X = X
    have hcoe : SpecialLinearGroup.toGL g =
        (Q : GL (Fin 3) K)⁻¹ * SpecialLinearGroup.toGL h * Q := hgcoe
    rw [hcoe, map_mul, map_mul, map_inv, MulAut.mul_apply, MulAut.mul_apply, hQX, hfixD]
    rw [← hQX, ← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
  have hne : rho hK g ≠ 1 := by
    intro hg1
    have hρT : rhoT hK (SpecialLinearGroup.toGL g) = 1 := hg1
    obtain ⟨d', hd'⟩ := scalar_of_rhoT_eq_one hK hρT
    have hH : SpecialLinearGroup.toGL h =
        (Q : GL (Fin 3) K) * SpecialLinearGroup.toGL g * (Q : GL (Fin 3) K)⁻¹ := by
      have hcoe : SpecialLinearGroup.toGL g =
          (Q : GL (Fin 3) K)⁻¹ * SpecialLinearGroup.toGL h * Q := hgcoe
      rw [hcoe]
      group
    have hHmat : (h : Matrix (Fin 3) (Fin 3) K) = d' • 1 := by
      have hval := congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) hH
      change (h : Matrix (Fin 3) (Fin 3) K) =
        (Q : Matrix (Fin 3) (Fin 3) K) *
          (SpecialLinearGroup.toGL g : Matrix (Fin 3) (Fin 3) K) *
            ((Q⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) at hval
      rw [hd'] at hval
      rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one] at hval
      have hmul : (Q : Matrix (Fin 3) (Fin 3) K) *
          ((Q⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      rw [hmul] at hval
      simpa using hval
    have hd3 : d' ^ 3 = 1 := by
      have hdet : (h : Matrix (Fin 3) (Fin 3) K).det = 1 := h.2
      rw [hHmat] at hdet
      simpa [Matrix.det_smul, Matrix.det_one] using hdet
    have hd0 : d' ≠ 0 := by
      intro h0
      rw [h0] at hd3
      norm_num at hd3
    let c : Kˣ := Units.mk0 d' hd0
    have hc3 : c ^ 3 = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val]
      change d' ^ 3 = 1
      exact hd3
    have hscal : h ∈ scalars 3 K := by
      refine LinearFlag.mem_scalars.mpr ⟨c, hc3, ?_⟩
      rw [hHmat, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
      simp [c]
    have hcontra : aP u = 1 := LinearFlag.proj_eq_one_iff.mpr hscal
    exact aP_ne_one hK hu hcontra
  exact ⟨g, hg3, hne, hgX⟩

theorem exists_order_three_fix_hermitian
    (hK : Nat.card K = (2 ^ 1) ^ 2) (X : HMod 1 K) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 3) K,
      g ^ 3 = 1 ∧ rho hK g ≠ 1 ∧ rho hK g X = X := by
  have hsigma : (H.SU3.bar 1 : K ≃+* K) ^ 2 = 1 := by
    ext x
    exact H.SU3.bar_bar hK x
  obtain ⟨u, hu⟩ := exists_units_ne_one hK
  have hne : (H.SU3.bar 1 : K ≃+* K) ≠ 1 := by
    intro hbar
    have h1 : H.SU3.bar 1 (u : K) = (u : K) := by rw [hbar]; rfl
    have h2 : H.SU3.bar 1 (u : K) = (u : K) * u := by
      rw [H.SU3.bar_apply, pow_one, pow_two]
    have h3 : (u : K) * u = (u : K) := h2.symm.trans h1
    have h4 : (u : K) = 1 := mul_left_cancel₀ u.ne_zero (by simpa using h3)
    exact hu (Units.ext h4)
  obtain ⟨P, d, hd01, hPX⟩ := CFSG.LinearAlgebra.exists_diagonal_congr_of_hermitian
    (sigma := H.SU3.bar 1) hsigma hne (mat X) (herm_mat X)
  exact exists_order_three_fix_hermitian_of_congr hK X ⟨P, d, hd01, hPX⟩

open CFSG.Quasithin.Kleidman.F204.Sec

private theorem exists_order_three_fix_of_binaryNineTensor_aux
    {W : Type} [CommGroup W]
    (hW : ∀ w : W, w ^ 2 = 1)
    {G : Subgroup (MulAut W)} {U Z : Subgroup W}
    (hmodel : BinaryNineTensor G U Z 1)
    (hZ : Z ≤ fixV G) (w : W) (hw : w ∈ U)
    (hpoint : ∀ (K : Type) [Field K] [Finite K] [CharP K 2]
      (hK : Nat.card K = (2 ^ 1) ^ 2) (X : HMod 1 K),
      ∃ g : Matrix.SpecialLinearGroup (Fin 3) K,
        g ^ 3 = 1 ∧ rho hK g ≠ 1 ∧ rho hK g X = X) :
    ∃ b ∈ G, orderOf b = 3 ∧ (b : MulAut W) w = w := by
  obtain ⟨K, hfield, hfinite, hchar, hcard, π, hπ⟩ := hmodel
  letI := hfield
  letI := hfinite
  letI := hchar
  obtain ⟨-, -, -, hUinv, -, hsecinv, -, β, hβsurj, hβkermem, hβeq⟩ := hπ
  let u : ↥U := ⟨w, hw⟩
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β u)
  let X : HMod 1 K := m
  have hK : Nat.card K = (2 ^ 1) ^ 2 := by
    rw [hcard]
    norm_num
  obtain ⟨g, hg3, hgne, hgfix⟩ := hpoint K hK X
  let γ : ↥(StatedSL 3 K) := specialLinearGroupEquivStatedSL 3 K g
  have hγ3 : γ ^ 3 = 1 := by
    change (specialLinearGroupEquivStatedSL 3 K g) ^ 3 = 1
    rw [← map_pow, hg3, map_one]
  have hγcoe : (γ : GL (Fin 3) K) = SpecialLinearGroup.toGL g := by
    apply Units.ext
    simpa using specialLinearGroupEquivStatedSL_coe 3 K g
  let b : MulAut W := ((π γ : ↥G) : MulAut W)
  have hbH : b ∈ G := (π γ).2
  have hπγ3 : (π γ : ↥G) ^ 3 = 1 := by
    calc (π γ : ↥G) ^ 3 = π (γ ^ 3) := (map_pow π γ 3).symm
      _ = π 1 := congrArg π hγ3
      _ = 1 := map_one π
  have hb3 : b ^ 3 = 1 := by
    change ((π γ : ↥G) : MulAut W) ^ 3 = 1
    rw [← Subgroup.coe_pow, hπγ3, Subgroup.coe_one]
  let toAmb : HMod 1 K → (FFModel.twistTensor 1 (StatedSL 3 K)).Amb :=
    fun Y => Y.1
  let toAmbSec : ↥(FFModel.twistTensor 1 (StatedSL 3 K)).sec →
      (FFModel.twistTensor 1 (StatedSL 3 K)).Amb :=
    fun Y => Y.1
  have hact_eq : ∀ (δ : ↥(StatedSL 3 K)) (Y : HMod 1 K),
      (FFModel.twistTensor 1 (StatedSL 3 K)).act δ (toAmb Y) =
        toAmb (rhoT hK (δ : GL (Fin 3) K) Y) := by
    intro δ Y
    apply Multiplicative.toAdd.injective
    change (δ : GL (Fin 3) K) * H.L3Nine.mat Y *
        (frobPow 1 ((δ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))ᵀ =
      (δ : GL (Fin 3) K) * H.L3Nine.mat Y *
        (H.SU3.conjM 1 ((δ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))ᵀ
    simp [H.L3Nine.frobPow_eq_conjM]
  have hact_X : (FFModel.twistTensor 1 (StatedSL 3 K)).act γ (toAmb X) =
      toAmb X := by
    have hgfix' : rhoT hK (γ : GL (Fin 3) K) X = X := by
      simpa [rho, ← hγcoe] using hgfix
    have h1 := hact_eq γ X
    have h2 : toAmb (rhoT hK (γ : GL (Fin 3) K) X) = toAmb X := by
      simp [hgfix']
    exact h1.trans h2
  have hact_m : (FFModel.twistTensor 1 (StatedSL 3 K)).act γ (toAmbSec m) =
      toAmbSec m := by
    simpa [toAmb, toAmbSec, X] using hact_X
  have hbw_mem : b w * w⁻¹ ∈ Z := by
    have hbwU : ((π γ : ↥G) : MulAut W) w ∈ U := hUinv (π γ) w hw
    have hU' : b w * w⁻¹ ∈ U := mul_mem hbwU (inv_mem u.2)
    have hβu' : β ⟨b w, hbwU⟩ = β u := by
      have hmsec : (FFModel.twistTensor 1 (StatedSL 3 K)).act γ (toAmbSec m) ∈
          (FFModel.twistTensor 1 (StatedSL 3 K)).sec := hsecinv γ (toAmbSec m) m.2
      have heq := hβeq γ u m hbwU hmsec hm.symm
      have hsub : (⟨(FFModel.twistTensor 1 (StatedSL 3 K)).act γ (toAmbSec m), hmsec⟩ :
          ↥(FFModel.twistTensor 1 (StatedSL 3 K)).sec) = m := Subtype.ext hact_m
      rw [hsub] at heq
      simpa using heq.trans hm
    have h2 : β ⟨b w * w⁻¹, hU'⟩ = 1 := by
      have hsplit : (⟨b w * w⁻¹, hU'⟩ : ↥U) = ⟨b w, hbwU⟩ * ⟨w, hw⟩⁻¹ :=
        Subtype.ext rfl
      rw [hsplit, map_mul, map_inv, hβu']
      change β u * (β u)⁻¹ = 1
      exact mul_inv_cancel _
    exact (hβkermem ⟨b w * w⁻¹, hU'⟩).mp h2
  have hbne : b ≠ 1 := by
    intro hb1
    have hπγ1 : π γ = 1 := Subtype.ext hb1
    have hact_all : ∀ m' : ↥(FFModel.twistTensor 1 (StatedSL 3 K)).sec,
        (FFModel.twistTensor 1 (StatedSL 3 K)).act γ (toAmbSec m') = toAmbSec m' := by
      intro m'
      obtain ⟨u', hu'⟩ := hβsurj (QuotientGroup.mk m')
      have hU' : ((π γ : ↥G) : MulAut W) (u' : W) ∈ U := hUinv (π γ) (u' : W) u'.2
      have hm'sec : (FFModel.twistTensor 1 (StatedSL 3 K)).act γ (toAmbSec m') ∈
          (FFModel.twistTensor 1 (StatedSL 3 K)).sec := hsecinv γ (toAmbSec m') m'.2
      have heq := hβeq γ u' m' hU' hm'sec hu'
      have hfixu : ((π γ : ↥G) : MulAut W) (u' : W) = (u' : W) := by
        rw [hπγ1]
        rfl
      have hL : β ⟨((π γ : ↥G) : MulAut W) (u' : W), hU'⟩ = β u' := by
        congr 1
        exact Subtype.ext hfixu
      have h3 : ((⟨(FFModel.twistTensor 1 (StatedSL 3 K)).act γ (toAmbSec m'), hm'sec⟩ :
            ↥(FFModel.twistTensor 1 (StatedSL 3 K)).sec) :
          ↥(FFModel.twistTensor 1 (StatedSL 3 K)).sec ⧸
            (FFModel.twistTensor 1 (StatedSL 3 K)).ker.subgroupOf
              (FFModel.twistTensor 1 (StatedSL 3 K)).sec) =
          (m' : ↥(FFModel.twistTensor 1 (StatedSL 3 K)).sec ⧸
            (FFModel.twistTensor 1 (StatedSL 3 K)).ker.subgroupOf
              (FFModel.twistTensor 1 (StatedSL 3 K)).sec) := by
        rw [← heq, hL, hu']
      have h4 : (⟨(FFModel.twistTensor 1 (StatedSL 3 K)).act γ (toAmbSec m'), hm'sec⟩ :
          ↥(FFModel.twistTensor 1 (StatedSL 3 K)).sec) = m' := by
        have h5 := QuotientGroup.eq.mp h3
        rw [show (FFModel.twistTensor 1 (StatedSL 3 K)).ker = ⊥ from rfl,
          Subgroup.bot_subgroupOf] at h5
        exact inv_mul_eq_one.mp (Subgroup.mem_bot.mp h5)
      exact congrArg Subtype.val h4
    have hrhoT : rhoT hK (γ : GL (Fin 3) K) = 1 := by
      apply MulEquiv.ext
      intro Y
      apply H.L3Nine.mat_injective
      rw [MulAut.one_apply]
      have h := hact_all (Y : ↥(FFModel.twistTensor 1 (StatedSL 3 K)).sec)
      have h2 : toAmb (rhoT hK (γ : GL (Fin 3) K) Y) = toAmb Y := by
        rw [← hact_eq γ Y]
        simpa [toAmb, toAmbSec] using h
      exact congrArg Multiplicative.toAdd h2
    have hg1 : rho hK g = 1 := by
      rw [show rho hK g = rhoT hK (SpecialLinearGroup.toGL g) from rfl, ← hγcoe]
      exact hrhoT
    exact hgne hg1
  have hord : orderOf b = 3 := orderOf_eq_prime hb3 hbne
  refine ⟨b, hbH, hord, ?_⟩
  have hbw_fix : b (b w * w⁻¹) = b w * w⁻¹ :=
    mem_fixV.mp (hZ hbw_mem) b hbH
  have hodd : Odd (orderOf (⟨b, hbH⟩ : ↥G)) := by
    rw [Subgroup.orderOf_mk b hbH, hord]
    norm_num
  have hc : G.subtype ⟨b, hbH⟩ (b w * w⁻¹) = b w * w⁻¹ := by
    simpa using hbw_fix
  have hmul : G.subtype ⟨b, hbH⟩ w = (b w * w⁻¹) * w := by
    change b w = (b w * w⁻¹) * w
    group
  have hW' : ∀ a : W, a * a = 1 := fun a => by
    rw [← pow_two]
    exact hW a
  have hfix := coprime_fix hW' hodd hc hmul
  simpa using hfix

theorem exists_order_three_fix_of_binaryNineTensor
    {W : Type} [CommGroup W]
    (hW : ∀ w : W, w ^ 2 = 1)
    {H : Subgroup (MulAut W)} {U Z : Subgroup W}
    (hmodel : BinaryNineTensor H U Z 1)
    (hZ : Z ≤ fixV H) (w : W) (hw : w ∈ U) :
    ∃ b ∈ H, orderOf b = 3 ∧ (b : MulAut W) w = w := by
  refine exists_order_three_fix_of_binaryNineTensor_aux hW hmodel hZ w hw ?_
  intro K _ _ _ hK X
  exact exists_order_three_fix_hermitian hK X

end CFSG.Quasithin
