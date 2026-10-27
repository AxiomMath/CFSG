module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148WL3CentGen
public import CFSG.RankThree.PartTwo.Sec14.Ronan148WL3CentU38Block
import CFSG.RankThree.PartTwo.Sec14.Ronan148WL3CentMat
import CFSG.RankThree.PartTwo.Sec14.Ronan148WL3CentCases
import CFSG.RankThree.PartTwo.Sec14.Ronan148WL3CentBlock
import CFSG.RankThree.PartTwo.Sec14.Ronan148WL3CentU38Mono
import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes
import CFSG.RankThree.PartTwo.Sec4.RonanK432Sylow
import CFSG.RankThree.PartTwo.Sec12.ONanKS128Diag
import CFSG.Open.SplitBNPair
import CFSG.Quasithin.Vol2.Ch10StatementsE
import CFSG.Quasithin.Vol2.Ch10StatementsInputs
import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
import CFSG.RankThree.PartTwo.Sec11.Inverter1118Proof
import CFSG.RankThree.PartTwo.Sec11.Inverter1118ProofSteps
import CFSG.RankThree.PartTwo.Sec11.Item1121Proof
import CFSG.RankThree.PartTwo.Sec11.Item119K
import CFSG.RankThree.PartTwo.Sec14.Item142ResProofPGL
import CFSG.RankThree.PartTwo.Sec20.OneSteps
import CFSG.RankThree.PartTwo.Sec21.Item211ProofListOf
import CFSG.RankThree.PartTwo.Sec4.Item423ResProof432
import CFSG.RankThree.PartTwo.Sec4.RonanK432Transport
import Certificates.Certificate8166

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148W

open CFSG CFSG.RankThree.PartTwo.Sec4 Matrix CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.RankThreeEven (projImage)

local notation "pmk" => Matrix.ProjGenLinGroup.mk

variable {K : Type} [Field K]

@[expose] noncomputable def blockOne {p f : ℕ} {h : UnitaryFieldData p f K}
    (X : TrOne h) : GL (Fin 3) K :=
  GeneralLinearGroup.mkOfDetNeZero (blockMat 1 (X : Matrix (Fin 2) (Fin 2) K)) (by
    rw [det_blockMat, one_mul, X.2.2.1]
    exact one_ne_zero)

theorem coe_blockOne {p f : ℕ} {h : UnitaryFieldData p f K} (X : TrOne h) :
    ((blockOne X : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      blockMat 1 (X : Matrix (Fin 2) (Fin 2) K) :=
  GeneralLinearGroup.val_mkOfDetNeZero _ _

theorem blockOne_mem_slPi {p f : ℕ} {h : UnitaryFieldData p f K} (X : TrOne h) :
    blockOne X ∈ slPi false 3 (p ^ f) K := by
  rw [mem_slPi_false h, coe_blockOne, det_blockMat, one_mul, blockMat_map _ (map_zero _),
    blockMat_transpose, blockMat_mul, map_one, one_mul, X.2.1, blockMat_one]
  exact ⟨X.2.2.1, rfl⟩

@[expose] def lowerBlock (A : Matrix (Fin 3) (Fin 3) K) : Matrix (Fin 2) (Fin 2) K :=
  !![A 1 1, A 1 2; A 2 1, A 2 2]

theorem eq_blockMat {A : Matrix (Fin 3) (Fin 3) K} (h01 : A 0 1 = 0) (h02 : A 0 2 = 0)
    (h10 : A 1 0 = 0) (h20 : A 2 0 = 0) : A = blockMat (A 0 0) (lowerBlock A) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockMat, lowerBlock, h01, h02, h10, h20]

theorem bar_frob_comm (h : UnitaryFieldData 2 3 K) {σ : K ≃+* K} {N : ℕ} (hσ : ∀ c, σ c = c ^ N)
    (c : K) : h.bar (σ c) = σ (h.bar c) := by
  rw [h.bar_apply, h.bar_apply, hσ, hσ, ← pow_mul, ← pow_mul, mul_comm]

variable {ι : Type*} {α : ι → MulAut (projImage (slPi false 3 (2 ^ 3) K))}
  {e₀ : projImage (slPi false 3 (2 ^ 3) K)}

theorem CentConfig.false_of_field_block (hK : PiField false 2 3 K)
    (hc : CentConfig false 2 3 K α e₀) {ε : Kˣ} (hε3 : (ε : K) ^ 3 = 1) (hε1 : ε ≠ 1)
    (he₀ : (e₀ : ProjGenLinGroup (Fin 3) K) = pmk (diagE ε))
    {γ : MulAut (projImage (slPi false 3 (2 ^ 3) K))} (hγ3 : γ ^ 3 = 1) (hγe : γ e₀ = e₀)
    (hgen : ∀ x, α x ∈ Subgroup.zpowers (MulAut.conj e₀) ⊔ Subgroup.zpowers γ)
    {σ : K ≃+* K} {N : ℕ} (hN : N = 4 ∨ N = 16) (hσ : ∀ c, σ c = c ^ N) {g : GL (Fin 3) K}
    (hgH : g ∈ glPi false 3 (2 ^ 3) K)
    (hγ : ∀ s (hs : s ∈ slPi false 3 (2 ^ 3) K),
      (γ (projOf _ ⟨s, hs⟩) : ProjGenLinGroup (Fin 3) K) = pmk (g * frobGL σ s * g⁻¹)) :
    False := by
  have hU := hK.unitary
  have := hK.finite
  haveI : CharP K 2 := hK.charP
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hq : ModThree false (2 ^ 3) := rfl
  have hε1' : (ε : K) ≠ 1 := fun h => hε1 (Units.ext h)
  obtain ⟨s₀, hs₀, hs₀e⟩ := exists_lift e₀
  obtain ⟨c, hc'⟩ := exists_frob_conj_eq_scalar_mul hγ hγe hs₀ hs₀e
  have hστ : σ (ε : K) = ε := by
    rw [hσ]
    rcases hN with rfl | rfl
    · rw [show 4 = 3 + 1 from rfl, pow_add, hε3, one_mul, pow_one]
    · rw [show 16 = 3 * 5 + 1 from rfl, pow_add, pow_mul, hε3, one_pow, one_mul, pow_one]
  have hg := commute_diagE_of_frob hK hq hε3 hστ (hs₀e.symm.trans he₀) hc'
  obtain ⟨g01, g02, g10, g20⟩ := entries_of_commute_diagE hε1 hg
  have hgi : g⁻¹ * diagE ε = diagE ε * g⁻¹ := by
    calc g⁻¹ * diagE ε = g⁻¹ * (diagE ε * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * diagE ε) * g⁻¹ := by rw [hg]
      _ = diagE ε * g⁻¹ := by group
  obtain ⟨i01, i02, i10, i20⟩ := entries_of_commute_diagE hε1 hgi
  set G := (g : Matrix (Fin 3) (Fin 3) K) with hG
  set Gi := ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hGi
  have hGb := eq_blockMat g01 g02 g10 g20
  have hGib := eq_blockMat i01 i02 i10 i20
  set B := lowerBlock G with hB
  set B' := lowerBlock Gi with hB'
  have hGGi : blockMat (G 0 0 * Gi 0 0) (B * B') = 1 := by
    rw [← blockMat_mul, ← hGb, ← hGib, hG, hGi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hGiG : blockMat (Gi 0 0 * G 0 0) (B' * B) = 1 := by
    rw [← blockMat_mul, ← hGb, ← hGib, hG, hGi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hblock1 : ∀ {x : K} {M : Matrix (Fin 2) (Fin 2) K}, blockMat x M = 1 → x = 1 ∧ M = 1 := by
    intro x M hxM
    refine ⟨by simpa [blockMat] using congrFun (congrFun hxM 0) 0, ?_⟩
    ext i j
    have := congrFun (congrFun hxM i.succ) j.succ
    fin_cases i <;> fin_cases j <;> simpa [blockMat] using this
  obtain ⟨ha1, hBB'⟩ := hblock1 hGGi
  obtain ⟨-, hB'B⟩ := hblock1 hGiG
  have hgu := (mem_glPi_false hU).mp hgH
  have hgiu := (mem_glPi_false hU).mp (inv_mem hgH)
  rw [← hG, hGb, blockMat_map _ (map_zero _), blockMat_transpose, blockMat_mul] at hgu
  rw [← hGi, hGib, blockMat_map _ (map_zero _), blockMat_transpose, blockMat_mul] at hgiu
  have hBu : (B.map hU.bar)ᵀ * B = 1 := (hblock1 hgu).2
  have hB'u : (B'.map hU.bar)ᵀ * B' = 1 := (hblock1 hgiu).2
  have hFmem : ∀ X : TrOne hU, B * (X : Matrix (Fin 2) (Fin 2) K).map σ * B' ∈ TrOne hU := by
    intro X
    obtain ⟨hXu, hXd, hXt⟩ := X.2
    have hσX : (((X : Matrix (Fin 2) (Fin 2) K).map σ).map hU.bar)ᵀ *
        (X : Matrix (Fin 2) (Fin 2) K).map σ = 1 := by
      have hc : ((X : Matrix (Fin 2) (Fin 2) K).map σ).map hU.bar =
          ((X : Matrix (Fin 2) (Fin 2) K).map hU.bar).map σ := by
        ext i j
        simp only [Matrix.map_apply, bar_frob_comm hU hσ]
      rw [hc, ← Matrix.transpose_map, ← Matrix.map_mul, hXu, Matrix.map_one _ (map_zero σ)
        (map_one σ)]
    refine ⟨?_, ?_, ?_⟩
    · rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul]
      calc (B'.map hU.bar)ᵀ * ((((X : Matrix (Fin 2) (Fin 2) K).map σ).map hU.bar)ᵀ *
            (B.map hU.bar)ᵀ) * (B * (X : Matrix (Fin 2) (Fin 2) K).map σ * B') =
          (B'.map hU.bar)ᵀ * ((((X : Matrix (Fin 2) (Fin 2) K).map σ).map hU.bar)ᵀ *
            ((B.map hU.bar)ᵀ * B) * (X : Matrix (Fin 2) (Fin 2) K).map σ) * B' := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hBu, Matrix.mul_one, hσX, Matrix.mul_one, hB'u]
    · have hdσ : ((X : Matrix (Fin 2) (Fin 2) K).map σ).det = σ (X : Matrix (Fin 2) (Fin 2) K).det :=
        (RingHom.map_det (σ : K →+* K) _).symm
      rw [det_mul, det_mul, hdσ, hXd, map_one, mul_one, ← det_mul, hBB', det_one]
    · rw [Matrix.trace_mul_cycle, hB'B, Matrix.one_mul, Matrix.trace]
      have : ∑ i, ((X : Matrix (Fin 2) (Fin 2) K).map σ).diag i =
          σ (∑ i, (X : Matrix (Fin 2) (Fin 2) K).diag i) := by
        rw [map_sum]
        rfl
      rw [this]
      change σ (X : Matrix (Fin 2) (Fin 2) K).trace = 1
      rw [hXt, map_one]
  let F : TrOne hU → TrOne hU := fun X => ⟨_, hFmem X⟩
  have hγF : ∀ X : TrOne hU, γ (projOf _ ⟨blockOne X, blockOne_mem_slPi X⟩) =
      projOf _ ⟨blockOne (F X), blockOne_mem_slPi (F X)⟩ := by
    intro X
    apply Subtype.ext
    rw [hγ, coe_projOf]
    congr 1
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_frobGL, coe_blockOne, coe_blockOne, ← hG, ← hGi, hGb,
      hGib, blockMat_map _ (map_zero σ), map_one, blockMat_mul, blockMat_mul, mul_one, ha1]
  have hinj : ∀ X Y : TrOne hU, projOf (slPi false 3 (2 ^ 3) K) ⟨blockOne X, blockOne_mem_slPi X⟩ =
      projOf _ ⟨blockOne Y, blockOne_mem_slPi Y⟩ → X = Y := by
    intro X Y hXY
    have h1 := congrArg Subtype.val hXY
    rw [coe_projOf, coe_projOf] at h1
    obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp h1
    have h00 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 0 0) hu
    simp [coe_blockOne, blockMat, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.mul_apply, Fin.sum_univ_three] at h00
    rw [h00, map_one, mul_one] at hu
    apply Subtype.ext
    ext i j
    have := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) i.succ j.succ) hu
    simp only [coe_blockOne] at this
    fin_cases i <;> fin_cases j <;> simpa [blockMat] using this
  have hF3 : ∀ X, F (F (F X)) = X := by
    intro X
    apply hinj
    have := congrArg (fun β : MulAut (projImage (slPi false 3 (2 ^ 3) K)) =>
      β (projOf _ ⟨blockOne X, blockOne_mem_slPi X⟩)) hγ3
    simp only [MulAut.one_apply] at this
    rw [_root_.pow_three γ, MulAut.mul_apply, MulAut.mul_apply, hγF, hγF, hγF] at this
    exact this
  classical
  have := Fintype.ofFinite (TrOne hU)
  let Fp : Equiv.Perm (TrOne hU) := ⟨F, fun X => F (F X), fun X => hF3 X, fun X => hF3 X⟩
  have hFp : Fp ^ 3 ^ 1 = 1 := by
    apply Equiv.ext
    intro X
    rw [pow_one, Equiv.Perm.coe_pow, Equiv.Perm.one_apply]
    exact hF3 X
  have hcard := not_three_dvd_card_trOne hU hε3 hε1'
  rw [Nat.card_eq_fintype_card] at hcard
  obtain ⟨X₀, hX₀⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 3) (n := 1)
    (hp := ⟨Nat.prime_three⟩) hcard hFp
  set w : projImage (slPi false 3 (2 ^ 3) K) :=
    projOf _ ⟨blockOne X₀, blockOne_mem_slPi X₀⟩ with hwdef
  have hFX : F X₀ = X₀ := hX₀
  have hw2 : γ w = w := by rw [hwdef, hγF, hFX]
  have hw1 : MulAut.conj e₀ w = w := Subtype.ext (by
    rw [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, he₀, hwdef,
      coe_projOf, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    have hcomm : diagE ε * blockOne X₀ = blockOne X₀ * diagE ε := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, coe_blockOne, coe_diagE]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [blockMat, Matrix.mul_apply, Fin.sum_univ_three,
        Matrix.diagonal]
    rw [hcomm, mul_inv_cancel_right])
  have hfix : ∀ x, α x w = w := fun x => fixed_of_mem_sup hw1 hw2 (hgen x)
  have hX3 : (X₀ : Matrix (Fin 2) (Fin 2) K) ^ 3 = 1 := TrOne.pow_three X₀.2
  have hb3 : blockOne X₀ ^ 3 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, coe_blockOne, pow_three', blockMat_mul, blockMat_mul, mul_one,
      mul_one, ← pow_three', hX3, blockMat_one, Units.val_one]
  have hw3 : w ^ 3 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, hwdef, coe_projOf, ← map_pow, hb3, map_one]
    rfl)
  have hmem := hc.hF3 w hw3 hfix
  have he₀3 : e₀ ^ 3 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, he₀, ← map_pow, diagE_pow_three hε3, map_one]; rfl)
  have hnot : ∀ (e' : Kˣ), pmk (blockOne X₀) ≠ pmk (diagE e') := by
    intro e' h
    obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp h
    have h11 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 1 1) hu
    have h22 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 2 2) hu
    simp [coe_blockOne, coe_diagE, blockMat, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal] at h11 h22
    obtain ⟨-, -, htr⟩ := X₀.2
    rw [Matrix.trace_fin_two] at htr
    have hu1 : (X₀ : Matrix (Fin 2) (Fin 2) K) 0 0 * (u : K) = 1 := h11
    have hu2 : (X₀ : Matrix (Fin 2) (Fin 2) K) 1 1 * (u : K) = 1 := h22
    have hu0 : (u : K) ≠ 0 := u.ne_zero
    have heq : (X₀ : Matrix (Fin 2) (Fin 2) K) 0 0 = (X₀ : Matrix (Fin 2) (Fin 2) K) 1 1 :=
      mul_right_cancel₀ hu0 (hu1.trans hu2.symm)
    rw [heq] at htr
    have : (1 : K) = 0 := by rw [← htr]; linear_combination (X₀ : Matrix (Fin 2) (Fin 2) K) 1 1 * h2
    exact one_ne_zero this
  rcases RonanK432.mem_zpowers_cases_of_pow_three he₀3 hmem with h | h | h
  · apply hnot 1
    have h' := congrArg Subtype.val h
    rw [hwdef, coe_projOf, Subgroup.coe_one] at h'
    rw [h', diagE, Sec12.KS128Move.diagUnits_one, map_one]
  · apply hnot ε
    have h' := congrArg Subtype.val h
    rw [hwdef, coe_projOf, he₀] at h'
    exact h'
  · apply hnot ε⁻¹
    have h' := congrArg Subtype.val h
    rw [hwdef, coe_projOf, Subgroup.coe_inv, he₀, ← map_inv, diagE, Sec12.KS128Move.diagUnits_inv,
      inv_one] at h'
    exact h'

end CFSG.RankThree.PartTwo.Sec14.Ronan148W
