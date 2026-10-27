module

public import CFSG.RankThree.PartTwo.Sec14.Item142L3Res2ProofU
import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.RankThree.PartTwo.Sec14.Item142L3ResProofGen

public section

namespace CFSG.RankThree.PartTwo.Sec14

open Matrix CFSG.RankThree.PartTwo.Sec4 CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.SeitzGeneration (heisC hS heisD homMat blockOneGL blockOneMat circMat)
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Assembly.LowTwoRank (StatedScalars)

@[expose] def KS142L3PGLGenStdUTwentySeven : Prop :=
  ∀ (p f : ℕ) (K : Type) [Field K] (hπ : false = false → UnitaryFieldData p f K),
    PiField false p f K → ModThree false (p ^ f) → (p ^ f % 27 = 26 ∨ p ^ f = 8) →
    Group.IsPerfect (projImage (slPi false 3 (p ^ f) K)) →
    ∀ (τ : K) (hτ : τ ^ 3 = 1), τ ≠ 1 → ∀ (β : K) (cβ : GL (Fin 3) K)
      (hcβ : cβ ∈ glPi false 3 (p ^ f) K) (hd : diagTau hτ ∈ glPi false 3 (p ^ f) K),
      (cβ : Matrix (Fin 3) (Fin 3) K) = heisC β → (¬ ∃ μ : K, μ ^ 3 = β) →
      sSup (invSet142 (Res8Hess.conjM' hπ hcβ) (Res8Hess.conjM' hπ hd)) = ⊤

namespace L3PGLU

variable {K : Type} [Field K]

theorem nine_mul_mU {q : ℕ} (h9 : q % 9 = 8) (h27 : q % 27 ≠ 26) : q + 1 = 9 * mU q := by
  have hn : q + 1 ≠ 0 := Nat.succ_ne_zero q
  have h1 : 2 ≤ (q + 1).factorization 3 :=
    (Nat.prime_three.pow_dvd_iff_le_factorization hn).mp (by norm_num; omega)
  have h2 : ¬ 3 ≤ (q + 1).factorization 3 := fun h =>
    h27 (by
      have := (Nat.prime_three.pow_dvd_iff_le_factorization hn).mpr h
      norm_num at this
      omega)
  have hf : (q + 1).factorization 3 = 2 := by omega
  have h3 : 3 ^ (q + 1).factorization 3 * mU q = q + 1 :=
    Nat.ordProj_mul_ordCompl_eq_self (q + 1) 3
  rw [hf] at h3
  norm_num at h3
  exact h3.symm

open CFSG.ClassicalGroups.UnitaryFlag CFSG.ClassicalInvolution.Phan in
theorem su_le_of_block_le {p f : ℕ} (h : UnitaryFieldData p f K) (hq : p ^ f ≠ 2)
    {Q : Subgroup (GL (Fin 3) K)} {β : K} (hβN : h.bar β * β = 1) {cβ : GL (Fin 3) K}
    (hcβm : (cβ : Matrix (Fin 3) (Fin 3) K) = heisC β) (hcQ : cβ ∈ Q)
    (hB : ∀ g : GL (Fin 2) K, g ∈ unitarySU p f K 2 → blockOneGL g ∈ Q) :
    ∀ x : GL (Fin 3) K, x ∈ unitarySU p f K 3 → x ∈ Q := by
  classical
  have hfin := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP K p := h.charP
  have hK : Nat.card K = (p ^ f) ^ 2 := h.card_eq_sq
  let ε : Su K p f 3 ≃* unitarySU p f K 3 :=
    MulEquiv.subgroupCongr (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hK 3)
  have hε : ∀ x : Su K p f 3, ((ε x : unitarySU p f K 3) : GL (Fin 3) K) = (x : GL (Fin 3) K) :=
    fun x => rfl
  have hmem2 : ∀ x : Su K p f 2, ((x : GL (Fin 2) K)) ∈ unitarySU p f K 2 := fun x => by
    exact (Subgroup.ext_iff.1 (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hK 2)
      (x : GL (Fin 2) K)).1 x.2
  have hβN' : β * h.bar β = 1 := by rw [mul_comm]; exact hβN
  have hcinv : ((cβ⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((heisC β).map h.bar)ᵀ := by
    have hU : ((heisC β).map h.bar)ᵀ * heisC β = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [heisC, Matrix.mul_apply, Fin.sum_univ_three, hβN]
    calc ((cβ⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
        = ((heisC β).map h.bar)ᵀ * heisC β * ((cβ⁻¹ : GL (Fin 3) K) :
            Matrix (Fin 3) (Fin 3) K) := by rw [hU, Matrix.one_mul]
      _ = ((heisC β).map h.bar)ᵀ := by
          rw [← hcβm, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
            Matrix.mul_one]
  have h0 : ∀ x : Su K p f 2, ((ε (blockEmb2 K p f 2 0 x) : unitarySU p f K 3) :
      GL (Fin 3) K) ∈ Q := fun x => by
    have e : ((ε (blockEmb2 K p f 2 0 x) : unitarySU p f K 3) : GL (Fin 3) K) =
        blockOneGL (x : GL (Fin 2) K) := by
      apply Units.ext
      rw [hε, blockEmb2, coe_coe_blockEmb, CFSG.LieType.SeitzGeneration.coe_blockOneGL]
      change blockMat 3 0 ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = _
      rw [CFSG.LieType.SeitzGeneration.blockMat_zero_eq]
    rw [e]
    exact hB _ (hmem2 x)
  have h1 : ∀ x : Su K p f 2, ((ε (blockEmb2 K p f 2 1 x) : unitarySU p f K 3) :
      GL (Fin 3) K) ∈ Q := fun x => by
    have e : ((ε (blockEmb2 K p f 2 1 x) : unitarySU p f K 3) : GL (Fin 3) K) =
        cβ * ((ε (blockEmb2 K p f 2 0 x) : unitarySU p f K 3) : GL (Fin 3) K) * cβ⁻¹ := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, hcinv, hcβm, hε, hε, blockEmb2, coe_coe_blockEmb,
        blockEmb2, coe_coe_blockEmb]
      change blockMat 3 1 ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
        heisC β * blockMat 3 0 ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
          ((heisC β).map h.bar)ᵀ
      rw [CFSG.LieType.SeitzGeneration.blockMat_one_eq,
        CFSG.LieType.SeitzGeneration.blockMat_zero_eq]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [heisC, hS, blockOneMat, Matrix.mul_apply, Fin.sum_univ_three, mul_comm, hβN']
    rw [e]
    exact Q.mul_mem (Q.mul_mem hcQ (h0 x)) (Q.inv_mem hcQ)
  have hgen : ⨆ i : Fin 2, (ε.toMonoidHom.comp (blockEmb2 K p f 2 i)).range = ⊤ := by
    have h1 := iSup_range_blockEmb2 (K := K) (p := p) (f := f) hK hq 2
    have h2 := congrArg (Subgroup.map ε.toMonoidHom) h1
    rw [Subgroup.map_iSup, Subgroup.map_top_of_surjective _ ε.surjective] at h2
    simpa [MonoidHom.range_comp] using h2
  have hle : (⊤ : Subgroup (unitarySU p f K 3)) ≤ Q.comap (unitarySU p f K 3).subtype := by
    rw [← hgen]
    refine iSup_le fun i => ?_
    rintro _ ⟨x, rfl⟩
    fin_cases i
    · exact h0 x
    · exact h1 x
  intro x hx
  exact hle (Subgroup.mem_top (⟨x, hx⟩ : unitarySU p f K 3))

section Nine

variable {p f : ℕ} [Finite K] (hπ : false = false → UnitaryFieldData p f K)
  (hK : PiField false p f K) (hq : ModThree false (p ^ f))
  {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {β : K} {cβ : GL (Fin 3) K}
  (hcβ : cβ ∈ glPi false 3 (p ^ f) K) (hd : diagTau hτ ∈ glPi false 3 (p ^ f) K)
  (hcβm : (cβ : Matrix (Fin 3) (Fin 3) K) = heisC β)

include hK hq hτ1 hcβm in
theorem genStdU_of_nine_two (h9 : p ^ f % 9 = 8)
    (h27 : p ^ f % 27 ≠ 26) (h17 : 17 ≤ p ^ f) (hβ : ¬ ∃ μ : K, μ ^ 3 = β) :
    sSup (invSet142 (Res8Hess.conjM' hπ hcβ) (Res8Hess.conjM' hπ hd)) = ⊤ := by
  have h := hπ rfl
  have hfin := finite_pgl (K := K)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact p.Prime := ⟨h.prime⟩
  set N := sSup (invSet142 (Res8Hess.conjM' hπ hcβ) (Res8Hess.conjM' hπ hd)) with hN
  set ρ := projOf (slPi false 3 (p ^ f) K) with hρ
  set Q := normGU hπ N with hQ
  have hq' : p ^ f % 3 = 2 := hq
  have hq3 : 3 ∣ p ^ f + 1 := by omega
  have hq2 : p ^ f ≠ 2 := by omega
  have hm9 := nine_mul_mU h9 h27
  have h3 : (3 : K) ≠ 0 := hK.three_ne_zero hq
  have hp3 : p ≠ 3 := by
    rintro rfl
    have h3f : 3 ∣ 3 ^ f := dvd_pow_self 3 (by have := hK.one_le; omega)
    omega
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    norm_num at hτ
  set τu : Kˣ := Units.mk0 τ hτ0 with hτu
  have hτu' : (τu : K) = τ := rfl
  have hβ0 : β ≠ 0 := by
    rintro rfl
    exact hβ ⟨0, by ring⟩
  have hβbar : h.bar β * β = 1 := by
    have hU := (mem_glPi_false h).mp hcβ
    have e := congrFun (congrFun hU 2) 2
    rw [hcβm] at e
    simpa [heisC, Matrix.mul_apply, Fin.sum_univ_three] using e
  have hβN : β ^ (p ^ f + 1) = 1 := by
    rw [pow_succ, ← h.bar_apply]
    exact hβbar
  have hcQ : cβ ∈ Q := cβ_mem_normGU hπ hτ hcβ hd
  have hdiag3 : ∀ x : Kˣ, x ^ (3 * mU (p ^ f)) = 1 → diagUnits 1 1 x ∈ Q := fun x hx =>
    diagUnits_mem_normGU hπ hK hq hτ hτ1 hcβ hd hcβm hx
  have hdiag1 : ∀ x : Kˣ, x ^ (3 * mU (p ^ f)) = 1 → diagUnits x 1 1 ∈ Q := by
    intro x hx
    rw [← conj_diagUnits_heisC hcβm 1 1 x]
    exact Q.mul_mem (Q.mul_mem hcQ (hdiag3 x hx)) (Q.inv_mem hcQ)
  have hscal : ∀ c : Kˣ, c ^ (p ^ f + 1) = 1 →
      Matrix.GeneralLinearGroup.scalar (Fin 3) c ∈ Q := fun c hc =>
    scalar_mem_normGU hπ ((scalar_mem_glPi_false_iff h c).mpr
      (by rw [← Units.val_pow_eq_pow_val, hc, Units.val_one]))
  obtain ⟨a, ha⟩ := CFSG.LieType.SeitzGeneration.exists_orderOf_eq h
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [orderOf_zero] at ha
    omega
  set au : Kˣ := Units.mk0 a ha0 with hau
  have hau' : (au : K) = a := rfl
  have haq : au ^ (p ^ f + 1) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hau', Units.val_one, ← ha]
    exact pow_orderOf_eq_one a
  set x : Kˣ := au⁻¹ ^ 3 with hxdef
  have hx : x ^ (3 * mU (p ^ f)) = 1 := by
    rw [hxdef, ← pow_mul, show 3 * (3 * mU (p ^ f)) = p ^ f + 1 by omega, inv_pow, haq, inv_one]
  have hxa : (x : K) = a⁻¹ ^ 2 * a⁻¹ := by
    rw [hxdef, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, hau', pow_succ]
  have hH1 : ∃ g ∈ Q, (g : Matrix (Fin 3) (Fin 3) K) = homMat h a (a⁻¹ ^ 2 - a) ![1, 0, 0] := by
    refine ⟨Matrix.GeneralLinearGroup.scalar (Fin 3) au * diagUnits x 1 1,
      Q.mul_mem (hscal au haq) (hdiag1 x hx), ?_⟩
    rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, coe_diagUnits, hau', hxa]
    ext i j
    rw [CFSG.LieType.SeitzGeneration.homMat_apply]
    fin_cases i <;> fin_cases j <;> simp
    all_goals field_simp
  have hH3 : ∃ g ∈ Q, (g : Matrix (Fin 3) (Fin 3) K) = homMat h a (a⁻¹ ^ 2 - a) ![0, 0, 1] := by
    refine ⟨Matrix.GeneralLinearGroup.scalar (Fin 3) au * diagUnits 1 1 x,
      Q.mul_mem (hscal au haq) (hdiag3 x hx), ?_⟩
    rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, coe_diagUnits, hau', hxa]
    ext i j
    rw [CFSG.LieType.SeitzGeneration.homMat_apply]
    fin_cases i <;> fin_cases j <;> simp
    all_goals field_simp
  have hprim : IsPrimitiveRoot τ 3 := by
    have ho : orderOf τ = 3 := orderOf_eq_prime hτ hτ1
    rw [← ho]
    exact IsPrimitiveRoot.orderOf τ
  obtain ⟨y, -, c₀, c₁, c₂, hcirc, hc0, hc1, hc2, hnot⟩ :=
    CFSG.LieType.SeitzGeneration.exists_generic_element h hq3 hq2 hprim hβN hβ
  set y' : slPi false 3 (p ^ f) K := ⟨(y : GL (Fin 3) K), y.2⟩ with hy'
  have hyT : y' ∈ torusU false p f K cβ := by
    rw [mem_torusU]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hcβm]
    change heisC β * ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * heisC β
    rw [hcirc]
    exact (CFSG.LieType.SeitzGeneration.circMat_comm β c₀ c₁ c₂).symm
  have hL3 : ((cβ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 3 = β • 1 := by
    rw [hcβm]
    exact L3PGL.heisC_pow_three β
  have hT1 : cβ * cβ * cβ⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 3) 1 * cβ := by
    rw [map_one, one_mul, mul_inv_cancel_right]
  have hT2 : diagTau hτ * cβ * (diagTau hτ)⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin 3) τu * cβ :=
    conj_eq_scalar_mul (by rw [hτu', hcβm]; exact L3PGL.diagTau_mul_heisC hτ β)
  have hTN : (torusU false p f K cβ).map ρ ≤ N :=
    le_sSup (torusU_mem_invSet142 hπ hτ hτ1 h3 hcβ hd hL3 hβ hT1 hT2)
  have hρyN : ρ y' ∈ N := hTN ⟨y', hyT, rfl⟩
  have hyQ : (y : GL (Fin 3) K) ∈ Q := mem_normGU_of_projOf_mem hπ (x := y') hρyN
  have hkey : ∀ z : GL (Fin 3) K, z ∈ Q → z ∈ glPi false 3 (p ^ f) K →
      ((z : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 0, 1]) 0 ≠ 0 →
      ((z : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 0, 1]) 1 ≠ 0 →
      ((z : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 0, 1]) 2 ≠ 0 →
      h.bar (((z : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 0, 1]) 2) *
        ((z : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 0, 1]) 2 ≠ 1 →
      ∀ g : GL (Fin 2) K, g ∈ CFSG.ClassicalGroups.UnitaryFlag.unitarySU p f K 2 →
        blockOneGL g ∈ Q := by
    intro z hzQ hzU hw0 hw1 hw2 hn2
    have hzU' := (mem_glPi_false h).mp hzU
    have hzP : (z : Matrix (Fin 3) (Fin 3) K) * ((z : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ = 1 :=
      mul_eq_one_comm.2 hzU'
    have hwN : h.bar (((z : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 0, 1]) 0) *
        ((z : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 0, 1]) 0 +
        h.bar (((z : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 0, 1]) 1) *
        ((z : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 0, 1]) 1 +
        h.bar (((z : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 0, 1]) 2) *
        ((z : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 0, 1]) 2 = 1 := by
      have := congrFun (congrFun hzU' 2) 2
      simpa [Matrix.mul_apply, Fin.sum_univ_three, Matrix.mulVec, dotProduct] using this
    obtain ⟨g₃, hg₃Q, hg₃m⟩ := hH3
    have hconj : (((z * g₃ * z⁻¹ : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) =
        homMat h a (a⁻¹ ^ 2 - a) ((z : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 0, 1]) := by
      have hzinv : ((z⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
          ((z : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ := by
        calc ((z⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
            = ((z : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ * (z : Matrix (Fin 3) (Fin 3) K) *
                ((z⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
              rw [hzU', Matrix.one_mul]
          _ = ((z : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ := by
              rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
                Matrix.mul_one]
      rw [Units.val_mul, Units.val_mul, hzinv, hg₃m]
      exact CFSG.LieType.SeitzGeneration.conj_homMat h _ hzP
    exact CFSG.LieType.SeitzGeneration.su2_block_mem_of_generic h hp3 h17 hq3 ha Q hH1
      ⟨g₃, hg₃Q, hg₃m⟩ hwN hw0 hw1 hw2
      (by intro h0; apply hn2; linear_combination hwN - h0)
      ⟨z * g₃ * z⁻¹, Q.mul_mem (Q.mul_mem hzQ hg₃Q) (Q.inv_mem hzQ), hconj⟩
  have hyU : (y : GL (Fin 3) K) ∈ glPi false 3 (p ^ f) K := slPi_le_glPi hπ y'.2
  have hC2 : heisC β *ᵥ ![0, 0, 1] = (![β, 0, 0] : Fin 3 → K) := by
    ext i
    fin_cases i <;> simp [heisC, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have hC0 : heisC β *ᵥ ![β, 0, 0] = (![0, β, 0] : Fin 3 → K) := by
    ext i
    fin_cases i <;> simp [heisC, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have hy0 : circMat β c₀ c₁ c₂ *ᵥ ![β, 0, 0] = ![β * c₀, β * c₁, β * c₂] := by
    ext i
    fin_cases i <;> simp [circMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring
  have hy1 : circMat β c₀ c₁ c₂ *ᵥ ![0, β, 0] = ![β * (β * c₂), β * c₀, β * c₁] := by
    ext i
    fin_cases i <;> simp [circMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring
  have hy2 : circMat β c₀ c₁ c₂ *ᵥ ![0, 0, 1] = ![β * c₁, β * c₂, c₀] := by
    ext i
    fin_cases i <;> simp [circMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have hym : ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = circMat β c₀ c₁ c₂ := hcirc
  have hNβ : ∀ c : K, h.bar (β * c) * (β * c) = h.bar c * c := by
    intro c
    rw [map_mul]
    linear_combination (h.bar c * c) * hβbar
  have hB : ∀ g : GL (Fin 2) K, g ∈ CFSG.ClassicalGroups.UnitaryFlag.unitarySU p f K 2 →
      blockOneGL g ∈ Q := by
    by_cases hn2 : h.bar c₂ * c₂ = 1
    · by_cases hn1 : h.bar c₁ * c₁ = 1
      · have hn0 : h.bar c₀ * c₀ ≠ 1 := fun h0 => hnot ⟨h0, hn1, hn2⟩
        have hw : ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 0, 1] =
            ![β * c₁, β * c₂, c₀] := by rw [hym, hy2]
        refine hkey (y : GL (Fin 3) K) hyQ hyU ?_ ?_ ?_ ?_
        · rw [hw]; simp [hβ0, hc1]
        · rw [hw]; simp [hβ0, hc2]
        · rw [hw]; simpa using hc0
        · rw [hw]; simpa using hn0
      · have hw : (((y : GL (Fin 3) K) * cβ * cβ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
            ![0, 0, 1] = ![β * (β * c₂), β * c₀, β * c₁] := by
          rw [Units.val_mul, Units.val_mul, hym, hcβm, ← Matrix.mulVec_mulVec,
            ← Matrix.mulVec_mulVec, hC2, hC0, hy1]
        refine hkey _ (Q.mul_mem (Q.mul_mem hyQ hcQ) hcQ) (mul_mem (mul_mem hyU hcβ) hcβ)
          ?_ ?_ ?_ ?_
        · rw [hw]; simp [hβ0, hc2]
        · rw [hw]; simp [hβ0, hc0]
        · rw [hw]; simp [hβ0, hc1]
        · rw [hw]
          change h.bar (β * c₁) * (β * c₁) ≠ 1
          rw [hNβ]
          exact hn1
    · have hw : (((y : GL (Fin 3) K) * cβ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
          ![0, 0, 1] = ![β * c₀, β * c₁, β * c₂] := by
        rw [Units.val_mul, hym, hcβm, ← Matrix.mulVec_mulVec, hC2, hy0]
      refine hkey _ (Q.mul_mem hyQ hcQ) (mul_mem hyU hcβ) ?_ ?_ ?_ ?_
      · rw [hw]; simp [hβ0, hc0]
      · rw [hw]; simp [hβ0, hc1]
      · rw [hw]; simp [hβ0, hc2]
      · rw [hw]
        change h.bar (β * c₂) * (β * c₂) ≠ 1
        rw [hNβ]
        exact hn2
  have hSU := su_le_of_block_le h hq2 hβbar hcβm hcQ hB
  have hnorm : N.Normal := by
    refine ⟨fun n hn m => ?_⟩
    obtain ⟨z, rfl⟩ := projOf_surjective _ m
    have hzQ := hSU (z : GL (Fin 3) K) z.2
    have hmap := map_le_of_mem_normGU hπ (slPi_le_glPi hπ z.2) hzQ
    rw [conjM'_eq_conj hπ z] at hmap
    exact hmap ⟨n, hn, rfl⟩
  have hsimple : IsSimpleGroup (projImage (slPi false 3 (p ^ f) K)) := by
    have hK2 : Nat.card K = (p ^ f) ^ 2 := h.card_eq_sq
    have hs := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K p f hK2 3 le_rfl
      (by intro e; exact hq2 (Prod.ext_iff.mp e).2)
    exact (Sec4.Census.statedProjEquivProjImage
      (CFSG.Assembly.LowTwoRank.StatedSU 3 (p ^ f) K)
      (P := projImage (slPi false 3 (p ^ f) K)) rfl).symm.isSimpleGroup
  have hy1 : ρ y' ≠ 1 := by
    intro e
    rw [projOf_eq_one_iff] at e
    obtain ⟨t, ht⟩ := e
    have h10 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 1 0) ht
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at h10
    rw [Matrix.diagonal_apply_ne _ (by decide)] at h10
    have hy10 : ((y' : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 0 = c₁ := by
      change ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 0 = c₁
      rw [hym]
      rfl
    rw [hy10] at h10
    exact hc1 h10.symm
  have := hnorm
  have := hsimple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hbot | htop
  · exact absurd (hbot ▸ hρyN : ρ y' ∈ (⊥ : Subgroup _)) (by
      rw [Subgroup.mem_bot]
      exact hy1)
  · exact htop

end Nine

end L3PGLU

theorem ks142L3PGLGenStdUNine_of_27
    (h27 : KS142L3PGLGenStdUTwentySeven) : KS142L3PGLGenStdUNine := by
  intro p f K _ hπ hK hq h9 hperf τ hτ hτ1 β cβ hcβ hd hcβm hβ
  by_cases hc : p ^ f % 27 = 26 ∨ p ^ f = 8
  · exact h27 p f K hπ hK hq hc hperf τ hτ hτ1 β cβ hcβ hd hcβm hβ
  · push Not at hc
    have := hK.finite
    have h17 : 17 ≤ p ^ f := by omega
    exact L3PGLU.genStdU_of_nine_two hπ hK hq hτ hτ1 hcβ hd hcβm h9 hc.1 h17 hβ

theorem ks142L3PGLGenStdU_of_27
    (h27 : KS142L3PGLGenStdUTwentySeven) : KS142L3PGLGenStdU :=
  ks142L3PGLGenStdU_of_nine (ks142L3PGLGenStdUNine_of_27 h27)

theorem step142LowerGenL3PGL_of_27
    (h27 : KS142L3PGLGenStdUTwentySeven) : Step142LowerGenL3PGL :=
  step142LowerGenL3PGL_of_U (ks142L3PGLGenStdU_of_27 h27)

end CFSG.RankThree.PartTwo.Sec14
