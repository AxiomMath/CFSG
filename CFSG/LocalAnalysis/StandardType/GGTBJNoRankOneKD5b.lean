module

public import CFSG.LocalAnalysis.StandardType.GGTBJNoRankOneDefs
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormDeterminant
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherIsotropicRadical
public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitarySemi
public import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSU
public import CFSG.LocalAnalysis.StandardType.GGInndiagNormalOtherUnitary
public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitaryOutdiag
public import CFSG.LocalAnalysis.StandardType.GGRootDetectSU
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import Certificates.Certificate1
public import Certificates.Certificate2

public section

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open Matrix

private noncomputable abbrev ltrkd5b_inner (G : Type*) [Group G] : Subgroup (MulAut G) :=
  CFSG.ComponentClassification.OuterAutomorphisms.inner G

private theorem ltrkd5b_primeForm_inner
    {K : Type} [Field K] [Finite K] [CharP K 2] {n f : ℕ} (h : UnitaryFieldData 2 f K)
    (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ 2 ^ f = 2))
    {t v : MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))}
    (htD : t ∈ primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (ht3 : t ^ 3 = 1)
    (hv : primeFormFieldFactor h (isPrimeFormGram_one (K := K) (n := n)) hn hq v =
      CFSG.LieType.BorelTits.unitaryInvolution K 2 f)
    (hcomm : t * v = v * t) :
    t ∈ ltrkd5b_inner (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  classical
  let hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  obtain ⟨-, -, -, -, huniq, hffapply, -, -, -, -, -⟩ :=
    unitary_prime_form_full_semilinear_realization h hC hn hq
  obtain ⟨φ, ⟨N, hN⟩, -⟩ := huniq v
  have hφ : φ = CFSG.LieType.BorelTits.unitaryInvolution K 2 f := by
    rw [← hffapply N φ, ← hN, hv]
  have hcomm' : t * (primeFormConjHom h _ N *
      primeFormFieldHom h hC (CFSG.LieType.BorelTits.unitaryInvolution K 2 f)) =
      (primeFormConjHom h _ N *
        primeFormFieldHom h hC (CFSG.LieType.BorelTits.unitaryInvolution K 2 f)) * t := by
    rw [← hφ, ← hN]
    exact hcomm
  obtain ⟨M, htM⟩ := htD
  set σ : K ≃+* K := CFSG.LieType.BorelTits.unitaryInvolution K 2 f with hσ
  set cM : MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
    primeFormConjHom h _ M with hcM
  set cN : MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
    primeFormConjHom h _ N with hcN
  set fσ : MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
    primeFormFieldHom h hC σ with hfσ
  have hconjσ : fσ * cM * fσ⁻¹ = primeFormConjHom h _ (primeFormFieldU h hC σ M) := by
    rw [hfσ, hcM]
    exact primeFormField_conj_eq h hC σ M
  have hfσcM : fσ * cM =
      primeFormConjHom h _ (primeFormFieldU h hC σ M) * fσ := by
    rw [← hconjσ]
    group
  have hMN : cM * cN = cN * primeFormConjHom h _ (primeFormFieldU h hC σ M) := by
    have h1 : cM * cN * fσ = cN * primeFormConjHom h _ (primeFormFieldU h hC σ M) * fσ := by
      calc cM * cN * fσ = cM * (cN * fσ) := by group
        _ = (cN * fσ) * cM := by simpa only [← htM] using hcomm'
        _ = cN * (fσ * cM) := by group
        _ = cN * (primeFormConjHom h _ (primeFormFieldU h hC σ M) * fσ) := by rw [hfσcM]
        _ = cN * primeFormConjHom h _ (primeFormFieldU h hC σ M) * fσ := by group
    exact mul_right_cancel h1
  have h4 : cM = primeFormConjHom h _ (N * primeFormFieldU h hC σ M * N⁻¹) := by
    have h3 : cM = cN * primeFormConjHom h _ (primeFormFieldU h hC σ M) * cN⁻¹ := by
      have hh := congrArg (fun x => x * cN⁻¹) hMN
      simpa only [mul_assoc, mul_inv_cancel, mul_one] using hh
    rw [h3, hcN, map_mul, map_mul, map_inv]
  have hX : primeFormConjHom h _ (M * (N * primeFormFieldU h hC σ M * N⁻¹)⁻¹) = 1 := by
    rw [map_mul, map_inv, ← hcM, h4, mul_inv_cancel]
  obtain ⟨c₀, hc₀N, hc₀X⟩ := eq_scalar_of_primeFormConjHom_eq_one h hC hn hX
  have hM3 : primeFormConjHom h _ (M ^ 3) = 1 := by
    rw [map_pow, ← hcM, htM, ht3]
  obtain ⟨c', hc'N, hc'M3⟩ := eq_scalar_of_primeFormConjHom_eq_one h hC hn hM3
  set XN : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    N * primeFormFieldU h hC σ M * N⁻¹ with hXN
  have hdetXN : GeneralLinearGroup.det (XN : GL (Fin n) K) =
      Units.map ((σ : K →+* K) : K →* K) (GeneralLinearGroup.det (M : GL (Fin n) K)) := by
    rw [hXN]
    rw [show ((N * primeFormFieldU h hC σ M * N⁻¹ :
        primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) : GL (Fin n) K) =
        (N : GL (Fin n) K) * (primeFormFieldU h hC σ M : GL (Fin n) K) * (N : GL (Fin n) K)⁻¹
      from rfl]
    rw [map_mul, map_mul, map_inv, coe_primeFormFieldU]
    rw [CFSG.GH74.Generic.BProg.B2.T4.T4OutCore.det_glAut]
    rw [mul_comm (GeneralLinearGroup.det (N : GL (Fin n) K))
        (Units.map ((σ : K →+* K) : K →* K) (GeneralLinearGroup.det (M : GL (Fin n) K))),
      mul_assoc, mul_inv_cancel, mul_one]
  have hdetX : GeneralLinearGroup.det (M : GL (Fin n) K) *
      (Units.map ((σ : K →+* K) : K →* K) (GeneralLinearGroup.det (M : GL (Fin n) K)))⁻¹ =
      c₀ ^ n := by
    have hh := congrArg (GeneralLinearGroup.det) hc₀X
    rw [show ((M * XN⁻¹ : primeFormUnitary h
          ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) : GL (Fin n) K) =
        (M : GL (Fin n) K) * (XN : GL (Fin n) K)⁻¹ from rfl] at hh
    rw [map_mul, map_inv, hdetXN, GeneralLinearGroup.det_scalar, Fintype.card_fin] at hh
    exact hh
  set dM : Kˣ := GeneralLinearGroup.det (M : GL (Fin n) K) with hdM
  have hnorm : h.norm ((dM : Kˣ) : K) = 1 := by
    rw [hdM, GeneralLinearGroup.val_det_apply]
    exact norm_det_eq_one h (1 : GL (Fin n) K) M.2
  have hσdM : σ ((dM : Kˣ) : K) = (((dM : Kˣ) : K))⁻¹ := by
    have h1 : ((dM : Kˣ) : K) * σ ((dM : Kˣ) : K) = 1 := by
      have hh : ((dM : Kˣ) : K) * h.bar ((dM : Kˣ) : K) = 1 := hnorm
      rw [RootDetectSU.bar_eq h] at hh
      exact hh
    exact (inv_eq_of_mul_eq_one_right h1).symm
  have hmapinv : Units.map ((σ : K →+* K) : K →* K) dM = dM⁻¹ := by
    apply Units.ext
    simpa [Units.coe_map, Units.val_inv_eq_inv_val] using hσdM
  have hdetM3 : dM ^ 3 = c' ^ n := by
    have hh := congrArg (GeneralLinearGroup.det) hc'M3
    have hL : GeneralLinearGroup.det (↑(M ^ 3) : GL (Fin n) K) =
        (GeneralLinearGroup.det (M : GL (Fin n) K)) ^ 3 := by
      rw [Subgroup.coe_pow, map_pow]
    rw [hL, ← hdM] at hh
    simpa only [GeneralLinearGroup.det_scalar, Fintype.card_fin] using hh
  have hdMsq : dM ^ 2 = c₀ ^ n := by
    rw [hmapinv] at hdetX
    simpa [sq] using hdetX
  have hdMpow : dM = (c' * c₀⁻¹) ^ n := by
    have h1 : dM = dM ^ 3 * (dM ^ 2)⁻¹ := by group
    rw [h1, hdetM3, hdMsq, mul_pow, inv_pow]
  have hvnorm : h.norm (((c' * c₀⁻¹ : Kˣ)) : K) = 1 := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val,
      CFSG.ClassicalGroups.UnitaryFlag.norm_mul_eq h,
      CFSG.ClassicalGroups.UnitaryFlag.norm_inv_eq h]
    simp [hc'N, hc₀N]
  have hinner :=
    CFSG.GH74.Generic.BProg.B2.T4.T4OutCore.primeFormConjHom_mem_inner_of_det h M hvnorm
      (by simpa only [hdM] using hdMpow)
  rw [← htM]
  exact hinner

theorem ggSU6DiagInvertedKnown_holds : GGSU6DiagInvertedKnown := by
  intro f h3 Q hQ
  change LargeEvenRecipeUnitary 6 (2 ^ f) Q at hQ
  change LargeEvenRecipeUnitary 6 (2 ^ f)
    (fun R _ I F => Q R I F ∧ GGSU6DiagInvertedAt I)
  obtain ⟨K, hKfield, hKfinite, hKcard, hQK⟩ := hQ
  refine ⟨K, hKfield, hKfinite, hKcard, hQK, ?_⟩
  letI := hKfield
  letI := hKfinite
  intro t htI ht3 htNotInn U hUne hU2 hUdisj hNorm
  have hf : 1 ≤ f := by
    by_contra hf
    have hf0 : f = 0 := by omega
    subst hf0
    norm_num at h3
  let h : UnitaryFieldData 2 f K := TableBU.unitaryFieldData_of_card hKcard hf
  haveI : CharP K 2 := h.charP
  have hd1 : 1 ≤ 6 := by norm_num
  have hd : 3 ≤ 6 := by norm_num
  have hq : ¬((6 : ℕ) = 3 ∧ 2 ^ f = 2) := by omega
  let hC : IsPrimeFormGram (1 : GL (Fin 6) K) := isPrimeFormGram_one
  let E := MulAut.congr (InndiagSU.projEquiv h hd1)
  have hIleD : ∀ φ, φ ∈ (LargeEvenMatConjImage (LargeEvenProjMk
        (LargeEvenSUGroup (Fin 6) K (2 ^ f))) (LargeEvenGUSet (Fin 6) K (2 ^ f))) →
      φ ∈ InndiagSU.inndiagU h hd1 := fun φ hφ =>
    (InndiagSU.mem_inndiagU h).mpr (InndiagSU.congr_mem_primeFormD h hd1 hKcard hφ)
  have hDleI : ∀ φ, φ ∈ InndiagSU.inndiagU h hd1 → φ ∈ (LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ f)))
      (LargeEvenGUSet (Fin 6) K (2 ^ f))) := fun φ hφ =>
    InndiagSU.mem_conjImage_of_mem_inndiagU h hφ
  have hclosure : Subgroup.closure (LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ f)))
        (LargeEvenGUSet (Fin 6) K (2 ^ f))) = InndiagSU.inndiagU h hd1 := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      exact hIleD
    · intro φ hφ
      exact Subgroup.subset_closure (hDleI φ hφ)
  have hdisj' : U ⊓ InndiagSU.inndiagU h hd1 = ⊥ := by
    rw [← hclosure]
    exact hUdisj
  have ht'D : E t ∈ primeFormD h ((1 : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) :=
    InndiagSU.congr_mem_primeFormD h hd1 hKcard htI
  have ht'3 : (E t) ^ 3 = 1 := by rw [← map_pow, ht3, map_one]
  have ht'NotInn : E t ∉ ltrkd5b_inner
      (primeFormP h ((1 : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) := by
    intro hinn
    apply htNotInn
    have hiff := InndiagSU.range_conj_eq_comap_inner h hd1
    have hmem : t ∈ (MulAut.conj : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ f)) →*
        MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ f)))).range := by
      rw [hiff]
      exact Subgroup.mem_comap.mpr hinn
    simpa [LargeEvenInnSet] using hmem
  have hlt : (⊥ : Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ f))))) < U :=
    lt_of_le_of_ne bot_le (Ne.symm hUne)
  obtain ⟨u, huU, hu1⟩ := SetLike.exists_of_lt hlt
  replace hu1 : u ≠ 1 := by simpa using hu1
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hU2 ⟨u, huU⟩
  rw [Subgroup.orderOf_mk] at hk
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at hk
    exact hu1 hk
  have hkpos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
  let w : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ f))) := u ^ (2 ^ (k - 1))
  have hwU : w ∈ U := U.pow_mem huU _
  have hw2 : w ^ 2 = 1 := by
    dsimp only [w]
    rw [← pow_mul,
      show 2 ^ (k - 1) * 2 = 2 ^ k by rw [← pow_succ, Nat.sub_add_cancel hkpos],
      ← hk, pow_orderOf_eq_one]
  have hw1 : w ≠ 1 := by
    dsimp only [w]
    intro hw
    have hdvd : orderOf u ∣ 2 ^ (k - 1) := orderOf_dvd_iff_pow_eq_one.mpr hw
    rw [hk] at hdvd
    have hle : k ≤ k - 1 := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp hdvd
    omega
  have hcentral : ∀ x ∈ U, t * x * t⁻¹ = x := by
    intro x hx
    have hx' : t * x * t⁻¹ ∈ U := hNorm x hx
    have hUmem : (t * x * t⁻¹) * x⁻¹ ∈ U := U.mul_mem hx' (U.inv_mem hx)
    have hdker : (t * x * t⁻¹) * x⁻¹ ∈ (InndiagSU.fieldFactorU h hd hq).ker := by
      have htker : InndiagSU.fieldFactorU h hd hq t = 1 := by
        have : t ∈ (InndiagSU.fieldFactorU h hd hq).ker := by
          rw [InndiagSU.ker_fieldFactorU h hd hq]
          exact (InndiagSU.mem_inndiagU h).mpr ht'D
        simpa using this
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, htker]
      group
    have hmemD : (t * x * t⁻¹) * x⁻¹ ∈ InndiagSU.inndiagU h hd1 := by
      rw [← InndiagSU.ker_fieldFactorU h hd hq]
      exact hdker
    have hmem : (t * x * t⁻¹) * x⁻¹ ∈ U ⊓ InndiagSU.inndiagU h hd1 := ⟨hUmem, hmemD⟩
    rw [hdisj', Subgroup.mem_bot] at hmem
    calc t * x * t⁻¹ = ((t * x * t⁻¹) * x⁻¹) * x := by group
      _ = 1 * x := by rw [hmem]
      _ = x := one_mul x
  have hwComm : t * w = w * t := by
    have h := hcentral w hwU
    calc t * w = (t * w * t⁻¹) * t := by group
      _ = w * t := by rw [h]
  have hwField : primeFormFieldFactor h hC hd hq (E w) =
      CFSG.LieType.BorelTits.unitaryInvolution K 2 f := by
    have hfac : InndiagSU.fieldFactorU h hd hq w =
        primeFormFieldFactor h hC hd hq (E w) := rfl
    rw [← hfac]
    have hw2' : (InndiagSU.fieldFactorU h hd hq w) ^ 2 = 1 := by
      rw [← map_pow, hw2, map_one]
    have hw1' : InndiagSU.fieldFactorU h hd hq w ≠ 1 := by
      intro h1
      have hmem : w ∈ (InndiagSU.fieldFactorU h hd hq).ker := h1
      rw [InndiagSU.ker_fieldFactorU h hd hq] at hmem
      have : w ∈ U ⊓ InndiagSU.inndiagU h hd1 := ⟨hwU, hmem⟩
      rw [hdisj', Subgroup.mem_bot] at this
      exact hw1 this
    exact AutPSU.eq_sigma_of_mul_self_eq_one h hw2' hw1'
  have hEwComm : (E t) * (E w) = (E w) * (E t) := by
    rw [← map_mul, ← map_mul, hwComm]
  have hinner := ltrkd5b_primeForm_inner h hd hq ht'D ht'3 hwField hEwComm
  exact ht'NotInn hinner

end CFSG.StandardType

end
