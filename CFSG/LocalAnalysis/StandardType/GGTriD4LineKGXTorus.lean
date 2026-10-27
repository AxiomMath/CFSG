module

public import CFSG.LocalAnalysis.StandardType.GGTriD4LineKGXDefs
import CFSG.LieType.Chevalley.CLSOddE7RationalEightGroup
import CFSG.RankThree.Chevalley.SteinbergBITrialitySingular
import CFSG.RankThree.PartTwo.Sec11.Item1118Res3ProofRep
import CFSG.GroupTheory.LocalCores.Fitting
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
import CFSG.RankThree.PartOne.KC.UnitaryPlaneOrthogonal
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Borel
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Lemma83
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Cardinalities
import CFSG.Walter.Defs

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private lemma triD4LineV_inv_eq_wordProd :
    triD4LineV⁻¹ = (coxeterSystem Tag.D4).wordProd [3, 1, 2, 0] := by
  rw [triD4LineV, ← CoxeterSystem.wordProd_reverse]
  rfl

private lemma triD4LineV_inv_smul_single
    (i : Fin Tag.D4.rank) :
    triD4LineV⁻¹ • (Pi.single i 1 : Fin Tag.D4.rank → ℤ) =
      ![![(-1 : ℤ), -1, -1, -1], ![0, 0, 1, 1], ![1, 0, 0, 0], ![0, 1, 1, 0]] i := by
  rw [triD4LineV_inv_eq_wordProd]
  rw [show (coxeterSystem Tag.D4).wordProd [3, 1, 2, 0] =
    (coxeterSystem Tag.D4).simple 3 * ((coxeterSystem Tag.D4).simple 1 *
      ((coxeterSystem Tag.D4).simple 2 * (coxeterSystem Tag.D4).simple 0)) by
    simp [CoxeterSystem.wordProd_cons]]
  rw [mul_smul, mul_smul, mul_smul, CFSG.LieType.Chevalley.simple_smul,
    CFSG.LieType.Chevalley.simple_smul, CFSG.LieType.Chevalley.simple_smul,
    CFSG.LieType.Chevalley.simple_smul]
  ext j
  fin_cases i <;> fin_cases j <;> decide +kernel

private lemma rootChar_triD4LineV_zero
    {L : Type} [Field L] (c : Fin Tag.D4.rank → Lˣ) :
    rootChar (τ := Tag.D4) c (triD4LineV⁻¹ • (Pi.single (0 : Fin Tag.D4.rank) 1)) =
      (c 0 * c 1 * c 2 * c 3)⁻¹ := by
  have h : triD4LineV⁻¹ • (Pi.single (0 : Fin Tag.D4.rank) 1 : Fin Tag.D4.rank → ℤ) =
      (![-1, -1, -1, -1] : Fin Tag.D4.rank → ℤ) := by
    rw [triD4LineV_inv_smul_single]; rfl
  rw [h]
  simp [rootChar, prod_fin_D4]
  ac_rfl

private lemma rootChar_triD4LineV_one
    {L : Type} [Field L] (c : Fin Tag.D4.rank → Lˣ) :
    rootChar (τ := Tag.D4) c (triD4LineV⁻¹ • (Pi.single (1 : Fin Tag.D4.rank) 1)) =
      c 2 * c 3 := by
  have h : triD4LineV⁻¹ • (Pi.single (1 : Fin Tag.D4.rank) 1 : Fin Tag.D4.rank → ℤ) =
      (![0, 0, 1, 1] : Fin Tag.D4.rank → ℤ) := by
    rw [triD4LineV_inv_smul_single]; rfl
  rw [h]
  simp [rootChar, prod_fin_D4]

private lemma rootChar_triD4LineV_two
    {L : Type} [Field L] (c : Fin Tag.D4.rank → Lˣ) :
    rootChar (τ := Tag.D4) c (triD4LineV⁻¹ • (Pi.single (2 : Fin Tag.D4.rank) 1)) = c 0 := by
  have h : triD4LineV⁻¹ • (Pi.single (2 : Fin Tag.D4.rank) 1 : Fin Tag.D4.rank → ℤ) =
      (![1, 0, 0, 0] : Fin Tag.D4.rank → ℤ) := by
    rw [triD4LineV_inv_smul_single]; rfl
  rw [h]
  simp [rootChar, prod_fin_D4]

private lemma rootChar_triD4LineV_three
    {L : Type} [Field L] (c : Fin Tag.D4.rank → Lˣ) :
    rootChar (τ := Tag.D4) c (triD4LineV⁻¹ • (Pi.single (3 : Fin Tag.D4.rank) 1)) =
      c 1 * c 2 := by
  have h : triD4LineV⁻¹ • (Pi.single (3 : Fin Tag.D4.rank) 1 : Fin Tag.D4.rank → ℤ) =
      (![0, 1, 1, 0] : Fin Tag.D4.rank → ℤ) := by
    rw [triD4LineV_inv_smul_single]; rfl
  rw [h]
  simp [rootChar, prod_fin_D4]

private lemma weylTuple_triD4LineV_zero
    {L : Type} [Field L] (c : Fin Tag.D4.rank → Lˣ) :
    weylTuple triD4LineV c 0 = (c 0 * c 1 * c 2 * c 3)⁻¹ := by
  simpa [weylTuple] using rootChar_triD4LineV_zero c

private lemma weylTuple_triD4LineV_one
    {L : Type} [Field L] (c : Fin Tag.D4.rank → Lˣ) :
    weylTuple triD4LineV c 1 = c 2 * c 3 := by
  simpa [weylTuple] using rootChar_triD4LineV_one c

private lemma weylTuple_triD4LineV_two
    {L : Type} [Field L] (c : Fin Tag.D4.rank → Lˣ) :
    weylTuple triD4LineV c 2 = c 0 := by
  simpa [weylTuple] using rootChar_triD4LineV_two c

private lemma weylTuple_triD4LineV_three
    {L : Type} [Field L] (c : Fin Tag.D4.rank → Lˣ) :
    weylTuple triD4LineV c 3 = c 1 * c 2 := by
  simpa [weylTuple] using rootChar_triD4LineV_three c

private lemma inv_conj_rootDiagUnit_weylTuple
    {L : Type} [Field L] (w : WeylGroup Tag.D4)
    (b : Fin Tag.D4.rank → Lˣ) :
    (canonicalRep (coxeterSystem Tag.D4) L w)⁻¹ * rootDiagUnit Tag.D4 b *
        canonicalRep (coxeterSystem Tag.D4) L w =
      rootDiagUnit Tag.D4 (fun j => rootChar b (w • (Pi.single j 1))) := by
  have h := (rootDiagUnit_eq_conj_canonicalRep_iff (K := L) b
    (fun j => rootChar b (w • (Pi.single j 1 : Fin Tag.D4.rank → ℤ))) w).2
    fun l => rootChar_smul_eq_rootChar b w l
  rw [h]
  group

private lemma d4A2TorusElt_eq_rootDiagUnit
    {L : Type} [Field L] (t u : Lˣ) :
    d4A2TorusElt t u = rootDiagUnit Tag.D4
      (fun j => t ^ Tag.D4.cartan 0 j * u ^ Tag.D4.cartan 2 j) := by
  rw [d4A2TorusElt, torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit, ← rootDiagUnit_mul]
  rfl

private lemma cartan_D4_zero_zero : Tag.D4.cartan 0 0 = 2 := rfl
private lemma cartan_D4_zero_one : Tag.D4.cartan 0 1 = 0 := rfl
private lemma cartan_D4_zero_two : Tag.D4.cartan 0 2 = -1 := rfl
private lemma cartan_D4_zero_three : Tag.D4.cartan 0 3 = 0 := rfl
private lemma cartan_D4_two_zero : Tag.D4.cartan 2 0 = -1 := rfl
private lemma cartan_D4_two_one : Tag.D4.cartan 2 1 = -1 := rfl
private lemma cartan_D4_two_two : Tag.D4.cartan 2 2 = 2 := rfl
private lemma cartan_D4_two_three : Tag.D4.cartan 2 3 = -1 := rfl

private lemma d4A2TorusElt_tuple_values {L : Type} [Field L] (t u : Lˣ) :
    (fun j => t ^ Tag.D4.cartan 0 j * u ^ Tag.D4.cartan 2 j) 0 = t ^ 2 * u⁻¹ ∧
      (fun j => t ^ Tag.D4.cartan 0 j * u ^ Tag.D4.cartan 2 j) 1 = u⁻¹ ∧
      (fun j => t ^ Tag.D4.cartan 0 j * u ^ Tag.D4.cartan 2 j) 2 = t⁻¹ * u ^ 2 ∧
      (fun j => t ^ Tag.D4.cartan 0 j * u ^ Tag.D4.cartan 2 j) 3 = u⁻¹ := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [cartan_D4_zero_zero, cartan_D4_zero_one, cartan_D4_zero_two, cartan_D4_zero_three,
      cartan_D4_two_zero, cartan_D4_two_one, cartan_D4_two_two, cartan_D4_two_three]

theorem triD4Line_rootDiagUnit_mem_Qv_iff
    (L : Type) [Field L] (b : Fin Tag.D4.rank → Lˣ) :
    rootDiagUnit Tag.D4 b ∈ d4A2Qv L triD4LineV ↔ b 1 = b 0 ∧ b 3 = b 0 := by
  constructor
  · intro hb
    obtain ⟨u₀, hu₀Q, hu₀eq⟩ := Subgroup.mem_map.1 hb
    have hu₀ : u₀ = (canonicalRep (coxeterSystem Tag.D4) L triD4LineV)⁻¹ *
        rootDiagUnit Tag.D4 b * canonicalRep (coxeterSystem Tag.D4) L triD4LineV := by
      rw [← hu₀eq, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    obtain ⟨t, s, hts⟩ :=
      CFSG.RankThree.PartTwo.Sec11.Item1118Res3Proof.exists_d4A2TorusElt_of_diagonal hu₀Q
        (d := fun k => ((rootChar (fun j => rootChar b (triD4LineV • (Pi.single j 1)))
          (d4A2Weight k) : Lˣ) : L)) (by
        rw [hu₀, inv_conj_rootDiagUnit_weylTuple]
        exact CFSG.RankThree.PartTwo.Sec11.Item1118Res3Proof.d4A2Mat_rootDiagUnit _)
    let c : Fin Tag.D4.rank → Lˣ := fun j => t ^ Tag.D4.cartan 0 j * s ^ Tag.D4.cartan 2 j
    have hwc : d4A2TorusElt t s = rootDiagUnit Tag.D4 c := d4A2TorusElt_eq_rootDiagUnit t s
    have hb_eq : rootDiagUnit Tag.D4 b = rootDiagUnit Tag.D4 (weylTuple triD4LineV c) := by
      calc rootDiagUnit Tag.D4 b
          = canonicalRep (coxeterSystem Tag.D4) L triD4LineV * u₀ *
            (canonicalRep (coxeterSystem Tag.D4) L triD4LineV)⁻¹ := by rw [hu₀]; group
        _ = canonicalRep (coxeterSystem Tag.D4) L triD4LineV * d4A2TorusElt t s *
            (canonicalRep (coxeterSystem Tag.D4) L triD4LineV)⁻¹ := by rw [hts]
        _ = canonicalRep (coxeterSystem Tag.D4) L triD4LineV * rootDiagUnit Tag.D4 c *
            (canonicalRep (coxeterSystem Tag.D4) L triD4LineV)⁻¹ := by rw [hwc]
        _ = rootDiagUnit Tag.D4 (weylTuple triD4LineV c) :=
            canonicalRep_conj_rootDiagUnit triD4LineV c
    have hbweyl : b = weylTuple triD4LineV c := rootDiagUnit_injective hb_eq
    have hb0 : b 0 = (c 0 * c 1 * c 2 * c 3)⁻¹ := by
      rw [hbweyl]; exact weylTuple_triD4LineV_zero c
    have hb1 : b 1 = c 2 * c 3 := by
      rw [hbweyl]; exact weylTuple_triD4LineV_one c
    have hb3 : b 3 = c 1 * c 2 := by
      rw [hbweyl]; exact weylTuple_triD4LineV_three c
    obtain ⟨hc0, hc1, hc2, hc3⟩ := d4A2TorusElt_tuple_values t s
    have hc0' : c 0 = t ^ 2 * s⁻¹ := hc0
    have hc1' : c 1 = s⁻¹ := hc1
    have hc2' : c 2 = t⁻¹ * s ^ 2 := hc2
    have hc3' : c 3 = s⁻¹ := hc3
    constructor
    · rw [hb1, hb0, hc0', hc1', hc2', hc3']
      ext
      simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
      field_simp
    · rw [hb3, hb0, hc0', hc1', hc2', hc3']
      ext
      simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
      field_simp
  · rintro ⟨hb1, hb3⟩
    have hb : b = ![b 0, b 0, b 2, b 0] := by
      funext i
      fin_cases i
      · change b 0 = b 0; rfl
      · change b 1 = b 0; exact hb1
      · change b 2 = b 2; rfl
      · change b 3 = b 0; exact hb3
    let t : Lˣ := b 0 * b 2
    let u : Lˣ := b 0 ^ 2 * b 2
    let c : Fin Tag.D4.rank → Lˣ := fun j => t ^ Tag.D4.cartan 0 j * u ^ Tag.D4.cartan 2 j
    have hwc : d4A2TorusElt t u = rootDiagUnit Tag.D4 c := d4A2TorusElt_eq_rootDiagUnit t u
    have hweyl : weylTuple triD4LineV c = ![b 0, b 0, b 2, b 0] := by
      funext i
      fin_cases i
      · change weylTuple triD4LineV c (0 : Fin Tag.D4.rank) = b 0
        rw [weylTuple_triD4LineV_zero]
        obtain ⟨hc0, hc1, hc2, hc3⟩ := d4A2TorusElt_tuple_values t u
        have hc0' : c 0 = t ^ 2 * u⁻¹ := hc0
        have hc1' : c 1 = u⁻¹ := hc1
        have hc2' : c 2 = t⁻¹ * u ^ 2 := hc2
        have hc3' : c 3 = u⁻¹ := hc3
        rw [hc0', hc1', hc2', hc3']
        ext
        simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
        simp only [t, u]
        field_simp
        simp only [Units.val_mul, Units.val_pow_eq_pow_val]
        ring
      · change weylTuple triD4LineV c (1 : Fin Tag.D4.rank) = b 0
        rw [weylTuple_triD4LineV_one]
        obtain ⟨hc0, hc1, hc2, hc3⟩ := d4A2TorusElt_tuple_values t u
        have hc0' : c 0 = t ^ 2 * u⁻¹ := hc0
        have hc1' : c 1 = u⁻¹ := hc1
        have hc2' : c 2 = t⁻¹ * u ^ 2 := hc2
        have hc3' : c 3 = u⁻¹ := hc3
        rw [hc2', hc3']
        ext
        simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
        simp only [t, u]
        field_simp
        simp only [Units.val_mul, Units.val_pow_eq_pow_val]
        ring
      · change weylTuple triD4LineV c (2 : Fin Tag.D4.rank) = b 2
        rw [weylTuple_triD4LineV_two]
        obtain ⟨hc0, hc1, hc2, hc3⟩ := d4A2TorusElt_tuple_values t u
        have hc0' : c 0 = t ^ 2 * u⁻¹ := hc0
        have hc1' : c 1 = u⁻¹ := hc1
        have hc2' : c 2 = t⁻¹ * u ^ 2 := hc2
        have hc3' : c 3 = u⁻¹ := hc3
        rw [hc0']
        simp only [t, u]
        ext
        simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
        field_simp
      · change weylTuple triD4LineV c (3 : Fin Tag.D4.rank) = b 0
        rw [weylTuple_triD4LineV_three]
        obtain ⟨hc0, hc1, hc2, hc3⟩ := d4A2TorusElt_tuple_values t u
        have hc0' : c 0 = t ^ 2 * u⁻¹ := hc0
        have hc1' : c 1 = u⁻¹ := hc1
        have hc2' : c 2 = t⁻¹ * u ^ 2 := hc2
        have hc3' : c 3 = u⁻¹ := hc3
        rw [hc1', hc2']
        ext
        simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
        simp only [t, u]
        field_simp
        simp only [Units.val_mul, Units.val_pow_eq_pow_val]
        ring
    refine Subgroup.mem_map.2 ⟨d4A2TorusElt t u, d4A2TorusElt_mem t u, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hwc, canonicalRep_conj_rootDiagUnit, hweyl]
    exact congrArg (rootDiagUnit Tag.D4) hb.symm

theorem triD4Line_d4A2QvEquiv_rootDiagUnit
    (L : Type) [Field L] (s t : Lˣ) (h : rootDiagUnit Tag.D4 ![s, s, t, s] ∈ d4A2Qv L triD4LineV) :
    ((d4A2QvEquiv (K := L) triD4LineV ⟨_, h⟩ : Matrix.SpecialLinearGroup (Fin 3) L) :
        Matrix (Fin 3) (Fin 3) L) =
      Matrix.diagonal ![((s * t : Lˣ) : L), (s : L), (((s ^ 2 * t)⁻¹ : Lˣ) : L)] := by
  let t0 : Lˣ := s * t
  let u0 : Lˣ := s ^ 2 * t
  let c : Fin Tag.D4.rank → Lˣ := fun j => t0 ^ Tag.D4.cartan 0 j * u0 ^ Tag.D4.cartan 2 j
  have hwc : d4A2TorusElt t0 u0 = rootDiagUnit Tag.D4 c := d4A2TorusElt_eq_rootDiagUnit t0 u0
  have hweyl : weylTuple triD4LineV c = ![s, s, t, s] := by
    funext i
    fin_cases i
    · change weylTuple triD4LineV c (0 : Fin Tag.D4.rank) = s
      rw [weylTuple_triD4LineV_zero]
      obtain ⟨hc0, hc1, hc2, hc3⟩ := d4A2TorusElt_tuple_values t0 u0
      have hc0' : c 0 = t0 ^ 2 * u0⁻¹ := hc0
      have hc1' : c 1 = u0⁻¹ := hc1
      have hc2' : c 2 = t0⁻¹ * u0 ^ 2 := hc2
      have hc3' : c 3 = u0⁻¹ := hc3
      rw [hc0', hc1', hc2', hc3']
      ext
      simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
      simp only [t0, u0]
      field_simp
      simp only [Units.val_mul, Units.val_pow_eq_pow_val]
      ring
    · change weylTuple triD4LineV c (1 : Fin Tag.D4.rank) = s
      rw [weylTuple_triD4LineV_one]
      obtain ⟨hc0, hc1, hc2, hc3⟩ := d4A2TorusElt_tuple_values t0 u0
      have hc0' : c 0 = t0 ^ 2 * u0⁻¹ := hc0
      have hc1' : c 1 = u0⁻¹ := hc1
      have hc2' : c 2 = t0⁻¹ * u0 ^ 2 := hc2
      have hc3' : c 3 = u0⁻¹ := hc3
      rw [hc2', hc3']
      ext
      simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
      simp only [t0, u0]
      field_simp
      simp only [Units.val_mul, Units.val_pow_eq_pow_val]
      ring
    · change weylTuple triD4LineV c (2 : Fin Tag.D4.rank) = t
      rw [weylTuple_triD4LineV_two]
      obtain ⟨hc0, hc1, hc2, hc3⟩ := d4A2TorusElt_tuple_values t0 u0
      have hc0' : c 0 = t0 ^ 2 * u0⁻¹ := hc0
      rw [hc0']
      simp only [t0, u0]
      ext
      simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
      field_simp
    · change weylTuple triD4LineV c (3 : Fin Tag.D4.rank) = s
      rw [weylTuple_triD4LineV_three]
      obtain ⟨hc0, hc1, hc2, hc3⟩ := d4A2TorusElt_tuple_values t0 u0
      have hc0' : c 0 = t0 ^ 2 * u0⁻¹ := hc0
      have hc1' : c 1 = u0⁻¹ := hc1
      have hc2' : c 2 = t0⁻¹ * u0 ^ 2 := hc2
      have hc3' : c 3 = u0⁻¹ := hc3
      rw [hc1', hc2']
      ext
      simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
      simp only [t0, u0]
      field_simp
      simp only [Units.val_mul, Units.val_pow_eq_pow_val]
      ring
  let w : subsystemGroup Tag.D4 L d4SuppA2 :=
    ⟨d4A2TorusElt t0 u0, d4A2TorusElt_mem t0 u0⟩
  have hwval : (w : ModGL Tag.D4 L) = d4A2TorusElt t0 u0 := rfl
  have hb : rootDiagUnit Tag.D4 ![s, s, t, s] =
      canonicalRep (coxeterSystem Tag.D4) L triD4LineV * (w : ModGL Tag.D4 L) *
        (canonicalRep (coxeterSystem Tag.D4) L triD4LineV)⁻¹ := by
    rw [hwval, hwc, canonicalRep_conj_rootDiagUnit, hweyl]
  have hQ : canonicalRep (coxeterSystem Tag.D4) L triD4LineV * (w : ModGL Tag.D4 L) *
      (canonicalRep (coxeterSystem Tag.D4) L triD4LineV)⁻¹ ∈ d4A2Qv L triD4LineV := by
    refine Subgroup.mem_map.2 ⟨w, w.2, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have hsub : (⟨rootDiagUnit Tag.D4 ![s, s, t, s], h⟩ : d4A2Qv L triD4LineV) =
      ⟨canonicalRep (coxeterSystem Tag.D4) L triD4LineV * (w : ModGL Tag.D4 L) *
        (canonicalRep (coxeterSystem Tag.D4) L triD4LineV)⁻¹, hQ⟩ := Subtype.ext hb
  have hvec : (![((t0 : Lˣ) : L), (((t0)⁻¹ * u0 : Lˣ) : L),
      (((u0)⁻¹ : Lˣ) : L)] : Fin 3 → L) =
      ![((s * t : Lˣ) : L), (s : L), (((s ^ 2 * t)⁻¹ : Lˣ) : L)] := by
    funext k
    fin_cases k
    · change ((t0 : Lˣ) : L) = ((s * t : Lˣ) : L); rfl
    · change (((t0)⁻¹ * u0 : Lˣ) : L) = (s : L)
      simp only [t0, u0, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
      field_simp
    · change (((u0)⁻¹ : Lˣ) : L) = (((s ^ 2 * t)⁻¹ : Lˣ) : L); rfl
  calc ((d4A2QvEquiv (K := L) triD4LineV ⟨_, h⟩ : Matrix.SpecialLinearGroup (Fin 3) L) :
        Matrix (Fin 3) (Fin 3) L)
      = ((d4A2QvEquiv (K := L) triD4LineV
          ⟨_, hQ⟩ : Matrix.SpecialLinearGroup (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) := by
          rw [hsub]
    _ = ((d4A2Rep L w :
          Matrix.SpecialLinearGroup (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) := by
          rw [d4A2QvEquiv_conj]
    _ = d4A2Mat (w : ModGL Tag.D4 L) := coe_d4A2Rep w
    _ = d4A2Mat (d4A2TorusElt t0 u0) := by rw [hwval]
    _ = Matrix.diagonal ![((t0 : Lˣ) : L), (((t0)⁻¹ * u0 : Lˣ) : L),
          (((u0)⁻¹ : Lˣ) : L)] := d4A2Mat_d4A2TorusElt t0 u0
    _ = Matrix.diagonal ![((s * t : Lˣ) : L), (s : L), (((s ^ 2 * t)⁻¹ : Lˣ) : L)] := by
          rw [hvec]

end CFSG.StandardType
