module

public import CFSG.LocalAnalysis.StandardType.GGResILineInputs
public import CFSG.RankThree.PartOne.KC.CommonEigenbasis
public import CFSG.LieType.SemisimpleCentralizers.HeldLangU64Ord
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGU6b
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniCubeCompEq
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniCubeQS
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniCubeCQ
public import CFSG.LocalAnalysis.StandardType.GGTPNDefs
public import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicTransfer
public import CFSG.LocalAnalysis.StandardType.GGAutomizerAbelianMatrix
public import CFSG.LocalAnalysis.StandardType.GGPGLToralityEigenspace
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeInner
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeThree
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitarySixThreeCases
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagProj
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GField
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GU64Pieces
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119

public section

namespace CFSG.StandardType

open Module Matrix CFSG.Assembly CFSG.Open CFSG.LieType.SemisimpleCentralizers.HeldLang
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.StandardType.TablePThreeKG
open CFSG.HardMathSupport.Solomon.Coordinator CFSG.RankThree.PartOne.KCUnitaryModel

theorem padicValNat_field_case_card {n : ℕ} (hn : 1 ≤ n) :
    padicValNat 2 ((2 ^ n) ^ 3 * ((2 ^ n) ^ 6 - 1)) = 3 * n := by
  have h3 : (2 ^ n) ^ 3 = 2 ^ (3 * n) := by ring
  have h6 : (2 ^ n) ^ 6 = 2 ^ (6 * n) := by ring
  rw [h3, h6]
  have hne : 2 ^ (6 * n) - 1 ≠ 0 := by
    have : 1 < 2 ^ (6 * n) := Nat.one_lt_two_pow (by omega)
    omega
  rw [padicValNat.mul (by positivity) hne, padicValNat.prime_pow]
  have hodd : Odd (2 ^ (6 * n) - 1) := by
    have heven : Even (2 ^ (6 * n)) := by
      rw [even_iff_two_dvd]
      exact dvd_pow_self 2 (by omega)
    obtain ⟨k, hk⟩ := heven
    have hk1 : 1 ≤ k := by
      have h1 : 1 ≤ 2 ^ (6 * n) := Nat.one_le_two_pow
      omega
    exact ⟨k - 1, by rw [hk]; omega⟩
  rw [padicValNat.eq_zero_of_not_dvd hodd.not_two_dvd_nat]
  ring

theorem padicValNat_card_of_ggHasLabel_twA3
    {R : Type} [Group R] [Finite R] {n : ℕ} (hn : 1 ≤ n)
    (h : GGHasLabel (⟨.twA, 3, n⟩ : LargeEvenLabel) R) :
    padicValNat 2 (Nat.card R) = n * 6 := by
  unfold GGHasLabel at h
  dsimp only [LargeEvenRawDatum] at h
  unfold LargeEvenRecipeUnitary at h
  obtain ⟨K', hK'f, hK'fin, hK'card, ⟨e⟩⟩ := h
  let : Field K' := hK'f
  let : Finite K' := hK'fin
  rw [Nat.card_congr e.toEquiv]
  have h4 : padicValNat 2
      (Nat.card (StatedProj (StatedSU 4 (2 ^ n) K'))) = n * 6 := by
    rw [padicValNat_card_psu (a := n) (d := 4) hn (by norm_num) hK'card]
  exact h4


theorem cubeEigen_finrank_eq_four_of_component_twA3
    {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hq3 : 3 ∣ 2 ^ n + 1)
    {d : GL (Fin 6) K} (hd : IsHermIsometry (2 ^ n) (d : Matrix (Fin 6) (Fin 6) K))
    (hd3 : d ^ 3 = 1)
    {δ' : MulAut (PSUg 6 K (2 ^ n))} (hδ : IsConjBy d δ')
    {Q : Subgroup (PSUg 6 K (2 ^ n))}
    (hQ : CFSG.Assembly.IsComponentOf Q (ggAutFixedSubgroup δ'))
    (hlab : GGHasLabel (⟨.twA, 3, n⟩ : LargeEvenLabel) (Q ⧸ Subgroup.center Q)) :
    ∃ μ : K, μ ^ 3 = 1 ∧
      Module.finrank K (cubeEigen d μ) = 4 := by
  classical
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h
    · rw [h0] at hq3
      norm_num at hq3
    · exact h
  obtain ⟨μ, hμ, rfl⟩ :=
    CFSG.StandardType.TablePThreeKG.uni_cube_component_eq_eigBlock hK hq3 (by norm_num) hd hd3 hδ hQ
  obtain ⟨e⟩ :=
    CFSG.StandardType.TablePThreeKG.uni_cube_eigBlock_centerQuot hK hq3 (by norm_num) hd hd3 hμ
  let m := Module.finrank K (cubeEigen d μ)
  have hqs : CFSG.Assembly.IsQuasisimple
      ↥(CFSG.StandardType.TablePThreeKG.eigBlock (2 ^ n) d μ) := hQ.2.2
  have hQS : CFSG.StandardType.TablePThreeKG.CubeBlockQS (2 ^ n) d μ :=
    (CFSG.StandardType.TablePThreeKG.uni_cube_eigBlock_quasisimple_iff
      hK hq3 (by norm_num) hd hd3 hμ).mp hqs
  have hm1 : 1 ≤ m := by
    unfold CFSG.StandardType.TablePThreeKG.CubeBlockQS at hQS
    omega
  have hmle : m ≤ 6 := by
    simpa [m] using Submodule.finrank_le (cubeEigen d μ)
  have hvL : padicValNat 2 (Nat.card
      (CFSG.StandardType.TablePThreeKG.eigBlock (2 ^ n) d μ ⧸
        Subgroup.center (CFSG.StandardType.TablePThreeKG.eigBlock (2 ^ n) d μ))) = n * 6 := by
    simpa using padicValNat_card_of_ggHasLabel_twA3 hn hlab
  have hcard : Nat.card
      (CFSG.StandardType.TablePThreeKG.eigBlock (2 ^ n) d μ ⧸
        Subgroup.center (CFSG.StandardType.TablePThreeKG.eigBlock (2 ^ n) d μ)) =
      Nat.card (LargeEvenProj (LargeEvenSUGroup (Fin m) K (2 ^ n))) :=
    Nat.card_congr e.toEquiv
  have hvR : padicValNat 2 (Nat.card
      (CFSG.StandardType.TablePThreeKG.eigBlock (2 ^ n) d μ ⧸
        Subgroup.center (CFSG.StandardType.TablePThreeKG.eigBlock (2 ^ n) d μ))) =
      n * (m * (m - 1) / 2) := by
    rw [hcard]
    change padicValNat 2 (Nat.card (StatedProj (StatedSU m (2 ^ n) K))) = _
    rw [padicValNat_card_psu (a := n) (d := m) hn hm1 hK]
  have hmul : n * 6 = n * (m * (m - 1) / 2) := by
    rw [← hvL, hvR]
  have hmn : n ≠ 0 := by omega
  have hmeq : m * (m - 1) / 2 = 6 :=
    (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hmn) hmul).symm
  have hm4 : m = 4 := by
    interval_cases m <;> norm_num at hmeq
    rfl
  exact ⟨μ, hμ, hm4⟩

theorem primeForm_cubeRoot_normOne_of_component_twA3
    {K : Type} [Field K] {n : ℕ} (h : UnitaryFieldData 2 n K)
    (hq3 : 3 ∣ 2 ^ n + 1)
    (A : primeFormUnitary h (idGram K 6)) {c : Kˣ}
    (hA : (A : GL (Fin 6) K) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) c)
    {T : Subgroup (primeFormP h (idGram K 6))}
    (hT : CFSG.Open.IsComponentOf T (fixSubgroup (primeFormConjHom h (idGram K 6) A)))
    (hlab : GGHasLabel (⟨.twA, 3, n⟩ : LargeEvenLabel) (T ⧸ Subgroup.center T)) :
    ∃ t : Kˣ, t ^ (2 ^ n + 1) = 1 ∧ t ^ 3 = c := by
  classical
  have := h.finite
  have : Fintype K := Fintype.ofFinite K
  have hn : 1 ≤ n := h.one_le
  have hc_mem : Matrix.GeneralLinearGroup.scalar (Fin 6) c ∈
      primeFormUnitary h (idGram K 6) := by
    rw [← hA]
    exact pow_mem A.2 3
  have hcnorm : h.norm (c : K) = 1 :=
    norm_eq_one_of_scalar_mem_primeFormUnitary h (by norm_num) (1 : GL (Fin 6) K) hc_mem
  have hcpow : (c : K) ^ (2 ^ n + 1) = 1 := by
    simpa [UnitaryFieldData.norm, UnitaryFieldData.bar_apply, pow_succ, mul_comm] using hcnorm
  have hcpowU : c ^ (2 ^ n + 1) = 1 := Units.ext hcpow
  by_contra hno
  push Not at hno
  have hnotcube : ∀ t : Kˣ, t ^ 3 ≠ c := by
    intro t ht
    have htnorm : t ^ (2 ^ n + 1) = 1 := by
      have h1 : (t ^ (2 ^ n + 1)) ^ 3 = 1 := by
        rw [← pow_mul, Nat.mul_comm, pow_mul, ht, hcpowU]
      have h2 : (t ^ (2 ^ n + 1)) ^ (2 ^ n - 1) = 1 := by
        rw [← pow_mul]
        have hmul : (2 ^ n + 1) * (2 ^ n - 1) = Nat.card K - 1 := by
          have hsq : (2 ^ n + 1) * (2 ^ n - 1) = (2 ^ n) ^ 2 - 1 := by
            rw [← Nat.sq_sub_sq]
          rw [hsq, h.card, show (2 ^ n) ^ 2 = 2 ^ (2 * n) by
            rw [← pow_mul, Nat.mul_comm]]
        rw [hmul]
        apply Units.ext
        simpa [Nat.card_eq_fintype_card] using
          FiniteField.pow_card_sub_one_eq_one (t : K) t.ne_zero
      have hcop : Nat.Coprime 3 (2 ^ n - 1) := by
        rw [Nat.prime_three.coprime_iff_not_dvd]
        intro hdvd
        have hsub : 3 ∣ (2 ^ n + 1) - (2 ^ n - 1) := Nat.dvd_sub hq3 hdvd
        have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
        have h2 : (2 ^ n + 1) - (2 ^ n - 1) = 2 := by omega
        rw [h2] at hsub
        norm_num at hsub
      have hdvd3 : orderOf (t ^ (2 ^ n + 1)) ∣ 3 := orderOf_dvd_of_pow_eq_one h1
      have hdvdq : orderOf (t ^ (2 ^ n + 1)) ∣ 2 ^ n - 1 := orderOf_dvd_of_pow_eq_one h2
      have hdvd1 : orderOf (t ^ (2 ^ n + 1)) ∣ 1 := by
        have := Nat.dvd_gcd hdvd3 hdvdq
        rwa [hcop.gcd_eq_one] at this
      exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd1)
    exact (hno t htnorm) ht
  have hfield := CFSG.LocalAnalysis.GLTheoremA.S265.SGU6.card_quot_center_of_field h A hA hnotcube hT
  have hvL : padicValNat 2 (Nat.card (T ⧸ Subgroup.center T)) = 6 * n := by
    simpa [mul_comm] using padicValNat_card_of_ggHasLabel_twA3 hn hlab
  have hvR : padicValNat 2 (Nat.card (T ⧸ Subgroup.center T)) = 3 * n := by
    rw [hfield, padicValNat_field_case_card hn]
  omega

theorem exists_four_eigenspace_of_component_twA3
    {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hq3 : 3 ∣ 2 ^ n + 1)
    {d : GL (Fin 6) K} (hd : IsHermIsometry (2 ^ n) (d : Matrix (Fin 6) (Fin 6) K))
    {c : Kˣ} (hd3 : d ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) c)
    {δ' : MulAut (PSUg 6 K (2 ^ n))} (hδ : IsConjBy d δ')
    {Q : Subgroup (PSUg 6 K (2 ^ n))}
    (hQ : CFSG.Assembly.IsComponentOf Q (ggAutFixedSubgroup δ'))
    (hlab : GGHasLabel (⟨.twA, 3, n⟩ : LargeEvenLabel) (Q ⧸ Subgroup.center Q)) :
    ∃ μ : K, μ ≠ 0 ∧ μ ^ 3 = (c : K) ∧
      Module.finrank K (cubeEigen d μ) = 4 := by
  classical
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h
    · rw [h0] at hq3
      norm_num at hq3
    · exact h
  have h : UnitaryFieldData 2 n K :=
    CFSG.AGLEmbedding.ToralCensus.unitaryFieldData_of_card_eq_sq hK hn
  let e := CFSG.StandardType.InndiagSU.projEquiv (d := 6) h (by norm_num : 1 ≤ 6)
  have hdm : d ∈ primeFormUnitary h (idGram K 6) :=
    uni_cube_mem_primeFormUnitary (q := 2 ^ n) (n := 6) h rfl hd
  let A : primeFormUnitary h (idGram K 6) := ⟨d, hdm⟩
  have hHmap : (ggAutFixedSubgroup δ').map e.toMonoidHom =
      fixSubgroup (primeFormConjHom h (idGram K 6) A) := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (uni_cube_fixSubgroup_projEquiv h (by norm_num : 1 ≤ 6) hδ hdm y).mp hy
    · intro hx
      refine ⟨e.symm x, ?_, ?_⟩
      · refine (uni_cube_fixSubgroup_projEquiv h (by norm_num : 1 ≤ 6) hδ hdm _).mpr ?_
        rw [MulEquiv.apply_symm_apply]
        exact hx
      · exact MulEquiv.apply_symm_apply _ x
  have hcomp : CFSG.Assembly.IsComponentOf (Q.map e.toMonoidHom)
      (fixSubgroup (primeFormConjHom h (idGram K 6) A)) := by
    have h' := isComponentOf_map_mulEquiv' e hQ
    rwa [hHmap] at h'
  have hcompOpen : CFSG.Open.IsComponentOf (Q.map e.toMonoidHom)
      (fixSubgroup (primeFormConjHom h (idGram K 6) A)) :=
    CFSG.Assembly.isComponentOf_iff_open.mp hcomp
  have eGroup : ↥Q ≃* ↥(Q.map e.toMonoidHom) :=
    Q.equivMapOfInjective e.toMonoidHom e.injective
  have hlabT : GGHasLabel (⟨.twA, 3, n⟩ : LargeEvenLabel)
      ((Q.map e.toMonoidHom) ⧸ Subgroup.center (Q.map e.toMonoidHom)) :=
    ggHasLabel_quotCenter_of_mulEquiv eGroup hlab
  have hA3 : (A : GL (Fin 6) K) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) c := by
    simpa [A] using hd3
  obtain ⟨t, ht1, ht3⟩ :=
    primeForm_cubeRoot_normOne_of_component_twA3 h hq3 A hA3 hcompOpen hlabT
  let s : GL (Fin 6) K := Matrix.GeneralLinearGroup.scalar (Fin 6) t⁻¹
  let d' : GL (Fin 6) K := s * d
  have hscomm : ∀ x : GL (Fin 6) K, s * x = x * s := by
    have hcenter : s ∈ Subgroup.center (GL (Fin 6) K) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨t⁻¹, rfl⟩
    intro x
    exact (Subgroup.mem_center_iff.mp hcenter x).symm
  have hd'3 : d' ^ 3 = 1 := by
    have hpow : d' ^ 3 = s ^ 3 * d ^ 3 :=
      Commute.mul_pow ((commute_iff_eq s d).mpr (hscomm d)) 3
    rw [hpow, ← map_pow, hd3, ← map_mul]
    have hone : (t⁻¹) ^ 3 * c = 1 := by
      rw [inv_pow, ht3, inv_mul_cancel]
    rw [hone, map_one]
  have hd' : IsHermIsometry (2 ^ n) ((d' : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := by
    have htinv : (t⁻¹ : Kˣ) ^ (2 ^ n + 1) = 1 := by rw [inv_pow, ht1, inv_one]
    have hval : ((t⁻¹ : Kˣ) : K) ^ (2 ^ n + 1) = 1 := by
      rw [← Units.val_pow_eq_pow_val, htinv, Units.val_one]
    have hnorm : h.norm ((t⁻¹ : Kˣ) : K) = 1 := by
      rw [UnitaryFieldData.norm_eq_pow]
      simpa [Units.val_inv_eq_inv_val] using hval
    have hs : Matrix.GeneralLinearGroup.scalar (Fin 6) t⁻¹ ∈
        primeFormUnitary h (idGram K 6) := by
      rw [mem_primeFormUnitary, Matrix.GeneralLinearGroup.coe_scalar,
        scalar_barTranspose_mul_mul, hnorm, one_smul]
    have hd'U : (Matrix.GeneralLinearGroup.scalar (Fin 6) t⁻¹ * d) ∈
        primeFormUnitary h (idGram K 6) := mul_mem hs hdm
    have hg := (gramForm_isometry_iff h (idGram K 6) _).mpr
      (mem_primeFormUnitary.mp hd'U)
    intro v w
    simpa [d', s, IsHermIsometry, gramForm_apply, dotProduct, idGram, h.bar_apply]
      using hg v w
  have hδ' : IsConjBy d' δ' := by
    intro x x' hx
    apply hδ x x'
    rw [hx]
    dsimp [d', s]
    rw [_root_.mul_inv_rev]
    calc (Matrix.GeneralLinearGroup.scalar (Fin 6) t⁻¹ * d) * x *
          (d⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin 6) t⁻¹)⁻¹) =
        Matrix.GeneralLinearGroup.scalar (Fin 6) t⁻¹ * (d * x * d⁻¹) *
          (Matrix.GeneralLinearGroup.scalar (Fin 6) t⁻¹)⁻¹ := by group
      _ = d * x * d⁻¹ := by
        rw [hscomm (d * x * d⁻¹)]
        dsimp [s]
        group
  obtain ⟨μ, hμ, hm⟩ :=
    cubeEigen_finrank_eq_four_of_component_twA3 hK hq3 hd' hd'3 hδ' hQ hlab
  have hd_eq : d = Matrix.GeneralLinearGroup.scalar (Fin 6) t * d' := by
    dsimp [d', s]
    rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  have heigs : cubeEigen d ((t : K) * μ) = cubeEigen d' μ := by
    rw [hd_eq, cubeEigen, cubeEigen]
    have htoLin : Matrix.toLin' (((Matrix.GeneralLinearGroup.scalar (Fin 6) t * d' :
          GL (Fin 6) K)) : Matrix (Fin 6) (Fin 6) K) =
        (t : K) • Matrix.toLin' ((d' : GL (Fin 6) K) :
          Matrix (Fin 6) (Fin 6) K) := by
      rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.toLin'_mul]
      have hscalar : Matrix.toLin' (Matrix.scalar (Fin 6) (t : K)) =
          (t : K) • (LinearMap.id : Module.End K (Fin 6 → K)) := by
        ext v
        simp [Matrix.toLin'_apply, Matrix.scalar_apply, Matrix.mulVec_diagonal]
      rw [hscalar]
      ext v
      simp
    rw [htoLin, Module.End.eigenspace_def, Module.End.eigenspace_def]
    have hsub : (t : K) •
          Matrix.toLin' ((d' : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) -
          ((t : K) * μ) • (1 : Module.End K (Fin 6 → K)) =
        (t : K) • (Matrix.toLin' ((d' : GL (Fin 6) K) :
          Matrix (Fin 6) (Fin 6) K) - μ • (1 : Module.End K (Fin 6 → K))) := by
      rw [smul_sub, smul_smul]
    rw [hsub, LinearMap.ker_smul _ (t : K) t.ne_zero]
  have hμne : μ ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by norm_num : 3 ≠ 0)] at hμ
    exact zero_ne_one hμ
  refine ⟨(t : K) * μ, mul_ne_zero t.ne_zero hμne, ?_, ?_⟩
  · have ht3K : (t : K) ^ 3 = (c : K) := by
      rw [← Units.val_pow_eq_pow_val, ht3]
    rw [mul_pow, ht3K, hμ, mul_one]
  · rw [heigs]
    exact hm

theorem largeEvenLabelAll_twA5_notDvdSCJ (n : ℕ) (hn1 : 1 ≤ n) (hpq : 3 ∣ 2 ^ n + 1) :
    LargeEvenLabelAll (⟨.twA, 5, n⟩ : LargeEvenLabel) fun R _ I _ =>
      GGTorusAutNotDvdSCJ 3 (⟨.twA, 3, n⟩ : LargeEvenLabel) R I 4 27 := by
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, hKfield, hKfinite, hKcard, hQ⟩ := hQ
  refine ⟨K, hKfield, hKfinite, hKcard, hQ, ?_⟩
  change GGTorusAutNotDvdSCJ 3 (⟨.twA, 3, n⟩ : LargeEvenLabel)
    (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ n)))
    (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ n)))
      (LargeEvenGUSet (Fin 6) K (2 ^ n))) 4 27
  intro L' _ _ ψ hψ hker hperf A hA hAI h3 hle hsc hcomp
  classical
  let h : UnitaryFieldData 2 n K :=
    CFSG.AGLEmbedding.ToralCensus.unitaryFieldData_of_card_eq_sq hKcard hn1
  have : CharP K 2 := h.charP
  let U : Subgroup (GL (Fin 6) K) := LargeEvenSUGroup (Fin 6) K (2 ^ n)
  have hdq : ((6 : ℕ), 2 ^ n) ≠ (3, 2) := by
    intro he
    have h := congrArg Prod.fst he
    simp only at h
    omega
  have hS : LargeEvenGUSet (Fin 6) K (2 ^ n) ⊆
      Subgroup.normalizer ((LargeEvenSUGroup (Fin 6) K (2 ^ n)) : Set (GL (Fin 6) K)) :=
    TableBUE.gu_subset_normalizer (d := 6) h
  obtain ⟨e, heA, J', hJ'comp, hJ'lab⟩ := hcomp
  obtain ⟨φ, hφI, hφe⟩ := hAI e heA
  have hJdesc : CFSG.Assembly.IsComponentOf (J'.map ψ) (ggFix φ) :=
    LayerCC.isComponentOf_map_ggFix hψ hker (fun x => (hφe x).symm) hJ'comp
  have hJ'perf : commutator ↥J' = ⊤ := hJ'comp.2.2.1
  let fJ : ↥J' →* ↥(J'.map ψ) :=
    MonoidHom.codRestrict (ψ.comp J'.subtype) (J'.map ψ)
      (fun x => Subgroup.mem_map_of_mem ψ x.2)
  have hfJsurj : Function.Surjective fJ := by
    rintro ⟨y, hy⟩
    rw [Subgroup.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have hfJker : fJ.ker ≤ Subgroup.center ↥J' := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx1 : ψ (x : L') = 1 := congrArg Subtype.val hx
    have hxcenter : (x : L') ∈ Subgroup.center L' := hker (MonoidHom.mem_ker.mpr hx1)
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.mp hxcenter (y : L'))
  obtain ⟨eJ⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.center_quot_equiv_of_surjective
    hJ'perf fJ hfJsurj hfJker
  have hJlab : GGHasLabel (⟨.twA, 3, n⟩ : LargeEvenLabel)
      ((J'.map ψ) ⧸ Subgroup.center (J'.map ψ)) :=
    ggHasLabel_of_mulEquiv eJ.symm hJ'lab
  obtain ⟨M, hMgu, hφeq⟩ := TableB.exists_eq_projConj hS hφI
  let δ' : MulAut (PSUg 6 K (2 ^ n)) :=
    TableB.projConj (LargeEvenSUGroup (Fin 6) K (2 ^ n)) ⟨M, hS hMgu⟩
  have hQ' : CFSG.Assembly.IsComponentOf (J'.map ψ) (ggAutFixedSubgroup δ') := by
    dsimp [δ']
    rw [← hφeq]
    exact hJdesc
  have hφ3 : φ ^ 3 = 1 := by
    ext r
    obtain ⟨l, rfl⟩ := hψ r
    have he3 : e ^ 3 = 1 := hA.2 e heA
    have h1 : (φ ^ 3) (ψ l) = ψ ((e ^ 3) l) := by
      simp [pow_succ, MulAut.mul_apply, hφe]
    rw [h1, he3]
    rfl
  have hM3N : M ^ 3 ∈ Subgroup.normalizer
      ((LargeEvenSUGroup (Fin 6) K (2 ^ n)) : Set (GL (Fin 6) K)) :=
    Subgroup.pow_mem _ (hS hMgu) 3
  have hM3proj : TableB.projConj (LargeEvenSUGroup (Fin 6) K (2 ^ n))
      ⟨M ^ 3, hM3N⟩ = 1 := by
    have hEq : (⟨M ^ 3, hM3N⟩ : Subgroup.normalizer
        ((LargeEvenSUGroup (Fin 6) K (2 ^ n)) : Set (GL (Fin 6) K))) =
        ⟨M, hS hMgu⟩ ^ 3 := Subtype.ext rfl
    rw [hEq, map_pow, ← hφeq]
    exact hφ3
  have hM3scal : (M ^ 3 : GL (Fin 6) K) ∈ LargeEvenScalars (Fin 6) K :=
    TableBUE.mem_scalars_of_projConj_eq_one h hKcard (by norm_num) hdq
      Nat.prime_three hpq hM3proj
  have hM3range : (M ^ 3 : GL (Fin 6) K) ∈
      (Matrix.GeneralLinearGroup.scalar (Fin 6)).range := by
    rwa [largeEvenScalars_def] at hM3scal
  obtain ⟨c, hc⟩ := hM3range
  have hc' : M ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) c := hc.symm
  obtain ⟨u, hU'U⟩ := TableBU63.exists_unitary_of_gu (h := h) (M := M) hMgu
  let U' : GL (Fin 6) K := Matrix.GeneralLinearGroup.scalar (Fin 6) u * M
  have hucomm : ∀ x : GL (Fin 6) K,
      Matrix.GeneralLinearGroup.scalar (Fin 6) u * x =
        x * Matrix.GeneralLinearGroup.scalar (Fin 6) u := by
    have hcenter : Matrix.GeneralLinearGroup.scalar (Fin 6) u ∈
        Subgroup.center (GL (Fin 6) K) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨u, rfl⟩
    intro x
    exact (Subgroup.mem_center_iff.mp hcenter x).symm
  have hU'3 : U' ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) (u ^ 3 * c) := by
    have hpow : U' ^ 3 = (Matrix.GeneralLinearGroup.scalar (Fin 6) u) ^ 3 * M ^ 3 :=
      Commute.mul_pow ((commute_iff_eq _ M).mpr (hucomm M)) 3
    rw [hpow, ← map_pow, hc', ← map_mul]
  have hU'herm : IsHermIsometry (2 ^ n) ((U' : GL (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K) := by
    have hg := (gramForm_isometry_iff h (idGram K 6) _).mpr
      (mem_primeFormUnitary.mp hU'U)
    intro v w
    simpa [U', IsHermIsometry, gramForm_apply, dotProduct, idGram, h.bar_apply]
      using hg v w
  have hδ'M : IsConjBy M δ' := by
    intro x x' hx
    dsimp [δ']
    rw [TableB.projConj_mk]
    congr 1
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    exact hx.symm
  have hδ'U' : IsConjBy U' δ' := by
    intro x x' hx
    apply hδ'M x x'
    rw [hx]
    dsimp [U']
    rw [_root_.mul_inv_rev]
    calc (Matrix.GeneralLinearGroup.scalar (Fin 6) u * M) * x *
          (M⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin 6) u)⁻¹) =
        Matrix.GeneralLinearGroup.scalar (Fin 6) u * (M * x * M⁻¹) *
          (Matrix.GeneralLinearGroup.scalar (Fin 6) u)⁻¹ := by group
      _ = M * x * M⁻¹ := by
        rw [hucomm (M * x * M⁻¹)]
        group
  obtain ⟨μ, hμne, hμcube, hm⟩ :=
    exists_four_eigenspace_of_component_twA3 hKcard hpq hU'herm hU'3 hδ'U' hQ' hJlab
  let X : Subgroup (MulAut (PSUg 6 K (2 ^ n))) := CFSG.StandardType.TypeA.inducedSub ψ A
  have hX : IsElemAbelian 3 X := CFSG.StandardType.TypeA.isElemAbelian_inducedSub hψ hA
  have hNscal : ∀ u : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin 6) u ∈
      Subgroup.normalizer ((LargeEvenSUGroup (Fin 6) K (2 ^ n)) :
        Set (GL (Fin 6) K)) :=
    fun u => TableB.scalar_mem_normalizer (LargeEvenSUGroup (Fin 6) K (2 ^ n)) ⟨u, rfl⟩
  have hρscal : ∀ u : Kˣ,
      TableB.projConj (LargeEvenSUGroup (Fin 6) K (2 ^ n))
        ⟨Matrix.GeneralLinearGroup.scalar (Fin 6) u, hNscal u⟩ = 1 :=
    fun u => TableB.projConj_of_scalar (LargeEvenSUGroup (Fin 6) K (2 ^ n)) ⟨u, rfl⟩
  have hkerρ : (TableB.projConj (LargeEvenSUGroup (Fin 6) K (2 ^ n))).ker ≤
      (LargeEvenScalars (Fin 6) K).subgroupOf
        (Subgroup.normalizer ((LargeEvenSUGroup (Fin 6) K (2 ^ n)) :
          Set (GL (Fin 6) K))) := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    exact TableBUE.mem_scalars_of_projConj_eq_one h hKcard (by norm_num) hdq
      Nat.prime_three hpq hx
  have hU'N : U' ∈ Subgroup.normalizer
      ((LargeEvenSUGroup (Fin 6) K (2 ^ n)) : Set (GL (Fin 6) K)) := by
    have hscalN : Matrix.GeneralLinearGroup.scalar (Fin 6) u ∈
        Subgroup.normalizer ((LargeEvenSUGroup (Fin 6) K (2 ^ n)) :
          Set (GL (Fin 6) K)) := hNscal u
    exact Subgroup.mul_mem _ hscalN (hS hMgu)
  have hU'X : TableB.projConj (LargeEvenSUGroup (Fin 6) K (2 ^ n))
      ⟨U', hU'N⟩ ∈ X := by
    have hscalN : Matrix.GeneralLinearGroup.scalar (Fin 6) u ∈
        Subgroup.normalizer ((LargeEvenSUGroup (Fin 6) K (2 ^ n)) :
          Set (GL (Fin 6) K)) := hNscal u
    have hsplit : (⟨U', hU'N⟩ : Subgroup.normalizer
        ((LargeEvenSUGroup (Fin 6) K (2 ^ n)) : Set (GL (Fin 6) K))) =
        ⟨Matrix.GeneralLinearGroup.scalar (Fin 6) u, hscalN⟩ *
          ⟨M, hS hMgu⟩ := Subtype.ext rfl
    rw [hsplit, map_mul,
      TableB.projConj_of_scalar (LargeEvenSUGroup (Fin 6) K (2 ^ n)) ⟨u, rfl⟩, one_mul,
      ← hφeq]
    exact CFSG.StandardType.TypeA.mem_inducedSub.mpr ⟨e, heA, hφe⟩
  have hE : U' ∈ (X.comap (TableB.projConj (LargeEvenSUGroup (Fin 6) K (2 ^ n)))).map
      (Subgroup.normalizer ((LargeEvenSUGroup (Fin 6) K (2 ^ n)) :
        Set (GL (Fin 6) K))).subtype :=
    Subgroup.mem_map.mpr ⟨⟨U', hU'N⟩, Subgroup.mem_comap.mpr hU'X, rfl⟩
  have hcommGL : ∀ g ∈ (X.comap (TableB.projConj
        (LargeEvenSUGroup (Fin 6) K (2 ^ n)))).map
        (Subgroup.normalizer ((LargeEvenSUGroup (Fin 6) K (2 ^ n)) :
          Set (GL (Fin 6) K))).subtype,
      ∀ h ∈ (X.comap (TableB.projConj
        (LargeEvenSUGroup (Fin 6) K (2 ^ n)))).map
        (Subgroup.normalizer ((LargeEvenSUGroup (Fin 6) K (2 ^ n)) :
          Set (GL (Fin 6) K))).subtype, g * h = h * g :=
    CFSG.StandardType.TypeA.PGLTor.pairwise_commute_of_isElemAbelian_comap_map_of_eigenspace_four
      (N := Subgroup.normalizer ((LargeEvenSUGroup (Fin 6) K (2 ^ n)) :
        Set (GL (Fin 6) K))) hNscal hρscal hkerρ hX hE hμne hm
  have hBcomm : ∀ b ∈ fullMatrixPreimage U ψ A, ∀ c ∈ fullMatrixPreimage U ψ A,
      b * c = c * b := by
    intro b hb c hc
    apply Subtype.ext
    have hb' : (b : GL (Fin 6) K) ∈ (X.comap (TableB.projConj
        (LargeEvenSUGroup (Fin 6) K (2 ^ n)))).map
        (Subgroup.normalizer ((LargeEvenSUGroup (Fin 6) K (2 ^ n)) :
          Set (GL (Fin 6) K))).subtype :=
      Subgroup.mem_map.mpr ⟨b, hb, rfl⟩
    have hc' : (c : GL (Fin 6) K) ∈ (X.comap (TableB.projConj
        (LargeEvenSUGroup (Fin 6) K (2 ^ n)))).map
        (Subgroup.normalizer ((LargeEvenSUGroup (Fin 6) K (2 ^ n)) :
          Set (GL (Fin 6) K))).subtype :=
      Subgroup.mem_map.mpr ⟨c, hc, rfl⟩
    simpa using hcommGL b.1 hb' c.1 hc'
  have hdiv : Nat.card (ggAutomizer (MulAut.conj : L' →* MulAut L').range A) ∣
      Nat.factorial 6 :=
    card_ggAutomizer_dvd_factorial_of_matConjImage_elemAbelian (d := 6) (by norm_num)
      (LargeEvenSUGroup (Fin 6) K (2 ^ n)) ψ hψ hker hperf hA hkerρ hS hAI hBcomm
  intro h27
  have h720 : Nat.factorial 6 = 720 := by norm_num
  rw [h720] at hdiv
  exact (by norm_num : ¬ 27 ∣ 720) (h27.trans hdiv)

end CFSG.StandardType

end
