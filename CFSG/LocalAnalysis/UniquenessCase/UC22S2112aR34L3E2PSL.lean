module

public import CFSG.LocalAnalysis.UniquenessCase.FundamentalLie
public import CFSG.Open.SignalizerFunctorDefs
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34L3E2Mat
import CFSG.LocalAnalysis.UniquenessCase.UC22FunCountAmbient
import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitAmbient
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherLinearAutNormal
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55L4Desc
public import CFSG.ClassicalInvolution.RouteD.TypeABridge
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd.Linear
public import CFSG.LocalAnalysis.SectionRank.SQT
import CFSG.GroupTheory.AutomorphismFixedSubgroupSimple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open

open CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.Phan CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17 (IsL2Over17)
open scoped MatrixGroups

private theorem uc22s2112r34_ordA_three_ne_two {q : ℕ} (hq : 3 ≤ q) (hodd : Odd q) :
    ordA 2 q ≠ ordA 1 q := by
  have h2 : ordA 2 q = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) / Nat.gcd 3 (q - 1) := by
    unfold ordA
    rw [show 2 * (2 + 1) / 2 = 3 by rfl, show Finset.Icc 2 (2 + 1) = {2, 3} by rfl,
      Finset.prod_pair (by norm_num)]
  have h1 : 2 * ordA 1 q = q * (q ^ 2 - 1) := by
    obtain ⟨m, hm⟩ := hodd
    rw [hm]
    unfold ordA
    rw [show 1 * (1 + 1) / 2 = 1 by rfl, show Finset.Icc 2 (1 + 1) = {2} by rfl,
      Finset.prod_singleton, pow_one]
    have hg : Nat.gcd 2 (2 * m + 1 - 1) = 2 := by
      rw [show 2 * m + 1 - 1 = 2 * m by omega]
      exact Nat.gcd_eq_left (Dvd.intro _ rfl)
    rw [hg]
    have hsq : (2 * m + 1) ^ 2 - 1 = 4 * (m * (m + 1)) := by
      rw [show (2 * m + 1) ^ 2 = 4 * (m * (m + 1)) + 1 by ring]; simp
    rw [hsq, show (2 * m + 1) * (4 * (m * (m + 1))) =
      2 * ((2 * m + 1) * (2 * (m * (m + 1)))) by ring,
      Nat.mul_div_cancel_left _ (by norm_num)]
  have hdiv : q ^ 3 ∣ ordA 2 q := by
    have hd : Nat.gcd 3 (q - 1) ∣ (q ^ 2 - 1) * (q ^ 3 - 1) := by
      have h1 : Nat.gcd 3 (q - 1) ∣ q - 1 := Nat.gcd_dvd_right _ _
      have h2 : q - 1 ∣ q ^ 2 - 1 := Nat.sub_one_dvd_pow_sub_one q 2
      have h3 : q - 1 ∣ q ^ 3 - 1 := Nat.sub_one_dvd_pow_sub_one q 3
      exact dvd_mul_of_dvd_left (h1.trans h2) _
    have hdN : Nat.gcd 3 (q - 1) ∣ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) :=
      hd.trans (dvd_mul_left _ _)
    have hmul : ordA 2 q * Nat.gcd 3 (q - 1) =
        q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
      rw [h2]
      exact Nat.div_mul_cancel hdN
    have hcopq : Nat.Coprime (q ^ 3) (q - 1) := by
      have h : Nat.Coprime q (q - 1) :=
        (Nat.coprime_self_sub_right (m := 1) (n := q) (by omega)).mpr
          (Nat.coprime_one_right q)
      exact h.pow_left 3
    have hcop : Nat.Coprime (q ^ 3) (Nat.gcd 3 (q - 1)) :=
      hcopq.of_dvd_right (Nat.gcd_dvd_right _ _)
    exact hcop.dvd_of_dvd_mul_right (by rw [hmul]; exact dvd_mul_right _ _)
  have hnot : ¬ q ^ 2 ∣ ordA 1 q := by
    intro h
    have h2' : q * q ∣ q * (q ^ 2 - 1) := by
      have hthis := h.mul_right 2
      rw [mul_comm (ordA 1 q) 2, h1] at hthis
      simpa [pow_two] using hthis
    have hqq : q ∣ q ^ 2 - 1 := Nat.dvd_of_mul_dvd_mul_left (k := q) (by omega) h2'
    have h3 : q ∣ 1 := by
      have hq2dvd : q ∣ q ^ 2 := dvd_pow_self q (by norm_num : 2 ≠ 0)
      have h4 := Nat.dvd_sub hq2dvd hqq
      have hq2pos : 1 ≤ q ^ 2 := Nat.one_le_pow 2 q (by omega)
      rwa [Nat.sub_sub_eq_min, min_eq_right hq2pos] at h4
    have := Nat.dvd_one.mp h3
    omega
  intro heq
  exact hnot (heq ▸ ((Nat.pow_dvd_pow q (by norm_num : 2 ≤ 3)).trans hdiv))

private theorem uc22s2112r34_blockMat_three {F : Type} [Field F] (A : Matrix (Fin 2) (Fin 2) F) :
    CFSG.ClassicalInvolution.Phan.blockMat 3 0 A =
      !![A 0 0, A 0 1, 0; A 1 0, A 1 1, 0; 0, 0, 1] := by
  ext a b
  rw [CFSG.ClassicalInvolution.Phan.blockMat_apply]
  fin_cases a <;> fin_cases b <;> simp

private theorem uc22s2112r34_fieldAutOdd_projectiveSL_notLinear
    {K : Type} [Field K] [Finite K] {n p f r : ℕ}
    (hp : p.Prime) (_hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) (hn : 3 ≤ n)
    (hr : r.Prime) (_hr2 : r ≠ 2)
    (θ : MulAut (projectiveSL n K)) (hθE : θ ∈ semilinearAutGroup n K)
    (hθD : θ ∉ linearAutGroup n K) (hθ : orderOf θ = r) :
    ∃ Y : Subgroup (projectiveSL n K), Y ≤ signalizerFixedSubgroup θ ∧
      IsSimpleGroup Y ∧ 2 ≤ CFSG.pRank p Y := by
  have _ : Fact p.Prime := ⟨hp⟩
  have : CharP K p := CFSG.SectionRank.ClassicalOdd.charP_of_card hK
  obtain ⟨hrf, σ, hσ, ⟨δ, -, hδ⟩, hcard⟩ :=
    CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.linear_prime_descent_char hp hf hn hK hr
      hθE hθD hθ
  let k := semilinearFixedSubfield σ
  have hf0 : 1 ≤ f / r := Nat.div_pos (Nat.le_of_dvd (by omega) hrf) hr.pos
  have : IsSimpleGroup (projectiveSL n k) :=
    CFSG.RankThree.PartOne.KCLinearSubfield.isSimpleGroup_projectiveSL hn
  let ι : projectiveSL n k →* projectiveSL n K :=
    δ.toMonoidHom.comp (CFSG.RankThree.PartOne.linearSubfieldInclusion n k)
  have hι : Function.Injective ι :=
    δ.injective.comp (CFSG.RankThree.PartOne.linearSubfieldInclusion_injective
      (by omega) k)
  have hfix : ∀ y, θ (ι y) = ι y := by
    intro y
    change θ (δ (CFSG.RankThree.PartOne.linearSubfieldInclusion n k y)) =
      δ (CFSG.RankThree.PartOne.linearSubfieldInclusion n k y)
    simp only [hδ, MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply]
    exact congrArg δ
      (CFSG.RankThree.PartOne.fieldAut_linearSubfieldInclusion
        (k := k) (σ := σ) (fun c hc => by
          change σ c = c at hc
          exact hc) y)
  have hrank : 2 ≤ CFSG.pRank p (projectiveSL n k) := by
    let e : projectiveSL n k ≃* CFSG.Assembly.LowTwoRank.StatedProj
        (CFSG.Assembly.LowTwoRank.StatedSL n k) :=
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL n k).symm.trans
        (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj n k)
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top,
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e]
    have h := CFSG.SectionRank.ClassicalOdd.le_pRank_SL (n := n) (a := 1) (b := 2)
      (by norm_num) (by omega) hcard
    omega
  exact CFSG.exists_simple_subgroup_le_fixed_of_injective ι hι θ hfix hrank


private theorem uc22s2112r34_linear_projective
    {F : Type} [Field F] [Finite F] {n : ℕ} (hn : n = 3) {r : ℕ} (hr : r.Prime) (hr3 : r ≠ 3)
    (_hrF : (r : F) ≠ 0) {g : GL (Fin n) F}
    (hconj : conjAut n F (g ^ 3) = 1)
    {i : SL(n, F)} {a : SL(n, F)} {A : SL(2, F)}
    (ha : a = (MulAut.conj i) (blockSL F n 2 0 (by omega) A))
    (hAdet : ((A : Matrix (Fin 2) (Fin 2) F) - 1).det ≠ 0)
    (hAr : A ^ r = 1)
    {θ' : MulAut (projectiveSL n F)} (hθ' : θ' = conjAut n F g)
    (hfixa : θ' (proj n F a) = proj n F a) :
    θ' ∈ (MulAut.conj : projectiveSL n F →* MulAut (projectiveSL n F)).range ∨
      ∃ R' : Subgroup (SL(n, F)), R' ∈ longRootSet (K := F) (by omega : 2 ≤ n) ∧
        ∀ x ∈ R', θ' (proj n F x) = proj n F x := by
  subst hn
  obtain ⟨c, hg3⟩ := (CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.conjAut_eq_one_iff
    (n := 3) (by norm_num : 3 ≤ 3) (g ^ 3)).mp hconj
  classical
  have har : a ^ r = 1 := by
    rw [ha, ← map_pow, ← map_pow, hAr, map_one, map_one]
  let B : SL(3, F) :=
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F g a
  have hBproj : proj 3 F B = proj 3 F a := by
    rw [← conjAut_proj (n := 3) (K := F) g a, ← hθ']
    exact hfixa
  have hmem : B⁻¹ * a ∈ scalars 3 F :=
    (proj_eq_proj_iff (n := 3) (K := F) (A := B) (B := a)).mp hBproj
  let ζ : SL(3, F) := (B⁻¹ * a)⁻¹
  have hζmem : ζ ∈ scalars 3 F := (scalars 3 F).inv_mem hmem
  have hζcenter : ζ ∈ Subgroup.center (SL(3, F)) := by
    rw [← scalars_eq_center]
    exact hζmem
  have hBζ : B = ζ * a := by
    have h1 : B⁻¹ = ζ⁻¹ * a⁻¹ := by
      show B⁻¹ = ((B⁻¹ * a)⁻¹)⁻¹ * a⁻¹
      group
    calc B = (B⁻¹)⁻¹ := by group
      _ = (ζ⁻¹ * a⁻¹)⁻¹ := by rw [h1]
      _ = a * ζ := by group
      _ = ζ * a := by rw [Subgroup.mem_center_iff.mp hζcenter a]
  obtain ⟨cc, hcc3, hζmat⟩ := mem_scalars.mp hζmem
  have hζ3 : ζ ^ 3 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, hζmat, ← map_pow]
    have hcc : ((cc : F) ^ 3) = 1 := by
      simpa using congrArg (fun u : Fˣ => (u : F)) hcc3
    rw [hcc, map_one, Matrix.SpecialLinearGroup.coe_one]
  have hBGL : (B : GL (Fin 3) F) = g * (a : GL (Fin 3) F) * g⁻¹ := by
    apply Units.ext
    change ((SpecialLinearGroup.toGL B : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((g * SpecialLinearGroup.toGL a * g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
    rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.coe_slConjugation]
    simp [Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
  have hB_r : B ^ r = 1 := by
    have h1 : (B : GL (Fin 3) F) ^ r = 1 := by
      rw [hBGL]
      have hconj : (g * (a : GL (Fin 3) F) * g⁻¹) ^ r =
          g * (a : GL (Fin 3) F) ^ r * g⁻¹ := by
        have h := map_pow (MulAut.conj g) (a : GL (Fin 3) F) r
        simpa only [MulAut.conj_apply] using h.symm
      rw [hconj]
      have haGL : (a : GL (Fin 3) F) ^ r = 1 := by
        have h := congrArg (fun z : SL(3, F) => (z : GL (Fin 3) F)) har
        simpa using h
      rw [haGL, mul_one, mul_inv_cancel]
    exact SpecialLinearGroup.toGL_injective (by simpa using h1)
  have hζr : ζ ^ r = 1 := by
    have hcomm : Commute ζ a := (Subgroup.mem_center_iff.mp hζcenter a).symm
    have hpow : (ζ * a) ^ r = ζ ^ r * a ^ r := hcomm.mul_pow r
    have h := hB_r
    rw [hBζ, hpow, har, mul_one] at h
    exact h
  have hcop : Nat.Coprime 3 r :=
    (Nat.coprime_primes Nat.prime_three hr).mpr (Ne.symm hr3)
  have hζ1 : ζ = 1 := (pow_eq_one_iff_of_coprime hcop).mp ⟨hζ3, hζr⟩
  have hB_eq : B = a := by rw [hBζ, hζ1, one_mul]
  let iG : GL (Fin 3) F := SpecialLinearGroup.toGL i
  let kG : GL (Fin 3) F :=
    SpecialLinearGroup.toGL (blockSL F 3 2 0 (by norm_num) A)
  let g' : GL (Fin 3) F := iG⁻¹ * g * iG
  have haG : (a : GL (Fin 3) F) = iG * kG * iG⁻¹ := by
    have h := congrArg (fun z : SL(3, F) => (z : GL (Fin 3) F)) ha
    simpa [iG, kG, MulAut.conj_apply] using h
  have hcommG : g' * kG * g'⁻¹ = kG := by
    calc g' * kG * g'⁻¹ =
          iG⁻¹ * (g * (iG * kG * iG⁻¹) * g⁻¹) * iG := by
          simp only [g']
          group
      _ = iG⁻¹ * (g * (a : GL (Fin 3) F) * g⁻¹) * iG := by rw [haG]
      _ = iG⁻¹ * (a : GL (Fin 3) F) * iG := by rw [← hBGL, hB_eq]
      _ = kG := by
          rw [haG]
          group
  have hg'3 : g' ^ 3 = GeneralLinearGroup.scalar (Fin 3) c := by
    calc g' ^ 3 = (iG⁻¹ * g * iG) ^ 3 := rfl
      _ = iG⁻¹ * g ^ 3 * iG := by
          rw [show iG⁻¹ * g * iG = (MulAut.conj iG⁻¹) g from by simp]
          rw [← map_pow, MulAut.conj_apply]
          simp
      _ = iG⁻¹ * GeneralLinearGroup.scalar (Fin 3) c * iG := by rw [hg3]
      _ = GeneralLinearGroup.scalar (Fin 3) c := by
          have hS : iG⁻¹ * GeneralLinearGroup.scalar (Fin 3) c =
              GeneralLinearGroup.scalar (Fin 3) c * iG⁻¹ :=
            (GeneralLinearGroup.scalar_commute c iG⁻¹).symm
          rw [hS, mul_assoc, inv_mul_cancel, mul_one]
  let gM : Matrix (Fin 3) (Fin 3) F := (g' : Matrix (Fin 3) (Fin 3) F)
  have hgMdet : gM.det ≠ 0 := GeneralLinearGroup.det_ne_zero g'
  have hgM3 : gM ^ 3 = Matrix.scalar (Fin 3) (c : F) := by
    have h := congrArg (fun z : GL (Fin 3) F => (z : Matrix (Fin 3) (Fin 3) F)) hg'3
    simpa [gM] using h
  have hcommM : gM *
      !![(A : Matrix (Fin 2) (Fin 2) F) 0 0, (A : Matrix (Fin 2) (Fin 2) F) 0 1, 0;
        (A : Matrix (Fin 2) (Fin 2) F) 1 0, (A : Matrix (Fin 2) (Fin 2) F) 1 1, 0; 0, 0, 1] =
      !![(A : Matrix (Fin 2) (Fin 2) F) 0 0, (A : Matrix (Fin 2) (Fin 2) F) 0 1, 0;
        (A : Matrix (Fin 2) (Fin 2) F) 1 0, (A : Matrix (Fin 2) (Fin 2) F) 1 1, 0; 0, 0, 1] *
        gM := by
    have h' : g' * kG = kG * g' := by
      calc g' * kG = (g' * kG * g'⁻¹) * g' := by group
        _ = kG * g' := by rw [hcommG]
    have h := congrArg (fun z : GL (Fin 3) F => (z : Matrix (Fin 3) (Fin 3) F)) h'
    have hb := uc22s2112r34_blockMat_three (A : Matrix (Fin 2) (Fin 2) F)
    simpa [gM, kG, CFSG.ClassicalInvolution.WeakCT.coe_blockSL, hb] using h
  obtain ⟨b, hbdet⟩ | ⟨P, μ, ν, hPdet, hPg⟩ :=
    uc22s2112r34_cube_or_conj_diag (K := F) (g := gM) hgMdet
      (c := (c : F)) hgM3 (A := (A : Matrix (Fin 2) (Fin 2) F)) hAdet hcommM
  · have hdetg' : (g' : Matrix (Fin 3) (Fin 3) F).det = b ^ 3 := hbdet
    have hdet : (g' : Matrix (Fin 3) (Fin 3) F).det = (g : Matrix (Fin 3) (Fin 3) F).det := by
      have hdetu : GeneralLinearGroup.det g' = GeneralLinearGroup.det g := by
        rw [show g' = iG⁻¹ * g * iG from rfl, map_mul, map_mul, map_inv]
        have hi1 : GeneralLinearGroup.det iG = 1 := by
          simp [iG]
        rw [hi1, inv_one, one_mul, mul_one]
      have := congrArg (fun u : Fˣ => (u : F)) hdetu
      simpa using this
    have hdetg : (g : Matrix (Fin 3) (Fin 3) F).det = b ^ 3 := by
      rw [← hdet]
      exact hdetg'
    have hb0 : b ≠ 0 := by
      intro h0
      apply hgMdet
      change (g' : Matrix (Fin 3) (Fin 3) F).det = 0
      rw [hdetg', h0]
      norm_num
    let s : SL(3, F) :=
      ⟨Matrix.scalar (Fin 3) b⁻¹ * (g : Matrix (Fin 3) (Fin 3) F), by
        rw [Matrix.det_mul, hdetg, Matrix.scalar_apply, Matrix.det_diagonal]
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        rw [inv_pow]
        exact inv_mul_cancel₀ (pow_ne_zero 3 hb0)⟩
    have hsGL : (s : GL (Fin 3) F) =
        GeneralLinearGroup.scalar (Fin 3) (Units.mk0 b hb0)⁻¹ * g := by
      apply Units.ext
      change (s : Matrix (Fin 3) (Fin 3) F) =
        Matrix.scalar (Fin 3) (((Units.mk0 b hb0)⁻¹ : Fˣ) : F) *
          (g : Matrix (Fin 3) (Fin 3) F)
      simp [s]
    have hconjS : conjAut 3 F (s : GL (Fin 3) F) = θ' := by
      rw [hsGL, map_mul, conjAut_scalar, one_mul, ← hθ']
    refine Or.inl ⟨proj 3 F s, ?_⟩
    rw [← conjAut_toGL s, hconjS]
  · let P2 : Matrix (Fin 3) (Fin 3) F := P
    have hP2det : P2.det = 1 := hPdet
    let P' : SL(3, F) := ⟨P2, hP2det⟩
    let j : SL(3, F) := i * P'
    let R' : Subgroup (SL(3, F)) :=
      (rootSL2 F (by norm_num : 2 ≤ 3)).map (MulAut.conj j).toMonoidHom
    refine Or.inr ⟨R', (mem_longRootSet_iff (by norm_num : 2 ≤ 3)).mpr ⟨j, rfl⟩, ?_⟩
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨A0, rfl⟩ := hk
    change θ' (proj 3 F (j * blockSL F 3 2 0 (by norm_num) A0 * j⁻¹)) =
      proj 3 F (j * blockSL F 3 2 0 (by norm_num) A0 * j⁻¹)
    let PG : GL (Fin 3) F := GeneralLinearGroup.mkOfDetNeZero P2 (by rw [hP2det]; norm_num)
    let Dmat : Matrix (Fin 3) (Fin 3) F := Matrix.diagonal ![μ, μ, ν]
    have hDdet : Dmat.det ≠ 0 := by
      have h1 := congrArg Matrix.det hPg
      rw [Matrix.det_mul, Matrix.det_mul, hPdet, mul_one, one_mul] at h1
      rw [← h1]
      exact hgMdet
    let DG : GL (Fin 3) F := GeneralLinearGroup.mkOfDetNeZero Dmat hDdet
    have hPgGL : g' * PG = PG * DG := by
      apply Units.ext
      change (g' : Matrix (Fin 3) (Fin 3) F) * P2 = P2 * Matrix.diagonal ![μ, μ, ν]
      simpa [PG, DG, P2, Dmat] using hPg
    have hDGk : ∀ A0 : SL(2, F),
        DG * (blockSL F 3 2 0 (by norm_num) A0 : GL (Fin 3) F) =
          (blockSL F 3 2 0 (by norm_num) A0 : GL (Fin 3) F) * DG := by
      intro A0
      apply Units.ext
      change Matrix.diagonal ![μ, μ, ν] * blockMat 3 0 (A0 : Matrix (Fin 2) (Fin 2) F) =
        blockMat 3 0 (A0 : Matrix (Fin 2) (Fin 2) F) * Matrix.diagonal ![μ, μ, ν]
      rw [uc22s2112r34_blockMat_three]
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [Matrix.diagonal_apply, Matrix.mul_apply, mul_comm]
    have hcommPG : ∀ A0 : SL(2, F),
        g' * (PG * (blockSL F 3 2 0 (by norm_num) A0 : GL (Fin 3) F) * PG⁻¹) =
          (PG * (blockSL F 3 2 0 (by norm_num) A0 : GL (Fin 3) F) * PG⁻¹) * g' := by
      intro A0
      have hg'eq : g' = PG * DG * PG⁻¹ := by
        calc g' = g' * PG * PG⁻¹ := by group
          _ = PG * DG * PG⁻¹ := by rw [hPgGL]
      calc g' * (PG * (blockSL F 3 2 0 (by norm_num) A0 : GL (Fin 3) F) * PG⁻¹)
          = (PG * DG * PG⁻¹) * (PG * (blockSL F 3 2 0 (by norm_num) A0 : GL (Fin 3) F) * PG⁻¹) := by
              rw [hg'eq]
        _ = PG * (DG * (blockSL F 3 2 0 (by norm_num) A0 : GL (Fin 3) F)) * PG⁻¹ := by group
        _ = PG * ((blockSL F 3 2 0 (by norm_num) A0 : GL (Fin 3) F) * DG) * PG⁻¹ := by rw [hDGk A0]
        _ = PG * (blockSL F 3 2 0 (by norm_num) A0 : GL (Fin 3) F) * PG⁻¹ *
              (PG * DG * PG⁻¹) := by group
        _ = (PG * (blockSL F 3 2 0 (by norm_num) A0 : GL (Fin 3) F) * PG⁻¹) * g' := by
              rw [hg'eq]
    have hji : (j : GL (Fin 3) F) = iG * PG := by
      apply Units.ext
      change ((i * P' : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
        (i : Matrix (Fin 3) (Fin 3) F) * P2
      rw [Matrix.SpecialLinearGroup.coe_mul]
    have hGL : g * (j * blockSL F 3 2 0 (by norm_num) A0 * j⁻¹) * g⁻¹ =
        j * blockSL F 3 2 0 (by norm_num) A0 * j⁻¹ := by
      have hg_eq : g = iG * g' * iG⁻¹ := by
        rw [show g' = iG⁻¹ * g * iG from rfl]
        group
      calc g * (j * blockSL F 3 2 0 (by norm_num) A0 * j⁻¹) * g⁻¹
          = (iG * g' * iG⁻¹) *
              ((iG * PG) * (blockSL F 3 2 0 (by norm_num) A0 : GL (Fin 3) F) * (iG * PG)⁻¹) *
              (iG * g'⁻¹ * iG⁻¹) := by
              rw [map_inv, hg_eq, hji]
              group
        _ = iG * (g' * (PG * (blockSL F 3 2 0 (by norm_num) A0 : GL (Fin 3) F) * PG⁻¹) * g'⁻¹) *
              iG⁻¹ := by group
        _ = iG * (PG * (blockSL F 3 2 0 (by norm_num) A0 : GL (Fin 3) F) * PG⁻¹) * iG⁻¹ := by
              have hX : g' * (PG * (blockSL F 3 2 0 (by norm_num) A0 : GL (Fin 3) F) * PG⁻¹) *
                    g'⁻¹ = PG * (blockSL F 3 2 0 (by norm_num) A0 : GL (Fin 3) F) * PG⁻¹ := by
                rw [hcommPG A0]
                group
              rw [hX]
        _ = (iG * PG) * (blockSL F 3 2 0 (by norm_num) A0 : GL (Fin 3) F) * (iG * PG)⁻¹ := by group
        _ = j * blockSL F 3 2 0 (by norm_num) A0 * j⁻¹ := by
              rw [map_inv, hji]
    have hsl : CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F g
        (j * blockSL F 3 2 0 (by norm_num) A0 * j⁻¹) =
          j * blockSL F 3 2 0 (by norm_num) A0 * j⁻¹ := by
      apply SpecialLinearGroup.toGL_injective
      rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation]
      simpa only [map_mul, map_inv] using hGL
    rw [hθ']
    rw [conjAut_proj]
    exact congrArg (proj 3 F) hsl



theorem uc22s2112r34_l3E2_trichotomy_psl {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .PSL 3 p f) (hX : CFSG.Blueprint.LieModel X .PSL 3 p f)
    (θ : MulAut X) (hθ3 : θ ^ 3 = 1)
    {K : Subgroup X} (hK : IsFundamentalOver (p ^ f) K) {x : X} (hxK : x ∈ K)
    (hxr : (orderOf x).Prime) (hx3 : orderOf x ≠ 3) (hxp : orderOf x ≠ p) (hθx : θ x = x) :
    θ ∈ (MulAut.conj : X →* MulAut X).range ∨
      (∃ K' : Subgroup X, IsFundamentalOver (p ^ f) K' ∧ K' ≤ signalizerFixedSubgroup θ) ∨
      ∃ Y : Subgroup X, Y ≤ signalizerFixedSubgroup θ ∧ IsSimpleGroup Y ∧ 2 ≤ CFSG.pRank p Y := by
  classical
  generalize hthree : (3 : ℕ) = n at hadm hX
  have hn : n = 2 + 1 := by omega
  subst hn
  have _ : Fact p.Prime := ⟨hp⟩
  have hf : 1 ≤ f := hadm.2.1
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hq3 : 3 ≤ p ^ f := by
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    exact hp3.trans (Nat.le_self_pow (by omega : f ≠ 0) p)
  have hoddq : Odd (p ^ f) := hpodd.pow
  have hZ : Subgroup.center X = ⊥ :=
    CFSG.ComponentClassification.RankTwoOddLie.center_eq_bot_of_simple
      (exists_noncommuting_of_isFundamentalOver hK)
  have hL2 : ¬ IsL2Over17 (X ⧸ Subgroup.center X) (p ^ f) := by
    intro hL2
    obtain ⟨r, f', hr, hr2, hq, hf', hm2⟩ := hL2
    have hcardX : Nat.card X = ordA 2 (p ^ f) :=
      CFSG.GH74.card_of_lieModel_PSL (by omega) hX
    have hcardQ : Nat.card (X ⧸ Subgroup.center X) = ordA 1 (r ^ f') :=
      CFSG.GH74.card_of_lieModel_PSL (by omega) hm2
    have hcardQ' : Nat.card (X ⧸ Subgroup.center X) = Nat.card X := by
      rw [hZ]
      exact Nat.card_congr (QuotientGroup.quotientBot (G := X)).toEquiv
    have heq : ordA 2 (p ^ f) = ordA 1 (p ^ f) := by
      calc ordA 2 (p ^ f) = Nat.card X := hcardX.symm
        _ = Nat.card (X ⧸ Subgroup.center X) := hcardQ'.symm
        _ = ordA 1 (r ^ f') := hcardQ
        _ = ordA 1 (p ^ f) := by rw [← hq]
    exact uc22s2112r34_ordA_three_ne_two hq3 hoddq heq
  obtain ⟨ψ, hψ, hker⟩ := CFSG.ClassicalInvolution.Upgrade.lieModelCentralCover
    .PSL (2 + 1) p f hp hp2 (by trivial) hadm X hX
  obtain ⟨R, hR, hRK, hRk⟩ :=
    exists_mem_fundamentalSubgroups_of_isFundamentalOver_general hp hp2 hadm hX
      (by trivial) (by simp) hL2 ψ hψ hker hK
  have hRlong : R ∈ longRootSet (K := GaloisField p f) (by norm_num : 2 ≤ 2 + 1) := by
    refine CFSG.ClassicalInvolution.RouteD.fundamentalSubgroups_psl_subset
      (m := 2) (F := GaloisField p f) (by norm_num) ?_
    change R ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups .PSL
      (CFSG.LieType.Universal.SpecialLinear.rootDatum 2 (GaloisField p f)) at hR
    exact hR
  obtain ⟨i, hi⟩ := (mem_longRootSet_iff (by norm_num : 2 ≤ 2 + 1)).mp hRlong
  obtain ⟨a, haR, hψa⟩ := Subgroup.mem_map.mp (hRK ▸ hxK)
  let as : SL(2 + 1, GaloisField p f) := a
  let ψs : SL(2 + 1, GaloisField p f) →* X := ψ
  let Rs : Subgroup (SL(2 + 1, GaloisField p f)) := R
  have hasR : as ∈ Rs := haR
  have hψas : ψs as = x := hψa
  have hRKs : K = Rs.map ψs := hRK
  have hRks : Rs ⊓ ψs.ker = ⊥ := hRk
  have hψss : Function.Surjective ψs := hψ
  obtain ⟨k, hkR, hka⟩ : ∃ k ∈ rootSL2 (GaloisField p f) (by norm_num : 2 ≤ 2 + 1),
      (MulAut.conj i) k = as := by
    have ha : as ∈ (rootSL2 (GaloisField p f) (by norm_num : 2 ≤ 2 + 1)).map
        (MulAut.conj i).toMonoidHom := by
      rw [← hi]
      exact hasR
    exact Subgroup.mem_map.mp ha
  obtain ⟨A, rfl⟩ := hkR
  have hka' : (MulAut.conj i) (blockSL (GaloisField p f) (2 + 1) 2 0 (by omega) A) = as := hka
  have hblockInj : Function.Injective (blockSL (GaloisField p f) (2 + 1) 2 0 (by omega)) := by
    intro B C hBC
    apply Subtype.ext
    apply CFSG.ClassicalInvolution.Phan.blockMat_injective (i := 0) (k := 2) (m := 2 + 1) (by omega)
    exact congrArg (fun z : SL(2 + 1, GaloisField p f) =>
      (z : Matrix (Fin (2 + 1)) (Fin (2 + 1)) (GaloisField p f))) hBC
  set r : ℕ := orderOf x with hr
  have hxr' : r.Prime := by rw [hr]; exact hxr
  have har : as ^ r = 1 := by
    have hmem : as ^ r ∈ Rs ⊓ ψs.ker := by
      refine ⟨Rs.pow_mem hasR r, ?_⟩
      show ψs (as ^ r) = 1
      rw [map_pow, hψas, hr, pow_orderOf_eq_one]
    rw [hRks] at hmem
    exact Subgroup.mem_bot.mp hmem
  have ha1 : as ≠ 1 := by
    intro h1
    have hx1 : x = 1 := by rw [← hψas, h1, map_one]
    exact hxr.ne_one (by rw [hr, hx1, orderOf_one])
  have hAr : A ^ r = 1 := by
    have h1 : (blockSL (GaloisField p f) (2 + 1) 2 0 (by omega) A) ^ r = 1 := by
      have h2 : (MulAut.conj i) ((blockSL (GaloisField p f) (2 + 1) 2 0 (by omega) A) ^ r) = 1 := by
        rw [map_pow, hka', har]
      exact (MulAut.conj i).injective (by simpa using h2)
    apply hblockInj
    rw [map_pow, h1, map_one]
  have hA1 : A ≠ 1 := by
    intro hA
    apply ha1
    rw [hA] at hka'
    simpa using hka'.symm
  have hrF : (r : GaloisField p f) ≠ 0 := by
    intro h0
    have hdvd : p ∣ r := (CharP.cast_eq_zero_iff (GaloisField p f) p r).mp h0
    have hpr : p = r := (Nat.prime_dvd_prime_iff_eq hp hxr').mp hdvd
    exact hxp (hpr.trans hr).symm
  have hAdet : ((A : Matrix (Fin 2) (Fin 2) (GaloisField p f)) - 1).det ≠ 0 := by
    refine uc22s2112r34_det_sub_one_ne_zero (A := (A : Matrix (Fin 2) (Fin 2) (GaloisField p f)))
      A.det_coe hrF ?_ ?_
    · have := congrArg (fun z : SL(2, GaloisField p f) =>
        (z : Matrix (Fin 2) (Fin 2) (GaloisField p f))) hAr
      simpa using this
    · intro h
      exact hA1 (Subtype.ext h)
  have hker_eq : scalars (2 + 1) (GaloisField p f) = ψs.ker := by
    refine le_antisymm ?_ ?_
    · intro s hs
      rw [MonoidHom.mem_ker]
      have hcenter : s ∈ Subgroup.center (SL(2 + 1, GaloisField p f)) := by
        rw [← scalars_eq_center]
        exact hs
      have hψcenter : ψs s ∈ Subgroup.center X := by
        rw [Subgroup.mem_center_iff]
        intro y
        obtain ⟨t, rfl⟩ := hψss y
        have hst : s * t = t * s := (Subgroup.mem_center_iff.mp hcenter t).symm
        rw [← map_mul, ← map_mul, hst]
      rw [hZ] at hψcenter
      exact Subgroup.mem_bot.mp hψcenter
    · intro s hs
      rw [scalars_eq_center (n := 2 + 1) (K := GaloisField p f)]
      exact hker hs
  let E : projectiveSL (2 + 1) (GaloisField p f) ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hker_eq).trans
      (QuotientGroup.quotientKerEquivOfSurjective (φ := ψs) hψss)
  have hEproj : ∀ s : SL(2 + 1, GaloisField p f),
      E (proj (2 + 1) (GaloisField p f) s) = ψs s := by
    intro s
    show (QuotientGroup.quotientKerEquivOfSurjective (φ := ψs) hψss)
      ((QuotientGroup.quotientMulEquivOfEq hker_eq)
        (QuotientGroup.mk' (scalars (2 + 1) (GaloisField p f)) s)) = ψs s
    rw [QuotientGroup.mk'_apply, QuotientGroup.quotientMulEquivOfEq_mk]
    exact QuotientGroup.kerLift_mk ψs s
  let θ' : MulAut (projectiveSL (2 + 1) (GaloisField p f)) := MulAut.congr E.symm θ
  have hθ'3 : θ' ^ 3 = 1 := by
    have h := congrArg (MulAut.congr E.symm) hθ3
    rw [map_pow, map_one] at h
    simpa [θ'] using h
  have hθx' : θ' (proj (2 + 1) (GaloisField p f) as) =
      proj (2 + 1) (GaloisField p f) as := by
    apply E.injective
    calc E (θ' (proj (2 + 1) (GaloisField p f) as)) =
          θ (E (proj (2 + 1) (GaloisField p f) as)) := by
          simp [θ', MulAut.congr_apply]
      _ = θ x := by rw [hEproj, hψas]
      _ = x := hθx
      _ = E (proj (2 + 1) (GaloisField p f) as) := by rw [hEproj, hψas]
  by_cases hD : θ' ∈ linearAutGroup (2 + 1) (GaloisField p f)
  · obtain ⟨g, hg⟩ := mem_linearAutGroup_iff.mp hD
    have hconj : conjAut (2 + 1) (GaloisField p f) (g ^ 3) = 1 := by
      rw [map_pow, hg, hθ'3]
    have ha : as = (MulAut.conj i) (blockSL (GaloisField p f) (2 + 1) 2 0 (by omega) A) :=
      hka'.symm
    obtain hinner | ⟨R', hR'long, hR'fix⟩ :=
      uc22s2112r34_linear_projective (F := GaloisField p f) (n := 2 + 1) rfl
        hxr' hx3 hrF (g := g) hconj (i := i) (a := as) (A := A) ha hAdet hAr
        (θ' := θ') hg.symm hθx'
    · obtain ⟨y, hy⟩ := hinner
      refine Or.inl ⟨E y, ?_⟩
      ext z
      obtain ⟨w, rfl⟩ := E.surjective z
      have h1 : E (θ' w) = θ (E w) := by
        simp [θ', MulAut.congr_apply]
      have h2 : θ' w = MulAut.conj y w := by rw [← hy]
      rw [← h1, h2]
      simp [MulAut.conj_apply]
    · have hR'fund : R' ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups .PSL
          (CFSG.ClassicalInvolution.Generic.modelUniv .PSL (2 + 1) p f hp).D := by
        have h := CFSG.ClassicalInvolution.RouteD.longRootSet_subset_fundamentalSubgroups_psl
          (m := 2) (F := GaloisField p f) (by norm_num) hR'long
        change R' ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups .PSL
          (CFSG.LieType.Universal.SpecialLinear.rootDatum 2 (GaloisField p f))
        exact h
      let K' : Subgroup X := R'.map ψs
      have hK'fund : IsFundamentalOver (p ^ f) K' :=
        ⟨.PSL, 2 + 1, p, f, hp, hp2, rfl, trivial, hadm, ψs, hψss,
          hker, R', hR'fund, rfl⟩
      have hK'le : K' ≤ signalizerFixedSubgroup θ := by
        rintro y ⟨s, hs, rfl⟩
        have hfixs : θ' (proj (2 + 1) (GaloisField p f) s) =
            proj (2 + 1) (GaloisField p f) s := hR'fix s hs
        calc θ (ψs s) = θ (E (proj (2 + 1) (GaloisField p f) s)) := by rw [hEproj]
          _ = E (θ' (proj (2 + 1) (GaloisField p f) s)) := by
                simp [θ', MulAut.congr_apply]
          _ = E (proj (2 + 1) (GaloisField p f) s) := by rw [hfixs]
          _ = ψs s := hEproj s
      exact Or.inr <| Or.inl ⟨K', hK'fund, hK'le⟩
  ·
    have hθ'ne : θ' ≠ 1 := fun h1 => hD (h1 ▸ (linearAutGroup (2 + 1) (GaloisField p f)).one_mem)
    have _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hθ'ord : orderOf θ' = 3 := orderOf_eq_prime hθ'3 hθ'ne
    have hθ'E : θ' ∈ semilinearAutGroup (2 + 1) (GaloisField p f) :=
      mem_semilinearAutGroup_of_pow_odd (by norm_num : 3 ≤ 2 + 1) (by decide : Odd 3) hθ'3
    have hK3 : Nat.card (GaloisField p f) = p ^ f :=
      CFSG.LieType.Catalog.card_galoisField p f hf
    obtain ⟨Y, hY, hYs, hYr⟩ :=
      uc22s2112r34_fieldAutOdd_projectiveSL_notLinear hp hp2 hf hK3
        (by norm_num : 3 ≤ 2 + 1) Nat.prime_three (by norm_num) θ' hθ'E hD hθ'ord
    let ι : Y →* X := E.toMonoidHom.comp Y.subtype
    have hι : Function.Injective ι := E.injective.comp Y.subtype_injective
    have hfix : ∀ y, θ (ι y) = ι y := by
      intro y
      have hy : θ' (y : projectiveSL (2 + 1) (GaloisField p f)) =
          (y : projectiveSL (2 + 1) (GaloisField p f)) := hY y.2
      have h2 : E (θ' (y : projectiveSL (2 + 1) (GaloisField p f))) =
          E (y : projectiveSL (2 + 1) (GaloisField p f)) := congrArg E hy
      have hcongr : E (θ' (y : projectiveSL (2 + 1) (GaloisField p f))) =
          θ (E (y : projectiveSL (2 + 1) (GaloisField p f))) := by
        simp [θ', MulAut.congr_apply]
      rw [hcongr] at h2
      simpa [ι] using h2
    exact Or.inr <| Or.inr <|
      CFSG.exists_simple_subgroup_le_fixed_of_injective ι hι θ hfix hYr

end CFSG.LocalAnalysis.UniquenessCase.UC22
