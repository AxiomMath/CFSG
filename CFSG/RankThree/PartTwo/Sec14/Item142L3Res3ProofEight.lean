module

public import CFSG.RankThree.PartTwo.Sec14.Item142L3Res2ProofNine
public import Certificates.Certificate8178
import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.PartTwo.Sec14.L3PGLU27

open Matrix CFSG.RankThree.PartTwo.Sec4 CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.SeitzGeneration (heisC heisD heisB12 blockOneGL blockOneMat)
open CFSG.LieType.SeitzGeneration.HeisSmall
open CFSG.ClassicalGroups.UnitaryFlag (unitarySU mem_unitarySU_iff)
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.RankThree.PartTwo.Sec14.L3PGLU

variable {K : Type} [Field K]

theorem isPrimitiveRoot_qOmega {F : Type} [Field F] [NoCubeRoot F] :
    IsPrimitiveRoot (QExt.omega : QExt F) 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := orderOf_eq_prime (QExt.omega_pow_three (F := F)) QExt.omega_ne_one
  rw [← h]
  exact IsPrimitiveRoot.orderOf _

theorem blockOneGL_mem_unitarySU {p f : ℕ} (h : UnitaryFieldData p f K) {g : GL (Fin 2) K}
    (hg : g ∈ unitarySU p f K 2) : blockOneGL g ∈ unitarySU p f K 3 := by
  obtain ⟨hdet, hu⟩ := (mem_unitarySU_iff h).1 hg
  rw [mem_unitarySU_iff h, CFSG.LieType.SeitzGeneration.coe_blockOneGL]
  refine ⟨?_, ?_⟩
  · rw [blockOneMat, Matrix.det_fin_three]
    rw [Matrix.det_fin_two] at hdet
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, Matrix.head_fin_const]
    linear_combination hdet
  · have e00 := congrFun (congrFun hu 0) 0
    have e01 := congrFun (congrFun hu 0) 1
    have e10 := congrFun (congrFun hu 1) 0
    have e11 := congrFun (congrFun hu 1) 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.map_apply,
      Matrix.one_apply_eq, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
      Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at e00 e01 e10 e11
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [blockOneMat, Matrix.mul_apply, Fin.sum_univ_three, e00, e01, e10, e11]

@[expose] def MatIn {p f : ℕ} (H : Subgroup (unitarySU p f K 3)) (A : Matrix (Fin 3) (Fin 3) K) :
    Prop :=
  ∃ g ∈ H, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = A

theorem matIn_evalW {p f : ℕ} {H : Subgroup (unitarySU p f K 3)} {L : Type} [Field L]
    (ι : L →+* K) {letters : List (M3 L)} (hl : ∀ x ∈ letters, MatIn H (toMat ι x)) :
    ∀ w : List ℕ, MatIn H (toMat ι (evalW letters w))
  | [] => ⟨1, H.one_mem, by rw [evalW, toMat_one]; rfl⟩
  | i :: w => by
    rw [evalW, toMat_mul]
    obtain ⟨g', hg', hgg'⟩ := matIn_evalW ι hl w
    have hi : MatIn H (toMat ι (letters.getD i 1)) := by
      by_cases hi : i < letters.length
      · rw [List.getD_eq_getElem _ _ hi]
        exact hl _ (List.getElem_mem hi)
      · rw [List.getD_eq_default _ _ (not_lt.1 hi), toMat_one]
        exact ⟨1, H.one_mem, rfl⟩
    obtain ⟨g, hg, hgg⟩ := hi
    exact ⟨g * g', H.mul_mem hg hg', by rw [← hgg, ← hgg']; rfl⟩

theorem heisB12_le_of_cover_matIn {p f : ℕ} {L : Type} [Field L] [DecidableEq L] [Fintype L]
    (h : UnitaryFieldData p f K) (ι : L →+* K) (hι : Function.Surjective ι) {q : ℕ}
    (hq : p ^ f = q) {H : Subgroup (unitarySU p f K 3)} {letters : List (M3 L)}
    {ws₂ : List (List ℕ)} (hl : ∀ x ∈ letters, MatIn H (toMat ι x))
    (hcov : CoverOk q (ws₂.map (evalW letters))) : heisB12 p f K ≤ H := by
  subst hq
  have hL2 : ∀ x ∈ ws₂.map (evalW letters), MatIn H (toMat ι x) := by
    intro x hx
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hx
    exact matIn_evalW ι hl w
  intro g hg
  obtain ⟨A, hA, hgA⟩ := CFSG.LieType.SeitzGeneration.mem_heisB12.1 hg
  obtain ⟨hdet, hu⟩ := (mem_unitarySU_iff h).1 hA
  obtain ⟨e10, e11, enorm⟩ := su2_entries h hdet hu
  obtain ⟨a, ha⟩ := hι ((A : Matrix (Fin 2) (Fin 2) K) 0 0)
  obtain ⟨b, hb⟩ := hι ((A : Matrix (Fin 2) (Fin 2) K) 0 1)
  have hn : a * a ^ p ^ f + b * b ^ p ^ f = 1 := by
    apply ι.injective
    simp only [map_add, map_mul, map_pow, ha, hb, enorm, map_one]
  obtain ⟨g', hg', hgg⟩ := hL2 _ (hcov a b hn)
  have hmat : toMat ι (blockM3 (p ^ f) a b) = ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [hgA]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [toMat, blockM3, ha, hb, e10, e11]
  have : g' = g := Subtype.ext (Units.ext (hgg.trans hmat))
  exact this ▸ hg'

section Main

variable {p f : ℕ} [Finite K] (hπ : false = false → UnitaryFieldData p f K)
  (hK : PiField false p f K) (hq : ModThree false (p ^ f))
  {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {β : K} {cβ : GL (Fin 3) K}
  (hcβ : cβ ∈ glPi false 3 (p ^ f) K) (hd : diagTau hτ ∈ glPi false 3 (p ^ f) K)
  (hcβm : (cβ : Matrix (Fin 3) (Fin 3) K) = heisC β)

include hK hq hτ1 hcβm in
theorem torusU_le_sSup (hβ : ¬ ∃ μ : K, μ ^ 3 = β) {n : ℕ} (hn : n < 3) :
    (torusU false p f K (cβ * diagTau hτ ^ n)).map (projOf (slPi false 3 (p ^ f) K)) ≤
      sSup (invSet142 (Res8Hess.conjM' hπ hcβ) (Res8Hess.conjM' hπ hd)) := by
  have h3 : (3 : K) ≠ 0 := hK.three_ne_zero hq
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    norm_num at hτ
  set τu : Kˣ := Units.mk0 τ hτ0 with hτu
  have hτu' : (τu : K) = τ := rfl
  have hL3 : ((cβ * diagTau hτ ^ n : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 3 =
      β • 1 := by
    rw [Units.val_mul, hcβm]
    interval_cases n
    · rw [pow_zero, Units.val_one, Matrix.mul_one]
      exact L3PGL.heisC_pow_three β
    · rw [pow_one]
      exact heisC_mul_diagTau_pow_three hτ β
    · exact heisC_mul_diagTau_sq_pow_three hτ β
  have h1 : cβ * (cβ * diagTau hτ ^ n) * cβ⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin 3) ((τu ^ 2) ^ n) * (cβ * diagTau hτ ^ n) := by
    refine conj_eq_scalar_mul ?_
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hτu', Units.val_mul, hcβm]
    exact heisC_mul_heisC_mul_pow hτ β n
  have h2 : diagTau hτ * (cβ * diagTau hτ ^ n) * (diagTau hτ)⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin 3) τu * (cβ * diagTau hτ ^ n) := by
    refine conj_eq_scalar_mul ?_
    rw [hτu', Units.val_mul, hcβm]
    exact diagTau_mul_heisC_mul_pow hτ β n
  exact le_sSup (torusU_mem_invSet142 hπ hτ hτ1 h3 hcβ hd hL3 hβ h1 h2)

omit [Finite K] in
theorem toMat_line_eq {L : Type} [Field L] [DecidableEq L] [Fintype L] (ι : L →+* K)
    {ω₀ α₀ : L} (hιω : ι ω₀ = τ) (hcβm' : (cβ : Matrix (Fin 3) (Fin 3) K) = heisC (ι α₀))
    {M : M3 L} (hM : M ∈ torusLineList ω₀ α₀) :
    ∃ n : ℕ, n < 3 ∧ toMat ι M = (τ ^ 2) ^ n •
      ((cβ * diagTau hτ ^ n : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  simp only [torusLineList, List.mem_cons, List.not_mem_nil, or_false] at hM
  have hD : toMat ι (dM3 ω₀) = τ ^ 2 • ((diagTau hτ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
    by rw [toMat_dM3_heisD, hιω, heisD_eq_smul hτ]
  rcases hM with rfl | rfl | rfl
  · refine ⟨0, by norm_num, ?_⟩
    rw [pow_zero, pow_zero, one_smul, Units.val_mul, Units.val_one, Matrix.mul_one, hcβm',
      toMat_cM3]
  · refine ⟨1, by norm_num, ?_⟩
    rw [pow_one, pow_one, toMat_mul, toMat_cM3, hD, Units.val_mul, hcβm', Matrix.mul_smul]
  · refine ⟨2, by norm_num, ?_⟩
    rw [toMat_mul, toMat_mul, toMat_cM3, hD, Units.val_mul, hcβm', Units.val_pow_eq_pow_val]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, sq]

include hK hq hτ1 hcβm in
theorem heisB12_le_comap_of_eight
    (h8 : p ^ f = 8) (hβ : ¬ ∃ μ : K, μ ^ 3 = β) :
    heisB12 p f K ≤ (sSup (invSet142 (Res8Hess.conjM' hπ hcβ) (Res8Hess.conjM' hπ hd))).comap
      (suToPsu p f K) := by
  classical
  have h := hπ rfl
  set N := sSup (invSet142 (Res8Hess.conjM' hπ hcβ) (Res8Hess.conjM' hπ hd)) with hN
  have hq3 : 3 ∣ p ^ f + 1 := by rw [h8]; norm_num
  have hprim : IsPrimitiveRoot τ 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have ho : orderOf τ = 3 := orderOf_eq_prime hτ hτ1
    rw [← ho]
    exact IsPrimitiveRoot.orderOf τ
  obtain ⟨ι, hι, hιω⟩ := exists_ringHom_omega (L := Q8) h hq3 (by rw [card_q8, h8])
    isPrimitiveRoot_qOmega hprim
  have hβN : β ^ (p ^ f + 1) = 1 := by
    have hU := (mem_glPi_false h).mp hcβ
    have e := congrFun (congrFun hU 2) 2
    rw [hcβm] at e
    simp [heisC, Matrix.mul_apply, Fin.sum_univ_three] at e
    rw [pow_succ, ← h.bar_apply]
    exact e
  have hcheck := (Certificates.certificate8178 :
    torusCheck 8 QExt.omega outerLetters8 torusTable8 = true)
  unfold torusCheck at hcheck
  rw [Bool.and_eq_true, List.all_eq_true] at hcheck
  obtain ⟨htab, hcovα⟩ := hcheck
  obtain ⟨β₀, rfl⟩ := hι β
  have hβ₀ : β₀ ^ (8 + 1) = 1 := by
    apply ι.injective
    rw [map_pow, map_one, ← h8]
    exact hβN
  have hβc₀ : ¬ ∃ μ : Q8, μ ^ 3 = β₀ := by
    rintro ⟨μ, hμ⟩
    exact hβ ⟨ι μ, by rw [← map_pow, hμ]⟩
  obtain ⟨e, he, heα⟩ := of_decide_eq_true hcovα β₀ hβ₀ hβc₀
  have hent := htab e he
  unfold torusEntryOk at hent
  rw [Bool.and_eq_true, List.all_eq_true] at hent
  obtain ⟨hgens, hwords⟩ := hent
  rw [heα] at hgens
  have hG : ∀ G ∈ e.gens, MatIn (N.comap (suToPsu p f K)) (toMat ι G) := by
    intro G hG
    obtain ⟨hdet, hu, M, hM, hc⟩ := of_decide_eq_true (hgens G hG)
    have hdet' : (toMat ι G).det = 1 := by rw [toMat_det, hdet, map_one]
    have hu' : ((toMat ι G).map h.bar)ᵀ * toMat ι G = 1 := by
      have hu8 : (G.map (· ^ (p ^ f))).transpose * G = 1 := by rw [h8]; exact hu
      rw [← toMat_transpose_map h, ← toMat_mul, hu8, toMat_one]
    let g : GL (Fin 3) K := Matrix.SpecialLinearGroup.toGL ⟨toMat ι G, hdet'⟩
    have hgU : g ∈ unitarySU p f K 3 := (mem_unitarySU_iff h).2 ⟨hdet', hu'⟩
    refine ⟨⟨g, hgU⟩, ?_, rfl⟩
    obtain ⟨n, hn, hMn⟩ := toMat_line_eq hτ ι hιω hcβm hM
    have hτ0 : (τ ^ 2) ^ n ≠ 0 := pow_ne_zero _ (pow_ne_zero _ (by
      rintro rfl
      norm_num at hτ))
    have hcomm : toMat ι G * toMat ι M = toMat ι M * toMat ι G := by
      rw [← toMat_mul, hc, toMat_mul]
    rw [hMn, Matrix.mul_smul, Matrix.smul_mul] at hcomm
    have hcomm' := smul_right_injective _ hτ0 hcomm
    set x : slPi false 3 (p ^ f) K := ⟨g, hgU⟩ with hx
    have hxT : x ∈ torusU false p f K (cβ * diagTau hτ ^ n) := by
      rw [mem_torusU]
      apply Units.ext
      rw [Units.val_mul, Units.val_mul]
      exact hcomm'.symm
    have hmem := torusU_le_sSup hπ hK hq hτ hτ1 hcβ hd hcβm (by
      rintro ⟨μ, hμ⟩
      exact hβ ⟨μ, hμ⟩) hn ⟨x, hxT, rfl⟩
    exact hmem
  have hwords' : e.words.map (evalW e.gens) = outerLetters8 := of_decide_eq_true hwords
  have hl : ∀ x ∈ outerLetters8, MatIn (N.comap (suToPsu p f K)) (toMat ι x) := by
    intro x hx
    rw [← hwords'] at hx
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hx
    exact matIn_evalW ι hG w
  have hcov : CoverOk 8 (words2_8.map (evalW outerLetters8)) := by
    have hc := (Certificates.certificate9709 :
      outerCheck 8 QExt.omega outerLetters8 words2_8 outerTable8 = true)
    unfold outerCheck at hc
    rw [Bool.and_eq_true, Bool.and_eq_true] at hc
    exact of_decide_eq_true hc.1.1
  exact heisB12_le_of_cover_matIn h ι hι h8 hl hcov

include hK hq hτ1 hcβm in
theorem genStdU_eight
    (h8 : p ^ f = 8) (hβ : ¬ ∃ μ : K, μ ^ 3 = β) :
    sSup (invSet142 (Res8Hess.conjM' hπ hcβ) (Res8Hess.conjM' hπ hd)) = ⊤ := by
  have h := hπ rfl
  have hfin := finite_pgl (K := K)
  have : Fact p.Prime := ⟨h.prime⟩
  set N := sSup (invSet142 (Res8Hess.conjM' hπ hcβ) (Res8Hess.conjM' hπ hd)) with hN
  set ρ := projOf (slPi false 3 (p ^ f) K) with hρ
  have hq2 : p ^ f ≠ 2 := by omega
  have hB12 := heisB12_le_comap_of_eight hπ hK hq hτ hτ1 hcβ hd hcβm h8 hβ
  have hβbar : h.bar β * β = 1 := by
    have hU := (mem_glPi_false h).mp hcβ
    have e := congrFun (congrFun hU 2) 2
    rw [hcβm] at e
    simpa [heisC, Matrix.mul_apply, Fin.sum_univ_three] using e
  have hBN : ∀ g : GL (Fin 2) K, ∀ hg : g ∈ unitarySU p f K 2,
      ρ (⟨blockOneGL g, blockOneGL_mem_unitarySU h hg⟩ : slPi false 3 (p ^ f) K) ∈ N := by
    intro g hg
    have h12 : (⟨blockOneGL g, blockOneGL_mem_unitarySU h hg⟩ : unitarySU p f K 3) ∈
        heisB12 p f K := by
      rw [heisB12, Subgroup.mem_subgroupOf]
      exact ⟨g, hg, rfl⟩
    exact hB12 h12
  have hB : ∀ g : GL (Fin 2) K, g ∈ unitarySU p f K 2 → blockOneGL g ∈ normGU hπ N :=
    fun g hg => mem_normGU_of_projOf_mem hπ (hBN g hg)
  have hcQ : cβ ∈ normGU hπ N := cβ_mem_normGU hπ hτ hcβ hd
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
  have hJdet : (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := by
    simp [Matrix.det_fin_two_of]
  set J : GL (Fin 2) K := Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; -1, 0] hJdet with hJ
  have hJU : J ∈ unitarySU p f K 2 := by
    rw [mem_unitarySU_iff h]
    refine ⟨by simp [J, Matrix.det_fin_two_of], ?_⟩
    change ((!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) K).map h.bar)ᵀ * !![0, 1; -1, 0] = 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hJ1 : ρ (⟨blockOneGL J, blockOneGL_mem_unitarySU h hJU⟩ : slPi false 3 (p ^ f) K) ≠ 1 := by
    intro e
    rw [projOf_eq_one_iff] at e
    obtain ⟨t, ht⟩ := e
    have h01 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 1) ht
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at h01
    rw [Matrix.diagonal_apply_ne _ (by decide)] at h01
    have hb : ((blockOneGL J : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 1 = 1 := by
      rw [CFSG.LieType.SeitzGeneration.coe_blockOneGL]
      simp [blockOneMat, J]
    change (0 : K) = ((blockOneGL J : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 1 at h01
    rw [hb] at h01
    exact zero_ne_one h01
  have := hnorm
  have := hsimple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hbot | htop
  · exact absurd (hbot ▸ hBN J hJU : _ ∈ (⊥ : Subgroup _)) (by
      rw [Subgroup.mem_bot]
      exact hJ1)
  · exact htop

end Main

end CFSG.RankThree.PartTwo.Sec14.L3PGLU27
