module

public import CFSG.LocalAnalysis.StandardType.GGBstarLIDUnitFieldR
public import CFSG.LocalAnalysis.StandardType.GGBstarLIDUnit63Frame

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

namespace LID63

open CFSG.Assembly Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher InndiagSU TableBUI TableBUD LIDUF
  CFSG.HardMathSupport.Foote.ModuleExclusions
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open CFSG.SectionRank.OddCover (diagHom coe_diagHom diagHom_injective det_diagHom)

variable {K : Type} [Field K] [Finite K] {n : ℕ}

theorem ggFieldInnR_unitary_63 (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n)
    (hpq : 3 ∣ 2 ^ n + 1) :
    GGFieldInnR 3 3 (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ n)))
        (LargeEvenGUSet (Fin 6) K (2 ^ n))) := by
  classical
  intro Eb Eh hEbI hEb hr h3 hV hle hEh ⟨f, hfEh, hfI⟩
  set h := TableBU.unitaryFieldData_of_card hK hn with hh
  have hd : 3 ≤ 6 := by norm_num
  have hd1 : 1 ≤ 6 := by norm_num
  have hdq : ((6 : ℕ), 2 ^ n) ≠ (3, 2) := fun he => by
    have := congrArg Prod.fst he
    simp only at this
    omega
  have hq : ¬((6 : ℕ) = 3 ∧ 2 ^ n = 2) := fun ⟨h1, _⟩ => by omega
  have hp : Nat.Prime 3 := Nat.prime_three
  have := Fact.mk hp
  have : NeZero 3 := ⟨hp.ne_zero⟩
  have : CharP K 2 := h.charP
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hEbD : Eb ≤ inndiagU h hd1 := fun e he => congr_mem_primeFormD h hd1 hK (hEbI he)
  obtain ⟨Q, hQ, hfr⟩ := exists_frame_inndiag63 hK hpq hEb hEbD h3 hV
  set Wb := frameWeights h Q hQ hd1 3 Eb with hWb
  obtain ⟨V, hV1, hV2, hEbV⟩ := hV
  have hcinj := mulAut_conj_injective (TableBUE.center_proj_eq_bot hK hd hdq)
  set φ₀ := (MulAut.conj : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ n)) →* MulAut _).comp
    (frameMk h Q hQ) with hφ₀
  have hkerφ₀ : φ₀.ker ≤ Subgroup.center ↥(unitarySU 2 n K 6) := by
    intro u hu
    apply ker_frameMk_le_center h Q hQ
    exact hcinj (by rw [map_one]; exact hu)
  set V' := V.map (MulAut.conj : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ n)) →* MulAut _)
    with hV'
  have hV'1 : V' ≠ ⊥ := by
    rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ hcinj]
    exact hV1
  have hV'2 : IsPGroup 2 V' := hV2.map _
  have hV'φ : V' ≤ φ₀.range := by
    rintro _ ⟨v, -, rfl⟩
    obtain ⟨u, rfl⟩ := frameMk_surjective h Q hQ v
    exact ⟨u, rfl⟩
  have hconjE : ∀ (α : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ n))))
      (v : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ n))),
      α * MulAut.conj v * α⁻¹ = MulAut.conj (α v) := by
    intro α v
    ext y
    simp only [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv, MulAut.inv_apply,
      MulEquiv.apply_symm_apply]
  have hBV : Eb ≤ Subgroup.normalizer (V' : Set (MulAut _)) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨v, hv, rfl⟩
      rw [hconjE]
      exact ⟨e v, hEbV e he v hv, rfl⟩
    · rintro ⟨v, hv, hve⟩
      have hy : y = MulAut.conj (e⁻¹ v) := by
        rw [← hconjE, hve]
        group
      rw [hy]
      exact ⟨e⁻¹ v, hEbV _ (Eb.inv_mem he) v hv, rfl⟩
  obtain ⟨i, j, hij, hpair⟩ :=
    SURepair.exists_framePair_of_twoSubgroup h hkerφ₀ hV'1 hV'2 hV'φ hBV
  have hacts : ∀ (e : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ n)))) σ,
      FrameAct h Q hQ e σ → (∀ k, ((σ k : Kˣ) : K) ^ (2 ^ n + 1) = 1) →
        SURep.GGFrameActs φ₀ e σ := by
    intro e σ hfrσ hσn
    refine ⟨hσn, fun s s' hss' => ?_⟩
    change e * MulAut.conj (frameMk h Q hQ s) * e⁻¹ = MulAut.conj (frameMk h Q hQ s')
    rw [hconjE, hfrσ.apply s s' hss']
  have hWbij : ∀ σ ∈ Wb, σ i = σ j := by
    rintro σ ⟨-, -, hσn, e, he, hfrσ⟩
    exact hpair e he σ (hacts e σ hfrσ hσn)
  have hfD : f ∉ inndiagU h hd1 := fun hf => hfI (mem_conjImage_of_mem_inndiagU h hf)
  have hfp : f ^ 3 = 1 := hEh.2 f hfEh
  obtain ⟨B, hB, hsl⟩ := exists_isSemilin h hd hq f
  set φ := fieldFactorU h hd hq f with hφ
  have hφp : φ ^ 3 = 1 := by rw [hφ, ← map_pow, hfp, map_one]
  have hφ1 : φ ≠ 1 := by
    intro h1
    apply hfD
    rw [← ker_fieldFactorU h hd hq]
    exact h1
  have hφord : orderOf φ = 3 := orderOf_eq_prime hφp hφ1
  have hφb : ∀ x, φ (h.bar x) = h.bar (φ x) := fun x => by
    rw [h.bar_apply, h.bar_apply, map_pow]
  have hsl' := hsl.frame h Q hQ
  set B' := Q⁻¹ * B * glAut φ Q with hB'
  have hB'u : B' ∈ primeFormUnitary h (idGram K 6) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hQ) hB)
      (glAut_mem_primeFormUnitary h (isPrimeFormGram_one (K := K) (n := 6)) φ hQ)
  have hB'mat : adjM h.bar (B' : Matrix (Fin 6) (Fin 6) K) * (B' : Matrix (Fin 6) (Fin 6) K) = 1 :=
    adjM_mul_self_of_mem hB'u
  have hconj : ∀ σ ∈ Wb, ∃ c : Kˣ,
      B' * diagHom 6 σ = Matrix.GeneralLinearGroup.scalar (Fin 6) c * diagHom 6 σ * B' := by
    rintro σ ⟨-, hσp, hσn, e, he, hfrσ⟩
    exact exists_conj_eq_smul_of_commute h hK hd hdq hp hpq hQ hB'u hφp hsl' hσp hσn hfrσ
      (TableB.IsElemAbelian.comm hEh hfEh (hle he))
  have hN1 : IsSemilin (frameMk h Q hQ) 1 (semilinNorm B' φ 3) 1 := by
    have := hsl'.pow h hB'u 3
    rwa [hfp, hφp] at this
  obtain ⟨c₀, hc₀⟩ := mem_scalars_of_isSemilin_one h hK hd hdq hp hpq Q hQ
    (semilinNorm_mem h hB'u φ 3) hN1
  have hcoe : ((Matrix.GeneralLinearGroup.scalar (Fin 6) c₀ : GL (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K) = Matrix.diagonal (fun _ => ((c₀ : Kˣ) : K)) := by
    simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  have hNmat : Ai φ (B' : Matrix (Fin 6) (Fin 6) K) 3 =
      ((c₀ : Kˣ) : K) • (1 : Matrix (Fin 6) (Fin 6) K) := by
    rw [← coe_semilinNorm, ← hc₀, hcoe, Matrix.smul_one_eq_diagonal]
  have hc₀q : ((c₀ : Kˣ) : K) ^ (2 ^ n + 1) = 1 := by
    have hu := adjM_mul_self_of_mem (semilinNorm_mem h hB'u φ 3)
    rw [← hc₀, hcoe, adjM_diagonal, Matrix.diagonal_mul_diagonal] at hu
    have := congrFun (congrFun hu ⟨0, by omega⟩) ⟨0, by omega⟩
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at this
    rw [h.bar_apply, ← pow_succ] at this
    exact this
  set W : Set (Fin 6 → K) := {τ | ∃ σ ∈ Wb, τ = fun k => ((σ k : Kˣ) : K)} with hW
  have hWij : ∀ τ ∈ W, τ i = τ j := by
    rintro τ ⟨σ, hσ, rfl⟩
    exact congrArg (fun u : Kˣ => (u : K)) (hWbij σ hσ)
  have hWp : ∀ τ ∈ W, ∀ k, τ k ^ 3 = 1 := by
    rintro τ ⟨σ, ⟨-, hσp, -, -⟩, rfl⟩ k
    rw [← Units.val_pow_eq_pow_val, hσp k, Units.val_one]
  have hWcoe : ∀ σ : Fin 6 → Kˣ, ((diagHom 6 σ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      Matrix.diagonal (fun k => ((σ k : Kˣ) : K)) := fun σ => rfl
  have hnorm1 : ∀ c : K, c ^ (2 ^ n + 1) = 1 → c * h.bar c = 1 := fun c hc => by
    rw [h.bar_apply, ← pow_succ']
    exact hc
  have hEbU : ∀ e ∈ Eb, ∃ σ : Fin 6 → Kˣ, (∀ k, ((σ k : Kˣ) : K) ^ (2 ^ n + 1) = 1) ∧
      FrameAct h Q hQ e σ ∧ (fun k => ((σ k : Kˣ) : K)) ∈ W := by
    intro e he
    obtain ⟨σ, h0, hσp, hσn, hfrσ⟩ := hfr e he
    exact ⟨σ, hσn, hfrσ, σ, ⟨h0, hσp, hσn, e, he, hfrσ⟩, rfl⟩
  by_cases hc1 : ∀ σ ∈ Wb, B' * diagHom 6 σ = diagHom 6 σ * B'
  ·
    have hcomm : ∀ τ ∈ W, (B' : Matrix (Fin 6) (Fin 6) K) * Matrix.diagonal τ =
        Matrix.diagonal τ * (B' : Matrix (Fin 6) (Fin 6) K) := by
      rintro τ ⟨σ, hσ, rfl⟩
      have := congrArg (fun g : GL (Fin 6) K => (g : Matrix (Fin 6) (Fin 6) K)) (hc1 σ hσ)
      simpa [Units.val_mul, hWcoe σ] using this
    obtain ⟨v, hv0, hviso, hveig, μ, hμq, hμ⟩ := exists_eigen_isotropic h hK hn hp hφord hφb
      hB'mat hc₀q hNmat W hij hWij hcomm
    set U : Matrix (Fin 6) (Fin 1) K := Matrix.of fun k _ => v k with hU
    have hUU : adjM h.bar U * U = 0 := by
      ext a b
      simp only [Matrix.mul_apply, adjM, Matrix.transpose_apply, Matrix.map_apply, hU,
        Matrix.of_apply, Matrix.zero_apply]
      exact hviso
    obtain ⟨k, l, hkl, hk, hl⟩ : ∃ k l : Fin 6, k ≠ l ∧ v k ≠ 0 ∧ v l ≠ 0 := by
      by_contra hcon
      push Not at hcon
      obtain ⟨k₀, hk₀⟩ : ∃ k, v k ≠ 0 := by
        by_contra h0
        push Not at h0
        exact hv0 (funext h0)
      have hsingle : ∀ l, l ≠ k₀ → v l = 0 := fun l hl => hcon k₀ l (Ne.symm hl) hk₀
      have h1 : LIDUF.herm h.bar v v = h.bar (v k₀) * v k₀ := by
        unfold LIDUF.herm
        rw [Finset.sum_eq_single k₀]
        · intro l _ hl
          rw [hsingle l hl, map_zero, zero_mul]
        · simp
      rw [h1] at hviso
      rcases mul_eq_zero.mp hviso with h2 | h2
      · exact hk₀ ((map_eq_zero_iff h.bar h.bar.injective).mp h2)
      · exact hk₀ h2
    have hns : tvGL h.bar hUU ∉ LargeEvenScalars (Fin 6) K := by
      refine tvGL_not_mem_scalars h.bar hUU hkl ?_
      have : tv h.bar U k l = v k * h.bar (v l) := by
        simp [tv, Matrix.add_apply, Matrix.mul_apply, adjM, Matrix.one_apply, hkl, hU]
      rw [this]
      exact mul_ne_zero hk (fun h0 => hl ((map_eq_zero_iff h.bar h.bar.injective).mp h0))
    have hnormσ : ∀ c : K, c ^ (2 ^ n + 1) = 1 → tv h.bar (c • U) = tv h.bar U :=
      fun c hc => tv_smul_unit h.bar (hnorm1 c hc) U
    obtain ⟨m, hm1, hm2, hEbm, hfm⟩ := exists_fixed_involution h Q hQ U hUU hns
      (Eb := Eb) (fun e he => by
        obtain ⟨σ, hσn, hfrσ, hσW⟩ := hEbU e he
        refine ⟨σ, hσn, hfrσ, ?_⟩
        have heq : Matrix.diagonal (fun k => ((σ k : Kˣ) : K)) * U = ((σ i : Kˣ) : K) • U := by
          ext a b
          have := congrFun (hveig _ hσW) a
          simpa [Matrix.diagonal_mul, hU, Matrix.smul_apply, Matrix.mulVec_diagonal] using this
        rw [heq]
        exact hnormσ _ (hσn i)) hB'u hsl' hφb (by
        have heq : (B' : Matrix (Fin 6) (Fin 6) K) * U.map φ = μ • U := by
          ext a b
          have := congrFun hμ a
          simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.map_apply, hU,
            Matrix.smul_apply] using this
        rw [heq]
        exact hnormσ _ hμq)
    exact exists_overgroup_of_fixed_involution hEbI hle hfEh hfI hm1 hm2 hEbm hfm
  ·
    push Not at hc1
    have hWc' : ∀ τ ∈ W, ∃ c : K, (B' : Matrix (Fin 6) (Fin 6) K) * Matrix.diagonal τ =
        c • (Matrix.diagonal τ * (B' : Matrix (Fin 6) (Fin 6) K)) := by
      rintro τ ⟨σ, hσ, rfl⟩
      obtain ⟨c, hc⟩ := hconj σ hσ
      refine ⟨(c : K), ?_⟩
      have := congrArg (fun g : GL (Fin 6) K => (g : Matrix (Fin 6) (Fin 6) K)) hc
      simp only [Units.val_mul, hWcoe σ, Matrix.GeneralLinearGroup.coe_scalar,
        Matrix.scalar_apply] at this
      rw [this, Matrix.smul_eq_diagonal_mul, Matrix.mul_assoc]
    have hnc : ∃ τ ∈ W, (B' : Matrix (Fin 6) (Fin 6) K) * Matrix.diagonal τ ≠
        Matrix.diagonal τ * (B' : Matrix (Fin 6) (Fin 6) K) := by
      obtain ⟨σ, hσ, hne⟩ := hc1
      refine ⟨_, ⟨σ, hσ, rfl⟩, fun heq => hne ?_⟩
      apply Units.ext
      simpa [Units.val_mul, hWcoe σ] using heq
    obtain ⟨U, hUU, hoff, hDU, hFU⟩ := exists_orbit_family h hp hφord hφb hpq hB'mat hc₀q hNmat
      W hWp hij hWij hWc' hnc
    have hns : tvGL h.bar hUU ∉ LargeEvenScalars (Fin 6) K :=
      tvGL_not_mem_scalars h.bar hUU hij.symm hoff
    obtain ⟨m, hm1, hm2, hEbm, hfm⟩ := exists_fixed_involution h Q hQ U hUU hns (Eb := Eb)
      (fun e he => by
        obtain ⟨σ, hσn, hfrσ, hσW⟩ := hEbU e he
        exact ⟨σ, hσn, hfrσ, hDU _ hσW⟩) hB'u hsl' hφb hFU
    exact exists_overgroup_of_fixed_involution hEbI hle hfEh hfI hm1 hm2 hEbm hfm

end LID63

end CFSG.StandardType

end
