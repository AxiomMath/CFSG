module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniCubeDefs
import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniCubeEigen
import CFSG.Open.StatedAPI
import CFSG.HardMathSupport.Curtis.UnitaryLevi.IsotropicNotOrthogonal
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55StepH3UAlg
import CFSG.LinearAlgebra.LinearGroups.UnitaryFourOrder
import CFSG.LocalAnalysis.ComponentClassification.BurgoyneProjSlice
import CFSG.RankThree.SubgroupLists.SymplecticTransvections

public section

namespace CFSG.StandardType.TablePThreeKG

open Matrix Module CFSG CFSG.Assembly CFSG.AGLEmbedding

section UniCubeNe

open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LinearGroups
open CFSG.HardMathSupport.Curtis.UnitaryLevi
open CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.StepH3U

private lemma cube_root_pow_three' {K : Type} [Field K] {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) : ω ^ 3 = 1 := by
  have h : (ω - 1) * (ω ^ 2 + ω + 1) = ω ^ 3 - 1 := by ring
  rw [hω, mul_zero] at h
  exact sub_eq_zero.mp h.symm

private lemma three_ne_zero' {K : Type} [Field K] [CharP K 2] : (3 : K) ≠ 0 := by
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h : (3 : K) = (2 : K) + 1 := by norm_num
  rw [h, htwo, zero_add]
  exact one_ne_zero

private lemma sq_add_self_add_one_eq_zero_of_cube_eq_one_of_ne_one {K : Type} [Field K] {μ : K}
    (hμ : μ ^ 3 = 1) (hμ1 : μ ≠ 1) : μ ^ 2 + μ + 1 = 0 := by
  have h : (μ - 1) * (μ ^ 2 + μ + 1) = 0 := by
    calc (μ - 1) * (μ ^ 2 + μ + 1) = μ ^ 3 - 1 := by ring
      _ = 0 := by rw [hμ]; ring
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hμ1)

private lemma cube_roots_distinct' {K : Type} [Field K] [CharP K 2] {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) :
    (1 : K) ≠ ω ∧ (1 : K) ≠ ω ^ 2 ∧ ω ≠ ω ^ 2 := by
  have h3 : (3 : K) ≠ 0 := three_ne_zero'
  have hω0 : ω ≠ 0 := by
    intro h0
    rw [h0] at hω
    norm_num at hω
  have h1ω : (1 : K) ≠ ω := by
    intro h
    apply h3
    have h' : (1 : K) ^ 2 + 1 + 1 = 0 := by simpa [← h] using hω
    calc (3 : K) = (1 : K) ^ 2 + 1 + 1 := by norm_num
      _ = 0 := h'
  have h1ω2 : (1 : K) ≠ ω ^ 2 := by
    intro h
    have h1 : (1 : K) + ω + 1 = 0 := by simpa [← h] using hω
    have h2 : ω = 0 := by
      have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
      have h1' : (1 : K) + ω + 1 = ω + 2 := by ring
      rw [h1'] at h1
      rw [htwo, add_zero] at h1
      exact h1
    exact hω0 h2
  have hωω2 : ω ≠ ω ^ 2 := by
    intro h
    have hfac : ω * (ω - 1) = 0 := by
      have h2 : ω = ω * ω := by simpa [pow_two] using h
      calc ω * (ω - 1) = ω * ω - ω := by ring
        _ = 0 := by rw [← h2]; ring
    rcases mul_eq_zero.mp hfac with h0 | h1
    · exact hω0 h0
    · exact h1ω (sub_eq_zero.mp h1).symm
  exact ⟨h1ω, h1ω2, hωω2⟩

private lemma stdHermForm_eq_sum_of_q {K : Type} [Field K] {p f n : ℕ}
    (hE : UnitaryFieldData p f K) {q : ℕ} (hq : q = p ^ f) (x y : Fin n → K) :
    stdHermForm hE n x y = ∑ i, x i ^ q * y i := by
  rw [stdHermForm_apply]
  exact Finset.sum_congr rfl fun i _ => by rw [UnitaryFieldData.bar_apply, ← hq]

private lemma stdHermForm_eq_zero_imp_zero {K : Type} [Field K] {p f n : ℕ}
    (hE : UnitaryFieldData p f K) {x : Fin n → K}
    (h : ∀ y, stdHermForm hE n x y = 0) : x = 0 := by
  funext j
  have hsingle : (∑ i, hE.bar (x i) * (Pi.single j 1 : Fin n → K) i) = 0 := by
    simpa [stdHermForm_apply] using h (Pi.single j 1)
  have hsum : (∑ i, hE.bar (x i) * (Pi.single j 1 : Fin n → K) i) = hE.bar (x j) := by
    have h := Finset.sum_eq_single (s := Finset.univ) (a := j)
      (f := fun i => hE.bar (x i) * (Pi.single j 1 : Fin n → K) i)
      (fun i _ hij => by simp [Pi.single_eq_of_ne hij])
      (fun hj' => absurd (Finset.mem_univ j) hj')
    simpa using h
  rw [hsum] at hsingle
  exact (hE.bar_eq_zero_iff).mp hsingle

private lemma eigenspace_separatingLeft {K : Type} [Field K] [Finite K] [CharP K 2]
    {q n f : ℕ} (hK : Nat.card K = q ^ 2) (hq3 : 3 ∣ q + 1)
    (hE : UnitaryFieldData 2 f K) (hq : q = 2 ^ f)
    {d : GL (Fin n) K} (hd : IsHermIsometry q (d : Matrix (Fin n) (Fin n) K)) (hd3 : d ^ 3 = 1)
    {μ ω : K} (hμ : μ ^ 3 = 1) (hω : ω ^ 2 + ω + 1 = 0) :
    ((stdHermForm hE n).domRestrict₁₂ (cubeEigen d μ) (cubeEigen d μ)).SeparatingLeft := by
  classical
  obtain ⟨horth, hdimsum⟩ := uni_cube_eigen hK hq3 hd hd3
  have hdist : (1 : K) ≠ ω ∧ (1 : K) ≠ ω ^ 2 ∧ ω ≠ ω ^ 2 := cube_roots_distinct' hω
  have hω3 : ω ^ 3 = 1 := cube_root_pow_three' hω
  have hω23 : (ω ^ 2) ^ 3 = 1 := by
    rw [show (ω ^ 2) ^ 3 = (ω ^ 3) ^ 2 by ring, hω3, one_pow]
  have hsup : ({1, ω, ω ^ 2} : Finset K).SupIndep (cubeEigen d) :=
    (Module.End.eigenspaces_iSupIndep
      (Matrix.toLin' (d : Matrix (Fin n) (Fin n) K))).supIndep' _
  have hBC : Disjoint (cubeEigen d ω) (cubeEigen d (ω ^ 2)) :=
    (Module.End.eigenspaces_iSupIndep
      (Matrix.toLin' (d : Matrix (Fin n) (Fin n) K))).pairwiseDisjoint hdist.2.2
  have hABC : Disjoint (cubeEigen d 1) (cubeEigen d ω ⊔ cubeEigen d (ω ^ 2)) := by
    have h := hsup.disjoint_sup_sup (u := ({1} : Finset K)) (v := ({ω, ω ^ 2} : Finset K))
      (by simp) (by simp) (by simp [hdist.1, hdist.2.1])
    simpa [Finset.sup_insert, Finset.sup_singleton, Finset.sup_empty] using h
  have hthree : cubeEigen d 1 ⊔ cubeEigen d ω ⊔ cubeEigen d (ω ^ 2) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Module.finrank_fin_fun]
    have hdim1 := Submodule.finrank_sup_add_finrank_inf_eq (cubeEigen d 1)
      (cubeEigen d ω ⊔ cubeEigen d (ω ^ 2))
    rw [hABC.eq_bot, finrank_bot, add_zero] at hdim1
    have hdim2 := Submodule.finrank_sup_add_finrank_inf_eq (cubeEigen d ω) (cubeEigen d (ω ^ 2))
    rw [hBC.eq_bot, finrank_bot, add_zero] at hdim2
    rw [sup_assoc, hdim1, hdim2, ← add_assoc]
    exact hdimsum ω hω
  intro x hx
  apply Subtype.ext
  apply stdHermForm_eq_zero_imp_zero hE
  intro z
  have hthree' : cubeEigen d 1 ⊔ (cubeEigen d ω ⊔ cubeEigen d (ω ^ 2)) = ⊤ := by
    rw [← sup_assoc]; exact hthree
  have hperpμ : ∀ w ∈ cubeEigen d μ, stdHermForm hE n x.1 w = 0 := by
    intro w hw
    simpa only [LinearMap.domRestrict₁₂_apply] using hx ⟨w, hw⟩
  have hperp_other : ∀ lam : K, lam ^ 3 = 1 → lam ≠ μ → ∀ w ∈ cubeEigen d lam,
      stdHermForm hE n x.1 w = 0 := by
    intro lam hlam hne w hw
    rw [stdHermForm_eq_sum_of_q hE hq]
    exact horth μ lam hμ hlam (Ne.symm hne) (x : Fin n → K) x.2 w hw
  have key : ∀ lam : K, lam ^ 3 = 1 → ∀ w ∈ cubeEigen d lam, stdHermForm hE n x.1 w = 0 := by
    intro lam hlam w hw
    by_cases hle : lam = μ
    · rw [hle] at hw
      exact hperpμ w hw
    · exact hperp_other lam hlam hle w hw
  have hz : z ∈ cubeEigen d 1 ⊔ (cubeEigen d ω ⊔ cubeEigen d (ω ^ 2)) := by
    rw [hthree']; trivial
  obtain ⟨z1, hz1, z23, hz23, hzeq⟩ := Submodule.mem_sup.mp hz
  obtain ⟨z2, hz2, z3, hz3, hz23eq⟩ := Submodule.mem_sup.mp hz23
  have k1 : stdHermForm hE n x.1 z1 = 0 := key 1 (by norm_num) z1 hz1
  have k2 : stdHermForm hE n x.1 z2 = 0 := key ω hω3 z2 hz2
  have k3 : stdHermForm hE n x.1 z3 = 0 := key (ω ^ 2) hω23 z3 hz3
  rw [← hzeq, ← hz23eq]
  simp only [map_add]
  rw [k1, k2, k3]
  simp

theorem uni_cube_blocks_ne {K : Type} [Field K] [Finite K] [CharP K 2] {q n : ℕ}
    (hK : Nat.card K = q ^ 2) (hq3 : 3 ∣ q + 1) (hn : 4 ≤ n)
    {d : GL (Fin n) K} (hd : IsHermIsometry q (d : Matrix (Fin n) (Fin n) K)) (hd3 : d ^ 3 = 1)
    {μ ν : K} (hμ : μ ^ 3 = 1) (hν : ν ^ 3 = 1) (hne : μ ≠ ν)
    (hμ2 : 2 ≤ Module.finrank K (cubeEigen d μ)) (hν2 : 2 ≤ Module.finrank K (cubeEigen d ν)) :
    ¬ ∀ x : PSUg n K q, InCubeBlock d μ x ↔ InCubeBlock d ν x := by
  classical
  obtain ⟨f, hf1, hq⟩ := CFSG.AGLEmbedding.ToralCensus.exists_eq_two_pow_of_card_eq_sq hK
  have hE : UnitaryFieldData 2 f K :=
    ⟨Nat.prime_two, hf1, by rw [hK, hq, ← pow_mul, mul_comm]⟩
  have hbar_map : hE.bar = (fun c : K => c ^ q) := by
    funext c
    rw [UnitaryFieldData.bar_apply, ← hq]
  have homega : ∃ ω : K, ω ^ 2 + ω + 1 = 0 := by
    rcases eq_or_ne μ 1 with hμ1 | hμ1
    · exact ⟨ν, sq_add_self_add_one_eq_zero_of_cube_eq_one_of_ne_one hν (by rw [← hμ1]; exact hne.symm)⟩
    · exact ⟨μ, sq_add_self_add_one_eq_zero_of_cube_eq_one_of_ne_one hμ hμ1⟩
  obtain ⟨ω, hω⟩ := homega
  have hω3 : ω ^ 3 = 1 := cube_root_pow_three' hω
  let Vμ := cubeEigen d μ
  let H : Vμ →ₛₗ[hE.bar] Vμ →ₗ[K] K := (stdHermForm hE n).domRestrict₁₂ Vμ Vμ
  have hHsymm : H.IsSymm := (stdHermForm_isSymm hE n).domRestrict Vμ
  have hHsep : H.SeparatingLeft :=
    eigenspace_separatingLeft hK hq3 hE hq hd hd3 hμ hω
  have hμ2V : 2 ≤ Module.finrank K Vμ := hμ2
  have hVne : Vμ ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hμ2V
    omega
  haveI : Nontrivial Vμ := Submodule.nontrivial_iff_ne_bot.mpr hVne
  obtain ⟨w₀, hw₀⟩ : ∃ w : Vμ, w ≠ 0 := by
    obtain ⟨a, b, hab⟩ := exists_pair_ne Vμ
    by_cases ha : a = 0
    · exact ⟨b, fun hb => hab (by rw [ha, hb])⟩
    · exact ⟨a, ha⟩
  obtain ⟨u, hu_iso, hu_ne⟩ := exists_isotropic_not_orthogonal hE hHsymm hHsep hμ2V (w := w₀) hw₀
  have hw_iso : stdHermForm hE n (u : Fin n → K) (u : Fin n → K) = 0 := by
    have h : ((stdHermForm hE n).domRestrict₁₂ Vμ Vμ) u u = 0 := hu_iso
    simpa only [LinearMap.domRestrict₁₂_apply] using h
  have hw_ne : stdHermForm hE n (u : Fin n → K) (w₀ : Fin n → K) ≠ 0 := by
    have h : ((stdHermForm hE n).domRestrict₁₂ Vμ Vμ) u w₀ ≠ 0 := hu_ne
    simpa only [LinearMap.domRestrict₁₂_apply] using h
  have hw0_notin : (w₀ : Fin n → K) ∉ Submodule.span K {(u : Fin n → K)} := by
    intro hmem
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
    have h0 : stdHermForm hE n (u : Fin n → K) (w₀ : Fin n → K) = 0 := by
      rw [← ha]
      simp only [map_smul, hw_iso, smul_zero]
    exact hw_ne h0
  have hunit : IsUnit (utvMat hE (u : Fin n → K) 1) := by
    rw [Matrix.isUnit_iff_isUnit_det, utvMat_det hE hw_iso 1]
    exact isUnit_one
  let A : GL (Fin n) K := hunit.unit
  have hA_coe : (A : Matrix (Fin n) (Fin n) K) = utvMat hE (u : Fin n → K) 1 :=
    IsUnit.unit_spec hunit
  have hb : hE.bar 1 = -1 := by
    rw [map_one]
    exact eq_neg_iff_add_eq_zero.mpr (by
      calc (1 : K) + 1 = (2 : K) := by norm_num
        _ = 0 := CharP.cast_eq_zero K 2)
  have hA_mem : A ∈ LargeEvenSUGroup (Fin n) K q := by
    change A ∈ Subgroup.closure {B : GL (Fin n) K |
      (B : Matrix (Fin n) (Fin n) K).det = 1 ∧
        (((B : Matrix (Fin n) (Fin n) K)).map (· ^ q))ᵀ * (B : Matrix (Fin n) (Fin n) K) = 1}
    exact Subgroup.subset_closure
      ⟨by rw [hA_coe]; exact utvMat_det hE hw_iso 1,
       by rw [hA_coe, ← hbar_map]; exact utvMat_unitary hE hw_iso hb⟩
  let x : PSUg n K q := LargeEvenProjMk (LargeEvenSUGroup (Fin n) K q) ⟨A, hA_mem⟩
  have hxμ : InCubeBlock d μ x := by
    refine ⟨⟨A, hA_mem⟩, rfl, ?_⟩
    intro ν' hν' hne' v hv
    have horth_v : stdHermForm hE n (u : Fin n → K) v = 0 := by
      rw [stdHermForm_eq_sum_of_q hE hq]
      exact (uni_cube_eigen hK hq3 hd hd3).1 μ ν' hμ hν' (Ne.symm hne') (u : Fin n → K) u.2 v hv
    rw [hA_coe, utvMat_mulVec]
    simp [horth_v]
  have hxν_not : ¬ InCubeBlock d ν x := by
    rintro ⟨g', hg'mk, hg'fix⟩
    obtain ⟨c, hc⟩ :=
      (CFSG.Open.StatedAPI.statedProj_mk_eq_iff
        (LargeEvenSUGroup (Fin n) K q) g' ⟨A, hA_mem⟩).mp hg'mk
    have hg'w : ((g' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
        ((c : K) • (w₀ : Fin n → K)) = (c : K) • (w₀ : Fin n → K) :=
      hg'fix μ hμ hne ((c : K) • (w₀ : Fin n → K)) (Submodule.smul_mem _ _ w₀.2)
    have hA_action : (A : Matrix (Fin n) (Fin n) K) *ᵥ (w₀ : Fin n → K) =
        (c : K) • (w₀ : Fin n → K) := by
      rw [hc]
      rw [← Matrix.mulVec_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hg'w]
    have hA_action' : (A : Matrix (Fin n) (Fin n) K) *ᵥ (w₀ : Fin n → K) =
        (w₀ : Fin n → K) +
          stdHermForm hE n (u : Fin n → K) (w₀ : Fin n → K) • (u : Fin n → K) := by
      rw [hA_coe, utvMat_mulVec, one_mul]
    have hdiff : ((c : K) - 1) • (w₀ : Fin n → K) =
        stdHermForm hE n (u : Fin n → K) (w₀ : Fin n → K) • (u : Fin n → K) := by
      calc ((c : K) - 1) • (w₀ : Fin n → K) = (c : K) • (w₀ : Fin n → K) - (w₀ : Fin n → K) := by
            rw [sub_smul, one_smul]
        _ = ((w₀ : Fin n → K) +
              stdHermForm hE n (u : Fin n → K) (w₀ : Fin n → K) • (u : Fin n → K)) -
              (w₀ : Fin n → K) := by rw [← hA_action, hA_action']
        _ = stdHermForm hE n (u : Fin n → K) (w₀ : Fin n → K) • (u : Fin n → K) := by
            rw [add_sub_cancel_left]
    by_cases hcfix : (c : K) - 1 = 0
    · have hzero : stdHermForm hE n (u : Fin n → K) (w₀ : Fin n → K) •
          (u : Fin n → K) = 0 := by
        rw [← hdiff, hcfix, zero_smul]
      rcases smul_eq_zero.mp hzero with hs | hu
      · exact hw_ne hs
      · exact hw_ne (by rw [hu]; simp)
    · have hw0u : (w₀ : Fin n → K) =
          (((c : K) - 1)⁻¹ * stdHermForm hE n (u : Fin n → K) (w₀ : Fin n → K)) •
            (u : Fin n → K) := by
        calc (w₀ : Fin n → K) =
              ((c : K) - 1)⁻¹ • (((c : K) - 1) • (w₀ : Fin n → K)) := by
              rw [smul_smul, inv_mul_cancel₀ hcfix, one_smul]
          _ = ((c : K) - 1)⁻¹ •
              (stdHermForm hE n (u : Fin n → K) (w₀ : Fin n → K) • (u : Fin n → K)) := by
              rw [hdiff]
          _ = (((c : K) - 1)⁻¹ *
              stdHermForm hE n (u : Fin n → K) (w₀ : Fin n → K)) • (u : Fin n → K) := by
              rw [smul_smul]
      exact hw0_notin (Submodule.mem_span_singleton.mpr ⟨_, hw0u.symm⟩)
  exact fun hall => hxν_not ((hall x).mp hxμ)

end UniCubeNe

end CFSG.StandardType.TablePThreeKG

end
