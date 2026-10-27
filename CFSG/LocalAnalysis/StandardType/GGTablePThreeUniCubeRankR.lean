module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniCubeDefs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeSplitR
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniModel
import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniRank
import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniCubeNe
import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniCubeEigen
import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryHermitian
import CFSG.Quasithin.EmptyFaithful.R3cBase
import CFSG.Open.LocalVocabulary
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.Assembly.GL83StatedBridge
import CFSG.ClassicalGroups.UnitaryFlag.GroupData
import CFSG.LocalAnalysis.StandardType.GGSUNonsplitTwoBlockRestrict
import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeInner
import CFSG.LocalAnalysis.StandardType.GGHermTools
import CFSG.LocalAnalysis.StandardType.GGSUNonsplitTwoBlockPiece
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
public import CFSG.Sporadic.HeldB.Common
public import CFSG.Sporadic.Schreier.RuPair
public import CFSG.Sporadic.Schreier.RuSylow
public import Certificates.Certificate7233Base
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
import CFSG.Milestones.CL_LIT_SQTK_simple_list
import CFSG.Quasithin.Background.A1cModuleCoprime
import CFSG.Quasithin.Background.B4Statement
import CFSG.Quasithin.Background.B5Statement
import CFSG.Quasithin.Background.OrderingMax
import CFSG.Quasithin.Vol2.Ch1Local
import Certificates.Certificate8026Base

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly

section Toolbox

open Matrix Module CFSG.Assembly CFSG.AGLEmbedding
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LinearGroups

private lemma uniCubeRank_cube_root_pow_three' {K : Type} [Field K] {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) : ω ^ 3 = 1 := by
  have h : (ω - 1) * (ω ^ 2 + ω + 1) = ω ^ 3 - 1 := by ring
  rw [hω, mul_zero] at h
  exact sub_eq_zero.mp h.symm

private lemma uniCubeRank_three_ne_zero' {K : Type} [Field K] [CharP K 2] : (3 : K) ≠ 0 := by
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h : (3 : K) = (2 : K) + 1 := by norm_num
  rw [h, htwo, zero_add]
  exact one_ne_zero

private lemma uniCubeRank_sq_add_self_add_one_eq_zero_of_cube_eq_one_of_ne_one {K : Type} [Field K] {μ : K}
    (hμ : μ ^ 3 = 1) (hμ1 : μ ≠ 1) : μ ^ 2 + μ + 1 = 0 := by
  have h : (μ - 1) * (μ ^ 2 + μ + 1) = 0 := by
    calc (μ - 1) * (μ ^ 2 + μ + 1) = μ ^ 3 - 1 := by ring
      _ = 0 := by rw [hμ]; ring
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hμ1)

private lemma uniCubeRank_cube_roots_distinct' {K : Type} [Field K] [CharP K 2] {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) :
    (1 : K) ≠ ω ∧ (1 : K) ≠ ω ^ 2 ∧ ω ≠ ω ^ 2 := by
  have h3 : (3 : K) ≠ 0 := uniCubeRank_three_ne_zero'
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

private lemma uniCubeRank_stdHermForm_eq_sum_of_q {K : Type} [Field K] {p f n : ℕ}
    (hE : UnitaryFieldData p f K) {q : ℕ} (hq : q = p ^ f) (x y : Fin n → K) :
    stdHermForm hE n x y = ∑ i, x i ^ q * y i := by
  rw [stdHermForm_apply]
  exact Finset.sum_congr rfl fun i _ => by rw [UnitaryFieldData.bar_apply, ← hq]

private lemma uniCubeRank_stdHermForm_eq_zero_imp_zero {K : Type} [Field K] {p f n : ℕ}
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

private lemma uniCubeRank_eigenspace_separatingLeft {K : Type} [Field K] [Finite K] [CharP K 2]
    {q n f : ℕ} (hK : Nat.card K = q ^ 2) (hq3 : 3 ∣ q + 1)
    (hE : UnitaryFieldData 2 f K) (hq : q = 2 ^ f)
    {d : GL (Fin n) K} (hd : IsHermIsometry q (d : Matrix (Fin n) (Fin n) K)) (hd3 : d ^ 3 = 1)
    {μ ω : K} (hμ : μ ^ 3 = 1) (hω : ω ^ 2 + ω + 1 = 0) :
    ((stdHermForm hE n).domRestrict₁₂ (cubeEigen d μ) (cubeEigen d μ)).SeparatingLeft := by
  classical
  obtain ⟨horth, hdimsum⟩ := uni_cube_eigen hK hq3 hd hd3
  have hdist : (1 : K) ≠ ω ∧ (1 : K) ≠ ω ^ 2 ∧ ω ≠ ω ^ 2 := uniCubeRank_cube_roots_distinct' hω
  have hω3 : ω ^ 3 = 1 := uniCubeRank_cube_root_pow_three' hω
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
  apply uniCubeRank_stdHermForm_eq_zero_imp_zero hE
  intro z
  have hthree' : cubeEigen d 1 ⊔ (cubeEigen d ω ⊔ cubeEigen d (ω ^ 2)) = ⊤ := by
    rw [← sup_assoc]; exact hthree
  have hperpμ : ∀ w ∈ cubeEigen d μ, stdHermForm hE n x.1 w = 0 := by
    intro w hw
    simpa only [LinearMap.domRestrict₁₂_apply] using hx ⟨w, hw⟩
  have hperp_other : ∀ lam : K, lam ^ 3 = 1 → lam ≠ μ → ∀ w ∈ cubeEigen d lam,
      stdHermForm hE n x.1 w = 0 := by
    intro lam hlam hne w hw
    rw [uniCubeRank_stdHermForm_eq_sum_of_q hE hq]
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

private lemma uniCubeRank_exists_cube_root_K {K : Type} [Field K] [Finite K] {f : ℕ}
    (hK : Nat.card K = (2 ^ f) ^ 2) : ∃ ω : K, ω ^ 2 + ω + 1 = 0 := by
  obtain ⟨ω, hω3, hω1⟩ := CFSG.Quasithin.R3c.exists_cube_root_of_card_two_pow (K := K) (n := f + f)
    ⟨f, rfl⟩ (by rw [hK, pow_two, ← pow_add])
  refine ⟨(ω : K), uniCubeRank_sq_add_self_add_one_eq_zero_of_cube_eq_one_of_ne_one ?_ ?_⟩
  · have := congrArg (fun u : Kˣ => (u : K)) hω3
    simpa [Units.val_pow_eq_pow_val] using this
  · intro h
    exact hω1 (Units.ext h)

private lemma uniCubeRank_eigenspaces_sup_eq_top {K : Type} [Field K] [Finite K] [CharP K 2] {q n : ℕ}
    (hK : Nat.card K = q ^ 2) (hq3 : 3 ∣ q + 1)
    {d : GL (Fin n) K} (hd : IsHermIsometry q (d : Matrix (Fin n) (Fin n) K)) (hd3 : d ^ 3 = 1)
    {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    cubeEigen d 1 ⊔ cubeEigen d ω ⊔ cubeEigen d (ω ^ 2) = ⊤ := by
  classical
  obtain ⟨-, hdimsum⟩ := uni_cube_eigen hK hq3 hd hd3
  have hdist : (1 : K) ≠ ω ∧ (1 : K) ≠ ω ^ 2 ∧ ω ≠ ω ^ 2 := uniCubeRank_cube_roots_distinct' hω
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
  apply Submodule.eq_top_of_finrank_eq
  rw [Module.finrank_fin_fun]
  have hdim1 := Submodule.finrank_sup_add_finrank_inf_eq (cubeEigen d 1)
    (cubeEigen d ω ⊔ cubeEigen d (ω ^ 2))
  rw [hABC.eq_bot, finrank_bot, add_zero] at hdim1
  have hdim2 := Submodule.finrank_sup_add_finrank_inf_eq (cubeEigen d ω) (cubeEigen d (ω ^ 2))
  rw [hBC.eq_bot, finrank_bot, add_zero] at hdim2
  rw [sup_assoc, hdim1, hdim2, ← add_assoc]
  exact hdimsum ω hω

private theorem uniCubeRank_isHermIsometry_iff_stdHermForm {K : Type} [Field K] {f n : ℕ}
    (h : UnitaryFieldData 2 f K) {A : Matrix (Fin n) (Fin n) K} :
    IsHermIsometry (2 ^ f) A ↔
      ∀ x y, stdHermForm h n (A *ᵥ x) (A *ᵥ y) = stdHermForm h n x y := by
  simp only [IsHermIsometry, stdHermForm_apply, h.bar_apply]

private theorem uniCubeRank_isHermIsometry_of_mem_SU {K : Type} [Field K] [Finite K] [CharP K 2]
    {q n : ℕ} (hK : Nat.card K = q ^ 2) {g : GL (Fin n) K}
    (hg : g ∈ LargeEvenSUGroup (Fin n) K q) :
    IsHermIsometry q (g : Matrix (Fin n) (Fin n) K) := by
  obtain ⟨f, hf, hq⟩ := CFSG.AGLEmbedding.ToralCensus.exists_eq_two_pow_of_card_eq_sq hK
  subst hq
  have h : UnitaryFieldData 2 f K :=
    CFSG.AGLEmbedding.ToralCensus.unitaryFieldData_of_card_eq_sq hK hf
  rw [uniCubeRank_isHermIsometry_iff_stdHermForm h]
  have hgU : g ∈ unitarySU 2 f K n := by
    rw [unitarySU, ← CFSG.Assembly.largeEvenSUGroup_eq_statedSU]
    exact hg
  exact ((mem_unitarySU_iff_isometry h).mp hgU).2

private theorem uniCubeRank_isHermIsometry_inv {K : Type} [Field K] [Finite K] [CharP K 2] {q n : ℕ}
    (hK : Nat.card K = q ^ 2) {g : GL (Fin n) K}
    (hg : IsHermIsometry q (g : Matrix (Fin n) (Fin n) K)) :
    IsHermIsometry q ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  obtain ⟨f, hf, hq⟩ := CFSG.AGLEmbedding.ToralCensus.exists_eq_two_pow_of_card_eq_sq hK
  subst hq
  have h : UnitaryFieldData 2 f K :=
    CFSG.AGLEmbedding.ToralCensus.unitaryFieldData_of_card_eq_sq hK hf
  rw [uniCubeRank_isHermIsometry_iff_stdHermForm h] at hg ⊢
  intro x y
  have h1 := hg ((g⁻¹ : GL (Fin n) K) *ᵥ x) ((g⁻¹ : GL (Fin n) K) *ᵥ y)
  have e1 : (g : Matrix (Fin n) (Fin n) K) *ᵥ ((g⁻¹ : GL (Fin n) K) *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec]
  have e2 : (g : Matrix (Fin n) (Fin n) K) *ᵥ ((g⁻¹ : GL (Fin n) K) *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec]
  rw [e1, e2] at h1
  exact h1.symm

private theorem uniCubeRank_isHermIsometry_mem_normalizer {K : Type} [Field K] [Finite K] [CharP K 2]
    {q n : ℕ} (hK : Nat.card K = q ^ 2) {g : GL (Fin n) K}
    (hg : IsHermIsometry q (g : Matrix (Fin n) (Fin n) K)) :
    g ∈ Subgroup.normalizer (LargeEvenSUGroup (Fin n) K q : Set (GL (Fin n) K)) := by
  obtain ⟨f, hf, hq⟩ := CFSG.AGLEmbedding.ToralCensus.exists_eq_two_pow_of_card_eq_sq hK
  subst hq
  have h : UnitaryFieldData 2 f K :=
    CFSG.AGLEmbedding.ToralCensus.unitaryFieldData_of_card_eq_sq hK hf
  have hgStd := (uniCubeRank_isHermIsometry_iff_stdHermForm h).mp hg
  have hbar : (⇑h.bar : K → K) = fun x => x ^ (2 ^ f) := funext fun x => h.bar_apply x
  have hmat : ((g : Matrix (Fin n) (Fin n) K).map (· ^ (2 ^ f)))ᵀ *
      (g : Matrix (Fin n) (Fin n) K) = 1 := by
    have hmap := CFSG.StandardType.SUTB.map_bar_transpose_mul_of_isometry h hgStd
    simpa only [hbar] using hmap
  have hgu : g ∈ LargeEvenGUSet (Fin n) K (2 ^ f) := by
    refine ⟨1, one_ne_zero, by simp, ?_⟩
    simpa using hmat
  exact CFSG.StandardType.TableBUE.gu_subset_normalizer (n := f) (d := n) h hgu

private theorem uniCubeRank_isConjBy_mul {n q : ℕ} {K : Type} [Field K] {g g' : GL (Fin n) K}
    {a a' : MulAut (PSUg n K q)}
    (hnorm : ∀ k ∈ LargeEvenSUGroup (Fin n) K q,
      g' * k * g'⁻¹ ∈ LargeEvenSUGroup (Fin n) K q)
    (h1 : IsConjBy g a) (h2 : IsConjBy g' a') : IsConjBy (g * g') (a * a') := by
  intro x x' hx
  let x'' : ↥(LargeEvenSUGroup (Fin n) K q) :=
    ⟨g' * (x : GL (Fin n) K) * g'⁻¹, hnorm x x.2⟩
  have hx'' : (x'' : GL (Fin n) K) = g' * (x : GL (Fin n) K) * g'⁻¹ := rfl
  have h2' : a' (LargeEvenProjMk (LargeEvenSUGroup (Fin n) K q) x) =
      LargeEvenProjMk (LargeEvenSUGroup (Fin n) K q) x'' := h2 x x'' hx''
  have h1' : a (LargeEvenProjMk (LargeEvenSUGroup (Fin n) K q) x'') =
      LargeEvenProjMk (LargeEvenSUGroup (Fin n) K q) x' :=
    h1 x'' x' (by
      show (x' : GL (Fin n) K) = g * (x'' : GL (Fin n) K) * g⁻¹
      rw [hx, hx'']
      group)
  calc (a * a') (LargeEvenProjMk (LargeEvenSUGroup (Fin n) K q) x)
      = a (a' (LargeEvenProjMk (LargeEvenSUGroup (Fin n) K q) x)) := rfl
    _ = a (LargeEvenProjMk (LargeEvenSUGroup (Fin n) K q) x'') := by rw [h2']
    _ = LargeEvenProjMk (LargeEvenSUGroup (Fin n) K q) x' := h1'

private theorem uniCubeRank_isConjBy_inv {n q : ℕ} {K : Type} [Field K] {g : GL (Fin n) K}
    {a : MulAut (PSUg n K q)} (h1 : IsConjBy g a) : IsConjBy g⁻¹ a⁻¹ := by
  intro x x' hx
  have hrel : (x : GL (Fin n) K) = g * (x' : GL (Fin n) K) * g⁻¹ := by rw [hx]; group
  have h := h1 x' x hrel
  calc a⁻¹ (LargeEvenProjMk (LargeEvenSUGroup (Fin n) K q) x)
      = a⁻¹ (a (LargeEvenProjMk (LargeEvenSUGroup (Fin n) K q) x')) := by rw [← h]
    _ = LargeEvenProjMk (LargeEvenSUGroup (Fin n) K q) x' := by
          rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]

private theorem uniCubeRank_isConjBy_one {n q : ℕ} {K : Type} [Field K] :
    IsConjBy (1 : GL (Fin n) K) (1 : MulAut (PSUg n K q)) := by
  intro x x' hx
  have hxx : x' = x := Subtype.ext (by simpa using hx)
  subst hxx
  rw [MulAut.one_apply]

private theorem uniCubeRank_isConjBy_pow {n q : ℕ} {K : Type} [Field K] {g : GL (Fin n) K}
    {a : MulAut (PSUg n K q)}
    (hnorm : ∀ k ∈ LargeEvenSUGroup (Fin n) K q,
      g * k * g⁻¹ ∈ LargeEvenSUGroup (Fin n) K q)
    (h : IsConjBy g a) : ∀ m : ℕ, IsConjBy (g ^ m) (a ^ m)
  | 0 => by simpa using (uniCubeRank_isConjBy_one (n := n) (q := q) (K := K))
  | m + 1 => by
      have ih := uniCubeRank_isConjBy_pow hnorm h m
      simpa [pow_succ] using uniCubeRank_isConjBy_mul hnorm ih h

private lemma uniCubeRank_scalarGL_injective {N : ℕ} {K : Type} [Field K] (hN : 1 ≤ N) :
    Function.Injective
      (fun u : Kˣ => (Matrix.GeneralLinearGroup.scalar (Fin N) u : GL (Fin N) K)) := by
  intro u v h
  have h' : ((Matrix.GeneralLinearGroup.scalar (Fin N) u : GL (Fin N) K) :
        Matrix (Fin N) (Fin N) K) =
      ((Matrix.GeneralLinearGroup.scalar (Fin N) v : GL (Fin N) K) :
        Matrix (Fin N) (Fin N) K) := by
    simpa using congrArg (fun Y : GL (Fin N) K => (Y : Matrix (Fin N) (Fin N) K)) h
  simp only [Matrix.GeneralLinearGroup.coe_scalar] at h'
  have h00 := congrFun (congrFun h' ⟨0, by omega⟩) ⟨0, by omega⟩
  simp [Matrix.smul_apply, Matrix.one_apply] at h00
  exact Units.ext h00

private lemma uniCubeRank_scalar_eq_smul_one {n : ℕ} {K : Type} [Field K] (c : K) :
    Matrix.scalar (Fin n) c = c • (1 : Matrix (Fin n) (Fin n) K) := by
  rw [Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul, Matrix.mul_one]

private lemma uniCubeRank_exists_scalar_of_mem_Ahat
    {K : Type} [Field K] [Finite K] [CharP K 2] {q N : ℕ} (hK : Nat.card K = q ^ 2)
    (hN : 1 ≤ N)
    {Ā : Subgroup (MulAut (PSUg N K q))} {δ' : MulAut (PSUg N K q)}
    {J' : Subgroup (PSUg N K q)} (hR : RDatum Ā δ' J') {Ahat : Subgroup (GL (Fin N) K)}
    (hL : UniLift N q K Ā Ahat) {d : GL (Fin N) K} (hdA : d ∈ Ahat) (hd3 : d ^ 3 = 1)
    (hδ : IsConjBy d δ') {a : GL (Fin N) K} (ha : a ∈ Ahat) :
    ∃ c : Kˣ, a * d * a⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin N) c * d ∧ c ^ 3 = 1 := by
  have hnorm_a : ∀ k ∈ LargeEvenSUGroup (Fin N) K q,
      a * k * a⁻¹ ∈ LargeEvenSUGroup (Fin N) K q :=
    fun k hk => (Subgroup.mem_normalizer_iff.mp
      (uniCubeRank_isHermIsometry_mem_normalizer hK (hL.iso a ha)) k).mp hk
  have hnorm_d : ∀ k ∈ LargeEvenSUGroup (Fin N) K q,
      d * k * d⁻¹ ∈ LargeEvenSUGroup (Fin N) K q :=
    fun k hk => (Subgroup.mem_normalizer_iff.mp
      (uniCubeRank_isHermIsometry_mem_normalizer hK (hL.iso d hdA)) k).mp hk
  have hnorm_ainv : ∀ k ∈ LargeEvenSUGroup (Fin N) K q,
      a⁻¹ * k * (a⁻¹)⁻¹ ∈ LargeEvenSUGroup (Fin N) K q :=
    fun k hk => (Subgroup.mem_normalizer_iff.mp
      (Subgroup.inv_mem _ (uniCubeRank_isHermIsometry_mem_normalizer hK (hL.iso a ha))) k).mp hk
  have hnorm_dinv : ∀ k ∈ LargeEvenSUGroup (Fin N) K q,
      d⁻¹ * k * (d⁻¹)⁻¹ ∈ LargeEvenSUGroup (Fin N) K q :=
    fun k hk => (Subgroup.mem_normalizer_iff.mp
      (Subgroup.inv_mem _ (uniCubeRank_isHermIsometry_mem_normalizer hK (hL.iso d hdA))) k).mp hk
  obtain ⟨ā, hāĀ, hā⟩ := hL.induces a ha
  have habel : ā * δ' * ā⁻¹ = δ' := by
    have hc := CFSG.Open.IsElemAbelian.comm hR.elem hāĀ hR.mem
    rw [hc]; group
  have hconj1 : IsConjBy (a * d * a⁻¹ * d⁻¹) (1 : MulAut (PSUg N K q)) := by
    have h1 : IsConjBy (a * d) (ā * δ') := uniCubeRank_isConjBy_mul hnorm_d hā hδ
    have h2 : IsConjBy (a * d * a⁻¹) (ā * δ' * ā⁻¹) :=
      uniCubeRank_isConjBy_mul hnorm_ainv h1 (uniCubeRank_isConjBy_inv hā)
    rw [habel] at h2
    have h3 : IsConjBy (a * d * a⁻¹ * d⁻¹) (δ' * δ'⁻¹) :=
      uniCubeRank_isConjBy_mul hnorm_dinv h2 (uniCubeRank_isConjBy_inv hδ)
    rw [mul_inv_cancel] at h3
    exact h3
  have hmem : a * d * a⁻¹ * d⁻¹ ∈ Ahat :=
    Ahat.mul_mem (Ahat.mul_mem (Ahat.mul_mem ha hdA) (Ahat.inv_mem ha)) (Ahat.inv_mem hdA)
  obtain ⟨c, hcnorm, hc⟩ := hL.ker (a * d * a⁻¹ * d⁻¹) hmem hconj1
  have haeq : a * d * a⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin N) c * d := by
    calc a * d * a⁻¹ = (a * d * a⁻¹ * d⁻¹) * d := by group
      _ = Matrix.GeneralLinearGroup.scalar (Fin N) c * d := by rw [hc]
  refine ⟨c, haeq, ?_⟩
  have hcd : Commute (Matrix.GeneralLinearGroup.scalar (Fin N) c) d :=
    Matrix.GeneralLinearGroup.scalar_commute c d
  have h1 : (Matrix.GeneralLinearGroup.scalar (Fin N) c * d) ^ 3 = 1 := by
    rw [← haeq]
    calc (a * d * a⁻¹) ^ 3 = a * d ^ 3 * a⁻¹ := by rw [conj_pow]
      _ = 1 := by rw [hd3]; group
  have h2 : (Matrix.GeneralLinearGroup.scalar (Fin N) c * d) ^ 3 =
      Matrix.GeneralLinearGroup.scalar (Fin N) (c ^ 3) := by
    rw [hcd.mul_pow, map_pow, hd3, mul_one]
  have h3 : Matrix.GeneralLinearGroup.scalar (Fin N) (c ^ 3) = 1 := h2 ▸ h1
  have h4 : Matrix.GeneralLinearGroup.scalar (Fin N) (c ^ 3) =
      Matrix.GeneralLinearGroup.scalar (Fin N) (1 : Kˣ) := by rw [h3, map_one]
  exact uniCubeRank_scalarGL_injective (N := N) hN h4

private lemma uniCubeRank_mulVec_mem_cubeEigen_of_conj {K : Type} [Field K] {N : ℕ}
    {d a : GL (Fin N) K} {c : Kˣ}
    (h : a * d * a⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin N) c * d)
    {lam : K} {v : Fin N → K} (hv : v ∈ cubeEigen d lam) :
    (a : Matrix (Fin N) (Fin N) K) *ᵥ v ∈ cubeEigen d (c⁻¹ * lam) := by
  have hv' : (d : Matrix (Fin N) (Fin N) K) *ᵥ v = lam • v := by
    have hmem := Module.End.mem_eigenspace_iff.mp hv
    simpa [cubeEigen, Matrix.toLin'_apply] using hmem
  have hGL : a * d = Matrix.GeneralLinearGroup.scalar (Fin N) c * d * a := by
    calc a * d = (a * d * a⁻¹) * a := by group
      _ = (Matrix.GeneralLinearGroup.scalar (Fin N) c * d) * a := by rw [h]
  have hmat : (a : Matrix (Fin N) (Fin N) K) * (d : Matrix (Fin N) (Fin N) K) =
      (c : K) • ((d : Matrix (Fin N) (Fin N) K) * (a : Matrix (Fin N) (Fin N) K)) := by
    have h' := congrArg (fun g : GL (Fin N) K => (g : Matrix (Fin N) (Fin N) K)) hGL
    simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, uniCubeRank_scalar_eq_smul_one,
      Matrix.smul_mul, Matrix.one_mul] at h'
    exact h'
  have hmat2 : (d : Matrix (Fin N) (Fin N) K) * (a : Matrix (Fin N) (Fin N) K) =
      (c⁻¹ : K) • ((a : Matrix (Fin N) (Fin N) K) * (d : Matrix (Fin N) (Fin N) K)) := by
    have h' := congrArg (fun g : GL (Fin N) K => (g : Matrix (Fin N) (Fin N) K)) hGL
    simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, uniCubeRank_scalar_eq_smul_one,
      Matrix.smul_mul, Matrix.one_mul] at h'
    have h2 := congrArg (fun M : Matrix (Fin N) (Fin N) K => (c⁻¹ : K) • M) h'
    rw [smul_smul, inv_mul_cancel₀ (Units.ne_zero c), one_smul] at h2
    exact h2.symm
  have key : (d : Matrix (Fin N) (Fin N) K) *ᵥ ((a : Matrix (Fin N) (Fin N) K) *ᵥ v) =
      (c⁻¹ * lam) • ((a : Matrix (Fin N) (Fin N) K) *ᵥ v) := by
    calc (d : Matrix (Fin N) (Fin N) K) *ᵥ ((a : Matrix (Fin N) (Fin N) K) *ᵥ v)
        = ((d : Matrix (Fin N) (Fin N) K) * (a : Matrix (Fin N) (Fin N) K)) *ᵥ v := by
          rw [Matrix.mulVec_mulVec]
      _ = ((c⁻¹ : K) • ((a : Matrix (Fin N) (Fin N) K) * (d : Matrix (Fin N) (Fin N) K))) *ᵥ v := by
          rw [hmat2]
      _ = (c⁻¹ : K) • (((a : Matrix (Fin N) (Fin N) K) * (d : Matrix (Fin N) (Fin N) K)) *ᵥ v) := by
          rw [Matrix.smul_mulVec]
      _ = (c⁻¹ : K) • ((a : Matrix (Fin N) (Fin N) K) *ᵥ ((d : Matrix (Fin N) (Fin N) K) *ᵥ v)) := by
          rw [Matrix.mulVec_mulVec]
      _ = (c⁻¹ : K) • ((a : Matrix (Fin N) (Fin N) K) *ᵥ (lam • v)) := by rw [hv']
      _ = (c⁻¹ : K) • (lam • ((a : Matrix (Fin N) (Fin N) K) *ᵥ v)) := by
          rw [Matrix.mulVec_smul]
      _ = (c⁻¹ * lam) • ((a : Matrix (Fin N) (Fin N) K) *ᵥ v) := by
          rw [smul_smul, Units.val_inv_eq_inv_val c]
  simpa [cubeEigen, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] using key

private lemma uniCubeRank_mulVec_mem_cubeEigen_of_conj_inv {K : Type} [Field K] {N : ℕ}
    {d a : GL (Fin N) K} {c : Kˣ}
    (h : a * d * a⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin N) c * d)
    {lam : K} {v : Fin N → K} (hv : v ∈ cubeEigen d lam) :
    ((a⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ v ∈ cubeEigen d (c * lam) := by
  have hGL : a * d = Matrix.GeneralLinearGroup.scalar (Fin N) c * d * a := by
    calc a * d = (a * d * a⁻¹) * a := by group
      _ = (Matrix.GeneralLinearGroup.scalar (Fin N) c * d) * a := by rw [h]
  have hGLinv : a⁻¹ * d * a = Matrix.GeneralLinearGroup.scalar (Fin N) c⁻¹ * d := by
    have h1 : Matrix.GeneralLinearGroup.scalar (Fin N) c * (a⁻¹ * d * a) = d := by
      calc Matrix.GeneralLinearGroup.scalar (Fin N) c * (a⁻¹ * d * a)
          = (Matrix.GeneralLinearGroup.scalar (Fin N) c * a⁻¹) * (d * a) := by group
        _ = (a⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin N) c) * (d * a) := by
              rw [Matrix.GeneralLinearGroup.scalar_commute c a⁻¹]
        _ = a⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin N) c * d * a) := by group
        _ = a⁻¹ * (a * d) := by rw [← hGL]
        _ = d := by group
    have h2 := congrArg (fun x => Matrix.GeneralLinearGroup.scalar (Fin N) c⁻¹ * x) h1
    rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul] at h2
    exact h2
  have := uniCubeRank_mulVec_mem_cubeEigen_of_conj (d := d) (a := a⁻¹) (c := c⁻¹) hGLinv hv
  simpa using this

private lemma uniCubeRank_conj_maps_eigSub {K : Type} [Field K] {q N : ℕ} {d a : GL (Fin N) K} {c : Kˣ}
    (h : a * d * a⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin N) c * d) (hc3 : c ^ 3 = 1)
    (hSU : ∀ k ∈ LargeEvenSUGroup (Fin N) K q, a * k * a⁻¹ ∈ LargeEvenSUGroup (Fin N) K q)
    {μ : K} {g : ↥(LargeEvenSUGroup (Fin N) K q)} (hg : g ∈ eigSub q d μ) :
    (⟨a * (g : GL (Fin N) K) * a⁻¹, hSU g g.2⟩ : ↥(LargeEvenSUGroup (Fin N) K q)) ∈
      eigSub q d (c⁻¹ * μ) := by
  intro ν hν hνne w hw
  let w' : Fin N → K := ((a⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ w
  have hw' : w' ∈ cubeEigen d (c * ν) := by
    dsimp only [w']
    exact uniCubeRank_mulVec_mem_cubeEigen_of_conj_inv h hw
  have hcν3 : (c * ν) ^ 3 = 1 := by
    have hc3' : ((c : K)) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, hc3]; rfl
    rw [mul_pow, hc3', hν, one_mul]
  have hcνne : c * ν ≠ μ := by
    intro hcon
    apply hνne
    have hνeq : ν = c⁻¹ * μ := by
      rw [← hcon]
      rw [← mul_assoc, Units.val_inv_eq_inv_val c, inv_mul_cancel₀ (Units.ne_zero c), one_mul]
    exact hνeq
  have hgfix : ((g : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ w' = w' :=
    hg (c * ν) hcν3 hcνne w' hw'
  show (((a * (g : GL (Fin N) K) * a⁻¹ : GL (Fin N) K)) : Matrix (Fin N) (Fin N) K) *ᵥ w = w
  have hcoe : (((a * (g : GL (Fin N) K) * a⁻¹ : GL (Fin N) K)) :
      Matrix (Fin N) (Fin N) K) =
      (a : Matrix (Fin N) (Fin N) K) * ((g : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *
        ((a⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) := by
    rw [Units.val_mul, Units.val_mul]
  rw [hcoe]
  have hw_eq : (a : Matrix (Fin N) (Fin N) K) *ᵥ w' = w := by
    dsimp only [w']
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel a,
      Units.val_one, Matrix.one_mulVec]
  calc ((a : Matrix (Fin N) (Fin N) K) * ((g : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *
        ((a⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)) *ᵥ w
      = ((a : Matrix (Fin N) (Fin N) K) * ((g : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)) *ᵥ
          (((a⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ w) := by
        rw [← Matrix.mulVec_mulVec]
    _ = ((a : Matrix (Fin N) (Fin N) K) * ((g : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)) *ᵥ w' := by
        rfl
    _ = (a : Matrix (Fin N) (Fin N) K) *ᵥ
          (((g : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ w') := by
        rw [← Matrix.mulVec_mulVec]
    _ = (a : Matrix (Fin N) (Fin N) K) *ᵥ w' := by rw [hgfix]
    _ = w := hw_eq

private lemma uniCubeRank_conj_inv_eq_scalar_inv {K : Type} [Field K] {N : ℕ}
    {d a : GL (Fin N) K} {c : Kˣ}
    (h : a * d * a⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin N) c * d) :
    a⁻¹ * d * (a⁻¹)⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin N) c⁻¹ * d := by
  have hGL : a * d = Matrix.GeneralLinearGroup.scalar (Fin N) c * d * a := by
    calc a * d = (a * d * a⁻¹) * a := by group
      _ = (Matrix.GeneralLinearGroup.scalar (Fin N) c * d) * a := by rw [h]
  have h1 : Matrix.GeneralLinearGroup.scalar (Fin N) c * (a⁻¹ * d * a) = d := by
    calc Matrix.GeneralLinearGroup.scalar (Fin N) c * (a⁻¹ * d * a)
        = (Matrix.GeneralLinearGroup.scalar (Fin N) c * a⁻¹) * (d * a) := by group
      _ = (a⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin N) c) * (d * a) := by
            rw [Matrix.GeneralLinearGroup.scalar_commute c a⁻¹]
      _ = a⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin N) c * d * a) := by group
      _ = a⁻¹ * (a * d) := by rw [← hGL]
      _ = d := by group
  have h2 := congrArg (fun x => Matrix.GeneralLinearGroup.scalar (Fin N) c⁻¹ * x) h1
  rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul] at h2
  simpa using h2

private lemma uniCubeRank_finrank_cubeEigen_inv_mul_eq {K : Type} [Field K] {N : ℕ}
    {d a : GL (Fin N) K} {c : Kˣ}
    (h : a * d * a⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin N) c * d) {μ : K} :
    Module.finrank K (cubeEigen d (c⁻¹ * μ)) = Module.finrank K (cubeEigen d μ) := by
  have h' : a⁻¹ * d * (a⁻¹)⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin N) c⁻¹ * d :=
    uniCubeRank_conj_inv_eq_scalar_inv h
  have key : ((((c⁻¹)⁻¹ : Kˣ)) : K) * ((((c⁻¹ : Kˣ)) : K) * μ) = μ := by
    rw [show ((c⁻¹)⁻¹ : Kˣ) = c from inv_inv c, ← mul_assoc, ← Units.val_mul,
      mul_inv_cancel c, Units.val_one, one_mul]
  let f : ↥(cubeEigen d μ) →ₗ[K] ↥(cubeEigen d (c⁻¹ * μ)) :=
    { toFun := fun v => ⟨(a : Matrix (Fin N) (Fin N) K) *ᵥ (v : Fin N → K),
        uniCubeRank_mulVec_mem_cubeEigen_of_conj h v.2⟩
      map_add' := fun v w => Subtype.ext (by
        show (a : Matrix (Fin N) (Fin N) K) *ᵥ ((v : Fin N → K) + (w : Fin N → K)) =
          (a : Matrix (Fin N) (Fin N) K) *ᵥ (v : Fin N → K) +
            (a : Matrix (Fin N) (Fin N) K) *ᵥ (w : Fin N → K)
        rw [Matrix.mulVec_add])
      map_smul' := fun r v => Subtype.ext (by
        show (a : Matrix (Fin N) (Fin N) K) *ᵥ (r • (v : Fin N → K)) =
          r • ((a : Matrix (Fin N) (Fin N) K) *ᵥ (v : Fin N → K))
        rw [Matrix.mulVec_smul]) }
  let g : ↥(cubeEigen d (c⁻¹ * μ)) →ₗ[K] ↥(cubeEigen d μ) :=
    { toFun := fun v => ⟨((a⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ (v : Fin N → K),
        by
          have hv := uniCubeRank_mulVec_mem_cubeEigen_of_conj h' (lam := c⁻¹ * μ) v.2
          rwa [key] at hv⟩
      map_add' := fun v w => Subtype.ext (by
        show ((a⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ
            ((v : Fin N → K) + (w : Fin N → K)) =
          ((a⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ (v : Fin N → K) +
            ((a⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ (w : Fin N → K)
        rw [Matrix.mulVec_add])
      map_smul' := fun r v => Subtype.ext (by
        show ((a⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ (r • (v : Fin N → K)) =
          r • (((a⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ (v : Fin N → K))
        rw [Matrix.mulVec_smul]) }
  have hgf : Function.LeftInverse g f := by
    intro v
    apply Subtype.ext
    show ((a⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ
        ((a : Matrix (Fin N) (Fin N) K) *ᵥ (v : Fin N → K)) = (v : Fin N → K)
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel a, Units.val_one,
      Matrix.one_mulVec]
  have hfg : Function.LeftInverse f g := by
    intro w
    apply Subtype.ext
    show (a : Matrix (Fin N) (Fin N) K) *ᵥ
        (((a⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ (w : Fin N → K)) = (w : Fin N → K)
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel a, Units.val_one,
      Matrix.one_mulVec]
  have hf : Function.Injective f := hgf.injective
  have hg : Function.Injective g := hfg.injective
  have h1 : Module.finrank K (cubeEigen d μ) ≤ Module.finrank K (cubeEigen d (c⁻¹ * μ)) :=
    LinearMap.finrank_le_finrank_of_injective hf
  have h2 : Module.finrank K (cubeEigen d (c⁻¹ * μ)) ≤ Module.finrank K (cubeEigen d μ) :=
    LinearMap.finrank_le_finrank_of_injective hg
  exact le_antisymm h2 h1

private lemma uniCubeRank_map_eigBlock_subset_of_conj {K : Type} [Field K] {q N : ℕ} {d a : GL (Fin N) K} {c : Kˣ}
    (h : a * d * a⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin N) c * d) (hc3 : c ^ 3 = 1)
    (hSU : ∀ k ∈ LargeEvenSUGroup (Fin N) K q, a * k * a⁻¹ ∈ LargeEvenSUGroup (Fin N) K q)
    {ā : MulAut (PSUg N K q)} (hā : IsConjBy a ā) {μ : K} :
    ∀ x ∈ eigBlock q d μ, ā x ∈ eigBlock q d (c⁻¹ * μ) := by
  intro x hx
  rw [mem_eigBlock_iff] at hx ⊢
  obtain ⟨g, hgx, hgfix⟩ := hx
  refine ⟨⟨a * (g : GL (Fin N) K) * a⁻¹, hSU g g.2⟩, ?_, ?_⟩
  · rw [← hgx]; exact (hā g _ rfl).symm
  · exact uniCubeRank_conj_maps_eigSub h hc3 hSU hgfix

private lemma uniCubeRank_conj_d_eq_of_mem_Ahat
    {K : Type} [Field K] [Finite K] [CharP K 2] {q N : ℕ} (hK : Nat.card K = q ^ 2)
    (hq3 : 3 ∣ q + 1) (hN : 4 ≤ N)
    {Ā : Subgroup (MulAut (PSUg N K q))} {δ' : MulAut (PSUg N K q)}
    {J' : Subgroup (PSUg N K q)} (hR : RDatum Ā δ' J') {Ahat : Subgroup (GL (Fin N) K)}
    (hL : UniLift N q K Ā Ahat) {d : GL (Fin N) K} (hdA : d ∈ Ahat) (hd3 : d ^ 3 = 1)
    (hδ : IsConjBy d δ') {μ : K} (hμ : μ ^ 3 = 1) (hJ : J' = eigBlock q d μ)
    (hk2 : 2 ≤ Module.finrank K (cubeEigen d μ)) {a : GL (Fin N) K} (ha : a ∈ Ahat) :
    a * d * a⁻¹ = d := by
  obtain ⟨c, haeq, hc3⟩ := uniCubeRank_exists_scalar_of_mem_Ahat hK (by omega) hR hL hdA hd3 hδ ha
  have hSUa : ∀ k ∈ LargeEvenSUGroup (Fin N) K q,
      a * k * a⁻¹ ∈ LargeEvenSUGroup (Fin N) K q :=
    fun k hk => (Subgroup.mem_normalizer_iff.mp
      (uniCubeRank_isHermIsometry_mem_normalizer hK (hL.iso a ha)) k).mp hk
  have hSUinv : ∀ k ∈ LargeEvenSUGroup (Fin N) K q,
      a⁻¹ * k * (a⁻¹)⁻¹ ∈ LargeEvenSUGroup (Fin N) K q :=
    fun k hk => (Subgroup.mem_normalizer_iff.mp
      (Subgroup.inv_mem _ (uniCubeRank_isHermIsometry_mem_normalizer hK (hL.iso a ha))) k).mp hk
  obtain ⟨ā, hāĀ, hā⟩ := hL.induces a ha
  have hsub := uniCubeRank_map_eigBlock_subset_of_conj haeq hc3 hSUa hā (μ := μ)
  have h' : a⁻¹ * d * (a⁻¹)⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin N) c⁻¹ * d :=
    uniCubeRank_conj_inv_eq_scalar_inv haeq
  have hc3inv : (c⁻¹) ^ 3 = 1 := by rw [inv_pow, hc3, inv_one]
  have hsubinv := uniCubeRank_map_eigBlock_subset_of_conj h' hc3inv hSUinv (uniCubeRank_isConjBy_inv hā)
    (μ := c⁻¹ * μ)
  have hkey : ((((c⁻¹)⁻¹ : Kˣ)) : K) * ((((c⁻¹ : Kˣ)) : K) * μ) = μ := by
    rw [show ((c⁻¹)⁻¹ : Kˣ) = c from inv_inv c, ← mul_assoc, ← Units.val_mul,
      mul_inv_cancel c, Units.val_one, one_mul]
  have hmap : J'.map ā.toMonoidHom = J' := by
    apply le_antisymm
    · intro y hy
      rw [Subgroup.mem_map] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      exact hR.norm ā hāĀ x hx
    · intro y hy
      rw [Subgroup.mem_map]
      exact ⟨ā⁻¹ y, hR.norm ā⁻¹ (Ā.inv_mem hāĀ) y hy, by simp⟩
  have hle1 : J' ≤ eigBlock q d (c⁻¹ * μ) := by
    rw [← hmap]
    intro y hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact hsub x (by rw [hJ] at hx; exact hx)
  have heq : eigBlock q d μ = eigBlock q d (c⁻¹ * μ) := by
    rw [← hJ]
    refine le_antisymm hle1 ?_
    intro x hx
    have hx' : ā⁻¹ x ∈ J' := by
      rw [hJ]
      have hmem := hsubinv x hx
      rwa [hkey] at hmem
    have hfin := hR.norm ā hāĀ (ā⁻¹ x) hx'
    rw [hJ] at hfin
    rw [hJ]
    simpa using hfin
  have hν2 : 2 ≤ Module.finrank K (cubeEigen d (c⁻¹ * μ)) := by
    rw [uniCubeRank_finrank_cubeEigen_inv_mul_eq haeq]
    exact hk2
  have hν3 : (c⁻¹ * μ) ^ 3 = 1 := by
    rw [mul_pow]
    have hc3' : (((c⁻¹ : Kˣ)) : K) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, hc3inv]; rfl
    rw [hc3', hμ, one_mul]
  have hc1 : c = 1 := by
    by_contra hcne
    have hνne : c⁻¹ * μ ≠ μ := by
      intro he
      apply hcne
      have hμ0 : μ ≠ 0 := by
        intro h0; rw [h0] at hμ; norm_num at hμ
      have h1K : (((c⁻¹ : Kˣ)) : K) = 1 :=
        mul_right_cancel₀ hμ0 (by rw [one_mul]; exact he)
      have h1 : c⁻¹ = 1 := Units.ext h1K
      exact inv_eq_one.mp h1
    have hall : ∀ x : PSUg N K q, InCubeBlock d μ x ↔ InCubeBlock d (c⁻¹ * μ) x := by
      intro x
      rw [← mem_eigBlock_iff, ← mem_eigBlock_iff, heq]
    exact absurd hall
      (uni_cube_blocks_ne hK hq3 hN (hL.iso d hdA) hd3 hμ hν3 (Ne.symm hνne) hk2 hν2)
  rw [haeq, hc1, map_one, one_mul]

private lemma uniCubeRank_cube_root_eq_one_or {K : Type} [Field K] {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) :
    ∀ μ : K, μ ^ 3 = 1 → μ = 1 ∨ μ = ω ∨ μ = ω ^ 2 := by
  have hω3 : ω ^ 3 = 1 := uniCubeRank_cube_root_pow_three' hω
  have hsum : ω + ω ^ 2 = -1 := by
    calc ω + ω ^ 2 = (ω ^ 2 + ω + 1) - 1 := by ring
      _ = -1 := by rw [hω, zero_sub]
  have hprod : ω * ω ^ 2 = 1 := by
    rw [show ω * ω ^ 2 = ω ^ 3 by ring, hω3]
  intro μ hμ
  have hfac : (μ - 1) * (μ ^ 2 + μ + 1) = 0 := by
    calc (μ - 1) * (μ ^ 2 + μ + 1) = μ ^ 3 - 1 := by ring
      _ = 0 := by rw [hμ]; ring
  rcases mul_eq_zero.mp hfac with h1 | hq
  · exact Or.inl (sub_eq_zero.mp h1)
  · have hquad : (μ - ω) * (μ - ω ^ 2) = 0 := by
      calc (μ - ω) * (μ - ω ^ 2) = μ ^ 2 - (ω + ω ^ 2) * μ + ω * ω ^ 2 := by ring
        _ = μ ^ 2 + μ + 1 := by rw [hsum, hprod]; ring
        _ = 0 := hq
    rcases mul_eq_zero.mp hquad with h | h
    · exact Or.inr (Or.inl (sub_eq_zero.mp h))
    · exact Or.inr (Or.inr (sub_eq_zero.mp h))

private lemma uniCubeRank_scalar_mulVec {K : Type} [Field K] {n : ℕ} (c : K) (v : Fin n → K) :
    Matrix.scalar (Fin n) c *ᵥ v = c • v := by
  ext i
  rw [Matrix.mulVec_apply_eq_sum, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
  · rw [Matrix.scalar_apply, Matrix.diagonal_apply]; simp
  · intro b _ hb
    rw [Matrix.scalar_apply, Matrix.diagonal_apply]
    simp [Ne.symm hb]

private lemma uniCubeRank_mem_of_perp_two
    {K : Type} [Field K] [Finite K] [CharP K 2] {q N f : ℕ} (hK : Nat.card K = q ^ 2)
    (hq3 : 3 ∣ q + 1) (hE : UnitaryFieldData 2 f K) (hq : q = 2 ^ f)
    {d : GL (Fin N) K} (hd : IsHermIsometry q (d : Matrix (Fin N) (Fin N) K)) (hd3 : d ^ 3 = 1)
    {ω : K} (hω : ω ^ 2 + ω + 1 = 0)
    {μ ν l : K} (hμ : μ ^ 3 = 1) (hν : ν ^ 3 = 1) (hl : l ^ 3 = 1)
    (hμν : μ ≠ ν) (hμl : μ ≠ l) (hνl : ν ≠ l)
    (hspan : cubeEigen d μ ⊔ (cubeEigen d ν ⊔ cubeEigen d l) = ⊤)
    {x : Fin N → K}
    (hxν : ∀ w ∈ cubeEigen d ν, stdHermForm hE N x w = 0)
    (hxl : ∀ w ∈ cubeEigen d l, stdHermForm hE N x w = 0) :
    x ∈ cubeEigen d μ := by
  have horth := (uni_cube_eigen hK hq3 hd hd3).1
  have horth' : ∀ {α β : K}, α ^ 3 = 1 → β ^ 3 = 1 → α ≠ β →
      ∀ a ∈ cubeEigen d α, ∀ b ∈ cubeEigen d β, stdHermForm hE N a b = 0 := by
    intro α β hα hβ hαβ a ha b hb
    rw [uniCubeRank_stdHermForm_eq_sum_of_q hE hq]
    exact horth α β hα hβ hαβ a ha b hb
  have hsepν : (∀ w ∈ cubeEigen d ν,
      (∀ w' ∈ cubeEigen d ν, stdHermForm hE N w w' = 0) → w = 0) := by
    intro w hw hw'
    have h := uniCubeRank_eigenspace_separatingLeft hK hq3 hE hq hd hd3 hν hω
    have h2 := h ⟨w, hw⟩ (fun y => by
      simpa only [LinearMap.domRestrict₁₂_apply] using hw' y.1 y.2)
    simpa using congrArg Subtype.val h2
  have hsepl : (∀ w ∈ cubeEigen d l,
      (∀ w' ∈ cubeEigen d l, stdHermForm hE N w w' = 0) → w = 0) := by
    intro w hw hw'
    have h := uniCubeRank_eigenspace_separatingLeft hK hq3 hE hq hd hd3 hl hω
    have h2 := h ⟨w, hw⟩ (fun y => by
      simpa only [LinearMap.domRestrict₁₂_apply] using hw' y.1 y.2)
    simpa using congrArg Subtype.val h2
  have hndν : SUTB.NondegOn (stdHermForm hE N) (cubeEigen d ν) :=
    SUTB.nondegOn_of_left (stdHermForm_isSymm hE N) hsepν
  have hndl : SUTB.NondegOn (stdHermForm hE N) (cubeEigen d l) :=
    SUTB.nondegOn_of_left (stdHermForm_isSymm hE N) hsepl
  have hndW : SUTB.NondegOn (stdHermForm hE N) (cubeEigen d ν ⊔ cubeEigen d l) :=
    SUTB.nondegOn_sup hndν hndl (fun u hu v hv =>
      ⟨horth' hl hν (Ne.symm hνl) u hu v hv, horth' hν hl hνl v hv u hu⟩)
  have hxmem : x ∈ cubeEigen d μ ⊔ (cubeEigen d ν ⊔ cubeEigen d l) := by
    rw [hspan]; trivial
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hxmem
  have hxall : ∀ w ∈ cubeEigen d ν ⊔ cubeEigen d l, stdHermForm hE N (a + b) w = 0 := by
    intro w hw
    obtain ⟨wν, hwν, wl, hwl, rfl⟩ := Submodule.mem_sup.mp hw
    rw [map_add, hxν wν hwν, hxl wl hwl, add_zero]
  have haperp : ∀ w ∈ cubeEigen d ν ⊔ cubeEigen d l, stdHermForm hE N a w = 0 := by
    intro w hw
    obtain ⟨wν, hwν, wl, hwl, rfl⟩ := Submodule.mem_sup.mp hw
    rw [map_add, horth' hμ hν hμν a ha wν hwν, horth' hμ hl hμl a ha wl hwl, add_zero]
  have hbperp : ∀ w ∈ cubeEigen d ν ⊔ cubeEigen d l, stdHermForm hE N b w = 0 := by
    intro w hw
    have h1 := hxall w hw
    have h2 := haperp w hw
    have h3 : stdHermForm hE N (a + b) w = stdHermForm hE N a w + stdHermForm hE N b w := by
      simp only [stdHermForm_apply, Pi.add_apply, map_add, LinearMap.add_apply, add_mul,
        Finset.sum_add_distrib]
    rw [h3, h2, zero_add] at h1
    exact h1
  have hb0 : b = 0 := by
    refine hndW b hb (fun n hn => ?_)
    have h1 : stdHermForm hE N b n = 0 := hbperp n hn
    have h2 : stdHermForm hE N n b = hE.bar (stdHermForm hE N b n) := by
      rw [stdHermForm_apply, stdHermForm_apply, map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_mul, hE.bar_bar]; ring
    rw [h2, h1, map_zero]
  rw [hb0, add_zero]
  exact ha

private lemma uniCubeRank_eigSub_maps_self
    {K : Type} [Field K] [Finite K] [CharP K 2] {q N f : ℕ} (hK : Nat.card K = q ^ 2)
    (hq3 : 3 ∣ q + 1) (hE : UnitaryFieldData 2 f K) (hq : q = 2 ^ f)
    {d : GL (Fin N) K} (hd : IsHermIsometry q (d : Matrix (Fin N) (Fin N) K)) (hd3 : d ^ 3 = 1)
    {ω : K} (hω : ω ^ 2 + ω + 1 = 0)
    {μ : K} (hμ : μ ^ 3 = 1)
    {g : ↥(LargeEvenSUGroup (Fin N) K q)} (hg : g ∈ eigSub q d μ)
    {v : Fin N → K} (hv : v ∈ cubeEigen d μ) :
    ((g : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ v ∈ cubeEigen d μ := by
  have hspan := uniCubeRank_eigenspaces_sup_eq_top hK hq3 hd hd3 hω
  have hω3 : ω ^ 3 = 1 := uniCubeRank_cube_root_pow_three' hω
  have hω23 : (ω ^ 2) ^ 3 = 1 := by
    rw [show (ω ^ 2) ^ 3 = (ω ^ 3) ^ 2 by ring, hω3, one_pow]
  have hdist := uniCubeRank_cube_roots_distinct' hω
  have hperpν : ∀ (ν : K) (hν : ν ^ 3 = 1) (hνμ : ν ≠ μ),
      ∀ w ∈ cubeEigen d ν, stdHermForm hE N
        (((g : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ v) w = 0 := by
    intro ν hν hνμ w hw
    have hisog : IsHermIsometry (2 ^ f) (((g : GL (Fin N) K)) : Matrix (Fin N) (Fin N) K) :=
      hq ▸ uniCubeRank_isHermIsometry_of_mem_SU hK g.2
    have hpres := (uniCubeRank_isHermIsometry_iff_stdHermForm hE).mp hisog v
      ((((g⁻¹ : ↥(LargeEvenSUGroup (Fin N) K q)) : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ w)
    have hgg : ((g : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ
        ((((g⁻¹ : ↥(LargeEvenSUGroup (Fin N) K q)) : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ w) = w := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, Subgroup.coe_inv, mul_inv_cancel, Units.val_one,
        Matrix.one_mulVec]
    rw [hgg] at hpres
    have hfix : ((((g⁻¹ : ↥(LargeEvenSUGroup (Fin N) K q)) : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)) *ᵥ w = w :=
      (eigSub q d μ).inv_mem hg ν hν hνμ w hw
    rw [hfix] at hpres
    rw [hpres, uniCubeRank_stdHermForm_eq_sum_of_q hE hq]
    exact (uni_cube_eigen hK hq3 hd hd3).1 μ ν hμ hν (Ne.symm hνμ) v hv w hw
  rcases uniCubeRank_cube_root_eq_one_or hω μ hμ with hμ1 | hμω | hμω2
  · subst μ
    refine uniCubeRank_mem_of_perp_two hK hq3 hE hq hd hd3 hω (μ := 1) (ν := ω) (l := ω ^ 2)
      (by norm_num) hω3 hω23 hdist.1 hdist.2.1 hdist.2.2 ?_ ?_ ?_
    · rw [show cubeEigen d 1 ⊔ (cubeEigen d ω ⊔ cubeEigen d (ω ^ 2)) =
        cubeEigen d 1 ⊔ cubeEigen d ω ⊔ cubeEigen d (ω ^ 2) from by ac_rfl]
      exact hspan
    · exact hperpν ω hω3 (Ne.symm hdist.1)
    · exact hperpν (ω ^ 2) hω23 (Ne.symm hdist.2.1)
  · subst μ
    refine uniCubeRank_mem_of_perp_two hK hq3 hE hq hd hd3 hω (μ := ω) (ν := 1) (l := ω ^ 2)
      hω3 (by norm_num) hω23 (Ne.symm hdist.1) hdist.2.2 hdist.2.1 ?_ ?_ ?_
    · rw [show cubeEigen d ω ⊔ (cubeEigen d 1 ⊔ cubeEigen d (ω ^ 2)) =
        cubeEigen d 1 ⊔ cubeEigen d ω ⊔ cubeEigen d (ω ^ 2) from by ac_rfl]
      exact hspan
    · exact hperpν 1 (by norm_num) hdist.1
    · exact hperpν (ω ^ 2) hω23 (Ne.symm hdist.2.2)
  · subst μ
    refine uniCubeRank_mem_of_perp_two hK hq3 hE hq hd hd3 hω (μ := ω ^ 2) (ν := 1) (l := ω)
      hω23 (by norm_num) hω3 (Ne.symm hdist.2.1) (Ne.symm hdist.2.2) hdist.1 ?_ ?_ ?_
    · rw [show cubeEigen d (ω ^ 2) ⊔ (cubeEigen d 1 ⊔ cubeEigen d ω) =
        cubeEigen d 1 ⊔ cubeEigen d ω ⊔ cubeEigen d (ω ^ 2) from by ac_rfl]
      exact hspan
    · exact hperpν 1 (by norm_num) hdist.2.1
    · exact hperpν ω hω3 hdist.2.2

private theorem uniCubeRank_isConjBy_zpow {n q : ℕ} {K : Type} [Field K] {g : GL (Fin n) K}
    {a : MulAut (PSUg n K q)}
    (hN : g ∈ Subgroup.normalizer (LargeEvenSUGroup (Fin n) K q : Set (GL (Fin n) K)))
    (h : IsConjBy g a) (m : ℤ) : IsConjBy (g ^ m) (a ^ m) := by
  have hnorm : ∀ k ∈ LargeEvenSUGroup (Fin n) K q,
      g * k * g⁻¹ ∈ LargeEvenSUGroup (Fin n) K q :=
    fun k hk => (Subgroup.mem_normalizer_iff.mp hN k).mp hk
  have hnorm_inv : ∀ k ∈ LargeEvenSUGroup (Fin n) K q,
      g⁻¹ * k * (g⁻¹)⁻¹ ∈ LargeEvenSUGroup (Fin n) K q :=
    fun k hk => (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hN) k).mp hk
  obtain ⟨k, hk | hk⟩ := Int.eq_nat_or_neg m
  · rw [hk, zpow_natCast, zpow_natCast]
    exact uniCubeRank_isConjBy_pow hnorm h k
  · rw [hk, _root_.zpow_neg, zpow_natCast, _root_.zpow_neg, zpow_natCast]
    exact uniCubeRank_isConjBy_inv (uniCubeRank_isConjBy_pow hnorm h k)

private lemma uniCubeRank_form_sumL {K V ι : Type} [Field K] [AddCommGroup V] [Module K V]
    (σ : K →+* K) (H : V → V → K)
    (haddL : ∀ x y z, H (x + y) z = H x z + H y z)
    (hsmulL : ∀ (c : K) x y, H (c • x) y = σ c * H x y)
    (s : Finset ι) (f : ι → K) (v : ι → V) (y : V) :
    H (∑ i ∈ s, f i • v i) y = ∑ i ∈ s, σ (f i) * H (v i) y := by
  classical
  refine Finset.induction_on s ?base ?step
  · have h0 : H 0 y = 0 := by
      have h := hsmulL 0 (0 : V) y
      simpa using h
    simpa using h0
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, haddL, hsmulL, ih]

private lemma uniCubeRank_form_sumR {K V ι : Type} [Field K] [AddCommGroup V] [Module K V]
    (H : V → V → K)
    (haddR : ∀ x y z, H x (y + z) = H x y + H x z)
    (hsmulR : ∀ (c : K) x y, H x (c • y) = c * H x y)
    (x : V) (s : Finset ι) (f : ι → K) (v : ι → V) :
    H x (∑ i ∈ s, f i • v i) = ∑ i ∈ s, f i * H x (v i) := by
  classical
  refine Finset.induction_on s ?base ?step
  · have h0 : H x 0 = 0 := by
      have h := hsmulR 0 x (0 : V)
      simpa using h
    simpa using h0
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, haddR, hsmulR, ih]

private lemma uniCubeRank_form_eq_sum_orthonormal {K V : Type} [Field K] [AddCommGroup V]
    [Module K V] (H : V → V → K) (σ : K →+* K)
    (haddL : ∀ x y z, H (x + y) z = H x z + H y z)
    (hsmulL : ∀ (c : K) x y, H (c • x) y = σ c * H x y)
    (haddR : ∀ x y z, H x (y + z) = H x y + H x z)
    (hsmulR : ∀ (c : K) x y, H x (c • y) = c * H x y)
    {k : ℕ} (b : Module.Basis (Fin k) K V)
    (horth : ∀ i j, H (b i) (b j) = if i = j then 1 else 0) (x y : V) :
    H x y = ∑ i, σ (b.repr x i) * (b.repr y i) := by
  classical
  conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y]
  rw [uniCubeRank_form_sumL σ H haddL hsmulL Finset.univ (fun i => b.repr x i) b
    (∑ j, b.repr y j • b j)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [uniCubeRank_form_sumR H haddR hsmulR (b i) Finset.univ (fun j => b.repr y j) b]
  have hinner : (∑ j, b.repr y j * H (b i) (b j)) = b.repr y i := by
    rw [Finset.sum_eq_single i]
    · rw [horth i i]; simp
    · intro j _ hji; rw [horth i j, if_neg (fun h => hji h.symm), mul_zero]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  rw [hinner]

private lemma uniCubeRank_exists_restrict_hom
    {K : Type} [Field K] [Finite K] [CharP K 2] {q N : ℕ} (hK : Nat.card K = q ^ 2)
    (hq3 : 3 ∣ q + 1) {Ahat : Subgroup (GL (Fin N) K)}
    (hiso : ∀ g ∈ Ahat, IsHermIsometry q (g : Matrix (Fin N) (Fin N) K))
    {d : GL (Fin N) K} (hdA : d ∈ Ahat) (hd3 : d ^ 3 = 1)
    (hcomm : ∀ a ∈ Ahat, a * d * a⁻¹ = d) {μ : K} (hμ : μ ^ 3 = 1) :
    ∃ ρ : Ahat →* GL (Fin (Module.finrank K (cubeEigen d μ))) K,
      (∀ a : Ahat, IsHermIsometry q ((ρ a : GL (Fin (Module.finrank K (cubeEigen d μ))) K) :
        Matrix (Fin (Module.finrank K (cubeEigen d μ))) (Fin (Module.finrank K (cubeEigen d μ))) K)) ∧
      (∀ a : Ahat, ρ a = 1 ↔
        ∀ v ∈ cubeEigen d μ, ((a : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ v = v) ∧
      (∀ (a : Ahat) (c : Kˣ), (a : GL (Fin N) K) = Matrix.GeneralLinearGroup.scalar (Fin N) c →
        ρ a = Matrix.GeneralLinearGroup.scalar (Fin (Module.finrank K (cubeEigen d μ))) c) := by
  classical
  obtain ⟨f, hf, hq⟩ := CFSG.AGLEmbedding.ToralCensus.exists_eq_two_pow_of_card_eq_sq hK
  have hcard2 : Nat.card K = (2 ^ f) ^ 2 := by rw [hK, hq]
  have hE : UnitaryFieldData 2 f K :=
    ⟨Nat.prime_two, hf, by rw [hcard2, ← pow_mul, mul_comm]⟩
  obtain ⟨ω, hω⟩ := uniCubeRank_exists_cube_root_K (f := f) hcard2
  let V : Submodule K (Fin N → K) := cubeEigen d μ
  let k : ℕ := Module.finrank K V
  let H : V → V → K := fun x y => stdHermForm hE N x.1 y.1
  have hHsep : ((stdHermForm hE N).domRestrict₁₂ V V).SeparatingLeft :=
    uniCubeRank_eigenspace_separatingLeft hK hq3 hE hq (hiso d hdA) hd3 hμ hω
  have hnondeg : ∀ x : V, (∀ y : V, H x y = 0) → x = 0 := by
    intro x hx
    have h := hHsep x (fun y => by simpa only [LinearMap.domRestrict₁₂_apply] using hx y)
    simpa using congrArg Subtype.val h
  have hherm : ∀ x y : V, H x y = hE.barEquiv (H y x) := by
    intro x y
    change stdHermForm hE N x.1 y.1 = hE.barEquiv (stdHermForm hE N y.1 x.1)
    rw [UnitaryFieldData.barEquiv_apply, stdHermForm_apply, stdHermForm_apply, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_mul, hE.bar_bar]; ring
  have haddL : ∀ x y z : V, H (x + y) z = H x z + H y z := by
    intro x y z
    change stdHermForm hE N (x.1 + y.1) z.1 =
      stdHermForm hE N x.1 z.1 + stdHermForm hE N y.1 z.1
    simp only [stdHermForm_apply, Pi.add_apply, map_add, LinearMap.add_apply, add_mul,
      Finset.sum_add_distrib]
  have hsmulL : ∀ (c : K) (x y : V), H (c • x) y = hE.barEquiv c * H x y := by
    intro c x y
    change stdHermForm hE N (c • x.1) y.1 = hE.barEquiv c * stdHermForm hE N x.1 y.1
    rw [UnitaryFieldData.barEquiv_apply, stdHermForm_apply, stdHermForm_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by
      simp only [Pi.smul_apply, smul_eq_mul, map_mul]; ring
  have haddR : ∀ x y z : V, H x (y + z) = H x y + H x z := by
    intro x y z
    change stdHermForm hE N x.1 (y.1 + z.1) =
      stdHermForm hE N x.1 y.1 + stdHermForm hE N x.1 z.1
    rw [map_add]
  have hsmulR : ∀ (c : K) (x y : V), H x (c • y) = c * H x y := by
    intro c x y
    change stdHermForm hE N x.1 (c • y.1) = c * stdHermForm hE N x.1 y.1
    rw [map_smul, smul_eq_mul]
  obtain ⟨b, hb⟩ := exists_hermOrthonormalBasis hE.barEquiv hE.isUnitaryInvolution_barEquiv
    H k rfl hherm haddL hsmulL haddR hsmulR hnondeg
  have hpres : ∀ (a : Ahat) (x : V),
      ((a : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ x.1 ∈ V := by
    intro a x
    have ha_d : (a : GL (Fin N) K) * d = d * (a : GL (Fin N) K) := by
      calc (a : GL (Fin N) K) * d =
            ((a : GL (Fin N) K) * d * (a : GL (Fin N) K)⁻¹) * (a : GL (Fin N) K) := by group
        _ = d * (a : GL (Fin N) K) := by rw [hcomm a a.2]
    have hxv : ((d : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ x.1 = μ • x.1 := by
      have h := Module.End.mem_eigenspace_iff.mp x.2
      simpa [cubeEigen, Matrix.toLin'_apply] using h
    have hda : ((d : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *
        ((a : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) =
        ((a : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *
        ((d : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) := by
      have h := congrArg (fun y : GL (Fin N) K => (y : Matrix (Fin N) (Fin N) K)) ha_d
      simpa only [Units.val_mul] using h.symm
    change ((a : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ x.1 ∈ cubeEigen d μ
    rw [cubeEigen, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    calc ((d : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ
          (((a : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ x.1)
        = (((d : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *
            ((a : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)) *ᵥ x.1 := by
            rw [Matrix.mulVec_mulVec]
      _ = (((a : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *
            ((d : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)) *ᵥ x.1 := by rw [hda]
      _ = ((a : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ
            (((d : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ x.1) := by
            rw [Matrix.mulVec_mulVec]
      _ = ((a : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ (μ • x.1) := by rw [hxv]
      _ = μ • (((a : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ x.1) := by
            rw [Matrix.mulVec_smul]
  let F : Ahat →* (V →ₗ[K] V) :=
    { toFun := fun a =>
        { toFun := fun x =>
            ⟨((a : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ x.1, hpres a x⟩
          map_add' := fun x y => Subtype.ext (by
            change ((a : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ (x.1 + y.1) =
              ((a : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ x.1 +
                ((a : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ y.1
            rw [Matrix.mulVec_add])
          map_smul' := fun c x => Subtype.ext (by
            change ((a : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ (c • x.1) =
              c • (((a : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ x.1)
            rw [Matrix.mulVec_smul]) }
      map_one' := by
        apply LinearMap.ext
        intro x
        apply Subtype.ext
        change ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ x.1 = x.1
        rw [Units.val_one, Matrix.one_mulVec]
      map_mul' := by
        intro a b
        apply LinearMap.ext
        intro x
        apply Subtype.ext
        change ((a * b : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ x.1 =
          ((a : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ
            (((b : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ x.1)
        rw [Units.val_mul, Matrix.mulVec_mulVec] }
  let ρ : Ahat →* GL (Fin k) K :=
    (Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toMulEquiv).toMonoidHom.comp
      (MonoidHom.toHomUnits F)
  have hρ_coe : ∀ a : Ahat, ((ρ a : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) =
      LinearMap.toMatrixAlgEquiv b (F a) := by
    intro a
    change ((Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toMulEquiv)
        (MonoidHom.toHomUnits F a) : Matrix (Fin k) (Fin k) K) =
      (LinearMap.toMatrixAlgEquiv b) (F a)
    rw [Units.coe_mapEquiv, MonoidHom.coe_toHomUnits]
    rfl
  have hHcoord : ∀ x y : V, H x y = stdHermForm hE k (b.equivFun x) (b.equivFun y) := by
    intro x y
    rw [uniCubeRank_form_eq_sum_orthonormal H hE.bar haddL hsmulL haddR hsmulR b hb x y,
      uniCubeRank_stdHermForm_eq_sum_of_q hE (q := 2 ^ f) rfl]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Module.Basis.equivFun_apply, Module.Basis.equivFun_apply, hE.bar_apply]
  have hcoord : ∀ (a : Ahat) (x : V),
      (LinearMap.toMatrixAlgEquiv b (F a)) *ᵥ (b.equivFun x) = b.equivFun (F a x) := by
    intro a x
    rw [Module.Basis.equivFun_apply b x, Module.Basis.equivFun_apply b (F a x)]
    exact LinearMap.toMatrix_mulVec_repr (v₁ := b) (v₂ := b) (F a) x
  have hequiv_sum : ∀ c : Fin k → K, b.equivFun (∑ i, c i • b i) = c := by
    intro c
    rw [Module.Basis.equivFun_apply]
    simpa using Module.Basis.repr_sum_self b c
  have hpreserve : ∀ (a : Ahat) (x y : V), H (F a x) (F a y) = H x y := by
    intro a x y
    have ha : IsHermIsometry (2 ^ f) (((a : GL (Fin N) K)) : Matrix (Fin N) (Fin N) K) :=
      hq ▸ hiso a a.2
    have h := (uniCubeRank_isHermIsometry_iff_stdHermForm hE).mp ha x.1 y.1
    change stdHermForm hE N
        ((((a : GL (Fin N) K)) : Matrix (Fin N) (Fin N) K) *ᵥ x.1)
        ((((a : GL (Fin N) K)) : Matrix (Fin N) (Fin N) K) *ᵥ y.1) =
      stdHermForm hE N x.1 y.1
    exact h
  refine ⟨ρ, ?_, ?_, ?_⟩
  · intro a
    rw [hq, uniCubeRank_isHermIsometry_iff_stdHermForm hE]
    intro c d
    have hX : b.equivFun (∑ i, c i • b i) = c := hequiv_sum c
    have hY : b.equivFun (∑ i, d i • b i) = d := hequiv_sum d
    have hMc := hcoord a (∑ i, c i • b i)
    have hMd := hcoord a (∑ i, d i • b i)
    rw [hX] at hMc
    rw [hY] at hMd
    rw [hρ_coe a, hMc, hMd, ← hHcoord (F a _) (F a _), hpreserve a _ _,
      hHcoord (∑ i, c i • b i) (∑ i, d i • b i), hX, hY]
  · intro a
    rw [← Units.val_eq_one, hρ_coe a]
    constructor
    · intro h v hv
      have hF : F a = 1 :=
        (LinearMap.toMatrixAlgEquiv b).injective (by rw [h, map_one])
      have hx : F a ⟨v, hv⟩ = ⟨v, hv⟩ := by rw [hF]; rfl
      show ((a : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ v = v
      exact congrArg Subtype.val hx
    · intro h
      have hF : F a = 1 := by
        apply LinearMap.ext
        intro x
        apply Subtype.ext
        change ((a : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ x.1 = x.1
        exact h x.1 x.2
      rw [hF, map_one]
  · intro a c ha
    apply Units.ext
    rw [hρ_coe a, Matrix.GeneralLinearGroup.coe_scalar]
    have hF : F a = (c : K) • (1 : V →ₗ[K] V) := by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      change ((a : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ x.1 = (c : K) • x.1
      rw [ha, Matrix.GeneralLinearGroup.coe_scalar, uniCubeRank_scalar_mulVec]
    rw [hF, map_smul, map_one, uniCubeRank_scalar_eq_smul_one]

private lemma uniCubeRank_card_fix_le_three
    {K : Type} [Field K] [Finite K] [CharP K 2] {q N : ℕ} (hK : Nat.card K = q ^ 2)
    (hq3 : 3 ∣ q + 1) (hN : 4 ≤ N)
    {Ā : Subgroup (MulAut (PSUg N K q))} {δ' : MulAut (PSUg N K q)}
    {J' : Subgroup (PSUg N K q)} (hR : RDatum Ā δ' J') {Ahat : Subgroup (GL (Fin N) K)}
    (hL : UniLift N q K Ā Ahat) {d : GL (Fin N) K} (hdA : d ∈ Ahat) (hd3 : d ^ 3 = 1)
    (hδ : IsConjBy d δ') {μ : K} (hμ : μ ^ 3 = 1) (hJ : J' = eigBlock q d μ)
    (hcomm : ∀ a ∈ Ahat, a * d * a⁻¹ = d) :
    Nat.card {x : Ahat // ∀ v ∈ cubeEigen d μ,
      ((x : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ v = v} ≤ 3 := by
  classical
  obtain ⟨f, hf, hq⟩ := CFSG.AGLEmbedding.ToralCensus.exists_eq_two_pow_of_card_eq_sq hK
  have hcard2 : Nat.card K = (2 ^ f) ^ 2 := by rw [hK, hq]
  have hE : UnitaryFieldData 2 f K :=
    ⟨Nat.prime_two, hf, by rw [hcard2, ← pow_mul, mul_comm]⟩
  obtain ⟨ω, hω⟩ := uniCubeRank_exists_cube_root_K (f := f) hcard2
  have hd' : IsHermIsometry q (d : Matrix (Fin N) (Fin N) K) := hL.iso d hdA
  have hspan := uniCubeRank_eigenspaces_sup_eq_top hK hq3 hd' hd3 hω
  have hω3 : ω ^ 3 = 1 := uniCubeRank_cube_root_pow_three' hω
  have hω23 : (ω ^ 2) ^ 3 = 1 := by
    rw [show (ω ^ 2) ^ 3 = (ω ^ 3) ^ 2 by ring, hω3, one_pow]
  have hdist := uniCubeRank_cube_roots_distinct' hω
  have hVne : cubeEigen d μ ≠ ⊥ := by
    intro hbot
    have heig : eigSub q d μ = ⊥ := by
      apply le_antisymm _ bot_le
      intro g hg
      rw [Subgroup.mem_bot]
      have hfixall : ∀ v, ((g : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ v = v := by
        intro v
        have hv : v ∈ cubeEigen d 1 ⊔ cubeEigen d ω ⊔ cubeEigen d (ω ^ 2) := by rw [hspan]; trivial
        obtain ⟨v12, hv12, v3, hv3, rfl⟩ := Submodule.mem_sup.mp hv
        obtain ⟨v1, hv1, v2, hv2, rfl⟩ := Submodule.mem_sup.mp hv12
        have hf1 : ((g : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ v1 = v1 := by
          by_cases h1 : (1 : K) = μ
          · have hbot' : cubeEigen d 1 = ⊥ := by rw [h1]; exact hbot
            rw [hbot', Submodule.mem_bot] at hv1
            rw [hv1, Matrix.mulVec_zero]
          · exact hg 1 (by norm_num) h1 v1 hv1
        have hf2 : ((g : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ v2 = v2 := by
          by_cases h2 : ω = μ
          · have hbot' : cubeEigen d ω = ⊥ := by rw [h2]; exact hbot
            rw [hbot', Submodule.mem_bot] at hv2
            rw [hv2, Matrix.mulVec_zero]
          · exact hg ω hω3 h2 v2 hv2
        have hf3 : ((g : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ v3 = v3 := by
          by_cases h3 : (ω ^ 2) = μ
          · have hbot' : cubeEigen d (ω ^ 2) = ⊥ := by rw [h3]; exact hbot
            rw [hbot', Submodule.mem_bot] at hv3
            rw [hv3, Matrix.mulVec_zero]
          · exact hg (ω ^ 2) hω23 h3 v3 hv3
        simp only [Matrix.mulVec_add, hf1, hf2, hf3]
      have hmat : ((g : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) = 1 := by
        apply Matrix.toLin'.injective
        apply LinearMap.ext
        intro v
        simpa only [Matrix.toLin'_apply, Matrix.one_mulVec] using hfixall v
      exact Subtype.ext (by rw [Subgroup.coe_one]; exact Units.ext (by rw [Units.val_one]; exact hmat))
    have hJbot : J' = ⊥ := by rw [hJ, eigBlock, heig, Subgroup.map_bot]
    haveI : Nontrivial (↥J' ⧸ Subgroup.center ↥J') := hR.comp.2.2.2.toNontrivial
    have hnt : Nontrivial ↥J' :=
      Function.Surjective.nontrivial (QuotientGroup.mk'_surjective (Subgroup.center ↥J'))
    rw [hJbot] at hnt
    exact (Subgroup.nontrivial_iff_ne_bot (⊥ : Subgroup (PSUg N K q))).mp hnt rfl
  obtain ⟨v0, hv0, hv00⟩ : ∃ v ∈ cubeEigen d μ, v ≠ 0 := by
    by_contra h
    push Not at h
    exact hVne (le_antisymm (fun x hx => by rw [Submodule.mem_bot]; exact h x hx) bot_le)
  have hμ0 : μ ≠ 0 := by
    intro h0; rw [h0] at hμ; norm_num at hμ
  let u : Kˣ := Units.mk0 μ hμ0
  have hu_val : (u : K) = μ := rfl
  have hxscalar : ∀ x : Ahat, (∀ v ∈ cubeEigen d μ,
        ((x : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ v = v) →
      ∃ j : Fin 3, (x : GL (Fin N) K) =
        Matrix.GeneralLinearGroup.scalar (Fin N) ((u ^ (j : ℤ))⁻¹) * d ^ (j : ℤ) := by
    intro x hx
    obtain ⟨xbar, hxbarĀ, hxbarconj⟩ := hL.induces x x.2
    have hxd : (x : GL (Fin N) K) * d = d * (x : GL (Fin N) K) := by
      calc (x : GL (Fin N) K) * d =
            ((x : GL (Fin N) K) * d * (x : GL (Fin N) K)⁻¹) * (x : GL (Fin N) K) := by group
        _ = d * (x : GL (Fin N) K) := by rw [hcomm x x.2]
    have hpres_x : ∀ (ν : K) (v : Fin N → K), v ∈ cubeEigen d ν →
        ((x : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ v ∈ cubeEigen d ν := by
      intro ν v hv
      have hv' : ((d : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ v = ν • v := by
        have h := Module.End.mem_eigenspace_iff.mp hv
        simpa [cubeEigen, Matrix.toLin'_apply] using h
      have hdx : ((d : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *
          ((x : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) =
          ((x : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *
          ((d : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) := by
        have h := congrArg (fun y : GL (Fin N) K => (y : Matrix (Fin N) (Fin N) K)) hxd
        simpa only [Units.val_mul] using h.symm
      rw [cubeEigen, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
      calc ((d : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ
            (((x : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ v)
          = (((d : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *
              ((x : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)) *ᵥ v := by
              rw [Matrix.mulVec_mulVec]
        _ = (((x : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *
              ((d : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)) *ᵥ v := by rw [hdx]
        _ = ((x : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ
              (((d : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ v) := by
              rw [Matrix.mulVec_mulVec]
        _ = ((x : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ (ν • v) := by rw [hv']
        _ = ν • (((x : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ v) := by
              rw [Matrix.mulVec_smul]
    have hfixJ : ∀ j ∈ J', xbar j = j := by
      intro j hj
      rw [hJ] at hj
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hj
      have hkey : ∀ (ν : K) (hν : ν ^ 3 = 1) (v : Fin N → K), v ∈ cubeEigen d ν →
          ((x : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ
              (((g : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ v) =
            ((g : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ
              (((x : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ v) := by
        intro ν hν v hv
        by_cases hνμ : ν = μ
        · subst ν
          have hgv : ((g : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ v ∈ cubeEigen d μ :=
            uniCubeRank_eigSub_maps_self hK hq3 hE hq hd' hd3 hω hμ hg hv
          rw [hx (((g : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ v) hgv, hx v hv]
        · have hgv : ((g : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ v = v := hg ν hν hνμ v hv
          have hxv : ((x : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ v ∈ cubeEigen d ν :=
            hpres_x ν v hv
          rw [hgv, hg ν hν hνμ (((x : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ v) hxv]
      have hcommv : ∀ v, ((x : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ
            (((g : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ v) =
          ((g : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ
            (((x : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ v) := by
        intro v
        have hv : v ∈ cubeEigen d 1 ⊔ cubeEigen d ω ⊔ cubeEigen d (ω ^ 2) := by rw [hspan]; trivial
        obtain ⟨v12, hv12, v3, hv3, rfl⟩ := Submodule.mem_sup.mp hv
        obtain ⟨v1, hv1, v2, hv2, rfl⟩ := Submodule.mem_sup.mp hv12
        simp only [Matrix.mulVec_add]
        rw [hkey 1 (by norm_num) v1 hv1, hkey ω hω3 v2 hv2, hkey (ω ^ 2) hω23 v3 hv3]
      have hcomm_mat : ((x : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *
          ((g : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) =
          ((g : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *
          ((x : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) := by
        apply Matrix.toLin'.injective
        apply LinearMap.ext
        intro v
        rw [Matrix.toLin'_mul_apply, Matrix.toLin'_mul_apply, Matrix.toLin'_apply,
          Matrix.toLin'_apply]
        exact hcommv v
      have hxg : (x : GL (Fin N) K) * (g : GL (Fin N) K) =
          (g : GL (Fin N) K) * (x : GL (Fin N) K) := Units.ext hcomm_mat
      have hconj_eq : (g : GL (Fin N) K) =
          (x : GL (Fin N) K) * (g : GL (Fin N) K) * (x : GL (Fin N) K)⁻¹ := by
        rw [hxg]; group
      exact hxbarconj g g hconj_eq
    have hxbar_zp : xbar ∈ Subgroup.zpowers δ' := hR.ker xbar hxbarĀ hfixJ
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hxbar_zp
    have hd3z : d ^ (3 : ℤ) = 1 := by
      show d ^ ((3 : ℕ) : ℤ) = 1
      rw [zpow_natCast, hd3]
    have hnorm_d : d ∈ Subgroup.normalizer (LargeEvenSUGroup (Fin N) K q : Set (GL (Fin N) K)) :=
      uniCubeRank_isHermIsometry_mem_normalizer hK hd'
    have hconj_di : IsConjBy (d ^ i) (δ' ^ i) := uniCubeRank_isConjBy_zpow hnorm_d hδ i
    have hconj_dx : IsConjBy (d ^ i) xbar := by rw [← hi]; exact hconj_di
    have hmod_nonneg : 0 ≤ i % 3 := Int.emod_nonneg i (by norm_num)
    have hmod_lt : i % 3 < 3 := Int.emod_lt_of_pos i (by norm_num)
    let j : Fin 3 := ⟨(i % 3).toNat, by omega⟩
    have hj : ((j : ℕ) : ℤ) = i % 3 := Int.toNat_of_nonneg hmod_nonneg
    have hdi : d ^ i = d ^ (j : ℤ) := by rw [zpow_eq_zpow_emod i hd3z, ← hj]
    have hconj_dj : IsConjBy (d ^ (j : ℤ)) xbar := by rw [← hdi]; exact hconj_dx
    have hy_mem : (x : GL (Fin N) K) * (d ^ (j : ℤ))⁻¹ ∈ Ahat :=
      Ahat.mul_mem x.2 (Ahat.inv_mem (Subgroup.zpow_mem Ahat hdA (j : ℤ)))
    have hnorm_dj_inv : ∀ k ∈ LargeEvenSUGroup (Fin N) K q,
        (d ^ (j : ℤ))⁻¹ * k * ((d ^ (j : ℤ))⁻¹)⁻¹ ∈ LargeEvenSUGroup (Fin N) K q :=
      fun k hk => (Subgroup.mem_normalizer_iff.mp
        (Subgroup.inv_mem _ (Subgroup.zpow_mem
          (Subgroup.normalizer (LargeEvenSUGroup (Fin N) K q : Set (GL (Fin N) K)))
          hnorm_d (j : ℤ))) k).mp hk
    have hconj_y : IsConjBy ((x : GL (Fin N) K) * (d ^ (j : ℤ))⁻¹)
        (1 : MulAut (PSUg N K q)) := by
      have h1 := uniCubeRank_isConjBy_mul hnorm_dj_inv hxbarconj (uniCubeRank_isConjBy_inv hconj_dj)
      simpa using h1
    obtain ⟨c, hc_norm, hc_eq⟩ := hL.ker ((x : GL (Fin N) K) * (d ^ (j : ℤ))⁻¹) hy_mem hconj_y
    have hx_gl : (x : GL (Fin N) K) =
        Matrix.GeneralLinearGroup.scalar (Fin N) c * d ^ (j : ℤ) := by
      calc (x : GL (Fin N) K) =
            ((x : GL (Fin N) K) * (d ^ (j : ℤ))⁻¹) * (d ^ (j : ℤ)) := by group
        _ = Matrix.GeneralLinearGroup.scalar (Fin N) c * d ^ (j : ℤ) := by rw [hc_eq]
    have hdjz : d ^ (j : ℤ) = d ^ (j : ℕ) := by
      show d ^ ((j : ℕ) : ℤ) = d ^ (j : ℕ)
      rw [zpow_natCast]
    have heig : Module.End.HasEigenvector
        (Matrix.toLin' ((d : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)) μ v0 :=
      Module.End.hasEigenvector_iff.mpr ⟨hv0, hv00⟩
    have hdjv : (d ^ (j : ℕ) : GL (Fin N) K) *ᵥ v0 = (μ ^ (j : ℕ)) • v0 := by
      have h1 := heig.pow_apply (j : ℕ)
      rw [← Matrix.toLin'_pow, Matrix.toLin'_apply, ← Units.val_pow_eq_pow_val] at h1
      exact h1
    have hcμ : c * (μ ^ (j : ℕ)) = 1 := by
      have h1 : ((Matrix.GeneralLinearGroup.scalar (Fin N) c * d ^ (j : ℤ) : GL (Fin N) K) :
          Matrix (Fin N) (Fin N) K) *ᵥ v0 = v0 := by
        rw [← hx_gl]; exact hx v0 hv0
      rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, ← Matrix.mulVec_mulVec, hdjz, hdjv,
        Matrix.mulVec_smul, uniCubeRank_scalar_mulVec, smul_smul] at h1
      obtain ⟨i0, hi0⟩ : ∃ i0, v0 i0 ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hv00 (funext hcon)
      have h2 := congrFun h1 i0
      rw [Pi.smul_apply, smul_eq_mul] at h2
      have h3 : (μ ^ (j : ℕ) * c - 1) * v0 i0 = 0 := by rw [sub_mul, one_mul, h2, sub_self]
      have h4 : μ ^ (j : ℕ) * c - 1 = 0 := (mul_eq_zero.mp h3).resolve_right hi0
      have h5 : μ ^ (j : ℕ) * c = 1 := sub_eq_zero.mp h4
      rw [mul_comm] at h5
      exact h5
    have hc_unit : c = (u ^ (j : ℤ))⁻¹ := by
      apply Units.ext
      rw [Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, hu_val, zpow_natCast]
      exact eq_inv_of_mul_eq_one_left hcμ
    exact ⟨j, by rw [hx_gl, hc_unit]⟩
  let g : {x : Ahat // ∀ v ∈ cubeEigen d μ,
      ((x : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ v = v} → Fin 3 :=
    fun x => Classical.choose (hxscalar x.1 x.2)
  have hg_inj : Function.Injective g := by
    intro x y hxy
    have hx := Classical.choose_spec (hxscalar x.1 x.2)
    have hy := Classical.choose_spec (hxscalar y.1 y.2)
    have hji : Classical.choose (hxscalar x.1 x.2) = Classical.choose (hxscalar y.1 y.2) := hxy
    exact Subtype.ext (Subtype.ext (by rw [hx, hy, hji]))
  calc Nat.card {x : Ahat // ∀ v ∈ cubeEigen d μ,
        ((x : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ v = v} ≤ Nat.card (Fin 3) :=
        Nat.card_le_card_of_injective g hg_inj
    _ = 3 := by simp

end Toolbox

theorem uniR_cube_rank {K : Type} [Field K] [Finite K] [CharP K 2] {q N : ℕ} (hK : Nat.card K = q ^ 2)
    (hq3 : 3 ∣ q + 1) (hN : 4 ≤ N)
    {Ā : Subgroup (MulAut (PSUg N K q))} {δ' : MulAut (PSUg N K q)}
    {J' : Subgroup (PSUg N K q)} (hR : RDatum Ā δ' J') {Ahat : Subgroup (GL (Fin N) K)}
    (hL : UniLift N q K Ā Ahat) (hcard : Nat.card Ahat = Nat.card Ā * (q + 1)) {d : GL (Fin N) K}
    (hdA : d ∈ Ahat) (hd3 : d ^ 3 = 1) (hδ : IsConjBy d δ')
    {μ : K} (hμ : μ ^ 3 = 1) (hJ : J' = eigBlock q d μ) (hQS : CubeBlockQS q d μ)
    (hk : Module.finrank K (cubeEigen d μ) = 2 ∨ Module.finrank K (cubeEigen d μ) = 3) :
    Nat.card Ā ≤ 3 ^ Module.finrank K (cubeEigen d μ) := by
  classical
  let k : ℕ := Module.finrank K (cubeEigen d μ)
  have hk2 : 2 ≤ k := by rcases hk with h | h <;> omega
  have hcomm : ∀ a ∈ Ahat, a * d * a⁻¹ = d :=
    fun a ha => uniCubeRank_conj_d_eq_of_mem_Ahat hK hq3 hN hR hL hdA hd3 hδ hμ hJ hk2 ha
  obtain ⟨ρ, hρ_iso, hρ_ker, hρ_scalar⟩ :=
    uniCubeRank_exists_restrict_hom hK hq3 hL.iso hdA hd3 hcomm hμ
  have hcard_ker_eq : Nat.card ρ.ker = Nat.card {x : Ahat // ∀ v ∈ cubeEigen d μ,
      Matrix.mulVec ((x : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) v = v} := by
    apply Nat.card_congr
    exact
      { toFun := fun x => ⟨x.1, (hρ_ker x.1).mp x.2⟩
        invFun := fun x => ⟨x.1, (hρ_ker x.1).mpr x.2⟩
        left_inv := fun x => Subtype.ext rfl
        right_inv := fun x => Subtype.ext rfl }
  have hker_le : Nat.card ρ.ker ≤ 3 := by
    rw [hcard_ker_eq]
    exact uniCubeRank_card_fix_le_three hK hq3 hN hR hL hdA hd3 hδ hμ hJ hcomm
  have hisoρ : ∀ g ∈ ρ.range, IsHermIsometry q (g : Matrix (Fin k) (Fin k) K) := by
    intro g hg
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hg
    exact hρ_iso a
  have hcommρ : ∀ g ∈ ρ.range, ∀ h ∈ ρ.range,
      ∃ c : Kˣ, g * h * g⁻¹ * h⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin k) c := by
    intro g hg h hh
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hg
    obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hh
    obtain ⟨ā, hā, haconj⟩ := hL.induces a a.2
    obtain ⟨bbar, hbbar, hbconj⟩ := hL.induces b b.2
    have hnorm_of : ∀ {x : GL (Fin N) K}, IsHermIsometry q (x : Matrix (Fin N) (Fin N) K) →
        ∀ m ∈ LargeEvenSUGroup (Fin N) K q, x * m * x⁻¹ ∈ LargeEvenSUGroup (Fin N) K q :=
      fun {x} hx m hm =>
        (Subgroup.mem_normalizer_iff.mp (uniCubeRank_isHermIsometry_mem_normalizer hK hx) m).mp hm
    have h1 : IsConjBy (a * b) (ā * bbar) := uniCubeRank_isConjBy_mul (hnorm_of (hL.iso b b.2)) haconj hbconj
    have h2 : IsConjBy (a * b * a⁻¹) (ā * bbar * ā⁻¹) :=
      uniCubeRank_isConjBy_mul (hnorm_of (uniCubeRank_isHermIsometry_inv hK (hL.iso a a.2))) h1 (uniCubeRank_isConjBy_inv haconj)
    have h3 : IsConjBy (a * b * a⁻¹ * b⁻¹) (ā * bbar * ā⁻¹ * bbar⁻¹) :=
      uniCubeRank_isConjBy_mul (hnorm_of (uniCubeRank_isHermIsometry_inv hK (hL.iso b b.2))) h2 (uniCubeRank_isConjBy_inv hbconj)
    have hcommĀ : ā * bbar * ā⁻¹ * bbar⁻¹ = 1 := by
      have hcm : ā * bbar = bbar * ā :=
        congrArg Subtype.val (hR.elem.1.is_comm.comm ⟨ā, hā⟩ ⟨bbar, hbbar⟩)
      calc ā * bbar * ā⁻¹ * bbar⁻¹ = bbar * ā * ā⁻¹ * bbar⁻¹ := by rw [hcm]
        _ = 1 := by group
    rw [hcommĀ] at h3
    let y : Ahat := a * b * a⁻¹ * b⁻¹
    have hy_conj : IsConjBy (y : GL (Fin N) K) (1 : MulAut (PSUg N K q)) := by
      change IsConjBy ((a : GL (Fin N) K) * (b : GL (Fin N) K) * (a : GL (Fin N) K)⁻¹ *
        (b : GL (Fin N) K)⁻¹) (1 : MulAut (PSUg N K q))
      exact h3
    obtain ⟨c, -, hc⟩ := hL.ker (y : GL (Fin N) K) y.2 hy_conj
    refine ⟨c, ?_⟩
    have hyρ : ρ y = ρ a * ρ b * (ρ a)⁻¹ * (ρ b)⁻¹ := by
      rw [show y = a * b * a⁻¹ * b⁻¹ from rfl]
      simp only [map_mul, map_inv]
    rw [← hyρ]
    exact hρ_scalar y c hc
  have hcubeρ : ∀ g ∈ ρ.range, ∃ c : Kˣ, g ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin k) c := by
    intro g hg
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hg
    obtain ⟨ā, hā, haconj⟩ := hL.induces a a.2
    have hā3 : ā ^ 3 = 1 := hR.elem.2 ā hā
    have hnorm_a : ∀ m ∈ LargeEvenSUGroup (Fin N) K q,
        a * m * a⁻¹ ∈ LargeEvenSUGroup (Fin N) K q :=
      fun m hm =>
        (Subgroup.mem_normalizer_iff.mp (uniCubeRank_isHermIsometry_mem_normalizer hK (hL.iso a a.2)) m).mp hm
    have h3 : IsConjBy ((a : GL (Fin N) K) ^ 3) (1 : MulAut (PSUg N K q)) := by
      have h := uniCubeRank_isConjBy_pow hnorm_a haconj 3
      rwa [hā3] at h
    let y : Ahat := a ^ 3
    have hy_conj : IsConjBy (y : GL (Fin N) K) (1 : MulAut (PSUg N K q)) := by
      change IsConjBy ((a : GL (Fin N) K) ^ 3) (1 : MulAut (PSUg N K q))
      exact h3
    obtain ⟨c, -, hc⟩ := hL.ker (y : GL (Fin N) K) y.2 hy_conj
    refine ⟨c, ?_⟩
    have hyρ : ρ y = ρ a ^ 3 := by
      rw [show y = a ^ 3 from rfl]
      simp only [map_pow]
    rw [← hyρ]
    exact hρ_scalar y c hc
  have hrange_le : Nat.card ρ.range ≤ 3 ^ (k - 1) * (q + 1) :=
    uni_gu_three_rank hK hq3 hk ρ.range hisoρ hcommρ hcubeρ
  have hcardAhat : Nat.card Ahat = Nat.card ρ.ker * Nat.card ρ.range :=
    (Subgroup.card_ker_mul_card_range ρ).symm
  have hpow : 3 * 3 ^ (k - 1) = 3 ^ k := by
    have hk1 : 1 ≤ k := by omega
    calc 3 * 3 ^ (k - 1) = 3 ^ (k - 1 + 1) := by rw [pow_succ']
      _ = 3 ^ k := by rw [Nat.sub_add_cancel hk1]
  have hmain : Nat.card Ā * (q + 1) ≤ 3 ^ k * (q + 1) := by
    rw [← hcard]
    calc Nat.card Ahat = Nat.card ρ.ker * Nat.card ρ.range := hcardAhat
      _ ≤ 3 * (3 ^ (k - 1) * (q + 1)) := Nat.mul_le_mul hker_le hrange_le
      _ = 3 * 3 ^ (k - 1) * (q + 1) := by ring
      _ = 3 ^ k * (q + 1) := by rw [hpow]
  exact Nat.le_of_mul_le_mul_right hmain (by omega : 0 < q + 1)

end CFSG.StandardType.TablePThreeKG

end
