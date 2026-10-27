module

public import CFSG.RankThree.PartTwo.Sec21.Hering214KRoot
public import CFSG.RankThree.PartTwo.Sec21.Hering214KEig
public import CFSG.RankThree.SubgroupLists.SymplecticTransvections
public import CFSG.RankThree.SubgroupLists.SymplecticBaseChange
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherAutomorphismData
public import CFSG.GroupTheory.BaerSuzuki
public import CFSG.LocalAnalysis.ComponentClassification.BlockMutualRanks
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionProperEmbedding
public import CFSG.RankThree.PartTwo.Sec11.Theorem1134
public import CFSG.RankThree.PartTwo.Sec21.Hering214KNine
public import CFSG.RankThree.PartTwo.Sec21.Item21Early3ProofExists
public import CFSG.RankThree.PartTwo.Sec4.LThreePiSLOn
public import CFSG.RankThree.PartTwo.Sec7.ThreeTranspositions
public import CFSG.RankThree.PartTwo.Sec8.Pairs
public import Certificates.Certificate3084
public import Certificates.Certificate3139
public import Certificates.Certificate3168
public import Certificates.Certificate3169

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214

open Matrix
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.LowTwoRank
open CFSG.RankThree.SubgroupLists
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

section Sp4M

variable {F : Type} [Field F]

local notation "V₄" => Fin 2 ⊕ Fin 2

noncomputable def spRoot (v : V₄ → F) (t : F) : ↥(StatedSp 2 F) :=
  ⟨spTrans v t, spTrans_mem_statedSp v t⟩

theorem spRoot_add (v : V₄ → F) (s t : F) : spRoot v (s + t) = spRoot v s * spRoot v t :=
  Subtype.ext (spTrans_add v s t).symm

theorem spRoot_inj {v : V₄ → F} (hv : v ≠ 0) {s t : F} (h : spRoot v s = spRoot v t) :
    s = t := by
  have h' : spTrans v s = spTrans v t := congrArg Subtype.val h
  obtain ⟨x, hx⟩ : ∃ x, spForm 2 F x v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hv (spForm_nondegenerate.2 v hcon)
  have h2 := congrArg (fun g : GL V₄ F => (g : Matrix V₄ V₄ F) *ᵥ x) h'
  simp only [spTrans_mulVec] at h2
  have h3 : (s * spForm 2 F x v) • v = (t * spForm 2 F x v) • v := add_left_cancel h2
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  have h4 := congrFun h3 i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h4 hi
  have h5 : (s - t) * (spForm 2 F x v * v i) = 0 := by linear_combination h4
  rcases mul_eq_zero.mp h5 with h6 | h6
  · exact sub_eq_zero.mp h6
  · exact absurd h6 (mul_ne_zero hx hi)

theorem spRoot_conj (v : V₄ → F) (g : ↥(StatedSp 2 F)) {l : F}
    (hg : ((g : GL V₄ F) : Matrix V₄ V₄ F) *ᵥ v = l • v) (t : F) :
    g * spRoot v t * g⁻¹ = spRoot v (l ^ 2 * t) := by
  apply Subtype.ext
  change (g : GL V₄ F) * spTrans v t * (g : GL V₄ F)⁻¹ = spTrans v (l ^ 2 * t)
  rw [conj_spTrans g.2 v t, hg, spTrans_smul]

theorem spTransMat_map (σ : F →+* F) (a : V₄ → F) (c : F) :
    (spTransMat a c).map σ = spTransMat (σ ∘ a) (σ c) := by
  have hJ : (spGram 2 F).map σ = spGram 2 F := spGram_map σ
  have hmv : ∀ j, σ ((spGram 2 F *ᵥ a) j) = (spGram 2 F *ᵥ (σ ∘ a)) j := fun j => by
    have h := RingHom.map_mulVec σ (spGram 2 F) a j
    rwa [hJ] at h
  ext i j
  simp only [spTransMat, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
    vecMulVec_apply, smul_eq_mul, map_add, map_mul, hmv, Function.comp]
  by_cases hij : i = j <;> simp [hij]

theorem fieldSp_spRoot (σ : F ≃+* F) (v : V₄ → F) (t : F) :
    fieldSp 2 F σ (spRoot v t) = spRoot (fun i => σ (v i)) (σ t) := by
  apply Subtype.ext
  apply Units.ext
  exact spTransMat_map σ.toRingHom v t

end Sp4M

section Sp4Four

variable {F : Type} [Field F] [CharP F 2]

local notation "V₄" => Fin 2 ⊕ Fin 2

theorem sp_mat_pow_three {g : ↥(StatedSp 2 F)} (h : g ^ 3 = 1) :
    ((g : GL V₄ F) : Matrix V₄ V₄ F) ^ 3 = 1 := by
  have := congrArg (fun x : ↥(StatedSp 2 F) => ((x : GL V₄ F) : Matrix V₄ V₄ F)) h
  simpa using this

theorem sq_ne_one_of_cube {l : F} (hl3 : l ^ 3 = 1) (hl1 : l ≠ 1) : l ^ 2 ≠ 1 := by
  intro h
  apply hl1
  calc l = l * l ^ 2 := by rw [h, mul_one]
    _ = l ^ 3 := by ring
    _ = 1 := hl3

theorem sq_pow_three {l : F} (hl3 : l ^ 3 = 1) : (l ^ 2) ^ 3 = 1 := by
  calc (l ^ 2) ^ 3 = (l ^ 3) ^ 2 := by ring
    _ = 1 := by rw [hl3, one_pow]

theorem sp4_four_inner {ω : F} (hω : ω ^ 2 + ω + 1 = 0) (hω1 : ω ≠ 1)
    {g₁ g₂ : ↥(StatedSp 2 F)} (h1 : g₁ ^ 3 = 1) (h2 : g₂ ^ 3 = 1) (hc : g₁ * g₂ = g₂ * g₁)
    (h11 : g₁ ≠ 1) :
    ∃ W : Subgroup ↥(StatedSp 2 F), IsElemAbelian 2 W ∧ Nat.card W = 4 ∧
      (∀ w ∈ W, g₁ * w * g₁⁻¹ ∈ W) ∧ (∀ w ∈ W, g₂ * w * g₂⁻¹ ∈ W) ∧
      ∃ w ∈ W, g₁ * w * g₁⁻¹ ≠ w := by
  have hMN : ((g₁ : GL V₄ F) : Matrix V₄ V₄ F) * ((g₂ : GL V₄ F) : Matrix V₄ V₄ F) =
      ((g₂ : GL V₄ F) : Matrix V₄ V₄ F) * ((g₁ : GL V₄ F) : Matrix V₄ V₄ F) := by
    have := congrArg (fun x : ↥(StatedSp 2 F) => ((x : GL V₄ F) : Matrix V₄ V₄ F)) hc
    simpa using this
  have hM1 : ((g₁ : GL V₄ F) : Matrix V₄ V₄ F) ≠ 1 := fun h => h11 (Subtype.ext (Units.ext h))
  obtain ⟨v, l, m, hv, hMv, hNv, hl3, hm3, hl1⟩ := exists_joint_eigenvector hω hω1
    (sp_mat_pow_three h1) (sp_mat_pow_three h2) hMN hM1
  have hmul := spRoot_add v
  have hinj : ∀ s t, spRoot v s = spRoot v t → s = t := fun s t h => spRoot_inj hv h
  refine ⟨rootFourOf (spRoot v) ω, (rootFourOf_spec hmul hinj hω hω1).1,
    (rootFourOf_spec hmul hinj hω hω1).2,
    rootFourOf_normalized hmul hω (sq_pow_three hl3) (spRoot_conj v g₁ hMv),
    rootFourOf_normalized hmul hω (sq_pow_three hm3) (spRoot_conj v g₂ hNv),
    spRoot v 1, mem_rootFourOf_one ω,
    rootFourOf_moved hinj (sq_ne_one_of_cube hl3 hl1) (spRoot_conj v g₁ hMv)⟩

theorem sp4_four_fixed {σ : F ≃+* F} {ω : F} (hω : ω ^ 2 + ω + 1 = 0) (hω1 : ω ≠ 1)
    (hσω : σ ω = ω) {g : ↥(StatedSp 2 F)} (h3 : g ^ 3 = 1) (hg1 : g ≠ 1)
    (hfix : fieldSp 2 F σ g = g) :
    ∃ W : Subgroup ↥(StatedSp 2 F), IsElemAbelian 2 W ∧ Nat.card W = 4 ∧
      (∀ w ∈ W, fieldSp 2 F σ w = w) ∧ (∀ w ∈ W, g * w * g⁻¹ ∈ W) ∧
      ∃ w ∈ W, g * w * g⁻¹ ≠ w := by
  have hM := sp_mat_pow_three h3
  have hM1 : ((g : GL V₄ F) : Matrix V₄ V₄ F) ≠ 1 := fun h => hg1 (Subtype.ext (Units.ext h))
  have hMσ : ((g : GL V₄ F) : Matrix V₄ V₄ F).map σ = ((g : GL V₄ F) : Matrix V₄ V₄ F) := by
    have := congrArg (fun x : ↥(StatedSp 2 F) => ((x : GL V₄ F) : Matrix V₄ V₄ F)) hfix
    simpa [coe_fieldSp] using this
  obtain ⟨v, l, m, hv, hvσ, hMv, -, hl3, -, hl1⟩ := exists_joint_eigenvector_fixed hω hω1 hσω hM
    hM rfl hM1 hMσ hMσ
  have hmul := spRoot_add v
  have hinj : ∀ s t, spRoot v s = spRoot v t → s = t := fun s t h => spRoot_inj hv h
  have hfixroot : ∀ t, σ t = t → fieldSp 2 F σ (spRoot v t) = spRoot v t := by
    intro t ht
    rw [fieldSp_spRoot, ht]
    congr 1
    funext i
    exact hvσ i
  refine ⟨rootFourOf (spRoot v) ω, (rootFourOf_spec hmul hinj hω hω1).1,
    (rootFourOf_spec hmul hinj hω hω1).2, ?_,
    rootFourOf_normalized hmul hω (sq_pow_three hl3) (spRoot_conj v g hMv),
    spRoot v 1, mem_rootFourOf_one ω,
    rootFourOf_moved hinj (sq_ne_one_of_cube hl3 hl1) (spRoot_conj v g hMv)⟩
  let Fix : Subgroup ↥(StatedSp 2 F) :=
    MonoidHom.eqLocus (fieldSp 2 F σ).toMonoidHom (MonoidHom.id _)
  have hW : rootFourOf (spRoot v) ω ≤ Fix := by
    rw [rootFourOf, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact hfixroot 1 (map_one σ)
    · exact hfixroot ω hσω
  intro w hw
  exact hW hw

end Sp4Four

end CFSG.RankThree.PartTwo.Sec21.Hering214
