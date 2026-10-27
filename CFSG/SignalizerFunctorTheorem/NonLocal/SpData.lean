module

public import CFSG.RankThree.PartOne.KC.SymplecticSubfieldSemilinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.SignalizerFunctorTheorem.NonLocal.Engine

public section

open Matrix CFSG.RankThree.Classical CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.RankThree.PartOne.KCSpFull
  CFSG.RankThree.PartOne.KCSpComm
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (subfieldSpHom)

namespace CFSG.SignalizerFunctorTheorem.NonLocal

section Data

variable (r : ℕ) (K : Type) [Field K]

@[expose] noncomputable def spProjData :
    ProjData K (Fin r ⊕ Fin r) (StatedSp r K) (StatedProj (StatedSp r K)) where
  ρ := (StatedSp r K).subtype
  hρ := Subtype.val_injective
  π := proj r K
  hπ := proj_surjective
  hker := by
    intro h
    rw [← MonoidHom.mem_ker, ker_proj, Subgroup.mem_subgroupOf, StatedScalars,
      MonoidHom.mem_range]
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_⟩
      have := congrArg (fun g : GL (Fin r ⊕ Fin r) K =>
        (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) hc
      simpa using this.symm
    · rintro ⟨c, hc⟩
      exact ⟨c, Units.ext (by simpa using hc.symm)⟩

end Data

variable {r : ℕ} {K : Type} [Field K]

theorem spForm_single_inl (j : Fin r) (v : Fin r ⊕ Fin r → K) :
    spForm r K (Pi.single (Sum.inl j) 1) v = v (Sum.inr j) := by
  rw [spForm_apply]
  simp [dotProduct, Pi.single_apply, CFSG.ClassicalInvolution.Models.SymplecticPairs.gram,
    Matrix.fromBlocks_mulVec]

theorem spForm_single_inr (j : Fin r) (v : Fin r ⊕ Fin r → K) :
    spForm r K (Pi.single (Sum.inr j) 1) v = - v (Sum.inl j) := by
  rw [spForm_apply]
  simp [dotProduct, Pi.single_apply, CFSG.ClassicalInvolution.Models.SymplecticPairs.gram,
    Matrix.fromBlocks_mulVec, Matrix.neg_mulVec]

theorem exists_spForm_single (b : Fin r ⊕ Fin r) :
    ∃ ε : K, ε ≠ 0 ∧ ∀ v : Fin r ⊕ Fin r → K,
      spForm r K (Pi.single b 1) v = ε * v (Sum.swap b) := by
  rcases b with j | j
  · exact ⟨1, one_ne_zero, fun v => by rw [spForm_single_inl]; simp⟩
  · exact ⟨-1, neg_ne_zero.mpr one_ne_zero, fun v => by rw [spForm_single_inr]; simp⟩

theorem sp_irreducible (k : Subfield K) (W : Submodule K (Fin r ⊕ Fin r → K))
    (hW : ∀ g : StatedSp r k, ∀ v ∈ W,
      (((subfieldSpHom r k g : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  classical
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  have hT : ∀ u : Fin r ⊕ Fin r → K, (∀ a, u a ∈ k) → ∀ w ∈ W,
      spForm r K w u • u ∈ W := by
    intro u hu w hw
    let u₀ : Fin r ⊕ Fin r → k := fun a => ⟨u a, hu a⟩
    have h1 := hW (spTransvection u₀ 1) w hw
    rw [subfieldSpHom_spTransvection] at h1
    have h2 : w + (((1 : k) : K) * spForm r K w (fun a => (u₀ a : K))) •
        (fun a => (u₀ a : K)) ∈ W := by
      rw [← spEnd_spTransvection]
      exact h1
    have h3 := W.sub_mem h2 hw
    have h4 : w + (((1 : k) : K) * spForm r K w (fun a => (u₀ a : K))) •
        (fun a => (u₀ a : K)) - w = spForm r K w u • u := by
      have : (fun a => (u₀ a : K)) = u := rfl
      rw [this]
      simp
    rwa [h4] at h3
  have hsingle : ∀ c : Fin r ⊕ Fin r, ∀ a, (Pi.single c (1 : K) : Fin r ⊕ Fin r → K) a ∈ k := by
    intro c a
    by_cases h : a = c <;> simp [h]
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  obtain ⟨b, hb⟩ : ∃ b : Fin r ⊕ Fin r, spForm r K w (Pi.single b 1) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hw0
    refine spForm_nondegenerate.1 w (fun n => ?_)
    have hn : n = ∑ c, n c • (Pi.single c (1 : K) : Fin r ⊕ Fin r → K) := by
      ext x
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hn, map_sum]
    simp [hcon]
  have heb : (Pi.single b (1 : K) : Fin r ⊕ Fin r → K) ∈ W := by
    have h1 := hT (Pi.single b 1) (hsingle b) w hwW
    have h2 := W.smul_mem (spForm r K w (Pi.single b 1))⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hb, one_smul] at h2
  obtain ⟨ε, hε, hεb⟩ := exists_spForm_single (K := K) b
  have hb' : (Pi.single (Sum.swap b) (1 : K) : Fin r ⊕ Fin r → K) ∈ W := by
    have h1 := hT (Pi.single (Sum.swap b) 1) (hsingle _) _ heb
    rw [hεb] at h1
    simp only [Pi.single_eq_same, mul_one] at h1
    have h2 := W.smul_mem ε⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hε, one_smul] at h2
  have hall : ∀ c : Fin r ⊕ Fin r, (Pi.single c (1 : K) : Fin r ⊕ Fin r → K) ∈ W := by
    intro c
    by_cases hc : c = Sum.swap b
    · rw [hc]
      exact hb'
    · have hsum : (fun a => (Pi.single (Sum.swap b) (1 : K) + Pi.single c 1 : Fin r ⊕ Fin r → K) a)
          ∈ W := by
        have h1 := hT (Pi.single (Sum.swap b) 1 + Pi.single c 1)
          (fun a => k.add_mem (hsingle _ a) (hsingle _ a)) _ heb
        rw [hεb] at h1
        have : (Pi.single (Sum.swap b) (1 : K) + Pi.single c 1 : Fin r ⊕ Fin r → K)
            (Sum.swap b) = 1 := by simp [Ne.symm hc]
        rw [this, mul_one] at h1
        have h2 := W.smul_mem ε⁻¹ h1
        rw [smul_smul, inv_mul_cancel₀ hε, one_smul] at h2
        exact h2
      have h3 := W.sub_mem hsum hb'
      have : (fun a => (Pi.single (Sum.swap b) (1 : K) + Pi.single c 1 : Fin r ⊕ Fin r → K) a)
          - Pi.single (Sum.swap b) 1 = Pi.single c 1 := by
        ext a
        simp
      rwa [this] at h3
  rw [eq_top_iff]
  intro v _
  have hv : v = ∑ c, v c • (Pi.single c (1 : K) : Fin r ⊕ Fin r → K) := by
    ext x
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hv]
  exact W.sum_mem (fun c _ => W.smul_mem _ (hall c))

theorem sp_centralizer_eq_one [NeZero r] (k : Subfield K) (x : StatedProj (StatedSp r K))
    (hx : ∀ g : StatedSp r k, x * proj r K (subfieldSpHom r k g) =
      proj r K (subfieldSpHom r k g) * x) : x = 1 := by
  obtain ⟨gx, rfl⟩ := proj_surjective (r := r) (K := K) x
  let A : gsp r K := ⟨(gx : GL (Fin r ⊕ Fin r) K), statedSp_le_gsp gx.2⟩
  have h : ∀ g : StatedSp r k, (conjAut r K A * fieldAut r K 1) (proj r K (subfieldSpHom r k g)) =
      proj r K (subfieldSpHom r k g) := by
    intro g
    rw [map_one, mul_one, conjAut_proj]
    have h1 : conjSp r K A (subfieldSpHom r k g) = gx * subfieldSpHom r k g * gx⁻¹ :=
      Subtype.ext rfl
    rw [h1, map_mul, map_mul, map_inv]
    exact mul_inv_eq_iff_eq_mul.mpr (hx g)
  obtain ⟨⟨b, hb⟩, -⟩ := semilinear_pointwise_centralizer k A 1 h
  rw [← MonoidHom.mem_ker, ker_proj, Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range]
  exact ⟨b, hb.symm⟩

end CFSG.SignalizerFunctorTheorem.NonLocal
