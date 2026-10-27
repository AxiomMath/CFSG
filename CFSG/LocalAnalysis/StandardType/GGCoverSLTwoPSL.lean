module

public import CFSG.LocalAnalysis.StandardType.GGCoverSLPSL
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

private lemma exists_conj_psl_two_of_pow_eq_one
    {d p k : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (hp : p.Prime) (hp2 : p ≠ 2) (hd : 3 ≤ d)
    {a : MulAut (projectiveSL d K)} (hk : a ^ p ^ k = 1) :
    ∃ ρ : projectiveSL d K, a = MulAut.conj ρ := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hcardK : Fintype.card K = 2 := by
    rw [← Nat.card_eq_fintype_card]; exact hK
  have hmem : ∀ x : K, x = 0 ∨ x = 1 := by
    intro x
    have hpair : ({0, 1} : Finset K) = Finset.univ :=
      Finset.eq_univ_of_card _ (by
        rw [Finset.card_insert_of_notMem (by simp [zero_ne_one]), Finset.card_singleton,
          hcardK])
    have hx : x ∈ ({0, 1} : Finset K) := by rw [hpair]; exact Finset.mem_univ x
    simpa using hx
  obtain ⟨-, hgen⟩ := LinearFlag.automorphism_generation (K := K) (n := d) hd
  obtain ⟨A, σ, ε, hε, hae⟩ := hgen a
  have hσ : σ = 1 := by
    ext x
    rcases hmem x with hx | hx <;> rw [hx] <;> simp
  have hfield : fieldAut d K σ = 1 := by
    rw [hσ]; exact map_one (fieldAut d K)
  have htrans := standard_automorphism_transport (K := K) (n := d)
  have hdualconj : ∀ A : GL (Fin d) K,
      dualAut d K * conjAut d K A * dualAut d K =
        conjAut d K (GeneralLinearGroup.inverseTranspose A) := htrans.2.2.2.2.1
  have hconjmul : ∀ A B : GL (Fin d) K,
      conjAut d K A * conjAut d K B = conjAut d K (A * B) := htrans.1
  have hε01 : ε = 0 ∨ ε = 1 := by omega
  have ha2 : a ^ 2 ∈ (conjAut d K).range := by
    rcases hε01 with rfl | rfl
    · have haA : a = conjAut d K A := by
        rw [hae, hfield, pow_zero, mul_one, mul_one]
      refine ⟨A ^ 2, ?_⟩
      rw [haA, ← map_pow]
    · have haA : a = conjAut d K A * dualAut d K := by
        rw [hae, hfield, pow_one, mul_one]
      refine ⟨A * GeneralLinearGroup.inverseTranspose A, ?_⟩
      have hsq : a ^ 2 =
          conjAut d K A * conjAut d K (GeneralLinearGroup.inverseTranspose A) := by
        rw [haA, pow_two]
        calc conjAut d K A * dualAut d K * (conjAut d K A * dualAut d K)
            = conjAut d K A * (dualAut d K * conjAut d K A * dualAut d K) := by group
          _ = conjAut d K A * conjAut d K (GeneralLinearGroup.inverseTranspose A) := by
                rw [hdualconj A]
      rw [hsq, ← hconjmul A (GeneralLinearGroup.inverseTranspose A)]
  have hnodd : Odd (p ^ k) := (hp.odd_of_ne_two hp2).pow
  obtain ⟨r, hr⟩ := hnodd
  have hm : 2 * (r + 1) = p ^ k + 1 := by omega
  have ha_eq : a = (a ^ 2) ^ (r + 1) := by
    have h1 : a ^ (p ^ k + 1) = a := by rw [pow_succ, hk, one_mul]
    have h2 : a ^ (p ^ k + 1) = (a ^ 2) ^ (r + 1) := by rw [← pow_mul, hm]
    exact h1.symm.trans h2
  obtain ⟨B0, hB0⟩ := ha2
  let B : GL (Fin d) K := B0 ^ (r + 1)
  have hB : conjAut d K B = a := by
    rw [map_pow, hB0]
    exact ha_eq.symm
  have hunits : ∀ u : Kˣ, u = 1 := by
    intro u
    rcases hmem (u : K) with h | h
    · exact absurd h (Units.ne_zero u)
    · exact Units.ext (by simpa using h)
  have hdetB : (B : Matrix (Fin d) (Fin d) K).det = 1 := by
    have h1 : Matrix.GeneralLinearGroup.det B = 1 := hunits _
    simpa using congrArg Units.val h1
  let g : SpecialLinearGroup (Fin d) K := ⟨(B : Matrix (Fin d) (Fin d) K), hdetB⟩
  have hBg : B = SpecialLinearGroup.toGL g := by
    refine Units.ext ?_
    rfl
  have hslc :
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d K
          (SpecialLinearGroup.toGL g) = MulAut.conj g := by
    apply MulEquiv.ext
    intro y
    apply SpecialLinearGroup.toGL_injective
    simp only [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation,
      MulAut.conj_apply, map_mul, map_inv]
  have hconj : conjAut d K (SpecialLinearGroup.toGL g) = MulAut.conj (proj d K g) := by
    ext x
    obtain ⟨y, rfl⟩ := proj_surjective d K x
    simp only [conjAut_proj, hslc, MulAut.conj_apply, map_mul, map_inv]
  exact ⟨proj d K g, by rw [← hB, hBg, hconj]⟩

theorem ggCoverPTableB_PSL_two
    {d p : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) (hp : p.Prime) (hp2 : p ≠ 2)
    (hd : 3 ≤ d) :
    GGCoverPTableB p (projectiveSL d K) (Set.range (conjAut d K)) := by
  intro M _ _ L' E θ hE hpos a ha
  obtain ⟨k, hk⟩ := ha
  obtain ⟨ρ, hρ⟩ := exists_conj_psl_two_of_pow_eq_one hK hp hp2 hd hk
  refine ⟨ρ, fun e => ?_⟩
  rw [hρ, inv_mul_cancel]
  exact Commute.one_left _

theorem largeEvenLabelAll_coverP_typeA_two
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (htag : lab.tag = .A) (hl : 3 ≤ lab.rank) (hn : lab.n = 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGCoverPTableB p R I := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hl hn ⊢
  subst htag
  subst hn
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, hfield, hfinite, hK, hQ'⟩ := hQ
  refine ⟨K, hfield, hfinite, hK, hQ', ?_⟩
  have hd : 3 ≤ l + 1 := by omega
  refine ggCoverPTableB_of_mulEquiv (R' := projectiveSL (l + 1) K)
    (I' := Set.range (conjAut (l + 1) K)) (TypeA.recipeEquiv (l + 1) K) ?_ ?_
  · intro φ hφ
    exact TypeA.congr_recipeEquiv_mem hφ
  · exact ggCoverPTableB_PSL_two (K := K) (by simpa using hK) hp hp2 hd

end CFSG.StandardType
