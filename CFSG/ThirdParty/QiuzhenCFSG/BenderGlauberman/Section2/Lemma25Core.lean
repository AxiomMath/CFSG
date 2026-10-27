module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section2.Basic
-- `import all`: `kappa`'s body is not `@[expose]`d, so at the default
-- `.exported` import level of a `module` file it is loaded as an axiom
-- (bodies of non-exposed definitions are stripped); the `h2.2.1` case of
-- `lemma_2_2` needs the definitional body (`LambdaChar l.1 * κ1`), so this
-- module is additionally imported with its private information (bodies).
import all CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section2.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section2.Coherence

namespace CFSG
end CFSG
open CFSG

/-!
# Bender--Glauberman: Lemma 2.5 — proof core

The proof helpers for Lemma 2.5: the character-theoretic core
(`1̃ = 1_G + φ`, `φ(t) = 1`, `λ̃₃ = ±ψ`), the Lemma-2.2 sum evaluation
(`V_sum_formula`), and the key identity `V = |G:H|(1 + 1/φ(1) − 4/λ̃₃(1)) =
2k²` (`V_eq_2k_sq`, stated in a `[Finite G]` section so its elaboration at
the `lemma_2_2` application site uses the same `Fintype.ofFinite G`
instances as `lemma_2_2`'s statement).  The final arithmetic is isolated in
the statement module `BenderGlauberman.Section2.Lemma25`.
-/

noncomputable section

open scoped BigOperators
open scoped commutatorElement
open scoped Pointwise

namespace CFSG.BenderGlauberman

open GorensteinWalter
open Theory.Character

-- Local instances matching `Theory.Character`'s subgroup-sum convention; see
-- `BenderGlauberman/ClassFunction.lean`.
attribute [local instance] Fintype.ofFinite
attribute [local instance] Classical.propDecidable

universe u

section Section2

variable {G : Type u} [Group G] [Fintype G]
variable (c : Hyp11 G)

/-- The trivial character `1_{H0}` as an irreducible character of `H0`. -/
private def lambdaOneIrr (c : Hyp11 G) : Irr (↥c.H0) :=
  ⟨(1 : ClassFunction (↥c.H0)), (isLinearCharacter_of_hom (1 : ↥c.H0 →* ℂˣ)).1⟩

/-- The linear character `λ_l` of `H0` as an irreducible character. -/
private def lambdaIrr (c : Hyp11 G) (l : LambdaHom c.H0 c.U) : Irr (↥c.H0) :=
  ⟨LambdaChar l.1, (isLinearCharacter_of_hom l.1).1⟩

/-- `t ∈ H = C_G(t)`. -/
private lemma t_mem_H (c : Hyp11 G) : c.t ∈ c.H := S_le_H c (c.S0_le_S c.t_mem_S0)

/-- `t ∈ T = H0 \ U`. -/
private lemma t_mem_T (c : Hyp11 G) : c.t ∈ c.T :=
  ⟨S0_le_H0 c c.t_mem_S0, t_not_mem_U c⟩

/-- The constant-one class function is a character. -/
private lemma isCharacter_one (G : Type u) [Group G] :
    IsCharacter (1 : ClassFunction G) := by
  refine ⟨1, Representation.trivial ℂ G (Fin 1 → ℂ), ?_⟩
  ext g
  simp [Representation.character, LinearMap.trace_id, Representation.isTrivial_def]

/-- The constant-one class function is a generalized character. -/
private lemma isGeneralizedCharacter_one (G : Type u) [Group G] :
    IsGeneralizedCharacter (1 : ClassFunction G) := by
  refine ⟨1, 0, isCharacter_one G, isCharacter_zero, ?_⟩
  simp

/-- The constant-one class function is an irreducible character. -/
private lemma isIrreducibleCharacter_one (G : Type u) [Group G] [Fintype G] :
    IsIrreducibleCharacter (1 : ClassFunction G) := by
  refine isIrreducibleCharacter_of_norm_one_inv (isCharacter_one G) ?_
  unfold scalarProductInv
  simp [Finset.sum_const]

/-- `1_{H0}` is fixed by `s`. -/
private lemma one_fixed_by_s (c : Hyp11 G) (h12 : Hyp12 c) :
    conjChar c.H0 (s_normalizes_H0 c h12) (1 : ClassFunction (↥c.H0)) = 1 := by
  ext x
  simp [conjChar]

/-- `l^2 ≠ 1` implies `λ_l^s ≠ λ_l`. -/
private lemma lambda_not_fixed_of_sq_ne_one (c : Hyp11 G) (h12 : Hyp12 c)
    {l : LambdaHom c.H0 c.U} (hl : l ^ 2 ≠ 1) :
    conjChar c.H0 (s_normalizes_H0 c h12) (LambdaChar l.1) ≠ LambdaChar l.1 := by
  intro hfix
  have h := (lambda_fixed_by_s_iff c h12 l).1 hfix
  rcases h with h1 | h2
  · have hl' : l ^ 2 = 1 := by
      rw [h1]
      simp
    exact hl hl'
  · have hl' : l ^ 2 = 1 := by
      rw [h2]
      exact lambdaTwo_sq_eq_one c h12
    exact hl hl'

/-- `λ_l(t) = ±1` for every linear character `λ_l` of `H0`. -/
private lemma lambda_t_value_pm_one (c : Hyp11 G) (l : LambdaHom c.H0 c.U) :
    (l.1 (tH0 c) : ℂ) = 1 ∨ (l.1 (tH0 c) : ℂ) = -1 := by
  have hsq : (l.1 (tH0 c) : ℂ) ^ 2 = 1 := by
    have hmap := congrArg (fun u : ℂˣ => (u : ℂ)) (map_pow l.1 (tH0 c) 2)
    have hpow : ((l.1 (tH0 c)) ^ 2 : ℂ) = (l.1 (tH0 c) : ℂ) ^ 2 :=
      Units.val_pow_eq_pow_val (l.1 (tH0 c)) 2
    have h : (tH0 c) ^ 2 = 1 := t_H0_sq c
    calc
      (l.1 (tH0 c) : ℂ) ^ 2 = ((l.1 (tH0 c)) ^ 2 : ℂ) := hpow.symm
      _ = (l.1 ((tH0 c) ^ 2) : ℂ) := hmap.symm
      _ = 1 := by rw [h]; simp
  exact sq_eq_one_iff.mp hsq

/-- `λ_l = 1` iff `l = 1` (the map `l ↦ LambdaChar l` is injective). -/
private lemma LambdaChar_eq_one_iff (c : Hyp11 G) (_h12 : Hyp12 c) (l : LambdaHom c.H0 c.U) :
    LambdaChar l.1 = (1 : ClassFunction (↥c.H0)) ↔ l = 1 := by
  constructor
  · intro hl
    apply Subtype.ext
    apply MonoidHom.ext
    intro x
    apply Units.ext
    have hx := congrFun hl x
    change (l.1 x : ℂ) = (1 : ℂ) at hx
    simpa using hx
  · intro hl
    rw [hl]
    ext x
    simp [LambdaChar]

/-- `1_{H0}` lies in the `Λ`-orbit of `λ_l`. -/
private lemma lambdaOne_mem_orbit_lambda (c : Hyp11 G) (_h12 : Hyp12 c)
    (l : LambdaHom c.H0 c.U) :
    (lambdaOneIrr c).1 ∈ orbit c.H0 c.U (lambdaIrr c l).1 := by
  classical
  refine Finset.mem_image.mpr ⟨l⁻¹, Finset.mem_univ _, ?_⟩
  change LambdaChar (l⁻¹).1 * LambdaChar l.1 = (1 : ClassFunction (↥c.H0))
  have hmul : LambdaChar (l⁻¹).1 * LambdaChar l.1 = LambdaChar ((l⁻¹ * l).1) := by
    ext x
    simp [LambdaChar]
  rw [hmul]
  have hinv : (l⁻¹ * l).1 = (1 : ↥c.H0 →* ℂˣ) := by
    have h : l⁻¹ * l = (1 : LambdaHom c.H0 c.U) := inv_mul_cancel l
    rw [h]
    rfl
  rw [hinv]
  ext x
  simp [LambdaChar]

end Section2

section Section2Finite

variable {G : Type u} [Group G] [Finite G]
variable (c : Hyp11 G)

/-- `1_{H0}` lies in the `Λ`-orbit of `λ_l`, with the `Finite G` instance
matching `lemma_2_2` (whose `orbit` is elaborated from `[Finite G]`). -/
private lemma lambdaOne_mem_orbit_lambda_finite (c : Hyp11 G) (_h12 : Hyp12 c)
    (l : LambdaHom c.H0 c.U) :
    (lambdaOneIrr c).1 ∈ orbit c.H0 c.U (lambdaIrr c l).1 := by
  classical
  refine Finset.mem_image.mpr ⟨l⁻¹, Finset.mem_univ _, ?_⟩
  change LambdaChar (l⁻¹).1 * LambdaChar l.1 = (1 : ClassFunction (↥c.H0))
  have hmul : LambdaChar (l⁻¹).1 * LambdaChar l.1 = LambdaChar ((l⁻¹ * l).1) := by
    ext x
    simp [LambdaChar]
  rw [hmul]
  have hinv : (l⁻¹ * l).1 = (1 : ↥c.H0 →* ℂˣ) := by
    have h : l⁻¹ * l = (1 : LambdaHom c.H0 c.U) := inv_mul_cancel l
    rw [h]
    rfl
  rw [hinv]
  ext x
  simp [LambdaChar]

end Section2Finite

section Section2

variable {G : Type u} [Group G] [Fintype G]
variable (c : Hyp11 G)

/-- `|1̃_{H0}|² = 2`. -/
private lemma lambdaOne_norm_two (c : Hyp11 G) (h12 : Hyp12 c) :
    normSq G (tildeNu c h12 (lambdaOneIrr c)) = 2 := by
  rw [tildeNu_norm]
  have hfix : conjChar c.H0 (s_normalizes_H0 c h12) (lambdaOneIrr c).1 =
      (lambdaOneIrr c).1 := by
    simpa [lambdaOneIrr] using one_fixed_by_s c h12
  simp [hfix]

/-- `|λ̃_l|² = 1` when `l^2 ≠ 1`. -/
private lemma lambdaThree_norm_one (c : Hyp11 G) (h12 : Hyp12 c)
    {l : LambdaHom c.H0 c.U} (hl : l ^ 2 ≠ 1) :
    normSq G (tildeNu c h12 (lambdaIrr c l)) = 1 := by
  rw [tildeNu_norm]
  have hfix : ¬ (conjChar c.H0 (s_normalizes_H0 c h12) (lambdaIrr c l).1 =
      (lambdaIrr c l).1) := by
    simpa [lambdaIrr] using lambda_not_fixed_of_sq_ne_one c h12 hl
  simp [hfix]

/-- `λ₁^H(t) = 2` for the trivial character `λ₁ = 1_{H0}`. -/
private lemma induced_lambdaOne_value_t (c : Hyp11 G) (h12 : Hyp12 c) :
    inducedFromSub (h12.H0_normal_in_H).1 (lambdaOneIrr c).1 ⟨c.t, t_mem_H c⟩ = 2 := by
  have h := inducedFromSub_eq_add_conj_index_two c.H0 c.H (h12.H0_normal_in_H).1
    (H0_index c h12) (s := c.s) (s_mem_H c) (s_not_mem_H0' c h12)
    (lambdaOneIrr c).1 (irreducibleCharacter_isClassFunction (isLinearCharacter_of_hom
      (1 : ↥c.H0 →* ℂˣ)).1) (h := c.t) (S0_le_H0 c c.t_mem_S0) (by
        rw [s_conj_t c]
        exact S0_le_H0 c c.t_mem_S0)
  rw [h]
  have hs : (lambdaOneIrr c).1 ⟨c.s * c.t * c.s⁻¹, by
      rw [s_conj_t c]
      exact S0_le_H0 c c.t_mem_S0⟩ = 1 := by
    simp [lambdaOneIrr]
  have hself : (lambdaOneIrr c).1 ⟨c.t, S0_le_H0 c c.t_mem_S0⟩ = 1 := by
    simp [lambdaOneIrr]
  simp [hs, hself]
  norm_num

/-- `λ_l^H(t) = 2λ_l(t)` for a linear character `λ_l` of `H0`. -/
private lemma induced_lambda_value_t (c : Hyp11 G) (h12 : Hyp12 c)
    (l : LambdaHom c.H0 c.U) :
    inducedFromSub (h12.H0_normal_in_H).1 (lambdaIrr c l).1 ⟨c.t, t_mem_H c⟩ =
      2 * (l.1 (tH0 c) : ℂ) := by
  have h := inducedFromSub_eq_add_conj_index_two c.H0 c.H (h12.H0_normal_in_H).1
    (H0_index c h12) (s := c.s) (s_mem_H c) (s_not_mem_H0' c h12)
    (lambdaIrr c l).1 (irreducibleCharacter_isClassFunction (isLinearCharacter_of_hom l.1).1)
    (h := c.t) (S0_le_H0 c c.t_mem_S0) (by
      rw [s_conj_t c]
      exact S0_le_H0 c c.t_mem_S0)
  rw [h]
  have hs : (lambdaIrr c l).1 ⟨c.s * c.t * c.s⁻¹, by
      rw [s_conj_t c]
      exact S0_le_H0 c c.t_mem_S0⟩ = (l.1 (tH0 c) : ℂ) := by
    apply congrArg (fun z : ↥c.H0 => (lambdaIrr c l).1 z)
    apply Subtype.ext
    exact s_conj_t c
  have hself : (lambdaIrr c l).1 ⟨c.t, S0_le_H0 c c.t_mem_S0⟩ = (l.1 (tH0 c) : ℂ) := by
    rfl
  simp [hs, hself, tH0]
  ring

/-- `λ̃₁(t) = 2` (from Coherence 2.3(v) on `T` and the hypothesis
`λ̃₃(t) = 2λ₃(t)`). -/
private lemma lambdaOne_value_t (c : Hyp11 G) (h12 : Hyp12 c)
    {l : LambdaHom c.H0 c.U}
    (hlt : tildeNu c h12 (lambdaIrr c l) c.t = 2 * (l.1 (tH0 c) : ℂ)) :
    tildeNu c h12 (lambdaOneIrr c) c.t = 2 := by
  have hEq := lambdaOne_mem_orbit_lambda c h12 l
  have hT := tildeNu_on_T c h12 hEq c.t (t_mem_T c) (t_mem_H c)
  rw [induced_lambdaOne_value_t c h12, induced_lambda_value_t c h12 l, hlt] at hT
  linear_combination hT

/-- `|1|² = 1` for the constant-one class function. -/
private lemma normSq_one (G : Type u) [Group G] [Fintype G] :
    normSq G (1 : ClassFunction G) = 1 := by
  unfold normSq scalarProduct
  simp [Finset.sum_const]

/-- The value of an induced class function at `1` is the index times the
value at `1`: `δ^G(1) = |G : H|·δ(1)`. -/
private lemma inducedClassFunction_apply_one (H : Subgroup G)
    (φ : ClassFunction (↥H)) :
    inducedClassFunction H φ 1 = (Nat.card G : ℂ) * (Nat.card (↥H) : ℂ)⁻¹ * φ 1 := by
  classical
  unfold inducedClassFunction
  calc
    (Nat.card (↥H) : ℂ)⁻¹ * (∑ x : G, if hx : x⁻¹ * 1 * x ∈ H then φ ⟨x⁻¹ * 1 * x, hx⟩ else 0)
        = (Nat.card (↥H) : ℂ)⁻¹ * ((Nat.card G : ℂ) * φ (1 : ↥H)) := by
          congr 1
          calc
            (∑ x : G, if hx : x⁻¹ * 1 * x ∈ H then φ ⟨x⁻¹ * 1 * x, hx⟩ else 0)
                = ∑ x : G, φ (1 : ↥H) := by
                  refine Finset.sum_congr rfl ?_
                  intro x hx
                  have hxH : x⁻¹ * 1 * x ∈ H := by simp
                  simp
                  rfl
            _ = (Nat.card G : ℂ) * φ (1 : ↥H) := by
                  simp [Finset.sum_const, nsmul_eq_mul]
    _ = (Nat.card G : ℂ) * (Nat.card (↥H) : ℂ)⁻¹ * φ 1 := by
          ring

/-- `1̃_{H0}(1) = λ̃_l(1)` for equivalent `1_{H0}`, `λ_l` (the induced
difference has degree zero). -/
private lemma lambdaOne_apply_one_eq_lambdaThree (c : Hyp11 G) (h12 : Hyp12 c)
    {l : LambdaHom c.H0 c.U} :
    tildeNu c h12 (lambdaOneIrr c) 1 = tildeNu c h12 (lambdaIrr c l) 1 := by
  classical
  have hEq := lambdaOne_mem_orbit_lambda c h12 l
  have hind := tildeNu_ind c h12 hEq
  have hval : inducedClassFunction c.H0 ((lambdaOneIrr c).1 - (lambdaIrr c l).1) 1 = 0 := by
    rw [inducedClassFunction_apply_one]
    have hzero : ((lambdaOneIrr c).1 - (lambdaIrr c l).1) 1 = 0 := by
      simp [lambdaOneIrr, lambdaIrr, LambdaChar]
    rw [hzero]
    ring
  have h : tildeNu c h12 (lambdaOneIrr c) 1 - tildeNu c h12 (lambdaIrr c l) 1 = 0 := by
    simpa [hind] using hval
  linear_combination h

/-- `(1_G, λ̃_l)_G = 0` for `l^2 ≠ 1` (the norm-one signed decomposition of
`λ̃_l` and the value `λ̃_l(t) = ±2` exclude the trivial character). -/
private lemma tildeNu_three_pairing_one_zero (c : Hyp11 G) (h12 : Hyp12 c)
    {l : LambdaHom c.H0 c.U} (hl : l ^ 2 ≠ 1)
    (hlt : tildeNu c h12 (lambdaIrr c l) c.t = 2 * (l.1 (tH0 c) : ℂ)) :
    scalarProduct G (1 : ClassFunction G) (tildeNu c h12 (lambdaIrr c l)) = 0 := by
  classical
  let ψ3 : ClassFunction G := tildeNu c h12 (lambdaIrr c l)
  have hgen : IsGeneralizedCharacter ψ3 := tildeNu_isGeneralized c h12 (lambdaIrr c l)
  have hnorm1 : scalarProduct G ψ3 ψ3 = 1 := by
    simpa [ψ3, normSq] using lambdaThree_norm_one c h12 hl
  rcases norm_one_signed_irreducible hgen hnorm1 with ⟨ψ, hψ, hcase⟩
  have hψne : ψ ≠ (1 : ClassFunction G) := by
    intro hψ1
    have hval1 : ψ3 c.t = 1 ∨ ψ3 c.t = -1 := by
      rcases hcase with h | h
      · left
        rw [h, hψ1]
        norm_num
      · right
        rw [h, hψ1]
        norm_num
    have hval3 : ψ3 c.t = 2 ∨ ψ3 c.t = -2 := by
      rcases lambda_t_value_pm_one c l with h1 | h1
      · left
        simpa [ψ3, h1] using hlt
      · right
        simpa [ψ3, h1] using hlt
    rcases hval1 with h1 | h1
    · rcases hval3 with h2 | h2
      · rw [h1] at h2
        norm_num at h2
      · rw [h1] at h2
        norm_num at h2
    · rcases hval3 with h2 | h2
      · rw [h1] at h2
        norm_num at h2
      · rw [h1] at h2
        norm_num at h2
  have hpair : scalarProduct G (1 : ClassFunction G) ψ = 0 := by
    rw [scalarProduct_irr_ite (isIrreducibleCharacter_one G) hψ]
    rw [if_neg (Ne.symm hψne)]
  rcases hcase with h | h
  · simpa [ψ3, h] using hpair
  · simp [ψ3, h, scalarProduct_neg_right, hpair]

/-- `(1_G, 1̃_{H0})_G = 1` (Frobenius reciprocity on the difference
`1̃ − λ̃_l = (1 − λ_l)^G`). -/
private lemma tildeNu_one_pairing_one (c : Hyp11 G) (h12 : Hyp12 c)
    {l : LambdaHom c.H0 c.U} (hl : l ^ 2 ≠ 1)
    (hlt : tildeNu c h12 (lambdaIrr c l) c.t = 2 * (l.1 (tH0 c) : ℂ)) :
    scalarProduct G (1 : ClassFunction G) (tildeNu c h12 (lambdaOneIrr c)) = 1 := by
  classical
  let ν1 : Irr (↥c.H0) := lambdaOneIrr c
  let ν3 : Irr (↥c.H0) := lambdaIrr c l
  let S : ℂ := ∑ χ : Irr G, (χ.1 c.t ^ 2 / χ.1 1) *
    scalarProduct G χ.1 (tildeNu c h12 ν1 - tildeNu c h12 ν3)
  have hEq : ν1.1 ∈ orbit c.H0 c.U ν3.1 := by simpa [ν1, ν3] using lambdaOne_mem_orbit_lambda c h12 l
  have hgen1 : IsGeneralizedCharacter (1 : ClassFunction G) := isGeneralizedCharacter_one G
  have hχc : IsClassFunction (1 : ClassFunction G) :=
    isClassFunction_of_isGeneralizedCharacter hgen1
  have hres : scalarProduct (↥c.H0) (fun y : ↥c.H0 => (1 : ClassFunction G) (y : G))
      (ν1.1 - ν3.1) = 1 := by
    rw [scalarProduct_sub_right]
    have hself : scalarProduct (↥c.H0) (fun y : ↥c.H0 => (1 : ClassFunction G) (y : G)) ν1.1 = 1 := by
      change scalarProduct (↥c.H0) (1 : ClassFunction (↥c.H0)) ν1.1 = 1
      simp [ν1, lambdaOneIrr]
      rw [scalarProduct_irr_ite (isIrreducibleCharacter_one (↥c.H0))
        (isIrreducibleCharacter_one (↥c.H0))]
      simp
    have horth : scalarProduct (↥c.H0) (fun y : ↥c.H0 => (1 : ClassFunction G) (y : G)) ν3.1 = 0 := by
      change scalarProduct (↥c.H0) (1 : ClassFunction (↥c.H0)) ν3.1 = 0
      simp [ν3, lambdaIrr]
      change scalarProduct (↥c.H0) (1 : ClassFunction (↥c.H0))
        (fun x : ↥c.H0 => (l.1 x : ℂ)) = 0
      rw [scalarProduct_irr_ite (isIrreducibleCharacter_one (↥c.H0))
        (isLinearCharacter_of_hom l.1).1]
      have hne : (1 : ClassFunction (↥c.H0)) ≠ fun x : ↥c.H0 => (l.1 x : ℂ) := by
        intro h
        have hle : LambdaChar l.1 = (1 : ClassFunction (↥c.H0)) := by
          change (fun x : ↥c.H0 => (l.1 x : ℂ)) = (1 : ClassFunction (↥c.H0))
          exact h.symm
        have hl1 : l = 1 := (LambdaChar_eq_one_iff c h12 l).1 hle
        apply hl
        rw [hl1]
        simp
      rw [if_neg hne]
    rw [hself, horth]
    norm_num
  have hfrob : scalarProduct G (1 : ClassFunction G)
      (inducedClassFunction c.H0 (ν1.1 - ν3.1)) = 1 := by
    rw [← scalarProduct_restrict_induced c.H0 hχc (ν1.1 - ν3.1)]
    exact hres
  have hind := tildeNu_ind c h12 hEq
  have hdiff : scalarProduct G (1 : ClassFunction G) (tildeNu c h12 ν1) -
      scalarProduct G (1 : ClassFunction G) (tildeNu c h12 ν3) = 1 := by
    have hsp : scalarProduct G (1 : ClassFunction G)
        (tildeNu c h12 ν1 - tildeNu c h12 ν3) = 1 := by
      simpa [hind] using hfrob
    rw [scalarProduct_sub_right] at hsp
    exact hsp
  have hq : scalarProduct G (1 : ClassFunction G) (tildeNu c h12 ν3) = 0 := by
    simpa [ν3] using tildeNu_three_pairing_one_zero c h12 hl hlt
  have hp : scalarProduct G (1 : ClassFunction G) (tildeNu c h12 ν1) = 1 := by
    have h' : scalarProduct G (1 : ClassFunction G) (tildeNu c h12 ν1) - 0 = 1 := by
      simpa [hq] using hdiff
    simpa using h'
  simpa [ν1] using hp

/-- A signed irreducible has norm one. -/
private lemma signed_irr_norm_one {G : Type u} [Group G] [Fintype G]
    {φ : ClassFunction G} (hφ : IsIrreducibleCharacter φ ∨ IsIrreducibleCharacter (-φ)) :
    scalarProduct G φ φ = 1 := by
  rcases hφ with hφ | hφ
  · rw [scalarProduct_eq_characterProduct_of_char (isCharacter_of_isIrreducibleCharacter hφ)]
    exact irreducibleCharacter_self hφ
  · calc
      scalarProduct G φ φ = scalarProduct G (-(-φ)) (-(-φ)) := by rw [neg_neg]
      _ = scalarProduct G (-φ) (-φ) := by simp [scalarProduct_neg_left, scalarProduct_neg_right]
      _ = 1 := by
        rw [scalarProduct_eq_characterProduct_of_char (isCharacter_of_isIrreducibleCharacter hφ)]
        exact irreducibleCharacter_self hφ

/-- A signed irreducible takes a rational integer value at `1`. -/
private lemma signed_irr_apply_one_int {G : Type u} [Group G] [Fintype G]
    {φ : ClassFunction G} (hφ : IsIrreducibleCharacter φ ∨ IsIrreducibleCharacter (-φ)) :
    ∃ n : ℕ, φ 1 = (n : ℂ) ∨ φ 1 = -((n : ℂ)) := by
  rcases hφ with hφ | hφ
  · rcases hφ with ⟨n, ρ, hρ, hφeq⟩
    refine ⟨Module.finrank ℂ (Fin n → ℂ), ?_⟩
    left
    have hρ1 : ρ.character 1 = (Module.finrank ℂ (Fin n → ℂ) : ℂ) := by
      unfold Representation.character
      simp [map_one]
    simp [hφeq, hρ1]
  · rcases hφ with ⟨n, ρ, hρ, hφeq⟩
    refine ⟨Module.finrank ℂ (Fin n → ℂ), ?_⟩
    right
    have hρ1 : ρ.character 1 = (Module.finrank ℂ (Fin n → ℂ) : ℂ) := by
      unfold Representation.character
      simp [map_one]
    -- `-φ = ρ.character`, so `φ 1 = -ρ.character 1`
    have hφ1 : φ 1 = -ρ.character 1 := by
      have h := congrFun hφeq 1
      change -φ 1 = ρ.character 1 at h
      linear_combination -h
    rw [hφ1, hρ1]

/-- A norm-two signed pair with `(1, δ) = 1` has the form `δ = 1 + φ` for a
signed irreducible `φ ≠ 1`. -/
private lemma one_mem_signed_pair {G : Type u} [Group G] [Fintype G]
    {δ a b : ClassFunction G}
    (ha : IsIrreducibleCharacter a) (hb : IsIrreducibleCharacter b) (hab : a ≠ b)
    (hn : normSq G δ = 2)
    (hcase : δ = a - b ∨ δ = a + b ∨ δ = -a - b ∨ δ = -a + b)
    (hp : scalarProduct G (1 : ClassFunction G) δ = 1) :
    ∃ φ : ClassFunction G,
      (IsIrreducibleCharacter φ ∨ IsIrreducibleCharacter (-φ)) ∧ φ ≠ (1 : ClassFunction G) ∧
      δ = (1 : ClassFunction G) + φ := by
  classical
  let one : ClassFunction G := (1 : ClassFunction G)
  have hpa : scalarProduct G one a = if (1 : ClassFunction G) = a then 1 else 0 := by
    simpa [one] using (scalarProduct_irr_ite (isIrreducibleCharacter_one G) ha)
  have hpb : scalarProduct G one b = if (1 : ClassFunction G) = b then 1 else 0 := by
    simpa [one] using (scalarProduct_irr_ite (isIrreducibleCharacter_one G) hb)
  have hamem : scalarProduct G one a = 1 ∨ scalarProduct G one a = 0 := by
    have h : scalarProduct G one a = if a = (1 : ClassFunction G) then 1 else 0 := by
      simpa [one, eq_comm] using (scalarProduct_irr_ite (isIrreducibleCharacter_one G) ha)
    rw [h]
    by_cases ha1 : a = (1 : ClassFunction G)
    · left
      simp [ha1]
    · right
      simp [ha1]
  have hbmem : scalarProduct G one b = 1 ∨ scalarProduct G one b = 0 := by
    have h : scalarProduct G one b = if b = (1 : ClassFunction G) then 1 else 0 := by
      simpa [one, eq_comm] using (scalarProduct_irr_ite (isIrreducibleCharacter_one G) hb)
    rw [h]
    by_cases hb1 : b = (1 : ClassFunction G)
    · left
      simp [hb1]
    · right
      simp [hb1]
  have hp1 : scalarProduct G one δ = 1 := by simpa [one] using hp
  rcases hcase with hcase | hcase | hcase | hcase
  · -- δ = a - b
    by_cases ha1 : a = one <;> by_cases hb1 : b = one
    · exfalso
      exact hab (ha1.trans hb1.symm)
    · refine ⟨-b, Or.inr ?_, ?_, ?_⟩
      · simpa using hb
      · intro hφ1
        have hbneg : b = -one := by
          have h := congrArg (fun z : ClassFunction G => -z) hφ1
          simpa [one] using h
        have hδ2 : δ = (2 : ℂ) • one := by
          rw [hcase, ha1, hbneg]
          ext x
          simp [one]
          ring
        have hnorm' : normSq G δ = 4 := by
          rw [hδ2]
          unfold normSq
          rw [scalarProduct_smul_left, scalarProduct_smul_right]
          have hone : scalarProduct G (1 : ClassFunction G) (1 : ClassFunction G) = 1 := by
            unfold scalarProduct
            simp [Finset.sum_const]
          rw [hone]
          norm_num
        have h42 : (4 : ℂ) = 2 := by rw [← hnorm', hn]
        norm_num at h42
      · change δ = one + (-b)
        rw [hcase, ha1]
        ext x
        simp [one, sub_eq_add_neg]
    · exfalso
      have hp' : scalarProduct G one δ = -1 := by
        rw [hcase, scalarProduct_sub_right]
        rw [hpa, hpb]
        simp [ha1, hb1, one, eq_comm]
      rw [hp1] at hp'
      norm_num at hp'
    · exfalso
      have hp' : scalarProduct G one δ = 0 := by
        rw [hcase, scalarProduct_sub_right]
        rw [hpa, hpb]
        simp [ha1, hb1, one, eq_comm]
      rw [hp1] at hp'
      norm_num at hp'
  · -- δ = a + b
    by_cases ha1 : a = one <;> by_cases hb1 : b = one
    · exfalso
      exact hab (ha1.trans hb1.symm)
    · refine ⟨b, Or.inl hb, ?_, ?_⟩
      · intro h
        exact hb1 h
      · change δ = one + b
        rw [hcase, ha1]
    · refine ⟨a, Or.inl ha, ?_, ?_⟩
      · intro h
        exact ha1 h
      · change δ = one + a
        rw [hcase, hb1, add_comm]
    · exfalso
      have hp' : scalarProduct G one δ = 0 := by
        rw [hcase, scalarProduct_add_right]
        rw [hpa, hpb]
        simp [ha1, hb1, one, eq_comm]
      rw [hp1] at hp'
      norm_num at hp'
  · -- δ = -a - b
    exfalso
    have hp' : scalarProduct G one δ = -(scalarProduct G one a) - scalarProduct G one b := by
      rw [hcase]
      simp [scalarProduct_neg_right, scalarProduct_sub_right]
    rcases hamem with ha1 | ha0 <;> rcases hbmem with hb1 | hb0
    · have hbad : (1 : ℂ) = -2 := by
        calc
          (1 : ℂ) = scalarProduct G one δ := hp1.symm
          _ = -(scalarProduct G one a) - scalarProduct G one b := hp'
          _ = -1 - 1 := by rw [ha1, hb1]
          _ = -2 := by norm_num
      norm_num at hbad
    · have hbad : (1 : ℂ) = -1 := by
        calc
          (1 : ℂ) = scalarProduct G one δ := hp1.symm
          _ = -(scalarProduct G one a) - scalarProduct G one b := hp'
          _ = -1 - 0 := by rw [ha1, hb0]
          _ = -1 := by norm_num
      norm_num at hbad
    · have hbad : (1 : ℂ) = -1 := by
        calc
          (1 : ℂ) = scalarProduct G one δ := hp1.symm
          _ = -(scalarProduct G one a) - scalarProduct G one b := hp'
          _ = -0 - 1 := by rw [ha0, hb1]
          _ = -1 := by norm_num
      norm_num at hbad
    · have hbad : (1 : ℂ) = 0 := by
        calc
          (1 : ℂ) = scalarProduct G one δ := hp1.symm
          _ = -(scalarProduct G one a) - scalarProduct G one b := hp'
          _ = -0 - 0 := by rw [ha0, hb0]
          _ = 0 := by norm_num
      norm_num at hbad
  · -- δ = -a + b
    by_cases ha1 : a = one <;> by_cases hb1 : b = one
    · exfalso
      exact hab (ha1.trans hb1.symm)
    · exfalso
      have hp' : scalarProduct G one δ = -1 := by
        rw [hcase, scalarProduct_add_right, scalarProduct_neg_right]
        rw [hpa, hpb]
        simp [ha1, hb1, one, eq_comm]
      rw [hp1] at hp'
      norm_num at hp'
    · refine ⟨-a, Or.inr ?_, ?_, ?_⟩
      · simpa using ha
      · intro hφ1
        have haneg : a = -one := by
          have h := congrArg (fun z : ClassFunction G => -z) hφ1
          simpa [one] using h
        have hδ2 : δ = (2 : ℂ) • one := by
          rw [hcase, hb1, haneg]
          ext x
          simp [one]
          ring
        have hnorm' : normSq G δ = 4 := by
          rw [hδ2]
          unfold normSq
          rw [scalarProduct_smul_left, scalarProduct_smul_right]
          have hone : scalarProduct G (1 : ClassFunction G) (1 : ClassFunction G) = 1 := by
            unfold scalarProduct
            simp [Finset.sum_const]
          rw [hone]
          norm_num
        have h42 : (4 : ℂ) = 2 := by rw [← hnorm', hn]
        norm_num at h42
      · change δ = one + (-a)
        rw [hcase, hb1, add_comm]
    · exfalso
      have hp' : scalarProduct G one δ = 0 := by
        rw [hcase, scalarProduct_add_right, scalarProduct_neg_right]
        rw [hpa, hpb]
        simp [ha1, hb1, one, eq_comm]
      rw [hp1] at hp'
      norm_num at hp'

/-- `1̃_{H0} = 1_G + φ` for a signed irreducible `φ ≠ 1` (the Frobenius
reciprocity content of Lemma 2.5). -/
private lemma exists_lambdaOne_decomp (c : Hyp11 G) (h12 : Hyp12 c)
    {l : LambdaHom c.H0 c.U} (hl : l ^ 2 ≠ 1)
    (hlt : tildeNu c h12 (lambdaIrr c l) c.t = 2 * (l.1 (tH0 c) : ℂ)) :
    ∃ φ : ClassFunction G,
      (IsIrreducibleCharacter φ ∨ IsIrreducibleCharacter (-φ)) ∧ φ ≠ (1 : ClassFunction G) ∧
      tildeNu c h12 (lambdaOneIrr c) = (1 : ClassFunction G) + φ := by
  classical
  have hgen := tildeNu_isGeneralized c h12 (lambdaOneIrr c)
  have hnorm2 : normSq G (tildeNu c h12 (lambdaOneIrr c)) = 2 := lambdaOne_norm_two c h12
  rcases signed_pair_decomp hgen hnorm2 with ⟨a, b, ha, hb, hab, hcase⟩
  have hp := tildeNu_one_pairing_one c h12 hl hlt
  rcases one_mem_signed_pair ha hb hab hnorm2 hcase hp with ⟨φ, hφ, hφne, hδeq⟩
  exact ⟨φ, hφ, hφne, hδeq⟩

/-- The constituent `φ` of `1̃_{H0}` takes the value `1` at `t`. -/
private lemma phi_value_t (c : Hyp11 G) (h12 : Hyp12 c)
    {l : LambdaHom c.H0 c.U}
    (hlt : tildeNu c h12 (lambdaIrr c l) c.t = 2 * (l.1 (tH0 c) : ℂ))
    (φ : ClassFunction G)
    (hδeq : tildeNu c h12 (lambdaOneIrr c) = (1 : ClassFunction G) + φ) :
    φ c.t = 1 := by
  have h1 : tildeNu c h12 (lambdaOneIrr c) c.t = 2 := lambdaOne_value_t c h12 hlt
  have h2 : tildeNu c h12 (lambdaOneIrr c) c.t = 1 + φ c.t := by
    rw [hδeq]
    rfl
  rw [h2] at h1
  linear_combination h1

/-- `λ̃_l = ±ψ` for an irreducible `ψ` (norm one). -/
private lemma exists_lambdaThree_decomp (c : Hyp11 G) (h12 : Hyp12 c)
    {l : LambdaHom c.H0 c.U} (hl : l ^ 2 ≠ 1) :
    ∃ ψ : ClassFunction G, IsIrreducibleCharacter ψ ∧
      (tildeNu c h12 (lambdaIrr c l) = ψ ∨ tildeNu c h12 (lambdaIrr c l) = -ψ) := by
  classical
  have hgen := tildeNu_isGeneralized c h12 (lambdaIrr c l)
  have hnorm1 : scalarProduct G (tildeNu c h12 (lambdaIrr c l))
      (tildeNu c h12 (lambdaIrr c l)) = 1 := by
    simpa [normSq] using lambdaThree_norm_one c h12 hl
  exact norm_one_signed_irreducible hgen hnorm1

/-- A sum over `Irr(G)` collapses to the single index where the pairing is
supported. -/
private lemma sum_over_irr_single {G : Type u} [Group G] [Fintype G]
    (δ : ClassFunction G) (χ₁ : Irr G) (f : ClassFunction G → ℂ)
    (hδ : ∀ χ : Irr G, χ ≠ χ₁ → scalarProduct G χ.1 δ = 0) :
    (∑ χ : Irr G, f χ.1 * scalarProduct G χ.1 δ) = f χ₁.1 * scalarProduct G χ₁.1 δ := by
  classical
  refine Finset.sum_eq_single χ₁ ?_ ?_
  · intro b hb hbne
    rw [hδ b hbne]
    simp
  · intro h
    exact False.elim (h (Finset.mem_univ χ₁))

/-- `Σ_χ f(χ)·(χ,1_G) = f(1_G)`. -/
private lemma sum_one_pairing {G : Type u} [Group G] [Fintype G]
    (f : ClassFunction G → ℂ) :
    (∑ χ : Irr G, f χ.1 * scalarProduct G χ.1 (1 : ClassFunction G)) =
      f (1 : ClassFunction G) := by
  classical
  let χ₁ : Irr G := ⟨(1 : ClassFunction G), isIrreducibleCharacter_one G⟩
  have hδ : ∀ χ : Irr G, χ ≠ χ₁ → scalarProduct G χ.1 (1 : ClassFunction G) = 0 := by
    intro χ hχ
    rw [scalarProduct_irr_ite χ.2 (isIrreducibleCharacter_one G)]
    have hne : χ.1 ≠ (1 : ClassFunction G) := by
      intro h
      apply hχ
      apply Subtype.ext
      exact h
    rw [if_neg hne]
  rw [sum_over_irr_single (1 : ClassFunction G) χ₁ f hδ]
  simp [χ₁, signed_irr_norm_one (Or.inl (isIrreducibleCharacter_one G))]

/-- `Σ_χ f(χ)·(χ,φ) = f(φ)` when `φ` is irreducible. -/
private lemma sum_phi_pairing_irr {G : Type u} [Group G] [Fintype G]
    (f : ClassFunction G → ℂ) {φ : ClassFunction G} (hφ : IsIrreducibleCharacter φ) :
    (∑ χ : Irr G, f χ.1 * scalarProduct G χ.1 φ) = f φ := by
  classical
  let χ₁ : Irr G := ⟨φ, hφ⟩
  have hδ : ∀ χ : Irr G, χ ≠ χ₁ → scalarProduct G χ.1 φ = 0 := by
    intro χ hχ
    rw [scalarProduct_irr_ite χ.2 hφ]
    have hne : χ.1 ≠ φ := by
      intro h
      apply hχ
      apply Subtype.ext
      exact h
    rw [if_neg hne]
  rw [sum_over_irr_single φ χ₁ f hδ]
  simp [χ₁, signed_irr_norm_one (Or.inl hφ)]

/-- `Σ_χ f(χ)·(χ,φ) = -f(-φ)` when `-φ` is irreducible. -/
private lemma sum_phi_pairing_neg_irr {G : Type u} [Group G] [Fintype G]
    (f : ClassFunction G → ℂ) {φ : ClassFunction G} (hφ : IsIrreducibleCharacter (-φ)) :
    (∑ χ : Irr G, f χ.1 * scalarProduct G χ.1 φ) = - f (-φ) := by
  classical
  let χ₁ : Irr G := ⟨-φ, hφ⟩
  have hδ : ∀ χ : Irr G, χ ≠ χ₁ → scalarProduct G χ.1 φ = 0 := by
    intro χ hχ
    have hφneg : φ = -(-φ) := by rw [neg_neg]
    rw [hφneg, scalarProduct_neg_right]
    have hpair : scalarProduct G χ.1 (-φ) = 0 := by
      rw [scalarProduct_irr_ite χ.2 hφ]
      have hne : χ.1 ≠ -φ := by
        intro h
        apply hχ
        apply Subtype.ext
        exact h
      rw [if_neg hne]
    rw [hpair]
    simp
  rw [sum_over_irr_single φ χ₁ f hδ]
  have hpair : scalarProduct G (-φ) φ = -1 := by
    rw [scalarProduct_neg_left, signed_irr_norm_one (Or.inr hφ)]
  simp [χ₁, hpair]

/-- `Σ_χ f(χ)·(χ,ψ) = f(ψ)` when `ψ` is irreducible. -/
private lemma sum_psi_pairing_irr {G : Type u} [Group G] [Fintype G]
    (f : ClassFunction G → ℂ) {ψ : ClassFunction G} (hψ : IsIrreducibleCharacter ψ) :
    (∑ χ : Irr G, f χ.1 * scalarProduct G χ.1 ψ) = f ψ := by
  classical
  let χ₁ : Irr G := ⟨ψ, hψ⟩
  have hδ : ∀ χ : Irr G, χ ≠ χ₁ → scalarProduct G χ.1 ψ = 0 := by
    intro χ hχ
    rw [scalarProduct_irr_ite χ.2 hψ]
    have hne : χ.1 ≠ ψ := by
      intro h
      apply hχ
      apply Subtype.ext
      exact h
    rw [if_neg hne]
  rw [sum_over_irr_single ψ χ₁ f hδ]
  simp [χ₁, signed_irr_norm_one (Or.inl hψ)]

/-- `λ̃_l(t)² = 4` (from `λ̃_l(t) = 2λ_l(t)` and `λ_l(t) = ±1`). -/
private lemma lambdaThree_value_sq_four (c : Hyp11 G) (h12 : Hyp12 c)
    {l : LambdaHom c.H0 c.U}
    (hlt : tildeNu c h12 (lambdaIrr c l) c.t = 2 * (l.1 (tH0 c) : ℂ)) :
    (tildeNu c h12 (lambdaIrr c l) c.t) ^ 2 = 4 := by
  have hz : (l.1 (tH0 c) : ℂ) = 1 ∨ (l.1 (tH0 c) : ℂ) = -1 := lambda_t_value_pm_one c l
  rcases hz with hz | hz
  · rw [hlt, hz]
    norm_num
  · rw [hlt, hz]
    norm_num

/-- The Lemma-2.2 sum for `(λ₁−λ₃)` evaluates to
`1 + 1/φ(1) − 4/λ̃₃(1)` (with `1̃ = 1_G + φ`). -/
private lemma V_sum_formula (c : Hyp11 G) (h12 : Hyp12 c)
    {l : LambdaHom c.H0 c.U} (hl : l ^ 2 ≠ 1)
    (hlt : tildeNu c h12 (lambdaIrr c l) c.t = 2 * (l.1 (tH0 c) : ℂ))
    (φ : ClassFunction G)
    (hφ : IsIrreducibleCharacter φ ∨ IsIrreducibleCharacter (-φ))
    (hδeq : tildeNu c h12 (lambdaOneIrr c) = (1 : ClassFunction G) + φ)
    (hφt : φ c.t = 1) :
    (∑ χ : Irr G, (χ.1 c.t ^ 2 / χ.1 1) *
      scalarProduct G χ.1 (tildeNu c h12 (lambdaOneIrr c) - tildeNu c h12 (lambdaIrr c l))) =
      1 + (φ 1)⁻¹ - 4 * (tildeNu c h12 (lambdaIrr c l) 1)⁻¹ := by
  classical
  let f : ClassFunction G → ℂ := fun ξ => ξ c.t ^ 2 / ξ 1
  rcases exists_lambdaThree_decomp c h12 hl with ⟨ψ, hψ, hψcase⟩
  have hψeq : tildeNu c h12 (lambdaIrr c l) = ψ ∨ tildeNu c h12 (lambdaIrr c l) = -ψ := hψcase
  have hsplit : (∑ χ : Irr G, f χ.1 *
        scalarProduct G χ.1 (tildeNu c h12 (lambdaOneIrr c) - tildeNu c h12 (lambdaIrr c l))) =
      (∑ χ : Irr G, f χ.1 * scalarProduct G χ.1 (1 : ClassFunction G)) +
        (∑ χ : Irr G, f χ.1 * scalarProduct G χ.1 φ) -
          (∑ χ : Irr G, f χ.1 * scalarProduct G χ.1 (tildeNu c h12 (lambdaIrr c l))) := by
    have hsp (χ : Irr G) :
        f χ.1 * scalarProduct G χ.1 (tildeNu c h12 (lambdaOneIrr c) - tildeNu c h12 (lambdaIrr c l)) =
          f χ.1 * scalarProduct G χ.1 (1 : ClassFunction G) +
            f χ.1 * scalarProduct G χ.1 φ -
              f χ.1 * scalarProduct G χ.1 (tildeNu c h12 (lambdaIrr c l)) := by
      rw [scalarProduct_sub_right, hδeq]
      rw [scalarProduct_add_right]
      ring
    calc
      (∑ χ : Irr G, f χ.1 *
          scalarProduct G χ.1 (tildeNu c h12 (lambdaOneIrr c) - tildeNu c h12 (lambdaIrr c l)))
          = ∑ χ : Irr G, (f χ.1 * scalarProduct G χ.1 (1 : ClassFunction G) +
              f χ.1 * scalarProduct G χ.1 φ -
              f χ.1 * scalarProduct G χ.1 (tildeNu c h12 (lambdaIrr c l))) := by
            refine Finset.sum_congr rfl ?_
            intro χ hχ
            exact hsp χ
      _ = (∑ χ : Irr G, f χ.1 * scalarProduct G χ.1 (1 : ClassFunction G)) +
            (∑ χ : Irr G, f χ.1 * scalarProduct G χ.1 φ) -
              (∑ χ : Irr G, f χ.1 * scalarProduct G χ.1 (tildeNu c h12 (lambdaIrr c l))) := by
            rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hsum1 : (∑ χ : Irr G, f χ.1 * scalarProduct G χ.1 (1 : ClassFunction G)) = 1 := by
    rw [sum_one_pairing f]
    simp [f]
  have hsum2 : (∑ χ : Irr G, f χ.1 * scalarProduct G χ.1 φ) = (φ 1)⁻¹ := by
    rcases hφ with hφirr | hφneg
    · rw [sum_phi_pairing_irr f hφirr]
      have ht : φ c.t ^ 2 = 1 := by rw [hφt]; norm_num
      simp [f, ht]
    · rw [sum_phi_pairing_neg_irr f hφneg]
      have ht : (-φ) c.t ^ 2 = 1 := by
        change (-(φ c.t)) ^ 2 = 1
        rw [hφt]
        norm_num
      have h1 : (-φ) 1 = -(φ 1) := by rfl
      simp [f, h1, hφt]
  have hsum3 : (∑ χ : Irr G, f χ.1 * scalarProduct G χ.1 (tildeNu c h12 (lambdaIrr c l))) =
      4 * (tildeNu c h12 (lambdaIrr c l) 1)⁻¹ := by
    rcases hψeq with hψeq | hψeq
    · -- λ̃3 = ψ
      rw [hψeq, sum_psi_pairing_irr f hψ]
      have ht : ψ c.t ^ 2 = 4 := by
        have h : ψ c.t = tildeNu c h12 (lambdaIrr c l) c.t := by rw [hψeq]
        rw [h]
        exact lambdaThree_value_sq_four c h12 hlt
      have h1 : ψ 1 = tildeNu c h12 (lambdaIrr c l) 1 := by rw [hψeq]
      simp [f, ht, h1, div_eq_mul_inv]
    · -- λ̃3 = -ψ
      rw [hψeq]
      rw [sum_phi_pairing_neg_irr f (hφ := (by simpa using hψ))]
      have ht : ψ c.t ^ 2 = 4 := by
        have h : -ψ c.t = tildeNu c h12 (lambdaIrr c l) c.t := by
          rw [hψeq]
          rfl
        rw [← neg_sq, h]
        exact lambdaThree_value_sq_four c h12 hlt
      have h1 : ψ 1 = -tildeNu c h12 (lambdaIrr c l) 1 := by
        rw [hψeq]
        change ψ 1 = -(-ψ 1)
        rw [neg_neg]
      simp [f, ht, h1, div_eq_mul_inv]
  rw [hsplit, hsum1, hsum2, hsum3]

end Section2

/-! ## Structural facts for the Lemma-2.5 arithmetic -/

section Section2Structure

variable {G : Type u} [Group G] [Finite G]
variable (c : Hyp11 G)

/-- `U ≤ H` (`U = O(H)`). -/
private lemma U_le_H (c : Hyp11 G) : c.U ≤ c.H := by
  intro x hx
  have huU : x ∈ (pPrimeCore 2 c.H).map c.H.subtype := by
    simpa [Hyp11.U, oddCoreOf] using hx
  exact SetLike.le_def.1 (Subgroup.map_subtype_le (H := c.H) (pPrimeCore 2 c.H)) huU

/-- `U ∩ S = 1`. -/
private lemma U_inter_S_eq_bot (c : Hyp11 G) {x : G} (hxU : x ∈ c.U)
    (hxS : x ∈ (c.S : Subgroup G)) : x = 1 := by
  classical
  have hcop : Nat.Coprime 2 (Nat.card ↥c.U) := by
    have h1 : Nat.card ↥c.U = Nat.card (pPrimeCore 2 c.H) := by
      dsimp [Hyp11.U]
      rw [oddCoreOf]
      exact Subgroup.card_map_of_injective (f := c.H.subtype)
        (K := pPrimeCore 2 c.H) (Subgroup.subtype_injective c.H)
    rw [h1]
    exact pPrimeCore_coprime_card (p := 2) (G := c.H)
  by_contra hx1
  have hordU : orderOf x ∣ Nat.card ↥c.U := by
    change orderOf (c.U.subtype (⟨x, hxU⟩ : ↥c.U)) ∣ Nat.card ↥c.U
    rw [orderOf_injective c.U.subtype (Subgroup.subtype_injective c.U) (⟨x, hxU⟩ : ↥c.U)]
    have hxU' : orderOf (⟨x, hxU⟩ : ↥c.U) ∣ Fintype.card ↥c.U :=
      orderOf_dvd_card (G := ↥c.U) (x := ⟨x, hxU⟩)
    rwa [← Nat.card_eq_fintype_card] at hxU'
  have hordS : orderOf x ∣ Nat.card (c.S : Subgroup G) := by
    change orderOf ((c.S : Subgroup G).subtype (⟨x, hxS⟩ : ↥(c.S : Subgroup G))) ∣
      Nat.card (c.S : Subgroup G)
    rw [orderOf_injective (c.S : Subgroup G).subtype
      (Subgroup.subtype_injective (c.S : Subgroup G)) (⟨x, hxS⟩ : ↥(c.S : Subgroup G))]
    have hxS' : orderOf (⟨x, hxS⟩ : ↥(c.S : Subgroup G)) ∣
        Fintype.card ↥(c.S : Subgroup G) :=
      orderOf_dvd_card (G := ↥(c.S : Subgroup G)) (x := ⟨x, hxS⟩)
    rwa [← Nat.card_eq_fintype_card] at hxS'
  have hpow : orderOf x ∣ 2 * 2 ^ c.m := by
    rw [← S_nat_card c]
    exact hordS
  have hpow' : orderOf x ∣ 2 ^ (c.m + 1) := by
    rw [pow_succ]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hpow
  have hcop' : Nat.Coprime (2 ^ (c.m + 1)) (Nat.card ↥c.U) := hcop.pow_left _
  have h1' : orderOf x = 1 := by
    have hdvd : orderOf x ∣ 1 := by
      rw [← hcop'.gcd_eq_one]
      exact Nat.dvd_gcd hpow' hordU
    exact Nat.dvd_one.mp hdvd
  exact hx1 (orderOf_eq_one_iff.mp h1')


/-- Every element of `S` normalizes `U = O(H)` (from `U ⊴ H` and `S ≤ H`). -/
private lemma S_le_normalizer_U (c : Hyp11 G) :
    (c.S : Subgroup G) ≤ Subgroup.normalizer (c.U : Set G) := by
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · intro hu
    exact U_normal_in_H c (S_le_H c hs) hu
  · intro hsu
    have hs' : s⁻¹ ∈ c.H := c.H.inv_mem (S_le_H c hs)
    have h1 := U_normal_in_H c hs' hsu
    have h2 : s⁻¹ * (s * u * s⁻¹) * (s⁻¹)⁻¹ = u := by group
    rwa [h2] at h1

/-- `H = U·S` (set product, from `H_eq_US` and `S ≤ N_G(U)`). -/
private lemma H_eq_U_mul_S (c : Hyp11 G) :
    (↑c.H : Set G) = (c.U : Set G) * (↑(c.S : Subgroup G) : Set G) := by
  rw [← c.H_eq_US]
  exact Subgroup.coe_mul_of_right_le_normalizer_left c.U (c.S : Subgroup G)
    (S_le_normalizer_U c)

/-- Uniqueness of the `U·K`-decomposition (`U ∩ K = 1`). -/
private lemma U_mul_K_decomp_unique (c : Hyp11 G) (K : Subgroup G)
    (hK : ∀ {x : G}, x ∈ c.U → x ∈ K → x = 1)
    {u₁ u₂ : ↥c.U} {s₁ s₂ : ↥K}
    (h : (u₁ : G) * (s₁ : G) = (u₂ : G) * (s₂ : G)) :
    u₁ = u₂ ∧ s₁ = s₂ := by
  have h1 : (u₂ : G)⁻¹ * (u₁ : G) * (s₁ : G) * (s₂ : G)⁻¹ = 1 := by
    calc
      (u₂ : G)⁻¹ * (u₁ : G) * (s₁ : G) * (s₂ : G)⁻¹ =
          (u₂ : G)⁻¹ * ((u₁ : G) * (s₁ : G)) * (s₂ : G)⁻¹ := by group
      _ = (u₂ : G)⁻¹ * ((u₂ : G) * (s₂ : G)) * (s₂ : G)⁻¹ := by rw [h]
      _ = 1 := by group
  have hU : (u₂ : G)⁻¹ * (u₁ : G) ∈ c.U := c.U.mul_mem (c.U.inv_mem u₂.2) u₁.2
  have hS : (s₂ : G) * (s₁ : G)⁻¹ ∈ K := K.mul_mem s₂.2 (K.inv_mem s₁.2)
  have hEq2 : (u₂ : G)⁻¹ * (u₁ : G) = (s₂ : G) * (s₁ : G)⁻¹ := by
    calc
      (u₂ : G)⁻¹ * (u₁ : G) =
          (u₂ : G)⁻¹ * (u₁ : G) * (s₁ : G) * (s₂ : G)⁻¹ * (s₂ : G) * (s₁ : G)⁻¹ := by group
      _ = 1 * (s₂ : G) * (s₁ : G)⁻¹ := by rw [h1]
      _ = (s₂ : G) * (s₁ : G)⁻¹ := by simp
  have hU2 : (u₂ : G)⁻¹ * (u₁ : G) ∈ K := by
    rw [hEq2]
    exact hS
  have h1' : (u₂ : G)⁻¹ * (u₁ : G) = 1 := hK hU hU2
  have hu12 : (u₁ : G) = (u₂ : G) := by
    calc
      (u₁ : G) = (u₂ : G) * ((u₂ : G)⁻¹ * (u₁ : G)) := by group
      _ = (u₂ : G) := by rw [h1']; simp
  constructor
  · apply Subtype.ext
    exact hu12
  · apply Subtype.ext
    calc
      (s₁ : G) = (u₁ : G)⁻¹ * ((u₁ : G) * (s₁ : G)) := by group
      _ = (u₂ : G)⁻¹ * ((u₂ : G) * (s₂ : G)) := by rw [h, hu12]
      _ = (s₂ : G) := by group

/-- The bijection `U × S ≃ H` (`H = U·S`, `U ∩ S = 1`). -/
private noncomputable def H_equiv_U_mul_S (c : Hyp11 G) :
    ↥c.U × ↥(c.S : Subgroup G) ≃ ↥c.H := by
  classical
  refine Equiv.ofBijective (fun p : ↥c.U × ↥(c.S : Subgroup G) =>
    ⟨(p.1 : G) * (p.2 : G), c.H.mul_mem (U_le_H c p.1.2) (S_le_H c p.2.2)⟩) ⟨?_, ?_⟩
  · intro p₁ p₂ h
    rcases U_mul_K_decomp_unique c (c.S : Subgroup G)
      (fun hxU hxK => U_inter_S_eq_bot c hxU hxK)
      (by exact congrArg (fun z : ↥c.H => (z : G)) h) with ⟨hu, hs⟩
    ext
    · exact congrArg (fun z : ↥c.U => (z : G)) hu
    · exact congrArg (fun z : ↥(c.S : Subgroup G) => (z : G)) hs
  · intro x
    have hx : (x : G) ∈ (c.U : Set G) * (↑(c.S : Subgroup G) : Set G) := by
      rw [← H_eq_U_mul_S c]
      exact x.2
    rcases hx with ⟨u, hu, s, hs, hxeq⟩
    refine ⟨(⟨u, hu⟩, ⟨s, hs⟩), ?_⟩
    apply Subtype.ext
    exact hxeq

/-- `|H| = |U|·|S|`. -/
private lemma H_card_eq (c : Hyp11 G) :
    Nat.card (↥c.H) = Nat.card ↥c.U * Nat.card (c.S : Subgroup G) := by
  simpa [Nat.card_prod] using (Nat.card_congr (H_equiv_U_mul_S c).symm)

/-- The bijection `U × S0 ≃ H0` (`H0 = U·S0`, `U ∩ S0 = 1`). -/
private noncomputable def H0_equiv_U_mul_S0 (c : Hyp11 G) (h12 : Hyp12 c) :
    ↥c.U × ↥(c.S0 : Subgroup G) ≃ ↥c.H0 := by
  classical
  refine Equiv.ofBijective (fun p : ↥c.U × ↥(c.S0 : Subgroup G) =>
    ⟨(p.1 : G) * (p.2 : G),
      c.H0.mul_mem ((h12.U_normal_in_H0).1 p.1.2) (S0_le_H0 c p.2.2)⟩) ⟨?_, ?_⟩
  · intro p₁ p₂ h
    rcases U_mul_K_decomp_unique c (c.S0 : Subgroup G)
      (fun hxU hxK => U_inter_S0_eq_bot c hxU hxK)
      (by exact congrArg (fun z : ↥c.H0 => (z : G)) h) with ⟨hu, hs⟩
    ext
    · exact congrArg (fun z : ↥c.U => (z : G)) hu
    · exact congrArg (fun z : ↥(c.S0 : Subgroup G) => (z : G)) hs
  · intro x
    rcases H0_eq_U_mul_S0 c h12 (x := x) with ⟨u, r, hxEq⟩
    refine ⟨(u, r), ?_⟩
    apply Subtype.ext
    exact hxEq.symm

/-- `|H0| = |U|·|S0|`. -/
private lemma H0_card_eq (c : Hyp11 G) (h12 : Hyp12 c) :
    Nat.card (↥c.H0) = Nat.card ↥c.U * Nat.card (c.S0 : Subgroup G) := by
  simpa [Nat.card_prod] using (Nat.card_congr (H0_equiv_U_mul_S0 c h12).symm)

/-- `|H0 : U| = |S0|` (the paper's `m = |S0|`). -/
private lemma U_index_eq_S0_card (c : Hyp11 G) (h12 : Hyp12 c) :
    (c.U.subgroupOf c.H0).index = Nat.card (c.S0 : Subgroup G) := by
  have h0 : (c.U.subgroupOf c.H0).index * Nat.card ↥(c.U.subgroupOf c.H0) =
      Nat.card (↥c.H0) :=
    Subgroup.index_mul_card (c.U.subgroupOf c.H0)
  have hUcard : Nat.card ↥(c.U.subgroupOf c.H0) = Nat.card ↥c.U := by
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := c.U) (K := c.H0)
      (h12.U_normal_in_H0).1).toEquiv
  have h1 : Nat.card (↥c.H0) = Nat.card ↥c.U * Nat.card (c.S0 : Subgroup G) :=
    H0_card_eq c h12
  have hEq : (c.U.subgroupOf c.H0).index * Nat.card ↥c.U =
      Nat.card (c.S0 : Subgroup G) * Nat.card ↥c.U := by
    calc
      (c.U.subgroupOf c.H0).index * Nat.card ↥c.U
          = (c.U.subgroupOf c.H0).index * Nat.card ↥(c.U.subgroupOf c.H0) := by
            rw [← hUcard]
      _ = Nat.card (↥c.H0) := h0
      _ = Nat.card ↥c.U * Nat.card (c.S0 : Subgroup G) := h1
      _ = Nat.card (c.S0 : Subgroup G) * Nat.card ↥c.U := by ring
  have hEq' : Nat.card ↥c.U * (c.U.subgroupOf c.H0).index =
      Nat.card ↥c.U * Nat.card (c.S0 : Subgroup G) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hEq
  exact mul_left_cancel₀ (Nat.card_pos.ne') hEq'

omit [Finite G] in
/-- Membership in the centralizer inside a subgroup. -/
private lemma mem_centralizerIn_iff' {X : Subgroup G} {s x : G} :
    x ∈ centralizerIn X s ↔ x ∈ X ∧ x * s = s * x := by
  unfold centralizerIn
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  simp [eq_comm]

/-- `C_H(t) = C_U(t)·C_S(t)` for `t ∈ S` (from `H = U·S` and `U ∩ S = 1`). -/
private lemma centralizer_H_eq_U_mul_S (c : Hyp11 G) {ti : G}
    (htiS : ti ∈ (c.S : Subgroup G)) :
    (centralizerIn c.H ti : Set G) =
      (centralizerIn c.U ti : Set G) * (centralizerIn (c.S : Subgroup G) ti : Set G) := by
  ext x
  constructor
  · intro hx
    have hxH : x ∈ c.H := ((mem_centralizerIn_iff' (X := c.H) (s := ti)).1 hx).1
    have hxU : (x : G) ∈ (c.U : Set G) * (↑(c.S : Subgroup G) : Set G) := by
      rw [← H_eq_U_mul_S c]
      exact hxH
    rcases hxU with ⟨u, huU, s', hsS, hxs⟩
    have hxcomm : (x : G) * ti = ti * (x : G) :=
      ((mem_centralizerIn_iff' (X := c.H) (s := ti)).1 hx).2
    have h1 : (u : G) * (s' * ti) = ti * (u : G) * s' := by
      calc
        (u : G) * (s' * ti) = ((u : G) * s') * ti := by group
        _ = (x : G) * ti := by rw [← hxs]
        _ = ti * (x : G) := hxcomm
        _ = ti * ((u : G) * s') := by rw [← hxs]
        _ = ti * (u : G) * s' := by group
    have h2 : (u : G) * (s' * ti * s'⁻¹) * (u : G)⁻¹ = ti := by
      calc
        (u : G) * (s' * ti * s'⁻¹) * (u : G)⁻¹ =
            ((u : G) * (s' * ti) * s'⁻¹) * (u : G)⁻¹ := by group
        _ = ((ti * (u : G) * s') * s'⁻¹) * (u : G)⁻¹ := by rw [h1]
        _ = ti := by group
    let a : G := s' * ti * s'⁻¹
    have haS : a ∈ (c.S : Subgroup G) := by
      dsimp [a]
      simpa [mul_assoc] using
        ((c.S : Subgroup G).mul_mem hsS
          ((c.S : Subgroup G).mul_mem htiS ((c.S : Subgroup G).inv_mem hsS)))
    have h3 : (u : G) * a * (u : G)⁻¹ * a⁻¹ ∈ c.U := by
      have h1' : a * (u : G)⁻¹ * a⁻¹ ∈ c.U :=
        U_normal_in_H c (S_le_H c haS) (c.U.inv_mem huU)
      have hEq : (u : G) * a * (u : G)⁻¹ * a⁻¹ =
          (u : G) * (a * (u : G)⁻¹ * a⁻¹) := by group
      rw [hEq]
      exact c.U.mul_mem huU h1'
    have hts : ti * a⁻¹ ∈ (c.S : Subgroup G) :=
      (c.S : Subgroup G).mul_mem htiS ((c.S : Subgroup G).inv_mem haS)
    have htsU : ti * a⁻¹ ∈ c.U := by
      rw [← h2]
      exact h3
    have hta : ti * a⁻¹ = 1 := U_inter_S_eq_bot c htsU hts
    have haeq : a = ti := by
      have ha1 : a⁻¹ = ti⁻¹ := by
        calc
          a⁻¹ = ti⁻¹ * (ti * a⁻¹) := by group
          _ = ti⁻¹ := by rw [hta]; simp
      calc
        a = (a⁻¹)⁻¹ := by simp
        _ = (ti⁻¹)⁻¹ := by rw [ha1]
        _ = ti := by simp
    have hs'comm : s' * ti = ti * s' := by
      have ha' : s' * ti * s'⁻¹ = ti := haeq
      calc
        s' * ti = s' * ti * s'⁻¹ * s' := by group
        _ = ti * s' := by rw [ha']
    have hucomm : (u : G) * ti = ti * (u : G) := by
      have h2' : (u : G) * ti * (u : G)⁻¹ = ti := by
        change (u : G) * a * (u : G)⁻¹ = ti at h2
        rwa [haeq] at h2
      calc
        (u : G) * ti = (u : G) * ti * (u : G)⁻¹ * (u : G) := by group
        _ = ti * (u : G) := by rw [h2']
    refine ⟨u, ?_, s', ?_, hxs⟩
    · exact (mem_centralizerIn_iff' (X := c.U) (s := ti)).mpr ⟨huU, hucomm⟩
    · exact (mem_centralizerIn_iff' (X := (c.S : Subgroup G)) (s := ti)).mpr
        ⟨hsS, hs'comm⟩
  · intro hx
    rcases hx with ⟨u, huC, s', hsC, hxs⟩
    have huU : (u : G) ∈ c.U := ((mem_centralizerIn_iff' (X := c.U) (s := ti)).1 huC).1
    have hsS : (s' : G) ∈ (c.S : Subgroup G) :=
      ((mem_centralizerIn_iff' (X := (c.S : Subgroup G)) (s := ti)).1 hsC).1
    have hxH : (x : G) ∈ c.H := by
      simpa [hxs] using c.H.mul_mem (U_le_H c huU) (S_le_H c hsS)
    have hxcomm : (x : G) * ti = ti * (x : G) := by
      have hucomm := ((mem_centralizerIn_iff' (X := c.U) (s := ti)).1 huC).2
      have hscomm := ((mem_centralizerIn_iff' (X := (c.S : Subgroup G)) (s := ti)).1 hsC).2
      have hmain : (u : G) * s' * ti = ti * ((u : G) * s') := by
        calc
          (u : G) * s' * ti = (u : G) * (s' * ti) := by group
          _ = (u : G) * (ti * s') := by rw [hscomm]
          _ = (u : G) * ti * s' := by group
          _ = ti * (u : G) * s' := by rw [hucomm]
          _ = ti * ((u : G) * s') := by group
      simpa [hxs] using hmain
    exact (mem_centralizerIn_iff' (X := c.H) (s := ti)).mpr ⟨hxH, hxcomm⟩

/-- The bijection `C_U(t) × C_S(t) ≃ C_H(t)`. -/
private noncomputable def centralizer_H_equiv (c : Hyp11 G) {ti : G}
    (htiS : ti ∈ (c.S : Subgroup G)) :
    ↥(centralizerIn c.U ti) × ↥(centralizerIn (c.S : Subgroup G) ti) ≃
      ↥(centralizerIn c.H ti) := by
  classical
  refine Equiv.ofBijective
    (fun p : ↥(centralizerIn c.U ti) × ↥(centralizerIn (c.S : Subgroup G) ti) =>
      ⟨(p.1 : G) * (p.2 : G), ?_⟩) ⟨?_, ?_⟩
  · have huU : (p.1 : G) ∈ c.U :=
      ((mem_centralizerIn_iff' (X := c.U) (s := ti)).1 p.1.2).1
    have hsS : (p.2 : G) ∈ (c.S : Subgroup G) :=
      ((mem_centralizerIn_iff' (X := (c.S : Subgroup G)) (s := ti)).1 p.2.2).1
    have hucomm := ((mem_centralizerIn_iff' (X := c.U) (s := ti)).1 p.1.2).2
    have hscomm := ((mem_centralizerIn_iff' (X := (c.S : Subgroup G)) (s := ti)).1 p.2.2).2
    refine (mem_centralizerIn_iff' (X := c.H) (s := ti)).mpr ⟨?_, ?_⟩
    · exact c.H.mul_mem (U_le_H c huU) (S_le_H c hsS)
    · calc
        (p.1 : G) * (p.2 : G) * ti = (p.1 : G) * ((p.2 : G) * ti) := by group
        _ = (p.1 : G) * (ti * (p.2 : G)) := by rw [hscomm]
        _ = (p.1 : G) * ti * (p.2 : G) := by group
        _ = ti * (p.1 : G) * (p.2 : G) := by rw [hucomm]
        _ = ti * ((p.1 : G) * (p.2 : G)) := by group
  · intro p₁ p₂ h
    have hu₁ : (p₁.1 : G) ∈ c.U :=
      ((mem_centralizerIn_iff' (X := c.U) (s := ti)).1 p₁.1.2).1
    have hu₂ : (p₂.1 : G) ∈ c.U :=
      ((mem_centralizerIn_iff' (X := c.U) (s := ti)).1 p₂.1.2).1
    have hs₁ : (p₁.2 : G) ∈ (c.S : Subgroup G) :=
      ((mem_centralizerIn_iff' (X := (c.S : Subgroup G)) (s := ti)).1 p₁.2.2).1
    have hs₂ : (p₂.2 : G) ∈ (c.S : Subgroup G) :=
      ((mem_centralizerIn_iff' (X := (c.S : Subgroup G)) (s := ti)).1 p₂.2.2).1
    rcases U_mul_K_decomp_unique c (c.S : Subgroup G)
      (fun hxU hxK => U_inter_S_eq_bot c hxU hxK)
      (u₁ := ⟨(p₁.1 : G), hu₁⟩) (u₂ := ⟨(p₂.1 : G), hu₂⟩)
      (s₁ := ⟨(p₁.2 : G), hs₁⟩) (s₂ := ⟨(p₂.2 : G), hs₂⟩) (by
        simpa using congrArg (fun z : ↥(centralizerIn c.H ti) => (z : G)) h) with ⟨hu, hs⟩
    ext
    · exact congrArg (fun z : ↥c.U => (z : G)) hu
    · exact congrArg (fun z : ↥(c.S : Subgroup G) => (z : G)) hs
  · intro x
    have hx : (x : G) ∈ (centralizerIn c.U ti : Set G) *
        (centralizerIn (c.S : Subgroup G) ti : Set G) := by
      rw [← centralizer_H_eq_U_mul_S c htiS]
      exact x.2
    rcases hx with ⟨u, huC, s, hsC, hxeq⟩
    refine ⟨(⟨u, huC⟩, ⟨s, hsC⟩), ?_⟩
    apply Subtype.ext
    exact hxeq

/-- `|C_H(t)| = |C_U(t)|·|C_S(t)|`. -/
private lemma centralizer_H_card (c : Hyp11 G) {ti : G}
    (htiS : ti ∈ (c.S : Subgroup G)) :
    Nat.card (↥(centralizerIn c.H ti)) =
      Nat.card (↥(centralizerIn c.U ti)) *
        Nat.card (↥(centralizerIn (c.S : Subgroup G) ti)) := by
  simpa [Nat.card_prod] using (Nat.card_congr (centralizer_H_equiv c htiS).symm)

/-- Any element of `S \ S0` inverts every element of `S0` (dihedral structure;
reduces to `s` via the index-two coset `r = w·s` with `w ∈ S0`). -/
private lemma reflection_inverts_S0 (c : Hyp11 G) {r : G} (hrS : r ∈ (c.S : Subgroup G))
    (hrS0 : r ∉ (c.S0 : Subgroup G)) {x : G} (hx : x ∈ (c.S0 : Subgroup G)) :
    r * x * r⁻¹ = x⁻¹ := by
  classical
  let K : Subgroup (↥(c.S : Subgroup G)) := (c.S0 : Subgroup G).subgroupOf (c.S : Subgroup G)
  have hwK : (⟨r * c.s, c.S.mul_mem hrS c.s_mem_S⟩ : ↥(c.S : Subgroup G)) ∈ K := by
    have hiff := Subgroup.mul_mem_iff_of_index_two (S0_index c) (G := ↥(c.S : Subgroup G))
      (H := K) (a := ⟨r, hrS⟩) (b := ⟨c.s, c.s_mem_S⟩)
    change (⟨r, hrS⟩ * ⟨c.s, c.s_mem_S⟩ : ↥(c.S : Subgroup G)) ∈ K
    rw [hiff]
    dsimp [K]
    simp [Subgroup.mem_subgroupOf, hrS0, c.s_not_mem_S0]
  have hw : r * c.s ∈ (c.S0 : Subgroup G) := Subgroup.mem_subgroupOf.mp hwK
  let w : ↥(c.S0 : Subgroup G) := ⟨r * c.s, hw⟩
  have hrs : r = (w : G) * c.s := by
    calc
      r = r * (c.s * c.s) := by
        have hs2 : c.s * c.s = 1 := by simpa [pow_two] using c.s_involution.2
        rw [hs2]
        simp
      _ = (r * c.s) * c.s := by group
      _ = (w : G) * c.s := rfl
  have hxs : (c.s * x * c.s⁻¹) = x⁻¹ := s_inverts_S0 c hx
  have hxw : (w : G) * x * (w : G)⁻¹ = x := by
    let : IsCyclic ↥(c.S0 : Subgroup G) := c.S0_cyclic
    let : CommGroup ↥(c.S0 : Subgroup G) := IsCyclic.commGroup
    have hcomm : w * ⟨x, hx⟩ = ⟨x, hx⟩ * w := mul_comm w ⟨x, hx⟩
    have hval : (w : G) * x = x * (w : G) :=
      congrArg (fun z : ↥(c.S0 : Subgroup G) => (z : G)) hcomm
    calc
      (w : G) * x * (w : G)⁻¹ = (x * (w : G)) * (w : G)⁻¹ := by rw [hval]
      _ = x := by group
  calc
    r * x * r⁻¹ = ((w : G) * c.s) * x * ((w : G) * c.s)⁻¹ := by rw [hrs]
    _ = (w : G) * (c.s * x * c.s⁻¹) * (w : G)⁻¹ := by group
    _ = (w : G) * x⁻¹ * (w : G)⁻¹ := by rw [hxs]
    _ = x⁻¹ := by
      let : IsCyclic ↥(c.S0 : Subgroup G) := c.S0_cyclic
      let : CommGroup ↥(c.S0 : Subgroup G) := IsCyclic.commGroup
      have hcomm : w * ⟨x⁻¹, (c.S0 : Subgroup G).inv_mem hx⟩ =
          ⟨x⁻¹, (c.S0 : Subgroup G).inv_mem hx⟩ * w := mul_comm w _
      have hval : (w : G) * x⁻¹ = x⁻¹ * (w : G) :=
        congrArg (fun z : ↥(c.S0 : Subgroup G) => (z : G)) hcomm
      rw [hval]
      group

/-- The centralizer of `ti ∈ S \ S0` in `S` has exactly four elements:
`{1, t, ti, t·ti}`. -/
private lemma C_S_card_eq_four (c : Hyp11 G) {ti : G}
    (htiS : ti ∈ (c.S : Subgroup G)) (htiS0 : ti ∉ (c.S0 : Subgroup G))
    (hti_ne : ti ≠ 1) (hti2 : ti * ti = 1) :
    Nat.card (↥(centralizerIn (c.S : Subgroup G) ti)) = 4 := by
  classical
  let Kf : Finset (↥(c.S : Subgroup G)) :=
    {1, ⟨c.t, c.S0_le_S c.t_mem_S0⟩, ⟨ti, htiS⟩,
      ⟨c.t * ti, c.S.mul_mem (c.S0_le_S c.t_mem_S0) htiS⟩}
  let K0 : Subgroup (↥(c.S : Subgroup G)) := (c.S0 : Subgroup G).subgroupOf (c.S : Subgroup G)
  have hmem : ∀ y : ↥(c.S : Subgroup G),
      (y : G) ∈ centralizerIn (c.S : Subgroup G) ti ↔
        y = 1 ∨ y = ⟨c.t, c.S0_le_S c.t_mem_S0⟩ ∨ y = ⟨ti, htiS⟩ ∨
          y = ⟨c.t * ti, c.S.mul_mem (c.S0_le_S c.t_mem_S0) htiS⟩ := by
    intro y
    constructor
    · intro hy
      have hxcomm : (y : G) * ti = ti * (y : G) :=
        ((mem_centralizerIn_iff' (X := (c.S : Subgroup G)) (s := ti)).1 hy).2
      by_cases hyS0 : (y : G) ∈ (c.S0 : Subgroup G)
      · have hyinv : (y : G) = (y : G)⁻¹ := by
          have hti_eq_inv : ti = ti⁻¹ := eq_inv_iff_mul_eq_one.mpr hti2
          have hri : ti * (y : G) * ti⁻¹ = (y : G)⁻¹ :=
            reflection_inverts_S0 c htiS htiS0 hyS0
          calc
            (y : G) = (y : G) * 1 := by simp
            _ = (y : G) * (ti * ti) := by rw [← hti2]
            _ = (y : G) * ti * ti := by group
            _ = ti * (y : G) * ti := by rw [hxcomm]
            _ = ti * (y : G) * ti⁻¹ := by rw [← hti_eq_inv]
            _ = (y : G)⁻¹ := hri
        have hy2 : (y : G) * (y : G) = 1 := by
          calc
            (y : G) * (y : G) = (y : G) * (y : G)⁻¹ := by rw [← hyinv]
            _ = 1 := by simp
        have hy2' : (⟨(y : G), hyS0⟩ : ↥(c.S0 : Subgroup G)) ^ 2 = 1 := by
          apply Subtype.ext
          simpa [Subgroup.coe_pow, pow_two] using hy2
        rcases (S0_sq_eq_one_iff c (x := ⟨(y : G), hyS0⟩)).1 hy2' with h1 | ht
        · left
          exact Subtype.ext_iff.2 (congrArg (fun z : ↥(c.S0 : Subgroup G) => (z : G)) h1)
        · right
          left
          exact Subtype.ext_iff.2 (congrArg (fun z : ↥(c.S0 : Subgroup G) => (z : G)) ht)
      · have hytiK0 : (⟨(y : G) * ti, c.S.mul_mem y.2 htiS⟩ : ↥(c.S : Subgroup G)) ∈ K0 := by
          have hiff := Subgroup.mul_mem_iff_of_index_two (S0_index c) (G := ↥(c.S : Subgroup G))
            (H := K0) (a := ⟨(y : G), y.2⟩) (b := ⟨ti, htiS⟩)
          change (⟨(y : G), y.2⟩ * ⟨ti, htiS⟩ : ↥(c.S : Subgroup G)) ∈ K0
          rw [hiff]
          dsimp [K0]
          simp [Subgroup.mem_subgroupOf, hyS0, htiS0]
        have hyti : (y : G) * ti ∈ (c.S0 : Subgroup G) := Subgroup.mem_subgroupOf.mp hytiK0
        let r : ↥(c.S0 : Subgroup G) := ⟨(y : G) * ti, hyti⟩
        have hyr : (y : G) = (r : G) * ti := by
          calc
            (y : G) = (y : G) * 1 := by simp
            _ = (y : G) * (ti * ti) := by rw [← hti2]
            _ = (y : G) * ti * ti := by group
            _ = (r : G) * ti := rfl
        have hr2 : (r : G) * (r : G) = 1 := by
          have hri : ti * (r : G) * ti⁻¹ = (r : G)⁻¹ :=
            reflection_inverts_S0 c htiS htiS0 r.2
          have hr_eq : (r : G) = (r : G)⁻¹ := by
            have hti_eq_inv : ti = ti⁻¹ := eq_inv_iff_mul_eq_one.mpr hti2
            calc
              (r : G) = (y : G) * ti := rfl
              _ = ti * (y : G) := hxcomm
              _ = ti * ((r : G) * ti) := by rw [hyr]
              _ = ti * (r : G) * ti := by group
              _ = ti * (r : G) * ti⁻¹ := by rw [← hti_eq_inv]
              _ = (r : G)⁻¹ := hri
          calc
            (r : G) * (r : G) = (r : G) * (r : G)⁻¹ := by rw [← hr_eq]
            _ = 1 := by simp
        have hr2' : (⟨(r : G), r.2⟩ : ↥(c.S0 : Subgroup G)) ^ 2 = 1 := by
          apply Subtype.ext
          simpa [Subgroup.coe_pow, pow_two] using hr2
        rcases (S0_sq_eq_one_iff c (x := ⟨(r : G), r.2⟩)).1 hr2' with hr1 | hrt
        · right
          right
          left
          exact Subtype.ext_iff.2 (by
          calc
            (y : G) = (r : G) * ti := hyr
            _ = 1 * ti := by
              rw [congrArg (fun z : ↥(c.S0 : Subgroup G) => (z : G)) hr1]
              simp
            _ = ti := by simp)
        · right
          right
          right
          exact Subtype.ext_iff.2 (by
          calc
            (y : G) = (r : G) * ti := hyr
            _ = c.t * ti := by
              rw [congrArg (fun z : ↥(c.S0 : Subgroup G) => (z : G)) hrt])
    · intro hy
      rcases hy with hy1 | hy2
      · subst hy1
        exact (mem_centralizerIn_iff' (X := (c.S : Subgroup G)) (s := ti)).mpr
          ⟨by simp, by simp⟩
      · rcases hy2 with hy2a | hy2b
        · subst hy2a
          exact (mem_centralizerIn_iff' (X := (c.S : Subgroup G)) (s := ti)).mpr ⟨
            c.S0_le_S c.t_mem_S0, by
              have h := S_conj_t c htiS
              calc
                c.t * ti = (ti * c.t * ti⁻¹) * ti := by rw [h]
                _ = ti * c.t := by group⟩
        · rcases hy2b with hy2c | hy2d
          · subst hy2c
            exact (mem_centralizerIn_iff' (X := (c.S : Subgroup G)) (s := ti)).mpr ⟨htiS, by
              simp [hti2]⟩
          · subst hy2d
            exact (mem_centralizerIn_iff' (X := (c.S : Subgroup G)) (s := ti)).mpr ⟨
              c.S.mul_mem (c.S0_le_S c.t_mem_S0) htiS, by
                calc
                  (c.t * ti) * ti = c.t * (ti * ti) := by group
                  _ = c.t := by rw [hti2]; simp
                  _ = ti * (c.t * ti) := by
                    have h := S_conj_t c htiS
                    calc
                      c.t = ti * c.t * ti⁻¹ := by rw [h]
                      _ = ti * c.t * ti := by
                        have hti_eq_inv : ti = ti⁻¹ := eq_inv_iff_mul_eq_one.mpr hti2
                        rw [← hti_eq_inv]
                      _ = ti * (c.t * ti) := by group⟩
  have hKf : Kf = Finset.univ.filter (fun y : ↥(c.S : Subgroup G) =>
      (y : G) ∈ centralizerIn (c.S : Subgroup G) ti) := by
    ext y
    simp [Kf, hmem y]
  have hKcard : Kf.card = 4 := by
    -- pairwise distinctness of the four elements
    have htS : (⟨c.t, c.S0_le_S c.t_mem_S0⟩ : ↥(c.S : Subgroup G)) ≠ 1 := by
      intro h
      exact c.t_involution.1 (by simpa using congrArg Subtype.val h)
    have htiS1 : (⟨ti, htiS⟩ : ↥(c.S : Subgroup G)) ≠ 1 := by
      intro h
      exact hti_ne (by simpa using congrArg Subtype.val h)
    have htt1 : (⟨c.t * ti, c.S.mul_mem (c.S0_le_S c.t_mem_S0) htiS⟩ : ↥(c.S : Subgroup G)) ≠ 1 := by
      intro h
      have hval : c.t * ti = 1 := by simpa using congrArg Subtype.val h
      have hti_t : ti = c.t := by
        calc
          ti = c.t⁻¹ * (c.t * ti) := by group
          _ = c.t⁻¹ := by rw [hval]; simp
          _ = c.t := by
            have ht2 : c.t * c.t = 1 := by simpa [pow_two] using c.t_involution.2
            exact (eq_inv_iff_mul_eq_one.mpr ht2).symm
      apply htiS0
      rw [hti_t]
      exact c.t_mem_S0
    have ht_ne_ti : (⟨c.t, c.S0_le_S c.t_mem_S0⟩ : ↥(c.S : Subgroup G)) ≠ ⟨ti, htiS⟩ := by
      intro h
      have hval : c.t = ti := by simpa using congrArg Subtype.val h
      exact htiS0 (by simpa [← hval] using c.t_mem_S0)
    have ht_ne_tti : (⟨c.t, c.S0_le_S c.t_mem_S0⟩ : ↥(c.S : Subgroup G)) ≠
        ⟨c.t * ti, c.S.mul_mem (c.S0_le_S c.t_mem_S0) htiS⟩ := by
      intro h
      have hval : c.t = c.t * ti := by simpa using congrArg Subtype.val h
      have hti1 : ti = 1 := by
        calc
          ti = c.t⁻¹ * (c.t * ti) := by group
          _ = c.t⁻¹ * c.t := by rw [← hval]
          _ = 1 := by simp
      exact hti_ne hti1
    have hti_ne_tti : (⟨ti, htiS⟩ : ↥(c.S : Subgroup G)) ≠
        ⟨c.t * ti, c.S.mul_mem (c.S0_le_S c.t_mem_S0) htiS⟩ := by
      intro h
      have hval : ti = c.t * ti := by simpa using congrArg Subtype.val h
      have ht1 : c.t = 1 := by
        have hval' : ti * ti = (c.t * ti) * ti := by rw [← hval]
        have hR : (c.t * ti) * ti = c.t := by
          calc
            (c.t * ti) * ti = c.t * (ti * ti) := by group
            _ = c.t := by rw [hti2]; simp
        calc
          c.t = (c.t * ti) * ti := hR.symm
          _ = ti * ti := by rw [← hval']
          _ = 1 := hti2
      exact c.t_involution.1 ht1
    change ({1, ⟨c.t, c.S0_le_S c.t_mem_S0⟩, ⟨ti, htiS⟩,
      ⟨c.t * ti, c.S.mul_mem (c.S0_le_S c.t_mem_S0) htiS⟩} :
      Finset (↥(c.S : Subgroup G))).card = 4
    have h1 : (1 : ↥(c.S : Subgroup G)) ∉
        ({⟨c.t, c.S0_le_S c.t_mem_S0⟩, ⟨ti, htiS⟩,
          ⟨c.t * ti, c.S.mul_mem (c.S0_le_S c.t_mem_S0) htiS⟩} :
      Finset (↥(c.S : Subgroup G))) := by
      simp [Ne.symm htS, Ne.symm htiS1, Ne.symm htt1]
    rw [Finset.card_insert_of_notMem h1]
    have h2 : (⟨c.t, c.S0_le_S c.t_mem_S0⟩ : ↥(c.S : Subgroup G)) ∉
        ({⟨ti, htiS⟩, ⟨c.t * ti, c.S.mul_mem (c.S0_le_S c.t_mem_S0) htiS⟩} :
          Finset (↥(c.S : Subgroup G))) := by
      simp [ht_ne_ti, ht_ne_tti]
    rw [Finset.card_insert_of_notMem h2]
    have h3 : (⟨ti, htiS⟩ : ↥(c.S : Subgroup G)) ∉
        ({⟨c.t * ti, c.S.mul_mem (c.S0_le_S c.t_mem_S0) htiS⟩} :
          Finset (↥(c.S : Subgroup G))) := by
      simp [hti_ne_tti]
    rw [Finset.card_insert_of_notMem h3]
    simp
  have hcardF : (Finset.univ.filter (fun y : ↥(c.S : Subgroup G) =>
      (y : G) ∈ centralizerIn (c.S : Subgroup G) ti)).card = 4 := by
    rw [← hKf]
    exact hKcard
  have hcardSub : Fintype.card {y : ↥(c.S : Subgroup G) //
      (y : G) ∈ centralizerIn (c.S : Subgroup G) ti} = 4 := by
    simpa [Fintype.card_subtype] using hcardF
  have heq : {y : ↥(c.S : Subgroup G) //
      (y : G) ∈ centralizerIn (c.S : Subgroup G) ti} ≃
      ↥(centralizerIn (c.S : Subgroup G) ti) := by
    refine (Equiv.subtypeSubtypeEquivSubtype
      (p := fun x : G => x ∈ (c.S : Subgroup G))
      (q := fun x : G => x ∈ centralizerIn (c.S : Subgroup G) ti) ?_)
    intro x hx
    exact ((mem_centralizerIn_iff' (X := (c.S : Subgroup G)) (s := ti)).1 hx).1
  rw [Nat.card_eq_fintype_card]
  exact (Fintype.card_congr heq).symm.trans hcardSub

/-- `2·k1 = |S0|·|U : B1|` (the paper's `k1 = |H : C_H(t1)| = ½|S0|·|U:B1|`). -/
private lemma k1_eq (c : Hyp11 G) :
    2 * c.k1 = Nat.card (c.S0 : Subgroup G) *
      ((centralizerIn c.U c.t1).subgroupOf c.U).index := by
  classical
  have hCH : Nat.card (↥(centralizerIn c.H c.t1)) =
      4 * Nat.card (↥(centralizerIn c.U c.t1)) := by
    rw [centralizer_H_card c c.t1_mem_S]
    rw [C_S_card_eq_four c c.t1_mem_S c.t1_not_mem_S0 c.t1_involution.1
      (by simpa [pow_two] using c.t1_involution.2)]
    ring
  have hCHcard : Nat.card ↥((centralizerIn c.H c.t1).subgroupOf c.H) =
      Nat.card ↥(centralizerIn c.H c.t1) := by
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (H := centralizerIn c.H c.t1) (K := c.H) inf_le_left).toEquiv
  have hk1m : c.k1 * Nat.card (↥(centralizerIn c.H c.t1)) = Nat.card (↥c.H) := by
    have h := Subgroup.index_mul_card (H := (centralizerIn c.H c.t1).subgroupOf c.H)
    rw [hCHcard] at h
    change ((centralizerIn c.H c.t1).subgroupOf c.H).index *
      Nat.card (↥(centralizerIn c.H c.t1)) = Nat.card (↥c.H)
    exact h
  have hB1card : Nat.card ↥((centralizerIn c.U c.t1).subgroupOf c.U) =
      Nat.card ↥(centralizerIn c.U c.t1) := by
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (H := centralizerIn c.U c.t1) (K := c.U) inf_le_left).toEquiv
  have hU : Nat.card ↥c.U =
      ((centralizerIn c.U c.t1).subgroupOf c.U).index *
        Nat.card (↥(centralizerIn c.U c.t1)) := by
    have h := Subgroup.index_mul_card (H := (centralizerIn c.U c.t1).subgroupOf c.U)
    rw [hB1card] at h
    simpa [mul_comm, mul_left_comm, mul_assoc] using h.symm
  have hMain : c.k1 * (4 * Nat.card (↥(centralizerIn c.U c.t1))) =
      Nat.card ↥c.U * (2 * Nat.card (c.S0 : Subgroup G)) := by
    calc
      c.k1 * (4 * Nat.card (↥(centralizerIn c.U c.t1)))
          = c.k1 * Nat.card (↥(centralizerIn c.H c.t1)) := by rw [hCH]
      _ = Nat.card (↥c.H) := hk1m
      _ = Nat.card ↥c.U * Nat.card (c.S : Subgroup G) := H_card_eq c
      _ = Nat.card ↥c.U * (2 * Nat.card (c.S0 : Subgroup G)) := by
        rw [S_nat_card c, S0_nat_card c]
  have hMain' : c.k1 * (4 * Nat.card (↥(centralizerIn c.U c.t1))) =
      ((centralizerIn c.U c.t1).subgroupOf c.U).index *
        Nat.card (↥(centralizerIn c.U c.t1)) *
        (2 * Nat.card (c.S0 : Subgroup G)) := by
    rwa [hU] at hMain
  have hcancel : c.k1 * 4 =
      ((centralizerIn c.U c.t1).subgroupOf c.U).index * 2 *
        Nat.card (c.S0 : Subgroup G) := by
    have hb : Nat.card (↥(centralizerIn c.U c.t1)) ≠ 0 := Nat.card_pos.ne'
    exact mul_left_cancel₀ hb (by
      calc
        Nat.card (↥(centralizerIn c.U c.t1)) * (c.k1 * 4)
            = c.k1 * (4 * Nat.card (↥(centralizerIn c.U c.t1))) := by ring
        _ = ((centralizerIn c.U c.t1).subgroupOf c.U).index *
              Nat.card (↥(centralizerIn c.U c.t1)) *
              (2 * Nat.card (c.S0 : Subgroup G)) := hMain'
        _ = Nat.card (↥(centralizerIn c.U c.t1)) *
              (((centralizerIn c.U c.t1).subgroupOf c.U).index * 2 *
                Nat.card (c.S0 : Subgroup G)) := by ring)
  have h2 : 2 * (2 * c.k1) =
      2 * (Nat.card (c.S0 : Subgroup G) *
        ((centralizerIn c.U c.t1).subgroupOf c.U).index) := by
    calc
      2 * (2 * c.k1) = c.k1 * 4 := by ring
      _ = ((centralizerIn c.U c.t1).subgroupOf c.U).index * 2 *
            Nat.card (c.S0 : Subgroup G) := hcancel
      _ = 2 * (Nat.card (c.S0 : Subgroup G) *
            ((centralizerIn c.U c.t1).subgroupOf c.U).index) := by ring
  exact mul_left_cancel₀ (by norm_num : (2 : ℕ) ≠ 0) h2

/-- `2·k2 = |S0|·|U : B2|`. -/
private lemma k2_eq (c : Hyp11 G) :
    2 * c.k2 = Nat.card (c.S0 : Subgroup G) *
      ((centralizerIn c.U c.t2).subgroupOf c.U).index := by
  classical
  have hCH : Nat.card (↥(centralizerIn c.H c.t2)) =
      4 * Nat.card (↥(centralizerIn c.U c.t2)) := by
    rw [centralizer_H_card c c.t2_mem_S]
    rw [C_S_card_eq_four c c.t2_mem_S c.t2_not_mem_S0 c.t2_involution.1
      (by simpa [pow_two] using c.t2_involution.2)]
    ring
  have hCHcard : Nat.card ↥((centralizerIn c.H c.t2).subgroupOf c.H) =
      Nat.card ↥(centralizerIn c.H c.t2) := by
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (H := centralizerIn c.H c.t2) (K := c.H) inf_le_left).toEquiv
  have hk2m : c.k2 * Nat.card (↥(centralizerIn c.H c.t2)) = Nat.card (↥c.H) := by
    have h := Subgroup.index_mul_card (H := (centralizerIn c.H c.t2).subgroupOf c.H)
    rw [hCHcard] at h
    change ((centralizerIn c.H c.t2).subgroupOf c.H).index *
      Nat.card (↥(centralizerIn c.H c.t2)) = Nat.card (↥c.H)
    exact h
  have hB2card : Nat.card ↥((centralizerIn c.U c.t2).subgroupOf c.U) =
      Nat.card ↥(centralizerIn c.U c.t2) := by
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (H := centralizerIn c.U c.t2) (K := c.U) inf_le_left).toEquiv
  have hU : Nat.card ↥c.U =
      ((centralizerIn c.U c.t2).subgroupOf c.U).index *
        Nat.card (↥(centralizerIn c.U c.t2)) := by
    have h := Subgroup.index_mul_card (H := (centralizerIn c.U c.t2).subgroupOf c.U)
    rw [hB2card] at h
    simpa [mul_comm, mul_left_comm, mul_assoc] using h.symm
  have hMain : c.k2 * (4 * Nat.card (↥(centralizerIn c.U c.t2))) =
      Nat.card ↥c.U * (2 * Nat.card (c.S0 : Subgroup G)) := by
    calc
      c.k2 * (4 * Nat.card (↥(centralizerIn c.U c.t2)))
          = c.k2 * Nat.card (↥(centralizerIn c.H c.t2)) := by rw [hCH]
      _ = Nat.card (↥c.H) := hk2m
      _ = Nat.card ↥c.U * Nat.card (c.S : Subgroup G) := H_card_eq c
      _ = Nat.card ↥c.U * (2 * Nat.card (c.S0 : Subgroup G)) := by
        rw [S_nat_card c, S0_nat_card c]
  have hMain' : c.k2 * (4 * Nat.card (↥(centralizerIn c.U c.t2))) =
      ((centralizerIn c.U c.t2).subgroupOf c.U).index *
        Nat.card (↥(centralizerIn c.U c.t2)) *
        (2 * Nat.card (c.S0 : Subgroup G)) := by
    rwa [hU] at hMain
  have hcancel : c.k2 * 4 =
      ((centralizerIn c.U c.t2).subgroupOf c.U).index * 2 *
        Nat.card (c.S0 : Subgroup G) := by
    have hb : Nat.card (↥(centralizerIn c.U c.t2)) ≠ 0 := Nat.card_pos.ne'
    exact mul_left_cancel₀ hb (by
      calc
        Nat.card (↥(centralizerIn c.U c.t2)) * (c.k2 * 4)
            = c.k2 * (4 * Nat.card (↥(centralizerIn c.U c.t2))) := by ring
        _ = ((centralizerIn c.U c.t2).subgroupOf c.U).index *
              Nat.card (↥(centralizerIn c.U c.t2)) *
              (2 * Nat.card (c.S0 : Subgroup G)) := hMain'
        _ = Nat.card (↥(centralizerIn c.U c.t2)) *
              (((centralizerIn c.U c.t2).subgroupOf c.U).index * 2 *
                Nat.card (c.S0 : Subgroup G)) := by ring)
  have h2 : 2 * (2 * c.k2) =
      2 * (Nat.card (c.S0 : Subgroup G) *
        ((centralizerIn c.U c.t2).subgroupOf c.U).index) := by
    calc
      2 * (2 * c.k2) = c.k2 * 4 := by ring
      _ = ((centralizerIn c.U c.t2).subgroupOf c.U).index * 2 *
            Nat.card (c.S0 : Subgroup G) := hcancel
      _ = 2 * (Nat.card (c.S0 : Subgroup G) *
            ((centralizerIn c.U c.t2).subgroupOf c.U).index) := by ring
  exact mul_left_cancel₀ (by norm_num : (2 : ℕ) ≠ 0) h2

/-- `|G : H|` is odd (`H = C_G(t)` contains the Sylow-2 subgroup `S`). -/
private lemma G_H_index_odd (c : Hyp11 G) : Odd c.H.index := by
  have hdiv : c.H.index ∣ (c.S : Subgroup G).index := Subgroup.index_dvd_of_le (S_le_H c)
  have hnot2 : ¬ (2 : ℕ) ∣ (c.S : Subgroup G).index := Sylow.not_dvd_index c.S
  exact (Nat.not_even_iff_odd).mp (by
    intro hEven
    exact hnot2 ((even_iff_two_dvd.mp hEven).trans hdiv))

/-- `2 | y` from `2 | A·y²` with `A` odd. -/
private lemma two_dvd_of_two_dvd_mul_sq {A : ℕ} {y : ℤ} (hAodd : Odd A)
    (h : (2 : ℤ) ∣ (A : ℤ) * y ^ 2) : (2 : ℤ) ∣ y := by
  have hEven : Even ((A : ℤ) * y ^ 2) := even_iff_two_dvd.mpr h
  rcases (Int.even_mul.mp hEven) with hA | hy
  · exact False.elim ((Nat.not_even_iff_odd.mpr hAodd)
      ((Int.even_coe_nat (n := A)).mp hA))
  · exact (even_iff_two_dvd (a := y)).mp (Int.even_pow.mp hy).1

/-- From `2^(2n) | A·y²` with `A` odd, get `2^n | y`. -/
private lemma two_pow_dvd_of_odd_mul_sq {A : ℕ} (hAodd : Odd A) (n : ℕ) {y : ℤ}
    (h : (2 : ℤ) ^ (2 * n) ∣ (A : ℤ) * y ^ 2) : (2 : ℤ) ^ n ∣ y := by
  classical
  induction n generalizing y with
  | zero =>
      exact ⟨y, by simp⟩
  | succ n ih =>
      have h2y : (2 : ℤ) ∣ y := by
        apply two_dvd_of_two_dvd_mul_sq hAodd
        exact dvd_trans (dvd_pow_self (2 : ℤ) (by omega : 2 * (n + 1) ≠ 0)) h
      rcases h2y with ⟨y1, hy1⟩
      have h' : (2 : ℤ) ^ (2 * n) ∣ (A : ℤ) * y1 ^ 2 := by
        rw [hy1] at h
        rcases h with ⟨t, ht⟩
        refine ⟨t, ?_⟩
        have ht' : (A : ℤ) * (2 * y1) ^ 2 = (2 : ℤ) ^ (2 * n + 2) * t := by
          simpa [Nat.mul_succ] using ht
        have hnorm : 4 * ((A : ℤ) * y1 ^ 2) = 4 * ((2 : ℤ) ^ (2 * n) * t) := by
          calc
            4 * ((A : ℤ) * y1 ^ 2) = (A : ℤ) * (2 * y1) ^ 2 := by ring
            _ = (2 : ℤ) ^ (2 * n + 2) * t := ht'
            _ = 4 * ((2 : ℤ) ^ (2 * n) * t) := by
              rw [pow_add]
              norm_num
              ring
        exact (mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0) hnorm)
      rcases ih h' with ⟨y2, hy2⟩
      refine ⟨y2, ?_⟩
      calc
        y = 2 * y1 := hy1
        _ = 2 * ((2 : ℤ) ^ n * y2) := by rw [hy2]
        _ = (2 : ℤ) ^ (n + 1) * y2 := by
          rw [pow_succ]
          ring

/-- `m = |H0 : U| = |S0|` divides `k = k1 + k2` (both `|U : B_i|` are odd). -/
private lemma m_dvd_k (c : Hyp11 G) (h12 : Hyp12 c) :
    (c.U.subgroupOf c.H0).index ∣ c.k := by
  classical
  have hk1 : 2 * c.k1 = Nat.card (c.S0 : Subgroup G) *
      ((centralizerIn c.U c.t1).subgroupOf c.U).index := k1_eq c
  have hk2 : 2 * c.k2 = Nat.card (c.S0 : Subgroup G) *
      ((centralizerIn c.U c.t2).subgroupOf c.U).index := k2_eq c
  have hUodd : Odd (Nat.card ↥c.U) := by
    have hcop : Nat.Coprime 2 (Nat.card ↥c.U) := by
      have h1 : Nat.card ↥c.U = Nat.card (pPrimeCore 2 c.H) := by
        dsimp [Hyp11.U]
        rw [oddCoreOf]
        exact Subgroup.card_map_of_injective (f := c.H.subtype)
          (K := pPrimeCore 2 c.H) (Subgroup.subtype_injective c.H)
      rw [h1]
      exact pPrimeCore_coprime_card (p := 2) (G := c.H)
    exact (Nat.coprime_two_left).mp hcop
  have hodd1 : Odd (((centralizerIn c.U c.t1).subgroupOf c.U).index) := by
    have hdiv : ((centralizerIn c.U c.t1).subgroupOf c.U).index ∣ Nat.card ↥c.U := by
      have h := Subgroup.index_mul_card (H := (centralizerIn c.U c.t1).subgroupOf c.U)
      exact ⟨Nat.card ↥((centralizerIn c.U c.t1).subgroupOf c.U), h.symm⟩
    exact (Nat.not_even_iff_odd).mp (by
      intro hEven
      have h2dvd : (2 : ℕ) ∣ Nat.card ↥c.U := (even_iff_two_dvd.mp hEven).trans hdiv
      have hEvenU : Even (Nat.card ↥c.U) := even_iff_two_dvd.mpr h2dvd
      exact (Nat.not_even_iff_odd.mpr hUodd) hEvenU)
  have hodd2 : Odd (((centralizerIn c.U c.t2).subgroupOf c.U).index) := by
    have hdiv : ((centralizerIn c.U c.t2).subgroupOf c.U).index ∣ Nat.card ↥c.U := by
      have h := Subgroup.index_mul_card (H := (centralizerIn c.U c.t2).subgroupOf c.U)
      exact ⟨Nat.card ↥((centralizerIn c.U c.t2).subgroupOf c.U), h.symm⟩
    exact (Nat.not_even_iff_odd).mp (by
      intro hEven
      have h2dvd : (2 : ℕ) ∣ Nat.card ↥c.U := (even_iff_two_dvd.mp hEven).trans hdiv
      have hEvenU : Even (Nat.card ↥c.U) := even_iff_two_dvd.mpr h2dvd
      exact (Nat.not_even_iff_odd.mpr hUodd) hEvenU)
  have hsum : 2 * c.k =
      Nat.card (c.S0 : Subgroup G) *
        (((centralizerIn c.U c.t1).subgroupOf c.U).index +
          ((centralizerIn c.U c.t2).subgroupOf c.U).index) := by
    rw [Hyp11.k, mul_add, hk1, hk2, ← mul_add]
  have heven : Even (((centralizerIn c.U c.t1).subgroupOf c.U).index +
      ((centralizerIn c.U c.t2).subgroupOf c.U).index) :=
    hodd1.add_odd hodd2
  rcases heven with ⟨q, hq⟩
  have hq' : ((centralizerIn c.U c.t1).subgroupOf c.U).index +
      ((centralizerIn c.U c.t2).subgroupOf c.U).index = 2 * q := by omega
  have hk : c.k = Nat.card (c.S0 : Subgroup G) * q := by
    have h2 : 2 * c.k = 2 * (Nat.card (c.S0 : Subgroup G) * q) := by
      calc
        2 * c.k =
            Nat.card (c.S0 : Subgroup G) *
              (((centralizerIn c.U c.t1).subgroupOf c.U).index +
                ((centralizerIn c.U c.t2).subgroupOf c.U).index) := hsum
        _ = Nat.card (c.S0 : Subgroup G) * (2 * q) := by rw [hq']
        _ = 2 * (Nat.card (c.S0 : Subgroup G) * q) := by ring
    exact mul_left_cancel₀ (by norm_num : (2 : ℕ) ≠ 0) h2
  have hUidx : (c.U.subgroupOf c.H0).index = Nat.card (c.S0 : Subgroup G) :=
    U_index_eq_S0_card c h12
  rw [hUidx]
  exact ⟨q, hk⟩

end Section2Structure

section Section2FiniteV

variable {G : Type u} [Group G] [Finite G]
variable (c : Hyp11 G)

/-- Lemma 2.2 case 2 applied to `μ = λ₁`, `ν = λ₃`, `κ₁ = 1`:
`|G:H|·(1 + 1/φ(1) − 4/λ̃₃(1)) = 2k²`.

Stated in a `[Finite G]` section (not `[Fintype G]`) because `lemma_2_2`
lives in a `[Finite G]` section: inside its type, `orbit`, `kappa` and
`lemma_2_2_V` are elaborated with the `Fintype.ofFinite G` instances
synthesized from `[Finite G]`.  Under the ambient `[Fintype G]` instance
`instFintype`, `Fintype.ofFinite (Finite.of_fintype instFintype)` is *not*
definitionally equal to `instFintype`, so an application from a
`[Fintype G]` section makes `isDefEq` repeatedly reduce the two instance
chains (`orbit` at the `lemma_2_2` application, `kappa` at `h2.2.1`, and
`∑ χ : Irr G` inside `lemma_2_2_V` vs the local `S`). -/
private lemma V_eq_2k_sq (c : Hyp11 G) (h12 : Hyp12 c)
    {l : LambdaHom c.H0 c.U} (hl : l ^ 2 ≠ 1)
    (hlt : tildeNu c h12 (lambdaIrr c l) c.t = 2 * (l.1 (tH0 c) : ℂ))
    (φ : ClassFunction G)
    (hφ : IsIrreducibleCharacter φ ∨ IsIrreducibleCharacter (-φ))
    (hδeq : tildeNu c h12 (lambdaOneIrr c) = (1 : ClassFunction G) + φ)
    (hφt : φ c.t = 1) :
    (c.H.index : ℂ) * (1 + (φ 1)⁻¹ - 4 * (tildeNu c h12 (lambdaIrr c l) 1)⁻¹) =
      (2 * c.k ^ 2 : ℂ) := by
  classical
  have hEq := lambdaOne_mem_orbit_lambda_finite c h12 l
  let ν1 : Irr (↥c.H0) := lambdaOneIrr c
  let ν3 : Irr (↥c.H0) := lambdaIrr c l
  let S : ℂ := ∑ χ : Irr G, (χ.1 c.t ^ 2 / χ.1 1) *
    scalarProduct G χ.1 (tildeNu c h12 ν1 - tildeNu c h12 ν3)
  have hκ1lin : IsLinearCharacter (1 : ClassFunction (↥c.H0)) :=
    isLinearCharacter_of_hom (1 : ↥c.H0 →* ℂˣ)
  have hκ1S0 : ∀ x : ↥c.H0, (x : G) ∈ (c.S0 : Subgroup G) →
      (1 : ClassFunction (↥c.H0)) x = 1 := by
    intro x hx
    rfl
  have hκ1comm : ∀ x : ↥c.H0, (x : G) ∈ ⁅(c.S : Subgroup G), c.U⁆ →
      (1 : ClassFunction (↥c.H0)) x = 1 := by
    intro x hx
    rfl
  have h2 := lemma_2_2 c h12 (μ := ν1) (ν := ν3) (hEq := hEq)
    (κ1 := (1 : ClassFunction (↥c.H0))) hκ1lin hκ1S0 hκ1comm
  have hV : lemma_2_2_V c ν1.1 ν3.1 = (2 * c.k ^ 2 : ℂ) := by
    have hμ1 : ν1.1 = (1 : ClassFunction (↥c.H0)) := by rfl
    have hl : ∃ l' : LambdaHom c.H0 c.U, l' ^ 2 ≠ 1 ∧ ν3.1 = kappa c
        (1 : ClassFunction (↥c.H0)) l' := by
      refine ⟨l, hl, ?_⟩
      simp [ν3, lambdaIrr]
      unfold kappa
      simp
    exact h2.2.1 hμ1 hl
  have hind := tildeNu_ind c h12 hEq
  have hS := V_sum_formula c h12 hl hlt φ hφ hδeq hφt
  have hS' : S = 1 + (φ 1)⁻¹ - 4 * (tildeNu c h12 ν3 1)⁻¹ := by
    dsimp [S, ν1, ν3]
    exact hS
  have hVexp : lemma_2_2_V c ν1.1 ν3.1 = (c.H.index : ℂ) * S := by
    unfold lemma_2_2_V
    congr 1
    refine Finset.sum_congr rfl ?_
    intro χ hχ
    dsimp [ν1, ν3]
    rw [hind]
  calc
    (c.H.index : ℂ) * (1 + (φ 1)⁻¹ - 4 * (tildeNu c h12 ν3 1)⁻¹)
        = (c.H.index : ℂ) * S := by rw [hS']
    _ = lemma_2_2_V c ν1.1 ν3.1 := hVexp.symm
    _ = (2 * c.k ^ 2 : ℂ) := hV

/-- Lemma 2.5 assembly: the character-theoretic core plus the structural facts
(`|G:H|` odd, `m | k`) and the `8 | x−1` arithmetic yield the full conclusion.
-/
public lemma lemma_2_5_assembly (c : Hyp11 G) (h12 : Hyp12 c)
    {l3 : LambdaHom c.H0 c.U} (hm : 4 ≤ (c.U.subgroupOf c.H0).index)
    (hl3 : l3 ^ 2 ≠ 1)
    (hl3t : tildeNu c h12 ⟨LambdaChar l3.1, (isLinearCharacter_of_hom l3.1).1⟩ c.t =
      2 * (l3.1 (tH0 c) : ℂ)) :
    ∃ φ : ClassFunction G,
      IsConstituentOf φ (tildeNu c h12 ⟨(1 : ClassFunction (↥c.H0)),
        (isLinearCharacter_of_hom (1 : ↥c.H0 →* ℂˣ)).1⟩) ∧
      φ ≠ 1 ∧ φ c.t = 1 ∧
      (2 / 3 : ℝ) ≤ 1 - 3 / (φ 1).re ∧
      1 - 3 / (φ 1).re < ↑((2 * (c.k : ℚ) ^ 2) / c.H.index : ℚ) ∧
      ↑((2 * (c.k : ℚ) ^ 2) / c.H.index : ℚ) < (2 : ℝ) := by
  classical
  rcases exists_lambdaOne_decomp c h12 hl3 hl3t with ⟨φ, hφsign, hφne1, hδeq⟩
  have hφt : φ c.t = 1 := phi_value_t c h12 hl3t φ hδeq
  rcases signed_irr_apply_one_int hφsign with ⟨n, hnφ⟩
  let x : ℤ := if h : φ 1 = (n : ℂ) then (n : ℤ) else - (n : ℤ)
  have hφx : φ 1 = (x : ℂ) := by
    by_cases h : φ 1 = (n : ℂ)
    · simp [x, h]
    · rcases hnφ with hnpos | hnneg
      · exact False.elim (h hnpos)
      · have hxdef : x = - (n : ℤ) := by simp [x, h]
        rw [hxdef, hnneg]
        norm_num
  have hlam3 : tildeNu c h12 (lambdaIrr c l3) 1 = (x : ℂ) + 1 := by
    have h1 : tildeNu c h12 (lambdaIrr c l3) 1 = tildeNu c h12 (lambdaOneIrr c) 1 :=
      (lambdaOne_apply_one_eq_lambdaThree c h12 (l := l3)).symm
    have h2 : tildeNu c h12 (lambdaOneIrr c) 1 = (φ 1) + 1 := by
      rw [hδeq]
      simp
      ring
    rw [h1, h2, hφx]
  have hx0 : x ≠ 0 := by
    intro hx0
    have hφ0 : φ 1 = 0 := by rw [hφx, hx0]; norm_num
    rcases hφsign with hφirr | hφneg
    · exact irreducible_char_one_ne_zero hφirr hφ0
    · have hneg0 : (-φ) 1 = 0 := by
        change -φ 1 = 0
        rw [hφ0]
        norm_num
      exact irreducible_char_one_ne_zero hφneg hneg0
  have hlam3ne0 : tildeNu c h12 (lambdaIrr c l3) 1 ≠ 0 := by
    rcases exists_lambdaThree_decomp c h12 hl3 with ⟨ψ, hψ, hψcase⟩
    rcases hψcase with hψeq | hψeq
    · rw [hψeq]
      exact irreducible_char_one_ne_zero hψ
    · rw [hψeq]
      intro hz
      have hψ0 : ψ 1 = 0 := by
        change -ψ 1 = 0 at hz
        exact neg_eq_zero.mp hz
      exact irreducible_char_one_ne_zero hψ hψ0
  have hx1 : x + 1 ≠ 0 := by
    intro hx1
    apply hlam3ne0
    rw [hlam3]
    exact_mod_cast hx1
  have hV := V_eq_2k_sq c h12 hl3 hl3t φ hφsign hδeq hφt
  have hVx : (c.H.index : ℂ) * (1 + (x : ℂ)⁻¹ - 4 * ((x : ℂ) + 1)⁻¹) =
      (2 * c.k ^ 2 : ℂ) := by
    simpa [hφx, hlam3] using hV
  have hx0c : (x : ℂ) ≠ 0 := by exact_mod_cast hx0
  have hx1c : (x : ℂ) + 1 ≠ 0 := by
    intro h
    apply hx1
    exact_mod_cast h
  have hVz : (c.H.index : ℤ) * (x - 1) ^ 2 =
      (2 * (c.k : ℤ) ^ 2) * x * (x + 1) := by
    have hfrac : 1 + (x : ℂ)⁻¹ - 4 * ((x : ℂ) + 1)⁻¹ =
        ((x : ℂ) - 1) ^ 2 / ((x : ℂ) * ((x : ℂ) + 1)) := by
      field_simp [hx0c, hx1c]
      ring
    have hVx' : (c.H.index : ℂ) *
        (((x : ℂ) - 1) ^ 2 / ((x : ℂ) * ((x : ℂ) + 1))) =
        (2 * (c.k : ℤ) ^ 2 : ℂ) := by
      rw [hfrac] at hVx
      exact hVx
    have hVx'' : (c.H.index : ℂ) * ((x : ℂ) - 1) ^ 2 =
        (2 * (c.k : ℤ) ^ 2 : ℂ) * (x : ℂ) * ((x : ℂ) + 1) := by
      field_simp [hx0c, hx1c] at hVx' ⊢
      exact hVx'
    exact_mod_cast hVx''
  -- `m | k` and `4 ≤ m` give `4 | k`
  have hfour : (4 : ℕ) ∣ c.k := by
    have hm_dvd : (c.U.subgroupOf c.H0).index ∣ c.k := m_dvd_k c h12
    have hUidx : (c.U.subgroupOf c.H0).index = Nat.card (c.S0 : Subgroup G) :=
      U_index_eq_S0_card c h12
    have hS0 : Nat.card (c.S0 : Subgroup G) = 2 ^ c.m := S0_nat_card c
    have h4 : 4 ≤ 2 ^ c.m := by
      rw [← hS0, ← hUidx]
      exact hm
    have hm2 : 2 ≤ c.m := by
      by_contra hnot
      have hle1 : c.m ≤ 1 := by omega
      have hpow : 2 ^ c.m ≤ 2 := by
        have h := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hle1
        simpa using h
      omega
    have h4m : (4 : ℕ) ∣ (c.U.subgroupOf c.H0).index := by
      rw [hUidx, hS0]
      refine ⟨2 ^ (c.m - 2), ?_⟩
      have hcm : c.m = 2 + (c.m - 2) := by omega
      rw [hcm, pow_add]
      norm_num
    exact dvd_trans h4m hm_dvd
  have hAodd : Odd c.H.index := G_H_index_odd c
  let y : ℤ := x - 1
  have hEqY : (c.H.index : ℤ) * y ^ 2 =
      (2 * (c.k : ℤ) ^ 2) * x * (x + 1) := by
    simpa [y] using hVz
  have h64 : (64 : ℤ) ∣ (c.H.index : ℤ) * y ^ 2 := by
    have h4k : (4 : ℤ) ∣ (c.k : ℤ) := by exact_mod_cast hfour
    rcases h4k with ⟨q, hq⟩
    have h16 : (16 : ℤ) ∣ (c.k : ℤ) ^ 2 := by
      refine ⟨q ^ 2, ?_⟩
      rw [hq]
      ring
    have h2x : (2 : ℤ) ∣ x * (x + 1) := Int.two_dvd_mul_add_one x
    rcases h16 with ⟨q16, hq16⟩
    rcases h2x with ⟨qx, hqx⟩
    rw [hEqY]
    refine ⟨q16 * qx, ?_⟩
    calc
      (2 * (c.k : ℤ) ^ 2) * x * (x + 1) = 2 * ((c.k : ℤ) ^ 2 * (x * (x + 1))) := by ring
      _ = 2 * ((16 * q16) * (2 * qx)) := by rw [hq16, hqx]
      _ = 64 * (q16 * qx) := by ring
  have h8y : (8 : ℤ) ∣ y := by
    have h := two_pow_dvd_of_odd_mul_sq hAodd 3 (by
      simpa [show (2 : ℤ) ^ 6 = 64 by norm_num] using h64)
    simpa using h
  have hyne : y ≠ 0 := by
    intro hy0
    have hx1' : x = 1 := by
      have hxy : x - 1 = 0 := by simpa [y] using hy0
      omega
    have hbad : (0 : ℤ) = 4 * (c.k : ℤ) ^ 2 := by
      have h := hVz
      rw [hx1'] at h
      have h' : (0 : ℤ) = (2 * (c.k : ℤ) ^ 2) * 1 * (1 + 1) := by
        calc
          (0 : ℤ) = (c.H.index : ℤ) * (1 - 1) ^ 2 := by ring
          _ = (2 * (c.k : ℤ) ^ 2) * 1 * (1 + 1) := by simpa using h
      norm_num at h'
      rw [h']
      ring
    have hk0 : (c.k : ℤ) = 0 := by
      have hsq : (c.k : ℤ) ^ 2 = 0 := by
        exact (mul_eq_zero.mp (by simpa using hbad.symm)).resolve_left
          (by norm_num : (4 : ℤ) ≠ 0)
      exact sq_eq_zero_iff.mp hsq
    have hk1pos : 0 < c.k1 := by
      exact Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite
        (H := (centralizerIn c.H c.t1).subgroupOf c.H))
    have hk2pos : 0 < c.k2 := by
      exact Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite
        (H := (centralizerIn c.H c.t2).subgroupOf c.H))
    have hkpos : 0 < c.k := by
      rw [Hyp11.k]
      omega
    have hk0N : c.k = 0 := by exact_mod_cast hk0
    omega
  have hcases : 9 ≤ x ∨ x ≤ -7 := by
    rcases h8y with ⟨q, hq⟩
    have hqne : q ≠ 0 := by
      intro hq0
      apply hyne
      rw [hq, hq0]
      ring
    rcases (lt_or_gt_of_ne hqne) with hqneg | hqpos
    · right
      have hqle : q ≤ -1 := by omega
      have hy8 : y ≤ -8 := by
        rw [hq]
        nlinarith
      omega
    · left
      have hqge : 1 ≤ q := by omega
      have hy8 : 8 ≤ y := by
        rw [hq]
        nlinarith
      omega
  -- the three ℝ inequalities
  have hre : (φ 1).re = (x : ℝ) := by
    rw [hφx]
    norm_num
  have hAposQ : (0 : ℚ) < (c.H.index : ℚ) := by
    exact_mod_cast (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := c.H)))
  have hxq0 : (x : ℚ) ≠ 0 := by exact_mod_cast hx0
  have hxq1 : (x : ℚ) + 1 ≠ 0 := by
    intro h
    apply hx1
    exact_mod_cast h
  have hEqQ : (c.H.index : ℚ) * ((x : ℚ) - 1) ^ 2 =
      (2 * (c.k : ℚ) ^ 2) * (x : ℚ) * ((x : ℚ) + 1) := by
    exact_mod_cast hVz
  have hdiv : (2 * (c.k : ℚ) ^ 2) / (c.H.index : ℚ) =
      ((x : ℚ) - 1) ^ 2 / ((x : ℚ) * ((x : ℚ) + 1)) := by
    field_simp [hAposQ.ne', hxq0, hxq1]
    ring_nf at hEqQ ⊢
    exact hEqQ.symm
  have hle1 : (2 / 3 : ℝ) ≤ 1 - 3 / (φ 1).re := by
    rw [hre]
    let z : ℝ := (x : ℝ)
    rcases hcases with hx9 | hx7
    · have hx9r : (9 : ℝ) ≤ z := by
        simpa [z] using (show (9 : ℝ) ≤ (x : ℝ) by exact_mod_cast hx9)
      have hzpos : (0 : ℝ) < z := by linarith
      have hz0 : z ≠ 0 := by linarith
      change (2 / 3 : ℝ) ≤ 1 - 3 / z
      have hz3 : 1 - 3 / z = (z - 3) / z := by
        field_simp [hz0]
      rw [hz3]
      rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 3) hzpos]
      nlinarith [hx9r]
    · have hx7r : z ≤ -7 := by
        simpa [z] using (show (x : ℝ) ≤ -7 by exact_mod_cast hx7)
      have hzneg : z < 0 := by linarith
      have hz0 : z ≠ 0 := by linarith
      change (2 / 3 : ℝ) ≤ 1 - 3 / z
      have hdiv : (3 / z : ℝ) ≤ 0 := div_nonpos_of_nonneg_of_nonpos (by norm_num) (le_of_lt hzneg)
      have hge1 : (1 : ℝ) ≤ 1 - 3 / z := by linarith
      linarith
  have hle2 : 1 - 3 / (φ 1).re < ↑((2 * (c.k : ℚ) ^ 2) / c.H.index : ℚ) := by
    rw [hre, hdiv]
    norm_num
    let z : ℝ := (x : ℝ)
    rcases hcases with hx9 | hx7
    · have hx9r : (9 : ℝ) ≤ z := by
        simpa [z] using (show (9 : ℝ) ≤ (x : ℝ) by exact_mod_cast hx9)
      have hzpos : (0 : ℝ) < z := by linarith
      have hz0 : z ≠ 0 := by linarith
      have hzprod : (0 : ℝ) < z * (z + 1) := by nlinarith
      change 1 - 3 / z < (z - 1) ^ 2 / (z * (z + 1))
      have hz3 : 1 - 3 / z = (z - 3) / z := by
        field_simp [hz0]
      rw [hz3]
      rw [div_lt_div_iff₀ hzpos hzprod]
      nlinarith [hx9r]
    · have hx7r : z ≤ -7 := by
        simpa [z] using (show (x : ℝ) ≤ -7 by exact_mod_cast hx7)
      have hzneg : z < 0 := by linarith
      have hz0 : z ≠ 0 := by linarith
      have hz10 : z + 1 ≠ 0 := by linarith
      have hzprod : (0 : ℝ) < z * (z + 1) := by nlinarith
      change 1 - 3 / z < (z - 1) ^ 2 / (z * (z + 1))
      have hz3 : 1 - 3 / z = (z - 3) / z := by
        field_simp [hz0]
      rw [hz3]
      have hdiff : (z - 1) ^ 2 / (z * (z + 1)) - (z - 3) / z =
          4 / (z * (z + 1)) := by
        field_simp [hz0, hz10]
        ring
      have hpos : (0 : ℝ) < 4 / (z * (z + 1)) := div_pos (by norm_num) hzprod
      nlinarith [hdiff, hpos]
  have hle3R : (2 * (c.k : ℝ) ^ 2) / (c.H.index : ℝ) < (2 : ℝ) := by
    have hIdxR : (c.H.index : ℝ) ≠ 0 := by exact_mod_cast hAposQ.ne'
    have hxR0 : (x : ℝ) ≠ 0 := by exact_mod_cast hxq0
    have hxR1 : (x : ℝ) + 1 ≠ 0 := by exact_mod_cast hxq1
    have hEqR : (c.H.index : ℝ) * ((x : ℝ) - 1) ^ 2 =
        (2 * (c.k : ℝ) ^ 2) * (x : ℝ) * ((x : ℝ) + 1) := by
      exact_mod_cast hEqQ
    have hdivR : (2 * (c.k : ℝ) ^ 2) / (c.H.index : ℝ) =
        ((x : ℝ) - 1) ^ 2 / ((x : ℝ) * ((x : ℝ) + 1)) := by
      field_simp [hIdxR, hxR0, hxR1]
      ring_nf at hEqR ⊢
      exact hEqR.symm
    rw [hdivR]
    let z : ℝ := (x : ℝ)
    rcases hcases with hx9 | hx7
    · have hx9r : (9 : ℝ) ≤ z := by
        simpa [z] using (show (9 : ℝ) ≤ (x : ℝ) by exact_mod_cast hx9)
      have hzpos : (0 : ℝ) < z := by linarith
      have hzprod : (0 : ℝ) < z * (z + 1) := by nlinarith
      change (z - 1) ^ 2 / (z * (z + 1)) < (2 : ℝ)
      rw [div_lt_iff₀ hzprod]
      nlinarith [hx9r]
    · have hx7r : z ≤ -7 := by
        simpa [z] using (show (x : ℝ) ≤ -7 by exact_mod_cast hx7)
      have hzneg : z < 0 := by linarith
      have hzprod : (0 : ℝ) < z * (z + 1) := by nlinarith
      change (z - 1) ^ 2 / (z * (z + 1)) < (2 : ℝ)
      rw [div_lt_iff₀ hzprod]
      nlinarith [hx7r]
  have hle3 : ↑((2 * (c.k : ℚ) ^ 2) / c.H.index : ℚ) < (2 : ℝ) := by
    rw [show (↑((2 * (c.k : ℚ) ^ 2) / c.H.index : ℚ) : ℝ) =
        (2 * (c.k : ℝ) ^ 2) / (c.H.index : ℝ) by norm_num]
    exact hle3R
  -- constituent certificate
  have hConst : IsConstituentOf φ (tildeNu c h12 ⟨(1 : ClassFunction (↥c.H0)),
      (isLinearCharacter_of_hom (1 : ↥c.H0 →* ℂˣ)).1⟩) := by
    unfold IsConstituentOf
    constructor
    · exact hφsign
    · change scalarProduct G φ (tildeNu c h12 (lambdaOneIrr c)) ≠ 0
      rw [hδeq]
      have hpair1 : scalarProduct G φ (1 : ClassFunction G) = 0 := by
        rcases hφsign with hφirr | hφneg
        · rw [scalarProduct_irr_ite hφirr (isIrreducibleCharacter_one G)]
          rw [if_neg hφne1]
        · have hpair : scalarProduct G (-φ) (1 : ClassFunction G) = 0 := by
            rw [scalarProduct_irr_ite hφneg (isIrreducibleCharacter_one G)]
            have hne : -φ ≠ (1 : ClassFunction G) := by
              intro h1
              have hφ1 : φ = -(1 : ClassFunction G) := by
                have h := congrArg (fun z : ClassFunction G => -z) h1
                simpa using h
              have hval : φ c.t = -1 := by
                rw [hφ1]
                rfl
              rw [hφt] at hval
              norm_num at hval
            rw [if_neg hne]
          calc
            scalarProduct G φ (1 : ClassFunction G) =
                scalarProduct G (-(-φ)) (1 : ClassFunction G) := by rw [neg_neg]
            _ = -(scalarProduct G (-φ) (1 : ClassFunction G)) := by
              rw [scalarProduct_neg_left]
            _ = 0 := by rw [hpair]; norm_num
      have hself : scalarProduct G φ φ = 1 := signed_irr_norm_one hφsign
      have hsum : scalarProduct G φ ((1 : ClassFunction G) + φ) = 1 := by
        rw [scalarProduct_add_right, hpair1, hself]
        norm_num
      rw [hsum]
      norm_num
  exact ⟨φ, hConst, hφne1, hφt, hle1, hle2, hle3⟩

end Section2FiniteV

end CFSG.BenderGlauberman
