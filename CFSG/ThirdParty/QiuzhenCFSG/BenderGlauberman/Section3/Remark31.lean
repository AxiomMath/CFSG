module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section2.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section2.Coherence
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.ClassFunction
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

namespace CFSG
end CFSG
open CFSG

/-!
# Bender--Glauberman: Section 3 — Remark 3.1

The `Λ(α)`-orbit analysis of Remark 3.1: existence and uniqueness of the
`Λ`-orbit whose elements restrict to `α1 + ⋯ + αn` on `U`, its cardinality
`m/n`, the degree sum `m·α(1)`, the `s`-fixedness criterion
(`S_α ≰ S0`), and the fact that every `Λ`-orbit is of the form `Λ(α)`.
Statement only (`sorry` body).
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

section Section3

variable {G : Type u} [Group G] [Fintype G]
variable (c : Hyp11 G)

/-- Multiplying by a `Λ`-character does not change the restriction to `U`. -/
public lemma restrictU_lambda_mul (c : Hyp11 G) (h12 : Hyp12 c)
    (l : LambdaHom c.H0 c.U) (ν : ClassFunction (↥c.H0)) :
    restrictU c h12 (LambdaChar l.1 * ν) = restrictU c h12 ν := by
  ext u
  have hl : l.1 ⟨(u : G), (h12.U_normal_in_H0).1 u.2⟩ = 1 := by
    exact l.2 ⟨(u : G), (h12.U_normal_in_H0).1 u.2⟩ u.2
  simp [restrictU, LambdaChar, hl]

/-- Every member of a `Λ`-orbit has the same restriction to `U`. -/
public lemma restrictU_orbit_mem (c : Hyp11 G) (h12 : Hyp12 c)
    [Fintype ↥(LambdaHom c.H0 c.U)] {ν μ : ClassFunction (↥c.H0)}
    (hμ : μ ∈ orbit c.H0 c.U ν) :
    restrictU c h12 μ = restrictU c h12 ν := by
  rcases (Finset.mem_image.mp hμ) with ⟨l, hl, rfl⟩
  exact restrictU_lambda_mul c h12 l ν

/-- The sum over an orbit of the restrictions equals the orbit size times the
common restriction. -/
public lemma restrictU_orbit_sum (c : Hyp11 G) (h12 : Hyp12 c)
    [Fintype ↥(LambdaHom c.H0 c.U)] (ν : ClassFunction (↥c.H0)) :
    (∑ μ ∈ orbit c.H0 c.U ν, restrictU c h12 μ) =
      (orbit c.H0 c.U ν).card • restrictU c h12 ν := by
  calc
    (∑ μ ∈ orbit c.H0 c.U ν, restrictU c h12 μ)
        = (∑ μ ∈ orbit c.H0 c.U ν, restrictU c h12 ν) := by
            refine Finset.sum_congr rfl ?_
            intro μ hμ
            exact restrictU_orbit_mem c h12 hμ
    _ = (orbit c.H0 c.U ν).card • restrictU c h12 ν := by
            rw [Finset.sum_const]

/-- Since `S'` centralizes `U`, every element of `S'` fixes every character of
`U` under conjugation. -/
public lemma SPrime_fixes_classFunction (c : Hyp11 G) (hSC : Section3Hyp c)
    {s' : G} (hs' : s' ∈ SPrime c) (ψ : ClassFunction (↥c.U)) :
    conjChar c.U (fun x : ↥c.U =>
      S_normalizes_U c s' (c.S0_le_S (SPrime_le_S0 c hs')) x.1 x.2) ψ = ψ := by
  ext u
  apply congrArg ψ
  apply Subtype.ext
  have hc : s' ∈ Subgroup.centralizer ((c.U : Subgroup G) : Set G) := hSC hs'
  have hcomm : (u : G) * s' = s' * (u : G) := (Subgroup.mem_centralizer_iff.mp hc) u u.2
  calc
    s' * (u : G) * s'⁻¹ = (u : G) * s' * s'⁻¹ := by rw [← hcomm]
    _ = (u : G) := by group

/-- Every element of `S'` fixes every `α ∈ Irr(U)`. -/
public lemma SPrime_fixes_alpha (c : Hyp11 G) (hSC : Section3Hyp c)
    (α : Irr (↥c.U)) {s' : G} (hs' : s' ∈ SPrime c) :
    conjIrrS c (c.S0_le_S (SPrime_le_S0 c hs')) α = α := by
  apply Subtype.ext
  exact SPrime_fixes_classFunction c hSC hs' α.1

/-- Conjugation by `1` is the identity on `Irr(U)`. -/
public lemma conjIrrS_one (c : Hyp11 G) (α : Irr (↥c.U)) :
    conjIrrS c (c.S0_le_S ((c.S0 : Subgroup G).one_mem)) α = α := by
  apply Subtype.ext
  ext u
  simp only [conjIrrS, conjChar, conjMonoidHom]
  change α.1 ⟨1 * (u : G) * 1⁻¹, _⟩ = α.1 u
  apply congrArg α.1
  apply Subtype.ext
  group

/-- Conjugation by an element of `S` is injective on `Irr(U)`. -/
public lemma conjIrrS_injective (c : Hyp11 G) {g : G} (hg : g ∈ (c.S : Subgroup G))
    {β γ : Irr (↥c.U)} (h : conjIrrS c hg β = conjIrrS c hg γ) : β = γ := by
  have hβ : conjIrrS c ((c.S : Subgroup G).inv_mem hg) (conjIrrS c hg β) = β :=
    conjIrrS_inv c hg β
  have hγ : conjIrrS c ((c.S : Subgroup G).inv_mem hg) (conjIrrS c hg γ) = γ :=
    conjIrrS_inv c hg γ
  rw [← hβ, ← hγ, h]

/-- `r0` fixes `α` iff `r0⁻¹` fixes `α`. -/
public lemma conjIrrS_r0_fixed_iff_r0_inv (c : Hyp11 G) (α : Irr (↥c.U)) :
    (conjIrrS c (c.S0_le_S (S0_generator_mem_S0 c)) α = α) ↔
      (conjIrrS c (c.S0_le_S ((c.S0 : Subgroup G).inv_mem (S0_generator_mem_S0 c))) α = α) := by
  constructor
  · intro h
    have hm := conjIrrS_mul c (c.S0_le_S (S0_generator_mem_S0 c))
      (c.S0_le_S ((c.S0 : Subgroup G).inv_mem (S0_generator_mem_S0 c))) α
    have h1 : conjIrrS c (c.S0_le_S ((c.S0 : Subgroup G).mul_mem (S0_generator_mem_S0 c)
        ((c.S0 : Subgroup G).inv_mem (S0_generator_mem_S0 c)))) α = α := by
      apply Subtype.ext
      ext u
      simp only [conjIrrS, conjChar, conjMonoidHom]
      change α.1 ⟨(S0_generator c) * (S0_generator c)⁻¹ * (u : G) *
          ((S0_generator c) * (S0_generator c)⁻¹)⁻¹, _⟩ = α.1 u
      apply congrArg α.1
      apply Subtype.ext
      group
    calc
      conjIrrS c (c.S0_le_S ((c.S0 : Subgroup G).inv_mem (S0_generator_mem_S0 c))) α
          = conjIrrS c (c.S0_le_S ((c.S0 : Subgroup G).inv_mem (S0_generator_mem_S0 c)))
              (conjIrrS c (c.S0_le_S (S0_generator_mem_S0 c)) α) := by rw [h]
      _ = conjIrrS c (c.S0_le_S ((c.S0 : Subgroup G).mul_mem (S0_generator_mem_S0 c)
              ((c.S0 : Subgroup G).inv_mem (S0_generator_mem_S0 c)))) α := by
            exact hm.symm
      _ = α := h1
  · intro h
    have hm := conjIrrS_mul c (c.S0_le_S ((c.S0 : Subgroup G).inv_mem (S0_generator_mem_S0 c)))
      (c.S0_le_S (S0_generator_mem_S0 c)) α
    have h1 : conjIrrS c (c.S0_le_S ((c.S0 : Subgroup G).mul_mem
        ((c.S0 : Subgroup G).inv_mem (S0_generator_mem_S0 c)) (S0_generator_mem_S0 c))) α = α := by
      apply Subtype.ext
      ext u
      simp only [conjIrrS, conjChar, conjMonoidHom]
      change α.1 ⟨(S0_generator c)⁻¹ * (S0_generator c) * (u : G) *
          ((S0_generator c)⁻¹ * (S0_generator c))⁻¹, _⟩ = α.1 u
      apply congrArg α.1
      apply Subtype.ext
      group
    calc
      conjIrrS c (c.S0_le_S (S0_generator_mem_S0 c)) α
          = conjIrrS c (c.S0_le_S (S0_generator_mem_S0 c))
              (conjIrrS c (c.S0_le_S ((c.S0 : Subgroup G).inv_mem (S0_generator_mem_S0 c))) α) := by rw [h]
      _ = conjIrrS c (c.S0_le_S ((c.S0 : Subgroup G).mul_mem
              ((c.S0 : Subgroup G).inv_mem (S0_generator_mem_S0 c)) (S0_generator_mem_S0 c))) α := by
            exact hm.symm
      _ = α := h1

/-- When `r0` moves `α`, conjugation by `r0⁻¹` agrees with conjugation by
`r0` (both send `α` to the unique other element of the `S0`-orbit). -/
public lemma conjIrrS_r0_eq_r0_inv_of_not_fixed (c : Hyp11 G) (hSC : Section3Hyp c)
    (α : Irr (↥c.U))
    (hα : conjIrrS c (c.S0_le_S (S0_generator_mem_S0 c)) α ≠ α) :
    conjIrrS c (c.S0_le_S ((c.S0 : Subgroup G).inv_mem (S0_generator_mem_S0 c))) α =
      conjIrrS c (c.S0_le_S (S0_generator_mem_S0 c)) α := by
  have hA : conjIrrS c (c.S0_le_S (S0_generator_mem_S0 c))
      (conjIrrS c (c.S0_le_S ((c.S0 : Subgroup G).inv_mem (S0_generator_mem_S0 c))) α) = α := by
    have hm := conjIrrS_mul c (c.S0_le_S ((c.S0 : Subgroup G).inv_mem (S0_generator_mem_S0 c)))
      (c.S0_le_S (S0_generator_mem_S0 c)) α
    have h1 : conjIrrS c (c.S0_le_S ((c.S0 : Subgroup G).mul_mem
        ((c.S0 : Subgroup G).inv_mem (S0_generator_mem_S0 c)) (S0_generator_mem_S0 c))) α = α := by
      apply Subtype.ext
      ext u
      simp only [conjIrrS, conjChar, conjMonoidHom]
      change α.1 ⟨(S0_generator c)⁻¹ * (S0_generator c) * (u : G) *
          ((S0_generator c)⁻¹ * (S0_generator c))⁻¹, _⟩ = α.1 u
      apply congrArg α.1
      apply Subtype.ext
      group
    exact hm.symm.trans h1
  have hsq : (S0_generator c) * (S0_generator c) ∈ SPrime c := by
    simpa [S0_generator, pow_two] using SPrime_mem_pow_two c
  have hB : conjIrrS c (c.S0_le_S (S0_generator_mem_S0 c))
      (conjIrrS c (c.S0_le_S (S0_generator_mem_S0 c)) α) = α := by
    have hm := conjIrrS_mul c (c.S0_le_S (S0_generator_mem_S0 c))
      (c.S0_le_S (S0_generator_mem_S0 c)) α
    have hfix : conjIrrS c (c.S0_le_S (SPrime_le_S0 c hsq)) α = α :=
      SPrime_fixes_alpha c hSC α hsq
    calc
      conjIrrS c (c.S0_le_S (S0_generator_mem_S0 c))
          (conjIrrS c (c.S0_le_S (S0_generator_mem_S0 c)) α)
          = conjIrrS c (c.S0_le_S ((c.S0 : Subgroup G).mul_mem (S0_generator_mem_S0 c)
              (S0_generator_mem_S0 c))) α := hm.symm
      _ = α := by
            simpa using hfix
  exact conjIrrS_injective c (c.S0_le_S (S0_generator_mem_S0 c)) (by
    calc
      conjIrrS c (c.S0_le_S (S0_generator_mem_S0 c))
          (conjIrrS c (c.S0_le_S ((c.S0 : Subgroup G).inv_mem (S0_generator_mem_S0 c))) α) = α := hA
      _ = conjIrrS c (c.S0_le_S (S0_generator_mem_S0 c))
          (conjIrrS c (c.S0_le_S (S0_generator_mem_S0 c)) α) := hB.symm)

/-- The `S0`-conjugates of any `α ∈ Irr(U)` number at most two (`S' ≤ S0` of
index `2` fixes `α`). -/
public lemma s0Orbit_card_le_two (c : Hyp11 G) (hSC : Section3Hyp c)
    (α : Irr (↥c.U)) : (s0Orbit c α).card ≤ 2 := by
  classical
  have hrel : (SPrime c).relIndex (c.S0 : Subgroup G) = 2 := by
    simpa [Subgroup.relIndex] using SPrime_index c
  rcases (Subgroup.relIndex_eq_two_iff_exists_notMem_and'.mp hrel) with
    ⟨a, haS0, _haSP, hall⟩
  have haS : (a⁻¹ : G) ∈ (c.S : Subgroup G) := c.S0_le_S ((c.S0 : Subgroup G).inv_mem haS0)
  have hsub : s0Orbit c α ⊆ ({α, conjIrrS c haS α} : Finset (Irr (↥c.U))) := by
    intro φ hφ
    rcases (Finset.mem_image.mp hφ) with ⟨g, hg, rfl⟩
    rcases (hall (g : G) g.2) with hgSP | hgSP
    · -- `a·g ∈ S'`: `g` is in the other coset, so `conjIrrS g α = conjIrrS (a⁻¹) α`
      have h1 : (a * (g : G)) ∈ (c.S : Subgroup G) :=
        c.S0_le_S (SPrime_le_S0 c hgSP)
      have hEqG : (a⁻¹ : G) * (a * (g : G)) = (g : G) := by group
      have hEq : conjIrrS c (c.S0_le_S g.2) α =
          conjIrrS c ((c.S : Subgroup G).mul_mem haS h1) α := by
        simpa [hEqG]
      have hEq2 : conjIrrS c ((c.S : Subgroup G).mul_mem haS h1) α =
          conjIrrS c haS α := by
        calc
          conjIrrS c ((c.S : Subgroup G).mul_mem haS h1) α =
              conjIrrS c h1 (conjIrrS c haS α) := conjIrrS_mul c haS h1 α
          _ = conjIrrS c haS α := by
            apply Subtype.ext
            exact SPrime_fixes_classFunction c hSC hgSP (conjIrrS c haS α).1
      rw [hEq, hEq2]
      simp
    · -- `g ∈ S'`: `g` fixes `α`
      have hfix : conjIrrS c (c.S0_le_S (SPrime_le_S0 c hgSP)) α = α :=
        SPrime_fixes_alpha c hSC α hgSP
      have hEq : conjIrrS c (c.S0_le_S g.2) α =
          conjIrrS c (c.S0_le_S (SPrime_le_S0 c hgSP)) α := by
        rfl
      rw [hEq, hfix]
      simp
  have hcard2 : ({α, conjIrrS c haS α} : Finset (Irr (↥c.U))).card ≤ 2 := by
    simpa using Finset.card_insert_le α ({conjIrrS c haS α} : Finset (Irr (↥c.U)))
  exact (Finset.card_le_card hsub).trans hcard2

/-- The `S0`-orbit of `α` is contained in `{α, α^{r0⁻¹}}`. -/
public lemma s0Orbit_subset_pair_inv (c : Hyp11 G) (hSC : Section3Hyp c) (α : Irr (↥c.U)) :
    s0Orbit c α ⊆
      ({α, conjIrrS c (c.S0_le_S ((c.S0 : Subgroup G).inv_mem (S0_generator_mem_S0 c))) α} :
        Finset (Irr (↥c.U))) := by
  intro φ hφ
  rcases (Finset.mem_image.mp hφ) with ⟨g, hg, rfl⟩
  rcases (S0_mem_SPrime_or_r0_mul c g.2) with hgSP | hr0gSP
  · rw [Finset.mem_insert, Finset.mem_singleton]
    left
    have hfix : conjIrrS c (c.S0_le_S (SPrime_le_S0 c hgSP)) α = α :=
      SPrime_fixes_alpha c hSC α hgSP
    have hEq : conjIrrS c (c.S0_le_S g.2) α = conjIrrS c (c.S0_le_S (SPrime_le_S0 c hgSP)) α := by
      rfl
    rw [hEq, hfix]
  · rw [Finset.mem_insert, Finset.mem_singleton]
    right
    have h1 : (S0_generator c) * (g : G) ∈ (c.S : Subgroup G) :=
      c.S0_le_S (SPrime_le_S0 c hr0gSP)
    have hgEq : (S0_generator c)⁻¹ * ((S0_generator c) * (g : G)) = (g : G) := by group
    have h2 : conjIrrS c (c.S0_le_S g.2) α =
        conjIrrS c ((c.S : Subgroup G).mul_mem (c.S0_le_S ((c.S0 : Subgroup G).inv_mem (S0_generator_mem_S0 c))) h1) α := by
      simpa [hgEq]
    have h3 : conjIrrS c ((c.S : Subgroup G).mul_mem (c.S0_le_S ((c.S0 : Subgroup G).inv_mem (S0_generator_mem_S0 c))) h1) α =
        conjIrrS c h1 (conjIrrS c (c.S0_le_S ((c.S0 : Subgroup G).inv_mem (S0_generator_mem_S0 c))) α) :=
      conjIrrS_mul c (c.S0_le_S ((c.S0 : Subgroup G).inv_mem (S0_generator_mem_S0 c))) h1 α
    have h4 : conjIrrS c h1 (conjIrrS c (c.S0_le_S ((c.S0 : Subgroup G).inv_mem (S0_generator_mem_S0 c))) α) =
        conjIrrS c (c.S0_le_S ((c.S0 : Subgroup G).inv_mem (S0_generator_mem_S0 c))) α :=
      SPrime_fixes_alpha c hSC (conjIrrS c (c.S0_le_S ((c.S0 : Subgroup G).inv_mem (S0_generator_mem_S0 c))) α) hr0gSP
    rw [h2, h3, h4]

/-- When `r0` fixes `α`, the `S0`-orbit is the singleton `{α}`. -/
public lemma s0Orbit_eq_singleton_of_fixed (c : Hyp11 G) (hSC : Section3Hyp c)
    (α : Irr (↥c.U))
    (hfix : conjIrrS c (c.S0_le_S (S0_generator_mem_S0 c)) α = α) :
    s0Orbit c α = {α} := by
  apply Finset.eq_singleton_iff_unique_mem.mpr
  constructor
  · refine Finset.mem_image.mpr
      ⟨⟨1, (c.S0 : Subgroup G).one_mem⟩, Finset.mem_univ _, ?_⟩
    exact conjIrrS_one c α
  · intro β hβ
    have hsub := s0Orbit_subset_pair_inv c hSC α hβ
    rw [Finset.mem_insert, Finset.mem_singleton] at hsub
    rcases hsub with hβ' | hβ'
    · exact hβ'
    · rw [hβ']
      exact (conjIrrS_r0_fixed_iff_r0_inv c α).mp hfix

/-- When `r0` moves `α`, the `S0`-orbit is the pair `{α, α^{r0⁻¹}}`. -/
public lemma s0Orbit_eq_pair_of_not_fixed (c : Hyp11 G) (hSC : Section3Hyp c)
    (α : Irr (↥c.U))
    (hα : conjIrrS c (c.S0_le_S (S0_generator_mem_S0 c)) α ≠ α) :
    s0Orbit c α =
      ({α, conjIrrS c (c.S0_le_S ((c.S0 : Subgroup G).inv_mem (S0_generator_mem_S0 c))) α} :
        Finset (Irr (↥c.U))) := by
  have hmem1 : α ∈ s0Orbit c α := by
    refine Finset.mem_image.mpr
      ⟨⟨1, (c.S0 : Subgroup G).one_mem⟩, Finset.mem_univ _, ?_⟩
    exact conjIrrS_one c α
  have hmem2 : conjIrrS c (c.S0_le_S ((c.S0 : Subgroup G).inv_mem (S0_generator_mem_S0 c))) α ∈
      s0Orbit c α := by
    refine Finset.mem_image.mpr
      ⟨⟨(S0_generator c)⁻¹, (c.S0 : Subgroup G).inv_mem (S0_generator_mem_S0 c)⟩,
        Finset.mem_univ _, rfl⟩
  have hne : conjIrrS c (c.S0_le_S ((c.S0 : Subgroup G).inv_mem (S0_generator_mem_S0 c))) α ≠ α := by
    intro h'
    exact hα ((conjIrrS_r0_fixed_iff_r0_inv c α).mpr h')
  have hsub : ({α, conjIrrS c (c.S0_le_S ((c.S0 : Subgroup G).inv_mem (S0_generator_mem_S0 c))) α} :
        Finset (Irr (↥c.U))) ⊆ s0Orbit c α := by
    intro β hβ
    rw [Finset.mem_insert, Finset.mem_singleton] at hβ
    rcases hβ with hβ' | hβ'
    · simpa [hβ'] using hmem1
    · simpa [hβ'] using hmem2
  have hcard2 : ({α, conjIrrS c (c.S0_le_S ((c.S0 : Subgroup G).inv_mem (S0_generator_mem_S0 c))) α} :
        Finset (Irr (↥c.U))).card = 2 := by
    have hmem : α ∉ ({conjIrrS c (c.S0_le_S ((c.S0 : Subgroup G).inv_mem (S0_generator_mem_S0 c))) α} :
        Finset (Irr (↥c.U))) := by
      intro h
      exact hne (Finset.mem_singleton.mp h).symm
    rw [Finset.card_insert_of_notMem hmem]
    · simp
  have hcard : 2 ≤ (s0Orbit c α).card := by
    rw [← hcard2]
    exact Finset.card_le_card hsub
  exact Finset.eq_of_subset_of_card_le (s0Orbit_subset_pair_inv c hSC α)
    (by rw [hcard2]; exact hcard)

/-- The orbit sum equals `α + α^r0` when `r0` moves `α`. -/
public lemma s0Orbit_sum_eq_α_add_r0_of_not_fixed (c : Hyp11 G) (hSC : Section3Hyp c)
    (α : Irr (↥c.U))
    (hα : conjIrrS c (c.S0_le_S (S0_generator_mem_S0 c)) α ≠ α) :
    (∑ α' ∈ s0Orbit c α, α'.1) =
      fun u : ↥c.U => α.1 u + (conjIrrS c (c.S0_le_S (S0_generator_mem_S0 c)) α).1 u := by
  ext u
  rw [s0Orbit_eq_pair_of_not_fixed c hSC α hα]
  have hsum : (∑ α' ∈ ({α, conjIrrS c (c.S0_le_S ((c.S0 : Subgroup G).inv_mem (S0_generator_mem_S0 c))) α} :
        Finset (Irr (↥c.U))), α'.1) =
      α.1 + (conjIrrS c (c.S0_le_S ((c.S0 : Subgroup G).inv_mem (S0_generator_mem_S0 c))) α).1 :=
    Finset.sum_pair (f := fun β : Irr (↥c.U) => β.1)
      (h := (fun hEq => hα ((conjIrrS_r0_fixed_iff_r0_inv c α).mpr hEq.symm)))
  rw [hsum]
  simp only [Pi.add_apply]
  congr 1
  exact congrArg (fun β : Irr (↥c.U) => β.1 u)
    (conjIrrS_r0_eq_r0_inv_of_not_fixed c hSC α hα)

/-- The orbit sum is `α` when `r0` fixes `α`. -/
public lemma s0Orbit_sum_eq_α_of_fixed (c : Hyp11 G) (hSC : Section3Hyp c)
    (α : Irr (↥c.U))
    (hfix : conjIrrS c (c.S0_le_S (S0_generator_mem_S0 c)) α = α) :
    (∑ α' ∈ s0Orbit c α, α'.1) = α.1 := by
  rw [s0Orbit_eq_singleton_of_fixed c hSC α hfix]
  simp

/-- Every irreducible character of `H0` has a `Λ`-orbit whose restriction to
`U` is the `S0`-orbit sum of some `α ∈ Irr(U)` (the Clifford step of Remark
3.1: choose a constituent of `μ|_X`, restrict it to `U`, and apply the
index-two induction of Remark 1.4). -/
public theorem orbit_restrict_eq_orbitSum_of_irr (c : Hyp11 G) (h12 : Hyp12 c)
    (hSC : Section3Hyp c) [Fintype ↥(LambdaHom c.H0 c.U)] (μ : Irr (↥c.H0)) :
    ∃ α : Irr (↥c.U), ∀ ν : ClassFunction (↥c.H0),
      ν ∈ orbit c.H0 c.U μ.1 →
        restrictU c h12 ν = ∑ α' ∈ s0Orbit c α, α'.1 := by
  classical
  let K : Subgroup (↥c.H0) := (extensionSubgroup c).subgroupOf c.H0
  let eK : K ≃* ↥(extensionSubgroup c) :=
    Subgroup.subgroupOfEquivOfLe (H := extensionSubgroup c) (K := c.H0)
      (SPrimeMulU_le_H0 c)
  let ψK : ClassFunction (↥K) := fun x => μ.1 (x : ↥c.H0)
  have hψK : IsCharacter ψK :=
    isCharacter_restrict (G := ↥c.H0) (H := K)
      (isCharacter_of_isIrreducibleCharacter μ.2)
  let ψX : ClassFunction (↥(extensionSubgroup c)) := fun x => ψK (eK.symm x)
  have hψX : IsCharacter ψX := isCharacter_congr eK.symm hψK
  have hne : ψX ≠ 0 := by
    intro h
    have hv := congrFun h (1 : ↥(extensionSubgroup c))
    simp [ψX, ψK] at hv
    exact irreducible_char_one_ne_zero μ.2 hv
  rcases exists_irr_constituent_of_character hψX hne with ⟨ξ, hξ, hsp⟩
  rcases exists_extensionChar_of_isIrreducible c hSC hξ with ⟨α, lam, hEq⟩
  have hψXeq : ψX = fun x : ↥(extensionSubgroup c) =>
      μ.1 ⟨(x : G), SPrimeMulU_le_H0 c x.2⟩ := by
    ext x
    change μ.1 (⟨(x : G), SPrimeMulU_le_H0 c x.2⟩ : ↥c.H0) =
      μ.1 ⟨(x : G), SPrimeMulU_le_H0 c x.2⟩
    rfl
  have hspRestrict : scalarProduct (↥(extensionSubgroup c)) ξ
      (fun x : ↥(extensionSubgroup c) => μ.1 ⟨(x : G), SPrimeMulU_le_H0 c x.2⟩) ≠ 0 := by
    simpa [hψXeq] using hsp
  have hspInd : scalarProduct (↥c.H0) (inducedFromSub (SPrimeMulU_le_H0 c) ξ) μ.1 ≠ 0 := by
    rw [frobenius_reciprocity_inducedFromSub (SPrimeMulU_le_H0 c) ξ
      (isCharacter_isClassFunction (isCharacter_of_isIrreducibleCharacter μ.2))]
    exact hspRestrict
  have hspInd' : scalarProduct (↥c.H0) (extensionChar_ind c hSC α lam) μ.1 ≠ 0 := by
    simpa [extensionChar_ind, hEq] using hspInd
  by_cases hα : conjIrrS c (c.S0_le_S (S0_generator_mem_S0 c)) α = α
  · -- `r0` fixes `α`: every constituent of `Ind_X^{H0}(α̂)` restricts to `α`.
    have hμres : restrictU c h12 μ.1 = α.1 :=
      extensionChar_ind_constituent_restrict_of_fixed c hSC h12 α lam hα μ.2 hspInd'
    refine ⟨α, ?_⟩
    intro ν hν
    calc
      restrictU c h12 ν = restrictU c h12 μ.1 := restrictU_orbit_mem c h12 hν
      _ = α.1 := hμres
      _ = ∑ α' ∈ s0Orbit c α, α'.1 :=
            (s0Orbit_sum_eq_α_of_fixed c hSC α hα).symm
  · -- `r0` moves `α`: the induced extension is irreducible and equal to `μ`.
    have hν : IsIrreducibleCharacter (extensionChar_ind c hSC α lam) :=
      extensionChar_ind_isIrreducible_of_not_fixed c hSC h12 α lam hα
    have hμeq : μ.1 = extensionChar_ind c hSC α lam := by
      by_contra hne'
      have hz : scalarProduct (↥c.H0) (extensionChar_ind c hSC α lam) μ.1 = 0 :=
        scalarProduct_irreducible_orthogonal hν μ.2 (by
          intro hEq
          exact hne' hEq.symm)
      exact hspInd' hz
    have hμres : restrictU c h12 μ.1 = ∑ α' ∈ s0Orbit c α, α'.1 := by
      rw [hμeq, extensionChar_ind_restrict]
      simpa [conjIrrS, conjChar, conjMonoidHom] using
        (s0Orbit_sum_eq_α_add_r0_of_not_fixed c hSC α hα).symm
    refine ⟨α, ?_⟩
    intro ν hν
    calc
      restrictU c h12 ν = restrictU c h12 μ.1 := restrictU_orbit_mem c h12 hν
      _ = ∑ α' ∈ s0Orbit c α, α'.1 := hμres

/-- `Λ(α)`: the unique `Λ`-orbit of Remark 3.1 whose elements restrict to
`α1 + ⋯ + αn` on `U`. -/
public noncomputable def orbitOfAlpha (c : Hyp11 G) (h12 : Hyp12 c) (hSC : Section3Hyp c)
    [Fintype ↥(LambdaHom c.H0 c.U)] (α : Irr (↥c.U)) : Finset (ClassFunction (↥c.H0)) :=
  let lam : ↥(SPrime c) →* ℂˣ := 1
  if hα : conjIrrS c (c.S0_le_S (S0_generator_mem_S0 c)) α = α then
    let p := Classical.choose (extensionChar_ind_decomp_of_fixed c hSC h12 α lam hα)
    orbit c.H0 c.U p
  else
    orbit c.H0 c.U (extensionChar_ind c hSC α lam)

/-- `Λ(α)` is a `Λ`-orbit and each of its elements restricts to the sum of
the `S0`-conjugates of `α`. -/
public theorem orbitOfAlpha_spec (c : Hyp11 G) (h12 : Hyp12 c) (hSC : Section3Hyp c)
    [Fintype ↥(LambdaHom c.H0 c.U)] (α : Irr (↥c.U)) :
    (∃ μ : Irr (↥c.H0), orbitOfAlpha c h12 hSC α = orbit c.H0 c.U μ.1) ∧
      (∀ ν : ClassFunction (↥c.H0), ν ∈ orbitOfAlpha c h12 hSC α →
        restrictU c h12 ν = ∑ α' ∈ s0Orbit c α, α'.1) := by
  classical
  let lam : ↥(SPrime c) →* ℂˣ := 1
  by_cases hα : conjIrrS c (c.S0_le_S (S0_generator_mem_S0 c)) α = α
  · let p := Classical.choose (extensionChar_ind_decomp_of_fixed c hSC h12 α lam hα)
    rcases Classical.choose_spec (extensionChar_ind_decomp_of_fixed c hSC h12 α lam hα) with
      ⟨σ₂, hp1, hσ₂, hne, hsum⟩
    constructor
    · refine ⟨⟨p, hp1⟩, ?_⟩
      simpa [orbitOfAlpha, lam, hα, p]
    · intro ν hν
      have hν' : ν ∈ orbit c.H0 c.U p := by
        simpa [orbitOfAlpha, lam, hα, p] using hν
      have hsp : scalarProduct (↥c.H0) (extensionChar_ind c hSC α lam) p ≠ 0 := by
        rw [hsum, scalarProduct_add_left]
        rw [scalarProduct_irreducible_self hp1]
        rw [scalarProduct_irreducible_orthogonal
          hσ₂ hp1 (fun hEq => hne hEq.symm)]
        norm_num
      have hres : restrictU c h12 p = α.1 :=
        extensionChar_ind_constituent_restrict_of_fixed c hSC h12 α lam hα hp1 hsp
      calc
        restrictU c h12 ν = restrictU c h12 p := restrictU_orbit_mem c h12 hν'
        _ = α.1 := hres
        _ = ∑ α' ∈ s0Orbit c α, α'.1 :=
              (s0Orbit_sum_eq_α_of_fixed c hSC α hα).symm
  · have hν : IsIrreducibleCharacter (extensionChar_ind c hSC α lam) :=
      extensionChar_ind_isIrreducible_of_not_fixed c hSC h12 α lam hα
    have hres : restrictU c h12 (extensionChar_ind c hSC α lam) =
        ∑ α' ∈ s0Orbit c α, α'.1 := by
      rw [extensionChar_ind_restrict]
      simpa [conjIrrS, conjChar, conjMonoidHom] using
        (s0Orbit_sum_eq_α_add_r0_of_not_fixed c hSC α hα).symm
    constructor
    · refine ⟨⟨extensionChar_ind c hSC α lam, hν⟩, ?_⟩
      simpa [orbitOfAlpha, lam, hα]
    · intro ν hν
      have hν' : ν ∈ orbit c.H0 c.U (extensionChar_ind c hSC α lam) := by
        simpa [orbitOfAlpha, lam, hα] using hν
      calc
        restrictU c h12 ν = restrictU c h12 (extensionChar_ind c hSC α lam) :=
              restrictU_orbit_mem c h12 hν'
        _ = ∑ α' ∈ s0Orbit c α, α'.1 := hres

/-- Orbits are equal-or-disjoint: if `μ ∈ orbit ν`, then `orbit μ = orbit ν`. -/
public lemma orbit_eq_of_mem' (c : Hyp11 G) [Fintype ↥(LambdaHom c.H0 c.U)]
    {ν μ : ClassFunction (↥c.H0)} (hμ : μ ∈ orbit c.H0 c.U ν) :
    orbit c.H0 c.U μ = orbit c.H0 c.U ν := by
  classical
  rcases (Finset.mem_image.mp hμ) with ⟨l₀, hl₀, hEq₀⟩
  apply Finset.ext
  intro ψ
  constructor
  · intro hψ
    rcases (Finset.mem_image.mp hψ) with ⟨l, hl, rfl⟩
    refine Finset.mem_image.mpr ⟨l * l₀, Finset.mem_univ _, ?_⟩
    rw [← hEq₀]
    ext x
    simp [LambdaChar, map_mul, mul_assoc]
  · intro hψ
    rcases (Finset.mem_image.mp hψ) with ⟨l, hl, rfl⟩
    refine Finset.mem_image.mpr ⟨l * l₀⁻¹, Finset.mem_univ _, ?_⟩
    ext x
    simp [LambdaChar, map_mul, map_inv, Units.val_inv, mul_assoc]
    have hμx : μ x = (l₀.1 x : ℂ) * ν x := (congrFun hEq₀ x).symm
    rw [hμx]
    have hne : (l₀.1 x : ℂ) ≠ 0 := unit_val_ne_zero (l₀.1 x)
    rw [← mul_assoc, inv_mul_cancel₀ hne]
    ring

/-- Clifford step for Remark 3.1: if `(α, μ|_U)_U = 1`, then `μ` is a
constituent of some induced extension `Ind_X^{H0}(α̂_lam)`. -/
public theorem exists_lam_constituent_of_scalarProduct_one (c : Hyp11 G) (h12 : Hyp12 c)
    (hSC : Section3Hyp c) (α : Irr (↥c.U)) {μ : Irr (↥c.H0)}
    (hsp : scalarProduct (↥c.U) α.1 (restrictU c h12 μ.1) = 1) :
    ∃ lam : ↥(SPrime c) →* ℂˣ,
      scalarProduct (↥c.H0) (extensionChar_ind c hSC α lam) μ.1 ≠ 0 := by
  classical
  let K : Subgroup (↥c.H0) := (extensionSubgroup c).subgroupOf c.H0
  let eK : K ≃* ↥(extensionSubgroup c) :=
    Subgroup.subgroupOfEquivOfLe (H := extensionSubgroup c) (K := c.H0)
      (SPrimeMulU_le_H0 c)
  let ψK : ClassFunction (↥K) := fun x => μ.1 (x : ↥c.H0)
  let ψX : ClassFunction (↥(extensionSubgroup c)) := fun x => ψK (eK.symm x)
  have hψK : IsCharacter ψK :=
    isCharacter_restrict (G := ↥c.H0) (H := K)
      (isCharacter_of_isIrreducibleCharacter μ.2)
  have hψX : IsCharacter ψX := isCharacter_congr eK.symm hψK
  have hψXeq : ψX = fun x : ↥(extensionSubgroup c) =>
      μ.1 ⟨(x : G), SPrimeMulU_le_H0 c x.2⟩ := by
    ext x
    change μ.1 (⟨(x : G), SPrimeMulU_le_H0 c x.2⟩ : ↥c.H0) =
      μ.1 ⟨(x : G), SPrimeMulU_le_H0 c x.2⟩
    rfl
  have hgen : IsGeneralizedCharacter ψX := ⟨ψX, 0, hψX, isCharacter_zero, by
    ext x
    simp⟩
  rcases char_decomp_generalized hgen with ⟨ι, hfi, χs, ms, hirr, hdist, hψXsum⟩
  let : Fintype ι := hfi
  let αi : ι → Irr (↥c.U) := fun i =>
    Classical.choose (exists_extensionChar_of_isIrreducible c hSC (hξ := hirr i))
  let lam : ι → (↥(SPrime c) →* ℂˣ) := fun i =>
    Classical.choose (Classical.choose_spec
      (exists_extensionChar_of_isIrreducible c hSC (hξ := hirr i)))
  have hχeq : ∀ i, χs i = extensionChar c hSC (αi i) (lam i) := by
    intro i
    exact Classical.choose_spec (Classical.choose_spec
      (exists_extensionChar_of_isIrreducible c hSC (hξ := hirr i)))
  have hres : ∀ i (u : ↥c.U), χs i ⟨(u : G),
      SetLike.le_def.mp (show c.U ≤ extensionSubgroup c from le_sup_right) u.2⟩ = (αi i).1 u := by
    intro i u
    rw [hχeq i]
    simpa using extensionChar_restrict c hSC (αi i) (lam i) u
  let ψU : ClassFunction (↥c.U) := restrictU c h12 μ.1
  have hψUeq : ψU = restrictU c h12 μ.1 := rfl
  have hψUsum : ψU = ∑ i, (ms i : ℂ) • (αi i).1 := by
    ext u
    calc
      ψU u = μ.1 ⟨(u : G), (h12.U_normal_in_H0).1 u.2⟩ := rfl
      _ = ψX ⟨(u : G), SetLike.le_def.mp (show c.U ≤ extensionSubgroup c from le_sup_right) u.2⟩ := by
            rw [hψXeq]
      _ = (∑ i, (ms i : ℂ) • χs i) ⟨(u : G),
          SetLike.le_def.mp (show c.U ≤ extensionSubgroup c from le_sup_right) u.2⟩ := by
            rw [hψXsum]
      _ = ∑ i, (ms i : ℂ) • (χs i ⟨(u : G),
          SetLike.le_def.mp (show c.U ≤ extensionSubgroup c from le_sup_right) u.2⟩) := by
            simp
      _ = (∑ i, (ms i : ℂ) • (αi i).1) u := by
            simp_rw [hres]
            simp
  have hspψU : scalarProduct (↥c.U) α.1 ψU = 1 := by
    rw [hψUeq, hsp]
  have hcoeff : (∑ i, (ms i : ℂ) * (if (αi i).1 = α.1 then 1 else 0)) = 1 := by
    have h := scalarProduct_decomp_left (G := ↥c.U) (ι := ι)
      (χ := α.1) (χs := fun i => (αi i).1) (ms := ms)
      (hχ := α.2) (hχs := fun i => (αi i).2)
    rw [← hψUsum, hspψU] at h
    exact h.symm
  have hex_i : ∃ i, ms i ≠ 0 ∧ (αi i).1 = α.1 := by
    by_contra hnone
    have hsum0 : (∑ i, (ms i : ℂ) * (if (αi i).1 = α.1 then 1 else 0)) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro i hi
      by_cases hms : ms i = 0
      · simp [hms]
      · have hαi : (αi i).1 ≠ α.1 := by
          intro hEq
          exact hnone ⟨i, hms, hEq⟩
        simp [hαi]
    exact (by norm_num : (1 : ℂ) ≠ 0) (hcoeff.symm.trans hsum0)
  rcases hex_i with ⟨i₀, hms₀, hαi₀⟩
  have hχ₀ : extensionChar c hSC α (lam i₀) = χs i₀ := by
    have hαeq : αi i₀ = α := Subtype.ext hαi₀
    rw [← hαeq]
    exact (hχeq i₀).symm
  have hspξ₀ : scalarProduct (↥(extensionSubgroup c)) (extensionChar c hSC α (lam i₀)) ψX =
      (ms i₀ : ℂ) := by
    have h := scalarProduct_decomp_left (G := ↥(extensionSubgroup c)) (ι := ι)
      (χ := χs i₀) (χs := χs) (ms := ms) (hχ := hirr i₀) (hχs := hirr)
    rw [← hψXsum] at h
    have hsum₀ : (∑ j, (ms j : ℂ) * (if χs j = χs i₀ then 1 else 0)) = (ms i₀ : ℂ) := by
      calc
        (∑ j, (ms j : ℂ) * (if χs j = χs i₀ then 1 else 0))
            = (ms i₀ : ℂ) * (if χs i₀ = χs i₀ then 1 else 0) := by
              refine Finset.sum_eq_single (s := Finset.univ)
                (f := fun j : ι => (ms j : ℂ) * (if χs j = χs i₀ then 1 else 0)) i₀ ?_ ?_
              · intro j hj hji
                simp [hdist j i₀ hji]
              · intro hnot
                exact (hnot (Finset.mem_univ i₀)).elim
        _ = (ms i₀ : ℂ) := by
              by_cases h : χs i₀ = χs i₀
              · simp [h]
              · simp [h]
    rw [hsum₀, ← hχ₀] at h
    exact h
  have hspRestrict : scalarProduct (↥(extensionSubgroup c)) (extensionChar c hSC α (lam i₀))
      (fun x : ↥(extensionSubgroup c) => μ.1 ⟨(x : G), SPrimeMulU_le_H0 c x.2⟩) ≠ 0 := by
    rw [← hψXeq]
    rw [hspξ₀]
    exact_mod_cast hms₀
  refine ⟨lam i₀, ?_⟩
  unfold extensionChar_ind
  rw [frobenius_reciprocity_inducedFromSub (SPrimeMulU_le_H0 c) (extensionChar c hSC α (lam i₀))
    (isCharacter_isClassFunction (isCharacter_of_isIrreducibleCharacter μ.2))]
  exact hspRestrict

/-- Uniqueness in Remark 3.1: any `Λ`-orbit whose elements restrict to the
sum of the `S0`-conjugates of `α` is `Λ(α)`. -/
public theorem orbitOfAlpha_unique (c : Hyp11 G) (h12 : Hyp12 c) (hSC : Section3Hyp c)
    [Fintype ↥(LambdaHom c.H0 c.U)] (α : Irr (↥c.U))
    (L : Finset (ClassFunction (↥c.H0)))
    (hL : (∃ μ : Irr (↥c.H0), L = orbit c.H0 c.U μ.1) ∧
      (∀ ν : ClassFunction (↥c.H0), ν ∈ L →
        restrictU c h12 ν = ∑ α' ∈ s0Orbit c α, α'.1)) :
    L = orbitOfAlpha c h12 hSC α := by
  classical
  let lam : ↥(SPrime c) →* ℂˣ := 1
  rcases hL with ⟨⟨μ, hμL⟩, hres⟩
  have hresμ : restrictU c h12 μ.1 = ∑ α' ∈ s0Orbit c α, α'.1 := hres μ.1 (by
    rw [hμL]
    exact Finset.mem_image.mpr ⟨1, Finset.mem_univ 1, by
      ext x
      simp [LambdaChar]⟩)
  have hspα : scalarProduct (↥c.U) α.1 (restrictU c h12 μ.1) = 1 := by
    by_cases hα : conjIrrS c (c.S0_le_S (S0_generator_mem_S0 c)) α = α
    · have hresα : restrictU c h12 μ.1 = α.1 := by
        rw [s0Orbit_sum_eq_α_of_fixed c hSC α hα] at hresμ
        exact hresμ
      rw [hresα]
      exact scalarProduct_irreducible_self α.2
    · have hresα : restrictU c h12 μ.1 =
        fun u : ↥c.U => α.1 u +
          (conjIrrS c (c.S0_le_S (S0_generator_mem_S0 c)) α).1 u := by
        rw [s0Orbit_sum_eq_α_add_r0_of_not_fixed c hSC α hα] at hresμ
        exact hresμ
      rw [hresα]
      change scalarProduct (↥c.U) α.1
        (α.1 + (conjIrrS c (c.S0_le_S (S0_generator_mem_S0 c)) α).1) = 1
      rw [scalarProduct_add_right, scalarProduct_irreducible_self α.2]
      rw [scalarProduct_irreducible_orthogonal α.2
        (conjIrrS c (c.S0_le_S (S0_generator_mem_S0 c)) α).2
        (fun hEq => hα (Subtype.ext hEq).symm)]
      norm_num
  rcases exists_lam_constituent_of_scalarProduct_one c h12 hSC α hspα with ⟨lam₀, hspInd⟩
  by_cases hα : conjIrrS c (c.S0_le_S (S0_generator_mem_S0 c)) α = α
  · let p : ClassFunction (↥c.H0) :=
      Classical.choose (extensionChar_ind_decomp_of_fixed c hSC h12 α lam hα)
    have hp : ∃ σ₂, IsIrreducibleCharacter p ∧ IsIrreducibleCharacter σ₂ ∧ p ≠ σ₂ ∧
        extensionChar_ind c hSC α lam = p + σ₂ :=
      Classical.choose_spec (extensionChar_ind_decomp_of_fixed c hSC h12 α lam hα)
    rcases hp with ⟨σ₂, hσp, hσ₂, hpne, hsum⟩
    rcases extensionChar_ind_decomp_of_fixed c hSC h12 α lam₀ hα with
      ⟨τ₁, τ₂, hτ₁, hτ₂, hτne, hτsum⟩
    have hspInd1 : scalarProduct (↥c.H0) (extensionChar_ind c hSC α lam₀) μ.1 = 1 := by
      rw [hτsum, scalarProduct_add_left]
      rw [scalarProduct_irr_ite hτ₁ μ.2, scalarProduct_irr_ite hτ₂ μ.2]
      by_cases h1 : τ₁ = μ.1
      · have h2 : τ₂ ≠ μ.1 := fun h2 => hτne (h2.trans h1.symm).symm
        simp [h1, h2]
      · by_cases h2 : τ₂ = μ.1
        · simp [h1, h2]
        · exfalso
          apply hspInd
          rw [hτsum, scalarProduct_add_left]
          rw [scalarProduct_irr_ite hτ₁ μ.2, scalarProduct_irr_ite hτ₂ μ.2]
          simp [h1, h2]
    rcases exists_lambdaHom_extending_lam c h12 lam₀ with ⟨l, hl⟩
    have hΛ : LambdaChar l.1 * extensionChar_ind c hSC α 1 =
        extensionChar_ind c hSC α lam₀ :=
      extensionChar_ind_lambda_mul c hSC h12 α lam₀ l hl
    have hΛ₂ : LambdaChar (lambdaTwo c h12).1 * p = σ₂ :=
      lambdaTwo_mul_sigma1_eq_sigma2_of_fixed c hSC h12 α hα hσp hσ₂ hpne
        (by simpa [lam] using hsum)
    have hΛp_irr : IsIrreducibleCharacter (LambdaChar l.1 * p) :=
      orbit_mem_isIrreducible c.H0 c.U hσp
        (Finset.mem_image.mpr ⟨l, Finset.mem_univ l, rfl⟩)
    have hΛσ₂_irr : IsIrreducibleCharacter (LambdaChar l.1 * σ₂) :=
      orbit_mem_isIrreducible c.H0 c.U hσ₂
        (Finset.mem_image.mpr ⟨l, Finset.mem_univ l, rfl⟩)
    have hΛsum : LambdaChar l.1 * p + LambdaChar l.1 * σ₂ =
        LambdaChar l.1 * extensionChar_ind c hSC α 1 := by
      rw [← mul_add, ← hsum]
    have hspΛ : scalarProduct (↥c.H0) (LambdaChar l.1 * p) μ.1 +
        scalarProduct (↥c.H0) (LambdaChar l.1 * σ₂) μ.1 = 1 := by
      have hsp' : scalarProduct (↥c.H0)
          (LambdaChar l.1 * p + LambdaChar l.1 * σ₂) μ.1 = 1 := by
        rw [hΛsum, hΛ]
        exact hspInd1
      simpa [scalarProduct_add_left] using hsp'
    have hexk : ∃ k : LambdaHom c.H0 c.U, μ.1 = LambdaChar k.1 * p := by
      rw [scalarProduct_irr_ite hΛp_irr μ.2, scalarProduct_irr_ite hΛσ₂_irr μ.2] at hspΛ
      by_cases h1 : LambdaChar l.1 * p = μ.1
      · refine ⟨l, h1.symm⟩
      · by_cases h2 : LambdaChar l.1 * σ₂ = μ.1
        · refine ⟨l * lambdaTwo c h12, ?_⟩
          rw [h2.symm, ← hΛ₂]
          ext x
          simp [LambdaChar, mul_assoc]
        · exfalso
          simp [h1, h2] at hspΛ
    have hμorbit : μ.1 ∈ orbit c.H0 c.U p := by
      rcases hexk with ⟨k, hk⟩
      exact Finset.mem_image.mpr ⟨k, Finset.mem_univ k, hk.symm⟩
    have hLp : L = orbit c.H0 c.U p := by
      rw [hμL]
      exact orbit_eq_of_mem' c hμorbit
    rw [hLp]
    simp [orbitOfAlpha, lam, hα, p]
  · have hInd_irr : IsIrreducibleCharacter (extensionChar_ind c hSC α lam₀) :=
      extensionChar_ind_isIrreducible_of_not_fixed c hSC h12 α lam₀ hα
    have hμeq : μ.1 = extensionChar_ind c hSC α lam₀ := by
      by_contra hne'
      have hz : scalarProduct (↥c.H0) (extensionChar_ind c hSC α lam₀) μ.1 = 0 :=
        scalarProduct_irreducible_orthogonal hInd_irr μ.2 (fun hEq => hne' hEq.symm)
      exact hspInd hz
    rcases exists_lambdaHom_extending_lam c h12 lam₀ with ⟨l, hl⟩
    have hΛ : LambdaChar l.1 * extensionChar_ind c hSC α 1 =
        extensionChar_ind c hSC α lam₀ :=
      extensionChar_ind_lambda_mul c hSC h12 α lam₀ l hl
    have hμorbit : μ.1 ∈ orbit c.H0 c.U (extensionChar_ind c hSC α 1) :=
      Finset.mem_image.mpr ⟨l, Finset.mem_univ l, by
        rw [hμeq, ← hΛ]⟩
    have hLInd : L = orbit c.H0 c.U (extensionChar_ind c hSC α 1) := by
      rw [hμL]
      exact orbit_eq_of_mem' c hμorbit
    rw [hLInd]
    simp [orbitOfAlpha, hα]

/-- Existence and uniqueness in Remark 3.1: a unique `Λ`-orbit `Λ(α)` whose
elements restrict to the sum of the `S0`-conjugates of `α` on `U`. -/
public theorem remark_3_1_exists (c : Hyp11 G) (h12 : Hyp12 c) (hSC : Section3Hyp c)
    [Fintype ↥(LambdaHom c.H0 c.U)] (α : Irr (↥c.U)) :
    ∃! L : Finset (ClassFunction (↥c.H0)),
      (∃ μ : Irr (↥c.H0), L = orbit c.H0 c.U μ.1) ∧
        (∀ ν : ClassFunction (↥c.H0), ν ∈ L →
          restrictU c h12 ν = ∑ α' ∈ s0Orbit c α, α'.1) := by
  refine ⟨orbitOfAlpha c h12 hSC α, orbitOfAlpha_spec c h12 hSC α, ?_⟩
  intro L hL
  exact orbitOfAlpha_unique c h12 hSC α L hL

/-- In the fixed branch (`r0` fixes `α`), the stabilizer of the first
constituent of `Ind_X^{H0}(α̂_1)` in `Λ` is trivial. -/
public lemma stabilizer_fixed_constituent_eq_one (c : Hyp11 G) (h12 : Hyp12 c)
    (hSC : Section3Hyp c) [Fintype ↥(LambdaHom c.H0 c.U)] (α : Irr (↥c.U))
    (hfix : conjIrrS c (c.S0_le_S (S0_generator_mem_S0 c)) α = α)
    {p σ₂ : ClassFunction (↥c.H0)} (hσp : IsIrreducibleCharacter p)
    (hσ₂ : IsIrreducibleCharacter σ₂) (hne : p ≠ σ₂)
    (hsum : extensionChar_ind c hSC α 1 = p + σ₂)
    (l : LambdaHom c.H0 c.U) (hl : LambdaChar l.1 * p = p) : l = 1 := by
  classical
  have hkS : ∀ s : ↥(SPrime c), l.1 ⟨(s : G), SPrime_le_H0 c s.2⟩ = 1 := by
    intro s
    apply Units.ext
    let x : ↥c.H0 := ⟨(s : G), SPrimeMulU_le_H0 c
      (SetLike.le_def.mp (show SPrime c ≤ extensionSubgroup c from le_sup_left) s.2)⟩
    have hval : (l.1 x : ℂ) * p x = p x := by
      have h' := congrFun hl x
      simpa [LambdaChar] using h'
    have hσpin : scalarProduct (↥c.H0) (extensionChar_ind c hSC α 1) p ≠ 0 := by
      rw [hsum, scalarProduct_add_left]
      rw [scalarProduct_irreducible_self hσp]
      rw [scalarProduct_irreducible_orthogonal hσ₂ hσp (fun hEq => hne hEq.symm)]
      norm_num
    have hpx : p x = α.1 1 := by
      have hX := extensionChar_ind_constituent_on_X_of_fixed c hSC h12 α 1 hfix hσp hσpin
        ⟨(s : G), SetLike.le_def.mp (show SPrime c ≤ extensionSubgroup c from le_sup_left) s.2⟩
      have hE : extensionChar c hSC α 1 ⟨(s : G),
          SetLike.le_def.mp (show SPrime c ≤ extensionSubgroup c from le_sup_left) s.2⟩ = α.1 1 := by
        simpa using extensionChar_mul c hSC α 1 (1 : ↥c.U) s
      rw [hX, hE]
    have hcancel : (l.1 x : ℂ) = 1 := by
      rw [hpx] at hval
      have hval' : α.1 1 * (l.1 x : ℂ) = α.1 1 * (1 : ℂ) := by
        rw [mul_comm] at hval
        simpa using hval
      exact mul_left_cancel₀ (irreducible_char_one_ne_zero α.2) hval'
    have hx : x = ⟨(s : G), SPrime_le_H0 c s.2⟩ := by
      apply Subtype.ext
      rfl
    rw [hx] at hcancel
    exact hcancel
  have hsq : l ^ 2 = 1 := lambda_sq_eq_one_of_kills_SPrime c h12 (by
    intro x hx
    simpa using hkS ⟨(x : G), hx⟩)
  rcases lambda_eq_one_or_two_of_sq_one c h12 l hsq with hl1 | hl2
  · exact hl1
  · exfalso
    have hlam₂ : LambdaChar (lambdaTwo c h12).1 * p = σ₂ :=
      lambdaTwo_mul_sigma1_eq_sigma2_of_fixed c hSC h12 α hfix hσp hσ₂ hne hsum
    have hEq : LambdaChar (lambdaTwo c h12).1 * p = p := by
      rw [hl2] at hl
      exact hl
    exact hne (hlam₂.symm.trans hEq).symm

/-- When `r0` moves `α`, the stabilizer of `Ind_X^{H0}(α̂_1)` in `Λ` is
exactly `{1, λ₂}`. -/
public lemma stabilizer_ind_not_fixed_eq_pair (c : Hyp11 G) (h12 : Hyp12 c)
    (hSC : Section3Hyp c) [Fintype ↥(LambdaHom c.H0 c.U)] (α : Irr (↥c.U))
    (hnot : conjIrrS c (c.S0_le_S (S0_generator_mem_S0 c)) α ≠ α) :
    ∀ l : LambdaHom c.H0 c.U,
      LambdaChar l.1 * extensionChar_ind c hSC α 1 = extensionChar_ind c hSC α 1 ↔
        l = 1 ∨ l = lambdaTwo c h12 := by
  intro l
  constructor
  · intro hl
    have hkS : ∀ s : ↥(SPrime c), l.1 ⟨(s : G), SPrime_le_H0 c s.2⟩ = 1 := by
      intro s
      apply Units.ext
      let x : ↥c.H0 := ⟨(s : G), SPrimeMulU_le_H0 c
        (SetLike.le_def.mp (show SPrime c ≤ extensionSubgroup c from le_sup_left) s.2)⟩
      have hval : (l.1 x : ℂ) * extensionChar_ind c hSC α 1 x =
          extensionChar_ind c hSC α 1 x := by
        have h' := congrFun hl x
        simpa [LambdaChar] using h'
      have hInd : extensionChar_ind c hSC α 1 x = 2 * α.1 1 := by
        have hxX : (x : G) ∈ extensionSubgroup c :=
          SetLike.le_def.mp (show SPrime c ≤ extensionSubgroup c from le_sup_left) s.2
        have hsh : (S0_generator c) * (x : G) * (S0_generator c)⁻¹ ∈ extensionSubgroup c :=
          S0_generator_normalizes_extensionSubgroup c hSC ⟨(x : G), hxX⟩
        have hmain := inducedFromSub_eq_add_conj_index_two (extensionSubgroup c) c.H0
          (SPrimeMulU_le_H0 c) (extensionSubgroup_index_two c hSC h12)
          (s := S0_generator c) (S0_generator_mem_H0 c)
          (S0_generator_not_mem_extensionSubgroup c hSC)
          (extensionChar c hSC α 1)
          (isCharacter_isClassFunction (extensionChar_isCharacter c hSC α 1)) hxX hsh
        have h1 : extensionChar c hSC α 1 ⟨(x : G), hxX⟩ = α.1 1 := by
          simpa using extensionChar_mul c hSC α 1 (1 : ↥c.U) s
        have h2 : extensionChar c hSC α 1
            ⟨(S0_generator c) * (x : G) * (S0_generator c)⁻¹, hsh⟩ = α.1 1 := by
          have hEq : (⟨(S0_generator c) * (x : G) * (S0_generator c)⁻¹, hsh⟩ :
                ↥(extensionSubgroup c)) = ⟨(x : G), hxX⟩ := by
            apply Subtype.ext
            have hrS0 : S0_generator c ∈ (c.S0 : Subgroup G) := S0_generator_mem_S0 c
            have hpS0 : (x : G) ∈ (c.S0 : Subgroup G) := SPrime_le_S0 c s.2
            let : IsCyclic ↥(c.S0 : Subgroup G) := c.S0_cyclic
            have hcomm : (S0_generator c) * (x : G) = (x : G) * (S0_generator c) := by
              simpa using congrArg (fun y : ↥(c.S0 : Subgroup G) => (y : G))
                (mul_comm' (⟨S0_generator c, hrS0⟩ : ↥(c.S0 : Subgroup G))
                  ⟨(x : G), hpS0⟩)
            calc
              (S0_generator c) * (x : G) * (S0_generator c)⁻¹
                  = (x : G) * (S0_generator c) * (S0_generator c)⁻¹ := by
                    exact congrArg (fun y : G => y * (S0_generator c)⁻¹) hcomm
              _ = (x : G) := by group
          rw [hEq]
          exact h1
        change @inducedFromSub G _ _ (extensionSubgroup c) c.H0 (SPrimeMulU_le_H0 c)
          (extensionChar c hSC α 1) ⟨(x : G), SPrimeMulU_le_H0 c hxX⟩ = 2 * α.1 1
        rw [hmain, h1, h2]
        ring
      have hcancel : (l.1 x : ℂ) = 1 := by
        rw [hInd] at hval
        have hval' : (2 * α.1 1) * (l.1 x : ℂ) = (2 * α.1 1) * (1 : ℂ) := by
          rw [mul_comm] at hval
          simpa using hval
        exact mul_left_cancel₀ (mul_ne_zero (by norm_num) (irreducible_char_one_ne_zero α.2)) hval'
      have hx : x = ⟨(s : G), SPrime_le_H0 c s.2⟩ := by
        apply Subtype.ext
        rfl
      rw [hx] at hcancel
      exact hcancel
    have hsq : l ^ 2 = 1 := lambda_sq_eq_one_of_kills_SPrime c h12 (by
      intro x hx
      simpa using hkS ⟨(x : G), hx⟩)
    exact lambda_eq_one_or_two_of_sq_one c h12 l hsq
  · intro hl
    rcases hl with rfl | hl2
    · ext x
      simp [LambdaChar]
    · rw [hl2]
      exact extensionChar_ind_lambda_mul c hSC h12 α 1 (lambdaTwo c h12)
        (by
          intro s
          simpa using lambdaTwo_trivial_on_SPrime c h12 ⟨(s : G), SPrime_le_H0 c s.2⟩ s.2)

/-- In the fixed branch the stabilizer of the canonical constituent has size
one. -/
public lemma stabilizer_fixed_constituent_card (c : Hyp11 G) (h12 : Hyp12 c)
    (hSC : Section3Hyp c) [Fintype ↥(LambdaHom c.H0 c.U)] (α : Irr (↥c.U))
    (hfix : conjIrrS c (c.S0_le_S (S0_generator_mem_S0 c)) α = α)
    {p σ₂ : ClassFunction (↥c.H0)} (hσp : IsIrreducibleCharacter p)
    (hσ₂ : IsIrreducibleCharacter σ₂) (hne : p ≠ σ₂)
    (hsum : extensionChar_ind c hSC α 1 = p + σ₂) :
    (Finset.univ.filter (fun s : LambdaHom c.H0 c.U => LambdaChar s.1 * p = p)).card = 1 := by
  classical
  have hsub : (Finset.univ.filter (fun s : LambdaHom c.H0 c.U =>
      LambdaChar s.1 * p = p)) ⊆ {1} := by
    intro l hl
    simp at hl
    exact Finset.mem_singleton.mpr
      (stabilizer_fixed_constituent_eq_one c h12 hSC α hfix hσp hσ₂ hne hsum l hl)
  have hcardle : (Finset.univ.filter (fun s : LambdaHom c.H0 c.U =>
      LambdaChar s.1 * p = p)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    have ha1 : a = 1 := Finset.mem_singleton.mp (hsub ha)
    have hb1 : b = 1 := Finset.mem_singleton.mp (hsub hb)
    rw [ha1, hb1]
  have hmem : (1 : LambdaHom c.H0 c.U) ∈ Finset.univ.filter (fun s : LambdaHom c.H0 c.U =>
      LambdaChar s.1 * p = p) :=
    one_mem_stab c.H0 c.U p
  have hcardge : 1 ≤ (Finset.univ.filter (fun s : LambdaHom c.H0 c.U =>
      LambdaChar s.1 * p = p)).card := by
    exact Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨1, hmem⟩)
  omega

/-- When `r0` moves `α`, the stabilizer of `Ind_X^{H0}(α̂_1)` has size two. -/
public lemma stabilizer_ind_not_fixed_card (c : Hyp11 G) (h12 : Hyp12 c)
    (hSC : Section3Hyp c) [Fintype ↥(LambdaHom c.H0 c.U)] (α : Irr (↥c.U))
    (hnot : conjIrrS c (c.S0_le_S (S0_generator_mem_S0 c)) α ≠ α) :
    (Finset.univ.filter (fun s : LambdaHom c.H0 c.U =>
      LambdaChar s.1 * extensionChar_ind c hSC α 1 = extensionChar_ind c hSC α 1)).card = 2 := by
  classical
  let F := Finset.univ.filter (fun s : LambdaHom c.H0 c.U =>
    LambdaChar s.1 * extensionChar_ind c hSC α 1 = extensionChar_ind c hSC α 1)
  have hsub : F ⊆ ({1, lambdaTwo c h12} : Finset (LambdaHom c.H0 c.U)) := by
    intro l hl
    simp [F] at hl
    simpa using (stabilizer_ind_not_fixed_eq_pair c h12 hSC α hnot l).mp hl
  have hsub' : ({1, lambdaTwo c h12} : Finset (LambdaHom c.H0 c.U)) ⊆ F := by
    intro l hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      ext x
      simp [LambdaChar]
    · simp [F, extensionChar_ind_lambda_mul c hSC h12 α 1 (lambdaTwo c h12) (by
        intro s
        simpa using lambdaTwo_trivial_on_SPrime c h12 ⟨(s : G), SPrime_le_H0 c s.2⟩ s.2)]
  have hcard2' : ({1, lambdaTwo c h12} : Finset (LambdaHom c.H0 c.U)).card = 2 := by
    rw [Finset.card_insert_of_notMem]
    · simp
    · intro h
      exact (lambdaTwo_ne_one c h12) (Finset.mem_singleton.mp h).symm
  have hpair_eq : ({1, lambdaTwo c h12} : Finset (LambdaHom c.H0 c.U)) = F :=
    Finset.eq_of_subset_of_card_le hsub'
      (by simpa [hcard2'] using (Finset.card_le_card hsub))
  have hEq : F = ({1, lambdaTwo c h12} : Finset (LambdaHom c.H0 c.U)) := hpair_eq.symm
  change F.card = 2
  rw [hEq, hcard2']

/-- `|Λ(α)| = m/n`, where `n` is the number of `S0`-conjugates of `α`. -/
public theorem orbitOfAlpha_card (c : Hyp11 G) (h12 : Hyp12 c) (hSC : Section3Hyp c)
    [Fintype ↥(LambdaHom c.H0 c.U)] (α : Irr (↥c.U)) :
    (orbitOfAlpha c h12 hSC α).card =
      (c.U.subgroupOf c.H0).index / (s0Orbit c α).card := by
  classical
  let lam : ↥(SPrime c) →* ℂˣ := 1
  have hΛ : Fintype.card (LambdaHom c.H0 c.U) = (c.U.subgroupOf c.H0).index := by
    simpa using lambda_card_eq_index c h12
  by_cases hα : conjIrrS c (c.S0_le_S (S0_generator_mem_S0 c)) α = α
  · have hcard1 : (s0Orbit c α).card = 1 := by
      rw [s0Orbit_eq_singleton_of_fixed c hSC α hα]
      simp
    let p : ClassFunction (↥c.H0) :=
      Classical.choose (extensionChar_ind_decomp_of_fixed c hSC h12 α lam hα)
    have hp : ∃ σ₂, IsIrreducibleCharacter p ∧ IsIrreducibleCharacter σ₂ ∧ p ≠ σ₂ ∧
        extensionChar_ind c hSC α lam = p + σ₂ :=
      Classical.choose_spec (extensionChar_ind_decomp_of_fixed c hSC h12 α lam hα)
    rcases hp with ⟨σ₂, hσp, hσ₂, hne, hsum⟩
    have horbit : (orbitOfAlpha c h12 hSC α).card = (orbit c.H0 c.U p).card := by
      simp [orbitOfAlpha, lam, hα, p]
    have hstab : (Finset.univ.filter (fun s : LambdaHom c.H0 c.U =>
        LambdaChar s.1 * p = p)).card = 1 := by
      have hsub : (Finset.univ.filter (fun s : LambdaHom c.H0 c.U =>
          LambdaChar s.1 * p = p)) ⊆ {1} := by
        intro l hl
        simp at hl
        exact Finset.mem_singleton.mpr
          (stabilizer_fixed_constituent_eq_one c h12 hSC α hα hσp hσ₂ hne
            (by simpa [lam] using hsum) l hl)
      have hcardle : (Finset.univ.filter (fun s : LambdaHom c.H0 c.U =>
          LambdaChar s.1 * p = p)).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro a ha b hb
        have ha1 : a = 1 := Finset.mem_singleton.mp (hsub ha)
        have hb1 : b = 1 := Finset.mem_singleton.mp (hsub hb)
        rw [ha1, hb1]
      have hmem : (1 : LambdaHom c.H0 c.U) ∈ Finset.univ.filter (fun s : LambdaHom c.H0 c.U =>
          LambdaChar s.1 * p = p) :=
        one_mem_stab c.H0 c.U p
      have hcardge : 1 ≤ (Finset.univ.filter (fun s : LambdaHom c.H0 c.U =>
          LambdaChar s.1 * p = p)).card := by
        exact Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨1, hmem⟩)
      omega
    have hmain := orbit_card_mul_stab c.H0 c.U p
    have hcard : (orbit c.H0 c.U p).card = (c.U.subgroupOf c.H0).index := by
      have hm : (orbit c.H0 c.U p).card * 1 = (c.U.subgroupOf c.H0).index := by
        rw [← hstab, hmain, hΛ]
      simpa using hm
    rw [horbit, hcard, hcard1]
    simp
  · have hcard2 : (s0Orbit c α).card = 2 := by
      rw [s0Orbit_eq_pair_of_not_fixed c hSC α hα]
      rw [Finset.card_insert_of_notMem]
      · simp
      · intro hEq
        have hfixinv : conjIrrS c (c.S0_le_S ((c.S0 : Subgroup G).inv_mem
            (S0_generator_mem_S0 c))) α = α := (Finset.mem_singleton.mp hEq).symm
        exact hα ((conjIrrS_r0_fixed_iff_r0_inv c α).mpr hfixinv)
    have horbit : (orbitOfAlpha c h12 hSC α).card =
        (orbit c.H0 c.U (extensionChar_ind c hSC α 1)).card := by
      simp [orbitOfAlpha, hα]
    have hstab : (Finset.univ.filter (fun s : LambdaHom c.H0 c.U =>
        LambdaChar s.1 * extensionChar_ind c hSC α 1 = extensionChar_ind c hSC α 1)).card = 2 := by
      let F := Finset.univ.filter (fun s : LambdaHom c.H0 c.U =>
        LambdaChar s.1 * extensionChar_ind c hSC α 1 = extensionChar_ind c hSC α 1)
      have hsub : F ⊆ ({1, lambdaTwo c h12} : Finset (LambdaHom c.H0 c.U)) := by
        intro l hl
        simp [F] at hl
        simpa using (stabilizer_ind_not_fixed_eq_pair c h12 hSC α hα l).mp hl
      have hsub' : ({1, lambdaTwo c h12} : Finset (LambdaHom c.H0 c.U)) ⊆ F := by
        intro l hl
        simp only [Finset.mem_insert, Finset.mem_singleton] at hl
        rcases hl with rfl | rfl
        · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          ext x
          simp [LambdaChar]
        · simp [F, extensionChar_ind_lambda_mul c hSC h12 α 1 (lambdaTwo c h12) (by
            intro s
            simpa using lambdaTwo_trivial_on_SPrime c h12 ⟨(s : G), SPrime_le_H0 c s.2⟩ s.2)]
      have hcard2' : ({1, lambdaTwo c h12} : Finset (LambdaHom c.H0 c.U)).card = 2 := by
        rw [Finset.card_insert_of_notMem]
        · simp
        · intro h
          exact (lambdaTwo_ne_one c h12) (Finset.mem_singleton.mp h).symm
      have hpair_eq : ({1, lambdaTwo c h12} : Finset (LambdaHom c.H0 c.U)) = F :=
        Finset.eq_of_subset_of_card_le hsub'
          (by simpa [hcard2'] using (Finset.card_le_card hsub))
      have hEq : F = ({1, lambdaTwo c h12} : Finset (LambdaHom c.H0 c.U)) := hpair_eq.symm
      change F.card = 2
      rw [hEq, hcard2']
    have hmain := orbit_card_mul_stab c.H0 c.U (extensionChar_ind c hSC α 1)
    have hcard : (orbit c.H0 c.U (extensionChar_ind c hSC α 1)).card =
        (c.U.subgroupOf c.H0).index / 2 := by
      have hm : (orbit c.H0 c.U (extensionChar_ind c hSC α 1)).card * 2 =
          (c.U.subgroupOf c.H0).index := by
        rw [← hstab, hmain, hΛ]
      rw [← hm]
      symm
      rw [mul_comm]
      exact Nat.mul_div_right (orbit c.H0 c.U (extensionChar_ind c hSC α 1)).card
        (by norm_num : 0 < 2)
    rw [horbit, hcard, hcard2]

/-- `Σ_{ν∈Λ(α)} ν(1) = m·α(1)`. -/
public theorem orbitOfAlpha_degree_sum (c : Hyp11 G) (h12 : Hyp12 c) (hSC : Section3Hyp c)
    [Fintype ↥(LambdaHom c.H0 c.U)] (α : Irr (↥c.U)) :
    (∑ ν ∈ orbitOfAlpha c h12 hSC α, ν 1) =
      ((c.U.subgroupOf c.H0).index : ℂ) * α.1 1 := by
  classical
  let lam : ↥(SPrime c) →* ℂˣ := 1
  have hΛ : Fintype.card (LambdaHom c.H0 c.U) = (c.U.subgroupOf c.H0).index := by
    simpa using lambda_card_eq_index c h12
  by_cases hα : conjIrrS c (c.S0_le_S (S0_generator_mem_S0 c)) α = α
  · let p : ClassFunction (↥c.H0) :=
      Classical.choose (extensionChar_ind_decomp_of_fixed c hSC h12 α lam hα)
    have hp : ∃ σ₂, IsIrreducibleCharacter p ∧ IsIrreducibleCharacter σ₂ ∧ p ≠ σ₂ ∧
        extensionChar_ind c hSC α lam = p + σ₂ :=
      Classical.choose_spec (extensionChar_ind_decomp_of_fixed c hSC h12 α lam hα)
    rcases hp with ⟨σ₂, hσp, hσ₂, hne, hsum⟩
    have hstab1 : (Finset.univ.filter (fun s : LambdaHom c.H0 c.U =>
        LambdaChar s.1 * p = p)).card = 1 :=
      stabilizer_fixed_constituent_card c h12 hSC α hα hσp hσ₂ hne (by simpa [lam] using hsum)
    have hσpin : scalarProduct (↥c.H0) (extensionChar_ind c hSC α 1) p ≠ 0 := by
      rw [hsum, scalarProduct_add_left]
      rw [scalarProduct_irreducible_self hσp]
      rw [scalarProduct_irreducible_orthogonal hσ₂ hσp (fun hEq => hne hEq.symm)]
      norm_num
    have hp1 : p 1 = α.1 1 := by
      have hrest := extensionChar_ind_constituent_restrict_of_fixed c hSC h12 α 1 hα hσp hσpin
      have hv := congrFun hrest (1 : ↥c.U)
      change p ⟨(1 : G), (h12.U_normal_in_H0).1 (1 : ↥c.U).2⟩ = α.1 1
      exact hv
    have hsumAll := orbitSumAll_eq_card_stab c.H0 c.U p 1
    have hLHS : orbitSumAll c.H0 c.U p 1 = (Fintype.card (LambdaHom c.H0 c.U) : ℂ) * p 1 := by
      simp [orbitSumAll]
    have hsumOrbit : (∑ ν ∈ orbit c.H0 c.U p, ν 1) = ((orbit c.H0 c.U p).card : ℂ) * p 1 := by
      have hsumAll' : orbitSumAll c.H0 c.U p 1 = (1 : ℂ) * orbitSum c.H0 c.U p 1 := by
        rw [hsumAll, hstab1]
        norm_num
      have hΛcard : Fintype.card (LambdaHom c.H0 c.U) = (orbit c.H0 c.U p).card := by
        rw [← orbit_card_mul_stab c.H0 c.U p, hstab1]
        simp
      calc
        orbitSum c.H0 c.U p 1 = orbitSumAll c.H0 c.U p 1 := by
              rw [hsumAll']
              ring
        _ = (Fintype.card (LambdaHom c.H0 c.U) : ℂ) * p 1 := hLHS
        _ = ((orbit c.H0 c.U p).card : ℂ) * p 1 := by rw [hΛcard]
    have horbit : orbitOfAlpha c h12 hSC α = orbit c.H0 c.U p := by
      simp [orbitOfAlpha, lam, hα, p]
    have hcard : ((orbit c.H0 c.U p).card : ℂ) = ((c.U.subgroupOf c.H0).index : ℂ) := by
      have hcard1 : (s0Orbit c α).card = 1 := by
        rw [s0Orbit_eq_singleton_of_fixed c hSC α hα]
        simp
      have hc := orbitOfAlpha_card c h12 hSC α
      rw [hcard1, horbit] at hc
      norm_num at hc
      exact_mod_cast hc
    rw [horbit]
    rw [hsumOrbit, hcard, hp1]
  · have hInd1 : extensionChar_ind c hSC α 1 1 = 2 * α.1 1 := by
      have hxX : (1 : G) ∈ extensionSubgroup c := (extensionSubgroup c).one_mem
      have hsh : (S0_generator c) * (1 : G) * (S0_generator c)⁻¹ ∈ extensionSubgroup c := by
        simpa using S0_generator_normalizes_extensionSubgroup c hSC (1 : ↥(extensionSubgroup c))
      have hmain := inducedFromSub_eq_add_conj_index_two (extensionSubgroup c) c.H0
        (SPrimeMulU_le_H0 c) (extensionSubgroup_index_two c hSC h12)
        (s := S0_generator c) (S0_generator_mem_H0 c)
        (S0_generator_not_mem_extensionSubgroup c hSC)
        (extensionChar c hSC α 1)
        (isCharacter_isClassFunction (extensionChar_isCharacter c hSC α 1)) hxX hsh
      have h1 : extensionChar c hSC α 1
          ⟨(1 : G), SetLike.le_def.mp (show c.U ≤ extensionSubgroup c from le_sup_right)
            (1 : ↥c.U).2⟩ = α.1 1 :=
        extensionChar_restrict c hSC α 1 (1 : ↥c.U)
      have h2 : extensionChar c hSC α 1
          ⟨(S0_generator c) * (1 : G) * (S0_generator c)⁻¹, hsh⟩ = α.1 1 := by
        have hEq : (⟨(S0_generator c) * (1 : G) * (S0_generator c)⁻¹, hsh⟩ :
              ↥(extensionSubgroup c)) = (1 : ↥(extensionSubgroup c)) := by
          apply Subtype.ext
          simp
        rw [hEq]
        exact h1
      change @inducedFromSub G _ _ (extensionSubgroup c) c.H0 (SPrimeMulU_le_H0 c)
        (extensionChar c hSC α 1) ⟨(1 : G), SPrimeMulU_le_H0 c hxX⟩ = 2 * α.1 1
      rw [hmain]
      simp [h1, h2]
      ring
    have hstab2 : (Finset.univ.filter (fun s : LambdaHom c.H0 c.U =>
        LambdaChar s.1 * extensionChar_ind c hSC α 1 = extensionChar_ind c hSC α 1)).card = 2 :=
      stabilizer_ind_not_fixed_card c h12 hSC α hα
    have hsumAll := orbitSumAll_eq_card_stab c.H0 c.U (extensionChar_ind c hSC α 1) 1
    have hLHS : orbitSumAll c.H0 c.U (extensionChar_ind c hSC α 1) 1 =
        (Fintype.card (LambdaHom c.H0 c.U) : ℂ) * extensionChar_ind c hSC α 1 1 := by
      simp [orbitSumAll]
    have hsumOrbit : (∑ ν ∈ orbit c.H0 c.U (extensionChar_ind c hSC α 1), ν 1) =
        ((orbit c.H0 c.U (extensionChar_ind c hSC α 1)).card : ℂ) *
          extensionChar_ind c hSC α 1 1 := by
      have hsumAll' : orbitSumAll c.H0 c.U (extensionChar_ind c hSC α 1) 1 =
          (2 : ℂ) * orbitSum c.H0 c.U (extensionChar_ind c hSC α 1) 1 := by
        rw [hsumAll, hstab2]
        norm_num
      have hΛcard : Fintype.card (LambdaHom c.H0 c.U) =
          (orbit c.H0 c.U (extensionChar_ind c hSC α 1)).card * 2 := by
        rw [← orbit_card_mul_stab c.H0 c.U (extensionChar_ind c hSC α 1), hstab2]
      have hcancel : (2 : ℂ) ≠ 0 := by norm_num
      have hmain : (2 : ℂ) * orbitSum c.H0 c.U (extensionChar_ind c hSC α 1) 1 =
          (2 : ℂ) * (((orbit c.H0 c.U (extensionChar_ind c hSC α 1)).card : ℂ) *
            extensionChar_ind c hSC α 1 1) := by
        calc
          (2 : ℂ) * orbitSum c.H0 c.U (extensionChar_ind c hSC α 1) 1
              = orbitSumAll c.H0 c.U (extensionChar_ind c hSC α 1) 1 := by
                    rw [hsumAll']
          _ = (Fintype.card (LambdaHom c.H0 c.U) : ℂ) * extensionChar_ind c hSC α 1 1 := hLHS
          _ = (((orbit c.H0 c.U (extensionChar_ind c hSC α 1)).card * 2 : ℕ) : ℂ) *
                extensionChar_ind c hSC α 1 1 := by
                    rw [← hΛcard]
          _ = (2 : ℂ) * (((orbit c.H0 c.U (extensionChar_ind c hSC α 1)).card : ℂ) *
                extensionChar_ind c hSC α 1 1) := by
                    rw [Nat.cast_mul]
                    ring
      exact mul_left_cancel₀ hcancel hmain
    have horbit : orbitOfAlpha c h12 hSC α = orbit c.H0 c.U (extensionChar_ind c hSC α 1) := by
      simp [orbitOfAlpha, hα]
    have hcard2 : (s0Orbit c α).card = 2 := by
      rw [s0Orbit_eq_pair_of_not_fixed c hSC α hα]
      rw [Finset.card_insert_of_notMem]
      · simp
      · intro hEq
        have hfixinv : conjIrrS c (c.S0_le_S ((c.S0 : Subgroup G).inv_mem
            (S0_generator_mem_S0 c))) α = α := (Finset.mem_singleton.mp hEq).symm
        exact hα ((conjIrrS_r0_fixed_iff_r0_inv c α).mpr hfixinv)
    have hcard : ((orbit c.H0 c.U (extensionChar_ind c hSC α 1)).card : ℂ) =
        (((c.U.subgroupOf c.H0).index / 2 : ℕ) : ℂ) := by
      have hc := orbitOfAlpha_card c h12 hSC α
      rw [hcard2, horbit] at hc
      exact_mod_cast hc
    have hdiv : ((c.U.subgroupOf c.H0).index / 2 : ℕ) * 2 =
        (c.U.subgroupOf c.H0).index := by
      have hc' : (orbit c.H0 c.U (extensionChar_ind c hSC α 1)).card =
          (c.U.subgroupOf c.H0).index / 2 := by
        have hc := orbitOfAlpha_card c h12 hSC α
        rw [hcard2, horbit] at hc
        exact hc
      have hm : (orbit c.H0 c.U (extensionChar_ind c hSC α 1)).card * 2 =
          (c.U.subgroupOf c.H0).index := by
        rw [← hstab2, orbit_card_mul_stab c.H0 c.U (extensionChar_ind c hSC α 1), hΛ]
      rw [← hc']
      exact hm
    rw [horbit]
    rw [hsumOrbit, hcard, hInd1]
    calc
      (((c.U.subgroupOf c.H0).index / 2 : ℕ) : ℂ) * (2 * α.1 1)
          = ((((c.U.subgroupOf c.H0).index / 2 : ℕ) * 2 : ℕ) : ℂ) * α.1 1 := by
            rw [show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num]
            rw [← mul_assoc]
            rw [← Nat.cast_mul]
      _ = ((c.U.subgroupOf c.H0).index : ℂ) * α.1 1 := by
            rw [hdiv]

/-- `α` lies in its own `S0`-orbit. -/
private lemma s0Orbit_self_mem (c : Hyp11 G) (α : Irr (↥c.U)) :
    α ∈ s0Orbit c α := by
  refine Finset.mem_image.mpr ⟨(1 : ↥(c.S0 : Subgroup G)), Finset.mem_univ _, ?_⟩
  exact conjIrrS_one c α

/-- Restriction commutes with conjugation by `s`. -/
private lemma restrictU_conjChar (c : Hyp11 G) (h12 : Hyp12 c)
    (ν : ClassFunction (↥c.H0)) :
    restrictU c h12 (conjChar c.H0 (s_normalizes_H0 c h12) ν) =
      conjChar c.U (fun x : ↥c.U => S_normalizes_U c c.s c.s_mem_S x.1 x.2)
        (restrictU c h12 ν) := by
  funext u
  simp [restrictU, conjChar, conjMonoidHom, conjIrrS]

/-- The scalar product of an orbit-sum of irreducibles with one of its
members is `1`. -/
private lemma scalarProduct_sum_self_mem {G : Type u} [Group G] [Fintype G]
    {s : Finset (Irr G)} {β : Irr G} (hβ : β ∈ s) :
    scalarProduct G (∑ γ ∈ s, γ.1) β.1 = 1 := by
  classical
  rw [← Finset.sum_coe_sort]
  change scalarProduct G (∑ γ : s, (γ : Irr G).1) β.1 = 1
  rw [scalarProduct_sum_left (f := fun γ : s => (γ : Irr G).1)]
  rw [Finset.sum_coe_sort (s := s)
    (f := fun γ : Irr G => scalarProduct G γ.1 β.1)]
  rw [Finset.sum_eq_single (s := s) (a := β)
    (f := fun b : Irr G => scalarProduct G b.1 β.1)]
  · exact scalarProduct_irreducible_self β.2
  · intro b hb hbβ
    exact scalarProduct_irreducible_orthogonal b.2 β.2 (by
      intro hEq
      exact hbβ (Subtype.ext hEq))
  · intro hnot
    exact (hnot hβ).elim

/-- If a sum of irreducibles equals a single irreducible, every member of
the sum is that irreducible. -/
private lemma mem_of_sum_eq_irr {G : Type u} [Group G] [Fintype G]
    {s : Finset (Irr G)} {α β : Irr G} (hβ : β ∈ s)
    (hsum : (∑ γ ∈ s, γ.1) = α.1) : β = α := by
  classical
  have hsp : scalarProduct G (∑ γ ∈ s, γ.1) β.1 = 1 :=
    scalarProduct_sum_self_mem hβ
  have hsp' : scalarProduct G α.1 β.1 = 1 := by
    rw [hsum] at hsp
    exact hsp
  by_contra hne
  have h0 : scalarProduct G α.1 β.1 = 0 :=
    scalarProduct_irreducible_orthogonal α.2 β.2 (by
      intro hEq
      exact hne (Subtype.ext hEq.symm))
  rw [hsp'] at h0
  norm_num at h0

/-- If a sum of irreducibles equals a sum of two distinct irreducibles,
every member of the sum is one of the two. -/
private lemma mem_pair_of_sum_eq_pair (c : Hyp11 G) {s : Finset (Irr (↥c.U))}
    {a b β : Irr (↥c.U)} (hne : a ≠ b) (hβ : β ∈ s)
    (hsum : (∑ γ ∈ s, γ.1) = a.1 + b.1) : β = a ∨ β = b := by
  classical
  have hsp1 : scalarProduct (↥c.U) (∑ γ ∈ s, γ.1) β.1 = 1 := by
    exact scalarProduct_sum_self_mem hβ
  have hspR : scalarProduct (↥c.U) (a.1 + b.1) β.1 = 1 := by
    rw [← hsum]
    exact hsp1
  by_cases ha : β = a
  · exact Or.inl ha
  · by_cases hb : β = b
    · exact Or.inr hb
    · have hneA : a.1 ≠ β.1 := by
        intro hEq
        exact ha (Subtype.ext hEq.symm)
      have hneB : b.1 ≠ β.1 := by
        intro hEq
        exact hb (Subtype.ext hEq.symm)
      have h0 : scalarProduct (↥c.U) (a.1 + b.1) β.1 = 0 := by
        rw [scalarProduct_add_left]
        rw [scalarProduct_irr_ite a.2 β.2, scalarProduct_irr_ite b.2 β.2]
        simp [hneA, hneB]
      rw [hspR] at h0
      norm_num at h0

/-- Conjugating the `S0`-orbit sum of `α` by `s` gives the `S0`-orbit sum
of `α^s`. -/
private lemma s0Orbit_conjIrrS (c : Hyp11 G) (hSC : Section3Hyp c)
    (α : Irr (↥c.U)) :
    conjChar c.U (fun x : ↥c.U => S_normalizes_U c c.s c.s_mem_S x.1 x.2)
        (∑ β ∈ s0Orbit c α, β.1) =
      ∑ β ∈ s0Orbit c (conjIrrS c c.s_mem_S α), β.1 := by
  classical
  let hs : ∀ x : ↥c.U, c.s * (x : G) * c.s⁻¹ ∈ c.U :=
    fun x => S_normalizes_U c c.s c.s_mem_S x.1 x.2
  let f : Irr (↥c.U) → Irr (↥c.U) := fun β => conjIrrS c c.s_mem_S β
  have hInj : Set.InjOn f ↑(s0Orbit c α) := by
    intro β hβ γ hγ hEq
    exact conjIrrS_injective c c.s_mem_S hEq
  have himage : (s0Orbit c α).image f = s0Orbit c (conjIrrS c c.s_mem_S α) := by
    ext γ
    constructor
    · intro hγ
      rcases Finset.mem_image.mp hγ with ⟨β, hβ, rfl⟩
      rcases Finset.mem_image.mp hβ with ⟨g, hg, rfl⟩
      have hconj : c.s⁻¹ * (g : G) * c.s ∈ (c.S0 : Subgroup G) := by
        simpa using S_conj_mem_S0 c ((c.S : Subgroup G).inv_mem c.s_mem_S) g.2
      have hgS : (g : G) ∈ (c.S : Subgroup G) := c.S0_le_S g.2
      have hconjS : c.s⁻¹ * (g : G) * c.s ∈ (c.S : Subgroup G) :=
        c.S0_le_S hconj
      refine Finset.mem_image.mpr
        ⟨⟨c.s⁻¹ * (g : G) * c.s, hconj⟩, Finset.mem_univ _, ?_⟩
      change conjIrrS c hconjS (conjIrrS c c.s_mem_S α) = f (conjIrrS c hgS α)
      calc
        conjIrrS c hconjS (conjIrrS c c.s_mem_S α)
            = conjIrrS c ((c.S : Subgroup G).mul_mem c.s_mem_S hconjS) α := by
              exact (conjIrrS_mul c c.s_mem_S hconjS α).symm
        _ = conjIrrS c ((c.S : Subgroup G).mul_mem
              hgS c.s_mem_S) α := by
              congr 1
              group
        _ = f (conjIrrS c hgS α) :=
              conjIrrS_mul c hgS c.s_mem_S α
    · intro hγ
      rcases Finset.mem_image.mp hγ with ⟨g, hg, rfl⟩
      have hconj : c.s * (g : G) * c.s⁻¹ ∈ (c.S0 : Subgroup G) :=
        S_conj_mem_S0 c c.s_mem_S g.2
      have hgS : (g : G) ∈ (c.S : Subgroup G) := c.S0_le_S g.2
      have hconjS : c.s * (g : G) * c.s⁻¹ ∈ (c.S : Subgroup G) :=
        c.S0_le_S hconj
      refine Finset.mem_image.mpr
        ⟨conjIrrS c hconjS α, ?_, ?_⟩
      · exact Finset.mem_image.mpr
          ⟨⟨c.s * (g : G) * c.s⁻¹, hconj⟩, Finset.mem_univ _, rfl⟩
      · change f (conjIrrS c hconjS α) = conjIrrS c hgS (conjIrrS c c.s_mem_S α)
        calc
          f (conjIrrS c hconjS α)
              = conjIrrS c ((c.S : Subgroup G).mul_mem hconjS c.s_mem_S) α := by
                  exact (conjIrrS_mul c hconjS c.s_mem_S α).symm
          _ = conjIrrS c ((c.S : Subgroup G).mul_mem c.s_mem_S hgS) α := by
                  congr 1
                  group
          _ = conjIrrS c hgS (conjIrrS c c.s_mem_S α) :=
                  conjIrrS_mul c c.s_mem_S hgS α
  funext u
  simp [conjChar, conjMonoidHom]
  change (∑ β ∈ s0Orbit c α, (f β).1 u) =
    ∑ β ∈ s0Orbit c (conjIrrS c c.s_mem_S α), β.1 u
  rw [← himage, Finset.sum_image hInj]

/-- If conjugation by `s` fixes the `S0`-orbit sum of `α`, then `α^s` lies
in that orbit. -/
private lemma sα_mem_s0Orbit_of_sum_fixed (c : Hyp11 G) (hSC : Section3Hyp c)
    (α : Irr (↥c.U))
    (hfix : conjChar c.U (fun x : ↥c.U => S_normalizes_U c c.s c.s_mem_S x.1 x.2)
        (∑ β ∈ s0Orbit c α, β.1) =
      ∑ β ∈ s0Orbit c α, β.1) :
    conjIrrS c c.s_mem_S α ∈ s0Orbit c α := by
  classical
  have hsum' : (∑ β ∈ s0Orbit c (conjIrrS c c.s_mem_S α), β.1) =
      ∑ β ∈ s0Orbit c α, β.1 := by
    rw [← s0Orbit_conjIrrS c hSC α]
    exact hfix
  by_cases hα : conjIrrS c (c.S0_le_S (S0_generator_mem_S0 c)) α = α
  · have horb : s0Orbit c α = {α} := s0Orbit_eq_singleton_of_fixed c hSC α hα
    have hsumα : (∑ β ∈ s0Orbit c (conjIrrS c c.s_mem_S α), β.1) = α.1 := by
      rw [hsum', horb]
      simp
    have hEq : conjIrrS c c.s_mem_S α = α :=
      mem_of_sum_eq_irr (s0Orbit_self_mem c (conjIrrS c c.s_mem_S α)) hsumα
    rw [hEq, horb]
    exact Finset.mem_singleton.mpr rfl
  · let β : Irr (↥c.U) := conjIrrS c
      (c.S0_le_S ((c.S0 : Subgroup G).inv_mem (S0_generator_mem_S0 c))) α
    have horb : s0Orbit c α =
        ({α, β} : Finset (Irr (↥c.U))) :=
      s0Orbit_eq_pair_of_not_fixed c hSC α hα
    have hβne : α ≠ β := by
      intro hEq
      apply hα
      have hfixinv : conjIrrS c
          (c.S0_le_S ((c.S0 : Subgroup G).inv_mem (S0_generator_mem_S0 c))) α = α := by
        simpa [β] using hEq.symm
      exact (conjIrrS_r0_fixed_iff_r0_inv c α).mpr hfixinv
    have hsumPair : (∑ γ ∈ s0Orbit c (conjIrrS c c.s_mem_S α), γ.1) = α.1 + β.1 := by
      rw [hsum', horb]
      exact Finset.sum_pair hβne
    rcases mem_pair_of_sum_eq_pair c hβne
      (s0Orbit_self_mem c (conjIrrS c c.s_mem_S α)) hsumPair with hEq | hEq
    · rw [hEq, horb]
      simp
    · rw [hEq, horb]
      simp

/-- If `α^s` lies in the `S0`-orbit of `α`, then `S_α` is not contained in
`S0`. -/
private lemma stabilizerS_not_le_S0_of_sα_mem (c : Hyp11 G) (α : Irr (↥c.U))
    (h : conjIrrS c c.s_mem_S α ∈ s0Orbit c α) :
    ¬ stabilizerS c α ≤ (c.S0 : Subgroup G) := by
  rcases Finset.mem_image.mp h with ⟨r, hr, hEq⟩
  let x : G := c.s * (r : G)⁻¹
  have hxS : x ∈ (c.S : Subgroup G) := by
    exact (c.S : Subgroup G).mul_mem c.s_mem_S
      ((c.S : Subgroup G).inv_mem (c.S0_le_S r.2))
  have hrInv : (r : G)⁻¹ ∈ (c.S : Subgroup G) :=
    (c.S : Subgroup G).inv_mem (c.S0_le_S r.2)
  have hfix : conjIrrS c hxS α = α := by
    have hmain : conjIrrS c ((c.S : Subgroup G).mul_mem c.s_mem_S hrInv) α =
        conjIrrS c hrInv (conjIrrS c c.s_mem_S α) :=
      conjIrrS_mul c c.s_mem_S hrInv α
    have hEq' : conjIrrS c hrInv (conjIrrS c c.s_mem_S α) = α := by
      rw [← hEq]
      exact conjIrrS_inv c (c.S0_le_S r.2) α
    exact hmain.trans hEq'
  have hxStab : x ∈ stabilizerS c α := ⟨hxS, hfix⟩
  have hxnotS0 : x ∉ (c.S0 : Subgroup G) := by
    intro hxS0
    have hmem : c.s ∈ (c.S0 : Subgroup G) := by
      have hprod : c.s = x * (r : G) := by
        dsimp [x]
        group
      rw [hprod]
      exact (c.S0 : Subgroup G).mul_mem hxS0 r.2
    exact c.s_not_mem_S0 hmem
  intro hle
  exact hxnotS0 (hle hxStab)

/-- If `S_α` is not contained in `S0`, then `α^s` lies in the `S0`-orbit
of `α`. -/
private lemma sα_mem_s0Orbit_of_stabilizerS_not_le_S0 (c : Hyp11 G)
    (α : Irr (↥c.U)) (h : ¬ stabilizerS c α ≤ (c.S0 : Subgroup G)) :
    conjIrrS c c.s_mem_S α ∈ s0Orbit c α := by
  classical
  have hx : ∃ x : G, x ∈ stabilizerS c α ∧ x ∉ (c.S0 : Subgroup G) := by
    by_contra hnone
    apply h
    intro x hx
    by_contra hxS0
    exact hnone ⟨x, hx, hxS0⟩
  rcases hx with ⟨x, hxStab, hxS0⟩
  rcases hxStab with ⟨hxS, hfix⟩
  let K : Subgroup (↥(c.S : Subgroup G)) :=
    (c.S0 : Subgroup G).subgroupOf (c.S : Subgroup G)
  have hK : K.index = 2 := S0_index c
  let a : ↥(c.S : Subgroup G) := ⟨c.s, c.s_mem_S⟩
  let b : ↥(c.S : Subgroup G) := ⟨x, hxS⟩
  have hiff := Subgroup.mul_mem_iff_of_index_two hK (a := a) (b := b)
  have haK : a ∉ K := by
    intro ha
    exact c.s_not_mem_S0 (Subgroup.mem_subgroupOf.mp ha)
  have hbK : b ∉ K := by
    intro hb
    exact hxS0 (Subgroup.mem_subgroupOf.mp hb)
  have habK : a * b ∈ K := by
    rw [hiff]
    simp [haK, hbK]
  have hrS0 : c.s * x ∈ (c.S0 : Subgroup G) := Subgroup.mem_subgroupOf.mp habK
  let r : ↥(c.S0 : Subgroup G) := ⟨c.s * x, hrS0⟩
  have hxeq : x = c.s * (r : G) := by
    dsimp [r]
    have hs2 : c.s * c.s = 1 := by simpa [pow_two] using c.s_involution.2
    have hxx : c.s * (c.s * x) = x := by
      calc
        c.s * (c.s * x) = (c.s * c.s) * x := by group
        _ = x := by rw [hs2]; simp
    exact hxx.symm
  have hfix' : conjIrrS c ((c.S : Subgroup G).mul_mem c.s_mem_S (c.S0_le_S r.2)) α = α := by
    simpa [hxeq] using hfix
  have hrInv : (r : G)⁻¹ ∈ (c.S : Subgroup G) :=
    (c.S : Subgroup G).inv_mem (c.S0_le_S r.2)
  have hright : conjIrrS c hrInv
      (conjIrrS c ((c.S : Subgroup G).mul_mem c.s_mem_S (c.S0_le_S r.2)) α) =
      conjIrrS c hrInv α := by
    rw [hfix']
  have hmain : conjIrrS c c.s_mem_S α = conjIrrS c hrInv α := by
    calc
      conjIrrS c c.s_mem_S α = conjIrrS c ((c.S : Subgroup G).mul_mem
          ((c.S : Subgroup G).mul_mem c.s_mem_S (c.S0_le_S r.2)) hrInv) α := by
            congr 1
            group
      _ = conjIrrS c hrInv (conjIrrS c ((c.S : Subgroup G).mul_mem
            c.s_mem_S (c.S0_le_S r.2)) α) :=
            conjIrrS_mul c ((c.S : Subgroup G).mul_mem c.s_mem_S (c.S0_le_S r.2)) hrInv α
      _ = conjIrrS c hrInv α := hright
  refine Finset.mem_image.mpr
    ⟨⟨(r : G)⁻¹, (c.S0 : Subgroup G).inv_mem r.2⟩, Finset.mem_univ _, ?_⟩
  exact hmain.symm

/-- An `S0`-orbit is determined by any one of its members. -/
private lemma s0Orbit_eq_of_mem (c : Hyp11 G) {α β : Irr (↥c.U)}
    (hβ : β ∈ s0Orbit c α) : s0Orbit c β = s0Orbit c α := by
  classical
  rcases Finset.mem_image.mp hβ with ⟨r, hr, rfl⟩
  apply Finset.ext
  intro γ
  constructor
  · intro hγ
    rcases Finset.mem_image.mp hγ with ⟨g, hg, rfl⟩
    refine Finset.mem_image.mpr
      ⟨⟨(r : G) * (g : G), (c.S0 : Subgroup G).mul_mem r.2 g.2⟩,
        Finset.mem_univ _, ?_⟩
    have hEq : conjIrrS c (c.S0_le_S ((c.S0 : Subgroup G).mul_mem r.2 g.2)) α =
        conjIrrS c (c.S0_le_S g.2) (conjIrrS c (c.S0_le_S r.2) α) :=
      conjIrrS_mul c (c.S0_le_S r.2) (c.S0_le_S g.2) α
    exact hEq
  · intro hγ
    rcases Finset.mem_image.mp hγ with ⟨g, hg, rfl⟩
    have hrinv : (r : G)⁻¹ * (g : G) ∈ (c.S0 : Subgroup G) :=
      (c.S0 : Subgroup G).mul_mem ((c.S0 : Subgroup G).inv_mem r.2) g.2
    refine Finset.mem_image.mpr
      ⟨⟨(r : G)⁻¹ * (g : G), hrinv⟩, Finset.mem_univ _, ?_⟩
    have hEq : conjIrrS c (c.S0_le_S ((c.S0 : Subgroup G).mul_mem r.2 hrinv)) α =
        conjIrrS c (c.S0_le_S hrinv) (conjIrrS c (c.S0_le_S r.2) α) :=
      conjIrrS_mul c (c.S0_le_S r.2) (c.S0_le_S hrinv) α
    calc
      conjIrrS c (c.S0_le_S hrinv) (conjIrrS c (c.S0_le_S r.2) α)
          = conjIrrS c (c.S0_le_S ((c.S0 : Subgroup G).mul_mem r.2 hrinv)) α := hEq.symm
      _ = conjIrrS c (c.S0_le_S g.2) α := by
            congr 1
            group

/-- `Λ(α)` is fixed by `s` iff `S_α` is not contained in `S0`. -/
public theorem orbitOfAlpha_fixed_iff (c : Hyp11 G) (h12 : Hyp12 c) (hSC : Section3Hyp c)
    [Fintype ↥(LambdaHom c.H0 c.U)] (α : Irr (↥c.U)) :
    (∀ ν : ClassFunction (↥c.H0), ν ∈ orbitOfAlpha c h12 hSC α →
      conjChar c.H0 (s_normalizes_H0 c h12) ν ∈ orbitOfAlpha c h12 hSC α) ↔
    ¬ stabilizerS c α ≤ (c.S0 : Subgroup G) := by
  classical
  let σ : ClassFunction (↥c.U) := ∑ β ∈ s0Orbit c α, β.1
  constructor
  · intro hfixed
    rcases orbitOfAlpha_spec c h12 hSC α with ⟨⟨μ, hL⟩, hres⟩
    have hμmem : μ.1 ∈ orbitOfAlpha c h12 hSC α := by
      rw [hL]
      refine Finset.mem_image.mpr
        ⟨(1 : LambdaHom c.H0 c.U), Finset.mem_univ _, ?_⟩
      ext x
      simp [LambdaChar]
    have hresμ : restrictU c h12 μ.1 = σ := hres μ.1 hμmem
    have hconjmem : conjChar c.H0 (s_normalizes_H0 c h12) μ.1 ∈
        orbitOfAlpha c h12 hSC α := hfixed μ.1 hμmem
    have hresconj : restrictU c h12 (conjChar c.H0 (s_normalizes_H0 c h12) μ.1) = σ :=
      hres _ hconjmem
    have hsumfix : conjChar c.U
        (fun x : ↥c.U => S_normalizes_U c c.s c.s_mem_S x.1 x.2) σ = σ := by
      calc
        conjChar c.U (fun x : ↥c.U => S_normalizes_U c c.s c.s_mem_S x.1 x.2) σ
            = conjChar c.U (fun x : ↥c.U => S_normalizes_U c c.s c.s_mem_S x.1 x.2)
                (restrictU c h12 μ.1) := by rw [hresμ]
        _ = restrictU c h12 (conjChar c.H0 (s_normalizes_H0 c h12) μ.1) :=
              (restrictU_conjChar c h12 μ.1).symm
        _ = σ := hresconj
    exact stabilizerS_not_le_S0_of_sα_mem c α
      (sα_mem_s0Orbit_of_sum_fixed c hSC α hsumfix)
  · intro hnot
    intro ν hν
    rcases orbitOfAlpha_spec c h12 hSC α with ⟨⟨μ, hL⟩, hres⟩
    have hνirr : IsIrreducibleCharacter ν :=
      orbit_mem_isIrreducible c.H0 c.U μ.2 (by simpa [hL] using hν)
    have hs_inv : ∀ x : ↥c.H0, c.s⁻¹ * (x : G) * c.s ∈ c.H0 := by
      intro x
      simpa using (h12.H0_normal_in_H).2 c.s⁻¹ (c.H.inv_mem (s_mem_H c)) (x : G) x.2
    let νs : Irr (↥c.H0) :=
      ⟨conjChar c.H0 (s_normalizes_H0 c h12) ν,
        isIrreducibleCharacter_conjChar c.H0 (s_normalizes_H0 c h12) hs_inv hνirr⟩
    have hresν : restrictU c h12 ν = σ := hres ν hν
    have hσeq : (∑ β ∈ s0Orbit c (conjIrrS c c.s_mem_S α), β.1) = σ := by
      have hmem : conjIrrS c c.s_mem_S α ∈ s0Orbit c α :=
        sα_mem_s0Orbit_of_stabilizerS_not_le_S0 c α hnot
      have horb : s0Orbit c (conjIrrS c c.s_mem_S α) = s0Orbit c α :=
        s0Orbit_eq_of_mem c hmem
      rw [horb]
    have hresνs : ∀ ψ : ClassFunction (↥c.H0), ψ ∈ orbit c.H0 c.U νs.1 →
        restrictU c h12 ψ = σ := by
      intro ψ hψ
      calc
        restrictU c h12 ψ = restrictU c h12 νs.1 := restrictU_orbit_mem c h12 hψ
        _ = conjChar c.U (fun x : ↥c.U => S_normalizes_U c c.s c.s_mem_S x.1 x.2)
              (restrictU c h12 ν) := restrictU_conjChar c h12 ν
        _ = conjChar c.U (fun x : ↥c.U => S_normalizes_U c c.s c.s_mem_S x.1 x.2) σ := by
              rw [hresν]
        _ = ∑ β ∈ s0Orbit c (conjIrrS c c.s_mem_S α), β.1 :=
              s0Orbit_conjIrrS c hSC α
        _ = σ := hσeq
    have hL' : orbit c.H0 c.U νs.1 = orbitOfAlpha c h12 hSC α :=
      orbitOfAlpha_unique c h12 hSC α (orbit c.H0 c.U νs.1) ⟨⟨νs, rfl⟩, hresνs⟩
    have hmemνs : νs.1 ∈ orbit c.H0 c.U νs.1 := by
      refine Finset.mem_image.mpr
        ⟨(1 : LambdaHom c.H0 c.U), Finset.mem_univ _, ?_⟩
      ext x
      simp [LambdaChar]
    rw [← hL']
    exact hmemνs

/-- `S_α ≤ S`. -/
private lemma stabilizerS_le_S (c : Hyp11 G) (α : Irr (↥c.U)) :
    stabilizerS c α ≤ (c.S : Subgroup G) := by
  intro g hg
  rcases hg with ⟨hgS, _⟩
  exact hgS

/-- `S' ≤ S_α` (from the Section 3 hypothesis). -/
private lemma SPrime_le_stabilizerS (c : Hyp11 G) (hSC : Section3Hyp c)
    (α : Irr (↥c.U)) : SPrime c ≤ stabilizerS c α := by
  intro s hs
  exact ⟨c.S0_le_S (SPrime_le_S0 c hs), SPrime_fixes_alpha c hSC α hs⟩

/-- If `S_α` is not contained in `S0`, some element of `S_α` lies outside
`S0`. -/
private lemma exists_outside_of_not_le (c : Hyp11 G) (α : Irr (↥c.U))
    (h : ¬ stabilizerS c α ≤ (c.S0 : Subgroup G)) :
    ∃ x : G, x ∈ stabilizerS c α ∧ x ∉ (c.S0 : Subgroup G) := by
  by_contra hnone
  apply h
  intro x hx
  by_contra hxS0
  exact hnone ⟨x, hx, hxS0⟩

/-- If `S0 ≤ S_α` and some outside element fixes `α`, then `S_α = S`. -/
private lemma stabilizerS_eq_S_of_outside (c : Hyp11 G) (hSC : Section3Hyp c)
    (α : Irr (↥c.U))
    (hS0le : (c.S0 : Subgroup G) ≤ stabilizerS c α)
    {x : G} (hxStab : x ∈ stabilizerS c α)
    (hxS0 : x ∉ (c.S0 : Subgroup G)) :
    stabilizerS c α = (c.S : Subgroup G) := by
  classical
  have hxS : x ∈ (c.S : Subgroup G) := hxStab.1
  apply le_antisymm
  · exact stabilizerS_le_S c α
  · intro g hgS
    let K : Subgroup (↥(c.S : Subgroup G)) :=
      (c.S0 : Subgroup G).subgroupOf (c.S : Subgroup G)
    let a : ↥(c.S : Subgroup G) := ⟨x, hxS⟩
    let b : ↥(c.S : Subgroup G) := ⟨g, hgS⟩
    have hK : K.index = 2 := S0_index c
    have hiff := Subgroup.mul_mem_iff_of_index_two hK (a := a) (b := b)
    have haK : a ∉ K := by
      intro ha
      exact hxS0 (Subgroup.mem_subgroupOf.mp ha)
    by_cases hbK : b ∈ K
    · exact hS0le (Subgroup.mem_subgroupOf.mp hbK)
    · have habK : a * b ∈ K := by
        rw [hiff]
        simp [haK, hbK]
      have habS0 : x * g ∈ (c.S0 : Subgroup G) := Subgroup.mem_subgroupOf.mp habK
      have habStab : x * g ∈ stabilizerS c α := hS0le habS0
      have hxInvStab : x⁻¹ ∈ stabilizerS c α := (stabilizerS c α).inv_mem hxStab
      have hprod : x⁻¹ * (x * g) = g := by group
      simpa [hprod] using (stabilizerS c α).mul_mem hxInvStab habStab

/-- When `r0` moves `α`, `S_α ∩ S0 = S'`. -/
private lemma stabilizerS_inf_S0_eq_SPrime (c : Hyp11 G) (hSC : Section3Hyp c)
    (α : Irr (↥c.U))
    (hnot : conjIrrS c (c.S0_le_S (S0_generator_mem_S0 c)) α ≠ α) :
    stabilizerS c α ⊓ (c.S0 : Subgroup G) = SPrime c := by
  classical
  apply le_antisymm
  · intro x hx
    rcases Subgroup.mem_inf.mp hx with ⟨hxStab, hxS0⟩
    rcases S0_mem_SPrime_or_r0_mul c hxS0 with hxSP | hr0xSP
    · exact hxSP
    · exfalso
      have hr0xStab : (S0_generator c) * x ∈ stabilizerS c α :=
        SPrime_le_stabilizerS c hSC α hr0xSP
      have hxInvStab : x⁻¹ ∈ stabilizerS c α := (stabilizerS c α).inv_mem hxStab
      have hprod : ((S0_generator c) * x) * x⁻¹ = S0_generator c := by group
      have hr0Stab : S0_generator c ∈ stabilizerS c α := by
        simpa [hprod] using (stabilizerS c α).mul_mem hr0xStab hxInvStab
      rcases hr0Stab with ⟨_, hr0fix⟩
      exact hnot hr0fix
  · intro x hxSP
    exact Subgroup.mem_inf.mpr
      ⟨SPrime_le_stabilizerS c hSC α hxSP, SPrime_le_S0 c hxSP⟩

/-- If `t·x ∈ K` and `t` is an involution, then `K⟨x⟩ = K⟨t⟩`. -/
private lemma sup_zpowers_eq_of_reflection {K : Subgroup G} {t x : G}
    (ht2 : t * t = 1) (htx : t * x ∈ K) :
    K ⊔ Subgroup.zpowers x = K ⊔ Subgroup.zpowers t := by
  classical
  have hx : x = t * (t * x) := by
    calc
      x = (t * t) * x := by rw [ht2]; simp
      _ = t * (t * x) := by group
  have ht : t = x * (t * x)⁻¹ := by
    have hx' : x * (t * x)⁻¹ = t := by
      nth_rewrite 1 [hx]
      group
    exact hx'.symm
  apply le_antisymm
  · refine sup_le ?_ ?_
    · exact le_sup_left
    · rw [Subgroup.zpowers_le]
      rw [hx]
      exact (K ⊔ Subgroup.zpowers t).mul_mem
        (SetLike.le_def.mp le_sup_right (Subgroup.mem_zpowers t))
        (SetLike.le_def.mp le_sup_left htx)
  · refine sup_le ?_ ?_
    · exact le_sup_left
    · rw [Subgroup.zpowers_le]
      rw [ht]
      exact (K ⊔ Subgroup.zpowers x).mul_mem
        (SetLike.le_def.mp le_sup_right (Subgroup.mem_zpowers x))
        (SetLike.le_def.mp le_sup_left (K.inv_mem htx))

/-- An element of `S \ S0` lies in one of the two subgroups
`S'⟨t1⟩`, `S'⟨t2⟩`. -/
private lemma outside_mem_sup_t1_or_t2 (c : Hyp11 G) {x : G}
    (hxS : x ∈ (c.S : Subgroup G)) (hxS0 : x ∉ (c.S0 : Subgroup G)) :
    (c.t1 * x ∈ SPrime c ∧ x ∈ SPrime c ⊔ Subgroup.zpowers c.t1) ∨
    (c.t2 * x ∈ SPrime c ∧ x ∈ SPrime c ⊔ Subgroup.zpowers c.t2) := by
  classical
  let K : Subgroup (↥(c.S : Subgroup G)) :=
    (c.S0 : Subgroup G).subgroupOf (c.S : Subgroup G)
  let a : ↥(c.S : Subgroup G) := ⟨c.t1, c.t1_mem_S⟩
  let b : ↥(c.S : Subgroup G) := ⟨x, hxS⟩
  have hK : K.index = 2 := S0_index c
  have hiff := Subgroup.mul_mem_iff_of_index_two hK (a := a) (b := b)
  have haK : a ∉ K := by
    intro ha
    exact c.t1_not_mem_S0 (Subgroup.mem_subgroupOf.mp ha)
  have hbK : b ∉ K := by
    intro hb
    exact hxS0 (Subgroup.mem_subgroupOf.mp hb)
  have habK : a * b ∈ K := by
    rw [hiff]
    simp [haK, hbK]
  have hrS0 : c.t1 * x ∈ (c.S0 : Subgroup G) := Subgroup.mem_subgroupOf.mp habK
  let r : ↥(c.S0 : Subgroup G) := ⟨c.t1 * x, hrS0⟩
  have ht1 : c.t1 * c.t1 = 1 := by simpa [pow_two] using c.t1_involution.2
  have hxeq : x = c.t1 * (r : G) := by
    dsimp [r]
    have hxx : c.t1 * (c.t1 * x) = x := by
      calc
        c.t1 * (c.t1 * x) = (c.t1 * c.t1) * x := by group
        _ = x := by rw [ht1]; simp
    exact hxx.symm
  rcases S0_mem_SPrime_or_r0_mul c r.2 with hrSP | hr0rSP
  · left
    constructor
    · simpa [r] using hrSP
    · have hmem : c.t1 * (r : G) ∈ SPrime c ⊔ Subgroup.zpowers c.t1 :=
        (SPrime c ⊔ Subgroup.zpowers c.t1).mul_mem
          (SetLike.le_def.mp le_sup_right (Subgroup.mem_zpowers c.t1))
          (SetLike.le_def.mp le_sup_left hrSP)
      simpa [hxeq] using hmem
  · right
    have hrev : c.t2 * c.t1 = (S0_generator c)⁻¹ := by
      have ht1i : c.t1⁻¹ = c.t1 :=
        (eq_inv_iff_mul_eq_one.mpr ht1).symm
      have ht2 : c.t2 * c.t2 = 1 := by simpa [pow_two] using c.t2_involution.2
      have ht2i : c.t2⁻¹ = c.t2 := (eq_inv_iff_mul_eq_one.mpr ht2).symm
      dsimp [S0_generator]
      rw [mul_inv_rev, ht1i, ht2i]
    have hsq : (S0_generator c) * (S0_generator c) ∈ SPrime c := by
      simpa [S0_generator, pow_two] using SPrime_mem_pow_two c
    have hmem0 : (S0_generator c)⁻¹ * (S0_generator c)⁻¹ ∈ SPrime c := by
      have hEq : (S0_generator c)⁻¹ * (S0_generator c)⁻¹ =
          ((S0_generator c) * (S0_generator c))⁻¹ := by group
      rw [hEq]
      exact (SPrime c).inv_mem hsq
    have hprod : c.t2 * x =
        (S0_generator c)⁻¹ * (S0_generator c)⁻¹ *
          ((S0_generator c) * (r : G)) := by
      rw [hxeq]
      calc
        c.t2 * (c.t1 * (r : G)) = (c.t2 * c.t1) * (r : G) := by group
        _ = (S0_generator c)⁻¹ * (r : G) := by rw [hrev]
        _ = (S0_generator c)⁻¹ * (S0_generator c)⁻¹ *
              ((S0_generator c) * (r : G)) := by group
    have hmem : c.t2 * x ∈ SPrime c := by
      rw [hprod]
      exact (SPrime c).mul_mem hmem0 hr0rSP
    constructor
    · exact hmem
    · have ht2 : c.t2 * c.t2 = 1 := by simpa [pow_two] using c.t2_involution.2
      have hx2 : x = c.t2 * (c.t2 * x) := by
        have hxx : c.t2 * (c.t2 * x) = x := by
          calc
            c.t2 * (c.t2 * x) = (c.t2 * c.t2) * x := by group
            _ = x := by rw [ht2]; simp
        exact hxx.symm
      have hmemSup : c.t2 * x ∈ SPrime c ⊔ Subgroup.zpowers c.t2 :=
        SetLike.le_def.mp le_sup_left hmem
      have hfinal : c.t2 * (c.t2 * x) ∈ SPrime c ⊔ Subgroup.zpowers c.t2 :=
        (SPrime c ⊔ Subgroup.zpowers c.t2).mul_mem
          (SetLike.le_def.mp le_sup_right (Subgroup.mem_zpowers c.t2)) hmemSup
      rw [hx2]
      exact hfinal

/-- If `x ∈ S \ S0` fixes `α` and `r0` moves `α`, then
`S_α = S'⟨x⟩`. -/
private lemma stabilizerS_eq_sup_of_outside (c : Hyp11 G) (hSC : Section3Hyp c)
    (α : Irr (↥c.U)) {x : G} (hxStab : x ∈ stabilizerS c α)
    (hxS0 : x ∉ (c.S0 : Subgroup G))
    (hnot : conjIrrS c (c.S0_le_S (S0_generator_mem_S0 c)) α ≠ α) :
    stabilizerS c α = SPrime c ⊔ Subgroup.zpowers x := by
  classical
  have hxS : x ∈ (c.S : Subgroup G) := hxStab.1
  have hinter : stabilizerS c α ⊓ (c.S0 : Subgroup G) = SPrime c :=
    stabilizerS_inf_S0_eq_SPrime c hSC α hnot
  have hSPrime : SPrime c ≤ stabilizerS c α := SPrime_le_stabilizerS c hSC α
  have hle : SPrime c ⊔ Subgroup.zpowers x ≤ stabilizerS c α := by
    exact sup_le hSPrime (by
      rw [Subgroup.zpowers_le]
      exact hxStab)
  apply le_antisymm
  · intro g hgStab
    have hgS : g ∈ (c.S : Subgroup G) := hgStab.1
    let K : Subgroup (↥(c.S : Subgroup G)) :=
      (c.S0 : Subgroup G).subgroupOf (c.S : Subgroup G)
    let a : ↥(c.S : Subgroup G) := ⟨x, hxS⟩
    let b : ↥(c.S : Subgroup G) := ⟨g, hgS⟩
    have hK : K.index = 2 := S0_index c
    have hiff := Subgroup.mul_mem_iff_of_index_two hK (a := a) (b := b)
    have haK : a ∉ K := by
      intro ha
      exact hxS0 (Subgroup.mem_subgroupOf.mp ha)
    by_cases hbK : b ∈ K
    · have hgS0 : g ∈ (c.S0 : Subgroup G) := Subgroup.mem_subgroupOf.mp hbK
      have hgSP : g ∈ SPrime c := by
        have hmem : g ∈ stabilizerS c α ⊓ (c.S0 : Subgroup G) :=
          Subgroup.mem_inf.mpr ⟨hgStab, hgS0⟩
        rw [hinter] at hmem
        exact hmem
      exact SetLike.le_def.mp le_sup_left hgSP
    · have habK : a * b ∈ K := by
        rw [hiff]
        simp [haK, hbK]
      have habS0 : x * g ∈ (c.S0 : Subgroup G) := Subgroup.mem_subgroupOf.mp habK
      have habStab : x * g ∈ stabilizerS c α :=
        (stabilizerS c α).mul_mem hxStab hgStab
      have habSP : x * g ∈ SPrime c := by
        have hmem : x * g ∈ stabilizerS c α ⊓ (c.S0 : Subgroup G) :=
          Subgroup.mem_inf.mpr ⟨habStab, habS0⟩
        rw [hinter] at hmem
        exact hmem
      have hxInvSup : x⁻¹ ∈ SPrime c ⊔ Subgroup.zpowers x :=
        SetLike.le_def.mp le_sup_right
          ((Subgroup.zpowers x).inv_mem (Subgroup.mem_zpowers x))
      have hprod : x⁻¹ * (x * g) = g := by group
      have hmemSup : x⁻¹ * (x * g) ∈ SPrime c ⊔ Subgroup.zpowers x :=
        (SPrime c ⊔ Subgroup.zpowers x).mul_mem hxInvSup
          (SetLike.le_def.mp le_sup_left habSP)
      simpa [hprod] using hmemSup
  · exact hle

/-- The `i.e.`-part of Remark 3.1: `S_α ≰ S0` iff (`n = 1` and `S_α = S`) or
(`n = 2` and `S_α = S'⟨t1⟩` or `S'⟨t2⟩`). -/
public theorem stabilizerS_not_le_S0_iff (c : Hyp11 G) (h12 : Hyp12 c) (hSC : Section3Hyp c)
    [Fintype ↥(LambdaHom c.H0 c.U)] (α : Irr (↥c.U)) :
    ¬ stabilizerS c α ≤ (c.S0 : Subgroup G) ↔
      ((s0Orbit c α).card = 1 ∧ stabilizerS c α = (c.S : Subgroup G)) ∨
      ((s0Orbit c α).card = 2 ∧
        (stabilizerS c α = SPrime c ⊔ Subgroup.zpowers c.t1 ∨
          stabilizerS c α = SPrime c ⊔ Subgroup.zpowers c.t2)) := by
  classical
  constructor
  · intro hnot
    rcases exists_outside_of_not_le c α hnot with ⟨x, hxStab, hxS0⟩
    have hxS : x ∈ (c.S : Subgroup G) := hxStab.1
    by_cases hα : conjIrrS c (c.S0_le_S (S0_generator_mem_S0 c)) α = α
    · have hcard1 : (s0Orbit c α).card = 1 := by
        rw [s0Orbit_eq_singleton_of_fixed c hSC α hα]
        simp
      have hS0le : (c.S0 : Subgroup G) ≤ stabilizerS c α := by
        intro g hg
        rcases S0_mem_SPrime_or_r0_mul c hg with hgSP | hr0gSP
        · exact SPrime_le_stabilizerS c hSC α hgSP
        · have hrinvfix : conjIrrS c
            (c.S0_le_S ((c.S0 : Subgroup G).inv_mem (S0_generator_mem_S0 c))) α = α :=
            (conjIrrS_r0_fixed_iff_r0_inv c α).mp hα
          have hmemInv : (S0_generator c)⁻¹ ∈ stabilizerS c α :=
            ⟨c.S0_le_S ((c.S0 : Subgroup G).inv_mem (S0_generator_mem_S0 c)), hrinvfix⟩
          have hmemProd : (S0_generator c) * (g : G) ∈ stabilizerS c α :=
            SPrime_le_stabilizerS c hSC α hr0gSP
          have hprod : (S0_generator c)⁻¹ * ((S0_generator c) * (g : G)) = g := by group
          simpa [hprod] using (stabilizerS c α).mul_mem hmemInv hmemProd
      have hEqS : stabilizerS c α = (c.S : Subgroup G) :=
        stabilizerS_eq_S_of_outside c hSC α hS0le hxStab hxS0
      exact Or.inl ⟨hcard1, hEqS⟩
    · have hcard2 : (s0Orbit c α).card = 2 := by
        rw [s0Orbit_eq_pair_of_not_fixed c hSC α hα]
        rw [Finset.card_insert_of_notMem]
        · simp
        · intro hEq
          have hfixinv : conjIrrS c
              (c.S0_le_S ((c.S0 : Subgroup G).inv_mem (S0_generator_mem_S0 c))) α = α :=
            (Finset.mem_singleton.mp hEq).symm
          exact hα ((conjIrrS_r0_fixed_iff_r0_inv c α).mpr hfixinv)
      have hEqSup : stabilizerS c α = SPrime c ⊔ Subgroup.zpowers x :=
        stabilizerS_eq_sup_of_outside c hSC α hxStab hxS0 hα
      rcases outside_mem_sup_t1_or_t2 c hxS hxS0 with ⟨htx1, hxT1⟩ | ⟨htx2, hxT2⟩
      · have hEq1 : SPrime c ⊔ Subgroup.zpowers x = SPrime c ⊔ Subgroup.zpowers c.t1 :=
          sup_zpowers_eq_of_reflection (K := SPrime c) (t := c.t1) (x := x)
            (by simpa [pow_two] using c.t1_involution.2) htx1
        exact Or.inr ⟨hcard2, Or.inl (by rw [hEqSup, hEq1])⟩
      · have hEq2 : SPrime c ⊔ Subgroup.zpowers x = SPrime c ⊔ Subgroup.zpowers c.t2 :=
          sup_zpowers_eq_of_reflection (K := SPrime c) (t := c.t2) (x := x)
            (by simpa [pow_two] using c.t2_involution.2) htx2
        exact Or.inr ⟨hcard2, Or.inr (by rw [hEqSup, hEq2])⟩
  · intro hrhs
    rcases hrhs with ⟨_hcard1, hEqS⟩ | ⟨_hcard2, hEqPair⟩
    · intro hle
      have ht1S0 : c.t1 ∈ (c.S0 : Subgroup G) := hle (by
        rw [hEqS]
        exact c.t1_mem_S)
      exact c.t1_not_mem_S0 ht1S0
    · rcases hEqPair with hEq1 | hEq2
      · intro hle
        have ht1S0 : c.t1 ∈ (c.S0 : Subgroup G) := hle (by
          rw [hEq1]
          exact SetLike.le_def.mp le_sup_right (Subgroup.mem_zpowers c.t1))
        exact c.t1_not_mem_S0 ht1S0
      · intro hle
        have ht2S0 : c.t2 ∈ (c.S0 : Subgroup G) := hle (by
          rw [hEq2]
          exact SetLike.le_def.mp le_sup_right (Subgroup.mem_zpowers c.t2))
        exact c.t2_not_mem_S0 ht2S0

/-- Every `Λ`-orbit is of the form `Λ(α)` for some `α ∈ Irr(U)`. -/
public theorem orbit_is_orbitOfAlpha (c : Hyp11 G) (h12 : Hyp12 c) (hSC : Section3Hyp c)
    [Fintype ↥(LambdaHom c.H0 c.U)] (μ : Irr (↥c.H0)) :
    ∃ α : Irr (↥c.U), orbit c.H0 c.U μ.1 = orbitOfAlpha c h12 hSC α := by
  rcases orbit_restrict_eq_orbitSum_of_irr c h12 hSC μ with ⟨α, hprop⟩
  exact ⟨α, orbitOfAlpha_unique c h12 hSC α (orbit c.H0 c.U μ.1)
    ⟨⟨μ, rfl⟩, hprop⟩⟩

/-- Remark 3.1: for `α ∈ Irr(U)`, with `S_α` the subgroup of elements of `S`
fixing `α` and `α1, …, αn` (`n ≤ 2`) the `S0`-conjugates of `α`: there is a
unique `Λ`-orbit `Λ(α)` such that `μ|_U = α1 + ⋯ + αn` for all `μ ∈ Λ(α)`;
`Λ(α)` is fixed by `s` iff `S_α ≰ S0`, i.e. (`n = 1` and `S_α = S`) or
(`n = 2` and `S_α = S'⟨t1⟩` or `S'⟨t2⟩`); `|Λ(α)| = m/n` and hence
`Σ_{ν∈Λ(α)} ν(1) = m·α(1)`; and every `Λ`-orbit is of the form `Λ(α)`. -/
public theorem remark_3_1 (c : Hyp11 G) (h12 : Hyp12 c) (hSC : Section3Hyp c)
    [Fintype ↥(LambdaHom c.H0 c.U)] (α : Irr (↥c.U)) :
    (∃! L : Finset (ClassFunction (↥c.H0)),
      (∃ μ : Irr (↥c.H0), L = orbit c.H0 c.U μ.1) ∧
        (∀ ν : ClassFunction (↥c.H0), ν ∈ L →
          restrictU c h12 ν = ∑ α' ∈ s0Orbit c α, α'.1)) ∧
    (s0Orbit c α).card ≤ 2 ∧
    (orbitOfAlpha c h12 hSC α).card =
      (c.U.subgroupOf c.H0).index / (s0Orbit c α).card ∧
    (∑ ν ∈ orbitOfAlpha c h12 hSC α, ν 1) =
      ((c.U.subgroupOf c.H0).index : ℂ) * α.1 1 ∧
    ((∀ ν : ClassFunction (↥c.H0), ν ∈ orbitOfAlpha c h12 hSC α →
        conjChar c.H0 (s_normalizes_H0 c h12) ν ∈ orbitOfAlpha c h12 hSC α) ↔
      ¬ stabilizerS c α ≤ (c.S0 : Subgroup G)) ∧
    (¬ stabilizerS c α ≤ (c.S0 : Subgroup G) ↔
      ((s0Orbit c α).card = 1 ∧ stabilizerS c α = (c.S : Subgroup G)) ∨
      ((s0Orbit c α).card = 2 ∧
        (stabilizerS c α = SPrime c ⊔ Subgroup.zpowers c.t1 ∨
          stabilizerS c α = SPrime c ⊔ Subgroup.zpowers c.t2))) ∧
    (∀ μ : Irr (↥c.H0), ∃ α : Irr (↥c.U),
      orbit c.H0 c.U μ.1 = orbitOfAlpha c h12 hSC α) := by
  exact ⟨remark_3_1_exists c h12 hSC α,
    s0Orbit_card_le_two c hSC α,
    orbitOfAlpha_card c h12 hSC α,
    orbitOfAlpha_degree_sum c h12 hSC α,
    orbitOfAlpha_fixed_iff c h12 hSC α,
    stabilizerS_not_le_S0_iff c h12 hSC α,
    orbit_is_orbitOfAlpha c h12 hSC⟩

end Section3

end CFSG.BenderGlauberman
