module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section2.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section2.Lemma22

namespace CFSG
end CFSG
open CFSG

/-!
# Bender--Glauberman: Section 2 — the Coherence Theorem 2.3 cluster

The `CoherenceData` structure, the provable core of the coherence proof
(the `(vi)`-step helpers, blocking on the `V = 0` content of Lemma 2.2),
`exists_coherence_data`, `tildeNu`, and `BOf` with its `BOf_*` lemmas.
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

/-- `|H| = 2·|H0|` (from `H0_index`). -/
private lemma H_card_eq_two_mul_H0_card (c : Hyp11 G) (h12 : Hyp12 c)
    (hH0index : (c.H0.subgroupOf c.H).index = 2) :
    (Nat.card (↥c.H) : ℂ) = 2 * (Nat.card (↥c.H0) : ℂ) := by
  have hc := Subgroup.card_mul_index (c.H0.subgroupOf c.H)
  have hc' : Nat.card (↥(c.H0.subgroupOf c.H)) = Nat.card (↥c.H0) := by
    exact Nat.card_congr {
      toFun := fun x : ↥(c.H0.subgroupOf c.H) => ⟨(x : G), Subgroup.mem_subgroupOf.mp x.2⟩
      invFun := fun y : ↥c.H0 => ⟨⟨(y : G), (h12.H0_normal_in_H).1 y.2⟩, Subgroup.mem_subgroupOf.mpr y.2⟩
      left_inv := by
        intro x
        apply Subtype.ext
        rfl
      right_inv := by
        intro y
        apply Subtype.ext
        rfl }
  have hc'' : (Nat.card (↥c.H) : ℂ) = 2 * (Nat.card (↥(c.H0.subgroupOf c.H)) : ℂ) := by
    rw [← hc, hH0index]
    push_cast
    ring
  rw [hc'']
  congr 1
  exact_mod_cast hc'

/-- Coherence Theorem 2.3: a mapping `ν ↦ ν̃` from `Irr(H0)` into the
generalized characters of `G` with `ν̃^{ν^s} = ν̃` and the six properties
(i)–(vi). -/
structure CoherenceData (c : Hyp11 G) (h12 : Hyp12 c) where
  /-- The map `ν ↦ ν̃`. -/
  tildeNu : Irr (↥c.H0) → ClassFunction G
  /-- `ν̃^{ν^s} = ν̃` (invariance under `s`). -/
  invariance : ∀ ν : Irr (↥c.H0), tildeNu (conjIrr c h12 ν) = tildeNu ν
  /-- Each `ν̃` is a generalized character of `G`. -/
  isGeneralized : ∀ ν : Irr (↥c.H0), IsGeneralizedCharacter (tildeNu ν)
  /-- (i) `|ν̃| = |ν^H|`, and both are `1` or `2` according as `ν^s ≠ ν` or
  `ν^s = ν`. -/
  norm : ∀ ν : Irr (↥c.H0),
    normSq G (tildeNu ν) = normSq (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν.1) ∧
      normSq G (tildeNu ν) =
        (if conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1 then 2 else 1)
  /-- (ii) `(μ−ν)* = μ̃−ν̃` for equivalent `μ, ν`. -/
  ind : ∀ μ ν : Irr (↥c.H0), μ.1 ∈ orbit c.H0 c.U ν.1 →
    inducedClassFunction c.H0 (μ.1 - ν.1) = tildeNu μ - tildeNu ν
  /-- (iii) `μ̃` and `ν̃` are disjoint if `μ` and `ν` are equivalent and not
  conjugate (distinct and not conjugate under `⟨s⟩`). -/
  disjoint : ∀ μ ν : Irr (↥c.H0), μ.1 ∈ orbit c.H0 c.U ν.1 →
    ν.1 ≠ μ.1 →
    conjChar c.H0 (s_normalizes_H0 c h12) ν.1 ≠ μ.1 →
    Theory.Character.Disjoint (tildeNu μ) (tildeNu ν)
  /-- (iv) for `Λ`-orbits `L1` and `L2` not conjugate under `⟨s⟩` (distinct,
  and `L1^s ≠ L2`), the generalized characters `μ̃1−ν̃1` and `μ̃2−ν̃2` are
  orthogonal whenever `μj, νj ∈ Lj`. -/
  orthogonal : ∀ ν₁ ν₂ μ₁ μ₂ : Irr (↥c.H0),
    μ₁.1 ∈ orbit c.H0 c.U ν₁.1 → μ₂.1 ∈ orbit c.H0 c.U ν₂.1 →
      ν₁.1 ∉ orbit c.H0 c.U ν₂.1 →
      conjChar c.H0 (s_normalizes_H0 c h12) ν₁.1 ∉ orbit c.H0 c.U ν₂.1 →
      scalarProduct G (tildeNu μ₁ - tildeNu ν₁) (tildeNu μ₂ - tildeNu ν₂) = 0
  /-- (v) `μ̃−ν̃ = μ^H−ν^H` on `T`, for equivalent `μ, ν`. -/
  on_T : ∀ μ ν : Irr (↥c.H0), μ.1 ∈ orbit c.H0 c.U ν.1 →
    ∀ g : G, g ∈ c.T → (hg : g ∈ c.H) →
      tildeNu μ g - tildeNu ν g =
        inducedFromSub (h12.H0_normal_in_H).1 μ.1 ⟨g, hg⟩ -
          inducedFromSub (h12.H0_normal_in_H).1 ν.1 ⟨g, hg⟩
  /-- (vi) `ν̃(t) = 2ν(t)` if `ν^s ≠ ν`, unless `|Λν| = 4` and
  `Λν^s = Λν`. -/
  at_t : ∀ ν : Irr (↥c.H0), conjChar c.H0 (s_normalizes_H0 c h12) ν.1 ≠ ν.1 →
    ¬ ((orbit c.H0 c.U ν.1).card = 4 ∧
      conjChar c.H0 (s_normalizes_H0 c h12) ν.1 ∈ orbit c.H0 c.U ν.1) →
    tildeNu ν c.t = 2 * ν.1 (tH0 c)

/-! ## Coherence Theorem 2.3: the provable core

The route `R1-orbitwise` (see `node_graph/bg_section2/coherence_2_3.md`).
The two genuinely hard steps — `(vi)` (`at_t`) and the `n ≥ 5` contradiction
of the orbit-lift — need the `V = 0` content of Lemma 2.2, which is blocked
on the dihedral-Sylow-2 structure `|H : H0| = 2` (`H0_index`, Lemma22.lean).
Formalized here: everything that is provable without those inputs —
(a) the sign choice (`μ ∈ L`, `μ^s ≠ μ`, `μ(t) = −ν(t)`) from Lemma 2.1,
(b) the full `(vi)`-argument from the (i),(ii),(v) fields plus the two
blocked inputs as explicit hypotheses (`at_t_of_V_zero`), (c) the reduction
`V = 0 ⟹ μ̃(t)² = ν̃(t)²` (`tilde_sq_eq_of_V_zero`). -/

/-- Members of a `Λ`-orbit have the same degree. -/
private lemma orbit_mem_degree_eq (c : Hyp11 G)
    [Fintype ↥(LambdaHom c.H0 c.U)] {ν μ : ClassFunction (↥c.H0)}
    (hμ : μ ∈ orbit c.H0 c.U ν) : μ 1 = ν 1 := by
  classical
  rcases (Finset.mem_image.mp hμ) with ⟨l, hl, rfl⟩
  simp [LambdaChar]

/-- An orbit member takes either the same or the opposite value as another
member at the central involution `t`. -/
private lemma orbit_mem_value_eq_or_neg (c : Hyp11 G)
    {ν μ : ClassFunction (↥c.H0)}
    (hν : IsIrreducibleCharacter ν) (hμ : IsIrreducibleCharacter μ)
    (hνL : ν ∈ orbit c.H0 c.U μ) :
    ν (tH0 c) = μ (tH0 c) ∨ ν (tH0 c) = -μ (tH0 c) := by
  have ht_sq : (tH0 c) ^ 2 = 1 := t_H0_sq c
  have ht_central : ∀ g : ↥c.H0, (tH0 c) * g = g * (tH0 c) := t_central_H0' c
  rcases char_apply_central_sign ht_central ht_sq hν with hνt | hνt
  · rcases char_apply_central_sign ht_central ht_sq hμ with hμt | hμt
    · left
      calc
        ν (tH0 c) = ν 1 := hνt
        _ = μ 1 := orbit_mem_degree_eq c hνL
        _ = μ (tH0 c) := hμt.symm
    · right
      calc
        ν (tH0 c) = ν 1 := hνt
        _ = μ 1 := orbit_mem_degree_eq c hνL
        _ = -μ (tH0 c) := by rw [hμt]; ring
  · rcases char_apply_central_sign ht_central ht_sq hμ with hμt | hμt
    · right
      calc
        ν (tH0 c) = -ν 1 := hνt
        _ = -μ 1 := by rw [orbit_mem_degree_eq c hνL]
        _ = -μ (tH0 c) := by rw [hμt]
    · left
      calc
        ν (tH0 c) = -ν 1 := hνt
        _ = -μ 1 := by rw [orbit_mem_degree_eq c hνL]
        _ = μ (tH0 c) := by rw [hμt]

/-- An orbit member fixed by `s` forces the whole orbit to be `s`-invariant:
`μ ∈ Lν`, `μ^s = μ` ⟹ `ν^s ∈ Lν`. -/
private lemma orbit_mem_conj_fixed_implies_conj_mem (c : Hyp11 G) (h12 : Hyp12 c)
    [Fintype ↥(LambdaHom c.H0 c.U)] {ν μ : ClassFunction (↥c.H0)}
    (hμ : μ ∈ orbit c.H0 c.U ν)
    (hμs : conjChar c.H0 (s_normalizes_H0 c h12) μ = μ) :
    conjChar c.H0 (s_normalizes_H0 c h12) ν ∈ orbit c.H0 c.U ν := by
  classical
  rcases (Finset.mem_image.mp hμ) with ⟨l, hl, rfl⟩
  -- `ls` = the `s`-conjugate of `l`, again in `Λ`
  let ls : ↥(LambdaHom c.H0 c.U) :=
    ⟨l.1.comp (conjMonoidHom c.H0 c.s (s_normalizes_H0 c h12)), by
      intro u hu
      change l.1 (conjMonoidHom c.H0 c.s (s_normalizes_H0 c h12) u) = 1
      exact l.2 (conjMonoidHom c.H0 c.s (s_normalizes_H0 c h12) u) (by
        change c.s * (u : G) * c.s⁻¹ ∈ c.U
        exact s_normalizes_U c hu)⟩
  have hcmul : conjChar c.H0 (s_normalizes_H0 c h12) (LambdaChar l.1 * ν) =
      LambdaChar ls.1 * conjChar c.H0 (s_normalizes_H0 c h12) ν := by
    ext x
    simp [conjChar, conjMonoidHom, LambdaChar, ls, mul_assoc]
  have hmain : conjChar c.H0 (s_normalizes_H0 c h12) ν =
      LambdaChar (l * ls⁻¹).1 * ν := by
    ext x
    have hpt := congrFun hμs x
    rw [hcmul] at hpt
    have hpt' : (ls.1 x : ℂ) * conjChar c.H0 (s_normalizes_H0 c h12) ν x =
        (l.1 x : ℂ) * ν x := by
      simpa [LambdaChar] using hpt
    have hc : conjChar c.H0 (s_normalizes_H0 c h12) ν x =
        ((l.1 x : ℂ) * ((ls.1 x : ℂ)⁻¹)) * ν x := by
      have hml := congrArg (fun z : ℂ => (ls.1 x : ℂ)⁻¹ * z) hpt'
      rw [← mul_assoc, inv_mul_cancel₀ (unit_val_ne_zero (ls.1 x)), one_mul] at hml
      rw [hml]
      ring
    simpa [LambdaChar, mul_assoc] using hc
  refine Finset.mem_image.mpr ⟨l * ls⁻¹, Finset.mem_univ _, ?_⟩
  exact hmain.symm

/-- The number of `s`-fixed characters in the orbit `Lν` is at most two. -/
private lemma orbit_s_fixed_card_le_two (c : Hyp11 G) (h12 : Hyp12 c)
    [Fintype ↥(LambdaHom c.H0 c.U)] {ν : ClassFunction (↥c.H0)}
    (hν : IsIrreducibleCharacter ν) :
    ((orbit c.H0 c.U ν).filter (fun μ =>
      conjChar c.H0 (s_normalizes_H0 c h12) μ = μ)).card ≤ 2 := by
  classical
  by_cases hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν ∈ orbit c.H0 c.U ν
  · have h : ((orbit c.H0 c.U ν).filter (fun μ =>
        conjChar c.H0 (s_normalizes_H0 c h12) μ = μ)).card = 2 :=
      lemma_2_1_b c h12 hν hνs
    omega
  · have hF : (orbit c.H0 c.U ν).filter (fun μ =>
        conjChar c.H0 (s_normalizes_H0 c h12) μ = μ) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro μ hμ
      rcases (Finset.mem_filter.mp hμ) with ⟨hμL, hμs⟩
      exact hνs (orbit_mem_conj_fixed_implies_conj_mem c h12 hμL hμs)
    rw [hF]
    simp

/-- An irreducible character of `H0` does not take opposite values at the
central involution `t`. -/
private lemma central_involution_char_ne_neg (c : Hyp11 G)
    {ν : ClassFunction (↥c.H0)} (hν : IsIrreducibleCharacter ν) :
    ν (tH0 c) ≠ -ν (tH0 c) := by
  have hνt0 : ν (tH0 c) ≠ 0 := char_apply_central_ne_zero (G := ↥c.H0) (t := tH0 c)
    (by simpa [tH0] using t_central_H0' c) (by simpa [tH0] using t_H0_sq c) hν
  intro hz
  have hνν : ν (tH0 c) + ν (tH0 c) = 0 := by
    nth_rewrite 2 [hz]
    ring
  have h2z : 2 * ν (tH0 c) = 0 := by
    calc
      2 * ν (tH0 c) = ν (tH0 c) + ν (tH0 c) := by ring
      _ = 0 := hνν
  rcases (mul_eq_zero.mp h2z) with h2z0 | hν0
  · norm_num at h2z0
  · exact hνt0 hν0

/-- Conjugation by `s` fixes the value of every `H0`-character at the central
involution `t` (because `s` fixes `t`). -/
private lemma conjChar_apply_tH0_eq (c : Hyp11 G) (h12 : Hyp12 c)
    (ν : ClassFunction (↥c.H0)) :
    conjChar c.H0 (s_normalizes_H0 c h12) ν (tH0 c) = ν (tH0 c) := by
  change ν (conjMonoidHom c.H0 c.s (s_normalizes_H0 c h12) (tH0 c)) = ν (tH0 c)
  congr 1
  apply Subtype.ext
  change c.s * c.t * c.s⁻¹ = c.t
  exact s_conj_t c

/-- Lemma 2.1 sign choice for the `(vi)`-step: if `ν^s ≠ ν` and not
`(|Lν| = 4 ∧ Lν^s = Lν)`, some `μ ∈ Lν` satisfies `μ^s ≠ μ` and
`μ(t) = −ν(t)`. -/
private lemma exists_mu_sign_choice (c : Hyp11 G) (h12 : Hyp12 c)
    [Fintype ↥(LambdaHom c.H0 c.U)] {ν : ClassFunction (↥c.H0)}
    (hν : IsIrreducibleCharacter ν)
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν ≠ ν)
    (hnot : ¬ ((orbit c.H0 c.U ν).card = 4 ∧
      conjChar c.H0 (s_normalizes_H0 c h12) ν ∈ orbit c.H0 c.U ν)) :
    ∃ μ : ClassFunction (↥c.H0), μ ∈ orbit c.H0 c.U ν ∧
      conjChar c.H0 (s_normalizes_H0 c h12) μ ≠ μ ∧
      μ (tH0 c) = -ν (tH0 c) := by
  classical
  let L := orbit c.H0 c.U ν
  let S1 := L.filter (fun μ => μ (tH0 c) = -ν (tH0 c))
  let F := L.filter (fun μ => conjChar c.H0 (s_normalizes_H0 c h12) μ = μ)
  have ht_sq : (tH0 c) ^ 2 = 1 := t_H0_sq c
  have ht_central : ∀ g : ↥c.H0, (tH0 c) * g = g * (tH0 c) := t_central_H0' c
  -- exactly half of `L` has `t` in the kernel
  have hhalf : ((L.filter (fun μ => μ (tH0 c) = μ 1)).card * 2 = L.card) := by
    simpa [L] using lemma_2_1_a c.H0 c.U (U_normal_subgroupOf c h12) (lambda_hcomm c h12)
      (t_not_mem_U c) ht_sq ht_central hν
  -- `|S1| = |L|/2` (the other half)
  have hS1 : S1.card * 2 = L.card := by
    have hsignν := char_apply_central_sign ht_central ht_sq hν
    rcases hsignν with hνt | hνt
    · -- ν(t) = ν(1): S1 = complement of the kernel filter
      have hEq : S1 = L.filter (fun μ => ¬ μ (tH0 c) = μ 1) := by
        ext μ
        simp only [S1, Finset.mem_filter]
        constructor
        · intro h
          rcases h with ⟨hμL, hμt⟩
          refine ⟨hμL, ?_⟩
          intro hμt1
          -- μ(t) = μ(1) = ν(1) = ν(t): contradicts μ(t) = −ν(t)
          have hdeg : μ 1 = ν 1 := orbit_mem_degree_eq c hμL
          have : ν (tH0 c) = -ν (tH0 c) := by
            calc
              ν (tH0 c) = ν 1 := hνt
              _ = μ 1 := hdeg.symm
              _ = μ (tH0 c) := hμt1.symm
              _ = -ν (tH0 c) := hμt
          exact (central_involution_char_ne_neg c hν) this
        · intro h
          rcases h with ⟨hμL, hμt⟩
          refine ⟨hμL, ?_⟩
          have hμirr : IsIrreducibleCharacter μ := orbit_mem_isIrreducible c.H0 c.U hν hμL
          have hdeg : μ 1 = ν 1 := orbit_mem_degree_eq c hμL
          rcases char_apply_central_sign ht_central ht_sq hμirr with hμt' | hμt'
          · -- μ(t) = μ(1): contradicts μ(t) ≠ μ(1)
            exfalso
            exact hμt hμt'
          · -- μ(t) = −μ(1) = −ν(1) = −ν(t)
            calc
              μ (tH0 c) = -μ 1 := hμt'
              _ = -ν 1 := by rw [hdeg]
              _ = -ν (tH0 c) := by rw [← hνt]
      calc
        S1.card * 2 = (L.filter (fun μ => ¬ μ (tH0 c) = μ 1)).card * 2 := by rw [hEq]
        _ = L.card := by
              have hpart : L = L.filter (fun μ => μ (tH0 c) = μ 1) ∪
                  L.filter (fun μ => ¬ μ (tH0 c) = μ 1) := by
                ext μ
                by_cases h : μ (tH0 c) = μ 1 <;> simp [h]
              have hdisj : Disjoint (L.filter (fun μ => μ (tH0 c) = μ 1))
                  (L.filter (fun μ => ¬ μ (tH0 c) = μ 1)) := by
                rw [Finset.disjoint_iff_ne]
                intro a ha b hb hEq
                have ha1 : a (tH0 c) = a 1 := (Finset.mem_filter.mp ha).2
                have hb1 : ¬ b (tH0 c) = b 1 := (Finset.mem_filter.mp hb).2
                exact hb1 (by simpa [hEq] using ha1)
              have hcard : (L.filter (fun μ => μ (tH0 c) = μ 1)).card +
                  (L.filter (fun μ => ¬ μ (tH0 c) = μ 1)).card = L.card := by
                rw [← Finset.card_union_of_disjoint hdisj, ← hpart]
              -- (a + b) = L and 2a = L ⟹ 2b = L
              have h2' : (L.filter (fun μ => ¬ μ (tH0 c) = μ 1)).card * 2 = L.card := by
                have h1 : (L.filter (fun μ => μ (tH0 c) = μ 1)).card * 2 +
                    (L.filter (fun μ => ¬ μ (tH0 c) = μ 1)).card * 2 = L.card * 2 := by
                  rw [← hcard]
                  ring
                omega
              exact h2'
    · -- ν(t) = −ν(1): S1 = the kernel filter
      have hEq : S1 = L.filter (fun μ => μ (tH0 c) = μ 1) := by
        ext μ
        simp only [S1, Finset.mem_filter]
        constructor
        · intro h
          rcases h with ⟨hμL, hμt⟩
          refine ⟨hμL, ?_⟩
          have hdeg : μ 1 = ν 1 := orbit_mem_degree_eq c hμL
          -- μ(t) = −ν(t) = −(−ν(1)) = ν(1) = μ(1)
          calc
            μ (tH0 c) = -ν (tH0 c) := hμt
            _ = -(-ν 1) := by rw [hνt]
            _ = ν 1 := by ring
            _ = μ 1 := hdeg.symm
        · intro h
          rcases h with ⟨hμL, hμt⟩
          refine ⟨hμL, ?_⟩
          have hdeg : μ 1 = ν 1 := orbit_mem_degree_eq c hμL
          -- μ(t) = μ(1) = ν(1) = −(−ν(1)) = −ν(t)
          calc
            μ (tH0 c) = μ 1 := hμt
            _ = ν 1 := hdeg
            _ = -ν (tH0 c) := by rw [hνt]; ring
      calc
        S1.card * 2 = (L.filter (fun μ => μ (tH0 c) = μ 1)).card * 2 := by rw [hEq]
        _ = L.card := hhalf
  -- some element of `S1` is not `s`-fixed
  have hS1neF : ∃ μ : ClassFunction (↥c.H0), μ ∈ S1 ∧ μ ∉ F := by
    by_contra h
    have hsub : S1 ⊆ F := by
      intro μ hμ
      by_contra hμF
      exact h ⟨μ, hμ, hμF⟩
    have hcardle : S1.card ≤ F.card := Finset.card_le_card hsub
    have hF : F.card ≤ 2 := by
      simpa [F] using orbit_s_fixed_card_le_two c h12 hν
    have hS1pos : 0 < S1.card := by
      -- |S1|·2 = |L| and L ≠ ∅
      have hLne : L.Nonempty := ⟨ν, by
        refine Finset.mem_image.mpr ⟨(1 : LambdaHom c.H0 c.U), Finset.mem_univ _, ?_⟩
        exact (Finset.mem_filter.mp (one_mem_stab c.H0 c.U ν)).2⟩
      have hLpos : 0 < L.card := Finset.card_pos.mpr hLne
      have hS1' : S1.card * 2 = L.card := hS1
      by_contra hz
      have hS10 : S1.card = 0 := Nat.eq_zero_of_not_pos hz
      omega
    have hLle : L.card ≤ 4 := by
      calc
        L.card = S1.card * 2 := hS1.symm
        _ ≤ F.card * 2 := by
              exact Nat.mul_le_mul_right 2 hcardle
        _ ≤ 4 := by omega
    -- |L| is even (|L| = 2·|S1|), so |L| ∈ {2, 4}; both contradict
    have hνsL : conjChar c.H0 (s_normalizes_H0 c h12) ν ∈ L := by
      by_contra hνsL
      -- then no orbit member is fixed: F = ∅, so |S1| ≤ 0, contradiction
      have hF' : F = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro μ hμ
        rcases (Finset.mem_filter.mp hμ) with ⟨hμL, hμs⟩
        exact hνsL (orbit_mem_conj_fixed_implies_conj_mem c h12 hμL hμs)
      have : F.card = 0 := by rw [hF']; simp
      omega
    have hEq4 : L.card = 4 := by
      -- |L| ∈ {2, 4} and |L| ≠ 2
      have hne2 : L.card ≠ 2 := by
        intro h2
        -- |L| = 2 and ν^s ∈ L ⟹ ν^s = ν (all fixed by Lemma 2.1(ii))
        have hF2 : F.card = 2 := by
          have : ((orbit c.H0 c.U ν).filter (fun μ =>
              conjChar c.H0 (s_normalizes_H0 c h12) μ = μ)).card = 2 :=
            lemma_2_1_b c h12 hν hνsL
          simpa [F, L] using this
        have hFeq : F = L := Finset.eq_of_subset_of_card_le
          (by intro μ hμ; exact (Finset.mem_filter.mp hμ).1)
          (by rw [hF2, h2])
        have hνF : ν ∈ F := by
          rw [hFeq]
          exact Finset.mem_image.mpr ⟨(1 : LambdaHom c.H0 c.U), Finset.mem_univ _,
            (Finset.mem_filter.mp (one_mem_stab c.H0 c.U ν)).2⟩
        exact hνs (by simpa using (Finset.mem_filter.mp hνF).2)
      have hL2 : 2 ∣ L.card := ⟨S1.card, by simpa [mul_comm] using hS1.symm⟩
      have hLcases : L.card = 0 ∨ L.card = 2 ∨ L.card = 4 := by omega
      rcases hLcases with h0 | h2 | h4
      · have : L.Nonempty := ⟨ν, by
          refine Finset.mem_image.mpr ⟨(1 : LambdaHom c.H0 c.U), Finset.mem_univ _, ?_⟩
          exact (Finset.mem_filter.mp (one_mem_stab c.H0 c.U ν)).2⟩
        omega
      · exfalso
        exact hne2 h2
      · exact h4
    exact hnot ⟨hEq4, by simpa [L] using hνsL⟩
  rcases hS1neF with ⟨μ, hμS1, hμF⟩
  refine ⟨μ, (Finset.mem_filter.mp hμS1).1, ?_, (Finset.mem_filter.mp hμS1).2⟩
  intro hμs
  exact hμF (by
    change μ ∈ L.filter (fun μ => conjChar c.H0 (s_normalizes_H0 c h12) μ = μ)
    rw [Finset.mem_filter]
    exact ⟨(Finset.mem_filter.mp hμS1).1, hμs⟩)

/-- The class-sum evaluation used in the `(vi)`-step: for `φ = ±χ₀` with
`χ₀` irreducible, `Σ_{χ∈Irr(G)} χ(t)²/χ(1)·(χ,φ)_G = φ(t)²/φ(1)`. -/
private lemma sum_chi_t_sq_over_deg (c : Hyp11 G) {φ χ₀ : ClassFunction G}
    (hχ₀ : IsIrreducibleCharacter χ₀) (hφ : φ = χ₀ ∨ φ = -χ₀) :
    (∑ χ : Irr G, (χ.1 c.t ^ 2 / χ.1 1) * scalarProduct G χ.1 φ) =
      (φ c.t) ^ 2 / φ 1 := by
  classical
  rcases hφ with hφpos | hφneg
  · have h1 : (∑ χ : Irr G, (χ.1 c.t ^ 2 / χ.1 1) * scalarProduct G χ.1 χ₀) =
        χ₀ c.t ^ 2 / χ₀ 1 := by
      rw [Finset.sum_eq_single ⟨χ₀, hχ₀⟩]
      · simp [scalarProduct_irr_ite hχ₀ hχ₀]
      · intro b hb hbne
        have hbne' : b.1 ≠ χ₀ := by
          intro h
          exact hbne (Subtype.ext h)
        simp [scalarProduct_irr_ite b.2 hχ₀, hbne']
      · intro hb
        exact False.elim (hb (Finset.mem_univ _))
    rwa [hφpos]
  · have h1 : (∑ χ : Irr G, (χ.1 c.t ^ 2 / χ.1 1) * scalarProduct G χ.1 (-χ₀)) =
        -χ₀ c.t ^ 2 / χ₀ 1 := by
      rw [Finset.sum_eq_single ⟨χ₀, hχ₀⟩]
      · simp [scalarProduct_irr_ite hχ₀ hχ₀, scalarProduct_neg_right]
        ring
      · intro b hb hbne
        have hbne' : b.1 ≠ χ₀ := by
          intro h
          exact hbne (Subtype.ext h)
        simp [scalarProduct_irr_ite b.2 hχ₀, scalarProduct_neg_right, hbne']
      · intro hb
        exact False.elim (hb (Finset.mem_univ _))
    rw [hφneg]
    calc
      (∑ χ : Irr G, (χ.1 c.t ^ 2 / χ.1 1) * scalarProduct G χ.1 (-χ₀))
          = -χ₀ c.t ^ 2 / χ₀ 1 := h1
      _ = (-χ₀ c.t) ^ 2 / -χ₀ 1 := by
            field_simp [irreducible_char_one_ne_zero hχ₀]

/-- The `(vi)`-step, reduced: with `δ* = (μ−ν)* = μ̃−ν̃` (field (ii)) and the
`V = 0` content of Lemma 2.2 (explicit hypothesis), `μ̃(t)² = ν̃(t)²`. -/
private lemma tilde_sq_eq_of_V_zero (c : Hyp11 G)
    [Fintype ↥(LambdaHom c.H0 c.U)]
    {tilde : Irr (↥c.H0) → ClassFunction G}
    (hgen : ∀ ν : Irr (↥c.H0), IsGeneralizedCharacter (tilde ν))
    {μ ν : Irr (↥c.H0)}
    (hμnorm : normSq G (tilde μ) = 1) (hνnorm : normSq G (tilde ν) = 1)
    (hind : ∀ μ ν : Irr (↥c.H0), μ.1 ∈ orbit c.H0 c.U ν.1 →
      inducedClassFunction c.H0 (μ.1 - ν.1) = tilde μ - tilde ν)
    (hμL : μ.1 ∈ orbit c.H0 c.U ν.1)
    (hV : (∑ χ : Irr G, (χ.1 c.t ^ 2 / χ.1 1) *
      scalarProduct G χ.1 (inducedClassFunction c.H0 (μ.1 - ν.1))) = 0) :
    (tilde μ c.t) ^ 2 = (tilde ν c.t) ^ 2 := by
  classical
  rcases norm_one_signed_irreducible (hgen μ) hμnorm with ⟨χ₁, hχ₁, hμcase⟩
  rcases norm_one_signed_irreducible (hgen ν) hνnorm with ⟨χ₂, hχ₂, hνcase⟩
  have hδeq : inducedClassFunction c.H0 (μ.1 - ν.1) = tilde μ - tilde ν := hind μ ν hμL
  -- δ*(1) = 0 (degrees are equal on an orbit)
  have hδ1 : (inducedClassFunction c.H0 (μ.1 - ν.1)) 1 = 0 := by
    unfold inducedClassFunction
    have hsum : (∑ x : G, (if hx : x⁻¹ * 1 * x ∈ c.H0 then (μ.1 - ν.1) ⟨x⁻¹ * 1 * x, hx⟩ else 0)) =
        Fintype.card G * (μ.1 1 - ν.1 1) := by
      calc
        (∑ x : G, (if hx : x⁻¹ * 1 * x ∈ c.H0 then (μ.1 - ν.1) ⟨x⁻¹ * 1 * x, hx⟩ else 0))
            = ∑ x : G, (μ.1 1 - ν.1 1) := by
                refine Finset.sum_congr rfl ?_
                intro x hx
                have hx1 : x⁻¹ * 1 * x = 1 := by group
                have hxmem : x⁻¹ * 1 * x ∈ c.H0 := by
                  rw [hx1]
                  exact c.H0.one_mem
                rw [dif_pos hxmem]
                have hxeq : (⟨x⁻¹ * 1 * x, hxmem⟩ : ↥c.H0) = (1 : ↥c.H0) := by
                  apply Subtype.ext
                  exact hx1
                rw [hxeq]
                rfl
        _ = Fintype.card G * (μ.1 1 - ν.1 1) := by
                rw [Finset.sum_const]
                simp [nsmul_eq_mul]
    rw [hsum]
    have hdeg : μ.1 1 = ν.1 1 := orbit_mem_degree_eq c hμL
    simp [hdeg]
  have hmu1 : tilde μ 1 = tilde ν 1 := by
    have h := congrFun hδeq 1
    rw [hδ1] at h
    have h' : tilde μ 1 - tilde ν 1 = 0 := by simpa using h.symm
    exact sub_eq_zero.mp h'
  have hmu1_ne : tilde μ 1 ≠ 0 := by
    rcases hμcase with hμcase1 | hμcase2
    · rw [hμcase1]
      exact irreducible_char_one_ne_zero hχ₁
    · rw [hμcase2]
      simpa using irreducible_char_one_ne_zero hχ₁
  have hν1_ne : tilde ν 1 ≠ 0 := by
    rcases hνcase with hνcase1 | hνcase2
    · rw [hνcase1]
      exact irreducible_char_one_ne_zero hχ₂
    · rw [hνcase2]
      simpa using irreducible_char_one_ne_zero hχ₂
  -- split V over the two signed irreducibles
  have hsplit : (∑ χ : Irr G, (χ.1 c.t ^ 2 / χ.1 1) *
        scalarProduct G χ.1 (inducedClassFunction c.H0 (μ.1 - ν.1))) =
      (∑ χ : Irr G, (χ.1 c.t ^ 2 / χ.1 1) * scalarProduct G χ.1 (tilde μ)) -
        (∑ χ : Irr G, (χ.1 c.t ^ 2 / χ.1 1) * scalarProduct G χ.1 (tilde ν)) := by
    rw [hδeq]
    simp [scalarProduct_sub_right, mul_sub, Finset.sum_sub_distrib]
  have hVμν : (tilde μ c.t) ^ 2 / tilde μ 1 - (tilde ν c.t) ^ 2 / tilde ν 1 = 0 := by
    have hA : (∑ χ : Irr G, (χ.1 c.t ^ 2 / χ.1 1) * scalarProduct G χ.1 (tilde μ)) =
        (tilde μ c.t) ^ 2 / tilde μ 1 := sum_chi_t_sq_over_deg c (φ := tilde μ) (χ₀ := χ₁) hχ₁ hμcase
    have hB : (∑ χ : Irr G, (χ.1 c.t ^ 2 / χ.1 1) * scalarProduct G χ.1 (tilde ν)) =
        (tilde ν c.t) ^ 2 / tilde ν 1 := sum_chi_t_sq_over_deg c (φ := tilde ν) (χ₀ := χ₂) hχ₂ hνcase
    rw [← hA, ← hB, ← hsplit]
    exact hV
  rw [hmu1] at hVμν
  have hVμν' : (tilde μ c.t) ^ 2 - (tilde ν c.t) ^ 2 = 0 := by
    field_simp [hmu1_ne] at hVμν
    simpa using hVμν
  exact sub_eq_zero.mp hVμν'

/-- The `(vi)`-argument of the Coherence Theorem: `ν̃(t) = 2ν(t)` for
`ν^s ≠ ν`, from the fields (i),(ii),(v), the Lemma-2.1 sign choice, the
`V = 0` content of Lemma 2.2, and `|H : H0| = 2` (the two blocked inputs as
explicit hypotheses; see the theorem card). -/
private lemma at_t_of_V_zero (c : Hyp11 G) (h12 : Hyp12 c)
    [Fintype ↥(LambdaHom c.H0 c.U)]
    (hH0index : (c.H0.subgroupOf c.H).index = 2)
    (tilde : Irr (↥c.H0) → ClassFunction G)
    (hgen : ∀ ν : Irr (↥c.H0), IsGeneralizedCharacter (tilde ν))
    (hnorm : ∀ ν : Irr (↥c.H0), normSq G (tilde ν) =
      (if conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1 then 2 else 1))
    (hind : ∀ μ ν : Irr (↥c.H0), μ.1 ∈ orbit c.H0 c.U ν.1 →
      inducedClassFunction c.H0 (μ.1 - ν.1) = tilde μ - tilde ν)
    (honT : ∀ μ ν : Irr (↥c.H0), μ.1 ∈ orbit c.H0 c.U ν.1 →
      ∀ g : G, g ∈ c.T → (hg : g ∈ c.H) →
      tilde μ g - tilde ν g =
        inducedFromSub (h12.H0_normal_in_H).1 μ.1 ⟨g, hg⟩ -
          inducedFromSub (h12.H0_normal_in_H).1 ν.1 ⟨g, hg⟩)
    {μ ν : Irr (↥c.H0)} (hμL : μ.1 ∈ orbit c.H0 c.U ν.1)
    (hμs : conjChar c.H0 (s_normalizes_H0 c h12) μ.1 ≠ μ.1)
    (hμt : μ.1 (tH0 c) = -ν.1 (tH0 c))
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 ≠ ν.1)
    (hV : (∑ χ : Irr G, (χ.1 c.t ^ 2 / χ.1 1) *
      scalarProduct G χ.1 (inducedClassFunction c.H0 (μ.1 - ν.1))) = 0) :
    tilde ν c.t = 2 * ν.1 (tH0 c) := by
  classical
  have hμnorm1 : normSq G (tilde μ) = 1 := by
    by_cases hμ : conjChar c.H0 (s_normalizes_H0 c h12) μ.1 = μ.1
    · exact False.elim (hμs hμ)
    · simpa [hμ] using hnorm μ
  have hνnorm1 : normSq G (tilde ν) = 1 := by
    by_cases hν : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1
    · exact False.elim (hνs hν)
    · simpa [hν] using hnorm ν
  have hsq := tilde_sq_eq_of_V_zero c (hgen := hgen) (hμnorm := hμnorm1)
    (hνnorm := hνnorm1) (hind := hind) (μ := μ) (ν := ν) hμL hV
  -- hsq : (tilde μ c.t)^2 = (tilde ν c.t)^2
  have htmem : c.t ∈ c.T := ⟨S0_le_H0 c c.t_mem_S0, t_not_mem_U c⟩
  have hHmem : c.t ∈ c.H := S_le_H c (c.S0_le_S c.t_mem_S0)
  -- (v) + Remark 1.4: μ̃(t) − ν̃(t) = μ^H(t) − ν^H(t) = 2μ(t) − 2ν(t) = 4μ(t)
  have hsh : c.s * c.t * c.s⁻¹ ∈ c.H0 := by
    rw [s_conj_t c]
    exact (tH0 c).2
  have hmuH : (inducedFromSub (h12.H0_normal_in_H).1 μ.1) ⟨c.t, (h12.H0_normal_in_H).1 (tH0 c).2⟩ =
      2 * μ.1 (tH0 c) := by
    have h1 := (remark_1_4 (h12.H0_normal_in_H).1 hH0index (S_le_H c c.s_mem_S)
      (s_not_mem_H0' c h12) μ.2).1 c.t (tH0 c).2 hsh
    have h2 : μ.1 ⟨c.s * c.t * c.s⁻¹, hsh⟩ = μ.1 (tH0 c) := by
      exact congrArg μ.1 (by
        apply Subtype.ext
        exact s_conj_t c)
    have h3 : μ.1 ⟨c.t, (tH0 c).2⟩ = μ.1 (tH0 c) := rfl
    calc
      (inducedFromSub (h12.H0_normal_in_H).1 μ.1) ⟨c.t, (h12.H0_normal_in_H).1 (tH0 c).2⟩
          = μ.1 ⟨c.t, (tH0 c).2⟩ + μ.1 ⟨c.s * c.t * c.s⁻¹, hsh⟩ := h1
      _ = 2 * μ.1 (tH0 c) := by simp [h2, h3, two_mul]
  have hnuH : (inducedFromSub (h12.H0_normal_in_H).1 ν.1) ⟨c.t, (h12.H0_normal_in_H).1 (tH0 c).2⟩ =
      2 * ν.1 (tH0 c) := by
    have h1 := (remark_1_4 (h12.H0_normal_in_H).1 hH0index (S_le_H c c.s_mem_S)
      (s_not_mem_H0' c h12) ν.2).1 c.t (tH0 c).2 hsh
    have h2 : ν.1 ⟨c.s * c.t * c.s⁻¹, hsh⟩ = ν.1 (tH0 c) := by
      exact congrArg ν.1 (by
        apply Subtype.ext
        exact s_conj_t c)
    have h3 : ν.1 ⟨c.t, (tH0 c).2⟩ = ν.1 (tH0 c) := rfl
    calc
      (inducedFromSub (h12.H0_normal_in_H).1 ν.1) ⟨c.t, (h12.H0_normal_in_H).1 (tH0 c).2⟩
          = ν.1 ⟨c.t, (tH0 c).2⟩ + ν.1 ⟨c.s * c.t * c.s⁻¹, hsh⟩ := h1
      _ = 2 * ν.1 (tH0 c) := by simp [h2, h3, two_mul]
  have hdiff : tilde μ c.t - tilde ν c.t = 4 * μ.1 (tH0 c) := by
    have h1 := honT μ ν hμL c.t htmem hHmem
    have h2 : (inducedFromSub (h12.H0_normal_in_H).1 μ.1) ⟨c.t, hHmem⟩ = 2 * μ.1 (tH0 c) := by
      convert hmuH using 1
    have h3 : (inducedFromSub (h12.H0_normal_in_H).1 ν.1) ⟨c.t, hHmem⟩ = 2 * ν.1 (tH0 c) := by
      convert hnuH using 1
    rw [h1, h2, h3]
    rw [hμt]
    ring
  have hdiff_ne : tilde μ c.t - tilde ν c.t ≠ 0 := by
    rw [hdiff]
    have hμt0 : μ.1 (tH0 c) ≠ 0 := char_apply_central_ne_zero
      (G := ↥c.H0) (t := tH0 c) (by simpa [tH0] using t_central_H0' c)
      (by simpa [tH0] using t_H0_sq c) μ.2
    intro hz
    rcases (mul_eq_zero.mp hz) with h4 | hν0
    · norm_num at h4
    · exact hμt0 hν0
  have hsum0 : tilde μ c.t + tilde ν c.t = 0 := by
    have hprod : (tilde μ c.t + tilde ν c.t) * (tilde μ c.t - tilde ν c.t) = 0 := by
      calc
        (tilde μ c.t + tilde ν c.t) * (tilde μ c.t - tilde ν c.t)
            = (tilde μ c.t) ^ 2 - (tilde ν c.t) ^ 2 := by ring
        _ = 0 := by rw [hsq]; ring
    exact (mul_eq_zero.mp hprod).resolve_right hdiff_ne
  have hb : tilde ν c.t = -tilde μ c.t := by
    linear_combination hsum0
  have ha : tilde μ c.t = 2 * μ.1 (tH0 c) := by
    have h2m : 2 * tilde μ c.t = 4 * μ.1 (tH0 c) := by
      linear_combination hdiff + hb
    calc
      tilde μ c.t = (2 * tilde μ c.t) / 2 := by ring
      _ = (4 * μ.1 (tH0 c)) / 2 := by rw [h2m]
      _ = 2 * μ.1 (tH0 c) := by ring
  calc
    tilde ν c.t = -tilde μ c.t := hb
    _ = -(2 * μ.1 (tH0 c)) := by rw [ha]
    _ = 2 * ν.1 (tH0 c) := by rw [hμt]; ring

/-! ## The orbit-lift construction (route `R1-orbitwise`, step `orbit-lift`)

For a `Λ`-orbit `L` of `Irr(H0)` with induced characters `θ₁, …, θ_n` (the set
`thetaOfOrbit L`), the paper constructs pairwise disjoint `θ̃_j` with
`|θ̃_j| = |θ_j|` and `δ_i* = θ̃_1 − θ̃_i`, where `δ_i* := (ν₁ − ν_i)^G`
(Convention B; see the theorem card).  Formalized here:

* the orbit infrastructure (`orbit_self_mem`, `orbit_eq_of_mem`,
  `orbit_mem_eq_on_U`, `conjLambda`, `orbit_conjChar_subset`, …);
* the `θ`-facts (`theta_pair_scalar_H0`, `theta_pair_scalar_H`,
  `theta_norm`, `theta_pair_orth`, `theta_eq_imp_conj`): the expansion
  `(θᵢ, θⱼ)_H = (1/2)·[(νᵢ,νⱼ) + (νᵢ,νⱼ^s) + (νᵢ^s,νⱼ) + (νᵢ^s,νⱼ^s)]`
  (Remark 1.4, `H0_index`);
* the `δ`-facts (`delta_pair_eq`, `delta_norm`): the Brauer–Suzuki
  Lemma 1.3 pairings `(δᵢ*, δⱼ*)_G = |θ₁|` (i ≠ j) and
  `|δᵢ*| = |θ₁| + |θᵢ|` (the support-on-`T` input is the `U`-agreement of
  orbit members);
* `exists_common_constituent_self`: the common constituent `χ₂₃` of `δ₂*`,
  `δ₃*` with multiplicity one (the `θ̃₁ := χ₂₃` step);
* `ThetaLift` and `exists_theta_lift`: the per-orbit lift.

The genuinely blocked inputs are recorded as explicit hypotheses of
`exists_theta_lift` and the assembly: the `V = 0` content of `lemma_2_2`
case 1 (the (vi)-step and the n ≥ 5 contradiction). -/

/-- A member of an orbit: `ν ∈ orbit ν`. -/
private lemma orbit_self_mem (c : Hyp11 G) [Fintype ↥(LambdaHom c.H0 c.U)]
    (ν : ClassFunction (↥c.H0)) : ν ∈ orbit c.H0 c.U ν := by
  classical
  refine Finset.mem_image.mpr ⟨(1 : LambdaHom c.H0 c.U), Finset.mem_univ _, ?_⟩
  exact (Finset.mem_filter.mp (one_mem_stab c.H0 c.U ν)).2

/-- Orbits are equal-or-disjoint: `μ ∈ orbit ν` implies `orbit μ = orbit ν`. -/
private lemma orbit_eq_of_mem (c : Hyp11 G) [Fintype ↥(LambdaHom c.H0 c.U)]
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

/-- Members of the same orbit agree on `U` (the `Λ`-characters are trivial on `U`). -/
private lemma orbit_mem_eq_on_U (c : Hyp11 G) [Fintype ↥(LambdaHom c.H0 c.U)]
    {ν μ : ClassFunction (↥c.H0)} (hμ : μ ∈ orbit c.H0 c.U ν)
    {x : ↥c.H0} (hx : (x : G) ∈ c.U) : μ x = ν x := by
  classical
  rcases (Finset.mem_image.mp hμ) with ⟨l, hl, rfl⟩
  have hlU : l.1 x = 1 := l.2 x hx
  simp [LambdaChar, hlU]

/-- The `s`-conjugate of a `Λ`-character is again a `Λ`-character
(`s` normalizes `U`). -/
private def conjLambda (c : Hyp11 G) (h12 : Hyp12 c) (l : LambdaHom c.H0 c.U) :
    LambdaHom c.H0 c.U := by
  classical
  refine ⟨l.1.comp (conjMonoidHom c.H0 c.s (s_normalizes_H0 c h12)), ?_⟩
  intro u hu
  change l.1 (conjMonoidHom c.H0 c.s (s_normalizes_H0 c h12) u) = 1
  exact l.2 (conjMonoidHom c.H0 c.s (s_normalizes_H0 c h12) u) (by
    change c.s * (u : G) * c.s⁻¹ ∈ c.U
    exact s_normalizes_U c hu)

/-- `s·(s·x·s⁻¹)·s⁻¹ = x` for the involution `s`. -/
private lemma s_conj_sq (c : Hyp11 G) (x : G) : c.s * (c.s * x * c.s⁻¹) * c.s⁻¹ = x := by
  have hs2 : c.s * c.s = 1 := by simpa [pow_two] using c.s_involution.2
  calc
    c.s * (c.s * x * c.s⁻¹) * c.s⁻¹ = (c.s * c.s) * x * (c.s⁻¹ * c.s⁻¹) := by group
    _ = x := by
      have hs2' : c.s⁻¹ * c.s⁻¹ = 1 := by
        rw [← mul_inv_rev]
        rw [hs2]
        simp
      rw [hs2, hs2']
      simp

/-- Conjugation by `s` is an involution on `H0`. -/
private lemma conjMonoidHom_conjMonoidHom (c : Hyp11 G) (h12 : Hyp12 c)
    (x : ↥c.H0) :
    (conjMonoidHom c.H0 c.s (s_normalizes_H0 c h12)
      (conjMonoidHom c.H0 c.s (s_normalizes_H0 c h12) x) : ↥c.H0) = x := by
  apply Subtype.ext
  exact s_conj_sq c (x : G)

/-- Conjugation by `s` maps the orbit of `ν^s` into the orbit of `ν`:
`μ ∈ orbit(ν^s)` implies `μ^s ∈ orbit ν`. -/
private lemma orbit_conjChar_subset (c : Hyp11 G) (h12 : Hyp12 c)
    [Fintype ↥(LambdaHom c.H0 c.U)] {ν : ClassFunction (↥c.H0)}
    (μ : ClassFunction (↥c.H0))
    (hμ : μ ∈ orbit c.H0 c.U (conjChar c.H0 (s_normalizes_H0 c h12) ν)) :
    conjChar c.H0 (s_normalizes_H0 c h12) μ ∈ orbit c.H0 c.U ν := by
  classical
  rcases (Finset.mem_image.mp hμ) with ⟨l, hl, rfl⟩
  refine Finset.mem_image.mpr ⟨conjLambda c h12 l, Finset.mem_univ _, ?_⟩
  ext x
  change (LambdaChar (conjLambda c h12 l).1 * ν) x =
    (conjChar c.H0 (s_normalizes_H0 c h12) (LambdaChar l.1 *
      conjChar c.H0 (s_normalizes_H0 c h12) ν)) x
  simp [conjChar, conjLambda, LambdaChar]
  have hx : (conjMonoidHom c.H0 c.s (s_normalizes_H0 c h12) x : ↥c.H0) =
      ⟨c.s * (x : G) * c.s⁻¹, s_normalizes_H0 c h12 x⟩ := rfl
  rw [hx]
  have hx' : (conjMonoidHom c.H0 c.s (s_normalizes_H0 c h12)
      ⟨c.s * (x : G) * c.s⁻¹, s_normalizes_H0 c h12 x⟩ : ↥c.H0) = x := by
    apply Subtype.ext
    exact s_conj_sq c (x : G)
  rw [hx']

/-- Conjugation by `s` maps the orbit of `ν` into the orbit of `ν^s`. -/
private lemma orbit_subset_conjChar (c : Hyp11 G) (h12 : Hyp12 c)
    [Fintype ↥(LambdaHom c.H0 c.U)] {ν : ClassFunction (↥c.H0)}
    (μ : ClassFunction (↥c.H0))
    (hμ : μ ∈ orbit c.H0 c.U ν) :
    conjChar c.H0 (s_normalizes_H0 c h12) μ ∈
      orbit c.H0 c.U (conjChar c.H0 (s_normalizes_H0 c h12) ν) := by
  classical
  rcases (Finset.mem_image.mp hμ) with ⟨l, hl, rfl⟩
  refine Finset.mem_image.mpr ⟨conjLambda c h12 l, Finset.mem_univ _, ?_⟩
  ext x
  change (LambdaChar (conjLambda c h12 l).1 * conjChar c.H0 (s_normalizes_H0 c h12) ν) x =
    (conjChar c.H0 (s_normalizes_H0 c h12) (LambdaChar l.1 * ν)) x
  simp [conjChar, conjLambda, LambdaChar]

/-- `s` is an involution, so conjugation by `s` is an involution on class
functions: `(ν^s)^s = ν`. -/
private lemma conjChar_conjChar (c : Hyp11 G) (h12 : Hyp12 c)
    (ν : ClassFunction (↥c.H0)) :
    conjChar c.H0 (s_normalizes_H0 c h12)
      (conjChar c.H0 (s_normalizes_H0 c h12) ν) = ν := by
  classical
  ext x
  simp [conjChar]
  rw [conjMonoidHom_conjMonoidHom c h12 x]

/-- The set of characters of `H` induced from the members of the orbit `L`. -/
private def thetaOfOrbit (c : Hyp11 G) (h12 : Hyp12 c)
    (L : Finset (ClassFunction (↥c.H0))) : Finset (ClassFunction (↥c.H)) := by
  classical
  exact L.image (fun φ : ClassFunction (↥c.H0) => inducedFromSub (h12.H0_normal_in_H).1 φ)

/-- `ν^H ∈ Θ(L)` for `ν ∈ L`. -/
private lemma thetaOfOrbit_mem (c : Hyp11 G) (h12 : Hyp12 c)
    {L : Finset (ClassFunction (↥c.H0))} {ν : ClassFunction (↥c.H0)}
    (hν : ν ∈ L) : inducedFromSub (h12.H0_normal_in_H).1 ν ∈ thetaOfOrbit c h12 L := by
  classical
  exact Finset.mem_image.mpr ⟨ν, hν, rfl⟩

/-- `ν^H ∈ Θ(orbit ν)`. -/
private lemma thetaOfOrbit_self (c : Hyp11 G) (h12 : Hyp12 c)
    [Fintype ↥(LambdaHom c.H0 c.U)] (ν : ClassFunction (↥c.H0)) :
    inducedFromSub (h12.H0_normal_in_H).1 ν ∈
      thetaOfOrbit c h12 (orbit c.H0 c.U ν) := by
  classical
  exact thetaOfOrbit_mem c h12 (orbit_self_mem c ν)

/-- `(ν^s)^H = ν^H` pointwise on `H` (Remark 1.4, with `|H : H0| = 2`). -/
private lemma inducedFromSub_conjChar_eq (c : Hyp11 G) (h12 : Hyp12 c)
    (hH0index : (c.H0.subgroupOf c.H).index = 2)
    {ν : ClassFunction (↥c.H0)} (hν : IsIrreducibleCharacter ν) :
    inducedFromSub (h12.H0_normal_in_H).1 (conjChar c.H0 (s_normalizes_H0 c h12) ν) =
      inducedFromSub (h12.H0_normal_in_H).1 ν := by
  classical
  ext x
  by_cases hx : (x : G) ∈ c.H0
  · -- on H0: both sides equal ν⟨x⟩ + ν⟨s·x·s⁻¹⟩ (Remark 1.4 pointwise)
    have hs_inv : ∀ x : ↥c.H0, c.s⁻¹ * (x : G) * c.s ∈ c.H0 := by
      intro x
      simpa using (h12.H0_normal_in_H).2 c.s⁻¹ (c.H.inv_mem (s_mem_H c)) (x : G) x.2
    have hνs_irr : IsIrreducibleCharacter (conjChar c.H0 (s_normalizes_H0 c h12) ν) :=
      isIrreducibleCharacter_conjChar c.H0 (s_normalizes_H0 c h12) hs_inv hν
    have h1 := (remark_1_4 (h12.H0_normal_in_H).1 hH0index (S_le_H c c.s_mem_S)
      (s_not_mem_H0' c h12) hν).1 (x : G) hx (s_normalizes_H0 c h12 ⟨(x : G), hx⟩)
    have h2 := (remark_1_4 (h12.H0_normal_in_H).1 hH0index (S_le_H c c.s_mem_S)
      (s_not_mem_H0' c h12) (ν := conjChar c.H0 (s_normalizes_H0 c h12) ν)
      hνs_irr).1 (x : G) hx (s_normalizes_H0 c h12 ⟨(x : G), hx⟩)
    calc
      inducedFromSub (h12.H0_normal_in_H).1 (conjChar c.H0 (s_normalizes_H0 c h12) ν)
          ⟨(x : G), (h12.H0_normal_in_H).1 hx⟩
          = conjChar c.H0 (s_normalizes_H0 c h12) ν ⟨(x : G), hx⟩ +
              conjChar c.H0 (s_normalizes_H0 c h12) ν
                ⟨c.s * (x : G) * c.s⁻¹, s_normalizes_H0 c h12 ⟨(x : G), hx⟩⟩ := h2
      _ = ν ⟨c.s * (x : G) * c.s⁻¹, s_normalizes_H0 c h12 ⟨(x : G), hx⟩⟩ +
              ν ⟨(x : G), hx⟩ := by
            simp [conjChar]
            have hx1 : (conjMonoidHom c.H0 c.s (s_normalizes_H0 c h12) ⟨(x : G), hx⟩ : ↥c.H0) =
                ⟨c.s * (x : G) * c.s⁻¹, s_normalizes_H0 c h12 ⟨(x : G), hx⟩⟩ := rfl
            have hx2 : (conjMonoidHom c.H0 c.s (s_normalizes_H0 c h12)
                ⟨c.s * (x : G) * c.s⁻¹, s_normalizes_H0 c h12 ⟨(x : G), hx⟩⟩ : ↥c.H0) =
                ⟨(x : G), hx⟩ := by
              apply Subtype.ext
              exact s_conj_sq c (x : G)
            rw [hx1, hx2]
      _ = ν ⟨(x : G), hx⟩ + ν ⟨c.s * (x : G) * c.s⁻¹, s_normalizes_H0 c h12 ⟨(x : G), hx⟩⟩ := by
            rw [add_comm]
      _ = inducedFromSub (h12.H0_normal_in_H).1 ν ⟨(x : G), (h12.H0_normal_in_H).1 hx⟩ := h1.symm
  · -- outside H0: both vanish
    have h1 : inducedFromSub (h12.H0_normal_in_H).1 (conjChar c.H0 (s_normalizes_H0 c h12) ν) x = 0 :=
      inducedFromSub_eq_zero_of_not_mem c.H0 c.H (h12.H0_normal_in_H).1 hH0index
        (ν := conjChar c.H0 (s_normalizes_H0 c h12) ν) (x := x) hx
    have h2 : inducedFromSub (h12.H0_normal_in_H).1 ν x = 0 :=
      inducedFromSub_eq_zero_of_not_mem c.H0 c.H (h12.H0_normal_in_H).1 hH0index
        (ν := ν) (x := x) hx
    rw [h1, h2]

/-- Remark 1.4 pointwise on `H0`: `ν^H(x) = ν(x) + ν^s(x)`. -/
private lemma theta_pointwise (c : Hyp11 G) (h12 : Hyp12 c)
    (hH0index : (c.H0.subgroupOf c.H).index = 2)
    {ν : ClassFunction (↥c.H0)} (hν : IsIrreducibleCharacter ν)
    (x : ↥c.H0) :
    inducedFromSub (h12.H0_normal_in_H).1 ν
        ⟨(x : G), (h12.H0_normal_in_H).1 x.2⟩ =
      ν x + ν ⟨c.s * (x : G) * c.s⁻¹, s_normalizes_H0 c h12 x⟩ := by
  exact (remark_1_4 (h12.H0_normal_in_H).1 hH0index (S_le_H c c.s_mem_S)
    (s_not_mem_H0' c h12) hν).1 (x : G) x.2 (s_normalizes_H0 c h12 x)

/-- The θ-sets of `ν` and `ν^s` agree (the induced characters of an orbit are
`s`-invariant as a set). -/
private lemma thetaOfOrbit_conj_eq (c : Hyp11 G) (h12 : Hyp12 c)
    [Fintype ↥(LambdaHom c.H0 c.U)] {ν : ClassFunction (↥c.H0)}
    (hν : IsIrreducibleCharacter ν) :
    thetaOfOrbit c h12 (orbit c.H0 c.U (conjChar c.H0 (s_normalizes_H0 c h12) ν)) =
      thetaOfOrbit c h12 (orbit c.H0 c.U ν) := by
  have hs_inv : ∀ x : ↥c.H0, c.s⁻¹ * (x : G) * c.s ∈ c.H0 := by
    intro x
    simpa using (h12.H0_normal_in_H).2 c.s⁻¹ (c.H.inv_mem (s_mem_H c)) (x : G) x.2
  have hνs_irr : IsIrreducibleCharacter (conjChar c.H0 (s_normalizes_H0 c h12) ν) :=
    isIrreducibleCharacter_conjChar c.H0 (s_normalizes_H0 c h12) hs_inv hν
  apply Finset.ext
  intro θ
  constructor
  · intro hθ
    rcases (Finset.mem_image.mp hθ) with ⟨μ, hμ, rfl⟩
    refine Finset.mem_image.mpr ⟨conjChar c.H0 (s_normalizes_H0 c h12) μ, ?_, ?_⟩
    · exact orbit_conjChar_subset c h12 μ hμ
    · exact inducedFromSub_conjChar_eq c h12 (H0_index c h12)
        (orbit_mem_isIrreducible c.H0 c.U hνs_irr hμ)
  · intro hθ
    rcases (Finset.mem_image.mp hθ) with ⟨μ, hμ, rfl⟩
    refine Finset.mem_image.mpr ⟨conjChar c.H0 (s_normalizes_H0 c h12) μ, ?_, ?_⟩
    · exact orbit_subset_conjChar c h12 μ hμ
    · exact inducedFromSub_conjChar_eq c h12 (H0_index c h12)
        (orbit_mem_isIrreducible c.H0 c.U hν hμ)

/-- The scalar product over `H0` of two induced characters: `(θ₁, θ₂)_{H0} =
(ν₁,ν₂) + (ν₁,ν₂^s) + (ν₁^s,ν₂) + (ν₁^s,ν₂^s)` (the `θ = ν + ν^s` identity). -/
private lemma theta_pair_scalar_H0 (c : Hyp11 G) (h12 : Hyp12 c)
    (hH0index : (c.H0.subgroupOf c.H).index = 2)
    {ν₁ ν₂ : ClassFunction (↥c.H0)} (hν₁ : IsIrreducibleCharacter ν₁)
    (hν₂ : IsIrreducibleCharacter ν₂) :
    scalarProduct (↥c.H0)
        (fun y : ↥c.H0 => inducedFromSub (h12.H0_normal_in_H).1 ν₁
          ⟨(y : G), (h12.H0_normal_in_H).1 y.2⟩)
        (fun y : ↥c.H0 => inducedFromSub (h12.H0_normal_in_H).1 ν₂
          ⟨(y : G), (h12.H0_normal_in_H).1 y.2⟩) =
      scalarProduct (↥c.H0) ν₁ ν₂ +
        scalarProduct (↥c.H0) ν₁ (conjChar c.H0 (s_normalizes_H0 c h12) ν₂) +
        scalarProduct (↥c.H0) (conjChar c.H0 (s_normalizes_H0 c h12) ν₁) ν₂ +
        scalarProduct (↥c.H0) (conjChar c.H0 (s_normalizes_H0 c h12) ν₁)
          (conjChar c.H0 (s_normalizes_H0 c h12) ν₂) := by
  classical
  unfold scalarProduct
  have hsum :
      (∑ y : ↥c.H0, (inducedFromSub (h12.H0_normal_in_H).1 ν₁)
          ⟨(y : G), (h12.H0_normal_in_H).1 y.2⟩ *
        star ((inducedFromSub (h12.H0_normal_in_H).1 ν₂)
          ⟨(y : G), (h12.H0_normal_in_H).1 y.2⟩)) =
      (∑ y : ↥c.H0, ν₁ y * star (ν₂ y)) +
        (∑ y : ↥c.H0, ν₁ y * star (conjChar c.H0 (s_normalizes_H0 c h12) ν₂ y)) +
        (∑ y : ↥c.H0, conjChar c.H0 (s_normalizes_H0 c h12) ν₁ y * star (ν₂ y)) +
        (∑ y : ↥c.H0, conjChar c.H0 (s_normalizes_H0 c h12) ν₁ y *
          star (conjChar c.H0 (s_normalizes_H0 c h12) ν₂ y)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro y hy
    have hθ₁ : inducedFromSub (h12.H0_normal_in_H).1 ν₁
        ⟨(y : G), (h12.H0_normal_in_H).1 y.2⟩ =
        ν₁ y + conjChar c.H0 (s_normalizes_H0 c h12) ν₁ y := by
      have h1 := theta_pointwise c h12 hH0index hν₁ y
      have h2 : ν₁ ⟨c.s * (y : G) * c.s⁻¹, s_normalizes_H0 c h12 y⟩ =
          conjChar c.H0 (s_normalizes_H0 c h12) ν₁ y := by
        simp [conjChar]
        have hx : (conjMonoidHom c.H0 c.s (s_normalizes_H0 c h12) y : ↥c.H0) =
            ⟨c.s * (y : G) * c.s⁻¹, s_normalizes_H0 c h12 y⟩ := rfl
        rw [hx]
      rw [h1, h2]
    have hθ₂ : inducedFromSub (h12.H0_normal_in_H).1 ν₂
        ⟨(y : G), (h12.H0_normal_in_H).1 y.2⟩ =
        ν₂ y + conjChar c.H0 (s_normalizes_H0 c h12) ν₂ y := by
      have h1 := theta_pointwise c h12 hH0index hν₂ y
      have h2 : ν₂ ⟨c.s * (y : G) * c.s⁻¹, s_normalizes_H0 c h12 y⟩ =
          conjChar c.H0 (s_normalizes_H0 c h12) ν₂ y := by
        simp [conjChar]
        have hx : (conjMonoidHom c.H0 c.s (s_normalizes_H0 c h12) y : ↥c.H0) =
            ⟨c.s * (y : G) * c.s⁻¹, s_normalizes_H0 c h12 y⟩ := rfl
        rw [hx]
      rw [h1, h2]
    rw [hθ₁, hθ₂]
    simp [map_add, add_mul, mul_add, mul_assoc, mul_left_comm, mul_comm]
    ring
  -- the factor `(Nat.card ↥H0)⁻¹` distributes over the four sums
  change (Nat.card (↥c.H0) : ℂ)⁻¹ * (∑ y : ↥c.H0,
      (inducedFromSub (h12.H0_normal_in_H).1 ν₁) ⟨(y : G), (h12.H0_normal_in_H).1 y.2⟩ *
        star ((inducedFromSub (h12.H0_normal_in_H).1 ν₂) ⟨(y : G), (h12.H0_normal_in_H).1 y.2⟩)) = _
  rw [hsum]
  ring

set_option maxHeartbeats 20000000 in
/-- The scalar product over `H` of two characters induced from `H0` is half the
scalar product over `H0` (they vanish outside `H0`; `|H : H0| = 2`). -/
private lemma theta_pair_scalar_H (c : Hyp11 G) (h12 : Hyp12 c)
    (hH0index : (c.H0.subgroupOf c.H).index = 2)
    {ν₁ ν₂ : ClassFunction (↥c.H0)} (hν₁ : IsIrreducibleCharacter ν₁)
    (hν₂ : IsIrreducibleCharacter ν₂) :
    scalarProduct (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν₁)
        (inducedFromSub (h12.H0_normal_in_H).1 ν₂) =
      (2 : ℂ)⁻¹ * scalarProduct (↥c.H0)
        (fun y : ↥c.H0 => inducedFromSub (h12.H0_normal_in_H).1 ν₁
          ⟨(y : G), (h12.H0_normal_in_H).1 y.2⟩)
        (fun y : ↥c.H0 => inducedFromSub (h12.H0_normal_in_H).1 ν₂
          ⟨(y : G), (h12.H0_normal_in_H).1 y.2⟩) := by
  classical
  unfold scalarProduct
  have hcard : (Nat.card (↥c.H) : ℂ) = 2 * (Nat.card (↥c.H0) : ℂ) :=
    H_card_eq_two_mul_H0_card c h12 hH0index
  -- the sum over H splits into H0 and s⁻¹·H0 (sum_split_index_two); the second
  -- part vanishes (the induced characters vanish outside H0)
  have hsplit := sum_split_index_two (H := ↥c.H) (K := c.H0.subgroupOf c.H)
    (hindex := hH0index) (s := ⟨c.s, s_mem_H c⟩)
    (hs := by
      intro hsK
      exact s_not_mem_H0' c h12 (Subgroup.mem_subgroupOf.mp hsK))
    (f := fun x : ↥c.H => (inducedFromSub (h12.H0_normal_in_H).1 ν₁) x *
      star ((inducedFromSub (h12.H0_normal_in_H).1 ν₂) x))
  have hvan : (∑ k : ↥(c.H0.subgroupOf c.H),
      (inducedFromSub (h12.H0_normal_in_H).1 ν₁) (⟨c.s, s_mem_H c⟩⁻¹ * (k : ↥c.H)) *
        star ((inducedFromSub (h12.H0_normal_in_H).1 ν₂)
          (⟨c.s, s_mem_H c⟩⁻¹ * (k : ↥c.H)))) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hk' : ((k : ↥c.H) : G) ∈ c.H0 := Subgroup.mem_subgroupOf.mp k.2
    have hsk : ((⟨c.s, s_mem_H c⟩⁻¹ * (k : ↥c.H) : ↥c.H) : G) ∉ c.H0 := by
      intro hsk
      apply s_not_mem_H0' c h12
      have h1 : c.s⁻¹ * (k : G) ∈ c.H0 := hsk
      have h2 : c.s⁻¹ * (k : G) * (k : G)⁻¹ ∈ c.H0 := c.H0.mul_mem h1 (c.H0.inv_mem hk')
      have hs' : c.s⁻¹ * (k : G) * (k : G)⁻¹ = c.s := by
        have hs2 : c.s * c.s = 1 := by simpa [pow_two] using c.s_involution.2
        calc
          c.s⁻¹ * (k : G) * (k : G)⁻¹ = c.s⁻¹ := by group
          _ = c.s := (eq_inv_of_mul_eq_one_left hs2).symm
      rwa [hs'] at h2
    have hz₁ : (inducedFromSub (h12.H0_normal_in_H).1 ν₁)
        (⟨c.s, s_mem_H c⟩⁻¹ * (k : ↥c.H)) = 0 := by
      exact inducedFromSub_eq_zero_of_not_mem c.H0 c.H (h12.H0_normal_in_H).1 hH0index hsk
    have hz₂ : (inducedFromSub (h12.H0_normal_in_H).1 ν₂)
        (⟨c.s, s_mem_H c⟩⁻¹ * (k : ↥c.H)) = 0 := by
      exact inducedFromSub_eq_zero_of_not_mem c.H0 c.H (h12.H0_normal_in_H).1 hH0index hsk
    simp [hz₁, hz₂]
  calc
    (Nat.card (↥c.H) : ℂ)⁻¹ * (∑ x : ↥c.H,
          (inducedFromSub (h12.H0_normal_in_H).1 ν₁) x *
            star ((inducedFromSub (h12.H0_normal_in_H).1 ν₂) x))
        = (Nat.card (↥c.H) : ℂ)⁻¹ * ((∑ k : ↥(c.H0.subgroupOf c.H),
              (inducedFromSub (h12.H0_normal_in_H).1 ν₁) (k : ↥c.H) *
                star ((inducedFromSub (h12.H0_normal_in_H).1 ν₂) (k : ↥c.H))) +
            ∑ k : ↥(c.H0.subgroupOf c.H),
              (inducedFromSub (h12.H0_normal_in_H).1 ν₁) (⟨c.s, s_mem_H c⟩⁻¹ * (k : ↥c.H)) *
                star ((inducedFromSub (h12.H0_normal_in_H).1 ν₂)
                  (⟨c.s, s_mem_H c⟩⁻¹ * (k : ↥c.H)))) := by
            rw [hsplit]
        _ = (Nat.card (↥c.H) : ℂ)⁻¹ * (∑ k : ↥(c.H0.subgroupOf c.H),
              (inducedFromSub (h12.H0_normal_in_H).1 ν₁) (k : ↥c.H) *
                star ((inducedFromSub (h12.H0_normal_in_H).1 ν₂) (k : ↥c.H))) := by
            rw [hvan]
            ring
        _ = (2 : ℂ)⁻¹ * ((Nat.card (↥c.H0) : ℂ)⁻¹ * (∑ k : ↥(c.H0.subgroupOf c.H),
              (inducedFromSub (h12.H0_normal_in_H).1 ν₁) (k : ↥c.H) *
                star ((inducedFromSub (h12.H0_normal_in_H).1 ν₂) (k : ↥c.H)))) := by
            have hHne : (Nat.card (↥c.H) : ℂ) ≠ 0 := by
              exact_mod_cast (Nat.card_pos (α := ↥c.H)).ne'
            have hH0ne : (Nat.card (↥c.H0) : ℂ) ≠ 0 := by
              exact_mod_cast (Nat.card_pos (α := ↥c.H0)).ne'
            have htwo : (2 : ℂ) ≠ 0 := by norm_num
            have hfac : (Nat.card (↥c.H) : ℂ)⁻¹ = (2 : ℂ)⁻¹ * (Nat.card (↥c.H0) : ℂ)⁻¹ := by
              rw [hcard]
              rw [mul_inv_rev]
              ring
            rw [hfac]
            ring
        _ = (2 : ℂ)⁻¹ * scalarProduct (↥c.H0)
              (fun y : ↥c.H0 => inducedFromSub (h12.H0_normal_in_H).1 ν₁
                ⟨(y : G), (h12.H0_normal_in_H).1 y.2⟩)
              (fun y : ↥c.H0 => inducedFromSub (h12.H0_normal_in_H).1 ν₂
                ⟨(y : G), (h12.H0_normal_in_H).1 y.2⟩) := by
            congr 1
            unfold scalarProduct
            congr 1
            -- reindex the sum over K = H0.subgroupOf H to the sum over H0
            refine Finset.sum_bij
              (fun k hk => (⟨(k : G), Subgroup.mem_subgroupOf.mp k.2⟩ : ↥c.H0)) ?_ ?_ ?_ ?_
            · intro k hk
              simp
            · intro a ha b hb hEq
              apply Subtype.ext
              simpa using congrArg (fun x : ↥c.H0 => (x : G)) hEq
            · intro y hy
              refine ⟨⟨⟨(y : G), (h12.H0_normal_in_H).1 y.2⟩,
                Subgroup.mem_subgroupOf.mpr y.2⟩, by simp, ?_⟩
              ext
              rfl
            · intro k hk
              simp


/-! ## The `θ`-facts and `δ`-facts (route `R1-orbitwise`, step `orbit-lift`)

All of this is downstream of Remark 1.4 (`H0_index`). -/

/-! ## The `θ`-facts and `δ`-facts (route `R1-orbitwise`, step `orbit-lift`)

All of this is downstream of Remark 1.4 (`H0_index`). -/

/-- The four-term expansion
`(θ₁,θ₂)_H = (1/2)·[(ν₁,ν₂) + (ν₁,ν₂^s) + (ν₁^s,ν₂) + (ν₁^s,ν₂^s)]`
(Remark 1.4 applied twice inside `theta_pair_scalar_H`). -/
private lemma theta_pair_scalar_H' (c : Hyp11 G) (h12 : Hyp12 c)
    (hH0index : (c.H0.subgroupOf c.H).index = 2)
    {ν₁ ν₂ : ClassFunction (↥c.H0)} (hν₁ : IsIrreducibleCharacter ν₁)
    (hν₂ : IsIrreducibleCharacter ν₂) :
    scalarProduct (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν₁)
        (inducedFromSub (h12.H0_normal_in_H).1 ν₂) =
      (2 : ℂ)⁻¹ * (scalarProduct (↥c.H0) ν₁ ν₂ +
        scalarProduct (↥c.H0) ν₁ (conjChar c.H0 (s_normalizes_H0 c h12) ν₂) +
        scalarProduct (↥c.H0) (conjChar c.H0 (s_normalizes_H0 c h12) ν₁) ν₂ +
        scalarProduct (↥c.H0) (conjChar c.H0 (s_normalizes_H0 c h12) ν₁)
          (conjChar c.H0 (s_normalizes_H0 c h12) ν₂)) := by
  classical
  rw [theta_pair_scalar_H c h12 hH0index hν₁ hν₂]
  rw [theta_pair_scalar_H0 c h12 hH0index hν₁ hν₂]

/-- `|ν^H| = 2` if `ν^s = ν`, and `= 1` otherwise (the `(i)`-value for the
induced characters). -/
private lemma theta_norm (c : Hyp11 G) (h12 : Hyp12 c)
    (hH0index : (c.H0.subgroupOf c.H).index = 2)
    {ν : ClassFunction (↥c.H0)} (hν : IsIrreducibleCharacter ν) :
    normSq (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν) =
      (if conjChar c.H0 (s_normalizes_H0 c h12) ν = ν then 2 else 1) := by
  classical
  have hs_inv : ∀ x : ↥c.H0, c.s⁻¹ * (x : G) * c.s ∈ c.H0 := by
    intro x
    simpa using (h12.H0_normal_in_H).2 c.s⁻¹ (c.H.inv_mem (s_mem_H c)) (x : G) x.2
  have hνs : IsIrreducibleCharacter (conjChar c.H0 (s_normalizes_H0 c h12) ν) :=
    isIrreducibleCharacter_conjChar c.H0 (s_normalizes_H0 c h12) hs_inv hν
  have h1 := theta_pair_scalar_H' c h12 hH0index hν hν
  have hvv : scalarProduct (↥c.H0) ν ν = 1 := by
    simp [scalarProduct_irr_ite hν hν]
  have hvsvs : scalarProduct (↥c.H0) (conjChar c.H0 (s_normalizes_H0 c h12) ν)
      (conjChar c.H0 (s_normalizes_H0 c h12) ν) = 1 := by
    simp [scalarProduct_irr_ite hνs hνs]
  by_cases h : conjChar c.H0 (s_normalizes_H0 c h12) ν = ν
  · have hvvs : scalarProduct (↥c.H0) ν
        (conjChar c.H0 (s_normalizes_H0 c h12) ν) = 1 := by
      rw [scalarProduct_irr_ite hν hνs]
      simp [h]
    have hvs : scalarProduct (↥c.H0) (conjChar c.H0 (s_normalizes_H0 c h12) ν) ν = 1 := by
      rw [scalarProduct_irr_ite hνs hν]
      simp [h]
    unfold normSq
    rw [h1, hvv, hvvs, hvs, hvsvs]
    simp [h]
    norm_num
  · have hvvs : scalarProduct (↥c.H0) ν
        (conjChar c.H0 (s_normalizes_H0 c h12) ν) = 0 := by
      rw [scalarProduct_irr_ite hν hνs]
      by_cases hEq : ν = conjChar c.H0 (s_normalizes_H0 c h12) ν
      · exact False.elim (h hEq.symm)
      · simp [hEq]
    have hvs : scalarProduct (↥c.H0) (conjChar c.H0 (s_normalizes_H0 c h12) ν) ν = 0 := by
      rw [scalarProduct_irr_ite hνs hν]
      by_cases hEq : conjChar c.H0 (s_normalizes_H0 c h12) ν = ν
      · exact False.elim (h hEq)
      · simp [hEq]
    unfold normSq
    rw [h1, hvv, hvvs, hvs, hvsvs]
    simp [h]
    norm_num

/-- `inducedClassFunction` is insensitive to the ambient `Fintype G` instance
(the Lemma22 lemmas are elaborated with `Fintype.ofFinite G`, the section
with its local `[Fintype G]`). -/
private lemma inducedClassFunction_fintype_inst (G : Type u) [Group G] [Fintype G]
    [Finite G] (H : Subgroup G) (φ : ClassFunction (↥H)) :
    @inducedClassFunction G _ (Fintype.ofFinite G) H φ = inducedClassFunction H φ := by
  funext g
  unfold inducedClassFunction
  congr 1
  apply Finset.sum_congr
  · ext x
    simp
  · intro x hx
    rfl

/-- `scalarProduct` is insensitive to the ambient `Fintype G` instance. -/
private lemma scalarProduct_fintype_inst (G : Type u) [Group G] [Fintype G]
    [Finite G] (φ ψ : ClassFunction G) :
    @scalarProduct G (Fintype.ofFinite G) φ ψ = scalarProduct G φ ψ := by
  unfold scalarProduct
  congr 1
  apply Finset.sum_congr
  · ext x
    simp
  · intro x hx
    rfl

/-- The difference of orbit members is supported on `T` (they agree on `U`). -/
private lemma delta_supported_on_T (c : Hyp11 G)
    [Fintype ↥(LambdaHom c.H0 c.U)] {ν μ : ClassFunction (↥c.H0)}
    (hμL : μ ∈ orbit c.H0 c.U ν) :
    supportedOn (μ - ν) {x : ↥c.H0 | (x : G) ∈ c.T} := by
  classical
  unfold supportedOn
  intro x hx
  have hxU : (x : G) ∈ c.U := by
    by_contra hU
    exact hx ⟨x.2, hU⟩
  have hEq := orbit_mem_eq_on_U c hμL hxU
  change μ x - ν x = 0
  rw [hEq]
  ring

/-- Induction from `H0` is linear: `(μ−ν)^H = μ^H − ν^H`. -/
private lemma inducedFromSub_sub (c : Hyp11 G) (h12 : Hyp12 c)
    (ν μ : ClassFunction (↥c.H0)) :
    inducedFromSub (h12.H0_normal_in_H).1 (μ - ν) =
      inducedFromSub (h12.H0_normal_in_H).1 μ -
        inducedFromSub (h12.H0_normal_in_H).1 ν := by
  classical
  unfold inducedFromSub
  change inducedClassFunction (c.H0.subgroupOf c.H)
    (fun x : ↥(c.H0.subgroupOf c.H) =>
      μ ⟨(x : G), Subgroup.mem_subgroupOf.mp x.2⟩ -
        ν ⟨(x : G), Subgroup.mem_subgroupOf.mp x.2⟩) =
    inducedClassFunction (c.H0.subgroupOf c.H)
      (fun x : ↥(c.H0.subgroupOf c.H) =>
        μ ⟨(x : G), Subgroup.mem_subgroupOf.mp x.2⟩) -
    inducedClassFunction (c.H0.subgroupOf c.H)
      (fun x : ↥(c.H0.subgroupOf c.H) =>
        ν ⟨(x : G), Subgroup.mem_subgroupOf.mp x.2⟩)
  rw [← inducedClassFunction_sub]
  rfl

/-- The `(v)`-value on `T`: for `μ, ν` in the same orbit and `x ∈ T ⊂ H0`,
the `G`-induction `(μ−ν)^G` equals the `H`-induction difference
`μ^H − ν^H` at `x`. Route: `μ−ν` is supported on the TI-set `T` with
`N_G(T) = H` (`delta_supported_on_T`), so the `G`-sum at `x ∈ T` restricts
to the `H`-sum (`induced_sum_eq_sum_subgroup`), and the summands agree
with the `H0 → H`-induction summands. -/
private lemma induced_star_eq_on_T (c : Hyp11 G) (h12 : Hyp12 c)
    [Fintype ↥(LambdaHom c.H0 c.U)]
    (hH0index : (c.H0.subgroupOf c.H).index = 2)
    {μ ν : ClassFunction (↥c.H0)}
    (hμL : μ ∈ orbit c.H0 c.U ν) (x : ↥c.H0) (hx : (x : G) ∈ c.T) :
    (inducedClassFunction c.H0 (μ - ν)) (x : G) =
      (inducedFromSub (h12.H0_normal_in_H).1 μ) ⟨x, (h12.H0_normal_in_H).1 x.2⟩ -
        (inducedFromSub (h12.H0_normal_in_H).1 ν) ⟨x, (h12.H0_normal_in_H).1 x.2⟩ := by
  classical
  have hsup := delta_supported_on_T c hμL
  let xH : ↥c.H := ⟨x, (h12.H0_normal_in_H).1 x.2⟩
  let ψ : ClassFunction (↥(c.H0.subgroupOf c.H)) := fun y =>
    (μ - ν) ⟨(y : G), Subgroup.mem_subgroupOf.mp y.2⟩
  -- the G-sum at `x` restricts to the H-sum (the summands vanish outside `H`)
  have hsumG : (∑ g : G, inducedSummand (μ - ν) (x : G) g) =
      ∑ g : ↥(c.H : Subgroup G), inducedSummand (μ - ν) (x : G) (g : G) :=
    induced_sum_eq_sum_subgroup h12.T_is_TI h12.T_normalizer (μ - ν) hsup hx
  -- the H-summands coincide with the `H0 → H`-induction summands
  have hsumH : (∑ g : ↥(c.H : Subgroup G), inducedSummand (μ - ν) (x : G) (g : G)) =
      ∑ g : ↥(c.H : Subgroup G), inducedSummand ψ xH g := by
    refine Finset.sum_congr rfl ?_
    intro g hg
    unfold inducedSummand
    have hiff : (g : G)⁻¹ * (x : G) * g ∈ c.H0 ↔ g⁻¹ * xH * g ∈ c.H0.subgroupOf c.H := by
      rw [Subgroup.mem_subgroupOf]
      rw [show ((g⁻¹ * xH * g : ↥c.H) : G) = (g : G)⁻¹ * (x : G) * g by
        simp [xH]]
    by_cases hmem : (g : G)⁻¹ * (x : G) * g ∈ c.H0
    · have hh : g⁻¹ * xH * g ∈ c.H0.subgroupOf c.H := hiff.mpr hmem
      simp [ψ, hmem, hh]
      all_goals
        try congr 1 <;> congr 1 <;> ext <;> rfl
    · have hhnot : ¬ (g⁻¹ * xH * g ∈ c.H0.subgroupOf c.H) := by
        intro h
        exact hmem (hiff.mp h)
      simp [hmem, hhnot]
  -- the cardinal normalization: `|↥(H0.subgroupOf H)| = |↥H0|`
  have hcard : (Nat.card (↥(c.H0.subgroupOf c.H)) : ℂ) = (Nat.card (↥c.H0) : ℂ) := by
    congr 1
    exact Nat.card_congr
      { toFun := fun y : ↥(c.H0.subgroupOf c.H) => ⟨(y : G), Subgroup.mem_subgroupOf.mp y.2⟩
        invFun := fun y : ↥c.H0 => ⟨⟨(y : G), (h12.H0_normal_in_H).1 y.2⟩,
          Subgroup.mem_subgroupOf.mpr y.2⟩
        left_inv := by intro y; ext; rfl
        right_inv := by intro y; ext; rfl }
  -- the G-induction value at `x` equals the `H0 → H`-induction value
  have hmain : (inducedClassFunction c.H0 (μ - ν)) (x : G) =
      (inducedClassFunction (c.H0.subgroupOf c.H) ψ) xH := by
    unfold inducedClassFunction
    change (Nat.card (↥c.H0) : ℂ)⁻¹ * (∑ g : G, inducedSummand (μ - ν) (x : G) g) =
      (Nat.card (↥(c.H0.subgroupOf c.H)) : ℂ)⁻¹ *
        (∑ g : ↥(c.H : Subgroup G), inducedSummand ψ xH g)
    rw [hsumG, hsumH, hcard]
  -- the H-induction is additive
  change (inducedClassFunction c.H0 (μ - ν)) (x : G) =
      (inducedFromSub (h12.H0_normal_in_H).1 μ - inducedFromSub (h12.H0_normal_in_H).1 ν)
        ⟨x, (h12.H0_normal_in_H).1 x.2⟩
  rw [← inducedFromSub_sub c h12 ν μ]
  exact hmain

set_option maxHeartbeats 8000000 in
/-- The orbit-level `(vi)`-argument: `θ̃(ν^H)(t) = 2ν(t)` for `ν^s ≠ ν`
(unless `|Λν| = 4 ∧ Λν^s = Λν`), from the orbit-lift's fields
(`isGeneralized`/norm/`(ii)`) plus the Lemma-2.1 sign choice
(`exists_mu_sign_choice`), the `V = 0` content of Lemma 2.2
(`lemma_2_2_V_zero_of_pair_sum`), the `(v)`-value on `T`
(`induced_star_eq_on_T`), and `|H : H0| = 2`. This is `at_t_of_V_zero`
specialized to a single orbit; it supplies the `θ̃₂(t) = 2α(t)` half of the
undefined-case contradiction (the other half is `lemma_1_7_iii`). -/
private lemma theta_tilde_two_eval (c : Hyp11 G) (h12 : Hyp12 c)
    [Fintype ↥(LambdaHom c.H0 c.U)]
    (hH0index : (c.H0.subgroupOf c.H).index = 2)
    {ν : ClassFunction (↥c.H0)} (hν : IsIrreducibleCharacter ν)
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν ≠ ν)
    (hnot : ¬ ((orbit c.H0 c.U ν).card = 4 ∧
      conjChar c.H0 (s_normalizes_H0 c h12) ν ∈ orbit c.H0 c.U ν))
    (thetaTilde : ClassFunction (↥c.H) → ClassFunction G)
    (hgen : ∀ θ' : ClassFunction (↥c.H), θ' ∈ thetaOfOrbit c h12 (orbit c.H0 c.U ν) →
      IsGeneralizedCharacter (thetaTilde θ'))
    (hnorm : ∀ θ' : ClassFunction (↥c.H), θ' ∈ thetaOfOrbit c h12 (orbit c.H0 c.U ν) →
      normSq G (thetaTilde θ') = normSq (↥c.H) θ')
    (hind : ∀ {μ ν' : ClassFunction (↥c.H0)}, μ ∈ orbit c.H0 c.U ν → ν' ∈ orbit c.H0 c.U ν →
      inducedClassFunction c.H0 (μ - ν') =
        thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 μ) -
          thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 ν'))
    (honT : ∀ {μ ν' : ClassFunction (↥c.H0)}, μ ∈ orbit c.H0 c.U ν → ν' ∈ orbit c.H0 c.U ν →
      ∀ hg : c.t ∈ c.H,
      (inducedClassFunction c.H0 (μ - ν')) c.t =
        (inducedFromSub (h12.H0_normal_in_H).1 μ) ⟨c.t, hg⟩ -
          (inducedFromSub (h12.H0_normal_in_H).1 ν') ⟨c.t, hg⟩) :
    thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 ν) c.t = 2 * ν (tH0 c) := by
  classical
  have hνL : ν ∈ orbit c.H0 c.U ν := orbit_self_mem c ν
  have hθνΘ : inducedFromSub (h12.H0_normal_in_H).1 ν ∈
      thetaOfOrbit c h12 (orbit c.H0 c.U ν) := thetaOfOrbit_mem c h12 hνL
  -- the sign-chosen companion `μ` (Lemma 2.1)
  rcases exists_mu_sign_choice c h12 hν hνs hnot with ⟨μ, hμL, hμs, hμt⟩
  have hμirr : IsIrreducibleCharacter μ := orbit_mem_isIrreducible c.H0 c.U hν hμL
  have hθμΘ : inducedFromSub (h12.H0_normal_in_H).1 μ ∈
      thetaOfOrbit c h12 (orbit c.H0 c.U ν) := thetaOfOrbit_mem c h12 hμL
  -- the pair-wise `V = 0` (Lemma 2.2 case 1)
  have hμL' : μ ∈ @orbit G _ (@Fintype.ofFinite G inferInstance) c.H0 c.U
      (instFintypeLambdaHom c.H0 c.U) ν := by
    simpa [orbit] using hμL
  have hV := lemma_2_2_V_zero_of_pair_sum (G := G) c h12
      (μ := ⟨μ, hμirr⟩) (ν := ⟨ν, hν⟩) hμL' hμs hνs
  have hnorm1μ : normSq G (thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 μ)) = 1 := by
    rw [hnorm (inducedFromSub (h12.H0_normal_in_H).1 μ) hθμΘ]
    change normSq (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 μ) = 1
    rw [theta_norm c h12 hH0index hμirr]
    rw [if_neg hμs]
  have hnorm1ν : normSq G (thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 ν)) = 1 := by
    rw [hnorm (inducedFromSub (h12.H0_normal_in_H).1 ν) hθνΘ]
    change normSq (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν) = 1
    rw [theta_norm c h12 hH0index hν]
    rw [if_neg hνs]
  rcases norm_one_signed_irreducible (hgen (inducedFromSub (h12.H0_normal_in_H).1 μ) hθμΘ)
    hnorm1μ with ⟨χ₁, hχ₁, hμcase⟩
  rcases norm_one_signed_irreducible (hgen (inducedFromSub (h12.H0_normal_in_H).1 ν) hθνΘ)
    hnorm1ν with ⟨χ₂, hχ₂, hνcase⟩
  have hδeq : inducedClassFunction c.H0 (μ - ν) =
      thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 μ) -
        thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 ν) := hind hμL hνL
  -- `(μ−ν)*(1) = 0` (the degrees are equal on the orbit)
  have hδ1 : (inducedClassFunction c.H0 (μ - ν)) 1 = 0 := by
    unfold inducedClassFunction
    have hsum : (∑ x : G, (if hx : x⁻¹ * 1 * x ∈ c.H0 then (μ - ν) ⟨x⁻¹ * 1 * x, hx⟩ else 0)) =
        Fintype.card G * (μ 1 - ν 1) := by
      calc
        (∑ x : G, (if hx : x⁻¹ * 1 * x ∈ c.H0 then (μ - ν) ⟨x⁻¹ * 1 * x, hx⟩ else 0))
            = ∑ x : G, (μ 1 - ν 1) := by
                refine Finset.sum_congr rfl ?_
                intro x hx
                have hx1 : x⁻¹ * 1 * x = 1 := by group
                have hxmem : x⁻¹ * 1 * x ∈ c.H0 := by
                  rw [hx1]
                  exact c.H0.one_mem
                rw [dif_pos hxmem]
                have hxeq : (⟨x⁻¹ * 1 * x, hxmem⟩ : ↥c.H0) = (1 : ↥c.H0) := by
                  apply Subtype.ext
                  exact hx1
                rw [hxeq]
                rfl
        _ = Fintype.card G * (μ 1 - ν 1) := by
                rw [Finset.sum_const]
                simp [nsmul_eq_mul]
    rw [hsum]
    have hdeg : μ 1 = ν 1 := orbit_mem_degree_eq c hμL
    simp [hdeg]
  have hmu1 : thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 μ) 1 =
      thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 ν) 1 := by
    have h := congrFun hδeq 1
    rw [hδ1] at h
    have h' : thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 μ) 1 -
        thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 ν) 1 = 0 := by simpa using h.symm
    exact sub_eq_zero.mp h'
  have hmu1_ne : thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 μ) 1 ≠ 0 := by
    rcases hμcase with hμcase1 | hμcase2
    · rw [hμcase1]
      exact irreducible_char_one_ne_zero hχ₁
    · rw [hμcase2]
      simpa using irreducible_char_one_ne_zero hχ₁
  have hν1_ne : thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 ν) 1 ≠ 0 := by
    rcases hνcase with hνcase1 | hνcase2
    · rw [hνcase1]
      exact irreducible_char_one_ne_zero hχ₂
    · rw [hνcase2]
      simpa using irreducible_char_one_ne_zero hχ₂
  -- split `V` over the two signed irreducibles
  have hsplit : (∑ χ : Irr G, (χ.1 c.t ^ 2 / χ.1 1) *
        scalarProduct G χ.1 (inducedClassFunction c.H0 (μ - ν))) =
      (∑ χ : Irr G, (χ.1 c.t ^ 2 / χ.1 1) *
        scalarProduct G χ.1 (thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 μ))) -
        (∑ χ : Irr G, (χ.1 c.t ^ 2 / χ.1 1) *
          scalarProduct G χ.1 (thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 ν))) := by
    rw [hδeq]
    simp [scalarProduct_sub_right, mul_sub, Finset.sum_sub_distrib]
  have hV' : (∑ χ : Irr G, (χ.1 c.t ^ 2 / χ.1 1) *
        scalarProduct G χ.1 (inducedClassFunction c.H0 (μ - ν))) = 0 := by
    convert hV using 1
    · apply Finset.sum_congr
      · ext χ
        simp
      · intro χ hχ
        rw [inducedClassFunction_fintype_inst G c.H0 (μ - ν)]
        rw [← scalarProduct_fintype_inst G (↑χ) (inducedClassFunction c.H0 (μ - ν))]
  have hVμν : (thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 μ) c.t) ^ 2 /
        thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 μ) 1 -
      (thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 ν) c.t) ^ 2 /
        thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 ν) 1 = 0 := by
    have hA : (∑ χ : Irr G, (χ.1 c.t ^ 2 / χ.1 1) *
        scalarProduct G χ.1 (thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 μ))) =
        (thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 μ) c.t) ^ 2 /
          thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 μ) 1 :=
      sum_chi_t_sq_over_deg c (φ := thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 μ))
        (χ₀ := χ₁) hχ₁ hμcase
    have hB : (∑ χ : Irr G, (χ.1 c.t ^ 2 / χ.1 1) *
        scalarProduct G χ.1 (thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 ν))) =
        (thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 ν) c.t) ^ 2 /
          thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 ν) 1 :=
      sum_chi_t_sq_over_deg c (φ := thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 ν))
        (χ₀ := χ₂) hχ₂ hνcase
    rw [← hA, ← hB, ← hsplit]
    exact hV'
  rw [hmu1] at hVμν
  have hVμν' : (thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 μ) c.t) ^ 2 -
      (thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 ν) c.t) ^ 2 = 0 := by
    field_simp [hmu1_ne] at hVμν
    simpa using hVμν
  have hsq : (thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 μ) c.t) ^ 2 =
      (thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 ν) c.t) ^ 2 := sub_eq_zero.mp hVμν'
  -- `(v)` on `T`: `θ̃(θμ)(t) − θ̃(θν)(t) = 4μ(t)`
  have hHmem : c.t ∈ c.H := S_le_H c (c.S0_le_S c.t_mem_S0)
  have hsh : c.s * c.t * c.s⁻¹ ∈ c.H0 := by
    rw [s_conj_t c]
    exact (tH0 c).2
  have hmuH : (inducedFromSub (h12.H0_normal_in_H).1 μ)
      ⟨c.t, (h12.H0_normal_in_H).1 (tH0 c).2⟩ = 2 * μ (tH0 c) := by
    have h1 := (remark_1_4 (h12.H0_normal_in_H).1 hH0index (S_le_H c c.s_mem_S)
      (s_not_mem_H0' c h12) hμirr).1 c.t (tH0 c).2 hsh
    have h2 : μ ⟨c.s * c.t * c.s⁻¹, hsh⟩ = μ (tH0 c) := by
      exact congrArg μ (by
        apply Subtype.ext
        exact s_conj_t c)
    have h3 : μ ⟨c.t, (tH0 c).2⟩ = μ (tH0 c) := rfl
    calc
      (inducedFromSub (h12.H0_normal_in_H).1 μ)
          ⟨c.t, (h12.H0_normal_in_H).1 (tH0 c).2⟩
          = μ ⟨c.t, (tH0 c).2⟩ + μ ⟨c.s * c.t * c.s⁻¹, hsh⟩ := h1
      _ = 2 * μ (tH0 c) := by simp [h2, h3, two_mul]
  have hnuH : (inducedFromSub (h12.H0_normal_in_H).1 ν)
      ⟨c.t, (h12.H0_normal_in_H).1 (tH0 c).2⟩ = 2 * ν (tH0 c) := by
    have h1 := (remark_1_4 (h12.H0_normal_in_H).1 hH0index (S_le_H c c.s_mem_S)
      (s_not_mem_H0' c h12) hν).1 c.t (tH0 c).2 hsh
    have h2 : ν ⟨c.s * c.t * c.s⁻¹, hsh⟩ = ν (tH0 c) := by
      exact congrArg ν (by
        apply Subtype.ext
        exact s_conj_t c)
    have h3 : ν ⟨c.t, (tH0 c).2⟩ = ν (tH0 c) := rfl
    calc
      (inducedFromSub (h12.H0_normal_in_H).1 ν)
          ⟨c.t, (h12.H0_normal_in_H).1 (tH0 c).2⟩
          = ν ⟨c.t, (tH0 c).2⟩ + ν ⟨c.s * c.t * c.s⁻¹, hsh⟩ := h1
      _ = 2 * ν (tH0 c) := by simp [h2, h3, two_mul]
  have hδeqt : thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 μ) c.t -
      thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 ν) c.t =
      (inducedClassFunction c.H0 (μ - ν)) c.t := by
    simpa using (congrFun hδeq c.t).symm
  have hdiff : thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 μ) c.t -
      thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 ν) c.t = 4 * μ (tH0 c) := by
    have h2 : (inducedFromSub (h12.H0_normal_in_H).1 μ) ⟨c.t, hHmem⟩ = 2 * μ (tH0 c) := by
      convert hmuH using 1
    have h3 : (inducedFromSub (h12.H0_normal_in_H).1 ν) ⟨c.t, hHmem⟩ = 2 * ν (tH0 c) := by
      convert hnuH using 1
    rw [hδeqt, honT hμL hνL hHmem, h2, h3]
    rw [hμt]
    ring
  have hdiff_ne : thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 μ) c.t -
      thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 ν) c.t ≠ 0 := by
    rw [hdiff]
    have hμt0 : μ (tH0 c) ≠ 0 := char_apply_central_ne_zero
      (G := ↥c.H0) (t := tH0 c) (by simpa [tH0] using t_central_H0' c)
      (by simpa [tH0] using t_H0_sq c) hμirr
    intro hz
    rcases (mul_eq_zero.mp hz) with h4 | hν0
    · norm_num at h4
    · exact hμt0 hν0
  have hsum0 : thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 μ) c.t +
      thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 ν) c.t = 0 := by
    have hprod : (thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 μ) c.t +
        thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 ν) c.t) *
      (thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 μ) c.t -
        thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 ν) c.t) = 0 := by
      calc
        (thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 μ) c.t +
            thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 ν) c.t) *
          (thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 μ) c.t -
            thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 ν) c.t)
            = (thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 μ) c.t) ^ 2 -
                (thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 ν) c.t) ^ 2 := by ring
        _ = 0 := by rw [hsq]; ring
    exact (mul_eq_zero.mp hprod).resolve_right hdiff_ne
  have hb : thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 ν) c.t =
      -thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 μ) c.t := by
    linear_combination hsum0
  have ha : thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 μ) c.t = 2 * μ (tH0 c) := by
    have h2m : 2 * thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 μ) c.t = 4 * μ (tH0 c) := by
      linear_combination hdiff + hb
    calc
      thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 μ) c.t =
          (2 * thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 μ) c.t) / 2 := by ring
      _ = (4 * μ (tH0 c)) / 2 := by rw [h2m]
      _ = 2 * μ (tH0 c) := by ring
  calc
    thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 ν) c.t =
        -thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 μ) c.t := hb
    _ = -(2 * μ (tH0 c)) := by rw [ha]
    _ = 2 * ν (tH0 c) := by rw [hμt]; ring



/-- The `(vi)`-value `ν̃(t) = 2ν(t)` specialized to one sign-chosen pair
`(μ,ν)`, so the fixed-member Fourier contradiction can use it without
constructing the whole orbit lift. -/
private lemma theta_tilde_two_eval_pair (c : Hyp11 G) (h12 : Hyp12 c)
    [Fintype ↥(LambdaHom c.H0 c.U)]
    (hH0index : (c.H0.subgroupOf c.H).index = 2)
    {ν μ : ClassFunction (↥c.H0)}
    (hν : IsIrreducibleCharacter ν)
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν ≠ ν)
    (hμ : IsIrreducibleCharacter μ)
    (hμL : μ ∈ orbit c.H0 c.U ν)
    (hμs : conjChar c.H0 (s_normalizes_H0 c h12) μ ≠ μ)
    (hμt : μ (tH0 c) = -ν (tH0 c))
    (thetaTilde : ClassFunction (↥c.H) → ClassFunction G)
    (hgenμ : IsGeneralizedCharacter
      (thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 μ)))
    (hgenν : IsGeneralizedCharacter
      (thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 ν)))
    (hnormμ : normSq G (thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 μ)) = 1)
    (hnormν : normSq G (thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 ν)) = 1)
    (hδeq : inducedClassFunction c.H0 (μ - ν) =
      thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 μ) -
        thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 ν))
    (honT : ∀ hg : c.t ∈ c.H,
      (inducedClassFunction c.H0 (μ - ν)) c.t =
        (inducedFromSub (h12.H0_normal_in_H).1 μ) ⟨c.t, hg⟩ -
          (inducedFromSub (h12.H0_normal_in_H).1 ν) ⟨c.t, hg⟩) :
    thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 ν) c.t = 2 * ν (tH0 c) := by
  classical
  have hμL' : μ ∈ @orbit G _ (@Fintype.ofFinite G inferInstance) c.H0 c.U
      (instFintypeLambdaHom c.H0 c.U) ν := by
    simpa [orbit] using hμL
  have hV := lemma_2_2_V_zero_of_pair_sum (G := G) c h12
      (μ := ⟨μ, hμ⟩) (ν := ⟨ν, hν⟩) hμL' hμs hνs
  rcases norm_one_signed_irreducible hgenμ hnormμ with ⟨χ₁, hχ₁, hμcase⟩
  rcases norm_one_signed_irreducible hgenν hnormν with ⟨χ₂, hχ₂, hνcase⟩
  have hδ1 : (inducedClassFunction c.H0 (μ - ν)) 1 = 0 := by
    unfold inducedClassFunction
    have hsum : (∑ x : G, (if hx : x⁻¹ * 1 * x ∈ c.H0 then (μ - ν) ⟨x⁻¹ * 1 * x, hx⟩ else 0)) =
        Fintype.card G * (μ 1 - ν 1) := by
      calc
        (∑ x : G, (if hx : x⁻¹ * 1 * x ∈ c.H0 then (μ - ν) ⟨x⁻¹ * 1 * x, hx⟩ else 0))
            = ∑ x : G, (μ 1 - ν 1) := by
                refine Finset.sum_congr rfl ?_
                intro x hx
                have hx1 : x⁻¹ * 1 * x = 1 := by group
                have hxmem : x⁻¹ * 1 * x ∈ c.H0 := by
                  rw [hx1]
                  exact c.H0.one_mem
                rw [dif_pos hxmem]
                have hxeq : (⟨x⁻¹ * 1 * x, hxmem⟩ : ↥c.H0) = (1 : ↥c.H0) := by
                  apply Subtype.ext
                  exact hx1
                rw [hxeq]
                rfl
        _ = Fintype.card G * (μ 1 - ν 1) := by
                rw [Finset.sum_const]
                simp [nsmul_eq_mul]
    rw [hsum]
    have hdeg : μ 1 = ν 1 := orbit_mem_degree_eq c hμL
    simp [hdeg]
  have hmu1 : thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 μ) 1 =
      thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 ν) 1 := by
    have h := congrFun hδeq 1
    rw [hδ1] at h
    have h' : thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 μ) 1 -
        thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 ν) 1 = 0 := by simpa using h.symm
    exact sub_eq_zero.mp h'
  have hmu1_ne : thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 μ) 1 ≠ 0 := by
    rcases hμcase with hμcase1 | hμcase2
    · rw [hμcase1]
      exact irreducible_char_one_ne_zero hχ₁
    · rw [hμcase2]
      simpa using irreducible_char_one_ne_zero hχ₁
  have hν1_ne : thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 ν) 1 ≠ 0 := by
    rcases hνcase with hνcase1 | hνcase2
    · rw [hνcase1]
      exact irreducible_char_one_ne_zero hχ₂
    · rw [hνcase2]
      simpa using irreducible_char_one_ne_zero hχ₂
  have hsplit : (∑ χ : Irr G, (χ.1 c.t ^ 2 / χ.1 1) *
        scalarProduct G χ.1 (inducedClassFunction c.H0 (μ - ν))) =
      (∑ χ : Irr G, (χ.1 c.t ^ 2 / χ.1 1) *
        scalarProduct G χ.1 (thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 μ))) -
        (∑ χ : Irr G, (χ.1 c.t ^ 2 / χ.1 1) *
          scalarProduct G χ.1 (thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 ν))) := by
    rw [hδeq]
    simp [scalarProduct_sub_right, mul_sub, Finset.sum_sub_distrib]
  have hV' : (∑ χ : Irr G, (χ.1 c.t ^ 2 / χ.1 1) *
        scalarProduct G χ.1 (inducedClassFunction c.H0 (μ - ν))) = 0 := by
    convert hV using 1
    · apply Finset.sum_congr
      · ext χ
        simp
      · intro χ hχ
        rw [inducedClassFunction_fintype_inst G c.H0 (μ - ν)]
        rw [← scalarProduct_fintype_inst G (↑χ) (inducedClassFunction c.H0 (μ - ν))]
  have hVμν : (thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 μ) c.t) ^ 2 /
        thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 μ) 1 -
      (thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 ν) c.t) ^ 2 /
        thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 ν) 1 = 0 := by
    have hA : (∑ χ : Irr G, (χ.1 c.t ^ 2 / χ.1 1) *
        scalarProduct G χ.1 (thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 μ))) =
        (thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 μ) c.t) ^ 2 /
          thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 μ) 1 :=
      sum_chi_t_sq_over_deg c (φ := thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 μ))
        (χ₀ := χ₁) hχ₁ hμcase
    have hB : (∑ χ : Irr G, (χ.1 c.t ^ 2 / χ.1 1) *
        scalarProduct G χ.1 (thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 ν))) =
        (thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 ν) c.t) ^ 2 /
          thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 ν) 1 :=
      sum_chi_t_sq_over_deg c (φ := thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 ν))
        (χ₀ := χ₂) hχ₂ hνcase
    rw [← hA, ← hB, ← hsplit]
    exact hV'
  rw [hmu1] at hVμν
  have hVμν' : (thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 μ) c.t) ^ 2 -
      (thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 ν) c.t) ^ 2 = 0 := by
    field_simp [hmu1_ne] at hVμν
    simpa using hVμν
  have hsq : (thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 μ) c.t) ^ 2 =
      (thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 ν) c.t) ^ 2 := sub_eq_zero.mp hVμν'
  have hHmem : c.t ∈ c.H := S_le_H c (c.S0_le_S c.t_mem_S0)
  have hsh : c.s * c.t * c.s⁻¹ ∈ c.H0 := by
    rw [s_conj_t c]
    exact (tH0 c).2
  have hmuH : (inducedFromSub (h12.H0_normal_in_H).1 μ)
      ⟨c.t, (h12.H0_normal_in_H).1 (tH0 c).2⟩ = 2 * μ (tH0 c) := by
    have h1 := (remark_1_4 (h12.H0_normal_in_H).1 hH0index (S_le_H c c.s_mem_S)
      (s_not_mem_H0' c h12) hμ).1 c.t (tH0 c).2 hsh
    have h2 : μ ⟨c.s * c.t * c.s⁻¹, hsh⟩ = μ (tH0 c) := by
      exact congrArg μ (by
        apply Subtype.ext
        exact s_conj_t c)
    have h3 : μ ⟨c.t, (tH0 c).2⟩ = μ (tH0 c) := rfl
    calc
      (inducedFromSub (h12.H0_normal_in_H).1 μ)
          ⟨c.t, (h12.H0_normal_in_H).1 (tH0 c).2⟩
          = μ ⟨c.t, (tH0 c).2⟩ + μ ⟨c.s * c.t * c.s⁻¹, hsh⟩ := h1
      _ = 2 * μ (tH0 c) := by simp [h2, h3, two_mul]
  have hnuH : (inducedFromSub (h12.H0_normal_in_H).1 ν)
      ⟨c.t, (h12.H0_normal_in_H).1 (tH0 c).2⟩ = 2 * ν (tH0 c) := by
    have h1 := (remark_1_4 (h12.H0_normal_in_H).1 hH0index (S_le_H c c.s_mem_S)
      (s_not_mem_H0' c h12) hν).1 c.t (tH0 c).2 hsh
    have h2 : ν ⟨c.s * c.t * c.s⁻¹, hsh⟩ = ν (tH0 c) := by
      exact congrArg ν (by
        apply Subtype.ext
        exact s_conj_t c)
    have h3 : ν ⟨c.t, (tH0 c).2⟩ = ν (tH0 c) := rfl
    calc
      (inducedFromSub (h12.H0_normal_in_H).1 ν)
          ⟨c.t, (h12.H0_normal_in_H).1 (tH0 c).2⟩
          = ν ⟨c.t, (tH0 c).2⟩ + ν ⟨c.s * c.t * c.s⁻¹, hsh⟩ := h1
      _ = 2 * ν (tH0 c) := by simp [h2, h3, two_mul]
  have hδeqt : thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 μ) c.t -
      thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 ν) c.t =
      (inducedClassFunction c.H0 (μ - ν)) c.t := by
    simpa using (congrFun hδeq c.t).symm
  have hdiff : thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 μ) c.t -
      thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 ν) c.t = 4 * μ (tH0 c) := by
    have h2 : (inducedFromSub (h12.H0_normal_in_H).1 μ) ⟨c.t, hHmem⟩ = 2 * μ (tH0 c) := by
      convert hmuH using 1
    have h3 : (inducedFromSub (h12.H0_normal_in_H).1 ν) ⟨c.t, hHmem⟩ = 2 * ν (tH0 c) := by
      convert hnuH using 1
    rw [hδeqt, honT hHmem, h2, h3]
    rw [hμt]
    ring
  have hdiff_ne : thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 μ) c.t -
      thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 ν) c.t ≠ 0 := by
    rw [hdiff]
    have hμt0 : μ (tH0 c) ≠ 0 := char_apply_central_ne_zero
      (G := ↥c.H0) (t := tH0 c) (by simpa [tH0] using t_central_H0' c)
      (by simpa [tH0] using t_H0_sq c) hμ
    intro hz
    rcases (mul_eq_zero.mp hz) with h4 | hν0
    · norm_num at h4
    · exact hμt0 hν0
  have hsum0 : thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 μ) c.t +
      thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 ν) c.t = 0 := by
    have hprod : (thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 μ) c.t +
        thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 ν) c.t) *
      (thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 μ) c.t -
        thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 ν) c.t) = 0 := by
      calc
        (thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 μ) c.t +
            thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 ν) c.t) *
          (thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 μ) c.t -
            thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 ν) c.t)
            = (thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 μ) c.t) ^ 2 -
                (thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 ν) c.t) ^ 2 := by ring
        _ = 0 := by rw [hsq]; ring
    exact (mul_eq_zero.mp hprod).resolve_right hdiff_ne
  have hb : thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 ν) c.t =
      -thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 μ) c.t := by
    linear_combination hsum0
  have ha : thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 μ) c.t = 2 * μ (tH0 c) := by
    have h2m : 2 * thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 μ) c.t = 4 * μ (tH0 c) := by
      linear_combination hdiff + hb
    calc
      thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 μ) c.t =
          (2 * thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 μ) c.t) / 2 := by ring
      _ = (4 * μ (tH0 c)) / 2 := by rw [h2m]
      _ = 2 * μ (tH0 c) := by ring
  calc
    thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 ν) c.t =
        -thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 μ) c.t := hb
    _ = -(2 * μ (tH0 c)) := by rw [ha]
    _ = 2 * ν (tH0 c) := by rw [hμt]; ring

/-- Clifford for `|H : H0| = 2`: `ν^H` is irreducible iff `ν^s ≠ ν`.
(`⟸` is `remark_1_4`'s second assertion; `⟹` via `theta_norm`:
`ν^s = ν` gives `|ν^H|² = 2`, while an irreducible has norm one.) -/
private lemma theta_irreducible_iff (c : Hyp11 G) (h12 : Hyp12 c)
    (hH0index : (c.H0.subgroupOf c.H).index = 2)
    {ν : ClassFunction (↥c.H0)} (hν : IsIrreducibleCharacter ν) :
    IsIrreducibleCharacter (inducedFromSub (h12.H0_normal_in_H).1 ν) ↔
      conjChar c.H0 (s_normalizes_H0 c h12) ν ≠ ν := by
  classical
  constructor
  · intro hIrr hEq
    have hnorm2 : normSq (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν) = 2 := by
      rw [theta_norm c h12 hH0index hν]
      simp [hEq]
    have hnorm1 : normSq (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν) = 1 := by
      rw [normSq]
      exact scalarProduct_irreducible_self hIrr
    rw [hnorm1] at hnorm2
    norm_num at hnorm2
  · intro hne
    apply (remark_1_4 (h12.H0_normal_in_H).1 hH0index (S_le_H c c.s_mem_S)
      (s_not_mem_H0' c h12) hν).2
    intro hAll
    apply hne
    ext x
    simpa [conjChar, conjMonoidHom] using (hAll (x : G) x.2 (s_normalizes_H0 c h12 x))

/-- `(ν−μ)*(1) = 0` for orbit members `ν, μ` (equal degrees): the value of the
induced difference at `1`. -/
private lemma inducedFromSub_one_eq (c : Hyp11 G) (h12 : Hyp12 c)
    {ν μ : ClassFunction (↥c.H0)} (hdeg : ν 1 = μ 1) :
    inducedClassFunction c.H0 (ν - μ) 1 = 0 := by
  classical
  unfold inducedClassFunction
  have hsum : (∑ x : G, if hx : x⁻¹ * 1 * x ∈ c.H0 then (ν - μ) ⟨x⁻¹ * 1 * x, hx⟩ else 0) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro x hx_univ
    have hsummand : ∀ (hx : x⁻¹ * 1 * x ∈ c.H0), (ν - μ) ⟨x⁻¹ * 1 * x, hx⟩ = 0 := by
      intro hx
      have he : (⟨x⁻¹ * 1 * x, hx⟩ : ↥c.H0) = 1 := by
        apply Subtype.ext
        simp
      rw [he]
      simp [hdeg]
    by_cases hc : x⁻¹ * 1 * x ∈ c.H0
    · rw [dif_pos hc]
      exact hsummand hc
    · rw [dif_neg hc]
  rw [hsum]
  simp

/-! ## The `Λ`-orbit counting (the n ≥ 4 argument's inputs) -/

/-- An `s`-invariant `Λ`-orbit of an irreducible has exactly two `s`-fixed
members (`lemma_2_1_b`, Basic.lean). -/
private lemma orbit_s_fixed_card_eq_two_of_invariant (c : Hyp11 G) (h12 : Hyp12 c)
    [Fintype ↥(LambdaHom c.H0 c.U)]
    {ν : ClassFunction (↥c.H0)} (hν : IsIrreducibleCharacter ν)
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν ∈ orbit c.H0 c.U ν) :
    ((orbit c.H0 c.U ν).filter (fun μ =>
      conjChar c.H0 (s_normalizes_H0 c h12) μ = μ)).card = 2 :=
  lemma_2_1_b c h12 hν hνs

/-- `|Λ| = [H0 : U]`: the dual of `H0/U` (the `Λ`-characters) has the same
cardinality as the quotient. Route: `Λ = ker (restrictHom K ℂˣ)` with
`K := U.subgroupOf H0`; the kernel factors through `H0/K` (the
`QuotientGroup.lift` bijection); `H0/K` is commutative (`H0_comm_le_U`);
the dual of a finite abelian group has the same cardinality. -/
public lemma lambda_card_eq_index (c : Hyp11 G) (h12 : Hyp12 c) :
    Nat.card (LambdaHom c.H0 c.U) = (c.U.subgroupOf c.H0).index := by
  classical
  let K : Subgroup (↥c.H0) := c.U.subgroupOf c.H0
  have hKnormal : K.Normal := U_normal_subgroupOf c h12
  have hcomm : _root_.commutator (↥c.H0) ≤ K := by
    rw [show _root_.commutator (↥c.H0) = ⁅(⊤ : Subgroup (↥c.H0)), ⊤⁆ by rfl]
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    have hU : (((⁅g₁, g₂⁆ : ↥c.H0) : G) ∈ c.U) := by
      have hc' : ⁅(g₁ : G), (g₂ : G)⁆ ∈ c.U := by
        exact (Subgroup.commutator_le.mp h12.H0_comm_le_U) (g₁ : G) g₁.2 (g₂ : G) g₂.2
      simpa [commutatorElement_def] using hc'
    exact Subgroup.mem_subgroupOf.mpr hU
  -- the factorization bijection `Λ ≃ (H0/K →* ℂˣ)`
  let e : (↥(LambdaHom c.H0 c.U)) ≃ (↥c.H0 ⧸ K →* ℂˣ) :=
    { toFun := fun l => QuotientGroup.lift K l.1 (by
        intro k hk
        exact MonoidHom.mem_ker.mpr (l.2 (k : ↥c.H0) (Subgroup.mem_subgroupOf.mp hk)))
      invFun := fun ψ => ⟨ψ.comp (QuotientGroup.mk' K), by
        intro u hu
        have hq : (u : ↥c.H0 ⧸ K) = 1 := by
          exact (QuotientGroup.eq_one_iff (u : ↥c.H0)).mpr (Subgroup.mem_subgroupOf.mpr hu)
        simp [hq]⟩
      left_inv := by
        intro l
        apply Subtype.ext
        ext x
        simpa using QuotientGroup.lift_mk (φ := l.1) (N := K)
          (by
            intro k hk
            exact MonoidHom.mem_ker.mpr (l.2 (k : ↥c.H0) (Subgroup.mem_subgroupOf.mp hk))) x
      right_inv := by
        intro ψ
        apply MonoidHom.ext
        intro q
        refine QuotientGroup.induction_on q ?_
        intro x
        simpa using QuotientGroup.lift_mk (φ := ψ.comp (QuotientGroup.mk' K)) (N := K)
          (by
            intro k hk
            simp) x
    }
  calc
    Nat.card (LambdaHom c.H0 c.U) = Nat.card (↥c.H0 ⧸ K →* ℂˣ) := by
      exact Nat.card_congr e
    _ = Nat.card (↥c.H0 ⧸ K) := by
      let : CommGroup (↥c.H0 ⧸ K) :=
        { (inferInstance : Group (↥c.H0 ⧸ K)) with
          mul_comm := isMulCommutative_iff.mp
            ((Subgroup.Normal.quotient_commutative_iff_commutator_le (N := K)
              (G := ↥c.H0)).2 hcomm) }
      exact CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (↥c.H0 ⧸ K) ℂ
    _ = K.index := by
      exact Subgroup.index_eq_card K

/-- `|S0| = 2^m` (duplicate of the private `S0_nat_card`, Basic.lean). -/
private lemma S0_card_eq_pow (c : Hyp11 G) : Nat.card (c.S0 : Subgroup G) = 2 ^ c.m := by
  exact Nat.mul_right_cancel (by norm_num : 0 < 2) (by
    calc
      Nat.card (c.S0 : Subgroup G) * 2 = 2 * Nat.card (c.S0 : Subgroup G) := by rw [mul_comm]
      _ = Nat.card (c.S : Subgroup G) := c.S_index_two.symm
      _ = 2 * 2 ^ c.m := S_nat_card c
      _ = 2 ^ c.m * 2 := by rw [mul_comm])

/-- `U ∩ S0 = 1` (coprime orders: `|U|` odd, `|S0|` a 2-power). -/
private lemma U_inter_S0_eq_one (c : Hyp11 G) {x : G} (hxU : x ∈ c.U)
    (hxS : x ∈ (c.S0 : Subgroup G)) : x = 1 := by
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
  have hordS : orderOf x ∣ Nat.card (c.S0 : Subgroup G) := by
    change orderOf ((c.S0 : Subgroup G).subtype (⟨x, hxS⟩ : ↥(c.S0 : Subgroup G))) ∣
      Nat.card (c.S0 : Subgroup G)
    rw [orderOf_injective (c.S0 : Subgroup G).subtype
      (Subgroup.subtype_injective (c.S0 : Subgroup G)) (⟨x, hxS⟩ : ↥(c.S0 : Subgroup G))]
    have hxS' : orderOf (⟨x, hxS⟩ : ↥(c.S0 : Subgroup G)) ∣
        Fintype.card ↥(c.S0 : Subgroup G) :=
      orderOf_dvd_card (G := ↥(c.S0 : Subgroup G)) (x := ⟨x, hxS⟩)
    rwa [← Nat.card_eq_fintype_card] at hxS'
  have hpow : orderOf x ∣ 2 ^ c.m := by
    rw [← S0_card_eq_pow c]
    exact hordS
  have hcop' : Nat.Coprime (2 ^ c.m) (Nat.card ↥c.U) := by
    exact hcop.pow_left _
  have h1' : orderOf x = 1 := by
    have hdvd : orderOf x ∣ 1 := by
      rw [← hcop'.gcd_eq_one]
      exact Nat.dvd_gcd hpow hordU
    exact Nat.dvd_one.mp hdvd
  exact hx1 (orderOf_eq_one_iff.mp h1')

/-- `[H0 : U] = |S0|`: the map `S0 → H0/U`, `r ↦ rU` is a bijection
(`H0 = U·S0` + `U ∩ S0 = 1`). -/
private lemma U_index_eq_S0_card (c : Hyp11 G) (h12 : Hyp12 c) :
    (c.U.subgroupOf c.H0).index = Nat.card (c.S0 : Subgroup G) := by
  classical
  let K : Subgroup (↥c.H0) := c.U.subgroupOf c.H0
  have hKnormal : K.Normal := U_normal_subgroupOf c h12
  let f : ↥c.S0 → ↥c.H0 ⧸ K := fun r =>
    (QuotientGroup.mk (⟨(r : G), S0_le_H0 c r.2⟩ : ↥c.H0) : ↥c.H0 ⧸ K)
  have hinj : Function.Injective f := by
    intro r₁ r₂ hEq
    unfold f at hEq
    have hf1 : f (r₁ * r₂⁻¹) = 1 := by
      unfold f
      have hsub : (⟨((r₁ * r₂⁻¹ : ↥c.S0) : G), S0_le_H0 c ((r₁ * r₂⁻¹ : ↥c.S0)).2⟩ : ↥c.H0) =
          (⟨(r₁ : G), S0_le_H0 c r₁.2⟩ : ↥c.H0) * (⟨(r₂ : G), S0_le_H0 c r₂.2⟩ : ↥c.H0)⁻¹ := by
        apply Subtype.ext
        rfl
      rw [hsub, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hEq]
      simp
    have hU : ((r₁ * r₂⁻¹ : ↥c.S0) : G) ∈ c.U := by
      let y : ↥c.H0 := ⟨((r₁ * r₂⁻¹ : ↥c.S0) : G), S0_le_H0 c ((r₁ * r₂⁻¹ : ↥c.S0)).2⟩
      have hk : y ∈ K := by
        exact (QuotientGroup.eq_one_iff y).1 (by
          simpa [f, y] using hf1)
      exact Subgroup.mem_subgroupOf.mp hk
    have hEq' : (r₁ * r₂⁻¹ : ↥c.S0) = 1 := by
      apply Subtype.ext
      exact U_inter_S0_eq_one c hU ((r₁ * r₂⁻¹ : ↥c.S0)).2
    apply Subtype.ext
    exact mul_inv_eq_one.mp (congrArg (fun z : ↥c.S0 => (z : G)) hEq')
  have hsurj : Function.Surjective f := by
    intro q
    rcases QuotientGroup.mk'_surjective K q with ⟨x, hx⟩
    rcases H0_eq_U_mul_S0 c h12 (x := x) with ⟨u, r, hxEq⟩
    refine ⟨r, ?_⟩
    have huH0 : (u : G) ∈ c.H0 := by
      exact (le_sup_left : c.U ≤ c.U ⊔ (c.S0 : Subgroup G)) u.2
    let uH0 : ↥c.H0 := ⟨(u : G), huH0⟩
    let rH0 : ↥c.H0 := ⟨(r : G), S0_le_H0 c r.2⟩
    have hxEq'' : x = uH0 * rH0 := by
      apply Subtype.ext
      exact hxEq
    have huK : uH0 ∈ K := by
      exact Subgroup.mem_subgroupOf.mpr u.2
    have hmk : (QuotientGroup.mk x : ↥c.H0 ⧸ K) = QuotientGroup.mk rH0 := by
      rw [hxEq'', QuotientGroup.mk_mul]
      have hu1 : (QuotientGroup.mk uH0 : ↥c.H0 ⧸ K) = 1 := by
        exact (QuotientGroup.eq_one_iff uH0).mpr huK
      rw [hu1, one_mul]
    unfold f
    exact hmk.symm.trans hx
  have hcard : Nat.card (↥c.H0 ⧸ K) = Nat.card (↥c.S0) := by
    exact Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩).symm
  calc
    (c.U.subgroupOf c.H0).index = Nat.card (↥c.H0 ⧸ K) := by
      exact Subgroup.index_eq_card K
    _ = Nat.card (↥c.S0) := hcard

/-- `|Λ| = 2^m` (via the dual-cardinality and `[H0 : U] = |S0| = 2^m`). -/
private lemma lambda_card_eq_pow (c : Hyp11 G) (h12 : Hyp12 c)
    [Fintype ↥(LambdaHom c.H0 c.U)] :
    Fintype.card (LambdaHom c.H0 c.U) = 2 ^ c.m := by
  rw [← Nat.card_eq_fintype_card, lambda_card_eq_index c h12, U_index_eq_S0_card c h12]
  exact S0_card_eq_pow c

/-- `|Λν|` is a 2-power: `|L| · |Stab ν| = |Λ| = 2^m` (orbit-fiber counting). -/
private lemma orbit_card_is_pow_two (c : Hyp11 G) (h12 : Hyp12 c)
    [Fintype ↥(LambdaHom c.H0 c.U)] (ν : ClassFunction (↥c.H0)) :
    ∃ k : ℕ, (orbit c.H0 c.U ν).card = 2 ^ k := by
  classical
  have hcard : (orbit c.H0 c.U ν).card *
      (Finset.univ.filter (fun s : LambdaHom c.H0 c.U => LambdaChar s.1 * ν = ν)).card =
      Fintype.card (LambdaHom c.H0 c.U) := by
    have hfib := Finset.card_eq_sum_card_fiberwise
      (f := fun l : LambdaHom c.H0 c.U => LambdaChar l.1 * ν)
      (s := Finset.univ) (t := orbit c.H0 c.U ν)
      (by intro l _; exact Finset.mem_image.mpr ⟨l, Finset.mem_univ l, rfl⟩)
    calc
      (orbit c.H0 c.U ν).card *
          (Finset.univ.filter (fun s : LambdaHom c.H0 c.U => LambdaChar s.1 * ν = ν)).card =
        ∑ μ ∈ orbit c.H0 c.U ν,
          (Finset.univ.filter (fun l : LambdaHom c.H0 c.U => LambdaChar l.1 * ν = μ)).card := by
            rw [Finset.sum_congr rfl (fun μ hμ => orbit_fiber_card c.H0 c.U ν μ hμ)]
            rw [← Finset.sum_const_nat (fun μ hμ => rfl)]
      _ = (Finset.univ : Finset (LambdaHom c.H0 c.U)).card := by
            exact hfib.symm
  have hdvd : (orbit c.H0 c.U ν).card ∣ Fintype.card (LambdaHom c.H0 c.U) := by
    exact ⟨(Finset.univ.filter (fun s : LambdaHom c.H0 c.U => LambdaChar s.1 * ν = ν)).card, hcard.symm⟩
  have hdvd' : (orbit c.H0 c.U ν).card ∣ 2 ^ c.m := by
    refine dvd_trans hdvd ?_
    rw [lambda_card_eq_pow c h12]
  rcases (Nat.dvd_prime_pow Nat.prime_two).1 hdvd' with ⟨k, _hk, hk⟩
  exact ⟨k, hk⟩

/-- Conjugation by `s` maps orbits to orbits: `orbit(ν^s)` is the
`s`-conjugate of `orbit ν`. -/
private lemma orbit_conjChar_eq (c : Hyp11 G) (h12 : Hyp12 c)
    [Fintype ↥(LambdaHom c.H0 c.U)] (ν : ClassFunction (↥c.H0)) :
    orbit c.H0 c.U (conjChar c.H0 (s_normalizes_H0 c h12) ν) =
      (orbit c.H0 c.U ν).image (fun μ =>
        conjChar c.H0 (s_normalizes_H0 c h12) μ) := by
  classical
  apply Finset.ext
  intro μ
  constructor
  · intro hμ
    refine Finset.mem_image.mpr
      ⟨conjChar c.H0 (s_normalizes_H0 c h12) μ,
        orbit_conjChar_subset c h12 μ hμ, conjChar_conjChar c h12 μ⟩
  · intro hμ
    rcases (Finset.mem_image.mp hμ) with ⟨a, ha, rfl⟩
    exact orbit_subset_conjChar c h12 a ha

/-- `(a,b) = 0` for orbit members from distinct orbits (orthogonality of
irreducible characters). -/
private lemma scalarProduct_orbit_disjoint (c : Hyp11 G)
    [Fintype ↥(LambdaHom c.H0 c.U)] {ν₁ ν₂ a b : ClassFunction (↥c.H0)}
    (hν₁ : IsIrreducibleCharacter ν₁) (hν₂ : IsIrreducibleCharacter ν₂)
    (ha : a ∈ orbit c.H0 c.U ν₁) (hb : b ∈ orbit c.H0 c.U ν₂)
    (hne : ν₁ ∉ orbit c.H0 c.U ν₂) : scalarProduct (↥c.H0) a b = 0 := by
  classical
  have hirr₁ : IsIrreducibleCharacter a := orbit_mem_isIrreducible c.H0 c.U hν₁ ha
  have hirr₂ : IsIrreducibleCharacter b := orbit_mem_isIrreducible c.H0 c.U hν₂ hb
  rw [scalarProduct_irr_ite hirr₁ hirr₂]
  by_cases h : a = b
  · exfalso
    apply hne
    have ho1 : orbit c.H0 c.U a = orbit c.H0 c.U ν₁ := orbit_eq_of_mem c ha
    have ho2 : orbit c.H0 c.U a = orbit c.H0 c.U ν₂ := orbit_eq_of_mem c (by rwa [← h] at hb)
    have hmem : ν₁ ∈ orbit c.H0 c.U ν₂ := by
      rw [← ho2, ho1]
      exact orbit_self_mem c ν₁
    exact hmem
  · simp [h]

/-- The `H`-side orthogonality for (iv): `(θ_{μ₁}−θ_{ν₁}, θ_{μ₂}−θ_{ν₂})_H = 0`
when the two orbits are distinct and not `s`-conjugate. -/
private lemma theta_pair_orth (c : Hyp11 G) (h12 : Hyp12 c)
    (hH0index : (c.H0.subgroupOf c.H).index = 2)
    {ν₁ ν₂ μ₁ μ₂ : ClassFunction (↥c.H0)}
    (hν₁ : IsIrreducibleCharacter ν₁) (hν₂ : IsIrreducibleCharacter ν₂)
    (hμ₁L : μ₁ ∈ orbit c.H0 c.U ν₁) (hμ₂L : μ₂ ∈ orbit c.H0 c.U ν₂)
    (hν₁not : ν₁ ∉ orbit c.H0 c.U ν₂)
    (hν₁s_not : conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ∉ orbit c.H0 c.U ν₂) :
    scalarProduct (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 μ₁ -
        inducedFromSub (h12.H0_normal_in_H).1 ν₁)
      (inducedFromSub (h12.H0_normal_in_H).1 μ₂ -
        inducedFromSub (h12.H0_normal_in_H).1 ν₂) = 0 := by
  classical
  have hμ₁ : IsIrreducibleCharacter μ₁ := orbit_mem_isIrreducible c.H0 c.U hν₁ hμ₁L
  have hμ₂ : IsIrreducibleCharacter μ₂ := orbit_mem_isIrreducible c.H0 c.U hν₂ hμ₂L
  have hs_inv : ∀ x : ↥c.H0, c.s⁻¹ * (x : G) * c.s ∈ c.H0 := by
    intro x
    simpa using (h12.H0_normal_in_H).2 c.s⁻¹ (c.H.inv_mem (s_mem_H c)) (x : G) x.2
  -- `ν₁ ∉ orbit(ν₂^s)` (from `ν₁^s ∉ orbit ν₂`, `s² = 1`)
  have hν₁s : IsIrreducibleCharacter (conjChar c.H0 (s_normalizes_H0 c h12) ν₁) :=
    isIrreducibleCharacter_conjChar c.H0 (s_normalizes_H0 c h12) hs_inv hν₁
  have hν₂s : IsIrreducibleCharacter (conjChar c.H0 (s_normalizes_H0 c h12) ν₂) :=
    isIrreducibleCharacter_conjChar c.H0 (s_normalizes_H0 c h12) hs_inv hν₂
  -- `ν₁ ∉ orbit(ν₂^s)` (from `ν₁^s ∉ orbit ν₂`, `s² = 1`)
  have hν₁not2 : ν₁ ∉ orbit c.H0 c.U (conjChar c.H0 (s_normalizes_H0 c h12) ν₂) := by
    intro h1
    apply hν₁s_not
    have h2 : conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ∈
        orbit c.H0 c.U (conjChar c.H0 (s_normalizes_H0 c h12)
          (conjChar c.H0 (s_normalizes_H0 c h12) ν₂)) :=
      orbit_subset_conjChar c h12 ν₁ h1
    rw [conjChar_conjChar c h12 ν₂] at h2
    exact h2
  -- `ν₁^s ∉ orbit(ν₂^s)` (from `ν₁ ∉ orbit ν₂`)
  have hν₁s_not2 : conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ∉
      orbit c.H0 c.U (conjChar c.H0 (s_normalizes_H0 c h12) ν₂) := by
    intro h1
    apply hν₁not
    have h2 : conjChar c.H0 (s_normalizes_H0 c h12)
        (conjChar c.H0 (s_normalizes_H0 c h12) ν₁) ∈
        orbit c.H0 c.U (conjChar c.H0 (s_normalizes_H0 c h12)
          (conjChar c.H0 (s_normalizes_H0 c h12) ν₂)) :=
      orbit_subset_conjChar c h12 (conjChar c.H0 (s_normalizes_H0 c h12) ν₁) h1
    rw [conjChar_conjChar c h12 ν₁] at h2
    rw [conjChar_conjChar c h12 ν₂] at h2
    exact h2
  -- the four expansions
  have e12 := theta_pair_scalar_H' c h12 hH0index hμ₁ hμ₂
  have e1ν2 := theta_pair_scalar_H' c h12 hH0index hμ₁ hν₂
  have eν12 := theta_pair_scalar_H' c h12 hH0index hν₁ hμ₂
  have eν1ν2 := theta_pair_scalar_H' c h12 hH0index hν₁ hν₂
  -- the sixteen vanishing scalar products
  have sp1 : scalarProduct (↥c.H0) μ₁ μ₂ = 0 :=
    scalarProduct_orbit_disjoint c hν₁ hν₂ hμ₁L hμ₂L hν₁not
  have sp2 : scalarProduct (↥c.H0) μ₁
      (conjChar c.H0 (s_normalizes_H0 c h12) μ₂) = 0 :=
    scalarProduct_orbit_disjoint c hν₁ hν₂s hμ₁L
      (orbit_subset_conjChar c h12 μ₂ hμ₂L) hν₁not2
  have sp3 : scalarProduct (↥c.H0) (conjChar c.H0 (s_normalizes_H0 c h12) μ₁) μ₂ = 0 :=
    scalarProduct_orbit_disjoint c hν₁s hν₂
      (orbit_subset_conjChar c h12 μ₁ hμ₁L) hμ₂L hν₁s_not
  have sp4 : scalarProduct (↥c.H0) (conjChar c.H0 (s_normalizes_H0 c h12) μ₁)
      (conjChar c.H0 (s_normalizes_H0 c h12) μ₂) = 0 :=
    scalarProduct_orbit_disjoint c hν₁s hν₂s
      (orbit_subset_conjChar c h12 μ₁ hμ₁L)
      (orbit_subset_conjChar c h12 μ₂ hμ₂L) hν₁s_not2
  have sp5 : scalarProduct (↥c.H0) μ₁ ν₂ = 0 :=
    scalarProduct_orbit_disjoint c hν₁ hν₂ hμ₁L (orbit_self_mem c ν₂) hν₁not
  have sp6 : scalarProduct (↥c.H0) μ₁
      (conjChar c.H0 (s_normalizes_H0 c h12) ν₂) = 0 :=
    scalarProduct_orbit_disjoint c hν₁ hν₂s hμ₁L
      (orbit_self_mem c (conjChar c.H0 (s_normalizes_H0 c h12) ν₂)) hν₁not2
  have sp7 : scalarProduct (↥c.H0) (conjChar c.H0 (s_normalizes_H0 c h12) μ₁) ν₂ = 0 :=
    scalarProduct_orbit_disjoint c hν₁s hν₂
      (orbit_subset_conjChar c h12 μ₁ hμ₁L) (orbit_self_mem c ν₂) hν₁s_not
  have sp8 : scalarProduct (↥c.H0) (conjChar c.H0 (s_normalizes_H0 c h12) μ₁)
      (conjChar c.H0 (s_normalizes_H0 c h12) ν₂) = 0 :=
    scalarProduct_orbit_disjoint c hν₁s hν₂s
      (orbit_subset_conjChar c h12 μ₁ hμ₁L)
      (orbit_self_mem c (conjChar c.H0 (s_normalizes_H0 c h12) ν₂)) hν₁s_not2
  have sp9 : scalarProduct (↥c.H0) ν₁ μ₂ = 0 :=
    scalarProduct_orbit_disjoint c hν₁ hν₂ (orbit_self_mem c ν₁) hμ₂L hν₁not
  have sp10 : scalarProduct (↥c.H0) ν₁
      (conjChar c.H0 (s_normalizes_H0 c h12) μ₂) = 0 :=
    scalarProduct_orbit_disjoint c hν₁ hν₂s (orbit_self_mem c ν₁)
      (orbit_subset_conjChar c h12 μ₂ hμ₂L) hν₁not2
  have sp11 : scalarProduct (↥c.H0) (conjChar c.H0 (s_normalizes_H0 c h12) ν₁) μ₂ = 0 :=
    scalarProduct_orbit_disjoint c hν₁s hν₂
      (orbit_self_mem c (conjChar c.H0 (s_normalizes_H0 c h12) ν₁)) hμ₂L hν₁s_not
  have sp12 : scalarProduct (↥c.H0) (conjChar c.H0 (s_normalizes_H0 c h12) ν₁)
      (conjChar c.H0 (s_normalizes_H0 c h12) μ₂) = 0 :=
    scalarProduct_orbit_disjoint c hν₁s hν₂s
      (orbit_self_mem c (conjChar c.H0 (s_normalizes_H0 c h12) ν₁))
      (orbit_subset_conjChar c h12 μ₂ hμ₂L) hν₁s_not2
  have sp13 : scalarProduct (↥c.H0) ν₁ ν₂ = 0 :=
    scalarProduct_orbit_disjoint c hν₁ hν₂ (orbit_self_mem c ν₁)
      (orbit_self_mem c ν₂) hν₁not
  have sp14 : scalarProduct (↥c.H0) ν₁
      (conjChar c.H0 (s_normalizes_H0 c h12) ν₂) = 0 :=
    scalarProduct_orbit_disjoint c hν₁ hν₂s (orbit_self_mem c ν₁)
      (orbit_self_mem c (conjChar c.H0 (s_normalizes_H0 c h12) ν₂)) hν₁not2
  have sp15 : scalarProduct (↥c.H0) (conjChar c.H0 (s_normalizes_H0 c h12) ν₁) ν₂ = 0 :=
    scalarProduct_orbit_disjoint c hν₁s hν₂
      (orbit_self_mem c (conjChar c.H0 (s_normalizes_H0 c h12) ν₁))
      (orbit_self_mem c ν₂) hν₁s_not
  have sp16 : scalarProduct (↥c.H0) (conjChar c.H0 (s_normalizes_H0 c h12) ν₁)
      (conjChar c.H0 (s_normalizes_H0 c h12) ν₂) = 0 :=
    scalarProduct_orbit_disjoint c hν₁s hν₂s
      (orbit_self_mem c (conjChar c.H0 (s_normalizes_H0 c h12) ν₁))
      (orbit_self_mem c (conjChar c.H0 (s_normalizes_H0 c h12) ν₂)) hν₁s_not2
  rw [scalarProduct_sub_left, scalarProduct_sub_right, scalarProduct_sub_right]
  rw [e12, e1ν2, eν12, eν1ν2]
  simp [sp1, sp2, sp3, sp4, sp5, sp6, sp7, sp8, sp9, sp10, sp11, sp12, sp13,
    sp14, sp15, sp16]

/-- `θ₁ = θ₂` forces `ν₂ = ν₁` or `ν₂^s = ν₁` (the orbit is recovered from the
induced character). -/
private lemma theta_eq_imp_conj (c : Hyp11 G) (h12 : Hyp12 c)
    (hH0index : (c.H0.subgroupOf c.H).index = 2)
    {ν₁ ν₂ : ClassFunction (↥c.H0)} (hν₁ : IsIrreducibleCharacter ν₁)
    (hν₂ : IsIrreducibleCharacter ν₂)
    (hEq : inducedFromSub (h12.H0_normal_in_H).1 ν₁ =
      inducedFromSub (h12.H0_normal_in_H).1 ν₂) :
    ν₂ = ν₁ ∨ conjChar c.H0 (s_normalizes_H0 c h12) ν₂ = ν₁ := by
  classical
  have hs_inv : ∀ x : ↥c.H0, c.s⁻¹ * (x : G) * c.s ∈ c.H0 := by
    intro x
    simpa using (h12.H0_normal_in_H).2 c.s⁻¹ (c.H.inv_mem (s_mem_H c)) (x : G) x.2
  have hν₂s : IsIrreducibleCharacter (conjChar c.H0 (s_normalizes_H0 c h12) ν₂) :=
    isIrreducibleCharacter_conjChar c.H0 (s_normalizes_H0 c h12) hs_inv hν₂
  have hnorm1 : normSq (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν₁) ≠ 0 := by
    have hn := theta_norm c h12 hH0index hν₁
    rw [hn]
    by_cases h : conjChar c.H0 (s_normalizes_H0 c h12) ν₁ = ν₁ <;> simp [h] <;> norm_num
  have hpair : scalarProduct (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν₁)
      (inducedFromSub (h12.H0_normal_in_H).1 ν₂) =
        normSq (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν₁) := by
    rw [hEq]
    rfl
  have h1 := theta_pair_scalar_H' c h12 hH0index hν₁ hν₂
  have hS0 : scalarProduct (↥c.H0) ν₁ ν₂ +
      scalarProduct (↥c.H0) ν₁ (conjChar c.H0 (s_normalizes_H0 c h12) ν₂) +
      scalarProduct (↥c.H0) (conjChar c.H0 (s_normalizes_H0 c h12) ν₁) ν₂ +
      scalarProduct (↥c.H0) (conjChar c.H0 (s_normalizes_H0 c h12) ν₁)
        (conjChar c.H0 (s_normalizes_H0 c h12) ν₂) ≠ 0 := by
    intro hz
    apply hnorm1
    have hz' : (2 : ℂ)⁻¹ * (scalarProduct (↥c.H0) ν₁ ν₂ +
        scalarProduct (↥c.H0) ν₁ (conjChar c.H0 (s_normalizes_H0 c h12) ν₂) +
        scalarProduct (↥c.H0) (conjChar c.H0 (s_normalizes_H0 c h12) ν₁) ν₂ +
        scalarProduct (↥c.H0) (conjChar c.H0 (s_normalizes_H0 c h12) ν₁)
          (conjChar c.H0 (s_normalizes_H0 c h12) ν₂)) = 0 := by
      rw [hz]
      norm_num
    rw [← hpair, h1]
    exact hz'
  by_cases h₂ : ν₂ = ν₁
  · left
    exact h₂
  · by_cases h₂s : conjChar c.H0 (s_normalizes_H0 c h12) ν₂ = ν₁
    · right
      exact h₂s
    · exfalso
      apply hS0
      have sp1 : scalarProduct (↥c.H0) ν₁ ν₂ = 0 := by
        rw [scalarProduct_irr_ite hν₁ hν₂]
        by_cases hEq : ν₁ = ν₂
        · exact False.elim (h₂ hEq.symm)
        · simp [hEq]
      have sp2 : scalarProduct (↥c.H0) ν₁
          (conjChar c.H0 (s_normalizes_H0 c h12) ν₂) = 0 := by
        rw [scalarProduct_irr_ite hν₁ hν₂s]
        by_cases hEq : ν₁ = conjChar c.H0 (s_normalizes_H0 c h12) ν₂
        · exact False.elim (h₂s hEq.symm)
        · simp [hEq]
      have sp3 : scalarProduct (↥c.H0) (conjChar c.H0 (s_normalizes_H0 c h12) ν₁) ν₂ = 0 := by
        rw [scalarProduct_irr_ite
          (isIrreducibleCharacter_conjChar c.H0 (s_normalizes_H0 c h12) hs_inv hν₁) hν₂]
        have h31 : conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ≠ ν₂ := by
          intro h3
          apply h₂s
          have hc := congrArg (conjChar c.H0 (s_normalizes_H0 c h12)) h3
          rw [conjChar_conjChar c h12 ν₁] at hc
          exact hc.symm
        simp [h31]
      have sp4 : scalarProduct (↥c.H0) (conjChar c.H0 (s_normalizes_H0 c h12) ν₁)
          (conjChar c.H0 (s_normalizes_H0 c h12) ν₂) = 0 := by
        rw [scalarProduct_irr_ite
          (isIrreducibleCharacter_conjChar c.H0 (s_normalizes_H0 c h12) hs_inv hν₁) hν₂s]
        have h41 : conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ≠
            conjChar c.H0 (s_normalizes_H0 c h12) ν₂ := by
          intro h4
          apply h₂
          have hc := congrArg (conjChar c.H0 (s_normalizes_H0 c h12)) h4
          rw [conjChar_conjChar c h12 ν₁] at hc
          rw [conjChar_conjChar c h12 ν₂] at hc
          exact hc.symm
        simp [h41]
      simp [sp1, sp2, sp3, sp4]



/-! ## The `n`-formula: `n = |L|` or `2n = |L| + 2` (Fact 2) -/

/-- A fixed member of an orbit forces the orbit to be `s`-invariant. -/
private lemma s_fixed_mem_imp_invariant (c : Hyp11 G) (h12 : Hyp12 c)
    [Fintype ↥(LambdaHom c.H0 c.U)] {ν μ : ClassFunction (↥c.H0)}
    (hμ : μ ∈ orbit c.H0 c.U ν)
    (hμs : conjChar c.H0 (s_normalizes_H0 c h12) μ = μ) :
    conjChar c.H0 (s_normalizes_H0 c h12) ν ∈ orbit c.H0 c.U ν := by
  classical
  have hσμ : conjChar c.H0 (s_normalizes_H0 c h12) μ ∈
      orbit c.H0 c.U (conjChar c.H0 (s_normalizes_H0 c h12) ν) := by
    rw [orbit_conjChar_eq c h12]
    exact Finset.mem_image.mpr ⟨μ, hμ, rfl⟩
  have hμ' : μ ∈ orbit c.H0 c.U (conjChar c.H0 (s_normalizes_H0 c h12) ν) := by
    rwa [hμs] at hσμ
  have ho1 : orbit c.H0 c.U μ =
      orbit c.H0 c.U (conjChar c.H0 (s_normalizes_H0 c h12) ν) :=
    orbit_eq_of_mem c hμ'
  have ho2 : orbit c.H0 c.U μ = orbit c.H0 c.U ν := orbit_eq_of_mem c hμ
  rw [← ho2, ho1]
  exact orbit_self_mem c (conjChar c.H0 (s_normalizes_H0 c h12) ν)

/-- The induced-character map is injective on the orbit when `ν^s ∉ Lν`
(`theta_eq_imp_conj`; the alternative `μ₂ = μ₁^s` would force `ν^s ∈ Lν`). -/
private lemma theta_of_orbit_injective_of_not_invariant (c : Hyp11 G) (h12 : Hyp12 c)
    [Fintype ↥(LambdaHom c.H0 c.U)] {ν : ClassFunction (↥c.H0)}
    (hν : IsIrreducibleCharacter ν)
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν ∉ orbit c.H0 c.U ν) :
    Set.InjOn (fun μ : ClassFunction (↥c.H0) =>
      inducedFromSub (h12.H0_normal_in_H).1 μ) (orbit c.H0 c.U ν) := by
  classical
  intro μ₁ hμ₁ μ₂ hμ₂ hEq
  have hIrr₁ : IsIrreducibleCharacter μ₁ := orbit_mem_isIrreducible c.H0 c.U hν hμ₁
  have hIrr₂ : IsIrreducibleCharacter μ₂ := orbit_mem_isIrreducible c.H0 c.U hν hμ₂
  rcases theta_eq_imp_conj c h12 (H0_index c h12) hIrr₁ hIrr₂ hEq with h | h
  · exact h.symm
  · exfalso
    apply hνs
    have hσμ₂ : conjChar c.H0 (s_normalizes_H0 c h12) μ₂ ∈
        orbit c.H0 c.U (conjChar c.H0 (s_normalizes_H0 c h12) ν) := by
      rw [orbit_conjChar_eq c h12]
      exact Finset.mem_image.mpr ⟨μ₂, hμ₂, rfl⟩
    have hμ₁' : μ₁ ∈ orbit c.H0 c.U (conjChar c.H0 (s_normalizes_H0 c h12) ν) := by
      rwa [h] at hσμ₂
    have ho1 : orbit c.H0 c.U μ₁ =
        orbit c.H0 c.U (conjChar c.H0 (s_normalizes_H0 c h12) ν) :=
      orbit_eq_of_mem c hμ₁'
    have ho2 : orbit c.H0 c.U μ₁ = orbit c.H0 c.U ν := orbit_eq_of_mem c hμ₁
    rw [← ho2, ho1]
    exact orbit_self_mem c (conjChar c.H0 (s_normalizes_H0 c h12) ν)

/-- `n = |L|` when `ν^s ∉ Lν` (no `s`-fixed members, all induced characters
irreducible, the induced map injective on the orbit). -/
private lemma theta_card_eq_orbit_card_of_not_invariant (c : Hyp11 G) (h12 : Hyp12 c)
    [Fintype ↥(LambdaHom c.H0 c.U)] {ν : ClassFunction (↥c.H0)}
    (hν : IsIrreducibleCharacter ν)
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν ∉ orbit c.H0 c.U ν) :
    (thetaOfOrbit c h12 (orbit c.H0 c.U ν)).card = (orbit c.H0 c.U ν).card := by
  classical
  rw [thetaOfOrbit]
  exact Finset.card_image_of_injOn (theta_of_orbit_injective_of_not_invariant c h12 hν hνs)


/-- For an `s`-invariant orbit, the `s`-image of a member lies in the orbit:
`σ(L) = L`. -/
private lemma orbit_s_closed_of_invariant (c : Hyp11 G) (h12 : Hyp12 c)
    {ν : ClassFunction (↥c.H0)}
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν ∈ orbit c.H0 c.U ν)
    {a : ClassFunction (↥c.H0)} (ha : a ∈ orbit c.H0 c.U ν) :
    conjChar c.H0 (s_normalizes_H0 c h12) a ∈ orbit c.H0 c.U ν := by
  classical
  have hσa : conjChar c.H0 (s_normalizes_H0 c h12) a ∈
      orbit c.H0 c.U (conjChar c.H0 (s_normalizes_H0 c h12) ν) := by
    rw [orbit_conjChar_eq c h12]
    exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
  have hEqOrbit : orbit c.H0 c.U (conjChar c.H0 (s_normalizes_H0 c h12) ν) =
      orbit c.H0 c.U ν := by
    rw [orbit_eq_of_mem c hνs]
  rwa [hEqOrbit] at hσa

/-- In an `s`-invariant orbit, each fiber of `θ` is the `s`-pair `{μ₀, σ μ₀}`. -/
private lemma theta_fiber_pair_of_invariant (c : Hyp11 G) (h12 : Hyp12 c)
    {ν : ClassFunction (↥c.H0)} (hν : IsIrreducibleCharacter ν)
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν ∈ orbit c.H0 c.U ν)
    {θ' : ClassFunction (↥c.H)} {μ₀ : ClassFunction (↥c.H0)}
    (hμ₀ : μ₀ ∈ orbit c.H0 c.U ν)
    (hμ₀θ' : inducedFromSub (h12.H0_normal_in_H).1 μ₀ = θ') :
    (orbit c.H0 c.U ν).filter (fun μ => inducedFromSub (h12.H0_normal_in_H).1 μ = θ') =
      ({μ₀, conjChar c.H0 (s_normalizes_H0 c h12) μ₀} :
        Finset (ClassFunction (↥c.H0))) := by
  classical
  let L : Finset (ClassFunction (↥c.H0)) := orbit c.H0 c.U ν
  let θ : ClassFunction (↥c.H0) → ClassFunction (↥c.H) := fun μ =>
    inducedFromSub (h12.H0_normal_in_H).1 μ
  let σ : ClassFunction (↥c.H0) → ClassFunction (↥c.H0) := fun μ =>
    conjChar c.H0 (s_normalizes_H0 c h12) μ
  have hσ2 : ∀ μ : ClassFunction (↥c.H0), σ (σ μ) = μ := by
    intro μ
    exact conjChar_conjChar c h12 μ
  have hLσ : ∀ a ∈ L, σ a ∈ L := by
    intro a ha
    exact orbit_s_closed_of_invariant c h12 hνs ha
  apply Finset.ext
  intro μ
  constructor
  · intro hμ
    have hμL : μ ∈ L := (Finset.mem_filter.mp hμ).1
    have hμθ : θ μ = θ' := (Finset.mem_filter.mp hμ).2
    have hIrr₀ : IsIrreducibleCharacter μ₀ := orbit_mem_isIrreducible c.H0 c.U hν hμ₀
    have hIrrμ : IsIrreducibleCharacter μ := orbit_mem_isIrreducible c.H0 c.U hν hμL
    rw [Finset.mem_insert, Finset.mem_singleton]
    rcases theta_eq_imp_conj c h12 (H0_index c h12) hIrr₀ hIrrμ
      (hμθ.trans hμ₀θ'.symm).symm with h | h
    · left
      exact h
    · right
      exact (hσ2 μ).symm.trans (congrArg σ h)
  · intro hμ
    rw [Finset.mem_insert, Finset.mem_singleton] at hμ
    rcases hμ with h | h
    · subst μ
      exact Finset.mem_filter.mpr ⟨hμ₀, hμ₀θ'⟩
    · subst h
      have hIrr₀ : IsIrreducibleCharacter μ₀ := orbit_mem_isIrreducible c.H0 c.U hν hμ₀
      exact Finset.mem_filter.mpr
        ⟨hLσ μ₀ hμ₀,
          (inducedFromSub_conjChar_eq c h12 (H0_index c h12) hIrr₀).trans hμ₀θ'⟩

/-- `2n = |L| + 2` for an `s`-invariant orbit: exactly two `s`-fixed members
(`orbit_s_fixed_card_eq_two_of_invariant`), the rest in `s`-pairs, and the
induced-character map is constant on each `s`-pair
(`inducedFromSub_conjChar_eq`) and injective across pairs
(`theta_eq_imp_conj`). -/
private lemma theta_card_mul_two_eq_orbit_card_add_two (c : Hyp11 G) (h12 : Hyp12 c)
    [Fintype ↥(LambdaHom c.H0 c.U)] {ν : ClassFunction (↥c.H0)}
    (hν : IsIrreducibleCharacter ν)
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν ∈ orbit c.H0 c.U ν) :
    (thetaOfOrbit c h12 (orbit c.H0 c.U ν)).card * 2 =
      (orbit c.H0 c.U ν).card + 2 := by
  classical
  let L : Finset (ClassFunction (↥c.H0)) := orbit c.H0 c.U ν
  let θ : ClassFunction (↥c.H0) → ClassFunction (↥c.H) :=
    fun μ => inducedFromSub (h12.H0_normal_in_H).1 μ
  let σ : ClassFunction (↥c.H0) → ClassFunction (↥c.H0) :=
    fun μ => conjChar c.H0 (s_normalizes_H0 c h12) μ
  let Θ : Finset (ClassFunction (↥c.H)) := thetaOfOrbit c h12 L
  have hσ2 : ∀ μ : ClassFunction (↥c.H0), σ (σ μ) = μ := by
    intro μ
    exact conjChar_conjChar c h12 μ
  -- the orbit is closed under `s`
  have hLσ : ∀ a ∈ L, σ a ∈ L := by
    intro a ha
    have hσa : σ a ∈ orbit c.H0 c.U (σ ν) := by
      rw [orbit_conjChar_eq c h12]
      exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
    have hEqOrbit : orbit c.H0 c.U (σ ν) = L := by
      change orbit c.H0 c.U (conjChar c.H0 (s_normalizes_H0 c h12) ν) = L
      rw [orbit_eq_of_mem c hνs]
    rwa [hEqOrbit] at hσa
  -- each fiber of `θ` is an `s`-pair
  have hfib_eq : ∀ {θ' : ClassFunction (↥c.H)} {μ₀ : ClassFunction (↥c.H0)},
      μ₀ ∈ L → θ μ₀ = θ' →
      L.filter (fun μ => θ μ = θ') = ({μ₀, σ μ₀} : Finset (ClassFunction (↥c.H0))) := by
    intro θ' μ₀ hμ₀ hμ₀θ'
    apply Finset.ext
    intro μ
    constructor
    · intro hμ
      have hμL : μ ∈ L := (Finset.mem_filter.mp hμ).1
      have hμθ : θ μ = θ' := (Finset.mem_filter.mp hμ).2
      have hIrr₀ : IsIrreducibleCharacter μ₀ := orbit_mem_isIrreducible c.H0 c.U hν hμ₀
      have hIrrμ : IsIrreducibleCharacter μ := orbit_mem_isIrreducible c.H0 c.U hν hμL
      rw [Finset.mem_insert, Finset.mem_singleton]
      rcases theta_eq_imp_conj c h12 (H0_index c h12) hIrr₀ hIrrμ
        (hμθ.trans hμ₀θ'.symm).symm with h | h
      · left
        exact h
      · right
        exact (hσ2 μ).symm.trans (congrArg σ h)
    · intro hμ
      rw [Finset.mem_insert, Finset.mem_singleton] at hμ
      rcases hμ with h | h
      · subst μ
        exact Finset.mem_filter.mpr ⟨hμ₀, hμ₀θ'⟩
      · subst h
        have hIrr₀ : IsIrreducibleCharacter μ₀ := orbit_mem_isIrreducible c.H0 c.U hν hμ₀
        exact Finset.mem_filter.mpr
          ⟨hLσ μ₀ hμ₀,
            (inducedFromSub_conjChar_eq c h12 (H0_index c h12) hIrr₀).trans hμ₀θ'⟩
  -- the pair cardinality
  have hpair_card : ∀ μ₀ : ClassFunction (↥c.H0),
      ({μ₀, σ μ₀} : Finset (ClassFunction (↥c.H0))).card =
        if σ μ₀ = μ₀ then 1 else 2 := by
    intro μ₀
    by_cases h : σ μ₀ = μ₀
    · simp [h]
    · have hne : μ₀ ≠ σ μ₀ := by
        intro hEq
        exact h hEq.symm
      rw [Finset.card_insert_of_notMem (by simpa [Finset.mem_singleton] using hne)]
      simp [h]
  -- the fiberwise count
  have hfib : L.card = ∑ θ' ∈ Θ, (L.filter (fun μ => θ μ = θ')).card := by
    exact Finset.card_eq_sum_card_fiberwise (f := θ) (s := L) (t := Θ) (by
      intro μ hμ
      exact thetaOfOrbit_mem c h12 hμ)
  -- the witness section of `θ` on `Θ`
  let w : ClassFunction (↥c.H) → ClassFunction (↥c.H0) := fun θ' =>
    if h : θ' ∈ Θ then Classical.choose (Finset.mem_image.mp h) else ν
  have hw : ∀ {θ' : ClassFunction (↥c.H)}, θ' ∈ Θ → w θ' ∈ L ∧ θ (w θ') = θ' := by
    intro θ' hθ'
    unfold w
    rw [dif_pos hθ']
    exact Classical.choose_spec (Finset.mem_image.mp hθ')
  -- the fiber cards in the sum
  have hsum : (∑ θ' ∈ Θ, (L.filter (fun μ => θ μ = θ')).card) =
      ∑ θ' ∈ Θ, (if σ (w θ') = w θ' then 1 else 2) := by
    apply Finset.sum_congr rfl
    intro θ' hθ'
    rw [hfib_eq (hw hθ').1 (hw hθ').2]
    exact hpair_card (w θ')
  -- the singles (fixed members) are exactly two
  have hfix : (L.filter (fun μ => σ μ = μ)).card = 2 := by
    change (L.filter (fun μ => conjChar c.H0 (s_normalizes_H0 c h12) μ = μ)).card = 2
    exact orbit_s_fixed_card_eq_two_of_invariant c h12 hν hνs
  have hsing : (Θ.filter (fun θ' => σ (w θ') = w θ')).card = 2 := by
    calc
      (Θ.filter (fun θ' => σ (w θ') = w θ')).card
          = (L.filter (fun μ => σ μ = μ)).card := by
            symm
            exact Finset.card_bij
              (fun μ hμ => θ μ)
              (by
                intro μ hμ
                have hμL : μ ∈ L := (Finset.mem_filter.mp hμ).1
                have hμs : σ μ = μ := (Finset.mem_filter.mp hμ).2
                have hθμΘ : θ μ ∈ Θ := thetaOfOrbit_mem c h12 hμL
                have hw_eq : w (θ μ) = μ := by
                  have hw' : w (θ μ) ∈ L ∧ θ (w (θ μ)) = θ μ := hw hθμΘ
                  have hfib' : L.filter (fun μ' => θ μ' = θ μ) =
                      ({μ, σ μ} : Finset (ClassFunction (↥c.H0))) :=
                    hfib_eq hμL rfl
                  have hwfib : w (θ μ) ∈ L.filter (fun μ' => θ μ' = θ μ) :=
                    Finset.mem_filter.mpr ⟨hw'.1, hw'.2⟩
                  rw [hfib'] at hwfib
                  rw [Finset.mem_insert, Finset.mem_singleton] at hwfib
                  rcases hwfib with h | h
                  · exact h
                  · exact h.trans hμs
                exact Finset.mem_filter.mpr ⟨hθμΘ, by rw [hw_eq]; exact hμs⟩)
              (by
                intro a ha b hb hEq
                have hIrr_a : IsIrreducibleCharacter a :=
                  orbit_mem_isIrreducible c.H0 c.U hν (Finset.mem_filter.mp ha).1
                have hIrr_b : IsIrreducibleCharacter b :=
                  orbit_mem_isIrreducible c.H0 c.U hν (Finset.mem_filter.mp hb).1
                rcases theta_eq_imp_conj c h12 (H0_index c h12) hIrr_a hIrr_b hEq with h | h
                · exact h.symm
                · exact h.symm.trans (Finset.mem_filter.mp hb).2)
              (by
                intro θ' hθ'
                have hθ'Θ : θ' ∈ Θ := (Finset.mem_filter.mp hθ').1
                have hw' : w θ' ∈ L ∧ θ (w θ') = θ' := hw hθ'Θ
                refine ⟨w θ', Finset.mem_filter.mpr ⟨hw'.1, (Finset.mem_filter.mp hθ').2⟩, hw'.2⟩)
      _ = 2 := hfix
  -- `|L| + #singles = 2n`: each fiber has size `1` or `2`, the singletons
  -- are the `s`-fixed members (`hfib_eq` + `hpair_card`)
  have hmain : L.card + (Θ.filter (fun θ' => σ (w θ') = w θ')).card = 2 * Θ.card := by
    rw [hfib, hsum]
    calc
      (∑ θ' ∈ Θ, (if σ (w θ') = w θ' then 1 else 2)) +
            (Θ.filter (fun θ' => σ (w θ') = w θ')).card
        = (∑ θ' ∈ Θ, (if σ (w θ') = w θ' then 1 else 2)) +
            (∑ θ' ∈ Θ, (if σ (w θ') = w θ' then 1 else 0)) := by
          congr 1
          exact (Finset.sum_boole (fun θ' : ClassFunction (↥c.H) => σ (w θ') = w θ') Θ).symm
      _ = (∑ θ' ∈ Θ, ((if σ (w θ') = w θ' then 1 else 2) +
            (if σ (w θ') = w θ' then 1 else 0))) := by
          rw [Finset.sum_add_distrib]
      _ = ∑ θ' ∈ Θ, 2 := by
          apply Finset.sum_congr rfl
          intro θ' hθ'
          by_cases h : σ (w θ') = w θ'
          · simp [h]
          · simp [h]
      _ = 2 * Θ.card := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
          norm_num
  have hfinal : L.card + 2 = 2 * Θ.card := by
    rw [hsing] at hmain
    exact hmain
  -- conclude: `2n = |L| + 2`
  have hfinal' : L.card + 2 = Θ.card * 2 := by
    rw [hfinal]
    rw [mul_comm]
  change Θ.card * 2 = L.card + 2
  exact hfinal'.symm


/-- For an `s`-invariant orbit with `n ≥ 4`: `n ≥ 5` (from `2n = 2^k + 2`,
the `Λ`-orbit cardinality being a power of two). -/
private lemma theta_card_ge_five_of_ge_four (c : Hyp11 G) (h12 : Hyp12 c)
    [Fintype ↥(LambdaHom c.H0 c.U)] {ν : ClassFunction (↥c.H0)}
    (hν : IsIrreducibleCharacter ν)
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν ∈ orbit c.H0 c.U ν)
    (hn4 : 4 ≤ (thetaOfOrbit c h12 (orbit c.H0 c.U ν)).card) :
    5 ≤ (thetaOfOrbit c h12 (orbit c.H0 c.U ν)).card := by
  classical
  let n := (thetaOfOrbit c h12 (orbit c.H0 c.U ν)).card
  rcases orbit_card_is_pow_two c h12 ν with ⟨k, hk⟩
  have h2n : n * 2 = (orbit c.H0 c.U ν).card + 2 := by
    change n * 2 = (orbit c.H0 c.U ν).card + 2
    exact theta_card_mul_two_eq_orbit_card_add_two c h12 hν hνs
  have hpow6 : 6 ≤ 2 ^ k := by
    rw [← hk]
    omega
  have hk3 : 3 ≤ k := by
    by_contra hk3
    have hk2 : k ≤ 2 := by omega
    have hle : 2 ^ k ≤ 4 := by
      exact Nat.pow_le_pow_right (by decide : 0 < 2) hk2
    nlinarith [hpow6, hle]
  have hk8 : 8 ≤ 2 ^ k := by
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hk3
  have hn : 5 ≤ n := by
    nlinarith [h2n, hk, hk8]
  change 5 ≤ (thetaOfOrbit c h12 (orbit c.H0 c.U ν)).card
  exact hn

/-- The reducible members of `Θ` are exactly the images of the `s`-fixed
members: `#reducible = #fixed` (`theta_irreducible_iff`, the Clifford
dichotomy). -/
private lemma theta_reducible_card_eq_s_fixed_card (c : Hyp11 G) (h12 : Hyp12 c)
    [Fintype ↥(LambdaHom c.H0 c.U)] {ν : ClassFunction (↥c.H0)}
    (hν : IsIrreducibleCharacter ν) :
    ((thetaOfOrbit c h12 (orbit c.H0 c.U ν)).filter
        (fun θ' : ClassFunction (↥c.H) => ¬ IsIrreducibleCharacter θ')).card =
      ((orbit c.H0 c.U ν).filter (fun μ =>
        conjChar c.H0 (s_normalizes_H0 c h12) μ = μ)).card := by
  classical
  let L : Finset (ClassFunction (↥c.H0)) := orbit c.H0 c.U ν
  let θ : ClassFunction (↥c.H0) → ClassFunction (↥c.H) :=
    fun μ => inducedFromSub (h12.H0_normal_in_H).1 μ
  let σ : ClassFunction (↥c.H0) → ClassFunction (↥c.H0) :=
    fun μ => conjChar c.H0 (s_normalizes_H0 c h12) μ
  let Θ : Finset (ClassFunction (↥c.H)) := thetaOfOrbit c h12 L
  have hred : ∀ μ ∈ L, IsIrreducibleCharacter (θ μ) ↔ σ μ ≠ μ := by
    intro μ hμL
    exact theta_irreducible_iff c h12 (H0_index c h12)
      (orbit_mem_isIrreducible c.H0 c.U hν hμL)
  change (Θ.filter (fun θ' : ClassFunction (↥c.H) => ¬ IsIrreducibleCharacter θ')).card =
      (L.filter (fun μ => σ μ = μ)).card
  symm
  exact Finset.card_bij
    (fun μ hμ => θ μ)
    (by
      intro μ hμ
      have hμL : μ ∈ L := (Finset.mem_filter.mp hμ).1
      have hμs : σ μ = μ := (Finset.mem_filter.mp hμ).2
      have hθμΘ : θ μ ∈ Θ := thetaOfOrbit_mem c h12 hμL
      exact Finset.mem_filter.mpr ⟨hθμΘ, by
        rw [hred μ hμL]
        simp [hμs]⟩)
    (by
      intro a ha b hb hEq
      have hIrr_a : IsIrreducibleCharacter a :=
        orbit_mem_isIrreducible c.H0 c.U hν (Finset.mem_filter.mp ha).1
      have hIrr_b : IsIrreducibleCharacter b :=
        orbit_mem_isIrreducible c.H0 c.U hν (Finset.mem_filter.mp hb).1
      have hμs_b : σ b = b := (Finset.mem_filter.mp hb).2
      rcases theta_eq_imp_conj c h12 (H0_index c h12) hIrr_a hIrr_b hEq with h | h
      · exact h.symm
      · exact h.symm.trans hμs_b)
    (by
      intro θ' hθ'
      have hθ'Θ : θ' ∈ Θ := (Finset.mem_filter.mp hθ').1
      have hθ'red : ¬ IsIrreducibleCharacter θ' := (Finset.mem_filter.mp hθ').2
      rcases (Finset.mem_image.mp hθ'Θ) with ⟨μ, hμL, hθμ⟩
      have hμs : σ μ = μ := by
        by_contra hne
        apply hθ'red
        rw [← hθμ]
        exact (hred μ hμL).2 hne
      refine ⟨μ, Finset.mem_filter.mpr ⟨hμL, hμs⟩, hθμ⟩)

/-- `(δ₁*, δ₂*)_G = (δ₁^H, δ₂^H)_H` for orbit differences (Brauer–Suzuki,
Lemma 1.3, with the `T`-support from the `U`-agreement of orbit members). -/
private lemma delta_pair_scalar (c : Hyp11 G) (h12 : Hyp12 c)
    {ν₁ ν₂ μ₁ μ₂ : ClassFunction (↥c.H0)}
    (hν₁ : IsIrreducibleCharacter ν₁) (hν₂ : IsIrreducibleCharacter ν₂)
    (hμ₁L : μ₁ ∈ orbit c.H0 c.U ν₁) (hμ₂L : μ₂ ∈ orbit c.H0 c.U ν₂) :
    scalarProduct G (inducedClassFunction c.H0 (μ₁ - ν₁))
        (inducedClassFunction c.H0 (μ₂ - ν₂)) =
      scalarProduct (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 μ₁ -
          inducedFromSub (h12.H0_normal_in_H).1 ν₁)
        (inducedFromSub (h12.H0_normal_in_H).1 μ₂ -
          inducedFromSub (h12.H0_normal_in_H).1 ν₂) := by
  classical
  have hcf₁ : IsClassFunction (μ₁ - ν₁) := by
    intro x g
    have hμx := isCharacter_isClassFunction (isCharacter_of_isIrreducibleCharacter hν₁) x g
    have hνx := isCharacter_isClassFunction
      (isCharacter_of_isIrreducibleCharacter (orbit_mem_isIrreducible c.H0 c.U hν₁ hμ₁L)) x g
    simp [hμx, hνx]
  have hcf₂ : IsClassFunction (μ₂ - ν₂) := by
    intro x g
    have hμx := isCharacter_isClassFunction (isCharacter_of_isIrreducibleCharacter hν₂) x g
    have hνx := isCharacter_isClassFunction
      (isCharacter_of_isIrreducibleCharacter (orbit_mem_isIrreducible c.H0 c.U hν₂ hμ₂L)) x g
    simp [hμx, hνx]
  have h1 := lemma_1_3 c h12 (δ1 := μ₁ - ν₁) (δ2 := μ₂ - ν₂) hcf₁ hcf₂
    (delta_supported_on_T c hμ₁L) (delta_supported_on_T c hμ₂L)
  rw [h1.1]
  rw [inducedFromSub_sub c h12 ν₁ μ₁, inducedFromSub_sub c h12 ν₂ μ₂]

/-- `star (φ,ψ) = (ψ,φ)` for the complex inner product. -/
private lemma scalarProduct_star_comm {G : Type u} [Group G] [Fintype G]
    (φ ψ : ClassFunction G) :
    star (scalarProduct G φ ψ) = scalarProduct G ψ φ := by
  classical
  unfold scalarProduct
  simp [map_sum, map_mul, map_star, mul_comm, mul_left_comm, mul_assoc]

private lemma delta_norm (c : Hyp11 G) (h12 : Hyp12 c)
    (hH0index : (c.H0.subgroupOf c.H).index = 2)
    {ν₁ ν₂ : ClassFunction (↥c.H0)}
    (hν₁ : IsIrreducibleCharacter ν₁) (hν₂ : IsIrreducibleCharacter ν₂)
    (hν₁L : ν₁ ∈ orbit c.H0 c.U ν₂)
    (hne : ν₁ ≠ ν₂) (hnes : conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ≠ ν₂) :
    normSq G (inducedClassFunction c.H0 (ν₁ - ν₂)) =
      normSq (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν₁) +
        normSq (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν₂) := by
  classical
  have hs_inv : ∀ x : ↥c.H0, c.s⁻¹ * (x : G) * c.s ∈ c.H0 := by
    intro x
    simpa using (h12.H0_normal_in_H).2 c.s⁻¹ (c.H.inv_mem (s_mem_H c)) (x : G) x.2
  have hν₁s : IsIrreducibleCharacter (conjChar c.H0 (s_normalizes_H0 c h12) ν₁) :=
    isIrreducibleCharacter_conjChar c.H0 (s_normalizes_H0 c h12) hs_inv hν₁
  have hν₂s : IsIrreducibleCharacter (conjChar c.H0 (s_normalizes_H0 c h12) ν₂) :=
    isIrreducibleCharacter_conjChar c.H0 (s_normalizes_H0 c h12) hs_inv hν₂
  have hne1 : ν₁ ≠ conjChar c.H0 (s_normalizes_H0 c h12) ν₂ := by
    intro h1
    apply hnes
    have hc := congrArg (conjChar c.H0 (s_normalizes_H0 c h12)) h1
    rw [conjChar_conjChar c h12 ν₂] at hc
    exact hc
  have hne2 : conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ≠
      conjChar c.H0 (s_normalizes_H0 c h12) ν₂ := by
    intro h2
    apply hne
    have hc := congrArg (conjChar c.H0 (s_normalizes_H0 c h12)) h2
    rw [conjChar_conjChar c h12 ν₁] at hc
    rw [conjChar_conjChar c h12 ν₂] at hc
    exact hc
  have h1 := delta_pair_scalar c h12 hν₂ hν₂ hν₁L hν₁L
  have hp := theta_pair_scalar_H' c h12 hH0index hν₁ hν₂
  have hsp : scalarProduct (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν₁)
      (inducedFromSub (h12.H0_normal_in_H).1 ν₂) = 0 := by
    rw [hp]
    have s1 : scalarProduct (↥c.H0) ν₁ ν₂ = 0 := by
      rw [scalarProduct_irr_ite hν₁ hν₂]
      by_cases hEq : ν₁ = ν₂
      · exact False.elim (hne hEq)
      · simp [hEq]
    have s2 : scalarProduct (↥c.H0) ν₁ (conjChar c.H0 (s_normalizes_H0 c h12) ν₂) = 0 := by
      rw [scalarProduct_irr_ite hν₁ hν₂s]
      by_cases hEq : ν₁ = conjChar c.H0 (s_normalizes_H0 c h12) ν₂
      · exact False.elim (hne1 hEq)
      · simp [hEq]
    have s3 : scalarProduct (↥c.H0) (conjChar c.H0 (s_normalizes_H0 c h12) ν₁) ν₂ = 0 := by
      rw [scalarProduct_irr_ite hν₁s hν₂]
      by_cases hEq : conjChar c.H0 (s_normalizes_H0 c h12) ν₁ = ν₂
      · exact False.elim (hnes hEq)
      · simp [hEq]
    have s4 : scalarProduct (↥c.H0) (conjChar c.H0 (s_normalizes_H0 c h12) ν₁)
        (conjChar c.H0 (s_normalizes_H0 c h12) ν₂) = 0 := by
      rw [scalarProduct_irr_ite hν₁s hν₂s]
      by_cases hEq : conjChar c.H0 (s_normalizes_H0 c h12) ν₁ =
          conjChar c.H0 (s_normalizes_H0 c h12) ν₂
      · exact False.elim (hne2 hEq)
      · simp [hEq]
    simp [s1, s2, s3, s4]
  have hsp' : scalarProduct (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν₂)
      (inducedFromSub (h12.H0_normal_in_H).1 ν₁) = 0 := by
    rw [← scalarProduct_star_comm
      (inducedFromSub (h12.H0_normal_in_H).1 ν₁) (inducedFromSub (h12.H0_normal_in_H).1 ν₂)]
    rw [hsp]
    simp
  calc
    normSq G (inducedClassFunction c.H0 (ν₁ - ν₂))
        = scalarProduct (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν₁ -
            inducedFromSub (h12.H0_normal_in_H).1 ν₂)
          (inducedFromSub (h12.H0_normal_in_H).1 ν₁ -
            inducedFromSub (h12.H0_normal_in_H).1 ν₂) := by
          simpa [h1]
      _ = normSq (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν₁) +
          normSq (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν₂) := by
          rw [scalarProduct_sub_left, scalarProduct_sub_right, scalarProduct_sub_right]
          simp [normSq, hsp, hsp']

/-- In an `s`-invariant orbit, the `s`-pair cancellation `(σa − a)* = 0`
(`σa ∈ orbit a`, `θ(σa) = θ(a)` via `inducedFromSub_conjChar_eq`). -/
private lemma sigma_pair_star_zero_of_invariant (c : Hyp11 G) (h12 : Hyp12 c)
    (hH0index : (c.H0.subgroupOf c.H).index = 2)
    {ν₀ : ClassFunction (↥c.H0)} (hν₀ : IsIrreducibleCharacter ν₀)
    (h_inv : conjChar c.H0 (s_normalizes_H0 c h12) ν₀ ∈ orbit c.H0 c.U ν₀)
    {a : ClassFunction (↥c.H0)} (ha : a ∈ orbit c.H0 c.U ν₀) :
    inducedClassFunction c.H0 (conjChar c.H0 (s_normalizes_H0 c h12) a - a) = 0 := by
  classical
  have hνirr : ∀ ν ∈ orbit c.H0 c.U ν₀, IsIrreducibleCharacter ν :=
    fun ν hνL => orbit_mem_isIrreducible c.H0 c.U hν₀ hνL
  have hσa : conjChar c.H0 (s_normalizes_H0 c h12) a ∈ orbit c.H0 c.U a := by
    rw [orbit_eq_of_mem c ha]
    exact orbit_s_closed_of_invariant c h12 h_inv ha
  have hnorm : normSq G (inducedClassFunction c.H0 (conjChar c.H0 (s_normalizes_H0 c h12) a - a)) = 0 := by
    have hsp := delta_pair_scalar c h12 (ν₁ := a) (ν₂ := a)
      (μ₁ := conjChar c.H0 (s_normalizes_H0 c h12) a)
      (μ₂ := conjChar c.H0 (s_normalizes_H0 c h12) a)
      (hνirr a ha) (hνirr a ha) hσa hσa
    change scalarProduct G (inducedClassFunction c.H0 (conjChar c.H0 (s_normalizes_H0 c h12) a - a))
        (inducedClassFunction c.H0 (conjChar c.H0 (s_normalizes_H0 c h12) a - a)) = 0
    rw [hsp]
    have hθeq : inducedFromSub (h12.H0_normal_in_H).1 (conjChar c.H0 (s_normalizes_H0 c h12) a) =
        inducedFromSub (h12.H0_normal_in_H).1 a :=
      inducedFromSub_conjChar_eq c h12 hH0index (hνirr a ha)
    rw [hθeq]
    simp [scalarProduct]
  exact (normSq_eq_zero_iff (inducedClassFunction c.H0 (conjChar c.H0 (s_normalizes_H0 c h12) a - a))).1 hnorm



/-! ## The common constituent, the per-orbit lift, and the assembly -/

/-- A character is a generalized character. -/
private lemma isGeneralizedCharacter_of_isCharacter {G : Type u} [Group G]
    {φ : ClassFunction G} (hφ : IsCharacter φ) : IsGeneralizedCharacter φ := by
  refine ⟨φ, 0, hφ, isCharacter_zero, ?_⟩
  simp

/-- Two `{0, ±1}`-valued pairings with signed sum `1` have an index with
matching sign and value: from `m(i₀)·a(i₀) + m(i₁)·a(i₁) = 1` with
`m, a` taking values in `{0, ±1}`, some `i` has `m i = a i = 1` or
`m i = a i = -1`. -/
private lemma signed_pair_sum_one {α : Type*} (i₀ i₁ : α) (m : α → ℤ) (a : α → ℂ)
    (hm₀ : m i₀ = 1 ∨ m i₀ = -1) (hm₁ : m i₁ = 1 ∨ m i₁ = -1)
    (ha₀ : a i₀ = 1 ∨ a i₀ = 0 ∨ a i₀ = -1) (ha₁ : a i₁ = 1 ∨ a i₁ = 0 ∨ a i₁ = -1)
    (h : (m i₀ : ℂ) * a i₀ + (m i₁ : ℂ) * a i₁ = 1) :
    ∃ i, (i = i₀ ∨ i = i₁) ∧
      (((m i : ℂ) = 1 ∧ a i = 1) ∨ ((m i : ℂ) = -1 ∧ a i = -1)) := by
  classical
  rcases hm₀ with hm₀ | hm₀ <;> rcases hm₁ with hm₁ | hm₁ <;>
    rcases ha₀ with ha₀ | ha₀ | ha₀ <;> rcases ha₁ with ha₁ | ha₁ | ha₁
  all_goals
    try norm_num [hm₀, hm₁, ha₀, ha₁] at h
    try
      first
      | exact ⟨i₀, Or.inl rfl, Or.inl ⟨by rw [hm₀]; norm_num, ha₀⟩⟩
      | exact ⟨i₀, Or.inl rfl, Or.inr ⟨by rw [hm₀]; norm_num, ha₀⟩⟩
      | exact ⟨i₁, Or.inr rfl, Or.inl ⟨by rw [hm₁]; norm_num, ha₁⟩⟩
      | exact ⟨i₁, Or.inr rfl, Or.inr ⟨by rw [hm₁]; norm_num, ha₁⟩⟩

/-- The common constituent `χ₂₃`: `(δ₂,δ₃)_G = 1` with `|δ₂| = |δ₃| = 2` gives a
signed irreducible `χ` with `(χ,δ₂) = (χ,δ₃) = 1` (Remark 1.5's input for
`θ̃₁ := χ₂₃`; the signed form is needed: `δ₂ = χ₁−χ₂`, `δ₃ = χ₃−χ₂` has
`−χ₂` as its common constituent). The extraction is a pure integer argument
from the decompositions (`Σmᵢ² = 2` gives a two-element support with
multiplicities `±1`; `aᵢ := (χs₂ i, δ₃) ∈ {0, ±1}` via the pairing with
`δ₃`'s constituents; `signed_pair_sum_one` extracts the matching index). -/
private lemma exists_common_constituent_self (c : Hyp11 G) (h12 : Hyp12 c)
    {δ₂ δ₃ : ClassFunction G} (hδ₂ : IsGeneralizedCharacter δ₂)
    (hδ₃ : IsGeneralizedCharacter δ₃) (hn₂ : normSq G δ₂ = 2)
    (hn₃ : normSq G δ₃ = 2) (hpair : scalarProduct G δ₂ δ₃ = 1) :
    ∃ χ : ClassFunction G,
      (IsIrreducibleCharacter χ ∨ IsIrreducibleCharacter (-χ)) ∧
      scalarProduct G χ δ₂ = 1 ∧ scalarProduct G χ δ₃ = 1 := by
  classical
  rcases char_decomp_generalized hδ₂ with ⟨ι₂, _, χs₂, ms₂, hirr₂, hdist₂, hδ₂sum⟩
  rcases char_decomp_generalized hδ₃ with ⟨ι₃, _, χs₃, ms₃, hirr₃, hdist₃, hδ₃sum⟩
  let a : ι₂ → ℂ := fun i => scalarProduct G (χs₂ i) δ₃
  have hnorm₂ : (∑ i, ((ms₂ i : ℤ) : ℂ)^2) = (2 : ℂ) := by
    rw [← decomp_scalarProduct hirr₂ hdist₂]
    rw [← hδ₂sum]
    simpa [normSq] using hn₂
  have hnorm₃ : (∑ j, ((ms₃ j : ℤ) : ℂ)^2) = (2 : ℂ) := by
    rw [← decomp_scalarProduct hirr₃ hdist₃]
    rw [← hδ₃sum]
    simpa [normSq] using hn₃
  have hmem₂ : ∀ i, ms₂ i = 0 ∨ ms₂ i = 1 ∨ ms₂ i = -1 :=
    int_sq_sum_mem (k := 2) (by norm_num) hnorm₂
  have hmem₃ : ∀ j, ms₃ j = 0 ∨ ms₃ j = 1 ∨ ms₃ j = -1 :=
    int_sq_sum_mem (k := 2) (by norm_num) hnorm₃
  let S₂ : Finset ι₂ := Finset.univ.filter (fun i => ms₂ i ≠ 0)
  have hS₂eq : (∑ i : ι₂, ((ms₂ i : ℤ) : ℂ)^2) =
      (∑ i : ι₂, (if ms₂ i ≠ 0 then (1 : ℂ) else 0)) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    by_cases h : ms₂ i = 0
    · simp [h]
    · rcases hmem₂ i with h0 | h1 | hneg1
      · contradiction
      · simp [h1]
      · simp [hneg1]
  have hcard₂ : S₂.card = 2 := by
    have h' : (∑ i : ι₂, (if ms₂ i ≠ 0 then (1 : ℂ) else 0)) = (2 : ℂ) := by
      rw [← hS₂eq, hnorm₂]
    have h'' : (∑ i : ι₂, (if ms₂ i ≠ 0 then (1 : ℂ) else 0)) = (S₂.card : ℂ) := by
      unfold S₂
      rw [Finset.sum_boole]
    exact_mod_cast (h''.symm.trans h')
  rcases Finset.card_eq_two.mp hcard₂ with ⟨i₀, i₁, hi01, hS₂m⟩
  have hmi₀S : i₀ ∈ S₂ := by
    rw [hS₂m]
    simp
  have hmi₁S : i₁ ∈ S₂ := by
    rw [hS₂m]
    simp
  have hmi₀ : ms₂ i₀ = 1 ∨ ms₂ i₀ = -1 := by
    rcases hmem₂ i₀ with h0 | h1 | hneg1
    · exfalso
      exact (Finset.mem_filter.mp hmi₀S).2 h0
    · exact Or.inl h1
    · exact Or.inr hneg1
  have hmi₁ : ms₂ i₁ = 1 ∨ ms₂ i₁ = -1 := by
    rcases hmem₂ i₁ with h0 | h1 | hneg1
    · exfalso
      exact (Finset.mem_filter.mp hmi₁S).2 h0
    · exact Or.inl h1
    · exact Or.inr hneg1
  have hzero₂ : ∀ i, i ≠ i₀ → i ≠ i₁ → ms₂ i = 0 := by
    intro i hi0 hi1
    by_contra h
    have hiS : i ∈ S₂ := Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩
    rw [hS₂m] at hiS
    simp [hi0, hi1] at hiS
  -- `aᵢ ∈ {0, ±1}`: pairings with the constituents of `δ₃`
  have hinner : ∀ i j, scalarProduct G (χs₂ i) (χs₃ j) = 0 ∨
      scalarProduct G (χs₂ i) (χs₃ j) = 1 := by
    intro i j
    by_cases h : χs₂ i = χs₃ j
    · right
      rw [h]
      exact scalarProduct_irreducible_self (hirr₃ j)
    · left
      exact scalarProduct_irreducible_orthogonal (hirr₂ i) (hirr₃ j) h
  have ha : ∀ i, a i = 1 ∨ a i = 0 ∨ a i = -1 := by
    intro i
    have haexp : a i = ∑ j : ι₃, (ms₃ j : ℂ) * scalarProduct G (χs₂ i) (χs₃ j) := by
      unfold a
      rw [hδ₃sum]
      rw [scalarProduct_sum_right]
      refine Finset.sum_congr rfl ?_
      intro j hj
      rw [scalarProduct_smul_right]
      simp [star_intCast]
      ring
    by_cases hnone : ∀ j, scalarProduct G (χs₂ i) (χs₃ j) ≠ 1
    · right
      left
      rw [haexp]
      refine Finset.sum_eq_zero ?_
      intro j hj
      rcases hinner i j with h | h
      · simp [h]
      · exfalso
        exact hnone j h
    · rcases not_forall.mp hnone with ⟨j₀, hj₀⟩
      have hj₀' : scalarProduct G (χs₂ i) (χs₃ j₀) = 1 := by
        rcases hinner i j₀ with h | h
        · exfalso
          exact hj₀ (by rw [h]; norm_num)
        · exact h
      have hsum : (∑ j : ι₃, (ms₃ j : ℂ) * scalarProduct G (χs₂ i) (χs₃ j)) =
          (ms₃ j₀ : ℂ) := by
        rw [Finset.sum_eq_single j₀]
        · rw [hj₀']
          simp
        · intro j hj jne
          have hin : scalarProduct G (χs₂ i) (χs₃ j) = 0 := by
            rcases hinner i j with h | h
            · exact h
            · exfalso
              have heq₁ : χs₃ j = χs₂ i := by
                by_cases hEq : χs₂ i = χs₃ j
                · exact hEq.symm
                · exfalso
                  have h0 : scalarProduct G (χs₂ i) (χs₃ j) = 0 :=
                    scalarProduct_irreducible_orthogonal (hirr₂ i) (hirr₃ j) hEq
                  rw [h0] at h
                  norm_num at h
              have heq₂ : χs₂ i = χs₃ j₀ := by
                by_cases hEq : χs₂ i = χs₃ j₀
                · exact hEq
                · exfalso
                  have h0 : scalarProduct G (χs₂ i) (χs₃ j₀) = 0 :=
                    scalarProduct_irreducible_orthogonal (hirr₂ i) (hirr₃ j₀) hEq
                  rw [h0] at hj₀'
                  norm_num at hj₀'
              exact (hdist₃ j j₀ jne) (heq₁.trans heq₂)
          simp [hin]
        · intro hnot
          exact (hnot (Finset.mem_univ j₀)).elim
      rw [haexp, hsum]
      rcases hmem₃ j₀ with h0 | h1 | hneg1
      · right
        left
        rw [h0]
        norm_num
      · left
        rw [h1]
        norm_num
      · right
        right
        rw [hneg1]
        norm_num
  -- the pairing `(δ₂,δ₃) = 1` in terms of the `aᵢ`
  have hpair' : (∑ i : ι₂, (ms₂ i : ℂ) * a i) = 1 := by
    rw [hδ₂sum] at hpair
    rw [scalarProduct_sum_left] at hpair
    have hterm : ∀ i, scalarProduct G ((ms₂ i : ℂ) • χs₂ i) δ₃ = (ms₂ i : ℂ) * a i := by
      intro i
      unfold a
      rw [scalarProduct_smul_left]
    rwa [show (∑ i, scalarProduct G ((ms₂ i : ℂ) • χs₂ i) δ₃) = ∑ i, (ms₂ i : ℂ) * a i from
      Finset.sum_congr rfl (by intro i hi; exact hterm i)] at hpair
  -- only the two support indices contribute
  have hpair2 : (ms₂ i₀ : ℂ) * a i₀ + (ms₂ i₁ : ℂ) * a i₁ = 1 := by
    have hrest : (∑ i ∈ (Finset.univ \ ({i₀, i₁} : Finset ι₂)), (ms₂ i : ℂ) * a i) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro i hi
      simp at hi
      rcases hi with ⟨hi0, hi1⟩
      simp [hzero₂ i hi0 hi1]
    have hsum : (∑ i : ι₂, (ms₂ i : ℂ) * a i) = (ms₂ i₀ : ℂ) * a i₀ + (ms₂ i₁ : ℂ) * a i₁ := by
      rw [← Finset.sum_sdiff (by simp : ({i₀, i₁} : Finset ι₂) ⊆ Finset.univ)]
      rw [hrest, zero_add]
      simp [hi01]
    exact hsum.symm.trans hpair'
  -- extract the matching index
  have hgood := signed_pair_sum_one i₀ i₁ ms₂ a hmi₀ hmi₁ (ha i₀) (ha i₁) hpair2
  rcases hgood with ⟨i, _hi, hsign⟩
  have hδ₂i : scalarProduct G (χs₂ i) δ₂ = (ms₂ i : ℂ) := by
    rw [hδ₂sum]
    rw [scalarProduct_sum_right]
    rw [Finset.sum_eq_single i]
    · rw [scalarProduct_smul_right]
      rw [scalarProduct_irreducible_self (hirr₂ i)]
      simp
    · intro j hj jne
      rw [scalarProduct_smul_right]
      have hsp : scalarProduct G (χs₂ i) (χs₂ j) = 0 :=
        scalarProduct_irreducible_orthogonal (hirr₂ i) (hirr₂ j) (hdist₂ i j jne.symm)
      simp [hsp, star_intCast]
    · intro hnot
      exact (hnot (Finset.mem_univ i)).elim
  rcases hsign with ⟨hm, ha⟩ | ⟨hm, ha⟩
  · refine ⟨χs₂ i, Or.inl (hirr₂ i), ?_, ?_⟩
    · rw [hδ₂i, hm]
    · unfold a at ha
      exact ha
  · refine ⟨-χs₂ i, Or.inr (by simpa using hirr₂ i), ?_, ?_⟩
    · rw [scalarProduct_neg_left, hδ₂i, hm]
      norm_num
    · unfold a at ha
      rw [scalarProduct_neg_left, ha]
      norm_num

/-- The `k = 3` analogue of `int_sq_sum_mem`: a sum of squares of integers
equal to `3` forces each integer to be `0`, `1`, or `-1` (the bound `k ≤ 2`
in `int_sq_sum_mem` is too strong here). -/
private lemma int_sq_sum_mem_three {ι : Type*} [Fintype ι] {m : ι → ℤ}
    (h : (∑ i, ((m i : ℤ) : ℂ)^2) = (3 : ℂ)) :
    ∀ i, m i = 0 ∨ m i = 1 ∨ m i = -1 := by
  intro i
  have hb : (m i : ℤ)^2 ≤ (3 : ℤ) := int_sq_sum_bound h i
  have hz : ((m i).natAbs : ℤ)^2 ≤ (3 : ℤ) := by
    simpa [Int.natAbs_mul_self] using hb
  have hz' : (m i).natAbs ^ 2 ≤ 3 := by exact_mod_cast hz
  have hnat : (m i).natAbs ≤ 1 := by
    by_contra hnot
    have hge : 2 ≤ (m i).natAbs := by omega
    have hsq : 4 ≤ (m i).natAbs ^ 2 := by
      simpa [pow_two] using (Nat.mul_le_mul hge hge)
    nlinarith
  have hcases : (m i).natAbs = 0 ∨ (m i).natAbs = 1 := by omega
  rcases hcases with h0 | h1
  · left
    omega
  · right
    omega

/-- `(m i) * a i = 1` with `m i = ±1` gives the matching sign pair at `i`. -/
private lemma match_of_signed_product_one {α : Type*} (i : α) (m : α → ℤ) (a : α → ℂ)
    (hm : m i = 1 ∨ m i = -1) (h : (m i : ℂ) * a i = 1) :
    ((m i : ℂ) = 1 ∧ a i = 1) ∨ ((m i : ℂ) = -1 ∧ a i = -1) := by
  rcases hm with hm | hm
  · left
    constructor
    · rw [hm]
      norm_num
    · rw [hm] at h
      norm_num at h
      exact h
  · right
    constructor
    · rw [hm]
      norm_num
    · rw [hm] at h
      norm_num at h
      simpa using congrArg Neg.neg h

/-- The three-support analogue of `signed_pair_sum_one` (the `|L| = 4`
invariant orbit: `|δᵢ*|² = 1 + 2 = 3`): three signed terms `(m i)·a i` with
`a i ∈ {0, ±1}` summing to `1` give an index with the matching signs
`(m i = 1 ∧ a i = 1)` or `(m i = -1 ∧ a i = -1)`. -/
private lemma signed_triple_sum_one {α : Type*} (i₀ i₁ i₂ : α) (m : α → ℤ) (a : α → ℂ)
    (hm₀ : m i₀ = 1 ∨ m i₀ = -1) (hm₁ : m i₁ = 1 ∨ m i₁ = -1) (hm₂ : m i₂ = 1 ∨ m i₂ = -1)
    (ha₀ : a i₀ = 1 ∨ a i₀ = 0 ∨ a i₀ = -1) (ha₁ : a i₁ = 1 ∨ a i₁ = 0 ∨ a i₁ = -1)
    (ha₂ : a i₂ = 1 ∨ a i₂ = 0 ∨ a i₂ = -1)
    (h : (m i₀ : ℂ) * a i₀ + (m i₁ : ℂ) * a i₁ + (m i₂ : ℂ) * a i₂ = 1) :
    ∃ i, (i = i₀ ∨ i = i₁ ∨ i = i₂) ∧
      (((m i : ℂ) = 1 ∧ a i = 1) ∨ ((m i : ℂ) = -1 ∧ a i = -1)) := by
  classical
  have ht₀ : (m i₀ : ℂ) * a i₀ = 1 ∨ (m i₀ : ℂ) * a i₀ = 0 ∨ (m i₀ : ℂ) * a i₀ = -1 := by
    rcases hm₀ with hm₀ | hm₀ <;> rcases ha₀ with ha₀ | ha₀ | ha₀ <;> norm_num [hm₀, ha₀]
  have ht₁ : (m i₁ : ℂ) * a i₁ = 1 ∨ (m i₁ : ℂ) * a i₁ = 0 ∨ (m i₁ : ℂ) * a i₁ = -1 := by
    rcases hm₁ with hm₁ | hm₁ <;> rcases ha₁ with ha₁ | ha₁ | ha₁ <;> norm_num [hm₁, ha₁]
  have ht₂ : (m i₂ : ℂ) * a i₂ = 1 ∨ (m i₂ : ℂ) * a i₂ = 0 ∨ (m i₂ : ℂ) * a i₂ = -1 := by
    rcases hm₂ with hm₂ | hm₂ <;> rcases ha₂ with ha₂ | ha₂ | ha₂ <;> norm_num [hm₂, ha₂]
  by_cases ht₀₁ : (m i₀ : ℂ) * a i₀ = 1
  · refine ⟨i₀, Or.inl rfl, match_of_signed_product_one i₀ m a hm₀ ht₀₁⟩
  · by_cases ht₁₁ : (m i₁ : ℂ) * a i₁ = 1
    · refine ⟨i₁, Or.inr (Or.inl rfl), match_of_signed_product_one i₁ m a hm₁ ht₁₁⟩
    · by_cases ht₂₁ : (m i₂ : ℂ) * a i₂ = 1
      · refine ⟨i₂, Or.inr (Or.inr rfl), match_of_signed_product_one i₂ m a hm₂ ht₂₁⟩
      · rcases ht₀ with ht₀ | ht₀ | ht₀ <;> rcases ht₁ with ht₁ | ht₁ | ht₁ <;>
          rcases ht₂ with ht₂ | ht₂ | ht₂
        all_goals
          try norm_num [ht₀, ht₁, ht₂] at h
          try contradiction

/-- The common constituent `χ₂₃` for the norm-3 case (the `|L| = 4` invariant
orbit: `|δᵢ*|² = |θ₁| + |θᵢ| = 1 + 2 = 3`): `(δ₂,δ₃)_G = 1` with
`|δ₂| = |δ₃| = 3` gives a signed irreducible `χ` with `(χ,δ₂) = (χ,δ₃) = 1`.
The extraction is the norm-2 argument with the three-element support
(`Σmᵢ² = 3`; `signed_triple_sum_one` extracts the matching index). -/
private lemma exists_common_constituent_self_norm3 (c : Hyp11 G) (h12 : Hyp12 c)
    {δ₂ δ₃ : ClassFunction G} (hδ₂ : IsGeneralizedCharacter δ₂)
    (hδ₃ : IsGeneralizedCharacter δ₃) (hn₂ : normSq G δ₂ = 3)
    (hn₃ : normSq G δ₃ = 3) (hpair : scalarProduct G δ₂ δ₃ = 1) :
    ∃ χ : ClassFunction G,
      (IsIrreducibleCharacter χ ∨ IsIrreducibleCharacter (-χ)) ∧
      scalarProduct G χ δ₂ = 1 ∧ scalarProduct G χ δ₃ = 1 := by
  classical
  rcases char_decomp_generalized hδ₂ with ⟨ι₂, _, χs₂, ms₂, hirr₂, hdist₂, hδ₂sum⟩
  rcases char_decomp_generalized hδ₃ with ⟨ι₃, _, χs₃, ms₃, hirr₃, hdist₃, hδ₃sum⟩
  let a : ι₂ → ℂ := fun i => scalarProduct G (χs₂ i) δ₃
  have hnorm₂ : (∑ i, ((ms₂ i : ℤ) : ℂ)^2) = (3 : ℂ) := by
    rw [← decomp_scalarProduct hirr₂ hdist₂]
    rw [← hδ₂sum]
    simpa [normSq] using hn₂
  have hnorm₃ : (∑ j, ((ms₃ j : ℤ) : ℂ)^2) = (3 : ℂ) := by
    rw [← decomp_scalarProduct hirr₃ hdist₃]
    rw [← hδ₃sum]
    simpa [normSq] using hn₃
  have hmem₂ : ∀ i, ms₂ i = 0 ∨ ms₂ i = 1 ∨ ms₂ i = -1 :=
    int_sq_sum_mem_three hnorm₂
  have hmem₃ : ∀ j, ms₃ j = 0 ∨ ms₃ j = 1 ∨ ms₃ j = -1 :=
    int_sq_sum_mem_three hnorm₃
  let S₂ : Finset ι₂ := Finset.univ.filter (fun i => ms₂ i ≠ 0)
  have hS₂eq : (∑ i : ι₂, ((ms₂ i : ℤ) : ℂ)^2) =
      (∑ i : ι₂, (if ms₂ i ≠ 0 then (1 : ℂ) else 0)) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    by_cases h : ms₂ i = 0
    · simp [h]
    · rcases hmem₂ i with h0 | h1 | hneg1
      · contradiction
      · simp [h1]
      · simp [hneg1]
  have hcard₂ : S₂.card = 3 := by
    have h' : (∑ i : ι₂, (if ms₂ i ≠ 0 then (1 : ℂ) else 0)) = (3 : ℂ) := by
      rw [← hS₂eq, hnorm₂]
    have h'' : (∑ i : ι₂, (if ms₂ i ≠ 0 then (1 : ℂ) else 0)) = (S₂.card : ℂ) := by
      unfold S₂
      rw [Finset.sum_boole]
    exact_mod_cast (h''.symm.trans h')
  rcases Finset.card_eq_three.mp hcard₂ with ⟨i₀, i₁, i₂, hi01, hi02, hi12, hS₂m⟩
  have hmi₀S : i₀ ∈ S₂ := by
    rw [hS₂m]
    simp
  have hmi₁S : i₁ ∈ S₂ := by
    rw [hS₂m]
    simp
  have hmi₂S : i₂ ∈ S₂ := by
    rw [hS₂m]
    simp
  have hmi₀ : ms₂ i₀ = 1 ∨ ms₂ i₀ = -1 := by
    rcases hmem₂ i₀ with h0 | h1 | hneg1
    · exfalso
      exact (Finset.mem_filter.mp hmi₀S).2 h0
    · exact Or.inl h1
    · exact Or.inr hneg1
  have hmi₁ : ms₂ i₁ = 1 ∨ ms₂ i₁ = -1 := by
    rcases hmem₂ i₁ with h0 | h1 | hneg1
    · exfalso
      exact (Finset.mem_filter.mp hmi₁S).2 h0
    · exact Or.inl h1
    · exact Or.inr hneg1
  have hmi₂ : ms₂ i₂ = 1 ∨ ms₂ i₂ = -1 := by
    rcases hmem₂ i₂ with h0 | h1 | hneg1
    · exfalso
      exact (Finset.mem_filter.mp hmi₂S).2 h0
    · exact Or.inl h1
    · exact Or.inr hneg1
  have hzero₂ : ∀ i, i ≠ i₀ → i ≠ i₁ → i ≠ i₂ → ms₂ i = 0 := by
    intro i hi0 hi1 hi2
    by_contra h
    have hiS : i ∈ S₂ := Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩
    rw [hS₂m] at hiS
    simp [hi0, hi1, hi2] at hiS
  -- `aᵢ ∈ {0, ±1}`: pairings with the constituents of `δ₃`
  have hinner : ∀ i j, scalarProduct G (χs₂ i) (χs₃ j) = 0 ∨
      scalarProduct G (χs₂ i) (χs₃ j) = 1 := by
    intro i j
    by_cases h : χs₂ i = χs₃ j
    · right
      rw [h]
      exact scalarProduct_irreducible_self (hirr₃ j)
    · left
      exact scalarProduct_irreducible_orthogonal (hirr₂ i) (hirr₃ j) h
  have ha : ∀ i, a i = 1 ∨ a i = 0 ∨ a i = -1 := by
    intro i
    have haexp : a i = ∑ j : ι₃, (ms₃ j : ℂ) * scalarProduct G (χs₂ i) (χs₃ j) := by
      unfold a
      rw [hδ₃sum]
      rw [scalarProduct_sum_right]
      refine Finset.sum_congr rfl ?_
      intro j hj
      rw [scalarProduct_smul_right]
      simp [star_intCast]
      ring
    by_cases hnone : ∀ j, scalarProduct G (χs₂ i) (χs₃ j) ≠ 1
    · right
      left
      rw [haexp]
      refine Finset.sum_eq_zero ?_
      intro j hj
      rcases hinner i j with h | h
      · simp [h]
      · exfalso
        exact hnone j h
    · rcases not_forall.mp hnone with ⟨j₀, hj₀⟩
      have hj₀' : scalarProduct G (χs₂ i) (χs₃ j₀) = 1 := by
        rcases hinner i j₀ with h | h
        · exfalso
          exact hj₀ (by rw [h]; norm_num)
        · exact h
      have hsum : (∑ j : ι₃, (ms₃ j : ℂ) * scalarProduct G (χs₂ i) (χs₃ j)) =
          (ms₃ j₀ : ℂ) := by
        rw [Finset.sum_eq_single j₀]
        · rw [hj₀']
          simp
        · intro j hj jne
          have hin : scalarProduct G (χs₂ i) (χs₃ j) = 0 := by
            rcases hinner i j with h | h
            · exact h
            · exfalso
              have heq₁ : χs₃ j = χs₂ i := by
                by_cases hEq : χs₂ i = χs₃ j
                · exact hEq.symm
                · exfalso
                  have h0 : scalarProduct G (χs₂ i) (χs₃ j) = 0 :=
                    scalarProduct_irreducible_orthogonal (hirr₂ i) (hirr₃ j) hEq
                  rw [h0] at h
                  norm_num at h
              have heq₂ : χs₂ i = χs₃ j₀ := by
                by_cases hEq : χs₂ i = χs₃ j₀
                · exact hEq
                · exfalso
                  have h0 : scalarProduct G (χs₂ i) (χs₃ j₀) = 0 :=
                    scalarProduct_irreducible_orthogonal (hirr₂ i) (hirr₃ j₀) hEq
                  rw [h0] at hj₀'
                  norm_num at hj₀'
              exact (hdist₃ j j₀ jne) (heq₁.trans heq₂)
          simp [hin]
        · intro hnot
          exact (hnot (Finset.mem_univ j₀)).elim
      rw [haexp, hsum]
      rcases hmem₃ j₀ with h0 | h1 | hneg1
      · right
        left
        rw [h0]
        norm_num
      · left
        rw [h1]
        norm_num
      · right
        right
        rw [hneg1]
        norm_num
  -- the pairing `(δ₂,δ₃) = 1` in terms of the `aᵢ`
  have hpair' : (∑ i : ι₂, (ms₂ i : ℂ) * a i) = 1 := by
    rw [hδ₂sum] at hpair
    rw [scalarProduct_sum_left] at hpair
    have hterm : ∀ i, scalarProduct G ((ms₂ i : ℂ) • χs₂ i) δ₃ = (ms₂ i : ℂ) * a i := by
      intro i
      unfold a
      rw [scalarProduct_smul_left]
    rwa [show (∑ i, scalarProduct G ((ms₂ i : ℂ) • χs₂ i) δ₃) = ∑ i, (ms₂ i : ℂ) * a i from
      Finset.sum_congr rfl (by intro i hi; exact hterm i)] at hpair
  -- only the three support indices contribute
  have hpair3 : (ms₂ i₀ : ℂ) * a i₀ + (ms₂ i₁ : ℂ) * a i₁ + (ms₂ i₂ : ℂ) * a i₂ = 1 := by
    have hrest : (∑ i ∈ (Finset.univ \ ({i₀, i₁, i₂} : Finset ι₂)), (ms₂ i : ℂ) * a i) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro i hi
      simp at hi
      rcases hi with ⟨hi0, hi1, hi2⟩
      simp [hzero₂ i hi0 hi1 hi2]
    have hsum : (∑ i : ι₂, (ms₂ i : ℂ) * a i) =
        (ms₂ i₀ : ℂ) * a i₀ + (ms₂ i₁ : ℂ) * a i₁ + (ms₂ i₂ : ℂ) * a i₂ := by
      rw [← Finset.sum_sdiff (by simp : ({i₀, i₁, i₂} : Finset ι₂) ⊆ Finset.univ)]
      rw [hrest, zero_add]
      simp [hi01, hi02, hi12]
      ac_rfl
    exact hsum.symm.trans hpair'
  -- extract the matching index
  have hgood := signed_triple_sum_one i₀ i₁ i₂ ms₂ a hmi₀ hmi₁ hmi₂ (ha i₀) (ha i₁) (ha i₂) hpair3
  rcases hgood with ⟨i, _hi, hsign⟩
  have hδ₂i : scalarProduct G (χs₂ i) δ₂ = (ms₂ i : ℂ) := by
    rw [hδ₂sum]
    rw [scalarProduct_sum_right]
    rw [Finset.sum_eq_single i]
    · rw [scalarProduct_smul_right]
      rw [scalarProduct_irreducible_self (hirr₂ i)]
      simp
    · intro j hj jne
      rw [scalarProduct_smul_right]
      have hsp : scalarProduct G (χs₂ i) (χs₂ j) = 0 :=
        scalarProduct_irreducible_orthogonal (hirr₂ i) (hirr₂ j) (hdist₂ i j jne.symm)
      simp [hsp, star_intCast]
    · intro hnot
      exact (hnot (Finset.mem_univ i)).elim
  rcases hsign with ⟨hm, ha⟩ | ⟨hm, ha⟩
  · refine ⟨χs₂ i, Or.inl (hirr₂ i), ?_, ?_⟩
    · rw [hδ₂i, hm]
    · unfold a at ha
      exact ha
  · refine ⟨-χs₂ i, Or.inr (by simpa using hirr₂ i), ?_, ?_⟩
    · rw [scalarProduct_neg_left, hδ₂i, hm]
      norm_num
    · unfold a at ha
      rw [scalarProduct_neg_left, ha]
      norm_num

/-- The signed-pair decomposition of a norm-2 generalized character: the two
irreducible constituents with the four sign patterns (the `n = 2` easy case
of the Coherence construction: `δ₂* = ±χ ± ψ`, and the lift is
`θ̃₁ := χ`, `θ̃₂ := χ − δ₂*` after matching the sign of `(χ, δ₂*)`). -/
public theorem signed_pair_decomp {G : Type u} [Group G] [Fintype G]
    {δ : ClassFunction G} (hδ : IsGeneralizedCharacter δ) (hn : normSq G δ = 2) :
    ∃ χ ψ : ClassFunction G,
      IsIrreducibleCharacter χ ∧ IsIrreducibleCharacter ψ ∧ χ ≠ ψ ∧
        (δ = χ - ψ ∨ δ = χ + ψ ∨ δ = -χ - ψ ∨ δ = -χ + ψ) := by
  classical
  rcases char_decomp_generalized hδ with ⟨ι, _, χs, ms, hirr, hdist, hδsum⟩
  have hnorm : (∑ i, ((ms i : ℤ) : ℂ)^2) = (2 : ℂ) := by
    rw [← decomp_scalarProduct hirr hdist]
    rw [← hδsum]
    simpa [normSq] using hn
  have hmem : ∀ i, ms i = 0 ∨ ms i = 1 ∨ ms i = -1 :=
    int_sq_sum_mem (k := 2) (by norm_num) hnorm
  let S : Finset ι := Finset.univ.filter (fun i => ms i ≠ 0)
  have hSeq : (∑ i : ι, ((ms i : ℤ) : ℂ)^2) =
      (∑ i : ι, (if ms i ≠ 0 then (1 : ℂ) else 0)) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    by_cases h : ms i = 0
    · simp [h]
    · rcases hmem i with h0 | h1 | hneg1
      · contradiction
      · simp [h1]
      · simp [hneg1]
  have hcard : S.card = 2 := by
    have h' : (∑ i : ι, (if ms i ≠ 0 then (1 : ℂ) else 0)) = (2 : ℂ) := by
      rw [← hSeq, hnorm]
    have h'' : (∑ i : ι, (if ms i ≠ 0 then (1 : ℂ) else 0)) = (S.card : ℂ) := by
      unfold S
      rw [Finset.sum_boole]
    exact_mod_cast (h''.symm.trans h')
  rcases Finset.card_eq_two.mp hcard with ⟨i₀, i₁, hi01, hSm⟩
  have hmi₀S : i₀ ∈ S := by
    rw [hSm]
    simp
  have hmi₁S : i₁ ∈ S := by
    rw [hSm]
    simp
  have hmi₀ : ms i₀ = 1 ∨ ms i₀ = -1 := by
    rcases hmem i₀ with h0 | h1 | hneg1
    · exfalso
      exact (Finset.mem_filter.mp hmi₀S).2 h0
    · exact Or.inl h1
    · exact Or.inr hneg1
  have hmi₁ : ms i₁ = 1 ∨ ms i₁ = -1 := by
    rcases hmem i₁ with h0 | h1 | hneg1
    · exfalso
      exact (Finset.mem_filter.mp hmi₁S).2 h0
    · exact Or.inl h1
    · exact Or.inr hneg1
  have hzero : ∀ i, i ≠ i₀ → i ≠ i₁ → ms i = 0 := by
    intro i hi0 hi1
    by_contra h
    have hiS : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩
    rw [hSm] at hiS
    simp [hi0, hi1] at hiS
  -- `δ` is the sum of the two constituents
  have hδtwo : δ = (ms i₀ : ℂ) • χs i₀ + (ms i₁ : ℂ) • χs i₁ := by
    rw [hδsum]
    have hrest : (∑ i ∈ (Finset.univ \ ({i₀, i₁} : Finset ι)), (ms i : ℂ) • χs i) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro i hi
      simp at hi
      rcases hi with ⟨hi0, hi1⟩
      simp [hzero i hi0 hi1]
    have hsum : (∑ i : ι, (ms i : ℂ) • χs i) =
        (ms i₀ : ℂ) • χs i₀ + (ms i₁ : ℂ) • χs i₁ := by
      rw [← Finset.sum_sdiff (by simp : ({i₀, i₁} : Finset ι) ⊆ Finset.univ)]
      rw [hrest, zero_add]
      simp [hi01]
    exact hsum
  rcases hmi₀ with h0 | h0
  · rcases hmi₁ with h1 | h1
    · refine ⟨χs i₀, χs i₁, hirr i₀, hirr i₁, hdist i₀ i₁ hi01, ?_⟩
      right
      left
      rw [hδtwo, h0, h1]
      simp [sub_eq_add_neg]
    · refine ⟨χs i₀, χs i₁, hirr i₀, hirr i₁, hdist i₀ i₁ hi01, ?_⟩
      left
      rw [hδtwo, h0, h1]
      simp [sub_eq_add_neg]
  · rcases hmi₁ with h1 | h1
    · refine ⟨χs i₀, χs i₁, hirr i₀, hirr i₁, hdist i₀ i₁ hi01, ?_⟩
      right
      right
      right
      rw [hδtwo, h0, h1]
      simp [sub_eq_add_neg]
    · refine ⟨χs i₀, χs i₁, hirr i₀, hirr i₁, hdist i₀ i₁ hi01, ?_⟩
      right
      right
      left
      rw [hδtwo, h0, h1]
      simp [sub_eq_add_neg]

/-- A signed irreducible `χ` paired with an irreducible `a` gives a value in
`{-1, 0, 1}`. -/
private lemma scalarProduct_signed_irr_irr_mem {G : Type u} [Group G] [Fintype G]
    {χ a : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ ∨ IsIrreducibleCharacter (-χ))
    (ha : IsIrreducibleCharacter a) :
    scalarProduct G χ a = 1 ∨ scalarProduct G χ a = 0 ∨ scalarProduct G χ a = -1 := by
  rcases hχ with hχ | hχneg
  · rw [scalarProduct_irr_ite hχ ha]
    by_cases h : χ = a
    · simp [h]
    · simp [h]
  · rw [← neg_neg χ, scalarProduct_neg_left]
    rw [scalarProduct_irr_ite hχneg ha]
    by_cases h : -χ = a
    · norm_num [h]
    · norm_num [h]

/-- A signed irreducible `χ` paired with an irreducible `a` with a non-zero
pairing satisfies `a = ±χ`. -/
private lemma signed_irr_irr_eq_of_ne_zero {G : Type u} [Group G] [Fintype G]
    {χ a : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ ∨ IsIrreducibleCharacter (-χ))
    (ha : IsIrreducibleCharacter a) (h : scalarProduct G χ a ≠ 0) :
    a = χ ∨ a = -χ := by
  rcases hχ with hχ | hχneg
  · left
    by_contra hne
    have hχa : χ ≠ a := fun hEq => hne hEq.symm
    rw [scalarProduct_irr_ite hχ ha] at h
    simp [hχa] at h
  · right
    by_contra hne
    have hχa : -χ ≠ a := fun hEq => hne hEq.symm
    have hηa0 : scalarProduct G (-χ) a = 0 := by
      rw [scalarProduct_irr_ite hχneg ha]
      simp [hχa]
    apply h
    rw [← neg_neg χ, scalarProduct_neg_left, hηa0]
    norm_num

/-- A norm-one signed irreducible `χ` paired with a norm-two generalized
character `ψ` gives a value in `{-1, 0, 1}`: the two constituents of `ψ`
(cf. `signed_pair_decomp`) are distinct irreducibles, so at most one of them
is `±χ`, and if both paired non-trivially `ψ` would have norm `0` or `4`.
This is the bound used to derive `(χ₂₃, δⱼ*) = 0` in the undefined case. -/
private lemma scalarProduct_norm_one_signed_norm_two_mem {G : Type u} [Group G]
    [Fintype G]
    {χ ψ : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ ∨ IsIrreducibleCharacter (-χ))
    (hψ : IsGeneralizedCharacter ψ) (hn : normSq G ψ = 2) :
    scalarProduct G χ ψ = 1 ∨ scalarProduct G χ ψ = 0 ∨ scalarProduct G χ ψ = -1 := by
  rcases signed_pair_decomp hψ hn with ⟨a, b, ha, hb, hab, hδcase⟩
  have hm1 : scalarProduct G χ a = 1 ∨ scalarProduct G χ a = 0 ∨ scalarProduct G χ a = -1 :=
    scalarProduct_signed_irr_irr_mem hχ ha
  have hm2 : scalarProduct G χ b = 1 ∨ scalarProduct G χ b = 0 ∨ scalarProduct G χ b = -1 :=
    scalarProduct_signed_irr_irr_mem hχ hb
  -- `a` and `b` cannot both pair non-trivially with `χ`: then `a, b = ±χ`
  -- with `a ≠ b`, so `ψ ∈ {0, ±2χ}` of norm `0` or `4`
  have hzeropro : scalarProduct G χ a = 0 ∨ scalarProduct G χ b = 0 := by
    by_contra h
    have hma : scalarProduct G χ a ≠ 0 := by
      intro hz
      exact h (Or.inl hz)
    have hmb : scalarProduct G χ b ≠ 0 := by
      intro hz
      exact h (Or.inr hz)
    have hapm : a = χ ∨ a = -χ := signed_irr_irr_eq_of_ne_zero hχ ha hma
    have hbpm : b = χ ∨ b = -χ := signed_irr_irr_eq_of_ne_zero hχ hb hmb
    have hbna : b = -a := by
      rcases hapm with hap | han
      · rcases hbpm with hbp | hbn
        · exfalso
          exact hab (hap.trans hbp.symm)
        · calc
            b = -χ := hbn
            _ = -a := by rw [hap]
      · rcases hbpm with hbp | hbn
        · calc
            b = χ := hbp
            _ = -a := by rw [han]; simp
        · exfalso
          apply hab
          calc
            a = -χ := han
            _ = b := hbn.symm
    rcases hδcase with hδcase | hδcase | hδcase | hδcase
    · -- `ψ = a - b = a + a`
      rw [hδcase, hbna] at hn
      have haa : a - -a = a + a := by simp
      have hnorm4 : normSq G (a + a) = 4 := by
        unfold normSq
        simp [scalarProduct_add_left, scalarProduct_add_right, scalarProduct_irr_ite ha ha]
        norm_num
      rw [haa, hnorm4] at hn
      norm_num at hn
    · -- `ψ = a + b = 0`
      rw [hδcase, hbna] at hn
      have hzero : a + -a = 0 := by
        ext
        simp [sub_eq_add_neg]
      have h0 : normSq G (0 : ClassFunction G) = 0 := by
        exact (normSq_eq_zero_iff (0 : ClassFunction G)).2 rfl
      rw [hzero, h0] at hn
      norm_num at hn
    · -- `ψ = -a - b = 0`
      rw [hδcase, hbna] at hn
      have hzero : -a - -a = 0 := by
        ext
        simp [sub_eq_add_neg]
      have h0 : normSq G (0 : ClassFunction G) = 0 := by
        exact (normSq_eq_zero_iff (0 : ClassFunction G)).2 rfl
      rw [hzero, h0] at hn
      norm_num at hn
    · -- `ψ = -a + b = -(a + a)`
      rw [hδcase, hbna] at hn
      have hneg : -a + -a = -(a + a) := by
        ext
        simp
      have hn4 : normSq G (-(a + a)) = normSq G (a + a) := by
        unfold normSq
        rw [scalarProduct_neg_left, scalarProduct_neg_right]
        simp
      have hnorm4 : normSq G (a + a) = 4 := by
        unfold normSq
        simp [scalarProduct_add_left, scalarProduct_add_right, scalarProduct_irr_ite ha ha]
        norm_num
      rw [hneg, hn4, hnorm4] at hn
      norm_num at hn
  -- the four sign patterns, with one of the two pairings vanishing
  rcases hδcase with hδcase | hδcase | hδcase | hδcase
  · rw [hδcase]
    rw [scalarProduct_sub_right]
    rcases hzeropro with h0a | h0b
    · rcases hm2 with hb1 | hb0 | hbn1
      · rw [h0a, hb1]
        norm_num
      · rw [h0a, hb0]
        norm_num
      · rw [h0a, hbn1]
        norm_num
    · rcases hm1 with ha1 | ha0 | han1
      · rw [ha1, h0b]
        norm_num
      · rw [ha0, h0b]
        norm_num
      · rw [han1, h0b]
        norm_num
  · rw [hδcase]
    rw [scalarProduct_add_right]
    rcases hzeropro with h0a | h0b
    · rcases hm2 with hb1 | hb0 | hbn1
      · rw [h0a, hb1]
        norm_num
      · rw [h0a, hb0]
        norm_num
      · rw [h0a, hbn1]
        norm_num
    · rcases hm1 with ha1 | ha0 | han1
      · rw [ha1, h0b]
        norm_num
      · rw [ha0, h0b]
        norm_num
      · rw [han1, h0b]
        norm_num
  · rw [hδcase]
    rw [scalarProduct_sub_right, scalarProduct_neg_right]
    rcases hzeropro with h0a | h0b
    · rcases hm2 with hb1 | hb0 | hbn1
      · rw [h0a, hb1]
        norm_num
      · rw [h0a, hb0]
        norm_num
      · rw [h0a, hbn1]
        norm_num
    · rcases hm1 with ha1 | ha0 | han1
      · rw [ha1, h0b]
        norm_num
      · rw [ha0, h0b]
        norm_num
      · rw [han1, h0b]
        norm_num
  · rw [hδcase]
    rw [scalarProduct_add_right, scalarProduct_neg_right]
    rcases hzeropro with h0a | h0b
    · rcases hm2 with hb1 | hb0 | hbn1
      · rw [h0a, hb1]
        norm_num
      · rw [h0a, hb0]
        norm_num
      · rw [h0a, hbn1]
        norm_num
    · rcases hm1 with ha1 | ha0 | han1
      · rw [ha1, h0b]
        norm_num
      · rw [ha0, h0b]
        norm_num
      · rw [han1, h0b]
        norm_num

/-- A signed irreducible paired with a norm-three generalized character has
value in `{-1, 0, 1}`: the norm-three character is a sum of three signed
irreducibles with coefficients `±1`, and a signed irreducible can pair
non-trivially with at most one of them. -/
private lemma scalarProduct_norm_one_signed_norm_three_mem {G : Type u} [Group G]
    [Fintype G]
    {χ ψ : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ ∨ IsIrreducibleCharacter (-χ))
    (hψ : IsGeneralizedCharacter ψ) (hn : normSq G ψ = 3) :
    scalarProduct G χ ψ = 1 ∨ scalarProduct G χ ψ = 0 ∨ scalarProduct G χ ψ = -1 := by
  classical
  rcases char_decomp_generalized hψ with ⟨ι, _, χs, m, hirr, hdist, hψsum⟩
  have hnorm : (∑ i, ((m i : ℤ) : ℂ)^2) = (3 : ℂ) := by
    rw [← decomp_scalarProduct hirr hdist]
    rw [← hψsum]
    simpa [normSq] using hn
  have hmem : ∀ i, m i = 0 ∨ m i = 1 ∨ m i = -1 :=
    int_sq_sum_mem_three hnorm
  have hpair : ∀ i, scalarProduct G χ (χs i) = 1 ∨
      scalarProduct G χ (χs i) = 0 ∨ scalarProduct G χ (χs i) = -1 := by
    intro i
    exact scalarProduct_signed_irr_irr_mem hχ (hirr i)
  have hatmost : ∀ i, scalarProduct G χ (χs i) ≠ 0 →
      ∀ j, j ≠ i → scalarProduct G χ (χs j) = 0 := by
    intro i hi j hji
    have hχi : χs i = χ ∨ χs i = -χ := signed_irr_irr_eq_of_ne_zero hχ (hirr i) hi
    have horth : scalarProduct G (χs j) (χs i) = 0 :=
      scalarProduct_irreducible_orthogonal (hirr j) (hirr i) (hdist j i hji)
    have hstar : ∀ {a b : ClassFunction G},
        scalarProduct G a b = star (scalarProduct G b a) := by
      intro a b
      rw [← scalarProduct_star_comm b a]
    rcases hχi with hχi | hχi
    · rw [hχi] at horth
      rw [hstar]
      simpa [horth]
    · rw [hχi] at horth
      have horth' : scalarProduct G (χs j) χ = 0 := by
        rw [scalarProduct_neg_right] at horth
        exact neg_eq_zero.mp horth
      rw [hstar]
      simpa [horth']
  by_cases hnone : ∀ i, scalarProduct G χ (χs i) = 0
  · right
    left
    have hsum : scalarProduct G χ ψ = 0 := by
      rw [hψsum]
      rw [scalarProduct_sum_right]
      refine Finset.sum_eq_zero ?_
      intro i hi
      rw [scalarProduct_smul_right]
      rw [hnone i]
      simp
    exact hsum
  · rcases not_forall.mp hnone with ⟨i, hi⟩
    have hsp : scalarProduct G χ ψ = ((m i : ℤ) : ℂ) * scalarProduct G χ (χs i) := by
      rw [hψsum]
      rw [scalarProduct_sum_right]
      rw [Finset.sum_eq_single i]
      · rw [scalarProduct_smul_right]
        rw [star_intCast]
        ring
      · intro j hj hji
        rw [scalarProduct_smul_right]
        rw [hatmost i hi j hji]
        rw [star_intCast]
        ring
      · intro hnot
        exact (hnot (Finset.mem_univ i)).elim
    rcases hmem i with h0 | h1 | hm1
    · right
      left
      rw [hsp, h0]
      norm_num
    · rcases hpair i with h1i | h0i | hm1i
      · left
        rw [hsp, h1, h1i]
        norm_num
      · right
        left
        rw [hsp, h1, h0i]
        norm_num
      · right
        right
        rw [hsp, h1, hm1i]
        norm_num
    · rcases hpair i with h1i | h0i | hm1i
      · right
        right
        rw [hsp, hm1, h1i]
        norm_num
      · right
        left
        rw [hsp, hm1, h0i]
        norm_num
      · left
        rw [hsp, hm1, hm1i]
        norm_num

/-- A signed irreducible paired with another signed irreducible has scalar
product in `{-1, 0, 1}`. -/
private lemma scalarProduct_signed_irr_signed_irr_mem {G : Type u} [Group G]
    [Fintype G] {χ ψ : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ ∨ IsIrreducibleCharacter (-χ))
    (hψ : IsIrreducibleCharacter ψ ∨ IsIrreducibleCharacter (-ψ)) :
    scalarProduct G χ ψ = 1 ∨ scalarProduct G χ ψ = 0 ∨ scalarProduct G χ ψ = -1 := by
  rcases hψ with hψ | hψneg
  · exact scalarProduct_signed_irr_irr_mem hχ hψ
  · rw [← neg_neg ψ, scalarProduct_neg_right]
    rcases scalarProduct_signed_irr_irr_mem hχ hψneg with h1 | h0 | hm1
    · right
      right
      simpa [h1]
    · right
      left
      simpa [h0]
    · left
      simpa [hm1]

/-- The induced class function of a character of `H0` is a character of `G`:
the explicit induced representation (`Representation.ind`), transported to a
`Fin m → ℂ` module via `charTrans` + the finite basis, with the character
matched to `inducedClassFunction` by `induced_character_formula` and the
`x ↦ x⁻¹` reindexing. -/
private lemma isCharacter_induced (c : Hyp11 G) (h12 : Hyp12 c)
    (ν : ClassFunction (↥c.H0)) (hν : IsCharacter ν) :
    IsCharacter (inducedClassFunction c.H0 ν) := by
  classical
  rcases hν with ⟨n, ρ, hνeq⟩
  let m := Module.finrank ℂ (Representation.IndV c.H0.subtype ρ)
  let e : Representation.IndV c.H0.subtype ρ ≃ₗ[ℂ] (Fin m → ℂ) :=
    (Module.finBasis ℂ (Representation.IndV c.H0.subtype ρ)).repr.trans
      (Finsupp.linearEquivFunOnFinite (α := Fin m) (R := ℂ) (M := ℂ))
  let ρ' : Representation ℂ G (Fin m → ℂ) :=
    charTrans e (Representation.ind c.H0.subtype ρ)
  refine ⟨m, ρ', ?_⟩
  ext g
  symm
  calc
    ρ'.character g = (Representation.ind c.H0.subtype ρ).character g := by
      exact congrFun ((Representation.char_iso
        (equiv_charTrans e (Representation.ind c.H0.subtype ρ))).symm) g
    _ = (Nat.card (↥c.H0) : ℂ)⁻¹ * ∑ x : G,
          if hx : x * g * x⁻¹ ∈ c.H0 then ρ.character ⟨x * g * x⁻¹, hx⟩ else 0 := by
            -- the formula's sum uses the `Fintype.ofFinite` instance; bridge to
            -- the section's `[Fintype G]` binder
            have hf := Theory.Representation.induced_character_formula c.H0 ρ g
            rw [hf]
            have hbridge : (∑ x ∈ @Finset.univ G (Fintype.ofFinite G),
                  if hx : x * g * x⁻¹ ∈ c.H0 then ρ.character ⟨x * g * x⁻¹, hx⟩ else 0) =
                (∑ x : G,
                  if hx : x * g * x⁻¹ ∈ c.H0 then ρ.character ⟨x * g * x⁻¹, hx⟩ else 0) := by
              apply Finset.sum_congr
              · ext x
                simp
              · intro x hx
                rfl
            rw [hbridge]
    _ = (Nat.card (↥c.H0) : ℂ)⁻¹ * ∑ x : G,
          if hx : x⁻¹ * g * x ∈ c.H0 then ρ.character ⟨x⁻¹ * g * x, hx⟩ else 0 := by
            congr 1
            refine Finset.sum_bij (fun x : G => fun hx : x ∈ Finset.univ => x⁻¹) ?_ ?_ ?_ ?_
            · intro x hx
              simp
            · intro x hx y hy hxy
              simpa [inv_inv] using congrArg (fun z : G => z⁻¹) hxy
            · intro b hb
              refine ⟨b⁻¹, by simp, ?_⟩
              simp [inv_inv]
            · intro x hx
              by_cases hxg : x * g * x⁻¹ ∈ c.H0
              · simp [hxg]
              · simp [hxg]
    _ = inducedClassFunction c.H0 ρ.character g := by
          unfold inducedClassFunction
          rfl
    _ = inducedClassFunction c.H0 ν g := by
          rw [hνeq]

/-- The induced of a generalized character of `H0` is a generalized character
of `G` (via `isCharacter_induced` + the linearity of induction). -/
private lemma isGeneralizedCharacter_induced (c : Hyp11 G) (h12 : Hyp12 c)
    (δ : ClassFunction (↥c.H0)) (hδ : IsGeneralizedCharacter δ) :
    IsGeneralizedCharacter (inducedClassFunction c.H0 δ) := by
  classical
  rcases hδ with ⟨χ, ψ, hχ, hψ, hδeq⟩
  refine ⟨inducedClassFunction c.H0 χ, inducedClassFunction c.H0 ψ,
    isCharacter_induced c h12 χ hχ, isCharacter_induced c h12 ψ hψ, ?_⟩
  rw [hδeq]
  exact inducedClassFunction_sub c.H0 χ ψ

/-- The negative of an irreducible character is a generalized character. -/
private lemma isGeneralizedCharacter_of_signed_irreducible {G : Type u} [Group G]
    {χ : ClassFunction G} (hχ : IsIrreducibleCharacter χ) :
    IsGeneralizedCharacter (-χ) := by
  rcases hχ with ⟨n, ρ, hρ, hχeq⟩
  refine ⟨0, χ, isCharacter_zero, ⟨n, ρ, hχeq⟩, ?_⟩
  simp

/-- Orthogonal norm-one generalized characters are disjoint (the
`θ̃`-lifts' pairwise disjointness: `θ̃ᵢ = ±χᵢ` with `χᵢ ≠ χⱼ` from the
orthogonality). -/
private lemma disjoint_of_orthogonal_norm_one {G : Type u} [Group G] [Fintype G]
    {φ ψ : ClassFunction G} (hφ : IsGeneralizedCharacter φ)
    (hψ : IsGeneralizedCharacter ψ)
    (hφ1 : scalarProduct G φ φ = 1) (hψ1 : scalarProduct G ψ ψ = 1)
    (horth : scalarProduct G φ ψ = 0) :
    Theory.Character.Disjoint φ ψ := by
  classical
  rcases norm_one_signed_irreducible hφ hφ1 with ⟨χ, hχ, hφeq⟩
  rcases norm_one_signed_irreducible hψ hψ1 with ⟨χ', hχ', hψeq⟩
  unfold Theory.Character.Disjoint
  intro α hα hαφ
  by_contra hαψ
  have hαχ : α = χ := by
    have hαχ0 : scalarProduct G α χ ≠ 0 := by
      rcases hφeq with hφeq | hφeq
      · rwa [hφeq] at hαφ
      · rw [hφeq, scalarProduct_neg_right] at hαφ
        intro h0
        apply hαφ
        rw [h0]
        norm_num
    by_cases h : α = χ
    · exact h
    · exfalso
      exact hαχ0 (scalarProduct_irreducible_orthogonal hα hχ h)
  have hαχ' : α = χ' := by
    have hαχ'0 : scalarProduct G α χ' ≠ 0 := by
      rcases hψeq with hψeq | hψeq
      · rwa [hψeq] at hαψ
      · rw [hψeq, scalarProduct_neg_right] at hαψ
        intro h0
        apply hαψ
        rw [h0]
        norm_num
    by_cases h : α = χ'
    · exact h
    · exfalso
      exact hαχ'0 (scalarProduct_irreducible_orthogonal hα hχ' h)
  have hχχ' : χ ≠ χ' := by
    intro h
    rcases hφeq with hφeq | hφeq <;> rcases hψeq with hψeq | hψeq
    · have this : scalarProduct G χ χ = 0 := by
        simpa [h, hφeq, hψeq] using horth
      rw [scalarProduct_irreducible_self hχ] at this
      norm_num at this
    · have this : scalarProduct G χ χ = 0 := by
        simpa [h, hφeq, hψeq, scalarProduct_neg_right] using horth
      rw [scalarProduct_irreducible_self hχ] at this
      norm_num at this
    · have this : scalarProduct G χ χ = 0 := by
        simpa [h, hφeq, hψeq, scalarProduct_neg_left] using horth
      rw [scalarProduct_irreducible_self hχ] at this
      norm_num at this
    · have this : scalarProduct G χ χ = 0 := by
        simpa [h, hφeq, hψeq, scalarProduct_neg_left, scalarProduct_neg_right] using horth
      rw [scalarProduct_irreducible_self hχ] at this
      norm_num at this
  exact hχχ' (hαχ.symm.trans hαχ')

/-- `Disjoint` is symmetric. -/
private lemma disjoint_comm {G : Type u} [Group G] [Fintype G]
    {φ ψ : ClassFunction G} (h : Theory.Character.Disjoint φ ψ) :
    Theory.Character.Disjoint ψ φ := by
  unfold Theory.Character.Disjoint
  intro χ hχ hχψ
  by_contra hχφ
  exact hχψ (h χ hχ hχφ)

/-- Orthogonal generalized characters of norms `1` and `2` are disjoint
(the norm-one side is a signed irreducible, so the orthogonality kills its
constituent's occurrence in the norm-two side). -/
private lemma disjoint_of_orthogonal_norm_one_two {G : Type u} [Group G] [Fintype G]
    {φ ψ : ClassFunction G} (hφ : IsGeneralizedCharacter φ)
    (hψ : IsGeneralizedCharacter ψ)
    (hφ1 : scalarProduct G φ φ = 1) (hψ2 : scalarProduct G ψ ψ = 2)
    (horth : scalarProduct G φ ψ = 0) :
    Theory.Character.Disjoint φ ψ := by
  classical
  rcases norm_one_signed_irreducible hφ hφ1 with ⟨χ, hχ, hφeq⟩
  unfold Theory.Character.Disjoint
  intro α hα hαφ
  have hαχ : α = χ := by
    have hαχ0 : scalarProduct G α χ ≠ 0 := by
      rcases hφeq with hφeq | hφeq
      · rwa [hφeq] at hαφ
      · rw [hφeq, scalarProduct_neg_right] at hαφ
        intro h0
        apply hαφ
        rw [h0]
        norm_num
    by_cases h : α = χ
    · exact h
    · exfalso
      exact hαχ0 (scalarProduct_irreducible_orthogonal hα hχ h)
  rw [hαχ]
  have hχψ : scalarProduct G χ ψ = 0 := by
    rcases hφeq with hφeq | hφeq
    · simpa [hφeq] using horth
    · simpa [hφeq, scalarProduct_neg_left] using horth
  exact hχψ

/-! ## Fact 4: the undefined-`θ̃ⱼ` constituent decomposition -/



/-- The difference of generalized characters is a generalized character. -/
private lemma isGeneralizedCharacter_sub {G : Type u} [Group G] [Fintype G]
    {φ ψ : ClassFunction G} (hφ : IsGeneralizedCharacter φ)
    (hψ : IsGeneralizedCharacter ψ) : IsGeneralizedCharacter (φ - ψ) := by
  rcases hφ with ⟨δ₁, δ₂, hδ₁, hδ₂, hφeq⟩
  rcases hψ with ⟨δ₃, δ₄, hδ₃, hδ₄, hψeq⟩
  refine ⟨δ₁ + δ₄, δ₂ + δ₃, isCharacter_add hδ₁ hδ₄, isCharacter_add hδ₂ hδ₃, ?_⟩
  rw [hφeq, hψeq]
  funext x
  simp [Pi.add_apply, Pi.sub_apply]
  ring

/-- The sum of generalized characters is a generalized character. -/
private lemma isGeneralizedCharacter_add {G : Type u} [Group G] [Fintype G]
    {φ ψ : ClassFunction G} (hφ : IsGeneralizedCharacter φ)
    (hψ : IsGeneralizedCharacter ψ) : IsGeneralizedCharacter (φ + ψ) := by
  rcases hφ with ⟨δ₁, δ₂, hδ₁, hδ₂, hφeq⟩
  rcases hψ with ⟨δ₃, δ₄, hδ₃, hδ₄, hψeq⟩
  refine ⟨δ₁ + δ₃, δ₂ + δ₄, isCharacter_add hδ₁ hδ₃, isCharacter_add hδ₂ hδ₄, ?_⟩
  rw [hφeq, hψeq]
  funext x
  simp [Pi.add_apply, Pi.sub_apply]
  ring

/-- The difference of irreducible characters is a generalized character. -/
private lemma isGeneralizedCharacter_sub_irr {G : Type u} [Group G] [Fintype G]
    {χ ψ : ClassFunction G} (hχ : IsIrreducibleCharacter χ)
    (hψ : IsIrreducibleCharacter ψ) : IsGeneralizedCharacter (χ - ψ) := by
  rcases hχ with ⟨n, ρ, hρ, hχeq⟩
  rcases hψ with ⟨m, σ, hσ, hψeq⟩
  refine ⟨χ, ψ, ?_, ?_, rfl⟩
  · exact ⟨n, ρ, hχeq⟩
  · exact ⟨m, σ, hψeq⟩

/-- `natAbs = 1` forces `m = ±1` (the `omega`-fallback: `omega` only handles
the `natAbs` values `0` and `1`). -/
private lemma int_natAbs_eq_one_iff {m : ℤ} (h : m.natAbs = 1) : m = 1 ∨ m = -1 := by
  have h' : m ^ 2 = (1 : ℤ) := by
    rw [pow_two]
    rw [← Int.natAbs_mul_self]
    rw [h]
    norm_num
  exact sq_eq_sq_iff_eq_or_eq_neg.mp (by simpa using h')

/-- `natAbs = 2` forces `m = ±2`. -/
private lemma int_natAbs_eq_two_iff {m : ℤ} (h : m.natAbs = 2) : m = 2 ∨ m = -2 := by
  have h' : m ^ 2 = (4 : ℤ) := by
    rw [pow_two]
    rw [← Int.natAbs_mul_self]
    rw [h]
    norm_num
  exact sq_eq_sq_iff_eq_or_eq_neg.mp (by simpa using h')

/-- The `k = 4` analogue of `int_sq_sum_mem`: a sum of squares of integers
equal to `4` forces each integer to be `0`, `±1`, or `±2`. -/
private lemma int_sq_sum_mem_four {ι : Type*} [Fintype ι] {m : ι → ℤ}
    (h : (∑ i, ((m i : ℤ) : ℂ)^2) = (4 : ℂ)) :
    ∀ i, m i = 0 ∨ m i = 1 ∨ m i = -1 ∨ m i = 2 ∨ m i = -2 := by
  intro i
  have hb : (m i : ℤ)^2 ≤ (4 : ℤ) := int_sq_sum_bound h i
  have hz : ((m i).natAbs : ℤ)^2 ≤ (4 : ℤ) := by
    simpa [Int.natAbs_mul_self] using hb
  have hz' : (m i).natAbs ^ 2 ≤ 4 := by exact_mod_cast hz
  have hnat : (m i).natAbs ≤ 2 := by
    by_contra hnot
    have hge : 3 ≤ (m i).natAbs := by omega
    have hsq : 9 ≤ (m i).natAbs ^ 2 := by
      simpa [pow_two] using (Nat.mul_le_mul hge hge)
    nlinarith
  have hcases : (m i).natAbs = 0 ∨ (m i).natAbs = 1 ∨ (m i).natAbs = 2 := by
    interval_cases (m i).natAbs
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  rcases hcases with h0 | h1 | h2
  · left
    exact Int.natAbs_eq_zero.mp h0
  · rcases int_natAbs_eq_one_iff h1 with h1p | h1n
    · right
      left
      exact h1p
    · right
      right
      left
      exact h1n
  · rcases int_natAbs_eq_two_iff h2 with h2p | h2n
    · right
      right
      right
      left
      exact h2p
    · right
      right
      right
      right
      exact h2n

/-- The signed sum of two irreducibles is a generalized character. -/
private lemma isGeneralizedCharacter_signed_pair {G : Type u} [Group G] [Fintype G]
    {χ ψ : ClassFunction G} (hχ : IsIrreducibleCharacter χ) (hψ : IsIrreducibleCharacter ψ)
    (ε₁ ε₂ : ℤ) (hε₁ : ε₁ = 1 ∨ ε₁ = -1) (hε₂ : ε₂ = 1 ∨ ε₂ = -1) :
    IsGeneralizedCharacter ((ε₁ : ℂ) • χ + (ε₂ : ℂ) • ψ) := by
  rcases hε₁ with hε₁ | hε₁ <;> rcases hε₂ with hε₂ | hε₂ <;>
    simp [hε₁, hε₂]
  · exact isGeneralizedCharacter_add
      (isGeneralizedCharacter_of_isCharacter (isCharacter_of_isIrreducibleCharacter hχ))
      (isGeneralizedCharacter_of_isCharacter (isCharacter_of_isIrreducibleCharacter hψ))
  · exact isGeneralizedCharacter_sub
      (isGeneralizedCharacter_of_isCharacter (isCharacter_of_isIrreducibleCharacter hχ))
      (isGeneralizedCharacter_of_isCharacter (isCharacter_of_isIrreducibleCharacter hψ))
  · exact isGeneralizedCharacter_add (isGeneralizedCharacter_of_signed_irreducible hχ)
      (isGeneralizedCharacter_of_isCharacter (isCharacter_of_isIrreducibleCharacter hψ))
  · exact isGeneralizedCharacter_sub (isGeneralizedCharacter_of_signed_irreducible hχ)
      (isGeneralizedCharacter_of_isCharacter (isCharacter_of_isIrreducibleCharacter hψ))

/-- The norm of a signed pair of distinct irreducibles is `2`. -/
private lemma normSq_signed_pair_two {G : Type u} [Group G] [Fintype G]
    {χ ψ : ClassFunction G} (hχ : IsIrreducibleCharacter χ) (hψ : IsIrreducibleCharacter ψ)
    (hne : χ ≠ ψ) (ε₁ ε₂ : ℤ) (hε₁ : ε₁ = 1 ∨ ε₁ = -1) (hε₂ : ε₂ = 1 ∨ ε₂ = -1) :
    normSq G ((ε₁ : ℂ) • χ + (ε₂ : ℂ) • ψ) = 2 := by
  rcases hε₁ with hε₁ | hε₁ <;> rcases hε₂ with hε₂ | hε₂ <;>
    simp [normSq, hε₁, hε₂, scalarProduct_add_left, scalarProduct_add_right,
      scalarProduct_smul_left, scalarProduct_smul_right, scalarProduct_neg_left,
      scalarProduct_neg_right, star_intCast,
      irreducible_scalarProduct_self hχ, irreducible_scalarProduct_self hψ,
      scalarProduct_irreducible_orthogonal hχ hψ hne,
      scalarProduct_irreducible_orthogonal hψ hχ hne.symm] <;> norm_num

/-- The pairing of two signed pairs of pairwise-distinct irreducibles is `0`. -/
private lemma scalarProduct_signed_pair_pair_zero {G : Type u} [Group G] [Fintype G]
    {χ ψ φ ρ : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ) (hψ : IsIrreducibleCharacter ψ)
    (hφ : IsIrreducibleCharacter φ) (hρ : IsIrreducibleCharacter ρ)
    (hχψ : χ ≠ ψ) (hχφ : χ ≠ φ) (hχρ : χ ≠ ρ)
    (hψφ : ψ ≠ φ) (hψρ : ψ ≠ ρ) (hφρ : φ ≠ ρ)
    (ε₁ ε₂ ε₃ ε₄ : ℤ)
    (hε₁ : ε₁ = 1 ∨ ε₁ = -1) (hε₂ : ε₂ = 1 ∨ ε₂ = -1)
    (hε₃ : ε₃ = 1 ∨ ε₃ = -1) (hε₄ : ε₄ = 1 ∨ ε₄ = -1) :
    scalarProduct G ((ε₁ : ℂ) • χ + (ε₂ : ℂ) • ψ) ((ε₃ : ℂ) • φ + (ε₄ : ℂ) • ρ) = 0 := by
  rcases hε₁ with hε₁ | hε₁ <;> rcases hε₂ with hε₂ | hε₂ <;>
    rcases hε₃ with hε₃ | hε₃ <;> rcases hε₄ with hε₄ | hε₄ <;>
      simp [hε₁, hε₂, hε₃, hε₄, scalarProduct_add_left, scalarProduct_add_right,
        scalarProduct_smul_left, scalarProduct_smul_right, scalarProduct_neg_left,
        scalarProduct_neg_right, star_intCast,
        scalarProduct_irreducible_orthogonal hχ hφ hχφ,
        scalarProduct_irreducible_orthogonal hχ hρ hχρ,
        scalarProduct_irreducible_orthogonal hψ hφ hψφ,
        scalarProduct_irreducible_orthogonal hψ hρ hψρ] <;> norm_num

/-- The norm-4 signed decomposition with a vanishing value at `1`: a
generalized character `δ` with `|δ|² = 4` and `δ(1) = 0` is a difference
`δ = A − B` of disjoint generalized characters with `|A|² = |B|² = 2`.
The `δ(1) = 0` kills the single `±2χ` constituent; the support is then
four `±1`-constituents, split uniformly as
`A := m₀χ₀ + m₁χ₁`, `B := −(m₂χ₂ + m₃χ₃)` (the `n = 2` invariant-orbit
lift's input). -/
private lemma normSq4_decomp_of_zero_one {G : Type u} [Group G] [Fintype G]
    {δ : ClassFunction G} (hδ : IsGeneralizedCharacter δ) (hn : normSq G δ = 4)
    (hdeg : δ 1 = 0) :
    ∃ A B : ClassFunction G,
      IsGeneralizedCharacter A ∧ IsGeneralizedCharacter B ∧
      normSq G A = 2 ∧ normSq G B = 2 ∧ scalarProduct G A B = 0 ∧ δ = A - B := by
  classical
  rcases char_decomp_generalized hδ with ⟨ι, _, χs, ms, hirr, hdist, hδsum⟩
  have hnorm : (∑ i, ((ms i : ℤ) : ℂ)^2) = (4 : ℂ) := by
    rw [← decomp_scalarProduct hirr hdist]
    rw [← hδsum]
    simpa [normSq] using hn
  have hmem : ∀ i, ms i = 0 ∨ ms i = 1 ∨ ms i = -1 ∨ ms i = 2 ∨ ms i = -2 :=
    int_sq_sum_mem_four hnorm
  -- no `±2` member: `δ(1) = Σ (ms j) • χs j 1` with a single `±2` would
  -- contradict the positivity of the irreducible degrees
  have hno2' : ∀ i, ms i = 2 ∨ ms i = -2 → False := by
    intro i hi
    -- the `i`-term saturates the norm, so the complement sum vanishes
    have hnorm_i : ((ms i : ℤ) : ℂ)^2 = (4 : ℂ) := by
      rcases hi with hi | hi <;> rw [hi] <;> norm_num
    have hrest : (∑ j ∈ Finset.univ.erase i, ((ms j : ℤ) : ℂ)^2) = 0 := by
      have hsplit : (∑ j : ι, ((ms j : ℤ) : ℂ)^2) =
          ((ms i : ℤ) : ℂ)^2 + (∑ j ∈ Finset.univ.erase i, ((ms j : ℤ) : ℂ)^2) := by
        rw [← Finset.sum_erase_add (s := Finset.univ)
          (f := fun j : ι => ((ms j : ℤ) : ℂ)^2) (a := i) (Finset.mem_univ i)]
        ring
      have hnorm' : ((ms i : ℤ) : ℂ)^2 + (∑ j ∈ Finset.univ.erase i, ((ms j : ℤ) : ℂ)^2) = (4 : ℂ) := by
        rwa [← hsplit]
      have hS : (∑ j ∈ Finset.univ.erase i, ((ms j : ℤ) : ℂ)^2) = 0 := by
        have hnorm'' : (4 : ℂ) + (∑ j ∈ Finset.univ.erase i, ((ms j : ℤ) : ℂ)^2) = (4 : ℂ) := by
          rwa [hnorm_i] at hnorm'
        have hS' : (∑ j ∈ Finset.univ.erase i, ((ms j : ℤ) : ℂ)^2) = (4 : ℂ) - (4 : ℂ) := by
          calc
            (∑ j ∈ Finset.univ.erase i, ((ms j : ℤ) : ℂ)^2)
                = (4 : ℂ) + (∑ j ∈ Finset.univ.erase i, ((ms j : ℤ) : ℂ)^2) - (4 : ℂ) := by
                  ring
            _ = (4 : ℂ) - (4 : ℂ) := by
                  rw [hnorm'']
        simpa using hS'
      exact hS
    have hzero_rest : ∀ j, j ≠ i → ms j = 0 := by
      intro j hj
      by_contra h
      have hsq_ge : (1 : ℝ) ≤ ((ms j : ℤ) : ℝ)^2 := by
        rcases hmem j with h0 | h1 | hneg1 | h2 | hneg2
        · contradiction
        · rw [h1]
          norm_num
        · rw [hneg1]
          norm_num
        · rw [h2]
          norm_num
        · rw [hneg2]
          norm_num
      have hres_r : (∑ k ∈ Finset.univ.erase i, ((ms k : ℤ) : ℝ)^2) = (0 : ℝ) := by
        exact_mod_cast hrest
      have hle : ((ms j : ℤ) : ℝ)^2 ≤
          (∑ k ∈ Finset.univ.erase i, ((ms k : ℤ) : ℝ)^2) := by
        exact Finset.single_le_sum (s := Finset.univ.erase i)
          (f := fun k => ((ms k : ℤ) : ℝ)^2)
          (fun k hk => sq_nonneg ((ms k : ℤ) : ℝ)) (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)
      nlinarith [hsq_ge, hle, hres_r]
    -- `δ` collapses to the single `±2χs i` term, so `δ(1) = ±2 • χs i 1 ≠ 0`
    have hδi : δ = (ms i : ℂ) • χs i := by
      rw [hδsum]
      have hsum : (∑ j : ι, (ms j : ℂ) • χs j) = (ms i : ℂ) • χs i := by
        rw [Finset.sum_eq_single i]
        · intro j hj jne
          simp [hzero_rest j jne]
        · intro hnot
          exact (hnot (Finset.mem_univ i)).elim
      exact hsum
    rw [hδi] at hdeg
    have hval : ((ms i : ℂ) • χs i) 1 = (ms i : ℂ) * χs i 1 := by simp
    rw [hval] at hdeg
    have hmsi_ne0 : (ms i : ℂ) ≠ 0 := by
      rcases hi with hi | hi <;> rw [hi] <;> norm_num
    exact (irreducible_char_one_ne_zero (hirr i))
      ((mul_eq_zero.mp hdeg).resolve_left hmsi_ne0)
  have hno2 : ∀ i, ms i ≠ 2 ∧ ms i ≠ -2 := by
    intro i
    constructor
    · intro hi
      exact hno2' i (Or.inl hi)
    · intro hi
      exact hno2' i (Or.inr hi)
  -- the support members are `±1`; the support has four elements
  have hmem1 : ∀ i, ms i ≠ 0 → ms i = 1 ∨ ms i = -1 := by
    intro i h
    rcases hmem i with h0 | h1 | hneg1 | h2 | hneg2
    · contradiction
    · exact Or.inl h1
    · exact Or.inr hneg1
    · exfalso
      exact (hno2 i).1 h2
    · exfalso
      exact (hno2 i).2 hneg2
  let S : Finset ι := Finset.univ.filter (fun i => ms i ≠ 0)
  have hSeq : (∑ i : ι, ((ms i : ℤ) : ℂ)^2) =
      (∑ i : ι, (if ms i ≠ 0 then (1 : ℂ) else 0)) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    by_cases h : ms i = 0
    · simp [h]
    · rcases hmem1 i h with h1 | hneg1
      · simp [h1]
      · simp [hneg1]
  have hcard : S.card = 4 := by
    have h' : (∑ i : ι, (if ms i ≠ 0 then (1 : ℂ) else 0)) = (4 : ℂ) := by
      rw [← hSeq, hnorm]
    have h'' : (∑ i : ι, (if ms i ≠ 0 then (1 : ℂ) else 0)) = (S.card : ℂ) := by
      unfold S
      rw [Finset.sum_boole]
    exact_mod_cast (h''.symm.trans h')
  rcases Finset.card_eq_four.mp hcard with
    ⟨i₀, i₁, i₂, i₃, hi01, hi02, hi03, hi12, hi13, hi23, hSm⟩
  have hmi₀S : i₀ ∈ S := by
    rw [hSm]
    simp
  have hmi₁S : i₁ ∈ S := by
    rw [hSm]
    simp
  have hmi₂S : i₂ ∈ S := by
    rw [hSm]
    simp
  have hmi₃S : i₃ ∈ S := by
    rw [hSm]
    simp
  have hmi₀ : ms i₀ = 1 ∨ ms i₀ = -1 := hmem1 i₀ (Finset.mem_filter.mp hmi₀S).2
  have hmi₁ : ms i₁ = 1 ∨ ms i₁ = -1 := hmem1 i₁ (Finset.mem_filter.mp hmi₁S).2
  have hmi₂ : ms i₂ = 1 ∨ ms i₂ = -1 := hmem1 i₂ (Finset.mem_filter.mp hmi₂S).2
  have hmi₃ : ms i₃ = 1 ∨ ms i₃ = -1 := hmem1 i₃ (Finset.mem_filter.mp hmi₃S).2
  have hzero : ∀ i, i ≠ i₀ → i ≠ i₁ → i ≠ i₂ → i ≠ i₃ → ms i = 0 := by
    intro i hi0 hi1 hi2 hi3
    by_contra h
    have hiS : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩
    rw [hSm] at hiS
    simp [hi0, hi1, hi2, hi3] at hiS
  -- `δ` is the sum of the four constituents
  have hδfour : δ = (ms i₀ : ℂ) • χs i₀ + (ms i₁ : ℂ) • χs i₁ +
      (ms i₂ : ℂ) • χs i₂ + (ms i₃ : ℂ) • χs i₃ := by
    rw [hδsum]
    have hrest : (∑ i ∈ (Finset.univ \ ({i₀, i₁, i₂, i₃} : Finset ι)), (ms i : ℂ) • χs i) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro i hi
      simp at hi
      rcases hi with ⟨hi0, hi1, hi2, hi3⟩
      simp [hzero i hi0 hi1 hi2 hi3]
    have hsum : (∑ i : ι, (ms i : ℂ) • χs i) =
        (ms i₀ : ℂ) • χs i₀ + (ms i₁ : ℂ) • χs i₁ +
          (ms i₂ : ℂ) • χs i₂ + (ms i₃ : ℂ) • χs i₃ := by
      rw [← Finset.sum_sdiff (by simp : ({i₀, i₁, i₂, i₃} : Finset ι) ⊆ Finset.univ)]
      rw [hrest, zero_add]
      simp [hi01, hi02, hi03, hi12, hi13, hi23]
      ac_rfl
    exact hsum
  -- the uniform split: `A := m₀χ₀ + m₁χ₁`, `B := −(m₂χ₂ + m₃χ₃)`
  have hε₂ : -ms i₂ = 1 ∨ -ms i₂ = -1 := by
    rcases hmi₂ with h | h <;> rw [h] <;> norm_num
  have hε₃ : -ms i₃ = 1 ∨ -ms i₃ = -1 := by
    rcases hmi₃ with h | h <;> rw [h] <;> norm_num
  let A : ClassFunction G := (ms i₀ : ℂ) • χs i₀ + (ms i₁ : ℂ) • χs i₁
  let B : ClassFunction G := ((-ms i₂ : ℤ) : ℂ) • χs i₂ + ((-ms i₃ : ℤ) : ℂ) • χs i₃
  refine ⟨A, B, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `A` is a generalized character
    exact isGeneralizedCharacter_signed_pair (hirr i₀) (hirr i₁) (ms i₀) (ms i₁) hmi₀ hmi₁
  · -- `B` is a generalized character
    exact isGeneralizedCharacter_signed_pair (hirr i₂) (hirr i₃) (-ms i₂) (-ms i₃) hε₂ hε₃
  · -- `|A|² = 2`
    exact normSq_signed_pair_two (hirr i₀) (hirr i₁) (hdist i₀ i₁ hi01) (ms i₀) (ms i₁) hmi₀ hmi₁
  · -- `|B|² = 2`
    exact normSq_signed_pair_two (hirr i₂) (hirr i₃) (hdist i₂ i₃ hi23) (-ms i₂) (-ms i₃) hε₂ hε₃
  · -- `(A, B) = 0`
    exact scalarProduct_signed_pair_pair_zero (hirr i₀) (hirr i₁) (hirr i₂) (hirr i₃)
      (hdist i₀ i₁ hi01) (hdist i₀ i₂ hi02) (hdist i₀ i₃ hi03)
      (hdist i₁ i₂ hi12) (hdist i₁ i₃ hi13) (hdist i₂ i₃ hi23)
      (ms i₀) (ms i₁) (-ms i₂) (-ms i₃) hmi₀ hmi₁ hε₂ hε₃
  · -- `δ = A − B`
    rw [hδfour]
    simp [A, B]
    ring

/-- `(θ(ν₁), θ(ν₂))_H = 0` for distinct non-`s`-conjugate irreducible
characters of `H0` (the same-orbit version of `theta_pair_orth`). -/
private lemma theta_pair_scalar_zero (c : Hyp11 G) (h12 : Hyp12 c)
    (hH0index : (c.H0.subgroupOf c.H).index = 2)
    {ν₁ ν₂ : ClassFunction (↥c.H0)} (hν₁ : IsIrreducibleCharacter ν₁)
    (hν₂ : IsIrreducibleCharacter ν₂)
    (hne : ν₁ ≠ ν₂) (hnes : conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ≠ ν₂) :
    scalarProduct (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν₁)
        (inducedFromSub (h12.H0_normal_in_H).1 ν₂) = 0 := by
  classical
  have hs_inv : ∀ x : ↥c.H0, c.s⁻¹ * (x : G) * c.s ∈ c.H0 := by
    intro x
    simpa using (h12.H0_normal_in_H).2 c.s⁻¹ (c.H.inv_mem (s_mem_H c)) (x : G) x.2
  have hν₂s : IsIrreducibleCharacter (conjChar c.H0 (s_normalizes_H0 c h12) ν₂) :=
    isIrreducibleCharacter_conjChar c.H0 (s_normalizes_H0 c h12) hs_inv hν₂
  have hν₁s : IsIrreducibleCharacter (conjChar c.H0 (s_normalizes_H0 c h12) ν₁) :=
    isIrreducibleCharacter_conjChar c.H0 (s_normalizes_H0 c h12) hs_inv hν₁
  rw [theta_pair_scalar_H' c h12 hH0index hν₁ hν₂]
  have h₁₂' : ν₁ ≠ conjChar c.H0 (s_normalizes_H0 c h12) ν₂ := by
    intro h
    apply hnes
    have hc := congrArg (conjChar c.H0 (s_normalizes_H0 c h12)) h
    rw [conjChar_conjChar c h12 ν₂] at hc
    exact hc
  have hs₁₂s : conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ≠
      conjChar c.H0 (s_normalizes_H0 c h12) ν₂ := by
    intro h
    apply hne
    have hc := congrArg (conjChar c.H0 (s_normalizes_H0 c h12)) h
    rw [conjChar_conjChar c h12 ν₁] at hc
    rw [conjChar_conjChar c h12 ν₂] at hc
    exact hc
  have h1 : scalarProduct (↥c.H0) ν₁ ν₂ = 0 := by
    rw [scalarProduct_irr_ite hν₁ hν₂]
    simp [hne]
  have h2 : scalarProduct (↥c.H0) ν₁ (conjChar c.H0 (s_normalizes_H0 c h12) ν₂) = 0 := by
    rw [scalarProduct_irr_ite hν₁ hν₂s]
    simp [h₁₂']
  have h3 : scalarProduct (↥c.H0) (conjChar c.H0 (s_normalizes_H0 c h12) ν₁) ν₂ = 0 := by
    rw [scalarProduct_irr_ite hν₁s hν₂]
    simp [hnes]
  have h4 : scalarProduct (↥c.H0) (conjChar c.H0 (s_normalizes_H0 c h12) ν₁)
      (conjChar c.H0 (s_normalizes_H0 c h12) ν₂) = 0 := by
    rw [scalarProduct_irr_ite hν₁s hν₂s]
    simp [hs₁₂s]
  simp [h1, h2, h3, h4]


/-- Fact 4 (the undefined-`θ̃ⱼ` case): for orbit members `ν₁, ν₂, ν₃, νⱼ`
with `θ₂, θ₃` irreducible and `χ₂₃` the signed common constituent of
`δ₂*` and `δ₃*` with `(χ₂₃, δⱼ*) = 0`, the decomposition
`δⱼ* = φ − θ̃₂ − θ̃₃` with `φ` a signed irreducible and pairwise orthogonal
constituents, and the corrected pairings `(θ̃₂, δⱼ*) = (θ̃₃, δⱼ*) = −1`,
`normSq G δⱼ* = 3` (NOT the old `= 2` claim). -/
private lemma delta_star_decomp_of_undefined (c : Hyp11 G) (h12 : Hyp12 c)
    (hH0index : (c.H0.subgroupOf c.H).index = 2)
    {ν₁ ν₂ ν₃ νⱼ : ClassFunction (↥c.H0)}
    (hν₁ : IsIrreducibleCharacter ν₁) (hν₂ : IsIrreducibleCharacter ν₂)
    (hν₃ : IsIrreducibleCharacter ν₃) (hνⱼ : IsIrreducibleCharacter νⱼ)
    (h₂₁ : ν₂ ∈ orbit c.H0 c.U ν₁) (h₃₁ : ν₃ ∈ orbit c.H0 c.U ν₁)
    (hⱼ₁ : νⱼ ∈ orbit c.H0 c.U ν₁)
    (hν₁s : conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ≠ ν₁)
    (hν₂s : conjChar c.H0 (s_normalizes_H0 c h12) ν₂ ≠ ν₂)
    (hν₃s : conjChar c.H0 (s_normalizes_H0 c h12) ν₃ ≠ ν₃)
    (h₁₂ : ν₁ ≠ ν₂ ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ≠ ν₂)
    (h₁₃ : ν₁ ≠ ν₃ ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ≠ ν₃)
    (h₁ⱼ : ν₁ ≠ νⱼ ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ≠ νⱼ)
    (h₂₃ : ν₂ ≠ ν₃ ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₂ ≠ ν₃)
    (h₂ⱼ : ν₂ ≠ νⱼ ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₂ ≠ νⱼ)
    (h₃ⱼ : ν₃ ≠ νⱼ ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₃ ≠ νⱼ)
    {χ₂₃ : ClassFunction G}
    (hχg : IsGeneralizedCharacter χ₂₃) (hχ₁ : normSq G χ₂₃ = 1)
    (hχ₂ : scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - ν₂)) = 1)
    (hχ₃ : scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - ν₃)) = 1)
    (hχⱼ : scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - νⱼ)) = 0) :
    ∃ φ : ClassFunction G,
      (IsIrreducibleCharacter φ ∨ IsIrreducibleCharacter (-φ)) ∧
      scalarProduct G φ (χ₂₃ - inducedClassFunction c.H0 (ν₁ - ν₂)) = 0 ∧
      scalarProduct G φ (χ₂₃ - inducedClassFunction c.H0 (ν₁ - ν₃)) = 0 ∧
      inducedClassFunction c.H0 (ν₁ - νⱼ) =
        φ - (χ₂₃ - inducedClassFunction c.H0 (ν₁ - ν₂)) -
          (χ₂₃ - inducedClassFunction c.H0 (ν₁ - ν₃)) ∧
      scalarProduct G (χ₂₃ - inducedClassFunction c.H0 (ν₁ - ν₂))
        (inducedClassFunction c.H0 (ν₁ - νⱼ)) = -1 ∧
      scalarProduct G (χ₂₃ - inducedClassFunction c.H0 (ν₁ - ν₃))
        (inducedClassFunction c.H0 (ν₁ - νⱼ)) = -1 ∧
      normSq G (inducedClassFunction c.H0 (ν₁ - νⱼ)) = 3 := by
  classical
  let δ₂ : ClassFunction G := inducedClassFunction c.H0 (ν₁ - ν₂)
  let δ₃ : ClassFunction G := inducedClassFunction c.H0 (ν₁ - ν₃)
  let dj : ClassFunction G := inducedClassFunction c.H0 (ν₁ - νⱼ)
  let th2 : ClassFunction G := χ₂₃ - δ₂
  let th3 : ClassFunction G := χ₂₃ - δ₃
  let θ₁ : ClassFunction (↥c.H) := inducedFromSub (h12.H0_normal_in_H).1 ν₁
  let θ₂ : ClassFunction (↥c.H) := inducedFromSub (h12.H0_normal_in_H).1 ν₂
  let θ₃ : ClassFunction (↥c.H) := inducedFromSub (h12.H0_normal_in_H).1 ν₃
  let θⱼ : ClassFunction (↥c.H) := inducedFromSub (h12.H0_normal_in_H).1 νⱼ
  -- the reverse memberships (for `delta_pair_scalar`/`delta_norm`)
  have h₁₂L : ν₁ ∈ orbit c.H0 c.U ν₂ := by
    rw [orbit_eq_of_mem c h₂₁]
    exact orbit_self_mem c ν₁
  have h₁₃L : ν₁ ∈ orbit c.H0 c.U ν₃ := by
    rw [orbit_eq_of_mem c h₃₁]
    exact orbit_self_mem c ν₁
  have h₁ⱼL : ν₁ ∈ orbit c.H0 c.U νⱼ := by
    rw [orbit_eq_of_mem c hⱼ₁]
    exact orbit_self_mem c ν₁
  -- the norms of the induced characters (|θ₁| = |θ₂| = |θ₃| = 1, |θⱼ| ∈ {1,2})
  have hθ₁₁ : scalarProduct (↥c.H) θ₁ θ₁ = 1 := by
    change normSq (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν₁) = 1
    rw [theta_norm c h12 hH0index hν₁]
    simp [hν₁s]
  have hθ₂₂ : scalarProduct (↥c.H) θ₂ θ₂ = 1 := by
    change normSq (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν₂) = 1
    rw [theta_norm c h12 hH0index hν₂]
    simp [hν₂s]
  have hθ₃₃ : scalarProduct (↥c.H) θ₃ θ₃ = 1 := by
    change normSq (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν₃) = 1
    rw [theta_norm c h12 hH0index hν₃]
    simp [hν₃s]
  -- the pairwise H-side orthogonality
  have hθ₁₂ : scalarProduct (↥c.H) θ₁ θ₂ = 0 := by
    change scalarProduct (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν₁)
      (inducedFromSub (h12.H0_normal_in_H).1 ν₂) = 0
    exact theta_pair_scalar_zero c h12 hH0index hν₁ hν₂ h₁₂.1 h₁₂.2
  have hθ₁₃ : scalarProduct (↥c.H) θ₁ θ₃ = 0 := by
    change scalarProduct (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν₁)
      (inducedFromSub (h12.H0_normal_in_H).1 ν₃) = 0
    exact theta_pair_scalar_zero c h12 hH0index hν₁ hν₃ h₁₃.1 h₁₃.2
  have hθ₁ⱼ : scalarProduct (↥c.H) θ₁ θⱼ = 0 := by
    change scalarProduct (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν₁)
      (inducedFromSub (h12.H0_normal_in_H).1 νⱼ) = 0
    exact theta_pair_scalar_zero c h12 hH0index hν₁ hνⱼ h₁ⱼ.1 h₁ⱼ.2
  have hθ₂₃ : scalarProduct (↥c.H) θ₂ θ₃ = 0 := by
    change scalarProduct (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν₂)
      (inducedFromSub (h12.H0_normal_in_H).1 ν₃) = 0
    exact theta_pair_scalar_zero c h12 hH0index hν₂ hν₃ h₂₃.1 h₂₃.2
  have hθ₂ⱼ : scalarProduct (↥c.H) θ₂ θⱼ = 0 := by
    change scalarProduct (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν₂)
      (inducedFromSub (h12.H0_normal_in_H).1 νⱼ) = 0
    exact theta_pair_scalar_zero c h12 hH0index hν₂ hνⱼ h₂ⱼ.1 h₂ⱼ.2
  have hθ₃ⱼ : scalarProduct (↥c.H) θ₃ θⱼ = 0 := by
    change scalarProduct (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν₃)
      (inducedFromSub (h12.H0_normal_in_H).1 νⱼ) = 0
    exact theta_pair_scalar_zero c h12 hH0index hν₃ hνⱼ h₃ⱼ.1 h₃ⱼ.2
  -- the star-flipped H-side pairings
  have hθ₂₁ : scalarProduct (↥c.H) θ₂ θ₁ = 0 := by
    rw [← scalarProduct_star_comm]
    simp [hθ₁₂]
  have hθ₃₁ : scalarProduct (↥c.H) θ₃ θ₁ = 0 := by
    rw [← scalarProduct_star_comm]
    simp [hθ₁₃]
  have hθⱼ₁ : scalarProduct (↥c.H) θⱼ θ₁ = 0 := by
    rw [← scalarProduct_star_comm]
    simp [hθ₁ⱼ]
  have hθ₃₂ : scalarProduct (↥c.H) θ₃ θ₂ = 0 := by
    rw [← scalarProduct_star_comm]
    simp [hθ₂₃]
  have hθⱼ₂ : scalarProduct (↥c.H) θⱼ θ₂ = 0 := by
    rw [← scalarProduct_star_comm]
    simp [hθ₂ⱼ]
  have hθⱼ₃ : scalarProduct (↥c.H) θⱼ θ₃ = 0 := by
    rw [← scalarProduct_star_comm]
    simp [hθ₃ⱼ]
  -- the `δ`-pairings: `(δᵢ*, δₖ*) = (θ₁ − θᵢ, θ₁ − θₖ)_H = 1`
  have hδ₂₃ : scalarProduct G δ₂ δ₃ = 1 := by
    change scalarProduct G (inducedClassFunction c.H0 (ν₁ - ν₂))
      (inducedClassFunction c.H0 (ν₁ - ν₃)) = 1
    rw [delta_pair_scalar c h12 hν₂ hν₃ h₁₂L h₁₃L]
    change scalarProduct (↥c.H) (θ₁ - θ₂) (θ₁ - θ₃) = 1
    simp [scalarProduct_sub_left, scalarProduct_sub_right, hθ₁₁, hθ₁₃, hθ₂₁, hθ₂₃]
  have hδ₂ⱼ : scalarProduct G δ₂ dj = 1 := by
    change scalarProduct G (inducedClassFunction c.H0 (ν₁ - ν₂))
      (inducedClassFunction c.H0 (ν₁ - νⱼ)) = 1
    rw [delta_pair_scalar c h12 hν₂ hνⱼ h₁₂L h₁ⱼL]
    change scalarProduct (↥c.H) (θ₁ - θ₂) (θ₁ - θⱼ) = 1
    simp [scalarProduct_sub_left, scalarProduct_sub_right, hθ₁₁, hθ₁ⱼ, hθ₂₁, hθ₂ⱼ]
  have hδ₃ⱼ : scalarProduct G δ₃ dj = 1 := by
    change scalarProduct G (inducedClassFunction c.H0 (ν₁ - ν₃))
      (inducedClassFunction c.H0 (ν₁ - νⱼ)) = 1
    rw [delta_pair_scalar c h12 hν₃ hνⱼ h₁₃L h₁ⱼL]
    change scalarProduct (↥c.H) (θ₁ - θ₃) (θ₁ - θⱼ) = 1
    simp [scalarProduct_sub_left, scalarProduct_sub_right, hθ₁₁, hθ₁ⱼ, hθ₃₁, hθ₃ⱼ]
  -- the `δ`-norms: `|δ₂*|² = |δ₃*|² = 2`, `|dj*|² ∈ {2, 3}`
  have hδ₂norm : normSq G δ₂ = 2 := by
    change normSq G (inducedClassFunction c.H0 (ν₁ - ν₂)) = 2
    rw [delta_norm c h12 hH0index hν₁ hν₂ h₁₂L h₁₂.1 h₁₂.2]
    rw [theta_norm c h12 hH0index hν₁, theta_norm c h12 hH0index hν₂]
    simp [hν₁s, hν₂s]
    norm_num
  have hδ₃norm : normSq G δ₃ = 2 := by
    change normSq G (inducedClassFunction c.H0 (ν₁ - ν₃)) = 2
    rw [delta_norm c h12 hH0index hν₁ hν₃ h₁₃L h₁₃.1 h₁₃.2]
    rw [theta_norm c h12 hH0index hν₁, theta_norm c h12 hH0index hν₃]
    simp [hν₁s, hν₃s]
    norm_num
  have hdjnorm23 : normSq G dj = 2 ∨ normSq G dj = 3 := by
    change normSq G (inducedClassFunction c.H0 (ν₁ - νⱼ)) = 2 ∨
      normSq G (inducedClassFunction c.H0 (ν₁ - νⱼ)) = 3
    rw [delta_norm c h12 hH0index hν₁ hνⱼ h₁ⱼL h₁ⱼ.1 h₁ⱼ.2]
    rw [theta_norm c h12 hH0index hν₁, theta_norm c h12 hH0index hνⱼ]
    by_cases h : conjChar c.H0 (s_normalizes_H0 c h12) νⱼ = νⱼ
    · right
      simp [hν₁s, h]
      norm_num
    · left
      simp [hν₁s, h]
      norm_num
  -- the degree facts: `δ*(1) = 0`, `th2(1) = th3(1) = χ₂₃(1)`, `χ₂₃(1) ≠ 0`
  have hδ₂1 : δ₂ 1 = 0 := by
    change inducedClassFunction c.H0 (ν₁ - ν₂) 1 = 0
    exact inducedFromSub_one_eq c h12 (orbit_mem_degree_eq c h₂₁).symm
  have hδ₃1 : δ₃ 1 = 0 := by
    change inducedClassFunction c.H0 (ν₁ - ν₃) 1 = 0
    exact inducedFromSub_one_eq c h12 (orbit_mem_degree_eq c h₃₁).symm
  have hdj1 : dj 1 = 0 := by
    change inducedClassFunction c.H0 (ν₁ - νⱼ) 1 = 0
    exact inducedFromSub_one_eq c h12 (orbit_mem_degree_eq c hⱼ₁).symm
  have hth21 : th2 1 = χ₂₃ 1 := by
    change (χ₂₃ - δ₂) 1 = χ₂₃ 1
    simp [hδ₂1]
  have hth31 : th3 1 = χ₂₃ 1 := by
    change (χ₂₃ - δ₃) 1 = χ₂₃ 1
    simp [hδ₃1]
  rcases norm_one_signed_irreducible hχg hχ₁ with ⟨χ, hχ, hχcase⟩
  have hχ₂₃₁ : χ₂₃ 1 ≠ 0 := by
    rcases hχcase with hχcase | hχcase
    · rw [hχcase]
      exact irreducible_char_one_ne_zero hχ
    · intro h0
      exact (irreducible_char_one_ne_zero hχ) (neg_eq_zero.mp (by simpa [hχcase] using h0))
  -- the `θ̃`-norms and pairings
  have hδ₂χ : scalarProduct G δ₂ χ₂₃ = 1 := by
    apply star_inj.mp
    rw [scalarProduct_star_comm]
    change scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - ν₂)) = star 1
    simpa using hχ₂
  have hδ₃χ : scalarProduct G δ₃ χ₂₃ = 1 := by
    apply star_inj.mp
    rw [scalarProduct_star_comm]
    change scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - ν₃)) = star 1
    simpa using hχ₃
  have hth2norm : normSq G th2 = 1 := by
    change normSq G (χ₂₃ - δ₂) = 1
    unfold normSq
    rw [scalarProduct_sub_left, scalarProduct_sub_right, scalarProduct_sub_right]
    change scalarProduct G χ₂₃ χ₂₃ = 1 at hχ₁
    simp [δ₂, hχ₁, hχ₂, hδ₂χ]
    change normSq G δ₂ - 1 = 1
    rw [hδ₂norm]
    norm_num
  have hth3norm : normSq G th3 = 1 := by
    change normSq G (χ₂₃ - δ₃) = 1
    unfold normSq
    rw [scalarProduct_sub_left, scalarProduct_sub_right, scalarProduct_sub_right]
    change scalarProduct G χ₂₃ χ₂₃ = 1 at hχ₁
    simp [δ₃, hχ₁, hχ₃, hδ₃χ]
    change normSq G δ₃ - 1 = 1
    rw [hδ₃norm]
    norm_num
  have hth2th3 : scalarProduct G th2 th3 = 0 := by
    change scalarProduct G (χ₂₃ - δ₂) (χ₂₃ - δ₃) = 0
    rw [scalarProduct_sub_left, scalarProduct_sub_right, scalarProduct_sub_right]
    change scalarProduct G χ₂₃ χ₂₃ = 1 at hχ₁
    simp [δ₂, δ₃, hχ₁, hχ₃, hδ₂χ, hδ₂₃]
  have hth3th2 : scalarProduct G th3 th2 = 0 := by
    apply star_inj.mp
    rw [scalarProduct_star_comm]
    change scalarProduct G th2 th3 = star 0
    simpa using hth2th3
  have hth2dj : scalarProduct G th2 dj = -1 := by
    change scalarProduct G (χ₂₃ - δ₂) dj = -1
    rw [scalarProduct_sub_left]
    simp [dj, hχⱼ, hδ₂ⱼ]
  have hth3dj : scalarProduct G th3 dj = -1 := by
    change scalarProduct G (χ₂₃ - δ₃) dj = -1
    rw [scalarProduct_sub_left]
    simp [dj, hχⱼ, hδ₃ⱼ]
  have hdjth2 : scalarProduct G dj th2 = -1 := by
    apply star_inj.mp
    rw [scalarProduct_star_comm]
    change scalarProduct G th2 dj = star (-1)
    simpa using hth2dj
  have hdjth3 : scalarProduct G dj th3 = -1 := by
    apply star_inj.mp
    rw [scalarProduct_star_comm]
    change scalarProduct G th3 dj = star (-1)
    simpa using hth3dj
  -- `|dj*|² = 3`: the `|dj*|² = 2` case would force `dj* = −th2 − th3`,
  -- contradicting `dj*(1) = 0` and `th2(1) = th3(1) = χ₂₃(1) ≠ 0`
  have hdj3 : normSq G dj = 3 := by
    rcases hdjnorm23 with hdj2 | hdj3
    · exfalso
      have hψnorm : normSq G (dj + th2 + th3) = 0 := by
        unfold normSq
        simp [dj, th2, th3, scalarProduct_add_left, scalarProduct_add_right,
          hdjth2, hth2dj, hdjth3, hth3dj, hth2th3, hth3th2]
        change normSq G dj + -1 + -1 + (-1 + normSq G th2) + (-1 + normSq G th3) = 0
        rw [hdj2, hth2norm, hth3norm]
        norm_num
      have hψ0 : dj + th2 + th3 = 0 := (normSq_eq_zero_iff (dj + th2 + th3)).1 hψnorm
      have hψ1 : (dj + th2 + th3) 1 = 0 := by
        rw [hψ0]
        rfl
      have hψ1' : (dj + th2 + th3) 1 = 2 * χ₂₃ 1 := by
        simp [hdj1, hth21, hth31]
        ring
      rw [hψ1'] at hψ1
      exact (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) hχ₂₃₁) hψ1
    · exact hdj3
  -- `φ := dj* + th2 + th3` has norm one and is a signed irreducible
  have hφnorm : normSq G (dj + th2 + th3) = 1 := by
    unfold normSq
    simp [dj, th2, th3, scalarProduct_add_left, scalarProduct_add_right,
      hdjth2, hth2dj, hdjth3, hth3dj, hth2th3, hth3th2]
    change normSq G dj + -1 + -1 + (-1 + normSq G th2) + (-1 + normSq G th3) = 1
    rw [hdj3, hth2norm, hth3norm]
    norm_num
  have hdjg : IsGeneralizedCharacter dj := by
    change IsGeneralizedCharacter (inducedClassFunction c.H0 (ν₁ - νⱼ))
    exact isGeneralizedCharacter_induced c h12 (ν₁ - νⱼ) (isGeneralizedCharacter_sub_irr hν₁ hνⱼ)
  have hδ₂g : IsGeneralizedCharacter δ₂ := by
    change IsGeneralizedCharacter (inducedClassFunction c.H0 (ν₁ - ν₂))
    exact isGeneralizedCharacter_induced c h12 (ν₁ - ν₂) (isGeneralizedCharacter_sub_irr hν₁ hν₂)
  have hδ₃g : IsGeneralizedCharacter δ₃ := by
    change IsGeneralizedCharacter (inducedClassFunction c.H0 (ν₁ - ν₃))
    exact isGeneralizedCharacter_induced c h12 (ν₁ - ν₃) (isGeneralizedCharacter_sub_irr hν₁ hν₃)
  have hφg : IsGeneralizedCharacter (dj + th2 + th3) := by
    have hth2g : IsGeneralizedCharacter th2 := by
      change IsGeneralizedCharacter (χ₂₃ - δ₂)
      exact isGeneralizedCharacter_sub hχg hδ₂g
    have hth3g : IsGeneralizedCharacter th3 := by
      change IsGeneralizedCharacter (χ₂₃ - δ₃)
      exact isGeneralizedCharacter_sub hχg hδ₃g
    have hdjth2g : IsGeneralizedCharacter (dj + th2) :=
      isGeneralizedCharacter_add hdjg hth2g
    exact isGeneralizedCharacter_add hdjth2g hth3g
  rcases norm_one_signed_irreducible hφg hφnorm with ⟨χφ, hχφ, hφcase⟩
  refine ⟨dj + th2 + th3, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the signed irreducibility
    rcases hφcase with hφcase | hφcase
    · left
      simpa [hφcase] using hχφ
    · right
      simpa [hφcase] using hχφ
  · -- `(φ, th2) = 0`
    change scalarProduct G (dj + th2 + th3) th2 = 0
    rw [scalarProduct_add_left, scalarProduct_add_left]
    rw [hdjth2, hth3th2]
    change -1 + normSq G th2 + 0 = 0
    rw [hth2norm]
    norm_num
  · -- `(φ, th3) = 0`
    change scalarProduct G (dj + th2 + th3) th3 = 0
    rw [scalarProduct_add_left, scalarProduct_add_left]
    rw [hdjth3, hth2th3]
    change -1 + 0 + normSq G th3 = 0
    rw [hth3norm]
    norm_num
  · -- `dj = φ − th2 − th3`
    ring
  · exact hth2dj
  · exact hth3dj
  · exact hdj3


/-- In the norm-two case (the non-fixed members of an orbit), the common
constituent `χ₂₃` of `δ₂*` and `δ₃*` is automatically a constituent of every
other `δⱼ*` with multiplicity one: if `(χ₂₃, δⱼ*) ≠ 1`, then the pairing is
`0` or `-1`; `-1` is excluded by the norm-one signed `θ̃₂` (its pairing with
`δⱼ*` would be `-2`), and `0` feeds `delta_star_decomp_of_undefined`, whose
`normSq δⱼ* = 3` contradicts the norm-two hypothesis. -/
private lemma pairing_eq_one_of_norm_two (c : Hyp11 G) (h12 : Hyp12 c)
    (hH0index : (c.H0.subgroupOf c.H).index = 2)
    {ν₁ ν₂ ν₃ νⱼ : ClassFunction (↥c.H0)}
    (hν₁ : IsIrreducibleCharacter ν₁) (hν₂ : IsIrreducibleCharacter ν₂)
    (hν₃ : IsIrreducibleCharacter ν₃) (hνⱼ : IsIrreducibleCharacter νⱼ)
    (h₂₁ : ν₂ ∈ orbit c.H0 c.U ν₁) (h₃₁ : ν₃ ∈ orbit c.H0 c.U ν₁)
    (hⱼ₁ : νⱼ ∈ orbit c.H0 c.U ν₁)
    (hν₁s : conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ≠ ν₁)
    (hν₂s : conjChar c.H0 (s_normalizes_H0 c h12) ν₂ ≠ ν₂)
    (hν₃s : conjChar c.H0 (s_normalizes_H0 c h12) ν₃ ≠ ν₃)
    (hνⱼs : conjChar c.H0 (s_normalizes_H0 c h12) νⱼ ≠ νⱼ)
    (h₁₂ : ν₁ ≠ ν₂ ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ≠ ν₂)
    (h₁₃ : ν₁ ≠ ν₃ ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ≠ ν₃)
    (h₁ⱼ : ν₁ ≠ νⱼ ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ≠ νⱼ)
    (h₂₃ : ν₂ ≠ ν₃ ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₂ ≠ ν₃)
    (h₂ⱼ : ν₂ ≠ νⱼ ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₂ ≠ νⱼ)
    (h₃ⱼ : ν₃ ≠ νⱼ ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₃ ≠ νⱼ)
    {χ₂₃ : ClassFunction G}
    (hχsig : IsIrreducibleCharacter χ₂₃ ∨ IsIrreducibleCharacter (-χ₂₃))
    (hχg : IsGeneralizedCharacter χ₂₃) (hχ₁ : normSq G χ₂₃ = 1)
    (hχ₂ : scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - ν₂)) = 1)
    (hχ₃ : scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - ν₃)) = 1)
    (hδⱼnorm : normSq G (inducedClassFunction c.H0 (ν₁ - νⱼ)) = 2) :
    scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - νⱼ)) = 1 := by
  classical
  by_contra hχjne1
  have hδⱼg : IsGeneralizedCharacter (inducedClassFunction c.H0 (ν₁ - νⱼ)) := by
    exact isGeneralizedCharacter_induced c h12 (ν₁ - νⱼ)
      (isGeneralizedCharacter_sub_irr hν₁ hνⱼ)
  have hδ₂g : IsGeneralizedCharacter (inducedClassFunction c.H0 (ν₁ - ν₂)) := by
    exact isGeneralizedCharacter_induced c h12 (ν₁ - ν₂)
      (isGeneralizedCharacter_sub_irr hν₁ hν₂)
  have hδ₃g : IsGeneralizedCharacter (inducedClassFunction c.H0 (ν₁ - ν₃)) := by
    exact isGeneralizedCharacter_induced c h12 (ν₁ - ν₃)
      (isGeneralizedCharacter_sub_irr hν₁ hν₃)
  have hχjmem :
      scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - νⱼ)) = 1 ∨
        scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - νⱼ)) = 0 ∨
        scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - νⱼ)) = -1 := by
    exact scalarProduct_norm_one_signed_norm_two_mem hχsig hδⱼg hδⱼnorm
  have h₁ⱼL : ν₁ ∈ orbit c.H0 c.U νⱼ := by
    rw [orbit_eq_of_mem c hⱼ₁]
    exact orbit_self_mem c ν₁
  have h₁₂L : ν₁ ∈ orbit c.H0 c.U ν₂ := by
    rw [orbit_eq_of_mem c h₂₁]
    exact orbit_self_mem c ν₁
  have h₁₃L : ν₁ ∈ orbit c.H0 c.U ν₃ := by
    rw [orbit_eq_of_mem c h₃₁]
    exact orbit_self_mem c ν₁
  have hδ₂ⱼpair :
      scalarProduct G (inducedClassFunction c.H0 (ν₁ - ν₂))
        (inducedClassFunction c.H0 (ν₁ - νⱼ)) = 1 := by
    rw [delta_pair_scalar c h12 (ν₁ := ν₂) (ν₂ := νⱼ) (μ₁ := ν₁)
      (μ₂ := ν₁) hν₂ hνⱼ h₁₂L h₁ⱼL]
    change scalarProduct (↥c.H)
      (inducedFromSub (h12.H0_normal_in_H).1 ν₁ -
        inducedFromSub (h12.H0_normal_in_H).1 ν₂)
      (inducedFromSub (h12.H0_normal_in_H).1 ν₁ -
        inducedFromSub (h12.H0_normal_in_H).1 νⱼ) = 1
    have hθ₁₁ : scalarProduct (↥c.H)
        (inducedFromSub (h12.H0_normal_in_H).1 ν₁)
        (inducedFromSub (h12.H0_normal_in_H).1 ν₁) = 1 := by
      change normSq (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν₁) = 1
      rw [theta_norm c h12 hH0index hν₁, if_neg hν₁s]
    have hθ₁₂ : scalarProduct (↥c.H)
        (inducedFromSub (h12.H0_normal_in_H).1 ν₁)
        (inducedFromSub (h12.H0_normal_in_H).1 ν₂) = 0 :=
      theta_pair_scalar_zero c h12 hH0index hν₁ hν₂ h₁₂.1 h₁₂.2
    have hθ₁ⱼ : scalarProduct (↥c.H)
        (inducedFromSub (h12.H0_normal_in_H).1 ν₁)
        (inducedFromSub (h12.H0_normal_in_H).1 νⱼ) = 0 :=
      theta_pair_scalar_zero c h12 hH0index hν₁ hνⱼ h₁ⱼ.1 h₁ⱼ.2
    have hθ₂₁ : scalarProduct (↥c.H)
        (inducedFromSub (h12.H0_normal_in_H).1 ν₂)
        (inducedFromSub (h12.H0_normal_in_H).1 ν₁) = 0 :=
      theta_pair_scalar_zero c h12 hH0index hν₂ hν₁ h₁₂.1.symm (by
        intro hEq
        apply h₁₂.2
        rw [← hEq, conjChar_conjChar c h12 ν₂])
    have hθ₂ⱼ : scalarProduct (↥c.H)
        (inducedFromSub (h12.H0_normal_in_H).1 ν₂)
        (inducedFromSub (h12.H0_normal_in_H).1 νⱼ) = 0 :=
      theta_pair_scalar_zero c h12 hH0index hν₂ hνⱼ h₂ⱼ.1 h₂ⱼ.2
    simp [scalarProduct_sub_left, scalarProduct_sub_right,
      hθ₁₁, hθ₁₂, hθ₁ⱼ, hθ₂₁, hθ₂ⱼ]
  have hχj0 :
      scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - νⱼ)) = 0 := by
    rcases hχjmem with hχj1 | hχj0 | hχjm1
    · exact False.elim (hχjne1 hχj1)
    · exact hχj0
    · exfalso
      have hth2g : IsGeneralizedCharacter
          (χ₂₃ - inducedClassFunction c.H0 (ν₁ - ν₂)) := by
        exact isGeneralizedCharacter_sub hχg hδ₂g
      have hδ₂χ :
          scalarProduct G (inducedClassFunction c.H0 (ν₁ - ν₂)) χ₂₃ = 1 := by
        apply star_inj.mp
        rw [scalarProduct_star_comm]
        change scalarProduct G χ₂₃
          (inducedClassFunction c.H0 (ν₁ - ν₂)) = star 1
        simpa using hχ₂
      have hth2norm :
          normSq G (χ₂₃ - inducedClassFunction c.H0 (ν₁ - ν₂)) = 1 := by
        unfold normSq
        rw [scalarProduct_sub_left, scalarProduct_sub_right, scalarProduct_sub_right]
        change scalarProduct G χ₂₃ χ₂₃ = 1 at hχ₁
        have hδ₂self : scalarProduct G
            (inducedClassFunction c.H0 (ν₁ - ν₂))
            (inducedClassFunction c.H0 (ν₁ - ν₂)) = 2 := by
          change normSq G (inducedClassFunction c.H0 (ν₁ - ν₂)) = 2
          rw [delta_norm c h12 hH0index hν₁ hν₂ h₁₂L h₁₂.1 h₁₂.2]
          rw [theta_norm c h12 hH0index hν₁, theta_norm c h12 hH0index hν₂]
          rw [if_neg hν₁s, if_neg hν₂s]
          norm_num
        rw [hχ₁, hχ₂, hδ₂χ, hδ₂self]
        norm_num
      have hth2signed :
          IsIrreducibleCharacter
              (χ₂₃ - inducedClassFunction c.H0 (ν₁ - ν₂)) ∨
            IsIrreducibleCharacter
              (-(χ₂₃ - inducedClassFunction c.H0 (ν₁ - ν₂))) := by
        rcases norm_one_signed_irreducible hth2g hth2norm with
          ⟨η, hη, hηeq⟩
        rcases hηeq with hηeq | hηeq
        · left
          simpa [hηeq] using hη
        · right
          simpa [hηeq] using hη
      have hth2jmem :
          scalarProduct G (χ₂₃ - inducedClassFunction c.H0 (ν₁ - ν₂))
              (inducedClassFunction c.H0 (ν₁ - νⱼ)) = 1 ∨
            scalarProduct G (χ₂₃ - inducedClassFunction c.H0 (ν₁ - ν₂))
              (inducedClassFunction c.H0 (ν₁ - νⱼ)) = 0 ∨
            scalarProduct G (χ₂₃ - inducedClassFunction c.H0 (ν₁ - ν₂))
              (inducedClassFunction c.H0 (ν₁ - νⱼ)) = -1 := by
        exact scalarProduct_norm_one_signed_norm_two_mem
          hth2signed hδⱼg hδⱼnorm
      have hth2jneg2 :
          scalarProduct G (χ₂₃ - inducedClassFunction c.H0 (ν₁ - ν₂))
              (inducedClassFunction c.H0 (ν₁ - νⱼ)) = -2 := by
        rw [scalarProduct_sub_left, hχjm1, hδ₂ⱼpair]
        norm_num
      rcases hth2jmem with h1 | h0 | hm1
      · rw [hth2jneg2] at h1
        norm_num at h1
      · rw [hth2jneg2] at h0
        norm_num at h0
      · rw [hth2jneg2] at hm1
        norm_num at hm1
  rcases delta_star_decomp_of_undefined c h12 hH0index
      hν₁ hν₂ hν₃ hνⱼ h₂₁ h₃₁ hⱼ₁ hν₁s hν₂s hν₃s
      h₁₂ h₁₃ h₁ⱼ h₂₃ h₂ⱼ h₃ⱼ hχg hχ₁ hχ₂ hχ₃ hχj0 with
    ⟨φ, hφsig, hφth2, hφth3, hφdec, hth2dj, hth3dj, hdj3⟩
  rw [hδⱼnorm] at hdj3
  norm_num at hdj3


/-- `(δ₂*, δa*) = 1` for orbit members `a` with base `ν₁` (the
`(θ₁ − θ₂, θ₁ − θa)_H` expansion, used for the fixed-member pairings). -/
private lemma delta_pair_same_base_eq_one (c : Hyp11 G) (h12 : Hyp12 c)
    (hH0index : (c.H0.subgroupOf c.H).index = 2)
    {ν₁ ν₂ a : ClassFunction (↥c.H0)}
    (hν₁ : IsIrreducibleCharacter ν₁) (hν₂ : IsIrreducibleCharacter ν₂)
    (ha : IsIrreducibleCharacter a)
    (h₂₁ : ν₂ ∈ orbit c.H0 c.U ν₁) (ha₁ : a ∈ orbit c.H0 c.U ν₁)
    (hν₁s : conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ≠ ν₁)
    (h₁₂ : ν₁ ≠ ν₂ ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ≠ ν₂)
    (h₁a : ν₁ ≠ a ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ≠ a)
    (h₂a : ν₂ ≠ a ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₂ ≠ a) :
    scalarProduct G (inducedClassFunction c.H0 (ν₁ - ν₂))
      (inducedClassFunction c.H0 (ν₁ - a)) = 1 := by
  classical
  have h₁₂L : ν₁ ∈ orbit c.H0 c.U ν₂ := by
    rw [orbit_eq_of_mem c h₂₁]
    exact orbit_self_mem c ν₁
  have h₁aL : ν₁ ∈ orbit c.H0 c.U a := by
    rw [orbit_eq_of_mem c ha₁]
    exact orbit_self_mem c ν₁
  have hσ₂₁ : conjChar c.H0 (s_normalizes_H0 c h12) ν₂ ≠ ν₁ := by
    intro hEq
    apply h₁₂.2
    have h := congrArg (conjChar c.H0 (s_normalizes_H0 c h12)) hEq
    rw [conjChar_conjChar c h12 ν₂] at h
    exact h.symm
  rw [delta_pair_scalar c h12 hν₂ ha h₁₂L h₁aL]
  change scalarProduct (↥c.H)
    (inducedFromSub (h12.H0_normal_in_H).1 ν₁ -
      inducedFromSub (h12.H0_normal_in_H).1 ν₂)
    (inducedFromSub (h12.H0_normal_in_H).1 ν₁ -
      inducedFromSub (h12.H0_normal_in_H).1 a) = 1
  have hθ₁₁ : scalarProduct (↥c.H)
      (inducedFromSub (h12.H0_normal_in_H).1 ν₁)
      (inducedFromSub (h12.H0_normal_in_H).1 ν₁) = 1 := by
    change normSq (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν₁) = 1
    rw [theta_norm c h12 hH0index hν₁, if_neg hν₁s]
  have hθ₁a : scalarProduct (↥c.H)
      (inducedFromSub (h12.H0_normal_in_H).1 ν₁)
      (inducedFromSub (h12.H0_normal_in_H).1 a) = 0 :=
    theta_pair_scalar_zero c h12 hH0index hν₁ ha h₁a.1 h₁a.2
  have hθ₂₁ : scalarProduct (↥c.H)
      (inducedFromSub (h12.H0_normal_in_H).1 ν₂)
      (inducedFromSub (h12.H0_normal_in_H).1 ν₁) = 0 :=
    theta_pair_scalar_zero c h12 hH0index hν₂ hν₁ h₁₂.1.symm hσ₂₁
  have hθ₂a : scalarProduct (↥c.H)
      (inducedFromSub (h12.H0_normal_in_H).1 ν₂)
      (inducedFromSub (h12.H0_normal_in_H).1 a) = 0 :=
    theta_pair_scalar_zero c h12 hH0index hν₂ ha h₂a.1 h₂a.2
  simp [scalarProduct_sub_left, scalarProduct_sub_right,
    hθ₁₁, hθ₁a, hθ₂₁, hθ₂a]


/-- For an `s`-fixed member `a` with `|δa*|² = 3`, the pairing with the
common constituent `χ₂₃` is `0` or `1` (the `-1` case is excluded by the
norm-one signed `θ̃₂`, whose pairing with `δa*` would be `-2`). -/
private lemma fixed_member_pairing_eq_zero_or_one (c : Hyp11 G) (h12 : Hyp12 c)
    (hH0index : (c.H0.subgroupOf c.H).index = 2)
    {ν₁ ν₂ ν₃ a : ClassFunction (↥c.H0)}
    (hν₁ : IsIrreducibleCharacter ν₁) (hν₂ : IsIrreducibleCharacter ν₂)
    (hν₃ : IsIrreducibleCharacter ν₃) (ha : IsIrreducibleCharacter a)
    (h₂₁ : ν₂ ∈ orbit c.H0 c.U ν₁) (h₃₁ : ν₃ ∈ orbit c.H0 c.U ν₁)
    (ha₁ : a ∈ orbit c.H0 c.U ν₁)
    (hν₁s : conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ≠ ν₁)
    (hν₂s : conjChar c.H0 (s_normalizes_H0 c h12) ν₂ ≠ ν₂)
    (hν₃s : conjChar c.H0 (s_normalizes_H0 c h12) ν₃ ≠ ν₃)
    (hfixa : conjChar c.H0 (s_normalizes_H0 c h12) a = a)
    (h₁a : ν₁ ≠ a ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ≠ a)
    (h₂a : ν₂ ≠ a ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₂ ≠ a)
    (h₃a : ν₃ ≠ a ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₃ ≠ a)
    (h₁₂ : ν₁ ≠ ν₂ ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ≠ ν₂)
    (h₁₃ : ν₁ ≠ ν₃ ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ≠ ν₃)
    (h₂₃ : ν₂ ≠ ν₃ ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₂ ≠ ν₃)
    {χ₂₃ : ClassFunction G}
    (hχsig : IsIrreducibleCharacter χ₂₃ ∨ IsIrreducibleCharacter (-χ₂₃))
    (hχg : IsGeneralizedCharacter χ₂₃) (hχ₁ : normSq G χ₂₃ = 1)
    (hχ₂ : scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - ν₂)) = 1)
    (hχ₃ : scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - ν₃)) = 1)
    (hδanorm : normSq G (inducedClassFunction c.H0 (ν₁ - a)) = 3) :
    scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - a)) = 0 ∨
      scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - a)) = 1 := by
  classical
  have hδag : IsGeneralizedCharacter (inducedClassFunction c.H0 (ν₁ - a)) := by
    exact isGeneralizedCharacter_induced c h12 (ν₁ - a)
      (isGeneralizedCharacter_sub_irr hν₁ ha)
  have hχamem : scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - a)) = 1 ∨
      scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - a)) = 0 ∨
      scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - a)) = -1 := by
    exact scalarProduct_norm_one_signed_norm_three_mem hχsig hδag hδanorm
  rcases hχamem with h1 | h0 | hm1
  · exact Or.inr h1
  · exact Or.inl h0
  · exfalso
    have h₁₂' : ν₁ ∈ orbit c.H0 c.U ν₂ := by
      rw [orbit_eq_of_mem c h₂₁]
      exact orbit_self_mem c ν₁
    have h₁a' : ν₁ ∈ orbit c.H0 c.U a := by
      rw [orbit_eq_of_mem c ha₁]
      exact orbit_self_mem c ν₁
    have hδ₂self : scalarProduct G (inducedClassFunction c.H0 (ν₁ - ν₂))
        (inducedClassFunction c.H0 (ν₁ - ν₂)) = 2 := by
      change normSq G (inducedClassFunction c.H0 (ν₁ - ν₂)) = 2
      rw [delta_norm c h12 hH0index hν₁ hν₂ h₁₂' h₁₂.1 h₁₂.2]
      rw [theta_norm c h12 hH0index hν₁, theta_norm c h12 hH0index hν₂]
      rw [if_neg hν₁s, if_neg hν₂s]
      norm_num
    have hδ₂χ : scalarProduct G (inducedClassFunction c.H0 (ν₁ - ν₂)) χ₂₃ = 1 := by
      apply star_inj.mp
      rw [scalarProduct_star_comm]
      change scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - ν₂)) = star 1
      simpa using hχ₂
    have hth2norm : normSq G (χ₂₃ - inducedClassFunction c.H0 (ν₁ - ν₂)) = 1 := by
      unfold normSq
      rw [scalarProduct_sub_left, scalarProduct_sub_right, scalarProduct_sub_right]
      change scalarProduct G χ₂₃ χ₂₃ = 1 at hχ₁
      rw [hχ₁, hχ₂, hδ₂χ, hδ₂self]
      norm_num
    have hδ₂g : IsGeneralizedCharacter (inducedClassFunction c.H0 (ν₁ - ν₂)) := by
      exact isGeneralizedCharacter_induced c h12 (ν₁ - ν₂)
        (isGeneralizedCharacter_sub_irr hν₁ hν₂)
    have hth2g : IsGeneralizedCharacter (χ₂₃ - inducedClassFunction c.H0 (ν₁ - ν₂)) :=
      isGeneralizedCharacter_sub hχg hδ₂g
    have hth2signed : IsIrreducibleCharacter
          (χ₂₃ - inducedClassFunction c.H0 (ν₁ - ν₂)) ∨
        IsIrreducibleCharacter (-(χ₂₃ - inducedClassFunction c.H0 (ν₁ - ν₂))) := by
      rcases norm_one_signed_irreducible hth2g hth2norm with ⟨η, hη, hηeq⟩
      rcases hηeq with hηeq | hηeq
      · left
        simpa [hηeq] using hη
      · right
        simpa [hηeq] using hη
    have hδ₂apair : scalarProduct G (inducedClassFunction c.H0 (ν₁ - ν₂))
        (inducedClassFunction c.H0 (ν₁ - a)) = 1 :=
      delta_pair_same_base_eq_one c h12 hH0index hν₁ hν₂ ha h₂₁ ha₁ hν₁s
        h₁₂ h₁a h₂a
    have hth2amem : scalarProduct G (χ₂₃ - inducedClassFunction c.H0 (ν₁ - ν₂))
          (inducedClassFunction c.H0 (ν₁ - a)) = 1 ∨
        scalarProduct G (χ₂₃ - inducedClassFunction c.H0 (ν₁ - ν₂))
          (inducedClassFunction c.H0 (ν₁ - a)) = 0 ∨
        scalarProduct G (χ₂₃ - inducedClassFunction c.H0 (ν₁ - ν₂))
          (inducedClassFunction c.H0 (ν₁ - a)) = -1 := by
      exact scalarProduct_norm_one_signed_norm_three_mem hth2signed hδag hδanorm
    have hth2aneg2 : scalarProduct G (χ₂₃ - inducedClassFunction c.H0 (ν₁ - ν₂))
          (inducedClassFunction c.H0 (ν₁ - a)) = -2 := by
      rw [scalarProduct_sub_left, hm1, hδ₂apair]
      norm_num
    rcases hth2amem with h1 | h0 | hm1'
    · rw [hth2aneg2] at h1
      norm_num at h1
    · rw [hth2aneg2] at h0
      norm_num at h0
    · rw [hth2aneg2] at hm1'
      norm_num at hm1'


/-- Expanding `(φ − th2 − th3, φ' − th2 − th3)` with the orthogonality of
`th2, th3` against everything and their norm-one self-pairings. -/
private lemma scalarProduct_twice_minus_two_three (φ φ' th2 th3 : ClassFunction G)
    (hφth2 : scalarProduct G φ th2 = 0) (hφth3 : scalarProduct G φ th3 = 0)
    (hth2φ' : scalarProduct G th2 φ' = 0) (hth3φ' : scalarProduct G th3 φ' = 0)
    (hth2th3 : scalarProduct G th2 th3 = 0) (hth3th2 : scalarProduct G th3 th2 = 0)
    (hth2norm : scalarProduct G th2 th2 = 1) (hth3norm : scalarProduct G th3 th3 = 1) :
    scalarProduct G (φ - th2 - th3) (φ' - th2 - th3) =
      scalarProduct G φ φ' + 2 := by
  simp [scalarProduct_sub_left, scalarProduct_sub_right,
    hφth2, hφth3,
    hth2φ', hth3φ', hth2th3, hth3th2, hth2norm, hth3norm]
  ring


/-- Two distinct `s`-fixed members cannot both be undefined
(`(χ₂₃,δ*) = 0`): their Fact-4 decompositions would force the two extra
constituents to be negatives, contradicting the degree identities. -/
private lemma two_bad_fixed_contradiction (c : Hyp11 G) (h12 : Hyp12 c)
    (hH0index : (c.H0.subgroupOf c.H).index = 2)
    {ν₁ ν₂ ν₃ ν ν' : ClassFunction (↥c.H0)}
    (hν₁ : IsIrreducibleCharacter ν₁) (hν₂ : IsIrreducibleCharacter ν₂)
    (hν₃ : IsIrreducibleCharacter ν₃) (hν : IsIrreducibleCharacter ν)
    (hν' : IsIrreducibleCharacter ν')
    (h₂₁ : ν₂ ∈ orbit c.H0 c.U ν₁) (h₃₁ : ν₃ ∈ orbit c.H0 c.U ν₁)
    (hνmem : ν ∈ orbit c.H0 c.U ν₁) (hν'mem : ν' ∈ orbit c.H0 c.U ν₁)
    (hν₁s : conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ≠ ν₁)
    (hν₂s : conjChar c.H0 (s_normalizes_H0 c h12) ν₂ ≠ ν₂)
    (hν₃s : conjChar c.H0 (s_normalizes_H0 c h12) ν₃ ≠ ν₃)
    (hfixν : conjChar c.H0 (s_normalizes_H0 c h12) ν = ν)
    (hfixν' : conjChar c.H0 (s_normalizes_H0 c h12) ν' = ν')
    (hνν' : ν ≠ ν')
    (h₁ν : ν₁ ≠ ν ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ≠ ν)
    (h₂ν : ν₂ ≠ ν ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₂ ≠ ν)
    (h₃ν : ν₃ ≠ ν ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₃ ≠ ν)
    (h₁ν' : ν₁ ≠ ν' ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ≠ ν')
    (h₂ν' : ν₂ ≠ ν' ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₂ ≠ ν')
    (h₃ν' : ν₃ ≠ ν' ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₃ ≠ ν')
    (h₁₂ : ν₁ ≠ ν₂ ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ≠ ν₂)
    (h₁₃ : ν₁ ≠ ν₃ ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ≠ ν₃)
    (h₂₃ : ν₂ ≠ ν₃ ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₂ ≠ ν₃)
    {χ₂₃ : ClassFunction G}
    (hχsig : IsIrreducibleCharacter χ₂₃ ∨ IsIrreducibleCharacter (-χ₂₃))
    (hχg : IsGeneralizedCharacter χ₂₃) (hχ₁ : normSq G χ₂₃ = 1)
    (hχ₂ : scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - ν₂)) = 1)
    (hχ₃ : scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - ν₃)) = 1)
    (hδ₂norm : normSq G (inducedClassFunction c.H0 (ν₁ - ν₂)) = 2)
    (hδ₃norm : normSq G (inducedClassFunction c.H0 (ν₁ - ν₃)) = 2)
    (hδ₂₃pair : scalarProduct G (inducedClassFunction c.H0 (ν₁ - ν₂))
      (inducedClassFunction c.H0 (ν₁ - ν₃)) = 1)
    (hχ0ν : scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - ν)) = 0)
    (hχ0ν' : scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - ν')) = 0)
    (hδνnorm : normSq G (inducedClassFunction c.H0 (ν₁ - ν)) = 3)
    (hδν'norm : normSq G (inducedClassFunction c.H0 (ν₁ - ν')) = 3) :
    False := by
  classical
  let δ₂ : ClassFunction G := inducedClassFunction c.H0 (ν₁ - ν₂)
  let δ₃ : ClassFunction G := inducedClassFunction c.H0 (ν₁ - ν₃)
  let δν : ClassFunction G := inducedClassFunction c.H0 (ν₁ - ν)
  let δν' : ClassFunction G := inducedClassFunction c.H0 (ν₁ - ν')
  let th2 : ClassFunction G := χ₂₃ - δ₂
  let th3 : ClassFunction G := χ₂₃ - δ₃
  have hν₂₁' : ν₁ ∈ orbit c.H0 c.U ν₂ := by
    rw [orbit_eq_of_mem c h₂₁]
    exact orbit_self_mem c ν₁
  have hν₃₁' : ν₁ ∈ orbit c.H0 c.U ν₃ := by
    rw [orbit_eq_of_mem c h₃₁]
    exact orbit_self_mem c ν₁
  have hνν₁' : ν₁ ∈ orbit c.H0 c.U ν := by
    rw [orbit_eq_of_mem c hνmem]
    exact orbit_self_mem c ν₁
  have hν'ν₁' : ν₁ ∈ orbit c.H0 c.U ν' := by
    rw [orbit_eq_of_mem c hν'mem]
    exact orbit_self_mem c ν₁
  rcases delta_star_decomp_of_undefined c h12 hH0index
      hν₁ hν₂ hν₃ hν h₂₁ h₃₁ hνmem hν₁s hν₂s hν₃s
      h₁₂ h₁₃ h₁ν h₂₃ h₂ν h₃ν hχg hχ₁ hχ₂ hχ₃ hχ0ν with
    ⟨φ, hφsig, hφth2, hφth3, hφdec, hth2dν, hth3dν, hdν3⟩
  rcases delta_star_decomp_of_undefined c h12 hH0index
      hν₁ hν₂ hν₃ hν' h₂₁ h₃₁ hν'mem hν₁s hν₂s hν₃s
      h₁₂ h₁₃ h₁ν' h₂₃ h₂ν' h₃ν' hχg hχ₁ hχ₂ hχ₃ hχ0ν' with
    ⟨φ', hφ'sig, hφ'th2, hφ'th3, hφ'dec, hth2dν', hth3dν', hdν'3⟩
  have hδ₂χ : scalarProduct G δ₂ χ₂₃ = 1 := by
    apply star_inj.mp
    rw [scalarProduct_star_comm]
    change scalarProduct G χ₂₃ δ₂ = star 1
    simpa [δ₂] using hχ₂
  have hδ₃χ : scalarProduct G δ₃ χ₂₃ = 1 := by
    apply star_inj.mp
    rw [scalarProduct_star_comm]
    change scalarProduct G χ₂₃ δ₃ = star 1
    simpa [δ₃] using hχ₃
  have hδ₂self : scalarProduct G δ₂ δ₂ = 2 := by
    change normSq G δ₂ = 2
    exact hδ₂norm
  have hδ₃self : scalarProduct G δ₃ δ₃ = 2 := by
    change normSq G δ₃ = 2
    exact hδ₃norm
  have hth2norm : normSq G th2 = 1 := by
    change normSq G (χ₂₃ - δ₂) = 1
    unfold normSq
    rw [scalarProduct_sub_left, scalarProduct_sub_right, scalarProduct_sub_right]
    change scalarProduct G χ₂₃ χ₂₃ = 1 at hχ₁
    rw [hχ₁, hδ₂χ, hχ₂, hδ₂self]
    norm_num
  have hth3norm : normSq G th3 = 1 := by
    change normSq G (χ₂₃ - δ₃) = 1
    unfold normSq
    rw [scalarProduct_sub_left, scalarProduct_sub_right, scalarProduct_sub_right]
    change scalarProduct G χ₂₃ χ₂₃ = 1 at hχ₁
    rw [hχ₁, hδ₃χ, hχ₃, hδ₃self]
    norm_num
  have hth2th3 : scalarProduct G th2 th3 = 0 := by
    change scalarProduct G (χ₂₃ - δ₂) (χ₂₃ - δ₃) = 0
    rw [scalarProduct_sub_left, scalarProduct_sub_right, scalarProduct_sub_right]
    change scalarProduct G χ₂₃ χ₂₃ = 1 at hχ₁
    rw [hχ₁, hχ₃, hδ₂χ, hδ₂₃pair]
    norm_num
  have hth3th2 : scalarProduct G th3 th2 = 0 := by
    rw [← scalarProduct_star_comm th2 th3]
    simpa using hth2th3
  have hth2φ : scalarProduct G th2 φ = 0 := by
    rw [← scalarProduct_star_comm φ th2]
    simpa using hφth2
  have hth3φ : scalarProduct G th3 φ = 0 := by
    rw [← scalarProduct_star_comm φ th3]
    simpa using hφth3
  have hth2φ' : scalarProduct G th2 φ' = 0 := by
    rw [← scalarProduct_star_comm φ' th2]
    simpa using hφ'th2
  have hth3φ' : scalarProduct G th3 φ' = 0 := by
    rw [← scalarProduct_star_comm φ' th3]
    simpa using hφ'th3
  have hφδ₂ : scalarProduct G φ δ₂ = scalarProduct G φ χ₂₃ := by
    have h : scalarProduct G φ χ₂₃ - scalarProduct G φ δ₂ = 0 := by
      simpa [δ₂, scalarProduct_sub_right] using hφth2
    exact (sub_eq_zero.mp h).symm
  have hφδ₃ : scalarProduct G φ δ₃ = scalarProduct G φ χ₂₃ := by
    have h : scalarProduct G φ χ₂₃ - scalarProduct G φ δ₃ = 0 := by
      simpa [δ₃, scalarProduct_sub_right] using hφth3
    exact (sub_eq_zero.mp h).symm
  have hφ'δ₂ : scalarProduct G φ' δ₂ = scalarProduct G φ' χ₂₃ := by
    have h : scalarProduct G φ' χ₂₃ - scalarProduct G φ' δ₂ = 0 := by
      simpa [δ₂, scalarProduct_sub_right] using hφ'th2
    exact (sub_eq_zero.mp h).symm
  have hφ'δ₃ : scalarProduct G φ' δ₃ = scalarProduct G φ' χ₂₃ := by
    have h : scalarProduct G φ' χ₂₃ - scalarProduct G φ' δ₃ = 0 := by
      simpa [δ₃, scalarProduct_sub_right] using hφ'th3
    exact (sub_eq_zero.mp h).symm
  have hχχ : scalarProduct G χ₂₃ χ₂₃ = 1 := by
    change scalarProduct G χ₂₃ χ₂₃ = 1
    exact hχ₁
  have hδ₃δ₂ : scalarProduct G δ₃ δ₂ = 1 := by
    apply star_inj.mp
    rw [scalarProduct_star_comm]
    change scalarProduct G δ₂ δ₃ = star 1
    simpa using hδ₂₃pair
  have hδνν' : scalarProduct G δν δν' = 1 := by
    change scalarProduct G (inducedClassFunction c.H0 (ν₁ - ν))
        (inducedClassFunction c.H0 (ν₁ - ν')) = 1
    exact delta_pair_same_base_eq_one c h12 hH0index hν₁ hν hν'
      hνmem hν'mem hν₁s h₁ν h₁ν' ⟨hνν', by
        intro hEq
        apply hνν'
        rw [← hfixν, hEq]⟩
  have hφφ' : scalarProduct G φ φ' = -1 := by
    have hcalc : scalarProduct G δν δν' = scalarProduct G φ φ' + 2 := by
      change scalarProduct G (inducedClassFunction c.H0 (ν₁ - ν))
          (inducedClassFunction c.H0 (ν₁ - ν')) =
        scalarProduct G φ φ' + 2
      rw [hφdec, hφ'dec]
      rw [show (χ₂₃ - δ₂) = th2 by rfl, show (χ₂₃ - δ₃) = th3 by rfl]
      exact scalarProduct_twice_minus_two_three φ φ' th2 th3
        hφth2 hφth3
        hth2φ' hth3φ' hth2th3 hth3th2
        (by change scalarProduct G th2 th2 = 1; exact hth2norm)
        (by change scalarProduct G th3 th3 = 1; exact hth3norm)
    rw [hcalc] at hδνν'
    linear_combination hδνν'
  have hφ'φ : scalarProduct G φ' φ = -1 := by
    rw [← scalarProduct_star_comm φ φ']
    rw [hφφ']
    simp
  have hφnorm : normSq G φ = 1 := by
    rcases hφsig with hφ | hφ
    · change scalarProduct G φ φ = 1
      exact irreducible_scalarProduct_self hφ
    · change scalarProduct G φ φ = 1
      simpa [scalarProduct_neg_left, scalarProduct_neg_right] using
        irreducible_scalarProduct_self hφ
  have hφ'norm : normSq G φ' = 1 := by
    rcases hφ'sig with hφ' | hφ'
    · change scalarProduct G φ' φ' = 1
      exact irreducible_scalarProduct_self hφ'
    · change scalarProduct G φ' φ' = 1
      simpa [scalarProduct_neg_left, scalarProduct_neg_right] using
        irreducible_scalarProduct_self hφ'
  have hsum_norm : normSq G (φ + φ') = 0 := by
    unfold normSq
    change scalarProduct G φ φ = 1 at hφnorm
    change scalarProduct G φ' φ' = 1 at hφ'norm
    simp [scalarProduct_add_left, scalarProduct_add_right,
      hφnorm, hφ'norm, hφφ', hφ'φ]
  have hsum0 : φ + φ' = 0 := (normSq_eq_zero_iff (φ + φ')).1 hsum_norm
  have hφ'neg : φ' = -φ := by
    linear_combination hsum0
  have hδν1 : δν 1 = 0 := by
    change inducedClassFunction c.H0 (ν₁ - ν) 1 = 0
    exact inducedFromSub_one_eq c h12 (orbit_mem_degree_eq c hνmem).symm
  have hδν'1 : δν' 1 = 0 := by
    change inducedClassFunction c.H0 (ν₁ - ν') 1 = 0
    exact inducedFromSub_one_eq c h12 (orbit_mem_degree_eq c hν'mem).symm
  have hδ₂1 : δ₂ 1 = 0 := by
    change inducedClassFunction c.H0 (ν₁ - ν₂) 1 = 0
    exact inducedFromSub_one_eq c h12 (orbit_mem_degree_eq c h₂₁).symm
  have hδ₃1 : δ₃ 1 = 0 := by
    change inducedClassFunction c.H0 (ν₁ - ν₃) 1 = 0
    exact inducedFromSub_one_eq c h12 (orbit_mem_degree_eq c h₃₁).symm
  have hth21 : th2 1 = χ₂₃ 1 := by
    change (χ₂₃ - δ₂) 1 = χ₂₃ 1
    simp [hδ₂1]
  have hth31 : th3 1 = χ₂₃ 1 := by
    change (χ₂₃ - δ₃) 1 = χ₂₃ 1
    simp [hδ₃1]
  have hχ1ne : χ₂₃ 1 ≠ 0 := by
    rcases hχsig with hχ | hχ
    · exact irreducible_char_one_ne_zero hχ
    · intro h0
      have hneg : (-χ₂₃) 1 ≠ 0 := irreducible_char_one_ne_zero hχ
      exact hneg (by simpa [h0])
  have hφdeg : φ 1 = 2 * χ₂₃ 1 := by
    have h := congrFun hφdec 1
    change δν 1 = φ 1 - th2 1 - th3 1 at h
    rw [hδν1, hth21, hth31] at h
    change 0 = φ 1 - χ₂₃ 1 - χ₂₃ 1 at h
    calc
      φ 1 = (φ 1 - χ₂₃ 1 - χ₂₃ 1) + 2 * χ₂₃ 1 := by ring
      _ = 0 + 2 * χ₂₃ 1 := by rw [← h]
      _ = 2 * χ₂₃ 1 := by ring
  have hφ'deg : φ' 1 = 2 * χ₂₃ 1 := by
    have h := congrFun hφ'dec 1
    change δν' 1 = φ' 1 - th2 1 - th3 1 at h
    rw [hδν'1, hth21, hth31] at h
    change 0 = φ' 1 - χ₂₃ 1 - χ₂₃ 1 at h
    calc
      φ' 1 = (φ' 1 - χ₂₃ 1 - χ₂₃ 1) + 2 * χ₂₃ 1 := by ring
      _ = 0 + 2 * χ₂₃ 1 := by rw [← h]
      _ = 2 * χ₂₃ 1 := by ring
  have hφ'negdeg : φ' 1 = -φ 1 := by
    rw [hφ'neg]
    simp
  have hcontra : 4 * χ₂₃ 1 = 0 := by
    have h := hφ'deg
    rw [hφ'negdeg, hφdeg] at h
    have hzero : -4 * χ₂₃ 1 = 0 := by
      linear_combination h
    linear_combination -hzero
  exact (mul_ne_zero (by norm_num : (4 : ℂ) ≠ 0) hχ1ne) hcontra


/-! ## Fact 5: the multiplicity structure and `7x² ≤ |(μ−γ)*|².re` -/

/-- Fact 5 (the constituent lemma): for `μ, γ` in a `Λ`-orbit other than
`Λν` (not `s`-conjugate to it), with `δⱼ* = φ − θ̃₂ − θ̃₃` the
undefined-case decomposition, the lifts `θ̃₁, θ̃₂, θ̃₃` have the same
multiplicity in `(μ−γ)*`, and `φ` has twice that multiplicity. -/
private lemma theta_pairings_eq_of_cross_orbit (c : Hyp11 G) (h12 : Hyp12 c)
    (hH0index : (c.H0.subgroupOf c.H).index = 2)
    {ν₁ ν₂ ν₃ νⱼ μ γ : ClassFunction (↥c.H0)}
    (hν₁ : IsIrreducibleCharacter ν₁) (hν₂ : IsIrreducibleCharacter ν₂)
    (hν₃ : IsIrreducibleCharacter ν₃) (hνⱼ : IsIrreducibleCharacter νⱼ)
    (hμ : IsIrreducibleCharacter μ) (hγ : IsIrreducibleCharacter γ)
    (h₂₁ : ν₂ ∈ orbit c.H0 c.U ν₁) (h₃₁ : ν₃ ∈ orbit c.H0 c.U ν₁)
    (hⱼ₁ : νⱼ ∈ orbit c.H0 c.U ν₁) (hμγ : μ ∈ orbit c.H0 c.U γ)
    (hν₁μ : ν₁ ∉ orbit c.H0 c.U μ)
    (hν₁sμ : conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ∉ orbit c.H0 c.U μ)
    (hν₂μ : ν₂ ∉ orbit c.H0 c.U μ)
    (hν₂sμ : conjChar c.H0 (s_normalizes_H0 c h12) ν₂ ∉ orbit c.H0 c.U μ)
    (hν₃μ : ν₃ ∉ orbit c.H0 c.U μ)
    (hν₃sμ : conjChar c.H0 (s_normalizes_H0 c h12) ν₃ ∉ orbit c.H0 c.U μ)
    (hνⱼμ : νⱼ ∉ orbit c.H0 c.U μ)
    (hνⱼsμ : conjChar c.H0 (s_normalizes_H0 c h12) νⱼ ∉ orbit c.H0 c.U μ)
    (hμne : μ ≠ γ) (hμs : conjChar c.H0 (s_normalizes_H0 c h12) μ ≠ γ)
    {χ₂₃ φ : ClassFunction G}
    (hφdec : inducedClassFunction c.H0 (ν₁ - νⱼ) =
      φ - (χ₂₃ - inducedClassFunction c.H0 (ν₁ - ν₂)) -
        (χ₂₃ - inducedClassFunction c.H0 (ν₁ - ν₃))) :
    scalarProduct G (inducedClassFunction c.H0 (ν₁ - ν₂))
        (inducedClassFunction c.H0 (μ - γ)) = 0 ∧
    scalarProduct G (inducedClassFunction c.H0 (ν₁ - ν₃))
        (inducedClassFunction c.H0 (μ - γ)) = 0 ∧
    scalarProduct G χ₂₃ (inducedClassFunction c.H0 (μ - γ)) =
      scalarProduct G (χ₂₃ - inducedClassFunction c.H0 (ν₁ - ν₂))
        (inducedClassFunction c.H0 (μ - γ)) ∧
    scalarProduct G (χ₂₃ - inducedClassFunction c.H0 (ν₁ - ν₂))
        (inducedClassFunction c.H0 (μ - γ)) =
      scalarProduct G (χ₂₃ - inducedClassFunction c.H0 (ν₁ - ν₃))
        (inducedClassFunction c.H0 (μ - γ)) ∧
    scalarProduct G φ (inducedClassFunction c.H0 (μ - γ)) =
      2 * scalarProduct G (χ₂₃ - inducedClassFunction c.H0 (ν₁ - ν₂))
        (inducedClassFunction c.H0 (μ - γ)) := by
  classical
  let δ₂ : ClassFunction G := inducedClassFunction c.H0 (ν₁ - ν₂)
  let δ₃ : ClassFunction G := inducedClassFunction c.H0 (ν₁ - ν₃)
  let δⱼ : ClassFunction G := inducedClassFunction c.H0 (ν₁ - νⱼ)
  let δ : ClassFunction G := inducedClassFunction c.H0 (μ - γ)
  let th2 : ClassFunction G := χ₂₃ - δ₂
  let th3 : ClassFunction G := χ₂₃ - δ₃
  -- the reverse memberships
  have h₁₂L : ν₁ ∈ orbit c.H0 c.U ν₂ := by
    rw [orbit_eq_of_mem c h₂₁]
    exact orbit_self_mem c ν₁
  have h₁₃L : ν₁ ∈ orbit c.H0 c.U ν₃ := by
    rw [orbit_eq_of_mem c h₃₁]
    exact orbit_self_mem c ν₁
  have h₁ⱼL : ν₁ ∈ orbit c.H0 c.U νⱼ := by
    rw [orbit_eq_of_mem c hⱼ₁]
    exact orbit_self_mem c ν₁
  -- the cross-orbit non-memberships (µ's orbit = γ's orbit)
  have hν₂γ : ν₂ ∉ orbit c.H0 c.U γ := by
    rwa [orbit_eq_of_mem c hμγ] at hν₂μ
  have hν₂sγ : conjChar c.H0 (s_normalizes_H0 c h12) ν₂ ∉ orbit c.H0 c.U γ := by
    rwa [orbit_eq_of_mem c hμγ] at hν₂sμ
  have hν₃γ : ν₃ ∉ orbit c.H0 c.U γ := by
    rwa [orbit_eq_of_mem c hμγ] at hν₃μ
  have hν₃sγ : conjChar c.H0 (s_normalizes_H0 c h12) ν₃ ∉ orbit c.H0 c.U γ := by
    rwa [orbit_eq_of_mem c hμγ] at hν₃sμ
  have hνⱼγ : νⱼ ∉ orbit c.H0 c.U γ := by
    rwa [orbit_eq_of_mem c hμγ] at hνⱼμ
  have hνⱼsγ : conjChar c.H0 (s_normalizes_H0 c h12) νⱼ ∉ orbit c.H0 c.U γ := by
    rwa [orbit_eq_of_mem c hμγ] at hνⱼsμ
  -- the cross-orbit orthogonality of the δ*'s
  have hδ₂δ : scalarProduct G δ₂ δ = 0 := by
    change scalarProduct G (inducedClassFunction c.H0 (ν₁ - ν₂)) δ = 0
    rw [delta_pair_scalar c h12 hν₂ hγ h₁₂L hμγ]
    change scalarProduct (↥c.H)
      (inducedFromSub (h12.H0_normal_in_H).1 ν₁ -
        inducedFromSub (h12.H0_normal_in_H).1 ν₂)
      (inducedFromSub (h12.H0_normal_in_H).1 μ -
        inducedFromSub (h12.H0_normal_in_H).1 γ) = 0
    exact theta_pair_orth c h12 hH0index hν₂ hγ h₁₂L hμγ hν₂γ hν₂sγ
  have hδ₃δ : scalarProduct G δ₃ δ = 0 := by
    change scalarProduct G (inducedClassFunction c.H0 (ν₁ - ν₃)) δ = 0
    rw [delta_pair_scalar c h12 hν₃ hγ h₁₃L hμγ]
    change scalarProduct (↥c.H)
      (inducedFromSub (h12.H0_normal_in_H).1 ν₁ -
        inducedFromSub (h12.H0_normal_in_H).1 ν₃)
      (inducedFromSub (h12.H0_normal_in_H).1 μ -
        inducedFromSub (h12.H0_normal_in_H).1 γ) = 0
    exact theta_pair_orth c h12 hH0index hν₃ hγ h₁₃L hμγ hν₃γ hν₃sγ
  have hδⱼδ : scalarProduct G δⱼ δ = 0 := by
    change scalarProduct G (inducedClassFunction c.H0 (ν₁ - νⱼ)) δ = 0
    rw [delta_pair_scalar c h12 hνⱼ hγ h₁ⱼL hμγ]
    change scalarProduct (↥c.H)
      (inducedFromSub (h12.H0_normal_in_H).1 ν₁ -
        inducedFromSub (h12.H0_normal_in_H).1 νⱼ)
      (inducedFromSub (h12.H0_normal_in_H).1 μ -
        inducedFromSub (h12.H0_normal_in_H).1 γ) = 0
    exact theta_pair_orth c h12 hH0index hνⱼ hγ h₁ⱼL hμγ hνⱼγ hνⱼsγ
  -- `(θ̃₁, δ) = (θ̃₂, δ)` and `(θ̃₂, δ) = (θ̃₃, δ)`
  have hm₁₂ : scalarProduct G χ₂₃ δ - scalarProduct G th2 δ = 0 := by
    have hdiff : χ₂₃ - (χ₂₃ - δ₂) = δ₂ := by
      change χ₂₃ - (χ₂₃ - inducedClassFunction c.H0 (ν₁ - ν₂)) =
        inducedClassFunction c.H0 (ν₁ - ν₂)
      ring
    have hsp : scalarProduct G (χ₂₃ - (χ₂₃ - δ₂)) δ = 0 := by
      rw [hdiff]
      exact hδ₂δ
    rwa [scalarProduct_sub_left] at hsp
  have hm₂₃ : scalarProduct G th2 δ - scalarProduct G th3 δ = 0 := by
    have hdiff : th2 - th3 = δ₃ - δ₂ := by
      change (χ₂₃ - δ₂) - (χ₂₃ - δ₃) = δ₃ - δ₂
      ring
    have hsp : scalarProduct G (th2 - th3) δ = 0 := by
      rw [hdiff]
      rw [scalarProduct_sub_left]
      simp [hδ₃δ, hδ₂δ]
    rwa [scalarProduct_sub_left] at hsp
  -- `(φ, δ) = 2(θ̃₂, δ)` from `δⱼ = φ − θ̃₂ − θ̃₃`
  have hmφ : scalarProduct G φ δ = 2 * scalarProduct G th2 δ := by
    have hsp : scalarProduct G (φ - th2 - th3) δ = 0 := by
      change scalarProduct G (φ - (χ₂₃ - δ₂) - (χ₂₃ - δ₃)) δ = 0
      rw [← hφdec]
      exact hδⱼδ
    rw [scalarProduct_sub_left, scalarProduct_sub_left] at hsp
    have h23 : scalarProduct G th3 δ = scalarProduct G th2 δ := (sub_eq_zero.mp hm₂₃).symm
    have hφδ : scalarProduct G φ δ =
        scalarProduct G th2 δ + scalarProduct G th3 δ := by
      have hsp1 : scalarProduct G φ δ - scalarProduct G th2 δ = scalarProduct G th3 δ :=
        sub_eq_zero.mp hsp
      rw [← sub_eq_iff_eq_add']
      exact hsp1
    rw [hφδ, h23]
    ring
  -- assemble
  change scalarProduct G δ₂ δ = 0 ∧ scalarProduct G δ₃ δ = 0 ∧
    scalarProduct G χ₂₃ δ = scalarProduct G th2 δ ∧
    scalarProduct G th2 δ = scalarProduct G th3 δ ∧
    scalarProduct G φ δ = 2 * scalarProduct G th2 δ
  exact ⟨hδ₂δ, hδ₃δ, sub_eq_zero.mp hm₁₂, sub_eq_zero.mp hm₂₃, hmφ⟩


/-- The norm-inequality (Fact 5): for pairwise orthogonal norm-one signed
characters `th1, th2, th3, φ` with the integer multiplicities
`(thi, δ) = x` and `(φ, δ) = 2x`: `7x² ≤ (normSq G δ).re` (the projection
onto the span of the four constituents). -/
private lemma normSq_re_ge_seven_sq {G : Type u} [Group G] [Fintype G]
    (δ : ClassFunction G) (x : ℤ) {th1 th2 th3 φ : ClassFunction G}
    (hth1 : scalarProduct G th1 th1 = 1) (hth2 : scalarProduct G th2 th2 = 1)
    (hth3 : scalarProduct G th3 th3 = 1) (hφ : scalarProduct G φ φ = 1)
    (hth1th2 : scalarProduct G th1 th2 = 0) (hth1th3 : scalarProduct G th1 th3 = 0)
    (hth1φ : scalarProduct G th1 φ = 0)
    (hth2th3 : scalarProduct G th2 th3 = 0) (hth2φ : scalarProduct G th2 φ = 0)
    (hth3φ : scalarProduct G th3 φ = 0)
    (hm₁ : scalarProduct G th1 δ = (x : ℂ)) (hm₂ : scalarProduct G th2 δ = (x : ℂ))
    (hm₃ : scalarProduct G th3 δ = (x : ℂ))
    (hmφ : scalarProduct G φ δ = (2 * x : ℂ)) :
    7 * (x : ℝ)^2 ≤ (normSq G δ).re := by
  classical
  let proj : ClassFunction G := (x : ℂ) • (th1 + th2 + th3) + (2 * x : ℂ) • φ
  let ψ : ClassFunction G := δ - proj
  -- the star-flipped orthogonality pairings
  have hth2th1 : scalarProduct G th2 th1 = 0 := by
    apply star_inj.mp
    rw [scalarProduct_star_comm]
    change scalarProduct G th1 th2 = star 0
    simpa using hth1th2
  have hth3th1 : scalarProduct G th3 th1 = 0 := by
    apply star_inj.mp
    rw [scalarProduct_star_comm]
    change scalarProduct G th1 th3 = star 0
    simpa using hth1th3
  have hth3th2 : scalarProduct G th3 th2 = 0 := by
    apply star_inj.mp
    rw [scalarProduct_star_comm]
    change scalarProduct G th2 th3 = star 0
    simpa using hth2th3
  have hφth1 : scalarProduct G φ th1 = 0 := by
    apply star_inj.mp
    rw [scalarProduct_star_comm]
    change scalarProduct G th1 φ = star 0
    simpa using hth1φ
  have hφth2 : scalarProduct G φ th2 = 0 := by
    apply star_inj.mp
    rw [scalarProduct_star_comm]
    change scalarProduct G th2 φ = star 0
    simpa using hth2φ
  have hφth3 : scalarProduct G φ th3 = 0 := by
    apply star_inj.mp
    rw [scalarProduct_star_comm]
    change scalarProduct G th3 φ = star 0
    simpa using hth3φ
  -- the star of the multiplicities: `(δ, thi) = (x : ℂ)`, `(δ, φ) = (2x : ℂ)`
  have hδth1 : scalarProduct G δ th1 = (x : ℂ) := by
    apply star_inj.mp
    rw [scalarProduct_star_comm]
    change scalarProduct G th1 δ = star (x : ℂ)
    simpa using hm₁
  have hδth2 : scalarProduct G δ th2 = (x : ℂ) := by
    apply star_inj.mp
    rw [scalarProduct_star_comm]
    change scalarProduct G th2 δ = star (x : ℂ)
    simpa using hm₂
  have hδth3 : scalarProduct G δ th3 = (x : ℂ) := by
    apply star_inj.mp
    rw [scalarProduct_star_comm]
    change scalarProduct G th3 δ = star (x : ℂ)
    simpa using hm₃
  have hδφ : scalarProduct G δ φ = (2 * x : ℂ) := by
    apply star_inj.mp
    rw [scalarProduct_star_comm]
    change scalarProduct G φ δ = star (2 * x : ℂ)
    simpa using hmφ
  -- `(proj, proj) = (δ, proj) = 7x²`
  have hproj : normSq G proj = (7 * (x : ℤ) * x : ℂ) := by
    unfold proj
    unfold normSq
    simp [scalarProduct_add_left, scalarProduct_add_right, scalarProduct_smul_left,
      scalarProduct_smul_right, hth1, hth2, hth3, hφ, hth1th2, hth1th3, hth1φ,
      hth2th3, hth2φ, hth3φ, hth2th1, hth3th1, hth3th2, hφth1, hφth2, hφth3]
    ring_nf
  have hδproj : scalarProduct G δ proj = (7 * (x : ℤ) * x : ℂ) := by
    unfold proj
    simp [scalarProduct_add_right, scalarProduct_smul_right, hδth1, hδth2, hδth3, hδφ]
    ring_nf
  have hψproj : scalarProduct G ψ proj = 0 := by
    unfold ψ
    rw [scalarProduct_sub_left]
    change scalarProduct G δ proj - normSq G proj = 0
    rw [hδproj, hproj]
    ring
  have hprojψ : scalarProduct G proj ψ = 0 := by
    apply star_inj.mp
    rw [scalarProduct_star_comm]
    change scalarProduct G ψ proj = star 0
    simpa using hψproj
  -- `|δ|² = |ψ|² + |proj|²` (the orthogonality of the projection)
  have hnorm : normSq G δ = normSq G ψ + normSq G proj := by
    have hδψ : δ = ψ + proj := by
      unfold ψ
      ring
    rw [hδψ]
    unfold normSq
    change scalarProduct G (ψ + proj) (ψ + proj) =
      scalarProduct G ψ ψ + scalarProduct G proj proj
    simp [scalarProduct_add_left, scalarProduct_add_right, hψproj, hprojψ]
  have hre : (normSq G proj).re ≤ (normSq G δ).re := by
    rw [hnorm]
    simp only [Complex.add_re]
    nlinarith [normSq_nonneg ψ]
  have hprojre : (normSq G proj).re = (7 * (x : ℤ) * x : ℝ) := by
    rw [hproj]
    norm_num
  calc
    7 * (x : ℝ)^2 ≤ (7 * (x : ℤ) * x : ℝ) := by
      ring_nf
      exact le_rfl
    _ = (normSq G proj).re := hprojre.symm
    _ ≤ (normSq G δ).re := hre


/-- The upper bound (Fact 5): `(normSq G (μ−γ)*).re ≤ 4` for distinct
non-`s`-conjugate orbit members (from `delta_norm` + `theta_norm`, each
H-side norm 1 or 2). -/
private lemma delta_star_re_le_four (c : Hyp11 G) (h12 : Hyp12 c)
    (hH0index : (c.H0.subgroupOf c.H).index = 2)
    {μ γ : ClassFunction (↥c.H0)} (hμ : IsIrreducibleCharacter μ)
    (hγ : IsIrreducibleCharacter γ) (hμγ : μ ∈ orbit c.H0 c.U γ)
    (hμne : μ ≠ γ) (hμs : conjChar c.H0 (s_normalizes_H0 c h12) μ ≠ γ) :
    (normSq G (inducedClassFunction c.H0 (μ - γ))).re ≤ 4 := by
  classical
  have hnorm : normSq G (inducedClassFunction c.H0 (μ - γ)) =
      normSq (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 μ) +
        normSq (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 γ) :=
    delta_norm c h12 hH0index hμ hγ hμγ hμne hμs
  have hθμ : (normSq (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 μ)).re ≤ 2 := by
    rw [theta_norm c h12 hH0index hμ]
    by_cases h : conjChar c.H0 (s_normalizes_H0 c h12) μ = μ
    · simp [h]
    · simp [h]
  have hθγ : (normSq (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 γ)).re ≤ 2 := by
    rw [theta_norm c h12 hH0index hγ]
    by_cases h : conjChar c.H0 (s_normalizes_H0 c h12) γ = γ
    · simp [h]
    · simp [h]
  rw [hnorm]
  simp only [Complex.add_re]
  nlinarith

/-- `x = 0` from `7x² ≤ 4` for an integer `x`. -/
private lemma int_eq_zero_of_seven_sq_le {x : ℤ} (h : 7 * (x : ℝ)^2 ≤ 4) : x = 0 := by
  by_contra hx
  have hsq : 0 < x ^ 2 := sq_pos_of_ne_zero hx
  have hx2ℤ : (1 : ℤ) ≤ x ^ 2 := by omega
  have hx2 : (1 : ℝ) ≤ (x : ℝ)^2 := by exact_mod_cast hx2ℤ
  nlinarith


/-- Fact 5 (the multiplicity-zero conclusion): for `μ, γ` in another orbit
and pairwise orthogonal norm-one signed lifts with the integer
multiplicities `(θ̃ᵢ, δ) = x`, `(φ, δ) = 2x`: `7x² ≤ (normSq G δ).re ≤ 4`
forces `x = 0`, so all four lifts are orthogonal to `(μ−γ)*`. -/
private lemma multiplicity_zero_of_cross_orbit (c : Hyp11 G) (h12 : Hyp12 c)
    (hH0index : (c.H0.subgroupOf c.H).index = 2)
    {μ γ : ClassFunction (↥c.H0)} (hμ : IsIrreducibleCharacter μ)
    (hγ : IsIrreducibleCharacter γ) (hμγ : μ ∈ orbit c.H0 c.U γ)
    (hμne : μ ≠ γ) (hμs : conjChar c.H0 (s_normalizes_H0 c h12) μ ≠ γ)
    {th1 th2 th3 φ : ClassFunction G} {x : ℤ}
    (hth1 : scalarProduct G th1 th1 = 1) (hth2 : scalarProduct G th2 th2 = 1)
    (hth3 : scalarProduct G th3 th3 = 1) (hφ : scalarProduct G φ φ = 1)
    (hth1th2 : scalarProduct G th1 th2 = 0) (hth1th3 : scalarProduct G th1 th3 = 0)
    (hth1φ : scalarProduct G th1 φ = 0)
    (hth2th3 : scalarProduct G th2 th3 = 0) (hth2φ : scalarProduct G th2 φ = 0)
    (hth3φ : scalarProduct G th3 φ = 0)
    (hm₁ : scalarProduct G th1 (inducedClassFunction c.H0 (μ - γ)) = (x : ℂ))
    (hm₂ : scalarProduct G th2 (inducedClassFunction c.H0 (μ - γ)) = (x : ℂ))
    (hm₃ : scalarProduct G th3 (inducedClassFunction c.H0 (μ - γ)) = (x : ℂ))
    (hmφ : scalarProduct G φ (inducedClassFunction c.H0 (μ - γ)) = (2 * x : ℂ)) :
    scalarProduct G th1 (inducedClassFunction c.H0 (μ - γ)) = 0 ∧
    scalarProduct G th2 (inducedClassFunction c.H0 (μ - γ)) = 0 ∧
    scalarProduct G th3 (inducedClassFunction c.H0 (μ - γ)) = 0 ∧
    scalarProduct G φ (inducedClassFunction c.H0 (μ - γ)) = 0 := by
  classical
  have hlow : 7 * (x : ℝ)^2 ≤
      (normSq G (inducedClassFunction c.H0 (μ - γ))).re :=
    normSq_re_ge_seven_sq (inducedClassFunction c.H0 (μ - γ)) x
      hth1 hth2 hth3 hφ hth1th2 hth1th3 hth1φ hth2th3 hth2φ hth3φ hm₁ hm₂ hm₃ hmφ
  have hup : (normSq G (inducedClassFunction c.H0 (μ - γ))).re ≤ 4 :=
    delta_star_re_le_four c h12 hH0index hμ hγ hμγ hμne hμs
  have hx0 : x = 0 := int_eq_zero_of_seven_sq_le (by nlinarith)
  rw [hm₁, hm₂, hm₃, hmφ, hx0]
  simp

/-- Multiplicities against a signed irreducible are integers. -/
private lemma signed_multiplicity_int {G : Type u} [Group G] [Fintype G]
    {χ δ : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ ∨ IsIrreducibleCharacter (-χ))
    (hδ : IsGeneralizedCharacter δ) :
    ∃ z : ℤ, scalarProduct G χ δ = (z : ℂ) := by
  rcases hχ with hχ | hχneg
  · exact multiplicity_int hχ δ hδ
  · rcases multiplicity_int hχneg δ hδ with ⟨z, hz⟩
    refine ⟨-z, ?_⟩
    rw [← neg_neg χ, scalarProduct_neg_left, hz]
    simp

/-- The cross-orbit coefficient-zero step of the undefined fixed-member
contradiction: for `μ, γ` in another `Λ`-orbit (not `s`-conjugate to the
`ν₁`-orbit), the lifts `θ̃₂ = χ₂₃−δ₂*` and `θ̃₃ = χ₂₃−δ₃*` are orthogonal to
`(μ−γ)*`.  This is Fact 5 (`theta_pairings_eq_of_cross_orbit` +
`multiplicity_zero_of_cross_orbit`) instantiated with the signed-integer
multiplicity of `θ̃₂`. -/
private lemma cross_orbit_coeff_zero_of_undefined (c : Hyp11 G) (h12 : Hyp12 c)
    (hH0index : (c.H0.subgroupOf c.H).index = 2)
    {ν₁ ν₂ ν₃ νⱼ μ γ : ClassFunction (↥c.H0)}
    (hν₁ : IsIrreducibleCharacter ν₁) (hν₂ : IsIrreducibleCharacter ν₂)
    (hν₃ : IsIrreducibleCharacter ν₃) (hνⱼ : IsIrreducibleCharacter νⱼ)
    (hμ : IsIrreducibleCharacter μ) (hγ : IsIrreducibleCharacter γ)
    (h₂₁ : ν₂ ∈ orbit c.H0 c.U ν₁) (h₃₁ : ν₃ ∈ orbit c.H0 c.U ν₁)
    (hⱼ₁ : νⱼ ∈ orbit c.H0 c.U ν₁) (hμγ : μ ∈ orbit c.H0 c.U γ)
    (hν₁s : conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ≠ ν₁)
    (hν₂s : conjChar c.H0 (s_normalizes_H0 c h12) ν₂ ≠ ν₂)
    (hν₃s : conjChar c.H0 (s_normalizes_H0 c h12) ν₃ ≠ ν₃)
    (h₁₂ : ν₁ ≠ ν₂ ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ≠ ν₂)
    (h₁₃ : ν₁ ≠ ν₃ ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ≠ ν₃)
    (h₁ⱼ : ν₁ ≠ νⱼ ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ≠ νⱼ)
    (h₂₃ : ν₂ ≠ ν₃ ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₂ ≠ ν₃)
    (h₂ⱼ : ν₂ ≠ νⱼ ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₂ ≠ νⱼ)
    (h₃ⱼ : ν₃ ≠ νⱼ ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₃ ≠ νⱼ)
    (hν₁μ : ν₁ ∉ orbit c.H0 c.U μ)
    (hν₁sμ : conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ∉ orbit c.H0 c.U μ)
    (hν₂μ : ν₂ ∉ orbit c.H0 c.U μ)
    (hν₂sμ : conjChar c.H0 (s_normalizes_H0 c h12) ν₂ ∉ orbit c.H0 c.U μ)
    (hν₃μ : ν₃ ∉ orbit c.H0 c.U μ)
    (hν₃sμ : conjChar c.H0 (s_normalizes_H0 c h12) ν₃ ∉ orbit c.H0 c.U μ)
    (hνⱼμ : νⱼ ∉ orbit c.H0 c.U μ)
    (hνⱼsμ : conjChar c.H0 (s_normalizes_H0 c h12) νⱼ ∉ orbit c.H0 c.U μ)
    (hμne : μ ≠ γ) (hμs : conjChar c.H0 (s_normalizes_H0 c h12) μ ≠ γ)
    {χ₂₃ : ClassFunction G}
    (hχsig : IsIrreducibleCharacter χ₂₃ ∨ IsIrreducibleCharacter (-χ₂₃))
    (hχg : IsGeneralizedCharacter χ₂₃) (hχ₁ : normSq G χ₂₃ = 1)
    (hχ₂ : scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - ν₂)) = 1)
    (hχ₃ : scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - ν₃)) = 1)
    (hχj0 : scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - νⱼ)) = 0)
    (hδⱼnorm : normSq G (inducedClassFunction c.H0 (ν₁ - νⱼ)) = 3) :
    scalarProduct G (χ₂₃ - inducedClassFunction c.H0 (ν₁ - ν₂))
        (inducedClassFunction c.H0 (μ - γ)) = 0 ∧
    scalarProduct G (χ₂₃ - inducedClassFunction c.H0 (ν₁ - ν₃))
        (inducedClassFunction c.H0 (μ - γ)) = 0 := by
  classical
  let δ₂ : ClassFunction G := inducedClassFunction c.H0 (ν₁ - ν₂)
  let δ₃ : ClassFunction G := inducedClassFunction c.H0 (ν₁ - ν₃)
  let δj : ClassFunction G := inducedClassFunction c.H0 (ν₁ - νⱼ)
  let δ : ClassFunction G := inducedClassFunction c.H0 (μ - γ)
  let th2 : ClassFunction G := χ₂₃ - δ₂
  let th3 : ClassFunction G := χ₂₃ - δ₃
  have hδ₂g : IsGeneralizedCharacter δ₂ := by
    change IsGeneralizedCharacter (inducedClassFunction c.H0 (ν₁ - ν₂))
    exact isGeneralizedCharacter_induced c h12 (ν₁ - ν₂)
      (isGeneralizedCharacter_sub_irr hν₁ hν₂)
  have hδ₃g : IsGeneralizedCharacter δ₃ := by
    change IsGeneralizedCharacter (inducedClassFunction c.H0 (ν₁ - ν₃))
    exact isGeneralizedCharacter_induced c h12 (ν₁ - ν₃)
      (isGeneralizedCharacter_sub_irr hν₁ hν₃)
  have hδⱼg : IsGeneralizedCharacter δj := by
    change IsGeneralizedCharacter (inducedClassFunction c.H0 (ν₁ - νⱼ))
    exact isGeneralizedCharacter_induced c h12 (ν₁ - νⱼ)
      (isGeneralizedCharacter_sub_irr hν₁ hνⱼ)
  have hδg : IsGeneralizedCharacter δ := by
    change IsGeneralizedCharacter (inducedClassFunction c.H0 (μ - γ))
    exact isGeneralizedCharacter_induced c h12 (μ - γ)
      (isGeneralizedCharacter_sub_irr hμ hγ)
  rcases delta_star_decomp_of_undefined c h12 hH0index hν₁ hν₂ hν₃ hνⱼ
      h₂₁ h₃₁ hⱼ₁ hν₁s hν₂s hν₃s h₁₂ h₁₃ h₁ⱼ h₂₃ h₂ⱼ h₃ⱼ
      hχg hχ₁ hχ₂ hχ₃ hχj0 with
    ⟨φ, hφsig, hφth2, hφth3, hφdec, hth2dj, hth3dj, hdj3⟩
  have hth2g : IsGeneralizedCharacter th2 := by
    change IsGeneralizedCharacter (χ₂₃ - δ₂)
    exact isGeneralizedCharacter_sub hχg hδ₂g
  have hth3g : IsGeneralizedCharacter th3 := by
    change IsGeneralizedCharacter (χ₂₃ - δ₃)
    exact isGeneralizedCharacter_sub hχg hδ₃g
  have hδ₂χ : scalarProduct G δ₂ χ₂₃ = 1 := by
    apply star_inj.mp
    rw [scalarProduct_star_comm]
    change scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - ν₂)) = star 1
    simpa using hχ₂
  have hδ₃χ : scalarProduct G δ₃ χ₂₃ = 1 := by
    apply star_inj.mp
    rw [scalarProduct_star_comm]
    change scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - ν₃)) = star 1
    simpa using hχ₃
  have hδ₂₃pair : scalarProduct G δ₂ δ₃ = 1 := by
    have h₁₂L : ν₁ ∈ orbit c.H0 c.U ν₂ := by
      rw [orbit_eq_of_mem c h₂₁]
      exact orbit_self_mem c ν₁
    have h₁₃L : ν₁ ∈ orbit c.H0 c.U ν₃ := by
      rw [orbit_eq_of_mem c h₃₁]
      exact orbit_self_mem c ν₁
    have hsp := delta_pair_scalar (ν₁ := ν₂) (ν₂ := ν₃) (μ₁ := ν₁) (μ₂ := ν₁)
      c h12 hν₂ hν₃ h₁₂L h₁₃L
    change scalarProduct G δ₂ δ₃ = 1
    rw [show δ₂ = -inducedClassFunction c.H0 (ν₂ - ν₁) by
      unfold δ₂
      rw [show ν₁ - ν₂ = -(ν₂ - ν₁) by ring]
      rw [inducedClassFunction_neg]]
    rw [show δ₃ = -inducedClassFunction c.H0 (ν₃ - ν₁) by
      unfold δ₃
      rw [show ν₁ - ν₃ = -(ν₃ - ν₁) by ring]
      rw [inducedClassFunction_neg]]
    have hsp' : scalarProduct G (inducedClassFunction c.H0 (ν₂ - ν₁))
        (inducedClassFunction c.H0 (ν₃ - ν₁)) =
        scalarProduct (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν₁ -
          inducedFromSub (h12.H0_normal_in_H).1 ν₂)
          (inducedFromSub (h12.H0_normal_in_H).1 ν₁ -
            inducedFromSub (h12.H0_normal_in_H).1 ν₃) := by
      simpa [show inducedClassFunction c.H0 (ν₂ - ν₁) =
          -inducedClassFunction c.H0 (ν₁ - ν₂) by
            rw [show ν₂ - ν₁ = -(ν₁ - ν₂) by ring]
            rw [inducedClassFunction_neg],
        show inducedClassFunction c.H0 (ν₃ - ν₁) =
          -inducedClassFunction c.H0 (ν₁ - ν₃) by
            rw [show ν₃ - ν₁ = -(ν₁ - ν₃) by ring]
            rw [inducedClassFunction_neg],
        scalarProduct_neg_left, scalarProduct_neg_right] using hsp
    rw [scalarProduct_neg_left, scalarProduct_neg_right]
    rw [hsp']
    simp
    change scalarProduct (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν₁ -
        inducedFromSub (h12.H0_normal_in_H).1 ν₂)
      (inducedFromSub (h12.H0_normal_in_H).1 ν₁ -
        inducedFromSub (h12.H0_normal_in_H).1 ν₃) = 1
    have hθ₁₁ : scalarProduct (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν₁)
        (inducedFromSub (h12.H0_normal_in_H).1 ν₁) = 1 := by
      change normSq (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν₁) = 1
      rw [theta_norm c h12 hH0index hν₁, if_neg hν₁s]
    have hθ₁₂ : scalarProduct (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν₁)
        (inducedFromSub (h12.H0_normal_in_H).1 ν₂) = 0 :=
      theta_pair_scalar_zero c h12 hH0index hν₁ hν₂ h₁₂.1 h₁₂.2
    have hθ₂₁ : scalarProduct (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν₂)
        (inducedFromSub (h12.H0_normal_in_H).1 ν₁) = 0 := by
      exact theta_pair_scalar_zero c h12 hH0index hν₂ hν₁ h₁₂.1.symm (by
        intro hEq
        apply h₁₂.2
        have h := congrArg (conjChar c.H0 (s_normalizes_H0 c h12)) hEq
        rw [conjChar_conjChar c h12 ν₂] at h
        exact h.symm)
    have hθ₁₃ : scalarProduct (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν₁)
        (inducedFromSub (h12.H0_normal_in_H).1 ν₃) = 0 :=
      theta_pair_scalar_zero c h12 hH0index hν₁ hν₃ h₁₃.1 h₁₃.2
    have hθ₂₃ : scalarProduct (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν₂)
        (inducedFromSub (h12.H0_normal_in_H).1 ν₃) = 0 :=
      theta_pair_scalar_zero c h12 hH0index hν₂ hν₃ h₂₃.1 h₂₃.2
    rw [scalarProduct_sub_left, scalarProduct_sub_right, scalarProduct_sub_right]
    simp [hθ₁₁, hθ₁₂, hθ₂₁, hθ₁₃, hθ₂₃]
  have hth2norm : scalarProduct G th2 th2 = 1 := by
    change scalarProduct G (χ₂₃ - δ₂) (χ₂₃ - δ₂) = 1
    rw [scalarProduct_sub_left, scalarProduct_sub_right, scalarProduct_sub_right]
    change scalarProduct G χ₂₃ χ₂₃ = 1 at hχ₁
    have hδ₂self : scalarProduct G δ₂ δ₂ = 2 := by
      change normSq G δ₂ = 2
      have h₁₂L : ν₁ ∈ orbit c.H0 c.U ν₂ := by
        rw [orbit_eq_of_mem c h₂₁]
        exact orbit_self_mem c ν₁
      rw [delta_norm c h12 hH0index hν₁ hν₂ h₁₂L h₁₂.1 h₁₂.2]
      rw [theta_norm c h12 hH0index hν₁, theta_norm c h12 hH0index hν₂]
      rw [if_neg hν₁s, if_neg hν₂s]
      norm_num
    rw [hχ₁, hχ₂, hδ₂χ, hδ₂self]
    norm_num
  have hth3norm : scalarProduct G th3 th3 = 1 := by
    change scalarProduct G (χ₂₃ - δ₃) (χ₂₃ - δ₃) = 1
    rw [scalarProduct_sub_left, scalarProduct_sub_right, scalarProduct_sub_right]
    change scalarProduct G χ₂₃ χ₂₃ = 1 at hχ₁
    have hδ₃self : scalarProduct G δ₃ δ₃ = 2 := by
      change normSq G δ₃ = 2
      have h₁₃L : ν₁ ∈ orbit c.H0 c.U ν₃ := by
        rw [orbit_eq_of_mem c h₃₁]
        exact orbit_self_mem c ν₁
      rw [delta_norm c h12 hH0index hν₁ hν₃ h₁₃L h₁₃.1 h₁₃.2]
      rw [theta_norm c h12 hH0index hν₁, theta_norm c h12 hH0index hν₃]
      rw [if_neg hν₁s, if_neg hν₃s]
      norm_num
    rw [hχ₁, hχ₃, hδ₃χ, hδ₃self]
    norm_num
  have hφnorm : scalarProduct G φ φ = 1 := by
    rcases hφsig with hφ | hφneg
    · change scalarProduct G φ φ = 1
      exact irreducible_scalarProduct_self hφ
    · change scalarProduct G φ φ = 1
      simpa [scalarProduct_neg_left, scalarProduct_neg_right] using
        irreducible_scalarProduct_self hφneg
  have hth1th2 : scalarProduct G χ₂₃ th2 = 0 := by
    change scalarProduct G χ₂₃ (χ₂₃ - δ₂) = 0
    rw [scalarProduct_sub_right]
    change scalarProduct G χ₂₃ χ₂₃ = 1 at hχ₁
    rw [hχ₁, hχ₂]
    norm_num
  have hth1th3 : scalarProduct G χ₂₃ th3 = 0 := by
    change scalarProduct G χ₂₃ (χ₂₃ - δ₃) = 0
    rw [scalarProduct_sub_right]
    change scalarProduct G χ₂₃ χ₂₃ = 1 at hχ₁
    rw [hχ₁, hχ₃]
    norm_num
  have hth2th3 : scalarProduct G th2 th3 = 0 := by
    change scalarProduct G (χ₂₃ - δ₂) (χ₂₃ - δ₃) = 0
    rw [scalarProduct_sub_left, scalarProduct_sub_right, scalarProduct_sub_right]
    change scalarProduct G χ₂₃ χ₂₃ = 1 at hχ₁
    rw [hχ₁, hχ₃, hδ₂χ, hδ₂₃pair]
    norm_num
  have hth2φ : scalarProduct G th2 φ = 0 := by
    rw [← scalarProduct_star_comm]
    rw [show scalarProduct G φ th2 = 0 by simpa [th2, δ₂] using hφth2]
    simp
  have hth3φ : scalarProduct G th3 φ = 0 := by
    rw [← scalarProduct_star_comm]
    rw [show scalarProduct G φ th3 = 0 by simpa [th3, δ₃] using hφth3]
    simp
  have hth1φ : scalarProduct G χ₂₃ φ = 0 := by
    have hφdef : φ = δj + th2 + th3 := by
      dsimp [δj, δ₂, δ₃, th2, th3]
      rw [hφdec]
      ring
    rw [hφdef]
    rw [scalarProduct_add_right, scalarProduct_add_right]
    change scalarProduct G χ₂₃ δj + scalarProduct G χ₂₃ th2 +
      scalarProduct G χ₂₃ th3 = 0
    dsimp [δj]
    rw [hχj0, hth1th2, hth1th3]
    norm_num
  have hth2sig : IsIrreducibleCharacter th2 ∨ IsIrreducibleCharacter (-th2) := by
    rcases norm_one_signed_irreducible hth2g hth2norm with ⟨η, hη, hcase⟩
    rcases hcase with hcase | hcase
    · left
      simpa [hcase] using hη
    · right
      simpa [hcase] using hη
  rcases signed_multiplicity_int hth2sig hδg with ⟨x, hx⟩
  have hp := theta_pairings_eq_of_cross_orbit c h12 hH0index
    hν₁ hν₂ hν₃ hνⱼ hμ hγ h₂₁ h₃₁ hⱼ₁ hμγ
    hν₁μ hν₁sμ hν₂μ hν₂sμ hν₃μ hν₃sμ hνⱼμ hνⱼsμ hμne hμs hφdec
  have hm₂ : scalarProduct G th2 δ = (x : ℂ) := by
    change scalarProduct G (χ₂₃ - δ₂) (inducedClassFunction c.H0 (μ - γ)) = (x : ℂ)
    exact hx
  have hm₁ : scalarProduct G χ₂₃ δ = (x : ℂ) := by
    change scalarProduct G χ₂₃ (inducedClassFunction c.H0 (μ - γ)) = (x : ℂ)
    rw [hp.2.2.1]
    simpa [th2, δ₂] using hm₂
  have hm₃ : scalarProduct G th3 δ = (x : ℂ) := by
    rw [← hp.2.2.2.1]
    simpa [th2, δ₂] using hm₂
  have hmφ : scalarProduct G φ δ = (2 * x : ℂ) := by
    change scalarProduct G φ (inducedClassFunction c.H0 (μ - γ)) = (2 * x : ℂ)
    rw [hp.2.2.2.2]
    simpa [th2, δ₂] using hm₂
  rcases multiplicity_zero_of_cross_orbit c h12 hH0index hμ hγ hμγ hμne hμs
    hχ₁ hth2norm hth3norm hφnorm
    hth1th2 hth1th3 hth1φ hth2th3 hth2φ hth3φ
    hm₁ hm₂ hm₃ hmφ with ⟨_, hth2δ0, hth3δ0, _⟩
  constructor
  · change scalarProduct G (χ₂₃ - δ₂) (inducedClassFunction c.H0 (μ - γ)) = 0
    exact hth2δ0
  · change scalarProduct G (χ₂₃ - δ₃) (inducedClassFunction c.H0 (μ - γ)) = 0
    exact hth3δ0

private lemma cross_orbit_zero_for_rep (c : Hyp11 G) (h12 : Hyp12 c)
    (hH0index : (c.H0.subgroupOf c.H).index = 2)
    {ν₁ ν₂ ν₃ νⱼ : ClassFunction (↥c.H0)}
    (hν₁ : IsIrreducibleCharacter ν₁) (hν₂ : IsIrreducibleCharacter ν₂)
    (hν₃ : IsIrreducibleCharacter ν₃) (hνⱼ : IsIrreducibleCharacter νⱼ)
    (h₂₁ : ν₂ ∈ orbit c.H0 c.U ν₁) (h₃₁ : ν₃ ∈ orbit c.H0 c.U ν₁)
    (hⱼ₁ : νⱼ ∈ orbit c.H0 c.U ν₁)
    (hν₁s : conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ≠ ν₁)
    (hν₂s : conjChar c.H0 (s_normalizes_H0 c h12) ν₂ ≠ ν₂)
    (hν₃s : conjChar c.H0 (s_normalizes_H0 c h12) ν₃ ≠ ν₃)
    (h₁₂ : ν₁ ≠ ν₂ ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ≠ ν₂)
    (h₁₃ : ν₁ ≠ ν₃ ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ≠ ν₃)
    (h₁ⱼ : ν₁ ≠ νⱼ ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ≠ νⱼ)
    (h₂₃ : ν₂ ≠ ν₃ ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₂ ≠ ν₃)
    (h₂ⱼ : ν₂ ≠ νⱼ ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₂ ≠ νⱼ)
    (h₃ⱼ : ν₃ ≠ νⱼ ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₃ ≠ νⱼ)
    {L : Finset (ClassFunction (↥c.H0))} (hL : L = orbit c.H0 c.U ν₁)
    (hσ₁L : conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ∈ L)
    {ι : Type u} [Fintype ι] (rep : ι → ClassFunction (↥c.H0))
    (hrep_irr : ∀ i : ι, IsIrreducibleCharacter (rep i))
    (hrep : ∀ ν : {ν : ClassFunction (↥c.H0) // IsIrreducibleCharacter ν},
      ∃! i : ι, ν.1 ∈ orbit c.H0 c.U (rep i))
    {χ₂₃ : ClassFunction G}
    (hχsig : IsIrreducibleCharacter χ₂₃ ∨ IsIrreducibleCharacter (-χ₂₃))
    (hχg : IsGeneralizedCharacter χ₂₃) (hχ₁ : normSq G χ₂₃ = 1)
    (hχ₂ : scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - ν₂)) = 1)
    (hχ₃ : scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - ν₃)) = 1)
    (hχj0 : scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - νⱼ)) = 0)
    (hδⱼnorm : normSq G (inducedClassFunction c.H0 (ν₁ - νⱼ)) = 3) :
    ∀ ν : {ν : ClassFunction (↥c.H0) // IsIrreducibleCharacter ν},
      ν.1 ∉ L →
        scalarProduct G (χ₂₃ - inducedClassFunction c.H0 (ν₁ - ν₂))
          (inducedClassFunction c.H0 (ν.1 - rep (Classical.choose (hrep ν)))) = 0 ∧
        scalarProduct G (χ₂₃ - inducedClassFunction c.H0 (ν₁ - ν₃))
          (inducedClassFunction c.H0 (ν.1 - rep (Classical.choose (hrep ν)))) = 0 := by
  intro ν hνnot
  let i : ι := Classical.choose (hrep ν)
  let γ : ClassFunction (↥c.H0) := rep i
  have hνγ : ν.1 ∈ orbit c.H0 c.U γ := (Classical.choose_spec (hrep ν)).1
  have hγirr : IsIrreducibleCharacter γ := hrep_irr i
  have hnotmem : ∀ ξ : ClassFunction (↥c.H0), ξ ∈ L → ξ ∉ orbit c.H0 c.U ν.1 := by
    intro ξ hξL hξν
    apply hνnot
    have horbitξ : orbit c.H0 c.U ξ = L := by
      have hξ₁ : ξ ∈ orbit c.H0 c.U ν₁ := by
        rw [← hL]
        exact hξL
      rw [hL]
      exact orbit_eq_of_mem c hξ₁
    have horbitν : orbit c.H0 c.U ν.1 = L := by
      rw [← horbitξ]
      exact (orbit_eq_of_mem c hξν).symm
    rw [← horbitν]
    exact orbit_self_mem c ν.1
  by_cases hνγeq : ν.1 = γ
  · have hzero : inducedClassFunction c.H0 (ν.1 - γ) = 0 := by
      rw [hνγeq]
      rw [show γ - γ = (0 : ClassFunction (↥c.H0)) by simp]
      exact inducedClassFunction_zero c.H0
    constructor <;> rw [hzero, scalarProduct_zero_right]
  · by_cases hνsγ : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = γ
    · have hσγν : conjChar c.H0 (s_normalizes_H0 c h12) γ = ν.1 := by
        rw [← hνsγ, conjChar_conjChar c h12 ν.1]
      have h_inv : conjChar c.H0 (s_normalizes_H0 c h12) γ ∈ orbit c.H0 c.U γ := by
        rw [hσγν]
        exact hνγ
      have hzero : inducedClassFunction c.H0 (ν.1 - γ) = 0 := by
        rw [← hσγν]
        exact sigma_pair_star_zero_of_invariant c h12 hH0index hγirr h_inv
          (orbit_self_mem c γ)
      constructor <;> rw [hzero, scalarProduct_zero_right]
    · have hmemL : ∀ ξ : ClassFunction (↥c.H0), ξ ∈ orbit c.H0 c.U ν₁ → ξ ∈ L := by
        intro ξ hξ
        rw [hL]
        exact hξ
      have hσmem : ∀ ξ : ClassFunction (↥c.H0), ξ ∈ orbit c.H0 c.U ν₁ →
          conjChar c.H0 (s_normalizes_H0 c h12) ξ ∈ orbit c.H0 c.U ν₁ := by
        have hσ₁orb : conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ∈
            orbit c.H0 c.U ν₁ := by
          rw [← hL]
          exact hσ₁L
        intro ξ hξ
        have h := orbit_s_closed_of_invariant c h12 hσ₁orb hξ
        simpa [orbit_eq_of_mem c hξ] using h
      have hν₁μ : ν₁ ∉ orbit c.H0 c.U ν.1 :=
        hnotmem ν₁ (hmemL ν₁ (orbit_self_mem c ν₁))
      have hσν₁μ : conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ∉ orbit c.H0 c.U ν.1 :=
        hnotmem (conjChar c.H0 (s_normalizes_H0 c h12) ν₁)
          (hmemL (conjChar c.H0 (s_normalizes_H0 c h12) ν₁)
            (hσmem ν₁ (orbit_self_mem c ν₁)))
      have hν₂μ : ν₂ ∉ orbit c.H0 c.U ν.1 := hnotmem ν₂ (hmemL ν₂ h₂₁)
      have hσν₂μ : conjChar c.H0 (s_normalizes_H0 c h12) ν₂ ∉ orbit c.H0 c.U ν.1 :=
        hnotmem (conjChar c.H0 (s_normalizes_H0 c h12) ν₂)
          (hmemL (conjChar c.H0 (s_normalizes_H0 c h12) ν₂)
            (hσmem ν₂ h₂₁))
      have hν₃μ : ν₃ ∉ orbit c.H0 c.U ν.1 := hnotmem ν₃ (hmemL ν₃ h₃₁)
      have hσν₃μ : conjChar c.H0 (s_normalizes_H0 c h12) ν₃ ∉ orbit c.H0 c.U ν.1 :=
        hnotmem (conjChar c.H0 (s_normalizes_H0 c h12) ν₃)
          (hmemL (conjChar c.H0 (s_normalizes_H0 c h12) ν₃)
            (hσmem ν₃ h₃₁))
      have hνⱼμ : νⱼ ∉ orbit c.H0 c.U ν.1 := hnotmem νⱼ (hmemL νⱼ hⱼ₁)
      have hσνⱼμ : conjChar c.H0 (s_normalizes_H0 c h12) νⱼ ∉ orbit c.H0 c.U ν.1 :=
        hnotmem (conjChar c.H0 (s_normalizes_H0 c h12) νⱼ)
          (hmemL (conjChar c.H0 (s_normalizes_H0 c h12) νⱼ)
            (hσmem νⱼ hⱼ₁))
      have hres := cross_orbit_coeff_zero_of_undefined c h12 hH0index
        hν₁ hν₂ hν₃ hνⱼ ν.2 hγirr h₂₁ h₃₁ hⱼ₁ hνγ
        hν₁s hν₂s hν₃s h₁₂ h₁₃ h₁ⱼ h₂₃ h₂ⱼ h₃ⱼ
        hν₁μ hσν₁μ hν₂μ hσν₂μ hν₃μ hσν₃μ hνⱼμ hσνⱼμ
        hνγeq hνsγ hχsig hχg hχ₁ hχ₂ hχ₃ hχj0 hδⱼnorm
      constructor
      · change scalarProduct G (χ₂₃ - inducedClassFunction c.H0 (ν₁ - ν₂))
          (inducedClassFunction c.H0 (ν.1 - rep (Classical.choose (hrep ν)))) = 0
        simpa [γ, i] using hres.1
      · change scalarProduct G (χ₂₃ - inducedClassFunction c.H0 (ν₁ - ν₃))
          (inducedClassFunction c.H0 (ν.1 - rep (Classical.choose (hrep ν)))) = 0
        simpa [γ, i] using hres.2


/-- `V = 0` is consumed directly from `lemma_2_2_V_zero_of_pair_sum`
(`Section2/Lemma22.lean`) at the `at_t`-wiring below; a local wrapper is
deliberately avoided (its `exact`-unification with the big sum hangs the
elaborator in this file's environment).

The per-orbit lift: for a set `Θ` of characters of `H` induced from a
`Λ`-orbit, a pairwise disjoint lift `θ ↦ θ̃` with `|θ̃| = |θ|` and
`(μ−ν)* = μ̃−ν̃`. -/
structure ThetaLift (c : Hyp11 G) (h12 : Hyp12 c)
    (L : Finset (ClassFunction (↥c.H0)))
    (Θ : Finset (ClassFunction (↥c.H))) where
  lift : ClassFunction (↥c.H) → ClassFunction G
  norm : ∀ θ ∈ Θ, normSq G (lift θ) = normSq (↥c.H) θ
  isGeneralized : ∀ θ ∈ Θ, IsGeneralizedCharacter (lift θ)
  ind : ∀ {ν μ : ClassFunction (↥c.H0)}, μ ∈ orbit c.H0 c.U ν →
    IsIrreducibleCharacter ν → ν ∈ L →
    inducedFromSub (h12.H0_normal_in_H).1 ν ∈ Θ →
    inducedFromSub (h12.H0_normal_in_H).1 μ ∈ Θ →
    inducedClassFunction c.H0 (μ - ν) =
      lift (inducedFromSub (h12.H0_normal_in_H).1 μ) -
        lift (inducedFromSub (h12.H0_normal_in_H).1 ν)
  disjoint : ∀ {ν μ : ClassFunction (↥c.H0)}, μ ∈ orbit c.H0 c.U ν →
    ν ∈ L → ν ≠ μ → conjChar c.H0 (s_normalizes_H0 c h12) ν ≠ μ →
    inducedFromSub (h12.H0_normal_in_H).1 ν ∈ Θ →
    inducedFromSub (h12.H0_normal_in_H).1 μ ∈ Θ →
    Theory.Character.Disjoint (lift (inducedFromSub (h12.H0_normal_in_H).1 μ))
      (lift (inducedFromSub (h12.H0_normal_in_H).1 ν))

/-- Existence of the per-orbit lift (the `θ̃ⱼ` construction): the `n = 2`
split, the `n ≥ 3` common-constituent `θ̃₁ := χ₂₃` with
`θ̃ᵢ := χ₂₃ − δᵢ*`, and the pairwise disjointness. The `θ̃ⱼ` undefined case
(`j ≥ 4`) is the paper's `n ≥ 5` contradiction, which needs the `V = 0`
content of `lemma_2_2` case 1 (`V_zero_of_pair`); that part is the recorded
`sorry`. The genuinely provable parts (the defined-case lift, the
`(δᵢ*,dj*)_G = |θ₁|` pairing via `delta_pair_scalar`/`theta_pair_orth`, the
norms via `delta_norm`, the disjointness via the orthogonal-norm-one lifts)
are downstream of the constituent extraction, which is itself recorded as a
`sorry` in `exists_common_constituent_self`. -/
private lemma exists_theta_lift (c : Hyp11 G) (h12 : Hyp12 c)
    (hH0index : (c.H0.subgroupOf c.H).index = 2)
    (ν₀ ν₁ ν₂ ν₃ : ClassFunction (↥c.H0))
    (hν₀ : IsIrreducibleCharacter ν₀) (hν₁ : IsIrreducibleCharacter ν₁)
    (hν₂ : IsIrreducibleCharacter ν₂) (hν₃ : IsIrreducibleCharacter ν₃)
    (h₁₀ : ν₁ ∈ orbit c.H0 c.U ν₀) (h₂₀ : ν₂ ∈ orbit c.H0 c.U ν₀)
    (h₃₀ : ν₃ ∈ orbit c.H0 c.U ν₀)
    (hν₀s : conjChar c.H0 (s_normalizes_H0 c h12) ν₀ ∉ orbit c.H0 c.U ν₀)
    (hν₁s : conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ≠ ν₁)
    (hν₂s : conjChar c.H0 (s_normalizes_H0 c h12) ν₂ ≠ ν₂)
    (hν₃s : conjChar c.H0 (s_normalizes_H0 c h12) ν₃ ≠ ν₃)
    (h₁₂ : ν₁ ≠ ν₂ ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ≠ ν₂)
    (h₁₃ : ν₁ ≠ ν₃ ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ≠ ν₃)
    (h₂₃ : ν₂ ≠ ν₃ ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₂ ≠ ν₃)
    {χ₂₃ : ClassFunction G}
    (hχg : IsGeneralizedCharacter χ₂₃) (hχ₁ : normSq G χ₂₃ = 1)
    (hχ₂ : scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - ν₂)) = 1)
    (hχ₃ : scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - ν₃)) = 1)
    (hχall : ∀ ν ∈ orbit c.H0 c.U ν₀, ν ≠ ν₁ →
      scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - ν)) = 1) :
    Nonempty (ThetaLift c h12 (orbit c.H0 c.U ν₀)
      (thetaOfOrbit c h12 (orbit c.H0 c.U ν₀))) := by
  classical
  let L : Finset (ClassFunction (↥c.H0)) := orbit c.H0 c.U ν₀
  let Θ : Finset (ClassFunction (↥c.H)) := thetaOfOrbit c h12 L
  let θ : ClassFunction (↥c.H0) → ClassFunction (↥c.H) := fun ν =>
    inducedFromSub (h12.H0_normal_in_H).1 ν
  let σ : ClassFunction (↥c.H0) → ClassFunction (↥c.H0) := fun ν =>
    conjChar c.H0 (s_normalizes_H0 c h12) ν
  let νθ : ClassFunction (↥c.H) → ClassFunction (↥c.H0) := fun θ' =>
    if h : θ' ∈ Θ then Classical.choose (Finset.mem_image.mp h) else ν₀
  let lift : ClassFunction (↥c.H) → ClassFunction G := fun θ' =>
    χ₂₃ - inducedClassFunction c.H0 (ν₁ - νθ θ')
  -- the witness properties of the preimage choice
  have hw : ∀ {θ' : ClassFunction (↥c.H)}, θ' ∈ Θ → νθ θ' ∈ L ∧ θ (νθ θ') = θ' := by
    intro θ' hθ'
    unfold νθ
    rw [dif_pos hθ']
    exact Classical.choose_spec (Finset.mem_image.mp hθ')
  -- the orbit has no `s`-fixed members (from `σν₀ ∉ L`)
  have hνsall : ∀ ν ∈ L, conjChar c.H0 (s_normalizes_H0 c h12) ν ≠ ν := by
    intro ν hνL hσν
    apply hν₀s
    exact s_fixed_mem_imp_invariant c h12 hνL hσν
  have hσ₁not : σ ν₁ ∉ L := by
    intro hσ₁L
    have hmem : σ ν₁ ∈ orbit c.H0 c.U (σ ν₀) := by
      rw [orbit_conjChar_eq c h12 ν₀]
      exact Finset.mem_image.mpr ⟨ν₁, h₁₀, rfl⟩
    have ho1 : orbit c.H0 c.U (σ ν₁) = orbit c.H0 c.U (σ ν₀) := orbit_eq_of_mem c hmem
    have ho2 : orbit c.H0 c.U (σ ν₁) = orbit c.H0 c.U ν₁ := by
      apply orbit_eq_of_mem
      rwa [orbit_eq_of_mem c h₁₀]
    have ho3 : orbit c.H0 c.U ν₁ = L := orbit_eq_of_mem c h₁₀
    apply hν₀s
    have hchain : orbit c.H0 c.U (σ ν₀) = orbit c.H0 c.U ν₀ := by
      calc
        orbit c.H0 c.U (σ ν₀) = orbit c.H0 c.U (σ ν₁) := ho1.symm
        _ = orbit c.H0 c.U ν₁ := ho2
        _ = orbit c.H0 c.U ν₀ := orbit_eq_of_mem c h₁₀
    rw [hchain.symm]
    exact orbit_self_mem c (σ ν₀)
  -- the members of `L` are irreducible
  have hνirr : ∀ ν ∈ L, IsIrreducibleCharacter ν :=
    fun ν hνL => orbit_mem_isIrreducible c.H0 c.U hν₀ hνL
  -- `(μ−ν)* = 0` for members with `θ(μ) = θ(ν)` (the `s`-pairs)
  have hpair_zero : ∀ {ν μ : ClassFunction (↥c.H0)}, ν ∈ L → μ ∈ L →
      θ μ = θ ν → inducedClassFunction c.H0 (μ - ν) = 0 := by
    intro ν μ hνL hμL hθeq
    have hnorm : normSq G (inducedClassFunction c.H0 (μ - ν)) = 0 := by
      have hμν : μ ∈ orbit c.H0 c.U ν := by
        rw [orbit_eq_of_mem c hνL]
        exact hμL
      have hsp := delta_pair_scalar (ν₁ := ν) (ν₂ := ν) (μ₁ := μ) (μ₂ := μ)
        c h12 (hνirr ν hνL) (hνirr ν hνL) hμν hμν
      change scalarProduct G (inducedClassFunction c.H0 (μ - ν))
          (inducedClassFunction c.H0 (μ - ν)) = 0
      rw [hsp]
      change scalarProduct (↥c.H) (θ μ - θ ν) (θ μ - θ ν) = 0
      simp [hθeq, scalarProduct]
    exact (normSq_eq_zero_iff (inducedClassFunction c.H0 (μ - ν))).1 hnorm
  -- `σ` maps `L` into the other orbit: no `σ`-image of a member of `L`
  -- lies in `L` (`σν₀ ∉ L` would then put `σν₀` in the orbit)
  have hσnot : ∀ μ ∈ L, σ μ ∉ L := by
    intro μ hμL hσμL
    apply hν₀s
    have hσμσ₀ : σ μ ∈ orbit c.H0 c.U (σ ν₀) := by
      rw [orbit_conjChar_eq c h12 ν₀]
      exact Finset.mem_image.mpr ⟨μ, hμL, rfl⟩
    have hoμ : orbit c.H0 c.U (σ μ) = orbit c.H0 c.U (σ ν₀) := orbit_eq_of_mem c hσμσ₀
    have hoμ' : orbit c.H0 c.U (σ μ) = L := orbit_eq_of_mem c hσμL
    change σ ν₀ ∈ L
    rw [← hoμ', hoμ]
    exact orbit_self_mem c (σ ν₀)
  -- `|θ̃(θ')|² = 1` for every `θ' ∈ Θ` (the `s`-pair branch and the
  -- `δ*`-norm branch)
  have hnorm1 : ∀ θ' ∈ Θ, normSq G (lift θ') = 1 := by
    intro θ' hθ'
    have hw' : νθ θ' ∈ L ∧ θ (νθ θ') = θ' := hw hθ'
    by_cases h₁ : θ (νθ θ') = θ ν₁
    · have hzero : inducedClassFunction c.H0 (ν₁ - νθ θ') = 0 := by
        exact hpair_zero (ν := νθ θ') (μ := ν₁) hw'.1 h₁₀ h₁.symm
      unfold lift
      rw [hzero]
      simp [hχ₁]
    · have hne : νθ θ' ≠ ν₁ := by
        intro hEq
        apply h₁
        rw [hEq]
      have hχ : scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - νθ θ')) = 1 := by
        exact hχall (νθ θ') hw'.1 hne
      have hδnorm : normSq G (inducedClassFunction c.H0 (ν₁ - νθ θ')) = 2 := by
        have h₁θ : ν₁ ∈ orbit c.H0 c.U (νθ θ') := by
          rw [orbit_eq_of_mem c hw'.1]
          exact h₁₀
        have hσ₁θ : conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ≠ νθ θ' := by
          intro hEq
          apply hσ₁not
          change conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ∈ L
          rw [hEq]
          exact hw'.1
        rw [delta_norm c h12 hH0index hν₁ (hνirr (νθ θ') hw'.1) h₁θ hne.symm hσ₁θ]
        rw [theta_norm c h12 hH0index hν₁, theta_norm c h12 hH0index (hνirr (νθ θ') hw'.1)]
        rw [if_neg hν₁s, if_neg (hνsall (νθ θ') hw'.1)]
        norm_num
      unfold lift
      change normSq G (χ₂₃ - inducedClassFunction c.H0 (ν₁ - νθ θ')) = 1
      unfold normSq
      rw [scalarProduct_sub_left, scalarProduct_sub_right, scalarProduct_sub_right]
      change scalarProduct G χ₂₃ χ₂₃ = 1 at hχ₁
      have hδχ : scalarProduct G (inducedClassFunction c.H0 (ν₁ - νθ θ')) χ₂₃ = 1 := by
        apply star_inj.mp
        rw [scalarProduct_star_comm]
        change scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - νθ θ')) = star 1
        simpa using hχ
      have hδδ : scalarProduct G (inducedClassFunction c.H0 (ν₁ - νθ θ'))
          (inducedClassFunction c.H0 (ν₁ - νθ θ')) = 2 := hδnorm
      rw [hχ₁, hχ, hδχ, hδδ]
      norm_num
  -- `|θ(ν)|² = 1` for `ν ∈ L` (no `s`-fixed member of `L`)
  have hθnorm1 : ∀ ν ∈ L, normSq (↥c.H) (θ ν) = 1 := by
    intro ν hνL
    change normSq (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν) = 1
    rw [theta_norm c h12 hH0index (hνirr ν hνL)]
    rw [if_neg (hνsall ν hνL)]
  -- the lift values are generalized characters
  have hgen : ∀ θ' ∈ Θ, IsGeneralizedCharacter (lift θ') := by
    intro θ' hθ'
    unfold lift
    exact isGeneralizedCharacter_sub hχg (isGeneralizedCharacter_induced c h12 (ν₁ - νθ θ')
      (isGeneralizedCharacter_sub_irr hν₁ (hνirr (νθ θ') (hw hθ').1)))
  apply Nonempty.intro
  refine ⟨lift, ?_, ?_, ?_, ?_⟩
  · -- norm: `|θ̃(θ')|² = 1 = |θ'|²`
    intro θ' hθ'
    have h1 := hnorm1 θ' hθ'
    have hw' : νθ θ' ∈ L ∧ θ (νθ θ') = θ' := hw hθ'
    rw [h1]
    rw [← hw'.2]
    exact (hθnorm1 (νθ θ') hw'.1).symm
  · -- isGeneralized
    intro θ' hθ'
    exact hgen θ' hθ'
  · -- ind: the fiber of `θ` on `L` is a singleton, so `νθ (θ μ) = μ` and
    -- the claim reduces to the additivity of the induced map
    intro ν μ hμL hνIrr hνL hθνΘ hθμΘ
    have hμL' : μ ∈ L := by
      rw [orbit_eq_of_mem c hνL] at hμL
      exact hμL
    have hμ' : νθ (θ μ) ∈ L ∧ θ (νθ (θ μ)) = θ μ := hw hθμΘ
    have hν' : νθ (θ ν) ∈ L ∧ θ (νθ (θ ν)) = θ ν := hw hθνΘ
    have hμpre : νθ (θ μ) = μ := by
      apply theta_of_orbit_injective_of_not_invariant c h12 hν₀ hν₀s
      · exact hμ'.1
      · exact hμL'
      · exact hμ'.2
    have hνpre : νθ (θ ν) = ν := by
      apply theta_of_orbit_injective_of_not_invariant c h12 hν₀ hν₀s
      · exact hν'.1
      · exact hνL
      · exact hν'.2
    change inducedClassFunction c.H0 (μ - ν) = lift (θ μ) - lift (θ ν)
    unfold lift
    rw [hμpre, hνpre]
    have hrhs : (χ₂₃ - inducedClassFunction c.H0 (ν₁ - μ)) -
          (χ₂₃ - inducedClassFunction c.H0 (ν₁ - ν)) =
          inducedClassFunction c.H0 (μ - ν) := by
      calc
        (χ₂₃ - inducedClassFunction c.H0 (ν₁ - μ)) -
            (χ₂₃ - inducedClassFunction c.H0 (ν₁ - ν))
            = inducedClassFunction c.H0 (ν₁ - ν) -
                inducedClassFunction c.H0 (ν₁ - μ) := by
              ring
        _ = inducedClassFunction c.H0 ((ν₁ - ν) - (ν₁ - μ)) := by
              rw [← inducedClassFunction_sub]
        _ = inducedClassFunction c.H0 (μ - ν) := by
              congr 1
              ring
    rw [← hrhs]
  · -- disjoint: the pairwise disjointness of the lift values on `Θ`
    intro ν μ hμL hνL hνμne hσνμ hθνΘ hθμΘ
    have hμL' : μ ∈ L := by
      rw [orbit_eq_of_mem c hνL] at hμL
      exact hμL
    have hμ' : νθ (θ μ) ∈ L ∧ θ (νθ (θ μ)) = θ μ := hw hθμΘ
    have hν' : νθ (θ ν) ∈ L ∧ θ (νθ (θ ν)) = θ ν := hw hθνΘ
    have hμpre : νθ (θ μ) = μ := by
      apply theta_of_orbit_injective_of_not_invariant c h12 hν₀ hν₀s
      · exact hμ'.1
      · exact hμL'
      · exact hμ'.2
    have hνpre : νθ (θ ν) = ν := by
      apply theta_of_orbit_injective_of_not_invariant c h12 hν₀ hν₀s
      · exact hν'.1
      · exact hνL
      · exact hν'.2
    -- orthogonality `(θ̃(θμ), θ̃(θν)) = 0`, split on whether `μ = ν₁` / `ν = ν₁`
    have hpairχχ : scalarProduct G χ₂₃ χ₂₃ = 1 := by
      change scalarProduct G χ₂₃ χ₂₃ = 1
      exact hχ₁
    have horth : scalarProduct G (lift (θ μ)) (lift (θ ν)) = 0 := by
      by_cases hμ1 : μ = ν₁
      · rw [hμ1] at hμ' hνμne ⊢
        have hzero : inducedClassFunction c.H0 (ν₁ - νθ (θ ν₁)) = 0 := by
          exact hpair_zero (ν := νθ (θ ν₁)) (μ := ν₁) hμ'.1 h₁₀ hμ'.2.symm
        have hlift1 : lift (θ ν₁) = χ₂₃ := by
          unfold lift
          rw [hzero]
          simp
        have hlift2 : lift (θ ν) = χ₂₃ - inducedClassFunction c.H0 (ν₁ - ν) := by
          unfold lift
          rw [hνpre]
        rw [hlift1, hlift2]
        rw [scalarProduct_sub_right]
        have hpair1 : scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - ν)) = 1 := by
          exact hχall ν hνL hνμne
        rw [hpairχχ, hpair1]
        norm_num
      · by_cases hν1 : ν = ν₁
        · rw [hν1] at hν' ⊢
          have hzero : inducedClassFunction c.H0 (ν₁ - νθ (θ ν₁)) = 0 := by
            exact hpair_zero (ν := νθ (θ ν₁)) (μ := ν₁) hν'.1 h₁₀ hν'.2.symm
          have hlift1 : lift (θ ν₁) = χ₂₃ := by
            unfold lift
            rw [hzero]
            simp
          have hlift2 : lift (θ μ) = χ₂₃ - inducedClassFunction c.H0 (ν₁ - μ) := by
            unfold lift
            rw [hμpre]
          rw [hlift2, hlift1]
          rw [scalarProduct_sub_left]
          have hpair1 : scalarProduct G (inducedClassFunction c.H0 (ν₁ - μ)) χ₂₃ = 1 := by
            apply star_inj.mp
            rw [scalarProduct_star_comm]
            change scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - μ)) = star 1
            simpa using hχall μ hμL' hμ1
          rw [hpairχχ, hpair1]
          norm_num
        · -- the generic case: `μ, ν ≠ ν₁`
          have hliftμ : lift (θ μ) = χ₂₃ - inducedClassFunction c.H0 (ν₁ - μ) := by
            unfold lift
            rw [hμpre]
          have hliftν : lift (θ ν) = χ₂₃ - inducedClassFunction c.H0 (ν₁ - ν) := by
            unfold lift
            rw [hνpre]
          rw [hliftμ, hliftν]
          rw [scalarProduct_sub_left, scalarProduct_sub_right, scalarProduct_sub_right]
          have hpairχμ : scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - μ)) = 1 :=
            hχall μ hμL' hμ1
          have hpairχν : scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - ν)) = 1 :=
            hχall ν hνL hν1
          have hpairμχ : scalarProduct G (inducedClassFunction c.H0 (ν₁ - μ)) χ₂₃ = 1 := by
            apply star_inj.mp
            rw [scalarProduct_star_comm]
            change scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - μ)) = star 1
            simpa using hpairχμ
          have hσν₁μ : conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ≠ μ := by
            intro hEq
            apply hσnot ν₁ h₁₀
            change conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ∈ L
            rwa [hEq]
          have hσν₁ν : conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ≠ ν := by
            intro hEq
            apply hσnot ν₁ h₁₀
            change conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ∈ L
            rwa [hEq]
          have hσμν : conjChar c.H0 (s_normalizes_H0 c h12) μ ≠ ν := by
            intro hEq
            apply hσνμ
            rw [← conjChar_conjChar c h12 μ, hEq]
          have hpairδδ : scalarProduct G (inducedClassFunction c.H0 (ν₁ - μ))
              (inducedClassFunction c.H0 (ν₁ - ν)) = 1 := by
            have hsp := delta_pair_scalar c h12 (ν₁ := ν₁) (ν₂ := ν₁) (μ₁ := μ) (μ₂ := ν)
              hν₁ hν₁ (by rw [orbit_eq_of_mem c h₁₀]; exact hμL')
              (by rw [orbit_eq_of_mem c h₁₀]; exact hνL)
            change scalarProduct G (inducedClassFunction c.H0 (ν₁ - μ))
                (inducedClassFunction c.H0 (ν₁ - ν)) = 1
            rw [show inducedClassFunction c.H0 (ν₁ - μ) = -inducedClassFunction c.H0 (μ - ν₁) by
              rw [show ν₁ - μ = -(μ - ν₁) by ring]
              rw [inducedClassFunction_neg]]
            rw [show inducedClassFunction c.H0 (ν₁ - ν) = -inducedClassFunction c.H0 (ν - ν₁) by
              rw [show ν₁ - ν = -(ν - ν₁) by ring]
              rw [inducedClassFunction_neg]]
            rw [scalarProduct_neg_left, scalarProduct_neg_right, hsp]
            simp
            change scalarProduct (↥c.H) (θ μ - θ ν₁) (θ ν - θ ν₁) = 1
            rw [scalarProduct_sub_left, scalarProduct_sub_right, scalarProduct_sub_right]
            have hθ₁₁H : scalarProduct (↥c.H) (θ ν₁) (θ ν₁) = 1 := by
              change normSq (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν₁) = 1
              rw [theta_norm c h12 hH0index hν₁]
              rw [if_neg hν₁s]
            have hθ₁μH : scalarProduct (↥c.H) (θ ν₁) (θ μ) = 0 := by
              exact theta_pair_scalar_zero c h12 hH0index hν₁ (hνirr μ hμL') (Ne.symm hμ1) hσν₁μ
            have hθμ₁H : scalarProduct (↥c.H) (θ μ) (θ ν₁) = 0 := by
              exact theta_pair_scalar_zero c h12 hH0index (hνirr μ hμL') hν₁ hμ1
                (by
                  intro hEq
                  apply hσnot μ hμL'
                  change conjChar c.H0 (s_normalizes_H0 c h12) μ ∈ L
                  rwa [hEq])
            have hθ₁νH : scalarProduct (↥c.H) (θ ν₁) (θ ν) = 0 := by
              exact theta_pair_scalar_zero c h12 hH0index hν₁ (hνirr ν hνL) (Ne.symm hν1) hσν₁ν
            have hθμνH : scalarProduct (↥c.H) (θ μ) (θ ν) = 0 := by
              exact theta_pair_scalar_zero c h12 hH0index (hνirr μ hμL') (hνirr ν hνL)
                hνμne.symm hσμν
            rw [hθμνH, hθμ₁H, hθ₁νH, hθ₁₁H]
            norm_num
          rw [hpairχχ, hpairχν, hpairμχ, hpairδδ]
          norm_num
    -- assemble via the orthogonal-norm-one criterion
    exact disjoint_of_orthogonal_norm_one (hgen (θ μ) hθμΘ) (hgen (θ ν) hθνΘ)
      (by change scalarProduct G (lift (θ μ)) (lift (θ μ)) = 1
          exact hnorm1 (θ μ) hθμΘ)
      (by change scalarProduct G (lift (θ ν)) (lift (θ ν)) = 1
          exact hnorm1 (θ ν) hθνΘ)
      horth
set_option maxHeartbeats 8000000 in
/-- The `s`-invariant orbit's lift (the paper's construction with the two
fixed members at the end): `θ̃(θ') := χ₂₃ − (ν₁ − νθ(θ'))*` on the
`θ`-values, well-defined on the `s`-pairs via `(σa − a)* = 0`, with the
norm `|θ̃(θ')|² = |θ'|²` (1 on the pair-values, 2 on the fixed values). -/
private lemma exists_theta_lift_invariant (c : Hyp11 G) (h12 : Hyp12 c)
    (hH0index : (c.H0.subgroupOf c.H).index = 2)
    (ν₀ ν₁ : ClassFunction (↥c.H0))
    (hν₀ : IsIrreducibleCharacter ν₀) (hν₁ : IsIrreducibleCharacter ν₁)
    (h₁₀ : ν₁ ∈ orbit c.H0 c.U ν₀)
    (hν₀s_inv : conjChar c.H0 (s_normalizes_H0 c h12) ν₀ ∈ orbit c.H0 c.U ν₀)
    (hν₁s : conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ≠ ν₁)
    {χ₂₃ : ClassFunction G}
    (hχg : IsGeneralizedCharacter χ₂₃) (hχ₁ : normSq G χ₂₃ = 1)
    (hχall : ∀ ν ∈ orbit c.H0 c.U ν₀, ν ≠ ν₁ →
      conjChar c.H0 (s_normalizes_H0 c h12) ν ≠ ν₁ →
      scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - ν)) = 1) :
    Nonempty (ThetaLift c h12 (orbit c.H0 c.U ν₀)
      (thetaOfOrbit c h12 (orbit c.H0 c.U ν₀))) := by
  classical
  let L : Finset (ClassFunction (↥c.H0)) := orbit c.H0 c.U ν₀
  let Θ : Finset (ClassFunction (↥c.H)) := thetaOfOrbit c h12 L
  let θ : ClassFunction (↥c.H0) → ClassFunction (↥c.H) := fun ν =>
    inducedFromSub (h12.H0_normal_in_H).1 ν
  let σ : ClassFunction (↥c.H0) → ClassFunction (↥c.H0) := fun ν =>
    conjChar c.H0 (s_normalizes_H0 c h12) ν
  let νθ : ClassFunction (↥c.H) → ClassFunction (↥c.H0) := fun θ' =>
    if h : θ' ∈ Θ then Classical.choose (Finset.mem_image.mp h) else ν₀
  let lift : ClassFunction (↥c.H) → ClassFunction G := fun θ' =>
    χ₂₃ - inducedClassFunction c.H0 (ν₁ - νθ θ')
  have hν₀L : ν₀ ∈ L := orbit_self_mem c ν₀
  have hνirr : ∀ ν ∈ L, IsIrreducibleCharacter ν :=
    fun ν hνL => orbit_mem_isIrreducible c.H0 c.U hν₀ hνL
  have hw : ∀ {θ' : ClassFunction (↥c.H)}, θ' ∈ Θ → νθ θ' ∈ L ∧ θ (νθ θ') = θ' := by
    intro θ' hθ'
    unfold νθ
    rw [dif_pos hθ']
    exact Classical.choose_spec (Finset.mem_image.mp hθ')
  -- the `s`-pair cancellation inside the orbit
  have hpair_zero : ∀ {ν μ : ClassFunction (↥c.H0)}, ν ∈ L → μ ∈ L →
      θ μ = θ ν → inducedClassFunction c.H0 (μ - ν) = 0 := by
    intro ν μ hνL hμL hθeq
    have hnorm : normSq G (inducedClassFunction c.H0 (μ - ν)) = 0 := by
      have hμν : μ ∈ orbit c.H0 c.U ν := by
        rw [orbit_eq_of_mem c hνL]
        exact hμL
      have hsp := delta_pair_scalar (ν₁ := ν) (ν₂ := ν) (μ₁ := μ) (μ₂ := μ)
        c h12 (hνirr ν hνL) (hνirr ν hνL) hμν hμν
      change scalarProduct G (inducedClassFunction c.H0 (μ - ν))
          (inducedClassFunction c.H0 (μ - ν)) = 0
      rw [hsp]
      change scalarProduct (↥c.H) (θ μ - θ ν) (θ μ - θ ν) = 0
      simp [hθeq, scalarProduct]
    exact (normSq_eq_zero_iff (inducedClassFunction c.H0 (μ - ν))).1 hnorm
  -- the s-pair of `ν₁` inside the orbit
  have hσ₁₁ : inducedClassFunction c.H0 (conjChar c.H0 (s_normalizes_H0 c h12) ν₁ - ν₁) = 0 :=
    sigma_pair_star_zero_of_invariant c h12 hH0index hν₀ hν₀s_inv h₁₀
  -- `σa ≠ ν₁` iff `a ≠ σν₁` (the `σ`-involution; the `hχall` excludes the
  -- `s`-pair of `ν₁`, where `(ν₁ − σν₁)* = 0` makes the pairing `0`)
  have hσa_ne_ν₁ : ∀ {a : ClassFunction (↥c.H0)},
      conjChar c.H0 (s_normalizes_H0 c h12) a ≠ ν₁ ↔ a ≠ conjChar c.H0 (s_normalizes_H0 c h12) ν₁ := by
    intro a
    constructor
    · intro h hEq
      apply h
      rw [hEq, conjChar_conjChar c h12 ν₁]
    · intro h hEq
      apply h
      exact (conjChar_conjChar c h12 a).symm.trans
        (congrArg (conjChar c.H0 (s_normalizes_H0 c h12)) hEq)
  -- the lift values are generalized characters
  have hgen : ∀ θ' ∈ Θ, IsGeneralizedCharacter (lift θ') := by
    intro θ' hθ'
    unfold lift
    exact isGeneralizedCharacter_sub hχg (isGeneralizedCharacter_induced c h12 (ν₁ - νθ θ')
      (isGeneralizedCharacter_sub_irr hν₁ (hνirr (νθ θ') (hw hθ').1)))
  apply Nonempty.intro
  refine ⟨lift, ?_, ?_, ?_, ?_⟩
  · -- norm: `|θ̃(θ')|² = |θ'|²` (1 on the pair-values, 2 on the fixed values)
    intro θ' hθ'
    have hw' : νθ θ' ∈ L ∧ θ (νθ θ') = θ' := hw hθ'
    by_cases h₁ : νθ θ' = ν₁
    · -- the `ν₁`-value: `lift = χ₂₃`
      have hzero : inducedClassFunction c.H0 (ν₁ - νθ θ') = 0 := by
        rw [h₁]
        rw [show ν₁ - ν₁ = (0 : ClassFunction (↥c.H0)) by simp]
        exact inducedClassFunction_zero c.H0
      have hlift : lift θ' = χ₂₃ := by
        unfold lift
        rw [hzero]
        simp
      rw [hlift]
      rw [hχ₁]
      rw [← hw'.2]
      rw [h₁]
      change 1 = normSq (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν₁)
      rw [theta_norm c h12 hH0index hν₁]
      rw [if_neg hν₁s]
    · by_cases h₂ : νθ θ' = conjChar c.H0 (s_normalizes_H0 c h12) ν₁
      · -- the `s`-pair of `ν₁`: `(ν₁ − σν₁)* = 0`, `lift = χ₂₃`
        have hzero : inducedClassFunction c.H0 (ν₁ - νθ θ') = 0 := by
          rw [h₂]
          rw [show ν₁ - conjChar c.H0 (s_normalizes_H0 c h12) ν₁ =
              -(conjChar c.H0 (s_normalizes_H0 c h12) ν₁ - ν₁) by ring]
          rw [inducedClassFunction_neg, hσ₁₁]
          simp
        have hlift : lift θ' = χ₂₃ := by
          unfold lift
          rw [hzero]
          simp
        rw [hlift]
        rw [hχ₁]
        rw [← hw'.2]
        rw [h₂]
        change 1 = normSq (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 (conjChar c.H0 (s_normalizes_H0 c h12) ν₁))
        rw [inducedFromSub_conjChar_eq c h12 hH0index hν₁]
        change 1 = normSq (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν₁)
        rw [theta_norm c h12 hH0index hν₁]
        rw [if_neg hν₁s]
      · -- the generic case: `a := νθ θ' ∉ {ν₁, σν₁}`, `|θ̃|² = |θ'|²`
        have hσ₁a : conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ≠ νθ θ' := by
          intro hEq
          apply h₂
          exact hEq.symm
        have hχa : scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - νθ θ')) = 1 :=
          hχall (νθ θ') hw'.1 (by intro hEq; exact h₁ hEq)
            ((hσa_ne_ν₁).2 (by intro hEq; exact h₂ hEq))
        have hδnorm : normSq G (inducedClassFunction c.H0 (ν₁ - νθ θ')) =
            1 + normSq (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 (νθ θ')) := by
          have h₁a : ν₁ ∈ orbit c.H0 c.U (νθ θ') := by
            rw [orbit_eq_of_mem c hw'.1]
            exact h₁₀
          rw [delta_norm c h12 hH0index hν₁ (hνirr (νθ θ') hw'.1) h₁a (Ne.symm h₁) hσ₁a]
          rw [theta_norm c h12 hH0index hν₁]
          rw [if_neg hν₁s]
        have hliftnorm : normSq G (lift θ') = normSq (↥c.H) (θ (νθ θ')) := by
          unfold lift
          change normSq G (χ₂₃ - inducedClassFunction c.H0 (ν₁ - νθ θ')) =
              normSq (↥c.H) (θ (νθ θ'))
          change scalarProduct G (χ₂₃ - inducedClassFunction c.H0 (ν₁ - νθ θ'))
              (χ₂₃ - inducedClassFunction c.H0 (ν₁ - νθ θ')) =
              normSq (↥c.H) (θ (νθ θ'))
          rw [scalarProduct_sub_left, scalarProduct_sub_right, scalarProduct_sub_right]
          have hχχ : scalarProduct G χ₂₃ χ₂₃ = 1 := by
            change scalarProduct G χ₂₃ χ₂₃ = 1
            exact hχ₁
          have hδχ : scalarProduct G (inducedClassFunction c.H0 (ν₁ - νθ θ')) χ₂₃ = 1 := by
            apply star_inj.mp
            rw [scalarProduct_star_comm]
            change scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - νθ θ')) = star 1
            simpa using hχa
          have hδδ : scalarProduct G (inducedClassFunction c.H0 (ν₁ - νθ θ'))
              (inducedClassFunction c.H0 (ν₁ - νθ θ')) =
              1 + normSq (↥c.H) (θ (νθ θ')) := by
            change scalarProduct G (inducedClassFunction c.H0 (ν₁ - νθ θ'))
                (inducedClassFunction c.H0 (ν₁ - νθ θ')) =
                1 + normSq (↥c.H) (θ (νθ θ'))
            exact hδnorm
          rw [hχχ, hχa, hδχ, hδδ]
          ring
        rw [hliftnorm]
        rw [hw'.2]
  · -- isGeneralized
    intro θ' hθ'
    exact hgen θ' hθ'
  · -- ind: the s-pair cancellation + the additivity
    intro ν μ hμL hνIrr hνL hθνΘ hθμΘ
    have hμL' : μ ∈ L := by
      rw [orbit_eq_of_mem c hνL] at hμL
      exact hμL
    have hμ' : νθ (θ μ) ∈ L ∧ θ (νθ (θ μ)) = θ μ := hw hθμΘ
    have hν' : νθ (θ ν) ∈ L ∧ θ (νθ (θ ν)) = θ ν := hw hθνΘ
    have hμc : inducedClassFunction c.H0 (μ - νθ (θ μ)) = 0 := by
      have hfib : L.filter (fun ν => θ ν = θ μ) =
          ({νθ (θ μ), conjChar c.H0 (s_normalizes_H0 c h12) (νθ (θ μ))} :
            Finset (ClassFunction (↥c.H0))) :=
        theta_fiber_pair_of_invariant c h12 hν₀ hν₀s_inv hμ'.1 hμ'.2
      have hμfib : μ ∈ L.filter (fun ν => θ ν = θ μ) :=
        Finset.mem_filter.mpr ⟨hμL', rfl⟩
      rw [hfib] at hμfib
      rw [Finset.mem_insert, Finset.mem_singleton] at hμfib
      rcases hμfib with h | h
      · rw [h]
        rw [hμ'.2]
        simp [inducedClassFunction_zero]
      · rw [h]
        rw [show νθ (θ (conjChar c.H0 (s_normalizes_H0 c h12) (νθ (θ μ)))) = νθ (θ μ) by
          have h1 : θ (conjChar c.H0 (s_normalizes_H0 c h12) (νθ (θ μ))) = θ (νθ (θ μ)) := by
            change inducedFromSub (h12.H0_normal_in_H).1 (conjChar c.H0 (s_normalizes_H0 c h12) (νθ (θ μ))) =
                inducedFromSub (h12.H0_normal_in_H).1 (νθ (θ μ))
            exact inducedFromSub_conjChar_eq c h12 hH0index (hνirr (νθ (θ μ)) hμ'.1)
          rw [h1, hμ'.2]]
        exact sigma_pair_star_zero_of_invariant c h12 hH0index hν₀ hν₀s_inv hμ'.1
    have hνc : inducedClassFunction c.H0 (ν - νθ (θ ν)) = 0 := by
      have hfib : L.filter (fun μ => θ μ = θ ν) =
          ({νθ (θ ν), conjChar c.H0 (s_normalizes_H0 c h12) (νθ (θ ν))} :
            Finset (ClassFunction (↥c.H0))) :=
        theta_fiber_pair_of_invariant c h12 hν₀ hν₀s_inv hν'.1 hν'.2
      have hνfib : ν ∈ L.filter (fun μ => θ μ = θ ν) :=
        Finset.mem_filter.mpr ⟨hνL, rfl⟩
      rw [hfib] at hνfib
      rw [Finset.mem_insert, Finset.mem_singleton] at hνfib
      rcases hνfib with h | h
      · rw [h]
        rw [hν'.2]
        simp [inducedClassFunction_zero]
      · rw [h]
        rw [show νθ (θ (conjChar c.H0 (s_normalizes_H0 c h12) (νθ (θ ν)))) = νθ (θ ν) by
          have h1 : θ (conjChar c.H0 (s_normalizes_H0 c h12) (νθ (θ ν))) = θ (νθ (θ ν)) := by
            change inducedFromSub (h12.H0_normal_in_H).1 (conjChar c.H0 (s_normalizes_H0 c h12) (νθ (θ ν))) =
                inducedFromSub (h12.H0_normal_in_H).1 (νθ (θ ν))
            exact inducedFromSub_conjChar_eq c h12 hH0index (hνirr (νθ (θ ν)) hν'.1)
          rw [h1, hν'.2]]
        exact sigma_pair_star_zero_of_invariant c h12 hH0index hν₀ hν₀s_inv hν'.1
    have hmain : inducedClassFunction c.H0 (νθ (θ μ) - νθ (θ ν)) =
        lift (θ μ) - lift (θ ν) := by
      unfold lift
      change inducedClassFunction c.H0 (νθ (θ μ) - νθ (θ ν)) =
        (χ₂₃ - inducedClassFunction c.H0 (ν₁ - νθ (θ μ))) -
          (χ₂₃ - inducedClassFunction c.H0 (ν₁ - νθ (θ ν)))
      have hrhs : (χ₂₃ - inducedClassFunction c.H0 (ν₁ - νθ (θ μ))) -
            (χ₂₃ - inducedClassFunction c.H0 (ν₁ - νθ (θ ν))) =
            inducedClassFunction c.H0 (νθ (θ μ) - νθ (θ ν)) := by
        calc
          (χ₂₃ - inducedClassFunction c.H0 (ν₁ - νθ (θ μ))) -
              (χ₂₃ - inducedClassFunction c.H0 (ν₁ - νθ (θ ν)))
              = inducedClassFunction c.H0 (ν₁ - νθ (θ ν)) -
                  inducedClassFunction c.H0 (ν₁ - νθ (θ μ)) := by
                ring
          _ = inducedClassFunction c.H0 ((ν₁ - νθ (θ ν)) - (ν₁ - νθ (θ μ))) := by
                rw [← inducedClassFunction_sub]
          _ = inducedClassFunction c.H0 (νθ (θ μ) - νθ (θ ν)) := by
                congr 1
                ring
      rw [← hrhs]
    change inducedClassFunction c.H0 (μ - ν) = lift (θ μ) - lift (θ ν)
    have hstep : μ - ν = (μ - νθ (θ μ)) + ((νθ (θ μ) - νθ (θ ν)) - (ν - νθ (θ ν))) := by
      ring
    rw [hstep]
    rw [show inducedClassFunction c.H0 (μ - νθ (θ μ) + ((νθ (θ μ) - νθ (θ ν)) - (ν - νθ (θ ν)))) =
          inducedClassFunction c.H0 (μ - νθ (θ μ)) +
            inducedClassFunction c.H0 ((νθ (θ μ) - νθ (θ ν)) - (ν - νθ (θ ν))) by
      exact inducedClassFunction_add c.H0 (μ - νθ (θ μ)) ((νθ (θ μ) - νθ (θ ν)) - (ν - νθ (θ ν)))]
    rw [show inducedClassFunction c.H0 ((νθ (θ μ) - νθ (θ ν)) - (ν - νθ (θ ν))) =
          inducedClassFunction c.H0 (νθ (θ μ) - νθ (θ ν)) - inducedClassFunction c.H0 (ν - νθ (θ ν)) by
      exact inducedClassFunction_sub c.H0 (νθ (θ μ) - νθ (θ ν)) (ν - νθ (θ ν))]
    rw [hμc, hνc]
    simp
    exact hmain
  · -- disjoint: the orthogonality `(θ̃(θμ), θ̃(θν)) = 0` (the preimage-pair
    -- case analysis: `a := νθ (θ μ) ∈ {ν₁, σν₁}` gives `θ̃ = χ₂₃`, else
    -- `θ̃ = χ₂₃ − δa*` with the `(χ₂₃, δa*) = 1`/`(δa*, δb*) = 1` pairings;
    -- the `a, b ∈ {ν₁, σν₁}`-simultaneous case contradicts `ν ≠ μ`/`σν ≠ μ`
    -- via the fiber `{a, σa}`) and the disjointness split on the norms
    -- (`disjoint_of_orthogonal_norm_one` for the norm-1 pairs,
    -- `disjoint_of_orthogonal_norm_one_two` for the mixed pairs, and
    -- `remark_1_5` for the norm-2 fixed pair — equal degrees via
    -- `(ν₁ − a)*(1) = 0`)
    intro ν μ hμL hνL hνμne hσνμ hθνΘ hθμΘ
    have hμL' : μ ∈ L := by
      rw [orbit_eq_of_mem c hνL] at hμL
      exact hμL
    have hμ' : νθ (θ μ) ∈ L ∧ θ (νθ (θ μ)) = θ μ := hw hθμΘ
    have hν' : νθ (θ ν) ∈ L ∧ θ (νθ (θ ν)) = θ ν := hw hθνΘ
    -- the `θ`-values of `μ, ν` are distinct: the fiber of `θ μ` is the
    -- `s`-pair `{a, σa}`, so `μ, ν` in it contradict `ν ≠ μ`/`σν ≠ μ`
    have hθμνne : θ μ ≠ θ ν := by
      intro hθeq
      have hfib : L.filter (fun ν => θ ν = θ μ) =
          ({νθ (θ μ), conjChar c.H0 (s_normalizes_H0 c h12) (νθ (θ μ))} :
            Finset (ClassFunction (↥c.H0))) :=
        theta_fiber_pair_of_invariant c h12 hν₀ hν₀s_inv hμ'.1 hμ'.2
      have hμfib : μ ∈ L.filter (fun ν => θ ν = θ μ) :=
        Finset.mem_filter.mpr ⟨hμL', rfl⟩
      have hνfib : ν ∈ L.filter (fun ν => θ ν = θ μ) :=
        Finset.mem_filter.mpr ⟨hνL, hθeq.symm⟩
      rw [hfib] at hμfib hνfib
      rw [Finset.mem_insert, Finset.mem_singleton] at hμfib hνfib
      rcases hμfib with hμ1 | hμ2
      · rcases hνfib with hν1 | hν2
        · exact hνμne (hν1.trans hμ1.symm)
        · exact hσνμ (by
            rw [hν2]
            rw [conjChar_conjChar c h12 (νθ (θ μ))]
            exact hμ1.symm)
      · rcases hνfib with hν1 | hν2
        · exact hσνμ (by
            rw [hν1]
            exact hμ2.symm)
        · exact hνμne (hν2.trans hμ2.symm)


    -- the lift-value forms
    have hliftμ : lift (θ μ) = χ₂₃ - inducedClassFunction c.H0 (ν₁ - νθ (θ μ)) := by rfl
    have hliftν : lift (θ ν) = χ₂₃ - inducedClassFunction c.H0 (ν₁ - νθ (θ ν)) := by rfl
    -- the orthogonality `(θ̃(θμ), θ̃(θν)) = 0`
    have horth : scalarProduct G (lift (θ μ)) (lift (θ ν)) = 0 := by
      by_cases hμ₁ : νθ (θ μ) = ν₁
      · by_cases hν₁' : νθ (θ ν) = ν₁
        · exfalso
          exact hθμνne (by
            rw [← hμ'.2, ← hν'.2, hμ₁, hν₁'])
        · by_cases hνσ : νθ (θ ν) = conjChar c.H0 (s_normalizes_H0 c h12) ν₁
          · exfalso
            exact hθμνne (by
              rw [← hμ'.2, ← hν'.2, hμ₁, hνσ]
              exact (inducedFromSub_conjChar_eq c h12 hH0index hν₁).symm)
          · -- `lift (θ μ) = χ₂₃`, `lift (θ ν) = χ₂₃ − δb*`
            have hzero : inducedClassFunction c.H0 (ν₁ - νθ (θ μ)) = 0 := by
              rw [hμ₁]
              rw [show ν₁ - ν₁ = (0 : ClassFunction (↥c.H0)) by simp]
              exact inducedClassFunction_zero c.H0
            rw [hliftμ, hliftν, hzero]
            simp
            rw [scalarProduct_sub_right]
            have hpairχχ : scalarProduct G χ₂₃ χ₂₃ = 1 := by
              change scalarProduct G χ₂₃ χ₂₃ = 1
              exact hχ₁
            have hpairχb : scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - νθ (θ ν))) = 1 :=
              hχall (νθ (θ ν)) hν'.1 (by intro hEq; exact hν₁' hEq)
                ((hσa_ne_ν₁).2 (by intro hEq; exact hνσ hEq))
            rw [hpairχχ, hpairχb]
            norm_num
      · by_cases hμσ : νθ (θ μ) = conjChar c.H0 (s_normalizes_H0 c h12) ν₁
        · by_cases hν₁' : νθ (θ ν) = ν₁
          · exfalso
            exact hθμνne (by
              rw [← hμ'.2, ← hν'.2, hμσ, hν₁']
              exact inducedFromSub_conjChar_eq c h12 hH0index hν₁)
          · by_cases hνσ : νθ (θ ν) = conjChar c.H0 (s_normalizes_H0 c h12) ν₁
            · exfalso
              exact hθμνne (by
                rw [← hμ'.2, ← hν'.2, hμσ, hνσ])
            · -- `lift (θ μ) = χ₂₃`, `lift (θ ν) = χ₂₃ − δb*`
              have hzero : inducedClassFunction c.H0 (ν₁ - νθ (θ μ)) = 0 := by
                rw [hμσ]
                rw [show ν₁ - conjChar c.H0 (s_normalizes_H0 c h12) ν₁ =
                    -(conjChar c.H0 (s_normalizes_H0 c h12) ν₁ - ν₁) by ring]
                rw [inducedClassFunction_neg, hσ₁₁]
                simp
              rw [hliftμ, hliftν, hzero]
              simp
              rw [scalarProduct_sub_right]
              have hpairχχ : scalarProduct G χ₂₃ χ₂₃ = 1 := by
                change scalarProduct G χ₂₃ χ₂₃ = 1
                exact hχ₁
              have hpairχb : scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - νθ (θ ν))) = 1 :=
                hχall (νθ (θ ν)) hν'.1 (by intro hEq; exact hν₁' hEq)
                ((hσa_ne_ν₁).2 (by intro hEq; exact hνσ hEq))
              rw [hpairχχ, hpairχb]
              norm_num
        · -- the generic `a`: `lift (θ μ) = χ₂₃ − δa*`
          by_cases hν₁' : νθ (θ ν) = ν₁
          · -- `lift (θ ν) = χ₂₃`
            have hzero : inducedClassFunction c.H0 (ν₁ - νθ (θ ν)) = 0 := by
              rw [hν₁']
              rw [show ν₁ - ν₁ = (0 : ClassFunction (↥c.H0)) by simp]
              exact inducedClassFunction_zero c.H0
            rw [hliftμ, hliftν, hzero]
            simp
            rw [scalarProduct_sub_left]
            have hpairχχ : scalarProduct G χ₂₃ χ₂₃ = 1 := by
              change scalarProduct G χ₂₃ χ₂₃ = 1
              exact hχ₁
            have hpairχa : scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - νθ (θ μ))) = 1 :=
              hχall (νθ (θ μ)) hμ'.1 (by intro hEq; exact hμ₁ hEq)
                ((hσa_ne_ν₁).2 (by intro hEq; exact hμσ hEq))
            have hpairaχ : scalarProduct G (inducedClassFunction c.H0 (ν₁ - νθ (θ μ))) χ₂₃ = 1 := by
              apply star_inj.mp
              rw [scalarProduct_star_comm]
              change scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - νθ (θ μ))) = star 1
              simpa using hpairχa
            rw [hpairχχ, hpairaχ]
            norm_num
          · by_cases hνσ : νθ (θ ν) = conjChar c.H0 (s_normalizes_H0 c h12) ν₁
            · -- `lift (θ ν) = χ₂₃`
              have hzero : inducedClassFunction c.H0 (ν₁ - νθ (θ ν)) = 0 := by
                rw [hνσ]
                rw [show ν₁ - conjChar c.H0 (s_normalizes_H0 c h12) ν₁ =
                    -(conjChar c.H0 (s_normalizes_H0 c h12) ν₁ - ν₁) by ring]
                rw [inducedClassFunction_neg, hσ₁₁]
                simp
              rw [hliftμ, hliftν, hzero]
              simp
              rw [scalarProduct_sub_left]
              have hpairχχ : scalarProduct G χ₂₃ χ₂₃ = 1 := by
                change scalarProduct G χ₂₃ χ₂₃ = 1
                exact hχ₁
              have hpairχa : scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - νθ (θ μ))) = 1 :=
                hχall (νθ (θ μ)) hμ'.1 (by intro hEq; exact hμ₁ hEq)
                ((hσa_ne_ν₁).2 (by intro hEq; exact hμσ hEq))
              have hpairaχ : scalarProduct G (inducedClassFunction c.H0 (ν₁ - νθ (θ μ))) χ₂₃ = 1 := by
                apply star_inj.mp
                rw [scalarProduct_star_comm]
                change scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - νθ (θ μ))) = star 1
                simpa using hpairχa
              rw [hpairχχ, hpairaχ]
              norm_num
            · -- the generic case: `θ̃(θμ) = χ₂₃ − δa*`, `θ̃(θν) = χ₂₃ − δb*`
              have hσ₁a : conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ≠ νθ (θ μ) := by
                intro hEq
                apply hμσ
                exact hEq.symm
              have hσ₁b : conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ≠ νθ (θ ν) := by
                intro hEq
                apply hνσ
                exact hEq.symm
              have hab : νθ (θ μ) ≠ νθ (θ ν) := by
                intro hEq
                apply hθμνne
                rw [← hμ'.2, ← hν'.2, hEq]
              have hσab : conjChar c.H0 (s_normalizes_H0 c h12) (νθ (θ μ)) ≠ νθ (θ ν) := by
                intro hEq
                apply hθμνne
                rw [← hμ'.2, ← hν'.2]
                rw [← hEq]
                exact (inducedFromSub_conjChar_eq c h12 hH0index (hνirr (νθ (θ μ)) hμ'.1)).symm
              rw [hliftμ, hliftν]
              rw [scalarProduct_sub_left, scalarProduct_sub_right, scalarProduct_sub_right]
              have hpairχχ : scalarProduct G χ₂₃ χ₂₃ = 1 := by
                change scalarProduct G χ₂₃ χ₂₃ = 1
                exact hχ₁
              have hpairχa : scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - νθ (θ μ))) = 1 :=
                hχall (νθ (θ μ)) hμ'.1 (by intro hEq; exact hμ₁ hEq)
                ((hσa_ne_ν₁).2 (by intro hEq; exact hμσ hEq))
              have hpairχb : scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - νθ (θ ν))) = 1 :=
                hχall (νθ (θ ν)) hν'.1 (by intro hEq; exact hν₁' hEq)
                ((hσa_ne_ν₁).2 (by intro hEq; exact hνσ hEq))
              have hpairaχ : scalarProduct G (inducedClassFunction c.H0 (ν₁ - νθ (θ μ))) χ₂₃ = 1 := by
                apply star_inj.mp
                rw [scalarProduct_star_comm]
                change scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - νθ (θ μ))) = star 1
                simpa using hpairχa
              have hpairδδ : scalarProduct G (inducedClassFunction c.H0 (ν₁ - νθ (θ μ)))
                  (inducedClassFunction c.H0 (ν₁ - νθ (θ ν))) = 1 := by
                have hsp := delta_pair_scalar (ν₁ := ν₁) (ν₂ := ν₁) (μ₁ := νθ (θ μ)) (μ₂ := νθ (θ ν))
                  c h12 hν₁ hν₁ (by rw [orbit_eq_of_mem c h₁₀]; exact hμ'.1)
                  (by rw [orbit_eq_of_mem c h₁₀]; exact hν'.1)
                change scalarProduct G (inducedClassFunction c.H0 (ν₁ - νθ (θ μ)))
                    (inducedClassFunction c.H0 (ν₁ - νθ (θ ν))) = 1
                rw [show inducedClassFunction c.H0 (ν₁ - νθ (θ μ)) =
                    -inducedClassFunction c.H0 (νθ (θ μ) - ν₁) by
                  rw [show ν₁ - νθ (θ μ) = -(νθ (θ μ) - ν₁) by ring]
                  rw [inducedClassFunction_neg]]
                rw [show inducedClassFunction c.H0 (ν₁ - νθ (θ ν)) =
                    -inducedClassFunction c.H0 (νθ (θ ν) - ν₁) by
                  rw [show ν₁ - νθ (θ ν) = -(νθ (θ ν) - ν₁) by ring]
                  rw [inducedClassFunction_neg]]
                rw [scalarProduct_neg_left, scalarProduct_neg_right, hsp]
                simp
                change scalarProduct (↥c.H) (θ (νθ (θ μ)) - θ ν₁) (θ (νθ (θ ν)) - θ ν₁) = 1
                rw [scalarProduct_sub_left, scalarProduct_sub_right, scalarProduct_sub_right]
                have hθ₁₁H : scalarProduct (↥c.H) (θ ν₁) (θ ν₁) = 1 := by
                  change normSq (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν₁) = 1
                  rw [theta_norm c h12 hH0index hν₁]
                  rw [if_neg hν₁s]
                have hθ₁aH : scalarProduct (↥c.H) (θ ν₁) (θ (νθ (θ μ))) = 0 := by
                  exact theta_pair_scalar_zero c h12 hH0index hν₁ (hνirr (νθ (θ μ)) hμ'.1)
                    (Ne.symm hμ₁) hσ₁a
                have hθa₁H : scalarProduct (↥c.H) (θ (νθ (θ μ))) (θ ν₁) = 0 := by
                  exact theta_pair_scalar_zero c h12 hH0index (hνirr (νθ (θ μ)) hμ'.1) hν₁
                    hμ₁ (by
                      intro hEq
                      apply hμσ
                      exact (conjChar_conjChar c h12 (νθ (θ μ))).symm.trans
                        (congrArg (conjChar c.H0 (s_normalizes_H0 c h12)) hEq))


                have hθ₁bH : scalarProduct (↥c.H) (θ ν₁) (θ (νθ (θ ν))) = 0 := by
                  exact theta_pair_scalar_zero c h12 hH0index hν₁ (hνirr (νθ (θ ν)) hν'.1)
                    (Ne.symm hν₁') hσ₁b
                have hθabH : scalarProduct (↥c.H) (θ (νθ (θ μ))) (θ (νθ (θ ν))) = 0 := by
                  exact theta_pair_scalar_zero c h12 hH0index (hνirr (νθ (θ μ)) hμ'.1)
                    (hνirr (νθ (θ ν)) hν'.1) hab hσab
                rw [hθabH, hθa₁H, hθ₁bH, hθ₁₁H]
                norm_num
              rw [hpairχχ, hpairχb, hpairaχ, hpairδδ]
              norm_num
    -- the norms of the lift values: 1 on the non-fixed values, 2 on the fixed
    have hnorm1 : ∀ θ' ∈ Θ, conjChar c.H0 (s_normalizes_H0 c h12) (νθ θ') ≠ νθ θ' →
        normSq G (lift θ') = 1 := by
      intro θ' hθ' hfix
      have hw' : νθ θ' ∈ L ∧ θ (νθ θ') = θ' := hw hθ'
      by_cases h₁ : νθ θ' = ν₁
      · have hzero : inducedClassFunction c.H0 (ν₁ - νθ θ') = 0 := by
          rw [h₁]
          rw [show ν₁ - ν₁ = (0 : ClassFunction (↥c.H0)) by simp]
          exact inducedClassFunction_zero c.H0
        unfold lift
        rw [hzero]
        simp
        change scalarProduct G χ₂₃ χ₂₃ = 1
        exact hχ₁
      · by_cases h₂ : νθ θ' = conjChar c.H0 (s_normalizes_H0 c h12) ν₁
        · have hzero : inducedClassFunction c.H0 (ν₁ - νθ θ') = 0 := by
            rw [h₂]
            rw [show ν₁ - conjChar c.H0 (s_normalizes_H0 c h12) ν₁ =
                -(conjChar c.H0 (s_normalizes_H0 c h12) ν₁ - ν₁) by ring]
            rw [inducedClassFunction_neg, hσ₁₁]
            simp
          unfold lift
          rw [hzero]
          simp
          change scalarProduct G χ₂₃ χ₂₃ = 1
          exact hχ₁
        · have hχa : scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - νθ θ')) = 1 :=
            hχall (νθ θ') hw'.1 (by intro hEq; exact h₁ hEq)
              ((hσa_ne_ν₁).2 (by intro hEq; exact h₂ hEq))
          unfold lift
          change scalarProduct G (χ₂₃ - inducedClassFunction c.H0 (ν₁ - νθ θ'))
              (χ₂₃ - inducedClassFunction c.H0 (ν₁ - νθ θ')) = 1
          rw [scalarProduct_sub_left, scalarProduct_sub_right, scalarProduct_sub_right]
          have hχχ : scalarProduct G χ₂₃ χ₂₃ = 1 := by
            change scalarProduct G χ₂₃ χ₂₃ = 1
            exact hχ₁
          have hδχ : scalarProduct G (inducedClassFunction c.H0 (ν₁ - νθ θ')) χ₂₃ = 1 := by
            apply star_inj.mp
            rw [scalarProduct_star_comm]
            change scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - νθ θ')) = star 1
            simpa using hχa
          have hδδ : scalarProduct G (inducedClassFunction c.H0 (ν₁ - νθ θ'))
              (inducedClassFunction c.H0 (ν₁ - νθ θ')) = 2 := by
            change normSq G (inducedClassFunction c.H0 (ν₁ - νθ θ')) = 2
            have hσ₁a : conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ≠ νθ θ' := by
              intro hEq
              apply h₂
              exact hEq.symm
            have h₁a : ν₁ ∈ orbit c.H0 c.U (νθ θ') := by
              rw [orbit_eq_of_mem c hw'.1]
              exact h₁₀
            rw [delta_norm c h12 hH0index hν₁ (hνirr (νθ θ') hw'.1) h₁a (Ne.symm h₁) hσ₁a]
            rw [theta_norm c h12 hH0index hν₁, theta_norm c h12 hH0index (hνirr (νθ θ') hw'.1)]
            rw [if_neg hν₁s, if_neg hfix]
            norm_num
          rw [hχχ, hχa, hδχ, hδδ]
          norm_num
    have hnorm2 : ∀ θ' ∈ Θ, conjChar c.H0 (s_normalizes_H0 c h12) (νθ θ') = νθ θ' →
        normSq G (lift θ') = 2 := by
      intro θ' hθ' hfix
      have hw' : νθ θ' ∈ L ∧ θ (νθ θ') = θ' := hw hθ'
      by_cases h₁ : νθ θ' = ν₁
      · exfalso
        apply hν₁s
        rw [← h₁]
        exact hfix
      · by_cases h₂ : νθ θ' = conjChar c.H0 (s_normalizes_H0 c h12) ν₁
        · exfalso
          apply hν₁s
          exact (h₂.symm.trans hfix.symm).trans
            ((congrArg (conjChar c.H0 (s_normalizes_H0 c h12)) h₂).trans
              (conjChar_conjChar c h12 ν₁))


        · have hχa : scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - νθ θ')) = 1 :=
            hχall (νθ θ') hw'.1 (by intro hEq; exact h₁ hEq)
              ((hσa_ne_ν₁).2 (by intro hEq; exact h₂ hEq))
          unfold lift
          change scalarProduct G (χ₂₃ - inducedClassFunction c.H0 (ν₁ - νθ θ'))
              (χ₂₃ - inducedClassFunction c.H0 (ν₁ - νθ θ')) = 2
          rw [scalarProduct_sub_left, scalarProduct_sub_right, scalarProduct_sub_right]
          have hχχ : scalarProduct G χ₂₃ χ₂₃ = 1 := by
            change scalarProduct G χ₂₃ χ₂₃ = 1
            exact hχ₁
          have hδχ : scalarProduct G (inducedClassFunction c.H0 (ν₁ - νθ θ')) χ₂₃ = 1 := by
            apply star_inj.mp
            rw [scalarProduct_star_comm]
            change scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - νθ θ')) = star 1
            simpa using hχa
          have hδδ : scalarProduct G (inducedClassFunction c.H0 (ν₁ - νθ θ'))
              (inducedClassFunction c.H0 (ν₁ - νθ θ')) = 3 := by
            change normSq G (inducedClassFunction c.H0 (ν₁ - νθ θ')) = 3
            have hσ₁a : conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ≠ νθ θ' := by
              intro hEq
              apply h₂
              exact hEq.symm
            have h₁a : ν₁ ∈ orbit c.H0 c.U (νθ θ') := by
              rw [orbit_eq_of_mem c hw'.1]
              exact h₁₀
            rw [delta_norm c h12 hH0index hν₁ (hνirr (νθ θ') hw'.1) h₁a (Ne.symm h₁) hσ₁a]
            rw [theta_norm c h12 hH0index hν₁, theta_norm c h12 hH0index (hνirr (νθ θ') hw'.1)]
            rw [if_neg hν₁s, if_pos hfix]
            norm_num
          rw [hχχ, hχa, hδχ, hδδ]
          norm_num
    -- the equal degrees of the fixed values: both are `χ₂₃(1)` (the
    -- `δ*(1) = 0` for the equal-degree orbit members)
    have hdegμν : (lift (θ μ)) 1 = (lift (θ ν)) 1 := by
      have hδμ1 : (inducedClassFunction c.H0 (ν₁ - νθ (θ μ))) 1 = 0 := by
        exact inducedFromSub_one_eq c h12 (orbit_mem_degree_eq c (by
          rw [orbit_eq_of_mem c h₁₀]
          exact hμ'.1)).symm
      have hδν1 : (inducedClassFunction c.H0 (ν₁ - νθ (θ ν))) 1 = 0 := by
        exact inducedFromSub_one_eq c h12 (orbit_mem_degree_eq c (by
          rw [orbit_eq_of_mem c h₁₀]
          exact hν'.1)).symm
      unfold lift
      simp [hδμ1, hδν1]


    -- the fixed-ness transfers: `x` is `s`-fixed iff `νθ (θ x)` is (the
    -- `θ`-fiber of `x` is the `s`-pair `{a, σa}`)
    have hfixνθ : ∀ {x : ClassFunction (↥c.H0)}, x ∈ L →
        (conjChar c.H0 (s_normalizes_H0 c h12) x = x ↔
          conjChar c.H0 (s_normalizes_H0 c h12) (νθ (θ x)) = νθ (θ x)) := by
      intro x hxL
      have hx' : νθ (θ x) ∈ L ∧ θ (νθ (θ x)) = θ x := hw (thetaOfOrbit_mem c h12 hxL)
      have hfib : L.filter (fun ν => θ ν = θ x) =
          ({νθ (θ x), conjChar c.H0 (s_normalizes_H0 c h12) (νθ (θ x))} :
            Finset (ClassFunction (↥c.H0))) :=
        theta_fiber_pair_of_invariant c h12 hν₀ hν₀s_inv hx'.1 hx'.2
      have hxfib : x ∈ L.filter (fun ν => θ ν = θ x) :=
        Finset.mem_filter.mpr ⟨hxL, rfl⟩
      rw [hfib] at hxfib
      rw [Finset.mem_insert, Finset.mem_singleton] at hxfib
      rcases hxfib with h | h
      · constructor
        · intro hEq
          rw [← h]
          exact hEq
        · intro hEq
          rw [h]
          exact hEq
      · constructor
        · intro hEq
          rw [h] at hEq
          exact hEq.symm.trans (conjChar_conjChar c h12 (νθ (θ x)))
        · intro hEq
          rw [h]
          exact (conjChar_conjChar c h12 (νθ (θ x))).trans hEq.symm
    -- the disjointness, split on the fixed-ness (the norm-1/norm-2 values)
    by_cases hμfix : conjChar c.H0 (s_normalizes_H0 c h12) μ = μ
    · by_cases hνfix : conjChar c.H0 (s_normalizes_H0 c h12) ν = ν
      · -- both fixed: the norm-2 pair via `remark_1_5`
        exact remark_1_5 (hgen (θ μ) hθμΘ) (hgen (θ ν) hθνΘ)
          (hnorm2 (θ μ) hθμΘ (by
            rw [← hfixνθ hμL']
            exact hμfix))
          (hnorm2 (θ ν) hθνΘ (by
            rw [← hfixνθ hνL]
            exact hνfix))
          hdegμν horth
      · -- `μ` fixed (norm 2), `ν` non-fixed (norm 1)
        exact disjoint_comm (disjoint_of_orthogonal_norm_one_two
          (hgen (θ ν) hθνΘ) (hgen (θ μ) hθμΘ)
          (by change scalarProduct G (lift (θ ν)) (lift (θ ν)) = 1
              exact hnorm1 (θ ν) hθνΘ (by
                intro hEq
                exact hνfix ((hfixνθ hνL).2 hEq)))
          (by change scalarProduct G (lift (θ μ)) (lift (θ μ)) = 2
              exact hnorm2 (θ μ) hθμΘ (by
                rw [← hfixνθ hμL']
                exact hμfix))
          (by
            rw [← scalarProduct_star_comm]
            simpa using congrArg star horth))
    · by_cases hνfix : conjChar c.H0 (s_normalizes_H0 c h12) ν = ν
      · -- `μ` non-fixed (norm 1), `ν` fixed (norm 2)
        exact disjoint_of_orthogonal_norm_one_two (hgen (θ μ) hθμΘ) (hgen (θ ν) hθνΘ)
          (by change scalarProduct G (lift (θ μ)) (lift (θ μ)) = 1
              exact hnorm1 (θ μ) hθμΘ (by
                intro hEq
                exact hμfix ((hfixνθ hμL').2 hEq)))
          (by change scalarProduct G (lift (θ ν)) (lift (θ ν)) = 2
              exact hnorm2 (θ ν) hθνΘ (by
                rw [← hfixνθ hνL]
                exact hνfix))
          horth
      · -- both non-fixed: the norm-1 pair
        exact disjoint_of_orthogonal_norm_one (hgen (θ μ) hθμΘ) (hgen (θ ν) hθνΘ)
          (by change scalarProduct G (lift (θ μ)) (lift (θ μ)) = 1
              exact hnorm1 (θ μ) hθμΘ (by
                intro hEq
                exact hμfix ((hfixνθ hμL').2 hEq)))
          (by change scalarProduct G (lift (θ ν)) (lift (θ ν)) = 1
              exact hnorm1 (θ ν) hθνΘ (by
                intro hEq
                exact hνfix ((hfixνθ hνL).2 hEq)))
          horth


/-- The `(vi)`-pair data for one sign-chosen companion `μ` of a non-fixed
`ν₂`: the orbit lift restricted to the two `θ`-fibers is generalized,
norm-one, and satisfies the induced-difference identity and the `T`-value
identity.  This is the fixed-member contradiction's `θ̃₂(t) = 2ν₂(t)` input,
split out so the caller does not carry the whole orbit-lift construction. -/
private lemma theta_tilde_two_pair_data (c : Hyp11 G) (h12 : Hyp12 c)
    (hH0index : (c.H0.subgroupOf c.H).index = 2)
    {ν₀ ν₁ ν₂ ν₃ μ : ClassFunction (↥c.H0)}
    (hν₀ : IsIrreducibleCharacter ν₀) (hν₁ : IsIrreducibleCharacter ν₁)
    (hν₂ : IsIrreducibleCharacter ν₂) (hν₃ : IsIrreducibleCharacter ν₃)
    (hμ : IsIrreducibleCharacter μ)
    (h_inv : conjChar c.H0 (s_normalizes_H0 c h12) ν₀ ∈ orbit c.H0 c.U ν₀)
    (hν₁L : ν₁ ∈ orbit c.H0 c.U ν₀) (hν₂L : ν₂ ∈ orbit c.H0 c.U ν₀)
    (hν₃L : ν₃ ∈ orbit c.H0 c.U ν₀) (hμL : μ ∈ orbit c.H0 c.U ν₀)
    (hν₁s : conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ≠ ν₁)
    (hν₂s : conjChar c.H0 (s_normalizes_H0 c h12) ν₂ ≠ ν₂)
    (hν₃s : conjChar c.H0 (s_normalizes_H0 c h12) ν₃ ≠ ν₃)
    (hμs : conjChar c.H0 (s_normalizes_H0 c h12) μ ≠ μ)
    (hν₂₁ : ν₂ ∈ orbit c.H0 c.U ν₁) (hν₃₁ : ν₃ ∈ orbit c.H0 c.U ν₁)
    (hμ₁ : μ ∈ orbit c.H0 c.U ν₁)
    (h₁₂ : ν₁ ≠ ν₂ ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ≠ ν₂)
    (h₁₃ : ν₁ ≠ ν₃ ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ≠ ν₃)
    (h₂₃ : ν₂ ≠ ν₃ ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₂ ≠ ν₃)
    {χ₂₃ : ClassFunction G}
    (hχsig : IsIrreducibleCharacter χ₂₃ ∨ IsIrreducibleCharacter (-χ₂₃))
    (hχg : IsGeneralizedCharacter χ₂₃) (hχ₁ : normSq G χ₂₃ = 1)
    (hχ₂ : scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - ν₂)) = 1)
    (hχ₃ : scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - ν₃)) = 1) :
    ∃ thetaTilde : ClassFunction (↥c.H) → ClassFunction G,
      IsGeneralizedCharacter (thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 ν₂)) ∧
      IsGeneralizedCharacter (thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 μ)) ∧
      normSq G (thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 ν₂)) = 1 ∧
      normSq G (thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 μ)) = 1 ∧
      inducedClassFunction c.H0 (μ - ν₂) =
        thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 μ) -
          thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 ν₂) ∧
      (∀ hg : c.t ∈ c.H, (inducedClassFunction c.H0 (μ - ν₂)) c.t =
        (inducedFromSub (h12.H0_normal_in_H).1 μ) ⟨c.t, hg⟩ -
          (inducedFromSub (h12.H0_normal_in_H).1 ν₂) ⟨c.t, hg⟩) ∧
      thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 ν₂) =
        χ₂₃ - inducedClassFunction c.H0 (ν₁ - ν₂) := by
  classical
  let L : Finset (ClassFunction (↥c.H0)) := orbit c.H0 c.U ν₀
  let Θ : Finset (ClassFunction (↥c.H)) := thetaOfOrbit c h12 L
  let θ : ClassFunction (↥c.H0) → ClassFunction (↥c.H) := fun a =>
    inducedFromSub (h12.H0_normal_in_H).1 a
  let νθ : ClassFunction (↥c.H) → ClassFunction (↥c.H0) := fun θ' =>
    if h : θ' ∈ Θ then Classical.choose (Finset.mem_image.mp h) else ν₁
  let lift : ClassFunction (↥c.H) → ClassFunction G := fun θ' =>
    χ₂₃ - inducedClassFunction c.H0 (ν₁ - νθ θ')
  have hνirr : ∀ a ∈ L, IsIrreducibleCharacter a :=
    fun a ha => orbit_mem_isIrreducible c.H0 c.U hν₀ ha
  have hν₁L' : ν₁ ∈ L := hν₁L
  have hν₂L' : ν₂ ∈ L := hν₂L
  have hν₃L' : ν₃ ∈ L := hν₃L
  have hμL' : μ ∈ L := hμL
  have hw : ∀ {θ' : ClassFunction (↥c.H)}, θ' ∈ Θ → νθ θ' ∈ L ∧ θ (νθ θ') = θ' := by
    intro θ' hθ'
    unfold νθ
    rw [dif_pos hθ']
    exact Classical.choose_spec (Finset.mem_image.mp hθ')
  have hpair_zero : ∀ {ν μ : ClassFunction (↥c.H0)},
      ν ∈ L → μ ∈ L → θ μ = θ ν → inducedClassFunction c.H0 (μ - ν) = 0 := by
    intro ν μ hνL hμL hθeq
    have hnorm : normSq G (inducedClassFunction c.H0 (μ - ν)) = 0 := by
      have hμν : μ ∈ orbit c.H0 c.U ν := by
        rw [orbit_eq_of_mem c hνL]
        exact hμL
      have hsp := delta_pair_scalar (ν₁ := ν) (ν₂ := ν) (μ₁ := μ) (μ₂ := μ)
        c h12 (hνirr ν hνL) (hνirr ν hνL) hμν hμν
      change scalarProduct G (inducedClassFunction c.H0 (μ - ν))
          (inducedClassFunction c.H0 (μ - ν)) = 0
      rw [hsp]
      change scalarProduct (↥c.H) (θ μ - θ ν) (θ μ - θ ν) = 0
      simp [hθeq, scalarProduct]
    exact (normSq_eq_zero_iff (inducedClassFunction c.H0 (μ - ν))).1 hnorm
  have hgenν : IsGeneralizedCharacter (lift (θ ν₂)) := by
    unfold lift
    have hw' := hw (thetaOfOrbit_mem c h12 hν₂L')
    exact isGeneralizedCharacter_sub hχg (isGeneralizedCharacter_induced
      c h12 (ν₁ - νθ (θ ν₂))
      (isGeneralizedCharacter_sub_irr hν₁ (hνirr (νθ (θ ν₂)) hw'.1)))
  have hgenμ : IsGeneralizedCharacter (lift (θ μ)) := by
    unfold lift
    have hw' := hw (thetaOfOrbit_mem c h12 hμL')
    exact isGeneralizedCharacter_sub hχg (isGeneralizedCharacter_induced
      c h12 (ν₁ - νθ (θ μ))
      (isGeneralizedCharacter_sub_irr hν₁ (hνirr (νθ (θ μ)) hw'.1)))
  have hnormν : normSq G (lift (θ ν₂)) = 1 := by
    have hw' := hw (thetaOfOrbit_mem c h12 hν₂L')
    by_cases hb : νθ (θ ν₂) = ν₂
    · unfold lift
      rw [hb]
      have hδ₂self : scalarProduct G (inducedClassFunction c.H0 (ν₁ - ν₂))
          (inducedClassFunction c.H0 (ν₁ - ν₂)) = 2 := by
        change normSq G (inducedClassFunction c.H0 (ν₁ - ν₂)) = 2
        rw [delta_norm c h12 hH0index hν₁ hν₂ (by
          rw [orbit_eq_of_mem c hν₂L']
          exact hν₁L') h₁₂.1 h₁₂.2]
        rw [theta_norm c h12 hH0index hν₁, theta_norm c h12 hH0index hν₂]
        rw [if_neg hν₁s, if_neg hν₂s]
        norm_num
      have hδ₂χ : scalarProduct G (inducedClassFunction c.H0 (ν₁ - ν₂)) χ₂₃ = 1 := by
        apply star_inj.mp
        rw [scalarProduct_star_comm]
        change scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - ν₂)) = star 1
        simpa using hχ₂
      change normSq G (χ₂₃ - inducedClassFunction c.H0 (ν₁ - ν₂)) = 1
      unfold normSq
      rw [scalarProduct_sub_left, scalarProduct_sub_right, scalarProduct_sub_right]
      change scalarProduct G χ₂₃ χ₂₃ = 1 at hχ₁
      rw [hχ₁, hχ₂, hδ₂χ, hδ₂self]
      norm_num
    · have hbσ : νθ (θ ν₂) = conjChar c.H0 (s_normalizes_H0 c h12) ν₂ := by
        have hEqθ : θ (νθ (θ ν₂)) = θ ν₂ := (hw (thetaOfOrbit_mem c h12 hν₂L')).2
        have hcases := theta_eq_imp_conj c h12 hH0index
          (ν₁ := ν₂) (ν₂ := νθ (θ ν₂))
          hν₂ (hνirr (νθ (θ ν₂)) (hw (thetaOfOrbit_mem c h12 hν₂L')).1) hEqθ.symm
        rcases hcases with h | h
        · exact False.elim (hb h)
        · have h' := congrArg (conjChar c.H0 (s_normalizes_H0 c h12)) h
          rw [conjChar_conjChar c h12 (νθ (θ ν₂))] at h'
          exact h'
      unfold lift
      rw [hbσ]
      have hδ : inducedClassFunction c.H0
          (ν₁ - conjChar c.H0 (s_normalizes_H0 c h12) ν₂) =
          inducedClassFunction c.H0 (ν₁ - ν₂) := by
        have hzero : inducedClassFunction c.H0
            (conjChar c.H0 (s_normalizes_H0 c h12) ν₂ - ν₂) = 0 :=
          sigma_pair_star_zero_of_invariant c h12 hH0index hν₀ h_inv hν₂L'
        rw [show ν₁ - conjChar c.H0 (s_normalizes_H0 c h12) ν₂ =
            (ν₁ - ν₂) - (conjChar c.H0 (s_normalizes_H0 c h12) ν₂ - ν₂) by ring]
        rw [inducedClassFunction_sub, hzero]
        simp
      rw [hδ]
      have hδ₂self : scalarProduct G (inducedClassFunction c.H0 (ν₁ - ν₂))
          (inducedClassFunction c.H0 (ν₁ - ν₂)) = 2 := by
        change normSq G (inducedClassFunction c.H0 (ν₁ - ν₂)) = 2
        rw [delta_norm c h12 hH0index hν₁ hν₂ (by
          rw [orbit_eq_of_mem c hν₂L']
          exact hν₁L') h₁₂.1 h₁₂.2]
        rw [theta_norm c h12 hH0index hν₁, theta_norm c h12 hH0index hν₂]
        rw [if_neg hν₁s, if_neg hν₂s]
        norm_num
      have hδ₂χ : scalarProduct G (inducedClassFunction c.H0 (ν₁ - ν₂)) χ₂₃ = 1 := by
        apply star_inj.mp
        rw [scalarProduct_star_comm]
        change scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - ν₂)) = star 1
        simpa using hχ₂
      change normSq G (χ₂₃ - inducedClassFunction c.H0 (ν₁ - ν₂)) = 1
      unfold normSq
      rw [scalarProduct_sub_left, scalarProduct_sub_right, scalarProduct_sub_right]
      change scalarProduct G χ₂₃ χ₂₃ = 1 at hχ₁
      rw [hχ₁, hχ₂, hδ₂χ, hδ₂self]
      norm_num
  have hnormμ : normSq G (lift (θ μ)) = 1 := by
    have hw' := hw (thetaOfOrbit_mem c h12 hμL')
    let b := νθ (θ μ)
    have hbL : b ∈ L := hw'.1
    have hbL' : b ∈ orbit c.H0 c.U ν₁ := by
      rw [orbit_eq_of_mem c hν₁L']
      exact hbL
    have hbirr : IsIrreducibleCharacter b := hνirr b hbL
    have hθb : θ b = θ μ := hw'.2
    by_cases hbσ₂ : b = conjChar c.H0 (s_normalizes_H0 c h12) ν₂
    · unfold lift
      change normSq G (χ₂₃ - inducedClassFunction c.H0 (ν₁ - b)) = 1
      rw [hbσ₂]
      have hδ : inducedClassFunction c.H0
          (ν₁ - conjChar c.H0 (s_normalizes_H0 c h12) ν₂) =
          inducedClassFunction c.H0 (ν₁ - ν₂) := by
        have hzero : inducedClassFunction c.H0
            (conjChar c.H0 (s_normalizes_H0 c h12) ν₂ - ν₂) = 0 :=
          sigma_pair_star_zero_of_invariant c h12 hH0index hν₀ h_inv hν₂L'
        rw [show ν₁ - conjChar c.H0 (s_normalizes_H0 c h12) ν₂ =
            (ν₁ - ν₂) - (conjChar c.H0 (s_normalizes_H0 c h12) ν₂ - ν₂) by ring]
        rw [inducedClassFunction_sub, hzero]
        simp
      rw [hδ]
      have hδ₂self : scalarProduct G (inducedClassFunction c.H0 (ν₁ - ν₂))
          (inducedClassFunction c.H0 (ν₁ - ν₂)) = 2 := by
        change normSq G (inducedClassFunction c.H0 (ν₁ - ν₂)) = 2
        rw [delta_norm c h12 hH0index hν₁ hν₂ (by
          rw [orbit_eq_of_mem c hν₂L']
          exact hν₁L') h₁₂.1 h₁₂.2]
        rw [theta_norm c h12 hH0index hν₁, theta_norm c h12 hH0index hν₂]
        rw [if_neg hν₁s, if_neg hν₂s]
        norm_num
      have hδ₂χ : scalarProduct G (inducedClassFunction c.H0 (ν₁ - ν₂)) χ₂₃ = 1 := by
        apply star_inj.mp
        rw [scalarProduct_star_comm]
        change scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - ν₂)) = star 1
        simpa using hχ₂
      change normSq G (χ₂₃ - inducedClassFunction c.H0 (ν₁ - ν₂)) = 1
      unfold normSq
      rw [scalarProduct_sub_left, scalarProduct_sub_right, scalarProduct_sub_right]
      change scalarProduct G χ₂₃ χ₂₃ = 1 at hχ₁
      rw [hχ₁, hχ₂, hδ₂χ, hδ₂self]
      norm_num
    · by_cases hbν₁ : b = ν₁
      · unfold lift
        change normSq G (χ₂₃ - inducedClassFunction c.H0 (ν₁ - b)) = 1
        rw [hbν₁]
        have hzero : inducedClassFunction c.H0 (ν₁ - ν₁) = 0 := by
          rw [show ν₁ - ν₁ = (0 : ClassFunction (↥c.H0)) by simp]
          exact inducedClassFunction_zero c.H0
        rw [hzero]
        simp [hχ₁]
      · by_cases hbσ₁ : b = conjChar c.H0 (s_normalizes_H0 c h12) ν₁
        · unfold lift
          change normSq G (χ₂₃ - inducedClassFunction c.H0 (ν₁ - b)) = 1
          rw [hbσ₁]
          have hzero' : inducedClassFunction c.H0
              (conjChar c.H0 (s_normalizes_H0 c h12) ν₁ - ν₁) = 0 :=
            sigma_pair_star_zero_of_invariant c h12 hH0index hν₀ h_inv hν₁L'
          have hzero : inducedClassFunction c.H0
              (ν₁ - conjChar c.H0 (s_normalizes_H0 c h12) ν₁) = 0 := by
            rw [show ν₁ - conjChar c.H0 (s_normalizes_H0 c h12) ν₁ =
                -(conjChar c.H0 (s_normalizes_H0 c h12) ν₁ - ν₁) by ring]
            rw [inducedClassFunction_neg, hzero']
            simp
          rw [hzero]
          simp [hχ₁]
        · by_cases hbν₂ : b = ν₂
          · unfold lift
            change normSq G (χ₂₃ - inducedClassFunction c.H0 (ν₁ - b)) = 1
            rw [hbν₂]
            have hδ₂self : scalarProduct G (inducedClassFunction c.H0 (ν₁ - ν₂))
                (inducedClassFunction c.H0 (ν₁ - ν₂)) = 2 := by
              change normSq G (inducedClassFunction c.H0 (ν₁ - ν₂)) = 2
              rw [delta_norm c h12 hH0index hν₁ hν₂ (by
                rw [orbit_eq_of_mem c hν₂L']
                exact hν₁L') h₁₂.1 h₁₂.2]
              rw [theta_norm c h12 hH0index hν₁, theta_norm c h12 hH0index hν₂]
              rw [if_neg hν₁s, if_neg hν₂s]
              norm_num
            have hδ₂χ : scalarProduct G (inducedClassFunction c.H0 (ν₁ - ν₂)) χ₂₃ = 1 := by
              apply star_inj.mp
              rw [scalarProduct_star_comm]
              change scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - ν₂)) = star 1
              simpa using hχ₂
            change normSq G (χ₂₃ - inducedClassFunction c.H0 (ν₁ - ν₂)) = 1
            unfold normSq
            rw [scalarProduct_sub_left, scalarProduct_sub_right, scalarProduct_sub_right]
            change scalarProduct G χ₂₃ χ₂₃ = 1 at hχ₁
            rw [hχ₁, hχ₂, hδ₂χ, hδ₂self]
            norm_num
          · by_cases hbν₃ : b = ν₃
            · unfold lift
              change normSq G (χ₂₃ - inducedClassFunction c.H0 (ν₁ - b)) = 1
              rw [hbν₃]
              have hδ₃χ : scalarProduct G (inducedClassFunction c.H0 (ν₁ - ν₃)) χ₂₃ = 1 := by
                apply star_inj.mp
                rw [scalarProduct_star_comm]
                change scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - ν₃)) = star 1
                simpa using hχ₃
              have hδ₃self : scalarProduct G (inducedClassFunction c.H0 (ν₁ - ν₃))
                  (inducedClassFunction c.H0 (ν₁ - ν₃)) = 2 := by
                change normSq G (inducedClassFunction c.H0 (ν₁ - ν₃)) = 2
                rw [delta_norm c h12 hH0index hν₁ hν₃ (by
                  rw [orbit_eq_of_mem c hν₃L']
                  exact hν₁L') h₁₃.1 h₁₃.2]
                rw [theta_norm c h12 hH0index hν₁, theta_norm c h12 hH0index hν₃]
                rw [if_neg hν₁s, if_neg hν₃s]
                norm_num
              change normSq G (χ₂₃ - inducedClassFunction c.H0 (ν₁ - ν₃)) = 1
              unfold normSq
              rw [scalarProduct_sub_left, scalarProduct_sub_right, scalarProduct_sub_right]
              change scalarProduct G χ₂₃ χ₂₃ = 1 at hχ₁
              rw [hχ₁, hχ₃, hδ₃χ, hδ₃self]
              norm_num
            · by_cases hbσ₃ : b = conjChar c.H0 (s_normalizes_H0 c h12) ν₃
              · unfold lift
                change normSq G (χ₂₃ - inducedClassFunction c.H0 (ν₁ - b)) = 1
                rw [hbσ₃]
                have hδ : inducedClassFunction c.H0
                    (ν₁ - conjChar c.H0 (s_normalizes_H0 c h12) ν₃) =
                    inducedClassFunction c.H0 (ν₁ - ν₃) := by
                  have hzero : inducedClassFunction c.H0
                      (conjChar c.H0 (s_normalizes_H0 c h12) ν₃ - ν₃) = 0 :=
                    sigma_pair_star_zero_of_invariant c h12 hH0index hν₀ h_inv hν₃L'
                  rw [show ν₁ - conjChar c.H0 (s_normalizes_H0 c h12) ν₃ =
                      (ν₁ - ν₃) - (conjChar c.H0 (s_normalizes_H0 c h12) ν₃ - ν₃) by ring]
                  rw [inducedClassFunction_sub, hzero]
                  simp
                rw [hδ]
                have hδ₃χ : scalarProduct G (inducedClassFunction c.H0 (ν₁ - ν₃)) χ₂₃ = 1 := by
                  apply star_inj.mp
                  rw [scalarProduct_star_comm]
                  change scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - ν₃)) = star 1
                  simpa using hχ₃
                have hδ₃self : scalarProduct G (inducedClassFunction c.H0 (ν₁ - ν₃))
                    (inducedClassFunction c.H0 (ν₁ - ν₃)) = 2 := by
                  change normSq G (inducedClassFunction c.H0 (ν₁ - ν₃)) = 2
                  rw [delta_norm c h12 hH0index hν₁ hν₃ (by
                    rw [orbit_eq_of_mem c hν₃L']
                    exact hν₁L') h₁₃.1 h₁₃.2]
                  rw [theta_norm c h12 hH0index hν₁, theta_norm c h12 hH0index hν₃]
                  rw [if_neg hν₁s, if_neg hν₃s]
                  norm_num
                change normSq G (χ₂₃ - inducedClassFunction c.H0 (ν₁ - ν₃)) = 1
                unfold normSq
                rw [scalarProduct_sub_left, scalarProduct_sub_right, scalarProduct_sub_right]
                change scalarProduct G χ₂₃ χ₂₃ = 1 at hχ₁
                rw [hχ₁, hχ₃, hδ₃χ, hδ₃self]
                norm_num
              · have hbs : conjChar c.H0 (s_normalizes_H0 c h12) b ≠ b := by
                  intro hfix
                  apply hμs
                  have hcases := theta_eq_imp_conj c h12 hH0index
                    (ν₁ := b) (ν₂ := μ) hbirr hμ hθb
                  rcases hcases with h | h
                  · rw [h]
                    exact hfix
                  · have hμb : μ = b := by
                      have h' := congrArg (conjChar c.H0 (s_normalizes_H0 c h12)) h
                      rw [conjChar_conjChar c h12 μ] at h'
                      rw [hfix] at h'
                      exact h'
                    rw [hμb]
                    exact hfix
                have hσ₁b : conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ≠ b := by
                  intro hEq
                  exact hbσ₁ hEq.symm
                have h₁b : ν₁ ≠ b ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ≠ b :=
                  ⟨fun hEq => hbν₁ hEq.symm, hσ₁b⟩
                have h₂b : ν₂ ≠ b ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₂ ≠ b :=
                  ⟨fun hEq => hbν₂ hEq.symm, fun hEq => hbσ₂ hEq.symm⟩
                have h₃b : ν₃ ≠ b ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₃ ≠ b :=
                  ⟨fun hEq => hbν₃ hEq.symm, fun hEq => hbσ₃ hEq.symm⟩
                have hδbnorm : normSq G (inducedClassFunction c.H0 (ν₁ - b)) = 2 := by
                  have h₁b' : ν₁ ∈ orbit c.H0 c.U b := by
                    rw [orbit_eq_of_mem c hbL]
                    exact hν₁L'
                  rw [delta_norm c h12 hH0index hν₁ hbirr h₁b' h₁b.1 h₁b.2]
                  rw [theta_norm c h12 hH0index hν₁, theta_norm c h12 hH0index hbirr]
                  rw [if_neg hν₁s, if_neg hbs]
                  norm_num
                have hχb : scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - b)) = 1 :=
                  pairing_eq_one_of_norm_two c h12 hH0index
                    hν₁ hν₂ hν₃ hbirr hν₂₁ hν₃₁ hbL'
                    hν₁s hν₂s hν₃s hbs h₁₂ h₁₃ h₁b h₂₃ h₂b h₃b
                    hχsig hχg hχ₁ hχ₂ hχ₃ hδbnorm
                have hδbχ : scalarProduct G (inducedClassFunction c.H0 (ν₁ - b)) χ₂₃ = 1 := by
                  apply star_inj.mp
                  rw [scalarProduct_star_comm]
                  change scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - b)) = star 1
                  simpa using hχb
                unfold lift
                change normSq G (χ₂₃ - inducedClassFunction c.H0 (ν₁ - b)) = 1
                unfold normSq
                rw [scalarProduct_sub_left, scalarProduct_sub_right, scalarProduct_sub_right]
                change scalarProduct G χ₂₃ χ₂₃ = 1 at hχ₁
                change scalarProduct G (inducedClassFunction c.H0 (ν₁ - b))
                    (inducedClassFunction c.H0 (ν₁ - b)) = 2 at hδbnorm
                rw [hχ₁, hχb, hδbχ, hδbnorm]
                norm_num
  have hδeq : inducedClassFunction c.H0 (μ - ν₂) = lift (θ μ) - lift (θ ν₂) := by
    have hμΘ : θ μ ∈ Θ := thetaOfOrbit_mem c h12 hμL'
    have hνΘ : θ ν₂ ∈ Θ := thetaOfOrbit_mem c h12 hν₂L'
    have hμ' : νθ (θ μ) ∈ L ∧ θ (νθ (θ μ)) = θ μ := hw hμΘ
    have hν' : νθ (θ ν₂) ∈ L ∧ θ (νθ (θ ν₂)) = θ ν₂ := hw hνΘ
    have hμc : inducedClassFunction c.H0 (μ - νθ (θ μ)) = 0 := by
      have hfib : L.filter (fun ν => θ ν = θ μ) =
          ({νθ (θ μ), conjChar c.H0 (s_normalizes_H0 c h12) (νθ (θ μ))} :
            Finset (ClassFunction (↥c.H0))) :=
        theta_fiber_pair_of_invariant c h12 hν₀ h_inv hμ'.1 hμ'.2
      have hμfib : μ ∈ L.filter (fun ν => θ ν = θ μ) :=
        Finset.mem_filter.mpr ⟨hμL', rfl⟩
      rw [hfib] at hμfib
      rw [Finset.mem_insert, Finset.mem_singleton] at hμfib
      rcases hμfib with h | h
      · rw [h]
        rw [hμ'.2]
        simp [inducedClassFunction_zero]
      · rw [h]
        rw [show νθ (θ (conjChar c.H0 (s_normalizes_H0 c h12) (νθ (θ μ)))) =
            νθ (θ μ) by
          have h1 : θ (conjChar c.H0 (s_normalizes_H0 c h12) (νθ (θ μ))) =
              θ (νθ (θ μ)) := by
            change inducedFromSub (h12.H0_normal_in_H).1
                (conjChar c.H0 (s_normalizes_H0 c h12) (νθ (θ μ))) =
                inducedFromSub (h12.H0_normal_in_H).1 (νθ (θ μ))
            exact inducedFromSub_conjChar_eq c h12 hH0index (hνirr (νθ (θ μ)) hμ'.1)
          rw [h1, hμ'.2]]
        exact sigma_pair_star_zero_of_invariant c h12 hH0index hν₀ h_inv hμ'.1
    have hνc : inducedClassFunction c.H0 (ν₂ - νθ (θ ν₂)) = 0 := by
      have hfib : L.filter (fun μ => θ μ = θ ν₂) =
          ({νθ (θ ν₂), conjChar c.H0 (s_normalizes_H0 c h12) (νθ (θ ν₂))} :
            Finset (ClassFunction (↥c.H0))) :=
        theta_fiber_pair_of_invariant c h12 hν₀ h_inv hν'.1 hν'.2
      have hνfib : ν₂ ∈ L.filter (fun μ => θ μ = θ ν₂) :=
        Finset.mem_filter.mpr ⟨hν₂L', rfl⟩
      rw [hfib] at hνfib
      rw [Finset.mem_insert, Finset.mem_singleton] at hνfib
      rcases hνfib with h | h
      · rw [h]
        rw [hν'.2]
        simp [inducedClassFunction_zero]
      · rw [h]
        rw [show νθ (θ (conjChar c.H0 (s_normalizes_H0 c h12) (νθ (θ ν₂)))) =
            νθ (θ ν₂) by
          have h1 : θ (conjChar c.H0 (s_normalizes_H0 c h12) (νθ (θ ν₂))) =
              θ (νθ (θ ν₂)) := by
            change inducedFromSub (h12.H0_normal_in_H).1
                (conjChar c.H0 (s_normalizes_H0 c h12) (νθ (θ ν₂))) =
                inducedFromSub (h12.H0_normal_in_H).1 (νθ (θ ν₂))
            exact inducedFromSub_conjChar_eq c h12 hH0index (hνirr (νθ (θ ν₂)) hν'.1)
          rw [h1, hν'.2]]
        exact sigma_pair_star_zero_of_invariant c h12 hH0index hν₀ h_inv hν'.1
    have hmain : inducedClassFunction c.H0 (νθ (θ μ) - νθ (θ ν₂)) =
        lift (θ μ) - lift (θ ν₂) := by
      unfold lift
      change inducedClassFunction c.H0 (νθ (θ μ) - νθ (θ ν₂)) =
        (χ₂₃ - inducedClassFunction c.H0 (ν₁ - νθ (θ μ))) -
          (χ₂₃ - inducedClassFunction c.H0 (ν₁ - νθ (θ ν₂)))
      have hrhs : (χ₂₃ - inducedClassFunction c.H0 (ν₁ - νθ (θ μ))) -
            (χ₂₃ - inducedClassFunction c.H0 (ν₁ - νθ (θ ν₂))) =
            inducedClassFunction c.H0 (νθ (θ μ) - νθ (θ ν₂)) := by
        calc
          (χ₂₃ - inducedClassFunction c.H0 (ν₁ - νθ (θ μ))) -
              (χ₂₃ - inducedClassFunction c.H0 (ν₁ - νθ (θ ν₂)))
              = inducedClassFunction c.H0 (ν₁ - νθ (θ ν₂)) -
                  inducedClassFunction c.H0 (ν₁ - νθ (θ μ)) := by ring
          _ = inducedClassFunction c.H0
              ((ν₁ - νθ (θ ν₂)) - (ν₁ - νθ (θ μ))) := by
                rw [← inducedClassFunction_sub]
          _ = inducedClassFunction c.H0 (νθ (θ μ) - νθ (θ ν₂)) := by
                congr 1
                ring
      rw [← hrhs]
    change inducedClassFunction c.H0 (μ - ν₂) = lift (θ μ) - lift (θ ν₂)
    have hstep : μ - ν₂ =
        (μ - νθ (θ μ)) + ((νθ (θ μ) - νθ (θ ν₂)) - (ν₂ - νθ (θ ν₂))) := by ring
    rw [hstep]
    rw [show inducedClassFunction c.H0
        (μ - νθ (θ μ) + ((νθ (θ μ) - νθ (θ ν₂)) - (ν₂ - νθ (θ ν₂)))) =
        inducedClassFunction c.H0 (μ - νθ (θ μ)) +
          inducedClassFunction c.H0
            ((νθ (θ μ) - νθ (θ ν₂)) - (ν₂ - νθ (θ ν₂))) by
      exact inducedClassFunction_add c.H0 (μ - νθ (θ μ))
        ((νθ (θ μ) - νθ (θ ν₂)) - (ν₂ - νθ (θ ν₂)))]
    rw [show inducedClassFunction c.H0
        ((νθ (θ μ) - νθ (θ ν₂)) - (ν₂ - νθ (θ ν₂))) =
        inducedClassFunction c.H0 (νθ (θ μ) - νθ (θ ν₂)) -
          inducedClassFunction c.H0 (ν₂ - νθ (θ ν₂)) by
      exact inducedClassFunction_sub c.H0
        (νθ (θ μ) - νθ (θ ν₂)) (ν₂ - νθ (θ ν₂))]
    rw [hμc, hνc, hmain]
    simp
  have honT : ∀ hg : c.t ∈ c.H,
      (inducedClassFunction c.H0 (μ - ν₂)) c.t =
        (inducedFromSub (h12.H0_normal_in_H).1 μ) ⟨c.t, hg⟩ -
          (inducedFromSub (h12.H0_normal_in_H).1 ν₂) ⟨c.t, hg⟩ := by
    intro hg
    have htT : c.t ∈ c.T := ⟨S0_le_H0 c c.t_mem_S0, t_not_mem_U c⟩
    have hμν₂ : μ ∈ orbit c.H0 c.U ν₂ := by
      rw [orbit_eq_of_mem c hν₂L']
      exact hμL'
    have hstar := induced_star_eq_on_T c h12 hH0index hμν₂ (tH0 c) htT
    have hcast : (⟨c.t, (h12.H0_normal_in_H).1 (tH0 c).2⟩ : ↥c.H) = ⟨c.t, hg⟩ := by
      apply Subtype.ext
      rfl
    simpa [hcast, tH0] using hstar
  have hliftν : lift (θ ν₂) = χ₂₃ - inducedClassFunction c.H0 (ν₁ - ν₂) := by
    have hw' := hw (thetaOfOrbit_mem c h12 hν₂L')
    by_cases hb : νθ (θ ν₂) = ν₂
    · unfold lift
      rw [hb]
    · have hbσ : νθ (θ ν₂) = conjChar c.H0 (s_normalizes_H0 c h12) ν₂ := by
        have hEqθ : θ (νθ (θ ν₂)) = θ ν₂ := hw'.2
        have hcases := theta_eq_imp_conj c h12 hH0index
          (ν₁ := ν₂) (ν₂ := νθ (θ ν₂))
          hν₂ (hνirr (νθ (θ ν₂)) hw'.1) hEqθ.symm
        rcases hcases with h | h
        · exact False.elim (hb h)
        · have h' := congrArg (conjChar c.H0 (s_normalizes_H0 c h12)) h
          rw [conjChar_conjChar c h12 (νθ (θ ν₂))] at h'
          exact h'
      unfold lift
      rw [hbσ]
      have hδ : inducedClassFunction c.H0
          (ν₁ - conjChar c.H0 (s_normalizes_H0 c h12) ν₂) =
          inducedClassFunction c.H0 (ν₁ - ν₂) := by
        have hzero : inducedClassFunction c.H0
            (conjChar c.H0 (s_normalizes_H0 c h12) ν₂ - ν₂) = 0 :=
          sigma_pair_star_zero_of_invariant c h12 hH0index hν₀ h_inv hν₂L'
        rw [show ν₁ - conjChar c.H0 (s_normalizes_H0 c h12) ν₂ =
            (ν₁ - ν₂) - (conjChar c.H0 (s_normalizes_H0 c h12) ν₂ - ν₂) by ring]
        rw [inducedClassFunction_sub, hzero]
        simp
      rw [hδ]
  refine ⟨lift, hgenν, hgenμ, hnormν, hnormμ, hδeq, honT, hliftν⟩



-- The `s`-image of a member of a non-invariant orbit lies in the other
-- orbit: `σν ∉ L` for `ν ∈ L` (from `σν₀ ∉ L` via the orbit chain
-- `orbit(σν) = orbit(σν₀)`).
private lemma sigma_image_not_mem_of_not_invariant (c : Hyp11 G) (h12 : Hyp12 c)
    {ν₀ ν : ClassFunction (↥c.H0)}
    (hν₀s : conjChar c.H0 (s_normalizes_H0 c h12) ν₀ ∉ orbit c.H0 c.U ν₀)
    (hνL : ν ∈ orbit c.H0 c.U ν₀) :
    conjChar c.H0 (s_normalizes_H0 c h12) ν ∉ orbit c.H0 c.U ν₀ := by
  classical
  intro hσνL
  apply hν₀s
  have hσνσ₀ : conjChar c.H0 (s_normalizes_H0 c h12) ν ∈
      orbit c.H0 c.U (conjChar c.H0 (s_normalizes_H0 c h12) ν₀) := by
    rw [orbit_conjChar_eq c h12 ν₀]
    exact Finset.mem_image.mpr ⟨ν, hνL, rfl⟩
  have hoν : orbit c.H0 c.U (conjChar c.H0 (s_normalizes_H0 c h12) ν) =
      orbit c.H0 c.U (conjChar c.H0 (s_normalizes_H0 c h12) ν₀) :=
    orbit_eq_of_mem c hσνσ₀
  have hoν' : orbit c.H0 c.U (conjChar c.H0 (s_normalizes_H0 c h12) ν) =
      orbit c.H0 c.U ν₀ := orbit_eq_of_mem c hσνL
  rw [← hoν', hoν]
  exact orbit_self_mem c (conjChar c.H0 (s_normalizes_H0 c h12) ν₀)

-- The per-orbit lift from an orbit base point. PROVED here: the
-- non-`s`-invariant orbit with `n ≥ 3` — the member-picking (`ν₂, ν₃` from
-- `3 ≤ |L|`), the `δ*`-norm/`(δ₂*, δ₃*) = 1` inputs, the common-constituent
-- extraction (`exists_common_constituent_self`) and the defined
-- `(χ₂₃, δᵢ*) = 1` case via `exists_theta_lift`. Recorded `sorry`s: (a) the
-- `s`-invariant orbit (the two fixed members, the `s`-pairs, the two-fixed
-- reindexing and the norm-2 lifts — needs `theta_card_mul_two_eq_orbit_card_add_two`
-- and the fixed-excluding picking); (b) the `n ≥ 5` undefined case (the
-- `lemma_1_7_iii` `θ̃₂(t)`-evaluation and the (vi)-argument are not yet
-- formalized); (c) the `n ≤ 2` easy case (the signed-pair decomposition of
-- `δ₂*`).

/-- The constant-one class function is a character (the trivial
representation on `Fin 1 → ℂ`). -/
private lemma isCharacter_one (G : Type u) [Group G] :
    IsCharacter (1 : ClassFunction G) := by
  refine ⟨1, Representation.trivial ℂ G (Fin 1 → ℂ), ?_⟩
  ext g
  simp [Representation.character, LinearMap.trace_id, Module.finrank_fin_fun, Representation.isTrivial_def]

/-- The constant-one class function is a generalized character. -/
private lemma isGeneralizedCharacter_one (G : Type u) [Group G] [Fintype G] :
    IsGeneralizedCharacter (1 : ClassFunction G) := by
  refine ⟨1, 0, isCharacter_one G, isCharacter_zero, ?_⟩
  simp

/-- `|1|² = 1`. -/
private lemma normSq_one (G : Type u) [Group G] [Fintype G] :
    normSq G (1 : ClassFunction G) = 1 := by
  unfold normSq scalarProduct
  simp [Finset.sum_const]

/-- The two-member lift (`n = 2`): for the two members `ν₀, ν₂` of the
non-`s`-invariant orbit and norm-one disjoint generalized characters
`A, B` with `(ν₀−ν₂)* = A − B`, the lift `θ̃(θν₀) := A`, `θ̃(θν₂) := B`
satisfies the `ThetaLift` fields. -/
private lemma theta_lift_two (c : Hyp11 G) (h12 : Hyp12 c)
    (hH0index : (c.H0.subgroupOf c.H).index = 2)
    (ν₀ ν₂ : ClassFunction (↥c.H0))
    (hν₀ : IsIrreducibleCharacter ν₀) (hν₂ : IsIrreducibleCharacter ν₂)
    (h₂₀ : ν₂ ∈ orbit c.H0 c.U ν₀)
    (hν₀s : conjChar c.H0 (s_normalizes_H0 c h12) ν₀ ∉ orbit c.H0 c.U ν₀)
    (hν₁s : conjChar c.H0 (s_normalizes_H0 c h12) ν₀ ≠ ν₀)
    (hν₂s : conjChar c.H0 (s_normalizes_H0 c h12) ν₂ ≠ ν₂)
    (hν₂ne : ν₂ ≠ ν₀)
    (hL : (orbit c.H0 c.U ν₀).card = 2)
    (A B : ClassFunction G)
    (hAg : IsGeneralizedCharacter A) (hBg : IsGeneralizedCharacter B)
    (hAnorm : normSq G A = 1) (hBnorm : normSq G B = 1)
    (hAB : scalarProduct G A B = 0)
    (hδAB : inducedClassFunction c.H0 (ν₀ - ν₂) = A - B) :
    Nonempty (ThetaLift c h12 (orbit c.H0 c.U ν₀)
      (thetaOfOrbit c h12 (orbit c.H0 c.U ν₀))) := by
  classical
  let L : Finset (ClassFunction (↥c.H0)) := orbit c.H0 c.U ν₀
  let θ : ClassFunction (↥c.H0) → ClassFunction (↥c.H) := fun ν =>
    inducedFromSub (h12.H0_normal_in_H).1 ν
  have hν₀L : ν₀ ∈ L := orbit_self_mem c ν₀
  have hν₂L : ν₂ ∈ L := h₂₀
  have hLc : L.card = 2 := by
    simpa [L] using hL
  have hνirr : ∀ ν ∈ L, IsIrreducibleCharacter ν :=
    fun ν hνL => orbit_mem_isIrreducible c.H0 c.U hν₀ hνL
  -- `L = {ν₀, ν₂}`: the membership split
  have hLmem : ∀ a ∈ L, a = ν₀ ∨ a = ν₂ := by
    intro a ha
    by_cases h : a = ν₀
    · exact Or.inl h
    · right
      have hae : a ∈ L.erase ν₀ := Finset.mem_erase.mpr ⟨h, ha⟩
      have hcard1 : (L.erase ν₀).card = 1 := by
        rw [Finset.card_erase_of_mem hν₀L]
        omega
      have hν₂e : ν₂ ∈ L.erase ν₀ := Finset.mem_erase.mpr ⟨hν₂ne, hν₂L⟩
      rcases Finset.card_eq_one.mp hcard1 with ⟨b, hb⟩
      have hbν₂ : b = ν₂ := by
        rw [hb] at hν₂e
        have h' : ν₂ = b := by simpa using hν₂e
        exact h'.symm
      have hab : a = b := by
        rw [hb] at hae
        simpa using hae
      exact hab.trans hbν₂
  -- the `θ`-values are distinct (`θ` injective on the orbit)
  have hθne : θ ν₀ ≠ θ ν₂ := by
    intro hEq
    apply hν₂ne
    exact (theta_of_orbit_injective_of_not_invariant c h12 hν₀ hν₀s hν₀L hν₂L hEq).symm
  -- the lift on the two `θ`-values
  let lift : ClassFunction (↥c.H) → ClassFunction G := fun θ' =>
    if θ' = θ ν₀ then A else B
  apply Nonempty.intro
  refine ⟨lift, ?_, ?_, ?_, ?_⟩
  · -- norm
    intro θ' hθ'
    by_cases h₀ : θ' = θ ν₀
    · rw [h₀]
      have hlift : lift (θ ν₀) = A := by
        unfold lift
        rw [show θ ν₀ = θ ν₀ by rfl]
        simp
      rw [hlift]
      change normSq G A = normSq (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν₀)
      rw [hAnorm]
      rw [theta_norm c h12 hH0index hν₀]
      rw [if_neg hν₁s]
    · have hθ₂ : θ' = θ ν₂ := by
        rcases Finset.mem_image.mp hθ' with ⟨a, ha, hθa⟩
        rcases hLmem a ha with h | h
        · exfalso
          apply h₀
          rw [h] at hθa
          exact hθa.symm
        · rw [h] at hθa
          exact hθa.symm
      rw [hθ₂]
      have hlift : lift (θ ν₂) = B := by
        unfold lift
        rw [show θ ν₂ = θ ν₂ by rfl]
        rw [if_neg hθne.symm]
      rw [hlift]
      change normSq G B = normSq (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν₂)
      rw [hBnorm]
      rw [theta_norm c h12 hH0index (hνirr ν₂ hν₂L)]
      rw [if_neg hν₂s]
  · -- isGeneralized
    intro θ' hθ'
    by_cases h₀ : θ' = θ ν₀
    · rw [h₀]
      unfold lift
      rw [show θ ν₀ = θ ν₀ by rfl]
      simp
      exact hAg
    · have hθ₂ : θ' = θ ν₂ := by
        rcases Finset.mem_image.mp hθ' with ⟨a, ha, hθa⟩
        rcases hLmem a ha with h | h
        · exfalso
          apply h₀
          rw [h] at hθa
          exact hθa.symm
        · rw [h] at hθa
          exact hθa.symm
      rw [hθ₂]
      unfold lift
      rw [show θ ν₂ = θ ν₂ by rfl]
      rw [if_neg hθne.symm]
      exact hBg
  · -- ind
    intro ν μ hμL hνIrr hνL hθνΘ hθμΘ
    have hμL' : μ ∈ L := by
      rw [orbit_eq_of_mem c hνL] at hμL
      exact hμL
    have hlift₀ : lift (inducedFromSub (h12.H0_normal_in_H).1 ν₀) = A := by
      unfold lift
      rw [show inducedFromSub (h12.H0_normal_in_H).1 ν₀ = θ ν₀ by rfl]
      simp
    have hlift₂ : lift (inducedFromSub (h12.H0_normal_in_H).1 ν₂) = B := by
      unfold lift
      rw [show inducedFromSub (h12.H0_normal_in_H).1 ν₂ = θ ν₂ by rfl]
      rw [if_neg hθne.symm]
    rcases hLmem ν hνL with hν₀e | hν₂e
    · rw [hν₀e]
      rcases hLmem μ hμL' with hμ₀e | hμ₂e
      · rw [hμ₀e]
        have hzero0 : inducedClassFunction c.H0 (ν₀ - ν₀) = 0 := by
          rw [show ν₀ - ν₀ = (0 : ClassFunction (↥c.H0)) by simp]
          exact inducedClassFunction_zero c.H0
        rw [hlift₀, hzero0]
        simp
      · rw [hμ₂e]
        have hleft : inducedClassFunction c.H0 (ν₂ - ν₀) =
            -(inducedClassFunction c.H0 (ν₀ - ν₂)) := by
          rw [show ν₂ - ν₀ = -(ν₀ - ν₂) by ring]
          rw [inducedClassFunction_neg]
        rw [hleft, hδAB, hlift₂, hlift₀]
        ring
    · rw [hν₂e]
      rcases hLmem μ hμL' with hμ₀e | hμ₂e
      · rw [hμ₀e]
        rw [hlift₀, hlift₂]
        exact hδAB
      · rw [hμ₂e]
        have hzero0 : inducedClassFunction c.H0 (ν₂ - ν₂) = 0 := by
          rw [show ν₂ - ν₂ = (0 : ClassFunction (↥c.H0)) by simp]
          exact inducedClassFunction_zero c.H0
        rw [hlift₂, hzero0]
        simp
  · -- disjoint
    intro ν μ hμL hνL hνμne hσνμ hθνΘ hθμΘ
    have hμL' : μ ∈ L := by
      rw [orbit_eq_of_mem c hνL] at hμL
      exact hμL
    have hBA : scalarProduct G B A = 0 := by
      rw [← scalarProduct_star_comm, hAB]
      simp
    rcases hLmem ν hνL with hν₀e | hν₂e
    · rw [hν₀e]
      rcases hLmem μ hμL' with hμ₀e | hμ₂e
      · exfalso
        apply hνμne
        exact hν₀e.trans hμ₀e.symm
      · rw [hμ₂e]
        have h₂' : lift (inducedFromSub (h12.H0_normal_in_H).1 ν₂) = B := by
          unfold lift
          rw [show inducedFromSub (h12.H0_normal_in_H).1 ν₂ = θ ν₂ by rfl]
          rw [if_neg hθne.symm]
        have h₀' : lift (inducedFromSub (h12.H0_normal_in_H).1 ν₀) = A := by
          unfold lift
          rw [show inducedFromSub (h12.H0_normal_in_H).1 ν₀ = θ ν₀ by rfl]
          simp
        rw [h₂', h₀']
        exact disjoint_of_orthogonal_norm_one hBg hAg hBnorm hAnorm hBA
    · rw [hν₂e]
      rcases hLmem μ hμL' with hμ₀e | hμ₂e
      · rw [hμ₀e]
        have h₀' : lift (inducedFromSub (h12.H0_normal_in_H).1 ν₀) = A := by
          unfold lift
          rw [show inducedFromSub (h12.H0_normal_in_H).1 ν₀ = θ ν₀ by rfl]
          simp
        have h₂' : lift (inducedFromSub (h12.H0_normal_in_H).1 ν₂) = B := by
          unfold lift
          rw [show inducedFromSub (h12.H0_normal_in_H).1 ν₂ = θ ν₂ by rfl]
          rw [if_neg hθne.symm]
        rw [h₀', h₂']
        exact disjoint_of_orthogonal_norm_one hAg hBg hAnorm hBnorm hAB
      · exfalso
        apply hνμne
        exact hν₂e.trans hμ₂e.symm

/-- The `s`-invariant `n = 2` orbit's two-valued lift (`|L| = 2` with both
members `s`-fixed, the two norm-2 `θ`-values): `θ̃(θν₀) := A`,
`θ̃(θν₂) := B` with the norm-two generalized characters `A, B`
(`(ν₀−ν₂)* = A − B`, `(A,B) = 0`, `A(1) = B(1)`), and the singleton
`θ`-fibers of the fixed members (`{a, σa} = {a}`). -/
private lemma theta_lift_two_invariant (c : Hyp11 G) (h12 : Hyp12 c)
    (hH0index : (c.H0.subgroupOf c.H).index = 2)
    (ν₀ ν₂ : ClassFunction (↥c.H0))
    (hν₀ : IsIrreducibleCharacter ν₀) (hν₂ : IsIrreducibleCharacter ν₂)
    (h₂₀ : ν₂ ∈ orbit c.H0 c.U ν₀)
    (hν₀s_inv : conjChar c.H0 (s_normalizes_H0 c h12) ν₀ ∈ orbit c.H0 c.U ν₀)
    (hfix₀ : conjChar c.H0 (s_normalizes_H0 c h12) ν₀ = ν₀)
    (hfix₂ : conjChar c.H0 (s_normalizes_H0 c h12) ν₂ = ν₂)
    (hν₂ne : ν₂ ≠ ν₀)
    (hL : (orbit c.H0 c.U ν₀).card = 2)
    (A B : ClassFunction G)
    (hAg : IsGeneralizedCharacter A) (hBg : IsGeneralizedCharacter B)
    (hAnorm : normSq G A = 2) (hBnorm : normSq G B = 2)
    (hAB : scalarProduct G A B = 0) (hdegAB : A 1 = B 1)
    (hδAB : inducedClassFunction c.H0 (ν₀ - ν₂) = A - B) :
    Nonempty (ThetaLift c h12 (orbit c.H0 c.U ν₀)
      (thetaOfOrbit c h12 (orbit c.H0 c.U ν₀))) := by
  classical
  let L : Finset (ClassFunction (↥c.H0)) := orbit c.H0 c.U ν₀
  let θ : ClassFunction (↥c.H0) → ClassFunction (↥c.H) := fun ν =>
    inducedFromSub (h12.H0_normal_in_H).1 ν
  have hν₀L : ν₀ ∈ L := orbit_self_mem c ν₀
  have hν₂L : ν₂ ∈ L := h₂₀
  have hLc : L.card = 2 := by
    simpa [L] using hL
  have hνirr : ∀ ν ∈ L, IsIrreducibleCharacter ν :=
    fun ν hνL => orbit_mem_isIrreducible c.H0 c.U hν₀ hνL
  -- `L = {ν₀, ν₂}`: the membership split
  have hLmem : ∀ a ∈ L, a = ν₀ ∨ a = ν₂ := by
    intro a ha
    by_cases h : a = ν₀
    · exact Or.inl h
    · right
      have hae : a ∈ L.erase ν₀ := Finset.mem_erase.mpr ⟨h, ha⟩
      have hcard1 : (L.erase ν₀).card = 1 := by
        rw [Finset.card_erase_of_mem hν₀L]
        omega
      have hν₂e : ν₂ ∈ L.erase ν₀ := Finset.mem_erase.mpr ⟨hν₂ne, hν₂L⟩
      rcases Finset.card_eq_one.mp hcard1 with ⟨b, hb⟩
      have hbν₂ : b = ν₂ := by
        rw [hb] at hν₂e
        have h' : ν₂ = b := by simpa using hν₂e
        exact h'.symm
      have hab : a = b := by
        rw [hb] at hae
        simpa using hae
      exact hab.trans hbν₂
  -- the `θ`-values are distinct: the fiber of `θ(ν₀)` is the singleton `{ν₀}`
  have hθne : θ ν₀ ≠ θ ν₂ := by
    intro hEq
    apply hν₂ne
    have hfib : L.filter (fun μ => θ μ = θ ν₀) =
        ({ν₀, conjChar c.H0 (s_normalizes_H0 c h12) ν₀} :
          Finset (ClassFunction (↥c.H0))) :=
      theta_fiber_pair_of_invariant c h12 hν₀ hν₀s_inv hν₀L rfl
    have hν₂fib : ν₂ ∈ L.filter (fun μ => θ μ = θ ν₀) :=
      Finset.mem_filter.mpr ⟨hν₂L, by simpa [θ] using hEq.symm⟩
    rw [hfib] at hν₂fib
    rw [Finset.mem_insert, Finset.mem_singleton] at hν₂fib
    rcases hν₂fib with h | h
    · exact h
    · exact h.trans hfix₀
  -- the lift on the two `θ`-values
  let lift : ClassFunction (↥c.H) → ClassFunction G := fun θ' =>
    if θ' = θ ν₀ then A else B
  apply Nonempty.intro
  refine ⟨lift, ?_, ?_, ?_, ?_⟩
  · -- norm
    intro θ' hθ'
    by_cases h₀ : θ' = θ ν₀
    · rw [h₀]
      have hlift : lift (θ ν₀) = A := by
        unfold lift
        rw [show θ ν₀ = θ ν₀ by rfl]
        simp
      rw [hlift]
      change normSq G A = normSq (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν₀)
      rw [hAnorm]
      rw [theta_norm c h12 hH0index hν₀]
      rw [if_pos hfix₀]
    · have hθ₂ : θ' = θ ν₂ := by
        rcases Finset.mem_image.mp hθ' with ⟨a, ha, hθa⟩
        rcases hLmem a ha with h | h
        · exfalso
          apply h₀
          rw [h] at hθa
          exact hθa.symm
        · rw [h] at hθa
          exact hθa.symm
      rw [hθ₂]
      have hlift : lift (θ ν₂) = B := by
        unfold lift
        rw [show θ ν₂ = θ ν₂ by rfl]
        rw [if_neg hθne.symm]
      rw [hlift]
      change normSq G B = normSq (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν₂)
      rw [hBnorm]
      rw [theta_norm c h12 hH0index (hνirr ν₂ hν₂L)]
      rw [if_pos hfix₂]
  · -- isGeneralized
    intro θ' hθ'
    by_cases h₀ : θ' = θ ν₀
    · rw [h₀]
      unfold lift
      rw [show θ ν₀ = θ ν₀ by rfl]
      simp
      exact hAg
    · have hθ₂ : θ' = θ ν₂ := by
        rcases Finset.mem_image.mp hθ' with ⟨a, ha, hθa⟩
        rcases hLmem a ha with h | h
        · exfalso
          apply h₀
          rw [h] at hθa
          exact hθa.symm
        · rw [h] at hθa
          exact hθa.symm
      rw [hθ₂]
      unfold lift
      rw [show θ ν₂ = θ ν₂ by rfl]
      rw [if_neg hθne.symm]
      exact hBg
  · -- ind
    intro ν μ hμL hνIrr hνL hθνΘ hθμΘ
    have hμL' : μ ∈ L := by
      rw [orbit_eq_of_mem c hνL] at hμL
      exact hμL
    have hlift₀ : lift (inducedFromSub (h12.H0_normal_in_H).1 ν₀) = A := by
      unfold lift
      rw [show inducedFromSub (h12.H0_normal_in_H).1 ν₀ = θ ν₀ by rfl]
      simp
    have hlift₂ : lift (inducedFromSub (h12.H0_normal_in_H).1 ν₂) = B := by
      unfold lift
      rw [show inducedFromSub (h12.H0_normal_in_H).1 ν₂ = θ ν₂ by rfl]
      rw [if_neg hθne.symm]
    rcases hLmem ν hνL with hν₀e | hν₂e
    · rw [hν₀e]
      rcases hLmem μ hμL' with hμ₀e | hμ₂e
      · rw [hμ₀e]
        have hzero0 : inducedClassFunction c.H0 (ν₀ - ν₀) = 0 := by
          rw [show ν₀ - ν₀ = (0 : ClassFunction (↥c.H0)) by simp]
          exact inducedClassFunction_zero c.H0
        rw [hlift₀, hzero0]
        simp
      · rw [hμ₂e]
        have hleft : inducedClassFunction c.H0 (ν₂ - ν₀) =
            -(inducedClassFunction c.H0 (ν₀ - ν₂)) := by
          rw [show ν₂ - ν₀ = -(ν₀ - ν₂) by ring]
          rw [inducedClassFunction_neg]
        rw [hleft, hδAB, hlift₂, hlift₀]
        ring
    · rw [hν₂e]
      rcases hLmem μ hμL' with hμ₀e | hμ₂e
      · rw [hμ₀e]
        rw [hlift₀, hlift₂]
        exact hδAB
      · rw [hμ₂e]
        have hzero0 : inducedClassFunction c.H0 (ν₂ - ν₂) = 0 := by
          rw [show ν₂ - ν₂ = (0 : ClassFunction (↥c.H0)) by simp]
          exact inducedClassFunction_zero c.H0
        rw [hlift₂, hzero0]
        simp
  · -- disjoint: the two norm-2 values via `remark_1_5` (equal degrees
    -- `A(1) = B(1)` from `δ*(1) = 0`)
    intro ν μ hμL hνL hνμne hσνμ hθνΘ hθμΘ
    have hμL' : μ ∈ L := by
      rw [orbit_eq_of_mem c hνL] at hμL
      exact hμL
    rcases hLmem ν hνL with hν₀e | hν₂e
    · rw [hν₀e]
      rcases hLmem μ hμL' with hμ₀e | hμ₂e
      · exfalso
        apply hνμne
        exact hν₀e.trans hμ₀e.symm
      · rw [hμ₂e]
        have h₂' : lift (inducedFromSub (h12.H0_normal_in_H).1 ν₂) = B := by
          unfold lift
          rw [show inducedFromSub (h12.H0_normal_in_H).1 ν₂ = θ ν₂ by rfl]
          rw [if_neg hθne.symm]
        have h₀' : lift (inducedFromSub (h12.H0_normal_in_H).1 ν₀) = A := by
          unfold lift
          rw [show inducedFromSub (h12.H0_normal_in_H).1 ν₀ = θ ν₀ by rfl]
          simp
        rw [h₂', h₀']
        have hBA : scalarProduct G B A = 0 := by
          rw [← scalarProduct_star_comm, hAB]
          simp
        exact remark_1_5 hBg hAg hBnorm hAnorm hdegAB.symm hBA
    · rw [hν₂e]
      rcases hLmem μ hμL' with hμ₀e | hμ₂e
      · rw [hμ₀e]
        have h₀' : lift (inducedFromSub (h12.H0_normal_in_H).1 ν₀) = A := by
          unfold lift
          rw [show inducedFromSub (h12.H0_normal_in_H).1 ν₀ = θ ν₀ by rfl]
          simp
        have h₂' : lift (inducedFromSub (h12.H0_normal_in_H).1 ν₂) = B := by
          unfold lift
          rw [show inducedFromSub (h12.H0_normal_in_H).1 ν₂ = θ ν₂ by rfl]
          rw [if_neg hθne.symm]
        rw [h₀', h₂']
        exact remark_1_5 hAg hBg hAnorm hBnorm hdegAB hAB
      · exfalso
        apply hνμne
        exact hν₂e.trans hμ₂e.symm

/-- The `Λ`-orbits of the irreducible characters of `H0` (early copy, used by
the per-orbit lift wrapper before the assembly block below). -/
private noncomputable def orbitSetEarly (c : Hyp11 G) (h12 : Hyp12 c) :
    Finset (Finset (ClassFunction (↥c.H0))) := by
  classical
  exact (Finset.univ : Finset (Irr (↥c.H0))).image (fun ν : Irr (↥c.H0) => orbit c.H0 c.U ν.1)

/-- An orbit in `orbitSetEarly` is nonempty. -/
private lemma orbitSetEarly_mem_nonempty (c : Hyp11 G) (h12 : Hyp12 c)
    {L : Finset (ClassFunction (↥c.H0))} (hL : L ∈ orbitSetEarly c h12) : L.Nonempty := by
  rcases Finset.mem_image.mp hL with ⟨ν, hν, hLν⟩
  refine ⟨ν.1, ?_⟩
  rw [← hLν]
  exact orbit_self_mem c ν.1

/-- The orbit representatives of `Irr(H0)` (early copy). -/
private lemma exists_orbit_representatives_early (c : Hyp11 G) (h12 : Hyp12 c) :
    ∃ (ι : Type u) (_ : Fintype ι) (rep : ι → ClassFunction (↥c.H0)),
      (∀ i : ι, IsIrreducibleCharacter (rep i)) ∧
      (∀ ν : {ν : ClassFunction (↥c.H0) // IsIrreducibleCharacter ν},
        ∃! i : ι, ν.1 ∈ orbit c.H0 c.U (rep i)) := by
  classical
  let ι : Type u := {L : Finset (ClassFunction (↥c.H0)) // L ∈ orbitSetEarly c h12}
  let rep : ι → ClassFunction (↥c.H0) := fun L =>
    Classical.choose (orbitSetEarly_mem_nonempty c h12 L.2)
  refine ⟨ι, inferInstance, rep, ?_, ?_⟩
  · intro L
    rcases Finset.mem_image.mp L.2 with ⟨ν, hν, hLν⟩
    have hspec : rep L ∈ L.1 := Classical.choose_spec (orbitSetEarly_mem_nonempty c h12 L.2)
    have hνL' : rep L ∈ orbit c.H0 c.U ν.1 := hLν ▸ hspec
    exact orbit_mem_isIrreducible c.H0 c.U ν.2 hνL'
  · intro ν
    refine ⟨⟨orbit c.H0 c.U ν.1, Finset.mem_image.mpr ⟨ν, Finset.mem_univ ν, rfl⟩⟩, ?_, ?_⟩
    · have hspec : rep ⟨orbit c.H0 c.U ν.1,
          Finset.mem_image.mpr ⟨ν, Finset.mem_univ ν, rfl⟩⟩ ∈ orbit c.H0 c.U ν.1 :=
        Classical.choose_spec (orbitSetEarly_mem_nonempty c h12
          (Finset.mem_image.mpr ⟨ν, Finset.mem_univ ν, rfl⟩ :
            orbit c.H0 c.U ν.1 ∈ orbitSetEarly c h12))
      change ν.1 ∈ orbit c.H0 c.U
        (rep ⟨orbit c.H0 c.U ν.1, Finset.mem_image.mpr ⟨ν, Finset.mem_univ ν, rfl⟩⟩)
      rw [orbit_eq_of_mem c hspec]
      exact orbit_self_mem c ν.1
    · intro L hLmem
      have hEqOrbit : L.1 = orbit c.H0 c.U ν.1 := by
        have hspec : rep L ∈ L.1 := Classical.choose_spec (orbitSetEarly_mem_nonempty c h12 L.2)
        rcases Finset.mem_image.mp L.2 with ⟨μ, hμ, hLμ⟩
        have ho1 : orbit c.H0 c.U (rep L) = orbit c.H0 c.U ν.1 :=
          (orbit_eq_of_mem c hLmem).symm
        have ho2 : orbit c.H0 c.U (rep L) = orbit c.H0 c.U μ.1 := by
          rw [← hLμ] at hspec
          exact orbit_eq_of_mem c hspec
        have ho3 : orbit c.H0 c.U μ.1 = L.1 := hLμ
        rw [← ho1, ho2, ho3]
      apply Subtype.ext
      exact hEqOrbit

/-- Orbit representatives with a prescribed representative `ν₁` for the
`Λ`-orbit of `ν₁`.  Used by the Lemma-1.7 Fourier reduction in the
fixed-member case (the orbit sum must be based at the construction's `ν₁`). -/
private lemma exists_orbit_representatives_with_base (c : Hyp11 G) (h12 : Hyp12 c)
    (ν₁ : ClassFunction (↥c.H0)) (hν₁ : IsIrreducibleCharacter ν₁) :
    ∃ (ι : Type u) (_ : Fintype ι) (rep : ι → ClassFunction (↥c.H0))
      (hrep_irr : ∀ i : ι, IsIrreducibleCharacter (rep i))
      (hrep : ∀ ν : {ν : ClassFunction (↥c.H0) // IsIrreducibleCharacter ν},
        ∃! i : ι, ν.1 ∈ orbit c.H0 c.U (rep i)),
      ∀ ν : {ν : ClassFunction (↥c.H0) // IsIrreducibleCharacter ν},
        ν.1 ∈ orbit c.H0 c.U ν₁ → rep (Classical.choose (hrep ν)) = ν₁ := by
  classical
  let ι : Type u := {L : Finset (ClassFunction (↥c.H0)) // L ∈ orbitSetEarly c h12}
  let oldRep : ι → ClassFunction (↥c.H0) := fun i =>
    Classical.choose (orbitSetEarly_mem_nonempty c h12 i.2)
  have hOld_mem : ∀ i : ι, oldRep i ∈ i.1 := fun i =>
    Classical.choose_spec (orbitSetEarly_mem_nonempty c h12 i.2)
  have hOld_irr : ∀ i : ι, IsIrreducibleCharacter (oldRep i) := by
    intro i
    rcases Finset.mem_image.mp i.2 with ⟨μ, hμ, hi⟩
    have hspec : oldRep i ∈ i.1 := hOld_mem i
    have hspec' : oldRep i ∈ orbit c.H0 c.U μ.1 := by
      rwa [← hi] at hspec
    exact orbit_mem_isIrreducible c.H0 c.U μ.2 hspec'
  have hOld_orbit : ∀ i : ι, orbit c.H0 c.U (oldRep i) = i.1 := by
    intro i
    rcases Finset.mem_image.mp i.2 with ⟨μ, hμ, hi⟩
    have hspec' : oldRep i ∈ orbit c.H0 c.U μ.1 := by
      have hm : oldRep i ∈ i.1 := hOld_mem i
      rwa [← hi] at hm
    rw [← hi]
    exact orbit_eq_of_mem c hspec'
  have hOld_uniq : ∀ ν : {ν : ClassFunction (↥c.H0) // IsIrreducibleCharacter ν},
      ∃! i : ι, ν.1 ∈ orbit c.H0 c.U (oldRep i) := by
    intro ν
    refine ⟨⟨orbit c.H0 c.U ν.1,
      (by simpa [orbitSetEarly] using
        (Finset.mem_image.mpr ⟨ν, Finset.mem_univ _, rfl⟩ :
          orbit c.H0 c.U ν.1 ∈ (Finset.univ : Finset (Irr (↥c.H0))).image
            (fun μ : Irr (↥c.H0) => orbit c.H0 c.U μ.1)))⟩, ?_, ?_⟩
    · have hspec : oldRep ⟨orbit c.H0 c.U ν.1,
          (by simpa [orbitSetEarly] using
            (Finset.mem_image.mpr ⟨ν, Finset.mem_univ _, rfl⟩ :
              orbit c.H0 c.U ν.1 ∈ (Finset.univ : Finset (Irr (↥c.H0))).image
                (fun μ : Irr (↥c.H0) => orbit c.H0 c.U μ.1)))⟩ ∈
          orbit c.H0 c.U ν.1 :=
        hOld_mem ⟨orbit c.H0 c.U ν.1,
          (by simpa [orbitSetEarly] using
            (Finset.mem_image.mpr ⟨ν, Finset.mem_univ _, rfl⟩ :
              orbit c.H0 c.U ν.1 ∈ (Finset.univ : Finset (Irr (↥c.H0))).image
                (fun μ : Irr (↥c.H0) => orbit c.H0 c.U μ.1)))⟩
      change ν.1 ∈ orbit c.H0 c.U (oldRep ⟨orbit c.H0 c.U ν.1,
        (by simpa [orbitSetEarly] using
          (Finset.mem_image.mpr ⟨ν, Finset.mem_univ _, rfl⟩ :
            orbit c.H0 c.U ν.1 ∈ (Finset.univ : Finset (Irr (↥c.H0))).image
              (fun μ : Irr (↥c.H0) => orbit c.H0 c.U μ.1)))⟩)
      rw [orbit_eq_of_mem c hspec]
      exact orbit_self_mem c ν.1
    · intro L hLmem
      have hEqOrbit : L.1 = orbit c.H0 c.U ν.1 := by
        have hspec : oldRep L ∈ L.1 := hOld_mem L
        rcases Finset.mem_image.mp L.2 with ⟨μ, hμ, hLμ⟩
        have ho1 : orbit c.H0 c.U (oldRep L) = orbit c.H0 c.U ν.1 :=
          (orbit_eq_of_mem c hLmem).symm
        have ho2 : orbit c.H0 c.U (oldRep L) = orbit c.H0 c.U μ.1 := by
          rw [← hLμ] at hspec
          exact orbit_eq_of_mem c hspec
        have ho3 : orbit c.H0 c.U μ.1 = L.1 := hLμ
        rw [← ho1, ho2, ho3]
      apply Subtype.ext
      exact hEqOrbit
  let L : Finset (ClassFunction (↥c.H0)) := orbit c.H0 c.U ν₁
  let hLidx : L ∈ orbitSetEarly c h12 :=
    by
      simpa [orbitSetEarly] using
        (Finset.mem_image.mpr ⟨⟨ν₁, hν₁⟩, Finset.mem_univ _, rfl⟩ :
          L ∈ (Finset.univ : Finset (Irr (↥c.H0))).image
            (fun μ : Irr (↥c.H0) => orbit c.H0 c.U μ.1))
  let rep' : ι → ClassFunction (↥c.H0) := fun i =>
    if i.1 = L then ν₁ else oldRep i
  have hrep'_irr : ∀ i : ι, IsIrreducibleCharacter (rep' i) := by
    intro i
    by_cases h : i.1 = L
    · simpa [rep', h] using hν₁
    · simpa [rep', h] using hOld_irr i
  have hrep'_uniq : ∀ ν : {ν : ClassFunction (↥c.H0) // IsIrreducibleCharacter ν},
      ∃! i : ι, ν.1 ∈ orbit c.H0 c.U (rep' i) := by
    intro ν
    by_cases hνL : ν.1 ∈ L
    · refine ⟨⟨L, hLidx⟩, ?_, ?_⟩
      · change ν.1 ∈ orbit c.H0 c.U (rep' ⟨L, hLidx⟩)
        have hrepL : rep' ⟨L, hLidx⟩ = ν₁ := by
          simp [rep', hLidx]
        rw [hrepL]
        exact hνL
      · intro j hj
        by_cases hjL : j.1 = L
        · apply Subtype.ext
          exact hjL
        · have hrepj : rep' j = oldRep j := by simp [rep', hjL]
          rw [hrepj] at hj
          rcases hOld_uniq ν with ⟨i₀, hi₀, huniq₀⟩
          have hji₀ : j = i₀ := huniq₀ j hj
          have hνi₀ : ν.1 ∈ orbit c.H0 c.U (oldRep i₀) := hi₀
          have hL_eq : i₀.1 = L := by
            have horb : orbit c.H0 c.U (oldRep i₀) = L := by
              calc
                orbit c.H0 c.U (oldRep i₀) = orbit c.H0 c.U ν.1 :=
                  (orbit_eq_of_mem c hνi₀).symm
                _ = orbit c.H0 c.U ν₁ := orbit_eq_of_mem c hνL
                _ = L := rfl
            rw [← hOld_orbit i₀, horb]
          subst hji₀
          apply Subtype.ext
          exact hL_eq
    · rcases hOld_uniq ν with ⟨i₀, hi₀, huniq₀⟩
      refine ⟨i₀, ?_, ?_⟩
      · by_cases hi₀L : i₀.1 = L
        · exfalso
          apply hνL
          have horb : orbit c.H0 c.U (oldRep i₀) = L := by
            rw [hOld_orbit i₀, hi₀L]
          rw [← horb]
          exact hi₀
        · simpa [rep', hi₀L] using hi₀
      · intro j hj
        by_cases hjL : j.1 = L
        · exfalso
          apply hνL
          have hrepj : rep' j = ν₁ := by simp [rep', hjL]
          rw [hrepj] at hj
          exact hj
        · have hrepj : rep' j = oldRep j := by simp [rep', hjL]
          rw [hrepj] at hj
          exact huniq₀ j hj
  refine ⟨ι, inferInstance, rep', hrep'_irr, hrep'_uniq, ?_⟩
  intro ν hνL
  have hLmem : ν.1 ∈ orbit c.H0 c.U (rep' ⟨L, hLidx⟩) := by
    have hrepL : rep' ⟨L, hLidx⟩ = ν₁ := by
      simp [rep', hLidx]
    rw [hrepL]
    exact hνL
  have hchoose : Classical.choose (hrep'_uniq ν) = ⟨L, hLidx⟩ :=
    ((Classical.choose_spec (hrep'_uniq ν)).2 ⟨L, hLidx⟩ hLmem).symm
  rw [hchoose]
  simp [rep', hLidx]

/-- Lemma 1.7(ii), reduced to a single `Λ`-orbit `L`: if the chosen
representative of `L` is `ν₁` and all coefficients outside `L` vanish, then
`χ` on `x ∈ T` is the orbit sum with differences based at `ν₁`. -/
private lemma fourier_value_eq_orbit_sum (c : Hyp11 G) (h12 : Hyp12 c)
    {ι : Type u} [Fintype ι] (rep : ι → ClassFunction (↥c.H0))
    (hrep_irr : ∀ i : ι, IsIrreducibleCharacter (rep i))
    (hrep : ∀ ν : {ν : ClassFunction (↥c.H0) // IsIrreducibleCharacter ν},
      ∃! i : ι, ν.1 ∈ orbit c.H0 c.U (rep i))
    {χ : ClassFunction G} (hχ : IsGeneralizedCharacter χ)
    {x : ↥c.H0} (hx : (x : G) ∉ c.U)
    {L : Finset (ClassFunction (↥c.H0))}
    (ν₁ : ClassFunction (↥c.H0)) (hν₁ : IsIrreducibleCharacter ν₁) (hν₁L : ν₁ ∈ L)
    (hL : L = orbit c.H0 c.U ν₁)
    (hrepL : ∀ ν : {ν : ClassFunction (↥c.H0) // IsIrreducibleCharacter ν},
      ν.1 ∈ L → rep (Classical.choose (hrep ν)) = ν₁)
    (hz : ∀ ν : {ν : ClassFunction (↥c.H0) // IsIrreducibleCharacter ν},
      ν.1 ∉ L → scalarProduct G χ (inducedClassFunction c.H0
        (ν.1 - rep (Classical.choose (hrep ν)))) = 0) :
    χ (x : G) =
      ∑ μ ∈ L, scalarProduct G χ (inducedClassFunction c.H0 (μ - ν₁)) * μ x := by
  classical
  have hii := lemma_1_7_ii c.H0 c.U rep hrep_irr hrep χ hχ x
  have hsum1 : (∑ i : ι, scalarProduct (↥c.H0) (fun y : ↥c.H0 => χ (y : G)) (rep i) *
      orbitSum c.H0 c.U (rep i) x) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    rw [lemma_1_7_i c.H0 c.U (U_normal_subgroupOf c h12) (lambda_hcomm c h12) (rep i) x hx]
    simp
  let S : Finset (Irr (↥c.H0)) := Finset.univ.filter (fun ν => ν.1 ∈ L)
  let f : Irr (↥c.H0) → ℂ := fun ν =>
    scalarProduct G χ (inducedClassFunction c.H0
      (ν.1 - rep (Classical.choose (hrep ν)))) * ν.1 x
  let g : ClassFunction (↥c.H0) → ℂ := fun μ =>
    scalarProduct G χ (inducedClassFunction c.H0 (μ - ν₁)) * μ x
  have hsum2 : (∑ ν : Irr (↥c.H0), f ν) = ∑ μ ∈ L, g μ := by
    have hsubset : S ⊆ Finset.univ := Finset.subset_univ S
    have hsum2a : (∑ ν : Irr (↥c.H0), f ν) = ∑ ν ∈ S, f ν := by
      symm
      refine Finset.sum_subset hsubset ?_
      intro ν hνuniv hνnot
      have hnotL : ν.1 ∉ L := by
        intro hL
        exact hνnot (Finset.mem_filter.mpr ⟨Finset.mem_univ ν, hL⟩)
      simp [f, hz ν hnotL]
    have hsum2b : (∑ ν ∈ S, f ν) = ∑ μ ∈ L, g μ := by
      refine Finset.sum_bij (fun ν _ => ν.1) ?_ ?_ ?_ ?_
      · intro ν hν
        exact (Finset.mem_filter.mp hν).2
      · intro a ha b hb hEq
        exact Subtype.ext hEq
      · intro μ hμ
        have hμ₁ : μ ∈ orbit c.H0 c.U ν₁ := by
          rw [← hL]
          exact hμ
        refine ⟨⟨μ, orbit_mem_isIrreducible c.H0 c.U hν₁ hμ₁⟩, ?_, ?_⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hμ⟩
        · simpa [f, g, hrepL ⟨μ, orbit_mem_isIrreducible c.H0 c.U hν₁ hμ₁⟩ hμ]
      · intro a ha
        simpa [f, g, hrepL a (Finset.mem_filter.mp ha).2]
    rw [hsum2a, hsum2b]
  rw [hii, hsum1, hsum2]
  simp [g]

/-- Simplification of an orbit sum whose coefficients are `0` everywhere
except `-1` at `ν₂`, `ν₃`, and on a small `Bad` subset: the sum is
`-ν₂ x - ν₃ x - Σ_{μ∈Bad} μ x`. -/
private lemma orbit_sum_coeff_fixed (c : Hyp11 G)
    {L : Finset (ClassFunction (↥c.H0))}
    (ν₁ ν₂ ν₃ : ClassFunction (↥c.H0))
    (Bad : Finset (ClassFunction (↥c.H0)))
    (hν₁L : ν₁ ∈ L) (hν₂L : ν₂ ∈ L) (hν₃L : ν₃ ∈ L)
    (hBadL : Bad ⊆ L)
    (hν₁₂ : ν₁ ≠ ν₂) (hν₁₃ : ν₁ ≠ ν₃) (hν₂₃ : ν₂ ≠ ν₃)
    (h₁Bad : ν₁ ∉ Bad) (h₂Bad : ν₂ ∉ Bad) (h₃Bad : ν₃ ∉ Bad)
    (coeff : ClassFunction (↥c.H0) → ℂ)
    (hcoeff₁ : coeff ν₁ = 0) (hcoeff₂ : coeff ν₂ = -1)
    (hcoeff₃ : coeff ν₃ = -1)
    (hcoeffBad : ∀ μ ∈ Bad, coeff μ = -1)
    (hcoeff0 : ∀ μ ∈ L, μ ∉ ({ν₁, ν₂, ν₃} : Finset (ClassFunction (↥c.H0))) ∪ Bad →
      coeff μ = 0)
    (x : ↥c.H0) :
    (∑ μ ∈ L, coeff μ * μ x) = -ν₂ x - ν₃ x - ∑ μ ∈ Bad, μ x := by
  classical
  let U : Finset (ClassFunction (↥c.H0)) :=
    ({ν₁, ν₂, ν₃} : Finset (ClassFunction (↥c.H0))) ∪ Bad
  have hUL : U ⊆ L := by
    intro μ hμ
    rw [Finset.mem_union] at hμ
    rcases hμ with hμT | hμB
    · rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hμT
      rcases hμT with h | h | h
      · rwa [h]
      · rwa [h]
      · rwa [h]
    · exact hBadL hμB
  have hsumL : (∑ μ ∈ L, coeff μ * μ x) = ∑ μ ∈ U, coeff μ * μ x := by
    symm
    refine Finset.sum_subset hUL ?_
    intro μ hμL hμnot
    rw [hcoeff0 μ hμL hμnot]
    simp
  have hdisj : Disjoint ({ν₁, ν₂, ν₃} : Finset (ClassFunction (↥c.H0))) Bad := by
    rw [Finset.disjoint_left]
    intro μ hμT hμB
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hμT
    rcases hμT with h | h | h
    · exact h₁Bad (by simpa [h] using hμB)
    · exact h₂Bad (by simpa [h] using hμB)
    · exact h₃Bad (by simpa [h] using hμB)
  have hTriple : (∑ μ ∈ ({ν₁, ν₂, ν₃} : Finset (ClassFunction (↥c.H0))),
      coeff μ * μ x) = -ν₂ x - ν₃ x := by
    rw [Finset.sum_insert]
    · rw [Finset.sum_insert]
      · rw [Finset.sum_singleton]
        simp [hcoeff₁, hcoeff₂, hcoeff₃]
        ring
      · intro h
        exact hν₂₃ (by simpa using h)
    · intro h
      rw [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h | h
      · exact hν₁₂ (by simpa [h])
      · exact hν₁₃ (by simpa [h])
  have hBadSum : (∑ μ ∈ Bad, coeff μ * μ x) = - (∑ μ ∈ Bad, μ x) := by
    rw [Finset.sum_congr rfl (by intro μ hμ; rw [hcoeffBad μ hμ])]
    simp [Finset.sum_neg_distrib]
  rw [hsumL, Finset.sum_union hdisj, hTriple, hBadSum]
  ring

/-- Simplification of the orbit sum for `θ̃₂ = χ₂₃ − (ν₁−ν₂)*` in the
fixed-member case: coefficients are `0` at `ν₁`, `+1` at `ν₂` and `σν₂`,
`+1` at the bad fixed member `ν`, an unknown `m ∈ {0,1}` at the other fixed
member `ν'`, and `0` everywhere else. -/
private lemma orbit_sum_coeff_theta_tilde_two (c : Hyp11 G)
    {L U : Finset (ClassFunction (↥c.H0))}
    (ν₁ ν₂ σν₂ ν ν' : ClassFunction (↥c.H0)) (m : ℂ)
    (hν₁L : ν₁ ∈ L) (hν₂L : ν₂ ∈ L) (hσL : σν₂ ∈ L)
    (hνL : ν ∈ L) (hν'L : ν' ∈ L)
    (hUL : U ⊆ L)
    (hU : U = insert ν' (insert ν (insert σν₂ (insert ν₂ {ν₁}))))
    (hν₁₂ : ν₁ ≠ ν₂) (hν₁σ : ν₁ ≠ σν₂) (hν₁ν : ν₁ ≠ ν) (hν₁ν' : ν₁ ≠ ν')
    (hν₂σ : ν₂ ≠ σν₂) (hν₂ν : ν₂ ≠ ν) (hν₂ν' : ν₂ ≠ ν')
    (hσν : σν₂ ≠ ν) (hσν' : σν₂ ≠ ν')
    (hνν' : ν ≠ ν')
    (coeff : ClassFunction (↥c.H0) → ℂ)
    (hcoeff₁ : coeff ν₁ = 0)
    (hcoeff₂ : coeff ν₂ = 1)
    (hcoeffσ : coeff σν₂ = 1)
    (hcoeffν : coeff ν = 1)
    (hcoeffν' : coeff ν' = m)
    (hcoeff0 : ∀ μ ∈ L, μ ∉ U →
      coeff μ = 0)
    (x : ↥c.H0) :
    (∑ μ ∈ L, coeff μ * μ x) = ν₂ x + σν₂ x + ν x + m * ν' x := by
  classical
  have hsumL : (∑ μ ∈ L, coeff μ * μ x) = ∑ μ ∈ U, coeff μ * μ x := by
    symm
    refine Finset.sum_subset hUL ?_
    intro μ hμL hμnot
    rw [hcoeff0 μ hμL hμnot]
    simp
  have hν'ne : ν' ∉ insert ν (insert σν₂ (insert ν₂ ({ν₁} : Finset (ClassFunction (↥c.H0))))) := by
    simp [hν₁ν'.symm, hν₂ν'.symm, hσν'.symm, hνν'.symm]
  have hνne : ν ∉ insert σν₂ (insert ν₂ ({ν₁} : Finset (ClassFunction (↥c.H0)))) := by
    simp [hν₁ν.symm, hν₂ν.symm, hσν.symm]
  have hσne : σν₂ ∉ insert ν₂ ({ν₁} : Finset (ClassFunction (↥c.H0))) := by
    simp [hν₁σ.symm, hν₂σ.symm]
  have hν₂ne : ν₂ ∉ ({ν₁} : Finset (ClassFunction (↥c.H0))) := by
    simp [hν₁₂.symm]
  have hsumU : (∑ μ ∈ U, coeff μ * μ x) = ν₂ x + σν₂ x + ν x + m * ν' x := by
    rw [hU]
    change (∑ μ ∈ insert ν' (insert ν (insert σν₂ (insert ν₂ {ν₁}))),
        coeff μ * μ x) = ν₂ x + σν₂ x + ν x + m * ν' x
    rw [Finset.sum_insert hν'ne, Finset.sum_insert hνne,
      Finset.sum_insert hσne, Finset.sum_insert hν₂ne, Finset.sum_singleton]
    simp [hcoeff₁, hcoeff₂, hcoeffσ, hcoeffν, hcoeffν']
    ring
  rw [hsumL, hsumU]

/-- The fixed-member arithmetic contradiction: with `σν₂(t) = ν₂(t) = a`,
`ν(t), ν'(t) ∈ {±a}` and `m ∈ {0,-1}`, the equality
`2a = -ν₂(t) - σν₂(t) - ν(t) + m·ν'(t)` is impossible for `a ≠ 0`. -/
private lemma fixed_value_contradiction (a : ℂ) (ha : a ≠ 0)
    {b s v w m : ℂ}
    (hb : b = a) (hs : s = a)
    (hv : v = a ∨ v = -a) (hw : w = a ∨ w = -a)
    (hm : m = 0 ∨ m = -1)
    (heq : 2 * a = -(b + s) - v + m * w) : False := by
  rcases hv with hv | hv <;> rcases hw with hw | hw <;> rcases hm with hm | hm
  · rw [hb, hs, hv, hw, hm] at heq
    have hz : (5 : ℂ) * a = 0 := by
      linear_combination heq
    exact ha ((mul_eq_zero.mp hz).resolve_left (by norm_num))
  · rw [hb, hs, hv, hw, hm] at heq
    have hz : (6 : ℂ) * a = 0 := by
      linear_combination heq
    exact ha ((mul_eq_zero.mp hz).resolve_left (by norm_num))
  · rw [hb, hs, hv, hw, hm] at heq
    have hz : (5 : ℂ) * a = 0 := by
      linear_combination heq
    exact ha ((mul_eq_zero.mp hz).resolve_left (by norm_num))
  · rw [hb, hs, hv, hw, hm] at heq
    have hz : (4 : ℂ) * a = 0 := by
      linear_combination heq
    exact ha ((mul_eq_zero.mp hz).resolve_left (by norm_num))
  · rw [hb, hs, hv, hw, hm] at heq
    have hz : (3 : ℂ) * a = 0 := by
      linear_combination heq
    exact ha ((mul_eq_zero.mp hz).resolve_left (by norm_num))
  · rw [hb, hs, hv, hw, hm] at heq
    have hz : (4 : ℂ) * a = 0 := by
      linear_combination heq
    exact ha ((mul_eq_zero.mp hz).resolve_left (by norm_num))
  · rw [hb, hs, hv, hw, hm] at heq
    have hz : (3 : ℂ) * a = 0 := by
      linear_combination heq
    exact ha ((mul_eq_zero.mp hz).resolve_left (by norm_num))
  · rw [hb, hs, hv, hw, hm] at heq
    have hz : (2 : ℂ) * a = 0 := by
      linear_combination heq
    exact ha ((mul_eq_zero.mp hz).resolve_left (by norm_num))

/-- A sum of at most two orbit values at the central involution is a small
integer multiple of their common absolute value `a`. -/
private lemma bad_sum_eq_small_multiple (c : Hyp11 G)
    {Bad : Finset (ClassFunction (↥c.H0))} (a : ℂ)
    (hBadcard : Bad.card = 1 ∨ Bad.card = 2)
    (hBad_t : ∀ μ ∈ Bad, μ (tH0 c) = a ∨ μ (tH0 c) = -a) :
    ∃ n : ℤ, n.natAbs ≤ 2 ∧ ∑ μ ∈ Bad, μ (tH0 c) = (n : ℂ) * a := by
  rcases hBadcard with hBad1 | hBad2
  · rcases Finset.card_eq_one.mp hBad1 with ⟨b, hb⟩
    have hbt : b (tH0 c) = a ∨ b (tH0 c) = -a :=
      hBad_t b (by rw [hb]; simp)
    rcases hbt with hba | hbna
    · refine ⟨1, by norm_num, ?_⟩
      rw [hb]
      simp [hba]
    · refine ⟨-1, by norm_num, ?_⟩
      rw [hb]
      simp [hbna]
  · rcases Finset.card_eq_two.mp hBad2 with ⟨b, d, hbd, hb⟩
    have hbt : b (tH0 c) = a ∨ b (tH0 c) = -a :=
      hBad_t b (by rw [hb]; simp)
    have hdt : d (tH0 c) = a ∨ d (tH0 c) = -a :=
      hBad_t d (by rw [hb]; simp)
    rcases hbt with hba | hbna <;> rcases hdt with hda | hdna
    · refine ⟨2, by norm_num, ?_⟩
      rw [hb]
      rw [Finset.sum_insert (by simpa using hbd), Finset.sum_singleton]
      simp [hba, hda]
      ring
    · refine ⟨0, by norm_num, ?_⟩
      rw [hb]
      rw [Finset.sum_insert (by simpa using hbd), Finset.sum_singleton]
      simp [hba, hdna]
    · refine ⟨0, by norm_num, ?_⟩
      rw [hb]
      rw [Finset.sum_insert (by simpa using hbd), Finset.sum_singleton]
      simp [hbna, hda]
    · refine ⟨-2, by norm_num, ?_⟩
      rw [hb]
      rw [Finset.sum_insert (by simpa using hbd), Finset.sum_singleton]
      simp [hbna, hdna]
      ring

set_option maxHeartbeats 8000000 in
/-- The arithmetic contradiction behind the fixed-member case: if the
Fourier formulas give
`θ̃₂(t)+ν₂(t)+ν₃(t)+Σ_{μ∈Bad} μ(t) = 0` and the same with `θ̃₃`, while
`θ̃₂(t) = 2ν₂(t)` and `θ̃₃(t) = 2ν₃(t)`, then `4ν₂(t) + Σ μ(t) = 0`; the
left side has absolute value at least `2|ν₂(t)|`, contradiction (all orbit
values at the central involution `t` are `±ν₂(t)` and `|Bad| ≤ 2`). -/
private lemma fixed_pairing_contradiction_of_formulas (c : Hyp11 G)
    (ν₂ ν₃ : ClassFunction (↥c.H0)) (a : ℂ) (ha : a ≠ 0)
    (hν₂t : ν₂ (tH0 c) = a ∨ ν₂ (tH0 c) = -a)
    (hν₃t : ν₃ (tH0 c) = a ∨ ν₃ (tH0 c) = -a)
    (Bad : Finset (ClassFunction (↥c.H0)))
    (hBadcard : Bad.card = 1 ∨ Bad.card = 2)
    (hBad_t : ∀ μ ∈ Bad, μ (tH0 c) = a ∨ μ (tH0 c) = -a)
    (th2 th3 : ClassFunction G)
    (hth2 : th2 c.t = 2 * ν₂ (tH0 c))
    (hth3 : th3 c.t = 2 * ν₃ (tH0 c))
    (hf2 : th2 c.t + ν₂ (tH0 c) + ν₃ (tH0 c) + ∑ μ ∈ Bad, μ (tH0 c) = 0)
    (hf3 : th3 c.t + ν₂ (tH0 c) + ν₃ (tH0 c) + ∑ μ ∈ Bad, μ (tH0 c) = 0) :
    False := by
  classical
  have hA : 3 * ν₂ (tH0 c) + ν₃ (tH0 c) + (∑ μ ∈ Bad, μ (tH0 c)) = 0 := by
    have h := hf2
    rw [hth2] at h
    ring_nf at h
    simpa [add_comm, mul_comm, add_left_comm] using h
  have hB : ν₂ (tH0 c) + 3 * ν₃ (tH0 c) + (∑ μ ∈ Bad, μ (tH0 c)) = 0 := by
    have h := hf3
    rw [hth3] at h
    ring_nf at h
    simpa [add_comm, mul_comm, add_left_comm] using h
  have hsub : ν₂ (tH0 c) = ν₃ (tH0 c) := by
    have hz : 2 * ν₂ (tH0 c) - 2 * ν₃ (tH0 c) = 0 := by
      linear_combination hA - hB
    have hz' : 2 * (ν₂ (tH0 c) - ν₃ (tH0 c)) = 0 := by
      linear_combination hz
    have hz'' : ν₂ (tH0 c) - ν₃ (tH0 c) = 0 :=
      (mul_eq_zero.mp hz').resolve_left (by norm_num)
    exact sub_eq_zero.mp hz''
  have hD : 4 * ν₂ (tH0 c) + (∑ μ ∈ Bad, μ (tH0 c)) = 0 := by
    have h := hA
    rw [hsub] at h
    ring_nf at h
    simpa [hsub, mul_comm, add_comm, add_left_comm] using h
  rcases bad_sum_eq_small_multiple c a hBadcard hBad_t with ⟨n, hn, hS⟩
  rw [hS] at hD
  rcases hν₂t with hν₂a | hν₂na
  · rw [hν₂a] at hD
    ring_nf at hD
    have hnz : (4 + n : ℤ) ≠ 0 := by omega
    have hD' : ((4 + n : ℤ) : ℂ) * a = 0 := by
      have hcast : ((4 + n : ℤ) : ℂ) = (4 : ℂ) + (n : ℂ) := by norm_num
      rw [hcast, ← hD]
      ring
    have ha0 : a = 0 := (mul_eq_zero.mp hD').resolve_left (by exact_mod_cast hnz)
    exact ha ha0
  · rw [hν₂na] at hD
    ring_nf at hD
    have hnz : (n - 4 : ℤ) ≠ 0 := by omega
    have hD' : ((n - 4 : ℤ) : ℂ) * a = 0 := by
      have hcast : ((n - 4 : ℤ) : ℂ) = (n : ℂ) - (4 : ℂ) := by norm_num
      rw [hcast, ← hD]
      ring
    have ha0 : a = 0 := (mul_eq_zero.mp hD').resolve_left (by exact_mod_cast hnz)
    exact ha ha0
set_option maxHeartbeats 8000000 in
private lemma exists_theta_lift_orbit (c : Hyp11 G) (h12 : Hyp12 c)
    (hH0index : (c.H0.subgroupOf c.H).index = 2)
    (ν₀ : ClassFunction (↥c.H0)) (hν₀ : IsIrreducibleCharacter ν₀) :
    Nonempty (ThetaLift c h12 (orbit c.H0 c.U ν₀)
      (thetaOfOrbit c h12 (orbit c.H0 c.U ν₀))) := by
  classical
  let L : Finset (ClassFunction (↥c.H0)) := orbit c.H0 c.U ν₀
  have hν₀L : ν₀ ∈ L := orbit_self_mem c ν₀
  have hνirr : ∀ ν ∈ L, IsIrreducibleCharacter ν :=
    fun ν hνL => orbit_mem_isIrreducible c.H0 c.U hν₀ hνL
  by_cases h_inv : conjChar c.H0 (s_normalizes_H0 c h12) ν₀ ∈ L
  · -- the `s`-invariant orbit: `σ(L) = L`, each `θ`-fiber an `s`-pair
    -- `{a, σa}`, exactly two `s`-fixed members (the norm-2 values), the rest
    -- in `s`-pairs (the norm-1 values)
    have hfix : (L.filter (fun μ => conjChar c.H0 (s_normalizes_H0 c h12) μ = μ)).card = 2 := by
      change ((orbit c.H0 c.U ν₀).filter (fun μ =>
        conjChar c.H0 (s_normalizes_H0 c h12) μ = μ)).card = 2
      exact orbit_s_fixed_card_eq_two_of_invariant c h12 hν₀ h_inv
    -- `|L|` is a 2-power (`orbit_card_is_pow_two`), and the two `s`-fixed
    -- members make `|L| ≠ 2` impossible in the pair-counting: the non-fixed
    -- members come in `s`-pairs, and `|L| = 2` with `hfix = 2` would force
    -- `σ a = ν₀` for the second member (then `σ² = id` gives `a = ν₀`)
    have hLpow : ∃ k : ℕ, L.card = 2 ^ k := by
      change ∃ k : ℕ, (orbit c.H0 c.U ν₀).card = 2 ^ k
      exact orbit_card_is_pow_two c h12 ν₀
    by_cases hL2 : L.card = 2
    · -- the `n = 2` sub-case: `L = {ν₀, a}` with both members `s`-fixed
      -- (the two norm-2 values): `|L| = 2` forces every member `s`-fixed
      -- (the fixed-card is already `2`), and `δ* = (ν₀ − a)*` has norm `4`
      -- with `δ*(1) = 0`, so the norm-4 decomposition gives the norm-2
      -- halves `A, B` with `δ* = A − B`, and the two-valued lift is
      -- `theta_lift_two_invariant` (the singleton `θ`-fibers)
      have hfilter : (L.filter (fun μ => conjChar c.H0 (s_normalizes_H0 c h12) μ = μ)) = L := by
        apply Finset.eq_of_subset_of_card_le
        · intro μ hμ
          exact (Finset.mem_filter.mp hμ).1
        · rw [hfix, hL2]
      have hfix₀ : conjChar c.H0 (s_normalizes_H0 c h12) ν₀ = ν₀ := by
        have hν₀f : ν₀ ∈ L.filter (fun μ => conjChar c.H0 (s_normalizes_H0 c h12) μ = μ) := by
          simpa [hfilter] using hν₀L
        exact (Finset.mem_filter.mp hν₀f).2
      rcases Finset.card_pos.mp (by
        rw [Finset.card_erase_of_mem hν₀L]
        omega : 0 < (L.erase ν₀).card) with ⟨ν₂, hν₂e⟩
      have hν₂ne : ν₂ ≠ ν₀ := (Finset.mem_erase.mp hν₂e).1
      have hν₂L : ν₂ ∈ L := (Finset.mem_erase.mp hν₂e).2
      have hfix₂ : conjChar c.H0 (s_normalizes_H0 c h12) ν₂ = ν₂ := by
        have hν₂f : ν₂ ∈ L.filter (fun μ => conjChar c.H0 (s_normalizes_H0 c h12) μ = μ) := by
          simpa [hfilter] using hν₂L
        exact (Finset.mem_filter.mp hν₂f).2
      -- `δ* = (ν₀ − ν₂)*`: a generalized character of norm `4` vanishing at `1`
      have hδg : IsGeneralizedCharacter (inducedClassFunction c.H0 (ν₀ - ν₂)) := by
        exact isGeneralizedCharacter_induced c h12 (ν₀ - ν₂)
          (isGeneralizedCharacter_sub_irr hν₀ (hνirr ν₂ hν₂L))
      have hν₀₂ : ν₀ ∈ orbit c.H0 c.U ν₂ := by
        rw [orbit_eq_of_mem c hν₂L]
        exact hν₀L
      have hσ₀₂ : conjChar c.H0 (s_normalizes_H0 c h12) ν₀ ≠ ν₂ := by
        intro hEq
        apply hν₂ne
        rw [hfix₀] at hEq
        exact hEq.symm
      have hδnorm : normSq G (inducedClassFunction c.H0 (ν₀ - ν₂)) = 4 := by
        rw [delta_norm c h12 hH0index hν₀ (hνirr ν₂ hν₂L) hν₀₂ hν₂ne.symm hσ₀₂]
        rw [theta_norm c h12 hH0index hν₀, theta_norm c h12 hH0index (hνirr ν₂ hν₂L)]
        rw [if_pos hfix₀, if_pos hfix₂]
        norm_num
      have hdeg01 : ν₀ 1 = ν₂ 1 := (orbit_mem_degree_eq c hν₂L).symm
      have hδdeg : (inducedClassFunction c.H0 (ν₀ - ν₂)) 1 = 0 :=
        inducedFromSub_one_eq c h12 hdeg01
      -- the norm-4 decomposition into the norm-2 halves
      rcases normSq4_decomp_of_zero_one hδg hδnorm hδdeg with
        ⟨A, B, hAg, hBg, hAnorm, hBnorm, hAB, hδAB⟩
      have hdegAB : A 1 = B 1 := by
        have hδ1 := hδdeg
        rw [hδAB] at hδ1
        exact sub_eq_zero.mp (by simpa using hδ1)
      exact theta_lift_two_invariant c h12 hH0index ν₀ ν₂ hν₀ (hνirr ν₂ hν₂L) hν₂L h_inv
        hfix₀ hfix₂ hν₂ne hL2 A B hAg hBg hAnorm hBnorm hAB hdegAB hδAB
    · by_cases hL4 : L.card = 4
      · -- the `n = 3` sub-case: `ν₁ :=` the non-fixed member, `ν₂, ν₃ :=`
        -- the two `s`-fixed members; `|δᵢ*|² = 1 + 2 = 3` so the common
        -- constituent uses the norm-3 extraction
        -- (`exists_common_constituent_self_norm3`); the `hχall`-pairings
        -- are exactly the extraction pairings, since the only other
        -- members are `ν₁, σν₁`, excluded by the `hχall`-conjuncts
        let N : Finset (ClassFunction (↥c.H0)) := L.filter (fun μ =>
          conjChar c.H0 (s_normalizes_H0 c h12) μ ≠ μ)
        let F : Finset (ClassFunction (↥c.H0)) := L.filter (fun μ =>
          conjChar c.H0 (s_normalizes_H0 c h12) μ = μ)
        have hFsL : F ⊆ L := by
          intro μ hμ
          exact (Finset.mem_filter.mp hμ).1
        have hFcard : F.card = 2 := by
          simpa [F] using hfix
        have hNcard : N.card = 2 := by
          have hNcomp : N = L \ F := by
            ext μ
            constructor
            · intro hμN
              refine Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp hμN).1, ?_⟩
              intro hμF
              exact (Finset.mem_filter.mp hμN).2 (Finset.mem_filter.mp hμF).2
            · intro hμsd
              refine Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hμsd).1, ?_⟩
              intro hfix
              exact (Finset.mem_sdiff.mp hμsd).2
                (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hμsd).1, hfix⟩)
          rw [hNcomp]
          rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hFsL, hL4, hFcard]
        rcases Finset.card_pos.mp (by omega : 0 < N.card) with ⟨ν₁, hν₁N⟩
        have hν₁L : ν₁ ∈ L := (Finset.mem_filter.mp hν₁N).1
        have hν₁s : conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ≠ ν₁ := (Finset.mem_filter.mp hν₁N).2
        have hν₁irr : IsIrreducibleCharacter ν₁ := hνirr ν₁ hν₁L
        rcases Finset.card_pos.mp (by omega : 0 < F.card) with ⟨ν₂, hν₂F⟩
        have hν₂L : ν₂ ∈ L := (Finset.mem_filter.mp hν₂F).1
        have hfix₂ : conjChar c.H0 (s_normalizes_H0 c h12) ν₂ = ν₂ := (Finset.mem_filter.mp hν₂F).2
        have hν₂irr : IsIrreducibleCharacter ν₂ := hνirr ν₂ hν₂L
        rcases Finset.card_pos.mp (by
          rw [Finset.card_erase_of_mem hν₂F]
          omega : 0 < (F.erase ν₂).card) with ⟨ν₃, hν₃Fe⟩
        have hν₃F : ν₃ ∈ F := (Finset.mem_erase.mp hν₃Fe).2
        have hν₃L : ν₃ ∈ L := (Finset.mem_filter.mp hν₃F).1
        have hfix₃ : conjChar c.H0 (s_normalizes_H0 c h12) ν₃ = ν₃ := (Finset.mem_filter.mp hν₃F).2
        have hν₃irr : IsIrreducibleCharacter ν₃ := hνirr ν₃ hν₃L
        have hν₃ne2 : ν₃ ≠ ν₂ := (Finset.mem_erase.mp hν₃Fe).1
        -- the `s`-conditions of the picked members
        have hν₂ne1 : ν₁ ≠ ν₂ := by
          intro hEq
          apply hν₁s
          rw [hEq, hfix₂]
        have hν₃ne1 : ν₁ ≠ ν₃ := by
          intro hEq
          apply hν₁s
          rw [hEq, hfix₃]
        have hσ₁₂ : conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ≠ ν₂ := by
          intro hEq
          apply hν₂ne1
          have hc := congrArg (conjChar c.H0 (s_normalizes_H0 c h12)) hEq
          rw [conjChar_conjChar c h12 ν₁, hfix₂] at hc
          exact hc
        have hσ₁₃ : conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ≠ ν₃ := by
          intro hEq
          apply hν₃ne1
          have hc := congrArg (conjChar c.H0 (s_normalizes_H0 c h12)) hEq
          rw [conjChar_conjChar c h12 ν₁, hfix₃] at hc
          exact hc
        have hσ₂₃ : conjChar c.H0 (s_normalizes_H0 c h12) ν₂ ≠ ν₃ := by
          intro hEq
          apply hν₃ne2
          rw [hfix₂] at hEq
          exact hEq.symm
        -- `δ₂*`, `δ₃*`: generalized characters of norm `3` with pairing `1`
        have hδ₂g : IsGeneralizedCharacter (inducedClassFunction c.H0 (ν₁ - ν₂)) := by
          exact isGeneralizedCharacter_induced c h12 (ν₁ - ν₂)
            (isGeneralizedCharacter_sub_irr hν₁irr hν₂irr)
        have hδ₃g : IsGeneralizedCharacter (inducedClassFunction c.H0 (ν₁ - ν₃)) := by
          exact isGeneralizedCharacter_induced c h12 (ν₁ - ν₃)
            (isGeneralizedCharacter_sub_irr hν₁irr hν₃irr)
        have h₁₂' : ν₁ ∈ orbit c.H0 c.U ν₂ := by
          rw [orbit_eq_of_mem c hν₂L]
          exact hν₁L
        have h₁₃' : ν₁ ∈ orbit c.H0 c.U ν₃ := by
          rw [orbit_eq_of_mem c hν₃L]
          exact hν₁L
        have hδ₂norm : normSq G (inducedClassFunction c.H0 (ν₁ - ν₂)) = 3 := by
          rw [delta_norm c h12 hH0index hν₁irr hν₂irr h₁₂' hν₂ne1 hσ₁₂]
          rw [theta_norm c h12 hH0index hν₁irr, theta_norm c h12 hH0index hν₂irr]
          rw [if_neg hν₁s, if_pos hfix₂]
          norm_num
        have hδ₃norm : normSq G (inducedClassFunction c.H0 (ν₁ - ν₃)) = 3 := by
          rw [delta_norm c h12 hH0index hν₁irr hν₃irr h₁₃' hν₃ne1 hσ₁₃]
          rw [theta_norm c h12 hH0index hν₁irr, theta_norm c h12 hH0index hν₃irr]
          rw [if_neg hν₁s, if_pos hfix₃]
          norm_num
        have hδ₂₃pair : scalarProduct G (inducedClassFunction c.H0 (ν₁ - ν₂))
            (inducedClassFunction c.H0 (ν₁ - ν₃)) = 1 := by
          have hsp := delta_pair_scalar (ν₁ := ν₁) (ν₂ := ν₁) (μ₁ := ν₂) (μ₂ := ν₃)
            c h12 hν₁irr hν₁irr
            (by rw [orbit_eq_of_mem c hν₁L]; exact hν₂L)
            (by rw [orbit_eq_of_mem c hν₁L]; exact hν₃L)
          rw [show inducedClassFunction c.H0 (ν₁ - ν₂) = -inducedClassFunction c.H0 (ν₂ - ν₁) by
            rw [show ν₁ - ν₂ = -(ν₂ - ν₁) by ring]
            rw [inducedClassFunction_neg]]
          rw [show inducedClassFunction c.H0 (ν₁ - ν₃) = -inducedClassFunction c.H0 (ν₃ - ν₁) by
            rw [show ν₁ - ν₃ = -(ν₃ - ν₁) by ring]
            rw [inducedClassFunction_neg]]
          rw [scalarProduct_neg_left, scalarProduct_neg_right, hsp]
          simp
          rw [scalarProduct_sub_left, scalarProduct_sub_right, scalarProduct_sub_right]
          have hθ₁₁ : scalarProduct (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν₁)
              (inducedFromSub (h12.H0_normal_in_H).1 ν₁) = 1 := by
            change normSq (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν₁) = 1
            rw [theta_norm c h12 hH0index hν₁irr]
            rw [if_neg hν₁s]
          have hθ₂₁ : scalarProduct (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν₂)
              (inducedFromSub (h12.H0_normal_in_H).1 ν₁) = 0 := by
            exact theta_pair_scalar_zero c h12 hH0index hν₂irr hν₁irr hν₂ne1.symm (by
              intro hEq
              have hc := hEq.symm
              rw [hfix₂] at hc
              exact hν₂ne1 hc)
          have hθ₁₃ : scalarProduct (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν₁)
              (inducedFromSub (h12.H0_normal_in_H).1 ν₃) = 0 := by
            exact theta_pair_scalar_zero c h12 hH0index hν₁irr hν₃irr hν₃ne1 hσ₁₃
          have hθ₂₃ : scalarProduct (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν₂)
              (inducedFromSub (h12.H0_normal_in_H).1 ν₃) = 0 := by
            exact theta_pair_scalar_zero c h12 hH0index hν₂irr hν₃irr hν₃ne2.symm hσ₂₃
          rw [hθ₂₃, hθ₂₁, hθ₁₃, hθ₁₁]
          norm_num
        -- the common constituent `χ₂₃` via the norm-3 extraction
        rcases exists_common_constituent_self_norm3 c h12 hδ₂g hδ₃g hδ₂norm hδ₃norm hδ₂₃pair with
          ⟨χ₂₃, hχ23irr, hχ₂, hχ₃⟩
        have hχg : IsGeneralizedCharacter χ₂₃ := by
          rcases hχ23irr with hχ | hχ
          · exact isGeneralizedCharacter_of_isCharacter (isCharacter_of_isIrreducibleCharacter hχ)
          · simpa using isGeneralizedCharacter_of_signed_irreducible hχ
        have hχ₁ : normSq G χ₂₃ = 1 := by
          rcases hχ23irr with hχ | hχ
          · change scalarProduct G χ₂₃ χ₂₃ = 1
            exact irreducible_scalarProduct_self hχ
          · change scalarProduct G χ₂₃ χ₂₃ = 1
            simpa [scalarProduct_neg_left, scalarProduct_neg_right] using
              irreducible_scalarProduct_self hχ
        -- `hχall`: the only members outside `{ν₁, σν₁}` are the fixed
        -- `ν₂, ν₃`, whose pairings are the extraction pairings
        have hχall : ∀ ν ∈ L, ν ≠ ν₁ →
            conjChar c.H0 (s_normalizes_H0 c h12) ν ≠ ν₁ →
            scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - ν)) = 1 := by
          intro ν hνL hνne1 hσνne1
          by_cases hν₂eq : ν = ν₂
          · rw [hν₂eq]
            exact hχ₂
          · by_cases hν₃eq : ν = ν₃
            · rw [hν₃eq]
              exact hχ₃
            · exfalso
              have hνNF : ν ∈ N ∨ ν ∈ F := by
                by_cases hfixν : conjChar c.H0 (s_normalizes_H0 c h12) ν = ν
                · right
                  exact Finset.mem_filter.mpr ⟨hνL, hfixν⟩
                · left
                  exact Finset.mem_filter.mpr ⟨hνL, hfixν⟩
              rcases hνNF with hνN | hνF
              · -- `ν ∈ N = {ν₁, σν₁}` contradicts `ν ≠ ν₁`/`σν ≠ ν₁`
                have hN₁σ : N = ({ν₁, conjChar c.H0 (s_normalizes_H0 c h12) ν₁} :
                    Finset (ClassFunction (↥c.H0))) := by
                  rcases Finset.card_eq_one.mp (by
                    rw [Finset.card_erase_of_mem hν₁N]
                    omega : (N.erase ν₁).card = 1) with ⟨b, hb⟩
                  have hbσ : b = conjChar c.H0 (s_normalizes_H0 c h12) ν₁ := by
                    have hσN : conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ∈ N := by
                      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
                      · change conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ∈ orbit c.H0 c.U ν₀
                        exact orbit_s_closed_of_invariant c h12 h_inv hν₁L
                      · intro hEq
                        apply hν₁s
                        exact hEq.symm.trans (conjChar_conjChar c h12 ν₁)
                    have hσe : conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ∈ N.erase ν₁ :=
                      Finset.mem_erase.mpr ⟨hν₁s, hσN⟩
                    rw [hb] at hσe
                    rw [Finset.mem_singleton] at hσe
                    exact hσe.symm
                  rw [← Finset.insert_erase hν₁N, hb, hbσ]
                rw [hN₁σ] at hνN
                rw [Finset.mem_insert, Finset.mem_singleton] at hνN
                rcases hνN with h | h
                · exact hνne1 h
                · exact hσνne1 (by
                    rw [h]
                    exact conjChar_conjChar c h12 ν₁)
              · -- `ν ∈ F = {ν₂, ν₃}` contradicts `ν ≠ ν₂`/`ν ≠ ν₃`
                have hF₂₃ : F = ({ν₂, ν₃} : Finset (ClassFunction (↥c.H0))) := by
                  rcases Finset.card_eq_one.mp (by
                    rw [Finset.card_erase_of_mem hν₂F]
                    omega : (F.erase ν₂).card = 1) with ⟨b, hb⟩
                  have hbν₃ : b = ν₃ := by
                    have hν₃e : ν₃ ∈ F.erase ν₂ := hν₃Fe
                    rw [hb] at hν₃e
                    rw [Finset.mem_singleton] at hν₃e
                    exact hν₃e.symm
                  rw [← Finset.insert_erase hν₂F, hb, hbν₃]
                rw [hF₂₃] at hνF
                rw [Finset.mem_insert, Finset.mem_singleton] at hνF
                rcases hνF with h | h
                · exact hν₂eq h
                · exact hν₃eq h
        exact exists_theta_lift_invariant c h12 hH0index ν₀ ν₁ hν₀ hν₁irr hν₁L h_inv hν₁s
          hχg hχ₁ hχall
      · -- the `n ≥ 5` sub-case (`|L| ≥ 8`): pick `ν₁, ν₂, ν₃` among the
        -- non-fixed members (one per `s`-pair, `|L| − 2 ≥ 6` of them) and
        -- extract via the norm-2 variant; `hχall` for the non-fixed members
        -- is the norm-two constituent argument, while the fixed members are
        -- the recorded undefined-case bridge below.
        let N : Finset (ClassFunction (↥c.H0)) := L.filter (fun μ =>
          conjChar c.H0 (s_normalizes_H0 c h12) μ ≠ μ)
        let F : Finset (ClassFunction (↥c.H0)) := L.filter (fun μ =>
          conjChar c.H0 (s_normalizes_H0 c h12) μ = μ)
        have hFsL : F ⊆ L := by
          intro μ hμ
          exact (Finset.mem_filter.mp hμ).1
        have hFcard : F.card = 2 := by
          simpa [F] using hfix
        have hNcomp : N = L \ F := by
          ext μ
          constructor
          · intro hμN
            refine Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp hμN).1, ?_⟩
            intro hμF
            exact (Finset.mem_filter.mp hμN).2 (Finset.mem_filter.mp hμF).2
          · intro hμsd
            refine Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hμsd).1, ?_⟩
            intro hfix
            exact (Finset.mem_sdiff.mp hμsd).2
              (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hμsd).1, hfix⟩)
        have hNcard : N.card = L.card - 2 := by
          rw [hNcomp, Finset.card_sdiff, Finset.inter_eq_left.mpr hFsL, hFcard]
        have hLge8 : 8 ≤ L.card := by
          have hLge2 : 2 ≤ L.card := by
            simpa [hFcard] using (Finset.card_le_card hFsL)
          rcases hLpow with ⟨k, hk⟩
          have hk3 : 3 ≤ k := by
            by_contra hklt
            have hk_le : k ≤ 2 := by omega
            have hk_cases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
            rcases hk_cases with hk0 | hk1 | hk2
            · have hc : L.card = 1 := by
                rw [hk, hk0]
                norm_num
              omega
            · have hc : L.card = 2 := by
                rw [hk, hk1]
                norm_num
              exact hL2 hc
            · have hc : L.card = 4 := by
                rw [hk, hk2]
                norm_num
              exact hL4 hc
          have hpow_ge : 8 ≤ 2 ^ k := by
            calc
              8 = 2 ^ 3 := by norm_num
              _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hk3
          simpa [hk] using hpow_ge
        have hNcard_ge : 6 ≤ N.card := by
          rw [hNcard]
          omega
        rcases Finset.card_pos.mp (by omega : 0 < N.card) with ⟨ν₁, hν₁N⟩
        have hν₁L : ν₁ ∈ L := (Finset.mem_filter.mp hν₁N).1
        have hν₁s : conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ≠ ν₁ :=
          (Finset.mem_filter.mp hν₁N).2
        have hν₁irr : IsIrreducibleCharacter ν₁ := hνirr ν₁ hν₁L
        let A₂ : Finset (ClassFunction (↥c.H0)) :=
          (N.erase ν₁).filter (fun μ =>
            μ ≠ conjChar c.H0 (s_normalizes_H0 c h12) ν₁)
        have hA₂card : 4 ≤ A₂.card := by
          let B : Finset (ClassFunction (↥c.H0)) :=
            ({conjChar c.H0 (s_normalizes_H0 c h12) ν₁} : Finset _)
          have hA₂eq : A₂ = (N.erase ν₁) \ B := by
            ext μ
            simp [A₂, B]
          rw [hA₂eq, Finset.card_sdiff]
          have hN1 : 5 ≤ (N.erase ν₁).card := by
            rw [Finset.card_erase_of_mem hν₁N]
            omega
          have hBcard : B.card = 1 := by
            simp [B]
          have hsub : (N.erase ν₁) ∩ B ⊆ B := by
            intro x hx
            exact (Finset.mem_inter.mp hx).2
          have hle1 : ((N.erase ν₁) ∩ B).card ≤ B.card :=
            Finset.card_le_card hsub
          have hle1' : (B ∩ (N.erase ν₁)).card ≤ 1 := by
            rw [Finset.inter_comm]
            simpa [B] using hle1
          omega
        rcases Finset.card_pos.mp (by omega : 0 < A₂.card) with ⟨ν₂, hν₂A⟩
        have hν₂N1 : ν₂ ∈ N.erase ν₁ := (Finset.mem_filter.mp hν₂A).1
        have hν₂ne1 : ν₂ ≠ ν₁ := (Finset.mem_erase.mp hν₂N1).1
        have hν₂N : ν₂ ∈ N := (Finset.mem_erase.mp hν₂N1).2
        have hν₂L : ν₂ ∈ L := (Finset.mem_filter.mp hν₂N).1
        have hν₂s : conjChar c.H0 (s_normalizes_H0 c h12) ν₂ ≠ ν₂ :=
          (Finset.mem_filter.mp hν₂N).2
        have hσ₁₂ : conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ≠ ν₂ := by
          exact (Finset.mem_filter.mp hν₂A).2.symm
        have hν₂irr : IsIrreducibleCharacter ν₂ := hνirr ν₂ hν₂L
        let A₃ : Finset (ClassFunction (↥c.H0)) :=
          ((N.erase ν₁).erase ν₂).filter (fun μ =>
            μ ≠ conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ∧
              μ ≠ conjChar c.H0 (s_normalizes_H0 c h12) ν₂)
        have hA₃card : 2 ≤ A₃.card := by
          let C : Finset (ClassFunction (↥c.H0)) :=
            ({conjChar c.H0 (s_normalizes_H0 c h12) ν₁,
              conjChar c.H0 (s_normalizes_H0 c h12) ν₂} : Finset _)
          have hA₃eq : A₃ = ((N.erase ν₁).erase ν₂) \ C := by
            ext μ
            simp [A₃, C, and_comm]
          rw [hA₃eq, Finset.card_sdiff]
          have hN2 : 4 ≤ ((N.erase ν₁).erase ν₂).card := by
            rw [Finset.card_erase_of_mem hν₂N1, Finset.card_erase_of_mem hν₁N]
            omega
          have hCcard : C.card ≤ 2 := by
            by_cases hC : conjChar c.H0 (s_normalizes_H0 c h12) ν₁ =
                conjChar c.H0 (s_normalizes_H0 c h12) ν₂
            · rw [show C = ({conjChar c.H0 (s_normalizes_H0 c h12) ν₁} :
                  Finset _) by
                ext μ
                simp [C, hC]]
              simp
            · rw [Finset.card_insert_of_notMem]
              · simp
              · intro hmem
                exact hC (Finset.mem_singleton.mp hmem)
          have hsubC : ((N.erase ν₁).erase ν₂) ∩ C ⊆ C := by
            intro x hx
            exact (Finset.mem_inter.mp hx).2
          have hleC : (((N.erase ν₁).erase ν₂) ∩ C).card ≤ C.card :=
            Finset.card_le_card hsubC
          have hleC' : (C ∩ ((N.erase ν₁).erase ν₂)).card ≤ 2 := by
            simpa [Finset.inter_comm] using (le_trans hleC hCcard)
          omega
        rcases Finset.card_pos.mp (by omega : 0 < A₃.card) with ⟨ν₃, hν₃A⟩
        have hν₃N2 : ν₃ ∈ (N.erase ν₁).erase ν₂ := (Finset.mem_filter.mp hν₃A).1
        have hν₃ne2 : ν₃ ≠ ν₂ := (Finset.mem_erase.mp hν₃N2).1
        have hν₃N1 : ν₃ ∈ N.erase ν₁ := (Finset.mem_erase.mp hν₃N2).2
        have hν₃ne1 : ν₃ ≠ ν₁ := (Finset.mem_erase.mp hν₃N1).1
        have hν₃N : ν₃ ∈ N := (Finset.mem_erase.mp hν₃N1).2
        have hν₃L : ν₃ ∈ L := (Finset.mem_filter.mp hν₃N).1
        have hν₃s : conjChar c.H0 (s_normalizes_H0 c h12) ν₃ ≠ ν₃ :=
          (Finset.mem_filter.mp hν₃N).2
        have hσ₁₃ : conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ≠ ν₃ :=
          (Finset.mem_filter.mp hν₃A).2.1.symm
        have hσ₂₃ : conjChar c.H0 (s_normalizes_H0 c h12) ν₂ ≠ ν₃ :=
          (Finset.mem_filter.mp hν₃A).2.2.symm
        have hν₃irr : IsIrreducibleCharacter ν₃ := hνirr ν₃ hν₃L
        have h₁₂ : ν₁ ≠ ν₂ ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ≠ ν₂ :=
          ⟨hν₂ne1.symm, hσ₁₂⟩
        have h₁₃ : ν₁ ≠ ν₃ ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ≠ ν₃ :=
          ⟨hν₃ne1.symm, hσ₁₃⟩
        have h₂₃ : ν₂ ≠ ν₃ ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₂ ≠ ν₃ :=
          ⟨hν₃ne2.symm, hσ₂₃⟩
        -- `δ₂*`, `δ₃*`: generalized characters of norm `2` with pairing `1`
        have hδ₂g : IsGeneralizedCharacter (inducedClassFunction c.H0 (ν₁ - ν₂)) := by
          exact isGeneralizedCharacter_induced c h12 (ν₁ - ν₂)
            (isGeneralizedCharacter_sub_irr hν₁irr hν₂irr)
        have hδ₃g : IsGeneralizedCharacter (inducedClassFunction c.H0 (ν₁ - ν₃)) := by
          exact isGeneralizedCharacter_induced c h12 (ν₁ - ν₃)
            (isGeneralizedCharacter_sub_irr hν₁irr hν₃irr)
        have h₁₂' : ν₁ ∈ orbit c.H0 c.U ν₂ := by
          rw [orbit_eq_of_mem c hν₂L]
          exact hν₁L
        have h₁₃' : ν₁ ∈ orbit c.H0 c.U ν₃ := by
          rw [orbit_eq_of_mem c hν₃L]
          exact hν₁L
        have hδ₂norm : normSq G (inducedClassFunction c.H0 (ν₁ - ν₂)) = 2 := by
          rw [delta_norm c h12 hH0index hν₁irr hν₂irr h₁₂' h₁₂.1 h₁₂.2]
          rw [theta_norm c h12 hH0index hν₁irr, theta_norm c h12 hH0index hν₂irr]
          rw [if_neg hν₁s, if_neg hν₂s]
          norm_num
        have hδ₃norm : normSq G (inducedClassFunction c.H0 (ν₁ - ν₃)) = 2 := by
          rw [delta_norm c h12 hH0index hν₁irr hν₃irr h₁₃' h₁₃.1 h₁₃.2]
          rw [theta_norm c h12 hH0index hν₁irr, theta_norm c h12 hH0index hν₃irr]
          rw [if_neg hν₁s, if_neg hν₃s]
          norm_num
        have hδ₂₃pair : scalarProduct G (inducedClassFunction c.H0 (ν₁ - ν₂))
            (inducedClassFunction c.H0 (ν₁ - ν₃)) = 1 := by
          have hν₂₁ : ν₂ ∈ orbit c.H0 c.U ν₁ := by
            rw [orbit_eq_of_mem c hν₁L]
            exact hν₂L
          have hν₃₁ : ν₃ ∈ orbit c.H0 c.U ν₁ := by
            rw [orbit_eq_of_mem c hν₁L]
            exact hν₃L
          have hsp := delta_pair_scalar (ν₁ := ν₁) (ν₂ := ν₁) (μ₁ := ν₂) (μ₂ := ν₃)
            c h12 hν₁irr hν₁irr hν₂₁ hν₃₁
          rw [show inducedClassFunction c.H0 (ν₁ - ν₂) = -inducedClassFunction c.H0 (ν₂ - ν₁) by
            rw [show ν₁ - ν₂ = -(ν₂ - ν₁) by ring]
            rw [inducedClassFunction_neg]]
          rw [show inducedClassFunction c.H0 (ν₁ - ν₃) = -inducedClassFunction c.H0 (ν₃ - ν₁) by
            rw [show ν₁ - ν₃ = -(ν₃ - ν₁) by ring]
            rw [inducedClassFunction_neg]]
          rw [scalarProduct_neg_left, scalarProduct_neg_right, hsp]
          simp
          rw [scalarProduct_sub_left, scalarProduct_sub_right, scalarProduct_sub_right]
          have hθ₁₁ : scalarProduct (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν₁)
              (inducedFromSub (h12.H0_normal_in_H).1 ν₁) = 1 := by
            change normSq (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν₁) = 1
            rw [theta_norm c h12 hH0index hν₁irr]
            rw [if_neg hν₁s]
          have hσ₂₁ : conjChar c.H0 (s_normalizes_H0 c h12) ν₂ ≠ ν₁ := by
            intro hEq
            apply hσ₁₂
            have h := congrArg (conjChar c.H0 (s_normalizes_H0 c h12)) hEq
            rw [conjChar_conjChar c h12 ν₂] at h
            exact h.symm
          have hθ₂₁ : scalarProduct (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν₂)
              (inducedFromSub (h12.H0_normal_in_H).1 ν₁) = 0 := by
            exact theta_pair_scalar_zero c h12 hH0index hν₂irr hν₁irr hν₂ne1 hσ₂₁
          have hθ₁₃ : scalarProduct (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν₁)
              (inducedFromSub (h12.H0_normal_in_H).1 ν₃) = 0 := by
            exact theta_pair_scalar_zero c h12 hH0index hν₁irr hν₃irr hν₃ne1.symm hσ₁₃
          have hθ₂₃ : scalarProduct (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν₂)
              (inducedFromSub (h12.H0_normal_in_H).1 ν₃) = 0 := by
            exact theta_pair_scalar_zero c h12 hH0index hν₂irr hν₃irr hν₃ne2.symm hσ₂₃
          rw [hθ₂₃, hθ₂₁, hθ₁₃, hθ₁₁]
          norm_num
        -- the common constituent `χ₂₃` via the norm-2 extraction
        rcases exists_common_constituent_self c h12 hδ₂g hδ₃g hδ₂norm hδ₃norm hδ₂₃pair with
          ⟨χ₂₃, hχ23irr, hχ₂, hχ₃⟩
        have hχg : IsGeneralizedCharacter χ₂₃ := by
          rcases hχ23irr with hχ | hχ
          · exact isGeneralizedCharacter_of_isCharacter (isCharacter_of_isIrreducibleCharacter hχ)
          · simpa using isGeneralizedCharacter_of_signed_irreducible hχ
        have hχ₁ : normSq G χ₂₃ = 1 := by
          rcases hχ23irr with hχ | hχ
          · change scalarProduct G χ₂₃ χ₂₃ = 1
            exact irreducible_scalarProduct_self hχ
          · change scalarProduct G χ₂₃ χ₂₃ = 1
            simpa [scalarProduct_neg_left, scalarProduct_neg_right] using
              irreducible_scalarProduct_self hχ
        -- `hχall`: non-fixed members by the norm-two constituent argument;
        -- the fixed members are the recorded undefined-case bridge.
        have hχall : ∀ ν ∈ L, ν ≠ ν₁ →
            conjChar c.H0 (s_normalizes_H0 c h12) ν ≠ ν₁ →
            scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - ν)) = 1 := by
          intro ν hνL hνne1 hσνne1
          by_cases hν₂eq : ν = ν₂
          · rw [hν₂eq]
            exact hχ₂
          · by_cases hν₃eq : ν = ν₃
            · rw [hν₃eq]
              exact hχ₃
            · by_cases hν₂σ : ν = conjChar c.H0 (s_normalizes_H0 c h12) ν₂
              · rw [hν₂σ]
                have hzero : inducedClassFunction c.H0
                    (conjChar c.H0 (s_normalizes_H0 c h12) ν₂ - ν₂) = 0 :=
                  sigma_pair_star_zero_of_invariant c h12 hH0index hν₀ h_inv hν₂L
                have hδ : inducedClassFunction c.H0
                    (ν₁ - conjChar c.H0 (s_normalizes_H0 c h12) ν₂) =
                    inducedClassFunction c.H0 (ν₁ - ν₂) := by
                  rw [show ν₁ - conjChar c.H0 (s_normalizes_H0 c h12) ν₂ =
                      (ν₁ - ν₂) - (conjChar c.H0 (s_normalizes_H0 c h12) ν₂ - ν₂) by ring]
                  rw [inducedClassFunction_sub, hzero]
                  simp
                rw [hδ]
                exact hχ₂
              · by_cases hν₃σ : ν = conjChar c.H0 (s_normalizes_H0 c h12) ν₃
                · rw [hν₃σ]
                  have hzero : inducedClassFunction c.H0
                      (conjChar c.H0 (s_normalizes_H0 c h12) ν₃ - ν₃) = 0 :=
                    sigma_pair_star_zero_of_invariant c h12 hH0index hν₀ h_inv hν₃L
                  have hδ : inducedClassFunction c.H0
                      (ν₁ - conjChar c.H0 (s_normalizes_H0 c h12) ν₃) =
                      inducedClassFunction c.H0 (ν₁ - ν₃) := by
                    rw [show ν₁ - conjChar c.H0 (s_normalizes_H0 c h12) ν₃ =
                        (ν₁ - ν₃) - (conjChar c.H0 (s_normalizes_H0 c h12) ν₃ - ν₃) by ring]
                    rw [inducedClassFunction_sub, hzero]
                    simp
                  rw [hδ]
                  exact hχ₃
                · by_cases hfixν : conjChar c.H0 (s_normalizes_H0 c h12) ν = ν
                  · -- the fixed members: `|δν*|² = 3`, so the Fourier +
                    -- `(vi)`-value contradiction replaces the norm-two argument
                    let σν₂ : ClassFunction (↥c.H0) :=
                      conjChar c.H0 (s_normalizes_H0 c h12) ν₂
                    have hνⱼirr : IsIrreducibleCharacter ν := hνirr ν hνL
                    have hⱼ₁ : ν ∈ orbit c.H0 c.U ν₁ := by
                      rw [orbit_eq_of_mem c hν₁L]
                      exact hνL
                    have h₁ⱼ' : ν₁ ∈ orbit c.H0 c.U ν := by
                      rw [orbit_eq_of_mem c hνL]
                      exact hν₁L
                    have hσ₁ν : conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ≠ ν := by
                      intro hEq
                      apply hσνne1
                      have h := congrArg (conjChar c.H0 (s_normalizes_H0 c h12)) hEq
                      rw [conjChar_conjChar c h12 ν₁] at h
                      exact h.symm
                    have h₁ⱼ : ν₁ ≠ ν ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ≠ ν :=
                      ⟨hνne1.symm, hσ₁ν⟩
                    have h₂ⱼ : ν₂ ≠ ν ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₂ ≠ ν := by
                      constructor
                      · intro hEq
                        exact hν₂eq (hEq.symm)
                      · intro hEq
                        exact hν₂σ (hEq.symm)
                    have h₃ⱼ : ν₃ ≠ ν ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₃ ≠ ν := by
                      constructor
                      · intro hEq
                        exact hν₃eq (hEq.symm)
                      · intro hEq
                        exact hν₃σ (hEq.symm)
                    have hν₂₁ : ν₂ ∈ orbit c.H0 c.U ν₁ := by
                      rw [orbit_eq_of_mem c hν₁L]
                      exact hν₂L
                    have hν₃₁ : ν₃ ∈ orbit c.H0 c.U ν₁ := by
                      rw [orbit_eq_of_mem c hν₁L]
                      exact hν₃L
                    have hδνnorm : normSq G (inducedClassFunction c.H0 (ν₁ - ν)) = 3 := by
                      rw [delta_norm c h12 hH0index hν₁irr hνⱼirr h₁ⱼ' h₁ⱼ.1 h₁ⱼ.2]
                      rw [theta_norm c h12 hH0index hν₁irr,
                        theta_norm c h12 hH0index hνⱼirr]
                      rw [if_neg hν₁s, if_pos hfixν]
                      norm_num
                    have hδνg : IsGeneralizedCharacter
                        (inducedClassFunction c.H0 (ν₁ - ν)) := by
                      exact isGeneralizedCharacter_induced c h12 (ν₁ - ν)
                        (isGeneralizedCharacter_sub_irr hν₁irr hνⱼirr)
                    by_contra hχjne1
                    have hχjmem :
                        scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - ν)) = 1 ∨
                          scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - ν)) = 0 ∨
                          scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - ν)) = -1 := by
                      exact scalarProduct_norm_one_signed_norm_three_mem
                        hχ23irr hδνg hδνnorm
                    have hχj0 :
                        scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₁ - ν)) = 0 := by
                      rcases hχjmem with hχj1 | hχj0 | hχjm1
                      · exact False.elim (hχjne1 hχj1)
                      · exact hχj0
                      · exfalso
                        have hδ₂g : IsGeneralizedCharacter
                            (inducedClassFunction c.H0 (ν₁ - ν₂)) := by
                          exact isGeneralizedCharacter_induced c h12 (ν₁ - ν₂)
                            (isGeneralizedCharacter_sub_irr hν₁irr hν₂irr)
                        have hδ₂χ :
                            scalarProduct G (inducedClassFunction c.H0 (ν₁ - ν₂)) χ₂₃ = 1 := by
                          apply star_inj.mp
                          rw [scalarProduct_star_comm]
                          change scalarProduct G χ₂₃
                            (inducedClassFunction c.H0 (ν₁ - ν₂)) = star 1
                          simpa using hχ₂
                        have hth2norm :
                            normSq G (χ₂₃ - inducedClassFunction c.H0 (ν₁ - ν₂)) = 1 := by
                          unfold normSq
                          rw [scalarProduct_sub_left, scalarProduct_sub_right,
                            scalarProduct_sub_right]
                          change scalarProduct G χ₂₃ χ₂₃ = 1 at hχ₁
                          have hδ₂self : scalarProduct G
                              (inducedClassFunction c.H0 (ν₁ - ν₂))
                              (inducedClassFunction c.H0 (ν₁ - ν₂)) = 2 := by
                            change normSq G (inducedClassFunction c.H0 (ν₁ - ν₂)) = 2
                            exact hδ₂norm
                          rw [hχ₁, hχ₂, hδ₂χ, hδ₂self]
                          norm_num
                        have hth2g : IsGeneralizedCharacter
                            (χ₂₃ - inducedClassFunction c.H0 (ν₁ - ν₂)) := by
                          exact isGeneralizedCharacter_sub hχg hδ₂g
                        have hth2signed :
                            IsIrreducibleCharacter
                                (χ₂₃ - inducedClassFunction c.H0 (ν₁ - ν₂)) ∨
                              IsIrreducibleCharacter
                                (-(χ₂₃ - inducedClassFunction c.H0 (ν₁ - ν₂))) := by
                          rcases norm_one_signed_irreducible hth2g hth2norm with
                            ⟨η, hη, hηeq⟩
                          rcases hηeq with hηeq | hηeq
                          · left
                            simpa [hηeq] using hη
                          · right
                            simpa [hηeq] using hη
                        have hth2jmem :
                            scalarProduct G (χ₂₃ - inducedClassFunction c.H0 (ν₁ - ν₂))
                                (inducedClassFunction c.H0 (ν₁ - ν)) = 1 ∨
                              scalarProduct G (χ₂₃ - inducedClassFunction c.H0 (ν₁ - ν₂))
                                (inducedClassFunction c.H0 (ν₁ - ν)) = 0 ∨
                              scalarProduct G (χ₂₃ - inducedClassFunction c.H0 (ν₁ - ν₂))
                                (inducedClassFunction c.H0 (ν₁ - ν)) = -1 := by
                          exact scalarProduct_norm_one_signed_norm_three_mem
                            hth2signed hδνg hδνnorm
                        have hδ₂νpair :
                            scalarProduct G (inducedClassFunction c.H0 (ν₁ - ν₂))
                              (inducedClassFunction c.H0 (ν₁ - ν)) = 1 := by
                          rw [delta_pair_scalar c h12 (ν₁ := ν₂) (ν₂ := ν)
                            (μ₁ := ν₁) (μ₂ := ν₁) hν₂irr hνⱼirr h₁₂' h₁ⱼ']
                          change scalarProduct (↥c.H)
                            (inducedFromSub (h12.H0_normal_in_H).1 ν₁ -
                              inducedFromSub (h12.H0_normal_in_H).1 ν₂)
                            (inducedFromSub (h12.H0_normal_in_H).1 ν₁ -
                              inducedFromSub (h12.H0_normal_in_H).1 ν) = 1
                          have hθ₁₁ : scalarProduct (↥c.H)
                              (inducedFromSub (h12.H0_normal_in_H).1 ν₁)
                              (inducedFromSub (h12.H0_normal_in_H).1 ν₁) = 1 := by
                            change normSq (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν₁) = 1
                            rw [theta_norm c h12 hH0index hν₁irr, if_neg hν₁s]
                          have hθ₁₂ : scalarProduct (↥c.H)
                              (inducedFromSub (h12.H0_normal_in_H).1 ν₁)
                              (inducedFromSub (h12.H0_normal_in_H).1 ν₂) = 0 :=
                            theta_pair_scalar_zero c h12 hH0index hν₁irr hν₂irr
                              h₁₂.1 h₁₂.2
                          have hθ₁ⱼ : scalarProduct (↥c.H)
                              (inducedFromSub (h12.H0_normal_in_H).1 ν₁)
                              (inducedFromSub (h12.H0_normal_in_H).1 ν) = 0 :=
                            theta_pair_scalar_zero c h12 hH0index hν₁irr hνⱼirr
                              h₁ⱼ.1 h₁ⱼ.2
                          have hθ₂₁ : scalarProduct (↥c.H)
                              (inducedFromSub (h12.H0_normal_in_H).1 ν₂)
                              (inducedFromSub (h12.H0_normal_in_H).1 ν₁) = 0 :=
                            theta_pair_scalar_zero c h12 hH0index hν₂irr hν₁irr
                              h₁₂.1.symm (by
                                intro hEq
                                apply h₁₂.2
                                rw [← hEq, conjChar_conjChar c h12 ν₂])
                          have hθ₂ⱼ : scalarProduct (↥c.H)
                              (inducedFromSub (h12.H0_normal_in_H).1 ν₂)
                              (inducedFromSub (h12.H0_normal_in_H).1 ν) = 0 :=
                            theta_pair_scalar_zero c h12 hH0index hν₂irr hνⱼirr
                              h₂ⱼ.1 h₂ⱼ.2
                          simp [scalarProduct_sub_left, scalarProduct_sub_right,
                            hθ₁₁, hθ₁₂, hθ₁ⱼ, hθ₂₁, hθ₂ⱼ]
                        have hth2jneg2 :
                            scalarProduct G (χ₂₃ - inducedClassFunction c.H0 (ν₁ - ν₂))
                              (inducedClassFunction c.H0 (ν₁ - ν)) = -2 := by
                          rw [scalarProduct_sub_left, hχjm1, hδ₂νpair]
                          norm_num
                        rcases hth2jmem with h1 | h0 | hm1
                        · rw [hth2jneg2] at h1
                          norm_num at h1
                        · rw [hth2jneg2] at h0
                          norm_num at h0
                        · rw [hth2jneg2] at hm1
                          norm_num at hm1
                    have hνF : ν ∈ F := Finset.mem_filter.mpr ⟨hνL, hfixν⟩
                    rcases Finset.card_pos.mp (by
                      rw [Finset.card_erase_of_mem hνF]
                      omega : 0 < (F.erase ν).card) with ⟨ν', hν'e⟩
                    have hν'F : ν' ∈ F := (Finset.mem_erase.mp hν'e).2
                    have hν'L : ν' ∈ L := (Finset.mem_filter.mp hν'F).1
                    have hfixν' : conjChar c.H0 (s_normalizes_H0 c h12) ν' = ν' :=
                      (Finset.mem_filter.mp hν'F).2
                    have hνν' : ν ≠ ν' := (Finset.mem_erase.mp hν'e).1.symm
                    have hν'irr : IsIrreducibleCharacter ν' := hνirr ν' hν'L
                    have hσ₂L : σν₂ ∈ L := by
                      change conjChar c.H0 (s_normalizes_H0 c h12) ν₂ ∈ orbit c.H0 c.U ν₀
                      exact orbit_s_closed_of_invariant c h12 h_inv hν₂L
                    have hLν₁ : L = orbit c.H0 c.U ν₁ := (orbit_eq_of_mem c hν₁L).symm
                    have hσ₁L : conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ∈ L := by
                      change conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ∈ orbit c.H0 c.U ν₀
                      exact orbit_s_closed_of_invariant c h12 h_inv hν₁L
                    rcases exists_orbit_representatives_with_base c h12 ν₁ hν₁irr with
                      ⟨ι, hFintype, rep, hrep_irr, hrep, hrepL⟩
                    let : Fintype ι := hFintype
                    have hz := cross_orbit_zero_for_rep c h12 hH0index
                      hν₁irr hν₂irr hν₃irr hνⱼirr hν₂₁ hν₃₁ hⱼ₁
                      hν₁s hν₂s hν₃s h₁₂ h₁₃ h₁ⱼ h₂₃ h₂ⱼ h₃ⱼ
                      hLν₁ hσ₁L rep hrep_irr hrep
                      hχ23irr hχg hχ₁ hχ₂ hχ₃ hχj0 hδνnorm
                    have hz2 : ∀ ν : {ν : ClassFunction (↥c.H0) //
                        IsIrreducibleCharacter ν},
                        ν.1 ∉ L → scalarProduct G
                          (χ₂₃ - inducedClassFunction c.H0 (ν₁ - ν₂))
                          (inducedClassFunction c.H0
                            (ν.1 - rep (Classical.choose (hrep ν)))) = 0 := by
                      intro ν hnot
                      exact (hz ν hnot).1
                    have hx : (tH0 c : G) ∉ c.U := by simpa [tH0] using t_not_mem_U c
                    have hth2g : IsGeneralizedCharacter
                        (χ₂₃ - inducedClassFunction c.H0 (ν₁ - ν₂)) := by
                      exact isGeneralizedCharacter_sub hχg (isGeneralizedCharacter_induced
                        c h12 (ν₁ - ν₂) (isGeneralizedCharacter_sub_irr hν₁irr hν₂irr))
                    have hrepL' : ∀ ν : {ν : ClassFunction (↥c.H0) //
                        IsIrreducibleCharacter ν},
                        ν.1 ∈ L → rep (Classical.choose (hrep ν)) = ν₁ := by
                      intro ν h
                      exact hrepL ν (by rwa [← hLν₁])
                    have hfourier := fourier_value_eq_orbit_sum c h12 rep hrep_irr hrep
                      (χ := χ₂₃ - inducedClassFunction c.H0 (ν₁ - ν₂)) hth2g
                      (x := tH0 c) hx (L := L) ν₁ hν₁irr hν₁L hLν₁ hrepL' hz2
                    let coeff : ClassFunction (↥c.H0) → ℂ := fun μ =>
                      scalarProduct G (χ₂₃ - inducedClassFunction c.H0 (ν₁ - ν₂))
                        (inducedClassFunction c.H0 (μ - ν₁))
                    let m : ℂ := coeff ν'
                    let U : Finset (ClassFunction (↥c.H0)) :=
                      insert ν' (insert ν (insert σν₂ (insert ν₂ {ν₁})))
                    have hUL : U ⊆ L := by
                      intro μ hμ
                      rw [Finset.mem_insert] at hμ
                      rcases hμ with hμ' | hμ
                      · rw [hμ']
                        exact hν'L
                      · rw [Finset.mem_insert] at hμ
                        rcases hμ with hμ' | hμ
                        · rw [hμ']
                          exact hνL
                        · rw [Finset.mem_insert] at hμ
                          rcases hμ with hμ' | hμ
                          · rw [hμ']
                            exact hσ₂L
                          · rw [Finset.mem_insert] at hμ
                            rcases hμ with hμ' | hμ
                            · rw [hμ']
                              exact hν₂L
                            · have hEq : μ = ν₁ := Finset.mem_singleton.mp hμ
                              rw [hEq]
                              exact hν₁L
                    have hν₁σ : ν₁ ≠ σν₂ := by
                      intro hEq
                      apply hσ₁₂
                      have h := congrArg (conjChar c.H0 (s_normalizes_H0 c h12)) hEq
                      rw [conjChar_conjChar c h12 ν₂] at h
                      exact h
                    have hν₁ν' : ν₁ ≠ ν' := by
                      intro hEq
                      apply hν₁s
                      calc
                        conjChar c.H0 (s_normalizes_H0 c h12) ν₁ =
                            conjChar c.H0 (s_normalizes_H0 c h12) ν' := by rw [hEq]
                        _ = ν' := hfixν'
                        _ = ν₁ := hEq.symm
                    have hν₂ν : ν₂ ≠ ν := fun hEq => hν₂eq hEq.symm
                    have hν₂ν' : ν₂ ≠ ν' := by
                      intro hEq
                      apply hν₂s
                      calc
                        conjChar c.H0 (s_normalizes_H0 c h12) ν₂ =
                            conjChar c.H0 (s_normalizes_H0 c h12) ν' := by rw [hEq]
                        _ = ν' := hfixν'
                        _ = ν₂ := hEq.symm
                    have hσν : σν₂ ≠ ν := fun hEq => hν₂σ hEq.symm
                    have hσν' : σν₂ ≠ ν' := by
                      intro hEq
                      apply hν₂ν'
                      have h := congrArg (conjChar c.H0 (s_normalizes_H0 c h12)) hEq
                      rw [conjChar_conjChar c h12 ν₂] at h
                      rw [hfixν'] at h
                      exact h
                    have hδ₂χ :
                        scalarProduct G (inducedClassFunction c.H0 (ν₁ - ν₂)) χ₂₃ = 1 := by
                      apply star_inj.mp
                      rw [scalarProduct_star_comm]
                      change scalarProduct G χ₂₃
                        (inducedClassFunction c.H0 (ν₁ - ν₂)) = star 1
                      simpa using hχ₂
                    have hδ₂self : scalarProduct G
                        (inducedClassFunction c.H0 (ν₁ - ν₂))
                        (inducedClassFunction c.H0 (ν₁ - ν₂)) = 2 := by
                      change normSq G (inducedClassFunction c.H0 (ν₁ - ν₂)) = 2
                      exact hδ₂norm
                    have hth2norm :
                        normSq G (χ₂₃ - inducedClassFunction c.H0 (ν₁ - ν₂)) = 1 := by
                      unfold normSq
                      rw [scalarProduct_sub_left, scalarProduct_sub_right,
                        scalarProduct_sub_right]
                      change scalarProduct G χ₂₃ χ₂₃ = 1 at hχ₁
                      rw [hχ₁, hχ₂, hδ₂χ, hδ₂self]
                      norm_num
                    have hcoeff₁ : coeff ν₁ = 0 := by
                      have hzero : inducedClassFunction c.H0 (ν₁ - ν₁) = 0 := by
                        rw [show ν₁ - ν₁ = (0 : ClassFunction (↥c.H0)) by simp]
                        exact inducedClassFunction_zero c.H0
                      unfold coeff
                      rw [hzero]
                      simp [scalarProduct_zero_right]
                    have hδ₂neg : inducedClassFunction c.H0 (ν₂ - ν₁) =
                        -inducedClassFunction c.H0 (ν₁ - ν₂) := by
                      rw [show ν₂ - ν₁ = -(ν₁ - ν₂) by ring]
                      rw [inducedClassFunction_neg]
                    have hcoeff₂ : coeff ν₂ = 1 := by
                      unfold coeff
                      rw [hδ₂neg, scalarProduct_neg_right,
                        scalarProduct_sub_left, hχ₂, hδ₂self]
                      norm_num
                    have hδσ : inducedClassFunction c.H0 (σν₂ - ν₁) =
                        -inducedClassFunction c.H0 (ν₁ - ν₂) := by
                      rw [show σν₂ - ν₁ = -(ν₁ - σν₂) by ring]
                      rw [inducedClassFunction_neg]
                      congr 1
                      have hzero : inducedClassFunction c.H0 (σν₂ - ν₂) = 0 :=
                        sigma_pair_star_zero_of_invariant c h12 hH0index hν₀ h_inv hν₂L
                      rw [show ν₁ - σν₂ = (ν₁ - ν₂) - (σν₂ - ν₂) by ring]
                      rw [inducedClassFunction_sub, hzero]
                      simp
                    have hcoeffσ : coeff σν₂ = 1 := by
                      unfold coeff
                      rw [hδσ, scalarProduct_neg_right,
                        scalarProduct_sub_left, hχ₂, hδ₂self]
                      norm_num
                    have hδ₂νpair :
                        scalarProduct G (inducedClassFunction c.H0 (ν₁ - ν₂))
                          (inducedClassFunction c.H0 (ν₁ - ν)) = 1 :=
                      delta_pair_same_base_eq_one c h12 hH0index
                        hν₁irr hν₂irr hνⱼirr hν₂₁ hⱼ₁ hν₁s h₁₂ h₁ⱼ h₂ⱼ
                    have hδνneg : inducedClassFunction c.H0 (ν - ν₁) =
                        -inducedClassFunction c.H0 (ν₁ - ν) := by
                      rw [show ν - ν₁ = -(ν₁ - ν) by ring]
                      rw [inducedClassFunction_neg]
                    have hcoeffν : coeff ν = 1 := by
                      unfold coeff
                      rw [hδνneg, scalarProduct_neg_right,
                        scalarProduct_sub_left, hχj0, hδ₂νpair]
                      norm_num
                    have hcoeffν' : coeff ν' = m := rfl
                    have hcoeff0 : ∀ μ ∈ L, μ ∉ U → coeff μ = 0 := by
                      intro μ hμL hμnot
                      by_cases hμfix : conjChar c.H0 (s_normalizes_H0 c h12) μ = μ
                      · have hμF : μ ∈ F := Finset.mem_filter.mpr ⟨hμL, hμfix⟩
                        have hpair : ({ν,ν'} : Finset (ClassFunction (↥c.H0))) ⊆ F := by
                          intro ξ hξ
                          rw [Finset.mem_insert, Finset.mem_singleton] at hξ
                          rcases hξ with hξ | hξ
                          · simpa [hξ] using hνF
                          · simpa [hξ] using hν'F
                        have hcardpair : ({ν,ν'} : Finset (ClassFunction (↥c.H0))).card = 2 := by
                          simp [hνν']
                        have hFeq : F = ({ν,ν'} : Finset (ClassFunction (↥c.H0))) :=
                          (Finset.eq_of_subset_of_card_le hpair (by rw [hFcard, hcardpair])).symm
                        have hμpair : μ ∈ ({ν,ν'} : Finset (ClassFunction (↥c.H0))) := by
                          rwa [← hFeq]
                        rw [Finset.mem_insert, Finset.mem_singleton] at hμpair
                        rcases hμpair with hμν | hμν'
                        · exact False.elim (hμnot (by
                            rw [Finset.mem_insert]
                            right
                            rw [Finset.mem_insert]
                            exact Or.inl hμν))
                        · exact False.elim (hμnot (by
                            rw [Finset.mem_insert]
                            exact Or.inl hμν'))
                      · by_cases hμ₁eq : μ = ν₁
                        · rw [hμ₁eq]
                          have hzero : inducedClassFunction c.H0 (ν₁ - ν₁) = 0 := by
                            rw [show ν₁ - ν₁ = (0 : ClassFunction (↥c.H0)) by simp]
                            exact inducedClassFunction_zero c.H0
                          unfold coeff
                          rw [hzero]
                          simp [scalarProduct_zero_right]
                        · by_cases hμσ₁eq : μ = conjChar c.H0 (s_normalizes_H0 c h12) ν₁
                          · rw [hμσ₁eq]
                            have hzero : inducedClassFunction c.H0
                                (conjChar c.H0 (s_normalizes_H0 c h12) ν₁ - ν₁) = 0 :=
                              sigma_pair_star_zero_of_invariant c h12 hH0index hν₀ h_inv hν₁L
                            unfold coeff
                            rw [hzero]
                            simp [scalarProduct_zero_right]
                          · by_cases hμ₃eq : μ = ν₃
                            · rw [hμ₃eq]
                              have hδ₃neg : inducedClassFunction c.H0 (ν₃ - ν₁) =
                                  -inducedClassFunction c.H0 (ν₁ - ν₃) := by
                                rw [show ν₃ - ν₁ = -(ν₁ - ν₃) by ring]
                                rw [inducedClassFunction_neg]
                              unfold coeff
                              rw [hδ₃neg, scalarProduct_neg_right,
                                scalarProduct_sub_left, hχ₃, hδ₂₃pair]
                              norm_num
                            · by_cases hμσ₃eq : μ = conjChar c.H0 (s_normalizes_H0 c h12) ν₃
                              · rw [hμσ₃eq]
                                have hδσ₃ : inducedClassFunction c.H0
                                    (conjChar c.H0 (s_normalizes_H0 c h12) ν₃ - ν₁) =
                                    -inducedClassFunction c.H0 (ν₁ - ν₃) := by
                                  rw [show conjChar c.H0 (s_normalizes_H0 c h12) ν₃ - ν₁ =
                                      -(ν₁ - conjChar c.H0 (s_normalizes_H0 c h12) ν₃) by ring]
                                  rw [inducedClassFunction_neg]
                                  congr 1
                                  have hzero : inducedClassFunction c.H0
                                      (conjChar c.H0 (s_normalizes_H0 c h12) ν₃ - ν₃) = 0 :=
                                    sigma_pair_star_zero_of_invariant c h12 hH0index
                                      hν₀ h_inv hν₃L
                                  rw [show ν₁ - conjChar c.H0 (s_normalizes_H0 c h12) ν₃ =
                                      (ν₁ - ν₃) -
                                        (conjChar c.H0 (s_normalizes_H0 c h12) ν₃ - ν₃) by ring]
                                  rw [inducedClassFunction_sub, hzero]
                                  simp
                                unfold coeff
                                rw [hδσ₃, scalarProduct_neg_right,
                                  scalarProduct_sub_left, hχ₃, hδ₂₃pair]
                                norm_num
                              · have hμirr : IsIrreducibleCharacter μ := hνirr μ hμL
                                have hμs : conjChar c.H0 (s_normalizes_H0 c h12) μ ≠ μ := hμfix
                                have hμ₁ : μ ∈ orbit c.H0 c.U ν₁ := by
                                  rw [orbit_eq_of_mem c hν₁L]
                                  exact hμL
                                have h₁μ' : ν₁ ∈ orbit c.H0 c.U μ := by
                                  rw [orbit_eq_of_mem c hμL]
                                  exact hν₁L
                                have hσ₁μ : conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ≠ μ := by
                                  intro hEq
                                  exact hμσ₁eq hEq.symm
                                have h₁μ : ν₁ ≠ μ ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ≠ μ :=
                                  ⟨fun hEq => hμ₁eq hEq.symm, hσ₁μ⟩
                                have hν₂U : ν₂ ∈ U := by
                                  change ν₂ ∈ insert ν' (insert ν (insert σν₂ (insert ν₂ {ν₁})))
                                  rw [Finset.mem_insert]
                                  right
                                  rw [Finset.mem_insert]
                                  right
                                  rw [Finset.mem_insert]
                                  right
                                  rw [Finset.mem_insert]
                                  left
                                  rfl
                                have hσ₂U : σν₂ ∈ U := by
                                  change conjChar c.H0 (s_normalizes_H0 c h12) ν₂ ∈
                                    insert ν' (insert ν (insert σν₂ (insert ν₂ {ν₁})))
                                  rw [Finset.mem_insert]
                                  right
                                  rw [Finset.mem_insert]
                                  right
                                  rw [Finset.mem_insert]
                                  left
                                  rfl
                                have h₂μ : ν₂ ≠ μ ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₂ ≠ μ := by
                                  constructor
                                  · intro hEq
                                    exact hμnot (by rwa [hEq] at hν₂U)
                                  · intro hEq
                                    exact hμnot (by simpa [σν₂, hEq] using hσ₂U)
                                have h₃μ : ν₃ ≠ μ ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₃ ≠ μ := by
                                  constructor
                                  · intro hEq
                                    exact hμ₃eq hEq.symm
                                  · intro hEq
                                    exact hμσ₃eq hEq.symm
                                have hδμnorm : normSq G (inducedClassFunction c.H0 (ν₁ - μ)) = 2 := by
                                  rw [delta_norm c h12 hH0index hν₁irr hμirr h₁μ' h₁μ.1 h₁μ.2]
                                  rw [theta_norm c h12 hH0index hν₁irr,
                                    theta_norm c h12 hH0index hμirr]
                                  rw [if_neg hν₁s, if_neg hμs]
                                  norm_num
                                have hχμ := pairing_eq_one_of_norm_two c h12 hH0index
                                  hν₁irr hν₂irr hν₃irr hμirr hν₂₁ hν₃₁ hμ₁
                                  hν₁s hν₂s hν₃s hμs h₁₂ h₁₃ h₁μ h₂₃ h₂μ h₃μ
                                  hχ23irr hχg hχ₁ hχ₂ hχ₃ hδμnorm
                                have hδ₂μpair :
                                    scalarProduct G (inducedClassFunction c.H0 (ν₁ - ν₂))
                                      (inducedClassFunction c.H0 (ν₁ - μ)) = 1 := by
                                  rw [delta_pair_scalar c h12 (ν₁ := ν₂) (ν₂ := μ)
                                    (μ₁ := ν₁) (μ₂ := ν₁) hν₂irr hμirr h₁₂' h₁μ']
                                  change scalarProduct (↥c.H)
                                    (inducedFromSub (h12.H0_normal_in_H).1 ν₁ -
                                      inducedFromSub (h12.H0_normal_in_H).1 ν₂)
                                    (inducedFromSub (h12.H0_normal_in_H).1 ν₁ -
                                      inducedFromSub (h12.H0_normal_in_H).1 μ) = 1
                                  have hθ₁₁ : scalarProduct (↥c.H)
                                      (inducedFromSub (h12.H0_normal_in_H).1 ν₁)
                                      (inducedFromSub (h12.H0_normal_in_H).1 ν₁) = 1 := by
                                    change normSq (↥c.H)
                                      (inducedFromSub (h12.H0_normal_in_H).1 ν₁) = 1
                                    rw [theta_norm c h12 hH0index hν₁irr, if_neg hν₁s]
                                  have hθ₁₂ : scalarProduct (↥c.H)
                                      (inducedFromSub (h12.H0_normal_in_H).1 ν₁)
                                      (inducedFromSub (h12.H0_normal_in_H).1 ν₂) = 0 :=
                                    theta_pair_scalar_zero c h12 hH0index hν₁irr hν₂irr
                                      h₁₂.1 h₁₂.2
                                  have hθ₁μ : scalarProduct (↥c.H)
                                      (inducedFromSub (h12.H0_normal_in_H).1 ν₁)
                                      (inducedFromSub (h12.H0_normal_in_H).1 μ) = 0 :=
                                    theta_pair_scalar_zero c h12 hH0index hν₁irr hμirr
                                      h₁μ.1 h₁μ.2
                                  have hθ₂₁ : scalarProduct (↥c.H)
                                      (inducedFromSub (h12.H0_normal_in_H).1 ν₂)
                                      (inducedFromSub (h12.H0_normal_in_H).1 ν₁) = 0 :=
                                    theta_pair_scalar_zero c h12 hH0index hν₂irr hν₁irr
                                      h₁₂.1.symm (by
                                        intro hEq
                                        apply h₁₂.2
                                        rw [← hEq, conjChar_conjChar c h12 ν₂])
                                  have hθ₂μ : scalarProduct (↥c.H)
                                      (inducedFromSub (h12.H0_normal_in_H).1 ν₂)
                                      (inducedFromSub (h12.H0_normal_in_H).1 μ) = 0 :=
                                    theta_pair_scalar_zero c h12 hH0index hν₂irr hμirr
                                      h₂μ.1 h₂μ.2
                                  simp [scalarProduct_sub_left, scalarProduct_sub_right,
                                    hθ₁₁, hθ₁₂, hθ₁μ, hθ₂₁, hθ₂μ]
                                have hδμneg : inducedClassFunction c.H0 (μ - ν₁) =
                                    -inducedClassFunction c.H0 (ν₁ - μ) := by
                                  rw [show μ - ν₁ = -(ν₁ - μ) by ring]
                                  rw [inducedClassFunction_neg]
                                unfold coeff
                                rw [hδμneg, scalarProduct_neg_right,
                                  scalarProduct_sub_left, hχμ, hδ₂μpair]
                                norm_num
                    have hsum : (∑ μ ∈ L, coeff μ * μ (tH0 c)) =
                        ν₂ (tH0 c) + σν₂ (tH0 c) + ν (tH0 c) + m * ν' (tH0 c) := by
                      exact orbit_sum_coeff_theta_tilde_two c (L := L) (U := U)
                        ν₁ ν₂ σν₂ ν ν' m
                        hν₁L hν₂L hσ₂L hνL hν'L hUL rfl
                        h₁₂.1 hν₁σ hνne1.symm hν₁ν' hν₂s.symm hν₂ν hν₂ν'
                        hσν hσν' hνν'
                        coeff hcoeff₁ hcoeff₂ hcoeffσ hcoeffν hcoeffν' hcoeff0 (tH0 c)
                    have hfourier' : (χ₂₃ - inducedClassFunction c.H0 (ν₁ - ν₂))
                        (tH0 c : G) =
                        ν₂ (tH0 c) + σν₂ (tH0 c) + ν (tH0 c) + m * ν' (tH0 c) := by
                      rw [hfourier, hsum]
                    have hnot : ¬ ((orbit c.H0 c.U ν₂).card = 4 ∧
                        conjChar c.H0 (s_normalizes_H0 c h12) ν₂ ∈ orbit c.H0 c.U ν₂) := by
                      intro h
                      rcases h with ⟨hcard, _⟩
                      have horbit : orbit c.H0 c.U ν₂ = L := orbit_eq_of_mem c hν₂L
                      rw [horbit] at hcard
                      omega
                    rcases exists_mu_sign_choice c h12 hν₂irr hν₂s hnot with
                      ⟨μ, hμL, hμs, hμt⟩
                    have hμirr : IsIrreducibleCharacter μ :=
                      orbit_mem_isIrreducible c.H0 c.U hν₂irr hμL
                    have hμL' : μ ∈ L := by
                      rw [orbit_eq_of_mem c hν₂L] at hμL
                      exact hμL
                    have hμ₁ : μ ∈ orbit c.H0 c.U ν₁ := by
                      rw [orbit_eq_of_mem c hν₁L]
                      exact hμL'
                    have hpairdata := theta_tilde_two_pair_data c h12 hH0index
                      hν₀ hν₁irr hν₂irr hν₃irr hμirr
                      h_inv hν₁L hν₂L hν₃L hμL'
                      hν₁s hν₂s hν₃s hμs
                      hν₂₁ hν₃₁ hμ₁ h₁₂ h₁₃ h₂₃
                      hχ23irr hχg hχ₁ hχ₂ hχ₃
                    rcases hpairdata with
                      ⟨thetaTilde, hgenν, hgenμ, hnormν, hnormμ, hδeq, honT, hliftν⟩
                    have hth2t : (χ₂₃ - inducedClassFunction c.H0 (ν₁ - ν₂))
                        (tH0 c : G) = 2 * ν₂ (tH0 c) := by
                      have hres := theta_tilde_two_eval_pair c h12 hH0index
                        hν₂irr hν₂s hμirr hμL hμs hμt
                        thetaTilde hgenμ hgenν hnormμ hnormν hδeq honT
                      have hT : thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 ν₂) =
                          χ₂₃ - inducedClassFunction c.H0 (ν₁ - ν₂) := hliftν
                      simpa [hT, tH0] using hres
                    have hσt : σν₂ (tH0 c) = ν₂ (tH0 c) :=
                      conjChar_apply_tH0_eq c h12 ν₂
                    have hlin : ν (tH0 c) + m * ν' (tH0 c) = 0 := by
                      rw [hth2t, hσt] at hfourier'
                      ring_nf at hfourier'
                      linear_combination -hfourier'
                    have hν'₁ : ν' ∈ orbit c.H0 c.U ν₁ := by
                      rw [orbit_eq_of_mem c hν₁L]
                      exact hν'L
                    have h₁ν'' : ν₁ ∈ orbit c.H0 c.U ν' := by
                      rw [orbit_eq_of_mem c hν'L]
                      exact hν₁L
                    have hσ₁ν' : conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ≠ ν' := by
                      intro hEq
                      apply hν₁ν'
                      have h := congrArg (conjChar c.H0 (s_normalizes_H0 c h12)) hEq
                      rw [conjChar_conjChar c h12 ν₁] at h
                      rw [hfixν'] at h
                      exact h
                    have h₁ν' : ν₁ ≠ ν' ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ≠ ν' :=
                      ⟨hν₁ν', hσ₁ν'⟩
                    have h₂ν' : ν₂ ≠ ν' ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₂ ≠ ν' :=
                      ⟨hν₂ν', hσν'⟩
                    have hν₃ν' : ν₃ ≠ ν' := by
                      intro hEq
                      apply hν₃s
                      rw [hEq, hfixν']
                    have hσν₃ν' : conjChar c.H0 (s_normalizes_H0 c h12) ν₃ ≠ ν' := by
                      intro hEq
                      apply hν₃ν'
                      have h := congrArg (conjChar c.H0 (s_normalizes_H0 c h12)) hEq
                      rw [conjChar_conjChar c h12 ν₃] at h
                      rw [hfixν'] at h
                      exact h
                    have h₃ν' : ν₃ ≠ ν' ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₃ ≠ ν' :=
                      ⟨hν₃ν', hσν₃ν'⟩
                    have hδν'norm : normSq G (inducedClassFunction c.H0 (ν₁ - ν')) = 3 := by
                      rw [delta_norm c h12 hH0index hν₁irr hν'irr h₁ν'' h₁ν'.1 h₁ν'.2]
                      rw [theta_norm c h12 hH0index hν₁irr,
                        theta_norm c h12 hH0index hν'irr]
                      rw [if_neg hν₁s, if_pos hfixν']
                      norm_num
                    have hδ₂ν'pair :
                        scalarProduct G (inducedClassFunction c.H0 (ν₁ - ν₂))
                          (inducedClassFunction c.H0 (ν₁ - ν')) = 1 :=
                      delta_pair_same_base_eq_one c h12 hH0index
                        hν₁irr hν₂irr hν'irr hν₂₁ hν'₁ hν₁s h₁₂ h₁ν' h₂ν'
                    rcases fixed_member_pairing_eq_zero_or_one c h12 hH0index
                      hν₁irr hν₂irr hν₃irr hν'irr hν₂₁ hν₃₁ hν'₁
                      hν₁s hν₂s hν₃s hfixν'
                      h₁ν' h₂ν' h₃ν' h₁₂ h₁₃ h₂₃
                      hχ23irr hχg hχ₁ hχ₂ hχ₃ hδν'norm with hχ0ν' | hχ1ν'
                    · -- `(χ₂₃, δν'*) = 0`: both `s`-fixed members are undefined,
                      -- contradicting the degree identities
                      exfalso
                      exact two_bad_fixed_contradiction c h12 hH0index
                        hν₁irr hν₂irr hν₃irr hνⱼirr hν'irr
                        hν₂₁ hν₃₁ hⱼ₁ hν'₁
                        hν₁s hν₂s hν₃s
                        hfixν hfixν'
                        hνν'
                        h₁ⱼ h₂ⱼ h₃ⱼ
                        h₁ν' h₂ν' h₃ν'
                        h₁₂ h₁₃ h₂₃
                        hχ23irr hχg hχ₁ hχ₂ hχ₃
                        hδ₂norm hδ₃norm hδ₂₃pair
                        hχj0 hχ0ν'
                        hδνnorm hδν'norm
                    · -- `(χ₂₃, δν'*) = 1`: the coefficient of `ν'` is `0`, so
                      -- the Fourier formula forces `ν(t) = 0`, contradicting
                      -- the nonzero value of the irreducible `ν` at `t`
                      have hm0 : m = 0 := by
                        have hδν'neg : inducedClassFunction c.H0 (ν' - ν₁) =
                            -inducedClassFunction c.H0 (ν₁ - ν') := by
                          rw [show ν' - ν₁ = -(ν₁ - ν') by ring]
                          rw [inducedClassFunction_neg]
                        have hcoeffν'' : coeff ν' = 0 := by
                          unfold coeff
                          rw [hδν'neg, scalarProduct_neg_right, scalarProduct_sub_left,
                            hχ1ν', hδ₂ν'pair]
                          norm_num
                        simpa [m] using hcoeffν''
                      exfalso
                      have hνt0 : ν (tH0 c) = 0 := by
                        have hlin0 : ν (tH0 c) + 0 * ν' (tH0 c) = 0 := by
                          simpa [hm0] using hlin
                        simpa using hlin0
                      exact (char_apply_central_ne_zero
                        (G := ↥c.H0) (t := tH0 c)
                        (by simpa [tH0] using t_central_H0' c)
                        (by simpa [tH0] using t_H0_sq c) hνⱼirr) hνt0
                  · have hνⱼirr : IsIrreducibleCharacter ν := hνirr ν hνL
                    have hνⱼs : conjChar c.H0 (s_normalizes_H0 c h12) ν ≠ ν := hfixν
                    have hⱼ₁ : ν ∈ orbit c.H0 c.U ν₁ := by
                      rw [orbit_eq_of_mem c hν₁L]
                      exact hνL
                    have hσ₁ν : conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ≠ ν := by
                      intro hEq
                      apply hσνne1
                      have h := congrArg (conjChar c.H0 (s_normalizes_H0 c h12)) hEq
                      rw [conjChar_conjChar c h12 ν₁] at h
                      exact h.symm
                    have h₁ⱼ : ν₁ ≠ ν ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ≠ ν :=
                      ⟨hνne1.symm, hσ₁ν⟩
                    have h₂ⱼ : ν₂ ≠ ν ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₂ ≠ ν := by
                      constructor
                      · intro hEq
                        exact hν₂eq (hEq.symm)
                      · intro hEq
                        exact hν₂σ (hEq.symm)
                    have h₃ⱼ : ν₃ ≠ ν ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₃ ≠ ν := by
                      constructor
                      · intro hEq
                        exact hν₃eq (hEq.symm)
                      · intro hEq
                        exact hν₃σ (hEq.symm)
                    have h₁ⱼ' : ν₁ ∈ orbit c.H0 c.U ν := by
                      rw [orbit_eq_of_mem c hνL]
                      exact hν₁L
                    have hν₂₁ : ν₂ ∈ orbit c.H0 c.U ν₁ := by
                      rw [orbit_eq_of_mem c hν₁L]
                      exact hν₂L
                    have hν₃₁ : ν₃ ∈ orbit c.H0 c.U ν₁ := by
                      rw [orbit_eq_of_mem c hν₁L]
                      exact hν₃L
                    have hδνnorm : normSq G (inducedClassFunction c.H0 (ν₁ - ν)) = 2 := by
                      rw [delta_norm c h12 hH0index hν₁irr hνⱼirr h₁ⱼ' h₁ⱼ.1 h₁ⱼ.2]
                      rw [theta_norm c h12 hH0index hν₁irr, theta_norm c h12 hH0index hνⱼirr]
                      rw [if_neg hν₁s, if_neg hνⱼs]
                      norm_num
                    exact pairing_eq_one_of_norm_two c h12 hH0index
                      hν₁irr hν₂irr hν₃irr hνⱼirr hν₂₁ hν₃₁ hⱼ₁
                      hν₁s hν₂s hν₃s hνⱼs h₁₂ h₁₃ h₁ⱼ h₂₃ h₂ⱼ h₃ⱼ
                      hχ23irr hχg hχ₁ hχ₂ hχ₃ hδνnorm
        exact exists_theta_lift_invariant c h12 hH0index ν₀ ν₁ hν₀ hν₁irr hν₁L h_inv hν₁s
          hχg hχ₁ hχall
  · -- the non-`s`-invariant orbit: no `s`-fixed member (`θ` injective on `L`)
    have hνsall : ∀ ν ∈ L, conjChar c.H0 (s_normalizes_H0 c h12) ν ≠ ν := by
      intro ν hνL hσν
      apply h_inv
      exact s_fixed_mem_imp_invariant c h12 hνL hσν
    by_cases hL : 3 ≤ L.card
    · -- `n ≥ 3`: pick `ν₂, ν₃`, extract the common constituent `χ₂₃` of
      -- `δ₂* = (ν₀−ν₂)*` and `δ₃* = (ν₀−ν₃)*`, and dispatch on the defined
      -- `(χ₂₃, δᵢ*) = 1` case
      have hL2 : 2 ≤ (L.erase ν₀).card := by
        rw [Finset.card_erase_of_mem hν₀L]
        omega
      rcases Finset.card_pos.mp (by omega : 0 < (L.erase ν₀).card) with ⟨ν₂, hν₂e⟩
      have hν₂ne : ν₂ ≠ ν₀ := (Finset.mem_erase.mp hν₂e).1
      have hν₂L : ν₂ ∈ L := (Finset.mem_erase.mp hν₂e).2
      have hL1 : 1 ≤ ((L.erase ν₀).erase ν₂).card := by
        rw [Finset.card_erase_of_mem hν₂e, Finset.card_erase_of_mem hν₀L]
        omega
      rcases Finset.card_pos.mp (by omega : 0 < ((L.erase ν₀).erase ν₂).card) with
        ⟨ν₃, hν₃e⟩
      have hν₃e' : ν₃ ∈ L.erase ν₀ := (Finset.mem_erase.mp hν₃e).2
      have hν₃ne : ν₃ ≠ ν₀ := (Finset.mem_erase.mp hν₃e').1
      have hν₃L : ν₃ ∈ L := (Finset.mem_erase.mp hν₃e').2
      -- the `s`-conditions of the picked members
      have hν₁s : conjChar c.H0 (s_normalizes_H0 c h12) ν₀ ≠ ν₀ := hνsall ν₀ hν₀L
      have hν₂s : conjChar c.H0 (s_normalizes_H0 c h12) ν₂ ≠ ν₂ := hνsall ν₂ hν₂L
      have hν₃s : conjChar c.H0 (s_normalizes_H0 c h12) ν₃ ≠ ν₃ := hνsall ν₃ hν₃L
      have hσ₀₂ : conjChar c.H0 (s_normalizes_H0 c h12) ν₀ ≠ ν₂ := by
        intro hEq
        apply h_inv
        rwa [hEq]
      have hσ₀₃ : conjChar c.H0 (s_normalizes_H0 c h12) ν₀ ≠ ν₃ := by
        intro hEq
        apply h_inv
        rwa [hEq]
      have hσ₂₀ : conjChar c.H0 (s_normalizes_H0 c h12) ν₂ ≠ ν₀ := by
        intro hEq
        apply sigma_image_not_mem_of_not_invariant c h12 h_inv hν₂L
        rwa [hEq]
      have hσ₂₃ : conjChar c.H0 (s_normalizes_H0 c h12) ν₂ ≠ ν₃ := by
        intro hEq
        apply sigma_image_not_mem_of_not_invariant c h12 h_inv hν₂L
        rwa [hEq]
      have h₁₂ : ν₀ ≠ ν₂ ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₀ ≠ ν₂ :=
        ⟨hν₂ne.symm, hσ₀₂⟩
      have h₁₃ : ν₀ ≠ ν₃ ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₀ ≠ ν₃ :=
        ⟨hν₃ne.symm, hσ₀₃⟩
      have h₂₃ : ν₂ ≠ ν₃ ∧ conjChar c.H0 (s_normalizes_H0 c h12) ν₂ ≠ ν₃ :=
        ⟨(Finset.mem_erase.mp hν₃e).1.symm, hσ₂₃⟩
      -- `δ₂*` and `δ₃*` are generalized characters of norm `2` with pairing `1`
      have hδ₂g : IsGeneralizedCharacter (inducedClassFunction c.H0 (ν₀ - ν₂)) := by
        exact isGeneralizedCharacter_induced c h12 (ν₀ - ν₂)
          (isGeneralizedCharacter_sub_irr hν₀ (hνirr ν₂ hν₂L))
      have hδ₃g : IsGeneralizedCharacter (inducedClassFunction c.H0 (ν₀ - ν₃)) := by
        exact isGeneralizedCharacter_induced c h12 (ν₀ - ν₃)
          (isGeneralizedCharacter_sub_irr hν₀ (hνirr ν₃ hν₃L))
      have h₀₂ : ν₀ ∈ orbit c.H0 c.U ν₂ := by
        rw [orbit_eq_of_mem c hν₂L]
        exact hν₀L
      have h₀₃ : ν₀ ∈ orbit c.H0 c.U ν₃ := by
        rw [orbit_eq_of_mem c hν₃L]
        exact hν₀L
      have hδ₂norm : normSq G (inducedClassFunction c.H0 (ν₀ - ν₂)) = 2 := by
        rw [delta_norm c h12 hH0index hν₀ (hνirr ν₂ hν₂L) h₀₂ hν₂ne.symm hσ₀₂]
        rw [theta_norm c h12 hH0index hν₀, theta_norm c h12 hH0index (hνirr ν₂ hν₂L)]
        rw [if_neg hν₁s, if_neg hν₂s]
        norm_num
      have hδ₃norm : normSq G (inducedClassFunction c.H0 (ν₀ - ν₃)) = 2 := by
        rw [delta_norm c h12 hH0index hν₀ (hνirr ν₃ hν₃L) h₀₃ hν₃ne.symm hσ₀₃]
        rw [theta_norm c h12 hH0index hν₀, theta_norm c h12 hH0index (hνirr ν₃ hν₃L)]
        rw [if_neg hν₁s, if_neg hν₃s]
        norm_num
      have hδ₂₃pair : scalarProduct G (inducedClassFunction c.H0 (ν₀ - ν₂))
          (inducedClassFunction c.H0 (ν₀ - ν₃)) = 1 := by
        have hsp := delta_pair_scalar c h12 (ν₁ := ν₀) (ν₂ := ν₀) (μ₁ := ν₂) (μ₂ := ν₃)
          hν₀ hν₀ hν₂L hν₃L
        rw [show inducedClassFunction c.H0 (ν₀ - ν₂) = -inducedClassFunction c.H0 (ν₂ - ν₀) by
              rw [show ν₀ - ν₂ = -(ν₂ - ν₀) by ring]
              rw [inducedClassFunction_neg]]
        rw [show inducedClassFunction c.H0 (ν₀ - ν₃) = -inducedClassFunction c.H0 (ν₃ - ν₀) by
              rw [show ν₀ - ν₃ = -(ν₃ - ν₀) by ring]
              rw [inducedClassFunction_neg]]
        rw [scalarProduct_neg_left, scalarProduct_neg_right, hsp]
        simp
        rw [scalarProduct_sub_left, scalarProduct_sub_right, scalarProduct_sub_right]
        have hθ₀₀ : scalarProduct (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν₀)
            (inducedFromSub (h12.H0_normal_in_H).1 ν₀) = 1 := by
          change normSq (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν₀) = 1
          rw [theta_norm c h12 hH0index hν₀]
          rw [if_neg hν₁s]
        have hθ₀₂ : scalarProduct (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν₀)
            (inducedFromSub (h12.H0_normal_in_H).1 ν₂) = 0 := by
          exact theta_pair_scalar_zero c h12 hH0index hν₀ (hνirr ν₂ hν₂L) hν₂ne.symm hσ₀₂
        have hθ₂₀ : scalarProduct (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν₂)
            (inducedFromSub (h12.H0_normal_in_H).1 ν₀) = 0 := by
          exact theta_pair_scalar_zero c h12 hH0index (hνirr ν₂ hν₂L) hν₀ hν₂ne hσ₂₀
        have hθ₀₃ : scalarProduct (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν₀)
            (inducedFromSub (h12.H0_normal_in_H).1 ν₃) = 0 := by
          exact theta_pair_scalar_zero c h12 hH0index hν₀ (hνirr ν₃ hν₃L) hν₃ne.symm hσ₀₃
        have hθ₂₃ : scalarProduct (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν₂)
            (inducedFromSub (h12.H0_normal_in_H).1 ν₃) = 0 := by
          exact theta_pair_scalar_zero c h12 hH0index (hνirr ν₂ hν₂L) (hνirr ν₃ hν₃L)
            h₂₃.1 h₂₃.2
        rw [hθ₂₃, hθ₂₀, hθ₀₃, hθ₀₀]
        norm_num
      -- the common constituent `χ₂₃` of `δ₂*` and `δ₃*`
      rcases exists_common_constituent_self c h12 hδ₂g hδ₃g hδ₂norm hδ₃norm hδ₂₃pair with
        ⟨χ₂₃, hχ23irr, hχ₂, hχ₃⟩
      have hχg : IsGeneralizedCharacter χ₂₃ := by
        rcases hχ23irr with hχ | hχ
        · exact isGeneralizedCharacter_of_isCharacter (isCharacter_of_isIrreducibleCharacter hχ)
        · simpa using isGeneralizedCharacter_of_signed_irreducible hχ
      have hχ₁ : normSq G χ₂₃ = 1 := by
        rcases hχ23irr with hχ | hχ
        · change scalarProduct G χ₂₃ χ₂₃ = 1
          exact irreducible_scalarProduct_self hχ
        · change scalarProduct G χ₂₃ χ₂₃ = 1
          simpa [scalarProduct_neg_left, scalarProduct_neg_right] using
            irreducible_scalarProduct_self hχ
      by_cases hχall : ∀ ν ∈ orbit c.H0 c.U ν₀, ν ≠ ν₀ →
          scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₀ - ν)) = 1
      · -- the defined case: `θ̃ᵢ := χ₂₃ − δᵢ*` for every member
        exact exists_theta_lift c h12 hH0index ν₀ ν₀ ν₂ ν₃ hν₀ hν₀
          (hνirr ν₂ hν₂L) (hνirr ν₃ hν₃L) hν₀L hν₂L hν₃L h_inv hν₁s hν₂s hν₃s
          h₁₂ h₁₃ h₂₃ hχg hχ₁ hχ₂ hχ₃ hχall
      · -- the undefined case: some `νⱼ` with `(χ₂₃, δⱼ*) ≠ 1` — the paper's
        -- `δⱼ* = φ − θ̃₂ − θ̃₃` route.  In a non-invariant orbit every
        -- induced value has norm one, so Fact 4's corrected `normSq = 3`
        -- conclusion is immediately contradictory.
        rcases (not_forall.mp hχall) with ⟨νⱼ, hνjimp⟩
        simp at hνjimp
        rcases hνjimp with ⟨hνjL, hνjne0, hχjne1⟩
        have hνⱼirr : IsIrreducibleCharacter νⱼ := hνirr νⱼ hνjL
        have hνⱼs : conjChar c.H0 (s_normalizes_H0 c h12) νⱼ ≠ νⱼ :=
          hνsall νⱼ hνjL
        have h₀ⱼ : ν₀ ∈ orbit c.H0 c.U νⱼ := by
          rw [orbit_eq_of_mem c hνjL]
          exact hν₀L
        have hσ₀ⱼ : conjChar c.H0 (s_normalizes_H0 c h12) ν₀ ≠ νⱼ := by
          intro hEq
          apply h_inv
          rwa [hEq]
        have hδⱼg : IsGeneralizedCharacter
            (inducedClassFunction c.H0 (ν₀ - νⱼ)) := by
          exact isGeneralizedCharacter_induced c h12 (ν₀ - νⱼ)
            (isGeneralizedCharacter_sub_irr hν₀ hνⱼirr)
        have hν₀ⱼne : ν₀ ≠ νⱼ := fun h => hνjne0 h.symm
        have hδⱼnorm : normSq G (inducedClassFunction c.H0 (ν₀ - νⱼ)) = 2 := by
          rw [delta_norm c h12 hH0index hν₀ hνⱼirr h₀ⱼ hν₀ⱼne hσ₀ⱼ]
          rw [theta_norm c h12 hH0index hν₀,
            theta_norm c h12 hH0index hνⱼirr]
          rw [if_neg hν₁s, if_neg hνⱼs]
          norm_num
        have hχjmem :
            scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₀ - νⱼ)) = 1 ∨
              scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₀ - νⱼ)) = 0 ∨
              scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₀ - νⱼ)) = -1 := by
          exact scalarProduct_norm_one_signed_norm_two_mem hχ23irr hδⱼg hδⱼnorm
        have hδ₂ⱼpair :
            scalarProduct G (inducedClassFunction c.H0 (ν₀ - ν₂))
              (inducedClassFunction c.H0 (ν₀ - νⱼ)) = 1 := by
          rw [delta_pair_scalar c h12 (ν₁ := ν₂) (ν₂ := νⱼ) (μ₁ := ν₀)
            (μ₂ := ν₀) (hνirr ν₂ hν₂L) hνⱼirr h₀₂ h₀ⱼ]
          change scalarProduct (↥c.H)
            (inducedFromSub (h12.H0_normal_in_H).1 ν₀ -
              inducedFromSub (h12.H0_normal_in_H).1 ν₂)
            (inducedFromSub (h12.H0_normal_in_H).1 ν₀ -
              inducedFromSub (h12.H0_normal_in_H).1 νⱼ) = 1
          have hθ₀₀ : scalarProduct (↥c.H)
              (inducedFromSub (h12.H0_normal_in_H).1 ν₀)
              (inducedFromSub (h12.H0_normal_in_H).1 ν₀) = 1 := by
            change normSq (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν₀) = 1
            rw [theta_norm c h12 hH0index hν₀, if_neg hν₁s]
          have hθ₀₂ : scalarProduct (↥c.H)
              (inducedFromSub (h12.H0_normal_in_H).1 ν₀)
              (inducedFromSub (h12.H0_normal_in_H).1 ν₂) = 0 :=
            theta_pair_scalar_zero c h12 hH0index hν₀ (hνirr ν₂ hν₂L)
              (Ne.symm hν₂ne) hσ₀₂
          have hθ₀ⱼ : scalarProduct (↥c.H)
              (inducedFromSub (h12.H0_normal_in_H).1 ν₀)
              (inducedFromSub (h12.H0_normal_in_H).1 νⱼ) = 0 :=
            theta_pair_scalar_zero c h12 hH0index hν₀ hνⱼirr hν₀ⱼne hσ₀ⱼ
          have hν₂ⱼne : ν₂ ≠ νⱼ := by
            intro hEq
            apply hχjne1
            rw [← hEq]
            exact hχ₂
          have hσ₂ⱼ : conjChar c.H0 (s_normalizes_H0 c h12) ν₂ ≠ νⱼ := by
            intro hEq
            apply sigma_image_not_mem_of_not_invariant c h12 h_inv hν₂L
            rwa [hEq]
          have hθ₂₀ : scalarProduct (↥c.H)
              (inducedFromSub (h12.H0_normal_in_H).1 ν₂)
              (inducedFromSub (h12.H0_normal_in_H).1 ν₀) = 0 :=
            theta_pair_scalar_zero c h12 hH0index (hνirr ν₂ hν₂L) hν₀
              hν₂ne hσ₂₀
          have hθ₂ⱼ : scalarProduct (↥c.H)
              (inducedFromSub (h12.H0_normal_in_H).1 ν₂)
              (inducedFromSub (h12.H0_normal_in_H).1 νⱼ) = 0 :=
            theta_pair_scalar_zero c h12 hH0index (hνirr ν₂ hν₂L) hνⱼirr
              hν₂ⱼne hσ₂ⱼ
          simp [scalarProduct_sub_left, scalarProduct_sub_right,
            hθ₀₀, hθ₀₂, hθ₀ⱼ, hθ₂₀, hθ₂ⱼ]
        have hχj0 :
            scalarProduct G χ₂₃ (inducedClassFunction c.H0 (ν₀ - νⱼ)) = 0 := by
          rcases hχjmem with hχj1 | hχj0 | hχjm1
          · exact False.elim (hχjne1 hχj1)
          · exact hχj0
          · exfalso
            have hth2g : IsGeneralizedCharacter
                (χ₂₃ - inducedClassFunction c.H0 (ν₀ - ν₂)) := by
              exact isGeneralizedCharacter_sub hχg hδ₂g
            have hδ₂χ :
                scalarProduct G (inducedClassFunction c.H0 (ν₀ - ν₂)) χ₂₃ = 1 := by
              apply star_inj.mp
              rw [scalarProduct_star_comm]
              change scalarProduct G χ₂₃
                (inducedClassFunction c.H0 (ν₀ - ν₂)) = star 1
              simpa using hχ₂
            have hth2norm :
                normSq G (χ₂₃ - inducedClassFunction c.H0 (ν₀ - ν₂)) = 1 := by
              unfold normSq
              rw [scalarProduct_sub_left, scalarProduct_sub_right,
                scalarProduct_sub_right]
              change scalarProduct G χ₂₃ χ₂₃ = 1 at hχ₁
              have hδ₂self : scalarProduct G
                  (inducedClassFunction c.H0 (ν₀ - ν₂))
                  (inducedClassFunction c.H0 (ν₀ - ν₂)) = 2 := by
                change normSq G (inducedClassFunction c.H0 (ν₀ - ν₂)) = 2
                exact hδ₂norm
              rw [hχ₁, hχ₂, hδ₂χ, hδ₂self]
              norm_num
            have hth2signed :
                IsIrreducibleCharacter
                    (χ₂₃ - inducedClassFunction c.H0 (ν₀ - ν₂)) ∨
                  IsIrreducibleCharacter
                    (-(χ₂₃ - inducedClassFunction c.H0 (ν₀ - ν₂))) := by
              rcases norm_one_signed_irreducible hth2g hth2norm with
                ⟨η, hη, hηeq⟩
              rcases hηeq with hηeq | hηeq
              · left
                simpa [hηeq] using hη
              · right
                simpa [hηeq] using hη
            have hth2jmem :
                scalarProduct G (χ₂₃ - inducedClassFunction c.H0 (ν₀ - ν₂))
                    (inducedClassFunction c.H0 (ν₀ - νⱼ)) = 1 ∨
                  scalarProduct G (χ₂₃ - inducedClassFunction c.H0 (ν₀ - ν₂))
                    (inducedClassFunction c.H0 (ν₀ - νⱼ)) = 0 ∨
                  scalarProduct G (χ₂₃ - inducedClassFunction c.H0 (ν₀ - ν₂))
                    (inducedClassFunction c.H0 (ν₀ - νⱼ)) = -1 := by
              exact scalarProduct_norm_one_signed_norm_two_mem
                hth2signed hδⱼg hδⱼnorm
            have hth2jneg2 :
                scalarProduct G (χ₂₃ - inducedClassFunction c.H0 (ν₀ - ν₂))
                    (inducedClassFunction c.H0 (ν₀ - νⱼ)) = -2 := by
              rw [scalarProduct_sub_left, hχjm1, hδ₂ⱼpair]
              norm_num
            rcases hth2jmem with h1 | h0 | hm1
            · rw [hth2jneg2] at h1
              norm_num at h1
            · rw [hth2jneg2] at h0
              norm_num at h0
            · rw [hth2jneg2] at hm1
              norm_num at hm1
        have hσ₂ⱼ :
            conjChar c.H0 (s_normalizes_H0 c h12) ν₂ ≠ νⱼ := by
          intro hEq
          apply sigma_image_not_mem_of_not_invariant c h12 h_inv hν₂L
          rwa [hEq]
        have hσ₃ⱼ :
            conjChar c.H0 (s_normalizes_H0 c h12) ν₃ ≠ νⱼ := by
          intro hEq
          apply sigma_image_not_mem_of_not_invariant c h12 h_inv hν₃L
          rwa [hEq]
        have hν₂ⱼne : ν₂ ≠ νⱼ := by
          intro hEq
          apply hχjne1
          rw [← hEq]
          exact hχ₂
        have hν₃ⱼne : ν₃ ≠ νⱼ := by
          intro hEq
          apply hχjne1
          rw [← hEq]
          exact hχ₃
        rcases delta_star_decomp_of_undefined c h12 hH0index
            hν₀ (hνirr ν₂ hν₂L) (hνirr ν₃ hν₃L) hνⱼirr
            hν₂L hν₃L hνjL hν₁s hν₂s hν₃s h₁₂ h₁₃
            ⟨hν₀ⱼne, hσ₀ⱼ⟩ h₂₃ ⟨hν₂ⱼne, hσ₂ⱼ⟩
            ⟨hν₃ⱼne, hσ₃ⱼ⟩ hχg hχ₁ hχ₂ hχ₃ hχj0 with
          ⟨φ, hφsig, hφth2, hφth3, hφdec, hth2dj, hth3dj, hdj3⟩
        exfalso
        rw [hδⱼnorm] at hdj3
        norm_num at hdj3
    · -- `|L| ≤ 2`: split on the singleton orbit / the two-member orbit
      by_cases hL1 : L.card ≤ 1
      · -- the singleton orbit `L = {ν₀}`: the constant lift `θ̃ := 1`
        have hLpos : 0 < L.card := Finset.card_pos.mpr ⟨ν₀, hν₀L⟩
        have hLsing : ∀ a ∈ L, a = ν₀ := by
          intro a ha
          rcases Finset.card_eq_one.mp (by omega : L.card = 1) with ⟨b, hb⟩
          have hν₀b : ν₀ = b := by
            rw [hb] at hν₀L
            simpa using hν₀L
          have hab : a = b := by
            rw [hb] at ha
            simpa using ha
          exact hab.trans hν₀b.symm
        let lift : ClassFunction (↥c.H) → ClassFunction G := fun _ => 1
        apply Nonempty.intro
        refine ⟨lift, ?_, ?_, ?_, ?_⟩
        · -- norm
          intro θ' hθ'
          have hθeq : θ' = inducedFromSub (h12.H0_normal_in_H).1 ν₀ := by
            rcases Finset.mem_image.mp hθ' with ⟨a, ha, hθa⟩
            rw [hLsing a ha] at hθa
            exact hθa.symm
          rw [hθeq]
          change normSq G (1 : ClassFunction G) =
              normSq (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν₀)
          rw [normSq_one]
          change 1 = normSq (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν₀)
          rw [theta_norm c h12 hH0index hν₀]
          rw [if_neg (hνsall ν₀ hν₀L)]
        · -- isGeneralized
          intro θ' hθ'
          exact isGeneralizedCharacter_one G
        · -- ind
          intro ν μ hμL hνIrr hνL hθνΘ hθμΘ
          rw [hLsing ν hνL] at hμL ⊢
          rw [orbit_eq_of_mem c hν₀L] at hμL
          rw [hLsing μ hμL]
          have hzero0 : inducedClassFunction c.H0 (0 : ClassFunction (↥c.H0)) = 0 := by
            rw [show (0 : ClassFunction (↥c.H0)) = (ν₀ - ν₀ : ClassFunction (↥c.H0)) by simp]
            rw [inducedClassFunction_sub]
            simp
          simp [lift, hzero0]
        · -- disjoint: `ν = μ = ν₀` contradicts `ν ≠ μ`
          intro ν μ hμL hνL hνμne hσνμ hθνΘ hθμΘ
          exfalso
          apply hνμne
          have hμL' : μ ∈ L := by
            rw [orbit_eq_of_mem c hνL] at hμL
            exact hμL
          exact (hLsing ν hνL).trans (hLsing μ hμL').symm
      · -- `|L| = 2`: the paper's `n = 2` easy case — the two-member lift
        -- `θ̃(θν₀) := A, θ̃(θν₂) := B` with `δ₂* = A − B` via
        -- `signed_pair_decomp` + the `(χ, δ₂*) = ±1` split
        have hL2 : L.card = 2 := by omega
        have hν₂ : ∃ ν₂' : ClassFunction (↥c.H0), ν₂' ∈ L.erase ν₀ := by
          rcases Finset.card_eq_one.mp (by rw [Finset.card_erase_of_mem hν₀L]; omega : (L.erase ν₀).card = 1) with ⟨a, ha⟩
          refine ⟨a, ?_⟩
          rw [ha]
          simp
        rcases hν₂ with ⟨ν₂, hν₂e⟩
        have hν₂ne : ν₂ ≠ ν₀ := (Finset.mem_erase.mp hν₂e).1
        have hν₂L : ν₂ ∈ L := (Finset.mem_erase.mp hν₂e).2
        have hν₂s : conjChar c.H0 (s_normalizes_H0 c h12) ν₂ ≠ ν₂ := hνsall ν₂ hν₂L
        have hσ₀₂ : conjChar c.H0 (s_normalizes_H0 c h12) ν₀ ≠ ν₂ := by
          intro hEq
          apply h_inv
          rwa [hEq]
        -- `δ₂* = (ν₀ − ν₂)*`: a generalized character of norm `2`
        have hδ₂g : IsGeneralizedCharacter (inducedClassFunction c.H0 (ν₀ - ν₂)) := by
          exact isGeneralizedCharacter_induced c h12 (ν₀ - ν₂)
            (isGeneralizedCharacter_sub_irr hν₀ (hνirr ν₂ hν₂L))
        have h₀₂ : ν₀ ∈ orbit c.H0 c.U ν₂ := by
          rw [orbit_eq_of_mem c hν₂L]
          exact hν₀L
        have hδ₂norm : normSq G (inducedClassFunction c.H0 (ν₀ - ν₂)) = 2 := by
          rw [delta_norm c h12 hH0index hν₀ (hνirr ν₂ hν₂L) h₀₂ hν₂ne.symm hσ₀₂]
          rw [theta_norm c h12 hH0index hν₀, theta_norm c h12 hH0index (hνirr ν₂ hν₂L)]
          rw [if_neg (hνsall ν₀ hν₀L), if_neg hν₂s]
          norm_num
        -- the signed-pair decomposition `δ₂* = ±χ ± ψ`
        rcases signed_pair_decomp hδ₂g hδ₂norm with ⟨χ, ψ, hχ, hψ, hχψ, hδdisj⟩
        have hχg : IsGeneralizedCharacter χ :=
          isGeneralizedCharacter_of_isCharacter (isCharacter_of_isIrreducibleCharacter hχ)
        have hχnorm : normSq G χ = 1 := by
          change scalarProduct G χ χ = 1
          exact irreducible_scalarProduct_self hχ
        -- `(χ, δ₂*) = ±1`
        have hχδ : scalarProduct G χ (inducedClassFunction c.H0 (ν₀ - ν₂)) = 1 ∨
            scalarProduct G χ (inducedClassFunction c.H0 (ν₀ - ν₂)) = -1 := by
          rcases hδdisj with h | h | h | h
          · left
            rw [h]
            rw [scalarProduct_sub_right]
            simp [scalarProduct_irreducible_self hχ, scalarProduct_irreducible_orthogonal hχ hψ hχψ]
          · left
            rw [h]
            rw [scalarProduct_add_right]
            simp [scalarProduct_irreducible_self hχ, scalarProduct_irreducible_orthogonal hχ hψ hχψ]
          · right
            rw [h]
            rw [scalarProduct_sub_right]
            simp [scalarProduct_neg_right, scalarProduct_irreducible_self hχ,
              scalarProduct_irreducible_orthogonal hχ hψ hχψ]
          · right
            rw [h]
            rw [scalarProduct_add_right]
            simp [scalarProduct_neg_right, scalarProduct_irreducible_self hχ,
              scalarProduct_irreducible_orthogonal hχ hψ hχψ]
        rcases hχδ with hχδ1 | hχδ1
        · -- `(χ, δ₂*) = 1`: `A := χ`, `B := χ − δ₂*`
          have hBnorm : normSq G (χ - inducedClassFunction c.H0 (ν₀ - ν₂)) = 1 := by
            unfold normSq
            rw [scalarProduct_sub_left, scalarProduct_sub_right, scalarProduct_sub_right]
            have hχχ : scalarProduct G χ χ = 1 := by
              change scalarProduct G χ χ = 1
              exact irreducible_scalarProduct_self hχ
            have hδχ : scalarProduct G (inducedClassFunction c.H0 (ν₀ - ν₂)) χ = 1 := by
              apply star_inj.mp
              rw [scalarProduct_star_comm]
              change scalarProduct G χ (inducedClassFunction c.H0 (ν₀ - ν₂)) = star 1
              simpa using hχδ1
            have hδδ : scalarProduct G (inducedClassFunction c.H0 (ν₀ - ν₂))
                (inducedClassFunction c.H0 (ν₀ - ν₂)) = 2 := hδ₂norm
            rw [hχχ, hχδ1, hδχ, hδδ]
            norm_num
          have hAB : scalarProduct G χ (χ - inducedClassFunction c.H0 (ν₀ - ν₂)) = 0 := by
            rw [scalarProduct_sub_right]
            rw [show scalarProduct G χ χ = 1 by
              change scalarProduct G χ χ = 1
              exact irreducible_scalarProduct_self hχ]
            rw [hχδ1]
            norm_num
          have hδAB : inducedClassFunction c.H0 (ν₀ - ν₂) = χ - (χ - inducedClassFunction c.H0 (ν₀ - ν₂)) := by
            ring
          have hBg : IsGeneralizedCharacter (χ - inducedClassFunction c.H0 (ν₀ - ν₂)) := by
            exact isGeneralizedCharacter_sub hχg hδ₂g
          exact theta_lift_two c h12 hH0index ν₀ ν₂ hν₀ (hνirr ν₂ hν₂L) hν₂L h_inv
            (hνsall ν₀ hν₀L) hν₂s hν₂ne (by simpa [L] using hL2)
            χ (χ - inducedClassFunction c.H0 (ν₀ - ν₂)) hχg hBg hχnorm hBnorm hAB hδAB
        · -- `(χ, δ₂*) = −1`: `A := −χ`, `B := −χ − δ₂*`
          have hBnorm : normSq G (-χ - inducedClassFunction c.H0 (ν₀ - ν₂)) = 1 := by
            rw [show -χ - inducedClassFunction c.H0 (ν₀ - ν₂) = -(χ + inducedClassFunction c.H0 (ν₀ - ν₂)) by ring]
            unfold normSq
            rw [scalarProduct_neg_left, scalarProduct_neg_right]
            rw [scalarProduct_add_left, scalarProduct_add_right, scalarProduct_add_right]
            have hχχ : scalarProduct G χ χ = 1 := by
              change scalarProduct G χ χ = 1
              exact irreducible_scalarProduct_self hχ
            have hδχ : scalarProduct G (inducedClassFunction c.H0 (ν₀ - ν₂)) χ = -1 := by
              apply star_inj.mp
              rw [scalarProduct_star_comm]
              change scalarProduct G χ (inducedClassFunction c.H0 (ν₀ - ν₂)) = star (-1)
              simpa using hχδ1
            have hδδ : scalarProduct G (inducedClassFunction c.H0 (ν₀ - ν₂))
                (inducedClassFunction c.H0 (ν₀ - ν₂)) = 2 := hδ₂norm
            rw [hχχ, hχδ1, hδχ, hδδ]
            norm_num
          have hAB : scalarProduct G (-χ) (-χ - inducedClassFunction c.H0 (ν₀ - ν₂)) = 0 := by
            rw [show -χ - inducedClassFunction c.H0 (ν₀ - ν₂) = -(χ + inducedClassFunction c.H0 (ν₀ - ν₂)) by ring]
            rw [scalarProduct_neg_left, scalarProduct_neg_right]
            rw [scalarProduct_add_right]
            rw [show scalarProduct G χ χ = 1 by
              change scalarProduct G χ χ = 1
              exact irreducible_scalarProduct_self hχ]
            rw [hχδ1]
            norm_num
          have hδAB : inducedClassFunction c.H0 (ν₀ - ν₂) = -χ - (-χ - inducedClassFunction c.H0 (ν₀ - ν₂)) := by
            ring
          have hχg' : IsGeneralizedCharacter (-χ) := isGeneralizedCharacter_of_signed_irreducible hχ
          have hχnorm' : normSq G (-χ) = 1 := by
            change scalarProduct G (-χ) (-χ) = 1
            rw [scalarProduct_neg_left, scalarProduct_neg_right]
            simpa using irreducible_scalarProduct_self hχ
          have hBg : IsGeneralizedCharacter (-χ - inducedClassFunction c.H0 (ν₀ - ν₂)) := by
            exact isGeneralizedCharacter_sub hχg' hδ₂g
          exact theta_lift_two c h12 hH0index ν₀ ν₂ hν₀ (hνirr ν₂ hν₂L) hν₂L h_inv
            (hνsall ν₀ hν₀L) hν₂s hν₂ne (by simpa [L] using hL2)
            (-χ) (-χ - inducedClassFunction c.H0 (ν₀ - ν₂)) hχg' hBg hχnorm' hBnorm hAB hδAB

/-- The `Λ`-orbits of the irreducible characters of `H0`. -/
private noncomputable def orbitSet (c : Hyp11 G) (h12 : Hyp12 c) :
    Finset (Finset (ClassFunction (↥c.H0))) := by
  classical
  exact (Finset.univ : Finset (Irr (↥c.H0))).image (fun ν : Irr (↥c.H0) => orbit c.H0 c.U ν.1)

/-- An orbit in `orbitSet` is nonempty (the base character's own orbit). -/
private lemma orbitSet_mem_nonempty (c : Hyp11 G) (h12 : Hyp12 c)
    {L : Finset (ClassFunction (↥c.H0))} (hL : L ∈ orbitSet c h12) : L.Nonempty := by
  rcases Finset.mem_image.mp hL with ⟨ν, hν, hLν⟩
  refine ⟨ν.1, ?_⟩
  rw [← hLν]
  exact orbit_self_mem c ν.1

/-- The orbit representatives of `Irr(H0)`: the `ι`-indexing required by
`lemma_1_7_iii` (`∀ ν, ∃! i, ν ∈ orbit (rep i)`), with each `rep i`
irreducible. -/
private lemma exists_orbit_representatives (c : Hyp11 G) (h12 : Hyp12 c) :
    ∃ (ι : Type u) (_ : Fintype ι) (rep : ι → ClassFunction (↥c.H0)),
      (∀ i : ι, IsIrreducibleCharacter (rep i)) ∧
      (∀ ν : {ν : ClassFunction (↥c.H0) // IsIrreducibleCharacter ν},
        ∃! i : ι, ν.1 ∈ orbit c.H0 c.U (rep i)) := by
  classical
  let ι : Type u := {L : Finset (ClassFunction (↥c.H0)) // L ∈ orbitSet c h12}
  let rep : ι → ClassFunction (↥c.H0) := fun L =>
    Classical.choose (orbitSet_mem_nonempty c h12 L.2)
  refine ⟨ι, inferInstance, rep, ?_, ?_⟩
  · intro L
    rcases Finset.mem_image.mp L.2 with ⟨ν, hν, hLν⟩
    have hspec : rep L ∈ L.1 := Classical.choose_spec (orbitSet_mem_nonempty c h12 L.2)
    have hνL' : rep L ∈ orbit c.H0 c.U ν.1 := hLν ▸ hspec
    exact orbit_mem_isIrreducible c.H0 c.U ν.2 hνL'
  · intro ν
    refine ⟨⟨orbit c.H0 c.U ν.1, Finset.mem_image.mpr ⟨ν, Finset.mem_univ ν, rfl⟩⟩, ?_, ?_⟩
    · have hspec : rep ⟨orbit c.H0 c.U ν.1, Finset.mem_image.mpr ⟨ν, Finset.mem_univ ν, rfl⟩⟩ ∈
          orbit c.H0 c.U ν.1 :=
        Classical.choose_spec (orbitSet_mem_nonempty c h12
          (Finset.mem_image.mpr ⟨ν, Finset.mem_univ ν, rfl⟩ : orbit c.H0 c.U ν.1 ∈ orbitSet c h12))
      change ν.1 ∈ orbit c.H0 c.U
        (rep ⟨orbit c.H0 c.U ν.1, Finset.mem_image.mpr ⟨ν, Finset.mem_univ ν, rfl⟩⟩)
      rw [orbit_eq_of_mem c hspec]
      exact orbit_self_mem c ν.1
    · intro L hLmem
      have hEqOrbit : L.1 = orbit c.H0 c.U ν.1 := by
        have hspec : rep L ∈ L.1 := Classical.choose_spec (orbitSet_mem_nonempty c h12 L.2)
        rcases Finset.mem_image.mp L.2 with ⟨μ, hμ, hLμ⟩
        have ho1 : orbit c.H0 c.U (rep L) = orbit c.H0 c.U ν.1 :=
          (orbit_eq_of_mem c hLmem).symm
        have ho2 : orbit c.H0 c.U (rep L) = orbit c.H0 c.U μ.1 := by
          rw [← hLμ] at hspec
          exact orbit_eq_of_mem c hspec
        have ho3 : orbit c.H0 c.U μ.1 = L.1 := hLμ
        rw [← ho1, ho2, ho3]
      apply Subtype.ext
      exact hEqOrbit

/-- The Coherence-Theorem map: `ν̃ := θ̃_{ν^H}` (the lift of the induced
character of `ν`, from the per-orbit `ThetaLift`). -/
private structure ThetaLiftChoice (c : Hyp11 G) (h12 : Hyp12 c)
    (Θ : Finset (ClassFunction (↥c.H))) where
  base : Irr (↥c.H0)
  theta_eq : thetaOfOrbit c h12 (orbit c.H0 c.U base.1) = Θ
  data : ThetaLift c h12 (orbit c.H0 c.U base.1) Θ

private lemma exists_theta_lift_choice (c : Hyp11 G) (h12 : Hyp12 c)
    (hH0index : (c.H0.subgroupOf c.H).index = 2)
    (Θ : Finset (ClassFunction (↥c.H)))
    (hΘ : ∃ ν : Irr (↥c.H0), thetaOfOrbit c h12 (orbit c.H0 c.U ν.1) = Θ) :
    Nonempty (ThetaLiftChoice c h12 Θ) := by
  classical
  rcases hΘ with ⟨ν, rfl⟩
  exact ⟨⟨ν, rfl, Classical.choice
    (exists_theta_lift_orbit c h12 hH0index ν.1 ν.2)⟩⟩

private noncomputable def canonicalThetaLiftChoice (c : Hyp11 G) (h12 : Hyp12 c)
    (hH0index : (c.H0.subgroupOf c.H).index = 2)
    (Θ : Finset (ClassFunction (↥c.H)))
    (hΘ : ∃ ν : Irr (↥c.H0), thetaOfOrbit c h12 (orbit c.H0 c.U ν.1) = Θ) :
    ThetaLiftChoice c h12 Θ :=
  Classical.choice (exists_theta_lift_choice c h12 hH0index Θ hΘ)

private noncomputable def canonicalLift (c : Hyp11 G) (h12 : Hyp12 c)
    (hH0index : (c.H0.subgroupOf c.H).index = 2)
    (Θ : Finset (ClassFunction (↥c.H))) :
    ClassFunction (↥c.H) → ClassFunction G := fun θ' =>
  if hΘ : ∃ ν : Irr (↥c.H0), thetaOfOrbit c h12 (orbit c.H0 c.U ν.1) = Θ then
    (canonicalThetaLiftChoice c h12 hH0index Θ hΘ).data.lift θ'
  else 0

/-- The Coherence-Theorem map: `ν̃ := θ̃_{ν^H}`.  The selected lift is keyed
by the induced-character set `Θ`, rather than by a base member of the orbit;
this makes the choices for `ν` and `ν^s` definitionally identical. -/
private noncomputable def tildeTheta (c : Hyp11 G) (h12 : Hyp12 c)
    (hH0index : (c.H0.subgroupOf c.H).index = 2)
    (ν : ClassFunction (↥c.H0)) (hν : IsIrreducibleCharacter ν) :
    ClassFunction G :=
  let Θ := thetaOfOrbit c h12 (orbit c.H0 c.U ν)
  canonicalLift c h12 hH0index Θ
    (inducedFromSub (h12.H0_normal_in_H).1 ν)

private lemma canonicalLift_congr (c : Hyp11 G) (h12 : Hyp12 c)
    (hH0index : (c.H0.subgroupOf c.H).index = 2)
    {Θ₁ Θ₂ : Finset (ClassFunction (↥c.H))}
    {θ₁ θ₂ : ClassFunction (↥c.H)}
    (hΘ : Θ₁ = Θ₂) (hθ : θ₁ = θ₂) :
    canonicalLift c h12 hH0index Θ₁ θ₁ =
      canonicalLift c h12 hH0index Θ₂ θ₂ := by
  subst Θ₂
  subst θ₂
  rfl

private lemma tildeTheta_isGeneralized (c : Hyp11 G) (h12 : Hyp12 c)
    (hH0index : (c.H0.subgroupOf c.H).index = 2)
    (ν : ClassFunction (↥c.H0)) (hν : IsIrreducibleCharacter ν) :
    IsGeneralizedCharacter (tildeTheta c h12 hH0index ν hν) := by
  classical
  unfold tildeTheta canonicalLift
  rw [dif_pos ⟨⟨ν, hν⟩, rfl⟩]
  exact (canonicalThetaLiftChoice c h12 hH0index
    (thetaOfOrbit c h12 (orbit c.H0 c.U ν)) ⟨⟨ν, hν⟩, rfl⟩).data.isGeneralized
      (inducedFromSub (h12.H0_normal_in_H).1 ν)
      (thetaOfOrbit_self c h12 ν)

private lemma tildeTheta_norm (c : Hyp11 G) (h12 : Hyp12 c)
    (hH0index : (c.H0.subgroupOf c.H).index = 2)
    (ν : ClassFunction (↥c.H0)) (hν : IsIrreducibleCharacter ν) :
    normSq G (tildeTheta c h12 hH0index ν hν) =
      normSq (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν) := by
  classical
  unfold tildeTheta canonicalLift
  rw [dif_pos ⟨⟨ν, hν⟩, rfl⟩]
  exact (canonicalThetaLiftChoice c h12 hH0index
    (thetaOfOrbit c h12 (orbit c.H0 c.U ν)) ⟨⟨ν, hν⟩, rfl⟩).data.norm
      (inducedFromSub (h12.H0_normal_in_H).1 ν)
      (thetaOfOrbit_self c h12 ν)

/-! The canonical orbit-keyed lift satisfies the induction-difference field
`(ii)`.  Keeping this as a named helper lets the `(v)` assembly field reuse
the same transport without rebuilding the choice-cast proof. -/
private lemma tildeTheta_ind (c : Hyp11 G) (h12 : Hyp12 c)
    (hH0index : (c.H0.subgroupOf c.H).index = 2)
    (μ ν : Irr (↥c.H0)) (hμL : μ.1 ∈ orbit c.H0 c.U ν.1) :
    inducedClassFunction c.H0 (μ.1 - ν.1) =
      tildeTheta c h12 hH0index μ.1 μ.2 -
        tildeTheta c h12 hH0index ν.1 ν.2 := by
  classical
  let Θ : Finset (ClassFunction (↥c.H)) :=
    thetaOfOrbit c h12 (orbit c.H0 c.U ν.1)
  let hΘ : ∃ ξ : Irr (↥c.H0),
      thetaOfOrbit c h12 (orbit c.H0 c.U ξ.1) = Θ := ⟨ν, rfl⟩
  let C : ThetaLiftChoice c h12 Θ :=
    canonicalThetaLiftChoice c h12 hH0index Θ hΘ
  have hνL : ν.1 ∈ orbit c.H0 c.U ν.1 := orbit_self_mem c ν.1
  have hθνΘ : inducedFromSub (h12.H0_normal_in_H).1 ν.1 ∈ Θ := by
    simpa [Θ] using thetaOfOrbit_mem c h12 hνL
  have hμθΘ : inducedFromSub (h12.H0_normal_in_H).1 μ.1 ∈ Θ := by
    simpa [Θ] using thetaOfOrbit_mem c h12 hμL
  have hθνBase : inducedFromSub (h12.H0_normal_in_H).1 ν.1 ∈
      thetaOfOrbit c h12 (orbit c.H0 c.U C.base.1) := by
    rw [C.theta_eq]
    exact hθνΘ
  have htildeμ : tildeTheta c h12 hH0index μ.1 μ.2 = C.data.lift
      (inducedFromSub (h12.H0_normal_in_H).1 μ.1) := by
    dsimp only [tildeTheta]
    calc
      canonicalLift c h12 hH0index
          (thetaOfOrbit c h12 (orbit c.H0 c.U μ.1))
          (inducedFromSub (h12.H0_normal_in_H).1 μ.1) =
          canonicalLift c h12 hH0index Θ
            (inducedFromSub (h12.H0_normal_in_H).1 μ.1) := by
              exact canonicalLift_congr c h12 hH0index (by
                dsimp [Θ]
                rw [orbit_eq_of_mem c hμL]) rfl
      _ = C.data.lift (inducedFromSub (h12.H0_normal_in_H).1 μ.1) := by
        unfold canonicalLift
        rw [dif_pos hΘ]
  have htildeν : tildeTheta c h12 hH0index ν.1 ν.2 = C.data.lift
      (inducedFromSub (h12.H0_normal_in_H).1 ν.1) := by
    dsimp only [tildeTheta]
    calc
      canonicalLift c h12 hH0index
          (thetaOfOrbit c h12 (orbit c.H0 c.U ν.1))
          (inducedFromSub (h12.H0_normal_in_H).1 ν.1) =
          canonicalLift c h12 hH0index Θ
            (inducedFromSub (h12.H0_normal_in_H).1 ν.1) := by
              exact canonicalLift_congr c h12 hH0index (by rfl) rfl
      _ = C.data.lift (inducedFromSub (h12.H0_normal_in_H).1 ν.1) := by
        unfold canonicalLift
        rw [dif_pos hΘ]
  rcases Finset.mem_image.mp hθνBase with ⟨a, ha, hθa⟩
  have hIrr_a : IsIrreducibleCharacter a :=
    orbit_mem_isIrreducible c.H0 c.U C.base.2 ha
  rcases theta_eq_imp_conj c h12 hH0index hIrr_a ν.2 hθa with hνa | hσνa
  · have hνBase : ν.1 ∈ orbit c.H0 c.U C.base.1 := by
      rw [hνa]
      exact ha
    have hdata := C.data.ind (ν := ν.1) (μ := μ.1) hμL ν.2 hνBase
      hθνΘ hμθΘ
    rw [htildeμ, htildeν]
    exact hdata
  · have hsHinv : ∀ x : ↥c.H0, c.s⁻¹ * (x : G) * c.s ∈ c.H0 := by
      intro x
      simpa using (h12.H0_normal_in_H).2 c.s⁻¹ (c.H.inv_mem (s_mem_H c))
        (x : G) x.2
    have hσνIrr : IsIrreducibleCharacter
        (conjChar c.H0 (s_normalizes_H0 c h12) ν.1) :=
      isIrreducibleCharacter_conjChar c.H0 (s_normalizes_H0 c h12)
        hsHinv ν.2
    have hσνBase : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 ∈
        orbit c.H0 c.U C.base.1 := by
      rw [hσνa]
      exact ha
    have hσμL : conjChar c.H0 (s_normalizes_H0 c h12) μ.1 ∈
        orbit c.H0 c.U
          (conjChar c.H0 (s_normalizes_H0 c h12) ν.1) :=
      orbit_subset_conjChar c h12 μ.1 hμL
    have hθσν : inducedFromSub (h12.H0_normal_in_H).1
        (conjChar c.H0 (s_normalizes_H0 c h12) ν.1) =
        inducedFromSub (h12.H0_normal_in_H).1 ν.1 :=
      inducedFromSub_conjChar_eq c h12 hH0index ν.2
    have hθσμ : inducedFromSub (h12.H0_normal_in_H).1
        (conjChar c.H0 (s_normalizes_H0 c h12) μ.1) =
        inducedFromSub (h12.H0_normal_in_H).1 μ.1 :=
      inducedFromSub_conjChar_eq c h12 hH0index μ.2
    have hθσνΘ : inducedFromSub (h12.H0_normal_in_H).1
        (conjChar c.H0 (s_normalizes_H0 c h12) ν.1) ∈ Θ := by
      rw [hθσν]
      exact hθνΘ
    have hθσμΘ : inducedFromSub (h12.H0_normal_in_H).1
        (conjChar c.H0 (s_normalizes_H0 c h12) μ.1) ∈ Θ := by
      rw [hθσμ]
      exact hμθΘ
    have hdata := C.data.ind
      (ν := conjChar c.H0 (s_normalizes_H0 c h12) ν.1)
      (μ := conjChar c.H0 (s_normalizes_H0 c h12) μ.1)
      hσμL hσνIrr hσνBase hθσνΘ hθσμΘ
    have hind_conj : ∀ δ : ClassFunction (↥c.H0),
        inducedClassFunction c.H0
            (conjChar c.H0 (s_normalizes_H0 c h12) δ) =
          inducedClassFunction c.H0 δ := by
      intro δ
      ext g
      unfold inducedClassFunction
      congr 1
      refine Finset.sum_bij (fun x _ => x * c.s⁻¹) ?_ ?_ ?_ ?_
      · intro x hx
        simp
      · intro a ha b hb hab
        exact mul_right_cancel hab
      · intro y hy
        refine ⟨y * c.s, ?_, ?_⟩
        · simp
        · simp
      · intro x hx
        by_cases hmem : x⁻¹ * g * x ∈ c.H0
        · simp only [hmem, dite_true]
          have hmem' : (x * c.s⁻¹)⁻¹ * g * (x * c.s⁻¹) ∈ c.H0 := by
            simpa [mul_assoc] using
              (s_normalizes_H0 c h12 ⟨x⁻¹ * g * x, hmem⟩)
          simp only [hmem', dite_true]
          simp [conjChar, conjMonoidHom, mul_assoc]
        · simp only [hmem, dite_false]
          have hmem' : ¬ (x * c.s⁻¹)⁻¹ * g * (x * c.s⁻¹) ∈ c.H0 := by
            intro h'
            apply hmem
            simpa [mul_assoc] using hsHinv
              ⟨(x * c.s⁻¹)⁻¹ * g * (x * c.s⁻¹), h'⟩
          simp only [hmem', dite_false]
    have hsub : conjChar c.H0 (s_normalizes_H0 c h12) (μ.1 - ν.1) =
        conjChar c.H0 (s_normalizes_H0 c h12) μ.1 -
          conjChar c.H0 (s_normalizes_H0 c h12) ν.1 := by
      ext x
      rfl
    calc
      inducedClassFunction c.H0 (μ.1 - ν.1) =
          inducedClassFunction c.H0
            (conjChar c.H0 (s_normalizes_H0 c h12) μ.1 -
              conjChar c.H0 (s_normalizes_H0 c h12) ν.1) := by
        rw [← hsub, hind_conj]
      _ = C.data.lift (inducedFromSub (h12.H0_normal_in_H).1 μ.1) -
          C.data.lift (inducedFromSub (h12.H0_normal_in_H).1 ν.1) := by
        rw [hθσμ, hθσν] at hdata
        exact hdata
      _ = tildeTheta c h12 hH0index μ.1 μ.2 -
          tildeTheta c h12 hH0index ν.1 ν.2 := by
        rw [htildeμ, htildeν]

/-- The main assembly: `exists_coherence_data` with all eight fields. The
`(i)`-norm and `isGeneralized` are the lift's fields plus `theta_norm`; the
remaining fields need the per-orbit-choice bookkeeping (the lift of `μ` and
`ν` in one orbit comes from the same `ThetaLift` — a cast across the
`thetaOfOrbit (orbit μ) = thetaOfOrbit (orbit ν)` equality, which the
`Classical.choice`-based `tildeTheta` does not make definitional) and the
`V = 0` input of `lemma_2_2` case 1 (`V_zero_of_pair`) for `(vi)`; these are
the recorded `sorry`s with the exact statements they discharge. -/
private theorem exists_coherence_data (c : Hyp11 G) (h12 : Hyp12 c) :
    Nonempty (CoherenceData c h12) := by
  classical
  let hH0index : (c.H0.subgroupOf c.H).index = 2 := H0_index c h12
  let tilde : Irr (↥c.H0) → ClassFunction G := fun ν =>
    tildeTheta c h12 hH0index ν.1 ν.2
  refine ⟨⟨tilde, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · -- invariance: the canonical lift is keyed by `Θ`, and the `Θ`-sets and
    -- induced characters of `ν` and `ν^s` agree.
    intro ν
    have hΘ := thetaOfOrbit_conj_eq c h12 ν.2
    have hθ := inducedFromSub_conjChar_eq c h12 hH0index ν.2
    have hΘeq : thetaOfOrbit c h12
        (orbit c.H0 c.U (conjIrr c h12 ν).1) =
        thetaOfOrbit c h12 (orbit c.H0 c.U ν.1) := by
      rw [conjIrr_coe]
      exact hΘ
    have hθeq : inducedFromSub (h12.H0_normal_in_H).1 (conjIrr c h12 ν).1 =
        inducedFromSub (h12.H0_normal_in_H).1 ν.1 := by
      rw [conjIrr_coe]
      exact hθ
    dsimp only [tilde, tildeTheta]
    exact canonicalLift_congr c h12 hH0index hΘeq hθeq
  · -- isGeneralized: the lift's field
    intro ν
    exact tildeTheta_isGeneralized c h12 hH0index ν.1 ν.2
  · -- norm: the lift norm + theta_norm
    intro ν
    constructor
    · exact tildeTheta_norm c h12 hH0index ν.1 ν.2
    · dsimp [tilde]
      rw [tildeTheta_norm c h12 hH0index ν.1 ν.2]
      exact theta_norm c h12 hH0index ν.2
  · -- ind: the lift's `ind`; needs the choice-cast for `μ` (same orbit)
    intro μ ν hμL
    let Θ : Finset (ClassFunction (↥c.H)) :=
      thetaOfOrbit c h12 (orbit c.H0 c.U ν.1)
    let hΘ : ∃ ξ : Irr (↥c.H0),
        thetaOfOrbit c h12 (orbit c.H0 c.U ξ.1) = Θ := ⟨ν, rfl⟩
    let C : ThetaLiftChoice c h12 Θ :=
      canonicalThetaLiftChoice c h12 hH0index Θ hΘ
    have hνL : ν.1 ∈ orbit c.H0 c.U ν.1 := orbit_self_mem c ν.1
    have hθνΘ : inducedFromSub (h12.H0_normal_in_H).1 ν.1 ∈ Θ := by
      simpa [Θ] using thetaOfOrbit_mem c h12 hνL
    have hμθΘ : inducedFromSub (h12.H0_normal_in_H).1 μ.1 ∈ Θ := by
      simpa [Θ] using thetaOfOrbit_mem c h12 hμL
    have hθνBase : inducedFromSub (h12.H0_normal_in_H).1 ν.1 ∈
        thetaOfOrbit c h12 (orbit c.H0 c.U C.base.1) := by
      rw [C.theta_eq]
      exact hθνΘ
    have htildeμ : tilde μ = C.data.lift
        (inducedFromSub (h12.H0_normal_in_H).1 μ.1) := by
      dsimp only [tilde, tildeTheta]
      calc
        canonicalLift c h12 hH0index
            (thetaOfOrbit c h12 (orbit c.H0 c.U μ.1))
            (inducedFromSub (h12.H0_normal_in_H).1 μ.1) =
            canonicalLift c h12 hH0index Θ
              (inducedFromSub (h12.H0_normal_in_H).1 μ.1) := by
                exact canonicalLift_congr c h12 hH0index (by
                  dsimp [Θ]
                  rw [orbit_eq_of_mem c hμL]) rfl
        _ = C.data.lift (inducedFromSub (h12.H0_normal_in_H).1 μ.1) := by
          unfold canonicalLift
          rw [dif_pos hΘ]
    have htildeν : tilde ν = C.data.lift
        (inducedFromSub (h12.H0_normal_in_H).1 ν.1) := by
      dsimp only [tilde, tildeTheta]
      calc
        canonicalLift c h12 hH0index
            (thetaOfOrbit c h12 (orbit c.H0 c.U ν.1))
            (inducedFromSub (h12.H0_normal_in_H).1 ν.1) =
            canonicalLift c h12 hH0index Θ
              (inducedFromSub (h12.H0_normal_in_H).1 ν.1) := by
                exact canonicalLift_congr c h12 hH0index (by rfl) rfl
        _ = C.data.lift (inducedFromSub (h12.H0_normal_in_H).1 ν.1) := by
          unfold canonicalLift
          rw [dif_pos hΘ]
    -- The canonical package may represent this `Θ` by the target orbit or
    -- by its `s`-conjugate; `theta_eq_imp_conj` is exactly the cast split.
    rcases Finset.mem_image.mp hθνBase with ⟨a, ha, hθa⟩
    have hIrr_a : IsIrreducibleCharacter a :=
      orbit_mem_isIrreducible c.H0 c.U C.base.2 ha
    rcases theta_eq_imp_conj c h12 hH0index hIrr_a ν.2 hθa with hνa | hσνa
    · have hνBase : ν.1 ∈ orbit c.H0 c.U C.base.1 := by
        rw [hνa]
        exact ha
      have hdata := C.data.ind (ν := ν.1) (μ := μ.1) hμL ν.2 hνBase
        hθνΘ hμθΘ
      rw [htildeμ, htildeν]
      exact hdata
    · have hsHinv : ∀ x : ↥c.H0, c.s⁻¹ * (x : G) * c.s ∈ c.H0 := by
        intro x
        simpa using (h12.H0_normal_in_H).2 c.s⁻¹ (c.H.inv_mem (s_mem_H c))
          (x : G) x.2
      have hσνIrr : IsIrreducibleCharacter
          (conjChar c.H0 (s_normalizes_H0 c h12) ν.1) :=
        isIrreducibleCharacter_conjChar c.H0 (s_normalizes_H0 c h12)
          hsHinv ν.2
      have hσνBase : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 ∈
          orbit c.H0 c.U C.base.1 := by
        rw [hσνa]
        exact ha
      have hσμL : conjChar c.H0 (s_normalizes_H0 c h12) μ.1 ∈
          orbit c.H0 c.U (conjChar c.H0 (s_normalizes_H0 c h12) ν.1) :=
        orbit_subset_conjChar c h12 μ.1 hμL
      have hθσν : inducedFromSub (h12.H0_normal_in_H).1
          (conjChar c.H0 (s_normalizes_H0 c h12) ν.1) =
          inducedFromSub (h12.H0_normal_in_H).1 ν.1 :=
        inducedFromSub_conjChar_eq c h12 hH0index ν.2
      have hθσμ : inducedFromSub (h12.H0_normal_in_H).1
          (conjChar c.H0 (s_normalizes_H0 c h12) μ.1) =
          inducedFromSub (h12.H0_normal_in_H).1 μ.1 :=
        inducedFromSub_conjChar_eq c h12 hH0index μ.2
      have hθσνΘ : inducedFromSub (h12.H0_normal_in_H).1
          (conjChar c.H0 (s_normalizes_H0 c h12) ν.1) ∈ Θ := by
        rw [hθσν]
        exact hθνΘ
      have hθσμΘ : inducedFromSub (h12.H0_normal_in_H).1
          (conjChar c.H0 (s_normalizes_H0 c h12) μ.1) ∈ Θ := by
        rw [hθσμ]
        exact hμθΘ
      have hdata := C.data.ind
        (ν := conjChar c.H0 (s_normalizes_H0 c h12) ν.1)
        (μ := conjChar c.H0 (s_normalizes_H0 c h12) μ.1)
        hσμL hσνIrr hσνBase hθσνΘ hθσμΘ
      -- Induction from `H0` is unchanged by conjugating the source by `s`;
      -- reindex the defining sum by right multiplication with `s⁻¹`.
      have hind_conj : ∀ δ : ClassFunction (↥c.H0),
          inducedClassFunction c.H0
              (conjChar c.H0 (s_normalizes_H0 c h12) δ) =
            inducedClassFunction c.H0 δ := by
        intro δ
        ext g
        unfold inducedClassFunction
        congr 1
        refine Finset.sum_bij (fun x _ => x * c.s⁻¹) ?_ ?_ ?_ ?_
        · intro x hx
          simp
        · intro a ha b hb hab
          exact mul_right_cancel hab
        · intro y hy
          refine ⟨y * c.s, ?_, ?_⟩
          · simp
          · simp
        · intro x hx
          by_cases hmem : x⁻¹ * g * x ∈ c.H0
          · simp only [hmem, dite_true]
            have hmem' : (x * c.s⁻¹)⁻¹ * g * (x * c.s⁻¹) ∈ c.H0 := by
              simpa [mul_assoc] using
                (s_normalizes_H0 c h12 ⟨x⁻¹ * g * x, hmem⟩)
            simp only [hmem', dite_true]
            simp [conjChar, conjMonoidHom, mul_assoc]
          · simp only [hmem, dite_false]
            have hmem' : ¬ (x * c.s⁻¹)⁻¹ * g * (x * c.s⁻¹) ∈ c.H0 := by
              intro h'
              apply hmem
              simpa [mul_assoc] using hsHinv
                ⟨(x * c.s⁻¹)⁻¹ * g * (x * c.s⁻¹), h'⟩
            simp only [hmem', dite_false]
      have hsub : conjChar c.H0 (s_normalizes_H0 c h12) (μ.1 - ν.1) =
          conjChar c.H0 (s_normalizes_H0 c h12) μ.1 -
            conjChar c.H0 (s_normalizes_H0 c h12) ν.1 := by
        ext x
        rfl
      calc
        inducedClassFunction c.H0 (μ.1 - ν.1) =
            inducedClassFunction c.H0
              (conjChar c.H0 (s_normalizes_H0 c h12) μ.1 -
                conjChar c.H0 (s_normalizes_H0 c h12) ν.1) := by
          rw [← hsub, hind_conj]
        _ = C.data.lift (inducedFromSub (h12.H0_normal_in_H).1 μ.1) -
            C.data.lift (inducedFromSub (h12.H0_normal_in_H).1 ν.1) := by
          rw [hθσμ, hθσν] at hdata
          exact hdata
        _ = tilde μ - tilde ν := by rw [htildeμ, htildeν]
  · -- disjoint: the lift's `disjoint`; needs the choice-cast for `μ`
    intro μ ν hμL hνne hσνne
    let Θ : Finset (ClassFunction (↥c.H)) :=
      thetaOfOrbit c h12 (orbit c.H0 c.U ν.1)
    let hΘ : ∃ ξ : Irr (↥c.H0),
        thetaOfOrbit c h12 (orbit c.H0 c.U ξ.1) = Θ := ⟨ν, rfl⟩
    let C : ThetaLiftChoice c h12 Θ :=
      canonicalThetaLiftChoice c h12 hH0index Θ hΘ
    have hνL : ν.1 ∈ orbit c.H0 c.U ν.1 := orbit_self_mem c ν.1
    have hθνΘ : inducedFromSub (h12.H0_normal_in_H).1 ν.1 ∈ Θ := by
      simpa [Θ] using thetaOfOrbit_mem c h12 hνL
    have hμθΘ : inducedFromSub (h12.H0_normal_in_H).1 μ.1 ∈ Θ := by
      simpa [Θ] using thetaOfOrbit_mem c h12 hμL
    have hθνBase : inducedFromSub (h12.H0_normal_in_H).1 ν.1 ∈
        thetaOfOrbit c h12 (orbit c.H0 c.U C.base.1) := by
      rw [C.theta_eq]
      exact hθνΘ
    have htildeμ : tilde μ = C.data.lift
        (inducedFromSub (h12.H0_normal_in_H).1 μ.1) := by
      dsimp only [tilde, tildeTheta]
      calc
        canonicalLift c h12 hH0index
            (thetaOfOrbit c h12 (orbit c.H0 c.U μ.1))
            (inducedFromSub (h12.H0_normal_in_H).1 μ.1) =
            canonicalLift c h12 hH0index Θ
              (inducedFromSub (h12.H0_normal_in_H).1 μ.1) := by
                exact canonicalLift_congr c h12 hH0index (by
                  dsimp [Θ]
                  rw [orbit_eq_of_mem c hμL]) rfl
        _ = C.data.lift (inducedFromSub (h12.H0_normal_in_H).1 μ.1) := by
          unfold canonicalLift
          rw [dif_pos hΘ]
    have htildeν : tilde ν = C.data.lift
        (inducedFromSub (h12.H0_normal_in_H).1 ν.1) := by
      dsimp only [tilde, tildeTheta]
      calc
        canonicalLift c h12 hH0index
            (thetaOfOrbit c h12 (orbit c.H0 c.U ν.1))
            (inducedFromSub (h12.H0_normal_in_H).1 ν.1) =
            canonicalLift c h12 hH0index Θ
              (inducedFromSub (h12.H0_normal_in_H).1 ν.1) := by
                exact canonicalLift_congr c h12 hH0index (by rfl) rfl
        _ = C.data.lift (inducedFromSub (h12.H0_normal_in_H).1 ν.1) := by
          unfold canonicalLift
          rw [dif_pos hΘ]
    -- As in `(ii)`, the canonical base is either this orbit or its
    -- `s`-conjugate; the latter case transports both disjointness side
    -- conditions through the involution.
    rcases Finset.mem_image.mp hθνBase with ⟨a, ha, hθa⟩
    have hIrr_a : IsIrreducibleCharacter a :=
      orbit_mem_isIrreducible c.H0 c.U C.base.2 ha
    rcases theta_eq_imp_conj c h12 hH0index hIrr_a ν.2 hθa with hνa | hσνa
    · have hνBase : ν.1 ∈ orbit c.H0 c.U C.base.1 := by
        rw [hνa]
        exact ha
      have hdata := C.data.disjoint hμL hνBase hνne hσνne hθνΘ hμθΘ
      rw [htildeμ, htildeν]
      exact hdata
    · have hσνBase : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 ∈
          orbit c.H0 c.U C.base.1 := by
        rw [hσνa]
        exact ha
      have hσμL : conjChar c.H0 (s_normalizes_H0 c h12) μ.1 ∈
          orbit c.H0 c.U (conjChar c.H0 (s_normalizes_H0 c h12) ν.1) :=
        orbit_subset_conjChar c h12 μ.1 hμL
      have hσνne' : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 ≠
          conjChar c.H0 (s_normalizes_H0 c h12) μ.1 := by
        intro h
        apply hνne
        have h' := congrArg (conjChar c.H0 (s_normalizes_H0 c h12)) h
        rw [conjChar_conjChar c h12 ν.1,
          conjChar_conjChar c h12 μ.1] at h'
        exact h'
      have hσpair : conjChar c.H0 (s_normalizes_H0 c h12)
            (conjChar c.H0 (s_normalizes_H0 c h12) ν.1) ≠
          conjChar c.H0 (s_normalizes_H0 c h12) μ.1 := by
        intro h
        apply hσνne
        have h' := congrArg (conjChar c.H0 (s_normalizes_H0 c h12)) h
        rw [conjChar_conjChar c h12
              (conjChar c.H0 (s_normalizes_H0 c h12) ν.1),
          conjChar_conjChar c h12 μ.1] at h'
        exact h'
      have hθσν : inducedFromSub (h12.H0_normal_in_H).1
          (conjChar c.H0 (s_normalizes_H0 c h12) ν.1) =
          inducedFromSub (h12.H0_normal_in_H).1 ν.1 :=
        inducedFromSub_conjChar_eq c h12 hH0index ν.2
      have hθσμ : inducedFromSub (h12.H0_normal_in_H).1
          (conjChar c.H0 (s_normalizes_H0 c h12) μ.1) =
          inducedFromSub (h12.H0_normal_in_H).1 μ.1 :=
        inducedFromSub_conjChar_eq c h12 hH0index μ.2
      have hθσνΘ : inducedFromSub (h12.H0_normal_in_H).1
          (conjChar c.H0 (s_normalizes_H0 c h12) ν.1) ∈ Θ := by
        rw [hθσν]
        exact hθνΘ
      have hθσμΘ : inducedFromSub (h12.H0_normal_in_H).1
          (conjChar c.H0 (s_normalizes_H0 c h12) μ.1) ∈ Θ := by
        rw [hθσμ]
        exact hμθΘ
      have hdata := C.data.disjoint
        (ν := conjChar c.H0 (s_normalizes_H0 c h12) ν.1)
        (μ := conjChar c.H0 (s_normalizes_H0 c h12) μ.1)
        hσμL hσνBase hσνne' hσpair hθσνΘ hθσμΘ
      rw [hθσμ, hθσν] at hdata
      rw [htildeμ, htildeν]
      exact hdata
  · -- orthogonal: transport both `(ii)` differences through the canonical
    -- orbit-keyed lift, then use `delta_pair_scalar` and `theta_pair_orth`.
    have h_ind :
        ∀ (μ ν : Irr (↥c.H0)), μ.1 ∈ orbit c.H0 c.U ν.1 →
          inducedClassFunction c.H0 (μ.1 - ν.1) = tilde μ - tilde ν := by
      intro μ ν hμL
      let Θ : Finset (ClassFunction (↥c.H)) :=
        thetaOfOrbit c h12 (orbit c.H0 c.U ν.1)
      let hΘ : ∃ ξ : Irr (↥c.H0),
          thetaOfOrbit c h12 (orbit c.H0 c.U ξ.1) = Θ := ⟨ν, rfl⟩
      let C : ThetaLiftChoice c h12 Θ :=
        canonicalThetaLiftChoice c h12 hH0index Θ hΘ
      have hνL : ν.1 ∈ orbit c.H0 c.U ν.1 := orbit_self_mem c ν.1
      have hθνΘ : inducedFromSub (h12.H0_normal_in_H).1 ν.1 ∈ Θ := by
        simpa [Θ] using thetaOfOrbit_mem c h12 hνL
      have hμθΘ : inducedFromSub (h12.H0_normal_in_H).1 μ.1 ∈ Θ := by
        simpa [Θ] using thetaOfOrbit_mem c h12 hμL
      have hθνBase : inducedFromSub (h12.H0_normal_in_H).1 ν.1 ∈
          thetaOfOrbit c h12 (orbit c.H0 c.U C.base.1) := by
        rw [C.theta_eq]
        exact hθνΘ
      have htildeμ : tilde μ = C.data.lift
          (inducedFromSub (h12.H0_normal_in_H).1 μ.1) := by
        dsimp only [tilde, tildeTheta]
        calc
          canonicalLift c h12 hH0index
              (thetaOfOrbit c h12 (orbit c.H0 c.U μ.1))
              (inducedFromSub (h12.H0_normal_in_H).1 μ.1) =
              canonicalLift c h12 hH0index Θ
                (inducedFromSub (h12.H0_normal_in_H).1 μ.1) := by
                  exact canonicalLift_congr c h12 hH0index (by
                    dsimp [Θ]
                    rw [orbit_eq_of_mem c hμL]) rfl
          _ = C.data.lift (inducedFromSub (h12.H0_normal_in_H).1 μ.1) := by
            unfold canonicalLift
            rw [dif_pos hΘ]
      have htildeν : tilde ν = C.data.lift
          (inducedFromSub (h12.H0_normal_in_H).1 ν.1) := by
        dsimp only [tilde, tildeTheta]
        calc
          canonicalLift c h12 hH0index
              (thetaOfOrbit c h12 (orbit c.H0 c.U ν.1))
              (inducedFromSub (h12.H0_normal_in_H).1 ν.1) =
              canonicalLift c h12 hH0index Θ
                (inducedFromSub (h12.H0_normal_in_H).1 ν.1) := by
                  exact canonicalLift_congr c h12 hH0index (by rfl) rfl
          _ = C.data.lift (inducedFromSub (h12.H0_normal_in_H).1 ν.1) := by
            unfold canonicalLift
            rw [dif_pos hΘ]
      rcases Finset.mem_image.mp hθνBase with ⟨a, ha, hθa⟩
      have hIrr_a : IsIrreducibleCharacter a :=
        orbit_mem_isIrreducible c.H0 c.U C.base.2 ha
      rcases theta_eq_imp_conj c h12 hH0index hIrr_a ν.2 hθa with hνa | hσνa
      · have hνBase : ν.1 ∈ orbit c.H0 c.U C.base.1 := by
          rw [hνa]
          exact ha
        have hdata := C.data.ind (ν := ν.1) (μ := μ.1) hμL ν.2 hνBase
          hθνΘ hμθΘ
        rw [htildeμ, htildeν]
        exact hdata
      · have hsHinv : ∀ x : ↥c.H0, c.s⁻¹ * (x : G) * c.s ∈ c.H0 := by
          intro x
          simpa using (h12.H0_normal_in_H).2 c.s⁻¹ (c.H.inv_mem (s_mem_H c))
            (x : G) x.2
        have hσνIrr : IsIrreducibleCharacter
            (conjChar c.H0 (s_normalizes_H0 c h12) ν.1) :=
          isIrreducibleCharacter_conjChar c.H0 (s_normalizes_H0 c h12)
            hsHinv ν.2
        have hσνBase : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 ∈
            orbit c.H0 c.U C.base.1 := by
          rw [hσνa]
          exact ha
        have hσμL : conjChar c.H0 (s_normalizes_H0 c h12) μ.1 ∈
            orbit c.H0 c.U
              (conjChar c.H0 (s_normalizes_H0 c h12) ν.1) :=
          orbit_subset_conjChar c h12 μ.1 hμL
        have hθσν : inducedFromSub (h12.H0_normal_in_H).1
            (conjChar c.H0 (s_normalizes_H0 c h12) ν.1) =
            inducedFromSub (h12.H0_normal_in_H).1 ν.1 :=
          inducedFromSub_conjChar_eq c h12 hH0index ν.2
        have hθσμ : inducedFromSub (h12.H0_normal_in_H).1
            (conjChar c.H0 (s_normalizes_H0 c h12) μ.1) =
            inducedFromSub (h12.H0_normal_in_H).1 μ.1 :=
          inducedFromSub_conjChar_eq c h12 hH0index μ.2
        have hθσνΘ : inducedFromSub (h12.H0_normal_in_H).1
            (conjChar c.H0 (s_normalizes_H0 c h12) ν.1) ∈ Θ := by
          rw [hθσν]
          exact hθνΘ
        have hθσμΘ : inducedFromSub (h12.H0_normal_in_H).1
            (conjChar c.H0 (s_normalizes_H0 c h12) μ.1) ∈ Θ := by
          rw [hθσμ]
          exact hμθΘ
        have hdata := C.data.ind
          (ν := conjChar c.H0 (s_normalizes_H0 c h12) ν.1)
          (μ := conjChar c.H0 (s_normalizes_H0 c h12) μ.1)
          hσμL hσνIrr hσνBase hθσνΘ hθσμΘ
        have hind_conj : ∀ δ : ClassFunction (↥c.H0),
            inducedClassFunction c.H0
                (conjChar c.H0 (s_normalizes_H0 c h12) δ) =
              inducedClassFunction c.H0 δ := by
          intro δ
          ext g
          unfold inducedClassFunction
          congr 1
          refine Finset.sum_bij (fun x _ => x * c.s⁻¹) ?_ ?_ ?_ ?_
          · intro x hx
            simp
          · intro a ha b hb hab
            exact mul_right_cancel hab
          · intro y hy
            refine ⟨y * c.s, ?_, ?_⟩
            · simp
            · simp
          · intro x hx
            by_cases hmem : x⁻¹ * g * x ∈ c.H0
            · simp only [hmem, dite_true]
              have hmem' : (x * c.s⁻¹)⁻¹ * g * (x * c.s⁻¹) ∈ c.H0 := by
                simpa [mul_assoc] using
                  (s_normalizes_H0 c h12 ⟨x⁻¹ * g * x, hmem⟩)
              simp only [hmem', dite_true]
              simp [conjChar, conjMonoidHom, mul_assoc]
            · simp only [hmem, dite_false]
              have hmem' : ¬ (x * c.s⁻¹)⁻¹ * g * (x * c.s⁻¹) ∈ c.H0 := by
                intro h'
                apply hmem
                simpa [mul_assoc] using hsHinv
                  ⟨(x * c.s⁻¹)⁻¹ * g * (x * c.s⁻¹), h'⟩
              simp only [hmem', dite_false]
        have hsub : conjChar c.H0 (s_normalizes_H0 c h12) (μ.1 - ν.1) =
            conjChar c.H0 (s_normalizes_H0 c h12) μ.1 -
              conjChar c.H0 (s_normalizes_H0 c h12) ν.1 := by
          ext x
          rfl
        calc
          inducedClassFunction c.H0 (μ.1 - ν.1) =
              inducedClassFunction c.H0
                (conjChar c.H0 (s_normalizes_H0 c h12) μ.1 -
                  conjChar c.H0 (s_normalizes_H0 c h12) ν.1) := by
            rw [← hsub, hind_conj]
          _ = C.data.lift (inducedFromSub (h12.H0_normal_in_H).1 μ.1) -
              C.data.lift (inducedFromSub (h12.H0_normal_in_H).1 ν.1) := by
            rw [hθσμ, hθσν] at hdata
            exact hdata
          _ = tilde μ - tilde ν := by rw [htildeμ, htildeν]
    intro ν₁ ν₂ μ₁ μ₂ hμ₁L hμ₂L hν₁not hν₁s_not
    calc
      scalarProduct G (tilde μ₁ - tilde ν₁) (tilde μ₂ - tilde ν₂) =
          scalarProduct G
            (inducedClassFunction c.H0 (μ₁.1 - ν₁.1))
            (inducedClassFunction c.H0 (μ₂.1 - ν₂.1)) := by
        rw [h_ind μ₁ ν₁ hμ₁L, h_ind μ₂ ν₂ hμ₂L]
      _ = scalarProduct (↥c.H)
          (inducedFromSub (h12.H0_normal_in_H).1 μ₁.1 -
            inducedFromSub (h12.H0_normal_in_H).1 ν₁.1)
          (inducedFromSub (h12.H0_normal_in_H).1 μ₂.1 -
            inducedFromSub (h12.H0_normal_in_H).1 ν₂.1) :=
        delta_pair_scalar c h12 ν₁.2 ν₂.2 hμ₁L hμ₂L
      _ = 0 :=
        theta_pair_orth c h12 hH0index ν₁.2 ν₂.2 hμ₁L hμ₂L hν₁not hν₁s_not
  · -- on_T: `(ii)` plus Lemma 1.3 pointwise plus `inducedFromSub_sub`
    intro μ ν hμL g hg hgH
    have hind := tildeTheta_ind c h12 hH0index μ ν hμL
    have hstar := induced_star_eq_on_T c h12 hH0index hμL
      ⟨g, hg.1⟩ hg
    have hpoint := congrFun hind (g : G)
    rw [hpoint] at hstar
    simpa using hstar
  · -- at_t: `at_t_of_V_zero` with `exists_mu_sign_choice` and the `V = 0`
    -- input of Lemma 2.2 case 1 (`V_zero_of_pair`)
    intro ν hνs hnot
    let Θ : Finset (ClassFunction (↥c.H)) :=
      thetaOfOrbit c h12 (orbit c.H0 c.U ν.1)
    let hΘ : ∃ ξ : Irr (↥c.H0),
        thetaOfOrbit c h12 (orbit c.H0 c.U ξ.1) = Θ := ⟨ν, rfl⟩
    let C : ThetaLiftChoice c h12 Θ :=
      canonicalThetaLiftChoice c h12 hH0index Θ hΘ
    let thetaTilde : ClassFunction (↥c.H) → ClassFunction G :=
      fun θ' => C.data.lift θ'
    have hgen : ∀ θ' : ClassFunction (↥c.H), θ' ∈ Θ →
        IsGeneralizedCharacter (thetaTilde θ') := by
      intro θ' hθ'
      exact C.data.isGeneralized θ' hθ'
    have hnorm : ∀ θ' : ClassFunction (↥c.H), θ' ∈ Θ →
        normSq G (thetaTilde θ') = normSq (↥c.H) θ' := by
      intro θ' hθ'
      exact C.data.norm θ' hθ'
    have hcast : ∀ (ξ : ClassFunction (↥c.H0))
        (hξ : IsIrreducibleCharacter ξ),
        ξ ∈ orbit c.H0 c.U ν.1 →
        tildeTheta c h12 hH0index ξ hξ =
          thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 ξ) := by
      intro ξ hξ hξL
      have hξΘ : inducedFromSub (h12.H0_normal_in_H).1 ξ ∈ Θ := by
        simpa [Θ] using thetaOfOrbit_mem c h12 hξL
      dsimp only [tildeTheta, thetaTilde]
      calc
        canonicalLift c h12 hH0index
            (thetaOfOrbit c h12 (orbit c.H0 c.U ξ))
            (inducedFromSub (h12.H0_normal_in_H).1 ξ) =
            canonicalLift c h12 hH0index Θ
              (inducedFromSub (h12.H0_normal_in_H).1 ξ) := by
                exact canonicalLift_congr c h12 hH0index (by
                  dsimp [Θ]
                  rw [orbit_eq_of_mem c hξL]) rfl
        _ = C.data.lift (inducedFromSub (h12.H0_normal_in_H).1 ξ) := by
          unfold canonicalLift
          rw [dif_pos hΘ]
    have hind : ∀ {μ ν' : ClassFunction (↥c.H0)},
        μ ∈ orbit c.H0 c.U ν.1 → ν' ∈ orbit c.H0 c.U ν.1 →
        inducedClassFunction c.H0 (μ - ν') =
          thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 μ) -
            thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 ν') := by
      intro μ ν' hμL hν'L
      have hμirr : IsIrreducibleCharacter μ :=
        orbit_mem_isIrreducible c.H0 c.U ν.2 hμL
      have hν'irr : IsIrreducibleCharacter ν' :=
        orbit_mem_isIrreducible c.H0 c.U ν.2 hν'L
      have hμν'L : μ ∈ orbit c.H0 c.U ν' := by
        rw [orbit_eq_of_mem c hν'L]
        exact hμL
      have hmain := tildeTheta_ind c h12 hH0index
        ⟨μ, hμirr⟩ ⟨ν', hν'irr⟩ hμν'L
      rw [hcast μ hμirr hμL, hcast ν' hν'irr hν'L] at hmain
      simpa using hmain
    have honT : ∀ {μ ν' : ClassFunction (↥c.H0)},
        μ ∈ orbit c.H0 c.U ν.1 → ν' ∈ orbit c.H0 c.U ν.1 →
        ∀ hg : c.t ∈ c.H,
        (inducedClassFunction c.H0 (μ - ν')) c.t =
          (inducedFromSub (h12.H0_normal_in_H).1 μ) ⟨c.t, hg⟩ -
            (inducedFromSub (h12.H0_normal_in_H).1 ν') ⟨c.t, hg⟩ := by
      intro μ ν' hμL hν'L hg
      have hμν'L : μ ∈ orbit c.H0 c.U ν' := by
        rw [orbit_eq_of_mem c hν'L]
        exact hμL
      have htT : c.t ∈ c.T :=
        ⟨S0_le_H0 c c.t_mem_S0, t_not_mem_U c⟩
      have hstar := induced_star_eq_on_T c h12 hH0index hμν'L
        ⟨c.t, (tH0 c).2⟩ htT
      simpa using hstar
    have hres := theta_tilde_two_eval c h12 hH0index (ν := ν.1) ν.2 hνs hnot
      thetaTilde hgen hnorm hind honT
    have htildeν : tilde ν =
        thetaTilde (inducedFromSub (h12.H0_normal_in_H).1 ν.1) := by
      dsimp only [tilde, tildeTheta, thetaTilde]
      unfold canonicalLift
      rw [dif_pos hΘ]
    rw [htildeν]
    exact hres



/-- `ν̃`: the Coherence-Theorem map from `Irr(H0)` to generalized characters
of `G`. -/
public noncomputable def tildeNu (c : Hyp11 G) (h12 : Hyp12 c) (ν : Irr (↥c.H0)) :
    ClassFunction G :=
  (Classical.choice (exists_coherence_data c h12)).tildeNu ν

/-- Coherence Theorem 2.3(ii) for the chosen `ν̃`: `(μ−ν)* = μ̃−ν̃` for
equivalent `μ, ν`. -/
public theorem tildeNu_ind (c : Hyp11 G) (h12 : Hyp12 c)
    {μ ν : Irr (↥c.H0)} (hμν : μ.1 ∈ orbit c.H0 c.U ν.1) :
    inducedClassFunction c.H0 (μ.1 - ν.1) = tildeNu c h12 μ - tildeNu c h12 ν := by
  classical
  let D : CoherenceData c h12 := Classical.choice (exists_coherence_data c h12)
  simpa [tildeNu, D] using D.ind μ ν hμν

/-- Coherence Theorem 2.3, invariance for the chosen `ν̃`:
`ν̃^{ν^s} = ν̃`. -/
public theorem tildeNu_invariance (c : Hyp11 G) (h12 : Hyp12 c)
    (ν : Irr (↥c.H0)) : tildeNu c h12 (conjIrr c h12 ν) = tildeNu c h12 ν := by
  classical
  let D : CoherenceData c h12 := Classical.choice (exists_coherence_data c h12)
  simpa [tildeNu, D] using D.invariance ν

/-- Coherence Theorem 2.3: each `ν̃` is a generalized character of `G`. -/
public theorem tildeNu_isGeneralized (c : Hyp11 G) (h12 : Hyp12 c)
    (ν : Irr (↥c.H0)) : IsGeneralizedCharacter (tildeNu c h12 ν) := by
  classical
  let D : CoherenceData c h12 := Classical.choice (exists_coherence_data c h12)
  simpa [tildeNu, D] using D.isGeneralized ν

/-- Coherence Theorem 2.3(i) for the chosen `ν̃`: `|ν̃| = 1` or `2`
according as `ν^s ≠ ν` or `ν^s = ν`. -/
public theorem tildeNu_norm (c : Hyp11 G) (h12 : Hyp12 c)
    (ν : Irr (↥c.H0)) :
    normSq G (tildeNu c h12 ν) =
      (if conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1 then 2 else 1) := by
  classical
  let D : CoherenceData c h12 := Classical.choice (exists_coherence_data c h12)
  simpa [tildeNu, D] using (D.norm ν).2

/-- Coherence Theorem 2.3(vi) for the chosen `ν̃`: `ν̃(t) = 2ν(t)` whenever
`ν^s ≠ ν`, unless `|Λν| = 4` and `Λν^s = Λν`. -/
public theorem tildeNu_at_t (c : Hyp11 G) (h12 : Hyp12 c)
    {ν : Irr (↥c.H0)}
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 ≠ ν.1)
    (hνL : ¬ ((orbit c.H0 c.U ν.1).card = 4 ∧
      conjChar c.H0 (s_normalizes_H0 c h12) ν.1 ∈ orbit c.H0 c.U ν.1)) :
    tildeNu c h12 ν c.t = 2 * ν.1 (tH0 c) := by
  classical
  let D : CoherenceData c h12 := Classical.choice (exists_coherence_data c h12)
  simpa [tildeNu, D] using D.at_t ν hνs hνL

/-- Coherence Theorem 2.3(iii) for the chosen `ν̃`: `μ̃` and `ν̃` are
disjoint if `μ, ν` are equivalent and neither equal nor `s`-conjugate. -/
public theorem tildeNu_disjoint (c : Hyp11 G) (h12 : Hyp12 c)
    {μ ν : Irr (↥c.H0)} (hμν : μ.1 ∈ orbit c.H0 c.U ν.1)
    (hνμ : ν.1 ≠ μ.1)
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 ≠ μ.1) :
    Theory.Character.Disjoint (tildeNu c h12 μ) (tildeNu c h12 ν) := by
  classical
  let D : CoherenceData c h12 := Classical.choice (exists_coherence_data c h12)
  simpa [tildeNu, D] using D.disjoint μ ν hμν hνμ hνs

/-- Coherence Theorem 2.3(iv) for the chosen `ν̃`: for `Λ`-orbits `L₁`,
`L₂` not conjugate under `⟨s⟩`, the generalized characters `μ̃₁−ν̃₁` and
`μ̃₂−ν̃₂` are orthogonal. -/
public theorem tildeNu_orthogonal (c : Hyp11 G) (h12 : Hyp12 c)
    {ν₁ ν₂ μ₁ μ₂ : Irr (↥c.H0)}
    (hμ₁ : μ₁.1 ∈ orbit c.H0 c.U ν₁.1)
    (hμ₂ : μ₂.1 ∈ orbit c.H0 c.U ν₂.1)
    (hν₁ : ν₁.1 ∉ orbit c.H0 c.U ν₂.1)
    (hν₁s : conjChar c.H0 (s_normalizes_H0 c h12) ν₁.1 ∉ orbit c.H0 c.U ν₂.1) :
    scalarProduct G (tildeNu c h12 μ₁ - tildeNu c h12 ν₁)
      (tildeNu c h12 μ₂ - tildeNu c h12 ν₂) = 0 := by
  classical
  let D : CoherenceData c h12 := Classical.choice (exists_coherence_data c h12)
  simpa [tildeNu, D] using D.orthogonal ν₁ ν₂ μ₁ μ₂ hμ₁ hμ₂ hν₁ hν₁s

/-- Coherence Theorem 2.3(v) for the chosen `ν̃`: `μ̃−ν̃ = μ^H−ν^H` on
`T`, for equivalent `μ, ν`. -/
public theorem tildeNu_on_T (c : Hyp11 G) (h12 : Hyp12 c)
    {μ ν : Irr (↥c.H0)} (hμν : μ.1 ∈ orbit c.H0 c.U ν.1)
    (g : G) (hgT : g ∈ c.T) (hg : g ∈ c.H) :
    tildeNu c h12 μ g - tildeNu c h12 ν g =
      inducedFromSub (h12.H0_normal_in_H).1 μ.1 ⟨g, hg⟩ -
        inducedFromSub (h12.H0_normal_in_H).1 ν.1 ⟨g, hg⟩ := by
  classical
  let D : CoherenceData c h12 := Classical.choice (exists_coherence_data c h12)
  simpa [tildeNu, D] using D.on_T μ ν hμν g hgT hg

/-- `B(χ)`: the set of `ν ∈ Irr(H0)` with `(χ, ν̃)_G ≠ 0`. -/
public noncomputable def BOf (c : Hyp11 G) (h12 : Hyp12 c) (χ : ClassFunction G) :
    Finset (Irr (↥c.H0)) := by
  classical
  exact Finset.univ.filter (fun ν : Irr (↥c.H0) => scalarProduct G χ (tildeNu c h12 ν) ≠ 0)

/-- Membership in `B(χ)`: `ν ∈ B(χ)` iff `(χ, ν̃)_G ≠ 0`. -/
public theorem BOf_mem_iff (c : Hyp11 G) (h12 : Hyp12 c) (χ : ClassFunction G)
    (ν : Irr (↥c.H0)) : ν ∈ BOf c h12 χ ↔ scalarProduct G χ (tildeNu c h12 ν) ≠ 0 := by
  classical
  simp [BOf]

/-- For `χ ∈ ±Irr(G)` and `ν ∈ B(χ)`, `(χ, ν̃)_G = ±1`. -/
public theorem BOf_scalar_eq_pm_one (c : Hyp11 G) (h12 : Hyp12 c) {χ : ClassFunction G}
    (hχ : IsPMIrr G χ) {ν : Irr (↥c.H0)} (hν : ν ∈ BOf c h12 χ) :
    scalarProduct G χ (tildeNu c h12 ν) = 1 ∨ scalarProduct G χ (tildeNu c h12 ν) = -1 := by
  classical
  have hpair_ne : scalarProduct G χ (tildeNu c h12 ν) ≠ 0 := by
    simpa [BOf] using hν
  let D : CoherenceData c h12 := Classical.choice (exists_coherence_data c h12)
  have hgen : IsGeneralizedCharacter (tildeNu c h12 ν) := by
    simpa [tildeNu, D] using D.isGeneralized ν
  have hnorm : normSq G (tildeNu c h12 ν) =
      (if conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1 then 2 else 1) := by
    simpa [tildeNu, D] using (D.norm ν).2
  by_cases hfix : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1
  · have hnorm2 : normSq G (tildeNu c h12 ν) = 2 := by simpa [hfix] using hnorm
    have hmem := scalarProduct_norm_one_signed_norm_two_mem hχ hgen hnorm2
    rcases hmem with h1 | h0 | hm1
    · exact Or.inl h1
    · exact False.elim (hpair_ne h0)
    · exact Or.inr hm1
  · have hnorm1 : normSq G (tildeNu c h12 ν) = 1 := by simpa [hfix] using hnorm
    have hnorm1' : scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 ν) = 1 := by
      simpa [normSq] using hnorm1
    rcases norm_one_signed_irreducible hgen hnorm1' with ⟨ψ, hψ, hψeq⟩
    have hmem : scalarProduct G χ (tildeNu c h12 ν) = 1 ∨
        scalarProduct G χ (tildeNu c h12 ν) = 0 ∨
        scalarProduct G χ (tildeNu c h12 ν) = -1 := by
      rcases hψeq with hψeq | hψeq
      · rw [hψeq]
        exact scalarProduct_signed_irr_signed_irr_mem hχ (Or.inl hψ)
      · rw [hψeq]
        rw [scalarProduct_neg_right]
        rcases scalarProduct_signed_irr_signed_irr_mem hχ (Or.inl hψ) with h1 | h0 | hm1
        · exact Or.inr (Or.inr (by simpa [h1]))
        · exact Or.inr (Or.inl (by simpa [h0]))
        · exact Or.inl (by simpa [hm1])
    rcases hmem with h1 | h0 | hm1
    · exact Or.inl h1
    · exact False.elim (hpair_ne h0)
    · exact Or.inr hm1

/-- `B(χ)` is invariant under `s`. -/
public theorem BOf_conj_iff (c : Hyp11 G) (h12 : Hyp12 c) (χ : ClassFunction G)
    (ν : Irr (↥c.H0)) :
    conjIrr c h12 ν ∈ BOf c h12 χ ↔ ν ∈ BOf c h12 χ := by
  classical
  let D : CoherenceData c h12 := Classical.choice (exists_coherence_data c h12)
  have hinv : tildeNu c h12 (conjIrr c h12 ν) = tildeNu c h12 ν := by
    simpa [tildeNu, D] using D.invariance ν
  simp only [BOf, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hinv]

/-- `B(χ)` intersects each `Λ`-orbit in at most two characters. -/
public theorem BOf_orbit_card_le_two (c : Hyp11 G) (h12 : Hyp12 c) (χ : ClassFunction G)
    (hχ : IsPMIrr G χ)
    (ν : Irr (↥c.H0)) :
    ((BOf c h12 χ).filter (fun μ : Irr (↥c.H0) => μ.1 ∈ orbit c.H0 c.U ν.1)).card ≤ 2 := by
  classical
  let D : CoherenceData c h12 := Classical.choice (exists_coherence_data c h12)
  have conj_eq_of_mem (a b : Irr (↥c.H0))
      (haB : a ∈ BOf c h12 χ) (hbB : b ∈ BOf c h12 χ)
      (haL : a.1 ∈ orbit c.H0 c.U ν.1) (hbL : b.1 ∈ orbit c.H0 c.U ν.1)
      (hab : a ≠ b) :
      conjChar c.H0 (s_normalizes_H0 c h12) a.1 = b.1 := by
    by_contra habs
    have hbaL : b.1 ∈ orbit c.H0 c.U a.1 := by
      rw [orbit_eq_of_mem c haL]
      exact hbL
    have hab' : a.1 ≠ b.1 := by
      intro h
      exact hab (Subtype.ext h)
    have hdisj : Theory.Character.Disjoint (tildeNu c h12 b) (tildeNu c h12 a) := by
      simpa [tildeNu, D] using D.disjoint b a hbaL hab' habs
    have haPair : scalarProduct G χ (tildeNu c h12 a) ≠ 0 := by
      simpa [BOf] using haB
    have hbPair : scalarProduct G χ (tildeNu c h12 b) ≠ 0 := by
      simpa [BOf] using hbB
    rcases hχ with hχ | hχ
    · exact haPair (hdisj χ hχ hbPair)
    · have haPairNeg : scalarProduct G (-χ) (tildeNu c h12 a) ≠ 0 := by
        rw [scalarProduct_neg_left]
        exact neg_ne_zero.mpr haPair
      have hbPairNeg : scalarProduct G (-χ) (tildeNu c h12 b) ≠ 0 := by
        rw [scalarProduct_neg_left]
        exact neg_ne_zero.mpr hbPair
      exact haPairNeg (hdisj (-χ) hχ hbPairNeg)
  by_contra hcard
  have hgt : 2 <
      ((BOf c h12 χ).filter
        (fun μ : Irr (↥c.H0) => μ.1 ∈ orbit c.H0 c.U ν.1)).card := by
    omega
  rcases Finset.two_lt_card.mp hgt with
    ⟨a, ha, b, hb, d, hd, hab, had, hbd⟩
  have ha' := Finset.mem_filter.mp ha
  have hb' := Finset.mem_filter.mp hb
  have hd' := Finset.mem_filter.mp hd
  have habs := conj_eq_of_mem a b ha'.1 hb'.1 ha'.2 hb'.2 hab
  have hads := conj_eq_of_mem a d ha'.1 hd'.1 ha'.2 hd'.2 had
  apply hbd
  exact Subtype.ext (habs.symm.trans hads)


end Section2

end CFSG.BenderGlauberman
