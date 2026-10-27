module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section2.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section2.Coherence
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section2.Lemma22
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section2.Lemma24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section3.Remark31
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section3.Theorem32
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section3.Lemma33
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Lemma19
import all CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Lemma19
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.ClassFunction
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

namespace CFSG
end CFSG
open CFSG

/-!
# Bender--Glauberman: Section 3 — Lemma 3.4

Lemma 3.4: if `B(χ)` contains a character `ν` not fixed by `s` with
`ν^s ∉ Λν` or `|Λν| = m`, then `B(χ) = {ν, ν^s}` and
`ν̃(t) = 2ν(t)`.
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

/-! ## The `B(χ) = {ν,ν^s}` ⟺ `ν̃(t) = 2ν(t)` equivalence

Both assertions are equivalent under `ν ∈ B(χ)`, `ν^s ≠ ν` (Lemma 2.4's
`T`-expansion at the central involution `t`, `|B(χ)| ≤ 3`, and the
fact that `χ = ±ν̃`).  This is the paper's "By Lemma 2.4 and
`|B(χ)| ≤ 3`, our two assertions are equivalent" step (L758).
-/

/-- `ν^s(t) = ν(t)` for the central involution `t` (`s` fixes `t`). -/
private lemma conjIrr_apply_tH0_eq (c : Hyp11 G) (h12 : Hyp12 c)
    (ν : Irr (↥c.H0)) :
    (conjIrr c h12 ν).1 (tH0 c) = ν.1 (tH0 c) := by
  rw [conjIrr_coe]
  change ν.1 (conjMonoidHom c.H0 c.s (s_normalizes_H0 c h12) (tH0 c)) = ν.1 (tH0 c)
  have h : conjMonoidHom c.H0 c.s (s_normalizes_H0 c h12) (tH0 c) = tH0 c := by
    apply Subtype.ext
    change c.s * c.t * c.s⁻¹ = c.t
    exact s_conj_t c
  rw [h]

/-- Two signed irreducibles with a nonzero scalar product are equal up to the
sign of the coefficient: `χ = (χ,ψ) • ψ` whenever `ψ` is a signed irreducible
of norm one and `(χ,ψ) ≠ 0`. -/
private lemma signed_irr_eq_smul_of_pairing_ne {G : Type u} [Group G] [Fintype G]
    {χ ψ : ClassFunction G} (hχ : IsPMIrr G χ)
    (hψ : IsIrreducibleCharacter ψ)
    (hne : scalarProduct G χ ψ ≠ 0) :
    χ = scalarProduct G χ ψ • ψ := by
  classical
  have hχg : IsGeneralizedCharacter χ := by
    rcases hχ with hχ | hχneg
    · exact ⟨χ, 0, isCharacter_of_isIrreducibleCharacter hχ, isCharacter_zero, by simp⟩
    · exact ⟨0, -χ, isCharacter_zero, isCharacter_of_isIrreducibleCharacter hχneg, by simp⟩
  have hχself : scalarProduct G χ χ = 1 := by
    rcases hχ with hχ | hχneg
    · exact scalarProduct_irreducible_self hχ
    · have h' : scalarProduct G (-χ) (-χ) = 1 := scalarProduct_irreducible_self hχneg
      rw [scalarProduct_neg_left, scalarProduct_neg_right] at h'
      simpa using h'
  rcases norm_one_signed_irreducible hχg hχself with ⟨ψ₀, hψ₀, hχeq⟩
  have hψ₀eq : ψ₀ = ψ := by
    by_contra h
    rcases hχeq with hχeq | hχeq
    · have h' : scalarProduct G χ ψ = 0 := by
        rw [hχeq]
        simpa [scalarProduct_irr_ite hψ₀ hψ, h]
      exact hne h'
    · have h' : scalarProduct G χ ψ = 0 := by
        rw [hχeq]
        rw [scalarProduct_neg_left]
        simpa [scalarProduct_irr_ite hψ₀ hψ, h]
      exact hne h'
  rcases hχeq with hχeq | hχeq
  · -- `χ = ψ₀ = ψ` and the coefficient is `1`
    have h1 : scalarProduct G χ ψ = 1 := by
      rw [hχeq, hψ₀eq]
      exact scalarProduct_irreducible_self hψ
    rw [h1, hχeq, hψ₀eq]
    simp
  · -- `χ = -ψ₀ = -ψ` and the coefficient is `-1`
    have h1 : scalarProduct G χ ψ = -1 := by
      rw [hχeq, hψ₀eq]
      rw [scalarProduct_neg_left]
      simp [scalarProduct_irreducible_self hψ]
    rw [h1, hχeq, hψ₀eq]
    simp

/-- Since `ν ∈ B(χ)` and `ν^s ≠ ν`, `ν̃` is a signed irreducible and
`χ = (χ,ν̃) • ν̃` pointwise. -/
private lemma chi_eq_smul_tildeNu (c : Hyp11 G) (h12 : Hyp12 c)
    {χ : ClassFunction G} (hχ : IsPMIrr G χ) {ν : Irr (↥c.H0)}
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 ≠ ν.1)
    (hνB : ν ∈ BOf c h12 χ) :
    χ = scalarProduct G χ (tildeNu c h12 ν) • tildeNu c h12 ν := by
  classical
  have hgen : IsGeneralizedCharacter (tildeNu c h12 ν) :=
    tildeNu_isGeneralized c h12 ν
  have hnorm : normSq G (tildeNu c h12 ν) = 1 := by
    rw [tildeNu_norm c h12 ν]
    simp [hνs]
  have hnorm1 : scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 ν) = 1 := by
    simpa [normSq] using hnorm
  rcases norm_one_signed_irreducible hgen hnorm1 with ⟨ψ, hψ, hψeq⟩
  have hne : scalarProduct G χ (tildeNu c h12 ν) ≠ 0 := by
    exact (BOf_mem_iff c h12 χ ν).1 hνB
  rcases hψeq with hψeq | hψeq
  · -- ν̃ = ψ
    have hne' : scalarProduct G χ ψ ≠ 0 := by simpa [hψeq] using hne
    have hEq := signed_irr_eq_smul_of_pairing_ne (hχ := hχ) (hψ := hψ) hne'
    simpa [hψeq] using hEq
  · -- ν̃ = -ψ
    have hne' : scalarProduct G χ (-ψ) ≠ 0 := by simpa [hψeq] using hne
    have hEq := signed_irr_eq_smul_of_pairing_ne (hχ := hχ) (hψ := hψ)
      (by
        have h' : scalarProduct G χ (-ψ) = -scalarProduct G χ ψ := by
          rw [scalarProduct_neg_right]
        have h'' : scalarProduct G χ ψ ≠ 0 := by
          intro h0
          apply hne'
          rw [h']
          rw [h0]
          norm_num
        exact h''
      )
    have h'' : scalarProduct G χ (tildeNu c h12 ν) • tildeNu c h12 ν =
        scalarProduct G χ ψ • ψ := by
      rw [hψeq]
      rw [scalarProduct_neg_right]
      simp [smul_neg, neg_smul, neg_neg]
    calc
      χ = scalarProduct G χ ψ • ψ := hEq
      _ = scalarProduct G χ (tildeNu c h12 ν) • tildeNu c h12 ν := h''.symm

/-- `t` belongs to the TI-set `T` and to `H0`. -/
private lemma t_mem_T_H0 (c : Hyp11 G) : c.t ∈ c.T ∧ c.t ∈ c.H0 := by
  exact ⟨⟨S0_le_H0 c c.t_mem_S0, t_not_mem_U c⟩, S0_le_H0 c c.t_mem_S0⟩

/-- A finset of cardinality at most three containing two distinct elements
`a,b` but not equal to `{a,b}` contains a third element `c`. -/
private lemma exists_third_of_card_le_three {α : Type u} [DecidableEq α]
    (s : Finset α) (a b : α) (has : a ∈ s) (hbs : b ∈ s) (hab : a ≠ b)
    (hne : s ≠ {a, b}) (hcard : s.card ≤ 3) :
    ∃ c : α, c ∈ s ∧ c ≠ a ∧ c ≠ b ∧ s = {a, b, c} := by
  classical
  have hsub : {a, b} ⊆ s := by
    intro x hx
    simp at hx
    rcases hx with rfl | rfl
    · exact has
    · exact hbs
  have h3 : 3 ≤ s.card := by
    by_contra hlt
    have hle2 : s.card ≤ 2 := by omega
    have hsubs : s ⊆ {a, b} := by
      intro x hx
      by_contra hxab
      have hxa : x ≠ a := by
        intro h
        exact hxab (by simp [h])
      have hxb : x ≠ b := by
        intro h
        exact hxab (by simp [h])
      have hsub3 : ({a, b, x} : Finset α) ⊆ s := by
        intro y hy
        simp at hy
        rcases hy with hy | hy | hy
        · exact hy ▸ has
        · exact hy ▸ hbs
        · exact hy ▸ hx
      have h3' : 3 ≤ s.card := by
        have hc3 : ({a, b, x} : Finset α).card = 3 := by
          rw [Finset.card_insert_of_notMem (by
            intro hm
            simp only [Finset.mem_insert, Finset.mem_singleton] at hm
            rcases hm with hm | hm
            · exact hab hm
            · exact hxa hm.symm)]
          rw [Finset.card_insert_of_notMem (by
            intro hm
            simp only [Finset.mem_singleton] at hm
            exact hxb hm.symm)]
          simp
        rw [← hc3]
        exact Finset.card_le_card hsub3
      omega
    have h1 : s = {a, b} := by
      apply Finset.eq_of_subset_of_card_le hsubs
      have hpair : ({a, b} : Finset α).card = 2 := by simp [hab]
      simpa [hpair] using Finset.card_le_card hsub
    exact hne h1
  have hcard3 : s.card = 3 := by omega
  have hsd : (s \ ({a, b} : Finset α)).card = 1 := by
    rw [Finset.card_sdiff]
    rw [hcard3]
    have hpair : ({a, b} : Finset α).card = 2 := by simp [hab]
    have hint : ({a, b} : Finset α) ∩ s = ({a, b} : Finset α) := by
      exact Finset.inter_eq_left.mpr hsub
    rw [hint, hpair]
  rcases Finset.card_eq_one.mp hsd with ⟨d, hd⟩
  have hd' : d ∈ s ∧ d ∉ ({a, b} : Finset α) := by
    have hmem : d ∈ s \ ({a, b} : Finset α) := by
      rw [hd]
      simp
    exact Finset.mem_sdiff.mp hmem
  have hda : d ≠ a := by
    intro h
    exact hd'.2 (by simp [h])
  have hdb : d ≠ b := by
    intro h
    exact hd'.2 (by simp [h])
  refine ⟨d, hd'.1, hda, hdb, ?_⟩
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    by_contra hxnot
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxnot
    have hxa : x ≠ a := by
      intro h
      exact hxnot (Or.inl h)
    have hxb : x ≠ b := by
      intro h
      exact hxnot (Or.inr (Or.inl h))
    have hxd : x ≠ d := by
      intro h
      exact hxnot (Or.inr (Or.inr h))
    have hsub4 : ({a, b, d, x} : Finset α) ⊆ s := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with hy | hy | hy | hy
      · exact hy ▸ has
      · exact hy ▸ hbs
      · exact hy ▸ hd'.1
      · exact hy ▸ hx
    have h4 : 4 ≤ s.card := by
      have hc4 : ({a, b, d, x} : Finset α).card = 4 := by
        rw [Finset.card_insert_of_notMem (by
          intro hm
          simp only [Finset.mem_insert, Finset.mem_singleton] at hm
          rcases hm with hm | hm | hm
          · exact hab hm
          · exact hda hm.symm
          · exact hxa hm.symm)]
        rw [Finset.card_insert_of_notMem (by
          intro hm
          simp only [Finset.mem_insert, Finset.mem_singleton] at hm
          rcases hm with hm | hm
          · exact hdb hm.symm
          · exact hxb hm.symm)]
        rw [Finset.card_insert_of_notMem (by
          intro hm
          simp only [Finset.mem_singleton] at hm
          exact hxd hm.symm)]
        simp
      rw [← hc4]
      exact Finset.card_le_card hsub4
    omega
  · have hc3 : ({a, b, d} : Finset α).card = 3 := by
      rw [Finset.card_insert_of_notMem (by
        intro hm
        simp only [Finset.mem_insert, Finset.mem_singleton] at hm
        rcases hm with hm | hm
        · exact hab hm
        · exact hda hm.symm)]
      rw [Finset.card_insert_of_notMem (by
        intro hm
        simp only [Finset.mem_singleton] at hm
        exact hdb hm.symm)]
      simp
    rw [hcard3, hc3]

/-- If `B(χ) = {ν, ν^s}`, then `ν̃(t) = 2ν(t)`. -/
private lemma BOf_eq_pair_of_pair_implies_tilde_two (c : Hyp11 G) (h12 : Hyp12 c)
    {χ : ClassFunction G} (hχ : IsPMIrr G χ) {ν : Irr (↥c.H0)}
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 ≠ ν.1)
    (hνB : ν ∈ BOf c h12 χ)
    (hB : BOf c h12 χ = {ν, conjIrr c h12 ν}) :
    tildeNu c h12 ν c.t = 2 * ν.1 (tH0 c) := by
  classical
  have hchi : χ = scalarProduct G χ (tildeNu c h12 ν) • tildeNu c h12 ν :=
    chi_eq_smul_tildeNu c h12 hχ hνs hνB
  have h24 := (lemma_2_4 c h12 hχ).1
  have htmem : c.t ∈ c.T := (t_mem_T_H0 c).1
  have htH0 : c.t ∈ c.H0 := (t_mem_T_H0 c).2
  have ht := h24 c.t htmem htH0
  have hνne : ν ≠ conjIrr c h12 ν := by
    intro h
    apply hνs
    have h' := congrArg Subtype.val h
    simpa [conjIrr_coe] using h'.symm
  have hsum : (∑ μ ∈ BOf c h12 χ, scalarProduct G χ (tildeNu c h12 μ) * μ.1 ⟨c.t, htH0⟩) =
      scalarProduct G χ (tildeNu c h12 ν) * ν.1 (tH0 c) +
        scalarProduct G χ (tildeNu c h12 ν) * ν.1 (tH0 c) := by
    rw [hB]
    rw [Finset.sum_pair hνne]
    have hconj : scalarProduct G χ (tildeNu c h12 (conjIrr c h12 ν)) =
        scalarProduct G χ (tildeNu c h12 ν) := by
      rw [tildeNu_invariance]
    have hvt : (conjIrr c h12 ν).1 ⟨c.t, htH0⟩ = ν.1 (tH0 c) := by
      change (conjIrr c h12 ν).1 (tH0 c) = ν.1 (tH0 c)
      exact conjIrr_apply_tH0_eq c h12 ν
    rw [hconj, hvt]
    have hvt' : ν.1 ⟨c.t, htH0⟩ = ν.1 (tH0 c) := rfl
    rw [hvt']
  have hχt : χ c.t = 2 * scalarProduct G χ (tildeNu c h12 ν) * ν.1 (tH0 c) := by
    rw [ht, hsum]
    ring
  have hnt : tildeNu c h12 ν c.t = scalarProduct G χ (tildeNu c h12 ν) * χ c.t := by
    have h' := congrFun hchi c.t
    rw [h']
    simp [Pi.smul_apply]
    rcases BOf_scalar_eq_pm_one c h12 hχ hνB with h1 | hm1
    · rw [h1]
      norm_num
    · rw [hm1]
      norm_num
  rw [hnt, hχt]
  have he : scalarProduct G χ (tildeNu c h12 ν) *
      (2 * scalarProduct G χ (tildeNu c h12 ν) * ν.1 (tH0 c)) = 2 * ν.1 (tH0 c) := by
    rcases BOf_scalar_eq_pm_one c h12 hχ hνB with h1 | hm1
    · rw [h1]
      norm_num
    · rw [hm1]
      norm_num
  exact he

/-- If `ν̃(t) = 2ν(t)` and `ν ∈ B(χ)`, then `B(χ) = {ν, ν^s}`. -/
private lemma tilde_two_implies_BOf_eq_pair (c : Hyp11 G) (h12 : Hyp12 c)
    (hSC : Section3Hyp c) {χ : ClassFunction G} (hχ : IsPMIrr G χ)
    {ν : Irr (↥c.H0)}
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 ≠ ν.1)
    (hνB : ν ∈ BOf c h12 χ)
    (hT : tildeNu c h12 ν c.t = 2 * ν.1 (tH0 c)) :
    BOf c h12 χ = {ν, conjIrr c h12 ν} := by
  classical
  by_contra hBne
  have hchi : χ = scalarProduct G χ (tildeNu c h12 ν) • tildeNu c h12 ν :=
    chi_eq_smul_tildeNu c h12 hχ hνs hνB
  have hνsB : conjIrr c h12 ν ∈ BOf c h12 χ := (BOf_conj_iff c h12 χ ν).2 hνB
  have hνne : ν ≠ conjIrr c h12 ν := by
    intro h
    apply hνs
    have h' := congrArg Subtype.val h
    simpa [conjIrr_coe] using h'.symm
  have hcard := theorem_3_2 c h12 hSC hχ
  rcases exists_third_of_card_le_three (BOf c h12 χ) ν (conjIrr c h12 ν)
    hνB hνsB hνne hBne hcard with ⟨μ, hμB, hμν, hμνs, hB⟩
  have h24 := (lemma_2_4 c h12 hχ).1
  have htmem : c.t ∈ c.T := (t_mem_T_H0 c).1
  have htH0 : c.t ∈ c.H0 := (t_mem_T_H0 c).2
  have ht := h24 c.t htmem htH0
  have hsum : (∑ η ∈ BOf c h12 χ, scalarProduct G χ (tildeNu c h12 η) * η.1 ⟨c.t, htH0⟩) =
      scalarProduct G χ (tildeNu c h12 ν) * ν.1 (tH0 c) +
        scalarProduct G χ (tildeNu c h12 ν) * ν.1 (tH0 c) +
          scalarProduct G χ (tildeNu c h12 μ) * μ.1 (tH0 c) := by
    rw [hB]
    rw [Finset.sum_insert (by
      intro hm
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with hm | hm
      · exact hνne hm
      · exact hμν hm.symm)]
    rw [Finset.sum_insert (by
      intro hm
      simp only [Finset.mem_singleton] at hm
      exact hμνs hm.symm)]
    rw [Finset.sum_singleton]
    have hconj : scalarProduct G χ (tildeNu c h12 (conjIrr c h12 ν)) =
        scalarProduct G χ (tildeNu c h12 ν) := by
      rw [tildeNu_invariance]
    have hvt : (conjIrr c h12 ν).1 ⟨c.t, htH0⟩ = ν.1 (tH0 c) := by
      change (conjIrr c h12 ν).1 (tH0 c) = ν.1 (tH0 c)
      exact conjIrr_apply_tH0_eq c h12 ν
    have hvt' : ν.1 ⟨c.t, htH0⟩ = ν.1 (tH0 c) := rfl
    have hμt : μ.1 ⟨c.t, htH0⟩ = μ.1 (tH0 c) := rfl
    rw [hconj, hvt, hvt', hμt]
    ring
  have hχt : χ c.t =
      2 * scalarProduct G χ (tildeNu c h12 ν) * ν.1 (tH0 c) +
        scalarProduct G χ (tildeNu c h12 μ) * μ.1 (tH0 c) := by
    rw [ht, hsum]
    ring
  have hnt : tildeNu c h12 ν c.t = scalarProduct G χ (tildeNu c h12 ν) * χ c.t := by
    have h' := congrFun hchi c.t
    rw [h']
    simp [Pi.smul_apply]
    rcases BOf_scalar_eq_pm_one c h12 hχ hνB with h1 | hm1
    · rw [h1]
      norm_num
    · rw [hm1]
      norm_num
  have hT' : scalarProduct G χ (tildeNu c h12 ν) * χ c.t = 2 * ν.1 (tH0 c) := by
    rwa [hnt] at hT
  have hμt : μ.1 (tH0 c) = 0 := by
    rw [hχt] at hT'
    rcases BOf_scalar_eq_pm_one c h12 hχ hνB with h1 | hm1
    · rcases BOf_scalar_eq_pm_one c h12 hχ hμB with h2 | hm2
      · rw [h1, h2] at hT'
        linear_combination hT'
      · rw [h1, hm2] at hT'
        linear_combination -hT'
    · rcases BOf_scalar_eq_pm_one c h12 hχ hμB with h2 | hm2
      · rw [hm1, h2] at hT'
        linear_combination -hT'
      · rw [hm1, hm2] at hT'
        linear_combination hT'
  have hμt0 : μ.1 (tH0 c) ≠ 0 := char_apply_central_ne_zero
    (G := ↥c.H0) (t := tH0 c)
    (by simpa [tH0] using t_central_H0' c) (t_H0_sq c) μ.2
  exact hμt0 hμt

/-- The two assertions of Lemma 3.4 are equivalent:
`B(χ) = {ν,ν^s}` iff `ν̃(t) = 2ν(t)`. -/
private lemma BOf_eq_pair_iff_tilde_two (c : Hyp11 G) (h12 : Hyp12 c)
    (hSC : Section3Hyp c) {χ : ClassFunction G} (hχ : IsPMIrr G χ)
    {ν : Irr (↥c.H0)}
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 ≠ ν.1)
    (hνB : ν ∈ BOf c h12 χ) :
    BOf c h12 χ = {ν, conjIrr c h12 ν} ↔ tildeNu c h12 ν c.t = 2 * ν.1 (tH0 c) := by
  constructor
  · exact BOf_eq_pair_of_pair_implies_tilde_two c h12 hχ hνs hνB
  · exact tilde_two_implies_BOf_eq_pair c h12 hSC hχ hνs hνB

/-! ## The false-branch setup

If the two assertions fail, `B(χ) = {ν,ν^s,μ}` for a third character `μ`,
and Theorem 2.3(vi) (`tildeNu_at_t`) gives the exceptional configuration
`ν^s ∈ Λν`, `|Λν| = 4`; the hypothesis `|Λν| = m` then forces `m = 4`
(`|S0| = 4`) and `|S| = 8`.  This is the paper's L758–L762 step.
-/

/-- `|Λ| = |S0|`: the index of `U` in `H0` equals the order of `S0`
(`H0 = U ⋊ S0`). -/
private lemma U_index_eq_S0_card (c : Hyp11 G) (h12 : Hyp12 c) :
    (c.U.subgroupOf c.H0).index = Nat.card (c.S0 : Subgroup G) := by
  classical
  let f : ↥c.U × ↥c.S0 → ↥c.H0 := fun p =>
    ⟨(p.1 : G) * (p.2 : G), c.H0.mul_mem ((h12.U_normal_in_H0).1 p.1.2) (S0_le_H0 c p.2.2)⟩
  have hinj : Function.Injective f := by
    intro p q hEq
    have hEq' : (p.1 : G) * (p.2 : G) = (q.1 : G) * (q.2 : G) := congrArg Subtype.val hEq
    have h₁ : (q.1 : G)⁻¹ * (p.1 : G) = (q.2 : G) * (p.2 : G)⁻¹ := by
      calc
        (q.1 : G)⁻¹ * (p.1 : G) = (q.1 : G)⁻¹ * ((p.1 : G) * (p.2 : G)) * (p.2 : G)⁻¹ := by group
        _ = (q.1 : G)⁻¹ * ((q.1 : G) * (q.2 : G)) * (p.2 : G)⁻¹ := by rw [hEq']
        _ = (q.2 : G) * (p.2 : G)⁻¹ := by group
    have hU : (q.1 : G)⁻¹ * (p.1 : G) ∈ c.U := (c.U).mul_mem ((c.U).inv_mem q.1.2) p.1.2
    have hS0 : (q.2 : G) * (p.2 : G)⁻¹ ∈ c.S0 := (c.S0).mul_mem q.2.2 ((c.S0).inv_mem p.2.2)
    have honeU : (q.1 : G)⁻¹ * (p.1 : G) = 1 := U_inter_S0_eq_bot c hU (by
      rw [h₁]
      exact hS0)
    have hS0inU : (q.2 : G) * (p.2 : G)⁻¹ ∈ c.U := by
      rw [← h₁]
      exact hU
    have honeS : (q.2 : G) * (p.2 : G)⁻¹ = 1 := U_inter_S0_eq_bot c hS0inU hS0
    apply Prod.ext
    · apply Subtype.ext
      exact mul_left_cancel (a := (q.1 : G)⁻¹) (by
        calc
          (q.1 : G)⁻¹ * (p.1 : G) = 1 := honeU
          _ = (q.1 : G)⁻¹ * (q.1 : G) := by group)
    · apply Subtype.ext
      exact (calc
        (q.2 : G) = (q.2 : G) * (p.2 : G)⁻¹ * (p.2 : G) := by group
        _ = (p.2 : G) := by rw [honeS]; simp).symm
  have hsurj : ∀ x : ↥c.H0, ∃ p : ↥c.U × ↥c.S0, f p = x := by
    intro x
    rcases H0_eq_U_mul_S0 c h12 (x := x) with ⟨u, r, hEq⟩
    refine ⟨(u, r), ?_⟩
    apply Subtype.ext
    exact hEq.symm
  have hcardcong : Nat.card (↥c.H0) = Nat.card (↥c.U) * Nat.card (↥c.S0) := by
    let e : ↥c.U × ↥c.S0 ≃ ↥c.H0 := Equiv.ofBijective f ⟨hinj, hsurj⟩
    have hc : Nat.card (↥c.U × ↥c.S0) = Nat.card (↥c.H0) := Nat.card_congr e
    rw [← hc]
    simp
  have hUcard : Nat.card (↥(c.U.subgroupOf c.H0)) = Nat.card (↥c.U) := by
    exact Nat.card_congr {
      toFun := fun x : ↥(c.U.subgroupOf c.H0) => ⟨(x : G), Subgroup.mem_subgroupOf.mp x.2⟩
      invFun := fun y : ↥c.U => ⟨⟨(y : G), (h12.U_normal_in_H0).1 y.2⟩,
        Subgroup.mem_subgroupOf.mpr y.2⟩
      left_inv := by intro x; apply Subtype.ext; rfl
      right_inv := by intro y; apply Subtype.ext; rfl }
  have hcm := Subgroup.card_mul_index (c.U.subgroupOf c.H0)
  have h1 : (c.U.subgroupOf c.H0).index * Nat.card (↥c.U) = Nat.card (↥c.H0) := by
    rw [← hUcard]
    rw [mul_comm]
    exact hcm
  have h2 : Nat.card (↥c.S0) * Nat.card (↥c.U) = Nat.card (↥c.H0) := by
    calc
      Nat.card (↥c.S0) * Nat.card (↥c.U) = Nat.card (↥c.U) * Nat.card (↥c.S0) := by rw [mul_comm]
      _ = Nat.card (↥c.H0) := hcardcong.symm
  exact mul_right_cancel₀ (b := Nat.card (↥c.U)) (Nat.card_pos (α := ↥c.U)).ne' (by
    calc
      (c.U.subgroupOf c.H0).index * Nat.card (↥c.U) = Nat.card (↥c.H0) := h1
      _ = Nat.card (↥c.S0) * Nat.card (↥c.U) := h2.symm)

/-- The false branch: a third character `μ`, the negated `t`-value, the
Coherence-(vi) exception `ν^s ∈ Λν` with `|Λν| = 4`, hence `m = 4` and
`|S| = 8`. -/
private lemma false_branch_setup (c : Hyp11 G) (h12 : Hyp12 c) (hSC : Section3Hyp c)
    {χ : ClassFunction G} (hχ : IsPMIrr G χ) {ν : Irr (↥c.H0)}
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 ≠ ν.1)
    (hνB : ν ∈ BOf c h12 χ)
    (hνL : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 ∉ orbit c.H0 c.U ν.1 ∨
      (orbit c.H0 c.U ν.1).card = (c.U.subgroupOf c.H0).index)
    (hBne : BOf c h12 χ ≠ {ν, conjIrr c h12 ν}) :
    ∃ μ : Irr (↥c.H0),
      μ ∈ BOf c h12 χ ∧ μ ≠ ν ∧ μ ≠ conjIrr c h12 ν ∧
      BOf c h12 χ = {ν, conjIrr c h12 ν, μ} ∧
      tildeNu c h12 ν c.t ≠ 2 * ν.1 (tH0 c) ∧
      conjChar c.H0 (s_normalizes_H0 c h12) ν.1 ∈ orbit c.H0 c.U ν.1 ∧
      (orbit c.H0 c.U ν.1).card = 4 ∧
      (c.U.subgroupOf c.H0).index = 4 ∧
      Nat.card (↥(c.S : Subgroup G)) = 8 := by
  classical
  have hνsB : conjIrr c h12 ν ∈ BOf c h12 χ := (BOf_conj_iff c h12 χ ν).2 hνB
  have hνne : ν ≠ conjIrr c h12 ν := by
    intro h
    apply hνs
    have h' := congrArg Subtype.val h
    simpa [conjIrr_coe] using h'.symm
  have hcard := theorem_3_2 c h12 hSC hχ
  rcases exists_third_of_card_le_three (BOf c h12 χ) ν (conjIrr c h12 ν)
    hνB hνsB hνne hBne hcard with ⟨μ, hμB, hμν, hμνs, hB⟩
  have hTfalse : tildeNu c h12 ν c.t ≠ 2 * ν.1 (tH0 c) := by
    intro hT
    exact hBne ((BOf_eq_pair_iff_tilde_two c h12 hSC hχ hνs hνB).2 hT)
  have hEx : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 ∈ orbit c.H0 c.U ν.1 ∧
      (orbit c.H0 c.U ν.1).card = 4 := by
    by_contra hnot
    apply hTfalse
    exact tildeNu_at_t c h12 hνs (by
      intro h
      exact hnot ⟨h.2, h.1⟩)
  have hindex : (c.U.subgroupOf c.H0).index = 4 := by
    have hL : (conjIrr c h12 ν).1 ∉ orbit c.H0 c.U ν.1 ∨
        (orbit c.H0 c.U ν.1).card = (c.U.subgroupOf c.H0).index := by
      simpa [conjIrr_coe] using hνL
    rcases hL with hleft | hright
    · exact False.elim (hleft (by simpa [conjIrr_coe] using hEx.1))
    · rw [← hright]
      exact hEx.2
  have hS : Nat.card (↥(c.S : Subgroup G)) = 8 := by
    have hS0 : Nat.card (c.S0 : Subgroup G) = 4 := by
      rw [← U_index_eq_S0_card c h12]
      exact hindex
    have hm : c.m = 2 := by
      have hpow : 2 ^ c.m = 4 := by
        rw [← S0_nat_card c]
        exact hS0
      have h' : 2 ^ c.m = 2 ^ 2 := by
        rw [hpow]
        norm_num
      exact Nat.pow_right_injective (by norm_num : (2 : ℕ) ≤ 2) h'
    rw [S_nat_card c, hm]
    norm_num
  exact ⟨μ, hμB, hμν, hμνs, hB, hTfalse, by simpa [conjIrr_coe] using hEx.1, hEx.2,
    hindex, hS⟩

/-! ## Local orbit and delta orthogonality helpers

The Coherence module keeps its `theta_pair_*`/`delta_*` facts private, so the
cross-orbit orthogonality used in the `|Λμ| = 4` branch is re-proved from the
public `tildeNu_ind` and `lemma_1_3` API.
-/

private lemma orbit_self_mem' (c : Hyp11 G) [Fintype ↥(LambdaHom c.H0 c.U)]
    (ν : ClassFunction (↥c.H0)) : ν ∈ orbit c.H0 c.U ν := by
  classical
  refine Finset.mem_image.mpr ⟨(1 : LambdaHom c.H0 c.U), Finset.mem_univ _, ?_⟩
  have h1 : LambdaChar (1 : LambdaHom c.H0 c.U).1 = (1 : ClassFunction (↥c.H0)) := by
    ext x
    simp [LambdaChar]
  rw [h1, one_mul]

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

private def conjLambda (c : Hyp11 G) (h12 : Hyp12 c) (l : LambdaHom c.H0 c.U) :
    LambdaHom c.H0 c.U := by
  classical
  refine ⟨l.1.comp (conjMonoidHom c.H0 c.s (s_normalizes_H0 c h12)), ?_⟩
  intro u hu
  change l.1 (conjMonoidHom c.H0 c.s (s_normalizes_H0 c h12) u) = 1
  exact l.2 (conjMonoidHom c.H0 c.s (s_normalizes_H0 c h12) u) (by
    change c.s * (u : G) * c.s⁻¹ ∈ c.U
    exact s_normalizes_U c hu)

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

private lemma conjMonoidHom_conjMonoidHom (c : Hyp11 G) (h12 : Hyp12 c)
    (x : ↥c.H0) :
    (conjMonoidHom c.H0 c.s (s_normalizes_H0 c h12)
      (conjMonoidHom c.H0 c.s (s_normalizes_H0 c h12) x) : ↥c.H0) = x := by
  apply Subtype.ext
  exact s_conj_sq c (x : G)

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

private lemma conjChar_conjChar (c : Hyp11 G) (h12 : Hyp12 c)
    (ν : ClassFunction (↥c.H0)) :
    conjChar c.H0 (s_normalizes_H0 c h12)
      (conjChar c.H0 (s_normalizes_H0 c h12) ν) = ν := by
  classical
  ext x
  simp [conjChar]
  rw [conjMonoidHom_conjMonoidHom c h12 x]

private lemma orbit_mem_eq_on_U (c : Hyp11 G)
    [Fintype ↥(LambdaHom c.H0 c.U)] {ν μ : ClassFunction (↥c.H0)}
    (hμ : μ ∈ orbit c.H0 c.U ν) {x : ↥c.H0} (hx : (x : G) ∈ c.U) :
    μ x = ν x := by
  classical
  rcases (Finset.mem_image.mp hμ) with ⟨l, hl, rfl⟩
  have hlU : l.1 x = 1 := l.2 x hx
  simp [LambdaChar, hlU]

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

private lemma isClassFunction_sub_irr {H : Type u} [Group H] [Fintype H]
    {μ ν : ClassFunction H} (hμ : IsIrreducibleCharacter μ)
    (hν : IsIrreducibleCharacter ν) : IsClassFunction (μ - ν) := by
  intro x g
  have hμx := isCharacter_isClassFunction (isCharacter_of_isIrreducibleCharacter hμ) x g
  have hνx := isCharacter_isClassFunction (isCharacter_of_isIrreducibleCharacter hν) x g
  simp [hμx, hνx]

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

private lemma theta_pointwise (c : Hyp11 G) (h12 : Hyp12 c)
    (hH0index : (c.H0.subgroupOf c.H).index = 2)
    {ν : ClassFunction (↥c.H0)} (hν : IsIrreducibleCharacter ν)
    (x : ↥c.H0) :
    inducedFromSub (h12.H0_normal_in_H).1 ν
        ⟨(x : G), (h12.H0_normal_in_H).1 x.2⟩ =
      ν x + ν ⟨c.s * (x : G) * c.s⁻¹, s_normalizes_H0 c h12 x⟩ := by
  exact (remark_1_4 (h12.H0_normal_in_H).1 hH0index (S_le_H c c.s_mem_S)
    (s_not_mem_H0' c h12) hν).1 (x : G) x.2 (s_normalizes_H0 c h12 x)

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
      exact orbit_self_mem' c ν₁
    exact hmem
  · simp [h]

private lemma scalarProduct_star_comm' {G : Type u} [Group G] [Fintype G]
    (φ ψ : ClassFunction G) :
    star (scalarProduct G φ ψ) = scalarProduct G ψ φ := by
  classical
  unfold scalarProduct
  simp [map_sum, map_mul, map_star, mul_comm, mul_left_comm, mul_assoc]

private lemma card_ge_four_of_four_mem {α : Type u} [DecidableEq α]
    (s : Finset α) {a b c d : α}
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (hd : d ∈ s)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) : 4 ≤ s.card := by
  classical
  have hsub : ({a, b, c, d} : Finset α) ⊆ s := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx | hx | hx
    · exact hx ▸ ha
    · exact hx ▸ hb
    · exact hx ▸ hc
    · exact hx ▸ hd
  have hcard : ({a, b, c, d} : Finset α).card = 4 := by
    rw [Finset.card_insert_of_notMem (by
      intro hm
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with hm | hm | hm
      · exact hab hm
      · exact hac hm
      · exact had hm)]
    rw [Finset.card_insert_of_notMem (by
      intro hm
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with hm | hm
      · exact hbc hm
      · exact hbd hm)]
    rw [Finset.card_insert_of_notMem (by
      intro hm
      simp only [Finset.mem_singleton] at hm
      exact hcd hm)]
    simp
  rw [← hcard]
  exact Finset.card_le_card hsub

private lemma card_ge_three_of_three_mem {α : Type u} [DecidableEq α]
    (s : Finset α) {a b c : α}
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : 3 ≤ s.card := by
  classical
  have hsub : ({a, b, c} : Finset α) ⊆ s := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx | hx
    · exact hx ▸ ha
    · exact hx ▸ hb
    · exact hx ▸ hc
  have hcard : ({a, b, c} : Finset α).card = 3 := by
    rw [Finset.card_insert_of_notMem (by
      intro hm
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with hm | hm
      · exact hab hm
      · exact hac hm)]
    rw [Finset.card_insert_of_notMem (by
      intro hm
      simp only [Finset.mem_singleton] at hm
      exact hbc hm)]
    simp
  rw [← hcard]
  exact Finset.card_le_card hsub

private lemma irr_ne_of_orbits_distinct (c : Hyp11 G)
    [Fintype ↥(LambdaHom c.H0 c.U)] {ν μ η θ : Irr (↥c.H0)}
    (hη : η.1 ∈ orbit c.H0 c.U ν.1)
    (hθ : θ.1 ∈ orbit c.H0 c.U μ.1)
    (hnot : μ.1 ∉ orbit c.H0 c.U ν.1) : η ≠ θ := by
  intro hEq
  apply hnot
  have hEq' : η.1 = θ.1 := congrArg Subtype.val hEq
  have hθL' : θ.1 ∈ orbit c.H0 c.U ν.1 := by simpa [hEq'] using hη
  have horbitθν : orbit c.H0 c.U θ.1 = orbit c.H0 c.U ν.1 := orbit_eq_of_mem c hθL'
  have horbitθμ : orbit c.H0 c.U θ.1 = orbit c.H0 c.U μ.1 := orbit_eq_of_mem c hθ
  have hEqOr : orbit c.H0 c.U μ.1 = orbit c.H0 c.U ν.1 := horbitθμ.symm.trans horbitθν
  rw [← hEqOr]
  exact orbit_self_mem' c μ.1

private lemma signed_irr_of_nonfixed (c : Hyp11 G) (h12 : Hyp12 c)
    {μ : Irr (↥c.H0)}
    (hμs : conjChar c.H0 (s_normalizes_H0 c h12) μ.1 ≠ μ.1) :
    IsPMIrr G (tildeNu c h12 μ) := by
  classical
  have hgen : IsGeneralizedCharacter (tildeNu c h12 μ) :=
    tildeNu_isGeneralized c h12 μ
  have hnorm : scalarProduct G (tildeNu c h12 μ) (tildeNu c h12 μ) = 1 := by
    have h := tildeNu_norm c h12 μ
    simp [hμs] at h
    simpa [normSq] using h
  rcases norm_one_signed_irreducible hgen hnorm with ⟨ψ, hψ, hψeq⟩
  rcases hψeq with hψeq | hψeq
  · exact Or.inl (by simpa [hψeq] using hψ)
  · exact Or.inr (by simpa [hψeq] using hψ)

private lemma exists_not_fixed_of_card_ge_four (c : Hyp11 G) (h12 : Hyp12 c)
    {ν : ClassFunction (↥c.H0)} (hν : IsIrreducibleCharacter ν)
    (hfix : conjChar c.H0 (s_normalizes_H0 c h12) ν = ν)
    (hcard : 4 ≤ (orbit c.H0 c.U ν).card) :
    ∃ μ ∈ orbit c.H0 c.U ν, conjChar c.H0 (s_normalizes_H0 c h12) μ ≠ μ := by
  classical
  by_contra hnone
  have hfixcount := lemma_2_1_b c h12 (ν := ν) hν (by
    simpa [hfix] using orbit_self_mem' c ν)
  have hall : ∀ μ ∈ orbit c.H0 c.U ν,
      conjChar c.H0 (s_normalizes_H0 c h12) μ = μ := by
    intro μ hμ
    by_contra hne
    exact hnone ⟨μ, hμ, hne⟩
  have hfilter : (orbit c.H0 c.U ν).filter (fun μ =>
      conjChar c.H0 (s_normalizes_H0 c h12) μ = μ) = orbit c.H0 c.U ν :=
    Finset.filter_true_of_mem hall
  have hcards : (orbit c.H0 c.U ν).card = 2 := by
    rw [← hfixcount, hfilter]
  omega

private lemma BOf_mem_orbit_eq_pair (c : Hyp11 G) (h12 : Hyp12 c)
    {χ : ClassFunction G} (hχ : IsPMIrr G χ)
    {ν η : Irr (↥c.H0)}
    (hνB : ν ∈ BOf c h12 χ)
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 ≠ ν.1)
    (hνsL : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 ∈ orbit c.H0 c.U ν.1)
    (hηB : η ∈ BOf c h12 χ)
    (hηL : η.1 ∈ orbit c.H0 c.U ν.1) :
    η = ν ∨ η = conjIrr c h12 ν := by
  classical
  by_contra h
  have hνsB : conjIrr c h12 ν ∈ BOf c h12 χ := (BOf_conj_iff c h12 χ ν).2 hνB
  have hνne : ν ≠ conjIrr c h12 ν := by
    intro hEq
    apply hνs
    have h' := congrArg Subtype.val hEq
    simpa [conjIrr_coe] using h'.symm
  have hηneν : η ≠ ν := by
    intro hEq
    exact h (Or.inl hEq)
  have hηneνs : η ≠ conjIrr c h12 ν := by
    intro hEq
    exact h (Or.inr hEq)
  have hνsL' : (conjIrr c h12 ν).1 ∈ orbit c.H0 c.U ν.1 := by
    simpa [conjIrr_coe] using hνsL
  have hνself : ν.1 ∈ orbit c.H0 c.U ν.1 := orbit_self_mem' c ν.1
  let F : Finset (Irr (↥c.H0)) :=
    (BOf c h12 χ).filter (fun μ : Irr (↥c.H0) => μ.1 ∈ orbit c.H0 c.U ν.1)
  have hmemν : ν ∈ F := Finset.mem_filter.mpr ⟨hνB, hνself⟩
  have hmemνs : conjIrr c h12 ν ∈ F := Finset.mem_filter.mpr ⟨hνsB, hνsL'⟩
  have hmemη : η ∈ F := Finset.mem_filter.mpr ⟨hηB, hηL⟩
  have h3 : 3 ≤ F.card :=
    @card_ge_three_of_three_mem (Irr (↥c.H0)) _ F ν η (conjIrr c h12 ν)
      hmemν hmemη hmemνs hηneν.symm hνne hηneνs
  have hle : F.card ≤ 2 := by
    simpa [F] using BOf_orbit_card_le_two c h12 χ hχ ν
  omega

private lemma mu_not_in_nu_orbit (c : Hyp11 G) (h12 : Hyp12 c)
    {χ : ClassFunction G} (hχ : IsPMIrr G χ)
    {ν μ : Irr (↥c.H0)}
    (hνB : ν ∈ BOf c h12 χ)
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 ≠ ν.1)
    (hνsL : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 ∈ orbit c.H0 c.U ν.1)
    (hμB : μ ∈ BOf c h12 χ) (hμν : μ ≠ ν) (hμνs : μ ≠ conjIrr c h12 ν) :
    μ.1 ∉ orbit c.H0 c.U ν.1 := by
  intro hμL
  rcases BOf_mem_orbit_eq_pair c h12 hχ hνB hνs hνsL hμB hμL with hEq | hEq
  · exact hμν hEq
  · exact hμνs hEq

private lemma mu_fixed_of_false_branch (c : Hyp11 G) (h12 : Hyp12 c)
    {χ : ClassFunction G} (hχ : IsPMIrr G χ)
    {ν μ : Irr (↥c.H0)}
    (hνB : ν ∈ BOf c h12 χ)
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 ≠ ν.1)
    (hνsL : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 ∈ orbit c.H0 c.U ν.1)
    (hμB : μ ∈ BOf c h12 χ) (hμν : μ ≠ ν) (hμνs : μ ≠ conjIrr c h12 ν)
    (hB : BOf c h12 χ = {ν, conjIrr c h12 ν, μ}) :
    conjChar c.H0 (s_normalizes_H0 c h12) μ.1 = μ.1 := by
  classical
  by_contra hμs
  have hμsB : conjIrr c h12 μ ∈ BOf c h12 χ := (BOf_conj_iff c h12 χ μ).2 hμB
  have hμne : conjIrr c h12 μ ≠ μ := by
    intro hEq
    apply hμs
    have h' := congrArg Subtype.val hEq
    simpa [conjIrr_coe] using h'
  have hmem : conjIrr c h12 μ ∈ BOf c h12 χ := hμsB
  rw [hB] at hmem
  simp at hmem
  rcases hmem with hEqν | hEqνs | hEqμ
  · -- conj μ = ν
    have hEqνs' : (conjIrr c h12 μ).1 = ν.1 := congrArg Subtype.val hEqν
    have hμL : μ.1 ∈ orbit c.H0 c.U ν.1 := by
      have h2 : μ.1 = conjChar c.H0 (s_normalizes_H0 c h12) ν.1 := by
        have hEqνs'' : conjChar c.H0 (s_normalizes_H0 c h12) μ.1 = ν.1 := by
          simpa [conjIrr_coe] using hEqνs'
        have h := congrArg (conjChar c.H0 (s_normalizes_H0 c h12)) hEqνs''
        rw [conjChar_conjChar c h12 μ.1] at h
        exact h
      rw [h2]
      exact hνsL
    exact mu_not_in_nu_orbit c h12 hχ hνB hνs hνsL hμB hμν hμνs hμL
  · -- conj μ = conj ν
    have hEq' : (conjIrr c h12 μ).1 = (conjIrr c h12 ν).1 := congrArg Subtype.val hEqνs
    have hμL : μ.1 ∈ orbit c.H0 c.U ν.1 := by
      have h2 : μ.1 = ν.1 := by
        have hEq'' : conjChar c.H0 (s_normalizes_H0 c h12) μ.1 =
            conjChar c.H0 (s_normalizes_H0 c h12) ν.1 := by
          simpa [conjIrr_coe] using hEq'
        have h1 := congrArg (conjChar c.H0 (s_normalizes_H0 c h12)) hEq''
        rw [conjChar_conjChar c h12 μ.1, conjChar_conjChar c h12 ν.1] at h1
        exact h1
      rw [h2]
      exact orbit_self_mem' c ν.1
    exact mu_not_in_nu_orbit c h12 hχ hνB hνs hνsL hμB hμν hμνs hμL
  · exact hμne hEqμ

private lemma exists_fixed_pairing_zero (c : Hyp11 G) (h12 : Hyp12 c)
    (hSC : Section3Hyp c) {ν μ μ' : Irr (↥c.H0)}
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 ≠ ν.1)
    (hνsL : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 ∈ orbit c.H0 c.U ν.1)
    (hμ'L : μ'.1 ∈ orbit c.H0 c.U μ.1)
    (hμfix : conjChar c.H0 (s_normalizes_H0 c h12) μ.1 = μ.1)
    (hμ's : conjChar c.H0 (s_normalizes_H0 c h12) μ'.1 ≠ μ'.1)
    (hnot : μ.1 ∉ orbit c.H0 c.U ν.1) :
    ∃ ν' : Irr (↥c.H0), ν'.1 ∈ orbit c.H0 c.U ν.1 ∧
      conjChar c.H0 (s_normalizes_H0 c h12) ν'.1 = ν'.1 ∧
      scalarProduct G (tildeNu c h12 ν') (tildeNu c h12 μ') = 0 := by
  classical
  let F : Finset (ClassFunction (↥c.H0)) :=
    (orbit c.H0 c.U ν.1).filter (fun x =>
      conjChar c.H0 (s_normalizes_H0 c h12) x = x)
  have hFcard : F.card = 2 := by
    simpa [F] using lemma_2_1_b c h12 ν.2 hνsL
  rcases Finset.card_eq_two.mp hFcard with ⟨a, b, hFab, hab⟩
  have haF : a ∈ F := by rw [hab]; simp
  have hbF : b ∈ F := by rw [hab]; simp
  have haP := Finset.mem_filter.mp haF
  have hbP := Finset.mem_filter.mp hbF
  have haL : a ∈ orbit c.H0 c.U ν.1 := haP.1
  have hbL : b ∈ orbit c.H0 c.U ν.1 := hbP.1
  have hafix : conjChar c.H0 (s_normalizes_H0 c h12) a = a := haP.2
  have hbfix : conjChar c.H0 (s_normalizes_H0 c h12) b = b := hbP.2
  let aI : Irr (↥c.H0) := ⟨a, orbit_mem_isIrreducible c.H0 c.U ν.2 haL⟩
  let bI : Irr (↥c.H0) := ⟨b, orbit_mem_isIrreducible c.H0 c.U ν.2 hbL⟩
  have hafixI : conjChar c.H0 (s_normalizes_H0 c h12) aI.1 = aI.1 := by
    simpa [aI] using hafix
  have hbfixI : conjChar c.H0 (s_normalizes_H0 c h12) bI.1 = bI.1 := by
    simpa [bI] using hbfix
  have hη : IsPMIrr G (tildeNu c h12 μ') := signed_irr_of_nonfixed c h12 hμ's
  by_contra hnone
  have hpa_ne : scalarProduct G (tildeNu c h12 aI) (tildeNu c h12 μ') ≠ 0 := by
    intro hz
    exact hnone ⟨aI, haL, hafixI, hz⟩
  have hpb_ne : scalarProduct G (tildeNu c h12 bI) (tildeNu c h12 μ') ≠ 0 := by
    intro hz
    exact hnone ⟨bI, hbL, hbfixI, hz⟩
  have hpa_ne' : scalarProduct G (tildeNu c h12 μ') (tildeNu c h12 aI) ≠ 0 := by
    intro hz
    apply hpa_ne
    have hstar := scalarProduct_star_comm' (tildeNu c h12 aI) (tildeNu c h12 μ')
    have hz' : star (scalarProduct G (tildeNu c h12 aI) (tildeNu c h12 μ')) = 0 := by
      simpa [hstar] using hz
    exact star_eq_zero.mp hz'
  have hpb_ne' : scalarProduct G (tildeNu c h12 μ') (tildeNu c h12 bI) ≠ 0 := by
    intro hz
    apply hpb_ne
    have hstar := scalarProduct_star_comm' (tildeNu c h12 bI) (tildeNu c h12 μ')
    have hz' : star (scalarProduct G (tildeNu c h12 bI) (tildeNu c h12 μ')) = 0 := by
      simpa [hstar] using hz
    exact star_eq_zero.mp hz'
  have haB : aI ∈ BOf c h12 (tildeNu c h12 μ') :=
    (BOf_mem_iff c h12 (tildeNu c h12 μ') aI).2 hpa_ne'
  have hbB : bI ∈ BOf c h12 (tildeNu c h12 μ') :=
    (BOf_mem_iff c h12 (tildeNu c h12 μ') bI).2 hpb_ne'
  have hself : normSq G (tildeNu c h12 μ') ≠ 0 := by
    have h := tildeNu_norm c h12 μ'
    simp [hμ's] at h
    rw [h]
    norm_num
  have hμB : μ' ∈ BOf c h12 (tildeNu c h12 μ') :=
    (BOf_mem_iff c h12 (tildeNu c h12 μ') μ').2 (by simpa [normSq] using hself)
  have hμsB : conjIrr c h12 μ' ∈ BOf c h12 (tildeNu c h12 μ') :=
    (BOf_conj_iff c h12 (tildeNu c h12 μ') μ').2 hμB
  have hμ'ne : μ' ≠ conjIrr c h12 μ' := by
    intro hEq
    apply hμ's
    have h' := congrArg Subtype.val hEq
    simpa [conjIrr_coe] using h'.symm
  have hconjL : (conjIrr c h12 μ').1 ∈ orbit c.H0 c.U μ.1 := by
    have h1 := orbit_subset_conjChar c h12 μ'.1 hμ'L
    simpa [conjIrr_coe, hμfix] using h1
  have haμne : aI ≠ μ' := irr_ne_of_orbits_distinct c haL hμ'L hnot
  have hbμne : bI ≠ μ' := irr_ne_of_orbits_distinct c hbL hμ'L hnot
  have haμsne : aI ≠ conjIrr c h12 μ' := irr_ne_of_orbits_distinct c haL hconjL hnot
  have hbμsne : bI ≠ conjIrr c h12 μ' := irr_ne_of_orbits_distinct c hbL hconjL hnot
  have habI : aI ≠ bI := by
    intro hEq
    apply hFab
    have h' := congrArg Subtype.val hEq
    exact h'
  let B := BOf c h12 (tildeNu c h12 μ')
  have h4 : 4 ≤ B.card :=
    @card_ge_four_of_four_mem (Irr (↥c.H0)) _ B aI bI μ' (conjIrr c h12 μ')
      haB hbB hμB hμsB habI haμne haμsne hbμne hbμsne hμ'ne
  have hle : B.card ≤ 3 := theorem_3_2 c h12 hSC hη
  omega

private lemma fixed_pairing_zero_with_nu (c : Hyp11 G) (h12 : Hyp12 c)
    {ν ν' : Irr (↥c.H0)}
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 ≠ ν.1)
    (hνsL : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 ∈ orbit c.H0 c.U ν.1)
    (hν'L : ν'.1 ∈ orbit c.H0 c.U ν.1)
    (hν'fix : conjChar c.H0 (s_normalizes_H0 c h12) ν'.1 = ν'.1) :
    scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 ν') = 0 := by
  classical
  by_contra hne
  have hνIrr : IsPMIrr G (tildeNu c h12 ν) := signed_irr_of_nonfixed c h12 hνs
  have hνB : ν ∈ BOf c h12 (tildeNu c h12 ν) := by
    rw [BOf_mem_iff]
    have hself : normSq G (tildeNu c h12 ν) ≠ 0 := by
      have h := tildeNu_norm c h12 ν
      simp [hνs] at h
      rw [h]
      norm_num
    simpa [normSq] using hself
  have hν'B : ν' ∈ BOf c h12 (tildeNu c h12 ν) :=
    (BOf_mem_iff c h12 (tildeNu c h12 ν) ν').2 hne
  rcases BOf_mem_orbit_eq_pair c h12 hνIrr hνB hνs hνsL hν'B hν'L with hEq | hEq
  · exfalso
    apply hνs
    have h1 : conjChar c.H0 (s_normalizes_H0 c h12) ν'.1 = ν'.1 := hν'fix
    have h2 : ν'.1 = ν.1 := congrArg Subtype.val hEq
    rw [h2] at h1
    exact h1
  · exfalso
    apply hνs
    have h2 : ν'.1 = (conjIrr c h12 ν).1 := congrArg Subtype.val hEq
    have h3 : conjChar c.H0 (s_normalizes_H0 c h12) (conjIrr c h12 ν).1 = ν.1 := by
      have h5 : conjChar c.H0 (s_normalizes_H0 c h12)
          (conjChar c.H0 (s_normalizes_H0 c h12) ν.1) = ν.1 := by
        rw [conjChar_conjChar c h12 ν.1]
      simpa [conjIrr_coe] using h5
    have h4 : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1 := by
      have hfixconj : conjChar c.H0 (s_normalizes_H0 c h12) (conjIrr c h12 ν).1 =
          (conjIrr c h12 ν).1 := by
        have htemp : conjChar c.H0 (s_normalizes_H0 c h12) ν'.1 = ν'.1 := hν'fix
        rwa [h2] at htemp
      have hEq'' : (conjIrr c h12 ν).1 = ν.1 := by
        rw [h3] at hfixconj
        exact hfixconj.symm
      exact (by simpa [conjIrr_coe] using hEq'')
    exact h4

private lemma chi_pairing_zero_implies_nu_pairing_zero (c : Hyp11 G) (h12 : Hyp12 c)
    {χ : ClassFunction G} (hχ : IsPMIrr G χ) {ν μ' : Irr (↥c.H0)}
    (hνB : ν ∈ BOf c h12 χ)
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 ≠ ν.1)
    (hχμ' : scalarProduct G χ (tildeNu c h12 μ') = 0) :
    scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 μ') = 0 := by
  classical
  have hchi : χ = scalarProduct G χ (tildeNu c h12 ν) • tildeNu c h12 ν :=
    chi_eq_smul_tildeNu c h12 hχ hνs hνB
  let ε : ℂ := scalarProduct G χ (tildeNu c h12 ν)
  have hchi' : χ = ε • tildeNu c h12 ν := by simpa [ε] using hchi
  have hEq : scalarProduct G χ (tildeNu c h12 μ') =
      ε *
        scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 μ') := by
    rw [hchi']
    rw [scalarProduct_smul_left]
  rcases BOf_scalar_eq_pm_one c h12 hχ hνB with hc1 | hc1
  · have h' : scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 μ') = 0 := by
      have hE := hEq
      rw [show ε = 1 by simpa [ε] using hc1, hχμ'] at hE
      norm_num at hE
      exact hE.symm
    exact h'
  · have h' : scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 μ') = 0 := by
      have hE := hEq
      rw [show ε = -1 by simpa [ε] using hc1, hχμ'] at hE
      norm_num at hE
      exact hE
    exact h'

private lemma BOf_pairing_pm_one (c : Hyp11 G) (h12 : Hyp12 c)
    {χ : ClassFunction G} (hχ : IsPMIrr G χ) {ν μ : Irr (↥c.H0)}
    (hνB : ν ∈ BOf c h12 χ) (hμB : μ ∈ BOf c h12 χ)
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 ≠ ν.1) :
    scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 μ) = 1 ∨
      scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 μ) = -1 := by
  classical
  have hchi : χ = scalarProduct G χ (tildeNu c h12 ν) • tildeNu c h12 ν :=
    chi_eq_smul_tildeNu c h12 hχ hνs hνB
  let ε : ℂ := scalarProduct G χ (tildeNu c h12 ν)
  have hchi' : χ = ε • tildeNu c h12 ν := by simpa [ε] using hchi
  have hEq : scalarProduct G χ (tildeNu c h12 μ) =
      ε *
        scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 μ) := by
    rw [hchi']
    rw [scalarProduct_smul_left]
  have hc := BOf_scalar_eq_pm_one c h12 hχ hνB
  have hχμ := BOf_scalar_eq_pm_one c h12 hχ hμB
  rcases hc with hc1 | hc1
  · rcases hχμ with hμ1 | hμ1
    · left
      have hE := hEq
      rw [show ε = 1 by simpa [ε] using hc1, hμ1] at hE
      norm_num at hE
      exact hE.symm
    · right
      have hE := hEq
      rw [show ε = 1 by simpa [ε] using hc1, hμ1] at hE
      norm_num at hE
      exact hE.symm
  · rcases hχμ with hμ1 | hμ1
    · right
      have hsp : scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 μ) = -1 := by
        have hE := hEq
        rw [show ε = -1 by simpa [ε] using hc1, hμ1] at hE
        norm_num at hE
        have h' := congrArg Neg.neg hE
        norm_num at h'
        exact h'.symm
      exact hsp
    · left
      have hsp : scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 μ) = 1 := by
        have hE := hEq
        rw [show ε = -1 by simpa [ε] using hc1, hμ1] at hE
        norm_num at hE
        have h' := congrArg Neg.neg hE
        norm_num at h'
        exact h'.symm
      exact hsp

private lemma isGeneralizedCharacter_neg {G : Type u} [Group G] [Fintype G]
    {φ : ClassFunction G} (hφ : IsGeneralizedCharacter φ) :
    IsGeneralizedCharacter (-φ) := by
  rcases hφ with ⟨χ, ψ, hχ, hψ, hφeq⟩
  refine ⟨ψ, χ, hψ, hχ, ?_⟩
  rw [hφeq]
  ext x
  simp

private lemma isGeneralizedCharacter_sub {G : Type u} [Group G] [Fintype G]
    {φ ψ : ClassFunction G} (hφ : IsGeneralizedCharacter φ)
    (hψ : IsGeneralizedCharacter ψ) : IsGeneralizedCharacter (φ - ψ) := by
  rcases hφ with ⟨α, β, hα, hβ, hφeq⟩
  rcases hψ with ⟨γ, δ, hγ, hδ, hψeq⟩
  refine ⟨α + δ, β + γ, isCharacter_add hα hδ, isCharacter_add hβ hγ, ?_⟩
  rw [hφeq, hψeq]
  ext x
  simp
  ring

private lemma eta_signed_irreducible (c : Hyp11 G) (h12 : Hyp12 c)
    {χ : ClassFunction G} (hχ : IsPMIrr G χ) {ν μ : Irr (↥c.H0)}
    (hνB : ν ∈ BOf c h12 χ) (hμB : μ ∈ BOf c h12 χ)
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 ≠ ν.1)
    (hμfix : conjChar c.H0 (s_normalizes_H0 c h12) μ.1 = μ.1) :
    IsPMIrr G
      (tildeNu c h12 μ -
        scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 μ) • tildeNu c h12 ν) := by
  classical
  let a : ℂ := scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 μ)
  have ha : a = 1 ∨ a = -1 := BOf_pairing_pm_one c h12 hχ hνB hμB hνs
  let η : ClassFunction G := tildeNu c h12 μ - a • tildeNu c h12 ν
  have hνnorm : scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 ν) = 1 := by
    have h := tildeNu_norm c h12 ν
    simp [hνs] at h
    simpa [normSq] using h
  have hμnorm : scalarProduct G (tildeNu c h12 μ) (tildeNu c h12 μ) = 2 := by
    have h := tildeNu_norm c h12 μ
    simp [hμfix] at h
    simpa [normSq] using h
  have hνμ : scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 μ) = a := rfl
  have hμν : scalarProduct G (tildeNu c h12 μ) (tildeNu c h12 ν) = star a := by
    have h := scalarProduct_star_comm' (tildeNu c h12 ν) (tildeNu c h12 μ)
    rw [hνμ] at h
    exact h.symm
  have ha_re : star a = a := by rcases ha with h | h <;> simp [h]
  have haa : a * star a = 1 := by rcases ha with h | h <;> simp [h]
  have hηnorm : scalarProduct G η η = 1 := by
    unfold η
    rw [scalarProduct_sub_left, scalarProduct_sub_right, scalarProduct_sub_right]
    simp only [scalarProduct_smul_right, scalarProduct_smul_left]
    rw [hμnorm, hνnorm, hνμ, hμν]
    rcases ha with h | h <;> simp [h, ha_re, haa] <;> ring
  have hηgen : IsGeneralizedCharacter η := by
    have hμgen := tildeNu_isGeneralized c h12 μ
    have hνgen := tildeNu_isGeneralized c h12 ν
    unfold η
    rcases ha with ha1 | ha1
    · have hsmul : a • tildeNu c h12 ν = tildeNu c h12 ν := by simp [ha1]
      rw [hsmul]
      exact isGeneralizedCharacter_sub hμgen hνgen
    · have hsmul : a • tildeNu c h12 ν = -tildeNu c h12 ν := by simp [ha1]
      rw [hsmul]
      exact isGeneralizedCharacter_sub hμgen (isGeneralizedCharacter_neg hνgen)
  rcases norm_one_signed_irreducible hηgen (by simpa [normSq] using hηnorm) with
    ⟨ψ, hψ, hψeq⟩
  rcases hψeq with hψeq | hψeq
  · exact Or.inl (by
      change IsIrreducibleCharacter η
      rw [hψeq]
      exact hψ)
  · exact Or.inr (by
      change IsIrreducibleCharacter (-η)
      rw [hψeq]
      simp
      exact hψ)

private lemma eta_mem_BOf_nu (c : Hyp11 G) (h12 : Hyp12 c)
    {ν ν' μ : Irr (↥c.H0)} {a : ℂ}
    (ha : a = 1 ∨ a = -1)
    (hνν' : scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 ν') = 0)
    (hμν' : scalarProduct G (tildeNu c h12 μ) (tildeNu c h12 ν') = a) :
    ν' ∈ BOf c h12 (tildeNu c h12 μ - a • tildeNu c h12 ν) := by
  classical
  rw [BOf_mem_iff]
  rw [scalarProduct_sub_left, scalarProduct_smul_left]
  rw [hμν', hνν']
  rcases ha with h | h <;> simp [h]

private lemma eta_mem_BOf_mu (c : Hyp11 G) (h12 : Hyp12 c)
    {ν μ : Irr (↥c.H0)} {a : ℂ}
    (hμfix : conjChar c.H0 (s_normalizes_H0 c h12) μ.1 = μ.1)
    (ha : a = 1 ∨ a = -1)
    (hνμ : scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 μ) = a) :
    μ ∈ BOf c h12 (tildeNu c h12 μ - a • tildeNu c h12 ν) := by
  classical
  rw [BOf_mem_iff]
  rw [scalarProduct_sub_left, scalarProduct_smul_left]
  have hμnorm : scalarProduct G (tildeNu c h12 μ) (tildeNu c h12 μ) = 2 := by
    have h := tildeNu_norm c h12 μ
    simp [hμfix] at h
    simpa [normSq] using h
  rw [hμnorm, hνμ]
  rcases ha with h | h <;> norm_num [h]

private lemma lambda_mu4_false (c : Hyp11 G) (h12 : Hyp12 c) (hSC : Section3Hyp c)
    {χ : ClassFunction G} (hχ : IsPMIrr G χ) {ν μ : Irr (↥c.H0)}
    (hνB : ν ∈ BOf c h12 χ)
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 ≠ ν.1)
    (hνsL : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 ∈ orbit c.H0 c.U ν.1)
    (hμB : μ ∈ BOf c h12 χ) (hμν : μ ≠ ν) (hμνs : μ ≠ conjIrr c h12 ν)
    (hB : BOf c h12 χ = {ν, conjIrr c h12 ν, μ})
    (hΛν4 : (orbit c.H0 c.U ν.1).card = 4)
    (hΛμ4 : (orbit c.H0 c.U μ.1).card = 4)
    (hindex : (c.U.subgroupOf c.H0).index = 4)
    (hS8 : Nat.card (↥(c.S : Subgroup G)) = 8) : False := by
  classical
  have hμfix : conjChar c.H0 (s_normalizes_H0 c h12) μ.1 = μ.1 :=
    mu_fixed_of_false_branch c h12 hχ hνB hνs hνsL hμB hμν hμνs hB
  have hnot : μ.1 ∉ orbit c.H0 c.U ν.1 :=
    mu_not_in_nu_orbit c h12 hχ hνB hνs hνsL hμB hμν hμνs
  have hμcard4 : 4 ≤ (orbit c.H0 c.U μ.1).card := by
    simpa [hΛμ4]
  rcases exists_not_fixed_of_card_ge_four c h12 μ.2 hμfix hμcard4 with ⟨μ'c, hμ'L, hμ's⟩
  let μ' : Irr (↥c.H0) := ⟨μ'c, orbit_mem_isIrreducible c.H0 c.U μ.2 hμ'L⟩
  have hμ'L' : μ'.1 ∈ orbit c.H0 c.U μ.1 := by simpa [μ'] using hμ'L
  have hμ's' : conjChar c.H0 (s_normalizes_H0 c h12) μ'.1 ≠ μ'.1 := by
    simpa [μ'] using hμ's
  rcases exists_fixed_pairing_zero c h12 hSC hνs hνsL hμ'L' hμfix hμ's' hnot with
    ⟨ν', hν'L, hν'fix, hν'μ'0⟩
  have hνν'0 : scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 ν') = 0 :=
    fixed_pairing_zero_with_nu c h12 hνs hνsL hν'L hν'fix
  have hnot_νμ : ν.1 ∉ orbit c.H0 c.U μ.1 := by
    intro hL
    apply hnot
    have hEq := orbit_eq_of_mem c hL
    rw [hEq]
    exact orbit_self_mem' c μ.1
  have hμ'ν : μ' ≠ ν := irr_ne_of_orbits_distinct c hμ'L' (orbit_self_mem' c ν.1) hnot_νμ
  have hμ'νs : μ' ≠ conjIrr c h12 ν :=
    irr_ne_of_orbits_distinct c hμ'L' (by simpa [conjIrr_coe] using hνsL) hnot_νμ
  have hμ'μ : μ' ≠ μ := by
    intro hEq
    apply hμ's'
    have h' := congrArg Subtype.val hEq
    rw [h']
    exact hμfix
  have hμ'Bnot : μ' ∉ BOf c h12 χ := by
    intro hmem
    rw [hB] at hmem
    simp at hmem
    rcases hmem with hEq | hEq | hEq
    · exact hμ'ν hEq
    · exact hμ'νs hEq
    · exact hμ'μ hEq
  have hχμ'0 : scalarProduct G χ (tildeNu c h12 μ') = 0 := by
    by_contra h
    exact hμ'Bnot ((BOf_mem_iff c h12 χ μ').2 h)
  have hνμ'0 : scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 μ') = 0 :=
    chi_pairing_zero_implies_nu_pairing_zero c h12 hχ hνB hνs hχμ'0
  have hnot_conjνμ : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 ∉ orbit c.H0 c.U μ.1 := by
    intro hL
    apply hnot_νμ
    have h1 := orbit_subset_conjChar c h12 (conjChar c.H0 (s_normalizes_H0 c h12) ν.1) hL
    rw [conjChar_conjChar c h12 ν.1] at h1
    simpa [hμfix] using h1
  have horth := tildeNu_orthogonal c h12 (μ₁ := ν') (ν₁ := ν) (μ₂ := μ') (ν₂ := μ)
    hν'L hμ'L' hnot_νμ hnot_conjνμ
  have horthExp : scalarProduct G (tildeNu c h12 ν' - tildeNu c h12 ν)
      (tildeNu c h12 μ' - tildeNu c h12 μ) = 0 := horth
  rw [scalarProduct_sub_left, scalarProduct_sub_right, scalarProduct_sub_right] at horthExp
  let a : ℂ := scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 μ)
  have ha : a = 1 ∨ a = -1 := BOf_pairing_pm_one c h12 hχ hνB hμB hνs
  have hν'μ : scalarProduct G (tildeNu c h12 ν') (tildeNu c h12 μ) = a := by
    rw [hν'μ'0, hνμ'0] at horthExp
    have hEq' : a - scalarProduct G (tildeNu c h12 ν') (tildeNu c h12 μ) = 0 := by
      linear_combination horthExp
    exact (sub_eq_zero.mp hEq').symm
  have hμν' : scalarProduct G (tildeNu c h12 μ) (tildeNu c h12 ν') = a := by
    have hstar := scalarProduct_star_comm' (tildeNu c h12 ν') (tildeNu c h12 μ)
    rw [hν'μ] at hstar
    have hstar' : star a = scalarProduct G (tildeNu c h12 μ) (tildeNu c h12 ν') := hstar
    have ha_re : star a = a := by rcases ha with h | h <;> simp [h]
    rw [ha_re] at hstar'
    exact hstar'.symm
  let η : ClassFunction G := tildeNu c h12 μ - a • tildeNu c h12 ν
  have hη : IsPMIrr G η := by
    have hη' := eta_signed_irreducible c h12 hχ hνB hμB hνs hμfix
    simpa [a, η] using hη'
  have hν'Bη : ν' ∈ BOf c h12 η := by
    simpa [η] using eta_mem_BOf_nu c h12 ha hνν'0 hμν'
  have hμBη : μ ∈ BOf c h12 η := by
    simpa [η] using eta_mem_BOf_mu c h12 hμfix ha (show scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 μ) = a by rfl)
  have hν'μne : ν' ≠ μ := irr_ne_of_orbits_distinct c hν'L (orbit_self_mem' c μ.1) hnot
  have hν'card : (orbit c.H0 c.U ν'.1).card = (c.U.subgroupOf c.H0).index := by
    have hEq := orbit_eq_of_mem c hν'L
    rw [hEq, hΛν4, hindex]
  have hμcard : (orbit c.H0 c.U μ.1).card = (c.U.subgroupOf c.H0).index := by
    rw [hΛμ4, hindex]
  have h2 : ∃ ν1 ν2 : Irr (↥c.H0),
      ν1 ∈ BOf c h12 η ∧ ν2 ∈ BOf c h12 η ∧ ν1 ≠ ν2 ∧
        conjChar c.H0 (s_normalizes_H0 c h12) ν1.1 = ν1.1 ∧
        conjChar c.H0 (s_normalizes_H0 c h12) ν2.1 = ν2.1 ∧
        (orbit c.H0 c.U ν1.1).card = (c.U.subgroupOf c.H0).index ∧
        (orbit c.H0 c.U ν2.1).card = (c.U.subgroupOf c.H0).index :=
    ⟨ν', μ, hν'Bη, hμBη, hν'μne, hν'fix, hμfix, hν'card, hμcard⟩
  have h33 := lemma_3_3 c h12 hSC hη h2
  have hS4 : Nat.card (↥(c.S : Subgroup G)) = 4 := h33.2
  omega

private lemma s0Orbit_self_mem (c : Hyp11 G) (α : Irr (↥c.U)) :
    α ∈ s0Orbit c α := by
  refine Finset.mem_image.mpr ⟨(1 : ↥(c.S0 : Subgroup G)), Finset.mem_univ _, ?_⟩
  exact conjIrrS_one c α

private lemma orbit_card_eq_two_of_ne_four (c : Hyp11 G) (h12 : Hyp12 c)
    (hSC : Section3Hyp c) {μ : Irr (↥c.H0)}
    (hindex : (c.U.subgroupOf c.H0).index = 4)
    (hne : (orbit c.H0 c.U μ.1).card ≠ 4) :
    (orbit c.H0 c.U μ.1).card = 2 := by
  classical
  rcases orbit_is_orbitOfAlpha c h12 hSC μ with ⟨α, hOrbit⟩
  have hcard : (orbitOfAlpha c h12 hSC α).card =
      (c.U.subgroupOf c.H0).index / (s0Orbit c α).card :=
    orbitOfAlpha_card c h12 hSC α
  have hle : (s0Orbit c α).card ≤ 2 := s0Orbit_card_le_two c hSC α
  have hpos : 0 < (s0Orbit c α).card :=
    Finset.card_pos.mpr ⟨α, s0Orbit_self_mem c α⟩
  have hcard' : (orbit c.H0 c.U μ.1).card = 4 / (s0Orbit c α).card := by
    rw [hOrbit]
    rw [hcard, hindex]
  have hcases : (s0Orbit c α).card = 1 ∨ (s0Orbit c α).card = 2 := by omega
  rcases hcases with h1 | h2
  · have h4 : (orbit c.H0 c.U μ.1).card = 4 := by
      rw [hcard', h1]
    omega
  · rw [hcard', h2]

/-! ## Final `|Λμ| = 2` branch: degree congruence, class sums, and the
Glauberman-correspondence contradiction

The paper's L776–L814 argument.  The degree congruence `4 ∣ χ(1)` comes from
Lemma 1.7(ii) at `x = 1` with orbit representatives chosen outside `B(χ)`;
each orbit degree sum is `m·α(1) = 4·α(1)` (Remark 3.1), and the `B(χ)`-terms
contribute `±2β(1) ± 2α(1)` with `α(1), β(1)` odd.  The class-sum step is the
quarter version of Gorenstein 4.2.10 plus `4 ∤ |G : C_G(u)|` for
`u ∈ C_U(t)` (`t ∈ S \ S0`), and the final contradiction is Lemma 1.8 +
Lemma 1.9 (Glauberman) on the fixed subgroup `C_U(t)`.
-/

private lemma U_coprime_two (c : Hyp11 G) : Nat.Coprime 2 (Nat.card (↥c.U)) := by
  have h1 : Nat.card (↥c.U) = Nat.card (pPrimeCore 2 c.H) := by
    dsimp [Hyp11.U]
    rw [oddCoreOf]
    exact Subgroup.card_map_of_injective (f := c.H.subtype)
      (K := pPrimeCore 2 c.H) (Subgroup.subtype_injective c.H)
  rw [h1]
  exact pPrimeCore_coprime_card (p := 2) (G := c.H)

/-- Members of a `Λ`-orbit have the same degree. -/
private lemma orbit_mem_degree_eq (c : Hyp11 G) [Fintype ↥(LambdaHom c.H0 c.U)]
    {ν μ : ClassFunction (↥c.H0)} (hμ : μ ∈ orbit c.H0 c.U ν) : μ 1 = ν 1 := by
  classical
  rcases (Finset.mem_image.mp hμ) with ⟨l, hl, rfl⟩
  simp [LambdaChar]

/-- `(χ|_{H0}, rep)_{H0}` is an integer for `rep` irreducible. -/
private lemma restrict_scalarProduct_int (c : Hyp11 G) (h12 : Hyp12 c)
    {χ : ClassFunction G} (hχ : IsPMIrr G χ)
    (rep : ClassFunction (↥c.H0)) (hrep : IsIrreducibleCharacter rep) :
    ∃ a : ℤ, scalarProduct (↥c.H0) (fun y : ↥c.H0 => χ (y : G)) rep = (a : ℂ) := by
  classical
  have hχg : IsGeneralizedCharacter χ := by
    rcases hχ with hχ | hχ
    · exact ⟨χ, 0, isCharacter_of_isIrreducibleCharacter hχ, isCharacter_zero, by ext x; simp⟩
    · exact ⟨0, -χ, isCharacter_zero, isCharacter_of_isIrreducibleCharacter hχ, by ext x; simp⟩
  have hχH0 : IsGeneralizedCharacter (fun y : ↥c.H0 => χ (y : G)) :=
    isGeneralizedCharacter_restrict c.H0 hχg
  rcases multiplicity_int hrep (fun y : ↥c.H0 => χ (y : G)) hχH0 with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  have hrev : star (scalarProduct (↥c.H0) rep (fun y : ↥c.H0 => χ (y : G))) =
      scalarProduct (↥c.H0) (fun y : ↥c.H0 => χ (y : G)) rep := by
    unfold scalarProduct
    simp [map_sum, map_mul, map_star, mul_comm, mul_left_comm, mul_assoc]
  rw [← hrev, ha]
  simp

/-- In a full `Λ`-orbit (`|Λν| = m = 4`), every member restricts to the same
irreducible `β ∈ Irr(U)`. -/
private lemma orbit_restrict_full (c : Hyp11 G) (h12 : Hyp12 c) (hSC : Section3Hyp c)
    (hindex : (c.U.subgroupOf c.H0).index = 4)
    {ν : Irr (↥c.H0)} (hcard : (orbit c.H0 c.U ν.1).card = 4) :
    ∃ β : Irr (↥c.U),
      orbit c.H0 c.U ν.1 = orbitOfAlpha c h12 hSC β ∧
      restrictU c h12 ν.1 = β.1 := by
  classical
  rcases orbit_is_orbitOfAlpha c h12 hSC ν with ⟨β, hOrbit⟩
  have hcard' : (orbitOfAlpha c h12 hSC β).card = 4 / (s0Orbit c β).card := by
    rw [orbitOfAlpha_card c h12 hSC β, hindex]
  have hle : (s0Orbit c β).card ≤ 2 := s0Orbit_card_le_two c hSC β
  have hpos : 0 < (s0Orbit c β).card :=
    Finset.card_pos.mpr ⟨β, s0Orbit_self_mem c β⟩
  have hcard1 : (s0Orbit c β).card = 1 := by
    have h4 : (orbitOfAlpha c h12 hSC β).card = 4 := by
      rw [← hOrbit]
      exact hcard
    rw [hcard'] at h4
    by_cases h1 : (s0Orbit c β).card = 1
    · exact h1
    · have h2 : (s0Orbit c β).card = 2 := by omega
      rw [h2] at h4
      norm_num at h4
  have hsing : s0Orbit c β = {β} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rw [Finset.mem_singleton] at hx
      simpa [hx] using s0Orbit_self_mem c β
    · rw [hcard1]
      simp
  have hres : restrictU c h12 ν.1 = β.1 := by
    have hspec := (orbitOfAlpha_spec c h12 hSC β).2 ν.1 (by
      simpa [hOrbit] using orbit_self_mem' c ν.1)
    rw [hspec, hsing]
    simp
  exact ⟨β, hOrbit, hres⟩

/-- In a two-element `Λ`-orbit (`|Λμ| = 2`), every member restricts to
`α + α^r0` for the two `S0`-conjugates of `α ∈ Irr(U)`. -/
private lemma orbit_restrict_pair (c : Hyp11 G) (h12 : Hyp12 c) (hSC : Section3Hyp c)
    (hindex : (c.U.subgroupOf c.H0).index = 4)
    {μ : Irr (↥c.H0)} (hcard : (orbit c.H0 c.U μ.1).card = 2) :
    ∃ α : Irr (↥c.U),
      orbit c.H0 c.U μ.1 = orbitOfAlpha c h12 hSC α ∧
      (s0Orbit c α).card = 2 ∧
      restrictU c h12 μ.1 =
        fun u : ↥c.U => α.1 u + (conjIrrS c (c.S0_le_S (S0_generator_mem_S0 c)) α).1 u := by
  classical
  rcases orbit_is_orbitOfAlpha c h12 hSC μ with ⟨α, hOrbit⟩
  have hcard' : (orbitOfAlpha c h12 hSC α).card = 4 / (s0Orbit c α).card := by
    rw [orbitOfAlpha_card c h12 hSC α, hindex]
  have hle : (s0Orbit c α).card ≤ 2 := s0Orbit_card_le_two c hSC α
  have hpos : 0 < (s0Orbit c α).card :=
    Finset.card_pos.mpr ⟨α, s0Orbit_self_mem c α⟩
  have hcard2 : (s0Orbit c α).card = 2 := by
    have h2 : (orbitOfAlpha c h12 hSC α).card = 2 := by
      rw [← hOrbit]
      exact hcard
    rw [hcard'] at h2
    by_cases h1 : (s0Orbit c α).card = 1
    · rw [h1] at h2
      norm_num at h2
    · have h2' : (s0Orbit c α).card = 2 := by omega
      exact h2'
  have hnotfix : conjIrrS c (c.S0_le_S (S0_generator_mem_S0 c)) α ≠ α := by
    intro hfix
    have hsing := s0Orbit_eq_singleton_of_fixed c hSC α hfix
    rw [hsing] at hcard2
    norm_num at hcard2
  have hres : restrictU c h12 μ.1 =
      fun u : ↥c.U => α.1 u + (conjIrrS c (c.S0_le_S (S0_generator_mem_S0 c)) α).1 u := by
    have hspec := (orbitOfAlpha_spec c h12 hSC α).2 μ.1 (by
      simpa [hOrbit] using orbit_self_mem' c μ.1)
    rw [hspec]
    exact s0Orbit_sum_eq_α_add_r0_of_not_fixed c hSC α hnotfix
  exact ⟨α, hOrbit, hcard2, hres⟩

/-- Conjugation does not change the degree. -/
private lemma conjIrrS_degree_eq (c : Hyp11 G) {g : G} (hg : g ∈ (c.S : Subgroup G))
    (α : Irr (↥c.U)) :
    (conjIrrS c hg α).1 (1 : ↥c.U) = α.1 (1 : ↥c.U) := by
  unfold conjIrrS
  change α.1 ⟨g * (1 : G) * g⁻¹, _⟩ = α.1 (1 : ↥c.U)
  apply congrArg α.1
  apply Subtype.ext
  simp

/-- Evaluating the restriction at `1` gives the degree. -/
private lemma restrictU_one (c : Hyp11 G) (h12 : Hyp12 c) (ν : ClassFunction (↥c.H0)) :
    restrictU c h12 ν (1 : ↥c.U) = ν (1 : ↥c.H0) := by
  change ν ⟨(1 : G), (h12.U_normal_in_H0).1 (1 : ↥c.U).2⟩ = ν (1 : ↥c.H0)
  congr 1

/-- Degrees of irreducible characters are integers. -/
private lemma irr_one_int {H : Type u} [Group H] [Fintype H] (ν : Irr H) :
    ∃ a : ℤ, (ν.1 (1 : H) : ℂ) = (a : ℂ) := by
  classical
  rcases ν.2 with ⟨n, ρ, hρ, hEq⟩
  rw [hEq]
  refine ⟨(Module.finrank ℂ (Fin n → ℂ) : ℤ), ?_⟩
  rw [Representation.char_one]
  norm_num

/-- `4 ∣ χ(1)` in the false branch with `|Λμ| = 2`: the paper's
`χ(1) = ±2β(1) ± 2α(1) + m·x` formula from Lemma 1.7(ii) at `1`, Remark 3.1
degree sums, and odd degrees. -/
private lemma chi_one_quarter_int (c : Hyp11 G) (h12 : Hyp12 c) (hSC : Section3Hyp c)
    {χ : ClassFunction G} (hχ : IsPMIrr G χ)
    {ν μ : Irr (↥c.H0)}
    (hνB : ν ∈ BOf c h12 χ)
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 ≠ ν.1)
    (hνsL : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 ∈ orbit c.H0 c.U ν.1)
    (hμB : μ ∈ BOf c h12 χ) (hμν : μ ≠ ν) (hμνs : μ ≠ conjIrr c h12 ν)
    (hB : BOf c h12 χ = {ν, conjIrr c h12 ν, μ})
    (hΛν4 : (orbit c.H0 c.U ν.1).card = 4)
    (hΛμ2 : (orbit c.H0 c.U μ.1).card = 2)
    (hindex : (c.U.subgroupOf c.H0).index = 4) :
    ∃ k : ℤ, (χ 1 : ℂ) / 4 = (k : ℂ) := by
  classical
  have hχg : IsGeneralizedCharacter χ := by
    rcases hχ with hχ | hχ
    · exact ⟨χ, 0, isCharacter_of_isIrreducibleCharacter hχ, isCharacter_zero, by ext x; simp⟩
    · exact ⟨0, -χ, isCharacter_zero, isCharacter_of_isIrreducibleCharacter hχ, by ext x; simp⟩
  rcases exists_orbit_reps c h12 with ⟨ι, hι, rep, hrep_irr, hrep⟩
  let : Fintype ι := hι
  let iν : ι := Classical.choose (hrep ⟨ν.1, ν.2⟩)
  let iμ : ι := Classical.choose (hrep ⟨μ.1, μ.2⟩)
  have hnot : μ.1 ∉ orbit c.H0 c.U ν.1 :=
    mu_not_in_nu_orbit c h12 hχ hνB hνs hνsL hμB hμν hμνs
  -- an `s`-fixed member `ν'` of `Λν` outside `B(χ)`
  let Fν : Finset (ClassFunction (↥c.H0)) :=
    (orbit c.H0 c.U ν.1).filter (fun x =>
      conjChar c.H0 (s_normalizes_H0 c h12) x = x)
  have hFν : Fν.card = 2 := lemma_2_1_b c h12 ν.2 hνsL
  rcases Finset.card_eq_two.mp hFν with ⟨a₀, b₀, hab₀, hFνeq⟩
  have ha₀F : a₀ ∈ Fν := by rw [hFνeq]; simp
  let ν' : Irr (↥c.H0) := ⟨a₀, orbit_mem_isIrreducible c.H0 c.U ν.2
    (Finset.mem_filter.mp ha₀F).1⟩
  have hν'fix : conjChar c.H0 (s_normalizes_H0 c h12) ν'.1 = ν'.1 := by
    change conjChar c.H0 (s_normalizes_H0 c h12) a₀ = a₀
    exact (Finset.mem_filter.mp ha₀F).2
  have hν'L : ν'.1 ∈ orbit c.H0 c.U ν.1 := by
    change a₀ ∈ orbit c.H0 c.U ν.1
    exact (Finset.mem_filter.mp ha₀F).1
  have hν'ν : ν' ≠ ν := by
    intro hEq
    apply hνs
    have h' := congrArg Subtype.val hEq
    rw [← h']
    exact hν'fix
  have hν'νs : ν' ≠ conjIrr c h12 ν := by
    intro hEq
    apply hνs
    have hEq' : ν'.1 = conjChar c.H0 (s_normalizes_H0 c h12) ν.1 := by
      simpa [conjIrr_coe] using congrArg Subtype.val hEq
    have hconj := congrArg (conjChar c.H0 (s_normalizes_H0 c h12)) hEq'
    rw [← hν'fix, hEq'] at hconj
    rw [conjChar_conjChar c h12 ν.1] at hconj
    exact hconj
  have hν'μ : ν' ≠ μ :=
    irr_ne_of_orbits_distinct c hν'L (orbit_self_mem' c μ.1) hnot
  have hν'Bnot : ν' ∉ BOf c h12 χ := by
    intro hmem
    rw [hB] at hmem
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with hEq | hEq | hEq
    · exact hν'ν hEq
    · exact hν'νs hEq
    · exact hν'μ hEq
  have hpairν' : scalarProduct G χ (tildeNu c h12 ν') = 0 := by
    by_contra hne
    exact hν'Bnot ((BOf_mem_iff c h12 χ ν').2 hne)
  -- a member `μ'` of `Λμ` different from `μ` (hence outside `B(χ)`)
  have hone : 1 < (orbit c.H0 c.U μ.1).card := by rw [hΛμ2]; norm_num
  rcases Finset.one_lt_card_iff.mp hone with ⟨x₀, y₀, hx₀L, hy₀L, hxy₀⟩
  have hμ'ex : ∃ b₀ : ClassFunction (↥c.H0), b₀ ∈ orbit c.H0 c.U μ.1 ∧ b₀ ≠ μ.1 := by
    by_cases hxμ : x₀ = μ.1
    · exact ⟨y₀, hy₀L, fun hEq => hxy₀ (by simpa [hxμ] using hEq.symm)⟩
    · exact ⟨x₀, hx₀L, hxμ⟩
  rcases hμ'ex with ⟨b₀, hb₀L, hb₀ne⟩
  let μ' : Irr (↥c.H0) := ⟨b₀, orbit_mem_isIrreducible c.H0 c.U μ.2 hb₀L⟩
  have hμ'L : μ'.1 ∈ orbit c.H0 c.U μ.1 := by simpa [μ'] using hb₀L
  have hμ'μ : μ' ≠ μ := by
    intro hEq
    exact hb₀ne (congrArg Subtype.val hEq)
  have hnot' : ν.1 ∉ orbit c.H0 c.U μ.1 := by
    intro hL
    apply hnot
    have hEq := orbit_eq_of_mem c hL
    rw [hEq]
    exact orbit_self_mem' c μ.1
  have hμ'ν : μ' ≠ ν := irr_ne_of_orbits_distinct c hμ'L (orbit_self_mem' c ν.1) hnot'
  have hμ'νs : μ' ≠ conjIrr c h12 ν :=
    irr_ne_of_orbits_distinct c hμ'L (by simpa [conjIrr_coe] using hνsL) hnot'
  have hμ'Bnot : μ' ∉ BOf c h12 χ := by
    intro hmem
    rw [hB] at hmem
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with hEq | hEq | hEq
    · exact hμ'ν hEq
    · exact hμ'νs hEq
    · exact hμ'μ hEq
  have hpairμ' : scalarProduct G χ (tildeNu c h12 μ') = 0 := by
    by_contra hne
    exact hμ'Bnot ((BOf_mem_iff c h12 χ μ').2 hne)
  -- the modified system of representatives (all outside `B(χ)`)
  let rep' : ι → ClassFunction (↥c.H0) := fun i =>
    if i = iν then ν'.1 else if i = iμ then μ'.1 else rep i
  have hνμ_rep : iν ≠ iμ := by
    intro hEq
    have hspecν : ν.1 ∈ orbit c.H0 c.U (rep iν) :=
      (Classical.choose_spec (hrep ⟨ν.1, ν.2⟩)).1
    have hspecμ : μ.1 ∈ orbit c.H0 c.U (rep iμ) :=
      (Classical.choose_spec (hrep ⟨μ.1, μ.2⟩)).1
    rw [← hEq] at hspecμ
    have hOrEq : orbit c.H0 c.U ν.1 = orbit c.H0 c.U (rep iν) := orbit_eq_of_mem c hspecν
    have hμL : μ.1 ∈ orbit c.H0 c.U ν.1 := by
      rw [hOrEq]
      exact hspecμ
    exact hnot hμL
  have hrep'_irr : ∀ i : ι, IsIrreducibleCharacter (rep' i) := by
    intro i
    by_cases hi : i = iν
    · simpa [rep', hi] using ν'.2
    · by_cases hi' : i = iμ
      · subst hi'
        simpa [rep', hνμ_rep.symm] using μ'.2
      · simpa [rep', hi, hi'] using hrep_irr i
  have horbit_eq (i : ι) : orbit c.H0 c.U (rep' i) = orbit c.H0 c.U (rep i) := by
    by_cases hi : i = iν
    · subst hi
      have hspec : ν.1 ∈ orbit c.H0 c.U (rep iν) :=
        (Classical.choose_spec (hrep ⟨ν.1, ν.2⟩)).1
      have hEq1 : orbit c.H0 c.U (rep' iν) = orbit c.H0 c.U ν'.1 := by
        simp [rep']
      have hEq2 : orbit c.H0 c.U ν'.1 = orbit c.H0 c.U ν.1 := orbit_eq_of_mem c hν'L
      have hEq3 : orbit c.H0 c.U ν.1 = orbit c.H0 c.U (rep iν) := orbit_eq_of_mem c hspec
      rw [hEq1, hEq2, hEq3]
    · by_cases hi' : i = iμ
      · subst hi'
        have hspec : μ.1 ∈ orbit c.H0 c.U (rep iμ) :=
          (Classical.choose_spec (hrep ⟨μ.1, μ.2⟩)).1
        have hEq1 : orbit c.H0 c.U (rep' iμ) = orbit c.H0 c.U μ'.1 := by
          simp [rep', hi]
        have hEq2 : orbit c.H0 c.U μ'.1 = orbit c.H0 c.U μ.1 := orbit_eq_of_mem c hμ'L
        have hEq3 : orbit c.H0 c.U μ.1 = orbit c.H0 c.U (rep iμ) := orbit_eq_of_mem c hspec
        rw [hEq1, hEq2, hEq3]
      · simp [rep', hi, hi']
  have hrep' : ∀ ξ : {ν : ClassFunction (↥c.H0) // IsIrreducibleCharacter ν},
      ∃! i : ι, ξ.1 ∈ orbit c.H0 c.U (rep' i) := by
    intro ξ
    refine ⟨Classical.choose (hrep ξ), ?_, ?_⟩
    · have hmem : ξ.1 ∈ orbit c.H0 c.U (rep (Classical.choose (hrep ξ))) :=
        (Classical.choose_spec (hrep ξ)).1
      dsimp
      rw [horbit_eq (Classical.choose (hrep ξ))]
      exact hmem
    · intro i hi
      have hi' : ξ.1 ∈ orbit c.H0 c.U (rep i) := by
        rwa [horbit_eq i] at hi
      exact (Classical.choose_spec (hrep ξ)).2 i hi'
  have hrep'_pair_zero : ∀ i : ι,
      scalarProduct G χ (tildeNu c h12 ⟨rep' i, hrep'_irr i⟩) = 0 := by
    intro i
    by_cases hi : i = iν
    · subst hi
      simpa [rep'] using hpairν'
    · by_cases hi' : i = iμ
      · subst hi'
        simpa [rep', hi] using hpairμ'
      · have hnotB : (⟨rep i, hrep_irr i⟩ : Irr (↥c.H0)) ∉ BOf c h12 χ := by
          intro hmem
          rw [hB] at hmem
          rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hmem
          rcases hmem with hEq | hEq | hEq
          · have hEq' : rep i = ν.1 := congrArg Subtype.val hEq
            have hLν : ν.1 ∈ orbit c.H0 c.U (rep i) := by
              rw [hEq']
              exact orbit_self_mem' c ν.1
            have hEq'' : i = iν :=
              (Classical.choose_spec (hrep ⟨ν.1, ν.2⟩)).2 i hLν
            exact hi hEq''
          · have hLνs : (conjIrr c h12 ν).1 ∈ orbit c.H0 c.U (rep i) := by
              have hEq' : rep i = (conjIrr c h12 ν).1 := congrArg Subtype.val hEq
              rw [hEq']
              exact orbit_self_mem' c (conjIrr c h12 ν).1
            have hOrEq : orbit c.H0 c.U (rep i) = orbit c.H0 c.U ν.1 := by
              have h1 : orbit c.H0 c.U (conjIrr c h12 ν).1 = orbit c.H0 c.U (rep i) :=
                orbit_eq_of_mem c hLνs
              have h2 : orbit c.H0 c.U (conjIrr c h12 ν).1 = orbit c.H0 c.U ν.1 := by
                simpa [conjIrr_coe] using orbit_eq_of_mem c hνsL
              exact h1.symm.trans h2
            have hLν : ν.1 ∈ orbit c.H0 c.U (rep i) := by
              rw [hOrEq]
              exact orbit_self_mem' c ν.1
            have hEq'' : i = iν :=
              (Classical.choose_spec (hrep ⟨ν.1, ν.2⟩)).2 i hLν
            exact hi hEq''
          · have hEq' : rep i = μ.1 := congrArg Subtype.val hEq
            have hLμ : μ.1 ∈ orbit c.H0 c.U (rep i) := by
              rw [hEq']
              exact orbit_self_mem' c μ.1
            have hEq'' : i = iμ :=
              (Classical.choose_spec (hrep ⟨μ.1, μ.2⟩)).2 i hLμ
            exact hi' hEq''
        have hpair : scalarProduct G χ (tildeNu c h12 ⟨rep i, hrep_irr i⟩) = 0 := by
          by_contra hne
          exact hnotB ((BOf_mem_iff c h12 χ ⟨rep i, hrep_irr i⟩).2 hne)
        simpa [rep', hi, hi'] using hpair
  -- Fourier expansion at `1`
  have hii := lemma_1_7_ii c.H0 c.U rep' hrep'_irr hrep' χ hχg (1 : ↥c.H0)
  have hcoef (ξ : {ν : ClassFunction (↥c.H0) // IsIrreducibleCharacter ν}) :
      scalarProduct G χ (inducedClassFunction c.H0
        (ξ.1 - rep' (Classical.choose (hrep' ξ)))) =
        scalarProduct G χ (tildeNu c h12 ⟨ξ.1, ξ.2⟩) -
          scalarProduct G χ (tildeNu c h12 ⟨rep' (Classical.choose (hrep' ξ)), hrep'_irr _⟩) := by
    have hL : ξ.1 ∈ orbit c.H0 c.U (rep' (Classical.choose (hrep' ξ))) :=
      (Classical.choose_spec (hrep' ξ)).1
    have hind := tildeNu_ind c h12 (μ := ⟨ξ.1, ξ.2⟩)
      (ν := ⟨rep' (Classical.choose (hrep' ξ)), hrep'_irr _⟩) hL
    rw [hind, scalarProduct_sub_right]
  have hsum2 : (∑ ξ : {ν : ClassFunction (↥c.H0) // IsIrreducibleCharacter ν},
        scalarProduct G χ (inducedClassFunction c.H0
          (ξ.1 - rep' (Classical.choose (hrep' ξ)))) * ξ.1 (1 : ↥c.H0)) =
      (∑ ξ : {ν : ClassFunction (↥c.H0) // IsIrreducibleCharacter ν},
        scalarProduct G χ (tildeNu c h12 ⟨ξ.1, ξ.2⟩) * ξ.1 (1 : ↥c.H0)) := by
    refine Finset.sum_congr rfl ?_
    intro ξ hξ
    have hc := hcoef ξ
    have h0 : scalarProduct G χ (tildeNu c h12 ⟨rep' (Classical.choose (hrep' ξ)), hrep'_irr _⟩) = 0 :=
      hrep'_pair_zero (Classical.choose (hrep' ξ))
    rw [hc, h0]
    ring
  have hsum3 : (∑ ξ : {ν : ClassFunction (↥c.H0) // IsIrreducibleCharacter ν},
        scalarProduct G χ (tildeNu c h12 ⟨ξ.1, ξ.2⟩) * ξ.1 (1 : ↥c.H0)) =
      scalarProduct G χ (tildeNu c h12 ν) * ν.1 (1 : ↥c.H0) +
      scalarProduct G χ (tildeNu c h12 (conjIrr c h12 ν)) * (conjIrr c h12 ν).1 (1 : ↥c.H0) +
      scalarProduct G χ (tildeNu c h12 μ) * μ.1 (1 : ↥c.H0) := by
    have hpart : (∑ ξ : {ν : ClassFunction (↥c.H0) // IsIrreducibleCharacter ν},
          scalarProduct G χ (tildeNu c h12 ⟨ξ.1, ξ.2⟩) * ξ.1 (1 : ↥c.H0)) =
        ∑ ξ ∈ BOf c h12 χ, scalarProduct G χ (tildeNu c h12 ξ) * ξ.1 (1 : ↥c.H0) := by
      symm
      refine Finset.sum_subset (Finset.subset_univ (BOf c h12 χ)) ?_
      intro ξ hξuniv hξnot
      have hz : scalarProduct G χ (tildeNu c h12 ξ) = 0 := by
        by_contra hne
        exact hξnot ((BOf_mem_iff c h12 χ ξ).2 hne)
      simp [hz]
    have hνne : ν ≠ conjIrr c h12 ν := by
      intro hEq
      apply hνs
      have h' := congrArg Subtype.val hEq
      simpa [conjIrr_coe] using h'.symm
    rw [hpart, hB]
    rw [Finset.sum_insert]
    rw [Finset.sum_insert]
    rw [Finset.sum_singleton]
    ring
    · rw [Finset.mem_singleton]
      exact fun h => hμνs h.symm
    · rw [Finset.mem_insert, Finset.mem_singleton]
      push_neg
      exact ⟨hνne, fun h => hμν h.symm⟩
  have hνsdeg : (conjIrr c h12 ν).1 (1 : ↥c.H0) = ν.1 (1 : ↥c.H0) :=
    orbit_mem_degree_eq c (by simpa [conjIrr_coe] using hνsL)
  have hνdeg : ∃ d : ℕ, Odd d ∧ (d : ℂ) = ν.1 (1 : ↥c.H0) := by
    rcases orbit_restrict_full c h12 hSC hindex hΛν4 with ⟨β, hOrbitν, hresν⟩
    have hdegU : ν.1 (1 : ↥c.H0) = β.1 (1 : ↥c.U) := by
      have hc := congrFun hresν (1 : ↥c.U)
      rw [restrictU_one c h12 ν.1] at hc
      exact hc
    rcases irr_degree_odd (U_coprime_two c) β with ⟨d, hdOdd, hd⟩
    exact ⟨d, hdOdd, by rw [hdegU]; exact hd⟩
  have hμdeg : ∃ dα : ℕ, Odd dα ∧ (2 * dα : ℂ) = μ.1 (1 : ↥c.H0) := by
    rcases orbit_restrict_pair c h12 hSC hindex hΛμ2 with ⟨α, hOrbitμ, hcardα2, hresμ⟩
    have hdegU : μ.1 (1 : ↥c.H0) =
        α.1 (1 : ↥c.U) + (conjIrrS c (c.S0_le_S (S0_generator_mem_S0 c)) α).1 (1 : ↥c.U) := by
      have hc := congrFun hresμ (1 : ↥c.U)
      rw [restrictU_one c h12 μ.1] at hc
      exact hc
    rcases irr_degree_odd (U_coprime_two c) α with ⟨dα, hdαOdd, hdα⟩
    refine ⟨dα, hdαOdd, ?_⟩
    rw [hdegU, conjIrrS_degree_eq c (c.S0_le_S (S0_generator_mem_S0 c)) α, ← hdα]
    ring
  -- orbit degree sums are `4·αᵢ(1)`
  let α_i : ι → Irr (↥c.U) := fun i =>
    Classical.choose (orbit_is_orbitOfAlpha c h12 hSC ⟨rep' i, hrep'_irr i⟩)
  have hOrbit_i (i : ι) : orbit c.H0 c.U (rep' i) = orbitOfAlpha c h12 hSC (α_i i) :=
    Classical.choose_spec (orbit_is_orbitOfAlpha c h12 hSC ⟨rep' i, hrep'_irr i⟩)
  have hSi (i : ι) : orbitSum c.H0 c.U (rep' i) (1 : ↥c.H0) =
      (4 : ℂ) * (α_i i).1 (1 : ↥c.U) := by
    have hd := orbitOfAlpha_degree_sum c h12 hSC (α_i i)
    have hd' : (∑ ν ∈ orbitOfAlpha c h12 hSC (α_i i), ν 1) =
        (4 : ℂ) * (α_i i).1 (1 : ↥c.U) := by
      rw [hd, hindex]
      norm_num
    change (∑ ν ∈ orbit c.H0 c.U (rep' i), ν (1 : ↥c.H0)) =
      (4 : ℂ) * (α_i i).1 (1 : ↥c.U)
    rw [hOrbit_i]
    exact hd'
  let ai : ι → ℤ := fun i =>
    Classical.choose (restrict_scalarProduct_int c h12 hχ (rep' i) (hrep'_irr i))
  have hai (i : ι) : (ai i : ℂ) =
      scalarProduct (↥c.H0) (fun y : ↥c.H0 => χ (y : G)) (rep' i) := by
    simpa using (Classical.choose_spec (restrict_scalarProduct_int c h12 hχ (rep' i) (hrep'_irr i))).symm
  have hirr_int (i : ι) : ∃ a : ℤ, ((α_i i).1 (1 : ↥c.U) : ℂ) = (a : ℂ) := by
    exact irr_one_int (α_i i)
  let di : ι → ℤ := fun i => Classical.choose (hirr_int i)
  have hdi (i : ι) : ((α_i i).1 (1 : ↥c.U) : ℂ) = (di i : ℂ) :=
    Classical.choose_spec (hirr_int i)
  have hsum1 : (∑ i : ι, scalarProduct (↥c.H0) (fun y : ↥c.H0 => χ (y : G)) (rep' i) *
        orbitSum c.H0 c.U (rep' i) (1 : ↥c.H0)) =
      (∑ i : ι, (ai i : ℂ) * ((4 : ℂ) * (α_i i).1 (1 : ↥c.U))) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [← hai i, hSi i]
  have hX : ∃ X : ℤ, (∑ i : ι, (ai i : ℂ) * ((4 : ℂ) * (α_i i).1 (1 : ↥c.U))) =
      (4 * X : ℂ) := by
    have h1 : (∑ i : ι, (ai i : ℂ) * ((4 : ℂ) * (α_i i).1 (1 : ↥c.U))) =
        (4 : ℂ) * (∑ i : ι, (ai i : ℂ) * (di i : ℂ)) := by
      calc
        (∑ i : ι, (ai i : ℂ) * ((4 : ℂ) * (α_i i).1 (1 : ↥c.U)))
            = (∑ i : ι, (ai i : ℂ) * ((4 : ℂ) * (di i : ℂ))) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                rw [hdi i]
        _ = (∑ i : ι, (4 : ℂ) * ((ai i : ℂ) * (di i : ℂ))) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                ring
        _ = (4 : ℂ) * (∑ i : ι, (ai i : ℂ) * (di i : ℂ)) := by
                rw [Finset.mul_sum (s := Finset.univ) (f := fun i : ι => (ai i : ℂ) * (di i : ℂ))
                  (a := (4 : ℂ))]
    have h2 : ∃ z : ℤ, (z : ℂ) = ∑ i : ι, (ai i : ℂ) * (di i : ℂ) := by
      refine ⟨∑ i : ι, ai i * di i, ?_⟩
      norm_num
    rcases h2 with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    calc
      (∑ i : ι, (ai i : ℂ) * ((4 : ℂ) * (α_i i).1 (1 : ↥c.U)))
          = (4 : ℂ) * (∑ i : ι, (ai i : ℂ) * (di i : ℂ)) := h1
      _ = (4 : ℂ) * (z : ℂ) := by rw [hz]
  rcases hX with ⟨X, hX⟩
  have heνs : scalarProduct G χ (tildeNu c h12 (conjIrr c h12 ν)) =
      scalarProduct G χ (tildeNu c h12 ν) := by
    rw [tildeNu_invariance c h12 ν]
  have hχ1eq : χ 1 =
      scalarProduct G χ (tildeNu c h12 ν) * ν.1 (1 : ↥c.H0) +
      scalarProduct G χ (tildeNu c h12 ν) * (conjIrr c h12 ν).1 (1 : ↥c.H0) +
      scalarProduct G χ (tildeNu c h12 μ) * μ.1 (1 : ↥c.H0) + (4 * X : ℂ) := by
    change χ ((1 : ↥c.H0) : G) =
      scalarProduct G χ (tildeNu c h12 ν) * ν.1 (1 : ↥c.H0) +
      scalarProduct G χ (tildeNu c h12 ν) * (conjIrr c h12 ν).1 (1 : ↥c.H0) +
      scalarProduct G χ (tildeNu c h12 μ) * μ.1 (1 : ↥c.H0) + (4 * X : ℂ)
    rw [hii, hsum1, hX, hsum2, hsum3, heνs]
    ring
  rcases BOf_scalar_eq_pm_one c h12 hχ hνB with hν1 | hνm1
  · rcases BOf_scalar_eq_pm_one c h12 hχ hμB with hμ1 | hμm1
    · rcases hνdeg with ⟨dν, hdνOdd, hdν⟩
      rcases hμdeg with ⟨dα, hdαOdd, hdα⟩
      rcases hdνOdd with ⟨b, hb⟩
      rcases hdαOdd with ⟨a, ha⟩
      refine ⟨(b + a + X + 1 : ℤ), ?_⟩
      rw [hχ1eq, hν1, hμ1, hνsdeg, ← hdν, ← hdα, hb, ha]
      norm_num
      ring
    · rcases hνdeg with ⟨dν, hdνOdd, hdν⟩
      rcases hμdeg with ⟨dα, hdαOdd, hdα⟩
      rcases hdνOdd with ⟨b, hb⟩
      rcases hdαOdd with ⟨a, ha⟩
      refine ⟨(b - a + X : ℤ), ?_⟩
      rw [hχ1eq, hν1, hμm1, hνsdeg, ← hdν, ← hdα, hb, ha]
      norm_num
      ring
  · rcases BOf_scalar_eq_pm_one c h12 hχ hμB with hμ1 | hμm1
    · rcases hνdeg with ⟨dν, hdνOdd, hdν⟩
      rcases hμdeg with ⟨dα, hdαOdd, hdα⟩
      rcases hdνOdd with ⟨b, hb⟩
      rcases hdαOdd with ⟨a, ha⟩
      refine ⟨(a - b + X : ℤ), ?_⟩
      rw [hχ1eq, hνm1, hμ1, hνsdeg, ← hdν, ← hdα, hb, ha]
      norm_num
      ring
    · rcases hνdeg with ⟨dν, hdνOdd, hdν⟩
      rcases hμdeg with ⟨dα, hdαOdd, hdα⟩
      rcases hdνOdd with ⟨b, hb⟩
      rcases hdαOdd with ⟨a, ha⟩
      refine ⟨(X - a - b - 1 : ℤ), ?_⟩
      rw [hχ1eq, hνm1, hμm1, hνsdeg, ← hdν, ← hdα, hb, ha]
      norm_num
      ring

/-! ## Class sums and the quarter integrality step

Gorenstein 4.2.10: `|G : C_G(u)|·χ(u)/χ(1)` is an algebraic integer.  With
`4 ∣ χ(1)` and `4 ∤ |G : C_G(u)|` for `u ∈ C_U(t)` (`t ∈ S \ S0`), we get
`χ(u)/2` integral, i.e. `χ(u) ≡ 0 (mod 2)`.
-/

private lemma chi_one_ne_zero_of_isPMIrr {G : Type u} [Group G] [Fintype G]
    {χ : ClassFunction G} (hχ : IsPMIrr G χ) : χ 1 ≠ 0 := by
  rcases hχ with hχ | hχ
  · exact irreducible_char_one_ne_zero hχ
  · have h' : (-χ) 1 ≠ 0 := irreducible_char_one_ne_zero hχ
    simpa using h'

private lemma pmIrr_classSum_isIntegral {G : Type u} [Group G] [Fintype G]
    (χ : ClassFunction G) (hχ : IsPMIrr G χ) (g : G) :
    IsIntegral ℤ ((Nat.card (ConjClasses.mk g).carrier : ℂ) * χ g / χ 1) := by
  classical
  rcases hχ with hχpos | hχneg
  · rcases hχpos with ⟨n, ρ, hρ, rfl⟩
    have : Representation.IsIrreducible ρ := hρ
    have hsc := classSumScalar_eq_card_mul_character_div (ρ := ρ) (ConjClasses.mk g) (x := g)
      ((ConjClasses.mem_carrier_iff_mk_eq).2 rfl)
    have hint := classSumScalar_isIntegral (ρ := ρ) (ConjClasses.mk g)
    rw [hsc] at hint
    exact hint
  · have hχneg0 : IsIrreducibleCharacter (-χ) := hχneg
    rcases hχneg with ⟨n, ρ, hρ, hEq⟩
    have hneg : χ = -ρ.character := by simpa using congrArg Neg.neg hEq
    have hρchar : IsIrreducibleCharacter ρ.character := by simpa [hEq] using hχneg0
    have h1ne : ρ.character 1 ≠ 0 := irreducible_char_one_ne_zero hρchar
    have hmain : (Nat.card (ConjClasses.mk g).carrier : ℂ) * χ g / χ 1 =
        (Nat.card (ConjClasses.mk g).carrier : ℂ) * ρ.character g / ρ.character 1 := by
      rw [hneg]
      simp only [Pi.neg_apply]
      field_simp [h1ne]
    have : Representation.IsIrreducible ρ := hρ
    have hsc := classSumScalar_eq_card_mul_character_div (ρ := ρ) (ConjClasses.mk g) (x := g)
      ((ConjClasses.mem_carrier_iff_mk_eq).2 rfl)
    have hint := classSumScalar_isIntegral (ρ := ρ) (ConjClasses.mk g)
    rw [hsc] at hint
    rw [hmain]
    exact hint

private lemma pmIrr_quarter_degree_classSum_isIntegral {G : Type u} [Group G] [Fintype G]
    (χ : ClassFunction G) (hχ : IsPMIrr G χ) (g : G)
    (hquarter : ∃ k : ℤ, (χ 1 : ℂ) / 4 = (k : ℂ)) :
    IsIntegral ℤ (((χ 1 / 4) * (Nat.card (ConjClasses.mk g).carrier : ℂ) * χ g) / χ 1) := by
  classical
  have ha : IsIntegral ℤ ((Nat.card (ConjClasses.mk g).carrier : ℂ) * χ g / χ 1) :=
    pmIrr_classSum_isIntegral χ hχ g
  rcases hquarter with ⟨k, hk⟩
  have hkint : IsIntegral ℤ ((k : ℂ) * ((Nat.card (ConjClasses.mk g).carrier : ℂ) * χ g / χ 1)) :=
    (isIntegral_intCast k).mul ha
  have h1ne : χ 1 ≠ 0 := chi_one_ne_zero_of_isPMIrr hχ
  convert hkint using 1
  rw [← hk]
  field_simp [h1ne]

private lemma odd_bezout_four (n : ℕ) (hn : Odd n) : ∃ a b : ℤ, a * (n : ℤ) + b * 4 = 1 := by
  rcases hn with ⟨q, hq⟩
  refine ⟨(n : ℤ), -((q : ℤ) * ((q : ℤ) + 1)), ?_⟩
  rw [hq]
  push_cast
  ring

private lemma odd_bezout (n : ℕ) (hn : Odd n) : ∃ a b : ℤ, a * (n : ℤ) + b * 2 = 1 := by
  have hcop : Nat.Coprime 2 n := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    exact (by
      have h : ¬ Even n := Nat.not_even_iff_odd.mpr hn
      simpa [even_iff_two_dvd] using h)
  rcases (Nat.Coprime.isCoprime hcop) with ⟨a, b, h⟩
  refine ⟨b, a, ?_⟩
  simpa [add_comm, mul_comm] using h

private lemma card_conjClass_eq_index {G : Type u} [Group G] [Finite G] (x : G) :
    Nat.card (ConjClasses.mk x).carrier = (Subgroup.centralizer ({x} : Set G)).index := by
  classical
  have hst := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct G) x
  have hst' : Fintype.card (ConjClasses.mk x).carrier *
      Fintype.card (MulAction.stabilizer (ConjAct G) x) = Fintype.card G := by
    simpa [ConjAct.orbit_eq_carrier_conjClasses] using hst
  let e : MulAction.stabilizer (ConjAct G) x ≃ ↥(Subgroup.centralizer ({x} : Set G)) :=
    { toFun := fun y =>
        ⟨ConjAct.ofConjAct y.1, by
          rw [Subgroup.mem_centralizer_iff]
          intro z hz
          simp at hz
          rw [hz]
          have hy : y.1 • x = x := y.2
          rw [ConjAct.smul_def] at hy
          have hmain : ConjAct.ofConjAct y.1 * x = x * ConjAct.ofConjAct y.1 := by
            calc
              ConjAct.ofConjAct y.1 * x = (ConjAct.ofConjAct y.1 * x * (ConjAct.ofConjAct y.1)⁻¹) *
                  ConjAct.ofConjAct y.1 := by group
              _ = x * ConjAct.ofConjAct y.1 := by
                    rw [hy]
          exact hmain.symm⟩
      invFun := fun z => ⟨ConjAct.toConjAct (z : G), by
        change ConjAct.toConjAct (z : G) • x = x
        rw [ConjAct.toConjAct_smul]
        exact mul_inv_eq_of_eq_mul ((Subgroup.mem_centralizer_iff.mp z.2) x (by simp)).symm⟩
      left_inv := by intro y; apply Subtype.ext; rfl
      right_inv := by intro z; apply Subtype.ext; rfl }
  have hC : Fintype.card (MulAction.stabilizer (ConjAct G) x) =
      Nat.card (↥(Subgroup.centralizer ({x} : Set G))) := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_congr e
  have hN : (Subgroup.centralizer ({x} : Set G)).index *
      Fintype.card (MulAction.stabilizer (ConjAct G) x) = Fintype.card G := by
    rw [hC]
    rw [← Nat.card_eq_fintype_card]
    exact Subgroup.index_mul_card (Subgroup.centralizer ({x} : Set G))
  rw [Nat.card_eq_fintype_card]
  exact Nat.mul_right_cancel
    (by positivity : 0 < Fintype.card (MulAction.stabilizer (ConjAct G) x)) (by
      rw [← hN] at hst'
      exact hst')

/-- `χ(g)/2` is integral when `χ(1)/4` is integral and `4 ∤ |G : C_G(g)|`. -/
private lemma chi_half_isIntegral_of_index_not_dvd_four {G : Type u} [Group G] [Fintype G]
    (χ : ClassFunction G) (hχ : IsPMIrr G χ) (g : G)
    (hquarter : ∃ k : ℤ, (χ 1 : ℂ) / 4 = (k : ℂ))
    (hnot4 : ¬ 4 ∣ (Subgroup.centralizer ({g} : Set G)).index) :
    IsIntegral ℤ (χ g / 2) := by
  classical
  let n : ℕ := (Subgroup.centralizer ({g} : Set G)).index
  have hA : IsIntegral ℤ ((n : ℂ) * χ g / χ 1) := by
    change IsIntegral ℤ (((Subgroup.centralizer ({g} : Set G)).index : ℂ) * χ g / χ 1)
    rw [← card_conjClass_eq_index g]
    exact pmIrr_classSum_isIntegral χ hχ g
  have hB : IsIntegral ℤ (((χ 1 / 4) * (n : ℂ) * χ g) / χ 1) := by
    change IsIntegral ℤ (((χ 1 / 4) *
      ((Subgroup.centralizer ({g} : Set G)).index : ℂ) * χ g) / χ 1)
    rw [← card_conjClass_eq_index g]
    exact pmIrr_quarter_degree_classSum_isIntegral χ hχ g hquarter
  have h1ne : χ 1 ≠ 0 := chi_one_ne_zero_of_isPMIrr hχ
  have hA' : IsIntegral ℤ ((n : ℂ) * (χ g / 4)) := by
    have hEq : ((χ 1 / 4) * (n : ℂ) * χ g) / χ 1 = (n : ℂ) * (χ g / 4) := by
      field_simp [h1ne]
    rw [← hEq]
    exact hB
  have hχg : IsIntegral ℤ (χ g) := by
    rcases hχ with hχ | hχ
    · rcases hχ with ⟨n0, ρ, hρ, hEq⟩
      rw [hEq]
      exact character_value_isIntegral ρ g
    · rcases hχ with ⟨n0, ρ, hρ, hEq⟩
      have hEq' : χ g = -ρ.character g := by
        have hneg : χ = -ρ.character := by simpa using congrArg Neg.neg hEq
        simpa using congrFun hneg g
      rw [hEq']
      exact (character_value_isIntegral ρ g).neg
  by_cases hOdd : Odd n
  · rcases odd_bezout_four n hOdd with ⟨a, b, hab⟩
    have hq : IsIntegral ℤ (χ g / 4) := by
      have hcoef : (a : ℂ) * ((n : ℂ) * (χ g / 4)) + (b : ℂ) * χ g = χ g / 4 := by
        have hab' : (a : ℂ) * (n : ℂ) + (b : ℂ) * 4 = 1 := by exact_mod_cast hab
        calc
          (a : ℂ) * ((n : ℂ) * (χ g / 4)) + (b : ℂ) * χ g
              = ((a : ℂ) * (n : ℂ) + (b : ℂ) * 4) * (χ g / 4) := by ring
          _ = χ g / 4 := by rw [hab']; simp
      rw [← hcoef]
      exact ((isIntegral_intCast a).mul hA').add ((isIntegral_intCast b).mul hχg)
    have hhalf : IsIntegral ℤ (χ g / 2) := by
      have h' : χ g / 2 = (2 : ℂ) * (χ g / 4) := by ring
      rw [h']
      exact (isIntegral_intCast (2 : ℤ)).mul hq
    exact hhalf
  · have hEven : Even n := Nat.not_odd_iff_even.mp hOdd
    rcases hEven with ⟨m, hm⟩
    have hmOdd : Odd m := by
      by_contra hnot
      have hEvenM : Even m := Nat.not_odd_iff_even.mp hnot
      rcases hEvenM with ⟨k, hk⟩
      apply hnot4
      change 4 ∣ n
      rw [hm, hk]
      refine ⟨k, ?_⟩
      omega
    rcases odd_bezout m hmOdd with ⟨a, b, hab⟩
    have hA'' : IsIntegral ℤ ((m : ℂ) * (χ g / 2)) := by
      have hEq : (n : ℂ) * (χ g / 4) = (m : ℂ) * (χ g / 2) := by
        rw [hm]
        push_cast
        ring
      rw [← hEq]
      exact hA'
    have hhalf : IsIntegral ℤ (χ g / 2) := by
      have hcoef : (a : ℂ) * ((m : ℂ) * (χ g / 2)) + (b : ℂ) * χ g = χ g / 2 := by
        have hab' : (a : ℂ) * (m : ℂ) + (b : ℂ) * 2 = 1 := by exact_mod_cast hab
        calc
          (a : ℂ) * ((m : ℂ) * (χ g / 2)) + (b : ℂ) * χ g
              = ((a : ℂ) * (m : ℂ) + (b : ℂ) * 2) * (χ g / 2) := by ring
          _ = χ g / 2 := by rw [hab']; simp
      rw [← hcoef]
      exact ((isIntegral_intCast a).mul hA'').add ((isIntegral_intCast b).mul hχg)
    exact hhalf

private lemma chi_congruent_zero_of_half_isIntegral {G : Type u} [Group G] [Fintype G]
    (χ : ClassFunction G) (g : G) (hhalf : IsIntegral ℤ (χ g / 2)) :
    CongruentModTwo (χ g) 0 := by
  refine ⟨χ g / 2, hhalf, ?_⟩
  ring

private lemma SPrime_card_two (c : Hyp11 G) (hS8 : Nat.card (↥(c.S : Subgroup G)) = 8) :
    Nat.card (SPrime c : Subgroup G) = 2 := by
  have hS0 : Nat.card (c.S0 : Subgroup G) = 4 := by
    have h2 : 2 * Nat.card (c.S0 : Subgroup G) = Nat.card (c.S : Subgroup G) := by
      rw [c.S_index_two]
    rw [hS8] at h2
    omega
  have hm : c.m = 2 := by
    have hpow : 2 ^ c.m = 4 := by
      rw [← S0_nat_card c]
      exact hS0
    have h' : 2 ^ c.m = 2 ^ 2 := by
      rw [hpow]
      norm_num
    exact Nat.pow_right_injective (by norm_num : (2 : ℕ) ≤ 2) h'
  have hSP : Nat.card (SPrime c : Subgroup G) = 2 ^ (c.m - 1) := by
    dsimp [SPrime]
    rw [Nat.card_zpowers]
    have hz2 : orderOf ((c.t1 * c.t2) ^ 2) = 2 ^ (c.m - 1) := by
      have hz : orderOf (c.t1 * c.t2) = 2 ^ c.m := by
        have hc : Nat.card (Subgroup.zpowers (c.t1 * c.t2) : Subgroup G) = 2 ^ c.m := by
          rw [← c.S0_eq_zpowers]
          exact S0_nat_card c
        rw [← Nat.card_zpowers]
        exact hc
      have h2dvd : 2 ∣ orderOf (c.t1 * c.t2) := by
        rw [hz, hm]
        norm_num
      rw [orderOf_pow_of_dvd (x := c.t1 * c.t2) (n := 2) (by norm_num : (2 : ℕ) ≠ 0) h2dvd, hz, hm]
      norm_num
    exact hz2
  rw [hSP, hm]
  norm_num

/-- `4 ∤ |G : C_G(u)|` for `u ∈ C_U(t)` with `t ∈ S \ S0` an involution
(in the `|S| = 8` false-branch situation). -/
private lemma not_four_dvd_index_of_mem_centralizerIn (c : Hyp11 G) (hSC : Section3Hyp c)
    (hS8 : Nat.card (↥(c.S : Subgroup G)) = 8)
    {t : G} (htS : t ∈ (c.S : Subgroup G)) (htS0 : t ∉ (c.S0 : Subgroup G))
    (ht2 : t * t = 1) {u : G} (huB : u ∈ centralizerIn c.U t) :
    ¬ 4 ∣ (Subgroup.centralizer ({u} : Set G)).index := by
  classical
  let H : Subgroup G := SPrime c ⊔ Subgroup.zpowers t
  have hHleC : H ≤ Subgroup.centralizer ({u} : Set G) := by
    refine sup_le ?_ ?_
    · intro s hs
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hy' : y = u := by simpa using hy
      subst y
      have huU : u ∈ c.U := (Subgroup.mem_inf.mp huB).1
      have hc : s ∈ Subgroup.centralizer ((c.U : Subgroup G) : Set G) := hSC hs
      exact (Subgroup.mem_centralizer_iff.mp hc) u huU
    · intro s hs
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hy' : y = u := by simpa using hy
      subst y
      have huc : u ∈ Subgroup.centralizer ({t} : Set G) := (Subgroup.mem_inf.mp huB).2
      have hcomm : Commute u t :=
        ((Subgroup.mem_centralizer_iff.mp huc) t (by simp)).symm
      have hcomm' : Commute t u := hcomm.symm
      rcases (Subgroup.mem_zpowers_iff.mp hs) with ⟨k, hk⟩
      exact (by simpa [hk] using (hcomm'.zpow_left k).eq.symm)
  have hHleS : H ≤ (c.S : Subgroup G) := by
    refine sup_le ?_ ?_
    · exact le_trans (SPrime_le_S0 c) (c.S0_le_S)
    · rw [Subgroup.zpowers_le]
      exact htS
  have hCdiv : (Subgroup.centralizer ({u} : Set G)).index ∣ H.index :=
    Subgroup.index_dvd_of_le hHleC
  have hoddS : Odd (c.S : Subgroup G).index := by
    have hnot : ¬ 2 ∣ (c.S : Subgroup G).index := c.S.not_dvd_index
    exact (Nat.not_even_iff_odd.mp (by simpa [even_iff_two_dvd] using hnot))
  have hrel : H.relIndex (c.S : Subgroup G) * (c.S : Subgroup G).index = H.index :=
    H.relIndex_mul_index hHleS
  let r : ℕ := H.relIndex (c.S : Subgroup G)
  have hcardrel : r * Nat.card (↥(H.subgroupOf (c.S : Subgroup G))) =
      Nat.card (↥(c.S : Subgroup G)) := by
    have h := Subgroup.index_mul_card (H := H.subgroupOf (c.S : Subgroup G))
      (G := (c.S : Subgroup G))
    rw [show r = (H.subgroupOf (c.S : Subgroup G)).index by rfl]
    exact h
  have hcardH : 4 ≤ Nat.card ↥H := by
    have ha : (c.t1 * c.t2) ^ 2 ∈ H := by
      exact SetLike.le_def.mp le_sup_left (SPrime_mem_pow_two c)
    have hb : t ∈ H := by
      exact SetLike.le_def.mp le_sup_right (Subgroup.mem_zpowers t)
    let a : ↥H := ⟨(c.t1 * c.t2) ^ 2, ha⟩
    let b : ↥H := ⟨t, hb⟩
    have hord : orderOf (c.t1 * c.t2) = 4 := by
      have hS0 : Nat.card (c.S0 : Subgroup G) = 4 := by
        have h2 : 2 * Nat.card (c.S0 : Subgroup G) = Nat.card (c.S : Subgroup G) := by
          rw [c.S_index_two]
        rw [hS8] at h2
        omega
      have hz : Nat.card (Subgroup.zpowers (c.t1 * c.t2) : Subgroup G) = 4 := by
        rw [← c.S0_eq_zpowers]
        exact hS0
      rw [Nat.card_zpowers] at hz
      exact hz
    have ha_ne : a ≠ 1 := by
      intro hEq
      have h' : (c.t1 * c.t2) ^ 2 = 1 := congrArg Subtype.val hEq
      have hdvd : orderOf (c.t1 * c.t2) ∣ 2 := by
        exact (orderOf_dvd_iff_pow_eq_one).mpr h'
      rw [hord] at hdvd
      omega
    have ha_sq : a * a = 1 := by
      apply Subtype.ext
      change (c.t1 * c.t2) ^ 2 * (c.t1 * c.t2) ^ 2 = 1
      have h4 : (c.t1 * c.t2) ^ orderOf (c.t1 * c.t2) = 1 := pow_orderOf_eq_one (c.t1 * c.t2)
      have hEq : ((c.t1 * c.t2) ^ 2) ^ 2 = (c.t1 * c.t2) ^ 4 := by
        exact (pow_mul (c.t1 * c.t2) 2 2).symm
      rw [← pow_two (a := (c.t1 * c.t2) ^ 2)]
      rw [hEq, ← hord, h4]
    have hb_ne : b ≠ 1 := by
      intro hEq
      have h' : t = 1 := congrArg Subtype.val hEq
      apply htS0
      rw [h']
      simp
    have hb_sq : b * b = 1 := by
      apply Subtype.ext
      simpa using ht2
    have hab : a ≠ b := by
      intro hEq
      have h' : (c.t1 * c.t2) ^ 2 = t := congrArg Subtype.val hEq
      apply htS0
      rw [← h']
      exact SPrime_le_S0 c (SPrime_mem_pow_two c)
    have hb_inv : b⁻¹ = b := by
      exact (inv_eq_iff_mul_eq_one.mpr hb_sq)
    have ha_inv : a⁻¹ = a := by
      exact (inv_eq_iff_mul_eq_one.mpr ha_sq)
    have hprod1 : a * b ≠ 1 := by
      intro hEq
      apply hab
      have h : a = b⁻¹ := mul_eq_one_iff_eq_inv.mp hEq
      have h' : a = b := by rwa [hb_inv] at h
      exact h'
    have hproda : a * b ≠ a := by
      intro hEq
      apply hb_ne
      have h' : b = 1 := by
        have h'' : a * b = a * 1 := by simpa using hEq
        exact mul_left_cancel h''
      exact h'
    have hprodb : a * b ≠ b := by
      intro hEq
      apply ha_ne
      have h' : a = 1 := by
        have h'' : a * b = 1 * b := by simpa using hEq
        exact mul_right_cancel h''
      exact h'
    let f : Fin 4 → ↥H := ![1, a, b, a * b]
    have hinj : Function.Injective f := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp [f, ha_ne, ha_ne.symm, hb_ne, hb_ne.symm, hab,
        hab.symm, hprod1, hprod1.symm, hproda, hproda.symm, hprodb, hprodb.symm]
        at hij ⊢
    have hle : Fintype.card (Fin 4) ≤ Fintype.card ↥H := Fintype.card_le_of_injective f hinj
    simpa using hle
  have hcardrel' : Nat.card (↥(H.subgroupOf (c.S : Subgroup G))) = Nat.card ↥H := by
    let e : (H.subgroupOf (c.S : Subgroup G)) ≃* H :=
      Subgroup.subgroupOfEquivOfLe (H := H) (K := (c.S : Subgroup G)) hHleS
    exact Nat.card_congr e.toEquiv
  have hrle : r ≤ 2 := by
    have h8 : Nat.card (↥(c.S : Subgroup G)) = 8 := hS8
    have h1 : r * 4 ≤ r * Nat.card (↥(H.subgroupOf (c.S : Subgroup G))) := by
      exact Nat.mul_le_mul_left r (by
        rw [hcardrel']
        exact hcardH)
    rw [hcardrel, h8] at h1
    omega
  have hnotH : ¬ 4 ∣ H.index := by
    intro h4
    have hrpos : 1 ≤ r := by
      have h' : 0 < r * Nat.card (↥(H.subgroupOf (c.S : Subgroup G))) := by
        rw [hcardrel]
        exact Nat.card_pos (α := ↥(c.S : Subgroup G))
      have h'' : 0 < r := by
        exact Nat.pos_of_mul_pos_right h'
      omega
    have hoddS' : ¬ 2 ∣ (c.S : Subgroup G).index := by
      intro h2
      exact (Nat.not_even_iff_odd.mpr hoddS) ((even_iff_two_dvd).mpr h2)
    by_cases hr1 : r = 1
    · have h4S : 4 ∣ (c.S : Subgroup G).index := by
        have h' : H.index = (c.S : Subgroup G).index := by
          rw [← hrel]
          change r * (c.S : Subgroup G).index = (c.S : Subgroup G).index
          rw [hr1]
          simp [r]
        rwa [h'] at h4
      have h2S : 2 ∣ (c.S : Subgroup G).index := by
        rcases h4S with ⟨k, hk⟩
        refine ⟨2 * k, ?_⟩
        omega
      exact hoddS' h2S
    · have hr2 : r = 2 := by omega
      have h4S : 4 ∣ 2 * (c.S : Subgroup G).index := by
        rw [← hrel] at h4
        change 4 ∣ r * (c.S : Subgroup G).index at h4
        rwa [hr2] at h4
      have h2S : 2 ∣ (c.S : Subgroup G).index := by
        rcases h4S with ⟨k, hk⟩
        refine ⟨k, ?_⟩
        omega
      exact hoddS' h2S
  intro h4
  exact hnotH (dvd_trans h4 hCdiv)

/-- `χ ≡ 0 (mod 2)` on `C_U(t)` for `t ∈ S \ S0` an involution, given
`4 ∣ χ(1)` and `|S| = 8`. -/
private lemma chi_congruent_zero_on_centralizerIn (c : Hyp11 G) (h12 : Hyp12 c)
    (hSC : Section3Hyp c) {χ : ClassFunction G} (hχ : IsPMIrr G χ)
    (hquarter : ∃ k : ℤ, (χ 1 : ℂ) / 4 = (k : ℂ))
    (hS8 : Nat.card (↥(c.S : Subgroup G)) = 8)
    {t : G} (htS : t ∈ (c.S : Subgroup G)) (htS0 : t ∉ (c.S0 : Subgroup G))
    (ht2 : t * t = 1) {u : G} (huB : u ∈ centralizerIn c.U t) :
    CongruentModTwo (χ u) 0 := by
  classical
  have hnot4 := not_four_dvd_index_of_mem_centralizerIn c hSC hS8 htS htS0 ht2 huB
  have hhalf : IsIntegral ℤ (χ u / 2) :=
    chi_half_isIntegral_of_index_not_dvd_four χ hχ u hquarter hnot4
  exact chi_congruent_zero_of_half_isIntegral χ u hhalf

/-! ## Final contradiction on `C_U(t)`

With `|Λμ| = 2`, Remark 3.1 gives `S_α = S'⟨t1⟩` or `S'⟨t2⟩` (both `α` and
its `S0`-conjugate `α₂` are then fixed by the chosen involution `t`), the
class-sum step gives `χ ≡ 0` on `C_U(t)`, and Lemma 2.4 gives
`χ ≡ α₁ + α₂` there; Lemma 1.8 + Lemma 1.9 (Glauberman correspondence)
contradict `α₁ + α₂ ≡ 0` on the fixed subgroup.
-/

/-- `⟨t⟩` normalizes `U` for `t ∈ S \ S0`. -/
private lemma SPrime_t_le_normalizer_U (c : Hyp11 G) (_hSC : Section3Hyp c)
    {t : G} (htS : t ∈ (c.S : Subgroup G)) :
    SPrime c ⊔ Subgroup.zpowers t ≤ Subgroup.normalizer (c.U : Set G) := by
  refine sup_le ?_ ?_
  · intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · intro hu
      exact S_normalizes_U c x (c.S0_le_S (SPrime_le_S0 c hx)) u hu
    · intro hsu
      have hxS : x ∈ (c.S : Subgroup G) := c.S0_le_S (SPrime_le_S0 c hx)
      have h1 := S_normalizes_U c x⁻¹ ((c.S : Subgroup G).inv_mem hxS) (x * u * x⁻¹) hsu
      have h2 : x⁻¹ * (x * u * x⁻¹) * (x⁻¹)⁻¹ = u := by group
      rwa [h2] at h1
  · intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · intro hu
      have hxS : x ∈ (c.S : Subgroup G) := (Subgroup.zpowers_le.mpr htS) hx
      exact S_normalizes_U c x hxS u hu
    · intro hsu
      have hxS : x ∈ (c.S : Subgroup G) := (Subgroup.zpowers_le.mpr htS) hx
      have h1 := S_normalizes_U c x⁻¹ ((c.S : Subgroup G).inv_mem hxS) (x * u * x⁻¹) hsu
      have h2 : x⁻¹ * (x * u * x⁻¹) * (x⁻¹)⁻¹ = u := by group
      rwa [h2] at h1

/-- `conjIrrS` does not depend on the proof of membership in `S`. -/
private lemma conjIrrS_proof_irrel (c : Hyp11 G) {g : G} (hg hg' : g ∈ (c.S : Subgroup G))
    (α : Irr (↥c.U)) : conjIrrS c hg α = conjIrrS c hg' α := by
  apply Subtype.ext
  funext u
  simp only [conjIrrS, conjChar, conjMonoidHom]

/-- `conjIrrS` respects equality of the conjugating element. -/
private lemma conjIrrS_eq_of_elements_eq (c : Hyp11 G) {a b : G}
    (ha : a ∈ (c.S : Subgroup G)) (hb : b ∈ (c.S : Subgroup G)) (hab : a = b)
    (α : Irr (↥c.U)) : conjIrrS c ha α = conjIrrS c hb α := by
  cases hab
  exact conjIrrS_proof_irrel c ha hb α

/-- If `t ∈ S \ S0` is an involution fixing `α ∈ Irr(U)`, then `α` is fixed
by the subgroup `⟨t⟩` acting on `U`. -/
private lemma fixedIrr_of_conjIrrS (c : Hyp11 G) (_hSC : Section3Hyp c)
    {t : G} (htS : t ∈ (c.S : Subgroup G)) (htS0 : t ∉ (c.S0 : Subgroup G)) (ht2 : t * t = 1)
    [Subgroup.Normalizes (Subgroup.zpowers t) c.U]
    {α : Irr (↥c.U)} (hfix : conjIrrS c htS α = α) :
    FixedIrr (↥(Subgroup.zpowers t)) (↥c.U) α := by
  classical
  unfold FixedIrr
  intro s
  funext u
  rcases (Subgroup.mem_zpowers_iff.mp s.2) with ⟨k, hk⟩
  have hsq : t ^ 2 = 1 := by simpa [pow_two] using ht2
  have ht1 : t ≠ 1 := by
    intro h
    apply htS0
    rw [h]
    simp
  have horder : orderOf t = 2 := by
    exact orderOf_eq_prime (p := 2) (by simpa [pow_two] using ht2) ht1
  have hmod : t ^ (k % (orderOf t : ℤ)) = t ^ k := zpow_mod_orderOf t k
  have hem : k % (2 : ℤ) = 0 ∨ k % (2 : ℤ) = 1 := by omega
  rcases hem with h0 | h1
  · have hk1 : t ^ k = 1 := by
      rw [← hmod, horder]
      simp [h0]
    have hsmul : s • u = u := by
      apply Subtype.ext
      simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hk.symm, hk1]
    rw [hsmul]
  · have hkodd : t ^ k = t := by
      rw [← hmod, horder]
      simp [h1]
    have hsmul : s • u = ⟨t * (u : G) * t⁻¹, S_normalizes_U c t htS (u : G) u.2⟩ := by
      apply Subtype.ext
      simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hk.symm, hkodd]
    rw [hsmul]
    have heq := congrFun (congrArg Subtype.val hfix) u
    change α.1 ⟨t * (u : G) * t⁻¹, _⟩ = α.1 u
    exact heq

/-- Lemma 1.8 + Lemma 1.9: `α₁ + α₂` cannot be `≡ 0 (mod 2)` on the fixed
subgroup `C_U(t)` when `t` fixes both `α₁` and `α₂` (distinct odd-degree
characters of the odd group `U`). -/
private lemma not_congruent_sum_two_on_fixed (c : Hyp11 G) (h12 : Hyp12 c) (hSC : Section3Hyp c)
    {χ : ClassFunction G} (hχ : IsPMIrr G χ)
    {ν μ : Irr (↥c.H0)}
    (_hνB : ν ∈ BOf c h12 χ) (_hμB : μ ∈ BOf c h12 χ)
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 ≠ ν.1)
    (hμν : μ ≠ ν) (hμνs : μ ≠ conjIrr c h12 ν)
    (hB : BOf c h12 χ = {ν, conjIrr c h12 ν, μ})
    {β α α₂ : Irr (↥c.U)}
    (hresν : restrictU c h12 ν.1 = β.1)
    (hresνs : restrictU c h12 (conjIrr c h12 ν).1 = β.1)
    (hresμ : restrictU c h12 μ.1 = fun u => α.1 u + α₂.1 u)
    {t : G} (htS : t ∈ (c.S : Subgroup G)) (htS0 : t ∉ (c.S0 : Subgroup G)) (ht2 : t * t = 1)
    (htfix₁ : conjIrrS c htS α = α) (htfix₂ : conjIrrS c htS α₂ = α₂)
    (hαne : α ≠ α₂)
    [Subgroup.Normalizes (Subgroup.zpowers t) c.U]
    (hχ0 : ∀ b : ↥(fixedSubgroup (↥(Subgroup.zpowers t)) (↥c.U)),
      CongruentModTwo (χ (b.1.1 : G)) 0) :
    False := by
  classical
  let B : Subgroup (↥c.U) := fixedSubgroup (↥(Subgroup.zpowers t)) (↥c.U)
  have hfixα : FixedIrr (↥(Subgroup.zpowers t)) (↥c.U) α :=
    fixedIrr_of_conjIrrS c hSC htS htS0 ht2 htfix₁
  have hfixα₂ : FixedIrr (↥(Subgroup.zpowers t)) (↥c.U) α₂ :=
    fixedIrr_of_conjIrrS c hSC htS htS0 ht2 htfix₂
  have hcong (b : ↥B) : CongruentModTwo (χ (b.1.1 : G)) (α.1 b.1 + α₂.1 b.1) := by
    let u : ↥c.U := b.1
    have hu : (u : G) ∈ c.H0 := U_le_H0 c u.2
    have h24 := (lemma_2_4 c h12 hχ).2 u hu
    have hνne : ν ≠ conjIrr c h12 ν := by
      intro hEq
      apply hνs
      have h' := congrArg Subtype.val hEq
      simpa [conjIrr_coe] using h'.symm
    have hsumEq : (∑ φ ∈ BOf c h12 χ, φ.1 ⟨(u : G), hu⟩) =
        ν.1 ⟨(u : G), hu⟩ + (conjIrr c h12 ν).1 ⟨(u : G), hu⟩ + μ.1 ⟨(u : G), hu⟩ := by
      rw [hB]
      rw [Finset.sum_insert]
      rw [Finset.sum_insert]
      rw [Finset.sum_singleton]
      ring
      · rw [Finset.mem_singleton]
        exact fun h => hμνs h.symm
      · rw [Finset.mem_insert, Finset.mem_singleton]
        push_neg
        exact ⟨hνne, fun h => hμν h.symm⟩
    have hsum : CongruentModTwo (χ (u : G))
        (ν.1 ⟨(u : G), hu⟩ + (conjIrr c h12 ν).1 ⟨(u : G), hu⟩ + μ.1 ⟨(u : G), hu⟩) :=
      h24.trans (CongruentModTwo.of_eq hsumEq)
    have hv : ν.1 ⟨(u : G), hu⟩ = β.1 u := by
      have he := congrFun hresν u
      simpa [restrictU] using he
    have hvs : (conjIrr c h12 ν).1 ⟨(u : G), hu⟩ = β.1 u := by
      have he := congrFun hresνs u
      simpa [restrictU] using he
    have hμv : μ.1 ⟨(u : G), hu⟩ = α.1 u + α₂.1 u := by
      have he := congrFun hresμ u
      simpa [restrictU] using he
    have hχβ : CongruentModTwo (χ (u : G)) (2 * β.1 u + (α.1 u + α₂.1 u)) := by
      have hEq : ν.1 ⟨(u : G), hu⟩ + (conjIrr c h12 ν).1 ⟨(u : G), hu⟩ + μ.1 ⟨(u : G), hu⟩ =
          2 * β.1 u + (α.1 u + α₂.1 u) := by
        rw [hv, hvs, hμv]
        ring
      exact hsum.trans (CongruentModTwo.of_eq hEq)
    have hβint : IsIntegral ℤ (β.1 u) := by
      rcases β.2 with ⟨n, ρ, hρ, hEq⟩
      rw [hEq]
      exact character_value_isIntegral ρ u
    have h2β0 : CongruentModTwo (2 * β.1 u) 0 := CongruentModTwo.two_mul_zero hβint
    have hγ : CongruentModTwo (α.1 u + α₂.1 u) (α.1 u + α₂.1 u) := CongruentModTwo.refl _
    have hstep : CongruentModTwo (2 * β.1 u + (α.1 u + α₂.1 u)) (α.1 u + α₂.1 u) := by
      have h' := CongruentModTwo.add h2β0 hγ
      exact h'.trans (CongruentModTwo.of_eq (by ring))
    have hmain := hχβ.trans hstep
    change CongruentModTwo (χ (b.1.1 : G)) (α.1 b.1 + α₂.1 b.1)
    simpa [u] using hmain
  have h0 : ∀ b : ↥B, CongruentModTwo (α.1 b.1 + α₂.1 b.1) 0 := by
    intro b
    exact (hcong b).symm.trans (hχ0 b)
  have hcorr := glauberman_correspondence (S := ↥(Subgroup.zpowers t)) (U := ↥c.U)
    (by
      have horder : orderOf t = 2 := by
        exact orderOf_eq_prime (p := 2) (by simpa [pow_two] using ht2)
          (by intro h; apply htS0; rw [h]; simp)
      have hcard : Nat.card (↥(Subgroup.zpowers t)) = 2 := by
        rw [Nat.card_zpowers, horder]
      exact IsPGroup.of_card (p := 2) (n := 1) (by rw [hcard]; norm_num))
    (U_coprime_two c)
  rcases hcorr with ⟨e, he⟩
  let β₁ : IrrBG19 (↥B) := e ⟨α, hfixα⟩
  let β₂ : IrrBG19 (↥B) := e ⟨α₂, hfixα₂⟩
  have hβne : β₁ ≠ β₂ := by
    intro hEq
    apply hαne
    have h' : (⟨α, hfixα⟩ : {α : IrrBG19 (↥c.U) // FixedIrr (↥(Subgroup.zpowers t)) (↥c.U) α}) =
        ⟨α₂, hfixα₂⟩ := by
      simpa [β₁, β₂] using congrArg e.symm hEq
    exact congrArg Subtype.val h'
  have hB2' : Nat.Coprime 2 (Nat.card (↥B)) := by
    exact Nat.Coprime.of_dvd_right
      (Subgroup.card_subgroup_dvd_card B) (U_coprime_two c)
  let I : Type u := ULift.{u} (Fin 2)
  let β : I → ClassFunction (↥B) := fun i => if i.down = 0 then β₁.1 else β₂.1
  have hβirr : ∀ i : I, IsIrreducibleCharacter (β i) := by
    intro i
    rcases i with ⟨i⟩
    fin_cases i
    · simpa [β] using β₁.2
    · simpa [β] using β₂.2
  have hβne' : β₁.1 ≠ β₂.1 := by
    intro hEq
    apply hβne
    exact Subtype.ext hEq
  have hβdist : Pairwise fun i j : I => β i ≠ β j := by
    intro i j hij
    rcases i with ⟨i⟩
    rcases j with ⟨j⟩
    fin_cases i <;> fin_cases j <;> simp [β, hβne', hβne'.symm] at hij ⊢
  have hsum (b : ↥B) : (∑ i : I, (1 : ℂ) * β i b) = β₁.1 b + β₂.1 b := by
    have huniv : (Finset.univ : Finset I) =
        ({ULift.up (0 : Fin 2), ULift.up 1} : Finset I) := by
      ext i
      rcases i with ⟨i⟩
      fin_cases i <;> simp
    rw [huniv, Finset.sum_pair]
    · simp [β]
    · intro hEq
      exact (by norm_num : (0 : Fin 2) ≠ 1) (ULift.up.inj hEq)
  have h0' : ∀ b : ↥B, CongruentModTwo (∑ i : I, (1 : ℂ) * β i b) 0 := by
    intro b
    have hαβ : CongruentModTwo (α.1 b.1 + α₂.1 b.1) (β₁.1 b + β₂.1 b) := by
      have h1 := he ⟨α, hfixα⟩ b
      have h2 := he ⟨α₂, hfixα₂⟩ b
      exact h1.add h2
    have hβ0 : CongruentModTwo (β₁.1 b + β₂.1 b) 0 := hαβ.symm.trans (h0 b)
    exact (CongruentModTwo.of_eq (hsum b)).trans hβ0
  have h18 := lemma_1_8 (B := ↥B) hB2' (I := I) (β := β) (c := fun _ => 1)
    hβirr hβdist (hc := by intro i; exact isIntegral_one) h0' (i := ULift.up (0 : Fin 2))
  have h1' : CongruentModTwo (1 : ℂ) 0 := by
    simpa [I, β] using h18
  exact (CongruentModTwo.not_zero_of_odd_nat (n := 1) (by norm_num)) (by simpa using h1'.symm)

/-- Lemma 3.4: if `B(χ)` contains a character `ν` not fixed by `s` with
`ν^s ∉ Λν` or `|Λν| = m`, then `B(χ) = {ν, ν^s}` and `ν̃(t) = 2ν(t)`. -/
public theorem lemma_3_4 (c : Hyp11 G) (h12 : Hyp12 c) (hSC : Section3Hyp c)
    {χ : ClassFunction G} (hχ : IsPMIrr G χ) {ν : Irr (↥c.H0)}
    (hν : ν ∈ BOf c h12 χ)
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 ≠ ν.1)
    (hνL : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 ∉ orbit c.H0 c.U ν.1 ∨
      (orbit c.H0 c.U ν.1).card = (c.U.subgroupOf c.H0).index) :
    BOf c h12 χ = {ν, conjIrr c h12 ν} ∧
      tildeNu c h12 ν c.t = 2 * ν.1 (tH0 c) := by
  classical
  by_cases hB : BOf c h12 χ = {ν, conjIrr c h12 ν}
  · constructor
    · exact hB
    · exact BOf_eq_pair_of_pair_implies_tilde_two c h12 hχ hνs hν hB
  · have hfalse := false_branch_setup c h12 hSC hχ hνs hν hνL hB
    rcases hfalse with ⟨μ, hμB, hμν, hμνs, hBset, _hTfalse, hνsL, hΛν4, hindex, hS8⟩
    have hμfix : conjChar c.H0 (s_normalizes_H0 c h12) μ.1 = μ.1 :=
      mu_fixed_of_false_branch c h12 hχ hν hνs hνsL hμB hμν hμνs hBset
    have hnot4 : (orbit c.H0 c.U μ.1).card ≠ 4 := by
      intro h4
      exact lambda_mu4_false c h12 hSC hχ hν hνs hνsL hμB hμν hμνs hBset
        hΛν4 h4 hindex hS8
    have hΛμ2 : (orbit c.H0 c.U μ.1).card = 2 :=
      orbit_card_eq_two_of_ne_four c h12 hSC hindex hnot4
    exfalso
    rcases orbit_restrict_full c h12 hSC hindex hΛν4 with ⟨β, _hOrbitν, hresν⟩
    have hresνs : restrictU c h12 (conjIrr c h12 ν).1 = β.1 := by
      have hmem : (conjIrr c h12 ν).1 ∈ orbit c.H0 c.U ν.1 := by
        simpa [conjIrr_coe] using hνsL
      have hEq := restrictU_orbit_mem c h12 hmem
      rwa [hresν] at hEq
    rcases orbit_restrict_pair c h12 hSC hindex hΛμ2 with ⟨α, hOrbitμ, hcardα2, hresμ⟩
    let α₂ : Irr (↥c.U) := conjIrrS c (c.S0_le_S (S0_generator_mem_S0 c)) α
    have hαne : α ≠ α₂ := by
      intro hEq
      have hfix : conjIrrS c (c.S0_le_S (S0_generator_mem_S0 c)) α = α := hEq.symm
      have hsing := s0Orbit_eq_singleton_of_fixed c hSC α hfix
      rw [hsing] at hcardα2
      norm_num at hcardα2
    have hnotfixα : conjIrrS c (c.S0_le_S (S0_generator_mem_S0 c)) α ≠ α := hαne.symm
    have hquarter := chi_one_quarter_int c h12 hSC hχ hν hνs hνsL hμB hμν hμνs
      hBset hΛν4 hΛμ2 hindex
    -- the `Λ`-orbit of `α` is fixed by `s` (since `μ` is), so `S_α ≰ S0`
    have hfixorbit : ∀ ξ : ClassFunction (↥c.H0),
        ξ ∈ orbitOfAlpha c h12 hSC α →
        conjChar c.H0 (s_normalizes_H0 c h12) ξ ∈ orbitOfAlpha c h12 hSC α := by
      intro ξ hξ
      have hξ' : ξ ∈ orbit c.H0 c.U μ.1 := by simpa [hOrbitμ] using hξ
      have hc : conjChar c.H0 (s_normalizes_H0 c h12) ξ ∈
          orbit c.H0 c.U (conjChar c.H0 (s_normalizes_H0 c h12) μ.1) :=
        orbit_subset_conjChar c h12 ξ hξ'
      rw [hμfix] at hc
      simpa [hOrbitμ] using hc
    have hstab : ¬ stabilizerS c α ≤ (c.S0 : Subgroup G) :=
      (orbitOfAlpha_fixed_iff c h12 hSC α).mp hfixorbit
    have hstabcases := (stabilizerS_not_le_S0_iff c h12 hSC α).mp hstab
    rcases hstabcases with hcase1 | hcase2
    · rcases hcase1 with ⟨hcard1, _hstabS⟩
      rw [hcard1] at hcardα2
      norm_num at hcardα2
    · rcases hcase2 with ⟨_hcard2', hstabT⟩
      rcases hstabT with hstab1 | hstab2
      · -- `S_α = S'⟨t1⟩`: `t1` fixes both `α` and `α₂`
        have ht1stab : c.t1 ∈ stabilizerS c α := by
          rw [hstab1]
          exact SetLike.le_def.mp le_sup_right (Subgroup.mem_zpowers c.t1)
        have hfixα : conjIrrS c c.t1_mem_S α = α := by
          rcases ht1stab with ⟨hg, hfix⟩
          exact (conjIrrS_proof_irrel c c.t1_mem_S hg α).trans hfix
        have hnorm1 : Subgroup.zpowers c.t1 ≤
            Subgroup.normalizer ((c.U : Subgroup G) : Set G) :=
          le_trans (le_sup_right : Subgroup.zpowers c.t1 ≤ SPrime c ⊔ Subgroup.zpowers c.t1)
            (SPrime_t_le_normalizer_U c hSC c.t1_mem_S)
        have instNormT1 : Subgroup.Normalizes (Subgroup.zpowers c.t1) c.U := ⟨hnorm1⟩
        have hfixα₂ : conjIrrS c c.t1_mem_S α₂ = α₂ := by
          have hmem_r0 : S0_generator c ∈ (c.S : Subgroup G) :=
            c.S0_le_S (S0_generator_mem_S0 c)
          have hrinv : (S0_generator c)⁻¹ ∈ (c.S : Subgroup G) :=
            (c.S : Subgroup G).inv_mem hmem_r0
          change conjIrrS c c.t1_mem_S (conjIrrS c hmem_r0 α) =
            conjIrrS c hmem_r0 α
          have hEq1 : conjIrrS c c.t1_mem_S (conjIrrS c hmem_r0 α) =
              conjIrrS c ((c.S : Subgroup G).mul_mem hmem_r0 c.t1_mem_S) α :=
            (conjIrrS_mul c hmem_r0 c.t1_mem_S α).symm
          have hident : S0_generator c * c.t1 = c.t1 * (S0_generator c)⁻¹ := by
            have ht1sq : c.t1 * c.t1 = 1 := by simpa [pow_two] using c.t1_involution.2
            have ht2sq : c.t2 * c.t2 = 1 := by simpa [pow_two] using c.t2_involution.2
            have ht1inv : c.t1⁻¹ = c.t1 := inv_eq_of_mul_eq_one_right ht1sq
            have ht2inv : c.t2⁻¹ = c.t2 := inv_eq_of_mul_eq_one_right ht2sq
            have hrev : (c.t1 * c.t2)⁻¹ = c.t2 * c.t1 := by
              rw [mul_inv_rev]
              simp [ht1inv, ht2inv]
            dsimp [S0_generator]
            rw [hrev]
            exact mul_assoc c.t1 c.t2 c.t1
          have hEq2 : conjIrrS c ((c.S : Subgroup G).mul_mem hmem_r0 c.t1_mem_S) α =
              conjIrrS c ((c.S : Subgroup G).mul_mem c.t1_mem_S hrinv) α :=
            conjIrrS_eq_of_elements_eq c _ _ hident α
          have hEq3 : conjIrrS c ((c.S : Subgroup G).mul_mem c.t1_mem_S hrinv) α =
              conjIrrS c hrinv (conjIrrS c c.t1_mem_S α) :=
            conjIrrS_mul c c.t1_mem_S hrinv α
          have hEq4 : conjIrrS c hrinv α = conjIrrS c hmem_r0 α := by
            have h4 := conjIrrS_r0_eq_r0_inv_of_not_fixed c hSC α hnotfixα
            have h5 : conjIrrS c hrinv α =
                conjIrrS c (c.S0_le_S ((c.S0 : Subgroup G).inv_mem (S0_generator_mem_S0 c))) α :=
              conjIrrS_proof_irrel c hrinv
                (c.S0_le_S ((c.S0 : Subgroup G).inv_mem (S0_generator_mem_S0 c))) α
            exact h5.trans h4
          rw [hEq1, hEq2, hEq3, hfixα]
          exact hEq4
        have hχ0 : ∀ b : ↥(fixedSubgroup (↥(Subgroup.zpowers c.t1)) (↥c.U)),
            CongruentModTwo (χ (b.1.1 : G)) 0 := by
          intro b
          let u : ↥c.U := b.1
          have huU : (u : G) ∈ c.U := u.2
          have huB : (u : G) ∈ centralizerIn c.U c.t1 := by
            unfold centralizerIn
            refine Subgroup.mem_inf.mpr ⟨huU, ?_⟩
            rw [Subgroup.mem_centralizer_iff]
            intro h hh
            have ht : h = c.t1 := by simpa using hh
            subst h
            have hfix := (mem_fixedSubgroup_iff (↥(Subgroup.zpowers c.t1)) (↥c.U) u).1 b.2
              ⟨c.t1, Subgroup.mem_zpowers c.t1⟩
            have hcoef : (((⟨c.t1, Subgroup.mem_zpowers c.t1⟩ : ↥(Subgroup.zpowers c.t1)) • u : ↥c.U) : G) =
                c.t1 * (u : G) * c.t1⁻¹ := by
              rw [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
            have hEq : c.t1 * (u : G) * c.t1⁻¹ = (u : G) := by
              simpa [hcoef] using congrArg Subtype.val hfix
            have hcomm : c.t1 * (u : G) = (u : G) * c.t1 := by
              calc
                c.t1 * (u : G) = (c.t1 * (u : G) * c.t1⁻¹) * c.t1 := by group
                _ = (u : G) * c.t1 := by rw [hEq]
            simpa using hcomm
          have hc := chi_congruent_zero_on_centralizerIn c h12 hSC hχ hquarter hS8
            c.t1_mem_S c.t1_not_mem_S0 (by simpa [pow_two] using c.t1_involution.2) huB
          simpa [u] using hc
        exact not_congruent_sum_two_on_fixed c h12 hSC hχ hν hμB hνs hμν hμνs hBset
          hresν hresνs hresμ c.t1_mem_S c.t1_not_mem_S0
          (by simpa [pow_two] using c.t1_involution.2) hfixα hfixα₂ hαne hχ0
      · -- `S_α = S'⟨t2⟩`: `t2` fixes both `α` and `α₂`
        have ht2stab : c.t2 ∈ stabilizerS c α := by
          rw [hstab2]
          exact SetLike.le_def.mp le_sup_right (Subgroup.mem_zpowers c.t2)
        have hfixα' : conjIrrS c c.t2_mem_S α = α := by
          rcases ht2stab with ⟨hg, hfix⟩
          exact (conjIrrS_proof_irrel c c.t2_mem_S hg α).trans hfix
        have hnorm2 : Subgroup.zpowers c.t2 ≤
            Subgroup.normalizer ((c.U : Subgroup G) : Set G) :=
          le_trans (le_sup_right : Subgroup.zpowers c.t2 ≤ SPrime c ⊔ Subgroup.zpowers c.t2)
            (SPrime_t_le_normalizer_U c hSC c.t2_mem_S)
        have instNormT2 : Subgroup.Normalizes (Subgroup.zpowers c.t2) c.U := ⟨hnorm2⟩
        have hfixα₂' : conjIrrS c c.t2_mem_S α₂ = α₂ := by
          have hmem_r0 : S0_generator c ∈ (c.S : Subgroup G) :=
            c.S0_le_S (S0_generator_mem_S0 c)
          have hrinv : (S0_generator c)⁻¹ ∈ (c.S : Subgroup G) :=
            (c.S : Subgroup G).inv_mem hmem_r0
          change conjIrrS c c.t2_mem_S (conjIrrS c hmem_r0 α) =
            conjIrrS c hmem_r0 α
          have hEq1 : conjIrrS c c.t2_mem_S (conjIrrS c hmem_r0 α) =
              conjIrrS c ((c.S : Subgroup G).mul_mem hmem_r0 c.t2_mem_S) α :=
            (conjIrrS_mul c hmem_r0 c.t2_mem_S α).symm
          have hident : S0_generator c * c.t2 = c.t2 * (S0_generator c)⁻¹ := by
            have ht1sq : c.t1 * c.t1 = 1 := by simpa [pow_two] using c.t1_involution.2
            have ht2sq : c.t2 * c.t2 = 1 := by simpa [pow_two] using c.t2_involution.2
            have ht1inv : c.t1⁻¹ = c.t1 := inv_eq_of_mul_eq_one_right ht1sq
            have ht2inv : c.t2⁻¹ = c.t2 := inv_eq_of_mul_eq_one_right ht2sq
            have hrev : (c.t1 * c.t2)⁻¹ = c.t2 * c.t1 := by
              rw [mul_inv_rev]
              simp [ht1inv, ht2inv]
            dsimp [S0_generator]
            rw [hrev]
            rw [mul_assoc c.t1 c.t2 c.t2]
            rw [← mul_assoc c.t2 c.t2 c.t1]
            rw [ht2sq]
            simp
          have hEq2 : conjIrrS c ((c.S : Subgroup G).mul_mem hmem_r0 c.t2_mem_S) α =
              conjIrrS c ((c.S : Subgroup G).mul_mem c.t2_mem_S hrinv) α :=
            conjIrrS_eq_of_elements_eq c _ _ hident α
          have hEq3 : conjIrrS c ((c.S : Subgroup G).mul_mem c.t2_mem_S hrinv) α =
              conjIrrS c hrinv (conjIrrS c c.t2_mem_S α) :=
            conjIrrS_mul c c.t2_mem_S hrinv α
          have hEq4 : conjIrrS c hrinv α = conjIrrS c hmem_r0 α := by
            have h4 := conjIrrS_r0_eq_r0_inv_of_not_fixed c hSC α hnotfixα
            have h5 : conjIrrS c hrinv α =
                conjIrrS c (c.S0_le_S ((c.S0 : Subgroup G).inv_mem (S0_generator_mem_S0 c))) α :=
              conjIrrS_proof_irrel c hrinv
                (c.S0_le_S ((c.S0 : Subgroup G).inv_mem (S0_generator_mem_S0 c))) α
            exact h5.trans h4
          rw [hEq1, hEq2, hEq3, hfixα']
          exact hEq4
        have hχ0 : ∀ b : ↥(fixedSubgroup (↥(Subgroup.zpowers c.t2)) (↥c.U)),
            CongruentModTwo (χ (b.1.1 : G)) 0 := by
          intro b
          let u : ↥c.U := b.1
          have huU : (u : G) ∈ c.U := u.2
          have huB : (u : G) ∈ centralizerIn c.U c.t2 := by
            unfold centralizerIn
            refine Subgroup.mem_inf.mpr ⟨huU, ?_⟩
            rw [Subgroup.mem_centralizer_iff]
            intro h hh
            have ht : h = c.t2 := by simpa using hh
            subst h
            have hfix := (mem_fixedSubgroup_iff (↥(Subgroup.zpowers c.t2)) (↥c.U) u).1 b.2
              ⟨c.t2, Subgroup.mem_zpowers c.t2⟩
            have hcoef : (((⟨c.t2, Subgroup.mem_zpowers c.t2⟩ : ↥(Subgroup.zpowers c.t2)) • u : ↥c.U) : G) =
                c.t2 * (u : G) * c.t2⁻¹ := by
              rw [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
            have hEq : c.t2 * (u : G) * c.t2⁻¹ = (u : G) := by
              simpa [hcoef] using congrArg Subtype.val hfix
            have hcomm : c.t2 * (u : G) = (u : G) * c.t2 := by
              calc
                c.t2 * (u : G) = (c.t2 * (u : G) * c.t2⁻¹) * c.t2 := by group
                _ = (u : G) * c.t2 := by rw [hEq]
            simpa using hcomm
          have hc := chi_congruent_zero_on_centralizerIn c h12 hSC hχ hquarter hS8
            c.t2_mem_S c.t2_not_mem_S0 (by simpa [pow_two] using c.t2_involution.2) huB
          simpa [u] using hc
        exact not_congruent_sum_two_on_fixed c h12 hSC hχ hν hμB hνs hμν hμνs hBset
          hresν hresνs hresμ c.t2_mem_S c.t2_not_mem_S0
          (by simpa [pow_two] using c.t2_involution.2) hfixα' hfixα₂' hαne hχ0

end Section3

end CFSG.BenderGlauberman
