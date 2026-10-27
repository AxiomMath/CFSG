module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section2.Basic
import all CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section2.Coherence
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section2.Lemma24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section3.Remark31
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section3.Theorem32
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Lemma19
import all CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Lemma19
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.ClassFunction
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.Divisibility
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

namespace CFSG
end CFSG
open CFSG

/-!
# Bender--Glauberman: Section 3 — Lemma 3.3

Lemma 3.3: if `B(χ)` contains two `s`-fixed characters with `|Λν| = m`,
then `B(χ)` consists of three such characters and `S` has order `4`.
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

/-! ## Local δ/θ helpers (re-proved from the landed public API)

The Coherence file keeps its `theta_pair_*`/`delta_*` facts private.  The
three-character contradiction only needs the small subset reproduced below,
using the public `remark_1_4`, `lemma_1_3`, `H0_index` and `tildeNu` API.
-/

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

private lemma H_card_eq_two_mul_H0_card (c : Hyp11 G) (h12 : Hyp12 c)
    (hH0index : (c.H0.subgroupOf c.H).index = 2) :
    Nat.card (↥c.H) = 2 * Nat.card (↥c.H0) := by
  classical
  have hU : Nat.card (↥(c.H0.subgroupOf c.H)) = Nat.card (↥c.H0) := by
    exact Nat.card_congr {
      toFun := fun x : ↥(c.H0.subgroupOf c.H) => ⟨(x : G), Subgroup.mem_subgroupOf.mp x.2⟩
      invFun := fun y : ↥c.H0 => ⟨⟨(y : G), (h12.H0_normal_in_H).1 y.2⟩,
        Subgroup.mem_subgroupOf.mpr y.2⟩
      left_inv := by intro x; apply Subtype.ext; rfl
      right_inv := by intro y; apply Subtype.ext; rfl }
  have hcm := Subgroup.card_mul_index (c.H0.subgroupOf c.H)
  rw [hU, hH0index] at hcm
  simpa [mul_comm] using hcm.symm

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
  change (Nat.card (↥c.H0) : ℂ)⁻¹ * (∑ y : ↥c.H0,
      (inducedFromSub (h12.H0_normal_in_H).1 ν₁) ⟨(y : G), (h12.H0_normal_in_H).1 y.2⟩ *
        star ((inducedFromSub (h12.H0_normal_in_H).1 ν₂) ⟨(y : G), (h12.H0_normal_in_H).1 y.2⟩)) = _
  rw [hsum]
  ring

set_option maxHeartbeats 20000000 in
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
  have hcard : (Nat.card (↥c.H) : ℂ) = 2 * (Nat.card (↥c.H0) : ℂ) := by
    exact_mod_cast H_card_eq_two_mul_H0_card c h12 hH0index
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
    ring
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
    ring

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

private lemma scalarProduct_sub_left' {G : Type u} [Group G] [Fintype G]
    (φ₁ φ₂ ψ : ClassFunction G) :
    scalarProduct G (φ₁ - φ₂) ψ = scalarProduct G φ₁ ψ - scalarProduct G φ₂ ψ := by
  calc
    scalarProduct G (φ₁ - φ₂) ψ = scalarProduct G (φ₁ + (-1 : ℂ) • φ₂) ψ := by
          congr 1
          funext x
          simp [sub_eq_add_neg]
    _ = scalarProduct G φ₁ ψ + scalarProduct G ((-1 : ℂ) • φ₂) ψ := scalarProduct_add_left _ _ _
    _ = scalarProduct G φ₁ ψ - scalarProduct G φ₂ ψ := by
          rw [scalarProduct_smul_left]
          ring

private lemma scalarProduct_star_comm' {G : Type u} [Group G] [Fintype G]
    (φ ψ : ClassFunction G) :
    star (scalarProduct G φ ψ) = scalarProduct G ψ φ := by
  classical
  unfold scalarProduct
  simp [map_sum, map_mul, map_star, mul_comm, mul_left_comm, mul_assoc]

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
  have hν₁s : IsIrreducibleCharacter (conjChar c.H0 (s_normalizes_H0 c h12) ν₁) :=
    isIrreducibleCharacter_conjChar c.H0 (s_normalizes_H0 c h12) hs_inv hν₁
  have hν₂s : IsIrreducibleCharacter (conjChar c.H0 (s_normalizes_H0 c h12) ν₂) :=
    isIrreducibleCharacter_conjChar c.H0 (s_normalizes_H0 c h12) hs_inv hν₂
  have hν₁not2 : ν₁ ∉ orbit c.H0 c.U (conjChar c.H0 (s_normalizes_H0 c h12) ν₂) := by
    intro h1
    apply hν₁s_not
    have h2 : conjChar c.H0 (s_normalizes_H0 c h12) ν₁ ∈
        orbit c.H0 c.U (conjChar c.H0 (s_normalizes_H0 c h12)
          (conjChar c.H0 (s_normalizes_H0 c h12) ν₂)) :=
      orbit_subset_conjChar c h12 ν₁ h1
    rw [conjChar_conjChar c h12 ν₂] at h2
    exact h2
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
  have e12 := theta_pair_scalar_H' c h12 hH0index hμ₁ hμ₂
  have e1ν2 := theta_pair_scalar_H' c h12 hH0index hμ₁ hν₂
  have eν12 := theta_pair_scalar_H' c h12 hH0index hν₁ hμ₂
  have eν1ν2 := theta_pair_scalar_H' c h12 hH0index hν₁ hν₂
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
    scalarProduct_orbit_disjoint c hν₁ hν₂ hμ₁L (orbit_self_mem' c ν₂) hν₁not
  have sp6 : scalarProduct (↥c.H0) μ₁
      (conjChar c.H0 (s_normalizes_H0 c h12) ν₂) = 0 :=
    scalarProduct_orbit_disjoint c hν₁ hν₂s hμ₁L
      (orbit_self_mem' c (conjChar c.H0 (s_normalizes_H0 c h12) ν₂)) hν₁not2
  have sp7 : scalarProduct (↥c.H0) (conjChar c.H0 (s_normalizes_H0 c h12) μ₁) ν₂ = 0 :=
    scalarProduct_orbit_disjoint c hν₁s hν₂
      (orbit_subset_conjChar c h12 μ₁ hμ₁L) (orbit_self_mem' c ν₂) hν₁s_not
  have sp8 : scalarProduct (↥c.H0) (conjChar c.H0 (s_normalizes_H0 c h12) μ₁)
      (conjChar c.H0 (s_normalizes_H0 c h12) ν₂) = 0 :=
    scalarProduct_orbit_disjoint c hν₁s hν₂s
      (orbit_subset_conjChar c h12 μ₁ hμ₁L)
      (orbit_self_mem' c (conjChar c.H0 (s_normalizes_H0 c h12) ν₂)) hν₁s_not2
  have sp9 : scalarProduct (↥c.H0) ν₁ μ₂ = 0 :=
    scalarProduct_orbit_disjoint c hν₁ hν₂ (orbit_self_mem' c ν₁) hμ₂L hν₁not
  have sp10 : scalarProduct (↥c.H0) ν₁
      (conjChar c.H0 (s_normalizes_H0 c h12) μ₂) = 0 :=
    scalarProduct_orbit_disjoint c hν₁ hν₂s (orbit_self_mem' c ν₁)
      (orbit_subset_conjChar c h12 μ₂ hμ₂L) hν₁not2
  have sp11 : scalarProduct (↥c.H0) (conjChar c.H0 (s_normalizes_H0 c h12) ν₁) μ₂ = 0 :=
    scalarProduct_orbit_disjoint c hν₁s hν₂
      (orbit_self_mem' c (conjChar c.H0 (s_normalizes_H0 c h12) ν₁)) hμ₂L hν₁s_not
  have sp12 : scalarProduct (↥c.H0) (conjChar c.H0 (s_normalizes_H0 c h12) ν₁)
      (conjChar c.H0 (s_normalizes_H0 c h12) μ₂) = 0 :=
    scalarProduct_orbit_disjoint c hν₁s hν₂s
      (orbit_self_mem' c (conjChar c.H0 (s_normalizes_H0 c h12) ν₁))
      (orbit_subset_conjChar c h12 μ₂ hμ₂L) hν₁s_not2
  have sp13 : scalarProduct (↥c.H0) ν₁ ν₂ = 0 :=
    scalarProduct_orbit_disjoint c hν₁ hν₂ (orbit_self_mem' c ν₁)
      (orbit_self_mem' c ν₂) hν₁not
  have sp14 : scalarProduct (↥c.H0) ν₁
      (conjChar c.H0 (s_normalizes_H0 c h12) ν₂) = 0 :=
    scalarProduct_orbit_disjoint c hν₁ hν₂s (orbit_self_mem' c ν₁)
      (orbit_self_mem' c (conjChar c.H0 (s_normalizes_H0 c h12) ν₂)) hν₁not2
  have sp15 : scalarProduct (↥c.H0) (conjChar c.H0 (s_normalizes_H0 c h12) ν₁) ν₂ = 0 :=
    scalarProduct_orbit_disjoint c hν₁s hν₂
      (orbit_self_mem' c (conjChar c.H0 (s_normalizes_H0 c h12) ν₁))
      (orbit_self_mem' c ν₂) hν₁s_not
  have sp16 : scalarProduct (↥c.H0) (conjChar c.H0 (s_normalizes_H0 c h12) ν₁)
      (conjChar c.H0 (s_normalizes_H0 c h12) ν₂) = 0 :=
    scalarProduct_orbit_disjoint c hν₁s hν₂s
      (orbit_self_mem' c (conjChar c.H0 (s_normalizes_H0 c h12) ν₁))
      (orbit_self_mem' c (conjChar c.H0 (s_normalizes_H0 c h12) ν₂)) hν₁s_not2
  rw [scalarProduct_sub_left', scalarProduct_sub_right, scalarProduct_sub_right]
  rw [e12, e1ν2, eν12, eν1ν2]
  simp [sp1, sp2, sp3, sp4, sp5, sp6, sp7, sp8, sp9, sp10, sp11, sp12, sp13,
    sp14, sp15, sp16]

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
  have hcf₁ : IsClassFunction (μ₁ - ν₁) :=
    isClassFunction_sub_irr (orbit_mem_isIrreducible c.H0 c.U hν₁ hμ₁L) hν₁
  have hcf₂ : IsClassFunction (μ₂ - ν₂) :=
    isClassFunction_sub_irr (orbit_mem_isIrreducible c.H0 c.U hν₂ hμ₂L) hν₂
  have h1 := lemma_1_3 c h12 (δ1 := μ₁ - ν₁) (δ2 := μ₂ - ν₂) hcf₁ hcf₂
    (delta_supported_on_T c hμ₁L) (delta_supported_on_T c hμ₂L)
  rw [h1.1]
  rw [inducedFromSub_sub c h12 ν₁ μ₁, inducedFromSub_sub c h12 ν₂ μ₂]

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
    apply star_inj.mp
    rw [scalarProduct_star_comm']
    simpa using hsp
  unfold normSq
  rw [h1]
  change scalarProduct (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν₁ -
        inducedFromSub (h12.H0_normal_in_H).1 ν₂)
      (inducedFromSub (h12.H0_normal_in_H).1 ν₁ -
        inducedFromSub (h12.H0_normal_in_H).1 ν₂) =
    scalarProduct (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν₁)
        (inducedFromSub (h12.H0_normal_in_H).1 ν₁) +
      scalarProduct (↥c.H) (inducedFromSub (h12.H0_normal_in_H).1 ν₂)
        (inducedFromSub (h12.H0_normal_in_H).1 ν₂)
  rw [scalarProduct_sub_left', scalarProduct_sub_right, scalarProduct_sub_right]
  rw [hsp, hsp']
  ring

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
      invFun := fun y : ↥c.U => ⟨⟨(y : G), (h12.U_normal_in_H0).1 y.2⟩, Subgroup.mem_subgroupOf.mpr y.2⟩
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

private lemma isGeneralizedCharacter_of_isPMIrr {G : Type u} [Group G] [Fintype G]
    {χ : ClassFunction G} (hχ : IsPMIrr G χ) : IsGeneralizedCharacter χ := by
  rcases hχ with hχ | hχ
  · exact ⟨χ, 0, isCharacter_of_isIrreducibleCharacter hχ, isCharacter_zero, by simp⟩
  · exact ⟨0, -χ, isCharacter_zero, isCharacter_of_isIrreducibleCharacter hχ, by simp⟩

private lemma isGeneralizedCharacter_sub' {G : Type u} [Group G] [Fintype G]
    {φ ψ : ClassFunction G} (hφ : IsGeneralizedCharacter φ)
    (hψ : IsGeneralizedCharacter ψ) : IsGeneralizedCharacter (φ - ψ) := by
  rcases hφ with ⟨δ₁, δ₂, hδ₁, hδ₂, hφeq⟩
  rcases hψ with ⟨ε₁, ε₂, hε₁, hε₂, hψeq⟩
  refine ⟨δ₁ + ε₂, δ₂ + ε₁, isCharacter_add hδ₁ hε₂, isCharacter_add hδ₂ hε₁, ?_⟩
  rw [hφeq, hψeq]
  funext x
  simp [Pi.add_apply, Pi.sub_apply]
  ring

private lemma scalarProduct_self_eq_one_of_isPMIrr {G : Type u} [Group G] [Fintype G]
    {χ : ClassFunction G} (hχ : IsPMIrr G χ) : scalarProduct G χ χ = 1 := by
  rcases hχ with hχ | hχ
  · exact scalarProduct_irreducible_self hχ
  · have h' : scalarProduct G (-χ) (-χ) = 1 := scalarProduct_irreducible_self hχ
    rw [scalarProduct_neg_left, scalarProduct_neg_right] at h'
    simpa using h'

private lemma orbit_mem_degree_eq' (c : Hyp11 G) [Fintype ↥(LambdaHom c.H0 c.U)]
    {ν μ : ClassFunction (↥c.H0)} (hμ : μ ∈ orbit c.H0 c.U ν) : μ 1 = ν 1 := by
  rcases Finset.mem_image.mp hμ with ⟨l, hl, hEq⟩
  rw [← hEq]
  simp [LambdaChar]

private lemma chi_one_ne_zero_of_isPMIrr {G : Type u} [Group G] [Fintype G]
    {χ : ClassFunction G} (hχ : IsPMIrr G χ) : χ 1 ≠ 0 := by
  rcases hχ with h | h
  · exact irreducible_char_one_ne_zero h
  · have h' : (-χ) 1 ≠ 0 := irreducible_char_one_ne_zero h
    simpa using h'

private lemma BOf_orbit_pair_conj (c : Hyp11 G) (h12 : Hyp12 c)
    {χ : ClassFunction G} (hχ : IsPMIrr G χ)
    {μ ν : Irr (↥c.H0)}
    (hμB : μ ∈ BOf c h12 χ) (hνB : ν ∈ BOf c h12 χ)
    (hμL : μ.1 ∈ orbit c.H0 c.U ν.1) (hμν : μ ≠ ν) :
    conjChar c.H0 (s_normalizes_H0 c h12) μ.1 = ν.1 := by
  classical
  by_contra hμsν
  set eμ : ℂ := scalarProduct G χ (tildeNu c h12 μ) with hEμ
  set eν : ℂ := scalarProduct G χ (tildeNu c h12 ν) with hEν
  have heμ : eμ = 1 ∨ eμ = -1 := by
    simpa [eμ] using BOf_scalar_eq_pm_one c h12 hχ hμB
  have heν : eν = 1 ∨ eν = -1 := by
    simpa [eν] using BOf_scalar_eq_pm_one c h12 hχ hνB
  have heμreal : star eμ = eμ := by
    rcases heμ with h | h <;> simp [h]
  have heνreal : star eν = eν := by
    rcases heν with h | h <;> simp [h]
  have heμsq : eμ * star eμ = 1 := by
    rcases heμ with h | h <;> simp [h]
  have heνsq : eν * star eν = 1 := by
    rcases heν with h | h <;> simp [h]
  have hA : normSq G (tildeNu c h12 μ) =
      (if conjChar c.H0 (s_normalizes_H0 c h12) μ.1 = μ.1 then 2 else 1) :=
    tildeNu_norm c h12 μ
  have hB : normSq G (tildeNu c h12 ν) =
      (if conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1 then 2 else 1) :=
    tildeNu_norm c h12 ν
  let I : ClassFunction G := inducedClassFunction c.H0 (μ.1 - ν.1)
  have hμν' : μ.1 ≠ ν.1 := by
    intro h
    exact hμν (Subtype.ext h)
  have hI_norm : normSq G I =
      (if conjChar c.H0 (s_normalizes_H0 c h12) μ.1 = μ.1 then 2 else 1) +
        (if conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1 then 2 else 1) := by
    change normSq G (inducedClassFunction c.H0 (μ.1 - ν.1)) = _
    rw [delta_norm c h12 (H0_index c h12) μ.2 ν.2 hμL hμν' hμsν]
    rw [theta_norm c h12 (H0_index c h12) μ.2]
    rw [theta_norm c h12 (H0_index c h12) ν.2]
  have hind : I = tildeNu c h12 μ - tildeNu c h12 ν := by
    change inducedClassFunction c.H0 (μ.1 - ν.1) = tildeNu c h12 μ - tildeNu c h12 ν
    exact tildeNu_ind c h12 hμL
  have hW' : scalarProduct G (tildeNu c h12 μ) (tildeNu c h12 ν) +
      scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 μ) =
      normSq G (tildeNu c h12 μ) + normSq G (tildeNu c h12 ν) -
        normSq G I := by
    rw [hind]
    simp only [normSq]
    rw [scalarProduct_sub_left, scalarProduct_sub_right, scalarProduct_sub_right]
    ring_nf
  have hW0 : scalarProduct G (tildeNu c h12 μ) (tildeNu c h12 ν) +
      scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 μ) = 0 := by
    rw [hW', hI_norm, hA, hB]
    by_cases hμμ : conjChar c.H0 (s_normalizes_H0 c h12) μ.1 = μ.1
    · by_cases hνν : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1
      · simp [hμμ, hνν]
      · simp [hμμ, hνν]
    · by_cases hνν : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1
      · simp [hμμ, hνν]
      · simp [hμμ, hνν]
  set ξ : ClassFunction G := eμ • tildeNu c h12 μ + eν • tildeNu c h12 ν with hξDef
  have hξξ : scalarProduct G ξ ξ = normSq G (tildeNu c h12 μ) + normSq G (tildeNu c h12 ν) := by
    rw [hξDef]
    rcases heμ with hμ1 | hμm
    · rcases heν with hν1 | hνm
      · rw [hμ1, hν1]
        simp
        rw [scalarProduct_add_left, scalarProduct_add_right, scalarProduct_add_right]
        calc
          scalarProduct G (tildeNu c h12 μ) (tildeNu c h12 μ) +
              scalarProduct G (tildeNu c h12 μ) (tildeNu c h12 ν) +
              (scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 μ) +
                scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 ν))
              = scalarProduct G (tildeNu c h12 μ) (tildeNu c h12 μ) +
                  (scalarProduct G (tildeNu c h12 μ) (tildeNu c h12 ν) +
                    scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 μ)) +
                scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 ν) := by ring
          _ = normSq G (tildeNu c h12 μ) + normSq G (tildeNu c h12 ν) := by
                rw [hW0]
                simp only [normSq]
                ring
      · rw [hμ1, hνm]
        simp
        rw [scalarProduct_add_left, scalarProduct_add_right, scalarProduct_add_right]
        simp only [scalarProduct_neg_left, scalarProduct_neg_right]
        simp
        calc
          scalarProduct G (tildeNu c h12 μ) (tildeNu c h12 μ) +
              -scalarProduct G (tildeNu c h12 μ) (tildeNu c h12 ν) +
              (-scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 μ) +
                scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 ν))
              = scalarProduct G (tildeNu c h12 μ) (tildeNu c h12 μ) -
                  (scalarProduct G (tildeNu c h12 μ) (tildeNu c h12 ν) +
                    scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 μ)) +
                scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 ν) := by ring
          _ = normSq G (tildeNu c h12 μ) + normSq G (tildeNu c h12 ν) := by
                rw [hW0]
                simp only [normSq]
                ring
    · rcases heν with hν1 | hνm
      · rw [hμm, hν1]
        simp
        rw [scalarProduct_add_left, scalarProduct_add_right, scalarProduct_add_right]
        simp only [scalarProduct_neg_left, scalarProduct_neg_right]
        simp
        calc
          scalarProduct G (tildeNu c h12 μ) (tildeNu c h12 μ) +
              -scalarProduct G (tildeNu c h12 μ) (tildeNu c h12 ν) +
              (-scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 μ) +
                scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 ν))
              = scalarProduct G (tildeNu c h12 μ) (tildeNu c h12 μ) -
                  (scalarProduct G (tildeNu c h12 μ) (tildeNu c h12 ν) +
                    scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 μ)) +
                scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 ν) := by ring
          _ = normSq G (tildeNu c h12 μ) + normSq G (tildeNu c h12 ν) := by
                rw [hW0]
                simp only [normSq]
                ring
      · rw [hμm, hνm]
        simp
        rw [scalarProduct_add_left, scalarProduct_add_right, scalarProduct_add_right]
        simp only [scalarProduct_neg_left, scalarProduct_neg_right]
        simp
        calc
          scalarProduct G (tildeNu c h12 μ) (tildeNu c h12 μ) +
              scalarProduct G (tildeNu c h12 μ) (tildeNu c h12 ν) +
              (scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 μ) +
                scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 ν))
              = scalarProduct G (tildeNu c h12 μ) (tildeNu c h12 μ) +
                  (scalarProduct G (tildeNu c h12 μ) (tildeNu c h12 ν) +
                    scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 μ)) +
                scalarProduct G (tildeNu c h12 ν) (tildeNu c h12 ν) := by ring
          _ = normSq G (tildeNu c h12 μ) + normSq G (tildeNu c h12 ν) := by
                rw [hW0]
                simp only [normSq]
                ring
  have hχξ : scalarProduct G χ ξ = 2 := by
    rw [hξDef]
    rw [scalarProduct_add_right]
    simp only [scalarProduct_smul_right]
    rw [← hEμ, ← hEν]
    rw [heμreal, heνreal]
    have heμsq2 : eμ * eμ = 1 := by rcases heμ with h | h <;> simp [h]
    have heνsq2 : eν * eν = 1 := by rcases heν with h | h <;> simp [h]
    rw [heμsq2, heνsq2]
    norm_num
  have hξχ : scalarProduct G ξ χ = 2 := by
    have h' := scalarProduct_conj χ ξ
    rw [hχξ] at h'
    norm_num at h'
    exact h'.symm
  have hdiff : scalarProduct G (ξ - (2 : ℂ) • χ) (ξ - (2 : ℂ) • χ) =
      scalarProduct G ξ ξ - 4 := by
    rw [scalarProduct_sub_left, scalarProduct_sub_right, scalarProduct_sub_right]
    rw [scalarProduct_smul_left, scalarProduct_smul_right, scalarProduct_smul_left,
      scalarProduct_smul_right]
    rw [hξχ, hχξ, scalarProduct_self_eq_one_of_isPMIrr hχ]
    norm_num
  have hcs : 0 ≤ (scalarProduct G (ξ - (2 : ℂ) • χ) (ξ - (2 : ℂ) • χ)).re := by
    simpa [normSq] using normSq_nonneg (ξ - (2 : ℂ) • χ)
  have hξξ4c : 0 ≤ (scalarProduct G ξ ξ - 4).re := by
    rw [hdiff] at hcs
    exact hcs
  have hξξ_vals : scalarProduct G ξ ξ = 2 ∨ scalarProduct G ξ ξ = 3 ∨
      scalarProduct G ξ ξ = 4 := by
    rw [hξξ, hA, hB]
    by_cases hμμ : conjChar c.H0 (s_normalizes_H0 c h12) μ.1 = μ.1
    · by_cases hνν : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1
      · right; right; simp [hμμ, hνν]; norm_num
      · right; left; simp [hμμ, hνν]; norm_num
    · by_cases hνν : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1
      · right; left; simp [hμμ, hνν]; norm_num
      · left; simp [hμμ, hνν]; norm_num
  have hξξ4 : scalarProduct G ξ ξ = 4 := by
    rcases hξξ_vals with h2 | h3 | h4
    · exfalso
      have h' : (scalarProduct G ξ ξ - 4).re = -2 := by rw [h2]; norm_num
      rw [h'] at hξξ4c
      norm_num at hξξ4c
    · exfalso
      have h' : (scalarProduct G ξ ξ - 4).re = -1 := by rw [h3]; norm_num
      rw [h'] at hξξ4c
      norm_num at hξξ4c
    · exact h4
  have hμμ : conjChar c.H0 (s_normalizes_H0 c h12) μ.1 = μ.1 := by
    by_contra hμμ
    have hA1 : normSq G (tildeNu c h12 μ) = 1 := by rw [hA]; simp [hμμ]
    rw [hξξ, hA1, hB] at hξξ4
    by_cases hνν : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1
    · simp [hνν] at hξξ4
      norm_num at hξξ4
    · simp [hνν] at hξξ4
      norm_num at hξξ4
  have hνν : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1 := by
    by_contra hνν
    have hB1 : normSq G (tildeNu c h12 ν) = 1 := by rw [hB]; simp [hνν]
    rw [hξξ, hA, hB1] at hξξ4
    simp [hμμ] at hξξ4
    norm_num at hξξ4
  have hA2 : normSq G (tildeNu c h12 μ) = 2 := by rw [hA]; simp [hμμ]
  have hB2 : normSq G (tildeNu c h12 ν) = 2 := by rw [hB]; simp [hνν]
  have hξeq : ξ = (2 : ℂ) • χ := by
    have hd0 : scalarProduct G (ξ - (2 : ℂ) • χ) (ξ - (2 : ℂ) • χ) = 0 := by
      rw [hdiff, hξξ4]
      norm_num
    have hφ0 : ξ - (2 : ℂ) • χ = 0 := (normSq_eq_zero_iff (ξ - (2 : ℂ) • χ)).1 hd0
    exact sub_eq_zero.mp hφ0
  set η : ClassFunction G := tildeNu c h12 μ - eμ • χ with hηDef
  have hηgen : IsGeneralizedCharacter η := by
    rw [hηDef]
    have heμχgen : IsGeneralizedCharacter (eμ • χ) := by
      rcases heμ with h | h
      · rw [h]
        simpa using isGeneralizedCharacter_of_isPMIrr hχ
      · rw [h]
        have hχneg_gen : IsGeneralizedCharacter (-χ) := by
          exact isGeneralizedCharacter_of_isPMIrr (hχ.elim (fun hh => Or.inr (by simpa using hh))
            (fun hh => Or.inl hh))
        simpa using hχneg_gen
    exact isGeneralizedCharacter_sub' (tildeNu_isGeneralized c h12 μ) heμχgen
  have hmuChi : scalarProduct G (tildeNu c h12 μ) χ = eμ := by
    have h' := scalarProduct_conj χ (tildeNu c h12 μ)
    change star eμ = scalarProduct G (tildeNu c h12 μ) χ at h'
    rw [heμreal] at h'
    exact h'.symm
  have hηη : scalarProduct G η η = 1 := by
    rw [hηDef]
    rw [scalarProduct_sub_left, scalarProduct_sub_right, scalarProduct_sub_right]
    rw [scalarProduct_smul_left, scalarProduct_smul_right]
    rw [show scalarProduct G (eμ • χ) (eμ • χ) =
        eμ * (star eμ * scalarProduct G χ χ) from by
          rw [scalarProduct_smul_left, scalarProduct_smul_right]
          ring]
    have hAA : scalarProduct G (tildeNu c h12 μ) (tildeNu c h12 μ) = 2 := by
      rw [← normSq]
      exact hA2
    rw [hAA, ← hEμ, heμreal, hmuChi, scalarProduct_self_eq_one_of_isPMIrr hχ]
    have heμsq2 : eμ * eμ = 1 := by rcases heμ with h | h <;> simp [h]
    simp [heμsq2]
    norm_num
  rcases norm_one_signed_irreducible hηgen hηη with ⟨ψ, hψ, hψeq⟩
  have hη1 : η 1 ≠ 0 := by
    rcases hψeq with h | h
    · rw [h]
      exact irreducible_char_one_ne_zero hψ
    · rw [h]
      have hψ1 : ψ 1 ≠ 0 := irreducible_char_one_ne_zero hψ
      simpa using neg_ne_zero.mpr hψ1
  have hχ1 : χ 1 ≠ 0 := chi_one_ne_zero_of_isPMIrr hχ
  have hmu1 : tildeNu c h12 μ 1 = η 1 + eμ * χ 1 := by
    have hmu : tildeNu c h12 μ = η + eμ • χ := by
      rw [hηDef]
      abel
    have h' := congrFun hmu 1
    simpa [Pi.add_apply, Pi.smul_apply] using h'
  have hξ2χ : eμ • tildeNu c h12 μ + eν • tildeNu c h12 ν = (2 : ℂ) • χ := by
    simpa [hξDef] using hξeq
  have hnu1 : tildeNu c h12 ν 1 = eν * (χ 1 - eμ * η 1) := by
    have hpt := congrFun hξ2χ 1
    simp only [Pi.add_apply, Pi.smul_apply] at hpt
    simp at hpt
    rw [hmu1] at hpt
    have heμsq2 : eμ * eμ = 1 := by rcases heμ with h | h <;> simp [h]
    have heνsq2 : eν * eν = 1 := by rcases heν with h | h <;> simp [h]
    rcases heμ with hμ1 | hμm
    · rcases heν with hν1 | hνm
      · rw [hμ1, hν1] at hpt ⊢
        simp at hpt ⊢
        linear_combination hpt
      · rw [hμ1, hνm] at hpt ⊢
        simp at hpt ⊢
        linear_combination -hpt
    · rcases heν with hν1 | hνm
      · rw [hμm, hν1] at hpt ⊢
        simp at hpt ⊢
        linear_combination hpt
      · rw [hμm, hνm] at hpt ⊢
        simp at hpt ⊢
        linear_combination -hpt
  have hI1 : inducedClassFunction c.H0 (μ.1 - ν.1) 1 = 0 := by
    unfold inducedClassFunction
    have hsum : (∑ x : G, if hx : x⁻¹ * 1 * x ∈ c.H0 then
          (μ.1 - ν.1) ⟨x⁻¹ * 1 * x, hx⟩ else 0) =
        (Nat.card G : ℂ) * (μ.1 1 - ν.1 1) := by
      calc
        (∑ x : G, if hx : x⁻¹ * 1 * x ∈ c.H0 then (μ.1 - ν.1) ⟨x⁻¹ * 1 * x, hx⟩ else 0)
            = ∑ x : G, (μ.1 - ν.1) ⟨1, by simp⟩ := by
                refine Finset.sum_congr rfl ?_
                intro x hx
                have hmem : x⁻¹ * 1 * x ∈ c.H0 := by simp
                rw [dif_pos hmem]
                apply congrArg (μ.1 - ν.1)
                apply Subtype.ext
                simp
        _ = (Nat.card G : ℂ) * (μ.1 1 - ν.1 1) := by
              change (∑ x : G, (μ.1 - ν.1) 1) = (Nat.card G : ℂ) * (μ.1 1 - ν.1 1)
              simp [Pi.sub_apply, Nat.card_eq_fintype_card]
              ring
    rw [hsum]
    have hdeg : μ.1 1 = ν.1 1 := orbit_mem_degree_eq' c hμL
    simp [hdeg]
  have hI1' : tildeNu c h12 μ 1 - tildeNu c h12 ν 1 = 0 := by
    have h' := congrFun (tildeNu_ind c h12 hμL) (1 : G)
    rw [hI1] at h'
    exact h'.symm
  have hmain : (eμ - eν) * χ 1 + (1 + eμ * eν) * η 1 = 0 := by
    rw [← hI1']
    rw [hmu1, hnu1]
    ring
  rcases heμ with hμ1 | hμm
  · rcases heν with hν1 | hνm
    · rw [hμ1, hν1] at hmain
      have h' : (2 : ℂ) * η 1 = 0 := by linear_combination hmain
      have h2ne : (2 : ℂ) ≠ 0 := by norm_num
      exact hη1 ((mul_eq_zero.mp h').resolve_left h2ne)
    · rw [hμ1, hνm] at hmain
      have h' : (2 : ℂ) * χ 1 = 0 := by linear_combination hmain
      have h2ne : (2 : ℂ) ≠ 0 := by norm_num
      exact hχ1 ((mul_eq_zero.mp h').resolve_left h2ne)
  · rcases heν with hν1 | hνm
    · rw [hμm, hν1] at hmain
      have h' : (2 : ℂ) * χ 1 = 0 := by linear_combination (-1) * hmain
      have h2ne : (2 : ℂ) ≠ 0 := by norm_num
      exact hχ1 ((mul_eq_zero.mp h').resolve_left h2ne)
    · rw [hμm, hνm] at hmain
      have h' : (2 : ℂ) * η 1 = 0 := by linear_combination hmain
      have h2ne : (2 : ℂ) ≠ 0 := by norm_num
      exact hη1 ((mul_eq_zero.mp h').resolve_left h2ne)

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

private lemma fixed_orbit_delta_norm (c : Hyp11 G) (h12 : Hyp12 c)
    {ν : Irr (↥c.H0)} (hfix : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1)
    {μ : ClassFunction (↥c.H0)} (hμL : μ ∈ orbit c.H0 c.U ν.1)
    (hμs : conjChar c.H0 (s_normalizes_H0 c h12) μ ≠ μ) :
    normSq G (inducedClassFunction c.H0 (μ - ν.1)) = 3 := by
  classical
  have hμirr : IsIrreducibleCharacter μ :=
    orbit_mem_isIrreducible c.H0 c.U ν.2 hμL
  have hμν : μ ≠ ν.1 := by
    intro hEq
    apply hμs
    rw [hEq, hfix]
  have hμsν : conjChar c.H0 (s_normalizes_H0 c h12) μ ≠ ν.1 := by
    intro hEq
    apply hμs
    have h' := congrArg (conjChar c.H0 (s_normalizes_H0 c h12)) hEq
    rw [conjChar_conjChar c h12 μ, hfix] at h'
    rw [h', hfix]
  rw [delta_norm c h12 (H0_index c h12) hμirr ν.2 hμL hμν hμsν]
  rw [theta_norm c h12 (H0_index c h12) hμirr]
  rw [theta_norm c h12 (H0_index c h12) ν.2]
  norm_num [hfix, hμs]

private lemma fixed_orbit_delta_degree_zero (c : Hyp11 G) (h12 : Hyp12 c)
    {ν : Irr (↥c.H0)} {μ : ClassFunction (↥c.H0)}
    (hμL : μ ∈ orbit c.H0 c.U ν.1) :
    inducedClassFunction c.H0 (μ - ν.1) 1 = 0 := by
  classical
  unfold inducedClassFunction
  have hsum : (∑ x : G, if hx : x⁻¹ * 1 * x ∈ c.H0 then
        (μ - ν.1) ⟨x⁻¹ * 1 * x, hx⟩ else 0) =
      (Nat.card G : ℂ) * (μ 1 - ν.1 1) := by
    calc
      (∑ x : G, if hx : x⁻¹ * 1 * x ∈ c.H0 then (μ - ν.1) ⟨x⁻¹ * 1 * x, hx⟩ else 0)
          = ∑ x : G, (μ - ν.1) ⟨1, by simp⟩ := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              have hmem : x⁻¹ * 1 * x ∈ c.H0 := by simp
              rw [dif_pos hmem]
              apply congrArg (μ - ν.1)
              apply Subtype.ext
              simp
      _ = (Nat.card G : ℂ) * (μ 1 - ν.1 1) := by
            change (∑ x : G, (μ - ν.1) 1) = (Nat.card G : ℂ) * (μ 1 - ν.1 1)
            simp [Pi.sub_apply, Nat.card_eq_fintype_card]
            ring
  rw [hsum]
  have hdeg : μ 1 = ν.1 1 := orbit_mem_degree_eq' c hμL
  simp [hdeg]

private lemma fixed_orbit_delta_pairing (c : Hyp11 G) (h12 : Hyp12 c)
    {χ : ClassFunction G} (hχ : IsPMIrr G χ)
    {ν : Irr (↥c.H0)} (hνB : ν ∈ BOf c h12 χ)
    (hfix : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1)
    {μ : ClassFunction (↥c.H0)} (hμL : μ ∈ orbit c.H0 c.U ν.1)
    (hμs : conjChar c.H0 (s_normalizes_H0 c h12) μ ≠ μ) :
    scalarProduct G χ (inducedClassFunction c.H0 (μ - ν.1)) = 1 ∨
      scalarProduct G χ (inducedClassFunction c.H0 (μ - ν.1)) = -1 := by
  classical
  let μI : Irr (↥c.H0) := ⟨μ, orbit_mem_isIrreducible c.H0 c.U ν.2 hμL⟩
  have hμB : μI ∉ BOf c h12 χ := by
    intro hμB
    have hμν : μI ≠ ν := by
      intro hEq
      apply hμs
      change conjChar c.H0 (s_normalizes_H0 c h12) μI.1 = μI.1
      rw [hEq, hfix]
    have hpair := BOf_orbit_pair_conj c h12 hχ hμB hνB hμL hμν
    apply hμs
    have hEq : μ = ν.1 := by
      have h' := congrArg (conjChar c.H0 (s_normalizes_H0 c h12)) hpair
      rw [conjChar_conjChar c h12 μ, hfix] at h'
      exact h'
    rw [hEq, hfix]
  have hpair0 : scalarProduct G χ (tildeNu c h12 μI) = 0 := by
    by_contra hne
    exact hμB ((BOf_mem_iff c h12 χ μI).2 hne)
  have hind := tildeNu_ind c h12 (show μI.1 ∈ orbit c.H0 c.U ν.1 from hμL)
  have hc := congrArg (fun φ : ClassFunction G => scalarProduct G χ φ) hind
  rw [scalarProduct_sub_right] at hc
  have hνpair := BOf_scalar_eq_pm_one c h12 hχ hνB
  rcases hνpair with hp1 | hpm1
  · right
    rw [hc, hpair0, hp1]
    norm_num
  · left
    rw [hc, hpair0, hpm1]
    norm_num

private lemma fixed_orbit_delta_orthogonal (c : Hyp11 G) (h12 : Hyp12 c)
    {χ : ClassFunction G} (hχ : IsPMIrr G χ)
    {ν₁ ν₂ : Irr (↥c.H0)}
    (hν₁B : ν₁ ∈ BOf c h12 χ) (hν₂B : ν₂ ∈ BOf c h12 χ)
    (hν₁fix : conjChar c.H0 (s_normalizes_H0 c h12) ν₁.1 = ν₁.1)
    (hν₂fix : conjChar c.H0 (s_normalizes_H0 c h12) ν₂.1 = ν₂.1)
    (hν₁ν₂ : ν₁ ≠ ν₂)
    {μ₁ μ₂ : ClassFunction (↥c.H0)}
    (hμ₁L : μ₁ ∈ orbit c.H0 c.U ν₁.1)
    (hμ₂L : μ₂ ∈ orbit c.H0 c.U ν₂.1)
    (hμ₁s : conjChar c.H0 (s_normalizes_H0 c h12) μ₁ ≠ μ₁)
    (hμ₂s : conjChar c.H0 (s_normalizes_H0 c h12) μ₂ ≠ μ₂) :
    scalarProduct G (inducedClassFunction c.H0 (μ₁ - ν₁.1))
        (inducedClassFunction c.H0 (μ₂ - ν₂.1)) = 0 := by
  classical
  have hν₁not : ν₁.1 ∉ orbit c.H0 c.U ν₂.1 := by
    intro hL
    have hpair := BOf_orbit_pair_conj c h12 hχ hν₁B hν₂B hL hν₁ν₂
    have hEq : ν₁.1 = ν₂.1 := by
      calc
        ν₁.1 = conjChar c.H0 (s_normalizes_H0 c h12) ν₁.1 := hν₁fix.symm
        _ = ν₂.1 := hpair
    exact hν₁ν₂ (Subtype.ext hEq)
  have hν₁s_not : conjChar c.H0 (s_normalizes_H0 c h12) ν₁.1 ∉ orbit c.H0 c.U ν₂.1 := by
    simpa [hν₁fix] using hν₁not
  have hμ₁irr : IsIrreducibleCharacter μ₁ :=
    orbit_mem_isIrreducible c.H0 c.U ν₁.2 hμ₁L
  have hμ₂irr : IsIrreducibleCharacter μ₂ :=
    orbit_mem_isIrreducible c.H0 c.U ν₂.2 hμ₂L
  have hsp := delta_pair_scalar c h12 (ν₁ := ν₁.1) (ν₂ := ν₂.1)
    (μ₁ := μ₁) (μ₂ := μ₂) ν₁.2 ν₂.2 hμ₁L hμ₂L
  have horth := theta_pair_orth c h12 (H0_index c h12) ν₁.2 ν₂.2
    hμ₁L hμ₂L hν₁not hν₁s_not
  rw [hsp]
  exact horth

private lemma S0_card_ge_four_of_S_ge_eight (c : Hyp11 G)
    (hS : 8 ≤ Nat.card (c.S : Subgroup G)) :
    4 ≤ Nat.card (c.S0 : Subgroup G) := by
  classical
  have hS' : 8 ≤ 2 * 2 ^ c.m := by
    rw [S_nat_card c] at hS
    exact hS
  have hm : 2 ≤ c.m := by
    by_contra hm
    have hmle : c.m ≤ 1 := by omega
    have hpowle : 2 ^ c.m ≤ 2 := pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) hmle
    have hsmall : 2 * 2 ^ c.m ≤ 4 := by nlinarith
    omega
  have hpow : 4 ≤ 2 ^ c.m := pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) hm
  change 4 ≤ Nat.card (c.S0 : Subgroup G)
  rw [S0_nat_card c]
  exact hpow

/-! ## Exactly-two branch: class sums and the Gorenstein integrality step

For `χ ∈ ±Irr(G)` the class-sum scalar
`|G : C_G(g)|·χ(g)/χ(1)` is an algebraic integer (Gorenstein 4.2.10,
formalized through `classSumScalar`).  When `χ(1)` is even, multiplying by
`χ(1)/2` gives `|G : C_G(g)|·χ(g)/2`, and for `g ∈ B` the index
`|G : C_G(g)|` is odd, so `χ(g)/2` is an algebraic integer, i.e.
`χ(g) ≡ 0 (mod 2)`.
-/

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

private lemma pmIrr_half_degree_classSum_isIntegral {G : Type u} [Group G] [Fintype G]
    (χ : ClassFunction G) (hχ : IsPMIrr G χ) (g : G)
    (hhalf : ∃ k : ℤ, (χ 1 : ℂ) / 2 = (k : ℂ)) :
    IsIntegral ℤ (((χ 1 / 2) * (Nat.card (ConjClasses.mk g).carrier : ℂ) * χ g) / χ 1) := by
  classical
  have ha : IsIntegral ℤ ((Nat.card (ConjClasses.mk g).carrier : ℂ) * χ g / χ 1) :=
    pmIrr_classSum_isIntegral χ hχ g
  rcases hhalf with ⟨k, hk⟩
  have hkint : IsIntegral ℤ ((k : ℂ) * ((Nat.card (ConjClasses.mk g).carrier : ℂ) * χ g / χ 1)) :=
    (isIntegral_intCast k).mul ha
  have h1ne : χ 1 ≠ 0 := by
    rcases hχ with hχpos | hχneg
    · exact irreducible_char_one_ne_zero hχpos
    · have h' : (-χ) 1 ≠ 0 := irreducible_char_one_ne_zero hχneg
      simpa using h'
  convert hkint using 1
  rw [← hk]
  field_simp [h1ne]

private lemma odd_bezout (n : ℕ) (hn : Odd n) : ∃ a b : ℤ, a * (n : ℤ) + b * 2 = 1 := by
  have hcop : Nat.Coprime 2 n := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    exact (by
      have h : ¬ Even n := Nat.not_even_iff_odd.mpr hn
      simpa [even_iff_two_dvd] using h)
  rcases (Nat.Coprime.isCoprime hcop) with ⟨a, b, h⟩
  refine ⟨b, a, ?_⟩
  simpa [add_comm, mul_comm] using h

private lemma pmIrr_chi_half_isIntegral_of_odd_index {G : Type u} [Group G] [Fintype G]
    (χ : ClassFunction G) (hχ : IsPMIrr G χ) (g : G)
    (hhalf : ∃ k : ℤ, (χ 1 : ℂ) / 2 = (k : ℂ))
    (hodd : Odd (Nat.card (ConjClasses.mk g).carrier)) :
    IsIntegral ℤ (χ g / 2) := by
  classical
  let n : ℕ := Nat.card (ConjClasses.mk g).carrier
  rcases odd_bezout n hodd with ⟨a, b, hab⟩
  have ha : IsIntegral ℤ (((χ 1 / 2) * (n : ℂ) * χ g) / χ 1) := by
    simpa [n] using pmIrr_half_degree_classSum_isIntegral χ hχ g hhalf
  have h1ne : χ 1 ≠ 0 := by
    rcases hχ with hχpos | hχneg
    · exact irreducible_char_one_ne_zero hχpos
    · have h' : (-χ) 1 ≠ 0 := irreducible_char_one_ne_zero hχneg
      simpa using h'
  have hnHalf : IsIntegral ℤ ((n : ℂ) * (χ g / 2)) := by
    have hEq : ((χ 1 / 2) * (n : ℂ) * χ g) / χ 1 = (n : ℂ) * (χ g / 2) := by
      field_simp [h1ne]
    rw [← hEq]
    exact ha
  have hχg : IsIntegral ℤ (χ g) := by
    rcases hχ with hχpos | hχneg
    · rcases hχpos with ⟨n0, ρ, hρ, rfl⟩
      exact character_value_isIntegral ρ g
    · have hχneg0 : IsIrreducibleCharacter (-χ) := hχneg
      rcases hχneg with ⟨n0, ρ, hρ, hEq⟩
      have hEq' : χ g = -ρ.character g := by
        have hneg : χ = -ρ.character := by simpa using congrArg Neg.neg hEq
        simpa using congrFun hneg g
      rw [hEq']
      exact (character_value_isIntegral ρ g).neg
  have hcoef : (a : ℂ) * ((n : ℂ) * (χ g / 2)) + (b : ℂ) * χ g = χ g / 2 := by
    have hab' : (a : ℂ) * (n : ℂ) + (b : ℂ) * 2 = 1 := by
      exact_mod_cast hab
    calc
      (a : ℂ) * ((n : ℂ) * (χ g / 2)) + (b : ℂ) * χ g
          = ((a : ℂ) * (n : ℂ) + (b : ℂ) * 2) * (χ g / 2) := by ring
      _ = χ g / 2 := by rw [hab']; simp
  rw [← hcoef]
  exact ((isIntegral_intCast a).mul hnHalf).add ((isIntegral_intCast b).mul hχg)

private lemma chi_congruent_zero_of_half_isIntegral {G : Type u} [Group G] [Fintype G]
    (χ : ClassFunction G) (g : G) (hhalf : IsIntegral ℤ (χ g / 2)) :
    CongruentModTwo (χ g) 0 := by
  refine ⟨χ g / 2, hhalf, ?_⟩
  ring

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

/-! ## `B = C_U(S)` as the fixed subgroup of the conjugation action of `S` on `U` -/

private lemma S_le_normalizer_U' (c : Hyp11 G) :
    (c.S : Subgroup G) ≤ Subgroup.normalizer (c.U : Set G) := by
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · intro hu
    exact S_normalizes_U c s hs u hu
  · intro hsu
    have h1 := S_normalizes_U c s⁻¹ ((c.S : Subgroup G).inv_mem hs) (s * u * s⁻¹) hsu
    have h2 : s⁻¹ * (s * u * s⁻¹) * (s⁻¹)⁻¹ = u := by group
    rwa [h2] at h1

local instance instNormalizesS (c : Hyp11 G) :
    Subgroup.Normalizes (c.S : Subgroup G) c.U := ⟨S_le_normalizer_U' c⟩

private lemma mem_U_of_mem_B' (c : Hyp11 G) {b : G} (hbB : b ∈ c.B) : b ∈ c.U := by
  unfold Hyp11.B at hbB
  have hbB1 : b ∈ Hyp11.B1 c := (inf_le_left : Hyp11.B1 c ⊓ Hyp11.B2 c ≤ Hyp11.B1 c) hbB
  unfold Hyp11.B1 centralizerIn at hbB1
  exact (inf_le_left : c.U ⊓ Subgroup.centralizer ({c.t1} : Set G) ≤ c.U) hbB1

private lemma mem_B1_of_mem_B' (c : Hyp11 G) {b : G} (hbB : b ∈ c.B) : b ∈ Hyp11.B1 c := by
  unfold Hyp11.B at hbB
  exact (inf_le_left : Hyp11.B1 c ⊓ Hyp11.B2 c ≤ Hyp11.B1 c) hbB

private lemma mem_B2_of_mem_B' (c : Hyp11 G) {b : G} (hbB : b ∈ c.B) : b ∈ Hyp11.B2 c := by
  unfold Hyp11.B at hbB
  exact (inf_le_right : Hyp11.B1 c ⊓ Hyp11.B2 c ≤ Hyp11.B2 c) hbB

private lemma b_mem_fixedSubgroup' (c : Hyp11 G) {b : G} (hbB : b ∈ c.B) :
    (⟨b, mem_U_of_mem_B' c hbB⟩ : ↥c.U) ∈
      fixedSubgroup (c.S : Subgroup G) c.U := by
  classical
  rw [mem_fixedSubgroup_iff]
  intro a
  apply Subtype.ext
  change (a : G) * b * (a : G)⁻¹ = b
  have hbt1 : Commute c.t1 b := by
    have hbB1 := mem_B1_of_mem_B' c hbB
    have hbcent : b ∈ Subgroup.centralizer ({c.t1} : Set G) := by
      unfold Hyp11.B1 centralizerIn at hbB1
      exact hbB1.2
    have hcomm : c.t1 * b = b * c.t1 :=
      (Subgroup.mem_centralizer_iff).1 hbcent c.t1 (by simp)
    exact hcomm
  have hbt2 : Commute c.t2 b := by
    have hbB2 := mem_B2_of_mem_B' c hbB
    have hbcent : b ∈ Subgroup.centralizer ({c.t2} : Set G) := by
      unfold Hyp11.B2 centralizerIn at hbB2
      exact hbB2.2
    have hcomm : c.t2 * b = b * c.t2 :=
      (Subgroup.mem_centralizer_iff).1 hbcent c.t2 (by simp)
    exact hcomm
  have hbt1t2 : Commute (c.t1 * c.t2) b :=
    (Commute.mul_right hbt1.symm hbt2.symm).symm
  by_cases haS0 : (a : G) ∈ (c.S0 : Subgroup G)
  · rcases (Subgroup.mem_zpowers_iff.mp (by simpa [c.S0_eq_zpowers] using haS0)) with
      ⟨k, hk⟩
    have hk' : Commute ((c.t1 * c.t2) ^ k) b := hbt1t2.zpow_left k
    have hEq : (a : G) * b * (a : G)⁻¹ = b := by
      rw [← hk]
      rw [hk'.eq]
      group
    exact hEq
  · let aS : ↥(c.S : Subgroup G) := a
    let t1S : ↥(c.S : Subgroup G) := ⟨c.t1, c.t1_mem_S⟩
    have haS : aS ∉ (c.S0 : Subgroup G).subgroupOf (c.S : Subgroup G) := by
      exact fun h => haS0 (Subgroup.mem_subgroupOf.mp h)
    have ht1S : t1S ∉ (c.S0 : Subgroup G).subgroupOf (c.S : Subgroup G) := by
      exact fun h => c.t1_not_mem_S0 (Subgroup.mem_subgroupOf.mp h)
    have hmul : aS * t1S ∈ (c.S0 : Subgroup G).subgroupOf (c.S : Subgroup G) := by
      exact (Subgroup.mul_mem_iff_of_index_two (S0_index c)).2 (by simpa [haS, ht1S])
    have hrS0 : (a : G) * c.t1 ∈ (c.S0 : Subgroup G) := by
      simpa [aS, t1S, Subgroup.coe_mul] using (Subgroup.mem_subgroupOf.mp hmul)
    rcases (Subgroup.mem_zpowers_iff.mp (by simpa [c.S0_eq_zpowers] using hrS0)) with
      ⟨k, hk⟩
    have hbr : Commute ((a : G) * c.t1) b := by
      simpa [hk.symm] using hbt1t2.zpow_left k
    have hb_rt : Commute b ((a : G) * c.t1 * c.t1) :=
      Commute.mul_right hbr.symm hbt1.symm
    have ha_eq : (a : G) = (a : G) * c.t1 * c.t1 := by
      calc
        (a : G) = (a : G) * 1 := by simp
        _ = (a : G) * (c.t1 * c.t1) := by rw [← pow_two, c.t1_involution.2]
        _ = (a : G) * c.t1 * c.t1 := by group
    have hb_a : Commute b (a : G) := by
      simpa [ha_eq.symm] using hb_rt
    have hEq : (a : G) * b * (a : G)⁻¹ = b := by
      rw [hb_a.symm.eq]
      group
    exact hEq

private lemma mem_B_of_fixed (c : Hyp11 G) {b : ↥c.U}
    (hb : b ∈ fixedSubgroup (c.S : Subgroup G) c.U) :
    (b : G) ∈ c.B := by
  classical
  rw [mem_fixedSubgroup_iff] at hb
  have hb1 : (b : G) ∈ Hyp11.B1 c := by
    unfold Hyp11.B1 centralizerIn
    constructor
    · exact b.2
    · change (b : G) ∈ Subgroup.centralizer ({c.t1} : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have ht : h = c.t1 := by simpa using hh
      subst h
      have hfix := hb ⟨c.t1, c.t1_mem_S⟩
      have hsmul : (⟨c.t1, c.t1_mem_S⟩ : ↥(c.S : Subgroup G)) • b = b := hfix
      have hcoef : (((⟨c.t1, c.t1_mem_S⟩ : ↥(c.S : Subgroup G)) • b : ↥c.U) : G) =
          c.t1 * (b : G) * c.t1⁻¹ := by
        rw [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
      have hEq : c.t1 * (b : G) * c.t1⁻¹ = (b : G) := by
        simpa [hcoef] using congrArg Subtype.val hsmul
      have hcomm : c.t1 * (b : G) = (b : G) * c.t1 := by
        calc
          c.t1 * (b : G) = (c.t1 * (b : G) * c.t1⁻¹) * c.t1 := by group
          _ = (b : G) * c.t1 := by rw [hEq]
      simpa using hcomm
  have hb2 : (b : G) ∈ Hyp11.B2 c := by
    unfold Hyp11.B2 centralizerIn
    constructor
    · exact b.2
    · change (b : G) ∈ Subgroup.centralizer ({c.t2} : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have ht : h = c.t2 := by simpa using hh
      subst h
      have hfix := hb ⟨c.t2, c.t2_mem_S⟩
      have hcoef : (((⟨c.t2, c.t2_mem_S⟩ : ↥(c.S : Subgroup G)) • b : ↥c.U) : G) =
          c.t2 * (b : G) * c.t2⁻¹ := by
        rw [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
      have hEq : c.t2 * (b : G) * c.t2⁻¹ = (b : G) := by
        simpa [hcoef] using congrArg Subtype.val hfix
      have hcomm : c.t2 * (b : G) = (b : G) * c.t2 := by
        calc
          c.t2 * (b : G) = (c.t2 * (b : G) * c.t2⁻¹) * c.t2 := by group
          _ = (b : G) * c.t2 := by rw [hEq]
      simpa using hcomm
  unfold Hyp11.B
  exact ⟨hb1, hb2⟩

/-! ## Restriction of full-orbit fixed characters to `U` -/

private lemma s0Orbit_self_mem' (c : Hyp11 G) (α : Irr (↥c.U)) : α ∈ s0Orbit c α := by
  classical
  refine Finset.mem_image.mpr ⟨⟨1, (c.S0 : Subgroup G).one_mem⟩, Finset.mem_univ _, ?_⟩
  exact conjIrrS_one c α

private lemma s0Orbit_eq_singleton_of_card_one (c : Hyp11 G) (α : Irr (↥c.U))
    (hcard : (s0Orbit c α).card = 1) : s0Orbit c α = {α} := by
  classical
  rcases Finset.card_eq_one.mp hcard with ⟨β, hβ⟩
  have hαmem : α ∈ s0Orbit c α := s0Orbit_self_mem' c α
  have hαβ : α = β := by
    rw [hβ] at hαmem
    simpa using hαmem
  rw [hβ, hαβ]

private lemma sum_s0Orbit_eq_α_of_card_one (c : Hyp11 G) (α : Irr (↥c.U))
    (hcard : (s0Orbit c α).card = 1) :
    (∑ α' ∈ s0Orbit c α, α'.1) = α.1 := by
  rw [s0Orbit_eq_singleton_of_card_one c α hcard]
  simp

private lemma conjIrrS_eval_smul (c : Hyp11 G) {g : G} (hg : g ∈ (c.S : Subgroup G))
    (α : Irr (↥c.U)) (u : ↥c.U) :
    (conjIrrS c hg α).1 u = α.1 ((⟨g, hg⟩ : ↥(c.S : Subgroup G)) • u) := by
  classical
  change α.1 ⟨g * (u : G) * g⁻¹, S_normalizes_U c g hg (u : G) u.2⟩ =
    α.1 ((⟨g, hg⟩ : ↥(c.S : Subgroup G)) • u)
  congr 1

private lemma s0Orbit_fixed_under_S0 (c : Hyp11 G)
    {α β : Irr (↥c.U)} (hβ : β ∈ s0Orbit c α)
    {b : ↥c.U} (hb : b ∈ fixedSubgroup (c.S : Subgroup G) c.U) :
    β.1 b = α.1 b := by
  classical
  rcases Finset.mem_image.mp hβ with ⟨g, hg, rfl⟩
  have hfix : (⟨(g : G), c.S0_le_S g.2⟩ : ↥(c.S : Subgroup G)) • b = b := by
    exact (mem_fixedSubgroup_iff (c.S : Subgroup G) c.U b).1 hb ⟨(g : G), c.S0_le_S g.2⟩
  calc
    (conjIrrS c (c.S0_le_S g.2) α).1 b = α.1 ((⟨(g : G), c.S0_le_S g.2⟩ : ↥(c.S : Subgroup G)) • b) :=
      conjIrrS_eval_smul c (c.S0_le_S g.2) α b
    _ = α.1 b := by rw [hfix]

private lemma s0Orbit_sum_eval_eq_card_mul (c : Hyp11 G)
    (α : Irr (↥c.U)) {b : ↥c.U} (hb : b ∈ fixedSubgroup (c.S : Subgroup G) c.U) :
    (∑ α' ∈ s0Orbit c α, α'.1) b = ((s0Orbit c α).card : ℂ) * α.1 b := by
  classical
  calc
    (∑ α' ∈ s0Orbit c α, α'.1) b = ∑ α' ∈ s0Orbit c α, α'.1 b := by
      rw [Finset.sum_apply]
    _ = ∑ α' ∈ s0Orbit c α, α.1 b := by
      refine Finset.sum_congr rfl ?_
      intro α' hα'
      exact s0Orbit_fixed_under_S0 c hα' hb
    _ = ((s0Orbit c α).card : ℂ) * α.1 b := by
      rw [Finset.sum_const]
      simp [nsmul_eq_mul, mul_comm]

/-- The filtered set `F` of `s`-fixed full-orbit members of `B(χ)` (the set
whose cardinality Lemma 3.3 controls). -/
private def F (c : Hyp11 G) (h12 : Hyp12 c) (χ : ClassFunction G) : Finset (Irr (↥c.H0)) :=
  (BOf c h12 χ).filter (fun ν : Irr (↥c.H0) =>
    conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1 ∧
      (orbit c.H0 c.U ν.1).card = (c.U.subgroupOf c.H0).index)

private lemma fixed_full_orbit_restrict (c : Hyp11 G) (h12 : Hyp12 c) (hSC : Section3Hyp c)
    {ν : Irr (↥c.H0)}
    (hfix : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1)
    (horbit : (orbit c.H0 c.U ν.1).card = (c.U.subgroupOf c.H0).index) :
    ∃ α : Irr (↥c.U),
      orbit c.H0 c.U ν.1 = orbitOfAlpha c h12 hSC α ∧
      restrictU c h12 ν.1 = α.1 ∧
      FixedIrr (c.S : Subgroup G) c.U α ∧
      ν.1 (1 : ↥c.H0) = α.1 (1 : ↥c.U) := by
  classical
  rcases orbit_is_orbitOfAlpha c h12 hSC ν with ⟨α, hOrbitEq⟩
  have hindex2 : 2 ≤ (c.U.subgroupOf c.H0).index := by
    rw [U_index_eq_S0_card c h12]
    rw [S0_nat_card c]
    have hpow : 2 ^ 1 ≤ 2 ^ c.m := pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) c.one_le_m
    simpa using hpow
  have hmain : (c.U.subgroupOf c.H0).index =
      (c.U.subgroupOf c.H0).index / (s0Orbit c α).card := by
    rw [← orbitOfAlpha_card c h12 hSC α]
    simpa [hOrbitEq] using horbit.symm
  have hcardα : (s0Orbit c α).card = 1 := by
    have hnle : (s0Orbit c α).card ≤ 2 := (remark_3_1 c h12 hSC α).2.1
    have hnpos : 0 < (s0Orbit c α).card := Finset.card_pos.mpr ⟨α, s0Orbit_self_mem' c α⟩
    by_cases hn1 : (s0Orbit c α).card = 1
    · exact hn1
    · have hn2 : (s0Orbit c α).card = 2 := by omega
      exfalso
      have hlt : (c.U.subgroupOf c.H0).index / 2 < (c.U.subgroupOf c.H0).index :=
        Nat.div_lt_self (by omega : 0 < (c.U.subgroupOf c.H0).index) (by norm_num : 1 < 2)
      rw [hn2] at hmain
      exact (not_lt_of_ge (by omega : (c.U.subgroupOf c.H0).index ≤
        (c.U.subgroupOf c.H0).index / 2)) hlt
  have hres : restrictU c h12 ν.1 = α.1 := by
    have hspec := (orbitOfAlpha_spec c h12 hSC α).2 ν.1 (by
      simpa [hOrbitEq] using orbit_self_mem' c ν.1)
    rw [hspec, sum_s0Orbit_eq_α_of_card_one c α hcardα]
  have hfixorb : ∀ μ : ClassFunction (↥c.H0), μ ∈ orbitOfAlpha c h12 hSC α →
      conjChar c.H0 (s_normalizes_H0 c h12) μ ∈ orbitOfAlpha c h12 hSC α := by
    intro μ hμ
    have hμ' : μ ∈ orbit c.H0 c.U ν.1 := by simpa [hOrbitEq] using hμ
    have hc := orbit_subset_conjChar c h12 μ hμ'
    simpa [hfix, hOrbitEq] using hc
  have hnotle : ¬ stabilizerS c α ≤ (c.S0 : Subgroup G) := by
    intro hle
    exact (orbitOfAlpha_fixed_iff c h12 hSC α).1 hfixorb hle
  have hstab : stabilizerS c α = (c.S : Subgroup G) := by
    rcases (stabilizerS_not_le_S0_iff c h12 hSC α).1 hnotle with h | h
    · exact h.2
    · exfalso
      omega
  have hfixIr : FixedIrr (c.S : Subgroup G) c.U α := by
    unfold FixedIrr
    intro s
    funext u
    have hmem : (s : G) ∈ stabilizerS c α := by
      rw [hstab]
      exact s.2
    rcases hmem with ⟨hsS, hconj⟩
    have hsub : (⟨(s : G), hsS⟩ : ↥(c.S : Subgroup G)) = s := by
      apply Subtype.ext
      rfl
    have hconj' : conjIrrS c s.2 α = α := by
      simpa [hsub] using hconj
    have heq := congrFun (congrArg Subtype.val hconj') u
    rw [conjIrrS_eval_smul c s.2 α u] at heq
    exact heq
  have hdeg : ν.1 (1 : ↥c.H0) = α.1 (1 : ↥c.U) := by
    have heq := congrFun hres (1 : ↥c.U)
    change ν.1 ⟨(1 : G), (h12.U_normal_in_H0).1 (1 : ↥c.U).2⟩ = α.1 (1 : ↥c.U) at heq
    have h1 : ν.1 ⟨(1 : G), (h12.U_normal_in_H0).1 (1 : ↥c.U).2⟩ = ν.1 (1 : ↥c.H0) := by
      congr 1
    rw [h1] at heq
    exact heq
  exact ⟨α, hOrbitEq, hres, hfixIr, hdeg⟩

private lemma U_coprime_two (c : Hyp11 G) : Nat.Coprime 2 (Nat.card (↥c.U)) := by
  have h1 : Nat.card (↥c.U) = Nat.card (pPrimeCore 2 c.H) := by
    dsimp [Hyp11.U]
    rw [oddCoreOf]
    exact Subgroup.card_map_of_injective (f := c.H.subtype)
      (K := pPrimeCore 2 c.H) (Subgroup.subtype_injective c.H)
  rw [h1]
  exact pPrimeCore_coprime_card (p := 2) (G := c.H)

private lemma B_coprime_two (c : Hyp11 G) :
    Nat.Coprime 2 (Nat.card (↥(fixedSubgroup (c.S : Subgroup G) c.U))) := by
  classical
  have hU2' : Nat.Coprime 2 (Nat.card (↥c.U)) := U_coprime_two c
  have hdiv : Nat.card (↥(fixedSubgroup (c.S : Subgroup G) c.U)) ∣ Nat.card (↥c.U) := by
    exact Subgroup.card_subgroup_dvd_card (fixedSubgroup (c.S : Subgroup G) c.U)
  exact Nat.Coprime.of_dvd_right hdiv hU2'

private lemma pmIrr_one_int {G : Type u} [Group G] [Fintype G]
    (χ : ClassFunction G) (hχ : IsPMIrr G χ) : ∃ m : ℤ, (χ 1 : ℂ) = (m : ℂ) := by
  classical
  rcases hχ with hχpos | hχneg
  · rcases hχpos with ⟨n, ρ, hρ, rfl⟩
    refine ⟨(Module.finrank ℂ (Fin n → ℂ) : ℤ), ?_⟩
    rw [Representation.char_one]
    norm_num
  · rcases hχneg with ⟨n, ρ, hρ, hEq⟩
    have hneg : χ = -ρ.character := by simpa using congrArg Neg.neg hEq
    rw [hneg]
    refine ⟨-(Module.finrank ℂ (Fin n → ℂ) : ℤ), ?_⟩
    rw [Pi.neg_apply, Representation.char_one]
    norm_num

private lemma irr_one_int {H : Type u} [Group H] [Fintype H] (ν : Irr H) :
    ∃ a : ℤ, (ν.1 1 : ℂ) = (a : ℂ) := by
  classical
  rcases ν.2 with ⟨n, ρ, hρ, hEq⟩
  rw [hEq]
  refine ⟨(Module.finrank ℂ (Fin n → ℂ) : ℤ), ?_⟩
  rw [Representation.char_one]
  norm_num

private lemma odd_degree_one (c : Hyp11 G) (α : Irr (↥c.U)) :
    ∃ d : ℕ, Odd d ∧ (d : ℂ) = α.1 (1 : ↥c.U) := by
  exact irr_degree_odd (U_coprime_two c) α

private lemma chi_one_half_int_of_congruence {ν₁₁ ν₂₁ : ℂ} (χ : ClassFunction G)
    (hχ : IsPMIrr G χ)
    (hχ1 : ∃ m : ℤ, (χ 1 : ℂ) = (m : ℂ))
    (hcong : CongruentModTwo (χ 1) (ν₁₁ + ν₂₁))
    (hν₁₁ : ∃ a₁ : ℤ, (ν₁₁ : ℂ) = (a₁ : ℂ))
    (hν₂₁ : ∃ a₂ : ℤ, (ν₂₁ : ℂ) = (a₂ : ℂ))
    (hodd₁ : ∃ d₁ : ℕ, Odd d₁ ∧ (d₁ : ℂ) = (ν₁₁ : ℂ))
    (hodd₂ : ∃ d₂ : ℕ, Odd d₂ ∧ (d₂ : ℂ) = (ν₂₁ : ℂ)) :
    ∃ k : ℤ, (χ 1 : ℂ) / 2 = (k : ℂ) := by
  classical
  rcases hχ1 with ⟨m, hm⟩
  rcases hν₁₁ with ⟨a₁, ha₁⟩
  rcases hν₂₁ with ⟨a₂, ha₂⟩
  rcases hodd₁ with ⟨d₁, hodd₁d, hd₁⟩
  rcases hodd₂ with ⟨d₂, hodd₂d, hd₂⟩
  have ha₁d₁ : a₁ = (d₁ : ℤ) := by
    have hEqℂ : (a₁ : ℂ) = (d₁ : ℂ) := by
      rw [← ha₁, ← hd₁]
    exact_mod_cast hEqℂ
  have ha₂d₂ : a₂ = (d₂ : ℤ) := by
    have hEqℂ : (a₂ : ℂ) = (d₂ : ℂ) := by
      rw [← ha₂, ← hd₂]
    exact_mod_cast hEqℂ
  have hodd₁a : Odd a₁ := by
    rw [ha₁d₁]
    exact_mod_cast hodd₁d
  have hodd₂a : Odd a₂ := by
    rw [ha₂d₂]
    exact_mod_cast hodd₂d
  have heven : Even (a₁ + a₂ : ℤ) := Odd.add_odd hodd₁a hodd₂a
  have hcong' : CongruentModTwo ((m : ℂ)) ((a₁ + a₂ : ℤ) : ℂ) := by
    simpa [hm, ha₁, ha₂] using hcong
  have hdiv : (2 : ℤ) ∣ m - (a₁ + a₂) := CongruentModTwo.eq_of_int hcong'
  have hdiv2 : (2 : ℤ) ∣ (a₁ + a₂ : ℤ) := even_iff_two_dvd.mp heven
  have hdivm : (2 : ℤ) ∣ m := by
    rcases hdiv with ⟨q, hq⟩
    rcases hdiv2 with ⟨r, hr⟩
    refine ⟨q + r, ?_⟩
    have hq' : m = 2 * q + (a₁ + a₂) := by omega
    rw [hq', hr]
    ring
  rcases hdivm with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  rw [hm, hk]
  norm_num

private lemma not_F_congruent_zero_on_B (c : Hyp11 G) (h12 : Hyp12 c) (hSC : Section3Hyp c)
    {χ : ClassFunction G} (hχ : IsPMIrr G χ)
    (hBOfle : (BOf c h12 χ).card ≤ 3)
    {ν : Irr (↥c.H0)} (hνB : ν ∈ BOf c h12 χ) (hνnotF : ν ∉ F c h12 χ)
    {ν₁ ν₂ : Irr (↥c.H0)}
    (hν₁F : ν₁ ∈ F c h12 χ) (hν₂F : ν₂ ∈ F c h12 χ) (hν₁ν₂ : ν₁ ≠ ν₂)
    (b : ↥c.U) (hb : b ∈ fixedSubgroup (c.S : Subgroup G) c.U)
    (hbH0 : (b : G) ∈ c.H0) :
    CongruentModTwo (ν.1 ⟨(b : G), hbH0⟩) 0 := by
  classical
  rcases orbit_is_orbitOfAlpha c h12 hSC ν with ⟨α, hOrbitEq⟩
  have hcardα : (s0Orbit c α).card = 2 := by
    by_contra hne
    have hcard1 : (s0Orbit c α).card = 1 := by
      have hle : (s0Orbit c α).card ≤ 2 := (remark_3_1 c h12 hSC α).2.1
      have hpos : 0 < (s0Orbit c α).card := Finset.card_pos.mpr ⟨α, s0Orbit_self_mem' c α⟩
      omega
    have hfull : (orbit c.H0 c.U ν.1).card = (c.U.subgroupOf c.H0).index := by
      rw [hOrbitEq, orbitOfAlpha_card c h12 hSC α, hcard1]
      simp
    have hνnotfix : ¬ conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1 := by
      intro hfix
      exact hνnotF (Finset.mem_filter.mpr ⟨hνB, hfix, hfull⟩)
    let ν' : Irr (↥c.H0) := conjIrr c h12 ν
    have hν'B : ν' ∈ BOf c h12 χ := by
      rw [BOf_mem_iff]
      rw [BOf_mem_iff] at hνB
      simpa [ν', tildeNu_invariance] using hνB
    have hν'neν : ν' ≠ ν := by
      intro hEq
      apply hνnotfix
      have h' := congrArg (fun μ : Irr (↥c.H0) => μ.1) hEq
      rw [conjIrr_coe] at h'
      exact h'
    have hν'notF : ν' ∉ F c h12 χ := by
      intro hF'
      have hfix' : conjChar c.H0 (s_normalizes_H0 c h12) ν'.1 = ν'.1 := (Finset.mem_filter.mp hF').2.1
      rw [conjIrr_coe] at hfix'
      have hfixν : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1 := by
        rw [conjChar_conjChar c h12 ν] at hfix'
        exact hfix'.symm
      exact hνnotfix hfixν
    have hν'neν₁ : ν' ≠ ν₁ := by
      intro hEq
      have hfixν : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1 := by
        have hc := congrArg (fun μ : Irr (↥c.H0) => μ.1) hEq
        rw [conjIrr_coe] at hc
        have hfix₁ : conjChar c.H0 (s_normalizes_H0 c h12) ν₁.1 = ν₁.1 := (Finset.mem_filter.mp hν₁F).2.1
        have hEq2 : ν.1 = ν₁.1 := by
          have hc' := congrArg (conjChar c.H0 (s_normalizes_H0 c h12)) hc
          rw [conjChar_conjChar c h12 ν] at hc'
          rw [hfix₁] at hc'
          exact hc'
        exact hc.trans hEq2.symm
      exact hνnotfix hfixν
    have hν'neν₂ : ν' ≠ ν₂ := by
      intro hEq
      have hfixν : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1 := by
        have hc := congrArg (fun μ : Irr (↥c.H0) => μ.1) hEq
        rw [conjIrr_coe] at hc
        have hfix₂ : conjChar c.H0 (s_normalizes_H0 c h12) ν₂.1 = ν₂.1 := (Finset.mem_filter.mp hν₂F).2.1
        have hEq2 : ν.1 = ν₂.1 := by
          have hc' := congrArg (conjChar c.H0 (s_normalizes_H0 c h12)) hc
          rw [conjChar_conjChar c h12 ν] at hc'
          rw [hfix₂] at hc'
          exact hc'
        exact hc.trans hEq2.symm
      exact hνnotfix hfixν
    have hνneν₁ : ν ≠ ν₁ := by
      intro hEq
      exact hνnotF (by simpa [hEq] using hν₁F)
    have hνneν₂ : ν ≠ ν₂ := by
      intro hEq
      exact hνnotF (by simpa [hEq] using hν₂F)
    have hν₁B : ν₁ ∈ BOf c h12 χ := (Finset.mem_filter.mp hν₁F).1
    have hν₂B : ν₂ ∈ BOf c h12 χ := (Finset.mem_filter.mp hν₂F).1
    have hsub : ({ν₁, ν₂, ν, ν'} : Finset (Irr (↥c.H0))) ⊆ BOf c h12 χ := by
      intro μ hμ
      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hμ
      rcases hμ with rfl | rfl | rfl | rfl
      · exact hν₁B
      · exact hν₂B
      · exact hνB
      · exact hν'B
    have h₁not : ν₁ ∉ ({ν₂, ν, ν'} : Finset (Irr (↥c.H0))) := by
      intro h
      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h | h | h
      · exact hν₁ν₂ h
      · exact hνneν₁ h.symm
      · exact hν'neν₁ h.symm
    have h₂not : ν₂ ∉ ({ν, ν'} : Finset (Irr (↥c.H0))) := by
      intro h
      rw [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h | h
      · exact hνneν₂ h.symm
      · exact hν'neν₂ h.symm
    have h₃not : ν ∉ ({ν'} : Finset (Irr (↥c.H0))) := by
      intro h
      exact hν'neν (Finset.mem_singleton.mp h).symm
    have hcard4 : 4 ≤ ({ν₁, ν₂, ν, ν'} : Finset (Irr (↥c.H0))).card := by
      rw [Finset.card_insert_of_notMem h₁not]
      rw [Finset.card_insert_of_notMem h₂not]
      rw [Finset.card_insert_of_notMem h₃not]
      norm_num
    have hcardle : ({ν₁, ν₂, ν, ν'} : Finset (Irr (↥c.H0))).card ≤ (BOf c h12 χ).card :=
      Finset.card_le_card hsub
    omega
  have hspec := (orbitOfAlpha_spec c h12 hSC α).2 ν.1 (by
    simpa [hOrbitEq] using orbit_self_mem' c ν.1)
  have hval : ν.1 ⟨(b : G), hbH0⟩ = (∑ α' ∈ s0Orbit c α, α'.1) b := by
    have he := congrFun hspec b
    simpa [restrictU] using he
  have hsum2 : (∑ α' ∈ s0Orbit c α, α'.1) b = 2 * α.1 b := by
    rw [s0Orbit_sum_eval_eq_card_mul c α hb, hcardα]
    norm_num
  have hz : CongruentModTwo (2 * α.1 b) 0 :=
    CongruentModTwo.two_mul_zero (irr_value_isIntegral α b)
  rw [hval, hsum2]
  exact hz

private lemma chi_congruent_sum_two_on_B (c : Hyp11 G) (h12 : Hyp12 c) (hSC : Section3Hyp c)
    {χ : ClassFunction G} (hχ : IsPMIrr G χ)
    (hBOfle : (BOf c h12 χ).card ≤ 3)
    {ν₁ ν₂ : Irr (↥c.H0)}
    (hν₁F : ν₁ ∈ F c h12 χ) (hν₂F : ν₂ ∈ F c h12 χ)
    (hν₁ν₂ : ν₁ ≠ ν₂) (hFcard : (F c h12 χ).card = 2)
    {α₁ α₂ : Irr (↥c.U)}
    (hres₁ : restrictU c h12 ν₁.1 = α₁.1) (hres₂ : restrictU c h12 ν₂.1 = α₂.1) :
    ∀ b : ↥(fixedSubgroup (c.S : Subgroup G) c.U),
      CongruentModTwo (χ (b.1.1 : G)) (α₁.1 b.1 + α₂.1 b.1) := by
  classical
  intro b
  have hbH0 : (b.1.1 : G) ∈ c.H0 := U_le_H0 c b.1.2
  have h24 := (lemma_2_4 c h12 hχ).2 b.1 hbH0
  have hνcong : ∀ ν : Irr (↥c.H0), ν ∈ BOf c h12 χ →
      CongruentModTwo (ν.1 ⟨(b.1.1 : G), hbH0⟩)
        (if ν ∈ F c h12 χ then ν.1 ⟨(b.1.1 : G), hbH0⟩ else 0) := by
    intro ν hν
    by_cases hF : ν ∈ F c h12 χ
    · simpa [hF] using CongruentModTwo.refl (ν.1 ⟨(b.1.1 : G), hbH0⟩)
    · have hz := not_F_congruent_zero_on_B c h12 hSC hχ hBOfle hν hF hν₁F hν₂F hν₁ν₂ b.1 b.2 hbH0
      simp [hF, hz]
  have hsum1 : CongruentModTwo (∑ ν ∈ BOf c h12 χ, ν.1 ⟨(b.1.1 : G), hbH0⟩)
      (∑ ν ∈ BOf c h12 χ, if ν ∈ F c h12 χ then ν.1 ⟨(b.1.1 : G), hbH0⟩ else 0) := by
    rw [← Finset.sum_coe_sort (s := BOf c h12 χ) (f := fun ν : Irr (↥c.H0) =>
      ν.1 ⟨(b.1.1 : G), hbH0⟩)]
    rw [← Finset.sum_coe_sort (s := BOf c h12 χ) (f := fun ν : Irr (↥c.H0) =>
      if ν ∈ F c h12 χ then ν.1 ⟨(b.1.1 : G), hbH0⟩ else 0)]
    exact CongruentModTwo.sum (fun ν : {ν : Irr (↥c.H0) // ν ∈ BOf c h12 χ} =>
      hνcong ν.1 ν.2)
  have hfilter : (BOf c h12 χ).filter (fun ν : Irr (↥c.H0) => ν ∈ F c h12 χ) = F c h12 χ := by
    ext ν
    rw [Finset.mem_filter]
    constructor
    · intro h
      exact h.2
    · intro hνF
      exact ⟨(Finset.mem_filter.mp hνF).1, hνF⟩
  have hsum2 : (∑ ν ∈ BOf c h12 χ, if ν ∈ F c h12 χ then ν.1 ⟨(b.1.1 : G), hbH0⟩ else 0) =
      ∑ ν ∈ F c h12 χ, ν.1 ⟨(b.1.1 : G), hbH0⟩ := by
    calc
      (∑ ν ∈ BOf c h12 χ, if ν ∈ F c h12 χ then ν.1 ⟨(b.1.1 : G), hbH0⟩ else 0)
          = ∑ ν ∈ (BOf c h12 χ).filter (fun ν : Irr (↥c.H0) => ν ∈ F c h12 χ),
              ν.1 ⟨(b.1.1 : G), hbH0⟩ := by
              rw [Finset.sum_filter]
      _ = ∑ ν ∈ F c h12 χ, ν.1 ⟨(b.1.1 : G), hbH0⟩ := by rw [hfilter]
  have hFpair : F c h12 χ = ({ν₁, ν₂} : Finset (Irr (↥c.H0))) := by
    have hsub : ({ν₁, ν₂} : Finset (Irr (↥c.H0))) ⊆ F c h12 χ := by
      intro ν hν
      rw [Finset.mem_insert, Finset.mem_singleton] at hν
      rcases hν with hν | hν
      · simpa [hν] using hν₁F
      · simpa [hν] using hν₂F
    have hcard2 : ({ν₁, ν₂} : Finset (Irr (↥c.H0))).card = 2 := Finset.card_pair hν₁ν₂
    have hle : (F c h12 χ).card ≤ ({ν₁, ν₂} : Finset (Irr (↥c.H0))).card := by
      rw [hcard2, hFcard]
    exact (Finset.eq_of_subset_of_card_le hsub hle).symm
  have hsum3 : (∑ ν ∈ F c h12 χ, ν.1 ⟨(b.1.1 : G), hbH0⟩) =
      ν₁.1 ⟨(b.1.1 : G), hbH0⟩ + ν₂.1 ⟨(b.1.1 : G), hbH0⟩ := by
    rw [hFpair]
    exact Finset.sum_pair hν₁ν₂
  have hres1' : ν₁.1 ⟨(b.1.1 : G), hbH0⟩ = α₁.1 b.1 := by
    have he := congrFun hres₁ b.1
    simpa [restrictU] using he
  have hres2' : ν₂.1 ⟨(b.1.1 : G), hbH0⟩ = α₂.1 b.1 := by
    have he := congrFun hres₂ b.1
    simpa [restrictU] using he
  have hsum : CongruentModTwo (∑ ν ∈ BOf c h12 χ, ν.1 ⟨(b.1.1 : G), hbH0⟩)
      (α₁.1 b.1 + α₂.1 b.1) := by
    have h1' := hsum1.trans (CongruentModTwo.of_eq (by rw [hsum2, hsum3]))
    have hEq : ν₁.1 ⟨(b.1.1 : G), hbH0⟩ + ν₂.1 ⟨(b.1.1 : G), hbH0⟩ = α₁.1 b.1 + α₂.1 b.1 := by
      rw [hres1', hres2']
    exact h1'.trans (CongruentModTwo.of_eq hEq)
  exact h24.trans hsum

private lemma odd_index_of_mem_B (c : Hyp11 G) {b : G} (hbB : b ∈ c.B) :
    Odd (Nat.card (ConjClasses.mk b).carrier) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSleC : (c.S : Subgroup G) ≤ Subgroup.centralizer ({b} : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hEq : h = b := by simpa using hh
    subst h
    have hfix := b_mem_fixedSubgroup' c hbB
    have hfix' : (⟨b, mem_U_of_mem_B' c hbB⟩ : ↥c.U) ∈
        fixedSubgroup (c.S : Subgroup G) c.U := hfix
    have hsmul := (mem_fixedSubgroup_iff (c.S : Subgroup G) c.U
      (⟨b, mem_U_of_mem_B' c hbB⟩ : ↥c.U)).1 hfix' (⟨a, ha⟩ : ↥(c.S : Subgroup G))
    have hcoef : (((⟨a, ha⟩ : ↥(c.S : Subgroup G)) •
        (⟨b, mem_U_of_mem_B' c hbB⟩ : ↥c.U) : ↥c.U) : G) = a * b * a⁻¹ := by
      rw [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
    have hEq' : a * b * a⁻¹ = b := by
      simpa [hcoef] using congrArg Subtype.val hsmul
    have hEq'' : a * b = b * a := by
      calc
        a * b = (a * b * a⁻¹) * a := by group
        _ = b * a := by rw [hEq']
    exact hEq''.symm
  have hdiv : (Subgroup.centralizer ({b} : Set G)).index ∣ (c.S : Subgroup G).index :=
    Subgroup.index_dvd_of_le hSleC
  have hSodd : Odd (c.S : Subgroup G).index := by
    have hnot : ¬ 2 ∣ (c.S : Subgroup G).index := c.S.not_dvd_index
    exact (Nat.not_even_iff_odd.mp (by simpa [even_iff_two_dvd] using hnot))
  have hCodd : Odd (Subgroup.centralizer ({b} : Set G)).index := Odd.of_dvd_nat hSodd hdiv
  rw [card_conjClass_eq_index b]
  exact hCodd

private lemma chi_congruent_zero_on_B (c : Hyp11 G) {χ : ClassFunction G} (hχ : IsPMIrr G χ)
    (hhalf : ∃ k : ℤ, (χ 1 : ℂ) / 2 = (k : ℂ)) {b : G} (hbB : b ∈ c.B) :
    CongruentModTwo (χ b) 0 := by
  have hodd := odd_index_of_mem_B c hbB
  have hint := pmIrr_chi_half_isIntegral_of_odd_index χ hχ b hhalf hodd
  exact chi_congruent_zero_of_half_isIntegral χ b hint

private lemma exists_not_congruent_zero_on_B (c : Hyp11 G) (h12 : Hyp12 c) (hSC : Section3Hyp c)
    {χ : ClassFunction G} (hχ : IsPMIrr G χ)
    (hBOfle : (BOf c h12 χ).card ≤ 3)
    {ν₁ ν₂ : Irr (↥c.H0)}
    (hν₁F : ν₁ ∈ F c h12 χ) (hν₂F : ν₂ ∈ F c h12 χ) (hν₁ν₂ : ν₁ ≠ ν₂)
    (hFcard : (F c h12 χ).card = 2) :
    ∃ b : ↥(fixedSubgroup (c.S : Subgroup G) c.U),
      ¬ CongruentModTwo (χ (b.1.1 : G)) 0 := by
  classical
  rcases fixed_full_orbit_restrict c h12 hSC (Finset.mem_filter.mp hν₁F).2.1
    (Finset.mem_filter.mp hν₁F).2.2 with ⟨α₁, hOrbitEq₁, hres₁, hfix₁, hdeg₁⟩
  rcases fixed_full_orbit_restrict c h12 hSC (Finset.mem_filter.mp hν₂F).2.1
    (Finset.mem_filter.mp hν₂F).2.2 with ⟨α₂, hOrbitEq₂, hres₂, hfix₂, hdeg₂⟩
  have hαne : α₁ ≠ α₂ := by
    intro hEq
    apply hν₁ν₂
    have hL : ν₁.1 ∈ orbit c.H0 c.U ν₂.1 := by
      simpa [hOrbitEq₁, hOrbitEq₂, hEq] using orbit_self_mem' c ν₁.1
    have hpair := BOf_orbit_pair_conj c h12 hχ (Finset.mem_filter.mp hν₁F).1
      (Finset.mem_filter.mp hν₂F).1 hL hν₁ν₂
    have hfix₁' : conjChar c.H0 (s_normalizes_H0 c h12) ν₁.1 = ν₁.1 := (Finset.mem_filter.mp hν₁F).2.1
    have hEq' : ν₂.1 = ν₁.1 := by
      rw [hfix₁'] at hpair
      exact hpair.symm
    exact Subtype.ext hEq'.symm
  have hcongB := chi_congruent_sum_two_on_B c h12 hSC hχ hBOfle hν₁F hν₂F hν₁ν₂ hFcard hres₁ hres₂
  have hcorr := glauberman_correspondence (S := ↥(c.S : Subgroup G)) (U := ↥c.U)
    c.S.isPGroup' (U_coprime_two c)
  rcases hcorr with ⟨e, he⟩
  let β₁ : IrrBG19 (↥(fixedSubgroup (c.S : Subgroup G) c.U)) := e ⟨α₁, hfix₁⟩
  let β₂ : IrrBG19 (↥(fixedSubgroup (c.S : Subgroup G) c.U)) := e ⟨α₂, hfix₂⟩
  have hβne : β₁ ≠ β₂ := by
    intro hEq
    apply hαne
    have h' : (⟨α₁, hfix₁⟩ : {α : IrrBG19 (↥c.U) // FixedIrr (c.S : Subgroup G) c.U α}) =
        ⟨α₂, hfix₂⟩ := by
      simpa [β₁, β₂] using congrArg e.symm hEq
    exact congrArg Subtype.val h'
  by_contra hne
  have hzero : ∀ b : ↥(fixedSubgroup (c.S : Subgroup G) c.U),
      CongruentModTwo (χ (b.1.1 : G)) 0 := by
    intro b
    by_contra hb
    exact hne ⟨b, hb⟩
  let I : Type u := {ν : Irr (↥c.H0) // ν ∈ F c h12 χ}
  let β : I → ClassFunction (↥(fixedSubgroup (c.S : Subgroup G) c.U)) := fun i =>
    if i.1 = ν₁ then β₁.1 else β₂.1
  let coef : I → ℂ := fun _ => 1
  have hFpair : F c h12 χ = ({ν₁, ν₂} : Finset (Irr (↥c.H0))) := by
    have hsub : ({ν₁, ν₂} : Finset (Irr (↥c.H0))) ⊆ F c h12 χ := by
      intro ν hν
      rw [Finset.mem_insert, Finset.mem_singleton] at hν
      rcases hν with hν | hν
      · simpa [hν] using hν₁F
      · simpa [hν] using hν₂F
    have hcard2 : ({ν₁, ν₂} : Finset (Irr (↥c.H0))).card = 2 := Finset.card_pair hν₁ν₂
    have hle : (F c h12 χ).card ≤ ({ν₁, ν₂} : Finset (Irr (↥c.H0))).card := by
      rw [hcard2, hFcard]
    exact (Finset.eq_of_subset_of_card_le hsub hle).symm
  have hβirr : ∀ i : I, IsIrreducibleCharacter (β i) := by
    intro i
    by_cases hi : i.1 = ν₁
    · simpa [β, hi] using β₁.2
    · have hmem : i.1 ∈ F c h12 χ := i.2
      have hmem' : i.1 ∈ ({ν₁, ν₂} : Finset (Irr (↥c.H0))) := by
        simpa [hFpair] using hmem
      rw [Finset.mem_insert, Finset.mem_singleton] at hmem'
      rcases hmem' with hmem | hmem
      · exact False.elim (hi hmem)
      · simpa [β, hi, hmem, hν₁ν₂.symm] using β₂.2
  have hβdist : Pairwise (fun i j : I => β i ≠ β j) := by
    intro i j hij
    by_cases hi : i.1 = ν₁
    · by_cases hj : j.1 = ν₁
      · have hij' : i = j := by
          apply Subtype.ext
          exact hi.trans hj.symm
        exact False.elim (hij hij')
      · have hmem : j.1 ∈ F c h12 χ := j.2
        have hmem' : j.1 ∈ ({ν₁, ν₂} : Finset (Irr (↥c.H0))) := by
          simpa [hFpair] using hmem
        rw [Finset.mem_insert, Finset.mem_singleton] at hmem'
        rcases hmem' with hmem | hmem
        · exact False.elim (hj hmem)
        · intro hEq
          apply hβne
          have hβi : β i = β₁.1 := by simp [β, hi]
          have hβj : β j = β₂.1 := by simp [β, hj, hmem, hν₁ν₂.symm]
          rw [hβi, hβj] at hEq
          exact Subtype.ext hEq
    · by_cases hj : j.1 = ν₁
      · have hmem : i.1 ∈ F c h12 χ := i.2
        have hmem' : i.1 ∈ ({ν₁, ν₂} : Finset (Irr (↥c.H0))) := by
          simpa [hFpair] using hmem
        rw [Finset.mem_insert, Finset.mem_singleton] at hmem'
        rcases hmem' with hmem | hmem
        · exact False.elim (hi hmem)
        · intro hEq
          apply hβne
          have hβi : β i = β₂.1 := by simp [β, hi, hmem, hν₁ν₂.symm]
          have hβj : β j = β₁.1 := by simp [β, hj]
          rw [hβi, hβj] at hEq
          exact Subtype.ext hEq.symm
      · have hij' : i = j := by
          apply Subtype.ext
          have hmem : i.1 ∈ F c h12 χ := i.2
          have hmem' : i.1 ∈ ({ν₁, ν₂} : Finset (Irr (↥c.H0))) := by
            simpa [hFpair] using hmem
          rw [Finset.mem_insert, Finset.mem_singleton] at hmem'
          rcases hmem' with hmem | hmem
          · exact False.elim (hi hmem)
          · have hmemj : j.1 ∈ F c h12 χ := j.2
            have hmemj' : j.1 ∈ ({ν₁, ν₂} : Finset (Irr (↥c.H0))) := by
              simpa [hFpair] using hmemj
            rw [Finset.mem_insert, Finset.mem_singleton] at hmemj'
            rcases hmemj' with hmemj | hmemj
            · exact False.elim (hj hmemj)
            · exact hmem.trans hmemj.symm
        exact False.elim (hij hij')
  have hsum : ∀ b : ↥(fixedSubgroup (c.S : Subgroup G) c.U),
      (∑ i : I, coef i * β i b) = β₁.1 b + β₂.1 b := by
    intro b
    have huniv : (Finset.univ : Finset I) = ({⟨ν₁, hν₁F⟩, ⟨ν₂, hν₂F⟩} : Finset I) := by
      ext i
      constructor
      · intro _
        have hmem : i.1 ∈ F c h12 χ := i.2
        have hmem' : i.1 ∈ ({ν₁, ν₂} : Finset (Irr (↥c.H0))) := by
          simpa [hFpair] using hmem
        rw [Finset.mem_insert, Finset.mem_singleton] at hmem'
        rcases hmem' with hmem | hmem
        · exact Finset.mem_insert.mpr (Or.inl (Subtype.ext hmem))
        · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (Subtype.ext hmem)))
      · intro h
        simp
    rw [huniv]
    rw [Finset.sum_pair (f := fun i : I => coef i * β i b)]
    · simp [coef, β, hν₁ν₂, hν₁ν₂.symm]
    · intro hEq
      exact hν₁ν₂ (by simpa using congrArg Subtype.val hEq)
  have h0 : ∀ b : ↥(fixedSubgroup (c.S : Subgroup G) c.U),
      CongruentModTwo (∑ i : I, coef i * β i b) 0 := by
    intro b
    have hχ0 := hzero b
    have hcongB' := hcongB b
    have hα0 : CongruentModTwo (α₁.1 b.1 + α₂.1 b.1) 0 := hcongB'.symm.trans hχ0
    have hβ1 := he ⟨α₁, hfix₁⟩ b
    have hβ2 := he ⟨α₂, hfix₂⟩ b
    have hαβ : CongruentModTwo (α₁.1 b.1 + α₂.1 b.1) (β₁.1 b + β₂.1 b) := hβ1.add hβ2
    have hβ0 : CongruentModTwo (β₁.1 b + β₂.1 b) 0 := hαβ.symm.trans hα0
    exact (CongruentModTwo.of_eq (hsum b)).trans hβ0
  have h1_8 := lemma_1_8 (B := ↥(fixedSubgroup (c.S : Subgroup G) c.U)) (B_coprime_two c)
    (I := I) (β := β) (c := coef) hβirr hβdist
    (hc := by intro i; exact isIntegral_one) h0 (i := ⟨ν₁, hν₁F⟩)
  have h1' : CongruentModTwo (1 : ℂ) 0 := by
    simpa [coef] using h1_8
  exact (CongruentModTwo.not_zero_of_odd_nat (n := 1) (by norm_num)) (by simpa using h1'.symm)

private lemma not_exactly_two_fixed (c : Hyp11 G) (h12 : Hyp12 c) (hSC : Section3Hyp c)
    {χ : ClassFunction G} (hχ : IsPMIrr G χ)
    (hBOfle : (BOf c h12 χ).card ≤ 3)
    (hFcard : (F c h12 χ).card = 2) : False := by
  classical
  rcases Finset.card_eq_two.mp hFcard with ⟨ν₁, ν₂, hν₁ν₂, hF⟩
  have mem₁ : ν₁ ∈ F c h12 χ := by
    rw [hF]
    simp
  have mem₂ : ν₂ ∈ F c h12 χ := by
    rw [hF]
    simp
  rcases fixed_full_orbit_restrict c h12 hSC (Finset.mem_filter.mp mem₁).2.1
    (Finset.mem_filter.mp mem₁).2.2 with ⟨α₁, hOrbitEq₁, hres₁, hfix₁, hdeg₁⟩
  rcases fixed_full_orbit_restrict c h12 hSC (Finset.mem_filter.mp mem₂).2.1
    (Finset.mem_filter.mp mem₂).2.2 with ⟨α₂, hOrbitEq₂, hres₂, hfix₂, hdeg₂⟩
  have hcongB := chi_congruent_sum_two_on_B c h12 hSC hχ hBOfle mem₁ mem₂ hν₁ν₂ hFcard hres₁ hres₂
  have hχ1int := pmIrr_one_int χ hχ
  have hcong1 : CongruentModTwo (χ 1) (α₁.1 (1 : ↥c.U) + α₂.1 (1 : ↥c.U)) := by
    have hb := hcongB (1 : ↥(fixedSubgroup (c.S : Subgroup G) c.U))
    simpa using hb
  have hhalf : ∃ k : ℤ, (χ 1 : ℂ) / 2 = (k : ℂ) :=
    chi_one_half_int_of_congruence χ hχ hχ1int hcong1 (irr_one_int α₁) (irr_one_int α₂)
      (odd_degree_one c α₁) (odd_degree_one c α₂)
  have hzero : ∀ b : ↥(fixedSubgroup (c.S : Subgroup G) c.U),
      CongruentModTwo (χ (b.1.1 : G)) 0 := by
    intro b
    have hbB : (b.1.1 : G) ∈ c.B := mem_B_of_fixed c b.2
    exact chi_congruent_zero_on_B c hχ hhalf hbB
  have hnotzero := exists_not_congruent_zero_on_B c h12 hSC hχ hBOfle mem₁ mem₂ hν₁ν₂ hFcard
  rcases hnotzero with ⟨b, hb⟩
  exact hb (hzero b)

private lemma not_three_fixed_of_S_ge_eight (c : Hyp11 G) (h12 : Hyp12 c)
    (hSC : Section3Hyp c) {χ : ClassFunction G} (hχ : IsPMIrr G χ)
    (hFcard : ((BOf c h12 χ).filter (fun ν : Irr (↥c.H0) =>
      conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1 ∧
        (orbit c.H0 c.U ν.1).card = (c.U.subgroupOf c.H0).index)).card = 3)
    (hSge : 8 ≤ Nat.card (c.S : Subgroup G)) : False := by
  classical
  let F := (BOf c h12 χ).filter (fun ν : Irr (↥c.H0) =>
      conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1 ∧
        (orbit c.H0 c.U ν.1).card = (c.U.subgroupOf c.H0).index)
  rcases Finset.card_eq_three.mp hFcard with ⟨ν₁, ν₂, ν₃, h12ne, h13ne, h23ne, hF⟩
  have mem₁ : ν₁ ∈ F := by
    change ν₁ ∈ (BOf c h12 χ).filter (fun ν : Irr (↥c.H0) =>
      conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1 ∧
        (orbit c.H0 c.U ν.1).card = (c.U.subgroupOf c.H0).index)
    rw [hF]
    simp
  have mem₂ : ν₂ ∈ F := by
    change ν₂ ∈ (BOf c h12 χ).filter (fun ν : Irr (↥c.H0) =>
      conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1 ∧
        (orbit c.H0 c.U ν.1).card = (c.U.subgroupOf c.H0).index)
    rw [hF]
    simp
  have mem₃ : ν₃ ∈ F := by
    change ν₃ ∈ (BOf c h12 χ).filter (fun ν : Irr (↥c.H0) =>
      conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1 ∧
        (orbit c.H0 c.U ν.1).card = (c.U.subgroupOf c.H0).index)
    rw [hF]
    simp
  have hν₁P := Finset.mem_filter.mp mem₁
  have hν₂P := Finset.mem_filter.mp mem₂
  have hν₃P := Finset.mem_filter.mp mem₃
  have hν₁B : ν₁ ∈ BOf c h12 χ := hν₁P.1
  have hν₂B : ν₂ ∈ BOf c h12 χ := hν₂P.1
  have hν₃B : ν₃ ∈ BOf c h12 χ := hν₃P.1
  have hν₁fix : conjChar c.H0 (s_normalizes_H0 c h12) ν₁.1 = ν₁.1 := hν₁P.2.1
  have hν₂fix : conjChar c.H0 (s_normalizes_H0 c h12) ν₂.1 = ν₂.1 := hν₂P.2.1
  have hν₃fix : conjChar c.H0 (s_normalizes_H0 c h12) ν₃.1 = ν₃.1 := hν₃P.2.1
  have horbit₁ : (orbit c.H0 c.U ν₁.1).card = (c.U.subgroupOf c.H0).index := hν₁P.2.2
  have horbit₂ : (orbit c.H0 c.U ν₂.1).card = (c.U.subgroupOf c.H0).index := hν₂P.2.2
  have horbit₃ : (orbit c.H0 c.U ν₃.1).card = (c.U.subgroupOf c.H0).index := hν₃P.2.2
  have hS0ge4 := S0_card_ge_four_of_S_ge_eight c hSge
  have hcard4₁ : 4 ≤ (orbit c.H0 c.U ν₁.1).card := by
    rw [horbit₁, U_index_eq_S0_card c h12]
    exact hS0ge4
  have hcard4₂ : 4 ≤ (orbit c.H0 c.U ν₂.1).card := by
    rw [horbit₂, U_index_eq_S0_card c h12]
    exact hS0ge4
  have hcard4₃ : 4 ≤ (orbit c.H0 c.U ν₃.1).card := by
    rw [horbit₃, U_index_eq_S0_card c h12]
    exact hS0ge4
  rcases exists_not_fixed_of_card_ge_four c h12 ν₁.2 hν₁fix hcard4₁ with ⟨μ₁, hμ₁L, hμ₁s⟩
  rcases exists_not_fixed_of_card_ge_four c h12 ν₂.2 hν₂fix hcard4₂ with ⟨μ₂, hμ₂L, hμ₂s⟩
  rcases exists_not_fixed_of_card_ge_four c h12 ν₃.2 hν₃fix hcard4₃ with ⟨μ₃, hμ₃L, hμ₃s⟩
  let δ₁ : ClassFunction G := inducedClassFunction c.H0 (μ₁ - ν₁.1)
  let δ₂ : ClassFunction G := inducedClassFunction c.H0 (μ₂ - ν₂.1)
  let δ₃ : ClassFunction G := inducedClassFunction c.H0 (μ₃ - ν₃.1)
  have hnorm₁ : normSq G δ₁ = 3 := by
    simpa [δ₁] using fixed_orbit_delta_norm c h12 hν₁fix hμ₁L hμ₁s
  have hnorm₂ : normSq G δ₂ = 3 := by
    simpa [δ₂] using fixed_orbit_delta_norm c h12 hν₂fix hμ₂L hμ₂s
  have hnorm₃ : normSq G δ₃ = 3 := by
    simpa [δ₃] using fixed_orbit_delta_norm c h12 hν₃fix hμ₃L hμ₃s
  have hdeg₁ : δ₁ 1 = 0 := by
    simpa [δ₁] using fixed_orbit_delta_degree_zero c h12 hμ₁L
  have hdeg₂ : δ₂ 1 = 0 := by
    simpa [δ₂] using fixed_orbit_delta_degree_zero c h12 hμ₂L
  have hdeg₃ : δ₃ 1 = 0 := by
    simpa [δ₃] using fixed_orbit_delta_degree_zero c h12 hμ₃L
  have hpair₁ := fixed_orbit_delta_pairing c h12 hχ hν₁B hν₁fix hμ₁L hμ₁s
  have hpair₂ := fixed_orbit_delta_pairing c h12 hχ hν₂B hν₂fix hμ₂L hμ₂s
  have hpair₃ := fixed_orbit_delta_pairing c h12 hχ hν₃B hν₃fix hμ₃L hμ₃s
  have horth₁₂ := fixed_orbit_delta_orthogonal c h12 hχ hν₁B hν₂B hν₁fix hν₂fix h12ne
    hμ₁L hμ₂L hμ₁s hμ₂s
  have horth₁₃ := fixed_orbit_delta_orthogonal c h12 hχ hν₁B hν₃B hν₁fix hν₃fix h13ne
    hμ₁L hμ₃L hμ₁s hμ₃s
  have horth₂₃ := fixed_orbit_delta_orthogonal c h12 hχ hν₂B hν₃B hν₂fix hν₃fix h23ne
    hμ₂L hμ₃L hμ₂s hμ₃s
  have horth₂₁ : scalarProduct G δ₂ δ₁ = 0 := by
    apply star_inj.mp
    rw [scalarProduct_star_comm']
    simpa [horth₁₂]
  have horth₃₁ : scalarProduct G δ₃ δ₁ = 0 := by
    apply star_inj.mp
    rw [scalarProduct_star_comm']
    simpa [horth₁₃]
  have horth₃₂ : scalarProduct G δ₃ δ₂ = 0 := by
    apply star_inj.mp
    rw [scalarProduct_star_comm']
    simpa [horth₂₃]
  let a₁ : ℂ := scalarProduct G χ δ₁
  let a₂ : ℂ := scalarProduct G χ δ₂
  let a₃ : ℂ := scalarProduct G χ δ₃
  have ha₁ : a₁ = 1 ∨ a₁ = -1 := by simpa [a₁, δ₁] using hpair₁
  have ha₂ : a₂ = 1 ∨ a₂ = -1 := by simpa [a₂, δ₂] using hpair₂
  have ha₃ : a₃ = 1 ∨ a₃ = -1 := by simpa [a₃, δ₃] using hpair₃
  let v : ClassFunction G := (a₁ / 3) • δ₁ + (a₂ / 3) • δ₂ + (a₃ / 3) • δ₃
  have hχnorm : scalarProduct G χ χ = 1 := scalarProduct_self_eq_one_of_isPMIrr hχ
  have hvv : scalarProduct G v v = 1 := by
    unfold v
    simp only [δ₁, δ₂, δ₃, scalarProduct_add_left, scalarProduct_add_right, scalarProduct_smul_left,
      scalarProduct_smul_right, horth₁₂, horth₁₃, horth₂₃,
      horth₂₁, horth₃₁, horth₃₂]
    have hself₁ : scalarProduct G δ₁ δ₁ = 3 := by simpa [normSq] using hnorm₁
    have hself₂ : scalarProduct G δ₂ δ₂ = 3 := by simpa [normSq] using hnorm₂
    have hself₃ : scalarProduct G δ₃ δ₃ = 3 := by simpa [normSq] using hnorm₃
    rw [hself₁, hself₂, hself₃]
    have ha1star : star a₁ = a₁ := by rcases ha₁ with h | h <;> simp [h]
    have ha2star : star a₂ = a₂ := by rcases ha₂ with h | h <;> simp [h]
    have ha3star : star a₃ = a₃ := by rcases ha₃ with h | h <;> simp [h]
    have ha1' : a₁ * star a₁ = 1 := by rcases ha₁ with h | h <;> simp [h]
    have ha2' : a₂ * star a₂ = 1 := by rcases ha₂ with h | h <;> simp [h]
    have ha3' : a₃ * star a₃ = 1 := by rcases ha₃ with h | h <;> simp [h]
    have ha1sq : a₁ * a₁ = 1 := by simpa [ha1star] using ha1'
    have ha2sq : a₂ * a₂ = 1 := by simpa [ha2star] using ha2'
    have ha3sq : a₃ * a₃ = 1 := by simpa [ha3star] using ha3'
    simp [ha1star, ha2star, ha3star]
    ring_nf
    simp [pow_two, ha1sq, ha2sq, ha3sq]
    norm_num
  have hχv : scalarProduct G χ v = 1 := by
    unfold v
    simp only [scalarProduct_add_right, scalarProduct_smul_right]
    rw [show scalarProduct G χ δ₁ = a₁ by rfl]
    rw [show scalarProduct G χ δ₂ = a₂ by rfl]
    rw [show scalarProduct G χ δ₃ = a₃ by rfl]
    have ha1star : star a₁ = a₁ := by rcases ha₁ with h | h <;> simp [h]
    have ha2star : star a₂ = a₂ := by rcases ha₂ with h | h <;> simp [h]
    have ha3star : star a₃ = a₃ := by rcases ha₃ with h | h <;> simp [h]
    have ha1s : a₁ * a₁ = 1 := by rcases ha₁ with h | h <;> simp [h]
    have ha2s : a₂ * a₂ = 1 := by rcases ha₂ with h | h <;> simp [h]
    have ha3s : a₃ * a₃ = 1 := by rcases ha₃ with h | h <;> simp [h]
    simp [ha1star, ha2star, ha3star, ha1s, ha2s, ha3s]
    ring_nf
    simp [pow_two, ha1s, ha2s, ha3s]
    norm_num
  have hvχ : scalarProduct G v χ = 1 := by
    have h' := scalarProduct_conj χ v
    rw [hχv] at h'
    norm_num at h'
    exact h'.symm
  have hd : scalarProduct G (χ - v) (χ - v) = 0 := by
    rw [scalarProduct_sub_left, scalarProduct_sub_right, scalarProduct_sub_right]
    rw [hχnorm, hvv, hχv, hvχ]
    norm_num
  have hχeq : χ = v := by
    have h0 : χ - v = 0 := (normSq_eq_zero_iff (χ - v)).1 (by simpa [normSq] using hd)
    exact sub_eq_zero.mp h0
  have hχ1 : χ 1 = 0 := by
    have hc := congrFun hχeq 1
    rw [hc]
    unfold v
    simp [δ₁, δ₂, δ₃, hdeg₁, hdeg₂, hdeg₃]
  exact chi_one_ne_zero_of_isPMIrr hχ hχ1

/-- Lemma 3.3: if `B(χ)` contains two characters `ν` with `ν^s = ν` and
`|Λν| = m`, then `B(χ)` consists of three such characters, and `S` has
order `4`. -/
public theorem lemma_3_3 (c : Hyp11 G) (h12 : Hyp12 c) (hSC : Section3Hyp c)
    {χ : ClassFunction G} (hχ : IsPMIrr G χ)
    (h2 : ∃ ν1 ν2 : Irr (↥c.H0),
      ν1 ∈ BOf c h12 χ ∧ ν2 ∈ BOf c h12 χ ∧ ν1 ≠ ν2 ∧
        conjChar c.H0 (s_normalizes_H0 c h12) ν1.1 = ν1.1 ∧
        conjChar c.H0 (s_normalizes_H0 c h12) ν2.1 = ν2.1 ∧
        (orbit c.H0 c.U ν1.1).card = (c.U.subgroupOf c.H0).index ∧
        (orbit c.H0 c.U ν2.1).card = (c.U.subgroupOf c.H0).index) :
    ((BOf c h12 χ).filter (fun ν : Irr (↥c.H0) =>
      conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1 ∧
        (orbit c.H0 c.U ν.1).card = (c.U.subgroupOf c.H0).index)).card = 3 ∧
    Nat.card (↥(c.S : Subgroup G)) = 4 := by
  classical
  have hBOfle : (BOf c h12 χ).card ≤ 3 := theorem_3_2 c h12 hSC hχ
  change (F c h12 χ).card = 3 ∧ Nat.card (↥(c.S : Subgroup G)) = 4
  have hFle : (F c h12 χ).card ≤ 3 := by
    exact le_trans (Finset.card_le_card (Finset.filter_subset
      (fun ν : Irr (↥c.H0) => conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1 ∧
        (orbit c.H0 c.U ν.1).card = (c.U.subgroupOf c.H0).index) (BOf c h12 χ))) hBOfle
  rcases h2 with ⟨ν₁, ν₂, hν₁B, hν₂B, hν₁ν₂, hfix₁, hfix₂, horbit₁, horbit₂⟩
  have h2le : 2 ≤ (F c h12 χ).card := by
    have hsub : ({ν₁, ν₂} : Finset (Irr (↥c.H0))) ⊆ F c h12 χ := by
      intro ν hν
      rw [Finset.mem_insert, Finset.mem_singleton] at hν
      rcases hν with hν | hν
      · rw [hν]
        exact Finset.mem_filter.mpr ⟨hν₁B, hfix₁, horbit₁⟩
      · rw [hν]
        exact Finset.mem_filter.mpr ⟨hν₂B, hfix₂, horbit₂⟩
    have hcard2 : ({ν₁, ν₂} : Finset (Irr (↥c.H0))).card = 2 := Finset.card_pair hν₁ν₂
    rw [← hcard2]
    exact Finset.card_le_card hsub
  have hFcases : (F c h12 χ).card = 2 ∨ (F c h12 χ).card = 3 := by omega
  rcases hFcases with hFcard2 | hFcard3
  · exfalso
    exact not_exactly_two_fixed c h12 hSC hχ hBOfle hFcard2
  · constructor
    · exact hFcard3
    · by_contra hSne
      have hSge : 8 ≤ Nat.card (c.S : Subgroup G) := by
        have hS' : 2 * 2 ^ c.m ≠ 4 := by
          rwa [S_nat_card c] at hSne
        have hm2 : 2 ≤ c.m := by
          by_contra hm
          have hmle : c.m ≤ 1 := by omega
          have hpow : 2 ^ c.m ≤ 2 := pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) hmle
          have hsmall : 2 * 2 ^ c.m ≤ 4 := by nlinarith
          have hge : 4 ≤ 2 * 2 ^ c.m := by
            have hpow1 : 2 ≤ 2 ^ c.m := by
              have h1 : 2 ^ 1 ≤ 2 ^ c.m := pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) c.one_le_m
              simpa using h1
            nlinarith
          exact hS' (le_antisymm hsmall hge)
        have hpow8 : 8 ≤ 2 * 2 ^ c.m := by
          have hpowm : 4 ≤ 2 ^ c.m := pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) hm2
          nlinarith
        rw [S_nat_card c]
        exact hpow8
      have hFcard3' : ((BOf c h12 χ).filter (fun ν : Irr (↥c.H0) =>
        conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1 ∧
          (orbit c.H0 c.U ν.1).card = (c.U.subgroupOf c.H0).index)).card = 3 := by
        simpa [F] using hFcard3
      exact not_three_fixed_of_S_ge_eight c h12 hSC hχ hFcard3' hSge

end Section3

end CFSG.BenderGlauberman
