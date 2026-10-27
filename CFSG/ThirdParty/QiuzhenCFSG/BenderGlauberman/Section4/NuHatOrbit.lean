module

import all CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section4.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section4.Basic

namespace CFSG
end CFSG
open CFSG

/-!
# Bender--Glauberman: Section 4 — the `N_G(S)`-orbit on `Irr(B)`

The `N_G(S)`-conjugacy orbit of a character `β ∈ Irr(B)` and its small
orbit API.  This is shared by Lemma 4.2 (orbit size `1` or `3`) and
Theorem 4.3 (the non-fixed `ν̂` case), so it lives in its own infra module
below both.
-/

noncomputable section

open scoped BigOperators
open scoped commutatorElement
open scoped Pointwise

namespace CFSG.BenderGlauberman

open GorensteinWalter
open Theory.Character

-- Local instances matching `Theory.Character`'s subgroup-sum convention.
attribute [local instance] Fintype.ofFinite
attribute [local instance] Classical.propDecidable

universe u

section Section4

variable {G : Type u} [Group G] [Fintype G]
variable (c : Hyp11 G)

/-- The `N_G(S)`-orbit of a character of `B`. -/
@[expose]
public def nuHatOrbit (h12 : Hyp12 c) (β : Irr (↥c.B)) : Finset (Irr (↥c.B)) :=
  Finset.univ.filter (fun β' : Irr (↥c.B) =>
    ∃ g : G, ∃ hg : g ∈ normalizerS c,
      conjIrrB c (B_conj_mem_of_normalizerS c hg) β = β')

/-- Pointwise value of a conjugated character of `B`. -/
public lemma conjIrrB_apply_local (c : Hyp11 G) {g : G}
    (hg : g ∈ normalizerS c) (β : Irr (↥c.B)) (b : ↥c.B) :
    (conjIrrB c (B_conj_mem_of_normalizerS c hg) β).1 b =
      β.1 ⟨g * (b : G) * g⁻¹, B_conj_mem_of_normalizerS c hg b⟩ :=
  rfl

/-- Conjugation by a product of normalizer elements composes. -/
public lemma conjIrrB_mul_local (c : Hyp11 G) {g h : G}
    (hg : g ∈ normalizerS c) (hh : h ∈ normalizerS c) (β : Irr (↥c.B)) :
    conjIrrB c (B_conj_mem_of_normalizerS c ((normalizerS c).mul_mem hg hh)) β =
      conjIrrB c (B_conj_mem_of_normalizerS c hh)
        (conjIrrB c (B_conj_mem_of_normalizerS c hg) β) := by
  apply Subtype.ext
  funext b
  dsimp [conjIrrB]
  simp [conjIrrB_apply_local]
  group

/-- Conjugation by `g⁻¹` undoes conjugation by `g`. -/
public lemma conjIrrB_inv_local (c : Hyp11 G) {g : G}
    (hg : g ∈ normalizerS c) (β : Irr (↥c.B)) :
    conjIrrB c (B_conj_mem_of_normalizerS c ((normalizerS c).inv_mem hg))
        (conjIrrB c (B_conj_mem_of_normalizerS c hg) β) = β := by
  apply Subtype.ext
  funext b
  dsimp [conjIrrB]
  simp [conjIrrB_apply_local]
  group

/-- Conjugation by `1` is the identity. -/
public lemma conjIrrB_one_local (c : Hyp11 G) (β : Irr (↥c.B)) :
    conjIrrB c (B_conj_mem_of_normalizerS c (normalizerS c).one_mem) β = β := by
  apply Subtype.ext
  funext b
  dsimp [conjIrrB]
  simp

/-- Orbits of `N_G(S)`-conjugate characters agree. -/
public lemma nuHatOrbit_eq_of_mem (c : Hyp11 G) (h12 : Hyp12 c)
    {β γ : Irr (↥c.B)}
    (hβγ : β ∈ nuHatOrbit c h12 γ) :
    nuHatOrbit c h12 β = nuHatOrbit c h12 γ := by
  classical
  rw [nuHatOrbit] at hβγ
  rcases (Finset.mem_filter.mp hβγ).2 with ⟨g, hg, hEq⟩
  ext δ
  constructor
  · intro hδ
    rw [nuHatOrbit] at hδ
    rcases (Finset.mem_filter.mp hδ).2 with ⟨k, hk, hEq'⟩
    rw [nuHatOrbit]
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ δ, ?_⟩
    refine ⟨g * k, (normalizerS c).mul_mem hg hk, ?_⟩
    calc
      conjIrrB c (B_conj_mem_of_normalizerS c ((normalizerS c).mul_mem hg hk)) γ
          = conjIrrB c (B_conj_mem_of_normalizerS c hk)
              (conjIrrB c (B_conj_mem_of_normalizerS c hg) γ) :=
              conjIrrB_mul_local c hg hk γ
      _ = conjIrrB c (B_conj_mem_of_normalizerS c hk) β := by
            rw [hEq]
      _ = δ := hEq'
  · intro hδ
    rw [nuHatOrbit] at hδ
    rcases (Finset.mem_filter.mp hδ).2 with ⟨k, hk, hEq'⟩
    rw [nuHatOrbit]
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ δ, ?_⟩
    refine ⟨g⁻¹ * k, (normalizerS c).mul_mem ((normalizerS c).inv_mem hg) hk, ?_⟩
    have hγ : conjIrrB c (B_conj_mem_of_normalizerS c ((normalizerS c).inv_mem hg)) β = γ := by
      rw [← hEq]
      exact conjIrrB_inv_local c hg γ
    calc
      conjIrrB c (B_conj_mem_of_normalizerS c
          ((normalizerS c).mul_mem ((normalizerS c).inv_mem hg) hk)) β
          = conjIrrB c (B_conj_mem_of_normalizerS c hk)
              (conjIrrB c (B_conj_mem_of_normalizerS c ((normalizerS c).inv_mem hg)) β) :=
              conjIrrB_mul_local c ((normalizerS c).inv_mem hg) hk β
      _ = conjIrrB c (B_conj_mem_of_normalizerS c hk) γ := by
            rw [hγ]
      _ = δ := hEq'

/-- A character lies in its own `N_G(S)`-orbit. -/
public lemma nuHatOrbit_self_mem (c : Hyp11 G) (h12 : Hyp12 c)
    (β : Irr (↥c.B)) :
    β ∈ nuHatOrbit c h12 β := by
  rw [nuHatOrbit]
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ β, 1, (normalizerS c).one_mem,
    conjIrrB_one_local c β⟩

end Section4

end CFSG.BenderGlauberman

end
