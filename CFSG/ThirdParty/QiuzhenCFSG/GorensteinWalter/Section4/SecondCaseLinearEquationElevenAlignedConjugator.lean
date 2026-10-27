module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseComponentData
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Section 4, equation (11): the aligned conjugator (source L846--847)

For a conjugate `X = P^g ≤ A` of the chosen order-`p` subgroup `P` with
`N_G(P) = M`, the normalizer `N_G(X) = M^g` carries only one class of
involutions.  Both the distinguished involution `t` and its conjugate
`t^g` are involutions of `M^g` (the first by hypothesis, the second
because `t ∈ M`), so the conjugating element `n ∈ M^g` fusing `t^g` back
to `t` adjusts the representative of `X`: the new conjugator
`g' = n · g` still satisfies `P^{g'} = X` (since `n` normalizes
`X = P^g`), and satisfies `t^{g'} = t`.

This is the formal content of the source sentence "As `N_G(X) = M^g` has
only one class of involutions, we can choose `g` subject to `t^g = t`."
The downstream aligned identities (`A^g = A`, the join identities, and the
normalizer/intersection chains) then all use the adjusted `g`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- The normalizer of a conjugate is the conjugate of the normalizer:
`N_G(P^g) = N_G(P)^g`. -/
private lemma normalizer_conjugate_eq
    {G : Type u} [Group G] {P : Subgroup G} (g : G) :
    Subgroup.normalizer ((conjugateSubgroup P g) : Set G) =
      conjugateSubgroup (Subgroup.normalizer (P : Set G)) g := by
  change Subgroup.normalizer ((P.map (MulAut.conj g).toMonoidHom) : Set G) =
    (Subgroup.normalizer (P : Set G)).map (MulAut.conj g).toMonoidHom
  exact (Subgroup.map_normalizer_eq_of_bijective P (MulAut.conj g).bijective).symm

/-- A conjugate of an involution is an involution. -/
private lemma isInvolution_conjugate
    {G : Type u} [Group G] {g x : G} (hx : IsInvolution x) :
    IsInvolution (g * x * g⁻¹) := by
  constructor
  · intro h1
    apply hx.1
    have hc := congrArg (fun y : G => g⁻¹ * y * g) h1
    simpa [mul_assoc] using hc
  · calc
      (g * x * g⁻¹) ^ 2 = g * (x ^ 2) * g⁻¹ := by
        simp only [pow_two]
        group
      _ = 1 := by rw [hx.2]; simp

/-- Conjugating `P` by `n·g` conjugates the conjugate `P^g` by `n`:
`P^{n·g} = (P^g)^n`. -/
private lemma conjugate_mul
    {G : Type u} [Group G] {P : Subgroup G} (n g : G) :
    conjugateSubgroup P (n * g) = conjugateSubgroup (conjugateSubgroup P g) n := by
  have hcomp : (MulAut.conj (n * g)).toMonoidHom =
      (MulAut.conj n).toMonoidHom.comp (MulAut.conj g).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  calc
    conjugateSubgroup P (n * g) = P.map (MulAut.conj (n * g)).toMonoidHom := rfl
    _ = P.map ((MulAut.conj n).toMonoidHom.comp (MulAut.conj g).toMonoidHom) := by
      rw [hcomp]
    _ = (P.map (MulAut.conj g).toMonoidHom).map (MulAut.conj n).toMonoidHom := by
      rw [Subgroup.map_map]
    _ = conjugateSubgroup (conjugateSubgroup P g) n := rfl

/-- The aligned conjugator: every conjugate `X = P^g` of the chosen order-`p`
subgroup admits a representative `g'` with `P^{g'} = X` and `t^{g'} = t`,
because `N_G(X) = M^g` has only one class of involutions (source L846--847).

The hypotheses are exactly the source's ingredients:

* `hNP` — `N_G(P) = M`;
* `hX` — `X = P^g`;
* `htMg` — `t ∈ M^g` (so that both `t` and `t^g` are involutions of
  `M^g`);
* `hclasses` — the unique involution class of `M^g`: any two involutions
  of `M^g` are conjugate inside `M^g`.
-/
public theorem secondCase_equation11_aligned_exists_conjugator_fixing_t
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (P X : Subgroup G) (g : G)
    (hNP : Subgroup.normalizer (P : Set G) = w.M)
    (hX : X = conjugateSubgroup P g)
    (htMg : c.t ∈ conjugateSubgroup w.M g)
    (hclasses : ∀ a b : G,
      a ∈ conjugateSubgroup w.M g → IsInvolution a →
      b ∈ conjugateSubgroup w.M g → IsInvolution b →
        ∃ n : G, n ∈ conjugateSubgroup w.M g ∧ n * a * n⁻¹ = b) :
    ∃ g' : G, conjugateSubgroup P g' = X ∧ g' * c.t * g'⁻¹ = c.t := by
  classical
  have htM : c.t ∈ w.M := (componentLayerOf_isNormalIn w.M).1 w.t_mem_componentLayer
  have htgM : g * c.t * g⁻¹ ∈ conjugateSubgroup w.M g := by
    exact Subgroup.mem_map.mpr ⟨c.t, htM, rfl⟩
  have htgI : IsInvolution (g * c.t * g⁻¹) := isInvolution_conjugate c.t_involution
  obtain ⟨n, hnMg, hnt⟩ := hclasses (g * c.t * g⁻¹) c.t htgM htgI htMg c.t_involution
  let g' : G := n * g
  refine ⟨g', ?_, ?_⟩
  · -- `P^{g'} = X`
    have hNX : Subgroup.normalizer (X : Set G) = conjugateSubgroup w.M g := by
      calc
        Subgroup.normalizer (X : Set G) =
            Subgroup.normalizer ((conjugateSubgroup P g) : Set G) := by rw [hX]
        _ = conjugateSubgroup (Subgroup.normalizer (P : Set G)) g :=
            normalizer_conjugate_eq g
        _ = conjugateSubgroup w.M g := by rw [hNP]
    have hnNX : n ∈ Subgroup.normalizer (X : Set G) := by
      rwa [hNX]
    calc
      conjugateSubgroup P g' = conjugateSubgroup (conjugateSubgroup P g) n := by
        simp [g', conjugate_mul]
      _ = conjugateSubgroup X n := by rw [hX]
      _ = X := by
        apply le_antisymm
        · intro x hx
          rcases Subgroup.mem_map.mp hx with ⟨y, hy, hxy⟩
          have hyn : n * y * n⁻¹ ∈ X :=
            (Subgroup.mem_normalizer_iff.mp hnNX y).1 hy
          have hxeq : x = n * y * n⁻¹ := by simpa [MulAut.conj_apply] using hxy.symm
          rwa [hxeq]
        · intro x hx
          have hback : n⁻¹ * x * n ∈ X :=
            (Subgroup.mem_normalizer_iff.mp hnNX (n⁻¹ * x * n)).2 (by
              have hx' : n * (n⁻¹ * x * n) * n⁻¹ = x := by group
              rwa [hx'])
          exact Subgroup.mem_map.mpr ⟨n⁻¹ * x * n, hback, by
            simp [MulAut.conj_apply, mul_assoc]⟩
  · -- `t^{g'} = t`
    calc
      g' * c.t * g'⁻¹ = n * (g * c.t * g⁻¹) * n⁻¹ := by
        simp [g', mul_assoc]
      _ = c.t := hnt

end CFSG.GorensteinWalter
