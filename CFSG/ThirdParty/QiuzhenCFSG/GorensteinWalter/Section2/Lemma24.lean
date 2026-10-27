module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.MinimalCounterexample
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.QdNotInvolvedOfDihedralSylowTwo
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma24ConjugatorOfQdNotInvolved

namespace CFSG
end CFSG
open CFSG

/-!
# Lemma 2.4: the common odd-`p`-group alternative forces `A = M`

The paper's Lemma 2.4 (Bender, p. 219) is the Glauberman ZJ application: if
`A ↝ M`, both are maximal, and `F*(A)`, `F*(M)` are `p`-groups for an odd
prime `p`, then `A = M`.

The proof combines the dihedral-Sylow obstruction to involvement of `Qd p`
with Glauberman's p-stability criterion, Theorems A and B, and the resulting
SD-subgroup conjugacy/normalizer transfer.

Once a conjugator `g` with `conjugateSubgroup A g = M` and `g ∈ A` is
supplied, the final equality is elementary: conjugating `A` by an element of
`A` gives `A` again.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- Conjugation of a subgroup by one of its own elements is the identity. -/
public theorem conjugateSubgroup_eq_self_of_mem
    {G : Type u} [Group G] (A : Subgroup G) (g : G) (hg : g ∈ A) :
    conjugateSubgroup A g = A := by
  apply le_antisymm
  · intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨a, ha, rfl⟩
    change g * a * g⁻¹ ∈ A
    exact A.mul_mem (A.mul_mem hg ha) (A.inv_mem hg)
  · intro a ha
    refine Subgroup.mem_map.mpr ⟨g⁻¹ * a * g, ?_, ?_⟩
    · exact A.mul_mem (A.mul_mem (A.inv_mem hg) ha) hg
    · change g * (g⁻¹ * a * g) * g⁻¹ = a
      group

/-- The Glauberman application in Lemma 2.4: `A` and `M` are conjugate by an
element of `A`. -/
public theorem lemma_2_4_glauberman_conjugator
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    {A M : Subgroup G} {p : ℕ}
    (hA : IsCoatom A) (hM : IsCoatom M)
    (hAM : NormalizerControlledBy A M)
    (hp : p.Prime) (hodd : Odd p)
    (hAp : IsPGroup p (generalizedFittingSubgroupOf A))
    (hMp : IsPGroup p (generalizedFittingSubgroupOf M)) :
    ∃ g : G, conjugateSubgroup A g = M ∧ g ∈ A := by
  let : Fact p.Prime := ⟨hp⟩
  have hpodd : p ≠ 2 := by
    rcases hodd with ⟨k, hk⟩
    omega
  exact lemma24_glauberman_conjugator_of_not_involved
    (minimalCounterexample_isSimple hmin) hA hM hAM hp hodd hAp hMp
    (qd_not_involved_of_hasDihedralSylowTwo hmin.1 hpodd)

/-- Lemma 2.4 (Bender p. 219): distinct common odd-`p`-group maximal
subgroups are impossible under `A ↝ M`. -/
public theorem lemma_2_4
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    {A M : Subgroup G} {p : ℕ}
    (hA : IsCoatom A) (hM : IsCoatom M)
    (hAM : NormalizerControlledBy A M)
    (hp : p.Prime) (hodd : Odd p)
    (hAp : IsPGroup p (generalizedFittingSubgroupOf A))
    (hMp : IsPGroup p (generalizedFittingSubgroupOf M)) :
    A = M := by
  rcases lemma_2_4_glauberman_conjugator hmin hA hM hAM hp hodd hAp hMp with
    ⟨g, hgM, hgA⟩
  calc
    A = conjugateSubgroup A g := (conjugateSubgroup_eq_self_of_mem A g hgA).symm
    _ = M := hgM

end CFSG.GorensteinWalter
