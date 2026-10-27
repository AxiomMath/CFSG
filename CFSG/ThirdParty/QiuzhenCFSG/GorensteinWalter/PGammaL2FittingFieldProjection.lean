module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2DihedralProjection
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Center
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The Fitting subgroup of a `PΓL₂(K)`-subgroup containing the canonical `PSL₂(K)` layer

This is the generic semilinear core of the PSL₂ branch of Bender's
Fact 1.10(ii) (`refs/bender-dihedral-sylow.tex`):  every normal nilpotent
(odd) subgroup of a subgroup `A ≤ PΓL₂(K)` containing the canonical
`PSL₂(K)` layer has trivial field projection, hence its induced action on
`PSL₂(K)` is inner.

The proof is the full normal/Fitting package, not a Sylow-centralization
shortcut:

1. `F(A)` is normal in `A` and nilpotent.
2. `F(A) ∩ PSL₂(K)` is a normal nilpotent subgroup of the simple layer, hence
   trivial.
3. The commutator `[F(A), PSL₂(K)]` lies in `F(A) ∩ PSL₂(K)`, hence is
   trivial, so `F(A)` centralizes the layer.
4. The canonical layer is self-centralizing in `PΓL₂(K)`
   (`pGammaL2_pslRange_centralizer_eq_bot`), so `F(A) = 1`.

Any normal nilpotent `N ◁ A` therefore vanishes.  The exported theorem
records the two consequences the equation-(4) consumer needs:  trivial field
projection (the projective-linear kernel) and containment in the `PSL₂(K)`
layer (whose elements induce inner automorphisms).
-/

noncomputable section

namespace CFSG.GorensteinWalter

open Matrix
open scoped MatrixGroups

universe u

/-- `L` normalizes `N` when `N` is normal in `L`. -/
private theorem le_normalizer_of_isNormalIn_local
    {G : Type u} [Group G]
    {L N : Subgroup G} (hN : IsNormalIn N L) :
    L ≤ Subgroup.normalizer (N : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact hN.2 x hx y hy
  · intro hy
    have hxinv : x⁻¹ ∈ L := L.inv_mem hx
    have h := hN.2 x⁻¹ hxinv (x * y * x⁻¹) hy
    simpa [mul_assoc] using h

/-- The Fitting subgroup of a subgroup is normal in that subgroup. -/
private theorem fittingSubgroupOf_isNormalIn_local
    {G : Type u} [Group G] (A : Subgroup G) :
    IsNormalIn (fittingSubgroupOf (G := G) A) A := by
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases (Subgroup.mem_map).1 hx with ⟨f, _hf, hfx⟩
    rw [← hfx]
    change (f : G) ∈ A
    simp
  · intro h hh k hk
    rcases (Subgroup.mem_map).1 hk with ⟨f, hf, hfk⟩
    rw [← hfk]
    have hconj : (⟨h, hh⟩ : ↥A) * f * (⟨h, hh⟩ : ↥A)⁻¹ ∈ fittingSubgroup (↥A) := by
      exact (fittingSubgroup_normal (G := ↥A)).conj_mem (n := f) hf (g := ⟨h, hh⟩)
    refine Subgroup.mem_map.mpr ⟨(⟨h, hh⟩ : ↥A) * f * (⟨h, hh⟩ : ↥A)⁻¹, hconj, ?_⟩
    rw [hfk]
    simp
    exact hfk

/-- The Fitting subgroup of a subgroup is nilpotent (as an ambient
subgroup). -/
private theorem fittingSubgroupOf_isNilpotent_local
    {G : Type u} [Group G] [Finite G] (H : Subgroup G) :
    Group.IsNilpotent (↥(fittingSubgroupOf H)) := by
  change Group.IsNilpotent (↥((fittingSubgroup (↥H)).map H.subtype))
  haveI : Group.IsNilpotent (fittingSubgroup (↥H)) := by infer_instance
  exact Group.nilpotent_of_mulEquiv
    (Subgroup.equivMapOfInjective (fittingSubgroup (↥H)) H.subtype H.subtype_injective)

/-- The Fitting subgroup of a subgroup of `PΓL₂(K)` containing the canonical
`PSL₂(K)` layer is trivial. -/
private theorem pGammaL2_fittingSubgroup_eq_bot_of_contains_psl
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (A : Subgroup (PGammaL2 K))
    (hPSL : pGammaL2PSLRange K ≤ A) :
    fittingSubgroupOf A = ⊥ := by
  classical
  letI : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  letI : Fintype K := Fintype.ofFinite K
  letI : Finite (K ≃+* K) :=
    Finite.of_injective (fun e : K ≃+* K => (e : K → K)) (by
      intro e f hef
      ext x
      exact congrFun hef x)
  letI : Finite (PGammaL2 K) :=
    Finite.of_injective
      (fun x : PGammaL2 K => (x.left, x.right)) (by
        intro x y hxy
        exact SemidirectProduct.ext
          (congrArg Prod.fst hxy) (congrArg Prod.snd hxy))
  let F : Subgroup (PGammaL2 K) := fittingSubgroupOf A
  let L : Subgroup (PGammaL2 K) := pGammaL2PSLRange K
  letI : L.Normal := pGammaL2PSLRange_normal K hK hcard
  have hFnormA : IsNormalIn F A := fittingSubgroupOf_isNormalIn_local A
  have hFnil : Group.IsNilpotent (↥F) := fittingSubgroupOf_isNilpotent_local A
  have hFleA : F ≤ A := hFnormA.1
  -- `F ∩ L = ⊥`: a normal nilpotent subgroup of the simple layer is trivial
  have hFL_bot : F ⊓ L = ⊥ := by
    apply le_antisymm
    · intro x hx
      let K0 : Subgroup (PGammaL2 K) := F ⊓ L
      have hK0leF : K0 ≤ F := inf_le_left
      have hK0leL : K0 ≤ L := inf_le_right
      have hK0nil : Group.IsNilpotent (↥K0) := by
        haveI : Group.IsNilpotent (↥F) := hFnil
        exact Group.nilpotent_of_mulEquiv (G := K0.subgroupOf F) (G' := ↥K0)
          (Subgroup.subgroupOfEquivOfLe hK0leF)
      have hK0normL : IsNormalIn K0 L := by
        refine ⟨hK0leL, ?_⟩
        intro l hl y hy
        refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · exact hFnormA.2 l (hPSL hl) y hy.1
        · exact L.mul_mem (L.mul_mem hl hy.2) (L.inv_mem hl)
      letI : (K0.subgroupOf L).Normal :=
        Subgroup.normal_subgroupOf_of_le_normalizer (H := L) (N := K0)
          (le_normalizer_of_isNormalIn_local hK0normL)
      have hcard4 : 4 ≤ Nat.card K := by omega
      letI : IsSimpleGroup (PSL2 K) :=
        Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hcard4
      let eL : PSL2 K ≃* L := pGammaL2PSLRangeEquiv K
      letI : IsSimpleGroup L :=
        (MulEquiv.isSimpleGroup_congr eL).mp
          (Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hcard4)
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K0.subgroupOf L) with
        hK0bot | hK0top
      · have hxK0 : x ∈ K0 := hx
        let xL : L := ⟨x, hK0leL hxK0⟩
        have hxK0L : xL ∈ K0.subgroupOf L := Subgroup.mem_subgroupOf.mpr hxK0
        rw [hK0bot] at hxK0L
        have hx1 : x = 1 := by
          have hxL1 : xL = 1 := Subgroup.mem_bot.mp hxK0L
          simpa [xL] using congrArg (fun z : L => (z : PGammaL2 K)) hxL1
        exact Subgroup.mem_bot.mpr hx1
      · have hLleF : L ≤ F := by
          intro y hy
          have hyK0' : (⟨y, hy⟩ : L) ∈ K0.subgroupOf L := by
            rw [hK0top]
            trivial
          have hyK0 : y ∈ K0 := Subgroup.mem_subgroupOf.mp hyK0'
          exact hyK0.1
        haveI : Group.IsNilpotent (↥L) := by
          haveI : Group.IsNilpotent (↥F) := hFnil
          exact Group.nilpotent_of_mulEquiv (G := L.subgroupOf F) (G' := ↥L)
            (Subgroup.subgroupOfEquivOfLe hLleF)
        have hLnilPSL : Group.IsNilpotent (PSL2 K) :=
          Group.nilpotent_of_mulEquiv (G := ↥L) (G' := PSL2 K) eL.symm
        have hPSLne : ¬ Group.IsNilpotent (PSL2 K) := by
          intro hnil
          letI : Group.IsNilpotent (PSL2 K) := hnil
          have hne : Subgroup.center (PSL2 K) ≠ ⊥ :=
            Group.IsNilpotent.center_ne_bot (PSL2 K)
          exact hne (psl2_center_eq_bot K)
        exact False.elim (hPSLne hLnilPSL)
    · exact bot_le
  -- `[F, L] ≤ F ⊓ L`
  have hFL : ⁅F, L⁆ ≤ F ⊓ L := by
    rw [Subgroup.commutator_le]
    intro f hf l hl
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have hlf : l * f⁻¹ * l⁻¹ ∈ F := hFnormA.2 l (hPSL hl) (f⁻¹) (F.inv_mem hf)
      convert F.mul_mem hf hlf using 1
      group
    · exact L.mul_mem ((inferInstance : L.Normal).conj_mem l hl f) (L.inv_mem hl)
  have hFLbot : ⁅F, L⁆ = ⊥ := by
    apply le_antisymm
    · intro x hx
      have hxFL : x ∈ F ⊓ L := hFL hx
      rw [hFL_bot] at hxFL
      exact hxFL
    · exact bot_le
  -- `F ≤ C_{PΓL₂(K)}(L) = ⊥`
  have hFleC : F ≤ Subgroup.centralizer (L : Set (PGammaL2 K)) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := F) (H₂ := L)).1 hFLbot
  have hCbot : Subgroup.centralizer (L : Set (PGammaL2 K)) = ⊥ := by
    simpa [L] using pGammaL2_pslRange_centralizer_eq_bot K hK hcard
  apply le_antisymm
  · intro x hx
    have hx1 : x ∈ Subgroup.centralizer (L : Set (PGammaL2 K)) := hFleC hx
    rw [hCbot] at hx1
    exact hx1
  · exact bot_le

/-- A normal nilpotent subgroup of a subgroup `A ≤ PΓL₂(K)` containing the
canonical `PSL₂(K)` layer has trivial field projection (it lies in the
projective-linear kernel of `A`) and lies in the `PSL₂(K)` layer itself, so
its induced action on `PSL₂(K)` is inner.  The odd-order hypothesis of the
source is not needed: the Fitting argument forces the subgroup to be
trivial. -/
public theorem pGammaL2_normal_nilpotent_odd_subgroup_fieldProjection_trivial
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (A : Subgroup (PGammaL2 K))
    (hPSL : pGammaL2PSLRange K ≤ A)
    (N : Subgroup A) [N.Normal]
    (hNnil : Group.IsNilpotent N) :
    N ≤ pGammaL2LinearKernel K A ∧ N ≤ (pGammaL2PSLRange K).subgroupOf A := by
  classical
  letI : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  letI : Fintype K := Fintype.ofFinite K
  letI : Finite (K ≃+* K) :=
    Finite.of_injective (fun e : K ≃+* K => (e : K → K)) (by
      intro e f hef
      ext x
      exact congrFun hef x)
  letI : Finite (PGammaL2 K) :=
    Finite.of_injective
      (fun x : PGammaL2 K => (x.left, x.right)) (by
        intro x y hxy
        exact SemidirectProduct.ext
          (congrArg Prod.fst hxy) (congrArg Prod.snd hxy))
  let N' : Subgroup (PGammaL2 K) := N.map A.subtype
  have hN'leA : N' ≤ A := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨n, _hn, rfl⟩
    exact n.2
  have hN'normal : IsNormalIn N' A := by
    refine ⟨hN'leA, ?_⟩
    intro a ha x hx
    rcases Subgroup.mem_map.mp hx with ⟨n, hn, rfl⟩
    refine Subgroup.mem_map.mpr ⟨(⟨a, ha⟩ : A) * n * (⟨a, ha⟩ : A)⁻¹, ?_, rfl⟩
    exact (inferInstance : N.Normal).conj_mem n hn ⟨a, ha⟩
  have hN'nil : Group.IsNilpotent (↥N') := by
    let e : N ≃* N' := Subgroup.equivMapOfInjective N A.subtype A.subtype_injective
    haveI : Group.IsNilpotent N := hNnil
    exact Group.nilpotent_of_mulEquiv (G := N) (G' := N') e
  -- a normal nilpotent subgroup of `A` lies in `F(A)`
  have hN'leF : N' ≤ fittingSubgroupOf A := by
    let N'' : Subgroup (↥A) := N'.subgroupOf A
    have hN''normal : N''.Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer (H := A) (N := N')
        (le_normalizer_of_isNormalIn_local hN'normal)
    have hN''nil : Group.IsNilpotent N'' := by
      haveI : Group.IsNilpotent N' := hN'nil
      exact Group.nilpotent_of_mulEquiv (G := N') (G' := N'')
        (Subgroup.subgroupOfEquivOfLe hN'leA).symm
    have hle : N'' ≤ fittingSubgroup (↥A) := le_sSup ⟨hN''normal, hN''nil⟩
    have hmap : N''.map A.subtype ≤ (fittingSubgroup (↥A)).map A.subtype :=
      Subgroup.map_mono (f := A.subtype) hle
    have hmapN : N''.map A.subtype = N' := Subgroup.map_subgroupOf_eq_of_le hN'leA
    have hmapF : (fittingSubgroup (↥A)).map A.subtype = fittingSubgroupOf A := rfl
    simpa [hmapN, hmapF] using hmap
  -- `F(A) = ⊥`, so `N' = ⊥` and `N = ⊥`
  have hFbot : fittingSubgroupOf A = ⊥ :=
    pGammaL2_fittingSubgroup_eq_bot_of_contains_psl K hK hcard A hPSL
  have hN'bot : N' = ⊥ := by
    apply le_antisymm
    · intro x hx
      have hxF : x ∈ fittingSubgroupOf A := hN'leF hx
      rw [hFbot] at hxF
      exact hxF
    · exact bot_le
  have hNbot : N = ⊥ := by
    apply le_antisymm
    · intro x hx
      have hxN' : (x : PGammaL2 K) ∈ N' := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
      rw [hN'bot] at hxN'
      exact Subtype.ext (Subgroup.mem_bot.mp hxN')
    · exact bot_le
  constructor
  · rw [hNbot]
    exact bot_le
  · rw [hNbot]
    exact bot_le

end CFSG.GorensteinWalter
