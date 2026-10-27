module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldSquare
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2FullSplitTorusFieldFixed
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DerivedSubgroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DeterminantSquare
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Inner split-torus subgroups fixed by a field automorphism

Inside the derived `PSL₂` layer, the split-torus parameter is a square.  For
an odd prime-order coefficient automorphism, square-class descent therefore
halves the full fixed split-torus bound.
-/

noncomputable section

namespace CFSG.GorensteinWalter

open Matrix
open scoped MatrixGroups

universe u

/-- A subgroup of the standard split torus that lies in the derived `PSL₂`
layer and is centralized by a pure odd-prime coefficient automorphism has
order dividing half the unit order of the fixed subfield. -/
public theorem pGammaL2_pureField_innerSplitTorus_fixedSubfield
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (sigma : K ≃+* K) (p : ℕ) (hp : p.Prime) (hpodd : Odd p)
    (hord : orderOf sigma = p)
    (A : Subgroup (PGL2 K))
    (hAtorus : A ≤ (pGammaL2FullSplitTorus K).range)
    (hAinner : A ≤ commutator (PGL2 K))
    (hcomm : ∀ x : PGL2 K, x ∈ A →
      Commute (SemidirectProduct.inr sigma : PGammaL2 K)
        (SemidirectProduct.inl x)) :
    let R := FixedPoints.subfield (Subgroup.zpowers sigma) K
    Nat.card A ∣ (Nat.card R - 1) / 2 := by
  classical
  let R := FixedPoints.subfield (Subgroup.zpowers sigma) K
  let B : Subgroup Kˣ := A.comap (pGammaL2FullSplitTorus K)
  have hBmap : B.map (pGammaL2FullSplitTorus K) = A := by
    apply le_antisymm
    · exact Subgroup.map_comap_le _ _
    · intro x hx
      rcases hAtorus hx with ⟨a, ha⟩
      exact Subgroup.mem_map.mpr ⟨a, by simpa [B, ha] using hx, ha⟩
  have hBcard : Nat.card B = Nat.card A := by
    rw [← hBmap]
    exact (Subgroup.card_map_of_injective (K := B)
      (pGammaL2FullSplitTorus_injective K)).symm
  have hfixed : ∀ a : Kˣ, a ∈ B → Units.map sigma.toRingHom a = a := by
    intro a ha
    apply pGammaL2FullSplitTorus_fixed K sigma a
    apply hcomm (pGammaL2FullSplitTorus K a)
    exact ha
  let g : B →* Rˣ :=
    { toFun := fun a => Units.mk0
        (⟨((a : Kˣ) : K), by
          change ((a : Kˣ) : K) ∈ MulAction.fixedPoints (Subgroup.zpowers sigma) K
          rw [MulAction.mem_fixedPoints]
          intro tau
          rcases Subgroup.mem_zpowers_iff.mp tau.2 with ⟨z, hz⟩
          have haFix : ((a : Kˣ) : K) ∈ MulAction.fixedBy K sigma := by
            change sigma ((a : Kˣ) : K) = ((a : Kˣ) : K)
            exact congrArg Units.val (hfixed (a : Kˣ) a.2)
          change (tau : K ≃+* K) ((a : Kˣ) : K) = ((a : Kˣ) : K)
          rw [← hz]
          exact MulAction.mem_fixedBy_zpow haFix z⟩)
        (by
          intro h0
          exact (a : Kˣ).ne_zero (congrArg Subtype.val h0))
      map_one' := by apply Units.ext; rfl
      map_mul' := by intro a b; apply Units.ext; rfl }
  have hginj : Function.Injective g := by
    intro a b hab
    apply Subtype.ext
    apply Units.ext
    exact congrArg (fun x : Rˣ => ((x : R) : K)) hab
  let Sq : Subgroup Rˣ := (powMonoidHom 2).range
  have hgSq : ∀ a : B, g a ∈ Sq := by
    intro a
    have haJ : pGammaL2FullSplitTorus K (a : Kˣ) ∈
        commutator (PGL2 K) := hAinner a.2
    have haPSL : pGammaL2FullSplitTorus K (a : Kˣ) ∈
        (Matrix.ProjectiveSpecialLinearGroup.toPGL
          (n := Fin 2) (R := K)).range := by
      rw [← pgl2_commutator_eq_psl2_range_of_card_gt_three K hK hcard]
      exact haJ
    have haSquareK : IsSquare (((a : Kˣ) : K)) := by
      have hm := (pgl2_mk_mem_psl2_range_iff_det_isSquare
        (pGammaL2FullSplitTorusGL K (a : Kˣ))).mp haPSL
      simpa [pGammaL2FullSplitTorusGL, Matrix.det_diagonal,
        Fin.prod_univ_two] using hm
    have haSquareR : IsSquare ((g a : Rˣ) : R) :=
      (fixedSubfield_isSquare_iff K sigma p hp hpodd hord (g a : R)).mp
        (by simpa [g] using haSquareK)
    rcases haSquareR with ⟨y, hy⟩
    have hy0 : y ≠ 0 := by
      intro hy0
      have hg0 : ((g a : Rˣ) : R) = 0 := by rw [hy, hy0]; simp
      exact (g a).ne_zero hg0
    let yu : Rˣ := Units.mk0 y hy0
    refine ⟨yu, ?_⟩
    apply Units.ext
    simpa [yu, pow_two] using hy.symm
  let gSq : B →* Sq := g.codRestrict Sq hgSq
  have hginjSq : Function.Injective gSq := by
    intro a b hab
    apply hginj
    exact congrArg Subtype.val hab
  have hdvd : Nat.card B ∣ Nat.card Sq :=
    Subgroup.card_dvd_of_injective gSq hginjSq
  have hRodd : Odd (Nat.card R) := by
    rcases hK with ⟨q, n, hq, hqodd, hn, hKcard⟩
    let : Fintype K := Fintype.ofFinite K
    let : Fact q.Prime := ⟨hq⟩
    have hcharK : CharP K q := charP_of_card_eq_prime_pow (by
      rw [← Nat.card_eq_fintype_card]
      exact hKcard)
    let : CharP K q := hcharK
    let : Fintype R := Fintype.ofFinite R
    let : CharP R q := Subfield.charP R q
    rcases FiniteField.card R q with ⟨nR, _hq, hRcard⟩
    rw [Nat.card_eq_fintype_card, hRcard]
    exact hqodd.pow
  have hSqcard : Nat.card Sq = (Nat.card R - 1) / 2 := by
    rw [show Sq = (powMonoidHom 2 : Rˣ →* Rˣ).range by rfl]
    rw [IsCyclic.card_powMonoidHom_range, Nat.card_units]
    have h2dvd : 2 ∣ Nat.card R - 1 := by
      rcases hRodd with ⟨k, hk⟩
      refine ⟨k, ?_⟩
      omega
    rw [Nat.gcd_eq_right_iff_dvd.mpr h2dvd]
  rw [hBcard, hSqcard] at hdvd
  exact hdvd

end CFSG.GorensteinWalter
