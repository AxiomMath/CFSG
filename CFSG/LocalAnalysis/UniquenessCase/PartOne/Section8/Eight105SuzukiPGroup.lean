module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105SuzukiRepFour
public import CFSG.RankThree.PartTwo.Sec20.Item20Res11ProofPGroup
import CFSG.RankThree.PartOne.S9.MinTwoAction.FixedRankBridge

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.SuzukiL2

open CFSG Subgroup
open scoped MatrixGroups IsMulCommutative


theorem rep_zmod_eq_one {K : Type} [Group K] [Finite K] [Group.IsPerfect K] {m : ℕ}
    (hL : UC22.IsL2 (K ⧸ CFSG.pCore 2 K) m) (hm : 4 ≤ m) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {W : Type*} [AddCommGroup W] [Module (ZMod p) W] [FiniteDimensional (ZMod p) W]
    (hW : Module.finrank (ZMod p) W ≤ 4) (ρ : Representation (ZMod p) K W) : ρ = 1 := by
  classical
  let n := Module.finrank (ZMod p) W
  let b := Module.finBasisOfFinrankEq (ZMod p) W (rfl : Module.finrank (ZMod p) W = n)
  let Lp := AlgebraicClosure (ZMod p)
  let eM : Module.End (ZMod p) W ≃ₐ[ZMod p] Matrix (Fin n) (Fin n) (ZMod p) :=
    LinearMap.toMatrixAlgEquiv b
  let Φ : Matrix (Fin n) (Fin n) (ZMod p) →* Module.End Lp (Fin n → Lp) :=
    (Matrix.toLinAlgEquiv' (R := Lp) (n := Fin n)).toAlgHom.toRingHom.toMonoidHom.comp
      (algebraMap (ZMod p) Lp).mapMatrix.toMonoidHom
  have hΦ : Function.Injective Φ := by
    intro x y hxy
    have h1 := Matrix.toLinAlgEquiv'.injective hxy
    exact Matrix.map_injective (algebraMap (ZMod p) Lp).injective h1
  let R : Representation Lp K (Fin n → Lp) := Φ.comp (eM.toMonoidHom.comp ρ)
  have h2 : (2 : Lp) ≠ 0 := by
    intro h0
    have h1 : ((2 : ℕ) : Lp) = 0 := by exact_mod_cast h0
    have h3 : p ∣ 2 := (CharP.cast_eq_zero_iff Lp p 2).mp h1
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h3)
  have hR := rep_eq_one_of_finrank_le_four hL hm h2 (by rwa [Module.finrank_fin_fun]) R
  refine MonoidHom.ext fun k => ?_
  have h1 : Φ (eM (ρ k)) = Φ 1 := by
    rw [map_one]
    exact DFunLike.congr_fun hR k
  have h4 : eM (ρ k) = eM 1 := by rw [hΦ h1, map_one]
  exact eM.injective h4

theorem eq_one_of_pRank_le_three {K : Type} [Group K] [Finite K] [Group.IsPerfect K] {m : ℕ}
    (hL : UC22.IsL2 (K ⧸ CFSG.pCore 2 K) m) (hm : 4 ≤ m)
    {P : Type*} [Group P] [Finite P] {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hP : IsPGroup p P) (hrank : CFSG.pRank p P ≤ 3) (ρ : K →* MulAut P) : ρ = 1 := by
  classical
  by_cases hnt : Nontrivial P
  swap
  · rw [not_nontrivial_iff_subsingleton] at hnt
    ext k x
    exact Subsingleton.elim _ _
  obtain ⟨D, hDc, -, hDexp, hDcomm, -, hker⟩ :=
    SectionRank.Ccomm.supercritical_witness hp2 hP
  have hDp : IsPGroup p D := hP.to_subgroup D
  have hDexp' : ∀ x : D, x ^ p = 1 := fun x => Subtype.ext (by
    rw [Subgroup.coe_pow, hDexp x x.2, Subgroup.coe_one])
  have hDclass : commutator D ≤ Subgroup.center D :=
    CFSG.RankThree.PartTwo.Sec20.Res11.commutator_le_center_of_le_centralizer hDcomm
  have hDrank : CFSG.pRank p D ≤ 3 :=
    (RankThree.PartOne.FixedRank36.pRank_le_of_injective D.subtype D.subtype_injective).trans hrank
  have hQrank : CFSG.pRank p (D ⧸ commutator D) ≤ 4 :=
    (CFSG.RankThree.PartTwo.class_two_small_rank_order_bounds hDp hDexp' hDclass).2.2 hDrank
  have hΦ : frattini D = commutator D := CFSG.RankThree.PartTwo.frattini_eq_commutator hDp hDexp'
  have : Fact (IsPGroup p D) := ⟨hDp⟩
  have hWel : IsElementaryAbelian p (D ⧸ frattini D) :=
    CFSG.isElementaryAbelian_quotient_frattini (R := D) (p := p)
  have hWrank : CFSG.pRank p (D ⧸ frattini D) ≤ 4 :=
    (RankThree.PartOne.FixedRank36.pRank_le_of_injective
      (QuotientGroup.quotientMulEquivOfEq hΦ).toMonoidHom
      (QuotientGroup.quotientMulEquivOfEq hΦ).injective).trans hQrank
  have : Module.Finite (ZMod p) (Additive (D ⧸ frattini D)) := Module.Finite.of_finite
  have hdim : Module.finrank (ZMod p) (Additive (D ⧸ frattini D)) ≤ 4 := by
    have hcard : Nat.card (D ⧸ frattini D) =
        p ^ Module.finrank (ZMod p) (Additive (D ⧸ frattini D)) := by
      rw [← Nat.card_congr (Additive.toMul : Additive (D ⧸ frattini D) ≃ _),
        Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
    have hWexp : ∀ x : D ⧸ frattini D, x ^ p = 1 := fun x =>
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hWel.exponent_dvd_p x
    rw [← CFSG.RankThree.PartTwo.pRank_eq_of_isMulCommutative hp.out hWexp
      hWel.toIsMulCommutative hcard]
    exact hWrank
  set σ : K →* MulAut (D ⧸ frattini D) := (SectionRank.Ccomm.frattiniAction D).comp ρ with hσ
  set ρW := RankThree.PartOne.FixedRank36.elemRep p σ with hρW
  have hρW1 : ρW = 1 := rep_zmod_eq_one hL hm hp2 hdim ρW
  have hσ1 : σ = 1 := by
    ext k w
    have h := congrArg (fun f : Module.End (ZMod p) (Additive (D ⧸ frattini D)) =>
      Additive.toMul (f (Additive.ofMul w))) (DFunLike.congr_fun hρW1 k)
    simpa [hρW, RankThree.PartOne.FixedRank36.elemRep_apply] using h
  apply CFSG.RankThree.PartTwo.Sec20.Res11.eq_one_of_isPGroup_range ρ (p := p)
  refine hker.to_le ?_
  rintro _ ⟨k, rfl⟩
  rw [MonoidHom.mem_ker]
  exact DFunLike.congr_fun hσ1 k

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.SuzukiL2
