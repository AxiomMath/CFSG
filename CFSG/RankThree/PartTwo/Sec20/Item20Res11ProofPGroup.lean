module

public import CFSG.RankThree.PartTwo.Sec20.Item20Res11ProofKlein
public import CFSG.RankThree.PartTwo.Sec20.Item20Res11ProofSL2
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
public import CFSG.RankThree.PartTwo.ExponentPrimeSmallRank
import CFSG.RankThree.PartOne.S9.MinTwoAction.FixedRankBridge

public section

namespace CFSG.RankThree.PartTwo.Sec20.Res11

open CFSG
open CFSG.Assembly.RankThreeEven (projSL)
open scoped IsMulCommutative commutatorElement

theorem eq_one_of_isPGroup_range {K H : Type*} [Group K] [Finite K] [Group.IsPerfect K]
    [Group H] (f : K →* H) {p : ℕ} [Fact p.Prime] (hf : IsPGroup p f.range) : f = 1 := by
  by_contra hne
  obtain ⟨k, hk⟩ : ∃ k, f k ≠ 1 := by
    by_contra h
    push Not at h
    exact hne (MonoidHom.ext h)
  have : Finite f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have : Nontrivial f.range :=
    ⟨⟨⟨f k, k, rfl⟩, 1, fun h => hk (congrArg Subtype.val h)⟩⟩
  have : Group.IsPerfect f.range := Group.IsPerfect.range f
  have : Group.IsNilpotent f.range := hf.isNilpotent
  exact Group.IsPerfect.not_isNilpotent f.range this

theorem commutator_le_center_of_le_centralizer {P : Type*} [Group P] {D : Subgroup P}
    (h : ⁅D, (⊤ : Subgroup P)⁆ ≤ D ⊓ Subgroup.centralizer (D : Set P)) :
    commutator D ≤ Subgroup.center D := by
  rw [commutator_def, Subgroup.commutator_le]
  intro x _ y _
  rw [Subgroup.mem_center_iff]
  intro z
  apply Subtype.ext
  have hxy : ⁅(x : P), (y : P)⁆ ∈ Subgroup.centralizer (D : Set P) :=
    (h (Subgroup.commutator_mem_commutator x.2 (Subgroup.mem_top (y : P)))).2
  have hcoe : ((⁅x, y⁆ : D) : P) = ⁅(x : P), (y : P)⁆ := rfl
  rw [Subgroup.coe_mul, Subgroup.coe_mul, hcoe]
  exact Subgroup.mem_centralizer_iff.mp hxy z z.2

theorem eq_one_of_pRank_le_two {K : Type*} [Group K] [Finite K] [Group.IsPerfect K]
    (hK : (∃ n : ℕ, 3 ≤ n ∧ Nonempty (K ⧸ CFSG.pCore 2 K ≃* projSL 3 (GaloisField 2 n))) ∨
      (∃ n : ℕ, 3 ≤ n ∧ Nonempty (K ⧸ CFSG.pCore 2 K ≃* projSL 2 (GaloisField 2 n))))
    {P : Type*} [Group P] [Finite P] {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hP : IsPGroup p P) (hrank : CFSG.pRank p P ≤ 2) (ρ : K →* MulAut P) : ρ = 1 := by
  classical
  by_cases hnt : Nontrivial P
  swap
  ·
    rw [not_nontrivial_iff_subsingleton] at hnt
    ext k x
    exact Subsingleton.elim _ _
  obtain ⟨D, hDc, -, hDexp, hDcomm, -, hker⟩ :=
    SectionRank.Ccomm.supercritical_witness hp2 hP
  have hDp : IsPGroup p D := hP.to_subgroup D
  have hDexp' : ∀ x : D, x ^ p = 1 := fun x => Subtype.ext (by
    rw [Subgroup.coe_pow, hDexp x x.2, Subgroup.coe_one])
  have hDclass : commutator D ≤ Subgroup.center D := commutator_le_center_of_le_centralizer hDcomm
  have hDrank : CFSG.pRank p D ≤ 2 :=
    (RankThree.PartOne.FixedRank36.pRank_le_of_injective D.subtype D.subtype_injective).trans hrank
  have hQrank : CFSG.pRank p (D ⧸ commutator D) ≤ 2 :=
    (class_two_small_rank_order_bounds hDp hDexp' hDclass).1 hDrank
  have hΦ : frattini D = commutator D := frattini_eq_commutator hDp hDexp'
  have : Fact (IsPGroup p D) := ⟨hDp⟩
  have hWel : IsElementaryAbelian p (D ⧸ frattini D) :=
    CFSG.isElementaryAbelian_quotient_frattini (R := D) (p := p)
  have hWrank : CFSG.pRank p (D ⧸ frattini D) ≤ 2 :=
    (RankThree.PartOne.FixedRank36.pRank_le_of_injective
      (QuotientGroup.quotientMulEquivOfEq hΦ).toMonoidHom
      (QuotientGroup.quotientMulEquivOfEq hΦ).injective).trans hQrank
  have : Module.Finite (ZMod p) (Additive (D ⧸ frattini D)) := Module.Finite.of_finite
  have hdim : Module.finrank (ZMod p) (Additive (D ⧸ frattini D)) ≤ 2 := by
    have hcard : Nat.card (D ⧸ frattini D) =
        p ^ Module.finrank (ZMod p) (Additive (D ⧸ frattini D)) := by
      rw [← Nat.card_congr (Additive.toMul : Additive (D ⧸ frattini D) ≃ _),
        Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
    have hWexp : ∀ x : D ⧸ frattini D, x ^ p = 1 := fun x =>
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hWel.exponent_dvd_p x
    rw [← pRank_eq_of_isMulCommutative hp.out hWexp hWel.toIsMulCommutative hcard]
    exact hWrank
  set σ : K →* MulAut (D ⧸ frattini D) := (SectionRank.Ccomm.frattiniAction D).comp ρ with hσ
  set ρW := RankThree.PartOne.FixedRank36.elemRep p σ with hρW
  have h2 : (2 : ZMod p) ≠ 0 :=
    Ring.two_ne_zero (by rw [ZMod.ringChar_zmod_n]; exact hp2)
  have hρW1 : ∀ k, ρW k = 1 :=
    rep_eq_one_of_finrank_le_two h2 hdim ρW (fun h => exists_klein_of_kType hK _ h)
  have hσ1 : σ = 1 := by
    ext k w
    have h := congrArg (fun f : Module.End (ZMod p) (Additive (D ⧸ frattini D)) =>
      Additive.toMul (f (Additive.ofMul w))) (hρW1 k)
    simpa [hρW, RankThree.PartOne.FixedRank36.elemRep_apply] using h
  apply eq_one_of_isPGroup_range ρ (p := p)
  refine hker.to_le ?_
  rintro _ ⟨k, rfl⟩
  rw [MonoidHom.mem_ker]
  exact DFunLike.congr_fun hσ1 k

end CFSG.RankThree.PartTwo.Sec20.Res11
