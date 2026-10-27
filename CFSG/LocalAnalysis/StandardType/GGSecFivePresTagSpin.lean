module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePresTagDefs
import CFSG.LieType.Universal.Spin.PlusCT
import CFSG.LieType.Universal.Spin.Generation
import CFSG.LieType.Universal.Spin.Twisted.Extras

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.LieType.Steinberg CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted

section RawHelpers

private theorem spin_neg_eq_self_of_two {K : Type*} [Field K] (h2 : (2 : K) = 0) (x : K) :
    -x = x := by
  rw [neg_eq_iff_add_eq_zero, ← two_mul, h2, zero_mul]

private theorem spin_units_neg_one_eq_one_of_two {K : Type*} [Field K] (h2 : (2 : K) = 0) :
    (-1 : Kˣ) = 1 :=
  Units.ext (by simpa only [Units.val_neg, Units.val_one] using spin_neg_eq_self_of_two h2 (1 : K))

private theorem spin_neg_planeOne_eq {K : Type*} [Field K] (h2 : (2 : K) = 0) :
    (-planeOne (K := K)) = planeOne (K := K) := by
  funext j
  exact spin_neg_eq_self_of_two h2 (planeOne (K := K) j)

private theorem spin_shortWeyl_mul_self {K : Type*} [Field K] {n : ℕ} {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (h2 : (2 : K) = 0) (i : Fin (n - 1)) :
    shortWeyl n hirr i * shortWeyl n hirr i = 1 := by
  have h : shortWeyl n hirr i ^ 2 = (shortTorusElt n hirr i (-planeOne (K := K)))⁻¹ := by
    rw [shortTorusElt, shortWeylElt_neg, ← shortWeyl, pow_two, mul_inv_rev, inv_inv]
  rw [← pow_two, h, spin_neg_planeOne_eq h2, shortTorusElt, shortWeyl, mul_inv_cancel, inv_one]

private theorem spin_minusWeyl_mul_self {K : Type*} [Field K] {n : ℕ} {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (h2 : (2 : K) = 0) (i : Fin (n - 1)) :
    minusWeyl n hirr i * minusWeyl n hirr i = 1 := by
  by_cases hi : i.val + 1 < n - 1
  · rw [minusWeyl_of_lt n hirr hi, HypFrame.longWeyl_mul_self,
      spin_units_neg_one_eq_one_of_two h2, map_one]
  · rw [minusWeyl_of_not_lt n hirr hi]
    exact spin_shortWeyl_mul_self hirr h2 i


theorem exists_weylLift_minusDatum {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hn : 4 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∃ ν : GGWeyl (minusDatum n hirr) →* spinGroup (quadMinus n K b c),
      GGWeylLift (minusDatum n hirr) ν ∧
        ∀ i : Fin (n - 1),
          ν ((coxeterMatrix (minusDatum n hirr).isFiniteType).simple i) = minusWeyl n hirr i := by
  have hct := minusDatum_isCTGroupDatum n hirr hn
  have hsq : ∀ i : Fin (n - 1), minusWeyl n hirr i * minusWeyl n hirr i = 1 :=
    spin_minusWeyl_mul_self hirr CharTwo.two_eq_zero
  refine ⟨ggWeylLiftOf hct hsq, ggWeylLiftOf_spec hct hsq, ?_⟩
  intro i
  exact ggWeylLiftOf_simple hct hsq i

end RawHelpers

section Tag

variable {G : Type} [Group G] [Finite G]

theorem ggTagFacts_POmegaPlus {n f : ℕ} (hadm : StatedLieAdmissible .POmegaPlus n 2 f)
    (hrank : 3 ≤ bnRank .POmegaPlus n) : GGTagFacts .POmegaPlus n f := by
  have hn : 3 ≤ n := by simpa only [bnRank] using hrank
  have h2 : (2 : GaloisField 2 f) = 0 := by
    exact_mod_cast CharP.cast_eq_zero (GaloisField 2 f) 2
  have hU : ggU .POmegaPlus n f =
      ⟨spinGroup (quadPlus n (GaloisField 2 f)), plusDatum n (GaloisField 2 f) hn⟩ := by
    simp only [ggU, lieUniversal, hn, ↓reduceDIte]
  refine ⟨?_, ?_⟩
  · rw [hU]
    show 2 ≤ (plusDatum n (GaloisField 2 f) hn).rank
    simp only [plusDatum]
    omega
  · rw [hU]
    show GGUniversalFacts (plusDatum n (GaloisField 2 f) hn)
    refine ggUniversalFacts_of_steinberg (D := plusDatum n (GaloisField 2 f) hn)
      (by show 0 < (plusDatum n (GaloisField 2 f) hn).rank; simp only [plusDatum]; omega)
      (plusDatum_isCTGroupDatum hn (plusDatum_iSup_eq_top n (GaloisField 2 f) hn))
      (plusDatum_steinbergExtras hn) ?_
    change ∀ i : Fin n, weylD (GaloisField 2 f) hn i * weylD (GaloisField 2 f) hn i = 1
    intro i
    rw [weylD_mul_self, spin_units_neg_one_eq_one_of_two h2, map_one]

theorem ggSecFivePres_of_psi_POmegaPlus {p : ℕ} {B : Subgroup G} {x : G} {L D J : Subgroup G}
    {n f : ℕ} (hadm : StatedLieAdmissible .POmegaPlus n 2 f) (hrank : 3 ≤ bnRank .POmegaPlus n)
    (ψ : (ggU .POmegaPlus n f).K →* G) (hker : ψ.ker ≤ Subgroup.center (ggU .POmegaPlus n f).K)
    (hrange : ψ.range = ggG0 p B x L D J) : GGSecFivePres p B x L D J .POmegaPlus n f :=
  ggSecFivePres_of_psi_of_tagFacts hadm hrank (ggTagFacts_POmegaPlus hadm hrank) ψ hker hrange

theorem ggTagFacts_POmegaMinus {n f : ℕ} (hadm : StatedLieAdmissible .POmegaMinus n 2 f)
    (hrank : 3 ≤ bnRank .POmegaMinus n) : GGTagFacts .POmegaMinus n f := by
  have hn : 4 ≤ n := hadm.2.2
  have h2 : (2 : GaloisField 2 f) = 0 := by
    exact_mod_cast CharP.cast_eq_zero (GaloisField 2 f) 2
  have hU : ggU .POmegaMinus n f =
      ⟨spinGroup (quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2),
        minusDatum n (minusCoeffs_irr 2 f)⟩ := rfl
  refine ⟨?_, ?_⟩
  · rw [hU]
    show 2 ≤ (minusDatum n (minusCoeffs_irr 2 f)).rank
    simp only [minusDatum]
    omega
  · rw [hU]
    show GGUniversalFacts (minusDatum n (minusCoeffs_irr 2 f))
    refine ggUniversalFacts_of_steinberg (D := minusDatum n (minusCoeffs_irr 2 f))
      (by show 0 < (minusDatum n (minusCoeffs_irr 2 f)).rank; simp only [minusDatum]; omega)
      (minusDatum_isCTGroupDatum n (minusCoeffs_irr 2 f) hn)
      (minusDatum_steinbergExtras n (minusCoeffs_irr 2 f)) ?_
    change ∀ i : Fin (n - 1),
      minusWeyl n (minusCoeffs_irr 2 f) i * minusWeyl n (minusCoeffs_irr 2 f) i = 1
    intro i
    exact spin_minusWeyl_mul_self (minusCoeffs_irr 2 f) h2 i

theorem ggSecFivePres_of_psi_POmegaMinus {p : ℕ} {B : Subgroup G} {x : G} {L D J : Subgroup G}
    {n f : ℕ} (hadm : StatedLieAdmissible .POmegaMinus n 2 f) (hrank : 3 ≤ bnRank .POmegaMinus n)
    (ψ : (ggU .POmegaMinus n f).K →* G) (hker : ψ.ker ≤ Subgroup.center (ggU .POmegaMinus n f).K)
    (hrange : ψ.range = ggG0 p B x L D J) : GGSecFivePres p B x L D J .POmegaMinus n f :=
  ggSecFivePres_of_psi_of_tagFacts hadm hrank (ggTagFacts_POmegaMinus hadm hrank) ψ hker hrange

end Tag

end CFSG.StandardType

end
