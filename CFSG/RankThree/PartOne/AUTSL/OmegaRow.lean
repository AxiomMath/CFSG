module

public import CFSG.RankThree.PartOne.AUTSL.OmegaCore
public import CFSG.RankThree.PartOne.AUTSL.OmegaModel
public import CFSG.RankThree.PartOne.AUTSL.OmegaFamily

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.ABGLocalTools StrongP CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData Matrix

namespace AUTSL

theorem coreStmt_omega (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    CoreStmt (matrixDerived (coordinateQuadMinus 4 K (by norm_num) b c)) := by
  intro S hS hsyl hne E B hEc hE5 hBE hBN hB α hαB hα3 hα1 x hxB
  have h14 : (1 : ℕ) ≤ 4 := by norm_num
  obtain ⟨S₀, hS₀⟩ := hsyl
  obtain ⟨𝒲, h𝒲ne, h𝒲, hJ⟩ := exists_stab_family_omega b c hirr
    (matrixDerived_eq_statedOmega (coordinateQuadMinus 4 K h14 b c)) S₀
    (Subgroup.normalizer (S : Set _)) hS₀ hne
  have hreg := regular_coordinateQuadMinus 4 K b c (le_refl 4) hirr
  exact omega_core (by simp) (coordinateQuadMinus 4 K h14 b c) hreg.1
    (fun T hT => omega_witt b c hirr T hT)
    (fun g hg v => (mem_matrixIsometries_iff _ g).1 (matrixDerived_le_isometries _ hg) v)
    (exists_matrix_form_omega b c hirr rfl) hS 𝒲 h𝒲ne (fun W hW => (h𝒲 W hW).1)
    (fun W hW => (h𝒲 W hW).2) hJ hEc hE5 hBE hBN hB α hαB hα3 hα1 x hxB

theorem kf1511BTEOm8m_holds : KF1511BTEOm8m := by
  refine kf1511BTEAt_of_core .POmegaMinus 4 ?_
  intro X _ _ f hmodel
  have hcl : StatedClassicalModel X .POmegaMinus 4 2 f := by
    rcases hmodel with ⟨-, h⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact h
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  obtain ⟨-, K, hF, hFin, hcard, b, c, hirr, ⟨e₀⟩⟩ := hcl
  have hchar : CharP K 2 := by
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨n, hp, hn⟩ := FiniteField.card K (ringChar K)
    have h1 : ringChar K ∣ 2 ^ f := by
      rw [← hcard, Nat.card_eq_fintype_card, hn]
      exact dvd_pow_self _ n.ne_zero
    have h3 : ringChar K = 2 :=
      (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h1)
    exact CharP.congr (ringChar K) h3
  have h14 : (1 : ℕ) ≤ 4 := by norm_num
  have hreg := regular_coordinateQuadMinus 4 K b c (le_refl 4) hirr
  have hQ : ∃ v, coordinateQuadMinus 4 K h14 b c v ≠ 0 :=
    exists_ne_zero_of_polar_nondegenerate (by norm_num) _ hreg.1
  let Ψ : X ≃* matrixDerived (coordinateQuadMinus 4 K h14 b c) :=
    (coordinateMinusWitnessEquiv K h14 b c e₀).trans (derivedProjEquiv _ hQ).symm
  exact transport_core Ψ (coreStmt_omega K b c hirr)

end AUTSL

end CFSG.RankThree.PartOne
