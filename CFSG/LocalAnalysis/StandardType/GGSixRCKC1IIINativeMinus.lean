module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeFAt
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIIUnitaryRecognition
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIIUnitaryOrthBlock
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIIUnitaryFour
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIINativeLinear
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpFPOmegaMinusFixed
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeF1POmegaMinus
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeLowPOmegaMinusTwo
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeFPOmegaMinusThree
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeOmegaFourMinusPOmegaMinus
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGCoKleinMinus
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGCoKleinPlus
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelSelfDualPOmegaMinus
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelSelfDualTwoPOmegaMinus
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelDualPairPOmegaMinus
import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerMinus
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockDegreeOneGFTwo
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpBlockFixed
import CFSG.LocalAnalysis.StandardType.TableC.OrthGram
public import CFSG.LocalAnalysis.StandardType.GGSixRCK1416Defs

public section

namespace CFSG.StandardType.RCKC1

open Matrix CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal
  CFSG.LieType.Universal.Unitary CFSG.StandardType CFSG.StandardType.RCKRP
  CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag StatedLieAdmissible)


theorem k2At_of_row_III_of_minus_modelID_small
    {X : Type} [Group X] [Finite X] {p m g : ℕ} {K J B₁ : Subgroup X} {d r : X}
    {V : Subgroup X}
    (hp : p.Prime) (hp2 : p ≠ 2) (hBab : IsElemAbelian p B₁) (hdB : d ∈ B₁)
    (hB1K : B₁ ≤ Subgroup.normalizer (K : Set X))
    (hg : 1 ≤ g) (φ : (ggU .POmegaMinus m g).K →* X) (hφr : φ.range = K)
    (hφk : φ.ker ≤ Subgroup.center (ggU .POmegaMinus m g).K)
    (hdiag : ∀ b ∈ B₁, GGPsiInnerDiag (ggU .POmegaMinus m g).D φ b)
    (hJcomp : IsComponentOf J (K ⊓ Subgroup.centralizer {d}))
    (hrow : GGSixRCKJRow .III J) (hJK : J ≤ K)
    (hFour : FourAt J V r) (hCore : CoreCommAt J V r) (hShort : ShortAt J r)
    (hm : m ≤ 3) : K2At K V r := by
  by_cases hm2 : m ≤ 2
  · rcases lt_or_eq_of_le hm2 with hm1 | rfl
    ·
      let Q := Spin.quadMinus m (GaloisField 2 g) (minusCoeffs 2 g).1 (minusCoeffs 2 g).2
      have hm0 : m - 1 = 0 := by omega
      have hcard : Fintype.card (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) = 2 := by
        rw [hm0]
        simp
      let e₂ : (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) ≃ Fin 2 :=
        Fintype.equivFinOfCardEq hcard
      let j₂ : (ggU .POmegaMinus m g).K →* GL (Fin 2) (GaloisField 2 g) :=
        (Units.mapEquiv (Matrix.reindexRingEquiv (GaloisField 2 g) e₂).toMulEquiv).toMonoidHom.comp
          (Spin.spinMatrix Q)
      have hinj : Function.Injective (Spin.spinMatrix Q) :=
        (MonoidHom.ker_eq_bot_iff _).mp
          (Spin.ker_spinMatrix_quadMinus_eq_bot (minusCoeffs_irr 2 g)
            (CharP.cast_eq_zero (GaloisField 2 g) 2))
      have hj₂ : Function.Injective j₂ :=
        (Units.mapEquiv (Matrix.reindexRingEquiv (GaloisField 2 g) e₂).toMulEquiv).injective.comp hinj
      have : Finite (ggU .POmegaMinus m g).K := Finite.of_injective j₂ hj₂
      have h3 : 3 ≤ 2 := three_le_of_row_III_of_matrix_range j₂ hj₂ φ
        (by rw [hφr]; exact hJK) hrow
      omega
    ·
      exact (ne_PSL_of_row_III_of_modelID hp hp2 (fun b hb => hBab.2 b hb) hB1K
        ⟨d, hdB, hJcomp⟩ hrow
        (rckClassicalModelIDAt_PSL_of_omegaMinus_two hg hB1K φ hφr hφk hdiag) rfl).elim
  ·
    have hm3 : m = 3 := by omega
    subst hm3
    have hPSU : RCKClassicalModelIDAt .PSU K B₁ :=
      rckClassicalModelIDAt_PSU_of_omegaMinus_three hg φ hφr hφk hdiag
    have hBlock : FixedSUBlockAt K J :=
      fixedSUBlockAt_of_unitary_modelID hp hp2 (fun b hb => hBab.2 b hb) hB1K hdB hPSU hJcomp hrow
    exact k2At_of_fixedSUBlockAt hBlock hJK hFour hCore hShort


theorem rowIII_minus_selfDual_rank_three
    {X : Type} [Group X] [Finite X] {n g : ℕ} {J : Subgroup X}
    (hn : 4 ≤ n) (hf : 1 ≤ g)
    (φ : (ggU .POmegaMinus n g).K →* X)
    (hφk : φ.ker ≤ Subgroup.center (ggU .POmegaMinus n g).K)
    (S : Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (GaloisField 2 g)))
    (hSU : ∀ s ∈ S, s ∈ (Spin.spinMatrix
      (Spin.quadMinus n (GaloisField 2 g) (minusCoeffs 2 g).1 (minusCoeffs 2 g).2)).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
      (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (GaloisField 2 g)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 g) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 g))
      (LinearMap.toMatrix₂' (GaloisField 2 g)
        (QuadraticMap.polarBilin
          (Spin.quadMinus n (GaloisField 2 g) (minusCoeffs 2 g).1 (minusCoeffs 2 g).2))) e = e)
    (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 g) (Units.val '' S)) e < 2)
    (hnm : ¬ (e.rank = 4 ∧ ∀ x y : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → GaloisField 2 g,
      e.mulVec x = x → e.mulVec y = y →
      Spin.quadMinus n (GaloisField 2 g) (minusCoeffs 2 g).1 (minusCoeffs 2 g).2 x = 0 →
      Spin.quadMinus n (GaloisField 2 g) (minusCoeffs 2 g).1 (minusCoeffs 2 g).2 y = 0 →
      QuadraticMap.polar
        (Spin.quadMinus n (GaloisField 2 g) (minusCoeffs 2 g).1 (minusCoeffs 2 g).2) x y = 0 →
      ¬ LinearIndependent (GaloisField 2 g) ![x, y]))
    {J' : Subgroup (ggU .POmegaMinus n g).K}
    (hJe : IsComponentOf J'
      ⁅(glBlockCentralizer (Spin.spinMatrix
          (Spin.quadMinus n (GaloisField 2 g) (minusCoeffs 2 g).1 (minusCoeffs 2 g).2)) S e :
          Subgroup (ggU .POmegaMinus n g).K),
        (glBlockCentralizer (Spin.spinMatrix
          (Spin.quadMinus n (GaloisField 2 g) (minusCoeffs 2 g).1 (minusCoeffs 2 g).2)) S e :
          Subgroup (ggU .POmegaMinus n g).K)⁆)
    (hJmap : J'.map φ = J) (hrow : GGSixRCKJRow .III J) :
    g = 1 ∧ LieModel (↥J ⧸ Subgroup.center ↥J) .PSU 4 2 1 ∧
      Module.finrank (GaloisField 2 g) (LinearMap.range (Matrix.toLin' e)) = 6 := by
  classical
  let Q := Spin.quadMinus n (GaloisField 2 g) (minusCoeffs 2 g).1 (minusCoeffs 2 g).2
  obtain ⟨t', m', ι, β₀, hshape, hlong, hcent, hrange, a₁, a₂, b₁, b₂, hQ, hb1, hb2,
    hb12, hsig, _hsig'⟩ :=
    exists_blockModel_selfDual_POmegaMinus_explicit n g hf S hSU hS hodd he hn hadj hdeg hnm hJe
  have mkNu : ∀ (t : StatedLieTag) (m : ℕ) (ι : (ggU t m g).K →* ↥(spinGroup Q)),
      (∀ y, ι y ∈ Subgroup.center ↥(spinGroup Q) → y ∈ Subgroup.center (ggU t m g).K) →
      ι.range = J' → ∃ ν : (ggU t m g).K →* X, ν.range = J ∧
        ν.ker ≤ Subgroup.center (ggU t m g).K := by
    intro t m ι hcentι hιr
    refine ⟨φ.comp ι, ?_, ?_⟩
    · calc (φ.comp ι).range = (ι.range).map φ := MonoidHom.range_comp φ ι
        _ = J'.map φ := by rw [hιr]
        _ = J := hJmap
    · intro y hy
      exact hcentι y (hφk hy)
  rcases hshape with ⟨htag, hm3, hdim2⟩ | ⟨ht, hm2, hdim4⟩
  · rcases htag with ht | ht
    ·
      subst ht
      by_cases hm'3 : m' = 3
      · subst hm'3
        obtain ⟨eP, heP⟩ := irgIsoCompat_omegaPlus_three (g := g) hf
        obtain ⟨γ, ιP, -, hrangeP, hcentP, -, -⟩ :=
          exists_model_of_irgIsoCompat (t' := .POmegaPlus) (m := 3) (g' := g)
            (t := .PSL) (n := 4) (g := g) (L := ↥(spinGroup Q)) (e := eP) heP ι hcent hlong
        obtain ⟨ν, hνr, hνk⟩ := mkNu .PSL 4 ιP hcentP (hrangeP.trans hrange)
        have hadm : StatedLieAdmissible .PSL 4 2 g := by
          refine ⟨Nat.prime_two, hf, by norm_num, ?_, ?_⟩
          · intro hbad
            exact absurd (Prod.mk.inj hbad).1 (by norm_num)
          · intro hbad
            exact absurd (Prod.mk.inj hbad).1 (by norm_num)
        have hM := irg_lieModel_quot (ht := Or.inl rfl) hadm ν hνr hνk
        rcases (lieModel_parameters_of_row_III hrow hM).2 with ⟨h, -⟩ | ⟨h, -⟩ <;> cases h
      · have hm'4 : 4 ≤ m' := by omega
        obtain ⟨ν, hνr, hνk⟩ := mkNu .POmegaPlus m' ι hcent hrange
        have hadm : StatedLieAdmissible .POmegaPlus m' 2 g :=
          ⟨Nat.prime_two, hf, hm'4⟩
        have hM := irg_lieModel_quot (ht := Or.inr (Or.inr (Or.inr (Or.inl rfl))))
          hadm ν hνr hνk
        rcases (lieModel_parameters_of_row_III hrow hM).2 with ⟨h, -⟩ | ⟨h, -⟩ <;> cases h
    ·
      subst ht
      by_cases hm'3 : m' = 3
      · subst hm'3
        obtain ⟨eM, heM⟩ := irgIsoCompat_omegaMinus_three (g := g) hf
        obtain ⟨γ, ιM, -, hrangeM, hcentM, -, -⟩ :=
          exists_model_of_irgIsoCompat (t' := .POmegaMinus) (m := 3) (g' := g)
            (t := .PSU) (n := 4) (g := g) (L := ↥(spinGroup Q)) (e := eM) heM ι hcent hlong
        obtain ⟨ν, hνr, hνk⟩ := mkNu .PSU 4 ιM hcentM (hrangeM.trans hrange)
        have hadm : StatedLieAdmissible .PSU 4 2 g := by
          refine ⟨Nat.prime_two, hf, by norm_num, ?_⟩
          intro hbad
          exact absurd (Prod.mk.inj hbad).1 (by norm_num)
        have hM := irg_lieModel_quot (ht := Or.inr (Or.inl rfl)) hadm ν hνr hνk
        have hg1 := (lieModel_parameters_of_row_III hrow hM).1
        refine ⟨hg1, ?_, ?_⟩
        · simpa [hg1] using hM
        · omega
      · have hm'4 : 4 ≤ m' := by omega
        obtain ⟨ν, hνr, hνk⟩ := mkNu .POmegaMinus m' ι hcent hrange
        have hadm : StatedLieAdmissible .POmegaMinus m' 2 g :=
          ⟨Nat.prime_two, hf, hm'4⟩
        have hM := irg_lieModel_quot (ht := Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
          hadm ν hνr hνk
        rcases (lieModel_parameters_of_row_III hrow hM).2 with ⟨h, -⟩ | ⟨h, -⟩ <;> cases h
  ·
    subst ht
    subst hm2
    obtain ⟨ν, hνr, hνk⟩ := mkNu .PSL 2 ι hcent hrange
    let j : (ggU .PSL 2 g).K →* GL (Fin 2) (GaloisField 2 g) := SpecialLinearGroup.toGL
    have hj : Function.Injective j := by
      intro x y hxy
      exact Subtype.ext (congrArg (fun a : GL (Fin 2) (GaloisField 2 g) =>
        (a : Matrix (Fin 2) (Fin 2) (GaloisField 2 g))) hxy)
    have : Finite (ggU .PSL 2 g).K :=
      inferInstanceAs (Finite (SpecialLinearGroup (Fin 2) (GaloisField 2 g)))
    have h3 := three_le_of_row_III_of_matrix_range j hj ν (le_of_eq hνr.symm) hrow
    omega

theorem rowIII_minus_selfDual_two_eq_one
    {X : Type} [Group X] [Finite X] {n g : ℕ} {J : Subgroup X}
    (hn : 4 ≤ n) (hf : 1 ≤ g)
    (φ : ↥(spinGroup (Spin.quadMinus n (GaloisField 2 g) (minusCoeffs 2 g).1
      (minusCoeffs 2 g).2)) →* X)
    (hφk : φ.ker ≤ Subgroup.center ↥(spinGroup (Spin.quadMinus n (GaloisField 2 g)
      (minusCoeffs 2 g).1 (minusCoeffs 2 g).2)))
    (S : Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (GaloisField 2 g)))
    (hSU : ∀ s ∈ S, s ∈ (Spin.spinMatrix
      (Spin.quadMinus n (GaloisField 2 g) (minusCoeffs 2 g).1 (minusCoeffs 2 g).2)).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
      (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (GaloisField 2 g)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 g) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 g))
      (LinearMap.toMatrix₂' (GaloisField 2 g)
        (QuadraticMap.polarBilin
          (Spin.quadMinus n (GaloisField 2 g) (minusCoeffs 2 g).1 (minusCoeffs 2 g).2))) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 g) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 g) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(spinGroup (Spin.quadMinus n (GaloisField 2 g)
      (minusCoeffs 2 g).1 (minusCoeffs 2 g).2))}
    (hJe : IsComponentOf J'
      ⁅(glBlockCentralizer (Spin.spinMatrix
          (Spin.quadMinus n (GaloisField 2 g) (minusCoeffs 2 g).1 (minusCoeffs 2 g).2)) S e :
          Subgroup ↥(spinGroup (Spin.quadMinus n (GaloisField 2 g)
            (minusCoeffs 2 g).1 (minusCoeffs 2 g).2))),
        (glBlockCentralizer (Spin.spinMatrix
          (Spin.quadMinus n (GaloisField 2 g) (minusCoeffs 2 g).1 (minusCoeffs 2 g).2)) S e :
          Subgroup ↥(spinGroup (Spin.quadMinus n (GaloisField 2 g)
            (minusCoeffs 2 g).1 (minusCoeffs 2 g).2)))⁆)
    (hJmap : J'.map φ = J) (hrow : GGSixRCKJRow .III J) : g = 1 := by
  by_contra hgne
  have hg2 : 2 ≤ g := by omega
  let Q := Spin.quadMinus n (GaloisField 2 g) (minusCoeffs 2 g).1 (minusCoeffs 2 g).2
  obtain ⟨r, ι, β₀, hdimr, hlong, hcent, hrange, a₁, a₂, b₁, b₂, hQ, hb1, hb2, hb12,
    hsig, _hsig'⟩ :=
    exists_blockModel_selfDualTwo_POmegaMinus_explicit n g S hSU hS hodd he hn hadj
      hdeg₁ hdeg₂ hJe
  let ιA : (ggU .PSU r (max g 1)).K →* ↥(spinGroup Q) := ι
  have hνr : (φ.comp ιA).range = J := by
    calc (φ.comp ιA).range = (ιA.range).map φ := MonoidHom.range_comp φ ιA
      _ = J'.map φ := by rw [show ιA.range = J' from hrange]
      _ = J := hJmap
  have hνk : (φ.comp ιA).ker ≤ Subgroup.center (ggU .PSU r (max g 1)).K := by
    intro y hy
    exact hcent y (hφk hy)
  have hq : CFSG.Assembly.IsQuasisimple ↥ι.range := by
    rw [hrange]
    exact hJe.2.2
  rcases rckRP_admissible_PSU_of_quasisimple_range (G := ↥(spinGroup Q))
      (le_max_right g 1) ι hq with hadm | ⟨rfl, hmax2⟩
  · have hM := irg_lieModel_quot (ht := Or.inr (Or.inl rfl)) hadm (φ.comp ιA) hνr hνk
    have hmax1 := (lieModel_parameters_of_row_III hrow hM).1
    omega
  ·
    obtain ⟨eU, hec⟩ := irgIsoCompat_su_two (g := max g 1) hmax2
    obtain ⟨γ, ιP, -, hrangeP, hcentP, -, -⟩ :=
      exists_model_of_irgIsoCompat (t' := .PSU) (m := 2) (g' := max g 1)
        (t := .PSL) (n := 2) (g := max g 1) (L := ↥(spinGroup Q)) (e := eU) hec ι hcent hlong
    let ιB : (ggU .PSL 2 (max g 1)).K →* ↥(spinGroup Q) := ιP
    have hνrB : (φ.comp ιB).range = J := by
      calc (φ.comp ιB).range = (ιB.range).map φ := MonoidHom.range_comp φ ιB
        _ = J'.map φ := by rw [show ιB.range = J' from hrangeP.trans hrange]
        _ = J := hJmap
    have hνkB : (φ.comp ιB).ker ≤ Subgroup.center (ggU .PSL 2 (max g 1)).K := by
      intro y hy
      exact hcentP y (hφk hy)
    have hadmP : StatedLieAdmissible .PSL 2 2 (max g 1) := by
      refine ⟨Nat.prime_two, le_max_right g 1, by norm_num, ?_, ?_⟩
      · intro hbad
        have hp := (Prod.mk.inj hbad).2
        have h4 : 4 ≤ 2 ^ max g 1 := by
          simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hmax2
        omega
      · intro hbad
        have hp := (Prod.mk.inj hbad).2
        have h4 : 4 ≤ 2 ^ max g 1 := by
          simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hmax2
        omega
    have hM := irg_lieModel_quot (ht := Or.inl rfl) hadmP (φ.comp ιB) hνrB hνkB
    rcases (lieModel_parameters_of_row_III hrow hM).2 with ⟨h, -⟩ | ⟨h, -⟩ <;> cases h

theorem k2At_of_row_III_of_minus_modelID_of_four_le
    {X : Type} [Group X] [Finite X] {p m g : ℕ} {K J B₁ : Subgroup X} {d r : X}
    {V : Subgroup X}
    (hp : p.Prime) (hp2 : p ≠ 2) (hBab : IsElemAbelian p B₁) (hdB : d ∈ B₁)
    (hrank : p ^ 2 * Nat.card ↥(B₁ ⊓ Subgroup.centralizer (J : Set X)) ≤ Nat.card B₁)
    (hg : 1 ≤ g) (hm4 : 4 ≤ m) (φ : (ggU .POmegaMinus m g).K →* X)
    (hφr : φ.range = K)
    (hφk : φ.ker ≤ Subgroup.center (ggU .POmegaMinus m g).K)
    (hdiag : ∀ b ∈ B₁, GGPsiInnerDiag (ggU .POmegaMinus m g).D φ b)
    (hJcomp : IsComponentOf J (K ⊓ Subgroup.centralizer {d}))
    (hrow : GGSixRCKJRow .III J) (hoddJ : Odd (Nat.card (Subgroup.center ↥J)))
    (hoddK : Odd (Nat.card (Subgroup.center ↥K))) (hJK : J ≤ K)
    (hFour : FourAt J V r) (hCore : CoreCommAt J V r) (hShort : ShortAt J r) :
    K2At K V r := by
  classical
  obtain ⟨s, hs, hsodd, ε, hε, J', hJ'comp, hJ'map⟩ :=
    rckF1_POmegaMinus hp hp2 (hBab.2 d hdB) (minusCoeffs_irr 2 g) hm4 φ hφr hφk
      (hdiag d hdB) hJcomp
  let j : ↥(spinGroup (Spin.quadMinus m (GaloisField 2 g) (minusCoeffs 2 g).1
      (minusCoeffs 2 g).2)) →* GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) (GaloisField 2 g) := by
    exact Spin.spinMatrix (Spin.quadMinus m (GaloisField 2 g) (minusCoeffs 2 g).1
      (minusCoeffs 2 g).2)
  have hSU : ∀ a ∈ ({j s} : Set (GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2)
      (GaloisField 2 g))), a ∈ j.range := by
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    exact ⟨s, ha.symm⟩
  have hS : ∀ a ∈ ({j s} : Set (GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2)
      (GaloisField 2 g))), ∀ b ∈ ({j s} : Set (GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2)
      (GaloisField 2 g))), Commute a b := by
    intro a ha b hb
    rw [Set.mem_singleton_iff] at ha hb
    subst a
    subst b
    exact Commute.refl _
  have hodd : ∀ a ∈ ({j s} : Set (GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2)
      (GaloisField 2 g))), Odd (orderOf a) := by
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    subst a
    exact hsodd
  obtain ⟨e, he, heε, hcase⟩ :=
    exists_isPrimIdemIn_of_isPrimAdjIdemIn_POmegaMinus m g
      ({j s} : Set (GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) (GaloisField 2 g))) hSU hS hε
  have hφinj : Function.Injective φ := by
    have hcenter : Subgroup.center (ggU .POmegaMinus m g).K = ⊥ :=
      PsiDiag.SpinM.center_eq_bot (minusCoeffs_irr 2 g) hm4
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    simpa [hcenter] using hφk hx
  rcases hcase with rfl | ⟨hne, hpair, hεeq⟩
  ·
    have hadj := hε.2.2.2.1
    by_cases hdeg2 : blockDegree (Algebra.adjoin (GaloisField 2 g)
        (Units.val '' ({j s} : Set (GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2)
          (GaloisField 2 g))))) e < 2
    ·
      have hnm : ¬ (e.rank = 4 ∧ ∀ x y : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 →
          GaloisField 2 g,
        e.mulVec x = x → e.mulVec y = y →
        Spin.quadMinus m (GaloisField 2 g) (minusCoeffs 2 g).1 (minusCoeffs 2 g).2 x = 0 →
        Spin.quadMinus m (GaloisField 2 g) (minusCoeffs 2 g).1 (minusCoeffs 2 g).2 y = 0 →
        QuadraticMap.polar
          (Spin.quadMinus m (GaloisField 2 g) (minusCoeffs 2 g).1 (minusCoeffs 2 g).2) x y = 0 →
        ¬ LinearIndependent (GaloisField 2 g) ![x, y]) := by
        intro hω
        exact rckF_POmegaMinus_not_omegaFourMinus hp hp2 hBab hdB hrank
          (minusCoeffs_irr 2 g) hm4 φ hφk hdiag s hs he hadj hω
          (hJ'comp.1.trans (Subgroup.commutator_le_self _)) hJ'map
      obtain ⟨hg1, hLie, hdim⟩ :=
        rowIII_minus_selfDual_rank_three hm4 hg φ hφk
          ({j s} : Set (GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) (GaloisField 2 g)))
          hSU hS hodd he hadj hdeg2 hnm hJ'comp hJ'map hrow
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 4 := ⟨m - 4, by omega⟩
      have hJ'eq := minus_component_eq_of_finrank_six k g
        ({j s} : Set (GL (Fin (k + 4 - 1) ⊕ Fin (k + 4 - 1) ⊕ Fin 2) (GaloisField 2 g)))
        hSU hS hodd he hadj hdeg2 hJ'comp hdim
      subst g
      have hse : (j s : Matrix (Fin (k + 4 - 1) ⊕ Fin (k + 4 - 1) ⊕ Fin 2)
          (Fin (k + 4 - 1) ⊕ Fin (k + 4 - 1) ⊕ Fin 2) (GaloisField 2 1)) * e = e :=
        mul_eq_self_of_blockDegree_lt_two_gf2 he hdeg2
      have hblock := blockOn_glBlockCentralizer_of_mul_eq_self j he hse
      have hact : (fun (u : ↥(spinGroup (Spin.quadMinus (k + 4) (GaloisField 2 1)
            (minusCoeffs 2 1).1 (minusCoeffs 2 1).2)))
          (v : Fin (k + 4 - 1) ⊕ Fin (k + 4 - 1) ⊕ Fin 2 → GaloisField 2 1) =>
          (j u : Matrix (Fin (k + 4 - 1) ⊕ Fin (k + 4 - 1) ⊕ Fin 2)
            (Fin (k + 4 - 1) ⊕ Fin (k + 4 - 1) ⊕ Fin 2) (GaloisField 2 1)) *ᵥ v) =
          fun u v => Spin.spinAction
            (Spin.quadMinus (k + 4) (GaloisField 2 1) (minusCoeffs 2 1).1
              (minusCoeffs 2 1).2) u v := by
        funext u v
        exact Spin.spinMatrix_mulVec _ u v
      rw [hact, ← hJ'eq] at hblock
      have hQnd := CFSG.StandardType.TableC.polarGram_isUnit_det _
        (Spin.nondegenerate_polarBilin_quadMinus_of_finite (k + 4) (GaloisField 2 1)
          (minusCoeffs_irr 2 1))
      have hEmbed : OmegaSixEmbed K J := by
        refine Or.inr ⟨k + 4, φ, LinearMap.range (Matrix.toLin' e),
          LinearMap.ker (Matrix.toLin' e), J', hφr, hφk, hblock, hJ'map, ?_, hdim⟩
        exact polar_eq_zero_of_formAdj_eq_self _ hQnd he.2.1 hadj
      exact k2At_of_omegaSixEmbed_shortAt_psu_four hoddJ hoddK hFour hCore hLie hShort hEmbed
    ·
      have hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 g)
          (Units.val '' ({j s} : Set (GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2)
            (GaloisField 2 g))))) e := Nat.le_of_not_lt hdeg2
      by_cases hdeg4 : blockDegree (Algebra.adjoin (GaloisField 2 g)
          (Units.val '' ({j s} : Set (GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2)
            (GaloisField 2 g))))) e < 4
      · have hg1 := rowIII_minus_selfDual_two_eq_one hm4 hg φ hφk
          ({j s} : Set (GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) (GaloisField 2 g)))
          hSU hS hodd he hadj hdeg₁ hdeg4 hJ'comp hJ'map hrow
        subst g
        let φK : ↥(spinGroup (Spin.quadMinus m (GaloisField 2 1) (minusCoeffs 2 1).1
            (minusCoeffs 2 1).2)) →* K :=
          φ.codRestrict K (fun x => by
            rw [← hφr]
            exact MonoidHom.mem_range.mpr ⟨x, rfl⟩)
        have hφKbij : Function.Bijective φK := by
          constructor
          · intro x y hxy
            exact hφinj (congrArg Subtype.val hxy)
          · intro k
            obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp (by rw [hφr]; exact k.2)
            exact ⟨x, Subtype.ext hx⟩
        let eK : ↥(spinGroup (Spin.quadMinus m (GaloisField 2 1) (minusCoeffs 2 1).1
            (minusCoeffs 2 1).2)) ≃* K := MulEquiv.ofBijective φK hφKbij
        let η : K ≃* ↥(spinGroup (Spin.quadMinus m (GaloisField 2 1) (minusCoeffs 2 1).1
            (minusCoeffs 2 1).2)) := eK.symm
        have hφη : ∀ k : K, φ (η k) = (k : X) := by
          intro k
          exact congrArg Subtype.val (eK.apply_symm_apply k)
        have hcomp : ((J.subgroupOf K).map η.toMonoidHom) = J' := by
          ext x
          constructor
          · rintro ⟨k, hk, rfl⟩
            have hxJ : φ (η k) ∈ J := by rw [hφη k]; exact Subgroup.mem_subgroupOf.mp hk
            rw [← hJ'map] at hxJ
            obtain ⟨y, hy, hyx⟩ := hxJ
            have hyk : y = η k := hφinj hyx
            simpa [hyk] using hy
          · intro hx
            have hφxK : φ x ∈ K := by
              rw [← hφr]
              exact ⟨x, rfl⟩
            have hφxJ : φ x ∈ J := by
              rw [← hJ'map]
              exact ⟨x, hx, rfl⟩
            refine ⟨⟨φ x, hφxK⟩, Subgroup.mem_subgroupOf.mpr hφxJ, ?_⟩
            apply hφinj
            show φ (η ⟨φ x, hφxK⟩) = φ x
            rw [hφη]
        have hBlock : FixedOrthBlockAt K J := by
          refine Or.inr ⟨m, hm4, η,
            ({j s} : Set (GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) (GaloisField 2 1))),
            e, hSU, hS, hodd, he, hadj, hdeg₁, hdeg4, ?_⟩
          rw [hcomp]
          exact hJ'comp
        exact k2At_of_fixedOrthBlockAt hBlock hJK hFour hCore hShort
      ·
        have hFE := ggSixLSevenFieldExtCase_POmegaMinus m (minusCoeffs_irr 2 g) hm4 g
          (GaloisField.card 2 g (by omega)) φ hφk
          ({j s} : Set (GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) (GaloisField 2 g)))
          hSU hS hodd hε hJ'comp he heε (Or.inl ⟨rfl, by omega⟩)
        exact (not_fieldExtCase_of_row_III hrow hg (by simpa [hJ'map] using hFE)).elim
  ·
    by_cases hdeg2 : blockDegree (Algebra.adjoin (GaloisField 2 g)
        (Units.val '' ({j s} : Set (GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2)
          (GaloisField 2 g))))) e < 2
    ·
      have hJe' : IsComponentOf J'
          ⁅(glBlockCentralizer (Spin.spinMatrix
              (Spin.quadMinus m (GaloisField 2 g) (minusCoeffs 2 g).1 (minusCoeffs 2 g).2))
              ({j s} : Set (GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) (GaloisField 2 g)))
              (e + formAdj (RingHom.id (GaloisField 2 g))
                (LinearMap.toMatrix₂' (GaloisField 2 g)
                  (QuadraticMap.polarBilin
                    (Spin.quadMinus m (GaloisField 2 g) (minusCoeffs 2 g).1
                      (minusCoeffs 2 g).2))) e) :
              Subgroup ↥(spinGroup (Spin.quadMinus m (GaloisField 2 g)
                (minusCoeffs 2 g).1 (minusCoeffs 2 g).2))),
            (glBlockCentralizer (Spin.spinMatrix
              (Spin.quadMinus m (GaloisField 2 g) (minusCoeffs 2 g).1 (minusCoeffs 2 g).2))
              ({j s} : Set (GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) (GaloisField 2 g)))
              (e + formAdj (RingHom.id (GaloisField 2 g))
                (LinearMap.toMatrix₂' (GaloisField 2 g)
                  (QuadraticMap.polarBilin
                    (Spin.quadMinus m (GaloisField 2 g) (minusCoeffs 2 g).1
                      (minusCoeffs 2 g).2))) e) :
              Subgroup ↥(spinGroup (Spin.quadMinus m (GaloisField 2 g)
                (minusCoeffs 2 g).1 (minusCoeffs 2 g).2)))⁆ := by
        simpa only [hεeq] using hJ'comp
      obtain ⟨r, ι, β₀, hdimr, hlong, hcent, hrange, a₁, a₂, b₁, b₂, hQ, hb1, hb2, hb12,
        hsig, _hsig'⟩ :=
        exists_blockModel_dualPair_POmegaMinus_explicit m g hg
          ({j s} : Set (GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) (GaloisField 2 g)))
          hSU hS hodd he hm4 hpair hdeg2 hJe'
      have hνr : (φ.comp ι).range = J := by
        calc (φ.comp ι).range = (ι.range).map φ := MonoidHom.range_comp φ ι
          _ = J'.map φ := by rw [hrange]
          _ = J := hJ'map
      have hνk : (φ.comp ι).ker ≤ Subgroup.center (ggU .PSL (r + 1) g).K := by
        intro y hy
        exact hcent y (hφk hy)
      let jj : (ggU .PSL (r + 1) g).K →* GL (Fin (r + 1)) (GaloisField 2 g) :=
        SpecialLinearGroup.toGL
      have hjj : Function.Injective jj := Matrix.SpecialLinearGroup.toGL_injective
      have : Finite (ggU .PSL (r + 1) g).K :=
        inferInstanceAs (Finite (SpecialLinearGroup (Fin (r + 1)) (GaloisField 2 g)))
      have h3 : 3 ≤ r + 1 := three_le_of_row_III_of_matrix_range jj hjj (φ.comp ι)
        (le_of_eq hνr.symm) hrow
      have hadm : StatedLieAdmissible .PSL (r + 1) 2 g := by
        refine ⟨Nat.prime_two, hg, by omega, ?_, ?_⟩
        · intro hbad
          exact absurd (Prod.mk.inj hbad).1 (by omega)
        · intro hbad
          exact absurd (Prod.mk.inj hbad).1 (by omega)
      have hM := irg_lieModel_quot (ht := Or.inl rfl) hadm (φ.comp ι) hνr hνk
      rcases (lieModel_parameters_of_row_III hrow hM).2 with ⟨h, -⟩ | ⟨h, -⟩ <;> cases h
    ·
      have hFE := ggSixLSevenFieldExtCase_POmegaMinus m (minusCoeffs_irr 2 g) hm4 g
        (GaloisField.card 2 g (by omega)) φ hφk
        ({j s} : Set (GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) (GaloisField 2 g)))
        hSU hS hodd hε hJ'comp he heε (Or.inr ⟨hne, by omega⟩)
      exact (not_fieldExtCase_of_row_III hrow hg (by simpa [hJ'map] using hFE)).elim

theorem k2At_of_row_III_of_minus_modelID
    {X : Type} [Group X] [Finite X] {p : ℕ} {K J B₁ : Subgroup X} {d r : X}
    {V : Subgroup X}
    (hp : p.Prime) (hp2 : p ≠ 2) (hBab : IsElemAbelian p B₁) (hdB : d ∈ B₁)
    (hB1K : B₁ ≤ Subgroup.normalizer (K : Set X))
    (hrank : p ^ 2 * Nat.card ↥(B₁ ⊓ Subgroup.centralizer (J : Set X)) ≤ Nat.card B₁)
    (hmodel : RCKClassicalModelIDAt .POmegaMinus K B₁)
    (hJcomp : IsComponentOf J (K ⊓ Subgroup.centralizer {d}))
    (hrow : GGSixRCKJRow .III J) (hoddJ : Odd (Nat.card (Subgroup.center ↥J)))
    (hoddK : Odd (Nat.card (Subgroup.center ↥K))) (hJK : J ≤ K)
    (hFour : FourAt J V r) (hCore : CoreCommAt J V r) (hShort : ShortAt J r) :
    K2At K V r := by
  obtain ⟨m, g, φ, hg, hφr, hφk, hdiag⟩ := hmodel
  by_cases hm : m ≤ 3
  · exact k2At_of_row_III_of_minus_modelID_small hp hp2 hBab hdB hB1K hg φ hφr hφk hdiag
      hJcomp hrow hJK hFour hCore hShort hm
  · exact k2At_of_row_III_of_minus_modelID_of_four_le hp hp2 hBab hdB hrank hg
      (by omega) φ hφr hφk hdiag hJcomp hrow hoddJ hoddK hJK hFour hCore hShort

end CFSG.StandardType.RCKC1
