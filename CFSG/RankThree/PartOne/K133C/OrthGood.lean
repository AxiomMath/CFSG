module

public import CFSG.RankThree.PartOne.K133C.OrthMoving
public import CFSG.RankThree.PartOne.K133C.LinearLeaves
public import CFSG.RankThree.PartOne.CTP.SeitzOrthCount
public import CFSG.RankThree.PartOne.KF.RankGL
public import CFSG.RankThree.PartOne.KF.ClsAltOdd
public import CFSG.RankThree.PartOne.KF.ClsOmegaMinusUpper
public import CFSG.RankThree.PartOne.S15K.PSylowOrth
public import CFSG.RankThree.PartOne.S15K.CommonEigen
public import CFSG.RankThree.PartOne.S11d.LieCentralizerPOmega
public import CFSG.RankThree.PartOne.S11d.OutOrthogonal
import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.RankThree.PartOne.K133C.FixedVectors
public import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive
public import CFSG.RankThree.PartOne.KC.LinearEndpointStatements
public import CFSG.RankThree.PartOne.KC.OrthogonalHighWittFixedSpace
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldFixed
public import CFSG.RankThree.PartOne.KC.PlaneReductionGeneral
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.Walter.Defs
public import Certificates.Certificate1
public import Certificates.Certificate2
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
import CFSG.Foundations
import CFSG.LieType.Universal.Spin.Roots
import CFSG.LieType.Universal.SpinOmega
import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement
import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.RankThree.PartOne.K133C

open Matrix CFSG CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.K133
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin CFSG.LieType.BorelTits
  CFSG.RankThree.PartOne.S15K CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.LIT
open CFSG.RankThree.Classical2 (orthDerived)
open scoped commutatorElement

set_option linter.unusedSectionVars false

section Model

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem polarQuad_of_form (R : QuadraticForm K (ι → K)) (hnd : (QuadraticMap.polarBilin R).Nondegenerate) :
    PolarQuad (⇑R) (LinearMap.BilinForm.toMatrix' (QuadraticMap.polarBilin R)) := by
  have hbf : ∀ x y : ι → K, bf (LinearMap.BilinForm.toMatrix' (QuadraticMap.polarBilin R)) x y =
      QuadraticMap.polar R x y := by
    intro x y
    have := Matrix.toBilin'_apply' (LinearMap.BilinForm.toMatrix' (QuadraticMap.polarBilin R)) x y
    rw [Matrix.toBilin'_toMatrix'] at this
    exact this.symm.trans (QuadraticMap.polarBilin_apply_apply R x y)
  refine ⟨fun x y => ?_, fun c x => ?_, ?_, fun w hw => ?_⟩
  · rw [hbf]
    simp only [QuadraticMap.polar]
    abel
  · rw [QuadraticMap.map_smul, smul_eq_mul, sq]
  · ext i j
    simp only [Matrix.transpose_apply, LinearMap.BilinForm.toMatrix'_apply, QuadraticMap.polarBilin_apply_apply]
    exact QuadraticMap.polar_comm _ _ _
  · refine hnd.2 w fun x => ?_
    rw [QuadraticMap.polarBilin_apply_apply, ← hbf x w]
    show x ⬝ᵥ (LinearMap.BilinForm.toMatrix' (QuadraticMap.polarBilin R) *ᵥ w) = 0
    rw [hw]
    simp


theorem not_dvd_pow_sub_one_of_dvd_four {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h4 : p ∣ q ^ 4 + 1) :
    ∀ i : ℕ, 0 < i → i < 8 → ¬ p ∣ q ^ i - 1 := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 ((ZMod.natCast_eq_zero_iff 2 p).1 this))
  have hx4 : (q : ZMod p) ^ 4 + 1 = 0 := by
    have := (ZMod.natCast_eq_zero_iff _ p).2 h4
    push_cast at this
    exact this
  have hq0 : q ≠ 0 := by
    rintro rfl
    simp at h4
    exact hp.one_lt.ne' h4
  intro i hi hi8 hdvd
  have hq1 : 1 ≤ q ^ i := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero hq0)
  have hxi : (q : ZMod p) ^ i = 1 := by
    have := (ZMod.natCast_eq_zero_iff _ p).2 hdvd
    rw [Nat.cast_sub hq1] at this
    push_cast at this
    exact sub_eq_zero.1 this
  set x : ZMod p := (q : ZMod p) with hx
  have h8 : x ^ 8 = 1 := by
    have : x ^ 4 = -1 := by linear_combination hx4
    calc x ^ 8 = (x ^ 4) ^ 2 := by ring
      _ = 1 := by rw [this]; norm_num
  have hne4 : ¬ orderOf x ∣ 4 := fun hd => by
    have := orderOf_dvd_iff_pow_eq_one.1 hd
    apply h2
    linear_combination hx4 - this
  have hd8 : orderOf x ∣ 2 ^ 3 := orderOf_dvd_of_pow_eq_one h8
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd8
  have hord : orderOf x = 8 := by
    interval_cases k
    · exact absurd (by rw [hk']; norm_num) hne4
    · exact absurd (by rw [hk']; norm_num) hne4
    · exact absurd (by rw [hk']; norm_num) hne4
    · rw [hk']; norm_num
  have := orderOf_dvd_iff_pow_eq_one.2 hxi
  rw [hord] at this
  have := Nat.le_of_dvd hi this
  omega


theorem not_dvd_pow_sub_one_of_dvd_three {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : 1 ≤ q)
    (h3 : p ∣ q ^ 3 - 1) (h1 : ¬ p ∣ q - 1) : ∀ i : ℕ, 0 < i → i < 3 → ¬ p ∣ q ^ i - 1 := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 ((ZMod.natCast_eq_zero_iff 2 p).1 this))
  intro i hi hi3
  interval_cases i
  · simpa using h1
  · intro hd
    have h' : p ∣ (q + 1) * (q - 1) := by
      have := Nat.sq_sub_sq q 1
      rw [one_pow] at this
      rw [← this]
      exact hd
    rcases (Nat.Prime.dvd_mul hp).1 h' with h4 | h4
    · have hx1 : (q : ZMod p) + 1 = 0 := by
        have := (ZMod.natCast_eq_zero_iff _ p).2 h4
        push_cast at this
        exact this
      have hq3 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ hq
      have hx3 : (q : ZMod p) ^ 3 = 1 := by
        have := (ZMod.natCast_eq_zero_iff _ p).2 h3
        rw [Nat.cast_sub hq3] at this
        push_cast at this
        exact sub_eq_zero.1 this
      apply h2
      linear_combination ((q : ZMod p) ^ 2 - (q : ZMod p) + 1) * hx1 - hx3
    · exact h1 h4

section Planes

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}

local notation "ιM" => (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2)

theorem exists_moving_statedOmega_quadMinus {m : ℕ} (hK : Nat.card K = 2 ^ m)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (F : Subgroup (GL ιM K)) (hFM : F ≤ StatedOmega (StatedQuadMinus 4 K b c))
    (hFe : IsElementaryAbelian p F) (hFc : Nat.card F = p ^ 2) :
    ∃ S : Subgroup (GL ιM K), S ≤ StatedOmega (StatedQuadMinus 4 K b c) ∧ IsPGroup 2 S ∧
      (∀ h ∈ F, ∀ x ∈ S, h * x * h⁻¹ ∈ S) ∧ ∃ h ∈ F, ∃ x ∈ S, h * x * h⁻¹ ≠ x := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hQ : ⇑(quadMinus 4 K b c) = StatedQuadMinus 4 K b c := coe_quadMinus 4 K b c
  obtain ⟨hnd, -⟩ := regular_quadMinus (n := 4) (K := K) (by norm_num) hirr
  have hP : PolarQuad (StatedQuadMinus 4 K b c)
      (LinearMap.BilinForm.toMatrix' (QuadraticMap.polarBilin (quadMinus 4 K b c))) := by
    rw [← hQ]
    exact polarQuad_of_form _ hnd
  set Q₀ := StatedQuadMinus 4 K b c with hQ₀
  have hpK : (p : K) ≠ 0 := by
    intro h
    have h2 : (2 : ℕ) ∣ p := (CharP.cast_eq_zero_iff K 2 p).1 h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h2).symm
  have hpow : ∀ h ∈ F, h ^ p = 1 := fun h hh =>
    CFSG.elemPow_eq_one_of_isElementaryAbelian h hh
  have hcomm : ∀ g ∈ F, ∀ h ∈ F, g * h = h * g := fun g hg h hh =>
    congrArg Subtype.val (hFe.is_comm.comm (⟨g, hg⟩ : F) ⟨h, hh⟩)
  have hFQ : F ≤ orthSub Q₀ := fun h hh v =>
    orthGroup_preserves Q₀ (statedOmega_le_orthGroup Q₀ (hFM hh)) v
  have hF1 : ∃ h ∈ F, h ≠ 1 := by
    by_contra hno
    push Not at hno
    have : F = ⊥ := (Subgroup.eq_bot_iff_forall F).2 hno
    rw [this, Subgroup.card_bot] at hFc
    have := Nat.one_lt_pow (n := 2) (by norm_num) hp.one_lt
    omega
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have hcardι : Fintype.card ιM = 8 := by simp
  set Θ : GL ιM K →* (ιM → K) ≃ₗ[K] (ιM → K) := (toLinEquiv ιM K).toMonoidHom with hΘ
  have hΘinj : Function.Injective Θ := (toLinEquiv ιM K).injective
  have hFO : F.map Θ ≤ TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 K b c) := by
    rintro _ ⟨h, hh, rfl⟩
    have hh' : h ∈ orthGroup Q₀ := statedOmega_le_orthGroup Q₀ (hFM hh)
    rw [orthGroup, closure_isometries_eq_comap hQ] at hh'
    exact hh'
  have hpowE : ∀ x ∈ F.map Θ, x ^ p = 1 := by
    rintro _ ⟨h, hh, rfl⟩
    rw [← map_pow, hpow h hh, map_one]
  by_cases hA : p ∣ (Nat.card K ^ 4 + 1) * (Nat.card K ^ 3 - 1) * Nat.card K ^ 6
  · rcases (Nat.Prime.dvd_mul hp).1 hA with h1 | h6
    · rcases (Nat.Prime.dvd_mul hp).1 h1 with h4 | h3
      ·
        exfalso
        have hb := card_le_pow_div_gl hp hpK (d := 8) (by norm_num)
          (not_dvd_pow_sub_one_of_dvd_four hp hp2 h4) F hcomm hpow
        rw [hcardι, hFc] at hb
        have hb' : p ^ 2 ≤ p := by simpa using hb
        nlinarith [hb', hp5]
      · by_cases h1' : p ∣ Nat.card K - 1
        ·
          obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_of_dvd hp h1'
          have hK2 : 2 < Nat.card K := by
            have h0 : 0 < Nat.card K - 1 := by
              have : 1 < Nat.card K := Finite.one_lt_card
              omega
            have := Nat.le_of_dvd h0 h1'
            omega
          have hW3 : 3 ≤ Module.finrank K (ιM → K) := by
            rw [Module.finrank_fintype_fun_eq_card, hcardι]
            norm_num
          have hPS := psylowSub_orthDerived hnd hW3 hK2 hp hp2 hζ
          have hmap : (StatedOmega Q₀).map Θ = orthDerived (quadMinus 4 K b c) := by
            rw [statedOmega_eq_comap hQ]
            exact Subgroup.map_comap_eq_self_of_surjective (toLinEquiv ιM K).surjective _
          have hPS' : PSylowSub p (StatedOmega Q₀) :=
            PSylowSub.of_map Θ hΘinj (by rw [hmap]; exact hPS)
          have hF1' : F ≠ ⊥ := by
            intro hb
            obtain ⟨h, hh, hne⟩ := hF1
            exact hne ((Subgroup.eq_bot_iff_forall F).1 hb h hh)
          obtain ⟨S, hSM, hS1, hS2, hSN, hSc⟩ := hPS' F hFM hcomm hpow hF1'
          exact ⟨S, hSM, hS2, fun h hh x hx => (Subgroup.mem_normalizer_iff.1 (hSN hh) x).1 hx,
            exists_moved_of_commutator_eq F S hS1 hSc⟩
        ·
          exfalso
          have hdiv3 := not_dvd_pow_sub_one_of_dvd_three hp hp2 hq1 h3 h1'
          have h3' : p ∣ Nat.card K ^ 3 - 1 := h3
          have hE'fin : Finite (F.map Θ) :=
            Nat.finite_of_card_ne_zero (by
              rw [Subgroup.card_map_of_injective hΘinj, hFc]
              exact pow_ne_zero 2 hp.ne_zero)
          have hcardE' : Nat.card (F.map Θ) = p ^ 2 := by
            rw [Subgroup.card_map_of_injective hΘinj, hFc]
          have hdim : Module.finrank K (ιM → K) = 8 := by
            rw [Module.finrank_fintype_fun_eq_card, hcardι]
          have hBnd : ∀ v, (∀ w, (QuadraticMap.polarBilin (quadMinus 4 K b c)) v w = 0) → v = 0 :=
            fun v hv => hnd.1 v hv
          have hBalt : ∀ v, (QuadraticMap.polarBilin (quadMinus 4 K b c)) v v = 0 := by
            intro v
            rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, two_smul,
              CharTwo.add_self_eq_zero]
          have hcommE' : ∀ g ∈ F.map Θ, ∀ h ∈ F.map Θ, g * h = h * g := by
            rintro _ ⟨a, ha, rfl⟩ _ ⟨a', ha', rfl⟩
            rw [← map_mul, ← map_mul, hcomm a ha a' ha']
          have hpresE' : ∀ g ∈ F.map Θ, ∀ u w, (QuadraticMap.polarBilin (quadMinus 4 K b c)) (g u) (g w) =
              (QuadraticMap.polarBilin (quadMinus 4 K b c)) u w := by
            intro g hg u w
            rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply]
            exact polar_map_of_mem (hFO hg) u w
          have hbound := card_le_pow_div_alt_odd hp hpK (d := 3) (by norm_num) (by decide) hdiv3 h3' 8
            (ιM → K) hdim (QuadraticMap.polarBilin (quadMinus 4 K b c)) hBnd hBalt (F.map Θ) hcommE'
            hpowE hpresE'
          rw [hcardE'] at hbound
          have hb' : p ^ 2 ≤ p := by simpa using hbound
          nlinarith [hb', hp5]
    · exfalso
      have h0 : p ∣ Nat.card K := hp.dvd_of_dvd_pow h6
      rw [hK] at h0
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h0))
  ·
    have hcardhp := CFSG.RankThree.PartOne.CTP.card_hypPairs_quadMinus_four hirr
    obtain ⟨P, hPfix⟩ := exists_fixed_hypPair hFO hpowE (by rw [hcardhp]; exact hA)
    have hs0 : P.e ≠ 0 := by
      intro h0
      have := P.polar_ef
      rw [h0, QuadraticMap.polar_zero_left] at this
      exact zero_ne_one this
    have hs : Q₀ P.e = 0 := by rw [← hQ]; exact P.Q_e
    have hfix : ∀ h ∈ F, (h : Matrix ιM ιM K) *ᵥ P.e = P.e := fun h hh =>
      (hPfix (Θ h) (Subgroup.mem_map_of_mem _ hh)).1
    obtain ⟨S, hSQ, hS2, hSst, hmv⟩ := exists_moving_orth hpK hP hs0 hs F hFQ hpow hfix hF1
    have hSF : F ≤ Subgroup.normalizer (S : Set (GL ιM K)) := by
      intro h hh
      rw [Subgroup.mem_normalizer_iff]
      intro x
      refine ⟨fun hx => hSst h hh x hx, fun hx => ?_⟩
      have := hSst h⁻¹ (F.inv_mem hh) (h * x * h⁻¹) hx
      simpa [mul_assoc] using this
    have hSO : S ≤ orthGroup Q₀ := fun x hx => Subgroup.subset_closure (hSQ hx)
    have hFO' : F ≤ orthGroup Q₀ := hFM.trans (statedOmega_le_orthGroup Q₀)
    have hN : ⁅S, F⁆ ≤ StatedOmega Q₀ := Subgroup.commutator_mono hSO hFO'
    have hFp : IsPGroup p F := by
      have := hFe
      exact IsElementaryAbelian.isPGroup p F
    exact exists_commutator_two_group hp hp2 F S (StatedOmega Q₀) hFp hS2 hSF hmv hN

end Planes

end Model

open CFSG.RankThree.PartOne.OutStructure CFSG.RankThree.PartOne.N143X CFSG.RankThree.PartOne.S13K
open CFSG.RankThree.PartOne.Census3 (IsoLie)

theorem good_of_model_POmegaMinus {X : Type} [Group X] [Finite X] {m p : ℕ} (hp : p.Prime)
    (h5 : 5 ≤ p) (hZ : Subgroup.center X = ⊥) (h : StatedClassicalModel X .POmegaMinus 4 2 m) :
    Good p X := by
  have hp2 : p ≠ 2 := by omega
  have hO := (outPNice_POmegaMinus hp hp2 (le_refl 4) h).toChain
  refine good_of_movingPlanes hp hZ hO fun P hPe hPc => ?_
  obtain ⟨hadm, K, hKf, hKfin, hK, b, c, hirr, ⟨e⟩⟩ := id h
  have : CharP K 2 := charP_two_of_card_eq_pow hK
  have : Nonempty (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) := ⟨Sum.inl ⟨0, by norm_num⟩⟩
  refine movingPlane_of_matrix_model (StatedOmega (StatedQuadMinus 4 K b c)) e hp (d := 1) ?_
    (fun hd => by have := Nat.le_of_dvd one_pos hd; omega) ?_ hPe hPc
  · intro z hz
    have hmem : (⟨Matrix.GeneralLinearGroup.scalar _ z, hz⟩ : StatedOmega (StatedQuadMinus 4 K b c)) ∈
        (StatedScalars (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) K).subgroupOf
          (StatedOmega (StatedQuadMinus 4 K b c)) := ⟨z, rfl⟩
    rw [statedScalars_subgroupOf_statedOmega_quadMinus_eq_bot, Subgroup.mem_bot] at hmem
    have h1 : Matrix.GeneralLinearGroup.scalar (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) z = 1 :=
      congrArg Subtype.val hmem
    have : z = 1 := scalar_unit_injective (by rw [h1, map_one])
    rw [this, one_pow]
  · intro F hFM hFe hFc
    exact exists_moving_statedOmega_quadMinus hK hirr hp h5 F hFM hFe hFc

theorem kf133ResMaxAt_leaf8_two (hTypes : ∀ r, 9 ≤ r → r ≤ 12 → KF132Types r) :
    KF133ResMaxAt (leaf8 2) := by
  refine KF133ResMaxAt.of_goodRes hTypes fun X _ _ _ hne hX p hp h5 => ?_
  obtain ⟨q, hq2, hv, ⟨e0⟩⟩ := hX
  have hmod := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even 4 q hv hq2 e0
  rw [hq2] at hmod
  exact (good_of_model_POmegaMinus hp h5 (center_bot_of_simple hne) hmod).goodRes

end CFSG.RankThree.PartOne.K133C
