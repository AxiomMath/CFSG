module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18Defs
public import CFSG.LocalAnalysis.EvenBN.U5.OuterInvolution
public import CFSG.GH74.KGroups.FieldGF
public import CFSG.ClassicalInvolution.ModelFacts.MF15S1UGeo
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18U54InvRankModel
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellBasic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsE
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22g
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveDefs
import CFSG.LocalAnalysis.EvenBN.U5.ModelLevi
import CFSG.LocalAnalysis.EvenBN.U5.ModelSylowRank
import CFSG.Quasithin.Background.F9FiveStruct
import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
import CFSG.Quasithin.EmptyFaithful.S142Statements
import CFSG.Quasithin.H13.A5S1326
import CFSG.Quasithin.H13.A5Top
import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModU5Gen
import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsThree
import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsUnitAut
import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsYamStd

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

open Matrix CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.U5K.Hyp
open U54InvRank (bar16 idx51)

private def Y16 : Matrix (HypIndex 2 1) (HypIndex 2 1) CFSG.GH74.KGroups.GF16 :=
  (!![CFSG.GH74.KGroups.GF16.ofNat' 11, CFSG.GH74.KGroups.GF16.ofNat' 14,
      CFSG.GH74.KGroups.GF16.ofNat' 1, CFSG.GH74.KGroups.GF16.ofNat' 5,
      CFSG.GH74.KGroups.GF16.ofNat' 3;
      CFSG.GH74.KGroups.GF16.ofNat' 11, CFSG.GH74.KGroups.GF16.ofNat' 1,
      CFSG.GH74.KGroups.GF16.ofNat' 12, CFSG.GH74.KGroups.GF16.ofNat' 3,
      CFSG.GH74.KGroups.GF16.ofNat' 0;
      CFSG.GH74.KGroups.GF16.ofNat' 11, CFSG.GH74.KGroups.GF16.ofNat' 2,
      CFSG.GH74.KGroups.GF16.ofNat' 5, CFSG.GH74.KGroups.GF16.ofNat' 1,
      CFSG.GH74.KGroups.GF16.ofNat' 12;
      CFSG.GH74.KGroups.GF16.ofNat' 14, CFSG.GH74.KGroups.GF16.ofNat' 15,
      CFSG.GH74.KGroups.GF16.ofNat' 11, CFSG.GH74.KGroups.GF16.ofNat' 11,
      CFSG.GH74.KGroups.GF16.ofNat' 11;
      CFSG.GH74.KGroups.GF16.ofNat' 15, CFSG.GH74.KGroups.GF16.ofNat' 4,
      CFSG.GH74.KGroups.GF16.ofNat' 2, CFSG.GH74.KGroups.GF16.ofNat' 14,
      CFSG.GH74.KGroups.GF16.ofNat' 1] : Matrix (Fin 5) (Fin 5) _).submatrix idx51 idx51

private theorem Y16_det : Y16.det = 1 := by decide +kernel

private theorem Y16_iso : (Y16.map bar16)ᵀ * hypGram 2 1 CFSG.GH74.KGroups.GF16 * Y16 =
    hypGram 2 1 CFSG.GH74.KGroups.GF16 := by decide +kernel

private theorem Y16_mul : (Y16.map bar16) * Y16 = 1 := by decide +kernel

private theorem Y16_pow : Y16 ^ 41 =
    Matrix.scalar (HypIndex 2 1) (CFSG.GH74.KGroups.GF16.ofNat' 8) := by decide +kernel

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6

open Matrix CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.U5K.Hyp
open U54InvRank (bar16 idx51)
open CFSG.LocalAnalysis.EvenBN.U5.OuterInvolution
open CFSG.ClassicalInvolution.ModelFacts.MF15

private theorem exists_order41_inverted {K : Type} [Field K] [Finite K]
    [Fact (Nat.Prime 2)] [CharP K 2] (h : UnitaryFieldData 2 2 K) :
    ∃ y : hypPSU h 2 1, orderOf y = 41 ∧
      Phi h (fieldElt h (barEquiv (p := 2) (f := 2) (K := K))) y = y⁻¹ := by
  letI : Fintype K := Fintype.ofFinite K
  have hK16 : Fintype.card K = 16 := by
    rw [Fintype.card_eq_nat_card, h.card]
    norm_num
  have hG16 : Fintype.card CFSG.GH74.KGroups.GF16 = 16 := by decide +kernel
  let ψ : K ≃+* CFSG.GH74.KGroups.GF16 :=
    FiniteField.ringEquivOfCardEq (hK16.trans hG16.symm)
  let Y : Matrix (HypIndex 2 1) (HypIndex 2 1) K := Y16.map ψ.symm
  have hYmap : Y.map ψ = Y16 := by
    ext i j
    simp [Y, Matrix.map_apply]
  have hYdet : Y.det = 1 := by
    apply ψ.injective
    have hdet : ψ Y.det = (Y.map ψ).det :=
      RingHom.map_det (ψ : K →+* CFSG.GH74.KGroups.GF16) Y
    rw [hdet, hYmap, Y16_det, map_one]
  have hgram : (hypGram 2 1 K).map ψ = hypGram 2 1 CFSG.GH74.KGroups.GF16 := by
    ext i j
    rcases i with i | (k | i) <;> rcases j with j | (l | j) <;>
      simp [hypGram, map_zero ψ, map_one ψ, Matrix.one_apply]
  have hYmap_bar : (Y.map h.bar).map ψ = Y16.map bar16 := by
    ext i j
    simp [Matrix.map_apply, Y, h.bar_apply, bar16, map_pow]
  have hYiso : (Y.map h.bar)ᵀ * hypGram 2 1 K * Y = hypGram 2 1 K := by
    apply Matrix.map_injective ψ.injective
    simp only [Matrix.map_mul, Matrix.transpose_map, hYmap_bar, hYmap, hgram, Y16_iso]
  have hYmul : (Y.map h.bar) * Y = 1 := by
    apply Matrix.map_injective ψ.injective
    simp only [Matrix.map_mul, hYmap_bar, hYmap, Y16_mul]
    exact (Matrix.map_one ψ (map_zero ψ) (map_one ψ)).symm
  have hYpow : Y ^ 41 =
      Matrix.scalar (HypIndex 2 1) (ψ.symm (CFSG.GH74.KGroups.GF16.ofNat' 8)) := by
    refine Matrix.map_injective (f := (ψ : K → CFSG.GH74.KGroups.GF16)) ψ.injective ?_
    change (Y ^ 41).map ψ =
      (Matrix.scalar (HypIndex 2 1) (ψ.symm (CFSG.GH74.KGroups.GF16.ofNat' 8))).map ψ
    rw [show (Y ^ 41).map ψ = RingEquiv.mapMatrix ψ (Y ^ 41) from
      (RingEquiv.mapMatrix_apply ψ (Y ^ 41)).symm]
    rw [map_pow, show RingEquiv.mapMatrix ψ Y = Y16 from
      (RingEquiv.mapMatrix_apply ψ Y).trans hYmap, Y16_pow]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.scalar_apply, Matrix.map_apply]
    · simp [Matrix.scalar_apply, Matrix.map_apply, hij]
  have hYentry : Y (.inl 0) (.inl 1) = ψ.symm (CFSG.GH74.KGroups.GF16.ofNat' 14) := by
    simp [Y, Y16, idx51, Matrix.map_apply]
  have hYentry_ne : Y (.inl 0) (.inl 1) ≠ 0 := by
    rw [hYentry]
    intro h0
    have h1 : (CFSG.GH74.KGroups.GF16.ofNat' 14) = 0 := by
      have := congrArg ψ h0
      rwa [RingEquiv.apply_symm_apply, map_zero] at this
    exact (by decide +kernel : (CFSG.GH74.KGroups.GF16.ofNat' 14) ≠ 0) h1
  let Ygl : GL (HypIndex 2 1) K :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero Y (by rw [hYdet]; exact one_ne_zero)
  have hYgl : (Ygl : Matrix (HypIndex 2 1) (HypIndex 2 1) K) = Y := rfl
  have hYsu : Ygl ∈ hypSU h 2 1 := by
    rw [mem_hypSU, hYgl]
    exact ⟨hYiso, hYdet⟩
  let Ysu : hypSU h 2 1 := ⟨Ygl, hYsu⟩
  have hYbar : (Y.map h.bar) = (Ygl : Matrix (HypIndex 2 1) (HypIndex 2 1) K)⁻¹ := by
    have h1 : ((Ygl⁻¹ : GL (HypIndex 2 1) K) :
        Matrix (HypIndex 2 1) (HypIndex 2 1) K) = Y⁻¹ := by
      rw [Matrix.GeneralLinearGroup.coe_inv, hYgl]
    have h2 : (Y.map h.bar) = Y⁻¹ := (Matrix.inv_eq_left_inv hYmul).symm
    rw [h2]
    exact h1.symm.trans (Matrix.GeneralLinearGroup.coe_inv Ygl)
  have hact : act h (fieldElt h (barEquiv (p := 2) (f := 2) (K := K))) Ysu = Ysu⁻¹ := by
    apply mat_injective
    rw [mat_act_fieldElt]
    rw [show mat Ysu = Y from rfl]
    rw [show mat (Ysu⁻¹) = (Ygl : Matrix (HypIndex 2 1) (HypIndex 2 1) K)⁻¹ from by
      change ((Ygl⁻¹ : GL (HypIndex 2 1) K) :
        Matrix (HypIndex 2 1) (HypIndex 2 1) K) = (Ygl : Matrix _ _ _)⁻¹
      exact Matrix.GeneralLinearGroup.coe_inv Ygl]
    exact hYbar
  have hPhi : Phi h (fieldElt h (barEquiv (p := 2) (f := 2) (K := K))) (hypProj h 2 1 Ysu) =
      (hypProj h 2 1 Ysu)⁻¹ := by
    rw [Phi_apply, hact, map_inv]
  have hc0 : ψ.symm (CFSG.GH74.KGroups.GF16.ofNat' 8) ≠ 0 := by
    intro h0
    have h1 : (CFSG.GH74.KGroups.GF16.ofNat' 8) = 0 := by
      have := congrArg ψ h0
      rwa [RingEquiv.apply_symm_apply, map_zero] at this
    exact (by decide +kernel : (CFSG.GH74.KGroups.GF16.ofNat' 8) ≠ 0) h1
  let c : Kˣ := Units.mk0 (ψ.symm (CFSG.GH74.KGroups.GF16.ofNat' 8)) hc0
  have hcval : (c : K) = ψ.symm (CFSG.GH74.KGroups.GF16.ofNat' 8) := rfl
  have hnorm : h.norm (c : K) = 1 := by
    apply ψ.injective
    change ψ ((c : K) * h.bar (c : K)) = ψ 1
    rw [map_mul, map_one, hcval]
    rw [h.bar_apply, map_pow, RingEquiv.apply_symm_apply]
    decide +kernel
  have hc5 : c ^ 5 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, hcval]
    apply ψ.injective
    rw [map_pow, RingEquiv.apply_symm_apply, map_one]
    decide +kernel
  have hYpowScalar : Ysu ^ 41 ∈ hypScalars h 2 1 := by
    rw [mem_normOneScalars]
    refine ⟨c, hnorm, hc5, ?_⟩
    apply Units.ext
    rw [Subgroup.coe_pow, show (Ysu : GL (HypIndex 2 1) K) = Ygl from rfl,
      Units.val_pow_eq_pow_val, hYgl, hYpow]
    exact (Matrix.GeneralLinearGroup.coe_scalar c).symm
  have hy41 : (hypProj h 2 1 Ysu) ^ 41 = 1 := by
    rw [← map_pow]
    rw [← MonoidHom.mem_ker, ker_hypProj]
    exact hYpowScalar
  have hyne : hypProj h 2 1 Ysu ≠ 1 := by
    intro h1
    have hmem : Ysu ∈ hypScalars h 2 1 := by
      rw [← ker_hypProj, MonoidHom.mem_ker]
      exact h1
    obtain ⟨c', -, -, hc'⟩ := (mem_normOneScalars (h := h) (H := hypSU h 2 1)
      (m := 2 * 2 + 1)).mp hmem
    have hYscalar : Y = Matrix.scalar (HypIndex 2 1) (c' : K) := by
      rw [← hYgl]
      exact congrArg (fun g : GL (HypIndex 2 1) K =>
        (g : Matrix (HypIndex 2 1) (HypIndex 2 1) K)) hc'
    apply hYentry_ne
    rw [hYscalar]
    by_cases hij : (.inl 0 : HypIndex 2 1) = .inl 1
    · exact absurd hij (by decide)
    · simp [Matrix.scalar_apply, Matrix.diagonal, hij]
  haveI : Fact (Nat.Prime 41) := ⟨by norm_num⟩
  refine ⟨hypProj h 2 1 Ysu, orderOf_eq_prime hy41 hyne, hPhi⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise
open Matrix CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.U5K.Hyp
open CFSG.LocalAnalysis.EvenBN.U5.OuterInvolution
open CFSG.ClassicalInvolution.ModelFacts.MF15

theorem k146U54OuterInv_holds : K146U54OuterInv := by
  intro S _ _ hS α hα hout
  obtain ⟨K, hfield, h, ⟨e₀⟩⟩ := U54InvRank.exists_hypPSU_equiv_of_lieModel hS
  letI := hfield
  letI : Finite K := h.finite
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  letI : CharP K 2 := h.charP
  let e : S ≃* hypPSU h 2 1 := e₀.symm
  let a : MulAut (hypPSU h 2 1) := MulAut.congr e α
  have ha2 : a * a = 1 := by
    change MulAut.congr e α * MulAut.congr e α = 1
    rw [← map_mul, show α * α = 1 by rw [← pow_two]; exact hα, map_one]
  have haout : a ∉ Pi h := by
    rintro ⟨z, hz⟩
    apply hout
    refine ⟨e.symm z, fun x => ?_⟩
    have h1 : a (e x) = z * e x * z⁻¹ := by
      rw [← hz]
      rfl
    have h2 := congrArg e.symm h1
    simpa [a, MulAut.congr_apply, map_mul, map_inv] using h2
  obtain ⟨σ, hσ, γ, hγ, hconj⟩ :=
    CFSG.LocalAnalysis.EvenBN.U5.exists_eq_conj_fieldElt ha2 haout
  have hσeq : σ = barEquiv (p := 2) (f := 2) (K := K) := by
    apply RingEquiv.ext
    intro c
    rw [barEquiv_apply h]
    exact hσ c
  rw [hσeq] at hconj
  obtain ⟨y0, hy0ord, hy0inv⟩ := exists_order41_inverted h
  let z0 : hypPSU h 2 1 := γ y0
  have hz0ord : orderOf z0 = 41 := by
    rw [show z0 = γ y0 from rfl, MulEquiv.orderOf_eq γ y0, hy0ord]
  have hz0inv : a z0 = z0⁻¹ := by
    rw [hconj]
    simp only [MulAut.mul_apply, MulAut.inv_apply]
    rw [show z0 = γ y0 from rfl]
    rw [MulEquiv.symm_apply_apply, hy0inv, map_inv]
  refine ⟨e.symm z0, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq, hz0ord]
  · have hαz : e.symm (a z0) = α (e.symm z0) := by
      simp [a, MulAut.congr_apply]
    rw [← hαz, congrArg e.symm hz0inv, map_inv]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6
