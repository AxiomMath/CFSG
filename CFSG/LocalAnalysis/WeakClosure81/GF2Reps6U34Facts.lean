module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6FourFacts
public import CFSG.Blueprint.Catalog
public import Certificates.Certificate745101
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6U34Wit
import CFSG.GH74.KGroups.CoverEven
import CFSG.GH74.Uniqueness.Bender.UnitaryFixed
import CFSG.CGT.T75A.OuterConj
import CFSG.RankThree.PartTwo.KFacts.KS21U34
import CFSG.GroupTheory.CommuteOfSqEqOne
public import CFSG.LieType.SeitzGeneration.NonabHeisThreeCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U34InvolutionGenModel
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeOrbits
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import CFSG.Assembly.OrderReductions.InvertedSubgroup
import CFSG.Assembly.OrderReductions.OddInversion
import CFSG.GH74.GLS.Classes
import CFSG.GH74.Statements
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_1_12

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch6

open CFSG.Blueprint (LieModel)
open CFSG.ClassicalGroups.UnitaryFlag CFSG.GH74.KGroups
open CFSG.GH74.Uniqueness.Bender
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.RankThree.PartTwo.KFacts

local notation "SU3" => unitarySU 2 2 GF16 3

private theorem exists_congr_fieldAut {Y : Type} [Group Y]
    (hY : LieModel Y .PSU 3 2 2) {β : MulAut Y} (hβ2 : β * β = 1)
    (hβout : β ∉ (MulAut.conj : Y →* MulAut Y).range) :
    ∃ Φ : SU3 ≃* Y,
      MulAut.congr Φ (suField unitaryFieldData_GF16 unitaryFieldData_GF16.barEquiv) = β := by
  let β₀ : MulAut SU3 := suField unitaryFieldData_GF16 unitaryFieldData_GF16.barEquiv
  have hβ₀2 : β₀ * β₀ = 1 := U34.suField_mul_self
  have hβ₀out : β₀ ∉ (MulAut.conj : SU3 →* MulAut SU3).range :=
    U34.suField_not_mem_range
  have hβ₀ne : β₀ ≠ 1 := fun h => hβ₀out ⟨1, by rw [map_one, h]⟩
  have hβ₀ord : orderOf β₀ = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hβ₀2) hβ₀ne
  have hD : CFSG.Open.StatedClassicalModel Y .PSU 3 2 2 := hY.statedClassicalModel (by decide)
  obtain ⟨eY⟩ := CFSG.RankThree.PartTwo.KFacts.KS21.U34.nonempty_equiv_Y hD
  let ψ : Y ≃* SU3 := eY.trans
    (CFSG.LieType.Universal.Unitary.equivStatedSU
      CFSG.RankThree.PartTwo.KFacts.KS21.U34.card_GF16 3)
  let α : MulAut Y := MulAut.congr ψ.symm β₀
  have hα := CFSG.CGT.T75A.transport_outer ψ.symm hβ₀ord hβ₀out
  have hα2 : orderOf α = 2 := hα.1
  have hαout : α ∉ (MulAut.conj : Y →* MulAut Y).range := by
    rintro ⟨y, hy⟩
    exact hα.2 y (by simpa [α] using hy.symm)
  have hβne : β ≠ 1 := fun h => hβout ⟨1, by rw [map_one, h]⟩
  have hβord : orderOf β = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hβ2) hβne
  have hconj : IsConj α β :=
    CFSG.CGT.T75A.outer_involutions_conj (D := Y) (f := 2) (by norm_num) hD hα2 hβord
      hαout hβout
  obtain ⟨γ, hγ⟩ := isConj_iff.1 hconj
  refine ⟨ψ.symm.trans γ, ?_⟩
  have hcomp : MulAut.congr (ψ.symm.trans γ) β₀ = γ * α * γ⁻¹ := by
    ext x
    simp [MulAut.congr_apply, MulEquiv.trans_apply, α]
  rw [hcomp, hγ]

private theorem isSimple_autFixed {Y : Type} [Group Y] [Finite Y] {e : ℕ}
    (hBen : BenderType Y 2 3 e) {β : MulAut Y} (hβ2 : β * β = 1)
    (hout : ¬ ∃ g : Y, ∀ x : Y, β x = g * x * g⁻¹) :
    IsSimpleGroup (autFixed β) := by
  obtain ⟨φ⟩ := hBen.fixed_unitary β hβ2 hout
  haveI : Finite (autFixed β) :=
    Finite.of_injective (fun x : autFixed β => (x : Y)) (fun x y h => Subtype.ext h)
  exact (BenderType.linear 2 le_rfl φ).isSimple

private theorem centralizer_autFixed {Y : Type} [Group Y] {e : ℕ}
    (hBen : BenderType Y 2 3 e) {B : Subgroup (MulAut Y)} {β : MulAut Y}
    (hB2 : ∀ b ∈ B, b * b = 1) (hβB : β ∈ B) (hβ2 : β * β = 1)
    (hout : ¬ ∃ g : Y, ∀ x : Y, β x = g * x * g⁻¹) :
    ∀ b ∈ B, (∀ y ∈ autFixed β, b y = y) → b = 1 ∨ b = β := by
  intro b hb hfix
  have hcomm : b * β = β * b := CFSG.commute_of_sq_eq_one (by rw [pow_two]; exact hB2 b hb)
    (by rw [pow_two]; exact hβ2) (by rw [pow_two]; exact hB2 (b * β) (B.mul_mem hb hβB))
  exact hBen.centralizer_unitary β hβ2 hout b hcomm hfix

theorem fourFacts_of_psu34 {Y : Type} [Group Y]
    (hY : LieModel Y .PSU 3 2 2) : FourFacts Y := by
  intro B hB4 hB2 hBnot
  obtain ⟨β, hβB, hβout⟩ := Set.not_subset.mp hBnot
  have hβ2 : β * β = 1 := hB2 β hβB
  let β₀ : MulAut SU3 := suField unitaryFieldData_GF16 unitaryFieldData_GF16.barEquiv
  obtain ⟨Φ, hΦβ⟩ := exists_congr_fieldAut (Y := Y) hY hβ2 hβout
  have hfin : Finite Y := Finite.of_injective (Φ.symm : Y → SU3) Φ.symm.injective
  have hfix : autFixed β = (autFixed β₀).map Φ.toMonoidHom := by
    rw [← hΦβ]
    exact autFixed_congr Φ β₀
  obtain ⟨e₁⟩ := CFSG.GH74.KGroups.equiv_psu3_of_lieModel_even (f := 2) (by norm_num) hY
  have hBen : BenderType Y 2 3 ((2 ^ 2 + 1) / Nat.gcd 3 (2 ^ 2 + 1)) :=
    .unitary 2 le_rfl e₁
  have hout : ¬ ∃ g : Y, ∀ x : Y, β x = g * x * g⁻¹ := by
    rintro ⟨g, hg⟩
    exact hβout ⟨g, MulEquiv.ext fun x => (hg x).symm⟩
  haveI := hfin
  have hs : IsSimpleGroup (autFixed β) := isSimple_autFixed hBen hβ2 hout
  have hc := centralizer_autFixed hBen hB2 hβB hβ2 hout
  have hle : autFixed β ≤ commY B β := autFixed_le_commY hB4 hB2 hβB hs hc
  obtain ⟨x₀, hord, h₁, h₂⟩ := U34.exists_fourGenWith
  have hord' : orderOf (β * (MulAut.conj (Φ x₀) * β *
      (MulAut.conj (Φ x₀))⁻¹)) = 4 := by
    rw [← hΦβ, orderOf_congr_mul_conj Φ β₀ x₀, hord]
  refine ⟨β, hβB, Φ x₀, ?_, ?_, ?_, ?_⟩
  · rw [hord']
    exact ⟨2, by norm_num⟩
  · rw [hord']
  · have hmap : FourGenWith (autFixed β) β (Φ x₀) := by
      have h := FourGenWith.map Φ h₁
      rwa [hΦβ, ← hfix] at h
    exact FourGenWith.fourGen hle hmap
  · have hmap : FourGenWith (autFixed β) β ((Φ x₀)⁻¹) := by
      have h := FourGenWith.map Φ h₂
      rw [map_inv] at h
      rwa [hΦβ, ← hfix] at h
    exact FourGenWith.fourGen hle hmap

end CFSG.LocalAnalysis.WeakClosure81.Asch6

end
