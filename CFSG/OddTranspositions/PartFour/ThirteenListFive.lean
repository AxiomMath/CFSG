module

public import CFSG.LocalAnalysis.WeakClosure81.OddTranspListDerivedCases
public import CFSG.OddTranspositions.PartFour.ThirteenListFiveForm
public import Certificates.Certificate1
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate42
public import Certificates.Certificate43
public import Certificates.Certificate44
public import Certificates.Certificate1383001
public import Certificates.Certificate1383002
public import Certificates.Certificate1383003
public import Certificates.Certificate1383004
public import Certificates.Certificate1383005
public import Certificates.Certificate1383006
public import Certificates.Certificate1383007
public import Certificates.Certificate1383008
public import Certificates.Certificate1383009
import CFSG.OddTranspositions.PartFour.ThirteenListFiveEmbed
import CFSG.OddTranspositions.PartFour.ThirteenListFiveLift
import CFSG.OddTranspositions.PartFour.ThirteenList
import CFSG.OddTranspositions.PartThree.Eleven.Minus.Pair
import CFSG.OddTranspositions.PartThree.Eleven.MinusModel
import CFSG.OddTranspositions.PartThree.Eleven.PlusWreath
import CFSG.OddTranspositions.PartThree.FiveReflectionFischerConverse
import CFSG.Timmesfeld.Bridge.Asc72YCount
public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenInputs
import CFSG.CGT.T75E.Lemma26
import CFSG.CGT.Timmesfeld75.Sec3TenCaseA
import CFSG.CGT.Timmesfeld75.Sec4CaseIBasic
import CFSG.CGT.Timmesfeld75.Sec4CaseIIIFour
import CFSG.CGT.Timmesfeld75.Sec4CaseIJFamily
import CFSG.CGT.Timmesfeld75.Sec4CaseIJIdent
import CFSG.CGT.Timmesfeld75.Sec4CaseIPGroup
import CFSG.CGT.Timmesfeld75.Sec4CaseIPartition4
import CFSG.CGT.Timmesfeld75.Sec4Three
import CFSG.CGT.Timmesfeld75.Sec5FiveEng
import CFSG.CGT.Timmesfeld75.Step511Card
import CFSG.CGT.Timmesfeld75.Step57Reduction
import CFSG.GH74.Uniqueness.Bender.OddCentralizer
import CFSG.GH74.Uniqueness.Bender.Unitary
import CFSG.LocalAnalysis.ComponentClassification.Asc76BenderFacts
import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3GoldschmidtFacts
import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvUnitary
import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderAutE4Unitary
import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderONan
import CFSG.OddTranspositions.PartFour.Fourteen.Statements
import CFSG.OddTranspositions.PartFour.Statements
import CFSG.OddTranspositions.PartThree.Eleven.PlusModel
import CFSG.RankThree.GF2n.Tim79aSec23Inputs
import CFSG.RankThree.GF2n.Tim79aSec23NoSqE1
import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Defs

public section

namespace CFSG.OddTranspositions.PartFour.ListFive

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.OddTranspositions.PartThree CFSG.LocalAnalysis.WeakClosure81
open CFSG.OddTranspositions.PartFour.TableE1Five


private instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

private theorem eq_of_mem_zpowers_of_ne_one {X : Type} [Group X] {s x : X} (hs : orderOf s = 2)
    (hx : x ∈ Subgroup.zpowers s) (hx1 : x ≠ 1) : x = s := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← zpow_mod_orderOf, hs, Nat.cast_ofNat] at hx1 ⊢
  rcases Int.emod_two_eq k with h | h
  · rw [h, zpow_zero] at hx1
    exact absurd rfl hx1
  · rw [h, zpow_one]

theorem exists_sevenNine_of_injective {X : Type} [Group X] [Finite X] {s : X}
    (hs : orderOf s = 2) (hZ : Odd (Nat.card (Subgroup.center X)))
    (ψ : fiveReflectionGroup 3 false true →* X ⧸ Subgroup.center X)
    (hψ : Function.Injective ψ) {r₀ : fiveReflectionGroup 3 false true}
    (hr₀ : (r₀ : GL (Fin (3 + 1)) (ZMod 5)) ∈ fiveReflections 3 false true)
    (hψs : ψ r₀ = QuotientGroup.mk s) :
    ∃ L : Subgroup X, s ∈ L ∧
      IsSevenNineGroup ↥L {x : ↥L | (x : X) ∈ Subgroup.zpowers s ∧ x ≠ 1} := by
  have hcR : Subgroup.center (fiveReflectionGroup 3 false true) = ⊥ := by
    have h := center_reflGroup_minusBilin
    rw [reflGroup_minusBilin] at h
    exact h
  obtain ⟨e₁, he₁⟩ := exists_minusRealize true
  let ρ : fiveReflectionGroup 3 false true ≃* minusPerm :=
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hcR.symm)).trans e₁
  have hρ : ∀ r, ρ r = e₁ (QuotientGroup.mk r) := fun r => rfl
  have hρr₀ : ρ r₀ ∈ minusClass := by
    rw [← he₁, hρ]
    exact ⟨_, ⟨r₀, hr₀, rfl⟩, rfl⟩
  have hcomm : (commutator (fiveReflectionGroup 3 false true)).map ρ.toMonoidHom = minusL := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top_of_surjective _ ρ.surjective, ← commutator_def,
      minusL_eq_commutator]
  have hmem : ∀ r, r ∈ commutator (fiveReflectionGroup 3 false true) ↔ ρ r ∈ minusL := fun r => by
    rw [← hcomm]
    exact (Subgroup.mem_map_iff_mem ρ.injective).symm
  have hr₀C : r₀ ∉ commutator (fiveReflectionGroup 3 false true) := fun h =>
    not_mem_minusL_of_mem_minusClass hρr₀ ((hmem r₀).mp h)
  have htop : (⊤ : Subgroup (fiveReflectionGroup 3 false true)) =
      commutator (fiveReflectionGroup 3 false true) ⊔ Subgroup.zpowers r₀ := by
    refine (eq_top_iff.mpr fun r _ => ?_).symm
    by_cases hr : r ∈ commutator (fiveReflectionGroup 3 false true)
    · exact Subgroup.mem_sup_left hr
    · have hrr : r * r₀ ∈ commutator (fiveReflectionGroup 3 false true) := by
        rw [hmem, map_mul]
        exact (Subgroup.mul_mem_iff_of_index_two index_minusL).mpr
          (iff_of_false (fun h => hr ((hmem r).mpr h)) (fun h => hr₀C ((hmem r₀).mpr h)))
      have : r = r * r₀ * r₀⁻¹ := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hrr)
        (Subgroup.mem_sup_right (Subgroup.inv_mem _ (Subgroup.mem_zpowers r₀)))
  obtain ⟨eL⟩ := nonempty_minusL_mulEquiv_psl225
  obtain ⟨C, hC⟩ : ∃ C : Subgroup (X ⧸ Subgroup.center X),
      C = (commutator (fiveReflectionGroup 3 false true)).map ψ := ⟨_, rfl⟩
  let eC : C ≃* QZ.PSL225 :=
    ((MulEquiv.subgroupCongr hC).trans
      (Subgroup.equivMapOfInjective (commutator (fiveReflectionGroup 3 false true)) ψ
        hψ).symm).trans
      (((Subgroup.equivMapOfInjective (commutator (fiveReflectionGroup 3 false true)) ρ.toMonoidHom
        ρ.injective).trans (MulEquiv.subgroupCongr hcomm)).trans eL)
  have hsC : (QuotientGroup.mk s : X ⧸ Subgroup.center X) ∈ Subgroup.normalizer C := by
    rw [hC, ← hψs]
    refine Subgroup.le_normalizer_map ψ ⟨r₀, ?_, rfl⟩
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top r₀
  have hs2 : s * s = 1 := by rw [← pow_two, ← hs, pow_orderOf_eq_one]
  have hK : Nat.card QZ.K25 = 5 ^ 2 := GaloisField.card 5 2 (by norm_num)
  obtain ⟨L, hsL, hLZ, hLmap⟩ := exists_lift_of_psl_two hZ hs2 (p := 5) (f := 2) (by norm_num) hK
    (by norm_num) (by rw [hK]; norm_num) C eC hsC
  have hrange : ψ.range = C ⊔ Subgroup.zpowers (QuotientGroup.mk s) := by
    rw [MonoidHom.range_eq_map, htop, Subgroup.map_sup, MonoidHom.map_zpowers, hψs, hC]
  have hinj : Function.Injective ((QuotientGroup.mk' (Subgroup.center X)).comp L.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxZ : (x : X) ∈ Subgroup.center X := (QuotientGroup.eq_one_iff _).mp hx
    have : (x : X) ∈ L ⊓ Subgroup.center X := Subgroup.mem_inf.mpr ⟨x.2, hxZ⟩
    rw [hLZ] at this
    exact Subtype.ext (Subgroup.mem_bot.mp this)
  have hLrange : ((QuotientGroup.mk' (Subgroup.center X)).comp L.subtype).range = ψ.range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hLmap, hrange]
  let κ : L ≃* ψ.range :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hLrange)
  let θ : fiveReflectionGroup 3 false true ≃* ψ.range := MonoidHom.ofInjective hψ
  let e : L ≃* fiveReflectionGroup 3 false true := κ.trans θ.symm
  have hes : e ⟨s, hsL⟩ = r₀ := by
    apply θ.injective
    show θ (θ.symm (κ ⟨s, hsL⟩)) = θ r₀
    rw [MulEquiv.apply_symm_apply]
    exact Subtype.ext hψs.symm
  refine ⟨L, hsL, isSevenNineGroup_of_mulEquiv (e.trans (MulEquiv.subgroupCongr
    reflGroup_minusBilin.symm)) fun d hd => ?_⟩
  have hds : d = ⟨s, hsL⟩ :=
    Subtype.ext (eq_of_mem_zpowers_of_ne_one hs hd.1 fun h => hd.2 (Subtype.ext h))
  rw [hds, reflSet_minusBilin]
  change ((e ⟨s, hsL⟩ : fiveReflectionGroup 3 false true) : GL (Fin (3 + 1)) (ZMod 5)) ∈
    fiveReflections 3 false true
  rw [hes]
  exact hr₀

theorem oddTranspListDerivedEqOFive_of_models : OddTranspListDerivedEqOFive := by
  intro X _ _ s hs _ _ hpc _ _ ⟨n, hn, b, hsym, hnd, φ, hφ⟩
  have hZ : Odd (Nat.card (Subgroup.center X)) :=
    CFSG.Timmesfeld.Bridge.Asc72.CentralQuot.odd_card_center hpc
  obtain ⟨h₀, hh₀T, hφs⟩ := (hφ (QuotientGroup.mk s)).mp (IsConj.refl _)
  rcases (show n = 4 ∨ 5 ≤ n by omega) with rfl | hn5
  · obtain ⟨ε, hε⟩ := exists_isFiveReflectionModel_of_fischerModel (k := 3) hsym hnd ⟨φ, hφ⟩
    obtain ⟨φ', hφ'⟩ := hε
    obtain ⟨h₁, hh₁, hφ's⟩ := (hφ' (QuotientGroup.mk s)).mp (IsConj.refl _)
    cases ε
    ·
      have hcR : Subgroup.center (fiveReflectionGroup 3 false true) = ⊥ :=
        reflGroup_minusBilin ▸ center_reflGroup_minusBilin
      refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
      refine exists_sevenNine_of_injective hs hZ
        (φ'.symm.toMonoidHom.comp (QuotientGroup.mk' _)) ?_ hh₁ ?_
      · refine φ'.symm.injective.comp fun r r' h => ?_
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, hcR,
          Subgroup.mem_bot] at h
        exact inv_mul_eq_one.mp h
      · rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, ← hφ's, MulEquiv.coe_toMonoidHom,
          MulEquiv.symm_apply_apply]
    ·
      obtain ⟨e, he⟩ := exists_plusRealize true
      obtain ⟨Ψ, hΨ⟩ := exists_l2WreathTwoTwo_mulEquiv_plusPerm
      have hmem : e (φ' (QuotientGroup.mk s)) ∈ Ψ '' {x | IsConj
          (SemidirectProduct.inr (Equiv.swap 0 1)) x} := by
        rw [hΨ, ← he, hφ's]
        exact ⟨_, ⟨h₁, hh₁, rfl⟩, rfl⟩
      obtain ⟨w, hw, hwe⟩ := hmem
      refine Or.inl ⟨2, 2, Or.inr (Or.inr (Or.inr ?_))⟩
      refine isWreathTransposition_of_isConj le_rfl (φ'.trans (e.trans Ψ.symm))
        (i := 0) (j := 1) (by decide) ?_
      rw [MulEquiv.trans_apply, MulEquiv.trans_apply, ← hwe, MulEquiv.symm_apply_apply]
      exact hw
  ·
    obtain ⟨v, hv, hvh⟩ := mem_reflSet_iff.mp hh₀T
    obtain ⟨ψ, hψ, hψe⟩ := exists_injective_reflGroup_minusBilin hsym hnd hn5 hv
    refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
    refine exists_sevenNine_of_injective hs hZ
      ((φ.symm.toMonoidHom.comp ψ).comp
        (MulEquiv.subgroupCongr reflGroup_minusBilin).symm.toMonoidHom)
      ((φ.symm.injective.comp hψ).comp (MulEquiv.subgroupCongr reflGroup_minusBilin).symm.injective)
      (r₀ := MulEquiv.subgroupCongr reflGroup_minusBilin
        ⟨refl minusBilin (Pi.single 0 1), refl_mem_reflGroup _⟩) ?_ ?_
    · change refl minusBilin (Pi.single 0 1) ∈ fiveReflections 3 false true
      rw [← reflSet_minusBilin]
      exact refl_mem_reflSet minusBilin_single_zero
    · change φ.symm (ψ ((MulEquiv.subgroupCongr reflGroup_minusBilin).symm
        (MulEquiv.subgroupCongr reflGroup_minusBilin
          ⟨refl minusBilin (Pi.single 0 1), refl_mem_reflGroup _⟩))) = _
      rw [MulEquiv.symm_apply_apply, hψe]
      have hh : (⟨refl b v, refl_mem_reflGroup v⟩ : reflGroup b) = h₀ := Subtype.ext hvh
      rw [hh]
      have h := congrArg φ.symm hφs
      rw [MulEquiv.symm_apply_apply] at h
      exact h.symm

end CFSG.OddTranspositions.PartFour.ListFive
