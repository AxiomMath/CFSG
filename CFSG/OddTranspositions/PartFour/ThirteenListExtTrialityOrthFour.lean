module

public import CFSG.OddTranspositions.PartFour.ThirteenListExtTrialityDerived
public import CFSG.OddTranspositions.PartFour.ThirteenListExtTrialityOrthFourGraph
public import CFSG.OddTranspositions.PartFour.ThirteenListExtTrialityOrthFourEquiv
public import CFSG.CGT.T75E.Lemma26
public import CFSG.CGT.Timmesfeld75.Sec3TenCaseA
public import CFSG.CGT.Timmesfeld75.Sec4CaseIBasic
public import CFSG.CGT.Timmesfeld75.Sec4CaseIIIFour
public import CFSG.CGT.Timmesfeld75.Sec4CaseIJFamily
public import CFSG.CGT.Timmesfeld75.Sec4CaseIJIdent
public import CFSG.CGT.Timmesfeld75.Sec4CaseIPGroup
public import CFSG.CGT.Timmesfeld75.Sec4CaseIPartition4
public import CFSG.CGT.Timmesfeld75.Sec4Three
public import CFSG.CGT.Timmesfeld75.Sec5FiveEng
public import CFSG.CGT.Timmesfeld75.Step511Card
public import CFSG.CGT.Timmesfeld75.Step57Reduction
public import CFSG.Combinatorics.AperiodicCentralInvolution
public import CFSG.Combinatorics.AperiodicFiveOfSix
public import CFSG.Combinatorics.AperiodicOppositeComponents
public import CFSG.Combinatorics.AperiodicSixteenGraphDistances
public import CFSG.Combinatorics.OuterLayerPredecessors
public import CFSG.GH74.Uniqueness.Bender.OddCentralizer
public import CFSG.GH74.Uniqueness.Bender.Unitary
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.Asc76BenderFacts
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupFacts
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3GoldschmidtFacts
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvUnitary
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderAutE4Unitary
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderONan
public import CFSG.LocalAnalysis.WeakClosure81.OddTranspListTriality
public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenInputs
public import CFSG.LocalAnalysis.WeakClosure81.SevenFour
public import CFSG.OddTranspositions.PartFour.Fourteen.Statements
public import CFSG.OddTranspositions.PartFour.Statements
public import CFSG.RankThree.GF2n.Tim79aSec2
public import CFSG.RankThree.GF2n.Tim79aSec23Inputs
public import CFSG.RankThree.GF2n.Tim79aSec23NoSqE1
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Defs

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld.Bridge CFSG.LocalAnalysis.WeakClosure81 CFSG.Open
open CFSG.StandardType CFSG.StandardType.Triality
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.RankThree.PartOne.AUTSL
  CFSG.ComponentClassification.OuterAutomorphisms

namespace ExtTrialityOrthFour

theorem isSwap_of_sq_eq_one (σ : Equiv.Perm (Fin 3)) (h1 : σ ≠ 1) (h2 : σ ^ 2 = 1) :
    σ.IsSwap := by
  have key : ∀ τ : Equiv.Perm (Fin 3), τ ≠ 1 → τ ^ 2 = 1 → τ.support.card = 2 := by decide
  exact Equiv.Perm.card_support_eq_two.1 (key σ h1 h2)

end ExtTrialityOrthFour

open ExtTrialityOrthFour

theorem extTrialityOrthPlusFour_holds : ExtTrialityOrthPlusFour := by
  intro G _ _ t M _ h Y₀ _ _ s₀ n hL hO
  obtain ⟨F, _, _, hF, e₀, he₀⟩ := hO
  have : CharP F 2 := by
    have := Fintype.ofFinite F
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hF])
  obtain ⟨eL, heL⟩ := hL.equiv
  set T : ↥(M ⊔ Subgroup.zpowers t) := ⟨t, Subgroup.mem_sup_right (Subgroup.mem_zpowers t)⟩
    with hT
  let Φ : ↥(M ⊔ Subgroup.zpowers t) ≃* ↥(CFSG.PGLModel.orthogonalPlus 4 F) := eL.symm.trans e₀
  have hΦ : Φ T = e₀ (QuotientGroup.mk s₀) := by
    change e₀ (eL.symm T) = _
    rw [← heL, MulEquiv.symm_apply_apply]
  let Λ := Φ.trans (orthEquiv F)
  let φ := Λ.symm
  let ψ : ↥M ≃* Om8 F := (h.derivedEquiv φ).symm.trans (derivedOm8Equiv F)
  obtain ⟨E, B, hBn, hEi, hBR, hBE⟩ := exists_graph (K := F)
  let ν : G →* MulAut (Om8 F) := (MulAut.congr ψ).toMonoidHom.comp MulAut.conjNormal
  have hνt : ν t = conjAct _ (matrixIsometryInclusion _ (Λ T)) := by
    refine MulEquiv.ext fun y => Subtype.ext ?_
    rw [conjAct_inclusion_val]
    set d := (derivedOm8Equiv F).symm y with hd
    have hy : y = derivedOm8Equiv F d := by rw [hd, MulEquiv.apply_symm_apply]
    have hx : φ (Λ T) = T := Λ.symm_apply_apply T
    have key := h.coe_derivedEquiv_conj φ (Λ T) d
    rw [hx] at key
    have hm : MulAut.conjNormal t (h.derivedEquiv φ d) =
        h.derivedEquiv φ ⟨Λ T * d * (Λ T)⁻¹,
          (derivedSeries_normal _ 1).conj_mem _ d.2 (Λ T)⟩ :=
      Subtype.ext (by rw [MulAut.conjNormal_apply, key])
    have hψs : ψ.symm y = h.derivedEquiv φ d := rfl
    change ((ψ (MulAut.conjNormal t (ψ.symm y)) : Om8 F) : GL (Fin (2 * 4)) F) = _
    rw [hψs, hm]
    change ((derivedOm8Equiv F ((h.derivedEquiv φ).symm (h.derivedEquiv φ _)) : Om8 F) :
      GL (Fin (2 * 4)) F) = _
    rw [MulEquiv.symm_apply_apply, hy]
    rfl
  have hνB : ∀ g, ν g ∈ B := by
    have hle : Subgroup.closure {x : G | IsConj t x} ≤ B.comap ν := by
      rw [Subgroup.closure_le]
      intro x hx
      obtain ⟨c, rfl⟩ := isConj_iff.mp hx
      change ν (c * t * c⁻¹) ∈ B
      rw [map_mul, map_mul, map_inv, hνt]
      exact hBn.conj_mem _ (hBR _) _
    rw [h.setup.gen] at hle
    exact fun g => hle (Subgroup.mem_top g)
  have hker : (E.comp ν).ker = M := by
    ext g
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
    constructor
    · intro hg
      obtain ⟨y, hy⟩ := hBE _ (hνB g) hg
      have hin : (MulAut.conjNormal g : MulAut ↥M) ∈
          CFSG.ComponentClassification.OuterAutomorphisms.inner ↥M := by
        refine ⟨ψ.symm y, MulEquiv.ext fun m => ?_⟩
        have h1 := congrArg (fun α : MulAut (Om8 F) => ψ.symm (α (ψ m))) hy
        simp only [MulAut.conj_apply, map_mul, map_inv, MulEquiv.symm_apply_apply] at h1
        rw [MulAut.conj_apply, h1]
        change ψ.symm (ψ (MulAut.conjNormal g (ψ.symm (ψ m)))) = _
        rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
      rw [← ExtSetting.ker_outerHomG h.centralizer, MonoidHom.mem_ker]
      exact (QuotientGroup.eq_one_iff _).2 hin
    · intro hg
      have : ν g = MulAut.conj (ψ ⟨g, hg⟩) := by
        change MulAut.congr ψ (MulAut.conjNormal g) = _
        rw [show (MulAut.conjNormal g : MulAut ↥M) = MulAut.conj ⟨g, hg⟩ from
          MulAut.conjNormal_val (h := ⟨g, hg⟩), congr_conj]
      rw [this]
      exact hEi ⟨_, rfl⟩
  have ht2 : t ^ 2 = 1 := by
    rw [← h.setup.oddT.1 t (IsConj.refl t)]
    exact pow_orderOf_eq_one t
  have hεt1 : (E.comp ν) t ≠ 1 := fun h1 => h.not_mem (hker ▸ h1)
  have hεt2 : (E.comp ν) t ^ 2 = 1 := by rw [← map_pow, ht2, map_one]
  have hsurj : Function.Surjective (E.comp ν) := by
    have hidx : (E.comp ν).ker.index = Nat.card (E.comp ν).range := Subgroup.index_ker _
    rw [hker] at hidx
    have h6 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by rw [Nat.card_perm, Nat.card_fin]; rfl
    have hdvd : Nat.card (E.comp ν).range ∣ 6 := h6 ▸ Subgroup.card_subgroup_dvd_card _
    have h2 : 2 ∣ Nat.card (E.comp ν).range := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have ho : orderOf ((E.comp ν) t) = 2 := orderOf_eq_prime hεt2 hεt1
      have hx : orderOf (⟨(E.comp ν) t, ⟨t, rfl⟩⟩ : (E.comp ν).range) = 2 := by
        rw [← Subgroup.orderOf_coe]
        exact ho
      have hd := orderOf_dvd_natCard (⟨(E.comp ν) t, ⟨t, rfl⟩⟩ : (E.comp ν).range)
      rwa [hx] at hd
    have hgt : 2 < Nat.card (E.comp ν).range := hidx ▸ h.index
    have hcard : Nat.card (E.comp ν).range = 6 := by
      have hle := Nat.le_of_dvd (by norm_num) hdvd
      interval_cases hc : Nat.card (E.comp ν).range <;> omega
    rw [← MonoidHom.range_eq_top]
    exact Subgroup.eq_top_of_card_eq _ (hcard.trans h6.symm)
  have hsup : (E.comp ν).ker ⊔ Subgroup.zpowers t = M ⊔ Subgroup.zpowers t := by rw [hker]
  let φ' : ↥((E.comp ν).ker ⊔ Subgroup.zpowers t) ≃* ↥(M ⊔ Subgroup.zpowers t) :=
    MulEquiv.subgroupCongr hsup
  have hZ := h.center_eq_bot φ'
  refine ⟨E.comp ν, hsurj, isSwap_of_sq_eq_one _ hεt1 hεt2, by rw [hker]; exact h.centralizer,
    n, F, inferInstance, inferInstance, hF,
    (((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans φ').trans Φ,
    ?_⟩
  have hv : ((((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans
      φ').trans Φ) (QuotientGroup.mk ⟨t, Subgroup.mem_sup_right (Subgroup.mem_zpowers t)⟩) =
        Φ T := rfl
  rw [hv, hΦ]
  exact he₀

end CFSG.OddTranspositions.PartFour
