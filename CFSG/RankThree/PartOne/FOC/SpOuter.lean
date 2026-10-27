module

public import CFSG.RankThree.PartOne.FOC.Assemble
public import CFSG.RankThree.PartOne.FOC.CompCommutator
public import CFSG.RankThree.PartOne.FOC.SpInner
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogQuadraticDescent
import CFSG.RankThree.PartOne.S11c.Sec66TFamily
public import CFSG.Monster.B.TwoA.Base.ElemAut
import CFSG.RankThree.PartOne.KC.SymplecticSubfieldRadical

public section

namespace CFSG.RankThree.PartOne.FOC

open Subgroup CFSG
open CFSG.RankThree.PartOne.Sec66T (fixSub innerAut mem_fixSub fixSubEquiv congr_self_eq)
open CFSG.RankThree.PartOne.KCSpComm
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.UnbalancedCatalog (descentField)
open CFSG.ComponentClassification.PresentationLocal (sympFour)
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)

variable {K : Type} [Field K] [Finite K] {r : ℕ}

theorem fixedGroup_equiv {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    (hr : 2 ≤ r) (hp : p.Prime) (hp2 : p ≠ 2) {β : MulAut (StatedProj (StatedSp r K))}
    (hβp : β ^ p = 1) (hβ : β ∉ innerAut (StatedProj (StatedSp r K))) :
    ∃ σ : K ≃+* K, σ ^ p = 1 ∧
      Nonempty (↥(fixSub β) ≃* StatedProj (StatedSp r (descentField σ))) := by
  have : NeZero r := ⟨by omega⟩
  have : Fact p.Prime := ⟨hp⟩
  have O := spOuter hℓ hf hr hK
  have hβ1 : β ≠ 1 := fun h => hβ (h ▸ Subgroup.one_mem _)
  have hord : orderOf β = p := orderOf_eq_prime hβp hβ1
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hβE : β ∈ spSemilinearAutGroup r K :=
    mem_of_odd_orderOf_of_index_dvd_two _ O.index_dvd (by rw [hord]; exact hodd)
  have hβD : β ∉ spLinearAutGroup r K := fun hD =>
    hβ (by
      have := inner_normal (StatedProj (StatedSp r K))
      exact mem_of_pow_eq_one_of_relIndex_dvd_two
        (O.relIndex_dvd.trans (Nat.gcd_dvd_left 2 _)) hp hp2 hD hβp)
  obtain ⟨-, σ, hσ, h, -, hβeq⟩ := O.descent p hp β hβE hβD hord
  have hσp : σ ^ p = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  refine ⟨σ, hσp, ⟨?_⟩⟩
  have hcongr : MulAut.congr (h : StatedProj (StatedSp r K) ≃* StatedProj (StatedSp r K))
      (fieldAut r K σ) = β := (congr_self_eq h _).trans hβeq.symm
  have e1 : ↥(fixSub (fieldAut r K σ)) ≃* ↥(fixSub β) :=
    (fixSubEquiv (h : StatedProj (StatedSp r K) ≃* StatedProj (StatedSp r K))
      (fieldAut r K σ)).trans (MulEquiv.subgroupCongr (congrArg fixSub hcongr))
  have h1 : fixSub (fieldAut r K σ) = (subfieldInj (r := r) σ).range := by
    rw [range_subfieldInj, ← spFixedGroup_fieldAut_eq_range hodd hσp]
    exact Subgroup.ext fun _ => Iff.rfl
  have e2 : ↥(fixSub (fieldAut r K σ)) ≃* StatedProj (StatedSp r (descentField σ)) :=
    (MulEquiv.subgroupCongr h1).trans (MonoidHom.ofInjective (subfieldInj_injective σ)).symm
  exact e1.symm.trans e2

theorem outerComp_sp {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    (hr : 2 ≤ r) (hp : p.Prime) (hp2 : p ≠ 2) : OuterComp p (StatedProj (StatedSp r K)) := by
  intro _ β hβp hβ _ y hβy hyp E hE
  obtain ⟨σ, hσp, ⟨e⟩⟩ := fixedGroup_equiv hℓ hf hK hr hp hp2 hβp hβ
  have : NeZero r := ⟨by omega⟩
  by_cases hex : r = 2 ∧ Nat.card (descentField σ) = 2
  · obtain ⟨rfl, hk⟩ := hex
    have e' : ↥(fixSub β) ≃* sympFour := e.trans (statedProjEquivSympFour hk)
    obtain ⟨hq, hodd⟩ := derived_of_mulEquiv_sympFour e'
    have hyF : y ∈ fixSub β := hβy
    refine mem_of_isComponentOf_of_mem_commutator hq hE hyF (hodd hp hp2 ⟨y, hyF⟩ ?_)
    exact Subtype.ext (by simpa using hyp)
  · obtain ⟨hs, -⟩ := simple_perfect_statedProj (k := descentField σ) hr hex
    have : IsSimpleGroup (StatedProj (StatedSp r (descentField σ))) := hs
    have : IsSimpleGroup ↥(fixSub β) := e.isSimpleGroup
    have hEeq := eq_of_isComponentOf_simple hE
    rw [hEeq]
    exact hβy

theorem innerComp_sp {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    (hr : 2 ≤ r) (hrq : ¬ (r = 2 ∧ ℓ ^ f = 2)) (hp : p.Prime) (hp5 : 5 ≤ p) (hpℓ : p ≠ ℓ) :
    InnerComp p (StatedProj (StatedSp r K)) :=
  fun hrank _ _ hbp hyp hby _ hE =>
    mem_sup_centralizer_of_component_sp hℓ hf hK hr hrq hp hp5 hpℓ hrank hbp hyp hby hE

theorem fieldInnerT_sp {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    (hr : 2 ≤ r) (hrq : ¬ (r = 2 ∧ ℓ ^ f = 2)) (hp : p.Prime) (hp5 : 5 ≤ p) (hpℓ : p ≠ ℓ)
    (hs : IsSimpleGroup (StatedProj (StatedSp r K)))
    (hnab : ∃ a b : StatedProj (StatedSp r K), a * b ≠ b * a) :
    FieldInnerT p (StatedProj (StatedSp r K)) :=
  fieldInnerT_of_comp (center_eq_bot_of_nonab hs hnab) (innerComp_sp hℓ hf hK hr hrq hp hp5 hpℓ)
    (outerComp_sp hℓ hf hK hr hp (by omega))

end CFSG.RankThree.PartOne.FOC
