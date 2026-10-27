module

public import CFSG.LocalAnalysis.WeakClosure81.Asc80BOdd
public import CFSG.LocalAnalysis.WeakClosure81.Asc80BExcTwE6Four
import CFSG.LieType.SeitzGeneration.TwistedOuterLocal
import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalDihedralTwisted
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSL
import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.Bridge

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration
open CFSG.ComponentClassification.UnbalancingLocal.DihedralTwisted


theorem seitzFour_twistedE6 :
    SeitzFour fun X _ => ∃ p f : ℕ, p ≠ 2 ∧ CFSG.Models.LieModel X .twistedE6 0 p f := by
  intro G _ _ L E hLn hLs hnab hP hC hE h4 _
  obtain ⟨p, f, hp2, hm⟩ := hP
  obtain ⟨hadm, hT⟩ :=
    (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.blueprintLieModel_of_models
      hm).chevalleyExceptionalModel (by decide)
  obtain ⟨K, _, _, hcard, σ, hσ, ⟨e⟩⟩ := hT
  set σ' : K ≃+* K :=
    RingEquiv.ofBijective σ ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩
    with hσ'def
  have hσσ' : σ'.toRingHom = σ := RingHom.ext fun _ => rfl
  have hσ'q : ∀ c, σ' c = c ^ (p ^ f) := fun c => hσ c
  have hcard2 : Nat.card K = (p ^ f) ^ 2 := hcard
  have hemodel : ↥L ≃* DerivedCentralQuotient
      (twistedFixedGroup TwistTag.E6 K σ'.toRingHom) := by
    rw [hσσ']
    exact e
  obtain ⟨φ⟩ :=
    nonempty_mulEquiv_graphFixedRootGroup' (σ := σ'.toRingHom) TwistTag.E6 hadm.1 hadm.2.1
      hcard hσ'q hemodel
  set A := E.map (MulAut.conjNormal : G →* MulAut ↥L)
  have hA : CFSG.Open.IsElemAbelian 2 A := hE.map _
  have hA4 : Nat.card A = 4 := by
    rw [Subgroup.card_map_of_injective (conjNormal_injective_of_centralizer_eq_bot hC), h4]
  set A' := A.map (MulAut.congr φ).toMonoidHom
  have hA' : CFSG.Open.IsElemAbelian 2 A' := hA.map _
  have hA'4 : Nat.card A' = 4 := by
    rw [Subgroup.card_map_of_injective (MulAut.congr φ).injective, hA4]
  have hKp : Nat.card K = p ^ (2 * f) := by rw [hcard2, ← pow_mul, mul_comm]
  have h1f : 1 ≤ 2 * f := by
    have := hadm.2.1
    omega
  have hcharp : CharP K p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      (p := p) (k := 2 * f) hadm.1 h1f hKp
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  obtain ⟨R, hR, hRr, hER⟩ :=
    exists_normalized_rSubgroup_four_twistedE6 σ' (p ^ f) hσ'q hcard2 hK2 A' hA' hA'4
  have hKr : Nat.card K = (ringChar K ^ f) ^ 2 := by rw [hcard2, ringChar.eq K p]
  have hσ'r : ∀ c, σ' c = c ^ (ringChar K ^ f) := by
    intro c
    rw [hσ'q c, ringChar.eq K p]
  have hcharK : CharP K (ringChar K) := ringChar.charP K
  have hprimeK : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K (ringChar K)⟩
  have hsimple : IsSimpleGroup ↥(graphFixedRootGroup TwistTag.E6 K σ'.toRingHom) :=
    φ.symm.isSimpleGroup
  have hPA' : PlaneGen A' :=
    planeGen_of_normalized_rSubgroup_twistedE6 hK2 hadm.2.1 hKr σ' hσ'r A' hA' hA'4 R hR hRr
      hER
  have hPA : PlaneGen A := (planeGen_map_congr φ A).1 hPA'
  exact iSup_centralizer_eq_of_seitzHyperGamma hC h4
    ((planeGen_iff_seitzHyperGamma Nat.prime_two (by rw [hA4]; norm_num)).1 hPA)

end CFSG.LocalAnalysis.WeakClosure81
