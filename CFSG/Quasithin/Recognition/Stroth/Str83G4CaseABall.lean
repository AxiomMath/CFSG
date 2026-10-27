module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.Recognition.Stroth.Str83G4CaseADefs
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Quasithin.F112R

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G}

theorem caseA_X_le_Qy {k : ℕ} (hb : caseABoundAt L1 L2 S k) {α ε : f112Gamma L1 L2 S}
    (hα : CosetGeom.vtype α = false) (hd : CosetGeom.dist α ε + 1 ≤ k) :
    caseAX α ≤ CosetGeom.Qy ε := by
  unfold caseAX
  refine iSup₂_le fun w hw => ?_
  have hwv : CosetGeom.vtype w = true := by
    have hne := CosetGeom.vtype_ne_of_adj hw
    rw [hα] at hne
    cases h : CosetGeom.vtype w <;> simp_all
  refine hb w ε hwv ?_
  have htri := CosetGeom.dist_triangle_of_adj hw.symm ε
  have hwα : CosetGeom.dist w α = 1 := CosetGeom.dist_eq_one_iff_adj.mpr hw.symm
  omega

theorem caseA_R_le_Qy {k : ℕ} (hb : caseABoundAt L1 L2 S k) {β ε : f112Gamma L1 L2 S}
    (hβ : CosetGeom.vtype β = true) (hd : CosetGeom.dist β ε + 2 ≤ k) :
    caseAR β ≤ CosetGeom.Qy ε := by
  unfold caseAR
  refine iSup₂_le fun w hw => ?_
  have hwv : CosetGeom.vtype w = false := by
    have hne := CosetGeom.vtype_ne_of_adj hw
    rw [hβ] at hne
    cases h : CosetGeom.vtype w <;> simp_all
  refine caseA_X_le_Qy hb hwv ?_
  have htri := CosetGeom.dist_triangle_of_adj hw.symm ε
  have hwβ : CosetGeom.dist w β = 1 := CosetGeom.dist_eq_one_iff_adj.mpr hw.symm
  omega

theorem caseA_commute_Z {k : ℕ} (hb : caseABoundAt L1 L2 S k) {β β' : f112Gamma L1 L2 S}
    (hβ : CosetGeom.vtype β = true) (hβ' : CosetGeom.vtype β' = true)
    (h : CosetGeom.dist β β' ≤ k) {x y : (f112Amalgam L1 L2 S).Ghat}
    (hx : x ∈ caseAZ β) (hy : y ∈ caseAZ β') : Commute x y := by
  have hxQ : x ∈ CosetGeom.Qy β' := hb β β' hβ h hx
  have hyC : y ∈ centerOf (CosetGeom.Qy β') :=
    CFSG.Quasithin.A4.omegaOneCenterOf_le_centerOf (CosetGeom.Qy β') hy
  have hycent : y ∈ Subgroup.centralizer
      (CosetGeom.Qy β' : Set (f112Amalgam L1 L2 S).Ghat) :=
    (Subgroup.mem_inf.mp hyC).2
  exact Subgroup.mem_centralizer_iff.mp hycent x hxQ

end CFSG.Quasithin.Stroth

end
