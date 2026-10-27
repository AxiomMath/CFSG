module

public import CFSG.Quasithin.Recognition.Stroth.F112Tree
public import CFSG.Quasithin.Background.F3Geometry

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Quasithin.F112R

variable {G : Type} [Group G]

@[expose] noncomputable def caseAZ {L1 L2 S : Subgroup G} (v : f112Gamma L1 L2 S) :
    Subgroup (f112Amalgam L1 L2 S).Ghat :=
  omegaOneCenterOf (CosetGeom.Qy v)

@[expose] noncomputable def caseAX {L1 L2 S : Subgroup G} (v : f112Gamma L1 L2 S) :
    Subgroup (f112Amalgam L1 L2 S).Ghat :=
  ⨆ (w : f112Gamma L1 L2 S) (_ : w ∈ CosetGeom.nbrs v), caseAZ w

@[expose] noncomputable def caseAR {L1 L2 S : Subgroup G} (v : f112Gamma L1 L2 S) :
    Subgroup (f112Amalgam L1 L2 S).Ghat :=
  ⨆ (w : f112Gamma L1 L2 S) (_ : w ∈ CosetGeom.nbrs v), caseAX w

@[expose] def caseABoundAt (L1 L2 S : Subgroup G) (k : ℕ) : Prop :=
  ∀ β δ : f112Gamma L1 L2 S, CosetGeom.vtype β = true → CosetGeom.dist β δ ≤ k →
    caseAZ β ≤ CosetGeom.Qy δ

@[expose] noncomputable def caseAB (L1 L2 S : Subgroup G) : ℕ :=
  sInf {n | ∃ β δ : f112Gamma L1 L2 S, CosetGeom.vtype β = true ∧ CosetGeom.dist β δ = n ∧
    ¬ caseAZ β ≤ CosetGeom.Qy δ}

end CFSG.Quasithin.Stroth

end
