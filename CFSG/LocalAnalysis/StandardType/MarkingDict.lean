module

public import CFSG.Assembly.LargeEvenDefs
public import CFSG.Blueprint.Catalog
public import CFSG.Open.StatedAPI

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint

@[expose] def markTag (lab : LargeEvenLabel) : StatedLieTag :=
  match lab.tag with
  | .A => .PSL
  | .twA => .PSU
  | .B | .C => .PSp
  | .D => if lab.rank = 3 then .PSL else .POmegaPlus
  | .twD => if lab.rank = 2 then .PSL else if lab.rank = 3 then .PSU else .POmegaMinus
  | .E6 => .E6
  | .E7 => .E7
  | .E8 => .E8
  | .F4 => .F4
  | .G2 => .G2
  | .twE6 => .twistedE6
  | .triD4 => .trialityD4
  | .twB2 => .twistedB2
  | .twF4 => .twistedF4
  | .B2der => .PSL
  | .G2der => .PSU
  | .twF4der => .Tits

@[expose] def markRank (lab : LargeEvenLabel) : ℕ :=
  match lab.tag with
  | .A | .twA => lab.rank + 1
  | .B | .C => lab.rank
  | .D => if lab.rank = 3 then 4 else lab.rank
  | .twD => if lab.rank = 2 then 2 else if lab.rank = 3 then 4 else lab.rank
  | .B2der => 2
  | .G2der => 3
  | _ => 0

@[expose] def markChar (lab : LargeEvenLabel) : ℕ :=
  match lab.tag with
  | .B2der | .G2der => 3
  | _ => 2

@[expose] def markDeg (lab : LargeEvenLabel) : ℕ :=
  match lab.tag with
  | .twD => if lab.rank = 2 then 2 * lab.n else lab.n
  | .B2der => 2
  | .G2der => 1
  | _ => lab.n

@[expose] def MarkedModel (lab : LargeEvenLabel) (R : Type) [Group R] : Prop :=
  LieModel R (markTag lab) (markRank lab) (markChar lab) (markDeg lab)

theorem statedClassicalModel_of_mulEquiv' {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    {t : StatedLieTag} {n p f : ℕ} (h : StatedClassicalModel G t n p f) :
    StatedClassicalModel G' t n p f :=
  CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e h

theorem lieModel_of_mulEquiv' {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    {t : StatedLieTag} {n p f : ℕ} (h : LieModel G t n p f) : LieModel G' t n p f :=
  CFSG.Blueprint.LieModel.of_mulEquiv e h

theorem MarkedModel.of_mulEquiv {lab : LargeEvenLabel} {R R' : Type} [Group R] [Group R']
    (e : R ≃* R') (h : MarkedModel lab R) : MarkedModel lab R' :=
  lieModel_of_mulEquiv' e h

theorem MarkedModel.catalog {lab : LargeEvenLabel} {R : Type} [Group R]
    (h : MarkedModel lab R) : Catalog R :=
  lieModel_catalog R _ _ _ _ h

end CFSG.StandardType
