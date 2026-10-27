module

public import CFSG.Quasithin.Recognition.GoldschmidtStatement
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Quasithin.Recognition.GoldschmidtFan86UnivAct
public import CFSG.Quasithin.Recognition.GoldschmidtGluing

public section

namespace CFSG.Quasithin.Fan86.Univ

open CFSG.Quasithin

@[expose] noncomputable def oTwoQuotMulEquiv {H H' : Type*} [Group H] [Group H'] (e : H ≃* H') :
    oTwoQuot H ≃* oTwoQuot H' :=
  QuotientGroup.congr (Open.pCore 2 H) (Open.pCore 2 H') e
    (CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 e)

theorem isIso_ofSubgroupPair_congr {D : Type*} [Group D] {P P' R R' : Subgroup D} (hP : P = P')
    (hR : R = R') :
    (GoldAmalgam.ofSubgroupPair P R).IsIso (GoldAmalgam.ofSubgroupPair P' R') := by
  subst hP
  subst hR
  exact GoldAmalgam.IsIso.refl _

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] (X : GoldAmalgam A C B)

theorem isIso_ofSubgroupPair_ofRange :
    X.IsIso (GoldAmalgam.ofSubgroupPair X.ofA.range X.ofB.range) := by
  have hinj : Function.Injective (Monoid.PushoutI.base X.diagram) :=
    Monoid.PushoutI.base_injective X.diagram_injective
  have hinf : X.ofA.range ⊓ X.ofB.range = (Monoid.PushoutI.base X.diagram).range :=
    X.ofA_range_inf_ofB_range
  let eC : C ≃* ↥(X.ofA.range ⊓ X.ofB.range) :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hinf.symm)
  refine ⟨⟨MonoidHom.ofInjective X.ofA_injective, eC, MonoidHom.ofInjective X.ofB_injective,
    fun c => ?_, fun c => ?_⟩⟩
  · refine Subtype.ext ?_
    show X.ofA (X.toA c) = Monoid.PushoutI.base X.diagram c
    exact X.ofA_toA c
  · refine Subtype.ext ?_
    show X.ofB (X.toB c) = Monoid.PushoutI.base X.diagram c
    exact X.ofB_toB c

theorem isIso_stabilizer_pair :
    X.IsIso (GoldAmalgam.ofSubgroupPair (MulAction.stabilizer X.Universal (baseA X))
      (MulAction.stabilizer X.Universal (baseB X))) :=
  (isIso_ofSubgroupPair_ofRange X).trans
    (isIso_ofSubgroupPair_congr (stabilizer_baseA X).symm (stabilizer_baseB X).symm)

end CFSG.Quasithin.Fan86.Univ
