module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.Hss26ShapeMain
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.BaumannA5
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.BaumannS3

public section

namespace CFSG.Quasithin.F53.SitSigma

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F53Push CFSG.Quasithin.F53Mod CFSG.Quasithin.F7 CosetGeom

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem false_or_orth_of_O2Ubar_trivial (hA : F53Amalgam H M S) (hb : 1 < bMin H M)
    {δ μ : Geo H M} {U : Subgroup G} (hSig : SitSigma δ μ U) (hQ : Qv μ ≤ U)
    (hR : pCoreOf 2 U ≤ Qv δ) :
    False ∨ (Nonempty (OTwoQuot U ≃* Equiv.Perm (Fin 5)) ∧
      IsOrthSec U (zZero U (conjJoinOf U (quasithinOmegaOneCenter (Qv μ))))
        (conjJoinOf U (quasithinOmegaOneCenter (Qv μ)))) :=
  sitSigma_false_of_O2Ubar_trivial (baumannS3_holds G) (baumannA5_holds G) hA hb hSig hQ hR

end CFSG.Quasithin.F53.SitSigma
