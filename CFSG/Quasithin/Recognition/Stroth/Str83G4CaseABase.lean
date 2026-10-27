module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4CaseADefs
public import CFSG.Quasithin.Recognition.Stroth.BenderH7
import CFSG.Quasithin.MS93.PUEquiv
import CFSG.GroupTheory.PCore.OpenTransport
import CFSG.Quasithin.Background.HZ82Base

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Quasithin.F112R

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G}

private theorem pCoreOf_map_iff_mem {X Y H : Type*} [Group X] [Group Y] [Group H]
    (W : Subgroup X) (ι : X →* Y) (hι : Function.Injective ι)
    (P : Subgroup H) (e : W ≃* ↥P) (h : W) :
    (ι (h : X) : Y) ∈ CFSG.Open.pCoreOf 2 (W.map ι) ↔
      (e h : H) ∈ CFSG.Open.pCoreOf 2 P := by
  rw [CFSG.Quasithin.H.ZTrans.pCoreOf_map_of_injective 2 ι hι W, Subgroup.mem_map_iff_mem hι,
    CFSG.mem_openPCoreOf_iff h, CFSG.mem_openPCoreOf_iff (e h),
    ← CFSG.pCore_map_iso 2 e]
  change h ∈ CFSG.pCore 2 W ↔ e.toMonoidHom h ∈ (CFSG.pCore 2 W).map e.toMonoidHom
  rw [Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective]

private theorem omegaOneCenterOf_map_iff_mem {X Y H : Type*} [Group X] [Group Y] [Group H]
    (W : Subgroup X) (ι : X →* Y) (hι : Function.Injective ι)
    (P : Subgroup H) (e : W ≃* ↥P) (h : W) :
    (ι (h : X) : Y) ∈ omegaOneCenterOf (CFSG.Open.pCoreOf 2 (W.map ι)) ↔
      (e h : H) ∈ omegaOneCenterOf (CFSG.Open.pCoreOf 2 P) := by
  rw [CFSG.Quasithin.H.ZTrans.pCoreOf_map_of_injective 2 ι hι W,
    CFSG.Quasithin.MS93.PU.omegaOneCenterOf_map (f := ι) hι (CFSG.Open.pCoreOf 2 W),
    Subgroup.mem_map_iff_mem (f := ι) hι,
    CFSG.openPCoreOf_eq_map_pCore 2 W,
    CFSG.Quasithin.MS93.PU.omegaOneCenterOf_map (f := W.subtype) W.subtype_injective
      (CFSG.pCore 2 W)]
  change W.subtype h ∈ (omegaOneCenterOf (CFSG.pCore 2 W)).map W.subtype ↔
    (e h : H) ∈ omegaOneCenterOf (CFSG.Open.pCoreOf 2 P)
  rw [Subgroup.mem_map_iff_mem (f := W.subtype) W.subtype_injective,
    CFSG.openPCoreOf_eq_map_pCore 2 P,
    CFSG.Quasithin.MS93.PU.omegaOneCenterOf_map (f := P.subtype) P.subtype_injective
      (CFSG.pCore 2 P)]
  change h ∈ omegaOneCenterOf (CFSG.pCore 2 W) ↔
    P.subtype (e h) ∈ (omegaOneCenterOf (CFSG.pCore 2 P)).map P.subtype
  rw [Subgroup.mem_map_iff_mem (f := P.subtype) P.subtype_injective,
    ← CFSG.pCore_map_iso 2 e,
    CFSG.Quasithin.MS93.PU.omegaOneCenterOf_map (f := e.toMonoidHom) e.injective
      (CFSG.pCore 2 W)]
  change h ∈ omegaOneCenterOf (CFSG.pCore 2 W) ↔
    e.toMonoidHom h ∈ (omegaOneCenterOf (CFSG.pCore 2 W)).map e.toMonoidHom
  rw [Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective]

omit [Finite G] in
theorem caseA_stab_γ₀ (L1 L2 S : Subgroup G) :
    CosetGeom.stab (f112Gamma0 L1 L2 S) = (f112Amalgam L1 L2 S).Ghat1 :=
  CosetGeom.stab_γ₀ le_sup_left

omit [Finite G] in
theorem caseA_stab_γ₁ (L1 L2 S : Subgroup G) :
    CosetGeom.stab (f112Gamma1 L1 L2 S) = (f112Amalgam L1 L2 S).Ghat2 :=
  CosetGeom.stab_γ₁ le_sup_right

theorem caseA_mem_Qy_γ₀_iff
    (h : MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma0 L1 L2 S)) :
    ((h : f112Acting L1 L2 S) : (f112Amalgam L1 L2 S).Ghat) ∈
        CosetGeom.Qy (f112Gamma0 L1 L2 S) ↔
      (f112StabEquiv0 L1 L2 S h : G) ∈ Q1 L1 L2 S := by
  change ((h : f112Acting L1 L2 S) : (f112Amalgam L1 L2 S).Ghat) ∈
      CFSG.Open.pCoreOf 2 ((MulAction.stabilizer (f112Acting L1 L2 S)
        (f112Gamma0 L1 L2 S)).map (Subgroup.subtype
          ((f112Amalgam L1 L2 S).Ghat1 ⊔ (f112Amalgam L1 L2 S).Ghat2))) ↔
    (f112StabEquiv0 L1 L2 S h : G) ∈ CFSG.Open.pCoreOf 2 (L1 ⊔ bigB L1 L2 S)
  exact pCoreOf_map_iff_mem
    (MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma0 L1 L2 S))
    (Subgroup.subtype ((f112Amalgam L1 L2 S).Ghat1 ⊔ (f112Amalgam L1 L2 S).Ghat2))
    (Subgroup.subtype_injective _) (L1 ⊔ bigB L1 L2 S) (f112StabEquiv0 L1 L2 S) h

theorem caseA_mem_Z_γ₀_iff
    (h : MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma0 L1 L2 S)) :
    ((h : f112Acting L1 L2 S) : (f112Amalgam L1 L2 S).Ghat) ∈ caseAZ (f112Gamma0 L1 L2 S) ↔
      (f112StabEquiv0 L1 L2 S h : G) ∈ Z1 L1 L2 S := by
  change ((h : f112Acting L1 L2 S) : (f112Amalgam L1 L2 S).Ghat) ∈
      omegaOneCenterOf (CFSG.Open.pCoreOf 2 ((MulAction.stabilizer (f112Acting L1 L2 S)
        (f112Gamma0 L1 L2 S)).map (Subgroup.subtype
          ((f112Amalgam L1 L2 S).Ghat1 ⊔ (f112Amalgam L1 L2 S).Ghat2)))) ↔
    (f112StabEquiv0 L1 L2 S h : G) ∈ omegaOneCenterOf
      (CFSG.Open.pCoreOf 2 (L1 ⊔ bigB L1 L2 S))
  exact omegaOneCenterOf_map_iff_mem
    (MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma0 L1 L2 S))
    (Subgroup.subtype ((f112Amalgam L1 L2 S).Ghat1 ⊔ (f112Amalgam L1 L2 S).Ghat2))
    (Subgroup.subtype_injective _) (L1 ⊔ bigB L1 L2 S) (f112StabEquiv0 L1 L2 S) h

theorem caseA_mem_Qy_γ₁_iff
    (h : MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma1 L1 L2 S)) :
    ((h : f112Acting L1 L2 S) : (f112Amalgam L1 L2 S).Ghat) ∈
        CosetGeom.Qy (f112Gamma1 L1 L2 S) ↔
      (f112StabEquiv1 L1 L2 S h : G) ∈ Q2 L1 L2 S := by
  change ((h : f112Acting L1 L2 S) : (f112Amalgam L1 L2 S).Ghat) ∈
      CFSG.Open.pCoreOf 2 ((MulAction.stabilizer (f112Acting L1 L2 S)
        (f112Gamma1 L1 L2 S)).map (Subgroup.subtype
          ((f112Amalgam L1 L2 S).Ghat1 ⊔ (f112Amalgam L1 L2 S).Ghat2))) ↔
    (f112StabEquiv1 L1 L2 S h : G) ∈ CFSG.Open.pCoreOf 2 (L2 ⊔ bigB L1 L2 S)
  exact pCoreOf_map_iff_mem
    (MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma1 L1 L2 S))
    (Subgroup.subtype ((f112Amalgam L1 L2 S).Ghat1 ⊔ (f112Amalgam L1 L2 S).Ghat2))
    (Subgroup.subtype_injective _) (L2 ⊔ bigB L1 L2 S) (f112StabEquiv1 L1 L2 S) h

theorem caseA_mem_Z_γ₁_iff
    (h : MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma1 L1 L2 S)) :
    ((h : f112Acting L1 L2 S) : (f112Amalgam L1 L2 S).Ghat) ∈ caseAZ (f112Gamma1 L1 L2 S) ↔
      (f112StabEquiv1 L1 L2 S h : G) ∈ Z2 L1 L2 S := by
  change ((h : f112Acting L1 L2 S) : (f112Amalgam L1 L2 S).Ghat) ∈
      omegaOneCenterOf (CFSG.Open.pCoreOf 2 ((MulAction.stabilizer (f112Acting L1 L2 S)
        (f112Gamma1 L1 L2 S)).map (Subgroup.subtype
          ((f112Amalgam L1 L2 S).Ghat1 ⊔ (f112Amalgam L1 L2 S).Ghat2)))) ↔
    (f112StabEquiv1 L1 L2 S h : G) ∈ omegaOneCenterOf
      (CFSG.Open.pCoreOf 2 (L2 ⊔ bigB L1 L2 S))
  exact omegaOneCenterOf_map_iff_mem
    (MulAction.stabilizer (f112Acting L1 L2 S) (f112Gamma1 L1 L2 S))
    (Subgroup.subtype ((f112Amalgam L1 L2 S).Ghat1 ⊔ (f112Amalgam L1 L2 S).Ghat2))
    (Subgroup.subtype_injective _) (L2 ⊔ bigB L1 L2 S) (f112StabEquiv1 L1 L2 S) h

end CFSG.Quasithin.Stroth

end
