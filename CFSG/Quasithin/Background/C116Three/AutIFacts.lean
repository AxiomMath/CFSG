module

public import CFSG.Quasithin.Background.C116Three.GroupDefs
import CFSG.Quasithin.EmptyFaithful.GoldschmidtLJWreath
import CFSG.Quasithin.Vol2.Ch10SecC9S49d
public import CFSG.Quasithin.Background.B2FactorizationBridge
public import CFSG.Quasithin.Background.C1GNA7Base
public import CFSG.Quasithin.Background.InternalSecB51
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Quot

public section

namespace CFSG.Quasithin.C116Three

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.R3c23 CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem b53Hyp_autI {H V : Subgroup G} (hSQ : IsSQTKTC H) (hVred : IsTwoReducedIn H V) :
    B53Hyp (ffJ (autI hVred.2.2.1 H)) := by
  haveI : IsMulCommutative ↥V := hVred.2.2.1.1
  have hS : SQTKGroup ↥H := C1GN.isSQTKTC_iff_sqtkGroup.1 hSQ
  have hO2 : pCoreOf 2 (autOn H V) = ⊥ := L246C127.pCoreOf_autI_eq_bot hVred.2.2.1 hVred
  exact InternalSec.b53Hyp_ffJ_autOn hVred.2.1 hS hO2

theorem autI_isQuasisimple_of_quasiData {H V L : Subgroup G} (hVred : IsTwoReducedIn H V)
    (hL : L ∈ cComp H) (hq : QuasiData V L) : CFSG.IsQuasisimple ↥(autI hVred.2.2.1 L) := by
  have hLN : L ≤ Subgroup.normalizer (V : Set G) := (le_of_mem_cComp hL).trans hVred.2.1
  obtain ⟨Q, _, φQ, hφs, hkerQ, hQq⟩ := hq
  have hk : (convHom hVred.2.2.1 L hLN).ker = φQ.ker := by
    rw [ker_convHom, hkerQ]
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
  let e : ↥(autI hVred.2.2.1 L) ≃* Q :=
    ((MulEquiv.subgroupCongr (range_convHom hVred.2.2.1 L hLN).symm).trans
      (QuotientGroup.quotientKerEquivRange (convHom hVred.2.2.1 L hLN)).symm).trans
      ((QuotientGroup.quotientMulEquivOfEq hk).trans
        (QuotientGroup.quotientKerEquivOfSurjective φQ hφs))
  exact hQq.of_mulEquiv e

theorem commutator_le_centralizer_of_commute {H V L K : Subgroup G} (hVred : IsTwoReducedIn H V)
    (hLN : L ≤ Subgroup.normalizer (V : Set G)) (hKN : K ≤ Subgroup.normalizer (V : Set G))
    (hcomm : ∀ a ∈ autI hVred.2.2.1 L, ∀ b ∈ autI hVred.2.2.1 K, a * b = b * a) :
    ⁅L, K⁆ ≤ Subgroup.centralizer (V : Set G) := by
  refine Subgroup.commutator_le.2 fun x hx y hy => ?_
  have ha := convI_mem_autI hVred.2.2.1 hx (hLN hx)
  have hb := convI_mem_autI hVred.2.2.1 hy (hKN hy)
  have h1 : convI hVred.2.2.1
      ⁅(⟨x, hLN hx⟩ : ↥(Subgroup.normalizer (V : Set G))), ⟨y, hKN hy⟩⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm _ ha _ hb
  exact (convI_eq_one_iff hVred.2.2.1 _).1 h1

theorem le_ffJ_autI {H T V L : Subgroup G} (hVred : IsTwoReducedIn H V) (hT : IsSylowTwoOf T H)
    (hL : L ∈ cComp H) (hq : QuasiData V L)
    (hnJ : ¬ ⁅L, thompsonJ T⁆ ≤ Subgroup.centralizer (V : Set G)) :
    autI hVred.2.2.1 L ≤ ffJ (autI hVred.2.2.1 H) := by
  have hLH : L ≤ H := le_of_mem_cComp hL
  have hLN : L ≤ Subgroup.normalizer (V : Set G) := hLH.trans hVred.2.1
  have hTN : thompsonJ T ≤ Subgroup.normalizer (V : Set G) :=
    ((B6.thompsonJ_le T).trans hT.1).trans hVred.2.1
  have hquasi : CFSG.Open.IsQuasisimple ↥(autI hVred.2.2.1 L) :=
    B1Red.isQuasisimple_to_open (autI_isQuasisimple_of_quasiData hVred hL hq)
  have hcomp : CFSG.Open.IsComponentOf (autI hVred.2.2.1 L) (autI hVred.2.2.1 H) :=
    CFSG.Quasithin.LJ.isComponentOf_autI hVred.2.2.1 hVred.2.1 hL hquasi
  have hcomp' := CFSG.Quasithin.isComponentOf_iff_subgroupOf.1 hcomp
  have hLX : autI hVred.2.2.1 L ≤ autI hVred.2.2.1 H := hcomp'.1
  have hK : CFSG.IsComponent ((autI hVred.2.2.1 L).subgroupOf (autI hVred.2.2.1 H)) :=
    (CFSG.isComponent_iff_open _).2 hcomp'.2
  have hJn : ((ffJ (autI hVred.2.2.1 H)).subgroupOf (autI hVred.2.2.1 H)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (B6.ffJ_le (autI hVred.2.2.1 H))).2
      (B6.le_normalizer_ffJ (autI hVred.2.2.1 H))
  have hTJ : autI hVred.2.2.1 (thompsonJ T) ≤ ffJ (autI hVred.2.2.1 H) :=
    CFSG.Quasithin.Vol2.Ch10.SecC.autI_thompsonJ_le_ffJ hVred.2.2.1 hVred hT
  rcases CFSG.LocalCores.component_normal_subgroup hK hJn with h | h
  · intro x hx
    have hx' : (⟨x, hLX hx⟩ : ↥(autI hVred.2.2.1 H)) ∈
        (autI hVred.2.2.1 L).subgroupOf (autI hVred.2.2.1 H) :=
      Subgroup.mem_subgroupOf.2 hx
    exact Subgroup.mem_subgroupOf.1 (h hx')
  · exfalso
    apply hnJ
    apply commutator_le_centralizer_of_commute hVred hLN hTN
    intro a ha b hb
    have ha' : (⟨a, hLX ha⟩ : ↥(autI hVred.2.2.1 H)) ∈
        (autI hVred.2.2.1 L).subgroupOf (autI hVred.2.2.1 H) :=
      Subgroup.mem_subgroupOf.2 ha
    have hbH : b ∈ autI hVred.2.2.1 H := B6.ffJ_le (autI hVred.2.2.1 H) (hTJ hb)
    have hb' : (⟨b, hbH⟩ : ↥(autI hVred.2.2.1 H)) ∈
        (ffJ (autI hVred.2.2.1 H)).subgroupOf (autI hVred.2.2.1 H) :=
      Subgroup.mem_subgroupOf.2 (hTJ hb)
    have hm := Subgroup.commutator_mem_commutator ha' hb'
    rw [h, Subgroup.mem_bot] at hm
    exact congrArg Subtype.val (commutatorElement_eq_one_iff_mul_comm.1 hm)

theorem ffJ_le_normalizer_autI {H V L : Subgroup G} (hVred : IsTwoReducedIn H V) (hL : L ∈ cComp H)
    (hq : QuasiData V L) :
    ∀ x ∈ ffJ (autI hVred.2.2.1 H),
      x ∈ Subgroup.normalizer ((autI hVred.2.2.1 L : Subgroup (MulAut (IntMod V hVred.2.2.1))) :
        Set (MulAut (IntMod V hVred.2.2.1))) := by
  have hquasi : CFSG.Open.IsQuasisimple ↥(autI hVred.2.2.1 L) :=
    B1Red.isQuasisimple_to_open (autI_isQuasisimple_of_quasiData hVred hL hq)
  have hcomp : CFSG.Open.IsComponentOf (autI hVred.2.2.1 L) (autI hVred.2.2.1 H) :=
    CFSG.Quasithin.LJ.isComponentOf_autI hVred.2.2.1 hVred.2.1 hL hquasi
  have hle : ffJ (autI hVred.2.2.1 H) ≤
      Subgroup.normalizer ((autI hVred.2.2.1 L : Subgroup (MulAut (IntMod V hVred.2.2.1))) :
        Set (MulAut (IntMod V hVred.2.2.1))) := by
    unfold ffJ
    refine iSup₂_le fun A hA => ?_
    exact CFSG.Quasithin.B15P4.asB15Part4 (IntMod V hVred.2.2.1) (fun v => IntMod.sq_eq_one v)
      (autI hVred.2.2.1 H) A hA (autI hVred.2.2.1 L) hcomp
  intro x hx
  exact hle hx

end CFSG.Quasithin.C116Three
