module

public import CFSG.Quasithin.Recognition.St84.Gen.G2qVertexData
public import CFSG.Quasithin.Recognition.St84.Gen.TransferG2qData
public import CFSG.Quasithin.Recognition.St84.Gen.TreeLLBase
public import CFSG.Quasithin.Recognition.St84.Gen.TransferLL

import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalIndec
import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalIndecBasic
import CFSG.Quasithin.Recognition.St84.Gen.L2RankOne
import CFSG.Quasithin.Recognition.St84.Gen.TransportG2qLocal
import CFSG.Quasithin.Recognition.St84.Gen.TransportTreeEquiv
import CFSG.Quasithin.Recognition.St84.Gen.TransportTreeLL
public import CFSG.CGT.PushingUpLit.BHS.OffenderInternal
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldNaturalAction
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftBaumannDelOrigData
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDelBlockTools
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDelH0
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceCommon
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathGate5
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathGate6
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Points
public import CFSG.Quasithin.Background.C1GNA7
public import CFSG.Quasithin.Background.C1PackBasic
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModPack28Proof
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModS5Irr
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModSecIrred
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.Steps
public import CFSG.Quasithin.EmptyFaithful.SzF53BasE
public import CFSG.Quasithin.EmptyFaithful.SzF53MSecB
public import CFSG.Quasithin.H13.GoldschmidtC137BaumMain
public import CFSG.Quasithin.H13.GoldschmidtC137Data
public import CFSG.Quasithin.H13.GoldschmidtC137U33Hyp
public import CFSG.Quasithin.H13.GoldschmidtC137U33S2Over
public import CFSG.Quasithin.H13.GoldschmidtC137U33S2Self
public import CFSG.Quasithin.H13.LinearOrders
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Defs
public import CFSG.Quasithin.Recognition.GoldschmidtFan86TArcEven
public import CFSG.Quasithin.Recognition.St84.AppTreeSAP1
public import CFSG.Quasithin.Recognition.St84.PushUp
public import CFSG.RankThree.PartTwo.Sec15.Item153PushProofTools
public import Certificates.Kernel.J4Count.Prim
import CFSG.Quasithin.H13.J4Order
import CFSG.Timmesfeld.RankOne.Defs

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.Quasithin.St84
  CFSG.Quasithin.Fan86 CFSG.Quasithin.Fan86.Univ
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H]

theorem G2qEdgeData.of_vertexData {L1 L2 S : Subgroup H} {f : ℕ} (hf : 3 ≤ f)
    (hH : Hyp111 (oTwoPrime (f112saP1' L1 L2 S)) (oTwoPrime (f112saP2' L1 L2 S))
      (S ⊓ f112saK L1 L2 S))
    (h1 : IsL2Quot f (oTwoQuot ↥(oTwoPrime (f112saP1' L1 L2 S))))
    (h2 : IsL2Quot f (oTwoQuot ↥(oTwoPrime (f112saP2' L1 L2 S))))
    (hd : G2qVertexData (oTwoPrime (f112saP1' L1 L2 S)) (oTwoPrime (f112saP2' L1 L2 S))
      (S ⊓ f112saK L1 L2 S) f)
    (hJ : ∃ J : Subgroup H,
      J ≤ bigB (oTwoPrime (f112saP1' L1 L2 S)) (oTwoPrime (f112saP2' L1 L2 S))
        (S ⊓ f112saK L1 L2 S) ∧ Odd (Nat.card J) ∧
      (∀ j ∈ J, ∀ l ∈ oTwoPrime (f112saP1' L1 L2 S),
        ⁅j, l⁆ ∈ pCoreOf 2 (oTwoPrime (f112saP1' L1 L2 S))) ∧
      pCoreOf 2 (oTwoPrime (f112saP1' L1 L2 S)) ⊓ Subgroup.centralizer (J : Set H) = ⊥) :
    G2qEdgeData L1 L2 S f := by
  obtain ⟨J, hJB, hJodd, hJcomm, hJbot⟩ := hJ
  have hcomm' : ∀ j ∈ J, ∀ l ∈ oTwoPrime (f112saP1' L1 L2 S),
      ⁅j, l⁆ ∈ pCoreOf 2 (f112saP1' L1 L2 S) := by
    intro j hj l hl
    have h := hJcomm j hj l hl
    rwa [pCoreOf_oTwoPrime (f112saP1' L1 L2 S)] at h
  have hbot' : pCoreOf 2 (f112saP1' L1 L2 S) ⊓ Subgroup.centralizer (J : Set H) = ⊥ := by
    rw [← pCoreOf_oTwoPrime (f112saP1' L1 L2 S)]
    exact hJbot
  refine
    { local_ := hd.toG2qLocalData
      indec_left := ?_
      indec_right := ?_
      relCent_left := ?_
      gen_left := ?_
      torus_left := ⟨J, hJB, hJodd, hcomm', hbot'⟩ }
  · have h := hd.indec_left
    rwa [pCoreOf_oTwoPrime (f112saP1' L1 L2 S)] at h
  ·
    have h := hd.toG2qLocalData.commutator_pCoreOf_right hf hH h1 h2
    rwa [pCoreOf_oTwoPrime (f112saP2' L1 L2 S)] at h
  · intro x hx hxc
    have hxQβ : x ∈ pCoreOf 2 (oTwoPrime (f112saP2' L1 L2 S)) := by
      rwa [← pCoreOf_oTwoPrime (f112saP2' L1 L2 S)] at hx
    have hxc' : ∀ l ∈ oTwoPrime (f112saP2' L1 L2 S),
        ⁅x, l⁆ ∈ centerOf (pCoreOf 2 (oTwoPrime (f112saP2' L1 L2 S))) := by
      intro l hl
      have h := hxc l hl
      rwa [← pCoreOf_oTwoPrime (f112saP2' L1 L2 S)] at h
    obtain ⟨c⟩ := hd.toG2qLocalData.exists_coordRight hH h2
    have hxW : x ∈ c.W := c.mem_W_iff.2 ⟨hxQβ, fun l hl => by
      simpa only [commutatorElement_inv] using
        (centerOf (pCoreOf 2 (oTwoPrime (f112saP2' L1 L2 S)))).inv_mem (hxc' l hl)⟩
    have h := G2qCoordRight.W_le_pCoreOf_left hH hd.toG2qLocalData h1 h2 c hxW
    rwa [pCoreOf_oTwoPrime (f112saP1' L1 L2 S)] at h
  · intro N hZN hNQ hNnorm
    have hZN' : centerOf (pCoreOf 2 (oTwoPrime (f112saP2' L1 L2 S))) ≤ N := by
      rwa [← pCoreOf_oTwoPrime (f112saP2' L1 L2 S)] at hZN
    have hNQ' : N ≤ pCoreOf 2 (oTwoPrime (f112saP1' L1 L2 S)) := by
      rwa [← pCoreOf_oTwoPrime (f112saP1' L1 L2 S)] at hNQ
    have h := hd.gen_left N hZN' hNQ' hNnorm
    rwa [pCoreOf_oTwoPrime (f112saP1' L1 L2 S)] at h

private theorem f112ll_gen_left_of_tree {L1 L2 S : Subgroup H} {m n f : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2))
    {X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S)}
    (hX0 : X.vert 0 = baseA (f112Gold L1 L2 S)) (hX1 : X.vert 1 = baseB (f112Gold L1 L2 S))
    (hd : G2qVertexData (X.L 0) (X.L 1) X.S f) {N : Subgroup H}
    (hZN : centerOf (pCoreOf 2 (oTwoPrime (f112saP2' L1 L2 S))) ≤ N)
    (hNQ : N ≤ pCoreOf 2 (oTwoPrime (f112saP1' L1 L2 S)))
    (hNnorm : oTwoPrime (f112saP1' L1 L2 S) ≤ Subgroup.normalizer (N : Set H)) :
    N = pCoreOf 2 (oTwoPrime (f112saP1' L1 L2 S)) := by
  have hR : Hyp111R L1 L2 S := hyp111R_of_isL2Quot (by omega) (by omega) hF.1 h1 h2
  let D := f112EOddBaseEdgeData hF hR X hX0 hX1
  have hdD : G2qVertexData (D.X.L 0) (D.X.L 1) D.X.S f := hd
  have hZN' : centerOf (pCoreOf 2 (oTwoPrime D.Pβ)) ≤ N := hZN
  have hNQ' : N ≤ pCoreOf 2 (oTwoPrime D.Pα) := hNQ
  have hNnorm' : oTwoPrime D.Pα ≤ Subgroup.normalizer (N : Set H) := hNnorm
  have hQαP : pCoreOf 2 (oTwoPrime D.Pα) ≤ f112P1 D.L1 D.L2 D.S :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 (oTwoPrime D.Pα)).trans
      ((oTwoPrime_le D.Pα).trans D.le_Pα)
  have hQβP₂ : pCoreOf 2 (oTwoPrime D.Pβ) ≤ f112P2 D.L1 D.L2 D.S :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 (oTwoPrime D.Pβ)).trans
      ((oTwoPrime_le D.Pβ).trans D.le_Pβ)
  have hNP₁ : N ≤ f112P1 D.L1 D.L2 D.S := hNQ'.trans hQαP
  obtain ⟨N', hN'Q, hN'norm, hN'map⟩ := D.exists_comap_of_tree hNQ' hNnorm'
  have hZP₁ : centerOf (pCoreOf 2 (oTwoPrime D.Pβ)) ≤ f112P1 D.L1 D.L2 D.S :=
    hZN'.trans hNP₁
  have hZP₂ : centerOf (pCoreOf 2 (oTwoPrime D.Pβ)) ≤ f112P2 D.L1 D.L2 D.S :=
    inf_le_left.trans hQβP₂
  have hZle : f112OfB D.L1 D.L2 D.S (centerOf (pCoreOf 2 (oTwoPrime D.Pβ))) ≤
      f112OfA D.L1 D.L2 D.S N := by
    rw [← ofA_subgroupOf_eq_ofB_subgroupOf D.L1 D.L2 D.S (le_inf hZP₁ hZP₂)]
    exact Subgroup.map_mono (f := (f112Gold D.L1 D.L2 D.S).ofA)
      (Subgroup.subgroupOf_mono (f112P1 D.L1 D.L2 D.S) hZN')
  have hcenterN' : centerOf (pCoreOf 2 (D.X.L 1)) ≤ N' := by
    intro c hc
    refine (Subgroup.mem_map_iff_mem D.E.subtype_injective).mp ?_
    rw [hN'map]
    have hmap : D.E.subtype c ∈ (centerOf (pCoreOf 2 (D.X.L 1))).map D.E.subtype :=
      Subgroup.mem_map.mpr ⟨c, hc, rfl⟩
    rw [D.centerOf_pCoreOf_L_one_map] at hmap
    exact hZle hmap
  have hN'eq : N' = pCoreOf 2 (D.X.L 0) := hdD.gen_left N' hcenterN' hN'Q hN'norm
  have hle : pCoreOf 2 (oTwoPrime D.Pα) ≤ N :=
    (D.le_iff_of_map_eq hQαP hNP₁ D.pCoreOf_L_zero_map hN'map).mp
      (le_of_eq hN'eq.symm)
  exact le_antisymm hNQ' hle

theorem f112ll_g2qVertexData_oTwoPrime_of_tree {L1 L2 S : Subgroup H} {m n f : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2))
    {X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S)}
    (hX0 : X.vert 0 = baseA (f112Gold L1 L2 S)) (hX1 : X.vert 1 = baseB (f112Gold L1 L2 S))
    (hd : G2qVertexData (X.L 0) (X.L 1) X.S f) :
    G2qVertexData (oTwoPrime (f112saP1' L1 L2 S)) (oTwoPrime (f112saP2' L1 L2 S))
      (S ⊓ f112saK L1 L2 S) f :=
  { toG2qLocalData :=
      f112ll_g2qLocalData_oTwoPrime_of_tree hF hm hn h1 h2 hX0 hX1 hd.toG2qLocalData
    indec_left := f112ll_commutator_pCoreOf_P1'_of_tree hF hm hn h1 h2 hX0 hX1 hd.indec_left
    gen_left := fun N hZN hNQ hNnorm =>
      f112ll_gen_left_of_tree hF hm hn h1 h2 hX0 hX1 hd hZN hNQ hNnorm }

end CFSG.Quasithin.F112R.St84

end
