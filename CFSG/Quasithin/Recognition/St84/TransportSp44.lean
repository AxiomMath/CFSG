module

public import CFSG.Quasithin.Recognition.St84.TreeBase
public import CFSG.Quasithin.Recognition.St84.TransferSp44Torus
public import CFSG.Quasithin.Recognition.St84.Sp44Index
public import CFSG.Quasithin.Recognition.St84.TransferA5A5
public import CFSG.Quasithin.Recognition.St84.Sec4TreeData
public import CFSG.Quasithin.Recognition.St84.Sp44Ident
public import CFSG.CGT.PushingUpLit.BHS.OffenderInternal
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldNaturalAction
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftBaumannDelOrigData
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDelBlockTools
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDelH0
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceCommon
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathGate5
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathGate6
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Points
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
public import CFSG.Quasithin.Recognition.St84.Sec6ZTools
public import CFSG.RankThree.PartTwo.Sec15.Item153PushProofTools
public import Certificates.Kernel.J4Count.Prim

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.Quasithin.St84
  CFSG.Quasithin.Fan86 CFSG.Quasithin.Fan86.Univ CFSG.GH74.QTGen4.DSGen4
open scoped Pointwise commutatorElement

variable {H : Type} [Group H] [Finite H]

theorem f112_sp44VertexData_of_treeSp44Data {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2)
    {X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112E5 L1 L2 S)}
    (hX0 : X.vert 0 = baseA (f112Gold L1 L2 S))
    (hX1 : X.vert 1 = baseB (f112Gold L1 L2 S))
    (hd : X.TreeSp44Data) :
    Sp44VertexData (f112saP1' L1 L2 S) ∧
      Sp44VertexData (f112saP2' L1 L2 S) ∧
      Nat.card ↥(S ⊓ f112saK L1 L2 S) = 2 ^ 8 ∧
      Nat.card ↥(pCoreOf 2 (f112saP1' L1 L2 S) ⊓
        pCoreOf 2 (f112saP2' L1 L2 S)) = 2 ^ 4 := by
  classical
  let D := f112BaseEdgeData hF h1 h2 X hX0 hX1
  have hdX : D.X.TreeSp44Data := hd
  have hcD : CharTwoStab (V := Vtx (f112Gold D.L1 D.L2 D.S)) (G := ↥D.E) :=
    f112_charTwoStab hF h1 h2
  have hLα : oTwoPrime D.Pα ≤ f112P1 D.L1 D.L2 D.S := (oTwoPrime_le D.Pα).trans D.le_Pα
  have hLβ : oTwoPrime D.Pβ ≤ f112P2 D.L1 D.L2 D.S := (oTwoPrime_le D.Pβ).trans D.le_Pβ
  have hQα : pCoreOf 2 (oTwoPrime D.Pα) ≤ f112P1 D.L1 D.L2 D.S :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 (oTwoPrime D.Pα)).trans hLα
  have hQβ : pCoreOf 2 (oTwoPrime D.Pβ) ≤ f112P2 D.L1 D.L2 D.S :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 (oTwoPrime D.Pβ)).trans hLβ
  have hZαY : centerOf (oTwoPrime D.Pα) ≤ oTwoPrime D.Pα :=
    fun x hx => (Subgroup.mem_inf.mp hx).1
  have hZα : centerOf (oTwoPrime D.Pα) ≤ f112P1 D.L1 D.L2 D.S := hZαY.trans hLα
  have hZβY : centerOf (oTwoPrime D.Pβ) ≤ oTwoPrime D.Pβ :=
    fun x hx => (Subgroup.mem_inf.mp hx).1
  have hZβ : centerOf (oTwoPrime D.Pβ) ≤ f112P2 D.L1 D.L2 D.S := hZβY.trans hLβ
  have hcenterA : (centerOf (D.X.L 0)).map D.E.subtype =
      f112OfA D.L1 D.L2 D.S (centerOf (oTwoPrime D.Pα)) := by
    rw [← CFSG.Quasithin.SimsD1.TransGrp.centerOf_map_eq D.E.subtype
      D.E.subtype_injective, D.L_zero_map, f112_ofA_centerOf D.L1 D.L2 D.S hLα]
  have hcenterB : (centerOf (D.X.L 1)).map D.E.subtype =
      f112OfB D.L1 D.L2 D.S (centerOf (oTwoPrime D.Pβ)) := by
    rw [← CFSG.Quasithin.SimsD1.TransGrp.centerOf_map_eq D.E.subtype
      D.E.subtype_injective, D.L_one_map, f112_ofB_centerOf D.L1 D.L2 D.S hLβ]
  refine ⟨?_, ?_, ?_, ?_⟩
  · show Sp44VertexData D.Pα
    refine ⟨f112_isL2Quot_oTwoPrime_P1' hF h1 h2, ?_, ?_, ?_, ?_, ?_⟩
    · have hiff := isElemAbelian_of_map_iff (L1 := D.L1) (L2 := D.L2) (S := D.S)
        (E := D.E) hQα D.pCoreOf_L_zero_map
      rw [pCoreOf_oTwoPrime D.Pα] at hiff
      exact hiff.mp hdX.elem_left
    · show Nat.card ↥(pCoreOf 2 D.Pα) = 2 ^ 6
      have h := card_of_map_eq (L1 := D.L1) (L2 := D.L2) (S := D.S)
        (E := D.E) hQα D.pCoreOf_L_zero_map
      rw [pCoreOf_oTwoPrime D.Pα, hdX.card_left] at h
      exact h.symm
    · show Nat.card ↥(centerOf (oTwoPrime D.Pα)) = 2 ^ 2
      have h := card_of_map_eq (L1 := D.L1) (L2 := D.L2) (S := D.S)
        (E := D.E) hZα hcenterA
      rw [hdX.center_left] at h
      exact h.symm
    · show NatSec (oTwoPrime D.Pα) (centerOf (oTwoPrime D.Pα)) (pCoreOf 2 D.Pα)
      have hiff := natSec_of_map_iff (L1 := D.L1) (L2 := D.L2) (S := D.S)
        (E := D.E) (L' := D.X.L 0) (K' := centerOf (D.X.L 0))
        (Q' := pCoreOf 2 (D.X.L 0)) (L := oTwoPrime D.Pα)
        (K := centerOf (oTwoPrime D.Pα)) (Q := pCoreOf 2 (oTwoPrime D.Pα))
        hLα hZα hQα D.L_zero_map hcenterA D.pCoreOf_L_zero_map
      rw [pCoreOf_oTwoPrime D.Pα] at hiff
      exact hiff.mp hdX.nat_left
    · show ⁅pCoreOf 2 D.Pα, oTwoPrime D.Pα⁆ = pCoreOf 2 D.Pα
      have hcomm : f112OfA D.L1 D.L2 D.S
          (⁅pCoreOf 2 (oTwoPrime D.Pα), oTwoPrime D.Pα⁆) =
          f112OfA D.L1 D.L2 D.S (pCoreOf 2 (oTwoPrime D.Pα)) := by
        rw [← f112_ofA_commutator D.L1 D.L2 D.S hQα hLα]
        calc ⁅f112OfA D.L1 D.L2 D.S (pCoreOf 2 (oTwoPrime D.Pα)),
              f112OfA D.L1 D.L2 D.S (oTwoPrime D.Pα)⁆
            = ⁅(pCoreOf 2 (D.X.L 0)).map D.E.subtype, (D.X.L 0).map D.E.subtype⁆ := by
              rw [← D.pCoreOf_L_zero_map, ← D.L_zero_map]
          _ = (⁅pCoreOf 2 (D.X.L 0), D.X.L 0⁆).map D.E.subtype :=
              (Subgroup.map_commutator (f := D.E.subtype)
                (H₁ := pCoreOf 2 (D.X.L 0)) (H₂ := D.X.L 0)).symm
          _ = (pCoreOf 2 (D.X.L 0)).map D.E.subtype := by rw [hdX.indec_left]
          _ = f112OfA D.L1 D.L2 D.S (pCoreOf 2 (oTwoPrime D.Pα)) := D.pCoreOf_L_zero_map
      have hindecU : f112OfA D.L1 D.L2 D.S
          (⁅pCoreOf 2 (oTwoPrime D.Pα), oTwoPrime D.Pα⁆) =
          f112OfA D.L1 D.L2 D.S (pCoreOf 2 (oTwoPrime D.Pα)) := hcomm
      have hsub : (⁅pCoreOf 2 (oTwoPrime D.Pα), oTwoPrime D.Pα⁆).subgroupOf
          (f112P1 D.L1 D.L2 D.S) =
          (pCoreOf 2 (oTwoPrime D.Pα)).subgroupOf (f112P1 D.L1 D.L2 D.S) :=
        Subgroup.map_injective (f := (f112Gold D.L1 D.L2 D.S).ofA)
          (f112Gold D.L1 D.L2 D.S).ofA_injective hindecU
      have hEq : ⁅pCoreOf 2 (oTwoPrime D.Pα), oTwoPrime D.Pα⁆ =
          pCoreOf 2 (oTwoPrime D.Pα) := by
        have hinf := Subgroup.subgroupOf_inj.mp hsub
        rwa [inf_eq_left.mpr (Subgroup.commutator_le_of_le hQα hLα),
          inf_eq_left.mpr hQα] at hinf
      rw [← pCoreOf_oTwoPrime D.Pα]
      exact hEq
  · show Sp44VertexData D.Pβ
    refine ⟨f112_isL2Quot_oTwoPrime_P2' hF h1 h2, ?_, ?_, ?_, ?_, ?_⟩
    · have hiff := isElemAbelian_of_map_iff_ofB (L1 := D.L1) (L2 := D.L2) (S := D.S)
        (E := D.E) hQβ D.pCoreOf_L_one_map
      rw [pCoreOf_oTwoPrime D.Pβ] at hiff
      exact hiff.mp hdX.elem_right
    · show Nat.card ↥(pCoreOf 2 D.Pβ) = 2 ^ 6
      have h := card_of_map_eq_ofB (L1 := D.L1) (L2 := D.L2) (S := D.S)
        (E := D.E) hQβ D.pCoreOf_L_one_map
      rw [pCoreOf_oTwoPrime D.Pβ, hdX.card_right] at h
      exact h.symm
    · show Nat.card ↥(centerOf (oTwoPrime D.Pβ)) = 2 ^ 2
      have h := card_of_map_eq_ofB (L1 := D.L1) (L2 := D.L2) (S := D.S)
        (E := D.E) hZβ hcenterB
      rw [hdX.center_right] at h
      exact h.symm
    · show NatSec (oTwoPrime D.Pβ) (centerOf (oTwoPrime D.Pβ)) (pCoreOf 2 D.Pβ)
      have hiff := natSec_of_map_iff_ofB (L1 := D.L1) (L2 := D.L2) (S := D.S)
        (E := D.E) (L' := D.X.L 1) (K' := centerOf (D.X.L 1))
        (Q' := pCoreOf 2 (D.X.L 1)) (L := oTwoPrime D.Pβ)
        (K := centerOf (oTwoPrime D.Pβ)) (Q := pCoreOf 2 (oTwoPrime D.Pβ))
        hLβ hZβ hQβ D.L_one_map hcenterB D.pCoreOf_L_one_map
      rw [pCoreOf_oTwoPrime D.Pβ] at hiff
      exact hiff.mp hdX.nat_right
    · show ⁅pCoreOf 2 D.Pβ, oTwoPrime D.Pβ⁆ = pCoreOf 2 D.Pβ
      have hcomm : f112OfB D.L1 D.L2 D.S
          (⁅pCoreOf 2 (oTwoPrime D.Pβ), oTwoPrime D.Pβ⁆) =
          f112OfB D.L1 D.L2 D.S (pCoreOf 2 (oTwoPrime D.Pβ)) := by
        rw [← f112_ofB_commutator D.L1 D.L2 D.S hQβ hLβ]
        calc ⁅f112OfB D.L1 D.L2 D.S (pCoreOf 2 (oTwoPrime D.Pβ)),
              f112OfB D.L1 D.L2 D.S (oTwoPrime D.Pβ)⁆
            = ⁅(pCoreOf 2 (D.X.L 1)).map D.E.subtype, (D.X.L 1).map D.E.subtype⁆ := by
              rw [← D.pCoreOf_L_one_map, ← D.L_one_map]
          _ = (⁅pCoreOf 2 (D.X.L 1), D.X.L 1⁆).map D.E.subtype :=
              (Subgroup.map_commutator (f := D.E.subtype)
                (H₁ := pCoreOf 2 (D.X.L 1)) (H₂ := D.X.L 1)).symm
          _ = (pCoreOf 2 (D.X.L 1)).map D.E.subtype := by rw [hdX.indec_right]
          _ = f112OfB D.L1 D.L2 D.S (pCoreOf 2 (oTwoPrime D.Pβ)) := D.pCoreOf_L_one_map
      have hindecU : f112OfB D.L1 D.L2 D.S
          (⁅pCoreOf 2 (oTwoPrime D.Pβ), oTwoPrime D.Pβ⁆) =
          f112OfB D.L1 D.L2 D.S (pCoreOf 2 (oTwoPrime D.Pβ)) := hcomm
      have hsub : (⁅pCoreOf 2 (oTwoPrime D.Pβ), oTwoPrime D.Pβ⁆).subgroupOf
          (f112P2 D.L1 D.L2 D.S) =
          (pCoreOf 2 (oTwoPrime D.Pβ)).subgroupOf (f112P2 D.L1 D.L2 D.S) :=
        Subgroup.map_injective (f := (f112Gold D.L1 D.L2 D.S).ofB)
          (f112Gold D.L1 D.L2 D.S).ofB_injective hindecU
      have hEq : ⁅pCoreOf 2 (oTwoPrime D.Pβ), oTwoPrime D.Pβ⁆ =
          pCoreOf 2 (oTwoPrime D.Pβ) := by
        have hinf := Subgroup.subgroupOf_inj.mp hsub
        rwa [inf_eq_left.mpr (Subgroup.commutator_le_of_le hQβ hLβ),
          inf_eq_left.mpr hQβ] at hinf
      rw [← pCoreOf_oTwoPrime D.Pβ]
      exact hEq
  · show Nat.card ↥(S ⊓ D.Ke) = 2 ^ 8
    have hKe : pCoreOf 2 D.Ke = S ⊓ D.Ke := f112_pCoreOf_K_eq hF h1 h2
    have hY : S ⊓ D.Ke ≤ f112P1 D.L1 D.L2 D.S :=
      (inf_le_right : S ⊓ D.Ke ≤ D.Ke).trans (D.le_Ke.trans inf_le_left)
    have hmap : (D.X.S).map D.E.subtype = f112OfA D.L1 D.L2 D.S (S ⊓ D.Ke) := by
      rw [D.S_map, hKe]
    have h := card_of_map_eq (L1 := D.L1) (L2 := D.L2) (S := D.S) (E := D.E) hY hmap
    rw [hdX.card_S] at h
    exact h.symm
  · show Nat.card ↥(pCoreOf 2 D.Pα ⊓ pCoreOf 2 D.Pβ) = 2 ^ 4
    have hQβP1 : pCoreOf 2 D.Pβ ≤ f112P1 D.L1 D.L2 D.S :=
      (D.pCoreOf_Pβ_le_inf hcD).trans inf_le_left
    have hQαP1 : pCoreOf 2 D.Pα ≤ f112P1 D.L1 D.L2 D.S :=
      (CFSG.LieType.BorelTits.pCoreOf_le 2 D.Pα).trans D.le_Pα
    have hY : pCoreOf 2 D.Pα ⊓ pCoreOf 2 D.Pβ ≤ f112P1 D.L1 D.L2 D.S :=
      (inf_le_left : pCoreOf 2 D.Pα ⊓ pCoreOf 2 D.Pβ ≤ pCoreOf 2 D.Pα).trans hQαP1
    have hmap : (D.X.Q 0 ⊓ D.X.Q 1).map D.E.subtype =
        f112OfA D.L1 D.L2 D.S (pCoreOf 2 D.Pα ⊓ pCoreOf 2 D.Pβ) := by
      rw [Subgroup.map_inf (D.X.Q 0) (D.X.Q 1) D.E.subtype D.E.subtype_injective,
        D.Q_zero_map, D.Q_one_map]
      exact ofA_map_inf_ofB_map D.L1 D.L2 D.S
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 D.Pα).trans D.le_Pα)
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 D.Pβ).trans D.le_Pβ)
    have hcardQ : Nat.card ↥(D.X.Q 0 ⊓ D.X.Q 1) = 2 ^ 4 := by
      haveI : Finite ↥(D.X.Gi 0) := D.X.hyp.finite_stab (D.X.vert 0)
      haveI : Finite ↥(D.X.Gi 1) := D.X.hyp.finite_stab (D.X.vert 1)
      have h := hdX.card_inf
      rw [pCoreOf_oTwoPrime (D.X.Gi 0), pCoreOf_oTwoPrime (D.X.Gi 1)] at h
      exact h
    have h := card_of_map_eq (L1 := D.L1) (L2 := D.L2) (S := D.S) (E := D.E) hY hmap
    rw [hcardQ] at h
    exact h.symm

theorem f112_sp44LocalData_of_treeSp44Data
    {L1 L2 S : Subgroup H} (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2)
    {X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112E5 L1 L2 S)}
    (hX0 : X.vert 0 = baseA (f112Gold L1 L2 S))
    (hX1 : X.vert 1 = baseB (f112Gold L1 L2 S))
    (hd : X.TreeSp44Data) :
    Sp44LocalData L1 L2 S := by
  classical
  obtain ⟨hV1, hV2, hcardT, hcardInf⟩ :=
    f112_sp44VertexData_of_treeSp44Data hF h1 h2 hX0 hX1 hd
  have hV1' : TransferVertexData (f112saP1' L1 L2 S) :=
    transferVertexData_of_sp44VertexData hV1 (f112sa_charTwo_P1' hF)
  have hV2' : TransferVertexData (f112saP2' L1 L2 S) :=
    transferVertexData_of_sp44VertexData hV2 (f112sa_charTwo_P2' hF)
  have hS : S ≤ f112saK L1 L2 S :=
    f112sa_le_K_of_transfer hF h1 h2 hV1' hV2' (f112_pCoreOf_sup_eq hF h1 h2).symm
  obtain ⟨hS1, hL1eq, hQ1eq⟩ :=
    f112sa_S_le_L1_and_eq_oTwoPrime_of_transferVertexData hF h1 hS hV1'
  obtain ⟨hS2, hL2eq, hQ2eq⟩ :=
    f112sa_S_le_L2_and_eq_oTwoPrime_of_transferVertexData hF h2 hS hV2'
  refine Sp44LocalData.of_core hF h1 h2 hS1 hS2 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · have h : S ⊓ f112saK L1 L2 S = S := inf_eq_left.mpr hS
    simpa [h] using hcardT
  · rw [hQ1eq]; exact hV1.elem
  · rw [hQ1eq, hV1.card]
  · rw [hL1eq]; exact hV1.center
  · let Eα := f112saP1' L1 L2 S
    have hL1eq' : L1 = oTwoPrime Eα := hL1eq
    have hQ1eq' : pCoreOf 2 L1 = pCoreOf 2 Eα := hQ1eq
    have hnat : NatSec (oTwoPrime Eα) (centerOf (oTwoPrime Eα)) (pCoreOf 2 Eα) := hV1.nat
    rw [hQ1eq', hL1eq']
    exact hnat
  · let Eα := f112saP1' L1 L2 S
    have hL1eq' : L1 = oTwoPrime Eα := hL1eq
    have hQ1eq' : pCoreOf 2 L1 = pCoreOf 2 Eα := hQ1eq
    have hind : ⁅pCoreOf 2 Eα, oTwoPrime Eα⁆ = pCoreOf 2 Eα := hV1.indec
    rw [hQ1eq', hL1eq']
    exact hind
  · rw [hQ2eq]; exact hV2.elem
  · rw [hQ2eq, hV2.card]
  · rw [hL2eq]; exact hV2.center
  · let Eβ := f112saP2' L1 L2 S
    have hL2eq' : L2 = oTwoPrime Eβ := hL2eq
    have hQ2eq' : pCoreOf 2 L2 = pCoreOf 2 Eβ := hQ2eq
    have hnat : NatSec (oTwoPrime Eβ) (centerOf (oTwoPrime Eβ)) (pCoreOf 2 Eβ) := hV2.nat
    rw [hQ2eq', hL2eq']
    exact hnat
  · let Eβ := f112saP2' L1 L2 S
    have hL2eq' : L2 = oTwoPrime Eβ := hL2eq
    have hQ2eq' : pCoreOf 2 L2 = pCoreOf 2 Eβ := hQ2eq
    have hind : ⁅pCoreOf 2 Eβ, oTwoPrime Eβ⁆ = pCoreOf 2 Eβ := hV2.indec
    rw [hQ2eq', hL2eq']
    exact hind
  · rw [hQ1eq, hQ2eq]; exact hcardInf

theorem f112_sp4_of_treeSp44Data
    {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2)
    {X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112E5 L1 L2 S)}
    (hX0 : X.vert 0 = baseA (f112Gold L1 L2 S))
    (hX1 : X.vert 1 = baseB (f112Gold L1 L2 S))
    (hd : X.TreeSp44Data) :
    IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsSp4Over 2) :=
  isAmalgamOfGroup_sp4_of_sp44LocalData hF h1 h2
    (f112_sp44LocalData_of_treeSp44Data hF h1 h2 hX0 hX1 hd)

end CFSG.Quasithin.F112R.St84
