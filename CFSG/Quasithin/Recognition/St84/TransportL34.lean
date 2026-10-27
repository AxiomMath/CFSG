module

public import CFSG.Quasithin.Recognition.St84.TreeBase
public import CFSG.Quasithin.Recognition.St84.TransferL34Torus
public import CFSG.Quasithin.Recognition.St84.Sec7Main
public import CFSG.Quasithin.Recognition.St84.L34Ident

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.Quasithin.St84
  CFSG.Quasithin.Fan86 CFSG.Quasithin.Fan86.Univ CFSG.GH74.QTGen4.DSGen4
open scoped Pointwise commutatorElement

variable {H : Type} [Group H] [Finite H]

theorem f112_l34VertexData_of_treeL34Data {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2)
    {X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112E5 L1 L2 S)}
    (hX0 : X.vert 0 = baseA (f112Gold L1 L2 S))
    (hX1 : X.vert 1 = baseB (f112Gold L1 L2 S))
    (hd : X.TreeL34Data) :
    L34VertexData (f112saP1' L1 L2 S) ∧
      L34VertexData (f112saP2' L1 L2 S) ∧
      Nat.card ↥(S ⊓ f112saK L1 L2 S) = 2 ^ 6 ∧
      Nat.card ↥(pCoreOf 2 (f112saP1' L1 L2 S) ⊓
        pCoreOf 2 (f112saP2' L1 L2 S)) = 2 ^ 2 := by
  classical
  let D := f112BaseEdgeData hF h1 h2 X hX0 hX1
  have hdX : D.X.TreeL34Data := hd
  have hcD : CharTwoStab (V := Vtx (f112Gold D.L1 D.L2 D.S)) (G := ↥D.E) :=
    f112_charTwoStab hF h1 h2
  have hLα : oTwoPrime D.Pα ≤ f112P1 D.L1 D.L2 D.S := (oTwoPrime_le D.Pα).trans D.le_Pα
  have hLβ : oTwoPrime D.Pβ ≤ f112P2 D.L1 D.L2 D.S := (oTwoPrime_le D.Pβ).trans D.le_Pβ
  have hYα : pCoreOf 2 (oTwoPrime D.Pα) ≤ f112P1 D.L1 D.L2 D.S :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 (oTwoPrime D.Pα)).trans hLα
  have hYβ : pCoreOf 2 (oTwoPrime D.Pβ) ≤ f112P2 D.L1 D.L2 D.S :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 (oTwoPrime D.Pβ)).trans hLβ
  refine ⟨?_, ?_, ?_, ?_⟩
  · show L34VertexData D.Pα
    refine ⟨f112_isL2Quot_oTwoPrime_P1' hF h1 h2, ?_, ?_, ?_⟩
    · have hiff := isElemAbelian_of_map_iff (L1 := D.L1) (L2 := D.L2) (S := D.S)
        (E := D.E) hYα D.pCoreOf_L_zero_map
      rw [pCoreOf_oTwoPrime D.Pα] at hiff
      exact hiff.mp hdX.elem_left
    · show Nat.card ↥(pCoreOf 2 D.Pα) = 16
      have h := card_of_map_eq (L1 := D.L1) (L2 := D.L2) (S := D.S)
        (E := D.E) hYα D.pCoreOf_L_zero_map
      rw [pCoreOf_oTwoPrime D.Pα, hdX.card_left] at h
      rw [h.symm]
      norm_num
    · have hiff := natSec_of_map_iff (L1 := D.L1) (L2 := D.L2) (S := D.S)
        (E := D.E) (L' := D.X.L 0) (K' := ⊥) (Q' := pCoreOf 2 (D.X.L 0))
        (L := oTwoPrime D.Pα) (K := ⊥) (Q := pCoreOf 2 (oTwoPrime D.Pα))
        hLα bot_le hYα D.L_zero_map
        (by
          show (⊥ : Subgroup ↥D.E).map D.E.subtype =
            ((⊥ : Subgroup H).subgroupOf (f112P1 D.L1 D.L2 D.S)).map
              (f112Gold D.L1 D.L2 D.S).ofA
          simp)
        D.pCoreOf_L_zero_map
      rw [pCoreOf_oTwoPrime D.Pα] at hiff
      exact hiff.mp hdX.nat_left
  · show L34VertexData D.Pβ
    refine ⟨f112_isL2Quot_oTwoPrime_P2' hF h1 h2, ?_, ?_, ?_⟩
    · have hiff := isElemAbelian_of_map_iff_ofB (L1 := D.L1) (L2 := D.L2) (S := D.S)
        (E := D.E) hYβ D.pCoreOf_L_one_map
      rw [pCoreOf_oTwoPrime D.Pβ] at hiff
      exact hiff.mp hdX.elem_right
    · show Nat.card ↥(pCoreOf 2 D.Pβ) = 16
      have h := card_of_map_eq_ofB (L1 := D.L1) (L2 := D.L2) (S := D.S)
        (E := D.E) hYβ D.pCoreOf_L_one_map
      rw [pCoreOf_oTwoPrime D.Pβ, hdX.card_right] at h
      rw [h.symm]
      norm_num
    · have hiff := natSec_of_map_iff_ofB (L1 := D.L1) (L2 := D.L2) (S := D.S)
        (E := D.E) (L' := D.X.L 1) (K' := ⊥) (Q' := pCoreOf 2 (D.X.L 1))
        (L := oTwoPrime D.Pβ) (K := ⊥) (Q := pCoreOf 2 (oTwoPrime D.Pβ))
        hLβ bot_le hYβ D.L_one_map
        (by
          show (⊥ : Subgroup ↥D.E).map D.E.subtype =
            ((⊥ : Subgroup H).subgroupOf (f112P2 D.L1 D.L2 D.S)).map
              (f112Gold D.L1 D.L2 D.S).ofB
          simp)
        D.pCoreOf_L_one_map
      rw [pCoreOf_oTwoPrime D.Pβ] at hiff
      exact hiff.mp hdX.nat_right
  · show Nat.card ↥(S ⊓ D.Ke) = 2 ^ 6
    have hKe : pCoreOf 2 D.Ke = S ⊓ D.Ke := by
      show pCoreOf 2 (f112saK L1 L2 S) = S ⊓ f112saK L1 L2 S
      exact f112_pCoreOf_K_eq hF h1 h2
    have hY : S ⊓ D.Ke ≤ f112P1 D.L1 D.L2 D.S :=
      (inf_le_right : S ⊓ D.Ke ≤ D.Ke).trans (D.le_Ke.trans inf_le_left)
    have hmap : (D.X.S).map D.E.subtype = f112OfA D.L1 D.L2 D.S (S ⊓ D.Ke) := by
      rw [D.S_map, hKe]
    have h := card_of_map_eq (L1 := D.L1) (L2 := D.L2) (S := D.S) (E := D.E) hY hmap
    rw [hdX.card_S] at h
    exact h.symm
  · show Nat.card ↥(pCoreOf 2 D.Pα ⊓ pCoreOf 2 D.Pβ) = 2 ^ 2
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
    have hcardQ : Nat.card ↥(D.X.Q 0 ⊓ D.X.Q 1) = 2 ^ 2 := by
      haveI : Finite ↥(D.X.Gi 0) := D.X.hyp.finite_stab (D.X.vert 0)
      haveI : Finite ↥(D.X.Gi 1) := D.X.hyp.finite_stab (D.X.vert 1)
      have h := hdX.card_inf
      rw [pCoreOf_oTwoPrime (D.X.Gi 0), pCoreOf_oTwoPrime (D.X.Gi 1)] at h
      exact h
    have h := card_of_map_eq (L1 := D.L1) (L2 := D.L2) (S := D.S)
      (E := D.E) hY hmap
    rw [hcardQ] at h
    exact h.symm

theorem f112_S_le_K_of_l34VertexData {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2)
    (hV1 : L34VertexData (f112saP1' L1 L2 S))
    (hV2 : L34VertexData (f112saP2' L1 L2 S)) :
    S ≤ f112saK L1 L2 S :=
  f112sa_le_K_of_transfer hF h1 h2
    (transferVertexData_of_l34VertexData hV1)
    (transferVertexData_of_l34VertexData hV2)
    (f112_pCoreOf_sup_eq hF h1 h2).symm

theorem f112_l34LocalData_of_treeL34Data {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2)
    {X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112E5 L1 L2 S)}
    (hX0 : X.vert 0 = baseA (f112Gold L1 L2 S))
    (hX1 : X.vert 1 = baseB (f112Gold L1 L2 S))
    (hd : X.TreeL34Data) :
    L34LocalData L1 L2 S := by
  obtain ⟨hV1, hV2, hcardT, hcardInf⟩ :=
    f112_l34VertexData_of_treeL34Data hF h1 h2 hX0 hX1 hd
  have hV1' : TransferVertexData (f112saP1' L1 L2 S) := transferVertexData_of_l34VertexData hV1
  have hV2' : TransferVertexData (f112saP2' L1 L2 S) := transferVertexData_of_l34VertexData hV2
  have hS : S ≤ f112saK L1 L2 S := f112_S_le_K_of_l34VertexData hF h1 h2 hV1 hV2
  obtain ⟨-, hL1eq, hQ1eq⟩ :=
    f112sa_S_le_L1_and_eq_oTwoPrime_of_transferVertexData hF h1 hS hV1'
  obtain ⟨-, hL2eq, hQ2eq⟩ :=
    f112sa_S_le_L2_and_eq_oTwoPrime_of_transferVertexData hF h2 hS hV2'
  refine
    { bigB_le := (f112sa_bigB_le_inf_of_l34Data hF h1 h2 hV1 hV2
        (f112_pCoreOf_sup_eq hF h1 h2).symm).1
      card_S := ?_
      elem_left := ?_
      card_left := ?_
      nat_left := ?_
      elem_right := ?_
      card_right := ?_
      nat_right := ?_
      card_inf := ?_ }
  · have h : S ⊓ f112saK L1 L2 S = S := inf_eq_left.mpr hS
    simpa [h] using hcardT
  · rw [hQ1eq]; exact hV1.elem
  · rw [hQ1eq, hV1.card]; norm_num
  · have h := hV1.nat
    rw [← hQ1eq, ← hL1eq] at h
    exact h
  · rw [hQ2eq]; exact hV2.elem
  · rw [hQ2eq, hV2.card]; norm_num
  · have h := hV2.nat
    rw [← hQ2eq, ← hL2eq] at h
    exact h
  · rw [hQ1eq, hQ2eq]; exact hcardInf

theorem f112_l34LocalData_of_even_singularity
    {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2) {s : ℕ}
    (hs : IsSingularity (f112Gold L1 L2 S).treeGraph ↥(f112E5 L1 L2 S) s) (hev : Even s) :
    L34LocalData L1 L2 S := by
  classical
  obtain ⟨X, hX0, hX1⟩ := f112_exists_setup_baseEdge hF h1 h2
  obtain ⟨-, hd⟩ := sec7_A5A5_even (f112_hyp30 hF h1 h2) (f112_charTwoStab hF h1 h2)
    (f112_nOf_eq_two hF h1 h2) hs hev X
  exact f112_l34LocalData_of_treeL34Data hF h1 h2 hX0 hX1 hd

theorem f112_psl3_of_even_singularity
    {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2) {s : ℕ}
    (hs : IsSingularity (f112Gold L1 L2 S).treeGraph ↥(f112E5 L1 L2 S) s) (hev : Even s) :
    IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsLieOverTwo .PSL 3 2) :=
  isAmalgamOfGroup_psl3_of_l34LocalData hF h1 h2
    (f112_l34LocalData_of_even_singularity hF h1 h2 hs hev)

end CFSG.Quasithin.F112R.St84
