module

public import CFSG.Quasithin.Recognition.St84.AppTreeE5
public import CFSG.Quasithin.Recognition.St84.Gen.TreeSLHyp
public import CFSG.Quasithin.Recognition.St84.TransferSetup
public import CFSG.Quasithin.Recognition.St84.Sec7Setup
public import CFSG.Quasithin.Recognition.St84.TransportMap
public import CFSG.Quasithin.Background.SimsD1TransGrp
public import CFSG.Quasithin.H13.GoldschmidtC137Baum
public import CFSG.GroupTheory.Commutator.SubgroupOf
public import CFSG.GH74.QTGen4.DSGen4.Statements

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.Quasithin.St84
  CFSG.Quasithin.Fan86 CFSG.Quasithin.Fan86.Univ CFSG.GH74.QTGen4.DSGen4
open scoped Pointwise commutatorElement

variable {H : Type} [Group H] [Finite H]

abbrev f112OfA (L1 L2 S : Subgroup H) (Y : Subgroup H) :
    Subgroup (f112Gold L1 L2 S).Universal :=
  (Y.subgroupOf (f112P1 L1 L2 S)).map (f112Gold L1 L2 S).ofA

abbrev f112OfB (L1 L2 S : Subgroup H) (Y : Subgroup H) :
    Subgroup (f112Gold L1 L2 S).Universal :=
  (Y.subgroupOf (f112P2 L1 L2 S)).map (f112Gold L1 L2 S).ofB

@[simp] theorem f112OfA_top (L1 L2 S : Subgroup H) :
    f112OfA L1 L2 S ⊤ = (f112Gold L1 L2 S).ofA.range := by
  show ((⊤ : Subgroup H).subgroupOf (f112P1 L1 L2 S)).map (f112Gold L1 L2 S).ofA = _
  rw [Subgroup.top_subgroupOf, Subgroup.map_top]

@[simp] theorem f112OfB_top (L1 L2 S : Subgroup H) :
    f112OfB L1 L2 S ⊤ = (f112Gold L1 L2 S).ofB.range := by
  show ((⊤ : Subgroup H).subgroupOf (f112P2 L1 L2 S)).map (f112Gold L1 L2 S).ofB = _
  rw [Subgroup.top_subgroupOf, Subgroup.map_top]

theorem f112OfA_sup {L1 L2 S : Subgroup H} {A B : Subgroup H}
    (hA : A ≤ f112P1 L1 L2 S) (hB : B ≤ f112P1 L1 L2 S) :
    f112OfA L1 L2 S (A ⊔ B) = f112OfA L1 L2 S A ⊔ f112OfA L1 L2 S B := by
  show ((A ⊔ B).subgroupOf (f112P1 L1 L2 S)).map (f112Gold L1 L2 S).ofA = _
  rw [Subgroup.subgroupOf_sup hA hB, Subgroup.map_sup]

theorem f112_ofA_pCoreOf (L1 L2 S : Subgroup H) {Y : Subgroup H}
    (hY : Y ≤ f112P1 L1 L2 S) :
    pCoreOf 2 (f112OfA L1 L2 S Y) = f112OfA L1 L2 S (pCoreOf 2 Y) := by
  show pCoreOf 2 ((Y.subgroupOf (f112P1 L1 L2 S)).map (f112Gold L1 L2 S).ofA) = _
  rw [pCoreOf_map_injective (f112Gold L1 L2 S).ofA (f112Gold L1 L2 S).ofA_injective,
    CFSG.Quasithin.H13.U3.GC137.pCoreOf_subgroupOf_eq hY]

theorem f112_ofB_pCoreOf (L1 L2 S : Subgroup H) {Y : Subgroup H}
    (hY : Y ≤ f112P2 L1 L2 S) :
    pCoreOf 2 (f112OfB L1 L2 S Y) = f112OfB L1 L2 S (pCoreOf 2 Y) := by
  show pCoreOf 2 ((Y.subgroupOf (f112P2 L1 L2 S)).map (f112Gold L1 L2 S).ofB) = _
  rw [pCoreOf_map_injective (f112Gold L1 L2 S).ofB (f112Gold L1 L2 S).ofB_injective,
    CFSG.Quasithin.H13.U3.GC137.pCoreOf_subgroupOf_eq hY]

theorem f112_ofA_oTwoPrime (L1 L2 S : Subgroup H) {Y : Subgroup H}
    (hY : Y ≤ f112P1 L1 L2 S) :
    oTwoPrime (f112OfA L1 L2 S Y) = f112OfA L1 L2 S (oTwoPrime Y) := by
  have hside : oTwoPrime (Y.subgroupOf (f112P1 L1 L2 S)) =
      (oTwoPrime Y).subgroupOf (f112P1 L1 L2 S) := by
    refine Subgroup.map_injective (f := (f112P1 L1 L2 S).subtype)
      (f112P1 L1 L2 S).subtype_injective ?_
    rw [← oTwoPrime_map (f := (f112P1 L1 L2 S).subtype)
        (f112P1 L1 L2 S).subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hY,
      Subgroup.map_subgroupOf_eq_of_le ((oTwoPrime_le Y).trans hY)]
  show oTwoPrime ((Y.subgroupOf (f112P1 L1 L2 S)).map (f112Gold L1 L2 S).ofA) = _
  rw [oTwoPrime_map (f := (f112Gold L1 L2 S).ofA) (f112Gold L1 L2 S).ofA_injective, hside]

theorem f112_ofB_oTwoPrime (L1 L2 S : Subgroup H) {Y : Subgroup H}
    (hY : Y ≤ f112P2 L1 L2 S) :
    oTwoPrime (f112OfB L1 L2 S Y) = f112OfB L1 L2 S (oTwoPrime Y) := by
  have hside : oTwoPrime (Y.subgroupOf (f112P2 L1 L2 S)) =
      (oTwoPrime Y).subgroupOf (f112P2 L1 L2 S) := by
    refine Subgroup.map_injective (f := (f112P2 L1 L2 S).subtype)
      (f112P2 L1 L2 S).subtype_injective ?_
    rw [← oTwoPrime_map (f := (f112P2 L1 L2 S).subtype)
        (f112P2 L1 L2 S).subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hY,
      Subgroup.map_subgroupOf_eq_of_le ((oTwoPrime_le Y).trans hY)]
  show oTwoPrime ((Y.subgroupOf (f112P2 L1 L2 S)).map (f112Gold L1 L2 S).ofB) = _
  rw [oTwoPrime_map (f := (f112Gold L1 L2 S).ofB) (f112Gold L1 L2 S).ofB_injective, hside]

theorem centerOf_subgroupOf {Y P : Subgroup H} (hY : Y ≤ P) :
    centerOf (Y.subgroupOf P) = (centerOf Y).subgroupOf P := by
  ext x
  simp only [centerOf, Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff,
    SetLike.mem_coe]
  constructor
  · rintro ⟨hx, hc⟩
    refine ⟨hx, fun a ha => ?_⟩
    have := hc ⟨a, hY ha⟩ ha
    exact congrArg Subtype.val this
  · rintro ⟨hx, hc⟩
    refine ⟨hx, fun a ha => Subtype.ext (hc a ha)⟩

theorem centerOf_map_eq_of_le {U : Type} [Group U] {P : Subgroup H} {φ : ↥P →* U}
    (hφ : Function.Injective φ) {Y : Subgroup H} (hY : Y ≤ P) :
    centerOf ((Y.subgroupOf P).map φ) = ((centerOf Y).subgroupOf P).map φ := by
  rw [CFSG.Quasithin.SimsD1.TransGrp.centerOf_map_eq φ hφ, centerOf_subgroupOf hY]

theorem f112_ofA_centerOf (L1 L2 S : Subgroup H) {Y : Subgroup H}
    (hY : Y ≤ f112P1 L1 L2 S) :
    centerOf (f112OfA L1 L2 S Y) = f112OfA L1 L2 S (centerOf Y) :=
  centerOf_map_eq_of_le (f112Gold L1 L2 S).ofA_injective hY

theorem f112_ofB_centerOf (L1 L2 S : Subgroup H) {Y : Subgroup H}
    (hY : Y ≤ f112P2 L1 L2 S) :
    centerOf (f112OfB L1 L2 S Y) = f112OfB L1 L2 S (centerOf Y) :=
  centerOf_map_eq_of_le (f112Gold L1 L2 S).ofB_injective hY

theorem commutator_map_eq_of_le {U : Type} [Group U] {P : Subgroup H} {φ : ↥P →* U}
    {A B : Subgroup H} (hA : A ≤ P) (hB : B ≤ P) :
    ⁅(A.subgroupOf P).map φ, (B.subgroupOf P).map φ⁆ = (⁅A, B⁆.subgroupOf P).map φ := by
  rw [← Subgroup.map_commutator, CFSG.GroupTheory.commutator_subgroupOf_eq hA hB]

theorem f112_ofA_commutator (L1 L2 S : Subgroup H) {A B : Subgroup H}
    (hA : A ≤ f112P1 L1 L2 S) (hB : B ≤ f112P1 L1 L2 S) :
    ⁅f112OfA L1 L2 S A, f112OfA L1 L2 S B⁆ = f112OfA L1 L2 S ⁅A, B⁆ :=
  commutator_map_eq_of_le hA hB

theorem f112_ofB_commutator (L1 L2 S : Subgroup H) {A B : Subgroup H}
    (hA : A ≤ f112P2 L1 L2 S) (hB : B ≤ f112P2 L1 L2 S) :
    ⁅f112OfB L1 L2 S A, f112OfB L1 L2 S B⁆ = f112OfB L1 L2 S ⁅A, B⁆ :=
  commutator_map_eq_of_le hA hB

theorem f112_stabilizer_baseA_map (L1 L2 S : Subgroup H)
    (E : Subgroup (f112Gold L1 L2 S).Universal) :
    (MulAction.stabilizer ↥E (baseA (f112Gold L1 L2 S))).map E.subtype =
      E ⊓ (f112Gold L1 L2 S).ofA.range := by
  rw [← MulAction.stabilizer_subgroupOf E (baseA (f112Gold L1 L2 S)),
    stabilizer_baseA (f112Gold L1 L2 S), ← Subgroup.inf_subgroupOf_left,
    Subgroup.map_subgroupOf_eq_of_le inf_le_left]

theorem f112_stabilizer_baseB_map (L1 L2 S : Subgroup H)
    (E : Subgroup (f112Gold L1 L2 S).Universal) :
    (MulAction.stabilizer ↥E (baseB (f112Gold L1 L2 S))).map E.subtype =
      E ⊓ (f112Gold L1 L2 S).ofB.range := by
  rw [← MulAction.stabilizer_subgroupOf E (baseB (f112Gold L1 L2 S)),
    stabilizer_baseB (f112Gold L1 L2 S), ← Subgroup.inf_subgroupOf_left,
    Subgroup.map_subgroupOf_eq_of_le inf_le_left]

structure BaseEdgeData (H : Type) [Group H] where
  L1 : Subgroup H
  L2 : Subgroup H
  S : Subgroup H
  E : Subgroup (f112Gold L1 L2 S).Universal
  Pα : Subgroup H
  Pβ : Subgroup H
  Ke : Subgroup H
  le_Pα : Pα ≤ f112P1 L1 L2 S
  le_Pβ : Pβ ≤ f112P2 L1 L2 S
  le_Ke : Ke ≤ f112P1 L1 L2 S ⊓ f112P2 L1 L2 S
  ofA_eq : E ⊓ (f112Gold L1 L2 S).ofA.range = f112OfA L1 L2 S Pα
  ofB_eq : E ⊓ (f112Gold L1 L2 S).ofB.range = f112OfB L1 L2 S Pβ
  ofA_inf_ofB_eq : E ⊓ (f112Gold L1 L2 S).ofA.range ⊓ (f112Gold L1 L2 S).ofB.range =
    f112OfA L1 L2 S Ke
  X : Setup (f112Gold L1 L2 S).treeGraph ↥E
  X_zero : X.vert 0 = baseA (f112Gold L1 L2 S)
  X_one : X.vert 1 = baseB (f112Gold L1 L2 S)

theorem BaseEdgeData.gi_zero_map (D : BaseEdgeData H) :
    (D.X.Gi 0).map D.E.subtype = f112OfA D.L1 D.L2 D.S D.Pα := by
  show (MulAction.stabilizer ↥D.E (D.X.vert 0)).map D.E.subtype = _
  rw [D.X_zero, f112_stabilizer_baseA_map D.L1 D.L2 D.S D.E, D.ofA_eq]

theorem BaseEdgeData.gi_one_map (D : BaseEdgeData H) :
    (D.X.Gi 1).map D.E.subtype = f112OfB D.L1 D.L2 D.S D.Pβ := by
  show (MulAction.stabilizer ↥D.E (D.X.vert 1)).map D.E.subtype = _
  rw [D.X_one, f112_stabilizer_baseB_map D.L1 D.L2 D.S D.E, D.ofB_eq]

theorem BaseEdgeData.gi_inf_map (D : BaseEdgeData H) :
    (D.X.Gi 0 ⊓ D.X.Gi 1).map D.E.subtype = f112OfA D.L1 D.L2 D.S D.Ke := by
  rw [Subgroup.map_inf (D.X.Gi 0) (D.X.Gi 1) D.E.subtype D.E.subtype_injective,
    D.gi_zero_map, D.gi_one_map, ← D.ofA_eq, ← D.ofB_eq, ← D.ofA_inf_ofB_eq]
  simp only [inf_assoc, inf_left_comm, inf_idem, inf_left_idem, inf_right_idem]

theorem BaseEdgeData.Q_zero_map (D : BaseEdgeData H) :
    (D.X.Q 0).map D.E.subtype = f112OfA D.L1 D.L2 D.S (pCoreOf 2 D.Pα) := by
  rw [← pCoreOf_map_injective (f := D.E.subtype) D.E.subtype_injective, D.gi_zero_map]
  exact f112_ofA_pCoreOf D.L1 D.L2 D.S D.le_Pα

theorem BaseEdgeData.Q_one_map (D : BaseEdgeData H) :
    (D.X.Q 1).map D.E.subtype = f112OfB D.L1 D.L2 D.S (pCoreOf 2 D.Pβ) := by
  rw [← pCoreOf_map_injective (f := D.E.subtype) D.E.subtype_injective, D.gi_one_map]
  exact f112_ofB_pCoreOf D.L1 D.L2 D.S D.le_Pβ

theorem BaseEdgeData.L_zero_map (D : BaseEdgeData H) :
    (D.X.L 0).map D.E.subtype = f112OfA D.L1 D.L2 D.S (oTwoPrime D.Pα) := by
  rw [← oTwoPrime_map (f := D.E.subtype) D.E.subtype_injective, D.gi_zero_map]
  exact f112_ofA_oTwoPrime D.L1 D.L2 D.S D.le_Pα

theorem BaseEdgeData.L_one_map (D : BaseEdgeData H) :
    (D.X.L 1).map D.E.subtype = f112OfB D.L1 D.L2 D.S (oTwoPrime D.Pβ) := by
  rw [← oTwoPrime_map (f := D.E.subtype) D.E.subtype_injective, D.gi_one_map]
  exact f112_ofB_oTwoPrime D.L1 D.L2 D.S D.le_Pβ

theorem BaseEdgeData.S_map (D : BaseEdgeData H) :
    (D.X.S).map D.E.subtype = f112OfA D.L1 D.L2 D.S (pCoreOf 2 D.Ke) := by
  rw [← pCoreOf_map_injective (f := D.E.subtype) D.E.subtype_injective, D.gi_inf_map]
  exact f112_ofA_pCoreOf D.L1 D.L2 D.S (D.le_Ke.trans inf_le_left)

theorem BaseEdgeData.pCoreOf_L_zero_map (D : BaseEdgeData H) :
    (pCoreOf 2 (D.X.L 0)).map D.E.subtype =
      f112OfA D.L1 D.L2 D.S (pCoreOf 2 (oTwoPrime D.Pα)) := by
  rw [← pCoreOf_map_injective (f := D.E.subtype) D.E.subtype_injective, D.L_zero_map]
  exact f112_ofA_pCoreOf D.L1 D.L2 D.S ((oTwoPrime_le D.Pα).trans D.le_Pα)

theorem BaseEdgeData.pCoreOf_L_one_map (D : BaseEdgeData H) :
    (pCoreOf 2 (D.X.L 1)).map D.E.subtype =
      f112OfB D.L1 D.L2 D.S (pCoreOf 2 (oTwoPrime D.Pβ)) := by
  rw [← pCoreOf_map_injective (f := D.E.subtype) D.E.subtype_injective, D.L_one_map]
  exact f112_ofB_pCoreOf D.L1 D.L2 D.S ((oTwoPrime_le D.Pβ).trans D.le_Pβ)

theorem card_of_map_eq_of_le {U : Type} [Group U] {P : Subgroup H} {φ : ↥P →* U}
    (hφ : Function.Injective φ) {E : Subgroup U} {Y' : Subgroup ↥E} {Y : Subgroup H}
    (hY : Y ≤ P) (h : Y'.map E.subtype = (Y.subgroupOf P).map φ) :
    Nat.card ↥Y' = Nat.card ↥Y := by
  rw [← Subgroup.card_map_of_injective (f := E.subtype) (K := Y') E.subtype_injective, h]
  rw [Subgroup.card_map_of_injective (f := φ) (K := Y.subgroupOf P) hφ]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hY).toEquiv

theorem card_of_map_eq {L1 L2 S : Subgroup H} {E : Subgroup (f112Gold L1 L2 S).Universal}
    {Y' : Subgroup ↥E} {Y : Subgroup H} (hY : Y ≤ f112P1 L1 L2 S)
    (h : Y'.map E.subtype = f112OfA L1 L2 S Y) :
    Nat.card ↥Y' = Nat.card ↥Y :=
  card_of_map_eq_of_le (f112Gold L1 L2 S).ofA_injective hY h

theorem card_of_map_eq_ofB {L1 L2 S : Subgroup H}
    {E : Subgroup (f112Gold L1 L2 S).Universal} {Y' : Subgroup ↥E} {Y : Subgroup H}
    (hY : Y ≤ f112P2 L1 L2 S) (h : Y'.map E.subtype = f112OfB L1 L2 S Y) :
    Nat.card ↥Y' = Nat.card ↥Y :=
  card_of_map_eq_of_le (f112Gold L1 L2 S).ofB_injective hY h

theorem isElemAbelian_map_iff_of_le {U : Type} [Group U] {P : Subgroup H} {φ : ↥P →* U}
    (hφ : Function.Injective φ) {E : Subgroup U} {Y' : Subgroup ↥E} {Y : Subgroup H}
    (hY : Y ≤ P) (h : Y'.map E.subtype = (Y.subgroupOf P).map φ) :
    IsElemAbelian 2 Y' ↔ IsElemAbelian 2 Y := by
  have hiff : IsElemAbelian 2 (Y.subgroupOf P) ↔ IsElemAbelian 2 Y := by
    constructor
    · intro h'
      have h2 := h'.map (f := P.subtype)
      rwa [Subgroup.map_subgroupOf_eq_of_le hY] at h2
    · intro h'
      exact h'.subgroupOf P
  rw [← CFSG.Quasithin.SimsD1.TransGrp.isElemAbelian_map_iff (f := E.subtype)
    E.subtype_injective 2 Y', h]
  rw [CFSG.Quasithin.SimsD1.TransGrp.isElemAbelian_map_iff (f := φ) hφ 2 (Y.subgroupOf P)]
  exact hiff

theorem isElemAbelian_of_map_iff {L1 L2 S : Subgroup H}
    {E : Subgroup (f112Gold L1 L2 S).Universal} {Y' : Subgroup ↥E} {Y : Subgroup H}
    (hY : Y ≤ f112P1 L1 L2 S) (h : Y'.map E.subtype = f112OfA L1 L2 S Y) :
    IsElemAbelian 2 Y' ↔ IsElemAbelian 2 Y :=
  isElemAbelian_map_iff_of_le (f112Gold L1 L2 S).ofA_injective hY h

theorem isElemAbelian_of_map_iff_ofB {L1 L2 S : Subgroup H}
    {E : Subgroup (f112Gold L1 L2 S).Universal} {Y' : Subgroup ↥E} {Y : Subgroup H}
    (hY : Y ≤ f112P2 L1 L2 S) (h : Y'.map E.subtype = f112OfB L1 L2 S Y) :
    IsElemAbelian 2 Y' ↔ IsElemAbelian 2 Y :=
  isElemAbelian_map_iff_of_le (f112Gold L1 L2 S).ofB_injective hY h

theorem natSec_subgroupOf_iff {P L K Q : Subgroup H} (hL : L ≤ P) (hK : K ≤ P) (hQ : Q ≤ P) :
    NatSec (L.subgroupOf P) (K.subgroupOf P) (Q.subgroupOf P) ↔ NatSec L K Q := by
  unfold NatSec FixFree
  constructor
  · intro h x hxL hx3 e heQ hc
    have hx3' : orderOf (⟨x, hL hxL⟩ : ↥P) = 3 := by
      rw [← Subgroup.orderOf_coe]
      exact hx3
    have hc' : (⁅(⟨e, hQ heQ⟩ : ↥P), (⟨x, hL hxL⟩ : ↥P)⁆ : ↥P) ∈ K.subgroupOf P := by
      rw [Subgroup.mem_subgroupOf]
      have hcoe : ((⁅(⟨e, hQ heQ⟩ : ↥P), (⟨x, hL hxL⟩ : ↥P)⁆ : ↥P) : H) = ⁅e, x⁆ :=
        map_commutatorElement P.subtype _ _
      rw [hcoe]
      exact hc
    exact Subgroup.mem_subgroupOf.mp (h ⟨x, hL hxL⟩ hxL hx3' ⟨e, hQ heQ⟩ heQ hc')
  · intro h x hxL hx3 e heQ hc
    have hx3H : orderOf ((x : ↥P) : H) = 3 := by
      rw [Subgroup.orderOf_coe]
      exact hx3
    have hcH : ⁅((e : ↥P) : H), ((x : ↥P) : H)⁆ ∈ K := by
      have hcoe : ((⁅e, x⁆ : ↥P) : H) = ⁅((e : ↥P) : H), ((x : ↥P) : H)⁆ :=
        map_commutatorElement P.subtype e x
      rw [← hcoe]
      exact Subgroup.mem_subgroupOf.mp hc
    exact Subgroup.mem_subgroupOf.mpr (h ((x : ↥P) : H) hxL hx3H ((e : ↥P) : H) heQ hcH)

theorem natSec_map_iff_of_le {U : Type} [Group U] {P : Subgroup H} {φ : ↥P →* U}
    (hφ : Function.Injective φ) {E : Subgroup U} {L' K' Q' : Subgroup ↥E}
    {L K Q : Subgroup H} (hL : L ≤ P) (hK : K ≤ P) (hQ : Q ≤ P)
    (hL' : L'.map E.subtype = (L.subgroupOf P).map φ)
    (hK' : K'.map E.subtype = (K.subgroupOf P).map φ)
    (hQ' : Q'.map E.subtype = (Q.subgroupOf P).map φ) :
    NatSec L' K' Q' ↔ NatSec L K Q := by
  rw [← NatSec.map_iff (f := E.subtype) E.subtype_injective, hL', hK', hQ',
    NatSec.map_iff (f := φ) hφ]
  exact natSec_subgroupOf_iff hL hK hQ

theorem natSec_of_map_iff {L1 L2 S : Subgroup H}
    {E : Subgroup (f112Gold L1 L2 S).Universal} {L' K' Q' : Subgroup ↥E}
    {L K Q : Subgroup H} (hL : L ≤ f112P1 L1 L2 S) (hK : K ≤ f112P1 L1 L2 S)
    (hQ : Q ≤ f112P1 L1 L2 S) (hL' : L'.map E.subtype = f112OfA L1 L2 S L)
    (hK' : K'.map E.subtype = f112OfA L1 L2 S K)
    (hQ' : Q'.map E.subtype = f112OfA L1 L2 S Q) :
    NatSec L' K' Q' ↔ NatSec L K Q :=
  natSec_map_iff_of_le (f112Gold L1 L2 S).ofA_injective hL hK hQ hL' hK' hQ'

theorem natSec_of_map_iff_ofB {L1 L2 S : Subgroup H}
    {E : Subgroup (f112Gold L1 L2 S).Universal} {L' K' Q' : Subgroup ↥E}
    {L K Q : Subgroup H} (hL : L ≤ f112P2 L1 L2 S) (hK : K ≤ f112P2 L1 L2 S)
    (hQ : Q ≤ f112P2 L1 L2 S) (hL' : L'.map E.subtype = f112OfB L1 L2 S L)
    (hK' : K'.map E.subtype = f112OfB L1 L2 S K)
    (hQ' : Q'.map E.subtype = f112OfB L1 L2 S Q) :
    NatSec L' K' Q' ↔ NatSec L K Q :=
  natSec_map_iff_of_le (f112Gold L1 L2 S).ofB_injective hL hK hQ hL' hK' hQ'

theorem isL2Quot_of_map_iff (L1 L2 S : Subgroup H)
    {E : Subgroup (f112Gold L1 L2 S).Universal} {Y' : Subgroup ↥E} {Y : Subgroup H}
    (hY : Y ≤ f112P1 L1 L2 S) (h : Y'.map E.subtype = f112OfA L1 L2 S Y) (n : ℕ) :
    IsL2Quot n (oTwoQuot ↥Y') ↔ IsL2Quot n (oTwoQuot ↥Y) := by
  have hmap : Y'.map E.subtype =
      (Y.subgroupOf (f112P1 L1 L2 S)).map (f112Gold L1 L2 S).ofA := h
  let e : ↥Y' ≃* ↥Y :=
    (Subgroup.equivMapOfInjective Y' E.subtype E.subtype_injective).trans
      ((MulEquiv.subgroupCongr hmap).trans
        ((Subgroup.equivMapOfInjective (Y.subgroupOf (f112P1 L1 L2 S))
          (f112Gold L1 L2 S).ofA (f112Gold L1 L2 S).ofA_injective).symm.trans
          (Subgroup.subgroupOfEquivOfLe hY)))
  have he : oTwoQuot ↥Y' ≃* oTwoQuot ↥Y := oTwoQuotMulEquiv e
  constructor
  · rintro ⟨e2⟩
    exact ⟨he.symm.trans e2⟩
  · rintro ⟨e2⟩
    exact ⟨he.trans e2⟩

theorem isL2Quot_of_map_iff_ofB (L1 L2 S : Subgroup H)
    {E : Subgroup (f112Gold L1 L2 S).Universal} {Y' : Subgroup ↥E} {Y : Subgroup H}
    (hY : Y ≤ f112P2 L1 L2 S) (h : Y'.map E.subtype = f112OfB L1 L2 S Y) (n : ℕ) :
    IsL2Quot n (oTwoQuot ↥Y') ↔ IsL2Quot n (oTwoQuot ↥Y) := by
  have hmap : Y'.map E.subtype =
      (Y.subgroupOf (f112P2 L1 L2 S)).map (f112Gold L1 L2 S).ofB := h
  let e : ↥Y' ≃* ↥Y :=
    (Subgroup.equivMapOfInjective Y' E.subtype E.subtype_injective).trans
      ((MulEquiv.subgroupCongr hmap).trans
        ((Subgroup.equivMapOfInjective (Y.subgroupOf (f112P2 L1 L2 S))
          (f112Gold L1 L2 S).ofB (f112Gold L1 L2 S).ofB_injective).symm.trans
          (Subgroup.subgroupOfEquivOfLe hY)))
  have he : oTwoQuot ↥Y' ≃* oTwoQuot ↥Y := oTwoQuotMulEquiv e
  constructor
  · rintro ⟨e2⟩
    exact ⟨he.symm.trans e2⟩
  · rintro ⟨e2⟩
    exact ⟨he.trans e2⟩

theorem ofA_subgroupOf_eq_ofB_subgroupOf (L1 L2 S : Subgroup H) {Y : Subgroup H}
    (hY : Y ≤ f112P1 L1 L2 S ⊓ f112P2 L1 L2 S) :
    f112OfA L1 L2 S Y = f112OfB L1 L2 S Y := by
  refine le_antisymm ?_ ?_
  · rintro u ⟨y, hy, rfl⟩
    have hyY : (y : H) ∈ Y := Subgroup.mem_subgroupOf.mp hy
    exact ⟨⟨(y : H), (hY hyY).2⟩, hyY,
      (f112sa_ofA_eq_ofB_of_mem_inf L1 L2 S ⟨y.2, (hY hyY).2⟩).symm⟩
  · rintro u ⟨z, hz, rfl⟩
    have hzY : (z : H) ∈ Y := Subgroup.mem_subgroupOf.mp hz
    exact ⟨⟨(z : H), (hY hzY).1⟩, hzY,
      (f112sa_ofA_eq_ofB_of_mem_inf L1 L2 S ⟨(hY hzY).1, z.2⟩)⟩

@[simp] theorem f112Gold_toA_val (L1 L2 S : Subgroup H)
    (c : ↥(f112P1 L1 L2 S ⊓ f112P2 L1 L2 S)) :
    ((f112Gold L1 L2 S).toA c : H) = (c : H) := rfl

@[simp] theorem f112Gold_toB_val (L1 L2 S : Subgroup H)
    (c : ↥(f112P1 L1 L2 S ⊓ f112P2 L1 L2 S)) :
    ((f112Gold L1 L2 S).toB c : H) = (c : H) := rfl

theorem ofA_map_inf_ofB_map (L1 L2 S : Subgroup H) {Y Z : Subgroup H}
    (hY : Y ≤ f112P1 L1 L2 S) (hZ : Z ≤ f112P2 L1 L2 S) :
    f112OfA L1 L2 S Y ⊓ f112OfB L1 L2 S Z = f112OfA L1 L2 S (Y ⊓ Z) := by
  refine le_antisymm ?_ ?_
  · rintro u ⟨huA, huB⟩
    obtain ⟨y, hy, rfl⟩ := huA
    obtain ⟨z, hz, hzy⟩ := huB
    have hyY : (y : H) ∈ Y := Subgroup.mem_subgroupOf.mp hy
    have hzZ : (z : H) ∈ Z := Subgroup.mem_subgroupOf.mp hz
    have huBase : (f112Gold L1 L2 S).ofA y ∈
        (Monoid.PushoutI.base (f112Gold L1 L2 S).diagram).range := by
      rw [← (f112Gold L1 L2 S).ofA_range_inf_ofB_range]
      exact ⟨⟨y, rfl⟩, ⟨z, hzy⟩⟩
    obtain ⟨c, hc⟩ := huBase
    have htoA : (f112Gold L1 L2 S).toA c = y :=
      (f112Gold L1 L2 S).ofA_injective (by rw [(f112Gold L1 L2 S).ofA_toA, hc])
    have htoB : (f112Gold L1 L2 S).toB c = z :=
      (f112Gold L1 L2 S).ofB_injective (by rw [(f112Gold L1 L2 S).ofB_toB, hc, hzy])
    have hcy : (c : H) = (y : H) := by
      rw [← f112Gold_toA_val L1 L2 S c]
      exact congrArg (fun w : ↥(f112P1 L1 L2 S) => (w : H)) htoA
    have hcz : (c : H) = (z : H) := by
      rw [← f112Gold_toB_val L1 L2 S c]
      exact congrArg (fun w : ↥(f112P2 L1 L2 S) => (w : H)) htoB
    have hyZ : (y : H) ∈ Z := by
      rw [← hcy, hcz]
      exact hzZ
    exact Subgroup.mem_map.mpr ⟨⟨(y : H), hY hyY⟩, ⟨hyY, hyZ⟩, rfl⟩
  · refine le_inf ?_ ?_
    · exact Subgroup.map_mono (Subgroup.subgroupOf_mono (f112P1 L1 L2 S) inf_le_left)
    · rintro u ⟨a, ha, rfl⟩
      have haZ : (a : H) ∈ Z := (Subgroup.mem_subgroupOf.mp ha).2
      exact ⟨⟨(a : H), hZ haZ⟩, Subgroup.mem_subgroupOf.mpr haZ,
        (f112sa_ofA_eq_ofB_of_mem_inf L1 L2 S ⟨a.2, hZ haZ⟩).symm⟩

theorem eq_pCoreOf_of_isSylowTwoOf {K T : Subgroup H} (hT : IsSylowTwoOf T K)
    (hO : IsSylowTwoOf (pCoreOf 2 K) K) : pCoreOf 2 K = T :=
  F1.eq_of_isSylowTwoOf_le hO hT.1 hT.2.1 (F7.isSylowTwoOf_pCoreOf_le hT)

theorem BaseEdgeData.isSylowTwoOf_pCoreOf (D : BaseEdgeData H) :
    IsSylowTwoOf (pCoreOf 2 D.Ke) D.Ke := by
  have htree : IsSylowTwoOf (D.X.edgeSylow 0) (D.X.Gi 0 ⊓ D.X.Gi 1) :=
    D.X.isSylowTwoOf_edgeSylow 0
  have hmapped : IsSylowTwoOf ((D.X.edgeSylow 0).map D.E.subtype)
      ((D.X.Gi 0 ⊓ D.X.Gi 1).map D.E.subtype) :=
    (CFSG.Quasithin.SimsD1.TransGrp.isSylowTwoOf_map_iff (f := D.E.subtype)
      D.E.subtype_injective (D.X.edgeSylow 0) (D.X.Gi 0 ⊓ D.X.Gi 1)).mpr htree
  rw [Setup.edgeSylow_zero, D.S_map, D.gi_inf_map] at hmapped
  have hsylP : IsSylowTwoOf
      ((pCoreOf 2 D.Ke).subgroupOf (f112P1 D.L1 D.L2 D.S))
      (D.Ke.subgroupOf (f112P1 D.L1 D.L2 D.S)) :=
    (CFSG.Quasithin.SimsD1.TransGrp.isSylowTwoOf_map_iff
      (f := (f112Gold D.L1 D.L2 D.S).ofA) (f112Gold D.L1 D.L2 D.S).ofA_injective
      ((pCoreOf 2 D.Ke).subgroupOf (f112P1 D.L1 D.L2 D.S))
      (D.Ke.subgroupOf (f112P1 D.L1 D.L2 D.S))).mp hmapped
  exact (CFSG.Quasithin.H13.U3.GC137.isSylowTwoOf_subgroupOf_iff
    (X := f112P1 D.L1 D.L2 D.S)
    (CFSG.LieType.BorelTits.pCoreOf_le 2 D.Ke) (D.le_Ke.trans inf_le_left)).mp hsylP

theorem BaseEdgeData.pCoreOf_Pβ_le_inf (D : BaseEdgeData H)
    (hc : CharTwoStab (V := Vtx (f112Gold D.L1 D.L2 D.S)) (G := ↥D.E)) :
    pCoreOf 2 D.Pβ ≤ f112P1 D.L1 D.L2 D.S ⊓ f112P2 D.L1 D.L2 D.S := by
  intro y hy
  have hyPβ : y ∈ D.Pβ := (CFSG.LieType.BorelTits.pCoreOf_le 2 D.Pβ) hy
  have hyP₂ : y ∈ f112P2 D.L1 D.L2 D.S := D.le_Pβ hyPβ
  have hQ1S : D.X.Q 1 ≤ D.X.S := by
    have h := D.X.sup_Q_eq_edgeSylow hc 0
    rw [Setup.edgeSylow_zero] at h
    rw [← h]
    exact le_sup_right
  have hmap : f112OfB D.L1 D.L2 D.S (pCoreOf 2 D.Pβ) ≤
      f112OfA D.L1 D.L2 D.S (pCoreOf 2 D.Ke) := by
    rw [← D.Q_one_map, ← D.S_map]
    exact Subgroup.map_mono hQ1S
  have hu : (f112Gold D.L1 D.L2 D.S).ofB ⟨y, hyP₂⟩ ∈
      f112OfA D.L1 D.L2 D.S (pCoreOf 2 D.Ke) :=
    hmap ⟨⟨y, D.le_Pβ hyPβ⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
  have huA : (f112Gold D.L1 D.L2 D.S).ofB ⟨y, hyP₂⟩ ∈
      (f112Gold D.L1 D.L2 D.S).ofA.range :=
    Subgroup.map_le_range _ _ hu
  have huBase : (f112Gold D.L1 D.L2 D.S).ofB ⟨y, hyP₂⟩ ∈
      (Monoid.PushoutI.base (f112Gold D.L1 D.L2 D.S).diagram).range := by
    rw [← (f112Gold D.L1 D.L2 D.S).ofA_range_inf_ofB_range]
    exact ⟨huA, ⟨⟨y, hyP₂⟩, rfl⟩⟩
  obtain ⟨c, hc_eq⟩ := huBase
  have htoB : (f112Gold D.L1 D.L2 D.S).toB c = ⟨y, hyP₂⟩ :=
    (f112Gold D.L1 D.L2 D.S).ofB_injective
      (by rw [(f112Gold D.L1 D.L2 D.S).ofB_toB, hc_eq])
  have hcy : (c : H) = y := by
    rw [← f112Gold_toB_val D.L1 D.L2 D.S c]
    exact congrArg (fun w : ↥(f112P2 D.L1 D.L2 D.S) => (w : H)) htoB
  rw [← hcy]
  exact c.2

theorem BaseEdgeData.sup_pCoreOf_eq_pCoreOf (D : BaseEdgeData H)
    (hc : CharTwoStab (V := Vtx (f112Gold D.L1 D.L2 D.S)) (G := ↥D.E)) :
    pCoreOf 2 D.Pα ⊔ pCoreOf 2 D.Pβ = pCoreOf 2 D.Ke := by
  have hPB : pCoreOf 2 D.Pβ ≤ f112P1 D.L1 D.L2 D.S ⊓ f112P2 D.L1 D.L2 D.S :=
    D.pCoreOf_Pβ_le_inf hc
  have hsupU : f112OfA D.L1 D.L2 D.S (pCoreOf 2 D.Pα) ⊔
      f112OfB D.L1 D.L2 D.S (pCoreOf 2 D.Pβ) =
      f112OfA D.L1 D.L2 D.S (pCoreOf 2 D.Ke) := by
    have h := congrArg (fun Y : Subgroup ↥D.E => Y.map D.E.subtype)
      (D.X.sup_Q_eq_edgeSylow hc 0)
    rw [Subgroup.map_sup, Setup.edgeSylow_zero] at h
    simp only [zero_add] at h
    rw [D.Q_zero_map, D.Q_one_map, D.S_map] at h
    exact h
  rw [← ofA_subgroupOf_eq_ofB_subgroupOf D.L1 D.L2 D.S hPB] at hsupU
  have hA : pCoreOf 2 D.Pα ≤ f112P1 D.L1 D.L2 D.S :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 D.Pα).trans D.le_Pα
  have hB : pCoreOf 2 D.Pβ ≤ f112P1 D.L1 D.L2 D.S := hPB.trans inf_le_left
  have hC : pCoreOf 2 D.Ke ≤ f112P1 D.L1 D.L2 D.S :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 D.Ke).trans (D.le_Ke.trans inf_le_left)
  have hAsupB : f112OfA D.L1 D.L2 D.S
      (pCoreOf 2 D.Pα ⊔ pCoreOf 2 D.Pβ) = f112OfA D.L1 D.L2 D.S (pCoreOf 2 D.Ke) := by
    rw [f112OfA_sup hA hB]
    exact hsupU
  have hsub : ((pCoreOf 2 D.Pα ⊔ pCoreOf 2 D.Pβ).subgroupOf (f112P1 D.L1 D.L2 D.S)) =
      ((pCoreOf 2 D.Ke).subgroupOf (f112P1 D.L1 D.L2 D.S)) :=
    Subgroup.map_injective (f := (f112Gold D.L1 D.L2 D.S).ofA)
      (f112Gold D.L1 D.L2 D.S).ofA_injective hAsupB
  have h2 : (pCoreOf 2 D.Pα ⊔ pCoreOf 2 D.Pβ) ⊓ (f112P1 D.L1 D.L2 D.S) =
      pCoreOf 2 D.Ke ⊓ f112P1 D.L1 D.L2 D.S := Subgroup.subgroupOf_inj.mp hsub
  calc pCoreOf 2 D.Pα ⊔ pCoreOf 2 D.Pβ
      = (pCoreOf 2 D.Pα ⊔ pCoreOf 2 D.Pβ) ⊓ (f112P1 D.L1 D.L2 D.S) :=
        (inf_of_le_left (sup_le hA hB)).symm
    _ = pCoreOf 2 D.Ke ⊓ f112P1 D.L1 D.L2 D.S := h2
    _ = pCoreOf 2 D.Ke := inf_of_le_left hC

theorem BaseEdgeData.isL2Quot_oTwoPrime_ofA (D : BaseEdgeData H) :
    IsL2Quot (nOf (f112Gold D.L1 D.L2 D.S).treeGraph (baseA (f112Gold D.L1 D.L2 D.S)))
      (oTwoQuot ↥(oTwoPrime D.Pα)) := by
  have hquot : IsL2Quot (nOf (f112Gold D.L1 D.L2 D.S).treeGraph (D.X.vert 0))
      (oTwoQuot ↥(D.X.L 0)) := (D.X.hyp.isLocL2_oTwoPrime (D.X.vert 0)).quot
  rw [D.X_zero] at hquot
  exact (isL2Quot_of_map_iff D.L1 D.L2 D.S ((oTwoPrime_le D.Pα).trans D.le_Pα) (D.L_zero_map)
    (nOf (f112Gold D.L1 D.L2 D.S).treeGraph (baseA (f112Gold D.L1 D.L2 D.S)))).mp hquot

theorem BaseEdgeData.isL2Quot_oTwoPrime_ofB (D : BaseEdgeData H) :
    IsL2Quot (nOf (f112Gold D.L1 D.L2 D.S).treeGraph (baseB (f112Gold D.L1 D.L2 D.S)))
      (oTwoQuot ↥(oTwoPrime D.Pβ)) := by
  have hquot : IsL2Quot (nOf (f112Gold D.L1 D.L2 D.S).treeGraph (D.X.vert 1))
      (oTwoQuot ↥(D.X.L 1)) := (D.X.hyp.isLocL2_oTwoPrime (D.X.vert 1)).quot
  rw [D.X_one] at hquot
  exact (isL2Quot_of_map_iff_ofB D.L1 D.L2 D.S ((oTwoPrime_le D.Pβ).trans D.le_Pβ)
    (D.L_one_map)
    (nOf (f112Gold D.L1 D.L2 D.S).treeGraph (baseB (f112Gold D.L1 D.L2 D.S)))).mp hquot

theorem f112_exists_setup_baseEdge {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2) :
    ∃ X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112E5 L1 L2 S),
      X.vert 0 = baseA (f112Gold L1 L2 S) ∧ X.vert 1 = baseB (f112Gold L1 L2 S) :=
  (f112_hyp30 hF h1 h2).exists_setup' (adj_baseA_baseB (f112Gold L1 L2 S))

noncomputable abbrev f112BaseEdgeData {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2)
    (X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112E5 L1 L2 S))
    (hX0 : X.vert 0 = baseA (f112Gold L1 L2 S))
    (hX1 : X.vert 1 = baseB (f112Gold L1 L2 S)) :
    BaseEdgeData H :=
  { L1 := L1, L2 := L2, S := S, E := f112E5 L1 L2 S
    Pα := f112saP1' L1 L2 S, Pβ := f112saP2' L1 L2 S, Ke := f112saK L1 L2 S
    le_Pα := f112sa_P1'_le_P1 hF
    le_Pβ := f112sa_P2'_le_P2 hF
    le_Ke := by rw [f112_inf_eq_bigB hF]; exact f112sa_K_le_bigB L1 L2 S
    ofA_eq := f112E5_inf_ofA_range hF h1 h2
    ofB_eq := f112E5_inf_ofB_range hF h1 h2
    ofA_inf_ofB_eq := f112E5_inf_ofA_range_inf_ofB_range hF h1 h2
    X := X, X_zero := hX0, X_one := hX1 }

theorem f112_pCoreOf_K_eq {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2) :
    pCoreOf 2 (f112saK L1 L2 S) = S ⊓ f112saK L1 L2 S := by
  classical
  obtain ⟨X, hX0, hX1⟩ := f112_exists_setup_baseEdge hF h1 h2
  let D := f112BaseEdgeData hF h1 h2 X hX0 hX1
  exact eq_pCoreOf_of_isSylowTwoOf (f112sa_T_sylow_K hF) (D.isSylowTwoOf_pCoreOf)

theorem f112_pCoreOf_sup_eq {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2) :
    pCoreOf 2 (f112saP1' L1 L2 S) ⊔ pCoreOf 2 (f112saP2' L1 L2 S) =
      S ⊓ f112saK L1 L2 S := by
  classical
  obtain ⟨X, hX0, hX1⟩ := f112_exists_setup_baseEdge hF h1 h2
  let D := f112BaseEdgeData hF h1 h2 X hX0 hX1
  rw [← f112_pCoreOf_K_eq hF h1 h2]
  exact D.sup_pCoreOf_eq_pCoreOf (f112_charTwoStab hF h1 h2)

theorem f112_isL2Quot_oTwoPrime_P1' {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2) :
    IsL2Quot 2 (oTwoQuot ↥(oTwoPrime (f112saP1' L1 L2 S))) := by
  classical
  obtain ⟨X, hX0, hX1⟩ := f112_exists_setup_baseEdge hF h1 h2
  let D := f112BaseEdgeData hF h1 h2 X hX0 hX1
  have h := D.isL2Quot_oTwoPrime_ofA
  rwa [f112_nOf_eq_two hF h1 h2 (baseA (f112Gold L1 L2 S))] at h

theorem f112_isL2Quot_oTwoPrime_P2' {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2) :
    IsL2Quot 2 (oTwoQuot ↥(oTwoPrime (f112saP2' L1 L2 S))) := by
  classical
  obtain ⟨X, hX0, hX1⟩ := f112_exists_setup_baseEdge hF h1 h2
  let D := f112BaseEdgeData hF h1 h2 X hX0 hX1
  have h := D.isL2Quot_oTwoPrime_ofB
  rwa [f112_nOf_eq_two hF h1 h2 (baseB (f112Gold L1 L2 S))] at h

theorem f112sa_exists_setup_baseEdge {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2) :
    ∃ X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S),
      X.vert 0 = baseA (f112Gold L1 L2 S) ∧ X.vert 1 = baseB (f112Gold L1 L2 S) :=
  (f112sl_hyp30 (n := 2) hF h1 le_rfl h2).exists_setup' (adj_baseA_baseB (f112Gold L1 L2 S))

theorem f112sa_pCoreOf_K_eq {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2) :
    pCoreOf 2 (f112saK L1 L2 S) = S ⊓ f112saK L1 L2 S := by
  classical
  obtain ⟨X, hX0, hX1⟩ := f112sa_exists_setup_baseEdge hF h1 h2
  let D : BaseEdgeData H :=
    { L1 := L1, L2 := L2, S := S, E := f112EOdd L1 L2 S
      Pα := f112saP1' L1 L2 S, Pβ := f112saP2' L1 L2 S, Ke := f112saK L1 L2 S
      le_Pα := f112sa_P1'_le_P1 hF.toW
      le_Pβ := f112sa_P2'_le_P2 hF.toW
      le_Ke := by rw [f112_inf_eq_bigB hF.toW]; exact f112sa_K_le_bigB L1 L2 S
      ofA_eq := f112sa_EOdd_inf_ofA_range hF h1 h2
      ofB_eq := f112sa_EOdd_inf_ofB_range hF h1 h2
      ofA_inf_ofB_eq := f112sa_EOdd_inf_ofA_range_inf_ofB_range hF h1 h2
      X := X, X_zero := hX0, X_one := hX1 }
  exact eq_pCoreOf_of_isSylowTwoOf (f112sa_T_sylow_K hF.toW) (D.isSylowTwoOf_pCoreOf)

theorem f112sa_pCoreOf_sup_eq {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2) :
    pCoreOf 2 (f112saP1' L1 L2 S) ⊔ pCoreOf 2 (f112saP2' L1 L2 S) =
      S ⊓ f112saK L1 L2 S := by
  classical
  obtain ⟨X, hX0, hX1⟩ := f112sa_exists_setup_baseEdge hF h1 h2
  let D : BaseEdgeData H :=
    { L1 := L1, L2 := L2, S := S, E := f112EOdd L1 L2 S
      Pα := f112saP1' L1 L2 S, Pβ := f112saP2' L1 L2 S, Ke := f112saK L1 L2 S
      le_Pα := f112sa_P1'_le_P1 hF.toW
      le_Pβ := f112sa_P2'_le_P2 hF.toW
      le_Ke := by rw [f112_inf_eq_bigB hF.toW]; exact f112sa_K_le_bigB L1 L2 S
      ofA_eq := f112sa_EOdd_inf_ofA_range hF h1 h2
      ofB_eq := f112sa_EOdd_inf_ofB_range hF h1 h2
      ofA_inf_ofB_eq := f112sa_EOdd_inf_ofA_range_inf_ofB_range hF h1 h2
      X := X, X_zero := hX0, X_one := hX1 }
  rw [← f112sa_pCoreOf_K_eq hF h1 h2]
  exact D.sup_pCoreOf_eq_pCoreOf (f112sa_charTwoStab hF h1 le_rfl h2)

theorem f112sa_isL2Quot_oTwoPrime_P1' {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2) :
    IsL2Quot 1 (oTwoQuot ↥(oTwoPrime (f112saP1' L1 L2 S))) := by
  classical
  obtain ⟨X, hX0, hX1⟩ := f112sa_exists_setup_baseEdge hF h1 h2
  let D : BaseEdgeData H :=
    { L1 := L1, L2 := L2, S := S, E := f112EOdd L1 L2 S
      Pα := f112saP1' L1 L2 S, Pβ := f112saP2' L1 L2 S, Ke := f112saK L1 L2 S
      le_Pα := f112sa_P1'_le_P1 hF.toW
      le_Pβ := f112sa_P2'_le_P2 hF.toW
      le_Ke := by rw [f112_inf_eq_bigB hF.toW]; exact f112sa_K_le_bigB L1 L2 S
      ofA_eq := f112sa_EOdd_inf_ofA_range hF h1 h2
      ofB_eq := f112sa_EOdd_inf_ofB_range hF h1 h2
      ofA_inf_ofB_eq := f112sa_EOdd_inf_ofA_range_inf_ofB_range hF h1 h2
      X := X, X_zero := hX0, X_one := hX1 }
  have h := D.isL2Quot_oTwoPrime_ofA
  have hn : nOf (f112Gold L1 L2 S).treeGraph (baseA (f112Gold L1 L2 S)) = 1 := by
    simpa using f112sa_nOf_alpha hF h1 le_rfl h2 (1 : (f112Gold L1 L2 S).Universal)
  rwa [hn] at h

theorem f112sa_isL2Quot_oTwoPrime_P2' {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2) :
    IsL2Quot 2 (oTwoQuot ↥(oTwoPrime (f112saP2' L1 L2 S))) := by
  classical
  obtain ⟨X, hX0, hX1⟩ := f112sa_exists_setup_baseEdge hF h1 h2
  let D : BaseEdgeData H :=
    { L1 := L1, L2 := L2, S := S, E := f112EOdd L1 L2 S
      Pα := f112saP1' L1 L2 S, Pβ := f112saP2' L1 L2 S, Ke := f112saK L1 L2 S
      le_Pα := f112sa_P1'_le_P1 hF.toW
      le_Pβ := f112sa_P2'_le_P2 hF.toW
      le_Ke := by rw [f112_inf_eq_bigB hF.toW]; exact f112sa_K_le_bigB L1 L2 S
      ofA_eq := f112sa_EOdd_inf_ofA_range hF h1 h2
      ofB_eq := f112sa_EOdd_inf_ofB_range hF h1 h2
      ofA_inf_ofB_eq := f112sa_EOdd_inf_ofA_range_inf_ofB_range hF h1 h2
      X := X, X_zero := hX0, X_one := hX1 }
  have h := D.isL2Quot_oTwoPrime_ofB
  have hn : nOf (f112Gold L1 L2 S).treeGraph (baseB (f112Gold L1 L2 S)) = 2 := by
    simpa using f112sa_nOf_beta hF h1 le_rfl h2 (1 : (f112Gold L1 L2 S).Universal)
  rwa [hn] at h

end CFSG.Quasithin.F112R.St84
