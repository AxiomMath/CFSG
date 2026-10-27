module

public import CFSG.Quasithin.Recognition.St84.G24Vertex2Complement
public import CFSG.GH74.QTGen4.DSGen4.Leaf.A5Classify
import CFSG.GH74.QTGen4.DSGen4.Leaf.Lin2OfNaturalB
import CFSG.GroupTheory.AlternatingFive.SmallImage
import CFSG.Quasithin.Background.SpecialPGroupCenter
public import CFSG.GH74.QTGen4.DSGen4.Leaf.A5ClassifySylow
public import CFSG.Quasithin.Recognition.St84.G24Vertex2Frame

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
  CFSG.GH74.QTGen4.DSGen4 CFSG.Quasithin.F7
open Certificates.A5GL42 (aN bN)
open scoped commutatorElement Matrix

variable {G : Type} [Group G]
variable {L1 L2 S : Subgroup G}

private theorem commutator_conj_left (g x l : G) :
    ⁅g * x * g⁻¹, l⁆ = g * ⁅x, g⁻¹ * l * g⁆ * g⁻¹ := by
  simp only [commutatorElement_def]
  group

private def frameW (L1 L2 S : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ dsQ L2 L1 S ∧ ∀ l ∈ L2, ⁅x, l⁆ ∈ centerOf (dsQ L2 L1 S)}
  one_mem' := by
    refine ⟨(dsQ L2 L1 S).one_mem, fun l hl => ?_⟩
    simp
  mul_mem' := by
    rintro x y ⟨hxQ, hx⟩ ⟨hyQ, hy⟩
    refine ⟨(dsQ L2 L1 S).mul_mem hxQ hyQ, fun l hl => ?_⟩
    have hxl := hx l hl
    have hyl := hy l hl
    have hconj : x * ⁅y, l⁆ * x⁻¹ = ⁅y, l⁆ := G24Vertex2.conj_eq_of_mem_centerOf hyl hxQ
    rw [commutatorElement_mul_left_eq_conj_mul, hconj]
    exact (centerOf (dsQ L2 L1 S)).mul_mem hyl hxl
  inv_mem' := by
    rintro x ⟨hxQ, hx⟩
    refine ⟨(dsQ L2 L1 S).inv_mem hxQ, fun l hl => ?_⟩
    have hxl := hx l hl
    have hinv : ⁅l, x⁆ = ⁅x, l⁆⁻¹ := (commutatorElement_inv (g₁ := x) (g₂ := l)).symm
    have hconj : x⁻¹ * ⁅x, l⁆⁻¹ * x = ⁅x, l⁆⁻¹ := by
      simpa using G24Vertex2.conj_eq_of_mem_centerOf ((centerOf (dsQ L2 L1 S)).inv_mem hxl)
        ((dsQ L2 L1 S).inv_mem hxQ)
    rw [commutatorElement_inv_left, hinv, hconj]
    exact (centerOf (dsQ L2 L1 S)).inv_mem hxl

private theorem mem_frameW {L1 L2 S : Subgroup G} {x : G} :
    x ∈ frameW L1 L2 S ↔ x ∈ dsQ L2 L1 S ∧
      ∀ l ∈ L2, ⁅x, l⁆ ∈ centerOf (dsQ L2 L1 S) := Iff.rfl

private theorem P2_le_normalizer_frameW [Finite G]
    {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) :
    L2 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer (frameW L1 L2 S : Set G) := by
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hL2N : L2 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer (L2 : Set G) :=
    G24LocalData.normal_L_right hR
  have hP2N := P_le_normalizer_dsQ_right L1 L2 S
  have hZ2N := P_le_normalizer_centerOf_dsQ_right L1 L2 S
  have key : ∀ h ∈ L2 ⊔ bigB L1 L2 S, ∀ x, x ∈ frameW L1 L2 S →
      h * x * h⁻¹ ∈ frameW L1 L2 S := by
    intro h hh x hx
    obtain ⟨hxQ, hxcomm⟩ := mem_frameW.mp hx
    have hxQ' : h * x * h⁻¹ ∈ dsQ L2 L1 S :=
      (Subgroup.mem_normalizer_iff.mp (hP2N hh) x).mp hxQ
    refine mem_frameW.mpr ⟨hxQ', fun l hl => ?_⟩
    have hl' : h⁻¹ * l * h ∈ L2 := by
      simpa using (Subgroup.mem_normalizer_iff.mp
        (hL2N ((L2 ⊔ bigB L1 L2 S).inv_mem hh)) l).mp hl
    have hz := hxcomm (h⁻¹ * l * h) hl'
    rw [commutator_conj_left h x l]
    exact (Subgroup.mem_normalizer_iff.mp (hZ2N hh) _).mp hz
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key g hg x
  · intro hx
    have h1 := key g⁻¹ ((L2 ⊔ bigB L1 L2 S).inv_mem hg) (g * x * g⁻¹) hx
    simpa [mul_assoc] using h1

private theorem not_comm_le_of_card [Finite G] {Q W L : Subgroup G}
    (hcomm : ⁅Q, L⁆ = Q) (hle : ⁅Q, L⁆ ≤ W)
    (hQ : Nat.card Q = 2 ^ 10) (hW : Nat.card W < 2 ^ 10) : False := by
  haveI : Finite ↥W := Subtype.finite
  have hle' : Q ≤ W := hcomm ▸ hle
  have hcards : Nat.card Q ≤ Nat.card W := Subgroup.card_le_of_le hle'
  rw [hQ] at hcards
  omega

private theorem A5Pre_and_model_of_mid [Finite G]
    {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S)
    (h2 : VA5 L2) (hD : G24LocalData L1 L2 S) {W0 : Subgroup G}
    (hZ2W0 : centerOf (dsQ L2 L1 S) ≤ W0) (hW0Q2 : W0 ≤ dsQ L2 L1 S)
    (hW0card : Nat.card W0 = 2 ^ 6)
    (hW0comm : ⁅W0, L2⁆ ≤ centerOf (dsQ L2 L1 S))
    (hW0nat : NatSec L2 W0 (dsQ L2 L1 S)) :
    A5Pre L2 L2 (dsQ L2 L1 S) W0 ∧
      Nonempty (A5Model L2 L2 (dsQ L2 L1 S) W0 Certificates.A5GL42.HN) := by
  classical
  let P2 : Subgroup G := L2 ⊔ bigB L1 L2 S
  let Q2 : Subgroup G := dsQ L2 L1 S
  let Z2 : Subgroup G := centerOf Q2
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hP2N : P2 ≤ Subgroup.normalizer (Q2 : Set G) := P_le_normalizer_dsQ_right L1 L2 S
  have hQ2eq : pCoreOf 2 L2 = Q2 := G24LocalData.pCoreOf_eq_dsQ_right hR hD.le_right
  have hQ2card : Nat.card Q2 = 2 ^ 10 := hD.card_right
  have hcommZ : ⁅Q2, Q2⁆ ≤ Z2 :=
    CFSG.Quasithin.IsSpecialPGroup.commutator_le_centerOf hD.special_right
  have hsqZ : ∀ x ∈ Q2, x ^ 2 ∈ Z2 :=
    fun x hx => CFSG.Quasithin.IsSpecialPGroup.pow_mem_centerOf hD.special_right hx
  have hW0N : L2 ≤ Subgroup.normalizer (W0 : Set G) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_left]
    exact hW0comm.trans hZ2W0
  have hpre0 : A5Pre L2 L2 Q2 W0 := by
    refine ⟨le_rfl, Subgroup.le_normalizer, (le_sup_left : L2 ≤ P2).trans hP2N, hW0N,
      ?_, ?_, ?_, h2, ?_⟩
    · exact ⟨hW0Q2, hcommZ.trans hZ2W0, fun e he => hZ2W0 (hsqZ e he)⟩
    · have h := Subgroup.relIndex_mul_card (H := W0) (K := Q2)
      rw [inf_eq_left.mpr hW0Q2, hW0card, hQ2card] at h
      omega
    · intro q hq e he
      have hq' : q ∈ Q2 := by simpa [← hQ2eq] using hq
      exact hZ2W0 (hcommZ (Subgroup.commutator_mem_commutator hq' he))
    · by_contra hcon
      push Not at hcon
      have hle : ⁅Q2, L2⁆ ≤ W0 := by
        rw [Subgroup.commutator_comm]
        exact Subgroup.commutator_le.mpr fun x hx y hy => hcon x hx y hy
      exact not_comm_le_of_card hD.comm_right hle hQ2card (by rw [hW0card]; norm_num)
  rcases A5Pre.exists_model' hpre0 with ⟨-, ⟨M⟩⟩ | ⟨hnot, -⟩
  · exact ⟨hpre0, ⟨M⟩⟩
  · exact absurd hW0nat hnot

private theorem exists_frameW_model_of_eq [Finite G]
    {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S)
    (h2 : VA5 L2) (hD : G24LocalData L1 L2 S) {W0 : Subgroup G}
    (hZ2W0 : centerOf (dsQ L2 L1 S) ≤ W0)
    (hW0card : Nat.card W0 = 2 ^ 6)
    (hW0nat : NatSec L2 W0 (dsQ L2 L1 S))
    (heq : frameW L1 L2 S = W0) :
    ∃ W : Subgroup G,
      (∀ x, x ∈ W ↔ x ∈ dsQ L2 L1 S ∧
        ∀ l ∈ L2, ⁅x, l⁆ ∈ centerOf (dsQ L2 L1 S)) ∧
      Nat.card W = 2 ^ 6 ∧
      Nonempty (A5Model (L2 ⊔ bigB L1 L2 S) L2 (dsQ L2 L1 S) W
        Certificates.A5GL42.HN) := by
  classical
  let P2 : Subgroup G := L2 ⊔ bigB L1 L2 S
  let Q2 : Subgroup G := dsQ L2 L1 S
  let Z2 : Subgroup G := centerOf Q2
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hQ2P2 : Q2 ≤ P2 := dsQ_le_P_right L1 L2 S
  have hP2N : P2 ≤ Subgroup.normalizer (Q2 : Set G) := P_le_normalizer_dsQ_right L1 L2 S
  have hL2N : P2 ≤ Subgroup.normalizer (L2 : Set G) := G24LocalData.normal_L_right hR
  have hQ2card : Nat.card Q2 = 2 ^ 10 := hD.card_right
  have hcommZ : ⁅Q2, Q2⁆ ≤ Z2 :=
    CFSG.Quasithin.IsSpecialPGroup.commutator_le_centerOf hD.special_right
  have hsqZ : ∀ x ∈ Q2, x ^ 2 ∈ Z2 :=
    fun x hx => CFSG.Quasithin.IsSpecialPGroup.pow_mem_centerOf hD.special_right hx
  have hWcard : Nat.card (frameW L1 L2 S) = 2 ^ 6 := by rw [heq]; exact hW0card
  have hZ2W : Z2 ≤ frameW L1 L2 S := by rw [heq]; exact hZ2W0
  have hWQ2 : frameW L1 L2 S ≤ Q2 := fun x hx => (mem_frameW.mp hx).1
  have hP2NW : P2 ≤ Subgroup.normalizer (frameW L1 L2 S : Set G) :=
    P2_le_normalizer_frameW hF
  have hpre : A5Pre P2 L2 Q2 (frameW L1 L2 S) := by
    refine ⟨le_sup_left, hL2N, hP2N, hP2NW, ?_, ?_, ?_, h2, ?_⟩
    · exact ⟨hWQ2, hcommZ.trans hZ2W, fun e he => hZ2W (hsqZ e he)⟩
    · have h := Subgroup.relIndex_mul_card (H := frameW L1 L2 S) (K := Q2)
      rw [inf_eq_left.mpr hWQ2, hWcard, hQ2card] at h
      omega
    · intro q hq e he
      have hq' : q ∈ Q2 := by
        change q ∈ dsQ L2 L1 S
        rw [dsQ_eq_pCoreOf_right]
        exact hq
      exact hZ2W (hcommZ (Subgroup.commutator_mem_commutator hq' he))
    · by_contra hcon
      push Not at hcon
      have hle : ⁅Q2, L2⁆ ≤ frameW L1 L2 S := by
        rw [Subgroup.commutator_comm]
        exact Subgroup.commutator_le.mpr fun x hx y hy => hcon x hx y hy
      exact not_comm_le_of_card hD.comm_right hle hQ2card (by rw [hWcard]; norm_num)
  obtain ⟨MN⟩ : Nonempty (A5Model P2 L2 Q2 (frameW L1 L2 S) Certificates.A5GL42.HN) := by
    rcases A5Pre.exists_model' hpre with ⟨-, ⟨M⟩⟩ | ⟨hnot, -⟩
    · exact ⟨M⟩
    · exact absurd (heq ▸ hW0nat) hnot
  exact ⟨frameW L1 L2 S, fun x => mem_frameW, hWcard, ⟨MN⟩⟩

private theorem exists_frameW_model [Finite G]
    {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S)
    (h2 : VA5 L2) (hD : G24LocalData L1 L2 S) :
    ∃ W : Subgroup G,
      (∀ x, x ∈ W ↔ x ∈ dsQ L2 L1 S ∧
        ∀ l ∈ L2, ⁅x, l⁆ ∈ centerOf (dsQ L2 L1 S)) ∧
      Nat.card W = 2 ^ 6 ∧
      Nonempty (A5Model (L2 ⊔ bigB L1 L2 S) L2 (dsQ L2 L1 S) W
        Certificates.A5GL42.HN) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P2 : Subgroup G := L2 ⊔ bigB L1 L2 S
  let Q2 : Subgroup G := dsQ L2 L1 S
  let Z2 : Subgroup G := centerOf Q2
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hQ2P2 : Q2 ≤ P2 := by
    dsimp only [Q2, P2]
    rw [dsQ_eq_pCoreOf_right]
    exact CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hP2N : P2 ≤ Subgroup.normalizer (Q2 : Set G) := by
    dsimp only [Q2, P2]
    rw [dsQ_eq_pCoreOf_right]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hL2N : P2 ≤ Subgroup.normalizer (L2 : Set G) := G24LocalData.normal_L_right hR
  have hQ2eq : pCoreOf 2 L2 = Q2 := G24LocalData.pCoreOf_eq_dsQ_right hR hD.le_right
  have hQ2card : Nat.card Q2 = 2 ^ 10 := hD.card_right
  obtain ⟨W0, hZ2W0, hW0Q2, hW0card, hW0comm, hW0nat⟩ := hD.mid_right
  obtain ⟨hpre0, ⟨M0⟩⟩ :=
    A5Pre_and_model_of_mid hF h2 hD hZ2W0 hW0Q2 hW0card hW0comm hW0nat
  let W : Subgroup G := frameW L1 L2 S
  have hmemW : ∀ x, x ∈ W ↔ x ∈ Q2 ∧ ∀ l ∈ L2, ⁅x, l⁆ ∈ Z2 :=
    fun x => mem_frameW
  have hW0W : W0 ≤ W := by
    intro w hw
    exact mem_frameW.mpr ⟨hW0Q2 hw, fun l hl =>
      hW0comm (Subgroup.commutator_mem_commutator hw hl)⟩
  have hWQ2 : W ≤ Q2 := fun x hx => (mem_frameW.mp hx).1
  have hL2NW : L2 ≤ Subgroup.normalizer (W : Set G) :=
    (le_sup_left : L2 ≤ P2).trans (P2_le_normalizer_frameW hF)
  have heq := A5Model.eq_or_eq_of_normalizes a5Facts a5Facts.groupN hpre0 M0
    hW0W hWQ2 hL2NW
  rcases heq with hWW0 | hWQ2eq
  · exact exists_frameW_model_of_eq hF h2 hD hZ2W0 hW0card hW0nat
      (by simpa [W] using hWW0)
  · exfalso
    have hle : ⁅Q2, L2⁆ ≤ Z2 := by
      refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
      have hxW : x ∈ W := by rw [hWQ2eq]; exact hx
      exact (mem_frameW.mp hxW).2 y hy
    exact not_comm_le_of_card hD.comm_right hle hQ2card
      (by rw [hD.card_centerOf_dsQ_right]; norm_num)

private theorem gl_one_of_model [Finite G] {L1 L2 S : Subgroup G} {A W : Subgroup G}
    {MN : A5Model (L2 ⊔ bigB L1 L2 S) L2 (dsQ L2 L1 S) W
      Certificates.A5GL42.HN}
    (hQ2eq : pCoreOf 2 L2 = dsQ L2 L1 S)
    (hAinf : A ⊓ dsQ L2 L1 S = ⊥) :
    ∀ (p : ↥(L2 ⊔ bigB L1 L2 S)), (p : G) ∈ A → (p : G) ∈ L2 →
      MN.F.M p = 1 → (p : G) = 1 := by
  intro p hpA hpL hM
  have hq : (p : G) ∈ pCoreOf 2 L2 := (MN.kerL p hpL).mp hM
  have hQ : (p : G) ∈ dsQ L2 L1 S := by rwa [hQ2eq] at hq
  have hbot : (p : G) ∈ A ⊓ dsQ L2 L1 S := ⟨hpA, hQ⟩
  rw [hAinf, Subgroup.mem_bot] at hbot
  exact hbot

private theorem exists_lift_mem_A_inf_L2 [Finite G] {L1 L2 S : Subgroup G}
    {A W : Subgroup G}
    {MN : A5Model (L2 ⊔ bigB L1 L2 S) L2 (dsQ L2 L1 S) W
      Certificates.A5GL42.HN}
    (hAP2 : A ≤ L2 ⊔ bigB L1 L2 S) (hQ2L2 : dsQ L2 L1 S ≤ L2)
    (hAinf : A ⊓ dsQ L2 L1 S = ⊥)
    (hdecomp : ∀ x ∈ L2 ⊔ bigB L1 L2 S, ∃ q ∈ dsQ L2 L1 S, ∃ c ∈ A, x = q * c)
    (gL : ↥(L2 ⊔ bigB L1 L2 S)) (hgL : (gL : G) ∈ L2)
    (Mgen : Matrix (Fin 4) (Fin 4) (ZMod 2))
    (hgM : glMat (MN.F.M gL) = Mgen) (hMgen1 : Mgen ≠ 1) :
    ∃ p : ↥(L2 ⊔ bigB L1 L2 S), (p : G) ∈ A ∧ (p : G) ∈ L2 ∧
      glMat (MN.F.M p) = Mgen ∧ (p : G) ∉ dsQ L2 L1 S := by
  let P2 : Subgroup G := L2 ⊔ bigB L1 L2 S
  let Q2 : Subgroup G := dsQ L2 L1 S
  have hQ2P2 : Q2 ≤ P2 := dsQ_le_P_right L1 L2 S
  obtain ⟨q, hq, c, hc, hgc⟩ := hdecomp (gL : G) gL.2
  let p : ↥P2 := ⟨c, hAP2 hc⟩
  have hgcP : gL = (⟨q, hQ2P2 hq⟩ : ↥P2) * p := Subtype.ext hgc
  have hqP : (q : G) ∈ pCoreOf 2 P2 := by
    rw [← dsQ_eq_pCoreOf_right]
    exact hq
  have hqM : MN.F.M (⟨q, hQ2P2 hq⟩ : ↥P2) = 1 := MN.core _ hqP
  have hpM : MN.F.M p = MN.F.M gL := by
    have h := congrArg MN.F.M hgcP
    rw [map_mul, hqM, one_mul] at h
    exact h.symm
  have hpL : (p : G) ∈ L2 := by
    change c ∈ L2
    have hc' : c = (q : G)⁻¹ * (gL : G) := by rw [hgc]; group
    rw [hc']
    exact L2.mul_mem (L2.inv_mem (hQ2L2 hq)) hgL
  have hpA : (p : G) ∈ A := hc
  have hpN : glMat (MN.F.M p) = Mgen := by rw [hpM, hgM]
  have hpQ : (p : G) ∉ Q2 := by
    intro h
    have hbot : (p : G) ∈ A ⊓ Q2 := ⟨hpA, h⟩
    rw [hAinf, Subgroup.mem_bot] at hbot
    have hp1 : p = 1 := Subtype.ext hbot
    rw [hp1, map_one] at hpN
    exact hMgen1 hpN.symm
  exact ⟨p, hpA, hpL, hpN, hpQ⟩

private theorem exists_generators_relations [Finite G] {L1 L2 S : Subgroup G}
    {A W : Subgroup G}
    {MN : A5Model (L2 ⊔ bigB L1 L2 S) L2 (dsQ L2 L1 S) W
      Certificates.A5GL42.HN}
    (hgl_one : ∀ (p : ↥(L2 ⊔ bigB L1 L2 S)), (p : G) ∈ A → (p : G) ∈ L2 →
      MN.F.M p = 1 → (p : G) = 1)
    {aP bP : ↥(L2 ⊔ bigB L1 L2 S)}
    (haA : (aP : G) ∈ A) (haL : (aP : G) ∈ L2) (haN : glMat (MN.F.M aP) = aN)
    (hbA : (bP : G) ∈ A) (hbL : (bP : G) ∈ L2) (hbN : glMat (MN.F.M bP) = bN)
    (ha1 : (aP : G) ≠ 1) (hb1 : (bP : G) ≠ 1) :
    (aP : G) ^ 2 = 1 ∧ (bP : G) ^ 3 = 1 ∧
      ((aP : G) * (bP : G)) ^ 5 = 1 ∧ (aP : G) * (bP : G) ≠ 1 := by
  have hMa2 : MN.F.M aP ^ 2 = 1 := by
    apply Units.ext
    change glMat (MN.F.M aP) ^ 2 = 1
    rw [haN]; exact (by decide : aN ^ 2 = 1)
  have hMb3 : MN.F.M bP ^ 3 = 1 := by
    apply Units.ext
    change glMat (MN.F.M bP) ^ 3 = 1
    rw [hbN]; exact (by decide : bN ^ 3 = 1)
  have hMab5 : (MN.F.M aP * MN.F.M bP) ^ 5 = 1 := by
    apply Units.ext
    change (glMat (MN.F.M aP) * glMat (MN.F.M bP)) ^ 5 = 1
    rw [haN, hbN]; exact (by decide : (aN * bN) ^ 5 = 1)
  have ha2 : (aP : G) ^ 2 = 1 := by
    have hM : MN.F.M (aP ^ 2) = 1 := by rw [map_pow, hMa2]
    simpa using hgl_one (aP ^ 2) (A.pow_mem haA 2) (L2.pow_mem haL 2) hM
  have hb3 : (bP : G) ^ 3 = 1 := by
    have hM : MN.F.M (bP ^ 3) = 1 := by rw [map_pow, hMb3]
    simpa using hgl_one (bP ^ 3) (A.pow_mem hbA 3) (L2.pow_mem hbL 3) hM
  have hab5 : ((aP : G) * (bP : G)) ^ 5 = 1 := by
    have hMab : MN.F.M (aP * bP) = MN.F.M aP * MN.F.M bP := map_mul _ _ _
    have hM : MN.F.M ((aP * bP) ^ 5) = 1 := by
      rw [map_pow]
      rw [hMab, hMab5]
    simpa using hgl_one ((aP * bP) ^ 5) (A.pow_mem (A.mul_mem haA hbA) 5)
      (L2.pow_mem (L2.mul_mem haL hbL) 5) hM
  have hab1 : (aP : G) * (bP : G) ≠ 1 := by
    intro h
    have hbeq' : (bP : G) = (aP : G) := by
      calc (bP : G) = (aP : G)⁻¹ := eq_inv_of_mul_eq_one_right h
        _ = (aP : G) := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using ha2)
    have horda : orderOf (aP : G) = 2 := orderOf_eq_prime ha2 ha1
    have hordb : orderOf (bP : G) = 3 := orderOf_eq_prime hb3 hb1
    rw [hbeq', horda] at hordb
    norm_num at hordb
  exact ⟨ha2, hb3, hab5, hab1⟩

private theorem closure_ab_k_eq_A [Finite G] {A : Subgroup G} {a b k : G}
    (hAcard : Nat.card A = 180) (hHcard : Nat.card ↥(A ⊓ L2) = 60)
    (haA : a ∈ A) (hbA : b ∈ A) (hkA : k ∈ A)
    (hclosure_ab : Subgroup.closure ({a, b} : Set G) = A ⊓ L2) (hkL : k ∉ L2) :
    Subgroup.closure ({a, b, k} : Set G) = A := by
  have hle : Subgroup.closure ({a, b, k} : Set G) ≤ A := by
    refine (Subgroup.closure_le (K := A)).mpr ?_
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact haA
    · exact hbA
    · exact hkA
  have hsub : Subgroup.closure ({a, b} : Set G) ≤
      Subgroup.closure ({a, b, k} : Set G) := by
    refine (Subgroup.closure_le (K := Subgroup.closure ({a, b, k} : Set G))).mpr ?_
    intro x hx
    rcases hx with rfl | rfl
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hknot : k ∉ Subgroup.closure ({a, b} : Set G) := by
    rw [hclosure_ab]
    exact fun h => hkL h.2
  have hstrict : Subgroup.closure ({a, b} : Set G) <
      Subgroup.closure ({a, b, k} : Set G) := by
    refine lt_of_le_of_ne hsub ?_
    intro heq
    apply hknot
    rw [heq]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
      (Set.mem_singleton _)))
  have h60 : Nat.card ↥(Subgroup.closure ({a, b} : Set G)) = 60 := by
    rw [hclosure_ab, hHcard]
  have hdiv : Nat.card ↥(Subgroup.closure ({a, b} : Set G)) ∣
      Nat.card ↥(Subgroup.closure ({a, b, k} : Set G)) :=
    Subgroup.card_dvd_of_le hsub
  have hlt : Nat.card ↥(Subgroup.closure ({a, b} : Set G)) <
      Nat.card ↥(Subgroup.closure ({a, b, k} : Set G)) :=
    Subgroup.card_lt_of_lt hstrict
  have hdvdA : Nat.card ↥(Subgroup.closure ({a, b, k} : Set G)) ∣
      Nat.card A := Subgroup.card_dvd_of_le hle
  rw [h60] at hdiv hlt
  rw [hAcard] at hdvdA
  have : Nat.card ↥(Subgroup.closure ({a, b, k} : Set G)) = 180 := by
    obtain ⟨m, hm⟩ := hdiv
    have hm_gt : 1 < m := by omega
    have hmdvd : m ∣ 3 := by
      have h180 : (180 : ℕ) = 60 * 3 := by norm_num
      rw [hm, h180] at hdvdA
      exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 60)).mp hdvdA
    rcases (Nat.dvd_prime Nat.prime_three).mp hmdvd with h1 | h3
    · omega
    · omega
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [this, hAcard])

private theorem center_model_exists [Finite G]
    {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S)
    (h2 : VA5 L2)
    (hD : G24LocalData L1 L2 S) :
    Nonempty (A5Model (L2 ⊔ bigB L1 L2 S) L2 (centerOf (dsQ L2 L1 S)) ⊥
      Certificates.A5GL42.HN) := by
  classical
  let P2 : Subgroup G := L2 ⊔ bigB L1 L2 S
  let Q2 : Subgroup G := dsQ L2 L1 S
  let Z2 : Subgroup G := centerOf Q2
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hL2N : P2 ≤ Subgroup.normalizer (L2 : Set G) := G24LocalData.normal_L_right hR
  have hP2NZ2 : P2 ≤ Subgroup.normalizer (Z2 : Set G) :=
    P_le_normalizer_centerOf_dsQ_right L1 L2 S
  have hZ2card : Nat.card Z2 = 2 ^ 4 := hD.card_center_right
  have hZ2exp : ∀ z ∈ Z2, z ^ 2 = 1 := fun z hz =>
    hD.sq_eq_one_of_mem_centerOf_right hz
  have hZ2comm : ∀ z ∈ Z2, ∀ z' ∈ Z2, z * z' = z' * z := by
    intro z hz z' hz'
    exact Subgroup.mem_centralizer_iff.mp hz'.2 z hz.1
  have hZ2pre : A5Pre P2 L2 Z2 ⊥ := by
    refine ⟨le_sup_left, hL2N, hP2NZ2, ?_, ?_, ?_, ?_, h2, ?_⟩
    · intro x hx
      rw [Subgroup.mem_normalizer_iff]
      intro y
      simp
    · refine ⟨bot_le, ?_, ?_⟩
      · refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
        rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
        exact hZ2comm a ha b hb
      · intro e he
        rw [Subgroup.mem_bot]
        exact hZ2exp e he
    · rw [Subgroup.relIndex_bot_left, hZ2card]
      norm_num
    · intro q hq e he
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      have hqQ : q ∈ Q2 := by
        change q ∈ dsQ L2 L1 S
        rw [dsQ_eq_pCoreOf_right]
        exact hq
      exact Subgroup.mem_centralizer_iff.mp he.2 q hqQ
    · obtain ⟨e5⟩ := CFSG.Quasithin.S1421QA17.nonempty_mulEquiv_alt5_of_isL2Quot_two h2
      obtain ⟨⟨l, hlL⟩, hl3⟩ :=
        CFSG.GroupTheory.AlternatingFive.exists_orderOf_eq_three_of_oTwoQuot_mulEquiv e5
      have hl3' : orderOf l = 3 := by rw [Subgroup.orderOf_mk] at hl3; exact hl3
      haveI : Nontrivial ↥Z2 := Finite.one_lt_card_iff_nontrivial.mp (by
        rw [hZ2card]; norm_num)
      obtain ⟨⟨e, he⟩, he1⟩ := exists_ne (1 : ↥Z2)
      refine ⟨l, hlL, e, he, ?_⟩
      intro hcomm
      have hcomm' : ⁅e, l⁆ = 1 := by
        rw [← commutatorElement_inv (g₁ := l) (g₂ := e), hcomm, inv_one]
      have hbot := hD.natZ_right l hlL hl3' e he (by
        rw [Subgroup.mem_bot]; exact hcomm')
      exact he1 (Subtype.ext (Subgroup.mem_bot.mp hbot))
  rcases A5Pre.exists_model' hZ2pre with ⟨-, ⟨M⟩⟩ | ⟨hnot, -⟩
  · exact ⟨M⟩
  · exact absurd hD.natZ_right hnot

private theorem exists_center_frame [Finite G]
    {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S)
    (hD : G24LocalData L1 L2 S)
    {k : G} (hkZ : ∀ z ∈ centerOf (dsQ L2 L1 S), k * z = z * k)
    {aP bP : ↥(L2 ⊔ bigB L1 L2 S)}
    (haLN : (aP : G) ∈ L2) (hbLN : (bP : G) ∈ L2)
    (ha2 : (aP : G) ^ 2 = 1) (haQ : (aP : G) ∉ dsQ L2 L1 S)
    (hb3 : (bP : G) ^ 3 = 1) (hb1 : (bP : G) ≠ 1)
    (hab5 : ((aP : G) * (bP : G)) ^ 5 = 1)
    (MZ : A5Model (L2 ⊔ bigB L1 L2 S) L2 (centerOf (dsQ L2 L1 S)) ⊥
      Certificates.A5GL42.HN) :
    ∃ FZ : ElemFrame (L2 ⊔ bigB L1 L2 S) (centerOf (dsQ L2 L1 S)) ⊥,
      glMat (FZ.M aP) = aN ∧ glMat (FZ.M bP) = bN ∧
      ∀ p : ↥(L2 ⊔ bigB L1 L2 S), (p : G) = k → FZ.M p = 1 := by
  classical
  let P2 : Subgroup G := L2 ⊔ bigB L1 L2 S
  let Q2 : Subgroup G := dsQ L2 L1 S
  let Z2 : Subgroup G := centerOf Q2
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hQ2eq : pCoreOf 2 L2 = Q2 := G24LocalData.pCoreOf_eq_dsQ_right hR hD.le_right
  have hP2NZ2 : P2 ≤ Subgroup.normalizer (Z2 : Set G) :=
    P_le_normalizer_centerOf_dsQ_right L1 L2 S
  have hMa : glMat (MZ.F.M aP) ∈ Certificates.A5GL42.HN := MZ.imgL aP haLN
  have hMb : glMat (MZ.F.M bP) ∈ Certificates.A5GL42.HN := MZ.imgL bP hbLN
  have ha : MZ.F.M aP * MZ.F.M aP = 1 := by
    rw [← map_mul, show aP * aP = 1 from Subtype.ext (by simpa [pow_two] using ha2),
      map_one]
  have ha1 : MZ.F.M aP ≠ 1 := by
    intro h
    have hq : (aP : G) ∈ pCoreOf 2 L2 := (MZ.kerL aP haLN).mp h
    exact haQ (by rwa [hQ2eq] at hq)
  have hb : MZ.F.M bP ^ 3 = 1 := by
    rw [← map_pow, show bP ^ 3 = 1 from Subtype.ext (by
      simpa [pow_succ, mul_assoc] using hb3), map_one]
  have hab : (MZ.F.M aP * MZ.F.M bP) ^ 5 = 1 := by
    rw [← map_mul, ← map_pow,
      show (aP * bP) ^ 5 = 1 from Subtype.ext (by simpa using hab5), map_one]
  have hff : ∀ v : Fin 4 → ZMod 2,
      (MZ.F.M bP : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v = v → v = 0 :=
    (fixFree_iff MZ.F hP2NZ2 bP).mp
      (hD.natZ_right (bP : G) hbLN (orderOf_eq_prime hb3 hb1))
  obtain ⟨g, hga, hgb⟩ :=
    CFSG.GH74.QTGen4.DSGen4.Lin2B.exists_natural_conj a5Facts
      (MZ.F.M aP) (MZ.F.M bP) ha ha1 hb hab hff
  refine ⟨MZ.F.conj g, ?_, ?_, ?_⟩
  · rw [ElemFrame.conj_M]
    simp only [glMat, Units.val_mul]
    rw [hga, mul_assoc, ElemFrame.glMat_mul_inv, mul_one]
  · rw [ElemFrame.conj_M]
    simp only [glMat, Units.val_mul]
    rw [hgb, mul_assoc, ElemFrame.glMat_mul_inv, mul_one]
  · intro p hp
    rw [ElemFrame.conj_M]
    have hM1 : MZ.F.M p = 1 := ElemFrame.M_eq_one MZ.F hP2NZ2 p (fun e he => by
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      rw [hp]
      exact hkZ e he)
    rw [hM1]
    simp

theorem exists_g24Frame2 [Finite G]
    {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S)
    (h2 : VA5 L2) (hD : G24LocalData L1 L2 S) {k : G}
    (hkB : k ∈ bigB L1 L2 S) (hk3 : orderOf k = 3) (hkL : k ∉ L2)
    (hkc : ∀ x ∈ L2 ⊔ bigB L1 L2 S, ⁅k, x⁆ ∈ dsQ L2 L1 S)
    (hkZ : ∀ z ∈ centerOf (dsQ L2 L1 S), k * z = z * k)
    (hkQ : dsQ L2 L1 S ⊓ Subgroup.centralizer ({k} : Set G) = centerOf (dsQ L2 L1 S))
    (hY : ∃ Y : Subgroup G, Y ≤ (L2 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({k} : Set G) ∧
      Nat.card Y = 4 ∧ Y ⊓ centerOf (dsQ L2 L1 S) = ⊥) :
    ∃ F : G24Frame2 L1 L2 S, F.k = k := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let P2 : Subgroup G := L2 ⊔ bigB L1 L2 S
  let Q2 : Subgroup G := dsQ L2 L1 S
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hQ2eq : pCoreOf 2 L2 = Q2 := G24LocalData.pCoreOf_eq_dsQ_right hR hD.le_right
  have hQ2L2 : Q2 ≤ L2 := by rw [← hQ2eq]; exact CFSG.LieType.BorelTits.pCoreOf_le 2 L2
  obtain ⟨A, hAle, hAinf, hAcard, hkA, hdecomp⟩ :=
    G24Vertex2.exists_complement_right hF h2 hD hkB hk3 hkc hkZ hkQ hY
  have hAP2 : A ≤ P2 := fun x hx => (hAle hx).1
  have hAcardL : Nat.card ↥(A ⊓ L2) = 60 :=
    G24Vertex2.card_inf_L2_of_complement hF h2 hD hAP2 hAcard hdecomp
  obtain ⟨W, hmemW, hWcard, ⟨MN⟩⟩ := exists_frameW_model hF h2 hD
  have hgl_one := gl_one_of_model (A := A) (W := W) (MN := MN) hQ2eq hAinf
  obtain ⟨aL, haL, haM⟩ := MN.surjL aN a5Facts.gens.1
  obtain ⟨aP, haA', haLN, haN, haQ⟩ :=
    exists_lift_mem_A_inf_L2 hAP2 hQ2L2 hAinf hdecomp aL haL aN haM
      (by decide : aN ≠ 1)
  obtain ⟨bL, hbL, hbM⟩ := MN.surjL bN a5Facts.gens.2.1
  obtain ⟨bP, hbA', hbLN, hbN, hbQ⟩ :=
    exists_lift_mem_A_inf_L2 hAP2 hQ2L2 hAinf hdecomp bL hbL bN hbM
      (by decide : bN ≠ 1)
  have ha1 : (aP : G) ≠ 1 := fun h => haQ (h ▸ Q2.one_mem)
  have hb1 : (bP : G) ≠ 1 := fun h => hbQ (h ▸ Q2.one_mem)
  obtain ⟨ha2, hb3, hab5, hab1⟩ :=
    exists_generators_relations hgl_one haA' haLN haN hbA' hbLN hbN ha1 hb1
  have hclosure_ab : Subgroup.closure ({(aP : G), (bP : G)} : Set G) = A ⊓ L2 :=
    G24Vertex2.closure_ab_eq_A_inf_L2 hF h2 hD hAP2 hAinf hAcard hdecomp
      haA' haLN hbA' hbLN ha1 hb1 ha2 hb3 hab5 hab1
  have hclosure_eq : Subgroup.closure ({(aP : G), (bP : G), k} : Set G) = A :=
    closure_ab_k_eq_A hAcard hAcardL haA' hbA' hkA hclosure_ab hkL
  obtain ⟨MZ⟩ := center_model_exists hF h2 hD
  obtain ⟨FZ, hFZa, hFZb, hFZk⟩ :=
    exists_center_frame hF hD hkZ haLN hbLN ha2 haQ hb3 hb1 hab5 MZ
  exact ⟨{
    k := k, a := (aP : G), b := (bP : G), A := A, W := W, FN := MN.F, FZ := FZ,
    k_mem := hkB, k_not_mem := hkL, orderOf_k := hk3, comm_k := hkc,
    cent_Z := hkZ, inf_centralizer := hkQ, A_le := hAle, inf_A := hAinf,
    decomp := hdecomp, card_A := hAcard, k_mem_A := hkA,
    a_mem := ⟨haA', haLN⟩, b_mem := ⟨hbA', hbLN⟩,
    a_sq := ha2, b_cube := hb3, ab_five := hab5,
    closure_ab := hclosure_ab, closure_eq := hclosure_eq,
    mem_W := hmemW, card_W := hWcard,
    FN_a := by
      intro p hp
      rw [show p = aP from Subtype.ext hp]
      exact haN,
    FN_b := by
      intro p hp
      rw [show p = bP from Subtype.ext hp]
      exact hbN,
    FZ_a := by
      intro p hp
      rw [show p = aP from Subtype.ext hp]
      exact hFZa,
    FZ_b := by
      intro p hp
      rw [show p = bP from Subtype.ext hp]
      exact hFZb,
    FZ_k := hFZk }, rfl⟩


end CFSG.Quasithin.F112R.St84
