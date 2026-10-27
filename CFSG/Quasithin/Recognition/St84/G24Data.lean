module

public import CFSG.GH74.QTGen4.DSGen4.Leaf.DSAA6
public import CFSG.Quasithin.Recognition.GoldschmidtF112RY9
public import CFSG.Quasithin.Recognition.GoldschmidtF112RSt84HypA
public import CFSG.Quasithin.Recognition.Stroth.BenderFrame
public import CFSG.RankThree.PartOne.K1214.Basic
import CFSG.GroupTheory.NormalizerInfCentralizer
public import CFSG.GH74.QTGen4.DSGen4.Statements
public import CFSG.Quasithin.Background.A1cA133

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
  CFSG.GH74.QTGen4.DSGen4 CFSG.Quasithin.F7
open scoped commutatorElement

variable {G : Type} [Group G]

structure G24LocalData (L1 L2 S : Subgroup G) : Prop where
  le_left : S ≤ L1
  le_right : S ≤ L2
  card_bigB : Nat.card (bigB L1 L2 S) = 2 ^ 12 * 3 ^ 2
  special_left : IsSpecialPow 2 (2 ^ 2) 2 ↥(dsQ L1 L2 S)
  center_left : centerOf (dsQ L1 L2 S) = centerOf L1
  irr_left : ∀ X : Subgroup G, centerOf (dsQ L1 L2 S) ≤ X → X ≤ dsQ L1 L2 S →
    L1 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer (X : Set G) →
      X = centerOf (dsQ L1 L2 S) ∨ X = dsQ L1 L2 S
  orth_left : ∃ E : Subgroup G, centerOf (dsQ L1 L2 S) ≤ E ∧ E ≤ dsQ L1 L2 S ∧
    (centerOf (dsQ L1 L2 S)).relIndex E = 16 ∧ L1 ≤ Subgroup.normalizer (E : Set G) ∧
    (∃ l ∈ L1, ∃ e ∈ E, ⁅l, e⁆ ∉ centerOf (dsQ L1 L2 S)) ∧
    ¬ NatSec L1 (centerOf (dsQ L1 L2 S)) E
  card_right : Nat.card (dsQ L2 L1 S) = 2 ^ 10
  special_right : IsSpecialPGroup 2 ↥(dsQ L2 L1 S)
  card_center_right : Nat.card ↥(centerOf (dsQ L2 L1 S)) = 2 ^ 4
  natZ_right : NatSec L2 ⊥ (centerOf (dsQ L2 L1 S))
  mid_right : ∃ W : Subgroup G, centerOf (dsQ L2 L1 S) ≤ W ∧ W ≤ dsQ L2 L1 S ∧
    Nat.card W = 2 ^ 6 ∧ ⁅W, L2⁆ ≤ centerOf (dsQ L2 L1 S) ∧ NatSec L2 W (dsQ L2 L1 S)
  comm_right : ⁅dsQ L2 L1 S, L2⁆ = dsQ L2 L1 S
  card_inf : Nat.card ↥(dsQ L1 L2 S ⊓ dsQ L2 L1 S) = 2 ^ 8

namespace G24LocalData

theorem pCoreOf_eq_dsQ_left [Finite G] {L1 L2 S : Subgroup G} (hR : Hyp111R L1 L2 S)
    (hSL : S ≤ L1) : pCoreOf 2 L1 = dsQ L1 L2 S := by
  refine le_antisymm (F1.pCoreOf_le_pCoreOf_parabolic hR) ?_
  have hQ : pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ≤ S :=
    isSylowTwoOf_pCoreOf_le (F112W.isSylowTwoOf_parabolic hR)
  rw [← F1.inf_pCoreOf_parabolic_eq hR]
  exact le_inf le_rfl (hQ.trans hSL)

theorem pCoreOf_eq_dsQ_right [Finite G] {L1 L2 S : Subgroup G} (hR : Hyp111R L1 L2 S)
    (hSR : S ≤ L2) : pCoreOf 2 L2 = dsQ L2 L1 S :=
  pCoreOf_eq_dsQ_left (L1 := L2) (L2 := L1) (S := S) hR.symm hSR

theorem normal_L_left {L1 L2 S : Subgroup G} (hR : Hyp111R L1 L2 S) :
    L1 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer (L1 : Set G) :=
  F1.parabolic_le_normalizer hR

theorem normal_L_right {L1 L2 S : Subgroup G} (hR : Hyp111R L1 L2 S) :
    L2 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer (L2 : Set G) := by
  have h := F1.parabolic_le_normalizer hR.symm
  rwa [bigB_comm] at h

theorem charTwo_P_left {L1 L2 S : Subgroup G} (hR : Hyp111R L1 L2 S) :
    CharTwo (L1 ⊔ bigB L1 L2 S) :=
  F1.parabolic_charTwo hR

theorem charTwo_P_right {L1 L2 S : Subgroup G} (hR : Hyp111R L1 L2 S) :
    CharTwo (L2 ⊔ bigB L1 L2 S) := by
  have h := F1.parabolic_charTwo hR.symm
  rwa [bigB_comm] at h

private theorem relIndex_bigB_left [Finite G]
    {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S) (h1 : VA5 L1)
    (hD : G24LocalData L1 L2 S) :
    (bigB L1 L2 S).relIndex (L1 ⊔ bigB L1 L2 S) = 5 := by
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hrel : (borelOf L1 S).relIndex L1 = 5 := by
    have h' := index_borelOf_of_psl2 (f := 2) (by norm_num) hF.1.h1.sylow h1
    simpa [Subgroup.relIndex] using h'
  rw [F112W.relIndex_sup_eq_relIndex_inf (N := L1) (B := bigB L1 L2 S)
    ((F1.bigB_le_normalizer_left hR).1), F1.inf_bigB_eq_borelOf hR]
  exact hrel

private theorem relIndex_bigB_right [Finite G]
    {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S) (h2 : VA5 L2)
    (hD : G24LocalData L1 L2 S) :
    (bigB L1 L2 S).relIndex (L2 ⊔ bigB L1 L2 S) = 5 := by
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hrel : (borelOf L2 S).relIndex L2 = 5 := by
    have h' := index_borelOf_of_psl2 (f := 2) (by norm_num) hF.1.h2.sylow h2
    simpa [Subgroup.relIndex] using h'
  have hinf : L2 ⊓ bigB L1 L2 S = borelOf L2 S := by
    have h := F1.inf_bigB_eq_borelOf hR.symm
    rwa [bigB_comm] at h
  rw [F112W.relIndex_sup_eq_relIndex_inf (N := L2) (B := bigB L1 L2 S)
    ((F1.bigB_le_normalizer_left hR).2), hinf]
  exact hrel

theorem card_vertex_left [Finite G] {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (hD : G24LocalData L1 L2 S) :
    Nat.card ↥(L1 ⊔ bigB L1 L2 S) = 2 ^ 12 * 45 := by
  have hrel := relIndex_bigB_left hF h1 hD
  have hBP : bigB L1 L2 S ≤ L1 ⊔ bigB L1 L2 S := le_sup_right
  have hcard := Subgroup.relIndex_mul_card (H := bigB L1 L2 S) (K := L1 ⊔ bigB L1 L2 S)
  rw [inf_eq_left.mpr hBP, hD.card_bigB, hrel] at hcard
  norm_num at hcard ⊢
  omega

theorem card_vertex_right [Finite G] {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) (h2 : VA5 L2) (hD : G24LocalData L1 L2 S) :
    Nat.card ↥(L2 ⊔ bigB L1 L2 S) = 2 ^ 12 * 45 := by
  have hrel := relIndex_bigB_right hF h2 hD
  have hBP : bigB L1 L2 S ≤ L2 ⊔ bigB L1 L2 S := le_sup_right
  have hcard := Subgroup.relIndex_mul_card (H := bigB L1 L2 S) (K := L2 ⊔ bigB L1 L2 S)
  rw [inf_eq_left.mpr hBP, hD.card_bigB, hrel] at hcard
  norm_num at hcard ⊢
  omega

theorem card_L_left [Finite G]
    {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S) (h1 : VA5 L1)
    (hD : G24LocalData L1 L2 S) :
    Nat.card L1 = 60 * Nat.card (dsQ L1 L2 S) := by
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hQ : pCoreOf 2 L1 = dsQ L1 L2 S := pCoreOf_eq_dsQ_left hR hD.le_left
  have h60 : Nat.card (oTwoQuot ↥L1) = 60 := by
    rw [IsL2Quot.card (by norm_num : 1 ≤ 2) h1]
    norm_num
  have hp : Nat.card (pCore 2 ↥L1) = Nat.card (pCoreOf 2 L1) := by
    rw [pCoreOf]
    exact (Subgroup.card_map_of_injective L1.subtype_injective).symm
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (pCore 2 ↥L1)
  rw [h60, hp, hQ] at h
  exact h

theorem card_L_right [Finite G]
    {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S) (h2 : VA5 L2)
    (hD : G24LocalData L1 L2 S) :
    Nat.card L2 = 60 * Nat.card (dsQ L2 L1 S) := by
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hQ : pCoreOf 2 L2 = dsQ L2 L1 S := pCoreOf_eq_dsQ_right hR hD.le_right
  have h60 : Nat.card (oTwoQuot ↥L2) = 60 := by
    rw [IsL2Quot.card (by norm_num : 1 ≤ 2) h2]
    norm_num
  have hp : Nat.card (pCore 2 ↥L2) = Nat.card (pCoreOf 2 L2) := by
    rw [pCoreOf]
    exact (Subgroup.card_map_of_injective L2.subtype_injective).symm
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (pCore 2 ↥L2)
  rw [h60, hp, hQ] at h
  exact h

private theorem card_borelOf_right [Finite G]
    {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S) (h2 : VA5 L2)
    (hD : G24LocalData L1 L2 S) :
    Nat.card (borelOf L2 S) = 12 * 2 ^ 10 := by
  have hrel : (borelOf L2 S).relIndex L2 = 5 := by
    have h' := index_borelOf_of_psl2 (f := 2) (by norm_num) hF.1.h2.sylow h2
    simpa [Subgroup.relIndex] using h'
  have hL := card_L_right hF h2 hD
  have hQ : Nat.card (dsQ L2 L1 S) = 2 ^ 10 := hD.card_right
  have h := Subgroup.relIndex_mul_card (H := borelOf L2 S) (K := L2)
  rw [inf_eq_left.mpr (F1.borelOf_le L2 S), hrel, hL, hQ] at h
  norm_num at h ⊢
  omega

private theorem exists_k_of_side [Finite G] {L P B Q : Subgroup G}
    (hLP : L ≤ P) (hPL : P ≤ Subgroup.normalizer (L : Set G))
    (hPQ : P ≤ Subgroup.normalizer (Q : Set G))
    (hQdef : Q = pCoreOf 2 L) (hquot : IsL2Quot 2 (oTwoQuot ↥L))
    (hQcard : Nat.card Q = 2 ^ 10) (hLcard : Nat.card L = 60 * Nat.card Q)
    (hPcard : Nat.card P = 2 ^ 12 * 45) (hBP : B ≤ P) (hPB : B.relIndex P = 5)
    (hBcard : Nat.card B = 2 ^ 12 * 3 ^ 2) (hQB : Q ≤ B) :
    ∃ k ∈ B, orderOf k = 3 ∧ k ∉ L ∧ ∀ x ∈ P, ⁅k, x⁆ ∈ Q := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQL : Q ≤ L := by rw [hQdef]; exact CFSG.LieType.BorelTits.pCoreOf_le 2 L
  have hQP : Q ≤ P := hQL.trans hLP
  have hidx : L.relIndex P = 3 := by
    have h := Subgroup.relIndex_mul_card (H := L) (K := P)
    rw [inf_eq_left.mpr hLP, hPcard, hLcard, hQcard] at h
    norm_num at h ⊢
    omega
  set C : Subgroup G := dsCentMod P L Q with hCdef
  have hQC : Q ≤ C := by
    rw [hCdef]
    exact dsa6_le_K hLP hQP hPQ
  have hCinf : C ⊓ L = Q := by
    refine le_antisymm ?_ (le_inf hQC hQL)
    rintro x ⟨hxC, hxL⟩
    have hxcomm : ∀ l ∈ L, ⁅x, l⁆ ∈ Q := (dsa6_mem_K.mp hxC).2.2
    have hxpc : x ∈ pCoreOf 2 L := by
      refine dsa6_K_inf (Q := Q) hquot ?_ hxL hxcomm
      rw [hQdef]
      exact inf_le_left
    rwa [← hQdef] at hxpc
  have hCne : C ≠ Q := by
    intro hCeq
    let ρ : ↥P →* MulAut (oTwoQuot ↥L) :=
      (CFSG.Quasithin.Stroth.oTwoQuotConj L).comp (Subgroup.inclusion hPL)
    have hcomm_iff : ∀ p : ↥P, ∀ l ∈ L,
        (p : G) * l⁻¹ * (p : G)⁻¹ * l ∈ pCoreOf 2 L ↔
          ⁅(p : G), l⁆ ∈ pCoreOf 2 L := by
      intro p l hl
      have hlN : l⁻¹ ∈ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
        (Subgroup.normalizer (pCoreOf 2 L : Set G)).inv_mem
          ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L) hl)
      have hA : (p : G) * l⁻¹ * (p : G)⁻¹ * l = l⁻¹ * ⁅(p : G), l⁆⁻¹ * l := by
        simp only [commutatorElement_def]
        group
      rw [hA]
      have h1 := (Subgroup.mem_normalizer_iff.mp hlN ⁅(p : G), l⁆⁻¹).symm.trans
        (Subgroup.inv_mem_iff (H := pCoreOf 2 L))
      simpa using h1
    have hρker : ρ.ker = C.subgroupOf P := by
      ext p
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      show CFSG.Quasithin.Stroth.oTwoQuotConj L ⟨(p : G), hPL p.2⟩ = 1 ↔ (p : G) ∈ C
      rw [CFSG.Quasithin.Stroth.oTwoQuotConj_eq_one_iff, hCdef, dsa6_mem_K]
      constructor
      · intro hh
        refine ⟨p.2, hPQ p.2, fun l hl => ?_⟩
        have := (hcomm_iff p l hl).mp (hh l hl)
        rwa [hQdef]
      · rintro ⟨-, -, hh⟩ l hl
        have hh' : ⁅(p : G), l⁆ ∈ pCoreOf 2 L := by
          rw [← hQdef]
          exact hh l hl
        exact (hcomm_iff p l hl).mpr hh'
    have hkerCard : Nat.card ρ.ker = Nat.card Q := by
      rw [hρker, hCeq]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQP).toEquiv
    obtain ⟨e⟩ := CFSG.Quasithin.S1421QA17.nonempty_mulEquiv_alt5_of_isL2Quot_two hquot
    have hbij :=
      CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 le_rfl (by norm_num)
    have hcardPerm : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
      norm_num
    have hcardAut : Nat.card (MulAut (oTwoQuot ↥L)) = 120 := by
      have h1 : Nat.card (MulAut (oTwoQuot ↥L)) =
          Nat.card (MulAut (alternatingGroup (Fin 5))) :=
        Nat.card_congr (MulAut.congr e).toEquiv
      rw [h1, ← Nat.card_congr (Equiv.ofBijective _ hbij)]
      exact hcardPerm
    have hle : Nat.card ρ.range ≤ 120 := by
      rw [← hcardAut]
      exact Subgroup.card_le_card_group (H := ρ.range)
    have hPQC : Nat.card P = 180 * Nat.card Q := by
      rw [hPcard, hQcard]
      norm_num
    have hfr := Subgroup.card_ker_mul_card_range ρ
    rw [hkerCard, hPQC] at hfr
    have hQpos : 0 < Nat.card Q := Nat.card_pos
    have hle2 : Nat.card Q * Nat.card ρ.range ≤ Nat.card Q * 120 :=
      Nat.mul_le_mul_left _ hle
    have hlt : Nat.card Q * 120 < Nat.card Q * 180 :=
      Nat.mul_lt_mul_of_pos_left (by norm_num) hQpos
    omega
  have hCsup : C ⊔ L = P := by
    have hnotle : ¬ C ≤ L := by
      intro hle
      exact hCne ((inf_eq_left.mpr hle).symm.trans hCinf)
    have h1 : C ⊔ L ≤ P :=
      sup_le (fun x hx => (dsa6_mem_K.mp (hCdef ▸ hx)).1) hLP
    have h2 : L ≤ C ⊔ L := le_sup_right
    have h3 : L.relIndex P = L.relIndex (C ⊔ L) * (C ⊔ L).relIndex P :=
      (Subgroup.relIndex_mul_relIndex L (C ⊔ L) P h2 h1).symm
    rw [hidx] at h3
    have hne1 : L.relIndex (C ⊔ L) ≠ 1 := by
      intro hh
      exact hnotle (le_trans le_sup_left (Subgroup.relIndex_eq_one.mp hh))
    have hdvd : L.relIndex (C ⊔ L) ∣ 3 := ⟨(C ⊔ L).relIndex P, h3⟩
    have h4 : L.relIndex (C ⊔ L) = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h' | h'
      · exact absurd h' hne1
      · exact h'
    have h5 : (C ⊔ L).relIndex P = 1 := by
      rw [h4] at h3
      omega
    exact le_antisymm h1 (Subgroup.relIndex_eq_one.mp h5)
  have hCNL : C ≤ Subgroup.normalizer (L : Set G) :=
    fun c hc => hPL (dsa6_mem_K.mp (hCdef ▸ hc)).1
  have hCcard : Nat.card C = 3 * Nat.card Q := by
    have h := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
      (A := L) (B := C) hCNL
    rw [show L ⊔ C = P by rw [sup_comm, hCsup], inf_comm, hCinf] at h
    have hPL3 : Nat.card P = 3 * Nat.card L := by
      rw [hPcard, hLcard, hQcard]
      norm_num
    have hcancel : Nat.card L * (3 * Nat.card Q) = Nat.card L * Nat.card C := by
      calc Nat.card L * (3 * Nat.card Q) = 3 * Nat.card L * Nat.card Q := by ring
        _ = Nat.card P * Nat.card Q := by rw [hPL3]
        _ = Nat.card L * Nat.card C := h
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hcancel.symm
  have hPNC : P ≤ Subgroup.normalizer (C : Set G) := by
    intro p hp
    rw [Subgroup.mem_normalizer_iff]
    intro c
    constructor
    · intro hc
      exact dsa6_K_conj hPL hPQ hp (hCdef ▸ hc)
    · intro hc
      have h1 := dsa6_K_conj hPL hPQ (P.inv_mem hp) (hCdef ▸ hc)
      rwa [show p⁻¹ * (p * c * p⁻¹) * (p⁻¹)⁻¹ = c by group] at h1
  have hBNC : B ≤ Subgroup.normalizer (C : Set G) := hBP.trans hPNC
  have hC_le_B : C ≤ B := by
    by_contra hle
    have hBmax : ∀ X : Subgroup G, B ≤ X → X ≤ P → X = B ∨ X = P := by
      intro X hBX hXP
      by_cases hXB : X = B
      · exact Or.inl hXB
      · right
        have hdvd := Subgroup.relIndex_mul_relIndex B X P hBX hXP
        rw [hPB] at hdvd
        have hne1 : B.relIndex X ≠ 1 := by
          intro h1
          exact hXB (le_antisymm (Subgroup.relIndex_eq_one.mp h1) hBX)
        have hdvd' : B.relIndex X ∣ 5 := ⟨X.relIndex P, hdvd.symm⟩
        rcases (Nat.dvd_prime Nat.prime_five).mp hdvd' with h1 | h5
        · exact absurd h1 hne1
        · have hXP1 : X.relIndex P = 1 := by
            rw [h5] at hdvd
            omega
          exact le_antisymm hXP (Subgroup.relIndex_eq_one.mp hXP1)
    have hCBle : C ⊔ B ≤ P :=
      sup_le (fun c hc => (dsa6_mem_K.mp (hCdef ▸ hc)).1) hBP
    have hlt : C ⊔ B ≠ B := by
      intro heq
      exact hle (fun c hc => by
        rw [← heq]
        exact Subgroup.mem_sup_left hc)
    have hsupCB : C ⊔ B = P := by
      rcases hBmax (C ⊔ B) le_sup_right hCBle with h | h
      · exact absurd h hlt
      · exact h
    have hcardCB := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
      (A := C) (B := B) hBNC
    rw [hsupCB] at hcardCB
    have hPQC : Nat.card P = 180 * Nat.card Q := by
      rw [hPcard, hQcard]
      norm_num
    have hBQ : Nat.card B = 36 * Nat.card Q := by
      rw [hBcard, hQcard]
      norm_num
    have heq : 180 * Nat.card Q * Nat.card ↥(C ⊓ B) = 108 * Nat.card Q * Nat.card Q := by
      calc 180 * Nat.card Q * Nat.card ↥(C ⊓ B)
          = Nat.card P * Nat.card ↥(C ⊓ B) := by rw [hPQC]
        _ = Nat.card C * Nat.card B := hcardCB
        _ = (3 * Nat.card Q) * (36 * Nat.card Q) := by rw [hCcard, hBQ]
        _ = 108 * Nat.card Q * Nat.card Q := by ring
    have hge : Nat.card Q ≤ Nat.card ↥(C ⊓ B) := Subgroup.card_le_of_le (le_inf hQC hQB)
    nlinarith [Nat.card_pos (α := Q), hge, heq]
  have hCP : C ≤ P := hC_le_B.trans hBP
  have hQnC : (Q.subgroupOf C).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (fun c hc => hPQ (hCP hc))
  have hCQcard : Nat.card (C ⧸ Q.subgroupOf C) = 3 := by
    have hq := Subgroup.card_eq_card_quotient_mul_card_subgroup (Q.subgroupOf C)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQC).toEquiv, hCcard] at hq
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hq.symm
  have hcommCC : ⁅C, C⁆ ≤ Q := by
    haveI : IsCyclic (C ⧸ Q.subgroupOf C) := isCyclic_of_prime_card hCQcard
    haveI : IsMulCommutative (C ⧸ Q.subgroupOf C) := IsCyclic.isMulCommutative
    haveI := hQnC
    have hcomm : _root_.commutator ↥C ≤ Q.subgroupOf C :=
      (Subgroup.Normal.quotient_commutative_iff_commutator_le
        (N := Q.subgroupOf C)).mp inferInstance
    rw [← Subgroup.map_subtype_commutator C]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact Subgroup.mem_subgroupOf.mp (hcomm hy)
  have hLCcomm : ⁅L, C⁆ ≤ Q := by
    refine Subgroup.commutator_le.mpr fun l hl c hc => ?_
    have h := (dsa6_mem_K.mp (hCdef ▸ hc)).2.2 l hl
    have h' : ⁅c, l⁆⁻¹ ∈ Q := Q.inv_mem h
    simpa [commutatorElement_inv] using h'
  have h3dvd : 3 ∣ Nat.card C := by
    rw [hCcard]
    exact dvd_mul_right 3 _
  obtain ⟨x, hx3⟩ := exists_prime_orderOf_dvd_card' 3 h3dvd
  have hxG3 : orderOf (x : G) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact hx3
  refine ⟨(x : G), hC_le_B x.2, hxG3, ?_, ?_⟩
  · intro hxL
    have hxQ : (x : G) ∈ Q := by
      have : (x : G) ∈ C ⊓ L := ⟨x.2, hxL⟩
      rwa [hCinf] at this
    have hQ2 : IsPGroup 2 Q := by rw [hQdef]; exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
    obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp hQ2) ⟨(x : G), hxQ⟩
    have hy3 : orderOf (⟨(x : G), hxQ⟩ : Q) = 3 := by
      rw [← Subgroup.orderOf_coe (⟨(x : G), hxQ⟩ : Q)]
      exact hxG3
    rw [hy3] at hn
    have hdvd : 3 ∣ 2 ^ n := by
      rw [← hn]
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
    norm_num at this
  · intro y hy
    have hdecomp : y ∈ L ⊔ C := by
      rw [sup_comm, hCsup]
      exact hy
    obtain ⟨a, ha, b, hb, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hCNL).mp hdecomp
    have h1 : ⁅b, (x : G)⁆ ∈ Q :=
      (Subgroup.commutator_le.mp hcommCC) b hb (x : G) x.2
    have h2 : a * ⁅b, (x : G)⁆ * a⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hPQ (hLP ha)) ⁅b, (x : G)⁆).mp h1
    have h3 : ⁅a, (x : G)⁆ ∈ Q :=
      (Subgroup.commutator_le.mp hLCcomm) a ha (x : G) x.2
    have h4 : ⁅a * b, (x : G)⁆ ∈ Q := by
      rw [commutatorElement_mul_left_eq_conj_mul]
      exact Q.mul_mem h2 h3
    rw [← commutatorElement_inv]
    exact Q.inv_mem h4

theorem exists_k_left [Finite G] {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (hD : G24LocalData L1 L2 S) :
    ∃ k ∈ bigB L1 L2 S, orderOf k = 3 ∧ k ∉ L1 ∧
      ∀ x ∈ L1 ⊔ bigB L1 L2 S, ⁅k, x⁆ ∈ dsQ L1 L2 S := by
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hQdef : dsQ L1 L2 S = pCoreOf 2 L1 :=
    (pCoreOf_eq_dsQ_left hR hD.le_left).symm
  refine exists_k_of_side (L := L1) (P := L1 ⊔ bigB L1 L2 S)
    (B := bigB L1 L2 S) (Q := dsQ L1 L2 S) le_sup_left (normal_L_left hR) ?_ hQdef h1
    ?_ (card_L_left hF h1 hD) (card_vertex_left hF h1 hD) le_sup_right
    (relIndex_bigB_left hF h1 hD) hD.card_bigB ?_
  · rw [show dsQ L1 L2 S = pCoreOf 2 (L1 ⊔ bigB L1 L2 S) from rfl]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  · have h := hD.special_left.2.1
    norm_num at h ⊢
    exact h
  · rw [show dsQ L1 L2 S = pCoreOf 2 (L1 ⊔ bigB L1 L2 S) from rfl]
    exact (isSylowTwoOf_pCoreOf_le (F112W.isSylowTwoOf_parabolic hR)).trans le_sup_right

theorem exists_k_right [Finite G] {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) (h2 : VA5 L2) (hD : G24LocalData L1 L2 S) :
    ∃ k ∈ bigB L1 L2 S, orderOf k = 3 ∧ k ∉ L2 ∧
      ∀ x ∈ L2 ⊔ bigB L1 L2 S, ⁅k, x⁆ ∈ dsQ L2 L1 S := by
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hQdef : dsQ L2 L1 S = pCoreOf 2 L2 :=
    (pCoreOf_eq_dsQ_right hR hD.le_right).symm
  refine exists_k_of_side (L := L2) (P := L2 ⊔ bigB L1 L2 S)
    (B := bigB L1 L2 S) (Q := dsQ L2 L1 S) le_sup_left (normal_L_right hR) ?_ hQdef h2
    hD.card_right (card_L_right hF h2 hD) (card_vertex_right hF h2 hD) le_sup_right
    (relIndex_bigB_right hF h2 hD) hD.card_bigB ?_
  · rw [show dsQ L2 L1 S = pCoreOf 2 (L2 ⊔ bigB L1 L2 S) from by
      unfold dsQ
      rw [bigB_comm]]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  · rw [show dsQ L2 L1 S = pCoreOf 2 (L2 ⊔ bigB L1 L2 S) from by
      unfold dsQ
      rw [bigB_comm]]
    exact (isSylowTwoOf_pCoreOf_le (F112W.isSylowTwoOf_parabolic' hR)).trans le_sup_right

theorem Q1_ne_Q2 {L1 L2 S : Subgroup G} (hD : G24LocalData L1 L2 S) :
    dsQ L1 L2 S ≠ dsQ L2 L1 S := by
  have hQ1card : Nat.card (dsQ L1 L2 S) = 2 ^ 10 := by
    have h := hD.special_left.2.1
    norm_num at h ⊢
    exact h
  have hQ2card : Nat.card (dsQ L2 L1 S) = 2 ^ 10 := hD.card_right
  intro heq
  have h := hD.card_inf
  rw [heq, inf_idem, hQ2card] at h
  norm_num at h

theorem center_vertex_left [Finite G] {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) (h2 : VA5 L2) (hD : G24LocalData L1 L2 S) :
    centerOf (L1 ⊔ bigB L1 L2 S) = ⊥ := by
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hSP : IsSylowTwoOf S (L1 ⊔ bigB L1 L2 S) := F112W.isSylowTwoOf_parabolic hR
  have hQ1S : dsQ L1 L2 S ≤ S := by
    rw [show dsQ L1 L2 S = pCoreOf 2 (L1 ⊔ bigB L1 L2 S) from rfl]
    exact isSylowTwoOf_pCoreOf_le hSP
  have hQ2S : dsQ L2 L1 S ≤ S := by
    rw [show dsQ L2 L1 S = pCoreOf 2 (L2 ⊔ bigB L1 L2 S) from by
      unfold dsQ
      rw [bigB_comm]]
    exact isSylowTwoOf_pCoreOf_le (F112W.isSylowTwoOf_parabolic' hR)
  have hQ2eq : dsQ L2 L1 S = pCoreOf 2 (L2 ⊔ bigB L1 L2 S) := by
    unfold dsQ
    rw [bigB_comm]
  have hQ2S' : pCoreOf 2 (L2 ⊔ bigB L1 L2 S) ≤ S := hQ2eq ▸ hQ2S
  have hchar2 := charTwo_P_right hR
  have hBcard2 := card_borelOf_right hF h2 hD
  have h3dvd : 3 ∣ Nat.card (borelOf L2 S) := by
    rw [hBcard2]
    norm_num
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx3⟩ := exists_prime_orderOf_dvd_card' 3 h3dvd
  have hxL : (x : G) ∈ L2 := F1.borelOf_le L2 S x.2
  have hxBig : (x : G) ∈ bigB L1 L2 S :=
    (show borelOf L2 S ≤ bigB L1 L2 S from le_sup_right.trans le_sup_left) x.2
  have hxP : (x : G) ∈ L1 ⊔ bigB L1 L2 S :=
    (show bigB L1 L2 S ≤ L1 ⊔ bigB L1 L2 S from le_sup_right) hxBig
  have hxG3 : orderOf (x : G) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact hx3
  refine le_antisymm ?_ bot_le
  rintro z hz
  unfold centerOf at hz
  rw [Subgroup.mem_inf] at hz
  obtain ⟨hzP, hzcent⟩ := hz
  have hSleP : S ≤ L1 ⊔ bigB L1 L2 S :=
    hD.le_left.trans (le_sup_left : L1 ≤ L1 ⊔ bigB L1 L2 S)
  have hQ1P : dsQ L1 L2 S ≤ L1 ⊔ bigB L1 L2 S := by
    rw [show dsQ L1 L2 S = pCoreOf 2 (L1 ⊔ bigB L1 L2 S) from rfl]
    exact CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hzQ1 : z ∈ dsQ L1 L2 S :=
    charTwo_P_left hR ⟨hzP, Subgroup.centralizer_le hQ1P hzcent⟩
  have hzS : z ∈ S := hQ1S hzQ1
  have hzcentS : z ∈ Subgroup.centralizer (S : Set G) :=
    Subgroup.centralizer_le hSleP hzcent
  have hzQ2' : z ∈ pCoreOf 2 (L2 ⊔ bigB L1 L2 S) :=
    hchar2 ⟨(hD.le_right.trans le_sup_left) hzS,
      Subgroup.centralizer_le hQ2S' hzcentS⟩
  have hzQ2 : z ∈ dsQ L2 L1 S := hQ2eq ▸ hzQ2'
  have hzZ2 : z ∈ centerOf (dsQ L2 L1 S) := by
    unfold centerOf
    rw [hQ2eq]
    exact ⟨hzQ2', Subgroup.centralizer_le hQ2S' hzcentS⟩
  have hcomm1 : ⁅z, (x : G)⁆ = 1 :=
    (Subgroup.mem_centralizer_iff_commutator_eq_one'.mp hzcent) (x : G) hxP
  have hzbot : z ∈ (⊥ : Subgroup G) :=
    hD.natZ_right (x : G) hxL hxG3 z hzZ2 (by
      rw [hcomm1]
      exact Subgroup.mem_bot.mpr rfl)
  exact Subgroup.mem_bot.mp hzbot

end G24LocalData

theorem dsQ_eq_pCoreOf_left (L1 L2 S : Subgroup G) :
    dsQ L1 L2 S = pCoreOf 2 (L1 ⊔ bigB L1 L2 S) :=
  rfl

theorem dsQ_eq_pCoreOf_right (L1 L2 S : Subgroup G) :
    dsQ L2 L1 S = pCoreOf 2 (L2 ⊔ bigB L1 L2 S) := by
  unfold dsQ
  rw [bigB_comm]

theorem dsQ_le_P_left (L1 L2 S : Subgroup G) :
    dsQ L1 L2 S ≤ L1 ⊔ bigB L1 L2 S := by
  rw [dsQ_eq_pCoreOf_left]
  exact CFSG.LieType.BorelTits.pCoreOf_le 2 _

theorem dsQ_le_P_right (L1 L2 S : Subgroup G) :
    dsQ L2 L1 S ≤ L2 ⊔ bigB L1 L2 S := by
  rw [← bigB_comm (L1 := L1)]
  exact CFSG.LieType.BorelTits.pCoreOf_le 2 _

theorem P_le_normalizer_dsQ_left (L1 L2 S : Subgroup G) :
    L1 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer (dsQ L1 L2 S : Set G) := by
  rw [dsQ_eq_pCoreOf_left]
  exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _

theorem P_le_normalizer_dsQ_right (L1 L2 S : Subgroup G) :
    L2 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer (dsQ L2 L1 S : Set G) := by
  rw [← bigB_comm (L1 := L1)]
  exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _

theorem P_le_normalizer_centerOf_dsQ_left (L1 L2 S : Subgroup G) :
    L1 ⊔ bigB L1 L2 S ≤
      Subgroup.normalizer (centerOf (dsQ L1 L2 S) : Set G) := by
  intro x hx
  exact CFSG.GroupTheory.mem_normalizer_inf_centralizer
    (P_le_normalizer_dsQ_left L1 L2 S hx) (P_le_normalizer_dsQ_left L1 L2 S hx)

theorem P_le_normalizer_centerOf_dsQ_right (L1 L2 S : Subgroup G) :
    L2 ⊔ bigB L1 L2 S ≤
      Subgroup.normalizer (centerOf (dsQ L2 L1 S) : Set G) := by
  intro x hx
  exact CFSG.GroupTheory.mem_normalizer_inf_centralizer
    (P_le_normalizer_dsQ_right L1 L2 S hx) (P_le_normalizer_dsQ_right L1 L2 S hx)

namespace G24LocalData

variable {L1 L2 S : Subgroup G}

theorem sq_eq_one_of_mem_centerOf_left (hD : G24LocalData L1 L2 S) {z : G}
    (hz : z ∈ centerOf (dsQ L1 L2 S)) : z ^ 2 = 1 := by
  rcases hD.special_left.1.2 with ⟨-, hexp⟩ | ⟨-, -, hexp⟩
  · simpa using hexp ⟨z, hz.1⟩
  · have hz' : (⟨z, hz.1⟩ : ↥(dsQ L1 L2 S)) ∈
        Subgroup.center ↥(dsQ L1 L2 S) := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hz.2 (y : G) y.2)
    simpa using hexp ⟨z, hz.1⟩ hz'

theorem sq_eq_one_of_mem_centerOf_right (hD : G24LocalData L1 L2 S) {z : G}
    (hz : z ∈ centerOf (dsQ L2 L1 S)) : z ^ 2 = 1 := by
  rcases hD.special_right.2 with ⟨-, hexp⟩ | ⟨-, -, hexp⟩
  · simpa using hexp ⟨z, hz.1⟩
  · have hz' : (⟨z, hz.1⟩ : ↥(dsQ L2 L1 S)) ∈
        Subgroup.center ↥(dsQ L2 L1 S) := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hz.2 (y : G) y.2)
    simpa using hexp ⟨z, hz.1⟩ hz'

theorem card_dsQ_left (hD : G24LocalData L1 L2 S) :
    Nat.card (dsQ L1 L2 S) = 2 ^ 10 := by
  simpa using hD.special_left.2.1

theorem card_dsQ_right (hD : G24LocalData L1 L2 S) :
    Nat.card (dsQ L2 L1 S) = 2 ^ 10 :=
  hD.card_right

theorem card_centerOf_dsQ_left (hD : G24LocalData L1 L2 S) :
    Nat.card (centerOf (dsQ L1 L2 S)) = 4 := by
  rw [CFSG.Quasithin.A1c.centerOf_eq_map_center,
    Subgroup.card_map_of_injective (f := (dsQ L1 L2 S).subtype)
      (Subgroup.subtype_injective (dsQ L1 L2 S))]
  simpa using hD.special_left.2.2

theorem card_centerOf_dsQ_right (hD : G24LocalData L1 L2 S) :
    Nat.card (centerOf (dsQ L2 L1 S)) = 2 ^ 4 := by
  simpa using hD.card_center_right

end G24LocalData

end CFSG.Quasithin.F112R.St84
