module

public import CFSG.GH74.QTGen4.DSGen4.Defs
public import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
public import CFSG.Quasithin.MS93.ASGroup
public import CFSG.Quasithin.Recognition.GoldschmidtF112RY9
public import CFSG.RankThree.PartOne.K1214.Basic
public import CFSG.Quasithin.EmptyFaithful.F112HypW
public import CFSG.GH74.QTGen4.DSGen4.Leaf.Lin2OfNaturalA

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
  CFSG.GH74.QTGen4.DSGen4
open scoped commutatorElement

variable {G : Type} [Group G]

structure Sp44LocalData (L1 L2 S : Subgroup G) : Prop where
  le_left : S ≤ L1
  le_right : S ≤ L2
  card_S : Nat.card S = 2 ^ 8
  elem_left : IsElemAbelian 2 (pCoreOf 2 L1)
  card_left : Nat.card (pCoreOf 2 L1) = 2 ^ 6
  center_left : Nat.card ↥(centerOf L1) = 2 ^ 2
  nat_left : NatSec L1 (centerOf L1) (pCoreOf 2 L1)
  indec_left : ⁅pCoreOf 2 L1, L1⁆ = pCoreOf 2 L1
  idx_left : L1.relIndex (L1 ⊔ bigB L1 L2 S) = 3
  elem_right : IsElemAbelian 2 (pCoreOf 2 L2)
  card_right : Nat.card (pCoreOf 2 L2) = 2 ^ 6
  center_right : Nat.card ↥(centerOf L2) = 2 ^ 2
  nat_right : NatSec L2 (centerOf L2) (pCoreOf 2 L2)
  indec_right : ⁅pCoreOf 2 L2, L2⁆ = pCoreOf 2 L2
  idx_right : L2.relIndex (L2 ⊔ bigB L1 L2 S) = 3
  card_inf : Nat.card ↥(pCoreOf 2 L1 ⊓ pCoreOf 2 L2) = 2 ^ 4

theorem Sp44LocalData.symm {L1 L2 S : Subgroup G} (h : Sp44LocalData L1 L2 S) :
    Sp44LocalData L2 L1 S where
  le_left := h.le_right
  le_right := h.le_left
  card_S := h.card_S
  elem_left := h.elem_right
  card_left := h.card_right
  center_left := h.center_right
  nat_left := h.nat_right
  indec_left := h.indec_right
  idx_left := by rw [bigB_comm]; exact h.idx_right
  elem_right := h.elem_left
  card_right := h.card_left
  center_right := h.center_left
  nat_right := h.nat_left
  indec_right := h.indec_left
  idx_right := by rw [bigB_comm]; exact h.idx_left
  card_inf := by rw [inf_comm]; exact h.card_inf

namespace Sp44

theorem exists_orderOf_eq_three_of_isL2Quot [Finite G] {L : Subgroup G}
    (h : IsL2Quot 2 (oTwoQuot ↥L)) : ∃ x ∈ L, orderOf x = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h60 : Nat.card (oTwoQuot ↥L) = 60 := by
    rw [CFSG.Quasithin.IsL2Quot.card (by norm_num : 1 ≤ 2) h]
    norm_num
  have hcard : Nat.card ↥L = Nat.card (oTwoQuot ↥L) * Nat.card (pCore 2 ↥L) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (pCore 2 ↥L)
  have h3dvd : 3 ∣ Nat.card ↥L := by
    rw [hcard, h60]
    exact (show (3 : ℕ) ∣ 60 by norm_num).trans (dvd_mul_right 60 _)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3dvd
  exact ⟨(x : G), x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩

theorem oTwo_eq [Finite G] {L P : Subgroup G} (hLP : L ≤ P)
    (hPn : P ≤ Subgroup.normalizer (L : Set G)) (hidx : L.relIndex P = 3) :
    pCoreOf 2 P = pCoreOf 2 L := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPL : pCoreOf 2 P ≤ L :=
    CFSG.Quasithin.MS93.pCoreOf_le_of_odd_relIndex hLP (by rw [hidx]; norm_num)
  refine le_antisymm ?_ ?_
  · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hPL
      (hLP.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P)
  · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans hLP)
      (hPn.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)

structure Sp44Side (L P S Q' : Subgroup G) : Prop where
  le : L ≤ P
  norm : P ≤ Subgroup.normalizer (L : Set G)
  charTwo : CharTwo P
  idx : L.relIndex P = 3
  oTwo : pCoreOf 2 P = pCoreOf 2 L
  sylL : IsSylowTwoOf S L
  sylP : IsSylowTwoOf S P
  card_S : Nat.card S = 2 ^ 8
  quot : IsL2Quot 2 (oTwoQuot ↥L)
  elem : IsElemAbelian 2 (pCoreOf 2 L)
  card : Nat.card (pCoreOf 2 L) = 2 ^ 6
  center : Nat.card ↥(centerOf L) = 2 ^ 2
  center_le : centerOf L ≤ pCoreOf 2 L
  nat : NatSec L (centerOf L) (pCoreOf 2 L)
  indec : ⁅pCoreOf 2 L, L⁆ = pCoreOf 2 L
  other_le : Q' ≤ S
  other_elem : IsElemAbelian 2 Q'
  card_inf : Nat.card ↥(pCoreOf 2 L ⊓ Q') = 2 ^ 4
  card_other : Nat.card Q' = 2 ^ 6

end Sp44

open Sp44 in
theorem Sp44LocalData.side_left [Finite G]
    {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S) (h1 : VA5 L1)
    (hD : Sp44LocalData L1 L2 S) :
    Sp44.Sp44Side L1 (L1 ⊔ bigB L1 L2 S) S (pCoreOf 2 L2) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hP : L1 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer (L1 : Set G) :=
    F1.parabolic_le_normalizer hR
  have hO : pCoreOf 2 (L1 ⊔ bigB L1 L2 S) = pCoreOf 2 L1 :=
    oTwo_eq le_sup_left hP hD.idx_left
  have hsylL : IsSylowTwoOf S L1 := by
    have := hR.hyp.h1.sylow
    rwa [inf_eq_left.mpr hD.le_left] at this
  have hsylP : IsSylowTwoOf S (L1 ⊔ bigB L1 L2 S) := by
    refine F7.isSylowTwoOf_of_relIndex (hD.le_left.trans le_sup_left) hsylL.2.1 ?_
    rw [← Subgroup.relIndex_mul_relIndex S L1 (L1 ⊔ bigB L1 L2 S) hD.le_left le_sup_left,
      hD.idx_left]
    intro h2
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2 with h | h
    · exact hsylL.2.2 h
    · norm_num at h
  have hsylR : IsSylowTwoOf S L2 := by
    have := hR.hyp.h2.sylow
    rwa [inf_eq_left.mpr hD.le_right] at this
  have hcenter_le : centerOf L1 ≤ pCoreOf 2 L1 := by
    have h1 : centerOf L1 ≤ L1 ⊔ bigB L1 L2 S := by
      intro x hx
      exact Subgroup.mem_sup_left (Subgroup.mem_inf.mp hx).1
    have h2 : centerOf L1 ≤
        Subgroup.centralizer (pCoreOf 2 (L1 ⊔ bigB L1 L2 S) : Set G) := by
      rw [hO]
      intro x hx
      change x ∈ L1 ⊓ Subgroup.centralizer (L1 : Set G) at hx
      exact Subgroup.centralizer_le (CFSG.LieType.BorelTits.pCoreOf_le 2 L1) hx.2
    have h3 : (L1 ⊔ bigB L1 L2 S) ⊓
        Subgroup.centralizer (pCoreOf 2 (L1 ⊔ bigB L1 L2 S) : Set G) ≤ pCoreOf 2 L1 := by
      simpa [CharTwo, hO] using (F1.parabolic_charTwo hR)
    exact (le_inf h1 h2).trans h3
  exact
    { le := le_sup_left
      norm := hP
      charTwo := F1.parabolic_charTwo hR
      idx := hD.idx_left
      oTwo := hO
      sylL := hsylL
      sylP := hsylP
      card_S := hD.card_S
      quot := h1
      elem := hD.elem_left
      card := hD.card_left
      center := hD.center_left
      center_le := hcenter_le
      nat := hD.nat_left
      indec := hD.indec_left
      other_le := F7.isSylowTwoOf_pCoreOf_le hsylR
      other_elem := hD.elem_right
      card_other := hD.card_right
      card_inf := hD.card_inf }

theorem Sp44LocalData.side_right [Finite G]
    {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2)
    (hD : Sp44LocalData L1 L2 S) :
    Sp44.Sp44Side L2 (L2 ⊔ bigB L1 L2 S) S (pCoreOf 2 L1) := by
  have h := Sp44LocalData.side_left (L1 := L2) (L2 := L1) (S := S) hF.symm h2 hD.symm
  rwa [bigB_comm L1 L2 S] at h

namespace Sp44

theorem Sp44Side.relIndex_center [Finite G] {L P S Q' : Subgroup G} (h : Sp44Side L P S Q') :
    (centerOf L).relIndex (pCoreOf 2 L) = 16 := by
  have hcard := Subgroup.relIndex_mul_card (H := centerOf L) (K := pCoreOf 2 L)
  rw [inf_eq_left.mpr h.center_le, h.card, h.center] at hcard
  norm_num at hcard ⊢
  omega

theorem Sp44Side.sup_eq {L P S Q' : Subgroup G} [Finite G] (h : Sp44Side L P S Q') :
    pCoreOf 2 L ⊔ Q' = S := by
  have hQS : pCoreOf 2 L ≤ S := F7.isSylowTwoOf_pCoreOf_le h.sylL
  have hsup_le : pCoreOf 2 L ⊔ Q' ≤ S := sup_le hQS h.other_le
  have hQ'N : Q' ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    h.other_le.trans (h.sylL.1.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L))
  have hformula :=
    CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
      (A := pCoreOf 2 L) (B := Q') hQ'N
  rw [h.card_inf, h.card_other, h.card] at hformula
  have hcard : Nat.card ↥(pCoreOf 2 L ⊔ Q') = 2 ^ 8 := by
    norm_num at hformula
    omega
  exact Subgroup.eq_of_le_of_card_ge hsup_le (by rw [h.card_S, hcard])

end Sp44

theorem Sp44LocalData.parabolic_inf [Finite G]
    {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S) (hD : Sp44LocalData L1 L2 S) :
    (L1 ⊔ bigB L1 L2 S) ⊓ (L2 ⊔ bigB L1 L2 S) = bigB L1 L2 S := by
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  exact F1.parabolic_inf_parabolic hR

theorem Sp44LocalData.bigB_eq_parabolic_inf [Finite G]
    {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S) (hD : Sp44LocalData L1 L2 S) :
    bigB L1 L2 S = (L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.normalizer (S : Set G) := by
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have h := F1.bigB_eq_parabolic_inf hR
  rw [inf_eq_left.mpr hD.le_left] at h
  exact h

end CFSG.Quasithin.F112R.St84
