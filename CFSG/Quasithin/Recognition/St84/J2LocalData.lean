module

public import CFSG.Quasithin.Recognition.GoldschmidtF112RY9
public import CFSG.Quasithin.EmptyFaithful.SzF53A2
public import CFSG.Quasithin.Recognition.F112J2Act
public import CFSG.GH74.QTGen4.DSGen4.Leaf.SylowS
public import CFSG.Quasithin.Recognition.GoldschmidtF112TitsBorel
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma1547Two
public import CFSG.GH74.QTGen4.DSGen4.Leaf.FaithfulA5
public import CFSG.Quasithin.EmptyFaithful.S1421QA17Setup

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G]

structure J2LocalData (L1 L2 S : Subgroup G) : Prop where
  bigB_le_right : bigB L2 L1 S ≤ L2
  q8d8_right : IsQ8D8 ↥(pCoreOf 2 L2)
  split_right : ∃ K : Subgroup G, K ≤ L2 ∧ K ⊓ pCoreOf 2 L2 = ⊥ ∧ Nat.card K = 60
  card_left : Nat.card (pCoreOf 2 L1) = 2 ^ 6

structure AutJ2LocalData (L1 L2 S : Subgroup G) : Prop where
  card_S : Nat.card S = 2 ^ 8
  perm5_right : Nonempty (oTwoQuot ↥(L2 ⊔ S) ≃* Equiv.Perm (Fin 5))
  q8d8_right : IsQ8D8 ↥(pCoreOf 2 L2)
  split_right : ∃ K : Subgroup G, K ≤ L2 ∧ K ⊓ pCoreOf 2 L2 = ⊥ ∧ Nat.card K = 60
  twist_right : ∃ u ∈ S, u ∉ L2 ∧ u ^ 2 = 1 ∧ ∃ v ∈ pCoreOf 2 L2, v ^ 2 = 1 ∧
    v ∉ Subgroup.centralizer (pCoreOf 2 L2 : Set G) ∧ u * v = v * u
  card_left : Nat.card (pCoreOf 2 L1) = 2 ^ 6

theorem hyp111R_of_vs3_va5 [Finite G] {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2) : Hyp111R L1 L2 S := by
  obtain ⟨e2⟩ := h2
  obtain ⟨e⟩ := F112J2.nonempty_psl_four_equiv_alt5
  exact hyp111R_of_perm_three_alt_five hF.1 h1 ⟨e2.trans e⟩

theorem parabolic_inf_eq_bigB_of_vs3_va5 [Finite G] {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2) :
    (L2 ⊔ bigB L2 L1 S) ⊓ (L1 ⊔ bigB L2 L1 S) = bigB L2 L1 S :=
  F1.parabolic_inf_parabolic (hyp111R_of_vs3_va5 hF h1 h2).symm

theorem J2LocalData.sup_eq {L1 L2 S : Subgroup G} (hD : J2LocalData L1 L2 S) :
    L2 ⊔ bigB L2 L1 S = L2 :=
  sup_eq_left.mpr hD.bigB_le_right

theorem card_eq_1920_of_va5_of_isQ8D8 {L : Subgroup G} (h2 : VA5 L)
    (hQ : IsQ8D8 ↥(pCoreOf 2 L)) : Nat.card L = 1920 := by
  have hcard := CFSG.Quasithin.S1421QA17.card_eq_card_oTwoQuot_mul L
  have hquot : Nat.card (oTwoQuot ↥L) = 60 := by
    rw [IsL2Quot.card (by norm_num) h2]
    norm_num
  have hcard' : Nat.card L =
      Nat.card (oTwoQuot ↥L) * Nat.card (pCoreOf 2 L) := by
    simpa only [OTwoQuot, oTwoQuot] using hcard
  rw [hquot, hQ.1] at hcard'
  omega

theorem J2LocalData.card_right {L1 L2 S : Subgroup G}
    (h2 : VA5 L2) (hD : J2LocalData L1 L2 S) : Nat.card L2 = 1920 :=
  card_eq_1920_of_va5_of_isQ8D8 h2 hD.q8d8_right

private theorem J2LocalData.isSylowTwoOf_right [Finite G] {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2) (hD : J2LocalData L1 L2 S) :
    IsSylowTwoOf S L2 := by
  have h := (CFSG.GH74.QTGen4.DSGen4.leafSylowS
    (hyp111R_of_vs3_va5 hF h1 h2).symm).2.1
  rwa [hD.sup_eq] at h

theorem J2LocalData.S_le_right [Finite G] {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2) (hD : J2LocalData L1 L2 S) :
    S ≤ L2 :=
  (J2LocalData.isSylowTwoOf_right hF h1 h2 hD).1

theorem J2LocalData.card_S [Finite G] {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2) (hD : J2LocalData L1 L2 S) :
    Nat.card S = 2 ^ 7 := by
  rw [(J2LocalData.isSylowTwoOf_right hF h1 h2 hD).card_eq]
  exact CFSG.Quasithin.S1421QA17.twoPart_eq_of_card (n := 7) (m := 15) (by norm_num)
    (by rw [J2LocalData.card_right h2 hD]; norm_num)

theorem J2LocalData.S_le_left [Finite G] {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2) (hD : J2LocalData L1 L2 S) :
    S ≤ L1 := by
  have hcardL1 : Nat.card L1 = 2 ^ 7 * 3 := by
    have hcard := CFSG.Quasithin.S1421QA17.card_eq_card_oTwoQuot_mul L1
    have hquot : Nat.card (oTwoQuot ↥L1) = 6 := by
      obtain ⟨e⟩ := h1
      rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
      norm_num
    have hcard' : Nat.card L1 =
        Nat.card (oTwoQuot ↥L1) * Nat.card (pCoreOf 2 L1) := by
      simpa only [OTwoQuot, oTwoQuot] using hcard
    rw [hquot, hD.card_left] at hcard'
    omega
  have hcardInf : Nat.card ↥(S ⊓ L1) = 2 ^ 7 := by
    rw [hF.1.h1.sylow.card_eq]
    exact CFSG.Quasithin.S1421QA17.twoPart_eq_of_card (n := 7) (m := 3) (by norm_num) hcardL1
  have hEq : S ⊓ L1 = S := by
    refine Subgroup.eq_of_le_of_card_ge inf_le_left ?_
    rw [J2LocalData.card_S hF h1 h2 hD, hcardInf]
  exact hEq.symm.le.trans inf_le_right

theorem sup_bigB_eq_sup_of_vs3 [Finite G] {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) : L2 ⊔ bigB L2 L1 S = L2 ⊔ S := by
  have hb : borelOf L1 S = S ⊓ L1 :=
    CFSG.Quasithin.F112TitsSlice.borelOf_eq_vs3 hF.1.h1 h1
  apply le_antisymm
  · refine sup_le le_sup_left ?_
    rw [bigB, hb]
    exact sup_le (sup_le ((F1.borelOf_le L2 S).trans le_sup_left)
      (inf_le_left.trans le_sup_right)) le_sup_right
  · refine sup_le le_sup_left ?_
    exact (le_sup_right : S ≤ (borelOf L2 S ⊔ borelOf L1 S) ⊔ S).trans le_sup_right

theorem AutJ2LocalData.card_right {L1 L2 S : Subgroup G}
    (h2 : VA5 L2) (hD : AutJ2LocalData L1 L2 S) : Nat.card L2 = 1920 :=
  card_eq_1920_of_va5_of_isQ8D8 h2 hD.q8d8_right

theorem AutJ2LocalData.card_parabolic_right [Finite G] {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2)
    (hD : AutJ2LocalData L1 L2 S) : Nat.card ↥(L2 ⊔ bigB L2 L1 S) = 3840 := by
  rw [sup_bigB_eq_sup_of_vs3 hF h1]
  have hSinf : Nat.card ↥(S ⊓ L2) = 2 ^ 7 := by
    rw [hF.1.h2.sylow.card_eq]
    exact CFSG.Quasithin.S1421QA17.twoPart_eq_of_card (n := 7) (m := 15) (by norm_num)
      (by rw [AutJ2LocalData.card_right h2 hD]; norm_num)
  have hprod := CFSG.Quasithin.EmptyFaithfulMultiple.L1547.card_sup_mul_card_inf
    (H := S) (K := L2) hF.1.h2.normalizes
  rw [sup_comm, hSinf, hD.card_S, AutJ2LocalData.card_right h2 hD] at hprod
  exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 2 ^ 7) (by
    rw [hprod]; norm_num)

theorem AutJ2LocalData.pCoreOf_parabolic_right [Finite G] {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2)
    (hD : AutJ2LocalData L1 L2 S) :
    pCoreOf 2 (L2 ⊔ bigB L2 L1 S) = pCoreOf 2 L2 := by
  rw [sup_bigB_eq_sup_of_vs3 hF h1]
  have hquot : Nat.card (oTwoQuot ↥(L2 ⊔ S)) = 120 := by
    obtain ⟨e⟩ := hD.perm5_right
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
    norm_num
  have hcardP : Nat.card ↥(L2 ⊔ S) = 3840 := by
    rw [← sup_bigB_eq_sup_of_vs3 hF h1]
    exact AutJ2LocalData.card_parabolic_right hF h1 h2 hD
  have hcoreP : Nat.card (pCoreOf 2 (L2 ⊔ S)) = 32 := by
    have hcard := CFSG.Quasithin.S1421QA17.card_eq_card_oTwoQuot_mul (L2 ⊔ S)
    have hcard' : Nat.card ↥(L2 ⊔ S) =
        Nat.card (oTwoQuot ↥(L2 ⊔ S)) * Nat.card (pCoreOf 2 (L2 ⊔ S)) := by
      simpa only [OTwoQuot, oTwoQuot] using hcard
    rw [hquot, hcardP] at hcard'
    omega
  have hnorm : L2 ⊔ S ≤ Subgroup.normalizer (L2 : Set G) :=
    sup_le Subgroup.le_normalizer hF.1.h2.normalizes
  have hle : pCoreOf 2 L2 ≤ pCoreOf 2 (L2 ⊔ S) :=
    CFSG.GH74.QTGen4.DSGen4.FaithfulA5.pCoreOf_le_of_normalizes le_sup_left hnorm
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcoreP, hD.q8d8_right.1])).symm

end CFSG.Quasithin.F112R.St84
