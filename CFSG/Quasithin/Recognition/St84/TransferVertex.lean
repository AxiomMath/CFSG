module

public import CFSG.Quasithin.Recognition.St84.TransferNormality
public import CFSG.Quasithin.Recognition.St84.TransferInner
public import CFSG.Quasithin.Recognition.St84.AppTreeE5
public import CFSG.GroupTheory.FixedCosetCommutator
public import CFSG.GH74.QTGen4.DSGen4.Defs
import CFSG.Quasithin.Background.F1VertexCore
import CFSG.Quasithin.EmptyFaithful.S1421QNSSurv
import CFSG.Quasithin.Recognition.St84.Gen.OTwoPrimeL2
import CFSG.Quasithin.Recognition.St84.Gen.TreeSLB
public import CFSG.GH74.QTGen4.DSGen4.Statements
public import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped Pointwise commutatorElement

variable {G : Type*} [Group G]

theorem pCoreOf_oTwoPrime (Y : Subgroup G) [Finite ↥Y] :
    pCoreOf 2 (oTwoPrime Y) = pCoreOf 2 Y := by
  refine le_antisymm ?_ ?_
  · have hle : pCoreOf 2 (oTwoPrime Y) ≤ Y :=
      (CFSG.LieType.BorelTits.pCoreOf_le 2 (oTwoPrime Y)).trans (oTwoPrime_le Y)
    haveI hchar : (CFSG.pCore 2 ↥(oTwoPrime Y)).Characteristic :=
      CFSG.LieType.BorelTits.pCore_characteristic 2
    have hnorm : Y ≤ Subgroup.normalizer (pCoreOf 2 (oTwoPrime Y) : Set G) :=
      (le_normalizer_oTwoPrime Y).trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
          (H := oTwoPrime Y) (K := CFSG.pCore 2 ↥(oTwoPrime Y)))
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hle hnorm
      (pCore_isPGroup (G := ↥(oTwoPrime Y)) (p := 2) |>.map (oTwoPrime Y).subtype)
  · refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ ?_ ?_
    · exact le_oTwoPrime_of_isPGroup
        (pCore_isPGroup (G := ↥Y) (p := 2) |>.map Y.subtype)
        (CFSG.LieType.BorelTits.pCoreOf_le 2 Y)
    · exact (oTwoPrime_le Y).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y)
    · exact pCore_isPGroup (G := ↥Y) (p := 2) |>.map Y.subtype

private theorem not_le_pCoreOf_of_mem_orderOf_eq_three {A E : Subgroup G} {a : G}
    (ha : a ∈ A) (ha3 : orderOf a = 3) : ¬ A ≤ pCoreOf 2 E := by
  intro hle
  have hp : IsPGroup 2 (pCoreOf 2 E) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥E)).map E.subtype
  obtain ⟨n, hn⟩ := hp.exists_orderOf_dvd_pow ⟨a, hle ha⟩
  rw [Subgroup.orderOf_mk, ha3] at hn
  have h3 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hn
  norm_num at h3

theorem oTwoPrime_eq_sup_pCoreOf_of_isL2Quot_of_two_le {A E : Subgroup G} [Finite ↥E] {n : ℕ}
    (hn : 2 ≤ n) (hA : A ≤ oTwoPrime E) (hAnorm : E ≤ Subgroup.normalizer (A : Set G))
    (hAQ : ¬ A ≤ pCoreOf 2 E) (hq : IsL2Quot n (oTwoQuot ↥(oTwoPrime E))) :
    oTwoPrime E = A ⊔ pCoreOf 2 E := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let L := oTwoPrime E
  let Q := pCoreOf 2 E
  have hAL : A ≤ L := hA
  have hQL : Q ≤ L := le_oTwoPrime_of_isPGroup
    (pCore_isPGroup (G := ↥E) (p := 2) |>.map E.subtype)
    (CFSG.LieType.BorelTits.pCoreOf_le 2 E)
  have hAnormal : (A.subgroupOf L).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer ((oTwoPrime_le E).trans hAnorm)
  have hQeq : Q.subgroupOf L = CFSG.pCore 2 ↥L := by
    have hQ : Q = pCoreOf 2 L := (pCoreOf_oTwoPrime E).symm
    rw [hQ, CFSG.openPCoreOf_subgroupOf]
  have hQnormal : (Q.subgroupOf L).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      ((oTwoPrime_le E).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 E))
  haveI : (Q.subgroupOf L).Normal := hQnormal
  let π : ↥L →* (↥L ⧸ Q.subgroupOf L) := QuotientGroup.mk' (Q.subgroupOf L)
  let Abar : Subgroup (↥L ⧸ Q.subgroupOf L) := (A.subgroupOf L).map π
  have hAbarNormal : Abar.Normal :=
    hAnormal.map π (QuotientGroup.mk'_surjective (N := Q.subgroupOf L))
  haveI : Abar.Normal := hAbarNormal
  haveI : IsSimpleGroup (↥L ⧸ Q.subgroupOf L) := by
    have e : (↥L ⧸ Q.subgroupOf L) ≃* oTwoQuot ↥L :=
      QuotientGroup.quotientMulEquivOfEq hQeq
    exact e.isSimpleGroup_congr.mpr
      (CFSG.Quasithin.S1421NS.isSimpleGroup_of_isL2Quot hn hq)
  have hAbarNe : Abar ≠ ⊥ := by
    intro hbar
    apply hAQ
    intro a ha
    have haL : a ∈ L := hAL ha
    have hmem : π ⟨a, haL⟩ ∈ Abar :=
      Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr ha)
    rw [hbar, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hmem)
  have hAbarTop : Abar = ⊤ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top Abar with h | h
    · exact absurd h hAbarNe
    · exact h
  have htopA : (A.subgroupOf L) ⊔ (Q.subgroupOf L) = ⊤ := by
    have hmap : ((A.subgroupOf L) ⊔ (Q.subgroupOf L)).map π = ⊤ := by
      rw [Subgroup.map_sup]
      change Abar ⊔ (Q.subgroupOf L).map π = ⊤
      have hmapQ : (Q.subgroupOf L).map π = ⊥ := by
        refine (Subgroup.map_eq_bot_iff (Q.subgroupOf L) (f := π)).mpr ?_
        intro y hy
        rw [QuotientGroup.ker_mk']
        exact hy
      rw [hAbarTop, hmapQ, sup_bot_eq]
    have hcomap := Subgroup.comap_map_eq_self (f := π)
      (H := (A.subgroupOf L) ⊔ (Q.subgroupOf L)) (by
        rw [QuotientGroup.ker_mk']
        exact le_sup_right)
    rw [hmap] at hcomap
    simpa using hcomap.symm
  have hsup : A ⊔ Q = L := by
    have h1 : (A ⊔ Q).subgroupOf L = ⊤ := by
      rw [Subgroup.subgroupOf_sup hAL hQL]
      exact htopA
    exact le_antisymm
      (sup_le hAL hQL)
      ((Subgroup.subgroupOf_eq_top (H := A ⊔ Q) (K := L)).mp h1)
  exact hsup.symm

theorem oTwoPrime_eq_sup_pCoreOf_of_isL2Quot {A E : Subgroup G} [Finite ↥E]
    (hA : A ≤ oTwoPrime E) (hAnorm : E ≤ Subgroup.normalizer (A : Set G))
    (h3 : ∃ a ∈ A, orderOf a = 3)
    (hq : IsL2Quot 2 (oTwoQuot ↥(oTwoPrime E))) :
    oTwoPrime E = A ⊔ pCoreOf 2 E := by
  obtain ⟨a, ha, ha3⟩ := h3
  exact oTwoPrime_eq_sup_pCoreOf_of_isL2Quot_of_two_le le_rfl hA hAnorm
    (not_le_pCoreOf_of_mem_orderOf_eq_three ha ha3) hq

end CFSG.Quasithin

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.GH74.QTGen4.DSGen4
open scoped Pointwise commutatorElement

variable {H : Type} [Group H] [Finite H]

theorem mem_normalizer_oTwoPrime {G : Type*} [Group G] {X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    g ∈ Subgroup.normalizer (oTwoPrime X : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hg ⊢
  change conjSub g (oTwoPrime X) = oTwoPrime X
  rw [conjSub_oTwoPrime]
  rw [show conjSub g X = X from hg]

theorem f112saP2'_eq_P1'_swap (L1 L2 S : Subgroup H) :
    f112saP2' L1 L2 S = f112saP1' L2 L1 S := by
  simp only [f112saP1', f112saP2', f112saX1, f112saX2, bigB_comm]

theorem f112saP1'_eq_P2'_swap (L1 L2 S : Subgroup H) :
    f112saP1' L1 L2 S = f112saP2' L2 L1 S :=
  (f112saP2'_eq_P1'_swap L2 L1 S).symm

theorem f112sa_T_le_oTwoPrime_P1'_of_hyp111R {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (hR : Hyp111R L1 L2 S) :
    S ⊓ f112saK L1 L2 S ≤ oTwoPrime (f112saP1' L1 L2 S) :=
  le_oTwoPrime_of_isPGroup (f112sa_T_sylow_P1'_of_hyp111R hF hR).2.1
    (f112sa_T_sylow_P1'_of_hyp111R hF hR).1

theorem f112sa_T_le_oTwoPrime_P1' {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) :
    S ⊓ f112saK L1 L2 S ≤ oTwoPrime (f112saP1' L1 L2 S) :=
  f112sa_T_le_oTwoPrime_P1'_of_hyp111R hF (Hyp111R.of_hyp111 rankOneListedFacts hF.1)

theorem f112sa_T_sylow_oTwoPrime_P1'_of_hyp111R {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (hR : Hyp111R L1 L2 S) :
    IsSylowTwoOf (S ⊓ f112saK L1 L2 S) (oTwoPrime (f112saP1' L1 L2 S)) :=
  F7.isSylowTwoOf_mono_right (f112sa_T_sylow_P1'_of_hyp111R hF hR)
    (f112sa_T_le_oTwoPrime_P1'_of_hyp111R hF hR) (oTwoPrime_le (f112saP1' L1 L2 S))

theorem f112sa_T_sylow_oTwoPrime_P1' {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) :
    IsSylowTwoOf (S ⊓ f112saK L1 L2 S) (oTwoPrime (f112saP1' L1 L2 S)) :=
  f112sa_T_sylow_oTwoPrime_P1'_of_hyp111R hF
    (Hyp111R.of_hyp111 rankOneListedFacts hF.1)

theorem f112sa_T_le_oTwoPrime_P2'_of_hyp111R {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (hR : Hyp111R L1 L2 S) :
    S ⊓ f112saK L1 L2 S ≤ oTwoPrime (f112saP2' L1 L2 S) := by
  rw [f112saP2'_eq_P1'_swap, f112saK_comm]
  exact f112sa_T_le_oTwoPrime_P1'_of_hyp111R hF.symm hR.symm

theorem f112sa_T_le_oTwoPrime_P2' {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) :
    S ⊓ f112saK L1 L2 S ≤ oTwoPrime (f112saP2' L1 L2 S) :=
  f112sa_T_le_oTwoPrime_P2'_of_hyp111R hF (Hyp111R.of_hyp111 rankOneListedFacts hF.1)

theorem f112sa_T_sylow_oTwoPrime_P2'_of_hyp111R {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (hR : Hyp111R L1 L2 S) :
    IsSylowTwoOf (S ⊓ f112saK L1 L2 S) (oTwoPrime (f112saP2' L1 L2 S)) := by
  rw [f112saP2'_eq_P1'_swap, f112saK_comm]
  exact f112sa_T_sylow_oTwoPrime_P1'_of_hyp111R hF.symm hR.symm

theorem f112sa_T_sylow_oTwoPrime_P2' {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) :
    IsSylowTwoOf (S ⊓ f112saK L1 L2 S) (oTwoPrime (f112saP2' L1 L2 S)) :=
  f112sa_T_sylow_oTwoPrime_P2'_of_hyp111R hF
    (Hyp111R.of_hyp111 rankOneListedFacts hF.1)

theorem f112sa_oTwoRes_le_oTwoPrime_P1'_of_isL2Quot {L1 L2 S : Subgroup H} {m : ℕ}
    (hm : 2 ≤ m) (h1 : IsL2Quot m (oTwoQuot ↥L1)) :
    oTwoRes L1 ≤ oTwoPrime (f112saP1' L1 L2 S) :=
  le_oTwoPrime_of_isL2Quot_of_two_le hm le_sup_left (f112sl_oTwoRes_quot hm h1)

theorem f112sa_oTwoRes_le_oTwoPrime_P1' {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) :
    oTwoRes L1 ≤ oTwoPrime (f112saP1' L1 L2 S) :=
  f112sa_oTwoRes_le_oTwoPrime_P1'_of_isL2Quot (m := 2) le_rfl h1

theorem f112sa_oTwoRes_le_oTwoPrime_P2'_of_isL2Quot {L1 L2 S : Subgroup H} {n : ℕ}
    (hn : 2 ≤ n) (h2 : IsL2Quot n (oTwoQuot ↥L2)) :
    oTwoRes L2 ≤ oTwoPrime (f112saP2' L1 L2 S) := by
  rw [f112saP2'_eq_P1'_swap]
  exact f112sa_oTwoRes_le_oTwoPrime_P1'_of_isL2Quot hn h2

theorem f112sa_oTwoRes_le_oTwoPrime_P2' {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h2 : VA5 L2) :
    oTwoRes L2 ≤ oTwoPrime (f112saP2' L1 L2 S) :=
  f112sa_oTwoRes_le_oTwoPrime_P2'_of_isL2Quot (n := 2) le_rfl h2

theorem f112sa_oTwoPrime_eq_oTwoRes_sup_pCoreOf_P1'_of_isL2Quot {L1 L2 S : Subgroup H}
    {m k : ℕ} (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (hk : 2 ≤ k) (hq : IsL2Quot k (oTwoQuot ↥(oTwoPrime (f112saP1' L1 L2 S)))) :
    oTwoPrime (f112saP1' L1 L2 S) = oTwoRes L1 ⊔ pCoreOf 2 (f112saP1' L1 L2 S) := by
  let E := f112saP1' L1 L2 S
  let A := oTwoRes L1
  have hAnorm : E ≤ Subgroup.normalizer (A : Set H) := by
    change f112saP1' L1 L2 S ≤ Subgroup.normalizer (oTwoRes L1 : Set H)
    rw [f112saP1']
    exact sup_le Subgroup.le_normalizer
      ((f112sa_X2_le_bigB L1 L2 S).trans (f112sa_bigB_le_normalizer_oTwoRes_left hF))
  have hAQ : ¬ A ≤ pCoreOf 2 E := by
    intro hle
    have hA2 : IsPGroup 2 A :=
      ((CFSG.pCore_isPGroup (p := 2) (G := ↥E)).map E.subtype).to_le hle
    have htop : pCoreOf 2 A = A := by
      refine le_antisymm (CFSG.LieType.BorelTits.pCoreOf_le 2 A) ?_
      exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_rfl
        Subgroup.le_normalizer hA2
    have hpcore : CFSG.pCore 2 ↥A = ⊤ := by
      rw [← CFSG.openPCoreOf_subgroupOf 2 A, htop, Subgroup.subgroupOf_self]
    have hqA : IsL2Quot m (oTwoQuot ↥A) := f112sl_oTwoRes_quot hm h1
    have hcard := IsL2Quot.card (by omega : 1 ≤ m) hqA
    have hcard1 : Nat.card (oTwoQuot ↥A) = 1 := by
      change Nat.card (↥A ⧸ CFSG.pCore 2 ↥A) = 1
      rw [hpcore]
      exact Nat.card_eq_one_iff_unique.mpr
        ⟨QuotientGroup.subsingleton_quotient_top, ⟨1⟩⟩
    have hge := two_pow_mul_four_pow_sub_one_ge m hm
    omega
  exact oTwoPrime_eq_sup_pCoreOf_of_isL2Quot_of_two_le hk
    (f112sa_oTwoRes_le_oTwoPrime_P1'_of_isL2Quot hm h1) hAnorm hAQ hq

theorem f112sa_oTwoPrime_eq_oTwoRes_sup_pCoreOf_P1'
    {L1 L2 S : Subgroup H} (hF : F112HypW L1 L2 S) (h1 : VA5 L1)
    (hq : IsL2Quot 2 (oTwoQuot ↥(oTwoPrime (f112saP1' L1 L2 S)))) :
    oTwoPrime (f112saP1' L1 L2 S) =
      oTwoRes L1 ⊔ pCoreOf 2 (f112saP1' L1 L2 S) :=
  f112sa_oTwoPrime_eq_oTwoRes_sup_pCoreOf_P1'_of_isL2Quot hF le_rfl h1 le_rfl hq

theorem f112sa_oTwoPrime_eq_oTwoRes_sup_pCoreOf_P2'_of_isL2Quot {L1 L2 S : Subgroup H}
    {n k : ℕ} (hF : F112HypW L1 L2 S) (hn : 2 ≤ n) (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (hk : 2 ≤ k) (hq : IsL2Quot k (oTwoQuot ↥(oTwoPrime (f112saP2' L1 L2 S)))) :
    oTwoPrime (f112saP2' L1 L2 S) = oTwoRes L2 ⊔ pCoreOf 2 (f112saP2' L1 L2 S) := by
  rw [f112saP2'_eq_P1'_swap] at hq ⊢
  exact f112sa_oTwoPrime_eq_oTwoRes_sup_pCoreOf_P1'_of_isL2Quot hF.symm hn h2 hk hq

theorem f112sa_oTwoPrime_eq_oTwoRes_sup_pCoreOf_P2'
    {L1 L2 S : Subgroup H} (hF : F112HypW L1 L2 S) (h2 : VA5 L2)
    (hq : IsL2Quot 2 (oTwoQuot ↥(oTwoPrime (f112saP2' L1 L2 S)))) :
    oTwoPrime (f112saP2' L1 L2 S) =
      oTwoRes L2 ⊔ pCoreOf 2 (f112saP2' L1 L2 S) :=
  f112sa_oTwoPrime_eq_oTwoRes_sup_pCoreOf_P2'_of_isL2Quot hF le_rfl h2 le_rfl hq

theorem f112sa_commutator_mem_pCoreOf_of_mem_oTwoPrime_P1'_of_isL2Quot
    {L1 L2 S : Subgroup H} {m k : ℕ} (hF : F112HypW L1 L2 S) (hm : 2 ≤ m)
    (h1 : IsL2Quot m (oTwoQuot ↥L1)) (hk : 2 ≤ k)
    (hq : IsL2Quot k (oTwoQuot ↥(oTwoPrime (f112saP1' L1 L2 S))))
    {c : H} (hcS : c ∈ S) (hcL : ∀ l ∈ L1, ⁅c, l⁆ ∈ pCoreOf 2 L1) :
    ∀ l ∈ oTwoPrime (f112saP1' L1 L2 S),
      ⁅c, l⁆ ∈ pCoreOf 2 (f112saP1' L1 L2 S) := by
  classical
  let E := f112saP1' L1 L2 S
  let A := oTwoRes L1
  let L := oTwoPrime E
  let Q := pCoreOf 2 E
  have hAE : A ≤ E := le_sup_left
  have hALE : A ≤ L := f112sa_oTwoRes_le_oTwoPrime_P1'_of_isL2Quot hm h1
  have hQleL : Q ≤ L := le_oTwoPrime_of_isPGroup
    (pCore_isPGroup (G := ↥E) (p := 2) |>.map E.subtype)
    (CFSG.LieType.BorelTits.pCoreOf_le 2 E)
  have hL : L = A ⊔ Q :=
    f112sa_oTwoPrime_eq_oTwoRes_sup_pCoreOf_P1'_of_isL2Quot hF hm h1 hk hq
  have hE_N_A : E ≤ Subgroup.normalizer (A : Set H) := by
    change f112saP1' L1 L2 S ≤ Subgroup.normalizer (oTwoRes L1 : Set H)
    rw [f112saP1']
    exact sup_le Subgroup.le_normalizer
      ((f112sa_X2_le_bigB L1 L2 S).trans (f112sa_bigB_le_normalizer_oTwoRes_left hF))
  have hQN_A : Q ≤ Subgroup.normalizer (A : Set H) :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 E).trans hE_N_A
  have hE_N_L1 : E ≤ Subgroup.normalizer (L1 : Set H) := by
    change f112saP1' L1 L2 S ≤ Subgroup.normalizer (L1 : Set H)
    rw [f112saP1']
    exact sup_le ((oTwoRes_le L1).trans Subgroup.le_normalizer)
      ((f112sa_X2_le_bigB L1 L2 S).trans (bigB_le_normalizer_of_hyp111 hF.1))
  have hE_N_pcore : E ≤ Subgroup.normalizer (pCoreOf 2 L1 : Set H) :=
    hE_N_L1.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L1)
  have hDE_le_Q : pCoreOf 2 L1 ⊓ E ≤ Q := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_ ?_
    · refine (le_inf hE_N_pcore Subgroup.le_normalizer).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    · exact (pCore_isPGroup (G := ↥L1) (p := 2) |>.map L1.subtype).to_le inf_le_left
  have hcP : c ∈ f112P1 L1 L2 S :=
    (le_sup_right : bigB L1 L2 S ≤ f112P1 L1 L2 S)
      ((le_sup_right : S ≤ bigB L1 L2 S) hcS)
  have hcE : c ∈ Subgroup.normalizer (E : Set H) := f112sa_P1_le_normalizer_P1' hF hcP
  have hcQ : c ∈ Subgroup.normalizer (Q : Set H) :=
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 E) hcE
  intro l hl
  have hlL : l ∈ L := hl
  obtain ⟨a, ha, q, hq_mem, rfl⟩ :=
    (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes hQN_A).mp (hL ▸ hlL)
  have haL1 : a ∈ L1 := oTwoRes_le L1 ha
  have hca : ⁅c, a⁆ ∈ Q := by
    have hcaE : ⁅c, a⁆ ∈ E := by
      have hconj : c * a * c⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hcE a).mp (hAE ha)
      rw [commutatorElement_def]
      exact E.mul_mem hconj (E.inv_mem (hAE ha))
    exact hDE_le_Q ⟨hcL a haL1, hcaE⟩
  have hcq : ⁅c, q⁆ ∈ Q := by
    have hconj : c * q * c⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hcQ q).mp hq_mem
    rw [commutatorElement_def]
    exact Q.mul_mem hconj (Q.inv_mem hq_mem)
  have haQ : a * ⁅c, q⁆ * a⁻¹ ∈ Q := by
    have haN : a ∈ Subgroup.normalizer (Q : Set H) :=
      ((oTwoPrime_le E).trans
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 E)) (hALE ha)
    exact (Subgroup.mem_normalizer_iff.mp haN ⁅c, q⁆).mp hcq
  rw [commutatorElement_mul_right_eq_mul_conj]
  have e : ⁅c, a⁆ * a * ⁅c, q⁆ * a⁻¹ = ⁅c, a⁆ * (a * ⁅c, q⁆ * a⁻¹) := by group
  rw [e]
  exact Q.mul_mem hca haQ

theorem f112sa_commutator_mem_pCoreOf_of_mem_oTwoPrime_P2'_of_isL2Quot
    {L1 L2 S : Subgroup H} {n k : ℕ} (hF : F112HypW L1 L2 S) (hn : 2 ≤ n)
    (h2 : IsL2Quot n (oTwoQuot ↥L2)) (hk : 2 ≤ k)
    (hq : IsL2Quot k (oTwoQuot ↥(oTwoPrime (f112saP2' L1 L2 S))))
    {c : H} (hcS : c ∈ S) (hcL : ∀ l ∈ L2, ⁅c, l⁆ ∈ pCoreOf 2 L2) :
    ∀ l ∈ oTwoPrime (f112saP2' L1 L2 S),
      ⁅c, l⁆ ∈ pCoreOf 2 (f112saP2' L1 L2 S) := by
  rw [f112saP2'_eq_P1'_swap] at hq ⊢
  exact f112sa_commutator_mem_pCoreOf_of_mem_oTwoPrime_P1'_of_isL2Quot hF.symm hn h2 hk hq hcS hcL

theorem f112sa_commutator_mem_pCoreOf_of_mem_oTwoPrime_P2'
    {L1 L2 S : Subgroup H} (hF : F112Hyp L1 L2 S) (h2 : VA5 L2)
    (hq : IsL2Quot 2 (oTwoQuot ↥(oTwoPrime (f112saP2' L1 L2 S))))
    {c : H} (hcS : c ∈ S) (hcL : ∀ l ∈ L2, ⁅c, l⁆ ∈ pCoreOf 2 L2) :
    ∀ l ∈ oTwoPrime (f112saP2' L1 L2 S),
      ⁅c, l⁆ ∈ pCoreOf 2 (f112saP2' L1 L2 S) :=
  f112sa_commutator_mem_pCoreOf_of_mem_oTwoPrime_P2'_of_isL2Quot hF.toW le_rfl h2 le_rfl hq hcS hcL

theorem f112saP1_eq_of_S_le_K {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (hS : S ≤ f112saK L1 L2 S) :
    f112P1 L1 L2 S = f112saP1' L1 L2 S := by
  have hK : f112saK L1 L2 S ≤ f112saP1' L1 L2 S := f112saK_le_P1' L1 L2 S
  have hB : bigB L1 L2 S ≤ f112saP1' L1 L2 S := by
    rw [f112sa_bigB_eq_S_sup_K hF]
    exact sup_le (hS.trans hK) hK
  rw [f112sa_P1_eq_P1'_sup_bigB hF]
  exact sup_eq_left.mpr hB

theorem f112saP2_eq_of_S_le_K {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (hS : S ≤ f112saK L1 L2 S) :
    f112P2 L1 L2 S = f112saP2' L1 L2 S := by
  have hK : f112saK L1 L2 S ≤ f112saP2' L1 L2 S := f112saK_le_P2' L1 L2 S
  have hB : bigB L1 L2 S ≤ f112saP2' L1 L2 S := by
    rw [f112sa_bigB_eq_S_sup_K hF]
    exact sup_le (hS.trans hK) hK
  rw [f112sa_P2_eq_P2'_sup_bigB hF]
  exact sup_eq_left.mpr hB

theorem f112sa_S_le_L1_and_eq_oTwoPrime_of_S_le_K_of_isL2Quot {L1 L2 S : Subgroup H} {m k : ℕ}
    (hF : F112HypW L1 L2 S) (hR : Hyp111R L1 L2 S) (hm : 2 ≤ m) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (hS : S ≤ f112saK L1 L2 S) (hk : 2 ≤ k)
    (hq : IsL2Quot k (oTwoQuot ↥(oTwoPrime (f112saP1' L1 L2 S))))
    (hindec : ⁅pCoreOf 2 (f112saP1' L1 L2 S),
      oTwoPrime (f112saP1' L1 L2 S)⁆ = pCoreOf 2 (f112saP1' L1 L2 S)) :
    S ≤ L1 ∧ L1 = oTwoPrime (f112saP1' L1 L2 S) ∧
      pCoreOf 2 L1 = pCoreOf 2 (f112saP1' L1 L2 S) := by
  classical
  let E := f112saP1' L1 L2 S
  let A := oTwoRes L1
  let L := oTwoPrime E
  let Q := pCoreOf 2 E
  have hP1N : f112P1 L1 L2 S ≤ Subgroup.normalizer (L1 : Set H) :=
    sup_le Subgroup.le_normalizer (F1.bigB_le_normalizer_left hR).1
  have hQN : Q ≤ Subgroup.normalizer (L1 : Set H) :=
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 E).trans (f112sa_P1'_le_P1 hF)).trans hP1N
  have hL : L = A ⊔ Q := f112sa_oTwoPrime_eq_oTwoRes_sup_pCoreOf_P1'_of_isL2Quot hF hm h1 hk hq
  have hAQ : A ≤ Subgroup.normalizer (Q : Set H) :=
    (le_sup_left : A ≤ E).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 E)
  have hQ_le_L1 : Q ≤ L1 := CFSG.GroupTheory.le_of_commutator_eq_of_sup_eq
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 E).isNilpotent hL (oTwoRes_le L1) hQN hAQ hindec
  have hLE_le_L1 : L ≤ L1 := by
    rw [hL]
    exact sup_le (oTwoRes_le L1) hQ_le_L1
  have hS_le_L : S ≤ L := by
    have hSyl := f112sa_T_sylow_oTwoPrime_P1'_of_hyp111R hF hR
    rw [inf_eq_left.mpr hS] at hSyl
    exact hSyl.1
  have hS_le_L1 : S ≤ L1 := hS_le_L.trans hLE_le_L1
  have hL1_le_L : L1 ≤ L := by
    have h := le_oTwoRes_sup_of_isSylowTwoOf hF.1.h1.sylow
    refine h.trans (sup_le (f112sa_oTwoRes_le_oTwoPrime_P1'_of_isL2Quot hm h1) ?_)
    exact (inf_le_left : S ⊓ L1 ≤ S).trans hS_le_L
  have hL1_eq_L : L1 = L := le_antisymm hL1_le_L hLE_le_L1
  have hpQ : pCoreOf 2 L1 = Q := by
    rw [hL1_eq_L]
    exact pCoreOf_oTwoPrime E
  exact ⟨hS_le_L1, hL1_eq_L, hpQ⟩

theorem f112sa_S_le_L1_and_eq_oTwoPrime_of_S_le_K
    {L1 L2 S : Subgroup H} (hF : F112HypW L1 L2 S) (h1 : VA5 L1)
    (hS : S ≤ f112saK L1 L2 S)
    (hq : IsL2Quot 2 (oTwoQuot ↥(oTwoPrime (f112saP1' L1 L2 S))))
    (hindec : ⁅pCoreOf 2 (f112saP1' L1 L2 S),
      oTwoPrime (f112saP1' L1 L2 S)⁆ = pCoreOf 2 (f112saP1' L1 L2 S)) :
    S ≤ L1 ∧ L1 = oTwoPrime (f112saP1' L1 L2 S) ∧
      pCoreOf 2 L1 = pCoreOf 2 (f112saP1' L1 L2 S) :=
  f112sa_S_le_L1_and_eq_oTwoPrime_of_S_le_K_of_isL2Quot hF
    (Hyp111R.of_hyp111 rankOneListedFacts hF.1) le_rfl h1 hS le_rfl hq hindec

theorem f112sa_S_le_L2_and_eq_oTwoPrime_of_S_le_K_of_isL2Quot {L1 L2 S : Subgroup H} {n k : ℕ}
    (hF : F112HypW L1 L2 S) (hR : Hyp111R L1 L2 S) (hn : 2 ≤ n) (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (hS : S ≤ f112saK L1 L2 S) (hk : 2 ≤ k)
    (hq : IsL2Quot k (oTwoQuot ↥(oTwoPrime (f112saP2' L1 L2 S))))
    (hindec : ⁅pCoreOf 2 (f112saP2' L1 L2 S),
      oTwoPrime (f112saP2' L1 L2 S)⁆ = pCoreOf 2 (f112saP2' L1 L2 S)) :
    S ≤ L2 ∧ L2 = oTwoPrime (f112saP2' L1 L2 S) ∧
      pCoreOf 2 L2 = pCoreOf 2 (f112saP2' L1 L2 S) := by
  rw [f112saP2'_eq_P1'_swap] at hq hindec ⊢
  have hS' : S ≤ f112saK L2 L1 S := by rwa [f112saK_comm]
  exact f112sa_S_le_L1_and_eq_oTwoPrime_of_S_le_K_of_isL2Quot hF.symm hR.symm hn h2 hS' hk hq
    hindec

theorem f112sa_S_le_L2_and_eq_oTwoPrime_of_S_le_K
    {L1 L2 S : Subgroup H} (hF : F112HypW L1 L2 S) (h2 : VA5 L2)
    (hS : S ≤ f112saK L1 L2 S)
    (hq : IsL2Quot 2 (oTwoQuot ↥(oTwoPrime (f112saP2' L1 L2 S))))
    (hindec : ⁅pCoreOf 2 (f112saP2' L1 L2 S),
      oTwoPrime (f112saP2' L1 L2 S)⁆ = pCoreOf 2 (f112saP2' L1 L2 S)) :
    S ≤ L2 ∧ L2 = oTwoPrime (f112saP2' L1 L2 S) ∧
      pCoreOf 2 L2 = pCoreOf 2 (f112saP2' L1 L2 S) :=
  f112sa_S_le_L2_and_eq_oTwoPrime_of_S_le_K_of_isL2Quot hF
    (Hyp111R.of_hyp111 rankOneListedFacts hF.1) le_rfl h2 hS le_rfl hq hindec

structure TransferVertexData (E : Subgroup H) : Prop where
  quot : IsL2Quot 2 (oTwoQuot ↥(oTwoPrime E))
  abelian : IsMulCommutative ↥(pCoreOf 2 E)
  index : (pCoreOf 2 E ⊓ Subgroup.centralizer (oTwoPrime E : Set H)).relIndex
    (pCoreOf 2 E) = 16
  nat : NatSec (oTwoPrime E) (pCoreOf 2 E ⊓ Subgroup.centralizer (oTwoPrime E : Set H))
    (pCoreOf 2 E)
  indec : ⁅pCoreOf 2 E, oTwoPrime E⁆ = pCoreOf 2 E

theorem f112sa_S_le_L1_and_eq_oTwoPrime_of_transferVertexData
    {L1 L2 S : Subgroup H} (hF : F112HypW L1 L2 S) (h1 : VA5 L1)
    (hS : S ≤ f112saK L1 L2 S) (hV : TransferVertexData (f112saP1' L1 L2 S)) :
    S ≤ L1 ∧ L1 = oTwoPrime (f112saP1' L1 L2 S) ∧
      pCoreOf 2 L1 = pCoreOf 2 (f112saP1' L1 L2 S) := by
  exact f112sa_S_le_L1_and_eq_oTwoPrime_of_S_le_K hF h1 hS hV.quot hV.indec

theorem f112sa_S_le_L2_and_eq_oTwoPrime_of_transferVertexData
    {L1 L2 S : Subgroup H} (hF : F112HypW L1 L2 S) (h2 : VA5 L2)
    (hS : S ≤ f112saK L1 L2 S) (hV : TransferVertexData (f112saP2' L1 L2 S)) :
    S ≤ L2 ∧ L2 = oTwoPrime (f112saP2' L1 L2 S) ∧
      pCoreOf 2 L2 = pCoreOf 2 (f112saP2' L1 L2 S) := by
  exact f112sa_S_le_L2_and_eq_oTwoPrime_of_S_le_K hF h2 hS hV.quot hV.indec

end CFSG.Quasithin.F112R.St84
