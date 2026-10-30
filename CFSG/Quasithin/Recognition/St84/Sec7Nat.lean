module

public import CFSG.Quasithin.Recognition.St84.Nat16
public import CFSG.Quasithin.Recognition.St84.EdgeStabB
public import CFSG.Quasithin.Background.GoldschmidtAmalgamPairBasic
public import CFSG.Quasithin.Vol2.Ch10SecKHLk2C
public import CFSG.Quasithin.Recognition.GoldschmidtFan86UnivAmalgam
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86
  CFSG.Quasithin.F6.GoldAmL3T CFSG.GH74.QTGen4.DSGen4
open scoped commutatorElement

section SetupType

variable {V : Type*} {G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem Setup.exists_order_five_not_centralizing (X : Setup Γ G)
    (hc : CharTwoStab (V := V) (G := G)) (i : ℤ) (hn : X.n i = 2) :
    ∃ x ∈ X.L i, orderOf x = 5 ∧ ∃ q ∈ X.Q i, x * q * x⁻¹ ≠ q := by
  classical
  haveI hfinGi : Finite ↥(X.Gi i) := X.hyp.finite_stab (X.vert i)
  haveI hfinL : Finite ↥(X.L i) :=
    Finite.of_injective (Subgroup.inclusion (X.L_le_Gi i))
      (Subgroup.inclusion_injective (X.L_le_Gi i))
  have hL : IsLocL2 Γ G (X.vert i) 2 (X.L i) := by
    simpa [Setup.n, hn] using X.hyp.isLocL2_oTwoPrime (X.vert i)
  have hquot : IsL2Quot 2 (oTwoQuot ↥(X.L i)) := by
    simpa [IsL2Quot, oTwoQuot] using hL.quot
  have hcardL : Nat.card ↥(X.L i) = 60 * Nat.card (CFSG.pCore 2 ↥(X.L i)) := by
    have h60 : Nat.card (oTwoQuot ↥(X.L i)) = 60 := by
      rw [CFSG.Quasithin.IsL2Quot.card (by norm_num : 1 ≤ 2) hquot]
      norm_num
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥(X.L i))
    rw [h60] at h
    exact h
  have h5dvd : 5 ∣ Nat.card ↥(X.L i) := by
    rw [hcardL]
    exact dvd_mul_of_dvd_left (by norm_num : 5 ∣ 60) _
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨x, hx5'⟩ := exists_prime_orderOf_dvd_card' 5 h5dvd
  have hx5 : orderOf (x : G) = 5 := by
    rw [Subgroup.orderOf_coe]
    exact hx5'
  have hxL : (x : G) ∈ X.L i := x.2
  have hxGi : (x : G) ∈ X.Gi i := X.L_le_Gi i hxL
  have hex : ∃ q ∈ X.Q i, (x : G) * q * (x : G)⁻¹ ≠ q := by
    by_contra hcon
    push Not at hcon
    have hxCent : (x : G) ∈ Subgroup.centralizer (X.Q i : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      calc q * (x : G) = ((x : G) * q * (x : G)⁻¹) * (x : G) := by rw [hcon q hq]
        _ = (x : G) * q := by group
    have hxQ : (x : G) ∈ X.Q i := hc (X.vert i) ⟨hxGi, hxCent⟩
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hQp : IsPGroup 2 (X.Q i) :=
      (CFSG.pCore_isPGroup (G := ↥(X.Gi i)) (p := 2)).map (X.Gi i).subtype
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hQp) ⟨(x : G), hxQ⟩
    rw [Subgroup.orderOf_mk, hx5] at hk
    rcases k with _ | k
    · simp at hk
    · have h2 : 2 ∣ 2 ^ (k + 1) := dvd_pow_self 2 (Nat.succ_ne_zero k)
      rw [← hk] at h2
      norm_num at h2
  exact ⟨(x : G), hxL, hx5, hex⟩

theorem Setup.isElemAbelian_Q_of_card (X : Setup Γ G)
    (hc : CharTwoStab (V := V) (G := G)) (i : ℤ) (hn : X.n i = 2)
    (hcard : Nat.card (X.Q i) = 2 ^ 4) : IsElemAbelian 2 (X.Q i) := by
  obtain ⟨x, hxL, hx5, q, hqQ, hqne⟩ := X.exists_order_five_not_centralizing hc i hn
  have hxGi : x ∈ X.Gi i := X.L_le_Gi i hxL
  have hxN : x ∈ Subgroup.normalizer (X.Q i : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi i) hxGi
  haveI : Finite ↥(X.Gi i) := X.hyp.finite_stab (X.vert i)
  haveI : Finite ↥(X.Q i) :=
    Finite.of_injective (Subgroup.inclusion (X.Q_le_Gi i))
      (Subgroup.inclusion_injective (X.Q_le_Gi i))
  have hcard16 : Nat.card (X.Q i) = 16 := by
    rw [hcard]
    norm_num
  exact (isElemAbelian_of_card_eq_sixteen hcard16 hxN hx5 ⟨q, hqQ, hqne⟩).1

end SetupType

theorem natSec_of_four_le_card_centralizer_of_finite
    {G : Type} [Group G] {P L T : Subgroup G} [Finite ↥P] (hLP : L ≤ P)
    (hPL : P ≤ Subgroup.normalizer (L : Set G)) (hchar : CharTwo P)
    (hquot : IsL2Quot 2 (oTwoQuot ↥L)) (hcard : Nat.card (pCoreOf 2 P) = 16)
    (hT : IsSylowTwoOf T L)
    (hC : 4 ≤ Nat.card ↥(pCoreOf 2 P ⊓ Subgroup.centralizer (T : Set G))) :
    IsElemAbelian 2 (pCoreOf 2 P) ∧ NatSec L ⊥ (pCoreOf 2 P) := by
  classical
  have hpTop : pCoreOf 2 (⊤ : Subgroup ↥P) = (pCoreOf 2 P).subgroupOf P := by
    have h := CFSG.Quasithin.Vol2.Ch10.SecB.C10KH.pCoreOf_subgroupOf_map'
      (K := P) (Y := P) le_rfl
    rw [Subgroup.subgroupOf_self] at h
    rw [← h]
    exact (Subgroup.comap_map_eq_self_of_injective P.subtype_injective
      (pCoreOf 2 (⊤ : Subgroup ↥P))).symm
  have hLP' : L.subgroupOf P ≤ (⊤ : Subgroup ↥P) := le_top
  have hPL' : (⊤ : Subgroup ↥P) ≤ Subgroup.normalizer (L.subgroupOf P : Set ↥P) := by
    exact le_of_eq (Subgroup.normalizer_eq_top_iff.mpr
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hLP).mpr hPL)).symm
  have hchar' : CharTwo (⊤ : Subgroup ↥P) := by
    simpa [Subgroup.subgroupOf_self] using
      (CFSG.Quasithin.F6.GoldPair.charTwo_subgroupOf_iff (I := P) (K := P) le_rfl).mpr hchar
  have hquot' : IsL2Quot 2 (oTwoQuot ↥(L.subgroupOf P)) := by
    obtain ⟨e⟩ := hquot
    exact ⟨(CFSG.Quasithin.Fan86.Univ.oTwoQuotMulEquiv
      (Subgroup.subgroupOfEquivOfLe hLP)).trans e⟩
  have hcard' : Nat.card (pCoreOf 2 (⊤ : Subgroup ↥P)) = 16 := by
    rw [hpTop]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (CFSG.openPCoreOf_le 2 P)).toEquiv).trans hcard
  have hcent : Subgroup.centralizer (T.subgroupOf P : Set ↥P) =
      (Subgroup.centralizer (T : Set G)).subgroupOf P := by
    ext x
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    constructor
    · intro h t ht
      simpa using congrArg Subtype.val (h ⟨t, hLP (hT.1 ht)⟩ ht)
    · intro h t ht
      apply Subtype.ext
      exact h (t : G) (Subgroup.mem_subgroupOf.mp ht)
  have hC' : 4 ≤ Nat.card ↥(pCoreOf 2 (⊤ : Subgroup ↥P) ⊓
      Subgroup.centralizer (T.subgroupOf P : Set ↥P)) := by
    rw [hpTop, hcent]
    rw [CFSG.Quasithin.F6.GoldPair.card_inf_subgroupOf (I₁ := pCoreOf 2 P)
      (I₂ := Subgroup.centralizer (T : Set G)) (K := P) (CFSG.openPCoreOf_le 2 P)]
    exact hC
  have hT' : IsSylowTwoOf (T.subgroupOf P) (L.subgroupOf P) := by
    refine ⟨fun x hx => hT.1 hx, ?_, ?_⟩
    · exact hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe (hT.1.trans hLP)).symm
    · have h2 : ((T.subgroupOf P).subgroupOf (L.subgroupOf P)).index =
          (T.subgroupOf L).index :=
        Subgroup.relIndex_subgroupOf (H := T) (K := L) (L := P) hLP
      rw [h2]
      exact hT.2.2
  have hmain := natSec_of_four_le_card_centralizer (G := ↥P) (P := (⊤ : Subgroup ↥P))
    (L := L.subgroupOf P) (T := T.subgroupOf P) hLP' hPL' hchar' hquot' hcard' hT' hC'
  refine ⟨?_, ?_⟩
  · have hElemTop : IsElemAbelian 2 (pCoreOf 2 (⊤ : Subgroup ↥P)) := hmain.1
    have hElemSub : IsElemAbelian 2 ((pCoreOf 2 P).subgroupOf P) := by
      rwa [hpTop] at hElemTop
    have hmap := CFSG.Open.IsElemAbelian.map (p := 2) hElemSub P.subtype
    rwa [Subgroup.map_subgroupOf_eq_of_le (CFSG.openPCoreOf_le 2 P)] at hmap
  · intro x hxL hx3 e heE heComm
    have hxP : x ∈ P := hLP hxL
    have hxP' : (⟨x, hxP⟩ : ↥P) ∈ L.subgroupOf P := hxL
    have hx3' : orderOf (⟨x, hxP⟩ : ↥P) = 3 := by
      rw [Subgroup.orderOf_mk]
      exact hx3
    have heP : e ∈ P := CFSG.openPCoreOf_le 2 P heE
    have heP' : (⟨e, heP⟩ : ↥P) ∈ pCoreOf 2 (⊤ : Subgroup ↥P) := by
      rw [hpTop]
      exact heE
    have hcomm' : ⁅(⟨e, heP⟩ : ↥P), (⟨x, hxP⟩ : ↥P)⁆ ∈ (⊥ : Subgroup ↥P) := by
      rw [Subgroup.mem_bot]
      apply Subtype.ext
      rw [Subgroup.coe_one]
      rw [show (((⁅(⟨e, heP⟩ : ↥P), (⟨x, hxP⟩ : ↥P)⁆ : ↥P) : G)) = ⁅e, x⁆ from
        map_commutatorElement P.subtype _ _]
      exact Subgroup.mem_bot.mp heComm
    have hmem := hmain.2 (⟨x, hxP⟩) hxP' hx3' (⟨e, heP⟩) heP' hcomm'
    rw [Subgroup.mem_bot] at hmem ⊢
    exact congrArg Subtype.val hmem

theorem Setup.natSec_Q_of_card {V G : Type} [Group G]
    [MulAction G V] {Γ : SimpleGraph V} (X : Setup Γ G)
    (hc : CharTwoStab (V := V) (G := G)) (i : ℤ) (hn : X.n i = 2)
    (hcard : Nat.card (X.Q i) = 2 ^ 4) {T : Subgroup G}
    (hT : IsSylowTwoOf T (X.L i))
    (hC : 4 ≤ Nat.card ↥(X.Q i ⊓ Subgroup.centralizer (T : Set G))) :
    NatSec (X.L i) ⊥ (pCoreOf 2 (X.L i)) := by
  haveI : Finite ↥(X.Gi i) := X.hyp.finite_stab (X.vert i)
  have hL : IsLocL2 Γ G (X.vert i) 2 (X.L i) := by
    simpa [Setup.n, hn] using X.hyp.isLocL2_oTwoPrime (X.vert i)
  have hquot : IsL2Quot 2 (oTwoQuot ↥(X.L i)) := by
    simpa [IsL2Quot, oTwoQuot] using hL.quot
  have hcard16 : Nat.card (pCoreOf 2 (X.Gi i)) = 16 := by
    simpa [Setup.Q] using hcard.trans (by norm_num : (2 : ℕ) ^ 4 = 16)
  have hC16 : 4 ≤ Nat.card ↥(pCoreOf 2 (X.Gi i) ⊓
      Subgroup.centralizer (T : Set G)) := by
    simpa [Setup.Q] using hC
  have h := natSec_of_four_le_card_centralizer_of_finite (P := X.Gi i) (L := X.L i) (T := T)
    (X.L_le_Gi i) (by simpa [Setup.L] using CFSG.Quasithin.le_normalizer_oTwoPrime (X.Gi i))
    (hc (X.vert i)) hquot hcard16 hT hC16
  rw [hL.pCoreOf_eq]
  exact h.2

end CFSG.Quasithin.St84
