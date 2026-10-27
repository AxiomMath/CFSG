module

public import CFSG.RankThree.PartTwo.Sec16.Item163U35Conf
import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofLA7
import CFSG.RankThree.PartTwo.Sec16.Item163ResProofU35Facts
import CFSG.CGT.PushingUp.TwoLocals
public import CFSG.RankThree.PartTwo.Sec15.Item15Steps
import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof163U35

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Sec17.HeadProof CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

section Generic

variable {A : Subgroup G} {LB : Subgroup G → Subgroup G}

theorem delta_le_normalizer_of_mem (h155 : Item155 A LB) {K M : Subgroup G}
    (hK : K ∈ scriptY0Star A LB)
    (hM : M ∈ CFSG.maximalTwoLocalsContaining ((A ⊔ K : Subgroup G) : Set G)) :
    delta A LB M ≤ Subgroup.normalizer (K : Set G) := by
  have hK4 : K ∈ scriptY4 A LB := hK.prop.1
  have hK3 : K ∈ scriptY3 A LB := ⟨hK.prop.2, hK4.2.2.1⟩
  have hKres : oPrimeResidualOf 3 K ∈ scriptY4 A LB := hK4.2.1 ▸ hK4
  have hKsup : K = oPrimeResidualOf 3 K ⊔ CFSG.Open.pCoreOf 2 K := by
    apply le_antisymm
    · calc K = oPrimeResidualOf 3 K := hK4.2.1
        _ ≤ oPrimeResidualOf 3 K ⊔ CFSG.Open.pCoreOf 2 K := le_sup_left
    · exact sup_le hK4.2.1.ge (CFSG.LieType.BorelTits.pCoreOf_le 2 K)
  have hgam : K ∈ gam155 A LB K (oPrimeResidualOf 3 K) :=
    ⟨hK, hK4.2.1.ge, Subgroup.le_normalizer⟩
  exact (h155 K hK3 hKres hKsup).2 K hgam (Or.inr hKsup) M hM

theorem mem_scriptQPiStar_top_of_mem (h153 : Item153Main A LB) (h155 : Item155 A LB)
    {K T : Subgroup G} (hK : K ∈ scriptY0Star A LB)
    (hT : T ∈ scriptQPiStar A LB (Subgroup.normalizer (K : Set G)) (piOf 2)) :
    T ∈ scriptQPiStar A LB ⊤ (piOf 2) := by
  set M := Subgroup.normalizer
    (oPrimeResidualOf 3 (delta A LB (Subgroup.normalizer (K : Set G))) : Set G) with hM
  have hMmem : CFSG.maximalTwoLocalsContaining ((K ⊔ A : Subgroup G) : Set G) = {M} := by
    simpa only [hM] using (h153 K hK).1
  have hKA : ((K ⊔ A : Subgroup G) : Set G) ⊆
      Subgroup.normalizer (CFSG.Open.pCoreOf 2 K : Set G) :=
    sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K)
      (hK.prop.1.1.2.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
  have hloc : IsPLocal 2 (Subgroup.normalizer (CFSG.Open.pCoreOf 2 K : Set G)) :=
    CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) K) hK.prop.2.2
  obtain ⟨M', hNM', hM'max⟩ := CFSG.CGT.PushingUp.exists_isMaximalTwoLocal_ge hloc
  have hM' : M' ∈ CFSG.maximalTwoLocalsContaining ((K ⊔ A : Subgroup G) : Set G) :=
    ⟨hM'max, hKA.trans hNM'⟩
  have hM'eq : M' = M := by
    have : M' ∈ ({M} : Set (Subgroup G)) := hMmem ▸ hM'
    exact Set.mem_singleton_iff.mp this
  have hNKleM : Subgroup.normalizer (K : Set G) ≤ M :=
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K).trans
      (hNM'.trans hM'eq.le)
  have hMAmem : M ∈ CFSG.maximalTwoLocalsContaining ((A ⊔ K : Subgroup G) : Set G) := by
    rw [sup_comm, hMmem]
    exact Set.mem_singleton M
  have hdelta : delta A LB M ≤ Subgroup.normalizer (K : Set G) :=
    delta_le_normalizer_of_mem h155 hK hMAmem
  have hTM : T ∈ scriptQPiStar A LB M (piOf 2) := by
    refine ⟨⟨⟨hT.prop.1.1, hT.prop.1.2.trans hNKleM⟩, hT.prop.2⟩, ?_⟩
    intro T' hT' hle
    exact hT.2 ⟨⟨hT'.1.1, (le_delta hT'.1.1 hT'.1.2).trans hdelta⟩, hT'.2⟩ hle
  exact ((h153 K hK).2.1 T hTM).1

end Generic

private theorem pCoreOf_eq_bot_of_card_eq {L : Subgroup G} (hcard : Nat.card L = 126000)
    (hs : IsSimpleGroup ↥L) : CFSG.Open.pCoreOf 2 L = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnormal : ((CFSG.Open.pCoreOf 2 L).subgroupOf L).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
  rcases hs.eq_bot_or_eq_top_of_normal ((CFSG.Open.pCoreOf 2 L).subgroupOf L) with h | h
  · rw [← Subgroup.map_subgroupOf_eq_of_le (CFSG.LieType.BorelTits.pCoreOf_le 2 L), h,
      Subgroup.map_bot]
  · exfalso
    have hLle : L ≤ CFSG.Open.pCoreOf 2 L := by
      intro x hx
      have h1 : (⟨x, hx⟩ : ↥L) ∈ (CFSG.Open.pCoreOf 2 L).subgroupOf L :=
        h ▸ Subgroup.mem_top _
      exact h1
    have h2 : IsPGroup 2 ↥L :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) L).to_le hLle
    obtain ⟨n, hn⟩ := h2.exists_card_eq
    have h3 : 3 ∣ Nat.card L := by rw [hcard]; norm_num
    rw [hn] at h3
    have h4 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    norm_num at h4

namespace Conf684

variable {A : Subgroup G} {c : G} {L Y : Subgroup G}

theorem case3_of_mem (h : Conf684 A c L Y) {K : Subgroup G}
    (hK : K ∈ scriptY0Star A (lB A)) (hKm : MeetsY4 A (lB A) L K) :
    Case1514Three A (lB A) c L K := by
  obtain ⟨hLs, hLcard, -, -, -, -, -, -⟩ := Res163U35Facts.facts h.sec15R h.mem_y h.case3
  rcases h.item1514 K hK hKm with h1 | h2 | h3
  · exfalso
    obtain ⟨-, hLK, -, -, -⟩ := h1
    have hO2 : CFSG.Open.pCoreOf 2 L = ⊥ := pCoreOf_eq_bot_of_card_eq hLcard hLs
    have hLKle : L ≤ K := by
      rw [hLK, hO2, sup_bot_eq]
      exact inf_le_right
    exact (h.case3.2.2.2.2.1 K hK) hLKle
  · exfalso
    obtain ⟨inst5, ⟨eSU⟩⟩ := h.case3.1
    obtain ⟨eA7⟩ := h2.1
    haveI := inst5
    have hcard : Nat.card (alternatingGroup (Fin 7)) =
        Nat.card (CFSG.Assembly.RankThreeEven.projSU 3 5 1) :=
      Nat.card_congr (eA7.symm.trans eSU).toEquiv
    rw [CFSG.RankThree.PartTwo.Sec15.Proof1515.card_projSU_three_five,
      nat_card_alternatingGroup, Nat.card_fin] at hcard
    norm_num at hcard
  · exact h3

theorem normalizer_le_normalizer (h : Conf684 A c L Y) :
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  obtain ⟨-, -, -, -, -, h9, -, -⟩ := Res163U35Facts.facts h.sec15R h.mem_y h.case3
  have hΩ : omegaA A = {Subgroup.zpowers c} := h.case3.2.2.2.1
  obtain ⟨d, hdAL, hdc⟩ : ∃ d ∈ A ⊓ L, d ∉ Subgroup.zpowers c := by
    by_contra hall
    push Not at hall
    have hle := Subgroup.card_le_of_le (show A ⊓ L ≤ Subgroup.zpowers c from hall)
    rw [h9, h.sec15R.toSec13Data.card_zpowers] at hle
    omega
  intro w hw
  exact Sec13.normalizer_inf_le_of_mem h.sec15R.toSec13Data.mem_thetaComponentsAt
    h.sec15R.toSec13Data.le_normalizer h.sec15R.toSec13Data.sectionCentralizer_eq
    hdAL.1 hdAL.2 hdc ⟨Sec15.normalizer_le_of_omegaA_eq hΩ hw, hw⟩

theorem map_conj_isZeta (h : Conf684 A c L Y) {u : G}
    (hu : u ∈ Subgroup.normalizer (A : Set G)) {T K : Subgroup G} (hTK : IsZeta A L T K) :
    IsZeta A L (T.map (MulAut.conj u).toMonoidHom) (K.map (MulAut.conj u).toMonoidHom) := by
  refine ⟨Sec16.map_conj_mem_scriptY0Star hu hTK.1, ?_, ?_⟩
  · obtain ⟨X, hX, hXLK⟩ := hTK.2.1
    refine ⟨X.map (MulAut.conj u).toMonoidHom, Sec16.map_conj_mem_scriptY4 hu hX, ?_⟩
    refine le_inf ?_ (Subgroup.map_mono fun x hx => (hXLK (x := x) hx).2)
    calc X.map (MulAut.conj u).toMonoidHom ≤ L.map (MulAut.conj u).toMonoidHom :=
          Subgroup.map_mono fun x hx => (hXLK (x := x) hx).1
      _ = L := Subgroup.mem_normalizer_iff_map_conj_eq.mp (normalizer_le_normalizer h hu)
  · have hmap := map_conj_mem_scriptQPiStar hu hTK.2.2
    rwa [Subgroup.map_equiv_normalizer_eq] at hmap

theorem mem_top_of_isZeta (h : Conf684 A c L Y) {T K : Subgroup G} (hTK : IsZeta A L T K) :
    T ∈ scriptQPiStar A (lB A) ⊤ (piOf 2) :=
  mem_scriptQPiStar_top_of_mem h.item153 h.item155 hTK.1 hTK.2.2

theorem exists_isZeta (h : Conf684 A c L Y) {T : Subgroup G}
    (hT : T ∈ scriptQPiStar A (lB A) ⊤ (piOf 2)) : ∃ K, IsZeta A L T K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ : CFSG.Open.pCoreOf 2 Y ∈ scriptQ A (lB A) :=
    Res163U35Facts.pCoreOf_mem_scriptQ h.sec15R h.mem_y h.case3 h.item1444 h.item146
  have hQpi : CFSG.Open.pCoreOf 2 Y ∈
      scriptQPi A (lB A) (Subgroup.normalizer (Y : Set G)) (piOf 2) := by
    refine ⟨⟨hQ, (CFSG.LieType.BorelTits.pCoreOf_le 2 Y).trans Subgroup.le_normalizer⟩, ?_⟩
    exact (isPiSubgroup_piOf_iff Nat.prime_two _).mpr
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y)
  obtain ⟨S, -, hS⟩ := Finite.exists_le_maximal
    (p := (· ∈ scriptQPi A (lB A) (Subgroup.normalizer (Y : Set G)) (piOf 2))) hQpi
  have hSY : IsZeta A L S Y := ⟨h.mem_y, h.meets, hS⟩
  have hSG : S ∈ scriptQPiStar A (lB A) ⊤ (piOf 2) := mem_top_of_isZeta h hSY
  obtain ⟨u, hu, hTS⟩ := h.item1411 S hSG T hT
  refine ⟨Y.map (MulAut.conj u).toMonoidHom, ?_⟩
  rw [hTS]
  exact map_conj_isZeta h hu.1 hSY

end Conf684

end CFSG.RankThree.PartTwo.Sec16.Proof163U35
