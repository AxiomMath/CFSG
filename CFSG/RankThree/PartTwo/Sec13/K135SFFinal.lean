module

public import CFSG.RankThree.PartTwo.Sec13.K135SFModule
public import CFSG.RankThree.PartTwo.Sec13.K135SFCenterOdd
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface

public section

namespace CFSG.RankThree.PartTwo.Sec13.K135SF

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4

theorem le_pPrimeCore_of_normal {M : Type*} [Group M] (p : ℕ) (K : Subgroup M) [K.Normal]
    (hK : Nat.Coprime p (Nat.card K)) : K ≤ CFSG.pPrimeCore p M :=
  le_sSup ⟨inferInstance, hK⟩

theorem odd_card_center_component_pPrimeCore {M : Type*} [Group M] [Finite M] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (J : Subgroup (M ⧸ CFSG.pPrimeCore p M))
    (hJ : CFSG.IsComponent J) : Odd (Nat.card (Subgroup.center J)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h := not_two_dvd_card_center_component hp hp2 (CFSG.pPrimeCore p M)
    CFSG.pPrimeCore_coprime_card (fun K hK hKp => by
      haveI := hK
      exact le_pPrimeCore_of_normal p K hKp) J hJ
  exact Nat.odd_iff.mpr (by omega)

theorem list42_or_gl12_of_pPrimeCore (hLP : Item4_1LargePrime)
    (hTC : Item4_1ThreeCover) (h42 : Item4_2)
    {M : Type} [Group M] [Finite M] (hM : SectionFourHyp M) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hRodd : Odd (Nat.card (CFSG.pPrimeCore p M))) (J : Subgroup (M ⧸ CFSG.pPrimeCore p M))
    (hJ : CFSG.IsComponent J) :
    Sec4.Census.List42 (J ⧸ Subgroup.center J) ∨
      (CFSG.IsKGroup (J ⧸ Subgroup.center J) ∧ GL12Data (J ⧸ Subgroup.center J)) := by
  haveI : IsSimpleGroup (J ⧸ Subgroup.center J) := hJ.1.2.1
  have hSn : ∃ a b : J ⧸ Subgroup.center J, a * b ≠ b * a := hJ.1.2.2
  refine (sectionFourHyp_or_gl12 hLP hTC sf2_holds hM (CFSG.pPrimeCore p M) hRodd J hJ
    (odd_card_center_component_pPrimeCore hp hp2 J hJ)).imp (fun h => ?_) id
  exact Sec4.Census.item4_2_iff.mp h42 _ h inferInstance hSn

theorem le_of_relPPrimeCore {G : Type*} [Group G] (H : Subgroup G) (p : ℕ) (R : Subgroup H)
    (hR : R.map H.subtype = CFSG.Open.relPPrimeCore p H) (K : Subgroup H) [K.Normal]
    (hK : Nat.Coprime p (Nat.card K)) : K ≤ R := by
  have hmem : K.map H.subtype ∈ {N : Subgroup G | N ≤ H ∧ (N.subgroupOf H).Normal ∧
      Nat.Coprime p (Nat.card N)} := by
    refine ⟨Subgroup.map_subtype_le K, ?_, ?_⟩
    · have h : (K.map H.subtype).subgroupOf H = K :=
        Subgroup.comap_map_eq_self_of_injective H.subtype_injective K
      rw [h]
      infer_instance
    · rw [Subgroup.card_map_of_injective H.subtype_injective]
      exact hK
  have hle : K.map H.subtype ≤ R.map H.subtype := by
    rw [hR]
    exact le_sSup hmem
  exact (Subgroup.map_le_map_iff_of_injective H.subtype_injective).mp hle

theorem list42_or_gl12_of_relPPrimeCore (hLP : Item4_1LargePrime)
    (hTC : Item4_1ThreeCover) (h42 : Item4_2)
    {G : Type} [Group G] [Finite G] (H : Subgroup G) (hM : SectionFourHyp H) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (R : Subgroup H) [R.Normal]
    (hRe : R.map H.subtype = CFSG.Open.relPPrimeCore p H) (hRodd : Odd (Nat.card R))
    (hRp : Nat.Coprime p (Nat.card R)) (J : Subgroup (H ⧸ R)) (hJ : CFSG.IsComponent J) :
    Sec4.Census.List42 (J ⧸ Subgroup.center J) ∨
      (CFSG.IsKGroup (J ⧸ Subgroup.center J) ∧ GL12Data (J ⧸ Subgroup.center J)) := by
  haveI : IsSimpleGroup (J ⧸ Subgroup.center J) := hJ.1.2.1
  have hSn : ∃ a b : J ⧸ Subgroup.center J, a * b ≠ b * a := hJ.1.2.2
  have h := not_two_dvd_card_center_component hp hp2 R hRp
    (fun K hK hKp => by
      haveI := hK
      exact le_of_relPPrimeCore H p R hRe K hKp) J hJ
  refine (sectionFourHyp_or_gl12 hLP hTC sf2_holds hM R hRodd J hJ
    (Nat.odd_iff.mpr (by omega))).imp (fun h' => ?_) id
  exact Sec4.Census.item4_2_iff.mp h42 _ h' inferInstance hSn

end CFSG.RankThree.PartTwo.Sec13.K135SF
