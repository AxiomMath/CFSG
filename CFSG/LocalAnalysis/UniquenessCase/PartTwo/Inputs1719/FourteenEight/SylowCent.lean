module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen3a
import CFSG.LocalAnalysis.GLTheoremA.CatA.I142NBase
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenAltTenUnique

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem centOverO2_le_normalizer (X L : Subgroup G) :
    F08.CentOverO2 X L ≤ normalizer (L : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rw [Subgroup.map_le_iff_le_comap]
    intro l hl
    rw [Subgroup.mem_comap]
    have hmem := L.mul_mem
      (CFSG.LieType.BorelTits.pCoreOf_le 2 L ((mem_centOverO2_iff.mp hx).2 l hl)) hl
    simpa [MulAut.conj_apply, mul_assoc] using hmem
  · rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]

theorem le_normalizer_of_isSylowOf_centOverO2 {X L R : Subgroup G} (hLX : L ≤ X)
    (hR : CFSG.ABGLocalTools.IsSylowOf 2 R (F08.CentOverO2 X L)) :
    L ≤ normalizer (R : Set G) := by
  classical
  set C := F08.CentOverO2 X L with hC
  set Q := pCoreOf 2 L with hQ
  have hQL : Q ≤ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L
  have hRC : R ≤ C := hR.le
  have hQC : Q ≤ C := by
    rw [hC]
    intro u hu
    rw [mem_centOverO2_iff]
    refine ⟨hLX (hQL hu), fun l hl => ?_⟩
    have hlu : l * u⁻¹ * l⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.1
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L hl) u⁻¹).1 (Q.inv_mem hu)
    have hmem := Q.mul_mem hu hlu
    convert hmem using 1
    group
  have hCN : C ≤ normalizer (Q : Set G) := by
    rw [hC]
    exact (centOverO2_le_normalizer X L).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)
  have hQnorm : (Q.subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQC).mpr hCN
  have : (Q.subgroupOf C).Normal := hQnorm
  obtain ⟨P, hP⟩ := hR
  have hQp : IsPGroup 2 (Q.subgroupOf C) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).comap_subtype
  have hQleP : Q.subgroupOf C ≤ (P : Subgroup C) := IsPGroup.le_sylow_of_normal hQp P
  have hQR : Q ≤ R := by
    have hmapQ : (Q.subgroupOf C).map C.subtype = Q := Subgroup.map_subgroupOf_eq_of_le hQC
    rw [← hmapQ, ← hP]
    exact Subgroup.map_mono hQleP
  intro l hl
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rw [Subgroup.map_le_iff_le_comap]
    intro r hr
    rw [Subgroup.mem_comap]
    have hcomm : r * l⁻¹ * r⁻¹ * l ∈ Q := by
      rw [hC] at hRC
      have h := (mem_centOverO2_iff.mp (hRC hr)).2 l⁻¹ (L.inv_mem hl)
      simpa [hQ] using h
    have hconj : l * (r * l⁻¹ * r⁻¹ * l) * l⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.1
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L hl) _).1 hcomm
    have hmem : (l * (r * l⁻¹ * r⁻¹ * l) * l⁻¹) * r ∈ R :=
      R.mul_mem (hQR hconj) hr
    convert hmem using 1
    change l * r * l⁻¹ = l * (r * l⁻¹ * r⁻¹ * l) * l⁻¹ * r
    group
  · rw [Subgroup.card_map_of_injective (MulAut.conj l).injective]

theorem le_centOverO2_of_le_normalizer {X L R : Subgroup G} (hL : L ∈ calC X)
    (hR : IsPGroup 2 R) (hRX : R ≤ X) (hLR : L ≤ normalizer (R : Set G)) :
    R ≤ F08.CentOverO2 X L := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLX : L ≤ X := CFSG.LocalAnalysis.GLTheoremA.I142N.isSubnormal_le hL.1
  have hsub : IsSubnormal L (L ⊔ R) :=
    CFSG.LocalAnalysis.GLTheoremA.I142N.isSubnormal_of_le_of_le hL.1 le_sup_left
      (sup_le hLX hRX)
  have hHR : L ⊔ R ≤ normalizer (R : Set G) := sup_le hLR Subgroup.le_normalizer
  have hnormH : (L.subgroupOf (L ⊔ R)).Normal :=
    CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.AltTen.subgroupOf_normal_of_isSubnormal
      hR hsub L hL.2.1 le_rfl (by rw [Subgroup.subgroupOf_self]; infer_instance) hHR le_rfl
  have hHL : L ⊔ R ≤ normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mp hnormH
  have hRH : R ≤ L ⊔ R := le_sup_right
  have hRL : R ≤ normalizer (L : Set G) := fun r hr => hHL (hRH hr)
  have hcore : L ⊓ R ≤ pCoreOf 2 L := by
    refine CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 (L ⊓ R) L
      inf_le_left ?_ (hR.to_inf_right (H := L))
    refine ⟨fun x hx l => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact ⟨L.mul_mem (L.mul_mem l.2 hx.1) (L.inv_mem l.2),
      (Subgroup.mem_normalizer_iff.1 (hLR l.2) (x : G)).1 hx.2⟩
  intro r hr
  rw [mem_centOverO2_iff]
  refine ⟨hRX hr, fun l hl => ?_⟩
  refine hcore ⟨?_, ?_⟩
  · exact L.mul_mem ((Subgroup.mem_normalizer_iff.1 (hRL hr) l).1 hl) (L.inv_mem hl)
  · have h1 : l * r⁻¹ * l⁻¹ ∈ R :=
      (Subgroup.mem_normalizer_iff.1 (hLR hl) r⁻¹).1 (R.inv_mem hr)
    have h2 : r * (l * r⁻¹ * l⁻¹) ∈ R := R.mul_mem hr h1
    rw [show r * l * r⁻¹ * l⁻¹ = r * (l * r⁻¹ * l⁻¹) by group]
    exact h2

theorem isSylowOf_centOverO2_of_maximal {X L R : Subgroup G} (hL : L ∈ calC X)
    (hR : IsPGroup 2 R) (hRX : R ≤ X) (hLR : L ≤ normalizer (R : Set G))
    (hmax : ∀ R' : Subgroup G, IsPGroup 2 R' → R' ≤ X → L ≤ normalizer (R' : Set G) → R ≤ R' →
      R' = R) :
    CFSG.ABGLocalTools.IsSylowOf 2 R (F08.CentOverO2 X L) := by
  classical
  have hLX : L ≤ X := CFSG.LocalAnalysis.GLTheoremA.I142N.isSubnormal_le hL.1
  set C := F08.CentOverO2 X L with hC
  have hRC : R ≤ C := le_centOverO2_of_le_normalizer hL hR hRX hLR
  have hCX : C ≤ X := by
    rw [hC]
    unfold F08.CentOverO2
    exact (Subgroup.closure_le X).mpr fun x hx => hx.1
  have hRsub : IsPGroup 2 (R.subgroupOf C) := hR.comap_subtype
  obtain ⟨P, hP⟩ := IsPGroup.exists_le_sylow hRsub
  refine ⟨P, ?_⟩
  have hPX : ((P : Subgroup C).map C.subtype : Subgroup G) ≤ X :=
    (Subgroup.map_subtype_le (P : Subgroup C)).trans hCX
  have hPp : IsPGroup 2 ((P : Subgroup C).map C.subtype : Subgroup G) :=
    P.isPGroup'.map C.subtype
  have hPL : L ≤ normalizer (((P : Subgroup C).map C.subtype : Subgroup G) : Set G) :=
    le_normalizer_of_isSylowOf_centOverO2 hLX ⟨P, rfl⟩
  have hRleP : R ≤ (P : Subgroup C).map C.subtype := by
    have hmapR : (R.subgroupOf C).map C.subtype = R := Subgroup.map_subgroupOf_eq_of_le hRC
    rw [← hmapR]
    exact Subgroup.map_mono hP
  exact hmax ((P : Subgroup C).map C.subtype) hPp hPX hPL hRleP

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight
