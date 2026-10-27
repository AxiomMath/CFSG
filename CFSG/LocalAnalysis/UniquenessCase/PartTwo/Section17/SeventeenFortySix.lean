module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsC
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22rg
public import CFSG.LocalAnalysis.SectionRank.PRankIndex
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811CoordsLift
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsBorAut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

theorem pCore_le_sylow_of_mem_calC {D : Data G} {L : Subgroup G} (hL : L ∈ calC D.M) :
    CFSG.pCore 2 ↥L ≤ (D.T ⊓ L).subgroupOf L := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22r_fo_sylow_inf
    (K := D.M) (H := L) D.sylowM hL.1
  have hQeq : (Q : Subgroup ↥L) = (D.T ⊓ L).subgroupOf L :=
    Subgroup.map_injective L.subtype_injective (by
      rw [hQ, Subgroup.map_subgroupOf_eq_of_le inf_le_right])
  exact CFSG.pCore_isPGroup.le_sylow_of_normal Q |>.trans (le_of_eq hQeq)

theorem normalizer_sylow_subgroupOf {D : Data G} {L : Subgroup G} :
    Subgroup.normalizer (((D.T ⊓ L).subgroupOf L : Subgroup ↥L) : Set ↥L) =
      (L ⊓ Subgroup.normalizer ((D.T ⊓ L : Subgroup G) : Set G)).subgroupOf L :=
  (Subgroup.subgroupOf_normalizer_eq inf_le_right).symm.trans
    (Subgroup.inf_subgroupOf_left _ _).symm

theorem pRank_normalizerQuotient_le_pRank_cartan {D : Data G} {L C : Subgroup G}
    (hL : L ∈ calC D.M) (hC : CIsCartanOf D.T L C) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    CFSG.Open.pRank r (⊤ : Subgroup
        (TauCeti.Subgroup.normalizerQuotient ((D.T ⊓ L).subgroupOf L))) ≤
      CFSG.Open.pRank r C := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  set T0 : Subgroup G := D.T ⊓ L with hT0
  set N : Subgroup ↥L := T0.subgroupOf L with hN
  set Nrm : Subgroup ↥L := Subgroup.normalizer (N : Set ↥L) with hNrm
  have hCL : C ≤ L := hC.1
  have hCN : C ≤ Subgroup.normalizer (T0 : Set G) := hC.2.2.1
  obtain ⟨k, hk⟩ := hC.2.2.2.2
  have hCle : C.subgroupOf L ≤ Nrm := by
    rw [hNrm, normalizer_sylow_subgroupOf]
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact ⟨x.2, hCN hx⟩
  have hrel : (C.subgroupOf L).relIndex Nrm = 2 ^ k := by
    rw [hNrm, normalizer_sylow_subgroupOf]
    rw [Subgroup.relIndex_subgroupOf (H := C)
      (K := L ⊓ Subgroup.normalizer (T0 : Set G)) (L := L) inf_le_left]
    exact hk
  have hN2 : IsPGroup 2 N := by
    have hS : CFSG.ABGLocalTools.IsSylowOf 2 T0 L :=
      CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22r_fo_sylow_inf D.sylowM hL.1
    exact hS.isPGroup.comap_subtype
  have hcardN : ¬ r ∣ Nat.card N := by
    obtain ⟨m, hm⟩ := hN2.exists_card_eq
    rw [hm]
    intro h
    have hd : r ∣ 2 := hr.dvd_of_dvd_pow h
    rcases (Nat.dvd_prime Nat.prime_two).1 hd with h1 | h2
    · exact hr.ne_one h1
    · exact hr2 h2
  have hidx : ((C.subgroupOf L).subgroupOf Nrm).index = 2 ^ k := by
    rw [← Subgroup.relIndex_top_right ((C.subgroupOf L).subgroupOf Nrm),
      ← Subgroup.subgroupOf_self (H := Nrm),
      Subgroup.relIndex_subgroupOf (le_refl Nrm), hrel]
  have htransfer : CFSG.Open.pRank r (⊤ : Subgroup ↥Nrm) ≤
      CFSG.Open.pRank r ((C.subgroupOf L).subgroupOf Nrm) :=
    CFSG.SectionRank.pRank_top_le_of_not_dvd_index hr
      ((C.subgroupOf L).subgroupOf Nrm) (by
        rw [hidx]
        intro h
        have hd : r ∣ 2 := hr.dvd_of_dvd_pow h
        rcases (Nat.dvd_prime Nat.prime_two).1 hd with h1 | h2
        · exact hr.ne_one h1
        · exact hr2 h2)
  have h1 : CFSG.Open.pRank r ((C.subgroupOf L).subgroupOf Nrm) = CFSG.Open.pRank r C := by
    calc CFSG.Open.pRank r ((C.subgroupOf L).subgroupOf Nrm)
        = CFSG.Open.pRank r (⊤ : Subgroup ↥((C.subgroupOf L).subgroupOf Nrm)) :=
          CFSG.SectionRank.pRank_eq_pRank_top_subgroup _
      _ = CFSG.Open.pRank r (⊤ : Subgroup ↥C) :=
          CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.one_lt
            ((Subgroup.subgroupOfEquivOfLe hCle).trans (Subgroup.subgroupOfEquivOfLe hCL))
      _ = CFSG.Open.pRank r C := (CFSG.SectionRank.pRank_eq_pRank_top_subgroup C).symm
  have h2 : CFSG.Open.pRank r (⊤ : Subgroup
        (TauCeti.Subgroup.normalizerQuotient N)) =
      CFSG.Open.pRank r (⊤ : Subgroup ↥Nrm) := by
    exact CFSG.SectionRank.pRank_quotient_eq (N.subgroupOf Nrm) (by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show N ≤ Nrm from
        Subgroup.le_normalizer)).toEquiv]
      exact hcardN)
  rw [h2]
  exact htransfer.trans (le_of_eq h1)

theorem pRank_conjSubgroup_eq {C : Subgroup G} {g : G} {r : ℕ} (hr : r.Prime) :
    CFSG.Open.pRank r (CFSG.Quasithin.conjSubgroup C g) = CFSG.Open.pRank r C := by
  rw [CFSG.Quasithin.conjSubgroup]
  exact CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.Coords.pRank_map_conj
    hr.one_lt g⁻¹ C

theorem pRank_cartan_le_pRank_Dc {D : Data G} {V₀ V L X : Subgroup G} {p n l : ℕ}
    {C Dc : Subgroup G} {Gamma : Set G} (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma)
    {r : ℕ} (hr : r.Prime) : CFSG.Open.pRank r C ≤ CFSG.Open.pRank r Dc := by
  obtain ⟨γ, ⟨hγ, hmem⟩, huniq⟩ := ctx.reps.2 1 (Subgroup.one_mem _)
  have hγΓ : γ ∈ Gamma := hγ
  have hle : CFSG.Quasithin.conjSubgroup C γ ≤ Dc := by
    rw [ctx.Dc_eq]
    exact le_iSup₂_of_le γ hγΓ le_rfl
  calc CFSG.Open.pRank r C = CFSG.Open.pRank r (CFSG.Quasithin.conjSubgroup C γ) :=
        (pRank_conjSubgroup_eq hr).symm
    _ ≤ CFSG.Open.pRank r Dc := CFSG.SectionRank.pRank_mono hr.one_lt hle

theorem isSylowTwoOf_sylowBar2 {D : Data G} {L : Subgroup G} (hL : L ∈ calC D.M) :
    CFSG.QuasithinUnique.IsSylowTwoOf
      (((D.T ⊓ L).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) ⊤ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22r_fo_sylow_inf
    (K := D.M) (H := L) D.sylowM hL.1
  have hQeq : (Q : Subgroup ↥L) = (D.T ⊓ L).subgroupOf L :=
    Subgroup.map_injective L.subtype_injective (by
      rw [hQ, Subgroup.map_subgroupOf_eq_of_le inf_le_right])
  let Q' : Sylow 2 (Bar2 L) := Q.mapSurjective (QuotientGroup.mk'_surjective _)
  have hcoe : (Q' : Subgroup (Bar2 L)) =
      ((D.T ⊓ L).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := by
    rw [Sylow.coe_mapSurjective, hQeq]
  refine ⟨le_top, ?_, ?_⟩
  · rw [← hcoe]
    exact Q'.isPGroup'
  · rw [← hcoe]
    rw [← Subgroup.relIndex_top_right (((Q' : Subgroup (Bar2 L)).subgroupOf ⊤)),
      ← Subgroup.subgroupOf_self (H := (⊤ : Subgroup (Bar2 L))),
      Subgroup.relIndex_subgroupOf (le_refl (⊤ : Subgroup (Bar2 L))),
      Subgroup.relIndex_top_right]
    exact Q'.not_dvd_index

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17