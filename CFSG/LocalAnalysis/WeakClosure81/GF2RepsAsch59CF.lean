module

public import CFSG.LocalAnalysis.WeakClosure81.W18ASNineCF
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20a
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveA5
public import CFSG.Quasithin.H13.GoldschmidtM22CaseBS5
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Quasithin.Vol2.Ch8Sec2L829LN1

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch59

open Equiv CFSG.Quasithin

theorem pRank_top_le_two_of_quotient_subgroup_permFive {Y : Type} [Group Y] [Finite Y]
    (f : Y →* Perm (Fin 5)) (hf : Function.Injective f) (M N : Subgroup Y)
    [(N.subgroupOf M).Normal] :
    CFSG.Open.pRank 2 (⊤ : Subgroup (↥M ⧸ N.subgroupOf M)) ≤ 2 := by
  classical
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.SectionRank.pRank_le (by norm_num) ?_
  intro E _ hEea
  let π : ↥M →* (↥M ⧸ N.subgroupOf M) := QuotientGroup.mk' (N.subgroupOf M)
  let P : Subgroup ↥M := E.comap π
  have hmapP : P.map π = E := by
    show (E.comap π).map π = E
    rw [Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
  let πP : ↥P →* ↥E := (π.comp P.subtype).codRestrict E fun p => by
    have hp : π (p : ↥M) ∈ P.map π := Subgroup.mem_map_of_mem π p.2
    rwa [hmapP] at hp
  have hπP : Function.Surjective πP := by
    intro e
    have he : (e : ↥M ⧸ N.subgroupOf M) ∈ P.map π := by rw [hmapP]; exact e.2
    obtain ⟨p, hp, hpe⟩ := Subgroup.mem_map.mp he
    exact ⟨⟨p, hp⟩, Subtype.ext hpe⟩
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 ↥P))
  let Q : Sylow 2 ↥E := S.mapSurjective (f := πP) hπP
  have hEtop : IsPGroup 2 (⊤ : Subgroup ↥E) :=
    hEea.isPGroup.of_injective (⊤ : Subgroup ↥E).subtype Subtype.val_injective
  have hQtop : (Q : Subgroup ↥E) = ⊤ :=
    (Q.is_maximal' (Q := ⊤) hEtop le_top).symm
  have hQcoe : (Q : Subgroup ↥E) = (S : Subgroup ↥P).map πP :=
    Sylow.coe_mapSurjective hπP S
  have hSmap : (S : Subgroup ↥P).map πP = ⊤ := by rw [← hQcoe, hQtop]
  have hEcard_dvd : Nat.card ↥E ∣ Nat.card (S : Subgroup ↥P) := by
    have hEcard : Nat.card ↥E = Nat.card (Q : Subgroup ↥E) := by
      rw [hQtop, Subgroup.card_top]
    rw [hEcard, hQcoe]
    exact Subgroup.card_map_dvd _ _
  let ι : ↥P →* Perm (Fin 5) := f.comp (M.subtype.comp P.subtype)
  have hι : Function.Injective ι :=
    hf.comp (M.subtype_injective.comp P.subtype_injective)
  let S5 : Subgroup (Perm (Fin 5)) := (S : Subgroup ↥P).map ι
  have hS5card : Nat.card S5 = Nat.card (S : Subgroup ↥P) :=
    Subgroup.card_map_of_injective hι
  have hS5p : IsPGroup 2 S5 := S.isPGroup'.map ι
  have hS_dvd : Nat.card (S : Subgroup ↥P) ∣ 8 := by
    rw [← hS5card]
    exact CFSG.Quasithin.H13.GM22.card_dvd_eight_of_isPGroup S5 hS5p
  have hE_le : Nat.card ↥E ≤ 8 :=
    Nat.le_of_dvd (by norm_num) (hEcard_dvd.trans hS_dvd)
  by_contra hlt
  have hE8 : Nat.card ↥E = 8 := by
    have hE_dvd_8 : Nat.card ↥E ∣ 8 := hEcard_dvd.trans hS_dvd
    have h5 : 5 ≤ Nat.card ↥E := by omega
    interval_cases Nat.card ↥E
    · norm_num at hE_dvd_8
    · norm_num at hE_dvd_8
    · norm_num at hE_dvd_8
    · rfl
  have hS8 : Nat.card (S : Subgroup ↥P) = 8 :=
    (Nat.dvd_antisymm (hE8 ▸ hEcard_dvd) hS_dvd).symm
  have hπSsurj : Function.Surjective (πP.comp (S : Subgroup ↥P).subtype) := by
    intro e
    have he : (e : ↥E) ∈ (S : Subgroup ↥P).map πP := by rw [hSmap]; exact Subgroup.mem_top e
    obtain ⟨s, hs, hse⟩ := Subgroup.mem_map.mp he
    exact ⟨⟨s, hs⟩, hse⟩
  have hbij : Function.Bijective (πP.comp (S : Subgroup ↥P).subtype) :=
    (Nat.bijective_iff_surjective_and_card _).2 ⟨hπSsurj, by rw [hS8, hE8]⟩
  let eS : ↥(S : Subgroup ↥P) ≃* ↥E := MulEquiv.ofBijective _ hbij
  have hSea : CFSG.Open.IsElemAbelian 2 (S : Subgroup ↥P) :=
    CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mpr
      (CFSG.IsElementaryAbelian.of_mulEquiv eS.symm
        (CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp hEea))
  have hS5ea : CFSG.Open.IsElemAbelian 2 S5 := hSea.map ι
  have hS5card8 : Nat.card S5 = 8 := by rw [hS5card, hS8]
  have hle4 := CFSG.ComponentClassification.RankTwoAltFive.card_le_four_of_elemAbelian_perm hS5ea
  omega

theorem isCompositionFactor_comm_or_pRank_two_le_two {X : Type} [Group X] [Finite X]
    (φ : X →* Perm (Fin 5)) (hker : IsPGroup 2 φ.ker) {L : Type} [Group L] [Finite L]
    (hL : E1.IsCompositionFactor X L) :
    (∀ a b : L, a * b = b * a) ∨ CFSG.Open.pRank 2 (⊤ : Subgroup L) ≤ 2 := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases isCompositionFactor_of_normal φ.ker hL with h1 | h2
  · left
    have hnil : Group.IsNilpotent ↥φ.ker := hker.isNilpotent
    have hsolv : Group.IsSolvable ↥φ.ker := IsNilpotent.to_isSolvable
    exact CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20a_abelian_of_compositionFactor
      inferInstance h1
  · right
    have hK : E1.IsCompositionFactor ↥φ.range L :=
      (CFSG.Quasithin.H13.L829N.isCompositionFactor_congr
        (QuotientGroup.quotientKerEquivRange φ)).1 h2
    obtain ⟨N, M, hN, -, -, -, -, ⟨e⟩⟩ := hK
    have hNinst := hN
    have hle := pRank_top_le_two_of_quotient_subgroup_permFive
      φ.range.subtype φ.range.subtype_injective M N
    have heq := CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 2) (by norm_num) e.symm
    rw [heq]
    exact hle

end CFSG.LocalAnalysis.WeakClosure81.Asch59
