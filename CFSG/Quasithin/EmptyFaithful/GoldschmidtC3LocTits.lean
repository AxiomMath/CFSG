module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtC3LocAsm
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtCMaxMBound
public import CFSG.Quasithin.Recognition.CertTitsOvergroup
public import CFSG.Sporadic.Schreier.TitsQTStrong
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsTits

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Sporadic.Schreier.Tits CFSG.QuasithinUnique.Setup.X6 CFSG.QuasithinUnique.Setup.X6.TitsLat
open CFSG.QuasithinUnique.Vol2Native.L239.Lie (ParabolicFacts)

namespace GoldC3

section Tits


theorem tits_normalizer_le :
    Subgroup.normalizer (titsFlagStab : Set ↥titsD) ≤ titsFlagStab := by
  have h := titsSD_normalizer_le
  rw [titsSD_eq_flagStab] at h
  exact h

theorem tits_sylow_eq : (titsSylow : Subgroup ↥titsD) = titsFlagStab :=
  coe_titsSylow.trans titsSD_eq_flagStab

theorem tits_center_eq {w : ↥titsD} (hw : w ∈ centerOf titsFlagStab) :
    w = 1 ∨ w = CFSG.Sporadic.Schreier.TitsQT.titsZD := by
  refine CFSG.Sporadic.Schreier.TitsQT.titsSylow_central_eq w ?_ fun p hp => ?_
  · rw [tits_sylow_eq]
    exact hw.1
  · rw [tits_sylow_eq] at hp
    exact Subgroup.mem_centralizer_iff.1 hw.2 p hp

theorem tits_zD_mem : CFSG.Sporadic.Schreier.TitsQT.titsZD ∈ centerOf titsFlagStab := by
  have hS : ∀ p : ↥titsD, p ∈ titsFlagStab → (p : Equiv.Perm (Fin 1755)) ∈ titsS := fun p hp => by
    rw [← titsSD_eq_flagStab] at hp
    exact Subgroup.mem_subgroupOf.1 hp
  refine ⟨?_, Subgroup.mem_centralizer_iff.2 fun p hp => ?_⟩
  · rw [← titsSD_eq_flagStab]
    exact Subgroup.mem_subgroupOf.2 titsZ_mem_titsS
  · have hz : titsZ ∈
        ((Subgroup.center titsS).map titsS.subtype : Set (Equiv.Perm (Fin 1755))) := by
      rw [titsS_center]
      exact Or.inr rfl
    obtain ⟨c, hc, hcz⟩ := hz
    have h1 := Subgroup.mem_center_iff.1 hc ⟨_, hS p hp⟩
    have h2 : (p : Equiv.Perm (Fin 1755)) * titsZ = titsZ * p := by
      rw [← hcz]
      exact congrArg Subtype.val h1
    exact Subtype.ext h2

theorem tits_H_le_C :
    titsPointStab ≤ Subgroup.centralizer (centerOf titsFlagStab : Set ↥titsD) := by
  intro h hh
  refine Subgroup.mem_centralizer_iff.2 fun w hw => ?_
  rcases tits_center_eq hw with rfl | rfl
  · simp
  · have hhH : (h : Equiv.Perm (Fin 1755)) ∈ titsH := by
      rw [titsH_eq_stab]
      exact ⟨h, hh, rfl⟩
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (titsH_le_centralizer_z hhH)).symm

theorem tits_C_ne_top : Subgroup.centralizer (centerOf titsFlagStab : Set ↥titsD) ≠ ⊤ := by
  intro htop
  have hcen : CFSG.Sporadic.Schreier.TitsQT.titsZD ∈ Subgroup.center ↥titsD := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ Subgroup.centralizer (centerOf titsFlagStab : Set ↥titsD) :=
      htop ▸ Subgroup.mem_top g
    exact (Subgroup.mem_centralizer_iff.1 hg _ tits_zD_mem).symm
  rw [titsD_center, Subgroup.mem_bot] at hcen
  exact titsZ_ne_one (congrArg Subtype.val hcen)

theorem c3Facts_tits : C3Facts ↥titsD titsFlagStab titsLineStab where
  le := titsFlagStab_le_line
  card := by rw [card_titsLineStab, card_titsFlagStab]
  not_normal := fun h => by
    have := Subgroup.card_le_of_le (h.trans tits_normalizer_le)
    rw [card_titsLineStab, card_titsFlagStab] at this
    omega
  not_centralizes := fun h => tits_C_ne_top (top_le_iff.1 (by
    rw [← generation_of_overgroup_lattice card_titsPointStab card_titsLineStab
      titsFlagStab_le_point card_titsFlagStab tits_overgroups]
    exact sup_le tits_H_le_C h))
  maximal := by
    rw [sup_eq_left.2 (tits_normalizer_le.trans titsFlagStab_le_line)]
    refine isMaxSubgroupIn_of_overgroup_bound (B := 6144)
      (ne_top_of_card card_titsPointStab card_titsLineStab).2 (by rw [card_titsLineStab])
      fun Y hY => ?_
    rcases tits_overgroups Y (titsFlagStab_le_line.trans hY) with rfl | rfl | rfl | rfl
    · right
      rw [card_titsFlagStab]
      norm_num
    · exfalso
      have := Subgroup.card_dvd_of_le hY
      rw [card_titsLineStab, card_titsPointStab] at this
      omega
    · right
      rw [card_titsLineStab]
    · left
      rfl
  blockFree := Or.inl ⟨titsK.subgroupOf titsD, by
    refine ParabolicFacts.of_map titsD.subtype titsD.subtype_injective ?_
    rw [← titsN_eq_stab, subgroupOf_map_titsD titsK_le_titsD]
    exact CFSG.QuasithinUnique.Vol2Native.L239.Lie.TitsPairs.parabolicFacts_titsN⟩
  inv := fun α hα => (invariant_of_overgroup_lattice card_titsFlagStab card_titsPointStab
    card_titsLineStab titsFlagStab_le_point titsFlagStab_le_line tits_overgroups hα).2
  cent := tits_normalizer_le.trans (le_centralizer_centerOf _)
  norm := Or.inl tits_normalizer_le

theorem threeCLocConcl_tits {G : Type} [Group G] [Finite G] {L S : Subgroup G}
    (hL : IsTits ↥L) (hS2 : IsPGroup 2 S) (hSN : S ≤ Subgroup.normalizer (L : Set G))
    (hSyl : IsSylowTwoOf (S ⊓ L) L) : ThreeCLocConcl G L S := by
  obtain ⟨e⟩ := titsModelEquiv ↥L 2 1 hL
  exact threeCLocConcl_of_hasC3Data e isSylowTwoOf_flagStab ⟨_, c3Facts_tits⟩ hS2 hSN hSyl

end Tits

end GoldC3

end CFSG.Quasithin
