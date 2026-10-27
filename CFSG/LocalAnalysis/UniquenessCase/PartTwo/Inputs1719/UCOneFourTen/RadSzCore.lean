module

import CFSG.GroupTheory.PGroup.LtInfNormalizer
import CFSG.ClassicalGroups.PCoreSection
import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem516
import CFSG.Quasithin.Vol2.F134Orders
import CFSG.RankThree.PartTwo.Sec16.Item166Proof
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem isSz_facts {B : Type} [Group B] {n : ℕ} (h : IsSz B n) :
    IsSimpleGroup B ∧ Odd n ∧ 3 ≤ n ∧
      Nat.card B = (2 ^ n) ^ 2 * (2 ^ n - 1) * ((2 ^ n) ^ 2 + 1) ∧
      2 ∣ Nat.card B ∧ ¬ 3 ∣ Nat.card B ∧ 5 ∣ Nat.card B := by
  unfold IsSz at h
  rcases h with ⟨hcl, -⟩ | ⟨-, hce, -⟩ | ⟨-, hree, -⟩ | ⟨-, -, hsz⟩
  · exact absurd hcl (by decide)
  · exact absurd hce (by decide)
  · exact absurd hree (by decide)
  · obtain ⟨a, ha, hn, hcard⟩ := CFSG.Quasithin.H13.card_of_suzukiModel hsz
    obtain ⟨h5, -⟩ := CFSG.Quasithin.H13.five_dvd_card_of_suzukiModel hsz
    refine ⟨CFSG.RankThree.PartTwo.Sec16.isSimpleGroup_of_suzukiModel hsz, ?_, ?_, hcard,
      ?_, CFSG.Quasithin.F134.not_three_dvd_card_of_suzukiModel hsz, h5⟩
    · exact ⟨a, hn⟩
    · omega
    · rw [hcard]
      have h2 : 2 ∣ (2 ^ n) ^ 2 := by
        rw [← pow_mul]
        exact dvd_pow_self 2 (by omega : n * 2 ≠ 0)
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h2 _) _

variable {S : Type} [Group S] [Finite S]

theorem exists_sylow_normalizer_le_of_radical (hBT : CFSG.LieType.BorelTits.Holds S 2)
    {U : Subgroup S} (hU : U ≠ ⊥) (hrad : CFSG.Open.pCoreOf 2 (normalizer (U : Set S)) = U) :
    ∃ T : Sylow 2 S, normalizer ((T : Subgroup S) : Set S) ≤ normalizer (U : Set S) := by
  have hUp : IsPGroup 2 U := by
    rw [← hrad]
    exact CFSG.ClassicalGroups.PCoreSection.isPGroup_pCoreOf 2 _
  obtain ⟨T, Q, -, hPQ, -, hUQ, hTQ⟩ := hBT U hU hUp
  let V : Subgroup S := CFSG.Open.pCoreOf 2 Q
  have hUV : U ≤ V := hUQ
  have hVp : IsPGroup 2 V := CFSG.ClassicalGroups.PCoreSection.isPGroup_pCoreOf 2 Q
  have hVU : V = U := by
    refine le_antisymm ?_ hUV
    by_contra hVnle
    have hltUV : U < V := lt_of_le_of_ne hUV (fun h => hVnle (le_of_eq h.symm))
    have hVnil : Group.IsNilpotent ↥V := hVp.isNilpotent
    have hlt : U < V ⊓ normalizer (U : Set S) :=
      @CFSG.GroupTheory.lt_inf_normalizer_of_isNilpotent S _ V U hVnil hltUV
    obtain ⟨w, hwV, hwU⟩ := SetLike.exists_of_lt hlt
    have hWleP : V ⊓ normalizer (U : Set S) ≤ normalizer (U : Set S) := inf_le_right
    have hWnorm : ∀ x ∈ normalizer (U : Set S), ∀ y ∈ V ⊓ normalizer (U : Set S),
        x * y * x⁻¹ ∈ V ⊓ normalizer (U : Set S) := by
      intro x hx y hy
      refine ⟨CFSG.ClassicalGroups.PCoreSection.conj_mem_pCoreOf (hPQ hx) hy.1, ?_⟩
      exact (normalizer (U : Set S)).mul_mem
        ((normalizer (U : Set S)).mul_mem hx hy.2)
        ((normalizer (U : Set S)).inv_mem hx)
    have hWp : IsPGroup 2 ↥(V ⊓ normalizer (U : Set S)) :=
      hVp.to_le (inf_le_left : V ⊓ normalizer (U : Set S) ≤ V)
    have hWcore : V ⊓ normalizer (U : Set S) ≤
        CFSG.Open.pCoreOf 2 (normalizer (U : Set S)) :=
      CFSG.ClassicalGroups.PCoreSection.le_pCoreOf hWleP hWnorm hWp
    rw [hrad] at hWcore
    exact hwU (hWcore ⟨hwV.1, hwV.2⟩)
  have hQle : Q ≤ normalizer (U : Set S) := by
    rw [← hVU]
    exact Subgroup.le_normalizer_iff.mpr fun x hx y hy =>
      CFSG.ClassicalGroups.PCoreSection.conj_mem_pCoreOf hx hy
  exact ⟨T, hTQ.trans hQle⟩

theorem normalizer_ne_top_of_isComponentOf (hS : IsSimpleGroup S) {U : Subgroup S} (hU : U ≠ ⊥)
    (hrad : CFSG.Open.pCoreOf 2 (normalizer (U : Set S)) = U)
    {B : Subgroup (↥(normalizer (U : Set S)) ⧸ CFSG.pCore 2 ↥(normalizer (U : Set S)))}
    (hB : CFSG.Open.IsComponentOf B ⊤) : normalizer (U : Set S) ≠ ⊤ := by
  intro htop
  let P : Subgroup S := normalizer (U : Set S)
  let G := ↥P
  have hradP : CFSG.Open.pCoreOf 2 P = U := hrad
  have hUnorm : U.Normal := (Subgroup.normalizer_eq_top_iff).mp htop
  have hUtop : U = ⊤ :=
    (@IsSimpleGroup.eq_bot_or_eq_top_of_normal S _ hS U hUnorm).resolve_left hU
  have hNtop : CFSG.pCore 2 G = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : (x : S) ∈ CFSG.Open.pCoreOf 2 P := by
      rw [hradP, hUtop]
      exact Subgroup.mem_top _
    unfold CFSG.Open.pCoreOf at hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, hyx⟩
    have hyx' : y = x := Subtype.ext hyx
    rw [hyx'] at hy
    exact hy
  have hquot : Subsingleton (G ⧸ CFSG.pCore 2 G) := by
    rw [QuotientGroup.subsingleton_iff, hNtop]
  have hBsub : Subsingleton ↥B :=
    ⟨fun a b => Subtype.ext
      (@Subsingleton.elim (G ⧸ CFSG.pCore 2 G) hquot (a : G ⧸ CFSG.pCore 2 G)
        (b : G ⧸ CFSG.pCore 2 G))⟩
  have hBnt : Nontrivial ↥B := by
    have hfin : Finite ↥B := inferInstance
    have hqfin : Finite (↥B ⧸ Subgroup.center ↥B) :=
      Finite.of_surjective (QuotientGroup.mk' (Subgroup.center ↥B))
        (QuotientGroup.mk'_surjective (Subgroup.center ↥B))
    have h1 : 1 < Nat.card (↥B ⧸ Subgroup.center ↥B) :=
      @Finite.one_lt_card _ hqfin hB.2.2.2.toNontrivial
    have hle : Nat.card (↥B ⧸ Subgroup.center ↥B) ≤ Nat.card ↥B :=
      Nat.le_of_dvd (@Nat.card_pos ↥B ⟨1⟩ hfin) (Subgroup.card_quotient_dvd_card _)
    exact (@Finite.one_lt_card_iff_nontrivial ↥B hfin).mp (lt_of_lt_of_le h1 hle)
  exact (not_nontrivial_iff_subsingleton.mpr hBsub) hBnt

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410
