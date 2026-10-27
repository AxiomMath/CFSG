module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs
import CFSG.LocalAnalysis.StandardType.GGNSJoinJA2AAuxCover
import CFSG.LocalAnalysis.StandardType.GGNSJoinJA2AAuxRank
import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompSUComp
import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompSUModel
import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitSU
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosRankAux2
import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.SectionRank.OddCover (diagHom)

theorem nsJA2_exists_pair_of_card_le_two {α : Type*} [DecidableEq α] [Nontrivial α]
    {s : Finset α} {i : α} (hi : i ∈ s) (hcard : s.card ≤ 2) :
    ∃ a b : α, a ≠ b ∧ s ⊆ {a, b} := by
  classical
  obtain ⟨j, hj⟩ := exists_ne i
  have hcard' : (s.erase i).card ≤ 1 := by
    have := Finset.card_erase_add_one hi
    omega
  obtain ⟨b, hbsub⟩ := Finset.card_le_one_iff_subset_singleton.mp hcard'
  by_cases hbi : b = i
  · refine ⟨i, j, hj.symm, fun x hx => ?_⟩
    by_cases hxi : x = i
    · simp [hxi]
    · have hxe : x ∈ s.erase i := Finset.mem_erase.mpr ⟨hxi, hx⟩
      have hxb : x = b := Finset.mem_singleton.mp (hbsub hxe)
      exact absurd (hxb.trans hbi) hxi
  · refine ⟨i, b, fun h => hbi h.symm, fun x hx => ?_⟩
    rw [Finset.mem_insert, Finset.mem_singleton]
    by_cases hxi : x = i
    · exact Or.inl hxi
    · exact Or.inr (Finset.mem_singleton.mp (hbsub (Finset.mem_erase.mpr ⟨hxi, hx⟩)))

theorem nsJA2_eq_of_blockSU_of_card_three_le
    {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K] [CharP K 2]
    {f m : ℕ} {ψ : ↥(unitarySU 2 f K (m + 1)) →* G} {S : Set G}
    {δ : G → Fin (m + 1) → Kˣ} {J : Subgroup G} {i : Fin (m + 1)}
    (hufd : UnitaryFieldData 2 f K)
    (hker : ψ.ker ≤ Subgroup.center ↥(unitarySU 2 f K (m + 1)))
    (hδ : ∀ e ∈ S, (e, diagHom (m + 1) (δ e)) ∈ SUTorus.suPairs ψ)
    (hJ : CFSG.Assembly.IsComponentOf J (ψ.range ⊓ Subgroup.centralizer S))
    (hiJ : J ≤ (TableBUE.blockSU (K := K) (n := f)
      (LinTorus.diagClass S δ i)).map ψ)
    (hV : 3 ≤ (LinTorus.diagClass S δ i).card)
    (hVq : ((LinTorus.diagClass S δ i).card, 2 ^ f) ≠ (3, 2)) :
    J = (TableBUE.blockSU (K := K) (n := f) (LinTorus.diagClass S δ i)).map ψ := by
  classical
  let P : Finset (Fin (m + 1)) := LinTorus.diagClass S δ i
  let Y : Subgroup G := (TableBUE.blockSU (K := K) (n := f) P).map ψ
  have hiJ' : J ≤ Y := hiJ
  have hYleC : Y ≤ Subgroup.centralizer S := by
    have hcen : ∀ e ∈ S, e ∈ Subgroup.centralizer (Y : Set G) := by
      intro e he
      have hc := SUTorus.mem_centralizer_map_blockSU (ψ := ψ) (I := P) (hδ e he)
        (fun j hj k hk => LinTorus.eq_of_mem_diagClass hj hk he)
      simpa [Y] using hc
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact ((Subgroup.mem_centralizer_iff.mp (hcen e he)) y hy).symm
  have hYle : Y ≤ ψ.range ⊓ Subgroup.centralizer S :=
    le_inf (Subgroup.map_le_range (f := ψ) (TableBUE.blockSU (K := K) (n := f) P)) hYleC
  have hYsub : CFSG.Assembly.IsSubnormal Y (ψ.range ⊓ Subgroup.centralizer S) := by
    have hc := SUTorus.isSubnormal_map_blockSU (ψ := ψ) hker hδ i
    simpa [P, Y] using hc
  have hYq : CFSG.Assembly.IsQuasisimple ↥Y := by
    have hc := SUTorus.isQuasisimple_map_blockSU (ψ := ψ) hufd hker (V := P) hV hVq
    simpa [Y] using hc
  have hYcomp : CFSG.Assembly.IsComponentOf Y (ψ.range ⊓ Subgroup.centralizer S) :=
    ⟨hYle, hYsub, hYq⟩
  have hEq : J = Y := eq_of_isComponentOf_le hJ hYcomp hiJ'
  simpa [P, Y] using hEq

theorem nsJA2_false_of_solvable_blockSU_two_one
    {G : Type} [Group G] {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    {ψ : ↥(unitarySU 2 1 K n) →* G} {S : Finset (Fin n)} {J : Subgroup G}
    (hufd : UnitaryFieldData 2 1 K) (hS1 : 1 ≤ S.card) (hS : S.card ≤ 3)
    (hJq : CFSG.Assembly.IsQuasisimple ↥J)
    (hiJ : J ≤ (TableBUE.blockSU (K := K) (n := 1) S).map ψ) : False := by
  haveI : Group.IsSolvable ↥((TableBUE.blockSU (K := K) (n := 1) S).map ψ) :=
    WitSU.isSolvable_map_blockSU_two_one hufd ψ hS1 hS
  have hJsolv : Group.IsSolvable ↥J :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hiJ)
  haveI : IsSimpleGroup (↥J ⧸ Subgroup.center ↥J) := hJq.2
  haveI : Nontrivial ↥J := by
    haveI : Nontrivial (↥J ⧸ Subgroup.center ↥J) := IsSimpleGroup.toNontrivial
    exact Function.Surjective.nontrivial
      (QuotientGroup.mk'_surjective (Subgroup.center ↥J))
  haveI : Group.IsPerfect ↥J := Group.IsPerfect.mk hJq.1
  exact (Group.IsPerfect.not_isSolvable (G := ↥J) hJsolv).elim

theorem nsJA2_exists_triple
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ} {ψ : Su K 2 f n →* G}
    (h : GGNSLocalHyp p B Bs K f n ψ) (hd : GGActsDiagonally (p := 2) (f := f) ψ Bs)
    (hrange : ψ.range = L) :
    ∃ a b c : Fin n, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
      (ggSuPairBlock K 2 f n a b).map ψ ≤ J ∧ (ggSuPairBlock K 2 f n b c).map ψ ≤ J := by
  classical
  have hDleBs : D ≤ Bs := hcfg.1.1.2.2.1.1.trans hcfg.1.1.2.1.1
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := h.four_le; omega⟩
  have hm : 2 < m + 1 := by have := h.four_le; omega
  have hufd : UnitaryFieldData 2 f K := ggNSPosPC_ufd h
  let ψ' : ↥(unitarySU 2 f K (m + 1)) →* G := nsJA2Cover h.card ψ
  let δwit : (e : G) → e ∈ Bs → Fin (m + 1) → Kˣ := fun e he =>
    Classical.choose (nsJA2Cover_mem_suPairs h.card
      (Classical.choose_spec (hd e he)).1 (Classical.choose_spec (hd e he)).2)
  let δ : G → Fin (m + 1) → Kˣ := fun e => if he : e ∈ Bs then δwit e he else 1
  have hδ : ∀ e ∈ (D : Set G), (e, diagHom (m + 1) (δ e)) ∈ SUTorus.suPairs ψ' := by
    intro e he
    have heB : e ∈ Bs := hDleBs he
    have hδe : δ e = δwit e heB := by
      simp only [δ]
      exact dif_pos heB
    rw [hδe]
    exact Classical.choose_spec (nsJA2Cover_mem_suPairs h.card
      (Classical.choose_spec (hd e heB)).1 (Classical.choose_spec (hd e heB)).2)
  have hcomp0 : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hcfg.1.1.2.2.1.2.2.2.2.2.1
  have hJcomp : IsComponentOf J (ψ'.range ⊓ Subgroup.centralizer (D : Set G)) := by
    simpa [ψ', nsJA2Cover_range h.card ψ, hrange] using hcomp0
  obtain ⟨i, hiJ⟩ := SUTorus.exists_le_map_blockSU (m := m) hufd h.prime h.dvd
    (nsJA2Cover_ker_le h.card h.ker) hδ hJcomp
  let P : Finset (Fin (m + 1)) := LinTorus.diagClass (D : Set G) δ i
  let Y : Subgroup G := (TableBUE.blockSU (K := K) (n := f) P).map ψ'
  have hiJ' : J ≤ Y := hiJ
  have hmem : i ∈ P := LinTorus.self_mem_diagClass (D : Set G) δ i
  by_cases hP2 : P.card ≤ 2
  · haveI : Nontrivial (Fin (m + 1)) := Fin.nontrivial_iff_two_le.mpr (by omega)
    obtain ⟨a, b, hab, hPsub⟩ := nsJA2_exists_pair_of_card_le_two hmem hP2
    have hYpair : Y ≤ (ggSuPairBlock K 2 f (m + 1) a b).map ψ := by
      simpa [Y, ψ'] using nsJA2Cover_map_blockSU_le_pairBlock h.card ψ hPsub
    exact (nsJA2_false_of_le_pairBlock hcfg h hd hab (hiJ'.trans hYpair)).elim
  · have h3 : 3 ≤ P.card := by omega
    by_cases hs : P.card = 3 ∧ 2 ^ f = 2
    · obtain ⟨hP3, hf2⟩ := hs
      have hf1 : f = 1 := (Nat.pow_eq_self_iff (by norm_num)).mp hf2
      subst f
      exact (nsJA2_false_of_solvable_blockSU_two_one (S := P) (J := J) hufd
        (by omega) (by omega) hJcomp.2.2 hiJ').elim
    · have hV : 3 ≤ P.card := h3
      have hVq : (P.card, 2 ^ f) ≠ (3, 2) := by
        intro hEq
        exact hs ⟨congrArg Prod.fst hEq, congrArg Prod.snd hEq⟩
      have hker : ψ'.ker ≤ Subgroup.center ↥(unitarySU 2 f K (m + 1)) :=
        nsJA2Cover_ker_le h.card h.ker
      have hJeqY : J = Y := by
        have hEq := nsJA2_eq_of_blockSU_of_card_three_le hufd hker hδ hJcomp hiJ' hV hVq
        simpa [P, Y] using hEq
      obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ :=
        Finset.two_lt_card.mp (by omega : 2 < P.card)
      refine ⟨a, b, c, hab, hbc, hac, ?_, ?_⟩
      · rw [hJeqY]
        simpa [Y, ψ'] using nsJA2Cover_map_pairBlock_le h.card ψ ha hb
      · rw [hJeqY]
        simpa [Y, ψ'] using nsJA2Cover_map_pairBlock_le h.card ψ hb hc

end CFSG.StandardType

end
