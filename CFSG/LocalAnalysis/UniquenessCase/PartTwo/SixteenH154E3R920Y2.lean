module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3R920Cfg
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3R920Comm
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F09 (calY2_9)
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace R920Cfg

variable {D : Data G} {L D₃ A : Subgroup G}

private theorem r920y2_conj_mem_of_mem (H : Subgroup G) {h x : G} (hh : h ∈ H) (hx : x ∈ H) :
    MulAut.conj h x ∈ H := by
  rw [MulAut.conj_apply]
  exact H.mul_mem (H.mul_mem hh hx) (H.inv_mem hh)

private theorem r920y2_map_conj_one (H : Subgroup G) :
    H.map (MulAut.conj (1 : G)).toMonoidHom = H := by
  rw [show MulAut.conj (1 : G) = 1 from map_one MulAut.conj]
  exact Subgroup.map_id H

theorem mem_calY2_9 (c : R920Cfg D L D₃ A) (h61 : UC6.R6_1 D) (h3 : 3 ∈ D.sig)
    (hex : ∃ N : Subgroup G, rankThreeIsMaxTwoLocal N ∧ L ≤ N ∧ N ≠ D.M) : L ∈ calY2_9 D := by
  have hO : Opp 3 L = L := c.opp_eq
  obtain ⟨N, hN, hLN, hNM⟩ := hex
  haveI : IsSimpleGroup G := D.standing.simple
  have hY9 : L ∈ F09.calY9 D := by
    refine ⟨c.le_M, ?_, ?_⟩
    ·
      have hNtop : N ≠ ⊤ :=
        CFSG.RankThreeCoreUniqueness.Helpers.twoLocal_ne_top D.standing.nonab N hN.1
      obtain ⟨N', hN'coat, hNN'⟩ := (IsCoatomic.eq_top_or_exists_le_coatom N).resolve_left hNtop
      have hN'mem : N' ∈ calNOf L := ⟨hN'coat, hLN.trans hNN'⟩
      intro hEq
      have hN'DM : N' = D.M := by
        have h1 := hN'mem
        rw [hEq] at h1
        simpa using h1
      exact hNM ((hN.2 D.M D.maxLocal.1 (hN'DM ▸ hNN')).symm)
    · intro E hEL hE
      exact c.mem_uniqueSet_of_card_three hEL hE
  have hMOf : calMOf L ≠ {D.M} := by
    intro hEq
    have hmem : N ∈ ({D.M} : Set (Subgroup G)) := by
      rw [← hEq]
      exact ⟨hN, hLN⟩
    exact hNM (Set.mem_singleton_iff.mp hmem)
  have hsub : calMOf L ⊆ F09.calH9 D L ∪ {D.M} := by
    intro N'' hN''
    rcases hN'' with ⟨hN''max, hL_N''⟩
    by_cases hN''M : N'' = D.M
    · rw [Set.mem_union]
      exact Or.inr (Set.mem_singleton_iff.mpr hN''M)
    · rw [Set.mem_union]
      refine Or.inl ⟨hL_N'', ?_, ?_⟩
      · intro hle
        exact hN''M ((hN''max.2 D.M D.maxLocal.1 hle).symm)
      · rw [hO]
        apply le_antisymm
        · calc CFSG.Open.pRank 3 (⨆ h : ↥N'', L.map (MulAut.conj (h : G)).toMonoidHom)
              ≤ CFSG.Open.pRank 3 N'' :=
                CFSG.RankThreeCoreUniqueness.Helpers.pRank_mono 3 (by norm_num) (by
                  apply iSup_le
                  intro h
                  refine Subgroup.map_le_iff_le_comap.mpr ?_
                  intro x hx
                  exact r920y2_conj_mem_of_mem N'' h.2 (hL_N'' hx))
            _ ≤ 1 := c.pRank_le_one_of_maxTwoLocal h61 h3 hN''max hL_N'' hN''M
        ·
          haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
          have hLle : L ≤ ⨆ h : ↥N'', L.map (MulAut.conj (h : G)).toMonoidHom := by
            have h1 : L.map (MulAut.conj ((1 : ↥N'') : G)).toMonoidHom = L := by
              simpa using r920y2_map_conj_one L
            exact (le_of_eq h1.symm).trans
              (le_iSup (fun h : ↥N'' => L.map (MulAut.conj (h : G)).toMonoidHom) 1)
          have hdvd : 3 ∣ Nat.card D₃ := by
            rw [c.D₃_card]
          obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥D₃) 3 hdvd
          have hxG : orderOf ((x : ↥D₃) : G) = 3 := by
            rw [Subgroup.orderOf_coe, hx]
          have hxG3 : ((x : ↥D₃) : G) ^ 3 = 1 := by
            rw [← hxG]
            exact pow_orderOf_eq_one _
          have hzx : CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers ((x : ↥D₃) : G)) :=
            CFSG.Open.isElemAbelian_zpowers hxG3
          have hzxcard : Nat.card (Subgroup.zpowers ((x : ↥D₃) : G)) = 3 ^ 1 := by
            rw [Nat.card_zpowers, hxG, pow_one]
          exact CFSG.SectionRank.le_pRank Nat.prime_three.one_lt
            ((Subgroup.zpowers_le.mpr (c.D₃_le x.2)).trans hLle) hzx hzxcard
  have hcomm : ∀ A ∈ F09.Inv9' D.M L 3, ⁅A, Opp 3 L⁆ ≤ pCoreOf 2 A := by
    intro A hA
    rw [hO]
    exact commutator_le_pCoreOf_of_mem_inv9' c.mem c.isL2 hA
  have hidx : ∃ k : ℕ, ((Opp 3 L).subgroupOf L).index = 2 ^ k := by
    refine ⟨0, ?_⟩
    simp [hO]
  exact ⟨hY9, hMOf, hsub, hcomm, hidx⟩

end R920Cfg

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
