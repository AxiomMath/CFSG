module

public import CFSG.LocalAnalysis.WeakClosure81.FiveSevenNormal

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem exists_maxOver_eq_singleton_sec5Hyp {H M A : Subgroup G} (h : Sec5Hyp H M A)
    (h1 : (maxOver H A).ncard = 1) : ∃ M₀ : Subgroup G, maxOver H A = {M₀} ∧ Sec5Hyp H M₀ A := by
  obtain ⟨M₀, hM₀⟩ := Set.ncard_eq_one.1 h1
  have hmem : M₀ ∈ maxOver H A := by
    rw [hM₀]
    exact Set.mem_singleton M₀
  obtain ⟨hM₀max, hAM₀⟩ := hmem
  have hlt : M ⊓ H < H :=
    lt_of_le_of_ne inf_le_right fun heq => h.not_le (heq.symm.le.trans inf_le_left)
  obtain ⟨N, hNmax, hNle⟩ := exists_isMaxSubgroupIn hlt
  have hN : N ∈ maxOver H A := ⟨hNmax, (le_inf h.le_M h.le_group).trans hNle⟩
  rw [hM₀, Set.mem_singleton_iff] at hN
  have hMM₀ : M ⊓ H ≤ M₀ := hNle.trans (le_of_eq hN)
  refine ⟨M₀, hM₀, h.isElemAbelian, h.le_group, hAM₀, not_le_of_gt hM₀max.1, ?_⟩
  have hdvd : M₀.relIndex H ∣ M.relIndex H := by
    have := Subgroup.relIndex_dvd_of_le_left H hMM₀
    rwa [Subgroup.inf_relIndex_right] at this
  exact Odd.of_dvd_nat h.odd_relIndex hdvd

theorem fstar_ne_bot_of_mulEquiv_alternatingGroup {H : Subgroup G} {n : ℕ} (hn : 5 ≤ n)
    (e : ↥(Fstar H) ≃* alternatingGroup (Fin n)) : Fstar H ≠ ⊥ := by
  haveI : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by simpa using hn)
  haveI : Nontrivial ↥(Fstar H) := e.symm.injective.nontrivial
  exact (Subgroup.nontrivial_iff_ne_bot _).1 inferInstance

theorem normal_subgroupOf_fstar (H : Subgroup G) : ((Fstar H).subgroupOf H).Normal := by
  refine ⟨fun x hx g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  simpa using conj_mem_fstar g.2 hx

theorem five_seven_reduction {H M A : Subgroup G} {n : ℕ} (hn : 5 ≤ n)
    (e : ↥(Fstar H) ≃* alternatingGroup (Fin n)) (h : Sec5Hyp H M A)
    (h1 : (maxOver H A).ncard = 1) :
    ∃ M₀ : Subgroup G, maxOver H A = {M₀} ∧ Sec5Hyp H M₀ A ∧ kerMOf M₀ H = ⊥ ∧ A ≠ ⊥ ∧
      H = Fstar H ⊔ A := by
  obtain ⟨M₀, hM₀, h₀⟩ := exists_maxOver_eq_singleton_sec5Hyp h h1
  have hker : kerMOf M₀ H = ⊥ := kerMOf_eq_bot_of_fstar_alt hn e h₀ hM₀
  have hAne : A ≠ ⊥ := ne_bot_of_maxOver_eq_singleton hn e hM₀
  have hmin : IsMinNormalOver H (kerMOf M₀ H) (Fstar H) := by
    rw [hker]
    refine ⟨bot_lt_iff_ne_bot.2 (fstar_ne_bot_of_mulEquiv_alternatingGroup hn e),
      fstar_le_group H, normal_subgroupOf_fstar H, fun Z _ hZF hZ => ?_⟩
    rcases eq_bot_or_fstar_le_of_normal hn e (hZF.trans (fstar_le_group H)) hZ with hb | hle
    · exact Or.inl hb
    · exact Or.inr (le_antisymm hZF hle)
  exact ⟨M₀, hM₀, h₀, hker, hAne, five_four_one hM₀ hmin⟩

end CFSG.LocalAnalysis.WeakClosure81
