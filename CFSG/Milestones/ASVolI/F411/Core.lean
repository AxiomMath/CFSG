module

public import CFSG.Milestones.ASVolI.F4

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF CFSG.Quasithin.F7

theorem burnsideF411_two_paths {V : Type} {Γ : SimpleGraph V}
    (hval : ∀ v a b : V, ∃ w, Γ.Adj v w ∧ w ≠ a ∧ w ≠ b) (u : V) {n : ℕ} (hn : 1 ≤ n) :
    ∃ q₁ : GPath Γ n, q₁ ∈ GPath.nbPaths Γ u n ∧ ∃ q₂ : GPath Γ n, q₂ ∈ GPath.nbPaths Γ u n ∧
      q₁ n ≠ q₂ n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨r, hr⟩ := GPath.exists_nbPaths hval u k
  obtain ⟨w₁, hw₁, hw₁a, -⟩ := hval (r k) (r (k - 1)) (r (k - 1))
  obtain ⟨w₂, hw₂, hw₂a, hw₂b⟩ := hval (r k) (r (k - 1)) w₁
  refine ⟨r.snoc w₁ hw₁, ⟨?_, GPath.noBack_snoc hr.2 hw₁ fun _ => hw₁a⟩,
    r.snoc w₂ hw₂, ⟨?_, GPath.noBack_snoc hr.2 hw₂ fun _ => hw₂a⟩, ?_⟩
  · rw [GPath.snoc_of_le _ _ _ (Nat.zero_le k)]
    exact hr.1
  · rw [GPath.snoc_of_le _ _ _ (Nat.zero_le k)]
    exact hr.1
  · rw [GPath.snoc_last, GPath.snoc_last]
    exact hw₂b.symm

theorem burnsideF411_Qu_ne_bot (h45 : F_4_5) (h46 : F_4_6) (hcompat : NativeChartCompatibilityGoal)
    {κ : GLKind} {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 κ p f Gp M₁ M₂) (hκ : κ.IsLie) (u : (incl M₁ M₂).Γ) :
    Qu p Gp (incl M₁ M₂) u ≠ ⊥ := by
  intro hQ
  have hext : IsLieExtAmalgam M₁ M₂ := ⟨κ, p, f, Gp, hκ, hyp⟩
  have F := h45 κ p f E Gp M₁ M₂ hyp (incl M₁ M₂) rfl
  have h5 := F.2.2.2.2.1 hext
  have h7 := F.2.2.2.2.2.2.1 hext
  have G := h46 κ p f E Gp M₁ M₂ hyp _ (incl M₁ M₂) (incl_faithful M₁ M₂) (incl M₁ M₂) rfl
  have h8 := G.2.2.2.2
  have hthick := burnsideF4a_thick_of_hyp hcompat hyp.toHypF_4_4g
  have hval := burnsideF4a_hval (incl_faithful M₁ M₂) hthick.1 hthick.2
  have hm : 1 ≤ κ.m := by cases κ <;> decide
  obtain ⟨q₁, hq₁, q₂, hq₂, hne⟩ := burnsideF411_two_paths hval u hm
  obtain ⟨g, hgu, hgq⟩ := GPath.trans_le hval (h7 u) 1 κ.m rfl q₁ q₂ hq₁ hq₂
  have hd : (incl M₁ M₂).graph.dist u (q₁ κ.m) = κ.m := (h8 u q₁ hq₁).2.1
  obtain ⟨-, -, -, hcomp⟩ := (h5 u (q₁ κ.m) hd).1
  obtain ⟨q, hq, k, hk, hqk⟩ := hcomp g (MulAction.mem_stabilizer_iff.mpr hgu)
  rw [hQ, Subgroup.mem_bot] at hq
  rw [hq, one_mul] at hqk
  have hfix : g • q₁ κ.m = q₁ κ.m := by
    rw [← hqk]
    exact MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp hk).2
  apply hne
  have : q₂ κ.m = g • q₁ κ.m := by
    rw [← hgq]
    rfl
  rw [this, hfix]

theorem burnsideF411_pCoreOf_ne_bot (h45 : F_4_5) (h46 : F_4_6)
    (hcompat : NativeChartCompatibilityGoal) {κ : GLKind} {p f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : HypF_4_4 κ p f Gp M₁ M₂) (hκ : κ.IsLie) :
    pCoreOf p (Gp ⊓ M₁) ≠ ⊥ ∧ pCoreOf p (Gp ⊓ M₂) ≠ ⊥ := by
  refine ⟨fun h => burnsideF411_Qu_ne_bot h45 h46 hcompat hyp hκ (incl M₁ M₂).xv ?_,
    fun h => burnsideF411_Qu_ne_bot h45 h46 hcompat hyp hκ (incl M₁ M₂).lv ?_⟩
  · have hQx : Qx p Gp (incl M₁ M₂) = ⊥ := by
      unfold Qx
      rw [h, Subgroup.bot_subgroupOf]
      exact Subgroup.map_bot _
    unfold Qu RankTwoAmalgam.Completion.Qvert
    refine le_bot_iff.mp (iSup₂_le fun g _ => ?_)
    show conjSub g (Qx p Gp (incl M₁ M₂)) ≤ ⊥
    rw [hQx]
    unfold conjSub
    rw [Subgroup.map_bot]
  · have hQl : Ql p Gp (incl M₁ M₂) = ⊥ := by
      unfold Ql
      rw [h, Subgroup.bot_subgroupOf]
      exact Subgroup.map_bot _
    unfold Qu RankTwoAmalgam.Completion.Qvert
    refine le_bot_iff.mp (iSup₂_le fun g _ => ?_)
    show conjSub g (Ql p Gp (incl M₁ M₂)) ≤ ⊥
    rw [hQl]
    unfold conjSub
    rw [Subgroup.map_bot]

end CFSG.ASVolI
