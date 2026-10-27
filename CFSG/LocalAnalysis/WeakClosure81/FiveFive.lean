module

public import CFSG.LocalAnalysis.WeakClosure81.FiveFiveAb
public import CFSG.LocalAnalysis.WeakClosure81.FiveFiveNon
public import CFSG.LocalAnalysis.WeakClosure81.FiveFiveFstar

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem five_five {H M A : Subgroup G} (h : Sec5Hyp H M A) (hM : maxOver H A = {M})
    (hA : ¬ A ≤ pCoreOf 2 H) (hK : kerMOf M H = ⊥) :
    (Nat.card A = 2 ∧ ∃ p : ℕ, p.Prime ∧ Odd p ∧ Nonempty (↥H ≃* DihedralGroup p)) ∨
      ∃ L : Subgroup G, IsSimpleGroup ↥L ∧ (¬ ∀ x ∈ L, ∀ y ∈ L, x * y = y * x) ∧
        Fstar H = L ∧ H = L ⊔ A := by
  have hHne : H ≠ ⊥ := fun hH => h.not_le (hH ▸ bot_le)
  have hbotH : (⊥ : Subgroup G) < H := bot_lt_iff_ne_bot.2 hHne
  have hbotn : ((⊥ : Subgroup G).subgroupOf H).Normal := by
    rw [Subgroup.bot_subgroupOf]
    exact Subgroup.normal_bot
  obtain ⟨X, hX⟩ := exists_isMinNormalOver hbotH hbotn
  by_cases hab : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x
  · exact Or.inl (five_five_abelian h hM hA hK hX hab)
  · refine Or.inr ⟨X, five_five_nonabelian h hM hK hX hab, hab, ?_, ?_⟩
    · have hsimple := five_five_nonabelian h hM hK hX hab
      have hHXA : H = X ⊔ A := five_four_one hM (by rw [hK]; exact hX)
      have hO2 := pCoreOf_two_eq_bot_of_maxOver_eq_singleton h hM hK
      have hC := inf_centralizer_eq_bot_of_isSimpleGroup h.isElemAbelian h.le_group hX.2.1
        hX.2.2.1 hHXA hO2 hsimple hab
      exact fstar_eq_of_isSimpleGroup_of_centralizer_eq_bot hX.2.1 hX.2.2.1 hsimple hab hC
    · exact five_four_one hM (by rw [hK]; exact hX)

end CFSG.LocalAnalysis.WeakClosure81
