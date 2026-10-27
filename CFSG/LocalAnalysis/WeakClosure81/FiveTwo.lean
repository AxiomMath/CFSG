module

public import CFSG.LocalAnalysis.WeakClosure81.FiveOne

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem b5_FiveTwo_le (n : ℕ) :
    ∀ {H M A : Subgroup G}, Nat.card H = n → Sec5Hyp H M A →
      H ≤ (M ⊓ H) ⊔ ⨆ g ∈ {g : G | g ∈ H ∧ conjSubgroup A g ≤ M},
        ⨆ D ∈ dFam H M (conjSubgroup A g), D := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro H M A hcard h
    by_cases hone : (maxOver H A).ncard = 1
    ·
      apply le_sup_of_le_right
      have hHmem : H ∈ dFam H M (conjSubgroup A 1) := by
        rw [conjSubgroup_one, mem_dFam]
        exact ⟨le_rfl, h.le_group, h.not_le, h.odd_relIndex, hone⟩
      exact le_iSup₂_of_le (1 : G) ⟨H.one_mem, by rw [conjSubgroup_one]; exact h.le_M⟩
        (le_iSup₂_of_le H hHmem le_rfl)
    ·
      have hN : 1 < (maxOver H A).ncard := by
        have hN₀lt : M ⊓ H < H :=
          lt_of_le_of_ne inf_le_right fun heq => h.not_le (by rw [← heq]; exact inf_le_left)
        obtain ⟨N₀, hN₀max, hMN₀⟩ := exists_isMaxSubgroupIn hN₀lt
        have hN₀mem : N₀ ∈ maxOver H A :=
          ⟨hN₀max, (le_inf h.le_M h.le_group).trans hMN₀⟩
        have hpos : 0 < (maxOver H A).ncard :=
          (Set.ncard_pos (Set.toFinite _)).2 ⟨N₀, hN₀mem⟩
        exact lt_of_le_of_ne (Nat.succ_le_iff.mpr hpos) fun h1 => hone h1.symm
      obtain ⟨g, hgH, hconjM, hgen⟩ := five_one h hN
      have hI : (⨆ N ∈ {N : Subgroup G | N ∈ maxOver H (conjSubgroup A g) ∧
            Odd (M.relIndex N)}, N) ≤
          (M ⊓ H) ⊔ ⨆ g' ∈ {g' : G | g' ∈ H ∧ conjSubgroup A g' ≤ M},
            ⨆ D ∈ dFam H M (conjSubgroup A g'), D := by
        refine iSup₂_le fun N hNmem => ?_
        have hNmax : N ∈ maxOver H (conjSubgroup A g) := hNmem.1
        have hNodd : Odd (M.relIndex N) := hNmem.2
        have hisMax : IsMaxSubgroupIn H N := hNmax.1
        have hleAN : conjSubgroup A g ≤ N := hNmax.2
        have hNH : N ≤ H := hisMax.le
        have hNlt : N < H := hisMax.1
        by_cases hNM : N ≤ M
        ·
          exact (le_inf hNM hNH).trans le_sup_left
        ·
          have hNsec : Sec5Hyp N M (conjSubgroup A g) :=
            ⟨h.isElemAbelian.map (MulAut.conj g⁻¹).toMonoidHom,
              hleAN, hconjM, hNM, hNodd⟩
          have hcardlt : Nat.card N < n := by
            rw [← hcard]
            exact Subgroup.card_lt_of_lt hNlt
          have hNind : N ≤ (M ⊓ N) ⊔
              ⨆ g' ∈ {g' : G | g' ∈ N ∧
                conjSubgroup (conjSubgroup A g) g' ≤ M},
                ⨆ D ∈ dFam N M (conjSubgroup (conjSubgroup A g) g'), D :=
            ih (Nat.card N) hcardlt rfl hNsec
          refine hNind.trans (sup_le ?_ ?_)
          ·
            exact (inf_le_inf_left M hNH).trans le_sup_left
          ·
            refine iSup₂_le fun g' hg' => iSup₂_le fun D hD => ?_
            have hgg'H : g * g' ∈ H := H.mul_mem hgH (hNH hg'.1)
            have hgg'M : conjSubgroup A (g * g') ≤ M := by
              rw [← conjSubgroup_conjSubgroup]
              exact hg'.2
            rw [conjSubgroup_conjSubgroup, mem_dFam] at hD
            have hDmem : D ∈ dFam H M (conjSubgroup A (g * g')) := by
              rw [mem_dFam]
              exact ⟨hD.1.trans hNH, hD.2.1, hD.2.2.1, hD.2.2.2.1, hD.2.2.2.2⟩
            exact le_sup_of_le_right
              (le_iSup₂_of_le (g * g') ⟨hgg'H, hgg'M⟩
                (le_iSup₂_of_le D hDmem le_rfl))
      exact hgen.trans_le hI

theorem five_two {H M A : Subgroup G} (h : Sec5Hyp H M A) :
    H = (M ⊓ H) ⊔ ⨆ g ∈ {g : G | g ∈ H ∧ conjSubgroup A g ≤ M},
      ⨆ D ∈ dFam H M (conjSubgroup A g), D := by
  refine le_antisymm (b5_FiveTwo_le (Nat.card H) rfl h) ?_
  refine sup_le inf_le_right ?_
  refine iSup₂_le fun g _ => iSup₂_le fun D hD => ?_
  exact (mem_dFam.1 hD).1

theorem five_two_exists {H M A : Subgroup G} (h : Sec5Hyp H M A) :
    ∃ g ∈ H, conjSubgroup A g ≤ M ∧ (dFam H M (conjSubgroup A g)).Nonempty := by
  by_contra hcon
  have hall : ∀ g ∈ {g : G | g ∈ H ∧ conjSubgroup A g ≤ M},
      ∀ D ∈ dFam H M (conjSubgroup A g), D ≤ M ⊓ H := fun g hg D hD =>
    absurd ⟨g, hg.1, hg.2, D, hD⟩ hcon
  have h3 : H ≤ M ⊓ H := by
    conv_lhs => rw [five_two h]
    exact sup_le le_rfl (iSup₂_le fun g hg => iSup₂_le fun D hD => hall g hg D hD)
  exact h.not_le (h3.trans inf_le_left)

end CFSG.LocalAnalysis.WeakClosure81
