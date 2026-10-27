module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNPGL27Facts

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup NFF7

theorem nfPGL27_holds : NFPGL27 := by
  intro X _ _ hX Lb Tb hLn hL1 hLp hTb
  obtain ⟨ψ⟩ := nonempty_equiv_pgl2_zmod hX
  obtain ⟨hLcard, hLsimple, hLcent⟩ := lb_facts ψ hLn hL1 hLp
  obtain ⟨φ, hφ⟩ := exists_model hX hTb
  have hX336 : Nat.card X = 336 := CFSG.GroupTheory.card_of_isPGL2_seven hX
  have hT16 : Nat.card Tb = 16 := by
    rw [hφ.card_eq (hφ.memT) t_sub t_nodup, t_length]
  refine ⟨hTb, ?_, hLn, ?_, ?_, ?_, hφ.pair hTb, hφ.table hTb, ?_⟩
  ·
    have h1 := card_dvd_of_le (le_sup_left : Lb ≤ Lb ⊔ Tb)
    have h2 := card_dvd_of_le (le_sup_right : Tb ≤ Lb ⊔ Tb)
    have h3 := card_subgroup_dvd_card (Lb ⊔ Tb)
    rw [hLcard] at h1
    rw [hT16] at h2
    rw [hX336] at h3
    have hpos : 0 < Nat.card (Lb ⊔ Tb : Subgroup X) := Nat.card_pos
    have hle : Nat.card (Lb ⊔ Tb : Subgroup X) ≤ 336 := Nat.le_of_dvd (by norm_num) h3
    apply eq_top_of_card_eq
    rw [hX336]
    omega
  · rw [hLcard]
    norm_num
  ·
    rintro K hKn ⟨x, hxK, hx2⟩
    have hN : ((K ⊓ Lb).subgroupOf Lb).Normal := by
      have : (K ⊓ Lb).Normal := inferInstance
      exact Subgroup.normal_subgroupOf
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hLsimple _ hN with hb | ht
    · exfalso
      have hKL : K ⊓ Lb = ⊥ := by
        refine le_bot_iff.mp fun y hy => ?_
        have hy' : (⟨y, hy.2⟩ : Lb) ∈ (K ⊓ Lb).subgroupOf Lb := hy
        rw [hb, mem_bot] at hy'
        exact mem_bot.mpr (congrArg Subtype.val hy')
      have hc : ⁅K, Lb⁆ = ⊥ := le_bot_iff.mp (hKL ▸ commutator_le_inf K Lb)
      have hKc := commutator_eq_bot_iff_le_centralizer.mp hc
      rw [hLcent] at hKc
      have hx1 : x = 1 := mem_bot.mp (hKc hxK)
      rw [hx1, orderOf_one] at hx2
      exact absurd hx2 (by norm_num)
    · intro l hl
      have : (⟨l, hl⟩ : Lb) ∈ (K ⊓ Lb).subgroupOf Lb := by
        rw [ht]
        exact mem_top _
      exact this.1
  · rw [hLcent]
    exact IsPGroup.of_bot
  · intro E hE hEn hEe h4
    exact (hφ.close E hE hEn hEe h4).elim

end CFSG.LocalAnalysis.WeakClosure81
