module

public import CFSG.Milestones.ASVolI.B4Ext.Three
public import CFSG.Milestones.ASVolI.B4Ext.III
public import CFSG.Milestones.ASVolI.B4Ext.IVc

public section

namespace CFSG.ASVolI

section Final

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

theorem burnsideB49x_Part2i : burnsideB49_Part2i := by
  unfold burnsideB49_Part2i
  intro V _ _ hV n f hnf K _ _ hK G U π hreal hquot T hT A hA
  rcases hnf with ⟨hn, rfl⟩ | ⟨rfl, hf⟩
  · exact burnsideB49x_part2i_f1 hV hn (by simpa using hK) hreal hquot hT hA
  · exact (burnsideB49x_three hV hf hK hreal hquot hT hA).1

theorem burnsideB49x_Part2ii : burnsideB49_Part2ii := by
  unfold burnsideB49_Part2ii
  intro V _ _ hV n f hnf K _ _ hK G U π hreal hquot T hT A hA hn3
  subst hn3
  rcases hnf with ⟨hn, -⟩ | ⟨-, hf⟩
  · omega
  · exact (burnsideB49x_three hV hf hK hreal hquot hT hA).2

theorem burnsideB49x_Part2iii : burnsideB49_Part2iii := by
  unfold burnsideB49_Part2iii
  intro V _ _ hV n f hnf K _ _ hK G U π hreal hquot T hT A hA hn4 hdual
  subst hn4
  have hf : f = 1 := by
    rcases hnf with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · omega
  subst hf
  have hK2 : Nat.card K = 2 := by simpa using hK
  have hAG' := burnsideB49x_offender_mono hT.1 hA
  have hoff := burnsideB49x_offender_card hAG'
  obtain ⟨-, h16⟩ := burnsideB49x_four_sixteen hV hK2 hreal hdual hAG'.1 hAG'.2.1 hoff
  have hle := (burnsideB49x_four_card_le hV hK2 hreal (Or.inr hdual) hAG'.1 hAG'.2.2.1).1
  have hcard : Nat.card A = 16 := le_antisymm hle h16
  refine ⟨(burnsideB49x_four_Jj hV hK2 hreal (Or.inr hdual) hT hA.1 hA.2.2.1 hcard).symm, ?_,
    burnsideB49x_four_q hV hK2 hreal hdual hAG'⟩
  show CFSG.Quasithin.rk ↥A = 4
  unfold CFSG.Quasithin.rk
  rw [hcard, show (16 : ℕ) = 2 ^ 4 by norm_num, padicValNat.prime_pow]

theorem burnsideB49x_Part2iv : burnsideB49_Part2iv := by
  unfold burnsideB49_Part2iv
  intro V _ _ hV n f hnf K _ _ hK G U π hreal hquot T hT A hA hn5 hdual
  subst hn5
  have hf : f = 1 := by
    rcases hnf with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · omega
  subst hf
  have hK2 : Nat.card K = 2 := by simpa using hK
  exact ⟨burnsideB49x_five_q hV hK2 hreal hdual, burnsideB49x_five_class hV hK2 hreal hdual hT hA⟩

section Certificates


theorem as_B_4_9 : B_4_9 :=
  burnsideB49_B_4_9_of_parts burnsideB49x_Part2i burnsideB49x_Part2ii burnsideB49x_Part2iii
    burnsideB49x_Part2iv

end Certificates

end Final

end CFSG.ASVolI
