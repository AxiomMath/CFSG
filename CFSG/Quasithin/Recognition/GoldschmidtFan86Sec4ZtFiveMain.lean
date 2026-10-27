module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P514Z5
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4ZtFiveMono

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem fan49_five (F : FanTree Γ G) (h40 : Fan40 F) (h28 : Fan28) (h33 : Fan33 F)
    (h48 : Fan48Two F) (T : Track Γ G) (j : ℤ) (hj : valence Γ (T.line.vert j) = 5) :
    ZT T j = ⊥ := by
  by_cases hT : T.fixer = ⊥
  · rw [eq_bot_iff]
    intro z hz
    rw [← hT]
    exact (mem_ZT_iff.1 hz).1
  obtain ⟨T', hreach, hstar⟩ := fan48_1 F h40 h28 T hT
  obtain ⟨d, hd5, hd⟩ := fan49_main_five F h40 h33 h48 hstar
  obtain ⟨d₀, hd₀5, hd₀⟩ := zt_push_five F hreach ⟨d, hd5, hd⟩
  have hpar := T.line.mod_two_eq_of_valence_eq F (hj.trans hd₀5.symm)
  obtain ⟨k, hk⟩ : ∃ k : ℤ, j = d₀ + 2 * k := ⟨(j - d₀) / 2, by omega⟩
  rw [hk]
  exact zt_shift F T hd₀ k

end CFSG.Quasithin.Fan86
