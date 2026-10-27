module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Loc
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5Defs
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5PSing

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem hasLenTwoReflection_of_inXi {T : Track Γ G} (hT : InXi T) : HasLenTwoReflection Γ G T := by
  obtain ⟨i, hi, -⟩ := hT
  rcases i with _ | _ | _ | _ | n
  · exact hi.elim
  · obtain ⟨-, d, f, -, -, hf⟩ := hi
    exact ⟨d, f, hf⟩
  · obtain ⟨f, hf⟩ := hi 0
    exact ⟨0, f, hf.1, hf.fixes, hf.2 1, hf.2 2⟩
  · exact hi
  · exact hi.elim

namespace Line

theorem exists_move_end {ℓ : Line Γ} {N m : ℕ} (hs : ¬ LineSingLe Γ G ℓ N) (a : ℤ) (hm1 : 1 ≤ m)
    (hmN : m ≤ N) {w : V} (hw : Γ.Adj (ℓ.vert (a + m)) w) (hwp : w ≠ ℓ.vert (a + m - 1)) :
    ∃ X : G, (∀ j : ℕ, j ≤ m → X • ℓ.vert (a + j) = ℓ.vert (a + j)) ∧ X • w ≠ w := by
  by_contra hcon
  push Not at hcon
  refine hs ⟨m, a, hm1, hmN, Or.inl ⟨w, ?_, ?_, ?_⟩⟩
  · simpa [Line.arc] using hw
  · have e : (ℓ.arc a m).vert (m - 1) = ℓ.vert (a + m - 1) := by
      simp only [Line.arc]
      congr 1
      push_cast [Nat.cast_sub hm1]
      ring
    rw [e]
    exact hwp
  · intro g hg
    refine hcon g fun j hj => ?_
    have := mem_stabRange.1 hg j (Nat.zero_le _) hj
    simpa [Line.arc] using this

theorem exists_fix_move_next (F : FanTree Γ G) {ℓ : Line Γ} {N m : ℕ} (hs : ¬ LineSingLe Γ G ℓ N)
    (a : ℤ) (hm1 : 1 ≤ m) (hmN : m ≤ N + 1) :
    ∃ X : G, (∀ j : ℕ, j + 1 ≤ m → X • ℓ.vert (a + j) = ℓ.vert (a + j)) ∧
      X • ℓ.vert (a + m) ≠ ℓ.vert (a + m) := by
  by_cases hm : m = 1
  · subst hm
    obtain ⟨γ, hγ, hγne⟩ := F.exists_adj_ne (ℓ.vert a) (ℓ.vert (a + 1))
    obtain ⟨X, hX, hXγ⟩ := F.loc_trans (ℓ.vert a) (ℓ.vert (a + 1)) γ (by simpa using ℓ.adj a) hγ
    refine ⟨X, fun j hj => ?_, ?_⟩
    · obtain rfl : j = 0 := by omega
      simpa using MulAction.mem_stabilizer_iff.1 hX
    · simp only [Nat.cast_one]
      rw [hXγ]
      exact hγne
  · have hns : ¬ RightSingular Γ G (ℓ.arc a (m - 1)).vert 0 (m - 1) := fun h =>
      hs ⟨m - 1, a, by omega, by omega, Or.inl h⟩
    obtain ⟨g, hfix, hmove⟩ := ℓ.exists_fixer_right' a (m - 1) 0 (m - 1) (by omega) hns
    refine ⟨g, fun j hj => hfix _ (by omega) (by push_cast [Nat.cast_sub hm1]; omega), ?_⟩
    rwa [show a + ((m - 1 : ℕ) : ℤ) + 1 = a + m by push_cast [Nat.cast_sub hm1]; ring] at hmove

end Line

end CFSG.Quasithin.Fan86
