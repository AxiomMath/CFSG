module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightK133Z3
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1Red
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1Z7

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

theorem s16k_isElemAbelianOfRank_one_of_cyclic {X : Type} [Group X] {n : ℕ}
    (h : IsCyclicOrd X n) : IsElemAbelianOfRank n 1 X := by
  obtain ⟨hc, hcard⟩ := h
  have e1 := zmodCyclicMulEquiv hc
  rw [hcard] at e1
  exact ⟨e1.symm.trans (AddEquiv.toMultiplicative (AddEquiv.funUnique (Fin 1) (ZMod n))).symm⟩

theorem s16k_concl163_of_133 (h : S16kBase D V₀ V L hV)
    {t : MulAut (Vtil V₀ V hV)}
    (h133 : Conc4_133 (Mbar D.M V₀ V hV) t (lBar V₀ V hV L)) : Concl163 D V₀ V hV L := by
  have hs : s15 D.M V₀ V hV L = 1 := h.s1
  have hrkT : ∀ n : ℕ, rk ↥(commSub ⊤ (lBar V₀ V hV L)) = n →
      rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) = n := fun n hn => by
    rw [← h.comm_top]
    exact hn
  have hrkW : ∀ n : ℕ, rk ↥(commSub ⊤ (lBar V₀ V hV L)) = n →
      rk ↥(wTil V₀ V hV L) = n := fun n hn => hn
  have hfalse4 : rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) ≤ 4 → False := fun hr =>
    s16e_false_of_rk_le_four D h.std.hx h.std.h4 h.std.h61 h.std.h127 h.setting.hyp16 hV hr
  obtain ⟨p, hp, hLp, hcomm, hind, hcases⟩ := h133
  rcases hcases with ⟨hZ, hrk⟩ | ⟨hZ, hrk⟩ | ⟨hP, hrk⟩ | ⟨hE, hrk, -, -⟩ | ⟨hZ, hrk⟩ |
    ⟨r, m, hpm, -, hE, hrk, -⟩ | ⟨hE, hrk, -⟩
  · rcases hrk with hrk | hrk | hrk
    · exact (hfalse4 (by have := hrkT _ hrk; omega)).elim
    · exact (hfalse4 (by have := hrkT _ hrk; omega)).elim
    · exact (s16k_false_of_z3_rk6 h hZ (hrkT _ hrk)).elim
  · exact (hfalse4 (by have := hrkT _ hrk; omega)).elim
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hP, hrkW _ hrk, hs.ge⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨hE, hrkW _ hrk⟩))))))))))
  · rcases hrk with hrk | hrk
    · exact (hfalse4 (by have := hrkT _ hrk; omega)).elim
    · exact (s16e_s1_false_of_z7 D h.std.hx h.std.h4 h.std.h61 h.std.h127 hV h.setting h.conc hs
        (s16k_isElemAbelianOfRank_one_of_cyclic hZ) (hrkW _ hrk)).elim
  · rcases hpm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨⟨r, hE, by rw [hrkW _ hrk, mul_comm]⟩, hs.ge⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl ⟨r, hE, by rw [hrkW _ hrk, mul_comm]⟩)))))))))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨⟨2, hE, by rw [hrkW _ hrk]⟩, hs.ge⟩))))))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
