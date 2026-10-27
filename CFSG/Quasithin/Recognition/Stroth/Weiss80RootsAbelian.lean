module

public import CFSG.Geometry.GeneralizedQuadrangles.Moufang.RootsAbelian
public import CFSG.Quasithin.Recognition.Stroth.Weiss80Route
public import CFSG.GH74.GLS.SP.Local.SPLFaith
public import CFSG.GH74.GLS.SP.Local.SPLRestrict

public section

namespace CFSG.Quasithin.Stroth

open SimpleGraph CFSG.Geometry.GeneralizedPolygons CFSG.Geometry.GeneralizedQuadrangles
  CFSG.Quasithin CFSG.Quasithin.Stroth

theorem fgqRootsAbelian : FGQRootsAbelian := by
  intro V _ Γ _ H _ _ _ _ hP hT hM s t _hs hst hdeg hne p hp a b ha hb
  obtain ⟨c⟩ := hP.isBipartite
  obtain ⟨S, T, hS2, hT2, -, hdegc⟩ := hP.exists_order (by norm_num) hT c
  obtain ⟨⟨x, hx⟩⟩ := hP.exists_point (by norm_num) hT c
  obtain ⟨L, hL⟩ := exists_line hP hT c
  have hxT : Γ.degree x = T + 1 := by rw [hdegc x, if_pos hx]
  have hLS : Γ.degree L = S + 1 := by rw [hdegc L, if_neg (by rw [hL]; decide)]
  have hTs : T = s ∨ T = t := by
    have := hdeg x
    rw [hxT] at this
    omega
  have hSs : S = s ∨ S = t := by
    have := hdeg L
    rw [hLS] at this
    omega
  have hpair : (S = s ∧ T = t) ∨ (S = t ∧ T = s) ∨ S = T := by
    rcases hSs with h1 | h1 <;> rcases hTs with h2 | h2
    · exact Or.inr (Or.inr (h1.trans h2.symm))
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr (Or.inl ⟨h1, h2⟩)
    · exact Or.inr (Or.inr (h1.trans h2.symm))
  by_cases hST : S ≤ T
  ·
    have hne' : ¬ ∃ q : ℕ, S = q ^ 2 ∧ T = q ^ 3 := by
      rintro ⟨q, hSq, hTq⟩
      rcases lt_or_eq_of_le hST with hlt | heq
      ·
        rcases hpair with ⟨h1, h2⟩ | ⟨h1, h2⟩ | hEq
        · exact hne ⟨q, h1.symm.trans hSq, h2.symm.trans hTq⟩
        · omega
        · omega
      ·
        have hq1 : q ≤ 1 := by
          by_contra h
          have hq2 : 2 ≤ q := by omega
          have hlt : q ^ 2 < q ^ 3 :=
            Nat.pow_lt_pow_right (by omega : 1 < q) (by norm_num : 2 < 3)
          omega
        have hS1 : S ≤ 1 := by
          calc S = q ^ 2 := hSq
            _ ≤ 1 ^ 2 := Nat.pow_le_pow_left hq1 2
            _ = 1 := by norm_num
        omega
    exact commute_of_mem_rootGroup hP hT c hdegc hST hM hne' p hp ha hb
  ·
    have hTS : T < S := by omega
    have hne' : ¬ ∃ q : ℕ, T = q ^ 2 ∧ S = q ^ 3 := by
      rintro ⟨q, hTq, hSq⟩
      rcases hpair with ⟨h1, h2⟩ | ⟨h1, h2⟩ | hEq
      · omega
      · exact hne ⟨q, h2.symm.trans hTq, h1.symm.trans hSq⟩
      · omega
    exact commute_of_mem_rootGroup hP hT (dualColoring c) (degree_eq_of_dualColoring hdegc)
      hTS.le hM hne' p hp ha hb

end CFSG.Quasithin.Stroth

end
