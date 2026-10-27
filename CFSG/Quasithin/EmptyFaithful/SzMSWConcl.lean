module

public import CFSG.Quasithin.MS93.SkAssembly
public import CFSG.Quasithin.EmptyFaithful.SzMSWTrans

public section

namespace CFSG.Quasithin.SzMSW

open CFSG.Quasithin CFSG.Quasithin.MS93 CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
  CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

variable {G : Type} [Group G] {M T L : Subgroup G}

@[expose] def MS93ConclASW (M T L : Subgroup G) : Prop :=
  MS93Case2 M L ∨ MS93Case3 M T L ∨ MS93Case4 M L ∨
    (Xq M ≤ Zq M L ⊔ Uq M T L ∧ MS93Case5 (Vq M L) L) ∨ MS93Case6 M L ∨ MS93Case8 M T L ∨
    MS93Case10 M L ∨ (Xq M ≤ Zq M L ⊔ Uq M T L ∧ MS93Case11 (Vq M L) T L) ∨
    (Xq M ≤ Zq M L ⊔ Uq M T L ∧ MS93Case13 (Vq M L) T L ∧ MS93Case13W (Vq M L) L)

theorem MS93ConclASW.of_case2 (h : MS93Case2 M L) : MS93ConclASW M T L := Or.inl h

theorem MS93ConclASW.of_case3 (h : MS93Case3 M T L) : MS93ConclASW M T L := Or.inr (Or.inl h)

theorem MS93ConclASW.of_case4 (h : MS93Case4 M L) : MS93ConclASW M T L :=
  Or.inr (Or.inr (Or.inl h))

theorem MS93ConclASW.of_case5 (hX : Xq M ≤ Zq M L ⊔ Uq M T L) (h : MS93Case5 (Vq M L) L) :
    MS93ConclASW M T L :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨hX, h⟩)))

theorem MS93ConclASW.of_case6 (h : MS93Case6 M L) : MS93ConclASW M T L :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

theorem MS93ConclASW.of_case8 (h : MS93Case8 M T L) : MS93ConclASW M T L :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))

theorem MS93ConclASW.of_case10 (h : MS93Case10 M L) : MS93ConclASW M T L :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))

theorem MS93ConclASW.of_case11 (hX : Xq M ≤ Zq M L ⊔ Uq M T L) (h : MS93Case11 (Vq M L) T L) :
    MS93ConclASW M T L :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hX, h⟩)))))))

theorem MS93ConclASW.of_case13 (hX : Xq M ≤ Zq M L ⊔ Uq M T L) (h : MS93Case13 (Vq M L) T L)
    (hW : MS93Case13W (Vq M L) L) : MS93ConclASW M T L :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hX, h, hW⟩)))))))

theorem MS93ConclASW.toConclAS (h : MS93ConclASW M T L) : MS93ConclAS M T L := by
  rcases h with h | h | h | ⟨hX, h⟩ | h | h | h | ⟨hX, h⟩ | ⟨hX, h, -⟩
  · exact MS93ConclAS.of_case2 h
  · exact MS93ConclAS.of_case3 h
  · exact MS93ConclAS.of_case4 h
  · exact MS93ConclAS.of_case5 hX h
  · exact MS93ConclAS.of_case6 h
  · exact MS93ConclAS.of_case8 h
  · exact MS93ConclAS.of_case10 h
  · exact MS93ConclAS.of_case11 hX h
  · exact MS93ConclAS.of_case13 hX h

end CFSG.Quasithin.SzMSW
