module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aShF
public import CFSG.Quasithin.Vol2.Ch11SecO11B
public import CFSG.Quasithin.Vol2.Ch11SecO11D
public import CFSG.Quasithin.Vol2.Ch11SecO11I
public import CFSG.Quasithin.Vol2.Ch11SecO11J

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint QuasithinUnique
open CFSG.Assembly.LowTwoRank (specialLinearGroupEquivStatedSL)

namespace O11

variable {Q : Type} [Group Q]

theorem shape4_of_sl3 (h : IsSL3 (2 ^ 2) Q) : Shape4 Q := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  exact Or.inl ⟨K, inferInstance, inferInstance, hK,
    ⟨e.trans (specialLinearGroupEquivStatedSL 3 K).symm⟩⟩

theorem shape4_of_psl3 (h : IsPSL 3 2 2 Q) : Shape4 Q :=
  Or.inr (Or.inl (Or.inl ⟨by decide, h⟩))

theorem shape4_of_psp4 (h : IsPSp4 2 2 Q) : Shape4 Q :=
  Or.inr (Or.inr (Or.inl (Or.inl ⟨by decide, h⟩)))

theorem shape4_of_g2 (h : IsG2 2 2 Q) : Shape4 Q :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by decide, h⟩))))

theorem false_of_2f4 (h : Is2F4 2 Q) : False := by
  obtain ⟨-, a, ha, -⟩ := h
  omega

end O11

open O11


theorem factShapeInspect_of (hU5 : FactU35UniqueL24) : FactShapeInspect := by
  intro Q _ _ hQ hJ4 S B₁ B₂ E hS hne h1 h2 hp1 hp2 hN1 hN2 hF1 hF2 hE hE3 hEN1 hEN2 _ _ _ _
  by_cases hs : Shape4 Q
  · exact ⟨hs, factParabGen_holds Q hs S hS B₁ B₂ hne h1 h2 hp1 hp2 hN1 hN2 hF1 hF2⟩
  exfalso
  have hpair : NoE9Pair S → False := fun h =>
    h B₁ B₂ E ⟨h1, hp1, hN1, hF1⟩ ⟨h2, hp2, hN2, hF2⟩ hne hE hEN1 hEN2
  rcases hQ with hQ | ⟨-, hQ⟩
  · rcases hQ with h | h | h | h | h | h | ⟨h, -⟩
    · exact hs (shape4_of_sl3 h)
    · exact hs (shape4_of_psl3 h)
    · exact hs (shape4_of_psp4 h)
    · exact hs (shape4_of_g2 h)
    · exact false_of_2f4 h
    · exact hpair (l24Unique_3d4 h hS).noE9Pair
    · omega
  · rcases hQ with h | h | ⟨p, hp, h5, h8, h⟩ | h | ⟨s, h⟩ | h | h | h | h | h | h | h | h | h |
      ⟨p, hp, h5, h8, -, hF, hnat⟩
    · exact hpair (l24Unique_alt7 h hS).noE9Pair
    · exact hpair (l24Unique_hat7 h hS).noE9Pair
    · exact false_of_psl2 hp (by omega) h hE hE3
    · exact false_of_psl2_25 h hE
    · cases s with
      | true =>
        rcases h with h | h
        · exact false_of_sl3_5 h hE
        · exact false_of_psl3_5 h hE
      | false => exact hpair (L24Unique.noE9Pair (hU5 Q h S hS))
    · exact hpair (l24Unique_m22 h hS).noE9Pair
    · exact hpair (l24Unique_hatM22 h hS).noE9Pair
    · exact hpair (noE9Pair_m23 h hS)
    · exact false_of_j1 h hE
    · exact hpair (l24Unique_j2 h hS).noE9Pair
    · exact hJ4 h
    · exact hpair (l24Unique_hs h hS).noE9Pair
    · exact hpair (l24Unique_ru h hS).noE9Pair
    · exact false_of_a36Case4 h hE
    · exact false_of_affine hp (by omega) hF hnat hE hE3

end CFSG.Quasithin.Vol2.Ch11.SecS
