module

public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperMoreUnitary
public import CFSG.LocalAnalysis.StandardType.GGTableBTwoThreeSp
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridgeInner

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGIOneMoreSpSixLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank = 3 ∧ lab.n = 1 ∧ p = 3

theorem recipeSymplectic_bstarEq_six {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeSymplectic 3 (2 ^ 1) false Q) :
    LargeEvenRecipeSymplectic 3 (2 ^ 1) false fun R _ I F => Q R I F ∧
      (∃ r, GGTorusLift 3 r R ∧ GGInnerDiagBound 3 r R I) ∧
        ∃ r, GGTorusLift 3 r R ∧ GGIRankLe 3 r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (le_refl 1) hK
  have hlift : GGTorusLift 3 2 (LargeEvenProj (LargeEvenSpGroup K 3)) :=
    TwoThree.ggTorusLift_sp_two (k := 2) hK2
  refine ⟨K, inferInstance, inferInstance, hK, hQ, ⟨2, hlift,
    ggInnerDiagBound_of_forall_mem fun φ _ =>
      innSet_subset_symplectic 3 (TwoThree.mem_range_conj_sp hK2 le_rfl φ)⟩,
    2, hlift, fun X hXI hX h4 => ?_⟩
  exfalso
  obtain ⟨A, hA, hAc⟩ := TableBSymp.exists_of_subset_inn
    (TableBSymp.center_spProj_eq_bot (K := K) (m := 3))
    (fun φ hφ => TableBSymp.sp_I_subset_inn (hXI hφ)) hX
  have h1 := TwoThree.card_sq_le_sp hK2 hA
  rw [hAc] at h1
  have h2 : (3 ^ 4) ^ 2 ≤ Nat.card X ^ 2 := Nat.pow_le_pow_left h4 2
  have h3 := h2.trans h1
  norm_num at h3

theorem largeEvenLabelAll_bstarEq_spSix {p : ℕ} {lab : LargeEvenLabel}
    (h : GGIOneMoreSpSixLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => (∃ r, GGTorusLift p r R ∧ GGInnerDiagBound p r R I) ∧
      ∃ r, GGTorusLift p r R ∧ GGIRankLe p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hl, hn, rfl⟩ := h
  dsimp only at ht hl hn
  subst hl hn
  intro Q hQ
  rcases ht with rfl | rfl <;> exact recipeSymplectic_bstarEq_six hQ

theorem ggStdSubIOneProperInputOn_spSix (ha₀ : GGLNoncyclicInput) :
    GGStdSubIOneProperInputOn GGIOneMoreSpSixLabel :=
  ggStdSubIOneProperInputOn_of_bstarEq ha₀ fun _ _ _ _ h _ => largeEvenLabelAll_bstarEq_spSix h

@[expose] def GGIOneMoreSpTwoRestLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .B ∨ lab.tag = .C) ∧ 4 ≤ lab.rank ∧ lab.n = 1 ∧ p = 3

@[expose] def GGIOneProperRestFiveLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGIOneMoreUnitaryRestLabel p lab ∨ GGIOneMoreTwDThreeFieldLabel p lab ∨
    GGIOneMoreSpTwoRestLabel p lab ∨ GGIOneMoreOrthPlusFourLabel p lab ∨
      GGIOneMoreOrthMinusOddFieldLabel p lab ∨ GGIOneMoreExcTwoLabel p lab ∨
        GGIOneMoreTwE6Label p lab ∨ GGIOneMoreE6ThreeLabel p lab

theorem ggIOneProperRestFourLabel_cover {p : ℕ} {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGIOneProperRestFourLabel p lab) :
    GGIOneMoreSpSixLabel p lab ∨ GGIOneProperRestFiveLabel p lab := by
  rcases h with hU | hT | ⟨ht, hn, hp3⟩ | hP | hM | hX | hE6 | hE3
  · exact Or.inr (Or.inl hU)
  · exact Or.inr (Or.inr (Or.inl hT))
  · have hl : 3 ≤ lab.rank := by
      obtain ⟨t, l, n⟩ := lab
      dsimp only at ht hn ⊢
      have h2 := hlab.2
      rcases ht with rfl | rfl <;> dsimp only at h2 <;> omega
    rcases (show lab.rank = 3 ∨ 4 ≤ lab.rank by omega) with h3 | h4
    · exact Or.inl ⟨ht, h3, hn, hp3⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ht, h4, hn, hp3⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hP))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hM)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hX))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hE6)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hE3)))))))

@[expose] def GGIOneProperRestNarrowLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGIOneProperRestFiveLabel p lab ∨ GGIOneMoreFieldLabel p lab ∨ GGIOneMoreOrthEnnolaLabel p lab

theorem ggIOneProperRestLabel_cover_narrow {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hp2 : p ≠ 2) (hlab : LargeEvenInLambda2 lab) (hs : LargeEvenSplit p lab)
    (h : GGIOneProperRestLabel p lab) :
    GGIOneMoreTypeACoprimeLabel p lab ∨ GGIOneMoreOrthEqLabel p lab ∨
      GGIOneMoreE6CoprimeLabel p lab ∨ GGIOneMoreE6TwoLabel p lab ∨
        GGIOneMoreUnitaryFourLabel p lab ∨ GGIOneMoreSpSixLabel p lab ∨
          GGIOneProperRestNarrowLabel p lab := by
  rcases ggIOneProperRestLabel_cover hp hp2 hlab hs h with h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases ggIOneProperRestTwoLabel_cover h with h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))
    · rcases ggIOneProperRestThreeLabel_cover h with h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · rcases ggIOneProperRestFourLabel_cover hlab h with h | h
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))

section Certs

theorem ggStdSubIOneProperInputOn_rest_of_restNarrow (ha₀ : GGLNoncyclicInput)
    (hR : GGStdSubIOneProperInputOn GGIOneProperRestNarrowLabel) :
    GGStdSubIOneProperInputOn GGIOneProperRestLabel :=
  (((((((ggStdSubIOneProperInputOn_typeACoprime ha₀).or (ggStdSubIOneProperInputOn_orthEq ha₀)).or
    (ggStdSubIOneProperInputOn_e6Coprime ha₀)).or (ggStdSubIOneProperInputOn_e6Two ha₀)).or
      (ggStdSubIOneProperInputOn_unitaryFour ha₀)).or (ggStdSubIOneProperInputOn_spSix ha₀)).or
        hR).mono_split fun _ _ hp hp2 hlab hs h => by
    rcases ggIOneProperRestLabel_cover_narrow hp hp2 hlab hs h with h | h | h | h | h | h | h
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h)))))
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))
    · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inl (Or.inr h)
    · exact Or.inr h

theorem ggStdSubIOneProperInputOn_restNarrow_of_restFive (ha₀ : GGLNoncyclicInput)
    (hC : GGIOneMoreFieldCorFourTwoInput) (hE : GGIOneMoreOrthEndNodeInput)
    (hR : GGStdSubIOneProperInputOn GGIOneProperRestFiveLabel) :
    GGStdSubIOneProperInputOn GGIOneProperRestNarrowLabel :=
  hR.or ((ggStdSubIOneProperInputOn_field ha₀ hC).or (ggStdSubIOneProperInputOn_orthEnnola ha₀ hE))

end Certs

end CFSG.StandardType
