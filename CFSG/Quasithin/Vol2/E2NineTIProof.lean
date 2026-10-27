module

public import CFSG.Quasithin.Vol2.E2NineTIPair
public import CFSG.Quasithin.Background.E2NParamStar
public import CFSG.Quasithin.Vol2.E2NineTI
public import CFSG.Quasithin.Vol2.E2SevenKG1Sz
public import CFSG.Quasithin.Vol2.E2SevenKG1U3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6

namespace ASInputs

@[expose] def AS_E_2_9_nStarTI_2b : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M V : Subgroup G), E2.Hyp28 H T M V →
    IsTISetIn V M → SQTKGroup ↥(⊤ : Subgroup (E2.StarQuot M H)) →
    ∀ (K : Subgroup (E2.StarQuot M H)) (n : ℕ), K ∈ cComp (⊤ : Subgroup (E2.StarQuot M H)) →
      (⊤ : Subgroup (E2.StarQuot M H)) = K ⊔ E2.star M H T →
      E2.star M H T ≤ Subgroup.normalizer (K : Set (E2.StarQuot M H)) → 1 ≤ n →
      (IsPSL 3 2 n ↥(E2.star (E2.star M H M) ⊤ K) ∨
        E2.IsSp4Prime n ↥(E2.star (E2.star M H M) ⊤ K)) →
      E2.IsDiagramNontrivial (E2.star (E2.star M H M) ⊤ (E2.star M H T))
        (E2.star (E2.star M H M) ⊤ K) (E2.star (E2.star M H M) ⊤ (E2.star M H T ⊓ K)) →
      E2.IsBorelIn (E2.star (E2.star M H M) ⊤ K)
        (E2.star (E2.star M H M) ⊤ (E2.star M H M ⊓ K)) →
      (n : ℕ∞) ≤ E1.nParam H

end ASInputs

namespace E2

theorem isBenderOf_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B) {n : ℕ}
    (h : IsBenderOf n B) : IsBenderOf n A := by
  obtain ⟨hn, hY | hY | hY⟩ := h
  · exact ⟨hn, Or.inl (isPSL_of_mulEquiv e hY)⟩
  · exact ⟨hn, Or.inr (Or.inl (isSz_of_mulEquiv' e hY))⟩
  · refine ⟨hn, Or.inr (Or.inr ?_)⟩
    obtain ⟨hadm, K, h1, h2, hK, ⟨g⟩⟩ := hY
    exact ⟨hadm, K, h1, h2, hK, ⟨e.trans g⟩⟩

variable {G : Type} [Group G] [Finite G] {H T M V : Subgroup G}

theorem Hyp28.one_le_nParam (h : Hyp28 H T M V) : (1 : ℕ∞) ≤ E1.nParam H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hlt
  have h0 : E1.nParam H = 0 := Order.lt_one_iff.mp (not_le.mp hlt)
  have hodd := E1.odd_of_nParam_le_zero (H := H) h0.le
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (B6.isPGroup_of_isElemAbelian h.elem)
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact h.ne_bot (Subgroup.eq_bot_of_card_eq V (by simpa using hk))
  have hdvd : 2 ∣ Nat.card H := by
    have h1 : 2 ∣ Nat.card V := by rw [hk]; exact dvd_pow_self 2 hk0
    exact h1.trans (Subgroup.card_dvd_of_le h.le_H)
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)

end E2

theorem ASInputs.as_E_2_9_nStarTI_of
    (hE22 : E2.E22StatementC) (hsq : ASInputs.AS_E_2_9_starSQTK)
    (h2b : ASInputs.AS_E_2_9_nStarTI_2b) : ASInputs.AS_E_2_9_nStarTI := by
  intro G _ _ H T M V h hTI
  have := E2P.finite_starQuot M H
  have hKG1 := E2.kgBenderInner_of_parts E2.kgBenderInnerL2_holds E2.kgBenderInnerSz_holds
    E2.kgBenderInnerU3_holds
  have hKG1' := E2.kgBenderInnerTwo_of_parts E2.kgBenderInnerTwoL2_holds
    E2.kgBenderInnerTwoSz_holds
  have hsq' := hsq G H T M V h
  have hY28 := h.star hsq'
  have hJY : kerIn (E2.star M H M) ⊤ = ⊥ := E2P.kerIn_star M H
  have h1H := h.one_le_nParam
  refine le_antisymm ?_ (E2.nParam_le_nParam_star h.minParabolic)
  by_cases hsolv : Group.IsSolvable ↥(⊤ : Subgroup (E2.StarQuot M H))
  · exact (E1.solvable_nParam_le_one hsolv).trans h1H
  obtain ⟨⟨K, hKc, hHK, hq, hcases⟩, hSQs⟩ :=
    hE22.1 _ ⊤ _ _ hY28.minParabolic hY28.sqtk hsolv
  have hNP := hE22.2 _ ⊤ _ _ K hY28.minParabolic hY28.sqtk hsolv hKc hHK hq hcases hSQs
  have hKH : K ≤ ⊤ := le_top
  dsimp only [E2.E22CasesNoN] at hcases
  dsimp only [E2.E22NParamCases] at hNP
  rcases hcases with ⟨hJQ, t, ht, hne, hM, h1⟩ | ⟨hTK, hJ2, h2⟩
  · obtain ⟨hA, hB⟩ := hNP.1 hJQ ⟨t, ht, hne, hM⟩
    rcases h1 with ⟨n, hn, hty, hBor⟩ | ⟨p, hp, hp8, hK, hMK, haut⟩
    ·
      have hP := E2.pairCase_of hY28 hJY hKc hHK ht hne (E2.isSimpleGroup_of_psl_or_sz hty)
      have eK := E2.equivStarOfKerInEqBot hJY hKH
      have hty' : IsPSL 2 2 n ↥K ∨ IsSz n ↥K :=
        hty.imp (E2.isPSL_of_mulEquiv eK) (E2.isSz_of_mulEquiv' eK)
      have hMK := E2.inf_eq_of_isBorelIn_star hY28.minParabolic hJY
        (subnormal_of_mem_cComp hKc) hKH hBor
      exact (hA n hn hty hBor).trans
        (E2.le_nParam_of_pair_ti hKG1' h hTI hsq' hP hHK hM hMK hn hty')
    ·
      rw [hB p hp hp8 hK hMK haut]
      exact h1H
  · obtain ⟨h2a, h2b', h2c, h2d⟩ := hNP.2 hTK hJ2
    rcases h2 with ⟨n, hBen, hBor⟩ | ⟨n, hn, hty, hD, hBor⟩ |
        ⟨p, e, hp, hp3, he, hpe, hK, hMK, haut⟩ | ⟨p, hp, hp2, hK, hMK⟩
    ·
      have eK := E2.equivStarOfKerInEqBot hJY hKH
      have hBen' : E2.IsBenderOf n ↥K := E2.isBenderOf_of_mulEquiv eK hBen
      have hKN : (⊤ : Subgroup (E2.StarQuot M H)) ≤
          Subgroup.normalizer (K : Set (E2.StarQuot M H)) := by
        rw [hHK]
        exact sup_le Subgroup.le_normalizer hTK
      have hKn : K.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hKN)
      exact (h2a n hBen hBor).1.trans
        (E2.le_nParam_of_bender_ti hKG1 h hTI hsq' hKn hHK.symm hBen')
    ·
      exact (h2b' n hn hty hD hBor).1.trans
        (h2b G H T M V h hTI hsq' K n hKc hHK hTK hn hty hD hBor)
    ·
      rw [h2c p e hp hp3 he hpe hK hMK haut]
      exact h1H
    ·
      rw [h2d p hp hp2 hK hMK]
      exact h1H

end CFSG.Quasithin
