module

public import CFSG.Quasithin.Vol2.Ch5LieQuot

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

@[expose] def E22FieldCases {Γ : Type} [Group Γ] (H T M K : Subgroup Γ) (k : ℕ) : Prop :=
  let Ks := E2.star M H K
  let MKs := E2.star M H (M ⊓ K)
  let TKs := E2.star M H (T ⊓ K)
  let Ts := E2.star M H T
  let Q := pCoreOf 2 H
  (kerIn M H = Q ∧ ∃ t ∈ T, cjSub t K ≠ K ∧ M = (M ⊓ K) ⊔ cjSub t (M ⊓ K) ⊔ T ∧
      2 ≤ k ∧ (IsPSL 2 2 k ↥Ks ∨ IsSz k ↥Ks) ∧ E2.IsBorelIn Ks MKs) ∨
    (T ≤ Subgroup.normalizer (K : Set Γ) ∧
      (∀ x : Γ, x ∈ kerIn M H ↔ x ∈ K ⊔ Q ∧ ∀ y ∈ K ⊔ Q, x * y * x⁻¹ * y⁻¹ ∈ Q) ∧
      ((E2.IsBenderOf k ↥Ks ∧ E2.IsBorelIn Ks MKs) ∨
        (2 ≤ k ∧ (IsPSL 3 2 k ↥Ks ∨ E2.IsSp4Prime k ↥Ks) ∧ E2.IsDiagramNontrivial Ts Ks TKs ∧
          E2.IsBorelIn Ks MKs)))

@[expose] def Stmt5_1_10_E22 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L H B D K : Subgroup G) (n k : ℕ),
    Hyp5_1_8 G T M L H n → IsNotation5_1_9 T M L H B D →
    K ∈ cComp H → H = K ⊔ T → CFSG.Open.IsQuasisimple (↥K ⧸ CFSG.Open.pCore 2 ↥K) →
    E22FieldCases H T (H ⊓ M) K k →
      oTwoUpper H = conjClosure K T ∧ E2.IsBorelIn (oTwoUpper H) (M ⊓ oTwoUpper H) ∧
      ((K < oTwoUpper H ∧ (LieModel (O2Q K) .PSL 2 2 k ∨ SuzukiModel (O2Q K) 2 k)) ∨
        (K = oTwoUpper H ∧ IsBenderCh5 k (O2Q (oTwoUpper H))) ∨
        (K = oTwoUpper H ∧
          (IsSL3Ch5 k (O2Q (oTwoUpper H)) ∨ LieModel (O2Q (oTwoUpper H)) .PSp 2 2 k) ∧
          E2.IsDiagramNontrivial T (oTwoUpper H) (T ⊓ oTwoUpper H)))

section General

variable {G : Type} [Group G]

theorem E22CasesC.exists_field {H T M K : Subgroup G} (hc : E2.E22CasesC H T M K)
    (h1 : 1 < E1.nParam H) : ∃ k : ℕ, (2 ≤ k ∧ E1.nParam H ≤ k) ∧ E22FieldCases H T M K k := by
  dsimp only [E2.E22CasesC] at hc
  dsimp only [E22FieldCases]
  rcases hc with ⟨hJ, t, ht, hne, hM, h1'⟩ | ⟨hTK, hJ, h2⟩
  · rcases h1' with ⟨k, hk2, hty, hB, hle⟩ | ⟨-, -, -, -, -, -, hnH⟩
    · exact ⟨k, ⟨hk2, hle⟩, Or.inl ⟨hJ, t, ht, hne, hM, hk2, hty, hB⟩⟩
    · exact absurd h1 (by rw [hnH]; exact lt_irrefl 1)
  · rcases h2 with ⟨k, hBen, hB, hle, -⟩ | ⟨k, -, hty, hD, hB, hle, -⟩ |
      ⟨_, _, _, _, _, _, _, _, _, hnH⟩ | ⟨_, _, _, _, _, hnH⟩
    · exact ⟨k, ⟨hBen.1, hle⟩, Or.inr ⟨hTK, hJ, Or.inl ⟨hBen, hB⟩⟩⟩
    · have hk2 := E2.E22A.two_le_of_one_lt_of_le h1 hle
      exact ⟨k, ⟨hk2, hle⟩, Or.inr ⟨hTK, hJ, Or.inr ⟨hk2, hty, hD, hB⟩⟩⟩
    · exact absurd h1 (by rw [hnH]; exact lt_irrefl 1)
    · exact absurd h1 (by rw [hnH]; exact lt_irrefl 1)

theorem E22CasesC.exists_field_of_lie [Finite G]
    {H T M K : Subgroup G} (hTH : T ≤ H) (hT : IsPGroup 2 T) (hK : K ∈ cComp H)
    (hHK : H = K ⊔ T) (hq : ∃ K' ∈ cComp H, E2.HasE22LieQuot K') (hc : E2.E22CasesC H T M K) :
    ∃ k : ℕ, (2 ≤ k ∧ E1.nParam H ≤ k) ∧ E22FieldCases H T M K k := by
  have hsmall : ¬ E2.IsE22SmallType ↥(E2.star M H K) :=
    E2.not_isE22SmallType_star_of_lie hTH hT hK hHK hq
  dsimp only [E2.E22CasesC] at hc
  dsimp only [E22FieldCases]
  rcases hc with ⟨hJ, t, ht, hne, hM, h1'⟩ | ⟨hTK, hJ, h2⟩
  · rcases h1' with ⟨k, hk2, hty, hB, hle⟩ | ⟨p, hp, hp8, hKs, -, -, -⟩
    · exact ⟨k, ⟨hk2, hle⟩, Or.inl ⟨hJ, t, ht, hne, hM, hk2, hty, hB⟩⟩
    · exact absurd (Or.inl ⟨p, hp, hp8, hKs⟩) hsmall
  · rcases h2 with ⟨k, hBen, hB, hle, -⟩ | ⟨k, hk1, hty, hD, hB, hle, -⟩ |
      ⟨p, e, hp, hp3, he, hpe, hKs, -, -, -⟩ | ⟨p, hp, hp2, hKs, -, -⟩
    · exact ⟨k, ⟨hBen.1, hle⟩, Or.inr ⟨hTK, hJ, Or.inl ⟨hBen, hB⟩⟩⟩
    · have hk2 : 2 ≤ k := by
        by_contra hlt
        have h1 : k = 1 := by omega
        subst h1
        rcases hty with h | h
        · exact hsmall (Or.inr (Or.inr (Or.inr (Or.inl h))))
        · exact hsmall (Or.inr (Or.inr (Or.inr (Or.inr h))))
      exact ⟨k, ⟨hk2, hle⟩, Or.inr ⟨hTK, hJ, Or.inr ⟨hk2, hty, hD, hB⟩⟩⟩
    · exact absurd (Or.inr (Or.inl ⟨p, e, hp, hp3, he, hpe, hKs⟩)) hsmall
    · exfalso
      rcases hKs with ⟨-, hU⟩ | ⟨-, hL, -⟩
      · exact hsmall (Or.inr (Or.inr (Or.inl ⟨p, hp, hp2, Or.inl hU⟩)))
      · exact hsmall (Or.inr (Or.inr (Or.inl ⟨p, hp, hp2, Or.inr hL⟩)))

theorem isHallTwoPrimeOf_inf_oTwoUpper [Finite G] {B M H : Subgroup G}
    (hB : Lin2.IsHallTwoPrimeOf B (M ⊓ H)) : Lin2.IsHallTwoPrimeOf B (M ⊓ oTwoUpper H) := by
  have hBK : B ≤ oTwoUpper H := by
    intro b hb
    refine Subgroup.subset_closure ⟨(hB.1 hb).2, ?_⟩
    have hdvd : orderOf (⟨b, hb⟩ : ↥B) ∣ Nat.card B := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at hdvd
    exact Odd.of_dvd_nat hB.2.1 hdvd
  have hBMK : B ≤ M ⊓ oTwoUpper H := le_inf (hB.1.trans inf_le_left) hBK
  have hMKH : M ⊓ oTwoUpper H ≤ M ⊓ H := inf_le_inf_left M (oTwoUpper_le H)
  obtain ⟨j, hj⟩ := hB.2.2
  have hmul := Subgroup.relIndex_mul_relIndex B (M ⊓ oTwoUpper H) (M ⊓ H) hBMK hMKH
  have hdvd : B.relIndex (M ⊓ oTwoUpper H) ∣ 2 ^ j := by
    rw [← hj, ← hmul]
    exact Dvd.intro _ rfl
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  exact ⟨hBMK, hB.2.1, i, hi⟩

end General

theorem stmt5_1_10_of (h331 : Stmt3_3_1) (hE22 : E2.E22StatementC)
    (hTr : Stmt5_1_10_E22) : Stmt5_1_10 := by
  intro G _ _ T M L H B D n hyp hN
  have h := hyp.toHyp5_0_1
  obtain ⟨hmp, -⟩ := h.minParabolic_of_isHStar h331 hyp.hStar
  obtain ⟨hns', hsqtk⟩ := h.not_isSolvable_and_sqtk_of_lie hyp.hStar hyp.lieQuot
  obtain ⟨⟨K, hKc, hHK, hq, hcases⟩, -⟩ := hE22.exists_cases hmp hsqtk hns'
  obtain ⟨k, hk, hfc⟩ := E22CasesC.exists_field_of_lie hmp.isSylow.1 hmp.isSylow.2.1 hKc hHK
    hyp.lieQuot hcases
  obtain ⟨hKeq, hBorel, hc⟩ := hTr G T M L H B D K n k hyp hN hKc hHK hq hfc
  exact ⟨k, hk, hBorel, isHallTwoPrimeOf_inf_oTwoUpper hN.1, K, hKc, hKeq, hc⟩

end CFSG.Quasithin.H13
