module

public import CFSG.Quasithin.Background.E2TwoC

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace E2

namespace E22A

theorem two_le_of_one_lt_of_le {x : ℕ∞} {n : ℕ} (h1 : 1 < x) (h2 : x ≤ n) : 2 ≤ n := by
  have := lt_of_lt_of_le h1 h2
  exact_mod_cast this

theorem eq_two_of_one_lt_of_le {x : ℕ∞} (h1 : 1 < x) (h2 : x ≤ 2) : x = 2 :=
  le_antisymm h2 (by simpa [one_add_one_eq_two] using Order.add_one_le_of_lt h1)

theorem eq_two_of_one_lt_of_le_of_eq {x : ℕ∞} {n : ℕ} (h1 : 1 < x) (h2 : x ≤ n) (hn : n = 2) :
    x = 2 :=
  eq_two_of_one_lt_of_le h1 (by subst hn; exact_mod_cast h2)

end E22A

variable {Γ : Type} [Group Γ]

@[expose] def E22CasesC (H T M K : Subgroup Γ) : Prop :=
  let Ks := star M H K
  let MKs := star M H (M ⊓ K)
  let TKs := star M H (T ⊓ K)
  let Ts := star M H T
  let Q := pCoreOf 2 H
  let ZTK := TKs ⊓ Subgroup.centralizer (TKs : Set (StarQuot M H))
  (kerIn M H = Q ∧ ∃ t ∈ T, cjSub t K ≠ K ∧ M = (M ⊓ K) ⊔ cjSub t (M ⊓ K) ⊔ T ∧
    ((∃ n : ℕ, 2 ≤ n ∧ (IsPSL 2 2 n ↥Ks ∨ IsSz n ↥Ks) ∧ IsBorelIn Ks MKs ∧
        E1.nParam H ≤ n) ∨
      (∃ p : ℕ, p.Prime ∧ (p % 8 = 1 ∨ p % 8 = 7) ∧ IsPSL 2 p 1 ↥Ks ∧
        MKs = Ks ⊓ Subgroup.centralizer (ZTK : Set (StarQuot M H)) ∧ 8 < autCard Ts Ks ∧
        E1.nParam H = 1))) ∨
  (T ≤ Subgroup.normalizer (K : Set Γ) ∧
    (∀ x : Γ, x ∈ kerIn M H ↔ x ∈ K ⊔ Q ∧ ∀ y ∈ K ⊔ Q, x * y * x⁻¹ * y⁻¹ ∈ Q) ∧
    ((∃ n : ℕ, IsBenderOf n ↥Ks ∧ IsBorelIn Ks MKs ∧
        E1.nParam H ≤ n ∧ E1.nParam (⊤ : Subgroup (StarQuot M H)) = n) ∨
      (∃ n : ℕ, 1 ≤ n ∧ (IsPSL 3 2 n ↥Ks ∨ IsSp4Prime n ↥Ks) ∧ IsDiagramNontrivial Ts Ks TKs ∧
        IsBorelIn Ks MKs ∧ E1.nParam H ≤ n ∧ E1.nParam (⊤ : Subgroup (StarQuot M H)) = n) ∨
      (∃ p e : ℕ, p.Prime ∧ 3 < p ∧ (e = 1 ∨ e = 2) ∧ (p ^ e % 8 = 1 ∨ p ^ e % 8 = 7) ∧
        IsPSL 2 p e ↥Ks ∧ MKs = Ks ⊓ Subgroup.centralizer (ZTK : Set (StarQuot M H)) ∧
        8 < autCard Ts Ks ∧ E1.nParam H = 1) ∨
      (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
        ((p % 4 = 1 ∧ IsPSU 3 p 1 ↥Ks) ∨ (p % 4 = 3 ∧ IsPSL 3 p 1 ↥Ks ∧ InducesOuter Ts Ks)) ∧
        MKs = Ks ⊓ Subgroup.centralizer (ZTK : Set (StarQuot M H)) ∧ E1.nParam H = 1)))

theorem e22CasesC_of_noN {H T M K : Subgroup Γ} (hc : E22CasesNoN H T M K)
    (hn : E22NParamCases H T M K) : E22CasesC H T M K := by
  dsimp only [E22CasesNoN] at hc
  dsimp only [E22NParamCases] at hn
  dsimp only [E22CasesC]
  rcases hc with ⟨hJ, t, ht, hne, hM, h1⟩ | ⟨hTK, hJ, h2⟩
  · obtain ⟨hla, hlb⟩ := hn.1 hJ ⟨t, ht, hne, hM⟩
    refine Or.inl ⟨hJ, t, ht, hne, hM, ?_⟩
    rcases h1 with ⟨n, hn2, hty, hB⟩ | ⟨p, hp, hp8, hK, hMK, haut⟩
    · exact Or.inl ⟨n, hn2, hty, hB, hla n hn2 hty hB⟩
    · exact Or.inr ⟨p, hp, hp8, hK, hMK, haut, hlb p hp hp8 hK hMK haut⟩
  · obtain ⟨ha, hb, hc', hd⟩ := hn.2 hTK hJ
    refine Or.inr ⟨hTK, hJ, ?_⟩
    rcases h2 with ⟨n, hBen, hB⟩ | ⟨n, h1n, hty, hD, hB⟩ |
        ⟨p, e, hp, hp3, he, hpe, hK, hMK, haut⟩ | ⟨p, hp, hp2, hK, hMK⟩
    · exact Or.inl ⟨n, hBen, hB, ha n hBen hB⟩
    · exact Or.inr (Or.inl ⟨n, h1n, hty, hD, hB, hb n h1n hty hD hB⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨p, e, hp, hp3, he, hpe, hK, hMK, haut,
        hc' p e hp hp3 he hpe hK hMK haut⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨p, hp, hp2, hK, hMK, hd p hp hp2 hK hMK⟩))

theorem exists_borel_of_e22CasesC {H T X K : Subgroup Γ} (hn1 : 1 < E1.nParam H)
    (hcases : E22CasesC H T X K) :
    ∃ n : ℕ, 2 ≤ n ∧ (IsBenderOf n ↥(star X H K) ∨ IsPSL 3 2 n ↥(star X H K) ∨
        IsPSp4 2 n ↥(star X H K)) ∧
      IsBorelIn (star X H K) (star X H (X ⊓ K)) ∧ E1.nParam H ≤ n := by
  dsimp only [E22CasesC] at hcases
  rcases hcases with ⟨-, -, -, -, -, h1⟩ | ⟨-, -, h2⟩
  · rcases h1 with ⟨n, hn, htype, hBor, hnH⟩ | ⟨_, _, _, _, _, _, hnH⟩
    · exact ⟨n, hn, Or.inl ⟨hn, htype.elim Or.inl fun h => Or.inr (Or.inl h)⟩, hBor, hnH⟩
    · exact absurd hn1 (by rw [hnH]; exact lt_irrefl 1)
  · rcases h2 with ⟨n, hBen, hBor, hnH, -⟩ | ⟨n, -, htype, -, hBor, hnH, -⟩ |
        ⟨_, _, _, _, _, _, _, _, _, hnH⟩ | ⟨_, _, _, _, _, hnH⟩
    · exact ⟨n, hBen.1, Or.inl hBen, hBor, hnH⟩
    · have hn2 := E22A.two_le_of_one_lt_of_le hn1 hnH
      refine ⟨n, hn2, ?_, hBor, hnH⟩
      rcases htype with h | h
      · exact Or.inr (Or.inl h)
      · right; right
        rw [IsSp4Prime] at h
        split_ifs at h with h1
        · omega
        · exact h
    · exact absurd hn1 (by rw [hnH]; exact lt_irrefl 1)
    · exact absurd hn1 (by rw [hnH]; exact lt_irrefl 1)

end E2

namespace E2.E22StatementC

theorem exists_cases (h : E2.E22StatementC) {G : Type} [Group G] [Finite G]
    {H T M : Subgroup G} (hmin : MinParabolic H T M) (hSQ : SQTKGroup ↥H)
    (hns : ¬ Group.IsSolvable ↥H) :
    (∃ K : Subgroup G, K ∈ cComp H ∧ H = K ⊔ T ∧
      CFSG.Open.IsQuasisimple (↥K ⧸ CFSG.Open.pCore 2 ↥K) ∧ E2.E22CasesC H T M K) ∧
    SQTKGroup (E2.StarQuot M H) := by
  obtain ⟨⟨K, hKc, hHK, hq, hc⟩, hSQs⟩ := h.toNoN G H T M hmin hSQ hns
  exact ⟨⟨K, hKc, hHK, hq,
    E2.e22CasesC_of_noN hc (h.toNParam G H T M K hmin hSQ hns hKc hHK hq hc hSQs)⟩, hSQs⟩

end E2.E22StatementC

end CFSG.Quasithin
