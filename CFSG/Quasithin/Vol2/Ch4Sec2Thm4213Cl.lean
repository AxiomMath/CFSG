module

public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213Irr

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Quasithin.A4 CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

namespace Conf4212

variable {T M L I H K : Subgroup G} (c : Conf4212 G T M L I H K)
include c

theorem case5_of_card
    (hcase : C48Case1 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆
        K ∨
      C48Case2 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K ∨
      C48Case3 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K ∨
      C48Case4 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K ∨
      C48Case5 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K ∨
      C48Case7 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K ∨
      C48Case8 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K)
    (h1080 : Nat.card (ModO2 L) = 1080) :
    C48Case5 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K := by
  rcases hcase with h | h | h | h | h5 | h7 | h
  · exact absurd h1080 (c.card_ne_of_cases (Or.inl h)).1
  · exact absurd h1080 (c.card_ne_of_cases (Or.inr (Or.inl h))).1
  · exact absurd h1080 (c.card_ne_of_cases (Or.inr (Or.inr (Or.inl h)))).1
  · exact absurd h1080 (c.card_ne_of_cases (Or.inr (Or.inr (Or.inr (Or.inl h))))).1
  · exact h5
  · exact absurd (h1080.symm.trans
      (T4213.card_of_lieModel_psu331 (c.lieModel_of_isG2Block h7.2))) (by norm_num)
  · exact absurd h1080 (c.card_ne_of_cases (Or.inr (Or.inr (Or.inr (Or.inr h))))).1

theorem case7_of_card
    (hcase : C48Case1 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆
        K ∨
      C48Case2 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K ∨
      C48Case3 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K ∨
      C48Case4 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K ∨
      C48Case5 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K ∨
      C48Case7 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K ∨
      C48Case8 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K)
    (h6048 : Nat.card (ModO2 L) = 6048) :
    C48Case7 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K := by
  rcases hcase with h | h | h | h | h5 | h7 | h
  · exact absurd h6048 (c.card_ne_of_cases (Or.inl h)).2
  · exact absurd h6048 (c.card_ne_of_cases (Or.inr (Or.inl h))).2
  · exact absurd h6048 (c.card_ne_of_cases (Or.inr (Or.inr (Or.inl h)))).2
  · exact absurd h6048 (c.card_ne_of_cases (Or.inr (Or.inr (Or.inr (Or.inl h))))).2
  · exact absurd (h6048.symm.trans
      (T4213.card_of_hatA6 (c.hat_of_isHatA6Block h5.2))) (by norm_num)
  · exact h7
  · exact absurd h6048 (c.card_ne_of_cases (Or.inr (Or.inr (Or.inr (Or.inr h))))).2

theorem typeList
    (hcase : C48Case1 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆
        K ∨
      C48Case2 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K ∨
      C48Case3 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K ∨
      C48Case4 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K ∨
      C48Case5 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K ∨
      C48Case7 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K ∨
      C48Case8 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K) :
    (∃ n : ℕ, 2 ≤ n ∧ LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 2 2 n) ∨
      LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1 ∨
      LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 4 2 1 ∨
      Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 7)) ∨
      (Group.IsPerfect (↥L ⧸ CFSG.pCore 2 ↥L) ∧
        Nat.card (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) = 3 ∧
        Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) ≃*
          alternatingGroup (Fin 6))) ∨
      LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1 := by
  rcases hcase with h | h | h | h | h | h | h
  · obtain ⟨n, hn, hL, -⟩ := c.type_of_case1 h
    exact Or.inl ⟨n, hn, hL⟩
  · rcases c.type_of_case2 h with ⟨hL, -⟩ | ⟨hL, -⟩
    · exact Or.inr (Or.inl hL)
    · exact Or.inr (Or.inr (Or.inl hL))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (c.equiv_alt_of_isAltBlockType h.2))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (c.equiv_alt7_of_isExcA7Block h.2)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (c.hat_of_isHatA6Block h.2))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (c.lieModel_of_isG2Block h.2))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (c.equiv_alt_of_isAltBlockType h.2))))

theorem card_of_isPSL_LH {m : ℕ} (h : IsPSL m 2 1 (ModO2 (perfectCore (L ⊓ H)))) :
    Nat.card (ModO2 L) = CFSG.Open.ordA (m - 1) (2 ^ 1) := by
  obtain ⟨e⟩ := c.nonempty_modO2_equiv
  rw [← Nat.card_congr e.toEquiv]
  exact C489.card_of_isPSL_two h

theorem natSum_three
    (hcase : C48Case1 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆
        K ∨
      C48Case2 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K ∨
      C48Case3 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K ∨
      C48Case4 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K ∨
      C48Case5 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K ∨
      C48Case7 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K ∨
      C48Case8 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K)
    (h3 : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1) :
    IsNaturalSumUnder 3 L ⁅reducedAggregate (L ⊔ T), L⁆ := by
  have h168 := T4213.card_of_lieModel_psl32 h3
  rcases hcase with h | h | h | h | h | h | h
  · exfalso
    obtain ⟨n, -, -, hn⟩ := c.type_of_case1 h
    exact (T4213.psl2_card_ne n).1 (hn.symm.trans h168)
  · obtain ⟨m, hm, hpsl, hV⟩ := h
    rcases hm with rfl | rfl
    · rcases hV with ⟨k, hk, hsum⟩ | ⟨h4, -⟩
      · exact c.isNaturalSumUnder_of_sum hk hsum
      · exact absurd h4 (by norm_num)
    · exact absurd (h168.symm.trans (c.card_of_isPSL_LH hpsl)) (by decide)
  · obtain ⟨e⟩ := c.equiv_alt_of_isAltBlockType h.2
    rw [Nat.card_congr e.toEquiv, C489.card_alt6] at h168
    norm_num at h168
  · obtain ⟨e⟩ := c.equiv_alt7_of_isExcA7Block h.2
    rw [Nat.card_congr e.toEquiv, C489.card_alt7] at h168
    norm_num at h168
  · exact absurd (h168.symm.trans (T4213.card_of_hatA6 (c.hat_of_isHatA6Block h.2)))
      (by norm_num)
  · exact absurd (h168.symm.trans
      (T4213.card_of_lieModel_psu331 (c.lieModel_of_isG2Block h.2))) (by norm_num)
  · obtain ⟨e⟩ := c.equiv_alt_of_isAltBlockType h.2
    rw [Nat.card_congr e.toEquiv, C489.card_alt6] at h168
    norm_num at h168

theorem natSum_four
    (hcase : C48Case1 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆
        K ∨
      C48Case2 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K ∨
      C48Case3 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K ∨
      C48Case4 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K ∨
      C48Case5 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K ∨
      C48Case7 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K ∨
      C48Case8 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K)
    (h4 : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 4 2 1) :
    IsNaturalSumUnder 4 L ⁅reducedAggregate (L ⊔ T), L⁆ ∨
      ∃ _ : IsMulCommutative ↥⁅reducedAggregate (L ⊔ T), L⁆,
        SLExteriorTwo (V := ↥⁅reducedAggregate (L ⊔ T), L⁆)
          (autOn L ⁅reducedAggregate (L ⊔ T), L⁆) ⊤ ⊥ 4 := by
  have h20160 := T4213.card_of_lieModel_psl42 h4
  rcases hcase with h | h | h | h | h | h | h
  · exfalso
    obtain ⟨n, -, -, hn⟩ := c.type_of_case1 h
    exact (T4213.psl2_card_ne n).2.1 (hn.symm.trans h20160)
  · obtain ⟨m, hm, hpsl, hV⟩ := h
    rcases hm with rfl | rfl
    · exact absurd (h20160.symm.trans (c.card_of_isPSL_LH hpsl)) (by decide)
    · rcases hV with ⟨k, hk, hsum⟩ | ⟨-, halt⟩
      · exact Or.inl (c.isNaturalSumUnder_of_sum hk hsum)
      · exact Or.inr (c.slExteriorTwo_of_alt halt)
  · obtain ⟨e⟩ := c.equiv_alt_of_isAltBlockType h.2
    rw [Nat.card_congr e.toEquiv, C489.card_alt6] at h20160
    norm_num at h20160
  · obtain ⟨e⟩ := c.equiv_alt7_of_isExcA7Block h.2
    rw [Nat.card_congr e.toEquiv, C489.card_alt7] at h20160
    norm_num at h20160
  · exact absurd (h20160.symm.trans (T4213.card_of_hatA6 (c.hat_of_isHatA6Block h.2)))
      (by norm_num)
  · exact absurd (h20160.symm.trans
      (T4213.card_of_lieModel_psu331 (c.lieModel_of_isG2Block h.2))) (by norm_num)
  · obtain ⟨e⟩ := c.equiv_alt_of_isAltBlockType h.2
    rw [Nat.card_congr e.toEquiv, C489.card_alt6] at h20160
    norm_num at h20160

theorem concl443TwoI_of
    (hcase : C48Case1 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆
        K ∨
      C48Case2 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K ∨
      C48Case3 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K ∨
      C48Case4 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K ∨
      C48Case5 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K ∨
      C48Case7 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K ∨
      C48Case8 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ K)
    (hFF : ∃ _ : IsMulCommutative ↥⁅reducedAggregate (L ⊔ T), L⁆,
      IsFFModule (V := ↥⁅reducedAggregate (L ⊔ T), L⁆)
        (autOn (L ⊔ T) ⁅reducedAggregate (L ⊔ T), L⁆))
    (hhat : C48Case5 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H))
        ⁅reducedAggregate (L ⊔ T), L⁆ K →
      ∀ z ∈ ⁅reducedAggregate (L ⊔ T), L⁆ ⊓ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G),
        orderOf z = 2 →
          ¬ ⁅reducedAggregate (L ⊔ T), L⁆ ≤ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)))
    (hpsu : C48Case7 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H))
        ⁅reducedAggregate (L ⊔ T), L⁆ K →
      Nat.card (⁅reducedAggregate (L ⊔ T), L⁆ : Subgroup G) = 2 ^ 6 →
        ∃ V₃ : Subgroup G, V₃ ≤ ⁅reducedAggregate (L ⊔ T), L⁆ ∧ Nat.card V₃ = 2 ^ 3 ∧
          T ⊓ L ≤ Subgroup.normalizer (V₃ : Set G) ∧ ¬ Subgroup.centralizer (V₃ : Set G) ≤ M) :
    Concl443TwoI G T M L ⁅reducedAggregate (L ⊔ T), L⁆ :=
  ⟨c.normal, c.typeList hcase, hFF, c.natSum_three hcase, c.natSum_four hcase,
    fun h => hhat (c.case5_of_card hcase (T4213.card_of_hatA6 h)),
    fun h => hpsu (c.case7_of_card hcase (T4213.card_of_lieModel_psu331 h))⟩

end Conf4212

end CFSG.Quasithin.H13.Ch4
