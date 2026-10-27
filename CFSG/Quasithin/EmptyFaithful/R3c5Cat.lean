module

public import CFSG.Quasithin.EmptyFaithful.R3c3Cat
public import CFSG.Quasithin.EmptyFaithful.R3c3Inner

public section

namespace CFSG.Quasithin.R3c5

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.R3c2
  CFSG.Quasithin.R3c3 CFSG.ComponentClassification.OuterAutomorphisms
open scoped MatrixGroups

@[expose] def RankOneOut (X : Type) [Group X] : Prop :=
  (∃ n : ℕ, IsPSL 2 2 n X) ∨ (∃ p : ℕ, p.Prime ∧ IsPSL 2 p 1 X) ∨
    (∃ m : ℕ, Odd m ∧ IsPSL 3 2 m X) ∨ (∃ m : ℕ, Even m ∧ IsPSU 3 2 m X)

theorem RankOneOut.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (h : RankOneOut X) :
    RankOneOut Y := by
  rcases h with ⟨n, h⟩ | ⟨p, hp, h⟩ | ⟨m, hm, h⟩ | ⟨m, hm, h⟩
  · exact Or.inl ⟨n, isPSL_of_mulEquiv e.symm h⟩
  · exact Or.inr (Or.inl ⟨p, hp, isPSL_of_mulEquiv e.symm h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨m, hm, isPSL_of_mulEquiv e.symm h⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨m, hm, isPSU_of_mulEquiv e.symm h⟩))

theorem outer_comm_of_rankOneOut {J : Type} [Group J] [Group.IsPerfect J]
    (h : RankOneOut (J ⧸ Subgroup.center J)) : ∀ a b : Outer J, a * b = b * a := by
  rcases h with ⟨n, h⟩ | ⟨p, hp, h⟩ | ⟨m, hm, h⟩ | ⟨m, hm, h⟩
  · exact (CFSG.LocalAnalysis.ComponentInitial.OuterDerived.linear_perfect_cover_outer_derived_diagonal_bound
      J 2 2 n h).2.2.2 rfl
  · exact (CFSG.LocalAnalysis.ComponentInitial.OuterDerived.linear_perfect_cover_outer_derived_diagonal_bound
      J 2 p 1 h).2.2.2 rfl
  · obtain ⟨-, hd, -⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.OuterDerived.linear_perfect_cover_outer_derived_diagonal_bound
        J 3 2 m h
    have h1 : Nat.gcd 3 (2 ^ m - 1) = 1 := by
      have h3 : ¬ 3 ∣ 2 ^ m - 1 := by
        have h := R3c.two_pow_mod_three_of_odd hm
        generalize 2 ^ m = N at h ⊢
        omega
      exact (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3)).symm
    rw [h1] at hd
    exact comm_of_card_commutator_eq_one (Nat.dvd_one.1 hd)
  · obtain ⟨-, hd, -⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.OuterDerived.unitary_perfect_cover_outer_derived_diagonal_bound
        J 3 2 m h
    have h1 : Nat.gcd 3 (2 ^ m + 1) = 1 := by
      have := R3c.two_pow_mod_three_of_even hm
      have h3 : ¬ 3 ∣ 2 ^ m + 1 := by omega
      exact (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3)).symm
    rw [h1] at hd
    exact comm_of_card_commutator_eq_one (Nat.dvd_one.1 hd)

section CaseA

variable {G : Type} [Group G] [Finite G]

theorem rankOneOut_of_lemma115LieCharTwo {L : Subgroup G} (hnoSz : ¬ ∃ e : ℕ, IsSz e ↥L)
    (hrk : CFSG.Open.pRank 3 L = 1) (hlie : Lemma115LieCharTwo ↥L) : RankOneOut ↥L := by
  have hE9 : ∀ {Y : Type} [Group Y] [Finite Y], (↥L ≃* Y) →
      2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Y) → RankOneOut ↥L := fun e h =>
    (false_of_two_le_top hrk e h).elim
  rcases hlie with ((⟨f, hfam⟩ | hTits) | ⟨n, hn, hPSL⟩) | ⟨⟨e⟩⟩ | hU33
  · rcases hfam with ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ |
      ⟨hodd, hf, hm⟩ | ⟨hodd, hf, hm⟩
    · exact Or.inl ⟨f, hm⟩
    · rcases Nat.even_or_odd f with hev | hodd
      · exact hE9 (MulEquiv.refl _) (two_le_pRank_three_isPSL_three_two_even hev hm)
      · exact Or.inr (Or.inr (Or.inl ⟨f, hodd, hm⟩))
    · rcases Nat.even_or_odd f with hev | hodd
      · exact Or.inr (Or.inr (Or.inr ⟨f, hev, hm⟩))
      · exact hE9 (MulEquiv.refl _) (two_le_pRank_three_isPSU_two_odd hodd hm)
    · exact hE9 (MulEquiv.refl _) (two_le_pRank_three_isPSp_two hm)
    · exact hE9 (MulEquiv.refl _) (two_le_pRank_three_isG2 hm)
    · exact hE9 (MulEquiv.refl _) (two_le_pRank_three_is3D4 hm)
    · exact hE9 (MulEquiv.refl _) (two_le_pRank_three_is2F4 hm)
    · exact (hnoSz ⟨f, hm⟩).elim
  · exact hE9 (MulEquiv.refl _) (two_le_pRank_three_isTits hTits)
  · exact hE9 (MulEquiv.refl _) (two_le_pRank_three_isPSL_two_one hn hPSL)
  · exact hE9 (MulEquiv.refl _) (two_le_pRank_three_alt (by norm_num) e)
  · exact hE9 (MulEquiv.refl _) (CFSG.Quasithin.two_le_pRank_of_isPSU_three_three1515e hU33)

end CaseA

section Main

variable {G : Type} [Group G] [Finite G]

theorem rankOneOut_of_lemma115 {L : Subgroup G} {z : G} (hcases : Lemma115Cases L z)
    (hq : CFSG.IsQuasisimple ↥L) (hcen : centerOf L = pCoreOf 2 L)
    (hnoSz : ¬ ∃ e : ℕ, IsSz e (↥L ⧸ Subgroup.center ↥L)) (hrk : CFSG.Open.pRank 3 L = 1) :
    RankOneOut (↥L ⧸ Subgroup.center ↥L) := by
  rcases hcases with ⟨hs, hlie, -⟩ | ⟨-, -, hL34, -⟩ | ⟨φ, σ, -, -, -⟩ | ⟨φ, σ, -, -, -⟩ |
    ⟨hE, -⟩ | ⟨⟨s, hs, ⟨e⟩⟩, -⟩
  ·
    have hp : Group.IsPerfect ↥L := hq.1
    let eC := quotCenterEquivOfSimple hs hp
    have hnoSz' : ¬ ∃ e : ℕ, IsSz e ↥L := fun ⟨e, he⟩ => hnoSz ⟨e, isSz_of_mulEquiv eC he⟩
    exact RankOneOut.of_mulEquiv eC.symm (rankOneOut_of_lemma115LieCharTwo hnoSz' hrk hlie)
  ·
    exfalso
    rw [R3c.pRank_three_eq_pCore_quotient L] at hrk
    rcases hL34 with hm | hm
    · have := two_le_pRank_three_isPSL_three_two_even (n := 2) ⟨1, rfl⟩ hm
      omega
    · have := two_le_pRank_three_isG2 hm
      omega
  ·
    exact (false_of_two_le_quotient hcen hrk φ (two_le_pRank_three_alt (n := 6) (by norm_num)
      (MulEquiv.refl _))).elim
  ·
    exact (false_of_two_le_quotient hcen hrk φ (two_le_pRank_three_alt (n := 7) (by norm_num)
      (MulEquiv.refl _))).elim
  ·
    rcases hE with hL33 | ⟨p, hFM, hm⟩
    · exact (false_of_two_le_top hrk (MulEquiv.refl _)
        (two_le_pRank_three_isPSL_three_three hL33)).elim
    · have hp3 : p ≠ 3 := by
        rintro rfl
        obtain ⟨⟨-, -, -, -, h23⟩, -⟩ := hm
        exact h23 (by simp)
      have hp2 : p ≠ 2 := by
        rintro rfl
        obtain ⟨⟨-, -, -, h22, -⟩, -⟩ := hm
        exact h22 (by simp)
      have hs : IsSimpleGroup ↥L := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 p 1 hm).2
      have hp : Group.IsPerfect ↥L := hq.1
      exact Or.inr (Or.inl ⟨p, hFM.1, isPSL_of_mulEquiv (quotCenterEquivOfSimple hs hp) hm⟩)
  ·
    exfalso
    rw [R3c.pRank_three_eq_pCore_quotient L] at hrk
    have := two_le_pRank_three_of_lemma115SporadicName hs e
    omega

end Main

end CFSG.Quasithin.R3c5
