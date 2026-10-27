module

public import CFSG.LocalAnalysis.StandardType.GGResILineInputs
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrRowFilter
public import CFSG.LocalAnalysis.StandardType.GGCSRHolds
public import CFSG.LocalAnalysis.StandardType.GGResJLineA3
public import CFSG.LocalAnalysis.StandardType.GGTBJConfigFacts
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrSmallRank
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBVac

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggTablePRow_three_A3_split {n : ℕ} (hn : 3 ∣ 2 ^ n - 1) {X : LargeEvenLabel}
    (h : GGTablePRow 3 ⟨.A, 3, n⟩ X) :
    X = ⟨.A, 4, n⟩ ∨ X = ⟨.A, 5, n⟩ ∨ X = ⟨.C, 4, n⟩ ∨ X = ⟨.D, 4, n⟩ ∨
      X = ⟨.twD, 5, n⟩ ∨
      (X.tag = .A ∧ (X.rank = 7 ∨ X.rank = 8) ∧ 2 * X.n = n ∧ 3 ∣ 2 ^ X.n + 1) := by
  unfold GGTablePRow at h
  norm_num at h
  rcases h with ⟨-, h⟩ | ⟨hadd, -⟩
  · exact h
  · exact (not_dvd_two_pow_sub_add (by norm_num) Nat.prime_three hn hadd).elim

theorem ggTablePRow_three_D3_split {n : ℕ} (hn : 3 ∣ 2 ^ n - 1) {X : LargeEvenLabel}
    (h : GGTablePRow 3 ⟨.D, 3, n⟩ X) : X = ⟨.D, 4, n⟩ := by
  unfold GGTablePRow at h
  norm_num at h
  rcases h with ⟨-, h⟩ | ⟨hadd, -⟩
  · exact h
  · exact (not_dvd_two_pow_sub_add (by norm_num) Nat.prime_three hn hadd).elim

theorem ggTablePRow_three_twA3_nonsplit {n : ℕ} (hn : 3 ∣ 2 ^ n + 1) {X : LargeEvenLabel}
    (h : GGTablePRow 3 ⟨.twA, 3, n⟩ X) :
    X = ⟨.twA, 4, n⟩ ∨ X = ⟨.twA, 5, n⟩ ∨ X = ⟨.C, 4, n⟩ ∨ X = ⟨.D, 4, n⟩ ∨
      X = ⟨.D, 5, n⟩ ∨ (X.tag = .twE6 ∧ 3 * X.n = n) := by
  unfold GGTablePRow at h
  norm_num at h
  rcases h with ⟨hsub, -⟩ | ⟨-, h⟩
  · exact (not_dvd_two_pow_sub_add (by norm_num) Nat.prime_three hsub hn).elim
  · exact h

theorem ggTablePRow_three_twD3_nonsplit {n : ℕ} (hn : 3 ∣ 2 ^ n + 1) {X : LargeEvenLabel}
    (h : GGTablePRow 3 ⟨.twD, 3, n⟩ X) : X = ⟨.D, 4, n⟩ := by
  unfold GGTablePRow at h
  norm_num at h
  rcases h with ⟨hsub, -⟩ | ⟨-, h⟩
  · exact (not_dvd_two_pow_sub_add (by norm_num) Nat.prime_three hsub hn).elim
  · exact h

theorem ggTablePRow_three_A3 {labJ labX : LargeEvenLabel}
    (hJ : ggResLineJLabel .A3 labJ) (hrow : GGTablePRow 3 labJ labX) :
    (labJ.tag = .A ∧ labJ.rank = 3 ∧ 3 ∣ 2 ^ labJ.n - 1 ∧
      (labX = ⟨.A, 4, labJ.n⟩ ∨ labX = ⟨.A, 5, labJ.n⟩ ∨ labX = ⟨.C, 4, labJ.n⟩ ∨
        labX = ⟨.D, 4, labJ.n⟩ ∨ labX = ⟨.twD, 5, labJ.n⟩ ∨
        (labX.tag = .A ∧ (labX.rank = 7 ∨ labX.rank = 8) ∧ 2 * labX.n = labJ.n ∧
          3 ∣ 2 ^ labX.n + 1))) ∨
    (labJ.tag = .D ∧ labJ.rank = 3 ∧ 3 ∣ 2 ^ labJ.n - 1 ∧ labX = ⟨.D, 4, labJ.n⟩) ∨
    (labJ.tag = .twA ∧ labJ.rank = 3 ∧ 3 ∣ 2 ^ labJ.n + 1 ∧
      (labX = ⟨.twA, 4, labJ.n⟩ ∨ labX = ⟨.twA, 5, labJ.n⟩ ∨ labX = ⟨.C, 4, labJ.n⟩ ∨
        labX = ⟨.D, 4, labJ.n⟩ ∨ labX = ⟨.D, 5, labJ.n⟩ ∨
        (labX.tag = .twE6 ∧ 3 * labX.n = labJ.n))) ∨
    (labJ.tag = .twD ∧ labJ.rank = 3 ∧ 3 ∣ 2 ^ labJ.n + 1 ∧ labX = ⟨.D, 4, labJ.n⟩) := by
  obtain ⟨tJ, rJ, nJ⟩ := labJ
  rcases hJ with ⟨htag | htag, hr, hdvd⟩ | ⟨htag | htag, hr, hdvd⟩
  · subst htag; subst hr
    exact Or.inl ⟨rfl, rfl, hdvd, ggTablePRow_three_A3_split hdvd hrow⟩
  · subst htag; subst hr
    exact Or.inr (Or.inl ⟨rfl, rfl, hdvd, ggTablePRow_three_D3_split hdvd hrow⟩)
  · subst htag; subst hr
    exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hdvd, ggTablePRow_three_twA3_nonsplit hdvd hrow⟩))
  · subst htag; subst hr
    exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, hdvd, ggTablePRow_three_twD3_nonsplit hdvd hrow⟩))

theorem ggTablePRow_three_A3_not_twE6 {labJ labX : LargeEvenLabel}
    (hJ : ggResLineJLabel .A3 labJ) (hrow : GGTablePRow 3 labJ labX)
    (hoff : ¬ (labX.tag = .twE6 ∧ 3 ∣ 2 ^ labX.n + 1)) :
    (labJ.tag = .A ∧ labJ.rank = 3 ∧ 3 ∣ 2 ^ labJ.n - 1 ∧
      (labX = ⟨.A, 4, labJ.n⟩ ∨ labX = ⟨.A, 5, labJ.n⟩ ∨ labX = ⟨.C, 4, labJ.n⟩ ∨
        labX = ⟨.D, 4, labJ.n⟩ ∨ labX = ⟨.twD, 5, labJ.n⟩ ∨
        (labX.tag = .A ∧ (labX.rank = 7 ∨ labX.rank = 8) ∧ 2 * labX.n = labJ.n ∧
          3 ∣ 2 ^ labX.n + 1))) ∨
    (labJ.tag = .D ∧ labJ.rank = 3 ∧ 3 ∣ 2 ^ labJ.n - 1 ∧ labX = ⟨.D, 4, labJ.n⟩) ∨
    (labJ.tag = .twA ∧ labJ.rank = 3 ∧ 3 ∣ 2 ^ labJ.n + 1 ∧
      (labX = ⟨.twA, 4, labJ.n⟩ ∨ labX = ⟨.twA, 5, labJ.n⟩ ∨ labX = ⟨.C, 4, labJ.n⟩ ∨
        labX = ⟨.D, 4, labJ.n⟩ ∨ labX = ⟨.D, 5, labJ.n⟩)) ∨
    (labJ.tag = .twD ∧ labJ.rank = 3 ∧ 3 ∣ 2 ^ labJ.n + 1 ∧ labX = ⟨.D, 4, labJ.n⟩) := by
  rcases ggTablePRow_three_A3 hJ hrow with hA | hD | htwA | htwD
  · exact Or.inl hA
  · exact Or.inr (Or.inl hD)
  · rcases htwA with ⟨htag, hr, hdvd, hX | hX | hX | hX | hX | ⟨htwE6, h3n⟩⟩
    · exact Or.inr (Or.inr (Or.inl ⟨htag, hr, hdvd, Or.inl hX⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨htag, hr, hdvd, Or.inr (Or.inl hX)⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨htag, hr, hdvd, Or.inr (Or.inr (Or.inl hX))⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨htag, hr, hdvd,
        Or.inr (Or.inr (Or.inr (Or.inl hX)))⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨htag, hr, hdvd,
        Or.inr (Or.inr (Or.inr (Or.inr hX)))⟩))
    · exfalso
      apply hoff
      refine ⟨htwE6, ?_⟩
      have hdvd3 : 3 ∣ 2 ^ (3 * labX.n) + 1 := by
        rwa [← h3n] at hdvd
      have hz : ((2 ^ (3 * labX.n) + 1 : ℕ) : ZMod 3) = 0 :=
        (ZMod.natCast_eq_zero_iff _ _).mpr hdvd3
      have hcube : ((2 : ZMod 3) ^ labX.n) ^ 3 + 1 = 0 := by
        rw [← hz]
        push_cast
        rw [show 3 * labX.n = labX.n * 3 by omega, pow_mul]
      have hx3 : (2 : ZMod 3) ^ labX.n = ((2 : ZMod 3) ^ labX.n) ^ 3 :=
        (ZMod.pow_card _).symm
      have hx : (2 : ZMod 3) ^ labX.n + 1 = 0 := by
        rw [hx3]
        exact hcube
      rw [← ZMod.natCast_eq_zero_iff]
      push_cast
      exact hx
  · exact Or.inr (Or.inr (Or.inr htwD))

end CFSG.StandardType

end
