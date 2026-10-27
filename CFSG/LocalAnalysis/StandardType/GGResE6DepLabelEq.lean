module

public import CFSG.LocalAnalysis.StandardType.GGResE6DepLabelDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l05nL4e_rank_eq_zero {lab : LargeEvenLabel} (h2 : LargeEvenInLambda2 lab)
    (h : lab.tag = .E6 ∨ lab.tag = .twE6) : lab.rank = 0 := by
  rcases h with h | h
  · unfold LargeEvenInLambda2 at h2
    rw [h] at h2
    exact h2.2
  · unfold LargeEvenInLambda2 at h2
    rw [h] at h2
    exact h2.2

private theorem l05nL4e_dvd_not_both (n : ℕ) :
    ¬ (3 ∣ 2 ^ n - 1 ∧ 3 ∣ 2 ^ n + 1) := by
  rintro ⟨h1, h2⟩
  have hpos : 0 < 2 ^ n := pow_pos (by norm_num) n
  obtain ⟨m, hm⟩ : ∃ m, 2 ^ n = m + 1 := ⟨2 ^ n - 1, by omega⟩
  have hm1 : 2 ^ n - 1 = m := by omega
  have hm2 : 2 ^ n + 1 = m + 2 := by omega
  rw [hm1] at h1
  rw [hm2] at h2
  obtain ⟨c1, hc1⟩ := h1
  obtain ⟨c2, hc2⟩ := h2
  omega

theorem ggResE6Dep_label_eq {a b : LargeEvenLabel} (ha2 : LargeEvenInLambda2 a)
    (hb2 : LargeEvenInLambda2 b) (ha : GGE6DepLabel a) (hb : GGE6DepLabel b) (hn : a.n = b.n) :
    a = b := by
  have hra : a.rank = 0 := by
    apply l05nL4e_rank_eq_zero ha2
    rcases ha with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  have hrb : b.rank = 0 := by
    apply l05nL4e_rank_eq_zero hb2
    rcases hb with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  have htag : a.tag = b.tag := by
    rcases ha with ⟨haE, hda⟩ | ⟨hatw, hda⟩ <;>
      rcases hb with ⟨hbE, hdb⟩ | ⟨hbtw, hdb⟩
    · exact haE.trans hbE.symm
    · exfalso
      rw [hn] at hda
      exact l05nL4e_dvd_not_both b.n ⟨hda, hdb⟩
    · exfalso
      rw [hn] at hda
      exact l05nL4e_dvd_not_both b.n ⟨hdb, hda⟩
    · exact hatw.trans hbtw.symm
  have hrank : a.rank = b.rank := by rw [hra, hrb]
  cases a with
  | mk ta ra na =>
    cases b with
    | mk tb rb nb =>
      rw [LargeEvenLabel.mk.injEq]
      exact ⟨htag, hrank, hn⟩

end CFSG.StandardType
