module

public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Quasithin.Background.G11Defs

public section

namespace CFSG.Quasithin

namespace RonanG1015

open CFSG.Open CFSG.Quasithin.G11

theorem not_cube_dvd_20160 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ^ 3 ∣ 20160 := by
  intro h
  have hle : p ^ 3 ≤ 20160 := Nat.le_of_dvd (by norm_num) h
  have hp27 : p ≤ 27 := by
    by_contra hlt
    push Not at hlt
    have : 28 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left hlt 3
    omega
  interval_cases p <;> first | omega | exact absurd hp (by norm_num) | exact absurd rfl hp2

theorem isStronglyQuasithin_of_card_dvd {G : Type*} [Group G] [Finite G]
    (h : Nat.card G ∣ 20160) : CFSG.IsStronglyQuasithin G := by
  rw [CFSG.IsStronglyQuasithin]
  intro p hp hp2
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  have hp1 : 1 < p := hp.one_lt
  refine CFSG.SectionRank.pRank_le hp1 fun E _ hE => ?_
  haveI : Fact p.Prime := ⟨hp⟩
  have hpg : IsPGroup p ↥E := fun g => ⟨1, Subtype.ext (by simpa using hE.2 g g.2)⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hpg
  have hdvd : Nat.card ↥E ∣ Nat.card G := Subgroup.card_subgroup_dvd_card E
  rw [hn] at hdvd
  have h20160 : p ^ n ∣ 20160 := hdvd.trans h
  by_cases hn2 : n ≤ 2
  · rw [hn]
    exact Nat.pow_le_pow_right hp.pos hn2
  · exfalso
    exact not_cube_dvd_20160 hp hp2 ((pow_dvd_pow p (by omega : 3 ≤ n)).trans h20160)

theorem card_alternatingGroup_dvd {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 8) :
    Nat.card ↥(alternatingGroup (Fin n)) ∣ 20160 := by
  rcases hn with rfl | rfl | rfl <;>
  · rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]

theorem isStronglyQuasithin_of_alt {K : Type*} [Group K] {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 8)
    (e : K ≃* ↥(alternatingGroup (Fin n))) : CFSG.IsStronglyQuasithin K := by
  haveI : Finite K := Finite.of_equiv _ e.symm.toEquiv
  refine isStronglyQuasithin_of_card_dvd ?_
  rw [Nat.card_congr e.toEquiv]
  exact card_alternatingGroup_dvd hn

variable {U : Type} [AddCommGroup U] [Module (ZMod 2) U]

end RonanG1015

end CFSG.Quasithin
