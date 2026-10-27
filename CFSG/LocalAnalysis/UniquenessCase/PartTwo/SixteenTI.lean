module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenFiveTen
public import CFSG.LocalAnalysis.UniquenessCase.UC6R

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s16_TI_not_isCyclic {p : ℕ} (hp : p.Prime) {E : Subgroup G}
    (hE : IsElemAbelian p E) (hcard : p ^ 2 ≤ Nat.card E) : ¬ IsCyclic E := by
  intro hcyc
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := E)
  have h1 : orderOf g ∣ p :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hE.2 g g.2))
  rw [hg] at h1
  have h2 := Nat.le_of_dvd hp.pos h1
  have h3 := hp.one_lt
  nlinarith

private theorem s16_TI_uniqueMax_of_le {M E C : Subgroup G} (hM : rankThreeIsMaxTwoLocal M)
    (hEC : E ≤ C) (hCM : C ≤ M) (hE : UniqueMax M E) : UniqueMax M C := by
  refine Set.eq_singleton_iff_unique_mem.2 ⟨⟨hM, hCM⟩, fun N hN => ?_⟩
  have hN' : N ∈ calMOf E := ⟨hN.1, hEC.trans hN.2⟩
  rw [hE] at hN'
  exact hN'

theorem s16_TI_of_pRank (D : Data G) (h61 : UC6.R6_1 D) {V : Subgroup G}
    (hV : IsElemAbelian 2 V) (hM : D.M ≤ normalizer (V : Set G))
    (h : ∀ w ∈ V, w ≠ 1 → ∃ p ∈ D.sig,
      2 ≤ CFSG.Open.pRank p (D.M ⊓ centralizer ({w} : Set G))) :
    CFSG.CGT.Timmesfeld75.IsTI V := by
  refine s15_FiveTen_isTI_of_uniqueMax D hV hM fun w hw hw1 => ?_
  obtain ⟨p, hp, hr⟩ := h w hw hw1
  have hpp : p.Prime := (D.sig_prime p hp).1
  obtain ⟨E, hEC, hE, hEcard⟩ :=
    CFSG.SectionRank.exists_pRank hpp.one_lt (D.M ⊓ centralizer ({w} : Set G))
  have hcard : p ^ 2 ≤ Nat.card E := by
    rw [hEcard]
    exact Nat.pow_le_pow_right hpp.pos hr
  have hEM : E ≤ D.M := hEC.trans inf_le_left
  exact s16_TI_uniqueMax_of_le D.maxLocal hEC inf_le_left
    (h61 p hp E hEM hE.isPGroup (s16_TI_not_isCyclic hpp hE hcard))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
