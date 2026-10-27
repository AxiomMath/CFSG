module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ub
public import CFSG.RankThree.PartTwo.Sec15.Item15Res3ProofInner

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16c34_uniqueMax_of_pRank (D : Data G) (h61 : UC6.R6_1 D) {p : ℕ} (hp : p ∈ D.sig)
    {X : Subgroup G} (hXM : X ≤ D.M) (h2 : 2 ≤ CFSG.Open.pRank p X) : UniqueMax D.M X := by
  have hpp := (D.sig_prime p hp).1
  obtain ⟨E, hEX, hE, hEc⟩ := CFSG.SectionRank.exists_pRank hpp.one_lt X
  have hEp : IsPGroup p E := CFSG.Open.IsElemAbelian.isPGroup hE
  have hEnc : ¬ IsCyclic ↥E := by
    intro hcyc
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := E)
    have h1 : orderOf g ∣ p :=
      orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hE.2 g g.2))
    rw [hg, hEc] at h1
    have h3 : p ^ 2 ≤ p ^ CFSG.Open.pRank p X := Nat.pow_le_pow_right hpp.pos h2
    have h4 : p < p ^ 2 := by nlinarith [hpp.one_lt]
    have := Nat.le_of_dvd hpp.pos h1
    omega
  have hU : UniqueMax D.M E := h61 p hp E (hEX.trans hXM) hEp hEnc
  unfold UniqueMax calMOf at hU ⊢
  ext N
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hN, hXN⟩
    have hmem : N ∈ {N | rankThreeIsMaxTwoLocal N ∧ E ≤ N} := ⟨hN, hEX.trans hXN⟩
    rw [hU] at hmem
    exact hmem
  · rintro rfl
    exact ⟨D.maxLocal, hXM⟩

theorem s16c34_exists_noncyclic_of_lBar {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    {L : Subgroup G} {p : ℕ} (hp : p.Prime) (h2 : 2 ≤ CFSG.Open.pRank p (lBar V₀ V hV L)) :
    ∃ P : Subgroup G, P ≤ L ∧ IsPGroup p P ∧ ¬ IsCyclic ↥P := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨E, hEL, hE, hEc⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (lBar V₀ V hV L)
  have hEp : IsPGroup p E := CFSG.Open.IsElemAbelian.isPGroup hE
  have hEnc : ¬ IsCyclic ↥E := by
    intro hcyc
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := E)
    have h1 : orderOf g ∣ p :=
      orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hE.2 g g.2))
    rw [hg, hEc] at h1
    have h3 : p ^ 2 ≤ p ^ CFSG.Open.pRank p (lBar V₀ V hV L) := Nat.pow_le_pow_right hp.pos h2
    have h4 : p < p ^ 2 := by nlinarith [hp.one_lt]
    have := Nat.le_of_dvd hp.pos h1
    omega
  obtain ⟨P, hPH, hPp, hPE⟩ :=
    CFSG.RankThree.PartTwo.Sec15.Proof15Res3Inner.exists_isPGroup_map_eq_of_le_map
      (actTil V₀ V hV) hEp (H := L.subgroupOf (stabTil V₀ V)) hEL
  refine ⟨P.map (stabTil V₀ V).subtype, ?_, hPp.map _, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (hPH hx)
  · intro hcyc
    have hP : IsCyclic ↥P :=
      (uc22p22u_isCyclic_map_iff _ (stabTil V₀ V).subtype_injective P).1 hcyc
    apply hEnc
    rw [← hPE]
    exact isCyclic_of_surjective ((actTil V₀ V hV).subgroupMap P)
      (MonoidHom.subgroupMap_surjective (actTil V₀ V hV) P)

theorem s16c34_uniqueMax_of_lBar (D : Data G) (h61 : UC6.R6_1 D) {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hLM : L ≤ D.M) {p : ℕ} (hp : p ∈ D.sig)
    (h2 : 2 ≤ CFSG.Open.pRank p (lBar V₀ V hV L)) : UniqueMax D.M L := by
  obtain ⟨P, hPL, hPp, hPc⟩ := s16c34_exists_noncyclic_of_lBar hV (D.sig_prime p hp).1 h2
  have hU : UniqueMax D.M P := h61 p hp P (hPL.trans hLM) hPp hPc
  unfold UniqueMax calMOf at hU ⊢
  ext N
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hN, hLN⟩
    have hmem : N ∈ {N | rankThreeIsMaxTwoLocal N ∧ P ≤ N} := ⟨hN, hPL.trans hLN⟩
    rw [hU] at hmem
    exact hmem
  · rintro rfl
    exact ⟨D.maxLocal, hLM⟩

theorem s16c34_mem_sig_of_four_le (D : Data G) (hSg : UC6S846.SigmaStd D) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h4 : 4 ≤ CFSG.Open.pRank p D.M) : p ∈ D.sig :=
  hSg.four_mem p hp hp2 h4

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
