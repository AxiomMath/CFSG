module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC6Rank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC6NonSing
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC6Sing
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC6Comm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC6U4Over

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

private theorem s16c6_not_isCyclic {p : ℕ} (hp : p.Prime) {E : Subgroup G}
    (hE : IsElemAbelian p E) (hcard : p ^ 2 ≤ Nat.card E) : ¬ IsCyclic E := by
  intro hcyc
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := E)
  have h1 : orderOf g ∣ p :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hE.2 g g.2))
  rw [hg] at h1
  have h2 := Nat.le_of_dvd hp.pos h1
  have h3 := hp.one_lt
  nlinarith

private theorem s16c6_uniqueMax_of_le {M E C : Subgroup G} (hM : rankThreeIsMaxTwoLocal M)
    (hEC : E ≤ C) (hCM : C ≤ M) (hE : UniqueMax M E) : UniqueMax M C := by
  refine Set.eq_singleton_iff_unique_mem.2 ⟨⟨hM, hCM⟩, fun N hN => ?_⟩
  have hN' : N ∈ calMOf E := ⟨hN.1, hEC.trans hN.2⟩
  rw [hE] at hN'
  exact hN'

private theorem s16c6_uniqueMax_of_pRank (D : Data G) (h61 : UC6.R6_1 D) {p : ℕ}
    (hp : p ∈ D.sig) {C : Subgroup G} (hCM : C ≤ D.M) (hr : 2 ≤ CFSG.Open.pRank p C) :
    UniqueMax D.M C := by
  have hpp : p.Prime := (D.sig_prime p hp).1
  obtain ⟨E, hEC, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank hpp.one_lt C
  have hcard : p ^ 2 ≤ Nat.card E := by
    rw [hEcard]
    exact Nat.pow_le_pow_right hpp.pos hr
  exact s16c6_uniqueMax_of_le D.maxLocal hEC hCM
    (h61 p hp E (hEC.trans hCM) hE.isPGroup (s16c6_not_isCyclic hpp hE hcard))

theorem s168e3_false_of_case163_6
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) (h924 : R9_24X D)
    (hc : Case163_6 D V₀ V hV L) : False := by
  have hS : Sect16 D V₀ V L hV := ⟨c.setting, c.ne, c.conc⟩
  have h3sig : 3 ∈ D.sig := by rw [hc.2.2.2.1]; rfl
  have hH : Hyp125 D V₀ V := c.setting.hyp16.hyp125
  have hMn : D.M ≤ normalizer (V : Set G) := hH.pairFacts.le_normalizer
  have hwT : wTil V₀ V hV L = ⊤ := wTil_eq_top_of_case163_2 c.conc hc.2.2.1
  have hNat : NatOmegaMinus (lBar V₀ V hV L) ⊤ ⊥ 6 3 := by
    have h := hc.2.1
    rwa [hwT] at h
  obtain ⟨F, hFfield, hFfin, b, c₀, hF, hirr, ε, ψ, hcoords⟩ :=
    S18.exists_natCoords_of_natOmegaMinus hNat
  letI := hFfield
  letI := hFfin
  let co : S16c6Coords V₀ V L hV :=
    { F := F, b := b, c := c₀, card_eq := by rw [hF], irr := hirr, ε := ε, ψ := ψ,
      coords := hcoords }
  have h129 : R129_1 D := r129_1_of_r127 D c.std.h127
  refine h129 V₀ V hH (s15_FiveTen_isTI_of_uniqueMax D hV hMn fun w hw hw1 => ?_)
  by_cases hw0 : w ∈ V₀
  · exact s16c6_uniqueMax_of_pRank D c.std.h61 h3sig inf_le_left
      (s16c6_v0_rank D hS hc hw hw1 hw0)
  · have hne1 : mkTil V₀ V hV (IntMod.mk hV ⟨w, hw⟩) ≠ 1 := by
      intro h
      have h' : mkTil V₀ V hV (IntMod.mk hV ⟨w, hw⟩) = mkTil V₀ V hV 1 := h.trans (map_one _).symm
      rw [mkTil_eq_iff] at h'
      have h'' : w * (1 : G)⁻¹ ∈ V₀ := h'
      exact hw0 (by simpa using h'')
    by_cases hQ : StatedQuadMinus 3 co.F co.b co.c (co.vec w hw) = 0
    · obtain ⟨K, P, X, hK, hKN, hU, hP, hX, hL2, hXp, hXle⟩ :=
        s16c6_singular_lift D c.std hS hc co hw ⟨hne1, hQ⟩
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hSP : IsStronglyPEmbedded 3 D.M :=
        UC6S846.sp_of_mem_sig c.std.hSg (UC6S846.not_solvable_of_mem_calC hK) h3sig
      have hcomm := s16c6_comm D hK hKN (n := 3) (by norm_num) hU
        (fun {_ _ _} hP' hX' hL2' hXR' => s16c6_u4_overgroup (by norm_num) hU hP' hX' hL2' hXR')
        hP hX hL2 hXp
      exact s16c6_uniqueMax_of_le D.maxLocal hXle inf_le_left
        (h924 K P X 3 hK hKN (by norm_num) hU hP hX hL2 hXp hcomm hSP)
    · exact s16c6_uniqueMax_of_pRank D c.std.h61 h3sig inf_le_left
        (s16c6_nonsing_rank D c.std hS hc co hw hQ)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
